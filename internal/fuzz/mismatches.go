package fuzz

import (
	"fmt"
	"os"
	"path/filepath"
	"sort" // Added for sorting simulator names
	"strings"
	"time"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

var (
	SKIP_X_OUTPUTS = true
	SKIP_Z_OUTPUTS = true
)

func compareOutputValues(ivValue, vlValue string) bool {
	ivNorm := strings.TrimSpace(strings.ToLower(ivValue))
	vlNorm := strings.TrimSpace(strings.ToLower(vlValue))
	if SKIP_X_OUTPUTS && (strings.Contains(ivNorm, "x") ||
		strings.Contains(vlNorm, "x")) {
		return true
	}
	if SKIP_Z_OUTPUTS && (strings.Contains(ivNorm, "z") ||
		strings.Contains(vlNorm, "z")) {
		return true
	}
	if ivNorm == vlNorm {
		return true
	}
	if len(ivNorm) == len(vlNorm) && ivNorm != vlNorm {
		if strings.Contains(ivNorm, "x") || strings.Contains(vlNorm, "x") {
			equivalent := true
			for i := 0; i < len(ivNorm); i++ {
				charMatch := ivNorm[i] == vlNorm[i] ||
					(ivNorm[i] == 'x' && vlNorm[i] == '0') ||
					(ivNorm[i] == '0' && vlNorm[i] == 'x')
				if !charMatch {
					equivalent = false
					break
				}
			}
			return equivalent
		}
	}
	return false
}

func replaceXandZwithZero(value string) string {
	// Replace 'x' and 'z' with '0'
	value = strings.ReplaceAll(value, "x", "0")
	value = strings.ReplaceAll(value, "z", "0")
	// Replace 'X' and 'Z' with '0'
	value = strings.ReplaceAll(value, "X", "0")
	value = strings.ReplaceAll(value, "Z", "0")
	return value
}

func cleanAllOutputValues(results map[string]map[string]string) {
	for simName, simResultMap := range results {
		for portName, value := range simResultMap {
			results[simName][portName] = replaceXandZwithZero(value)
		}
	}
}

func (sch *Scheduler) compareAllResults(
	results map[string]map[string]string,
) (bool, map[string]string) {
	mismatchFound := false
	mismatchDetails := make(map[string]string)

	if !SKIP_X_OUTPUTS && !SKIP_Z_OUTPUTS {
		cleanAllOutputValues(results)
	}

	simNames := make([]string, 0, len(results))
	for simName := range results {
		simNames = append(simNames, simName)
	}
	sort.Strings(simNames)

	allPorts := make(map[string]bool)
	for _, simResultMap := range results {
		for portName := range simResultMap {
			allPorts[portName] = true
		}
	}

	for portName := range allPorts {
		portReportEntries := make(map[string]string)
		actualValuesPresent := []string{}
		simsHavingThePortCount := 0

		for _, simName := range simNames {
			simResultMap, simExists := results[simName]
			if !simExists {
				portReportEntries[simName] = "SIM_DATA_MISSING"
				continue
			}
			if value, found := simResultMap[portName]; found {
				portReportEntries[simName] = value
				actualValuesPresent = append(actualValuesPresent, value)
				simsHavingThePortCount++
			} else {
				portReportEntries[simName] = "MISSING"
			}
		}

		isThisPortMismatch := false
		if simsHavingThePortCount > 0 && simsHavingThePortCount < len(simNames) {
			isThisPortMismatch = true
		} else if simsHavingThePortCount >= 2 {
			refValue := actualValuesPresent[0]
			for i := 1; i < len(actualValuesPresent); i++ {
				if !compareOutputValues(refValue, actualValuesPresent[i]) {
					isThisPortMismatch = true
					break
				}
			}
		}

		if isThisPortMismatch {
			mismatchFound = true
			detailParts := make([]string, 0, len(simNames))
			for _, simName := range simNames {
				detailParts = append(
					detailParts,
					fmt.Sprintf("%s=%s", simName, portReportEntries[simName]),
				)
			}
			mismatchDetails[portName] = strings.Join(detailParts, ", ")
			sch.debug.Warn("Mismatch for port %s: %s", portName, mismatchDetails[portName])
		}
	}

	if mismatchFound {
		var simNamesStr string
		if len(simNames) > 0 {
			simNamesStr = strings.Join(simNames, ", ")
		} else {
			sch.debug.Error("No simulator names found in results map")
		}
		sch.debug.Debug(
			"Comparison across %s found mismatches: %v",
			simNamesStr,
			mismatchDetails,
		)
	}

	return mismatchFound, mismatchDetails
}

// logMismatchInfo logs the mismatch information and updates statistics
func (sch *Scheduler) logMismatchInfo(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module,
) {
	sch.stats.AddMismatch(testCase)
	sch.debug.Info(
		"[%s] Mismatch FOUND in test %d for module %s",
		filepath.Base(testDir),
		testIndex,
		workerModule.Name,
	)
	sch.debug.Info("Inputs for test %d:", testIndex)
	for portName, value := range testCase {
		sch.debug.Info("  %s = %s", portName, value)
	}
	sch.debug.Info("Mismatched outputs:")
	for portName, detail := range mismatchDetails {
		sch.debug.Info("  %s: %s", portName, detail)
	}
}

// createMismatchDirectory creates a unique directory for storing mismatch artifacts
func (sch *Scheduler) createMismatchDirectory(testIndex int) (string, error) {
	mismatchInstanceName := fmt.Sprintf("mismatch_test_%d_time_%d",
		testIndex, time.Now().UnixNano())
	mismatchDir := filepath.Join(utils.MISMATCHES_DIR, mismatchInstanceName)

	if err := os.MkdirAll(mismatchDir, 0o755); err != nil {
		sch.debug.Error("Failed to create mismatch directory %s: %v", mismatchDir, err)
		return "", err
	}
	return mismatchDir, nil
}

// copyTestFiles copies files from the test directory to the mismatch directory
func (sch *Scheduler) copyTestFiles(testDir, mismatchDir string) {
	sch.debug.Debug(
		"Copying files from test directory %s to mismatch directory %s",
		testDir,
		mismatchDir,
	)
	files, err := os.ReadDir(testDir)
	if err != nil {
		sch.debug.Error("Failed to read test directory %s: %v", testDir, err)
		return
	}

	for _, file := range files {
		if !file.IsDir() {
			srcPath := filepath.Join(testDir, file.Name())
			destPath := filepath.Join(mismatchDir, file.Name())
			if err := utils.CopyFile(srcPath, destPath); err != nil {
				sch.debug.Error("Failed to copy file %s to %s: %v", srcPath, destPath, err)
			}
		}
	}
}

// writeMismatchSummary creates and writes the mismatch summary file
func (sch *Scheduler) writeMismatchSummary(
	testIndex int,
	mismatchDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
) {
	summaryPath := filepath.Join(mismatchDir, fmt.Sprintf("mismatch_%d_summary.txt", testIndex))
	fileContent := fmt.Sprintf("Test case %d\n\nInputs:\n", testIndex)

	for portName, value := range testCase {
		fileContent += fmt.Sprintf("  %s = %s\n", portName, value)
	}

	fileContent += "\nMismatched outputs:\n"
	for portName, detail := range mismatchDetails {
		fileContent += fmt.Sprintf("  %s:\n", portName)
		detailsSplit := strings.Split(detail, ", ")
		for _, part := range detailsSplit {
			fileContent += fmt.Sprintf("    %s\n", part)
		}
	}

	sch.debug.Debug("Writing mismatch summary to %s", summaryPath)
	if err := utils.WriteFileContent(summaryPath, fileContent); err != nil {
		sch.debug.Error("Failed to write mismatch summary to %s: %v", summaryPath, err)
	}
}

// copySvFile copies the main SystemVerilog file to the mismatch directory
func (sch *Scheduler) copySvFile(baseSrcDir, mismatchDir string) {
	if sch.svFile == nil || sch.svFile.Name == "" {
		sch.debug.Warn(
			"sch.svFile or sch.svFile.Name is not set. Skipping copy of original SV file.",
		)
		return
	}

	originalSvFileName := sch.svFile.Name
	sourceSvFilePath := filepath.Join(baseSrcDir, originalSvFileName)
	destSvFilePath := filepath.Join(mismatchDir, originalSvFileName)

	if _, statErr := os.Stat(sourceSvFilePath); statErr == nil {
		if copyErr := utils.CopyFile(sourceSvFilePath, destSvFilePath); copyErr != nil {
			sch.debug.Warn(
				"Failed to copy original SV file %s to %s: %v",
				sourceSvFilePath,
				destSvFilePath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied original SV file %s to %s", sourceSvFilePath, destSvFilePath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Error stating original SV file %s: %v. Skipping copy.", sourceSvFilePath, statErr)
	} else {
		sch.debug.Info("Original SV file %s not found. Skipping copy.", sourceSvFilePath)
	}
}

// copyTestbenchFile copies the testbench.sv file to the mismatch directory
func (sch *Scheduler) copyTestbenchFile(baseSrcDir, mismatchDir string) {
	sourceTestbenchPath := filepath.Join(baseSrcDir, "testbench.sv")
	destTestbenchPath := filepath.Join(mismatchDir, "testbench.sv")

	if _, statErr := os.Stat(sourceTestbenchPath); statErr == nil {
		if copyErr := utils.CopyFile(sourceTestbenchPath, destTestbenchPath); copyErr != nil {
			sch.debug.Warn(
				"Failed to copy testbench.sv %s to %s: %v",
				sourceTestbenchPath,
				destTestbenchPath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied testbench.sv %s to %s", sourceTestbenchPath, destTestbenchPath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Error stating testbench.sv %s: %v. Skipping copy.", sourceTestbenchPath, statErr)
	} else {
		sch.debug.Debug("testbench.sv %s not found. Skipping copy.", sourceTestbenchPath)
	}
}

// copyCxxrtlFiles copies CXXRTL-related files to the mismatch directory
func (sch *Scheduler) copyCxxrtlFiles(
	baseSrcDir, mismatchDir string,
	workerModule *verilog.Module,
) {
	cxxrtlDirNames := []string{"cxxrtl_sim", "cxxrtl_slang_sim"}

	for _, dirName := range cxxrtlDirNames {
		cxxrtlSimDir := filepath.Join(baseSrcDir, dirName)

		if _, statErr := os.Stat(cxxrtlSimDir); os.IsNotExist(statErr) {
			sch.debug.Debug("CXXRTL directory %s not found. Skipping.", cxxrtlSimDir)
			continue
		} else if statErr != nil {
			sch.debug.Warn("Error stating CXXRTL directory %s: %v. Skipping.", cxxrtlSimDir, statErr)
			continue
		}

		sch.debug.Debug("Checking for CXXRTL files in %s", cxxrtlSimDir)
		sch.copyCxxrtlTestbench(cxxrtlSimDir, mismatchDir, dirName)
		sch.copyCxxrtlModuleFile(cxxrtlSimDir, mismatchDir, dirName, workerModule)
	}
}

// copyCxxrtlTestbench copies the CXXRTL testbench.cpp file
func (sch *Scheduler) copyCxxrtlTestbench(cxxrtlSimDir, mismatchDir, dirName string) {
	sourceCppTestbenchPath := filepath.Join(cxxrtlSimDir, "testbench.cpp")
	destCppTestbenchPath := filepath.Join(mismatchDir, dirName+"_testbench.cpp")

	if _, statErr := os.Stat(sourceCppTestbenchPath); statErr == nil {
		if copyErr := utils.CopyFile(sourceCppTestbenchPath, destCppTestbenchPath); copyErr != nil {
			sch.debug.Error(
				"Failed to copy CXXRTL testbench %s to %s: %v",
				sourceCppTestbenchPath,
				destCppTestbenchPath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied CXXRTL testbench.cpp %s to %s", sourceCppTestbenchPath, destCppTestbenchPath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Could not stat CXXRTL testbench %s: %v. Skipping copy.", sourceCppTestbenchPath, statErr)
	}
}

// copyCxxrtlModuleFile copies the CXXRTL module .cc file
func (sch *Scheduler) copyCxxrtlModuleFile(
	cxxrtlSimDir, mismatchDir, dirName string,
	workerModule *verilog.Module,
) {
	if workerModule == nil || workerModule.Name == "" {
		sch.debug.Warn(
			"workerModule or workerModule.Name is not set. Skipping copy of CXXRTL module .cc file for %s.",
			dirName,
		)
		return
	}

	cxxrtlModuleCcFileName := workerModule.Name + ".cc"
	sourceModuleCcPath := filepath.Join(cxxrtlSimDir, cxxrtlModuleCcFileName)
	destModuleCcPath := filepath.Join(
		mismatchDir,
		fmt.Sprintf("%s_%s", dirName, cxxrtlModuleCcFileName),
	)

	if _, statErr := os.Stat(sourceModuleCcPath); statErr == nil {
		if copyErr := utils.CopyFile(sourceModuleCcPath, destModuleCcPath); copyErr != nil {
			sch.debug.Error(
				"Failed to copy CXXRTL module .cc file %s to %s: %v",
				sourceModuleCcPath,
				destModuleCcPath,
				copyErr,
			)
		} else {
			sch.debug.Debug("Copied CXXRTL module .cc file %s to %s", sourceModuleCcPath, destModuleCcPath)
		}
	} else if !os.IsNotExist(statErr) {
		sch.debug.Warn("Could not stat CXXRTL module .cc file %s: %v. Skipping copy.", sourceModuleCcPath, statErr)
	}
}

// copySpecificFiles copies specific files relevant to the test case
func (sch *Scheduler) copySpecificFiles(testDir, mismatchDir string, workerModule *verilog.Module) {
	sch.debug.Info("Copying specific files for mismatch in %s", mismatchDir)

	// Base directory for source files (design, testbench, etc.)
	// testDir is like .../work_dir/test_N. Its parent is work_dir.
	baseSrcDir := filepath.Join(testDir, "..")

	sch.copySvFile(baseSrcDir, mismatchDir)
	sch.copyTestbenchFile(baseSrcDir, mismatchDir)
	sch.copyCxxrtlFiles(baseSrcDir, mismatchDir, workerModule)
}

func (sch *Scheduler) handleMismatch(
	testIndex int,
	testDir string,
	testCase map[string]string,
	mismatchDetails map[string]string,
	workerModule *verilog.Module,
) {
	sch.logMismatchInfo(testIndex, testDir, testCase, mismatchDetails, workerModule)

	mismatchDir, err := sch.createMismatchDirectory(testIndex)
	if err != nil {
		return
	}

	sch.copyTestFiles(testDir, mismatchDir)
	sch.writeMismatchSummary(testIndex, mismatchDir, testCase, mismatchDetails)
	sch.copySpecificFiles(testDir, mismatchDir, workerModule)

	sch.debug.Debug("Mismatch artifacts for test %d saved to %s", testIndex, mismatchDir)
}
