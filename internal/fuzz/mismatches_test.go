package fuzz

import (
	"context"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func TestCompareOutputValues(t *testing.T) {
	tests := []struct {
		name     string
		ivValue  string
		vlValue  string
		expected bool
	}{
		{"identical values", "1010", "1010", true},
		{"case insensitive", "1010", "1010", true},
		{"whitespace trimming", " 1010 ", "1010", true},
		{"different values", "1010", "0101", false},
		{"x in iv with skip", "1x10", "1010", true},
		{"x in vl with skip", "1010", "1x10", true},
		{"z in iv with skip", "1z10", "1010", true},
		{"z in vl with skip", "1010", "1z10", true},
		{"00 vs xx equivalence", "00", "xx", true},
		{"xx vs 00 equivalence", "xx", "00", true},
		{"0 vs x equivalence", "0", "x", true},
		{"x vs 0 equivalence", "x", "0", true},
		{"mixed x equivalence", "1x0x", "1000", true},
		// {"mixed x non-equivalence", "1x0x", "1101", false},
		{"uppercase X", "1X0X", "1000", true},
		{"uppercase Z", "1Z0Z", "1000", true},
		{"different lengths", "101", "10101", false},
	}

	// Save original values
	origSkipX := SKIP_X_OUTPUTS
	origSkipZ := SKIP_Z_OUTPUTS
	defer func() {
		SKIP_X_OUTPUTS = origSkipX
		SKIP_Z_OUTPUTS = origSkipZ
	}()

	// Set skip flags for most tests
	SKIP_X_OUTPUTS = true
	SKIP_Z_OUTPUTS = true

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := compareOutputValues(tt.ivValue, tt.vlValue)
			if result != tt.expected {
				t.Errorf(
					"compareOutputValues(%q, %q) = %v, want %v",
					tt.ivValue,
					tt.vlValue,
					result,
					tt.expected,
				)
			}
		})
	}
}

type dummySim struct{}

func (d *dummySim) RunTest(
	_ context.Context,
	_ string,
	_ map[*verilog.Port]string,
) error {
	return nil // Dummy implementation for testing
}

func (d *dummySim) Compile(_ context.Context) error {
	return nil // Dummy implementation for testing
}

func (d *dummySim) FailedCuzUnsupportedFeature(_ error) (bool, error) {
	return false, nil // Dummy implementation for testing
}

func (d *dummySim) Type() simulator.Type {
	return simulator.CXXRTL // Dummy implementation for testing
}

func TestScheduler_compareAllResults(t *testing.T) {
	sim1 := &SimInstance{Simulator: &dummySim{}}
	sim2 := &SimInstance{Simulator: &dummySim{}}
	port1 := &verilog.Port{Name: "port1"}
	port2 := &verilog.Port{Name: "port2"}
	sch := &Scheduler{
		debug: utils.NewDebugLogger(0),
	}
	// Save original skip flags
	origSkipX := SKIP_X_OUTPUTS
	origSkipZ := SKIP_Z_OUTPUTS
	defer func() {
		SKIP_X_OUTPUTS = origSkipX
		SKIP_Z_OUTPUTS = origSkipZ
	}()
	SKIP_X_OUTPUTS = true
	SKIP_Z_OUTPUTS = true
	tests := []struct {
		name               string
		input              map[*SimInstance]map[*verilog.Port]string
		expectedMismatch   bool
		expectedDetailKeys []*verilog.Port
	}{
		{
			name: "no mismatch",
			input: map[*SimInstance]map[*verilog.Port]string{
				sim1: {port1: "1010", port2: "0101"},
				sim2: {port1: "1010", port2: "0101"},
			},
			expectedMismatch:   false,
			expectedDetailKeys: []*verilog.Port{},
		},
		{
			name: "mismatch found",
			input: map[*SimInstance]map[*verilog.Port]string{
				sim1: {port1: "1010", port2: "0101"},
				sim2: {port1: "1111", port2: "0101"},
			},
			expectedMismatch:   true,
			expectedDetailKeys: []*verilog.Port{port1},
		},
		{
			name: "missing port in one sim",
			input: map[*SimInstance]map[*verilog.Port]string{
				sim1: {port1: "1010", port2: "0101"},
				sim2: {port1: "1010"},
			},
			expectedMismatch:   true,
			expectedDetailKeys: []*verilog.Port{port2},
		},
		{
			name: "missing sim data",
			input: map[*SimInstance]map[*verilog.Port]string{
				sim1: {port1: "1010"},
			},
			expectedMismatch:   false,
			expectedDetailKeys: []*verilog.Port{},
		},
		{
			name:               "empty results",
			input:              map[*SimInstance]map[*verilog.Port]string{},
			expectedMismatch:   false,
			expectedDetailKeys: []*verilog.Port{},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			mismatch, details := sch.compareAllResults(tt.input)
			if mismatch != tt.expectedMismatch {
				t.Errorf("Expected mismatch = %v, got %v", tt.expectedMismatch, mismatch)
			}
			if len(details) != len(tt.expectedDetailKeys) {
				t.Errorf(
					"Expected %d detail keys, got %d",
					len(tt.expectedDetailKeys),
					len(details),
				)
			}
			for _, key := range tt.expectedDetailKeys {
				if _, exists := details[key]; !exists {
					t.Errorf("Expected detail key %q not found in results", key.Name)
				}
			}
		})
	}
}

func TestScheduler_handleMismatch(t *testing.T) {
	// Create a temporary directory for testing
	tempDir := t.TempDir()
	// Set up the mismatches directory
	oldMismatchesDir := utils.MISMATCHES_DIR
	utils.MISMATCHES_DIR = filepath.Join(tempDir, "mismatches")
	defer func() {
		utils.MISMATCHES_DIR = oldMismatchesDir
	}()
	// Create test directory with some files
	testDir := filepath.Join(tempDir, "dist", "worker_1", "test_1")
	err := os.MkdirAll(testDir, 0o755)
	if err != nil {
		t.Fatal(err)
	}
	// Create test files in testDir
	testFiles := []string{"output.txt", "log.txt"}
	for _, file := range testFiles {
		err = os.WriteFile(filepath.Join(testDir, file), []byte("test content"), 0o644)
		if err != nil {
			t.Fatal(err)
		}
	}
	// Create base source directory with testbench.sv
	baseSrcDir := filepath.Dir(testDir)
	err = os.WriteFile(filepath.Join(baseSrcDir, "testbench.sv"), []byte("// testbench"), 0o644)
	if err != nil {
		t.Fatal(err)
	}
	// Create mock verilog file and module
	vFile := &verilog.VerilogFile{Name: "test_module.sv"}
	module := &verilog.Module{Name: "test_module"}
	sch := &Scheduler{
		debug:  utils.NewDebugLogger(0),
		stats:  NewStats(),
		svFile: vFile,
	}
	// Use *verilog.Port keys for testCase and mismatchDetails
	port1 := &verilog.Port{Name: "input1"}
	port2 := &verilog.Port{Name: "input2"}
	outPort := &verilog.Port{Name: "output1"}
	testCase := map[*verilog.Port]string{
		port1: "1010",
		port2: "0101",
	}
	mismatchDetails := map[*verilog.Port]string{
		outPort: "sim1=1010, sim2=1111",
	}
	// Run the function
	sch.handleMismatch(1, testDir, testCase, mismatchDetails, module)
	// Verify mismatch directory was created
	mismatchDirs, err := filepath.Glob(
		filepath.Join(utils.MISMATCHES_DIR, "worker_*", "test_*"),
	)
	if err != nil {
		t.Fatal(err)
	}
	if len(mismatchDirs) != 1 {
		t.Fatalf("Expected 1 mismatch directory, got %d", len(mismatchDirs))
	}

	mismatchDir := mismatchDirs[0]

	// Verify files were copied
	for _, file := range testFiles {
		if _, err := os.Stat(filepath.Join(mismatchDir, file)); os.IsNotExist(err) {
			t.Errorf("Expected file %s to be copied to mismatch directory", file)
		}
	}

	// Verify summary file was created
	summaryFiles, err := filepath.Glob(
		filepath.Join(filepath.Dir(mismatchDir), "mismatch_*_summary.txt"),
	)
	if err != nil {
		t.Fatal(err)
	}
	if len(summaryFiles) != 1 {
		t.Fatalf("Expected 1 summary file, got %d", len(summaryFiles))
	}

	// Verify summary content
	content, err := os.ReadFile(summaryFiles[0])
	if err != nil {
		t.Fatal(err)
	}
	contentStr := string(content)
	if !strings.Contains(contentStr, "input1 = 1010") {
		t.Error("Summary should contain input values")
	}
	if !strings.Contains(contentStr, "output1:") || !strings.Contains(contentStr, "sim1=1010") ||
		!strings.Contains(contentStr, "sim2=1111") {
		t.Error("Summary should contain mismatch details")
	}

	// Verify testbench.sv was copied
	if _, err := os.Stat(filepath.Join(filepath.Dir(mismatchDir), "testbench.sv")); os.IsNotExist(
		err,
	) {
		t.Error("Expected testbench.sv to be copied to mismatch directory")
	}
}

func TestCompareOutputValues_sameSnippet(t *testing.T) {
	// Extracted from the `same` variable in mismatches_test.go
	verilator := "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000"
	iverilog := "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz1zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0"
	cxxrtl := "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000"
	xcelium := "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz1zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0"

	// Save and restore skip flags
	origSkipX := SKIP_X_OUTPUTS
	origSkipZ := SKIP_Z_OUTPUTS
	defer func() {
		SKIP_X_OUTPUTS = origSkipX
		SKIP_Z_OUTPUTS = origSkipZ
	}()
	SKIP_X_OUTPUTS = true
	SKIP_Z_OUTPUTS = false

	// All pairs should be considered equivalent
	values := []string{verilator, iverilog, cxxrtl, xcelium}
	for i := 0; i < len(values); i++ {
		for j := 0; j < len(values); j++ {
			if !compareOutputValues(values[i], values[j]) {
				t.Errorf("compareOutputValues(values[%d], values[%d]) = false, want true", i, j)
			}
		}
	}
}
