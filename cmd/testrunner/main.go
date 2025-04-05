package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/toby-bro/pfuzz/internal/fuzz"
	"github.com/toby-bro/pfuzz/internal/simulator"
	"github.com/toby-bro/pfuzz/internal/testgen"
	"github.com/toby-bro/pfuzz/internal/verilog"
)

func main() {
	// Define command line flags
	svFile := flag.String("file", "", "SystemVerilog file to test")
	moduleName := flag.String("module", "", "Name of the module to test")
	workDir := flag.String("workdir", "tmp_test", "Working directory for test")
	useVerilator := flag.Bool("verilator", true, "Use Verilator for simulation")
	useIVerilog := flag.Bool("iverilog", true, "Use IVerilog for simulation")
	verbose := flag.Bool("verbose", false, "Enable verbose output")

	flag.Parse()

	// Validate required parameters
	if *svFile == "" || *moduleName == "" {
		log.Fatal("SystemVerilog file (-file) and module name (-module) are required")
	}

	// Ensure file exists
	if _, err := os.Stat(*svFile); os.IsNotExist(err) {
		log.Fatalf("File %s does not exist", *svFile)
	}

	// Create working directory
	if err := os.MkdirAll(*workDir, 0755); err != nil {
		log.Fatalf("Failed to create working directory: %v", err)
	}

	// Process the file
	mockedPath := filepath.Join(*workDir, *moduleName+"_mocked.sv")
	if err := fuzz.PrepareSVFile(*svFile, mockedPath); err != nil {
		log.Fatalf("Failed to prepare SystemVerilog file: %v", err)
	}
	log.Printf("Created mocked file: %s", mockedPath)

	// Parse the module - use original module name to avoid double _mocked suffix
	module, err := verilog.ParseVerilogFile(mockedPath, *moduleName)
	if err != nil {
		log.Fatalf("Failed to parse module: %v", err)
	}
	log.Printf("Successfully parsed module with %d ports", len(module.Ports))

	// Generate testbench
	generator := testgen.NewGenerator(module)
	if err := generator.GenerateSVTestbench(); err != nil {
		log.Fatalf("Failed to generate testbenches: %v", err)
	}
	log.Printf("Generated testbench")

	// Create tmp_gen directory in working directory if needed
	tmpGenInWorkDir := filepath.Join(*workDir, "tmp_gen")
	if err := os.MkdirAll(tmpGenInWorkDir, 0755); err != nil {
		log.Fatalf("Failed to create tmp_gen directory: %v", err)
	}

	// Copy testbench to working directory
	testbenchSrcPath := filepath.Join("tmp_gen", "testbench.sv")
	testbenchDestPath := filepath.Join(*workDir, "testbench.sv")
	testbenchData, err := os.ReadFile(testbenchSrcPath)
	if err != nil {
		log.Fatalf("Failed to read generated testbench: %v", err)
	}
	if err := os.WriteFile(testbenchDestPath, testbenchData, 0644); err != nil {
		log.Fatalf("Failed to copy testbench to working directory: %v", err)
	}

	// Compile with chosen simulators
	if *useIVerilog {
		log.Printf("Compiling with IVerilog...")
		ivsim := simulator.NewIVerilogSimulator(*workDir, *verbose)

		// Only compile the specific module and testbench
		specificFiles := []string{
			filepath.Join(*workDir, *moduleName+"_mocked.sv"),
			filepath.Join(*workDir, "testbench.sv"),
		}

		if err := ivsim.CompileSpecific(specificFiles); err != nil {
			log.Fatalf("Failed to compile with IVerilog: %v", err)
		}
		log.Printf("Successfully compiled with IVerilog")
	}

	if *useVerilator {
		log.Printf("Compiling with Verilator...")
		vlsim := simulator.NewVerilatorSimulator(*workDir, *moduleName+"_mocked")
		if err := vlsim.Compile(); err != nil {
			log.Fatalf("Failed to compile with Verilator: %v", err)
		}
		log.Printf("Successfully compiled with Verilator")
	}

	fmt.Println("\nCompilation completed successfully!")
	fmt.Println("To run the simulation manually:")
	if *useIVerilog {
		fmt.Printf("  cd %s && ./module_sim_iv\n", *workDir)
	}
	if *useVerilator {
		fmt.Printf("  cd %s && ./obj_dir/V%s_mocked --input-dir=. --output-<PORT>=output_<PORT>.hex\n",
			*workDir, *moduleName)
	}
}
