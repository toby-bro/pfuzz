package snippets

import (
	"errors"
	"fmt"

	"github.com/toby-bro/pfuzz/pkg/utils"
	"github.com/toby-bro/pfuzz/pkg/verilog"
)

func (s *Snippet) writeSnippetToFile() error {
	if s.Module == nil {
		return errors.New("module is nil")
	}
	if s.ParentFile == nil {
		return errors.New("parent file is nil")
	}

	baseName := s.ParentFile.Name
	if len(baseName) > 3 && baseName[len(baseName)-3:] == ".sv" {
		baseName = baseName[:len(baseName)-3]
	}

	svFile := verilog.NewVerilogFile(s.Module.Name + ".sv")

	err := AddDependencies(svFile, s)
	if err != nil {
		return fmt.Errorf("failed to add dependencies: %v", err)
	}
	content, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		return fmt.Errorf("failed to print Verilog file: %v", err)
	}
	path, err := utils.GetRootDir()
	if err != nil {
		return fmt.Errorf("failed to get root directory: %v", err)
	}
	filePath := path + "/isolated/" + baseName
	err = utils.EnsureDir(filePath)
	if err != nil {
		return fmt.Errorf("failed to create directory for Verilog file: %v", err)
	}
	err = utils.WriteFileContent(filePath+"/"+svFile.Name, content)
	if err != nil {
		return fmt.Errorf("failed to write Verilog file: %v", err)
	}
	return nil
}

func splitVerilogFile(svFile *verilog.VerilogFile) ([]*Snippet, error) {
	if svFile == nil {
		return nil, errors.New("Verilog file is nil")
	}
	snippets := []*Snippet{}
	for _, module := range svFile.Modules {
		snippet := &Snippet{
			Name:       module.Name,
			Module:     module,
			ParentFile: svFile,
		}
		snippets = append(snippets, snippet)
	}
	return snippets, nil
}

func writeSnippetsToFile(snippets []*Snippet) error {
	for _, snippet := range snippets {
		err := snippet.writeSnippetToFile()
		if err != nil {
			return fmt.Errorf("failed to write snippet to file: %v", err)
		}
	}
	return nil
}

func WriteFileAsSnippets(svFile *verilog.VerilogFile) error {
	snippets, err := splitVerilogFile(svFile)
	if err != nil {
		return fmt.Errorf("failed to split Verilog file: %v", err)
	}
	err = writeSnippetsToFile(snippets)
	if err != nil {
		return fmt.Errorf("failed to write snippets to file: %v", err)
	}
	return nil
}

func PrintMinimalVerilogFileInDist(
	parentFile *verilog.VerilogFile,
	moduleName string,
	workerDir string,
) error {
	module := parentFile.Modules[moduleName]
	if module == nil {
		return errors.New("module is nil")
	}
	if parentFile == nil {
		return errors.New("parent file is nil")
	}

	svFile := verilog.NewVerilogFile(module.Name + ".sv")

	snippet := &Snippet{
		Name:       module.Name,
		ParentFile: parentFile,
		Module:     module,
	}

	err := AddDependencies(svFile, snippet)
	if err != nil {
		return fmt.Errorf("failed to add dependencies: %v", err)
	}
	content, err := verilog.PrintVerilogFile(svFile)
	if err != nil {
		return fmt.Errorf("failed to print Verilog file: %v", err)
	}
	err = utils.EnsureDir(workerDir)
	if err != nil {
		return fmt.Errorf("failed to create directory for Verilog file: %v", err)
	}
	err = utils.WriteFileContent(workerDir+"/"+svFile.Name, content)
	if err != nil {
		return fmt.Errorf("failed to write Verilog file: %v", err)
	}
	return nil
}

// WriteFileAsSnippetsSubset writes only the provided modules as snippets to the file
func WriteFileAsSnippetsSubset(svFile *verilog.VerilogFile, modules []*verilog.Module) error {
	if svFile == nil {
		return errors.New("verilog file is nil")
	}
	if len(modules) == 0 {
		return errors.New("no modules to write")
	}

	for _, module := range modules {
		snippet := &Snippet{
			Name:       module.Name,
			Module:     module,
			ParentFile: svFile,
		}
		err := snippet.writeSnippetToFile()
		if err != nil {
			return fmt.Errorf("failed to write snippet %s to file: %v", module.Name, err)
		}
	}

	return nil
}
