package verilog

func (m *Module) DeepCopy() *Module {
	if m == nil {
		return nil
	}
	copiedModule := &Module{
		Name:      m.Name,
		Body:      m.Body,
		AnsiStyle: m.AnsiStyle,
	}
	copiedModule.Ports = make([]*Port, len(m.Ports))
	copy(copiedModule.Ports, m.Ports)
	copiedModule.Parameters = make([]*Parameter, len(m.Parameters))
	copy(copiedModule.Parameters, m.Parameters)

	return copiedModule
}

func (d *DependencyNode) DeepCopy() *DependencyNode {
	if d == nil {
		return nil
	}
	copiedNode := &DependencyNode{
		Name:       d.Name,
		DependsOn:  make([]string, len(d.DependsOn)),
		DependedBy: make([]string, len(d.DependedBy)),
	}
	copy(copiedNode.DependsOn, d.DependsOn)
	copy(copiedNode.DependedBy, d.DependedBy)
	return copiedNode
}

func (vf *VerilogFile) DeepCopy() *VerilogFile {
	if vf == nil {
		return nil
	}
	copiedFile := &VerilogFile{
		Name:          vf.Name,
		Modules:       make(map[string]*Module),
		Interfaces:    make(map[string]*Interface),
		Packages:      make(map[string]*Package),
		Classes:       make(map[string]*Class),
		Structs:       make(map[string]*Struct),
		DependencyMap: make(map[string]*DependencyNode),
		Typedefs:      make(map[string]*Typedef),
	}
	for name, module := range vf.Modules {
		copiedFile.Modules[name] = module.DeepCopy()
	}
	for name, iface := range vf.Interfaces {
		copiedFile.Interfaces[name] = iface
	}
	for name, class := range vf.Classes {
		copiedFile.Classes[name] = class
	}
	for name, strct := range vf.Structs {
		copiedFile.Structs[name] = strct
	}
	for name, depNode := range vf.DependencyMap {
		copiedFile.DependencyMap[name] = depNode.DeepCopy()
	}
	for name, pkg := range vf.Packages {
		copiedFile.Packages[name] = pkg
	}
	for name, tdf := range vf.Typedefs {
		copiedFile.Typedefs[name] = tdf
	}
	return copiedFile
}
