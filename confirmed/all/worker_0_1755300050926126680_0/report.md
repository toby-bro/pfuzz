# Simulator Discrepancy Report: Dynamic Class Instantiation in `always_comb`

## 1. The Core Issue

A significant bug was identified where multiple industry-standard SystemVerilog simulators produce a different, incorrect result compared to Verilator for the same piece of code. The issue highlights a fundamental disagreement in how simulators handle non-synthesizable, dynamic code constructs within a synthesizable, combinational logic block.

## 2. The Problematic Code

The discrepancy originates from instantiating a SystemVerilog class object and accessing its properties from within an `always_comb` block in `design.sv`.

```systemverilog
// design.sv
class pkt_ext extends pkt;
    // ...
    function new(bit [7:0] id_i, bit [31:0] data_i);
        super.new(id_i, data_i);
        crc = ^{id_i, data_i}; // CRC calculation
    endfunction
endclass

module class_user (
    // ...
    output logic [15:0] crc_o
);
    always_comb begin
        pkt_ext p = new(id_i, data_i); // Instantiates a class
        crc_o = p.crc;                 // Accesses a class property
    end
endmodule
```

## 3. Simulator Behavior Analysis

The simulation results show a clear split in behavior between Verilator and all other tested simulators.

* **Expected (and Verilator's) Result**: The output `crc_o` is `16'h0001`. This is the correct logical result of the XOR-reduction CRC calculated in the class constructor.

* **Actual (Other Simulators') Result**: IVerilog, Xcelium (Cadence), Riviera-PRO (Aldec), QuestaSim (Siemens), and VCS (Synopsys) all produce an incorrect output of `16'h0000`.

## 4. The Root Cause

The discrepancy is caused by using **non-synthesizable, dynamic class objects in a combinational hardware block (`always_comb`)**. The IEEE 1800 SystemVerilog standard does not strictly define how this should behave, leading to different, incompatible interpretations by simulator vendors.

The specific reasons for failure vary:

1. **Verilator**: Interprets the code literally, executing the class instantiation and property access as written, and produces the logically correct result.

2. **VCS and Xcelium**: These simulators explicitly **ignore class properties** (like `p.crc`) when inferring the sensitivity list for the `always_comb` block. They issue clear warnings about this behavior:
    * **Xcelium**: `*W,STACPR: Ignore this class property inside the enclosing @*/always_comb/always_latch sensitivity list.`
    * **VCS**: `Warning-[IDTS] Ignoring dynamic type sensitivity... Dynamic types used in always_comb ... will be ignored for the inferred sensitivity list.`
    Because the logic is not sensitive to the class property, the output `crc_o` is never correctly assigned.

3. **IVerilog, Riviera-PRO, QuestaSim**: These simulators fail to execute the class constructor or property access correctly in this context. They produce the default output value of `0`. Adding a `static` lifetime qualifier to the object declaration silences some warnings but does not fix the incorrect output, as the fundamental issue of sensitivity list inference remains.

## 5. Conclusion

This is a classic **simulator compatibility bug** stemming from ambiguous, non-standard SystemVerilog code. While the code is syntactically valid, it relies on behavior that is not consistently implemented across different simulators because it does not map to a standard, synthesizable hardware construct.

Verilator's behavior is the most intuitive from a software perspective, but the other major commercial simulators prioritize synthesizability and adherence to hardware semantics, treating the dynamic construct as an unsupported feature within combinational logic. This case serves as a strong example of the risks of mixing dynamic, object-oriented programming features with synthesizable hardware descriptions.
