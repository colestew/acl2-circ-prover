package cs389r.circuitgraph;

/**
 * Created by colestewart on 4/8/15.
 */
public enum DefinedGates {
    XOR(Gate.GateType.LOGIC),
    AND(Gate.GateType.LOGIC),
    NAND(Gate.GateType.LOGIC),
    NANDX(Gate.GateType.LOGIC),
    OR(Gate.GateType.LOGIC),
    NOR(Gate.GateType.LOGIC),
    NORX(Gate.GateType.LOGIC),
    XNOR(Gate.GateType.LOGIC),
    INVERTER(Gate.GateType.LOGIC),
    INPUT(Gate.GateType.INPUT),
    OUTPUT(Gate.GateType.OUTPUT);

    public final Gate.GateType category;

    private DefinedGates(Gate.GateType type) {
        this.category = type;
    }

    public static final Gate fullAdder1() {
        return new Gate(Gate.GateType.BLOCK, "one-bit-adder");
    }

    public static final Gate fullAdder4() {
        return new Gate(Gate.GateType.BLOCK, "four-bit-adder");
    }
}
