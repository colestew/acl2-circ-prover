package cs389r;

/**
 * Created by colestewart on 4/5/15.
 */

public class Gates {
    public static final Gate xor() {
        return new Gate(Gate.GateType.LOGIC, "xor");
    }

    public static final Gate and() {
        return new Gate(Gate.GateType.LOGIC, "and");
    }

    public static final Gate nand() {
        return new Gate(Gate.GateType.LOGIC, "nand");
    }

    public static final Gate nandx() {
        return new Gate(Gate.GateType.LOGIC, "nandx");
    }

    public static final Gate or() {
        return new Gate(Gate.GateType.LOGIC, "or");
    }

    public static final Gate nor() {
        return new Gate(Gate.GateType.LOGIC, "nor");
    }

    public static final Gate norx() {
        return new Gate(Gate.GateType.LOGIC, "norx");
    }

    public static final Gate xnor() {
        return new Gate(Gate.GateType.LOGIC, "xnor");
    }

    public static final Gate input() {
        return new Gate(Gate.GateType.INPUT, "input");
    }

    public static final Gate output() {
        return new Gate(Gate.GateType.OUTPUT, "output");
    }

    public static final Gate inverter() {
        return new Gate(Gate.GateType.LOGIC, "not");
    }

    public static final Gate fullAdder1() {
        return new Gate(Gate.GateType.BLOCK, "one-bit-adder");
    }

    public static final Gate fullAdder4() {
        return new Gate(Gate.GateType.BLOCK, "four-bit-adder");
    }
}
