package cs389r.circuitgraph;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * Created by colestewart on 4/5/15.
 */
public class Gate {

    public enum GateType {
        INPUT,
        LOGIC,
        BLOCK,
        OUTPUT
    }

    public final List<Connection> inputs;
    public final List<Connection> outputs;

    public final GateType type;
    public final String modelId;
    private String name;

    public Gate(GateType type, String modelName) {
        inputs = new ArrayList<>();
        outputs = new ArrayList<>();
        this.type = type;
        this.modelId = modelName;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public void addInput(Connection input) {
        inputs.add(input);
        input.connectOutput(this);
    }

    public void addOutput(Connection output) {
        outputs.add(output);
        output.connectInput(this);
    }

    public String output() {
        return outputs.size() > 0 ? outputs.get(0).id : null;
    }

    public List<Connection> nthOutputs() {
        for (int i = 0; i < outputs.size(); ++i) {
            outputs.get(i).nthId = i;
        }

        return outputs;
    }

    public String input() {
        return inputs.size() > 0 ? inputs.get(0).id : null;
    }

    public String toString() {
        return modelId + "-> outputs: " + outputs + " | inputs: " + inputs;
    }
}
