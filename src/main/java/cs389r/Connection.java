package cs389r;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by colestewart on 4/5/15.
 */
public class Connection {
    public String id;
    List<Gate> inputs;
    List<Gate> outputs;

    public int nthId;

    public Connection(String id) {
        this.id = id;
        inputs = new ArrayList<>();
        outputs = new ArrayList<>();
    }

    public void connectInput(Gate input) {
        inputs.add(input);
    }

    public void connectOutput(Gate output) {
        outputs.add(output);
    }

    public void setId(String id) {
        this.id = id;
    }

    public String toString() {
        return id;
    }
}
