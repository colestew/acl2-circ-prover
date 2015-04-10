package cs389r.acl2models;

import cs389r.circuitgraph.Circuit;

import java.io.IOException;
import java.io.OutputStream;

/**
 * Created by colestewart on 4/5/15.
 */
public abstract class ModelGenerator {
    protected final Circuit circuit;
    protected final String modelName;

    public ModelGenerator(Circuit circuit, String modelName) {
        this.circuit = circuit;
        this.modelName = modelName;
    }

    public abstract void buildModel(ModelWriter writer);
}
