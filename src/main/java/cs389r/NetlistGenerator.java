package cs389r;

import com.github.mustachejava.DefaultMustacheFactory;
import com.github.mustachejava.Mustache;
import com.github.mustachejava.MustacheFactory;

import java.io.*;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * Created by colestewart on 4/5/15.
 */
public class NetlistGenerator extends ModelGenerator {

    public NetlistGenerator(Circuit circuit, String modelName) {
        super(circuit, modelName + "-netlist");
    }

    @Override
    public void buildModel(OutputStream stream) throws IOException {
        Writer w = new OutputStreamWriter(stream);
        MustacheFactory mf = new DefaultMustacheFactory();
        String templateName = "netlist.lisp";
        InputStream templateStream = getClass().getResourceAsStream('/' + templateName);
        Mustache mustache = mf.compile(new InputStreamReader(templateStream), templateName);

        Map<String, Object> scopes = new HashMap<>();
        scopes.put("modelName", modelName);
        scopes.put("inputs", circuit.getGates(Gate.GateType.INPUT));
        scopes.put("outputs", circuit.getGates(Gate.GateType.OUTPUT));
        scopes.put("logicGates", circuit.getGates(Gate.GateType.LOGIC));
        scopes.put("blocks", circuit.getGates(Gate.GateType.BLOCK));
        mustache.execute(w, scopes);

        w.flush();
    }
}
