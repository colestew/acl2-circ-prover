package cs389r.acl2models;

import com.github.mustachejava.DefaultMustacheFactory;
import com.github.mustachejava.Mustache;
import com.github.mustachejava.MustacheFactory;
import cs389r.circuitgraph.Circuit;
import cs389r.circuitgraph.Gate;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by colestewart on 4/5/15.
 */
public class NetlistGenerator extends ModelGenerator {
    public NetlistGenerator(Circuit circuit, String modelName) {
        super(circuit, modelName + "-netlist");
    }

    private Collection<String> getUsedLogicGates() {
        Set<String> usedGates = new HashSet<>();
        for (Gate g : circuit.getGates(Gate.GateType.LOGIC)) {
            String id = g.modelId;
            switch (id) {
                case "and" : continue;
                case "not" : continue;
                case "or" : continue;
            }

            // assume 2 inputs by default
            if (g.inputs.size() > 2) {
                id += g.inputs.size();
            }
            usedGates.add(id);
        }

        usedGates.remove("xor");

        return usedGates;
    }



    @Override
    public void buildModel(ModelWriter writer) {
        String templateName = "netlist/netlist-template.lisp";

        Map<String, Object> scopes = new HashMap<>();
        scopes.put("modelName", modelName);
        scopes.put("inputs", circuit.getGates(Gate.GateType.INPUT));
        scopes.put("outputs", circuit.getGates(Gate.GateType.OUTPUT));
        scopes.put("logicGates", circuit.getGates(Gate.GateType.LOGIC));
        scopes.put("blocks", circuit.getGates(Gate.GateType.BLOCK));

        Collection<String> usedGates = getUsedLogicGates();
        if (!usedGates.isEmpty()) {
            String piece = "";
            piece += ";; ----------------------------------------------------------------------------\n";
            piece += ";;                    Gate functions needed for netlist\n";
            piece += ";; ----------------------------------------------------------------------------\n";
            piece += '\n';
            writer.addModelPiece(piece);
        }

        usedGates.stream()
                .map(s -> "models/netlist/functions/" + s + ".lisp")
                .forEach(path -> {
                    InputStream in = getClass().getClassLoader().getResourceAsStream(path);
                    if (in == null) {
                        System.out.flush();
                        System.err.println("Could not find function file for: " + path);
                    } else {
                        writer.addModelPiece(in);
                    }
                });

        writer.addModelPieceFromTemplate(templateName, scopes);
    }
}
