package cs389r;

import cs389r.acl2models.ModelWriter;
import cs389r.acl2models.NetlistGenerator;
import cs389r.circuitgraph.Circuit;
import cs389r.parsers.CedarParser;

import javax.xml.parsers.ParserConfigurationException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;

public class Main {


    public static void main(String[] args) throws ParserConfigurationException, IOException {
        String cedarFile = args[0];
        String modelName = args[0].substring(cedarFile.lastIndexOf('/')+1, cedarFile.indexOf('.'));
        OutputStream stream = System.out;
        if (args.length > 1) {
            stream = new FileOutputStream(args[1]);
        }

        CedarParser parser = new CedarParser(cedarFile);
        Circuit circuit = parser.parse();
        NetlistGenerator generator = new NetlistGenerator(circuit, modelName);

        ModelWriter writer = new ModelWriter(stream);
        generator.buildModel(writer);

        writer.writePieces();
    }
}
