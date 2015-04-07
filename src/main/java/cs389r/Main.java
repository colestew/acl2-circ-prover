package cs389r;

import org.w3c.dom.Document;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.File;
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
        generator.buildModel(stream);
    }
}
