package cs389r;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

/**
 * Created by colestewart on 3/25/15.
 */
public class CedarParser {

    private Document _doc;

    public CircuitData parse() {
        NodeList list = _doc.getElementsByTagName("gate");

        for (int i = 0; i < list.getLength(); ++i) {
            Node n = list.item(i);
            if (n.getNodeType() == Node.ELEMENT_NODE) {
                Element en = (Element) n;
                Node typeNode = en.getElementsByTagName("type").item(0);
                System.out.println("type: " + typeNode.getTextContent());

                Node idNode = en.getElementsByTagName("ID").item(0);
                System.out.println("id: " + idNode.getTextContent());

                NodeList inputs = en.getElementsByTagName("input");
                for (int j = 0; j < inputs.getLength(); ++j) {
                    Node input = inputs.item(j);
                    if (input.getNodeType() == Node.ELEMENT_NODE) {
                        CedarID id = new CedarID((Element)input);
                        System.out.println("input: " + id.name + ": " + id.id);
                    }
                }

                NodeList outputs = en.getElementsByTagName("output");
                for (int j = 0; j < outputs.getLength(); ++j) {
                    Node output = outputs.item(j);
                    if (output.getNodeType() == Node.ELEMENT_NODE) {
                        System.out.println("output: " + parseID((Element)output));
                    }
                }
            }
            System.out.println();
        }
        return null;
    }

    private static String parseID(Element n) {
        NodeList idList = n.getElementsByTagName("ID");
        if (idList.getLength() > 0)
            return idList.item(0).getTextContent();
        return null;
    }

    private static class CedarID {
        private String name;
        private int id;

        public CedarID(Element inputOrOutput) {
            name = parseID(inputOrOutput);
            String content = inputOrOutput.getTextContent().trim();
            int contentInd = 0;
            //System.out.println(name);
            //System.out.println(content);
            if (content.startsWith(name)) {
                contentInd = name.length();
            }
            id = Integer.parseInt(content.substring(contentInd));
        }
    }

    private static InputStream fixCedarXml(String filename) throws IOException {
        StringBuilder result = new StringBuilder();
        BufferedReader r = new BufferedReader(new FileReader(filename));
        String line;
        int i = 1;
        while ((line = r.readLine()) != null) {
            if (    line.startsWith("<CurrentPage") ||
                    line.startsWith("<page") ||
                    line.startsWith("<Page"))
                continue;

            line = line.replace("</page 0>", "");
            result.append(line + "\n");
        }

        result.append("</circuit>");

        return new ByteArrayInputStream( result.toString().getBytes(StandardCharsets.UTF_8));
    }

    public CedarParser(String filename) {
        try {
            DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
            DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
            InputStream fixedXmlStream = fixCedarXml(filename);
            _doc = dBuilder.parse(fixedXmlStream);

        } catch (ParserConfigurationException e) {
            e.printStackTrace();
        } catch (SAXException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
