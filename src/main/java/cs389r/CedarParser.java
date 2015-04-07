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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by colestewart on 3/25/15.
 */
public class CedarParser {

    private Document _doc;

    public Circuit parse() {
        List<Gate> gates = new ArrayList<>();
        Map<Integer, Connection> connectionMap = new HashMap<>();
        NodeList list = _doc.getElementsByTagName("gate");

        for (int i = 0; i < list.getLength(); ++i) {
            Node n = list.item(i);
            if (n.getNodeType() == Node.ELEMENT_NODE) {
                Element en = (Element) n;
                Node typeNode = en.getElementsByTagName("type").item(0);
                Gate gate = getGateFromType(typeNode.getTextContent());
                if (gate.type == Gate.GateType.OUTPUT || gate.type == Gate.GateType.INPUT) {
                    gate.setName(getJunctionId(en));
                }

                NodeList inputs = en.getElementsByTagName("input");
                for (int j = 0; j < inputs.getLength(); ++j) {
                    Node input = inputs.item(j);
                    if (input.getNodeType() == Node.ELEMENT_NODE) {
                        CedarID id = new CedarID((Element)input);
                        Connection conn = connectionMap.get(id.id);
                        if (conn == null) {
                            conn = new Connection("w" + id.id);
                            connectionMap.put(id.id, conn);
                        }
                        if (gate.type == Gate.GateType.INPUT) {
                            conn.setId(gate.getName());

                            // For some reason circuit outputs in Cedar are parsed as inputs :|
                            gate.addOutput(conn);
                        } else {
                            gate.addInput(conn);
                        }
                    }
                }

                NodeList outputs = en.getElementsByTagName("output");
                for (int j = 0; j < outputs.getLength(); ++j) {
                    Node output = outputs.item(j);
                    if (output.getNodeType() == Node.ELEMENT_NODE) {
                        CedarID id = new CedarID((Element)output);
                        Connection conn = connectionMap.get(id.id);
                        if (conn == null) {
                            conn = new Connection("w" + id.id);
                            connectionMap.put(id.id, conn);
                        }
//                        if (gate.type == Gate.GateType.INPUT || gate.type == Gate.GateType.OUTPUT) {
//                            conn.setId(gate.getName());
//                        }
                        gate.addOutput(conn);
                    }
                }

                gates.add(gate);
            }
        }

        Circuit result = new Circuit(gates);
        return result;
    }

    private static String getJunctionId(Element e) {
        Node lparam = e.getElementsByTagName("lparam").item(0);
        if (lparam != null) {
            String result = lparam.getTextContent();
            result = result.replace("JUNCTION_ID ", "");
            return result;
        }
        return null;
    }

    private static Gate getGateFromType(String type) {
        String gateType = type.substring(3);
        switch (gateType) {
            // standard gates
            case "AND2" : return Gates.and();
            case "AND3" : return Gates.and();
            case "AND4" : return Gates.and();
            case "OR2" : return Gates.or();
            case "OR3" : return Gates.or();
            case "OR4" : return Gates.or();
            case "XOR2" : return Gates.xor();
            case "XOR3" : return Gates.xor();
            case "XOR4" : return Gates.xor();
            case "XNOR2" : return Gates.xnor();
            case "XNOR3" : return Gates.xnor();
            case "XNOR4" : return Gates.xnor();
            case "NAND2" : return Gates.nand();
            case "NAND3" : return Gates.nand();
            case "NAND4" : return Gates.nand();
            case "NOR2" : return Gates.nor();
            case "NOR3" : return Gates.nor();
            case "NOR4" : return Gates.nor();
            case "NANDX2" : return Gates.nandx();
            case "NANDX3" : return Gates.nandx();
            case "NANDX4" : return Gates.nandx();
            case "NORX2" : return Gates.norx();
            case "NORX3" : return Gates.norx();
            case "NORX4" : return Gates.norx();
            case "AND8" : return Gates.and();
            case "OR8" : return Gates.or();
            case "NAND8" : return Gates.nand();
            case "NOR8" : return Gates.nor();
            case "NANDX8" : return Gates.nand();
            case "NORX8" : return Gates.nor();

            // inverters
            case "SMALL_INVERTER" : return Gates.inverter();

            // adders
            case "FULLADDER_1BIT" : return Gates.fullAdder1();
            case "FULLADDER_4BIT" : return Gates.fullAdder4();

            // input/output
            case "FROM" : return Gates.input();
            case "TO" : return Gates.output();
            default : throw new IllegalArgumentException("Unsupported gate type: " + type);
        }
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
        //int i = 1;
        while ((line = r.readLine()) != null) {
            if (    line.startsWith("<CurrentPage") ||
                    line.startsWith("<page") ||
                    line.startsWith("<Page"))
                continue;
            //System.out.println(i++ + ": " + line);
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
