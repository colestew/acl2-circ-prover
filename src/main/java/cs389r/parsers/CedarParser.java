package cs389r.parsers;

import cs389r.circuitgraph.Circuit;
import cs389r.circuitgraph.Connection;
import cs389r.circuitgraph.Gate;
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
            case "AND2" : return CedarGates.and();
            case "AND3" : return CedarGates.and();
            case "AND4" : return CedarGates.and();
            case "OR2" : return CedarGates.or();
            case "OR3" : return CedarGates.or();
            case "OR4" : return CedarGates.or();
            case "XOR2" : return CedarGates.xor();
            case "XOR3" : return CedarGates.xor();
            case "XOR4" : return CedarGates.xor();
            case "XNOR2" : return CedarGates.xnor();
            case "XNOR3" : return CedarGates.xnor();
            case "XNOR4" : return CedarGates.xnor();
            case "NAND2" : return CedarGates.nand();
            case "NAND3" : return CedarGates.nand();
            case "NAND4" : return CedarGates.nand();
            case "NOR2" : return CedarGates.nor();
            case "NOR3" : return CedarGates.nor();
            case "NOR4" : return CedarGates.nor();
            case "NANDX2" : return CedarGates.nandx();
            case "NANDX3" : return CedarGates.nandx();
            case "NANDX4" : return CedarGates.nandx();
            case "NORX2" : return CedarGates.norx();
            case "NORX3" : return CedarGates.norx();
            case "NORX4" : return CedarGates.norx();
            case "AND8" : return CedarGates.and();
            case "OR8" : return CedarGates.or();
            case "NAND8" : return CedarGates.nand();
            case "NOR8" : return CedarGates.nor();
            case "NANDX8" : return CedarGates.nand();
            case "NORX8" : return CedarGates.nor();

            // inverters
            case "SMALL_INVERTER" : return CedarGates.inverter();

            // adders
            case "FULLADDER_1BIT" : return CedarGates.fullAdder1();
            case "FULLADDER_4BIT" : return CedarGates.fullAdder4();

            // input/output
            case "FROM" : return CedarGates.input();
            case "TO" : return CedarGates.output();
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
