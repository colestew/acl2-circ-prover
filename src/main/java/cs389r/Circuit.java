package cs389r;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by colestewart on 3/25/15.
 */
public class Circuit {

    private List<Gate> gates;

    public Circuit(Collection<Gate> gates) {
        this.gates = orderGatesByConnections(gates);
    }

    public static List<Gate> orderGatesByConnections(Collection<Gate> gates) {
        Map<Gate, Integer> priorities = new HashMap<>();
        List<Gate> inputs = gates.stream()
                .filter(g -> g.type == Gate.GateType.INPUT)
                .collect(Collectors.toList());

        for (Gate g : inputs) {
            orderGatesHelper(g, 0, priorities);
        }

        // now reverse the map
        Map<Integer, List<Gate>> prioritiesInv = new TreeMap<>();
        for (Gate g : priorities.keySet()) {
            List<Gate> gatesAtPriority = prioritiesInv.get(priorities.get(g));
            if (gatesAtPriority == null) {
                gatesAtPriority = new ArrayList<>();
            }
            gatesAtPriority.add(g);
            prioritiesInv.put(priorities.get(g), gatesAtPriority);
        }

        // now create the result
        List<Gate> result = new ArrayList<>(gates.size());
        for (Integer priority : prioritiesInv.keySet()) {
            result.addAll(prioritiesInv.get(priority));
        }

        return result;
    }

    private static void orderGatesHelper(Gate g, int i, Map<Gate, Integer> priorities) {
        if (!priorities.containsKey(g) ||
                (priorities.containsKey(g) && priorities.get(g) < i)) {
            priorities.put(g, i);
        }
        for (Connection c : g.outputs) {
            for (Gate go : c.outputs) {
                orderGatesHelper(go, i + 1, priorities);
            }
        }
    }

    public List<Gate> getGates(Gate.GateType... types) {
        List<Gate.GateType> typeList = Arrays.asList(types);
        return gates.stream().filter(g -> typeList.contains(g.type)).collect(Collectors.toList());
    }
}
