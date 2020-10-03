package SAT;

import java.util.HashSet;

public class Clause {
    protected HashSet<Integer> variables;
    protected int index;
    protected boolean satisfied;

    public Clause(int index, String[] var_ids){
        variables = new HashSet<Integer>(var_ids.length*2); // Avoid resizing
        satisfied = false;
        this.index = index;
        for(String s : var_ids){
            variables.add(Integer.valueOf(s));
        }
    }

    public boolean contains(int ID){
        return (variables.contains(ID) || variables.contains(ID*-1));
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(variables.size()*6);
        sb.append("Clause #");
        sb.append(index);
        sb.append(":\n   ");
        for(int i : variables){
            sb.append(i);
            sb.append(", ");
        }
        return sb.toString();
    }
}
