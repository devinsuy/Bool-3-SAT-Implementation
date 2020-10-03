package SAT;

import java.util.HashMap;
import java.util.HashSet;

public class Partition {

    protected int minVar;
    protected int maxVar;
    protected int midVar;
    protected int numVars;
    protected boolean leftPartition;
    protected HashSet<Clause> clauses;
    protected HashMap<Integer,HashMap<Integer, Boolean>> solution;
    protected Partition leftChild;
    protected Partition rightChild;
    protected Partition parent;

    public Partition(HashSet<Clause> c, int min, int max, boolean leftPartition){
        parent = null;
        solution = null;
        clauses = c;
        this.leftPartition = leftPartition;
        if(leftPartition){
            minVar = min;
            maxVar = max + 10;
        }
        else{
            minVar = min - 10;
            maxVar = max;
        }
        midVar = (maxVar + minVar) / 2;
        numVars = (maxVar - minVar) + 1;
    }

    // For base partition
    public Partition(HashSet<Clause> c, int min, int max){
        clauses = c;
        minVar = min;
        maxVar = max;
        midVar = (maxVar + minVar) / 2;
        numVars = (maxVar - minVar) + 1;
    }
    public void setSolution(HashMap<Integer,HashMap<Integer, Boolean>> solution){
        this.solution = solution;
        System.out.println("Solution set for variables #" + minVar + " through #" + maxVar);
    }
}
