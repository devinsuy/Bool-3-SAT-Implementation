package SAT;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

public class Main {

    static HashMap<Integer,Boolean> loadSolution(){
        int varIndex = 1;
        int numValue;
        HashMap<Integer,Boolean> solution = new HashMap<Integer,Boolean>();
        try{
            Scanner solution_in = new Scanner(new File("assignments.txt"));
            solution_in.useDelimiter("");
            while(solution_in.hasNext()){
                numValue = Integer.valueOf(solution_in.next());
                solution.put(varIndex++, (numValue > 0));
            }
        }
        catch(IOException io) { io.printStackTrace(); }

        return solution;
    }

    static int checkSolution(HashMap<Integer, Boolean> assignments, HashSet<Clause> clauses){
        int numSatisfied = 0;

        for(Clause currentClause : clauses){
            for(int varID : currentClause.variables){
                try{
                    if(varID < 0){
                        if(!assignments.get(varID*-1)){
                            numSatisfied++; // If the negated variable was assigned to false
                            break;
                        }
                    }
                    else if(assignments.get(varID)){ // Variable in clause is not negated and is assigned to true
                        numSatisfied++;
                        break;
                    }
                }
                catch(NullPointerException np) {}
            }
        }

        return numSatisfied;
    }

    static HashSet<Clause> loadClauses(){
        String currentLine;
        String[] lineValues;
        int index = 0;

        HashSet<Clause> clauses = new HashSet<Clause>();

        try{
            Scanner file_in = new Scanner(new File("instance.txt"));
            while(file_in.hasNextLine()){
                currentLine = file_in.nextLine();
                lineValues = currentLine.split(",");
                clauses.add(new Clause(index,lineValues));
                index++;
            }
        }
        catch(IOException io) { io.printStackTrace(); }

        return clauses;
    }

    static void writeSolution(HashMap<Integer,Boolean> solution, int numVariables){
        String currentBit;
        try{
            FileWriter fw = new FileWriter(new File("assignments.txt"));

            for(int i = 1; i <= numVariables; i++){
                currentBit = (solution.get(i)) ? "1" : "0";
                fw.write(currentBit);
            }
            fw.close();
        }
        catch(IOException io) { io.printStackTrace(); }
        System.out.println("\nSolution written to \"assignments.txt\"");
    }

    public static void main(String[] args) {
        Satisfiability s = new Satisfiability();

        // Optimize solution
        HashMap<Integer,Boolean> solution = loadSolution(); // Load the solution we calculated from satisfiability
        HashSet<Clause> clauses = loadClauses();

        ArrayList<Integer> keys = new ArrayList<Integer>(solution.keySet().size() * 2);
        for(int i = 1; i <= solution.size(); i++) { keys.add(i); }
        Collections.shuffle(keys);

        int keyPointer, currentKey, numBefore, numAfter;
        keyPointer = currentKey = numAfter =  numBefore = 0;
        boolean currentAssignment;

        System.out.println("Number clauses satisfied BEFORE optimization: " + checkSolution(solution,clauses) + "/" + clauses.size());

        while(keyPointer != keys.size()){
            currentKey = keys.get(keyPointer++);
            currentAssignment = solution.get(currentKey);

            numBefore = checkSolution(solution, clauses);
            solution.put(currentKey, !currentAssignment);
            numAfter = checkSolution(solution, clauses);

            System.out.println(keyPointer-1 + ": NUM BEFORE: " + numBefore + "     NUM AFTER: " + numAfter);

            if(numAfter == clauses.size()) { break; }

            if(numAfter < numBefore){ // Undo the assignment change
                solution.put(currentKey, currentAssignment);
            }
        }
        System.out.println("Number clauses satisfied AFTER optimization: " + checkSolution(solution,clauses) + "/" + clauses.size());
        writeSolution(solution,solution.size());
    }
}
