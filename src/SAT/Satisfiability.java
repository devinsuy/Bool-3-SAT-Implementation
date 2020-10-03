package SAT;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
public class Satisfiability {
    private HashSet<Clause> clauses;
    private int midVar;
    protected static int numVariables;
    protected int numSatisfied;
    HashMap<Integer,Boolean> assignments;
    // EX satisfiedCount.get(2) maps to the count of clauses satisfied by possAssignments.get(2)

    // The indices of all assignments that fufill the max # of clauses

    public Satisfiability(){
        clauses = new HashSet<Clause>();
        numVariables = loadClauses();
        midVar = (numVariables + 1 ) / 2;
        Partition base = new Partition(clauses, 1, numVariables); // Base has mid clauses for layer 1
                initialize(base);
    }

    /**
     * Parses all clauses in "instance.txt" into Clause[] clauses
     * as well as finds the largest variable number in the input file
     * @return The number of variables in the input file
     */
    public int loadClauses(){
        String currentLine;
        String[] lineValues;
        int currentValue, numVariables;
        int index = numVariables = 0;

        try{
            Scanner file_in = new Scanner(new File("instance.txt"));
            while(file_in.hasNextLine()){
                currentLine = file_in.nextLine();
                lineValues = currentLine.split(",");
                for(String s : lineValues){
                    currentValue = Math.abs(Integer.valueOf(s));
                    if(currentValue > numVariables){
                        numVariables = currentValue;
                    }
                }
                clauses.add(new Clause(index,lineValues));
                index++;
            }
        }
        catch(IOException io) { io.printStackTrace(); }

        return numVariables;
    }

    /**
     * Groups clauses that contain variables numbers between
     * startBound and endBound INCLUSIVE
     * @param clauses The set our partitioned clauses will be removed from
     * @param startBound The start of our range
     * @param endBound The end of our range
     * @return The partitioned clauses along with the min and max variable which occur in these clauses
     */
    public Partition partitionClauses(HashSet<Clause> clauses, int startBound, int endBound, boolean leftPartition) {
        HashSet<Clause> clausesToRemove = new HashSet<Clause>();
        HashSet<Clause> partitionedClauses = new HashSet<Clause>();
        HashSet<Integer> vars_in_partition = new HashSet<Integer>();
        for (int i = startBound; i <= endBound; i++) { vars_in_partition.add(i); }

        for (Clause c : clauses) {
            for (int var : c.variables) { // If the clause contains one of our variables we add it
                if (vars_in_partition.contains(Math.abs(var))) {
                    partitionedClauses.add(c);
                    clausesToRemove.add(c);
                    break;
                }
            }
        }
        clauses.removeAll(clausesToRemove);

        return new Partition(partitionedClauses, startBound, endBound, leftPartition);
    }


    /**
     * Takes a bitString and converts it to a HashMap<Integer, Boolean> for the left
     *     or right partition where the variable# maps to it's boolean assignment value
     * @param p The partition we are generating an assignment for
     * @param bitString The string of 0 and 1s
     * @param leftSection Whether or not we are are at the start and moving up +10
     * @return The mapped assignments for the bit string
     */
    public HashMap<Integer, Boolean> createAssignment(Partition p, String bitString, boolean leftSection){
        HashMap<Integer, Boolean> subAssignment = new HashMap<Integer, Boolean>();
        int varNum;

        if(leftSection){
            varNum = p.minVar; // Start at the first variable x up to x + 10
            for(int i = 0; i < bitString.length(); i++){
                subAssignment.put(varNum++, bitString.charAt(i) == '1');
            }
        }
        else{
            varNum = p.maxVar; // Start at the last variable y down to y - 10
            for(int i = 0; i < bitString.length(); i++){
                subAssignment.put(varNum--, bitString.charAt(i) == '1');
            }
        }

        return subAssignment;
    }

    /**
     * Generates all 2048 possible assignments for starting variable x up to x+10
     * Or from ending variable y down to y-10 and maps them in possAssignments
     * @param p The partition we are generating assignments for
     * @param leftSection Whether or not we are are at the start and moving up +10
     * @return A HashMap of all possible assignments for the 11 variables
     */
    public HashMap<Integer,HashMap<Integer,Boolean>> findAllAssignments(Partition p, boolean leftSection){
        String bitString;
        StringBuilder sb;
        int num_leadingZeros;
        int possIndex = 0;
        int numVars = 11; // The end variable and +- 10 within its range
        HashMap<Integer,HashMap<Integer,Boolean>> possAssignments = new HashMap<Integer,HashMap<Integer,Boolean>>();


        // Randomize our assignments so checking is not so linear
        // EX: Assignment 0000 only differs by one bit from the next
        // assignment 0001, so instead choose assignments at random especially if we timeout
        ArrayList<Integer> bitValues = new ArrayList<Integer>(3000);
        for(int i = 0; i < Math.pow(2,numVars); i++){ bitValues.add(i); }
        Collections.shuffle(bitValues);
        int bitPointer = 0;

        while(bitPointer != bitValues.size()){
            bitString = Integer.toBinaryString(bitValues.get(bitPointer++));
            if(bitString.length() < numVars){ // Add leading zeros
                num_leadingZeros = numVars - bitString.length();
                sb = new StringBuilder(numVars);
                for(int j = 0; j < num_leadingZeros; j++) { sb.append('0'); }
                sb.append(bitString);
                bitString = sb.toString();
            }
//            System.out.println("   Created " + i + "/" + 2048);
            possAssignments.put(possIndex++, createAssignment(p,bitString,leftSection));
        }
        return possAssignments;
    }


    /**
     * Takes a bitString and converts it to a HashMap<Integer, Boolean> for the middle partition
     *     Where the variable# maps to it's boolean assignment value
     * @param bitString The string of 0 and 1s
     * @param startVar The variable number the first bit in bitString represents
     * @return The mapped assignments for the bit  string
     */
    public HashMap<Integer, Boolean> createAssignmentM(String bitString, int startVar, int numVariables){
        HashMap<Integer, Boolean> subAssignment = new HashMap<Integer, Boolean>();
        int currentVarNum = startVar - (numVariables/2);

        for(int i = 0; i < bitString.length(); i++){
            subAssignment.put(currentVarNum++, bitString.charAt(i) == '1');
        }
        return subAssignment;
    }

    /**
     * Creates all possible 2^21 assignments for the middle partition
     * and maps them in possAssignments and returns it
     * @param midNum The middle variable number
     * @return possAssignments All the possible assignments for the 21 variables
     */
    public HashMap<Integer,HashMap<Integer,Boolean>> findAllAssignmentsM(Partition p, int midNum){
        String bitString;
        StringBuilder sb;
        int num_leadingZeros;
        int possIndex = 0;
        int numVars = 21; // Constant, includes our seed value and variables +- 10
        if(numVars > p.numVars){
            numVars = p.numVars;
        }
        HashMap<Integer,HashMap<Integer,Boolean>> possAssignments = new HashMap<Integer,HashMap<Integer,Boolean>>();


        // Randomize our assignments so checking is not so linear
        ArrayList<Integer> bitValues = new ArrayList<Integer>(2200000);
        for(int i = 0; i < Math.pow(2,numVars); i++){ bitValues.add(i); }
        Collections.shuffle(bitValues);
        int bitPointer = 0;

        while(bitPointer != bitValues.size()){
            bitString = Integer.toBinaryString(bitValues.get(bitPointer++));
            if(bitString.length() < numVars){ // Add leading zeros
                num_leadingZeros = numVars - bitString.length();
                sb = new StringBuilder(numVars);
                for(int j = 0; j < num_leadingZeros; j++) { sb.append('0'); }
                sb.append(bitString);
                bitString = sb.toString();
            }
//            System.out.println("   Created " + i + "/" + 2097152);
            possAssignments.put(possIndex++, createAssignmentM(bitString,midNum, numVars));
        }
        return possAssignments;
    }

    /**
     * Iterates through all clauses see how many are
     * satisfied by our assignments
     * @return The number of clauses this assignment satisfies
     */
    public int checkSolution(Partition p, HashMap<Integer, Boolean> assignments){
        int numSatisfied = 0;

        for(Clause currentClause : p.clauses){
            for(int varID : currentClause.variables){
                try{
                    if(Math.abs(varID) > p.maxVar || Math.abs(varID) < p.minVar){ continue; }
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


    /**
     * Iterates through each possible assignment and maps
     * the assignment index to the number of clauses that it satisfies
     * Also updates maxSatisfied to the max numClausesSatisfied found
     * @param possAssignments A HashMap of all possible assignments for the 11 variables
     * @return A hashmap of all assignments that fufill the max # of clauses
     */
    public HashMap<Integer, HashMap<Integer,Boolean>> updateSatisfiedCount(Partition p, HashMap<Integer,HashMap<Integer,Boolean>> possAssignments){
        HashMap<Integer, HashMap<Integer,Boolean>> finalizedAssignments = new HashMap<>();
        HashMap<Integer, Integer> satisfiedCount = new HashMap<Integer, Integer>();
        int numClausesSatisfied;
        int finalizedIndex = 0;
        int maxSatisfied = -1;

        // First pass to update all the totals and locate maxSatisfied
        for(int i : possAssignments.keySet()){
            numClausesSatisfied = checkSolution(p, possAssignments.get(i));
            if(numClausesSatisfied > maxSatisfied){
                maxSatisfied = numClausesSatisfied;
            }
            satisfiedCount.put(i,numClausesSatisfied);
        }
        // Second pass to find the populate finalizedAssignments
        for(int i : possAssignments.keySet()){
            if(satisfiedCount.get(i) == maxSatisfied){
                finalizedAssignments.put(finalizedIndex++, possAssignments.get(i));
            }
        }

        return finalizedAssignments;
    }

    public int checkFinalSolution(Partition p, HashSet<Clause> all_p_clauses, HashMap<Integer,Boolean> finalAssignments){
        int numSatisfied = 0;

        for(Clause currentClause : all_p_clauses){
            for(int varID : currentClause.variables){
                try{
                    if(Math.abs(varID) < p.minVar || Math.abs(varID) > p.maxVar) { continue; }
                    if(varID < 0){
                        if(!finalAssignments.get(varID*-1)){
                            numSatisfied++; // If the negated variable was assigned to false
                            break;
                        }
                    }
                    else if(finalAssignments.get(varID)){ // Variable in clause is not negated and is assigned to true
                        numSatisfied++;
                        break;
                    }
                }
                catch(NullPointerException np){}
            }
        }
        return numSatisfied;
    }

    public HashMap<Integer, HashMap<Integer,Boolean>> findFinalSolution(HashMap<Integer, HashMap<Integer, Boolean>> leftCandidates,
                                                                        HashMap<Integer, HashMap<Integer, Boolean>> rightCandidates,
                                                                        HashMap<Integer,HashMap<Integer,Boolean>> possAssignmentsM,
                                                                        Partition p, Partition l, Partition r){
        HashMap<Integer,Boolean> matchingVarsL;
        HashMap<Integer,Boolean> matchingVarsR;
        boolean addAssignment;
        int midCandidateIndex, numSatisfied;
        int numPasses = leftCandidates.size() * rightCandidates.size();
        int passCount, maxSatisfied, collectSatisfied, part_solutions_index;
        part_solutions_index = collectSatisfied = maxSatisfied = passCount = 0;
        HashMap<Integer,Boolean> finalAssignments = new HashMap<Integer,Boolean>();
        HashMap<Integer,Boolean> bestAssignment = new HashMap<Integer,Boolean>();
        HashSet<Clause> all_p_clauses = new HashSet<Clause>();
        HashMap<Integer, Boolean> partialSolution = new HashMap<Integer, Boolean>();
        HashMap<Integer, HashMap<Integer,Boolean>> partialSolutions = new HashMap<Integer, HashMap<Integer,Boolean>>();
        all_p_clauses.addAll(p.clauses);
        all_p_clauses.addAll(l.clauses);
        all_p_clauses.addAll(r.clauses);
        int numClauses = all_p_clauses.size();

        // Used to randomize candidates so assignment check isn't so linear
        ArrayList<Integer> leftKeys = new ArrayList<Integer>(leftCandidates.keySet().size() * 2);
        ArrayList<Integer> rightKeys = new ArrayList<Integer>(rightCandidates.keySet().size()*2);
        for(int i : leftCandidates.keySet()) { leftKeys.add(i); }
        for(int i : rightCandidates.keySet()) { rightKeys.add(i); }
        Collections.shuffle(leftKeys);
        Collections.shuffle(rightKeys);
        int left_key_pointer, right_key_pointer;
        left_key_pointer = 0;

        HashMap<Integer,Boolean> leftAssignment;
        HashMap<Integer,Boolean> rightAssignment;
        HashMap<Integer, HashMap<Integer,Boolean>> midCandidates;
        // Try every combination of overlapping left and right values
        while (left_key_pointer != leftKeys.size()){
            leftAssignment = leftCandidates.get(leftKeys.get(left_key_pointer++));
            matchingVarsL = new HashMap<Integer,Boolean>();
            right_key_pointer = 0;

            if((p.minVar+10) >= (p.midVar-10)){// Used for left overlap check
                if((p.minVar+10) == (p.midVar-10)){
                    matchingVarsL.put((p.minVar+10), leftAssignment.get((p.minVar+10)));
                }
                else{
                    for(int i = (p.midVar-10 < p.minVar) ? p.minVar : (p.midVar-10); i <= (p.minVar+10); i++){
                        matchingVarsL.put(i, leftAssignment.get(i));
                    }
                }
            }

            while (right_key_pointer != rightKeys.size()){
                rightAssignment = rightCandidates.get(rightKeys.get(right_key_pointer++));
                midCandidates = new HashMap<Integer, HashMap<Integer,Boolean>>();
                matchingVarsR = new HashMap<Integer,Boolean>();

                if((p.maxVar-10) <= (p.midVar+10)){ // Right overlap
                    if((p.maxVar-10) == (p.midVar+10)){
                        matchingVarsR.put((p.maxVar-10), rightAssignment.get((p.maxVar-10)));
                    }
                    else{
                        for(int i = (p.midVar+10 > p.maxVar) ? p.maxVar : (p.midVar+10); i >= (p.maxVar-10); i--){
                            matchingVarsR.put(i, rightAssignment.get(i));
                        }
                    }
                }
                midCandidateIndex = 0;

                for(HashMap<Integer,Boolean> midAssignment: possAssignmentsM.values()) {
                    addAssignment = true;
                    for(int i : matchingVarsL.keySet()){
                        // Don't consider an assignment if it's overlapping values don't match
                        if(midAssignment.get(i) != matchingVarsL.get(i)){
                            addAssignment = false;
                            break;
                        }
                    }
                    if(addAssignment){ // Only check the right overlap for this assignment if it passed the left overlap, otherwise discard
                        for(int i : matchingVarsR.keySet()){
                            if(midAssignment.get(i) != matchingVarsR.get(i)){
                                addAssignment = false;
                                break;
                            }
                        }
                    }
                    if(addAssignment){ // By here left and and right overlap passed, add this assignment for consideration
                        midCandidates.put(midCandidateIndex++, midAssignment);
                    }
                }
                finalAssignments = new HashMap<Integer,Boolean>();
                for(int i : leftAssignment.keySet()){ finalAssignments.put(i, leftAssignment.get(i)); }
                for(int i : rightAssignment.keySet()){ finalAssignments.put(i, rightAssignment.get(i)); }


                // Used to randomize candidates so assignment check isn't so linear
                ArrayList<Integer> midKeys = new ArrayList<Integer>(midCandidates.keySet().size()*2);
                for(int i : midCandidates.keySet()) { midKeys.add(i); }
                Collections.shuffle(midKeys);
                int mid_key_pointer = 0;

                HashMap<Integer,Boolean> midCandidate;
                int exit = (int)(midKeys.size() * 0.38);
                int stop = (int)(all_p_clauses.size() * 0.9925);

                while(mid_key_pointer != exit){
                    // If we have found a solution that satisfies 99 percent of clauses, return exactly 3 solutions
                    if(maxSatisfied >= stop && partialSolution.size() > 3){
                        for(int i = 0; i < 13; i++){
                            if(partialSolutions.size() <= 3) { break; }
                            if(partialSolutions.containsKey(i)) {
                                partialSolutions.remove(i);
                            }
                        }
                        System.out.println("Solution found within 99 percent ------------------------------");
                        return partialSolutions;
                    }
                    else if(maxSatisfied >= stop) {
                        System.out.println("Solution found within 99 percent ------------------------------");
                        return partialSolutions;
                    }

                    midCandidate = midCandidates.get(midKeys.get(mid_key_pointer++));
                    for(int i : midCandidate.keySet()){ finalAssignments.put(i,midCandidate.get(i)); }
                    numSatisfied = checkFinalSolution(p, all_p_clauses, finalAssignments);

                    if(numSatisfied >= maxSatisfied){
                        maxSatisfied = numSatisfied;
                        bestAssignment = new HashMap<Integer,Boolean>();
                        for(int i : finalAssignments.keySet()){
                            bestAssignment.put(i,finalAssignments.get(i));
                        }
                        partialSolutions.put(part_solutions_index++, bestAssignment);
                        System.out.println("PARTIAL INDEX IS " + part_solutions_index + " / 10 --------------------------------------------------");
                    }

                    if(part_solutions_index == 13) {
                        for(int i = 0; i < 9; i++){
                            if(partialSolutions.size() <= 3) { break; }
                            if(partialSolutions.containsKey(i)) { partialSolutions.remove(i); }
                        }

                        System.out.println("AFTER REMOVAL, SIZE OF CHILD partial being returned: " + partialSolutions.size());

                        return partialSolutions;
                    }

                }

                System.out.println("Pass #" + (++passCount) + "/" + numPasses + " best: " + maxSatisfied + "/" + numClauses);
                if(part_solutions_index == 13) {
                    for(int i = 0; i < 9; i++){
                        if(partialSolutions.size() <= 3) { break; }
                        if(partialSolutions.containsKey(i)) { partialSolutions.remove(i); }
                    }

                    System.out.println("AFTER REMOVAL, SIZE OF CHILD partial being returned: " + partialSolutions.size());

                    return partialSolutions;
                }
            }
            if(part_solutions_index == 13) {
                for(int i = 0; i < 9; i++){
                    if(partialSolutions.size() <= 3) { break; }
                    if(partialSolutions.containsKey(i)) { partialSolutions.remove(i); }
                }

                System.out.println("AFTER REMOVAL, SIZE OF CHILD partial being returned: " + partialSolutions.size());

                return partialSolutions;
            }
        }

        if(partialSolutions.isEmpty()){
            partialSolution = new HashMap<Integer, Boolean>();
            for(int i : bestAssignment.keySet()){
                partialSolution.put(i, bestAssignment.get(i));
            }
            partialSolutions.put(-1, partialSolution);
            System.out.println("IS EMPTY, WAS PUT --------------------------------");
        }
        return partialSolutions;
    }


    public void solvePartition(Partition p){
        // Only include clauses that have the FIRST 11 variables of this partition
        Partition left = partitionClauses(p.clauses, p.minVar, p.minVar,true);
        HashMap<Integer,HashMap<Integer,Boolean>> possAssignmentsL = findAllAssignments(left, true);
        HashMap<Integer, HashMap<Integer, Boolean>> leftCandidates = updateSatisfiedCount(left, possAssignmentsL);
        System.out.println("AFTER LEFT");
        // Only include clauses that have the LAST 11 variables of this partition
        Partition right = partitionClauses(p.clauses, p.maxVar, p.maxVar, false);
        HashMap<Integer,HashMap<Integer,Boolean>> possAssignmentsR = findAllAssignments(right, false);
        HashMap<Integer, HashMap<Integer, Boolean>> rightCandidates = updateSatisfiedCount(right, possAssignmentsR);
        System.out.println("AFTER RIGHT");
        // Enumerate all possible solutions for the middle section
        HashMap<Integer,HashMap<Integer,Boolean>> possAssignmentsM = findAllAssignmentsM(p, p.midVar);
        System.out.println("AFTER MID");
        p.setSolution(findFinalSolution(leftCandidates, rightCandidates, possAssignmentsM, p, left, right));
    }

    public Partition createLeftPartition(Partition p){
        Partition leftChild = partitionClauses(p.clauses, p.minVar, (p.midVar-11), true);
        leftChild.parent = p;
        return leftChild;
    }

    public Partition createRightPartition(Partition p){
        Partition rightChild = partitionClauses(p.clauses, (p.midVar+11), p.maxVar, false);
        rightChild.parent = p;
        return rightChild;
    }


    public HashMap<Integer, HashMap<Integer,Boolean>> solveParent(Partition parent){
        boolean addAssignment;
        int numSatisfied, maxSatisfied, midCandidateIndex, numClauses;
        HashMap<Integer,Boolean> finalAssignments = new HashMap<Integer,Boolean>();
        HashMap<Integer,Boolean> bestAssignment = new HashMap<Integer,Boolean>();
        HashMap<Integer,Boolean> matchingVarsL = new HashMap<Integer,Boolean>();
        HashMap<Integer,Boolean> matchingVarsR = new HashMap<Integer,Boolean>();
        HashMap<Integer, HashMap<Integer,Boolean>> possAssignmentsM = findAllAssignmentsM(parent, parent.midVar);
        HashMap<Integer, HashMap<Integer,Boolean>> midCandidates;
        HashMap<Integer, Boolean> partialSolution = new HashMap<Integer, Boolean>();
        HashMap<Integer, HashMap<Integer,Boolean>> partialSolutions = new HashMap<Integer, HashMap<Integer,Boolean>>();
        HashSet<Clause> all_p_clauses = new HashSet<Clause>();
        int numPasses = parent.leftChild.solution.size() * parent.rightChild.solution.size();
        int passCount, collectSatisfied, partial_solutions_index;
        passCount = collectSatisfied = maxSatisfied = midCandidateIndex = partial_solutions_index = 0;
        all_p_clauses.addAll(parent.clauses);
        all_p_clauses.addAll(parent.leftChild.clauses);
        all_p_clauses.addAll(parent.rightChild.clauses);
        numClauses = all_p_clauses.size();

        for(HashMap<Integer,Boolean> leftAssignment : parent.leftChild.solution.values()){
            matchingVarsL = new HashMap<Integer,Boolean>();
            // Used for left overlap check
            if((parent.minVar+10) >= (parent.midVar-10)){
                if((parent.minVar+10) == (parent.midVar-10)){
                    matchingVarsL.put((parent.minVar+10), leftAssignment.get((parent.minVar+10)));
                }
                else{
                    for(int i = (parent.midVar-10 < parent.minVar) ? parent.minVar : (parent.midVar-10); i <= (parent.minVar+10); i++){
                        matchingVarsL.put(i, leftAssignment.get(i));
                    }
                }
            }

            for(HashMap<Integer,Boolean> rightAssignment : parent.rightChild.solution.values()){
                midCandidates = new HashMap<Integer,HashMap<Integer,Boolean>>();
                matchingVarsR = new HashMap<Integer,Boolean>();

                // Populate right overlap check
                if((parent.maxVar-10) <= (parent.midVar+10)){
                    if((parent.maxVar-10) == (parent.midVar+10)){
                        matchingVarsR.put((parent.maxVar-10), rightAssignment.get((parent.maxVar-10)));
                    }
                    else{
                        for(int i = (parent.midVar+10 > parent.maxVar) ? parent.maxVar : (parent.midVar+10); i >= (parent.maxVar-10); i--){
                            matchingVarsR.put(i, rightAssignment.get(i));
                        }
                    }
                }
                midCandidateIndex = 0;

                for(HashMap<Integer,Boolean> midAssignment: possAssignmentsM.values()) {
                    addAssignment = true;
                    for(int i : matchingVarsL.keySet()){
                        // Don't consider an assignment if it's overlapping values don't match
                        if(midAssignment.get(i) != matchingVarsL.get(i)){
                            addAssignment = false;
                            break;
                        }
                    }
                    if(addAssignment){ // Only check the right overlap for this assignment if it passed the left overlap, otherwise discard
                        for(int i : matchingVarsR.keySet()){
                            if(midAssignment.get(i) != matchingVarsR.get(i)){
                                addAssignment = false;
                                break;
                            }
                        }
                    }
                    if(addAssignment){ // By here left and and right overlap passed, add this assignment for consideration
                        midCandidates.put(midCandidateIndex++, midAssignment);
                    }
                }

                finalAssignments = new HashMap<Integer, Boolean>();
                // Add in our previously calculated solutions
                for(int i : leftAssignment.keySet()){
                    finalAssignments.put(i, leftAssignment.get(i));
                }
                for(int i : rightAssignment.keySet()){
                    finalAssignments.put(i, rightAssignment.get(i));
                }

                // Used to randomize candidates so assignment check isn't so linear
                ArrayList<Integer> midKeys = new ArrayList<Integer>(midCandidates.keySet().size()*2);
                for(int i : midCandidates.keySet()) { midKeys.add(i); }
                Collections.shuffle(midKeys);
                int mid_key_pointer = 0;
                int stop = (int)(all_p_clauses.size() * 0.992);

                HashMap<Integer,Boolean> midCandidate;
                int exit = (int)(midKeys.size() * 0.38);
                while(mid_key_pointer != exit){
                    // If we have found a solution that satisfies 99 percent of clauses, return exactly 3 solutions
                    if(maxSatisfied >= stop && partialSolution.size() > 3){
                        for(int i = 0; i < 13; i++){
                            if(partialSolutions.size() <= 3) { break; }
                            if(partialSolutions.containsKey(i)) {
                                partialSolutions.remove(i);
                            }
                        }
                        System.out.println("Solution found within 99 percent ------------------------------");
                        return partialSolutions;
                    }
                    else if(maxSatisfied >= stop) {
                        System.out.println("Solution found within 99 percent ------------------------------");
                        return partialSolutions;
                    }
                    midCandidate = midCandidates.get(midKeys.get(mid_key_pointer++));
                    for(int i : midCandidate.keySet()){ finalAssignments.put(i,midCandidate.get(i)); }
                    numSatisfied = checkFinalSolution(parent, all_p_clauses, finalAssignments);

                    if(numSatisfied >= maxSatisfied){
                        maxSatisfied = numSatisfied;
                        bestAssignment = new HashMap<Integer,Boolean>();
                        for(int i : finalAssignments.keySet()){
                            bestAssignment.put(i,finalAssignments.get(i));
                        }
                        partialSolutions.put(partial_solutions_index++, bestAssignment);
                        System.out.println("PARTIAL INDEX IS " + partial_solutions_index + " / 10 --------------------------------------------------");
                    }

                    if(partial_solutions_index == 13) { // Remove The first 8 solutions because they are the worst
                        for(int i = 0; i < 9; i++){
                            if(partialSolutions.size() <= 3) { break; }
                            if(partialSolutions.containsKey(i)) { partialSolutions.remove(i); }
                        }

                        System.out.println("AFTER REMOVAL, SIZE OF CHILD partial being returned: " + partialSolutions.size());

                        return partialSolutions;
                    } // We have collected 10 partial solutions
                    //FIXME Solution can be improved by increasing passCount at the cost of time
                }

                System.out.println("Pass #" + (++passCount) + "/" + numPasses + " best: " + maxSatisfied + "/" + numClauses);
                if(partial_solutions_index == 13) { // Remove The first 8 solutions because they are the worst
                    for(int i = 0; i < 9; i++){
                        if(partialSolutions.size() <= 3) { break; }
                        if(partialSolutions.containsKey(i)) { partialSolutions.remove(i); }
                    }

                    return partialSolutions;
                } // We have collected 10 partial solutions
            }
            if(partial_solutions_index == 13) {
                for(int i = 0; i < 9; i++){
                    if(partialSolutions.size() <= 3) { break; }
                    if(partialSolutions.containsKey(i)) { partialSolutions.remove(i); }
                }

                System.out.println("AFTER REMOVAL, SIZE OF CHILD partial being returned: " + partialSolutions.size());

                return partialSolutions;
            }
        }
        if(partialSolutions.isEmpty()){
            partialSolution = new HashMap<Integer, Boolean>();
            for(int i : bestAssignment.keySet()){
                partialSolution.put(i, bestAssignment.get(i));
            }
            partialSolutions.put(-1, partialSolution);
            System.out.println("IS EMPTY, WAS PUT --------------------------------");
        }



        return partialSolutions;
    }



    public void initialize(Partition p){
        p.leftChild = createLeftPartition(p);
        p.rightChild = createRightPartition(p);

        if(p.leftChild.numVars <= 31){ // Base case L
            System.out.println("LEFT got to base case with numVariables: " + p.leftChild.numVars);
            System.out.println();
            solvePartition(p.leftChild);

        }
        else{ initialize(p.leftChild); }

        if(p.rightChild.numVars <= 31){ // Base case R
            System.out.println("RIGHT got to base case with numVariables: " + p.rightChild.numVars);
            System.out.println();
            solvePartition(p.rightChild);
            // Right child is always solved AFTER left child
        }
        else{ initialize(p.rightChild); }

        if((p.leftChild.solution != null) && (p.rightChild.solution != null)){
            System.out.println("PARENT:");
            p.setSolution(solveParent(p));
            System.out.println();
        }

        // We are at the root now, all solutions solved
        if(p.parent == null){
            int maxSatisfied, currentSatisfied, maxIndex;
            maxIndex = maxSatisfied = 0;

            System.out.println("Solution of size: " + p.solution.size());
            for(int i : p.solution.keySet()){
                currentSatisfied = checkRootSolution(p,i);
                if(currentSatisfied > maxSatisfied){
                    maxSatisfied = currentSatisfied;
                    maxIndex = i;
                }
            }
            this.numSatisfied = maxSatisfied;
            System.out.println("Solution satisfies " + this.numSatisfied + "/" + clauses.size() + " clauses");
            writeSolution(p, maxIndex);
        }
    }

    public int checkRootSolution(Partition root, int solutionIndex){
        int numSatisfied = 0;
        clauses = new HashSet<Clause>();
        loadClauses();

        for(Clause currentClause : clauses){
            for(int varID : currentClause.variables){
                if(varID < 0){
                    if(!root.solution.get(solutionIndex).get(varID*-1)){
                        numSatisfied++; // If the negated variable was assigned to false
                        break;
                    }
                }
                else if(root.solution.get(solutionIndex).get(varID)){ // Variable in clause is not negated and is assigned to true
                    numSatisfied++;
                    break;
                }
            }
        }
        return numSatisfied;
    }

    public void writeSolution(Partition root, int solutionIndex){
        String currentBit;
        try{
            FileWriter fw = new FileWriter(new File("assignments.txt"));
            HashMap<Integer, Boolean> solution = root.solution.get(solutionIndex);

            for(int i = 1; i <= numVariables; i++){
                currentBit = (solution.get(i)) ? "1" : "0";
                fw.write(currentBit);
            }
            fw.close();
        }
        catch(IOException io) { io.printStackTrace(); }
        System.out.println("\nSolution written to \"assignments.txt\"");
    }

    public void writeSolution(){
        String currentBit;
        try{
            FileWriter fw = new FileWriter(new File("assignments.txt"));

            for(int i = 1; i <= numVariables; i++){
                currentBit = (assignments.get(i)) ? "1" : "0";
                fw.write(currentBit);
            }
            fw.close();
        }
        catch(IOException io) { io.printStackTrace(); }
        System.out.println("\nSolution written to \"assignments.txt\"");
    }

}
