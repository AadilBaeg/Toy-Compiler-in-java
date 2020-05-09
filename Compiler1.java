package compiler1;

import java.util.ArrayList;
import java.util.Map;
import java.io.*;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Scanner;
import java.util.Stack;





public class Compiler1 {
    private ArrayList<String> tokens;
    private Map lineMap;
    String fileDirectory = "C:\\Users\\hp\\Documents\\NetBeansProjects\\Compiler1\\src\\compiler1\\test.c";

    CodeGenerator cg;
    public Compiler1() {
        InputReader ir = new InputReader(fileDirectory);
        tokens = ir.getTokens();
        System.out.println("Tokenization");
        for(int i=0;i<tokens.size();i++)
        {
          System.out.print("<"+tokens.get(i)+"> ");
        }
        System.out.println();
        SyntaxStateMachine ssm = new SyntaxStateMachine(StatementTransitionTable.stt, ExpressionTransitionTable.ett, tokens, ir.getTokensOfEachLine());
        ssm.syntaxHandler();
        if (ssm.isSyntaxOK()){
            SemanticStateMachine semanticSM = new SemanticStateMachine(tokens);
            semanticSM.semanticHandler();
            if (semanticSM.isSemanticOk())
                cg = new CodeGenerator(tokens);
        }
    }

    public static void main(String[] args) {
        new Compiler1();
    }
}


class ExpressionTransitionTable {

    public static final int[][] ett = new int[][]{
            {0,-12,3,2,10,-12,-12,1,-12},
            {-13,1,-13,-13,-13,0,-13,-13,-13},
            {-14,2,-14,-14,-14,-14,5,-14,4},
            {-16,3,-16,-16,-16,0,5,-16,4},
            {4,-15,2,2,-15,-15,-15,-15,-15},
            {5,-17,7,6,0,-17,-17,8,-17},
            {-18,6,-18,-18,-18,0,-18,-18,9},
            {-18,7,-18,-18,-18,0,-18,-18,9},
            {-19,8,-19,-19,-19,0,-19,-19,-19},
            {9,-15,6,6,-15,-15,-15,-15,-15},
            {-20,10,-20,-20,-20,-20,11,-20,-20},
            {-21,11,0,-21,0,-21,-21,-21,-21}
    };
}



class CodeGenerator {

    private int[] R;
    private String[] memory;
    private StatementTransitionTable stt;
    private SyntaxStateMachine ssm;
    private Map variableInMemoryIndex;
    private boolean[] isValidRegisterIndex;
    private int lastUsedMemoryWord;
    private Stack<Integer> processingRegisters;
    private int Rd;
    private int Rs;
    private int ls;
    private Stack<Integer> operandStack;
    private Stack<String> operatorStack;
    private int numOfExpressions = 0;
    private int lastValue;
    private Map<String, Integer> variableMemoryPosition;
    private String lastVariable = "";
    private Stack<Integer> parenthesisStack;
    private boolean inIf = false;
    private ArrayList<String> inIfCodes;
    private int lastIfValue = 0;
    private boolean isWhile = false;
    private Stack<Integer> openedBrace;

    public CodeGenerator(ArrayList<String> tokens) {
        ssm = new SyntaxStateMachine(StatementTransitionTable.stt, ExpressionTransitionTable.ett, tokens, new int[1]);
        R = new int[4];
        isValidRegisterIndex = new boolean[4];
        memory = new String[1024];
        inIfCodes = new ArrayList<>();
        variableInMemoryIndex = new HashMap();
        processingRegisters = new Stack<>();
        operandStack = new Stack<>();
        operatorStack = new Stack<>();
        parenthesisStack = new Stack<>();
        variableMemoryPosition = new HashMap<>();
        openedBrace = new Stack<>();
        Arrays.fill(R, 0);
        Arrays.fill(memory, "");
        Arrays.fill(isValidRegisterIndex, true);
        
        codeGeneratorStateMachine(tokens);
        
    }

    private int scs = 0;
    private void codeGeneratorStateMachine(ArrayList<String> tokens){
        int ecs = 0;

        for (String token : tokens){
            int key;
            if (token.equals(";")) scs = 0;
            if (token.equals("("))
                parenthesisStack.push(1);
            else if (token.equals(")"))
                parenthesisStack.pop();
            if (scs == 14 || scs == 15 || scs == 7){
                if (scs == 14){
                    isWhile = false;
                } else if (scs == 15){
                    isWhile = true;
                }
                key = ssm.expressionKeywordValueGenerator(token);
                if (!token.equals("{"))
                    ecs = ExpressionTransitionTable.ett[ecs][key];
                if (parenthesisStack.isEmpty()){
                    calculate(token);
                    openedBrace.push(1);
                    inIf = true;
                    scs = 0;
                    continue;
                }
                expressionCodeGeneratorHandler(ecs, token, key);
            } else {
                key = ssm.statementKeywordValueGenerator(token);
                ecs = 0;
                if (token.equals("}") ){
                    if (openedBrace.size() > 0){
                        openedBrace.pop();
                        loopAndIfJumpCheck();
                    }
                    scs = 0;
                    continue;
                } else if (token.equals("{"))
                    continue;
                scs = stt.stt[scs][key];
                if (scs == -8 && ls == 10 && key == 12) scs = 4;
                statementCodeGeneratorHandler(scs, token, key);
            }
            ls = scs;
        }
    }

    private void expressionCodeGeneratorHandler(int cs, String token, int key){
        switch (cs){
            case 8:
            case 1:
                if (token.equals(")")){
                    if (!operatorStack.contains('('))
                        break;
                    while (!operatorStack.peek().equals("("))
                        operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                    operatorStack.pop();
                } else if (token.equals("true")){
                    String bits  = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
                    int registerIndex = uselessRegisterIndexFinder();
//                    System.out.println("token: " + token);
//                    System.out.println("R_" + registerIndex);
                    processingRegisters.push(registerIndex);
                    mil(registerIndex, bits);
                    mih(registerIndex, bits);
                    operandStack.push(1);
                }
                else if (token.equals("false")){
                    String bits  = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(0)).replace(" ","0");
                    int registerIndex = uselessRegisterIndexFinder();
//                    System.out.println("token: " + token);
//                    System.out.println("R_" + registerIndex);
                    processingRegisters.push(registerIndex);
                    mil(registerIndex, bits);
                    mih(registerIndex, bits);
                    operandStack.push(0);
                }
                break;

            case 6:
            case 2:
                if (token.equals(")")){
                    while (!operatorStack.peek().equals("("))
                        operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                    operatorStack.pop();
                }
                else{
                    if (key == 3){
                        lastValue = Integer.parseInt(token);
                        operandStack.push(lastValue);
                    }
                    else {
                        int memoryAddressForLoad = uselessRegisterIndexFinder();
                        String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(variableMemoryPosition.get(token))).replace(" ","0");
                        processingRegisters.push(memoryAddressForLoad);
                        mil(memoryAddressForLoad, bits);
                        mih(memoryAddressForLoad, bits);
                        int loadedRegister = uselessRegisterIndexFinder();
                        lda(loadedRegister, memoryAddressForLoad);
                        operandStack.push(memoryAddressForLoad - 1000);
                    }
                }
                break;

            case 7:
            case 3:
                if (token.equals(")")){
                    while (operatorStack.peek().equals("("))
                        operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                    operatorStack.pop();
                }
                else{
                    int memoryAddressForLoad = uselessRegisterIndexFinder();
                    String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(variableMemoryPosition.get(token))).replace(" ","0");
                    processingRegisters.push(memoryAddressForLoad);
                    mil(memoryAddressForLoad, bits);
                    mih(memoryAddressForLoad, bits);
                    int loadedRegister = uselessRegisterIndexFinder();
                    lda(loadedRegister, memoryAddressForLoad);
                    operandStack.push(memoryAddressForLoad - 1000);
                }
                break;

            case 5:
            case 4:
                if (token.equals("(")) {
                    operatorStack.push(token);
                } else if (token.equals("||") || token.equals("&&") || token.equals("!") || token.equals("<") || token.equals(">") || token.equals("==") || token.equals("!=") ||
                        token.equals(">=") || token.equals("<=") || token.equals("+") || token.equals("-") ||
                        token.equals("*") || token.equals("/")) {
                    if (operandStack.size() > 1) {
                        while (!operatorStack.empty() && hasPrecedence(token, operatorStack.peek()))
                            operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                    }
                    operatorStack.push(token);
                }
                break;

            case 9:
                if (token.equals("(")) {
                    operatorStack.push(token);
                } else if (token.equals("||") || token.equals("&&") || token.equals("!") || token.equals("<") || token.equals("<") || token.equals("==") || token.equals("!=") ||
                        token.equals(">=") || token.equals("<=") || token.equals("+") || token.equals("-") ||
                        token.equals("*") || token.equals("/")) {
                    while (!operatorStack.empty() && hasPrecedence(token, operatorStack.peek()))
                        operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                    operatorStack.push(token);
                }
                break;

            default:
                break;
        }
    }

    private void statementCodeGeneratorHandler(int cs, String token, int key){
        switch (cs){
            case 0 : {
                expressionCheckCodeToPrint(token, cs, key);
                break;
            }

            case 2 : {
                lastVariable = token;
                memoryFiller(token);
                expressionCheckCodeToPrint(token,cs, key);
                break;
            }

            case 4 : {
                expressionCheckCodeToPrint(token,cs, key);
                break;
            }

            case 6 : {
                lastVariable = token;
                memoryFiller(token);
                expressionCheckCodeToPrint(token,cs, key);
                break;
            }

            case 9 : {
                lastVariable = token;
                expressionCheckCodeToPrint(token,cs, key);
                memoryFiller(token);
                break;
            }

            case 10: {
                expressionCheckCodeToPrint(token,cs, key);
                break;
            }

            case 11: {
                expressionCheckCodeToPrint(token,cs, key);
                break;
            }

            case 12: {
                expressionCheckCodeToPrint(token,cs, key);
                memoryFiller(token);
                lastVariable = token;
            }

            case 13: {
                expressionCheckCodeToPrint(token,cs, key);
                break;
            }

            default:
                break;
        }
    }

    private void memoryFiller(String data){
        int lastEmptyMemoryWordIndex = 1024;
        for (int i = 1023; i > 0; i--){
            if (memory[i].equals("")){
                lastEmptyMemoryWordIndex = i;
                break;
            }
        }

        lastUsedMemoryWord = lastEmptyMemoryWordIndex;
//        System.out.println(data + " --> " + lastEmptyMemoryWordIndex);
        variableMemoryPosition.put(data, lastEmptyMemoryWordIndex);
        memory[lastEmptyMemoryWordIndex] = data;
    }

    private int uselessRegisterIndexFinder(){
        int index = 0;
        for (int i = 0; i < 63; i++){
            index = i;
            if (!processingRegisters.contains(index)) break;
        }
        if (index > 4){
            awp(1);
        }
        return index;
    }

    private int registerIndexInStack(int R){
        for (int i = 0;i < processingRegisters.size(); i++){
            if (processingRegisters.get(i) == R)
                return i;
        }
        return -1;
    }

    private void expressionCheckCodeToPrint(String token, int cs, int key){

        if (cs == 0){
            if (ls == 11 || ls == 7 || ls == 4){
                if (ls == 11) calculate(token);
                String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(lastUsedMemoryWord)).replace(" ","0");
                int registerIndex = uselessRegisterIndexFinder();
                Rd = registerIndex;
                variableRegister = registerIndex;
//                System.out.println("token: " + lastVariable);
//                System.out.println("R_" + registerIndex);
                processingRegisters.push(registerIndex);
                mil(registerIndex, bits);
                mih(registerIndex, bits);
                sta();
                processingRegisters.removeAllElements();
            }
            numOfExpressions = 0;
        } else if (cs == 10) {
            if (token.equals("(")) {
                operatorStack.push(token);
            } else if (token.equals("||") || token.equals("&&") || token.equals("!") || token.equals("<") || token.equals("<") || token.equals("==") || token.equals("!=") ||
                    token.equals(">=") || token.equals("<=") || token.equals("+") || token.equals("-") ||
                    token.equals("*") || token.equals("/")) {
                while (!operatorStack.empty() && hasPrecedence(token, operatorStack.peek()))
                    operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                operatorStack.push(token);
            }
            if (!token.equals("="))
                numOfExpressions++;
        } else if (cs == 11){
            if (token.equals(")")){
                while (operatorStack.peek().equals("("))
                    operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
                operatorStack.pop();
            }
            else{
                if (token.equals("true")){
                    lastValue = 1;
                    operandStack.push(lastValue);
                }
                else if (token.equals("false")){
                    lastValue = 0;
                    operandStack.push(lastValue);
                }
                else if (key == 17){
                    lastValue = Integer.parseInt(token);
                    operandStack.push(lastValue);
                }
                else {
                    int memoryAddressForLoad = uselessRegisterIndexFinder();
                    String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(variableMemoryPosition.get(token))).replace(" ","0");
                    processingRegisters.push(memoryAddressForLoad);
                    mil(memoryAddressForLoad, bits);
                    mih(memoryAddressForLoad, bits);
                    int loadedRegister = uselessRegisterIndexFinder();
                    lda(loadedRegister, memoryAddressForLoad);
                    operandStack.push(memoryAddressForLoad - 1000);
                }
            }
            numOfExpressions++;
        } else if (cs == 4) {
            char[] chars = token.toCharArray();
            String bits  = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString((int)chars[1])).replace(" ","0");
            int registerIndex = uselessRegisterIndexFinder();
            Rs = registerIndex;
//            System.out.println("token: " + token);
//            System.out.println("R_" + registerIndex);
            lastValue = (int)token.charAt(1);
            processingRegisters.push(registerIndex);
            mil(registerIndex, bits);
            mih(registerIndex, bits);
        } else if (token.equals("true") || token.equals("false")){
            int number;
            if (token.equals("true")) number = 1;
            else number = 0;
            String bits  = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(number)).replace(" ","0");
            int registerIndex = uselessRegisterIndexFinder();
            Rs = registerIndex;
//            System.out.println("token: " + token);
//            System.out.println("R_" + registerIndex);
            processingRegisters.push(registerIndex);
            mil(registerIndex, bits);
            mih(registerIndex, bits);
        } else if (cs == 13) {
            String bits  = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
            int registerIndex = uselessRegisterIndexFinder();
//            System.out.println("token: " + token);
//            System.out.println("R_" + registerIndex);
            processingRegisters.push(registerIndex);
            mil(registerIndex, bits);
            mih(registerIndex, bits);

            int memoryAddressForLoad = uselessRegisterIndexFinder();
            bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(variableMemoryPosition.get(lastVariable))).replace(" ","0");
            processingRegisters.push(memoryAddressForLoad);
            mil(memoryAddressForLoad, bits);
            mih(memoryAddressForLoad, bits);
            lda(memoryAddressForLoad, memoryAddressForLoad);

            if (token.equals("++"))
                add(memoryAddressForLoad, registerIndex);
            else if (token.equals("--"))
                sub(memoryAddressForLoad, registerIndex);

        }
    }

    private void loopAndIfJumpCheck(){
        int register = uselessRegisterIndexFinder();
        String bits = "0000000000000000";
        processingRegisters.push(register);
        mil(register, bits);
        mih(register, bits);
        cmp(processingRegisters.pop(), lastIfValue);
        inIf = false;
        if (isWhile) brz(inIfCodes.size() + 5);
        else brz(inIfCodes.size() + 1);

        for (String s : inIfCodes){
            System.out.println(s);
        }
        if (isWhile){
            brz(255);
            brz(255);
            brz(255);
            brz(255 - inIfCodes.size());
        }
        inIfCodes.clear();
    }

    private int variableRegister = 0;

    public int calculate(String token) {
        if (numOfExpressions == 1){
            String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(lastValue)).replace(" ","0");
            int registerIndex = uselessRegisterIndexFinder();
            Rs = registerIndex;
//            System.out.println("token: " + lastValue);
//            System.out.println("R_" + registerIndex);
            processingRegisters.push(registerIndex);
            mil(registerIndex, bits);
            mih(registerIndex, bits);
        }
        while (!operatorStack.empty()){
            if (operatorStack.size() == 1){
                lastIfValue = operandStack.peek();
            }
            operandStack.push(applyOp(operatorStack.pop(), operandStack.pop(), operandStack.pop()));
        }
        if (scs != 0 && operandStack.size() == 0){
            if (token.equals("true")){
                String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
                int registerIndex = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex);
                mil(registerIndex, bits);
                mih(registerIndex, bits);
                operandStack.add(1);
            } else if (token.equals("false")){
                String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(0)).replace(" ","0");
                int registerIndex = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex);
                mil(registerIndex, bits);
                mih(registerIndex, bits);
                operandStack.add(0);
            }
        }
        return operandStack.pop();
    }


    public static boolean hasPrecedence(String op1, String op2) {
        int o1 = precedenceNumber(op1);
        int o2 = precedenceNumber(op2);

        if(o1 <= o2 || o1 == -1)
            return true;
        else
            return false;
    }

    private static int precedenceNumber(String s){
        switch (s){
            case "|" : return 0;
            case "&" : return 1;
            case "!" : return 2;
            case ">" : return 2;
            case "<" : return 2;
            case "<=" : return 2;
            case ">=" : return 2;
            case "==" : return 2;
            case "!=" : return 2;
            case "-" : return 4;
            case "+" : return 4;
            case "*" : return 5;
            case "/" : return 5;
            case "(" : return -1;
            case ")" : return 6;
        }
        return -1;
    }

    public int applyOp(String op, int b, int a) {
        int [] registers = new int[2];
        switch (op) {

            case "+":
                registers = addToRegisters(a,b);
                add(registers[0], registers[1]);
                return registers[0]-1000;

            case "-":
                registers = addToRegisters(a,b);
                sub(registers[0], registers[1]);
                return registers[0]-1000;

            case "*":
                registers = addToRegisters(a,b);
                mul(registers[0], registers[1]);
                return registers[0]-1000;


            case "||":
                registers = addToRegisters(a,b);
                orr(registers[0], registers[1]);
                return registers[0]-1000;

            case "&&":
                registers = addToRegisters(a,b);
                and(registers[0], registers[1]);
                return registers[0]-1000;

            case "<=":
            case ">":
                registers = addToRegisters(a,b);
                cmp(registers[1], registers[0]);
                brc(4);

                String bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
                int registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                jpr(3);

                bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(0)).replace(" ","0");
                registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                return registers[0]-1000;

            case ">=":
            case "<":
                registers = addToRegisters(a,b);
                cmp(registers[0], registers[1]);
                brc(4);

                bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
                registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                jpr(3);
                bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(0)).replace(" ","0");
                registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                return registers[0]-1000;


            case "!=":
                registers = addToRegisters(a,b);
                cmp(registers[0], registers[1]);
                brz(4);

                bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
                registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                jpr(3);
                bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(0)).replace(" ","0");
                registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                return registers[0]-1000;


            case "==":
                registers = addToRegisters(a,b);
                cmp(registers[0], registers[1]);

                brz(6);

                bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(1)).replace(" ","0");
                registerIndex1 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex1);
                mil(registerIndex1, bits);
                mih(registerIndex1, bits);

                int registerIndex2 = uselessRegisterIndexFinder();
                processingRegisters.push(registerIndex2);
                mil(registerIndex2, bits);
                mih(registerIndex2, bits);

                cmp(registerIndex1, registerIndex2);
                brz(5);

                jpr(3);
                return registers[0]-1000;

            case "|":
                registers = addToRegisters(a,b);
                orr(registers[0], registers[1]);
                return registers[0]-1000;

            case "&":
                registers = addToRegisters(a,b);
                and(registers[0], registers[1]);
                return registers[0]-1000;

        }
        return 0;
    }

    private int[] addToRegisters(int a, int b){
        int [] registers = new int[2];
        String bits;
        int registerIndex1 = 0;
        int registerIndex2 = 0;
        if (a < -995 && a > -1001) {
            a = a +1000;
            registerIndex1 = a;
//            System.out.println("Rd to ... : " + registerIndex1);
        } else {
            bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(a)).replace(" ","0");
            registerIndex1 = uselessRegisterIndexFinder();
//            System.out.println("token: " + a);
//            System.out.println("R_" + registerIndex1);
            processingRegisters.push(registerIndex1);
            mil(registerIndex1, bits);
            mih(registerIndex1, bits);
        }

        if (b < -995 && b > -1001){
            b = b + 1000;
            registerIndex2 = b;
//            System.out.println("Rs to sub : " + registerIndex2);
        } else {
            bits = String.format("%"+Integer.toString(16)+"s",Integer.toBinaryString(b)).replace(" ","0");
            registerIndex2 = uselessRegisterIndexFinder();
//            System.out.println("token: " + b);
//            System.out.println("R_" + registerIndex2);
            processingRegisters.push(registerIndex2);
            mil(registerIndex2, bits);
            mih(registerIndex2, bits);
        }
        registers[0] = registerIndex1;
        registers[1] = registerIndex2;
        return registers;
    }

    private void add(int Rdd, int Rss){
        if (Rdd > Rss){
            int temp = Rdd;
            Rdd = Rss;
            Rss = temp;
        }
        Rs = Rdd;
        if (inIf){
            inIfCodes.add("add : " + "1011" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
            processingRegisters.remove(registerIndexInStack(Rss));
        } else {
            System.out.println("add : " + "1011" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
//            System.out.println(processingRegisters);
            processingRegisters.remove(registerIndexInStack(Rss));
//            System.out.println(processingRegisters);
        }
    }

    private void sub(int Rdd, int Rss){
        System.out.print("sub : ");
        if (Rdd > Rss){
            int temp = Rdd;
            Rdd = Rss;
            Rss = temp;
        }
        Rs = Rdd;
        if (inIf){
            inIfCodes.add("1100" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
        } else {
            System.out.println("1100" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
        }

        if (registerIndexInStack(Rss) > 0){
            processingRegisters.remove(registerIndexInStack(Rss));
        }
    }

    private void mul(int Rdd, int Rss){
        if (Rdd > Rss){
            int temp = Rdd;
            Rdd = Rss;
            Rss = temp;
        }
        Rs = Rdd;
        if (registerIndexInStack(Rss) > 0){
            processingRegisters.remove(registerIndexInStack(Rss));
        }
        if (inIf){
            inIfCodes.add("mul : " + "1101" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
        } else {
            System.out.println("mul : " + "1101" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
//            System.out.println(processingRegisters);
        }

    }

    private void orr(int Rdd, int Rss){
        if (Rdd > Rss){
            int temp = Rdd;
            Rdd = Rss;
            Rss = temp;
        }
        Rs = Rdd;
        if (inIf){
            inIfCodes.add("orr : " + "0111" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
            processingRegisters.remove(registerIndexInStack(Rss));
        } else{
            System.out.println("orr : " + "0111" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
            processingRegisters.remove(registerIndexInStack(Rss));
//            System.out.println(processingRegisters);
        }
    }

    private void and(int Rdd, int Rss){
        if (Rdd > Rss){
            int temp = Rdd;
            Rdd = Rss;
            Rss = temp;
        }
        Rs = Rdd;
        if (inIf){
            inIfCodes.add("and : " + "0110" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
            processingRegisters.remove(registerIndexInStack(Rss));
        } else{
            System.out.println("and : " + "0110" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000");
            processingRegisters.remove(registerIndexInStack(Rss));
//            System.out.println(processingRegisters);
        }
    }

    private void mil(int registerIndex, String bits){
        if(inIf){
            String s = "mil : " + "1111" + binaryRegisterIndex(registerIndex) + "00";
            for (int i = 8; i < 16; i++)
                s += bits.toCharArray()[i];
            inIfCodes.add(s);
        } else {
            System.out.print("mil : " + "1111" + binaryRegisterIndex(registerIndex) + "00");
            for (int i = 8; i < 16; i++)
                System.out.print(bits.toCharArray()[i]);
            System.out.println();
        }
    }

    private void mih(int registerIndex, String bits){
        if (inIf){
            String s = "mih : " + "1111" + binaryRegisterIndex(registerIndex) + "01";
            for (int i = 0; i < 8; i++)
                s += bits.toCharArray()[i];
            inIfCodes.add(s);
        }else {
            System.out.print("mih : " + "1111" + binaryRegisterIndex(registerIndex) + "01");
            for (int i = 0; i < 8; i++)
                System.out.print(bits.toCharArray()[i]);
            System.out.println();
//            System.out.println(processingRegisters);
        }
    }

    private void sta(){
        if (Rd > Rs && Rd != variableRegister){
            int temp = Rd;
            Rd = Rs;
            Rs = temp;
        }
        //        processingRegisters.remove(registerIndexInStack(Rd));
        if (inIf){
            inIfCodes.add("sta : " + "0011" + binaryRegisterIndex(Rd) + binaryRegisterIndex(Rs) + "00000000");
            inIfCodes.add("mvr : " + "0001" + binaryRegisterIndex(Rs) + binaryRegisterIndex(Rd) + "00000000");
        } else {
//            System.out.println(processingRegisters);
            System.out.print("sta : " + "0011" + binaryRegisterIndex(Rd) + binaryRegisterIndex(Rs) + "00000000\n");
            System.out.print("mvr : " + "0001" + binaryRegisterIndex(Rs) + binaryRegisterIndex(Rd) + "00000000\n");
        }
    }

    private void lda(int Rdd, int Rss){
        if (Rdd > Rss && Rdd != variableRegister){
            int temp = Rdd;
            Rdd = Rss;
            Rss = temp;
        }
        if (inIf){
            inIfCodes.add("lda : " + "0010" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000\n");
            inIfCodes.add("mvr : " + "0001" + binaryRegisterIndex(Rss) + binaryRegisterIndex(Rdd) + "00000000\n");
        } else {
            System.out.print("lda : " + "0010" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000\n");
            System.out.print("mvr : " + "0001" + binaryRegisterIndex(Rss) + binaryRegisterIndex(Rdd) + "00000000\n");

        }
    }

    private void cmp(int Rdd, int Rss){
        if (inIf){
            inIfCodes.add("cmp : " + "1110" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000\n");
        } else {
            System.out.print("cmp : " + "1110" + binaryRegisterIndex(Rdd) + binaryRegisterIndex(Rss) + "00000000\n");
        }

    }

    private void brz(int number){
        if (inIf){
            inIfCodes.add("brz : " + "0000" + "10" + "00" +
                    String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(number)).replace(" ","0"));
        } else {
            System.out.print("brz : " + "0000" + "10" + "00" +
                    String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(number)).replace(" ","0") + "\n");

        }
    }

    private void brc(int number){
        if (inIf){
            inIfCodes.add("brc : " + "0000" + "10" + "01" +
                    String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(number)).replace(" ","0"));
        } else {
            System.out.print("brc : " + "0000" + "10" + "01" +
                    String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(number)).replace(" ","0") + "\n");

        }
    }

    private void jpr(int number){
        if (inIf){
            inIfCodes.add("jpr : " + "0000" + "01" + "11" +
                    String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(number)).replace(" ","0"));

        } else {
            System.out.print("jpr : " + "0000" + "01" + "11" +
                    String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(number)).replace(" ","0") + "\n");
        }
    }

    private void awp(int num){
        if (inIf){
            inIfCodes.add("awp : " + "00001010" + String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(num)).replace(" ","0"));
        } else {
            System.out.println("awp : " + "00001010" + String.format("%"+Integer.toString(8)+"s",Integer.toBinaryString(num)).replace(" ","0"));
        }
    }

    private String binaryRegisterIndex(int number){
        switch (number){
            case 0 :
                return "00";
            case 1 :
                return "01";
            case 2:
                return "10";
            case 3:
                return "11";
        }
        return "00";
    }

}

class InputReader {

    private Map lineMap;
    private String fileName;
    private File file;
    private ArrayList<String> tokens;
    private ArrayList<Character> invalidTokens;
    private int[] tokensOfEachLine = new int[100];
    private boolean isComment = false;
    private boolean isComment2 = false;

    public InputReader(String fileName) {
        this.fileName = fileName;
        for (int i = 0; i < tokensOfEachLine.length; i++)
            tokensOfEachLine[i] = 0;
        lineMap = new HashMap();
        file = new File(fileName);
        tokens = new ArrayList<>();
//        invalidTokens = invalidTokensGenerator();
        tokens = tokensGenerator(file);
    }

    private ArrayList<String> tokensGenerator(File file){
        ArrayList<String> tempTokens = new ArrayList<>();
        if (!file.exists()){
            System.out.println("File doesn't exist");
            return null;
        }
        if (!(file.isFile() && file.canRead())){
            System.out.println("File cannot be read");
            return null;
        }
        try {
            FileInputStream fis = new FileInputStream(file);
            String inputString = "";
            while (fis.available() > 0)
                inputString += (char)fis.read();

            mapFiller(inputString);

            int line = 0;
            int commentLine = 0;
            int wordCounterOfEachLine = 0;
            for (String retval : inputString.split("\\s+")){
                if (tokensOfEachLine[line] == wordCounterOfEachLine){
                    wordCounterOfEachLine = 0;
                    line++;
                }
                if (!retval.isEmpty()){
                    if (retval.equals("//")){
                        isComment = true;
                        commentLine = line;
                    } else if (retval.equals("/*")){
                        isComment2 = true;
                    }
                    if (isComment){
                        if (line > commentLine)
                            isComment = false;
                    }
                    if (!isComment && !isComment2)
                        tempTokens.add(retval);
                    if (isComment2){
                        if (retval.equals("*/"))
                            isComment2 = false;
                    }
                }
                wordCounterOfEachLine++;

            }

        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return tempTokens;
    }

    private void mapFiller(String string){
        int lineNumber = 0;
        Scanner sc = new Scanner(string);
        int counter = 0;
        while (sc.hasNext()){
            int num = sc.nextLine().split("\\s+").length;
            if (num != 1){
                tokensOfEachLine[counter] = num;
            }
            counter++;
        }

        for (String token : string.split("\\n+")){
            lineNumber++;
            for (String subToken : token.split("\\s+")){
                lineMap.put(subToken, lineNumber);
            }
        }
    }

    public ArrayList<String> getTokens() {
        return tokens;
    }

    public int[] getTokensOfEachLine() {
        return tokensOfEachLine;
    }
}


class SemanticStateMachine {

    private ArrayList<String> tokens;
    private Map isVariableDefined;
    private Map variableValue;
    private Map variableType;
    private boolean semanticIsOK = true;
    private boolean isExpression = false;

    public SemanticStateMachine(ArrayList<String> tokens) {
        this.tokens = tokens;
        isVariableDefined = new HashMap();
        variableValue = new HashMap();
        variableType = new HashMap();
    }

    private boolean afterEq = false;
    public void semanticHandler(){
        int cs = 0;
        int ls = 0;
        int key = 0;
        int tokenCounter = 0;
        String lastVariable = "";
        String afterEqString = "";
        boolean isNewLine = false;
        String lastToken = "";
        boolean isNegativeValue = false;
        String lastType = "";
        String lastDefinedVariable = "";
        String beforEqVariable = "";
        int parenthesis = 0;
        for (String token : tokens){
            tokenCounter++;
            if (isKeyword(token)){
                if (token.equals("if") || token.equals("while")){
                    isExpression = true;
                }
                continue;
            }
            if (isExpression){
                if (token.equals("(")) parenthesis++;
                else if (token.equals(")")) parenthesis --;
                if (parenthesis == 0){
                    isExpression = false;
                }
            }
            key = semanticKeyValueGenerator(token);
            if (key == 5 || token.equals("}"))
                continue;
            if (key == 0)
                lastType = token;
            if (key == 2)
                if (token.toCharArray()[0] == '-')
                    isNegativeValue = true;
            if (key == 1 && variableValue.containsKey(token))
                if (((String)variableType.get(token)).equals("int"))
                    if (Integer.parseInt((String) variableValue.get(token)) < 0)
                        isNegativeValue = true;

            if (semanticKeyValueGenerator(token) == 7) lastVariable = lastToken;
            ls = cs;
            if (key < 0){
                if (token.equals("{")){
                    cs = 0;
                    continue;
                }
                System.out.println(token + " : invalid token!");
                return;
            }

            cs = SemanticTransitionTable.semanticTT[cs][key];
            if (key == 7) beforEqVariable = lastToken;
            if (afterEq) {
                if (((String) variableType.get(lastDefinedVariable)).equals("int")){
                    if (key == 8) {
                        afterEq = false;
//                        System.out.println(afterEqString);
                        variableValue.put(lastVariable, Integer.toString(mathExpressionEvaluator(afterEqString)));
                        isNegativeValue = false;
                        afterEqString = "";
                    } else {
                        String value;
                        if (semanticKeyValueGenerator(token) == 1) {
                            value = variableValue.get(token) + " ";
                            if (isNegativeValue) {
                                value = ((String) variableValue.get(token)).toCharArray()[0] + " ";
                                for (int i = 1; i < ((String) variableValue.get(token)).toCharArray().length; i++)
                                    value += ((String) variableValue.get(token)).toCharArray()[i];
                            }
                            afterEqString += value;
                        }
                        else{
                            value = token + " ";
                            if (isNegativeValue){
                                value = token.toCharArray()[0] + " ";
                                for (int i = 1; i < token.toCharArray().length; i++)
                                    value+= token.toCharArray()[i];
                            }
                            afterEqString += value;
                        }
                    }
                }
            }
            if (key == 7) afterEq = true;
            switch (cs){
                case -1:
                    if (isExpression){
                        cs = 0;
                        continue;
                    }
                    System.out.print(token + " : ");
                    System.out.println("Semantic undefined error :(");
                    return;
                case 2:
                    if (ls == 1){
                        if (isVariableDefined.containsKey(token)){
                            errorHandler(-5, token);
                            return;
                        }else {
                            lastDefinedVariable = token;
                            variableType.put(token, lastType);
                            isVariableDefined.put(token, true);
                        }
                    } else {
                        if (!isVariableDefined.containsKey(token)){
                            errorHandler(-4,token);
                            return;
                        }
                    }
                    break;
                case 4:
                    variableValue.put(lastVariable, token);
                    break;
                case 5:
                    if (!variableValue.containsKey(token)){
                        errorHandler(-2, token);
                        return;
                    }
                    if (!variableType.get(beforEqVariable).equals(variableType.get(token))){
//                        System.out.println(beforEqVariable + " : "++ " " + token + " : "+ variableType.get(token));
                        errorHandler(-6, token);
                    }
                    break;
                case 8:
                    if (lastVariable.equals(token)){
                        if (Integer.parseInt((String)variableValue.get(token)) == 0){
                            errorHandler(-3, token);
                            return;
                        }
                    } else if (token.length() == 1 && (int)token.toCharArray()[0] == 48){
                        errorHandler(-3, token);
                        return;
                    }
                    break;

                default:
                    break;
            }
            lastToken = token;
        }

        if (tokenCounter == tokens.size() && semanticIsOK){
            semanticIsOK = true;
            System.out.println("Semantic is OK too ^_^");
        }
    }


    private void errorHandler(int error, String seenString){
        semanticIsOK = false;
        switch (error){
            case -2 :
                System.out.println(seenString + " : variable value is not defined");
                break;
            case -3:
                System.out.println("division by zero error");
                break;
            case -4:
                System.out.println(seenString + " : undeclared variable");
                break;
            case -5:
                System.out.println(seenString + " : multiple deceleration of variable");
                break;

            case -6:
                System.out.println("type problem.");
                break;
        }
    }


    private int semanticKeyValueGenerator(String token){
        if (token.equals("int") || token.equals("char") || token.equals("bool")) return 0;
        else if (token.equals("true")||token.equals("false")) return 3;
        else if (token.equals("(") || token.equals(")")) return 9;
        else if (token.matches("\\w+")){
            if ((int)token.toCharArray()[0] > 64 && (int)token.toCharArray()[0] < 91 ||
                    (int)token.toCharArray()[0] > 96 && (int)token.toCharArray()[0] < 123 )return 1;
            else return 2;
        }
        else if (token.toCharArray()[0] == '\'') return 4;
        else if (token.equals("+") ||token.equals("-") ||token.equals("*") || token.equals("++") || token.equals("--") ||
                token.equals("%") || token.equals("||") || token.equals("&&") || token.equals("==") || token.equals("!=")
                || token.equals("<") || token.equals(">") || token.equals("<=")
                || token.equals(">=")) return 5;
        else if (token.equals("/")) return 6;
        else if (token.equals("=")) return 7;
        else if (token.equals(";")) return 8;
        
        else return -1;
    }

    private boolean isKeyword(String token){
        return token.equals("if") || token.equals("while") || token.equals("else");
    }



    public int mathExpressionEvaluator(String expression) {
        char[] tokens = expression.toCharArray();
        Stack<Integer> values = new Stack<Integer>();
        Stack<Character> ops = new Stack<Character>();

        for (int i = 0; i < tokens.length; i++) {
            if (tokens[i] == ' ')
                continue;
            if (tokens[i] >= '0' && tokens[i] <= '9') {
                StringBuffer sbuf = new StringBuffer();
                while (i < tokens.length && tokens[i] >= '0' && tokens[i] <= '9')
                    sbuf.append(tokens[i++]);
                values.push(Integer.parseInt(sbuf.toString()));
            }

            else if (tokens[i] == '(')
                ops.push(tokens[i]);
            else if (tokens[i] == ')') {
                while (ops.peek() != '(')
                    values.push(applyOp(ops.pop(), values.pop(), values.pop()));
                ops.pop();
            }
            else if (tokens[i] == '+' || tokens[i] == '-' ||
                    tokens[i] == '*' || tokens[i] == '/') {
                while (!ops.empty() && hasPrecedence(tokens[i], ops.peek()))
                    values.push(applyOp(ops.pop(), values.pop(), values.pop()));
                ops.push(tokens[i]);
            }
        }
        while (!ops.empty())
            values.push(applyOp(ops.pop(), values.pop(), values.pop()));
        return values.pop();
    }

    public static boolean hasPrecedence(char op1, char op2) {
        if (op2 == '(' || op2 == ')')
            return false;
        if ((op1 == '*' || op1 == '/') && (op2 == '+' || op2 == '-'))
            return false;
        else
            return true;
    }

    public int applyOp(char op, int b, int a) {
        switch (op) {
            case '+':
                return a + b;
            case '-':
                return a - b;
            case '*':
                return a * b;
            case '/':
                if (b == 0){
                    errorHandler(-3," ");
                    return Integer.MAX_VALUE;
                }
                return a / b;
        }
        return 0;
    }

    public boolean isSemanticOk(){
        return semanticIsOK;
    }
}

class  StatementTransitionTable {

    public final static int[][] stt = new int[][] {
        // Int	Char	Bool	While	If	var	(	)	=	Op	;	,	‘ ‘	+=	Eif	Ewh	Inc	Num
            {8,	1,	5,	15,	14,	12,	-1,	-1,	-1,	-1,	0,	-1,	-1,	-1,	-1,	-1,	-1,	-1,	16,	-1},//0
            {-2,	-2,	-2,	-2,	-2,	2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2}, //1
            {-3,	-3,	-3,	-3,	-3,	-3,	-3,	-3,	3,	-3,	0,	1,	-3,	-3,	-3,	-3,	-3,	-3,	-3,	-3}, //2
            {-4,	-4,	-4,	-4,	-4,	4,	3,	-4,	-4,	-4,	-4,	-4,	4,	-4,	-4,	-4,	-4,	-4,	-4,	-4}, //3
            {-5,	-5,	-5,	-5,	-5,	-5,	-5,	4,	-5,	-5,	0,	-5,	-5,	-5,	-5,	-5,	-5,	-5,	-5,	-5}, //4
            {-2,	-2,	-2,	-2,	-2,	6,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2}, //5
            {-3,	-3,	-3,	-3,	-3,	-3,	-3,	-3,	7,	-3,	0,	5,	-3,	-3,	-3,	-3,	-3,	-3,	-3,	-3}, //6
            {-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	0,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7}, //7
            {-2,	-2,	-2,	-2,	-2,	9,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2,	-2}, //8
            {-3,	-3,	-3,	-3,	-3,	-3,	-3,	-3,	10,	-3,	0,	8,	-3,	-3,	-3,	-3,	-3,	-3,	-3,	-3}, //9
            {-8,	-8,	-8,	-8,	-8,	11,	10,	-8,	-8,	-8,	-8,	-8,	-8,	-8,	-8,	-8,	-8,	11,	-8,	-8}, //10
            {-9,	-9,	-9,	-9,	-9,	-9,	-9,	11,	-9,	10,	0,	-9,	-9,	-9,	-9,	-9,	-9,	-9,	-9,	-9}, //11
            {-10,	-10,	-10,	-10,	-10,	-10,	-10,	-10,	10,	-10,	-10,	-10,	-10,	10,	-10,	-10,	13,	-10,	-10,	-10}, //12
            {-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	0,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7,	-7}, //13
            {-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	0,	-11,	-11,	-11,	-11,	-11}, //14
            {-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	-11,	0,	-11,	-11,	-11,	-11},
            {16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	16,	0}//15
    };
}

class SemanticTransitionTable {

    public final static int[][] semanticTT = new int[][]{
            {1,	2,	-1,	-1,	-1,	-1,	-1,	-1,	-1, 0},
            {-1,	2,	-1,	-1,	-1,	-1,	-1,	-1,	-1, 1},
            {-1,	-1,	-1,	-1,	-1,	-1,	-1,	3,	0, 2},
            {-1,	5,	4,	4,	4,	-1,	-1,	-1,	-1, 3},
            {-1,	-1,	-1,	-1,	-1,	6,	7,	-1,	0, 4},
            {-1,	-1,	-1,	-1,	-1,	6,	7,	-1,	0, 5},
            {-1,	5,	4,	-1,	-1,	-1,	-1,	-1,	-1, 6},
            {-1,	8,	8,	-1,	-1,	-1,	-1,	-1,	0, 7},
            {-1,	-1,	-1,	-1,	-1,	9,	-1,	-1,	0, 8},
            {-1,	-1,	8,	-1,	-1,	-1,	-1,	-1,	-1, 9},
    };
}


class SyntaxStateMachine {

    private int[][] statementTransitionTable;
    private int[][] expressionTransitionTable;
    private ArrayList<String> tokens;
    private boolean isOpenBraceOrSemicolon = false;
    private boolean afterEq = false;
    private int scs = 0;
    private boolean oneTime = false;
    private int parenthesis = 0;
    private boolean syntaxIsOK = false;
    private int[] tokensOfEachLine;
    private boolean isBoolExpression = false;
    private int lineCounter =  0;
    private int ls = 0;

    public SyntaxStateMachine(int[][] statementTransitionTable, int[][] expressionTransitionTable,
                              ArrayList<String> tokens, int[] tokensOfEachLine) {
        this.statementTransitionTable = statementTransitionTable;
        this.expressionTransitionTable = expressionTransitionTable;
        this.tokens = tokens;
        this.tokensOfEachLine = tokensOfEachLine;
    }
    public void syntaxHandler(){
        int ecs = 0;
        int tokenCounter = 0;
        for (String string : tokens){
            while (tokenCounter == tokensOfEachLine[lineCounter]){
                lineCounter ++;
            }
            tokenCounter++;
            if (scs == -100 || ecs == -100 ) return;
            else if (scs == 14 || scs == 15 || scs == 7){
                isBoolExpression = true;
                ecs = expressionHandler(string, ecs);
                if (ecs == -100) return;
            } else {
                scs = statementHandler(string, scs);
                if (scs == -100) return;
            }
            if (tokenCounter == tokens.size()){
                if (!(string.equals(";") || string.equals("}"))){
                    System.out.println("; or } expected");
                    return;
                }
                syntaxIsOK = true;
                System.out.println("Syntax is OK :)");
            }
            ls = scs;
        }
    }

    private int statementHandler(String string, int cs){
        int key = statementKeywordValueGenerator(string);
        if (key < 0){
            System.out.println("In line" + lineCounter + ", " + string + " : invalid token.\n");
            return -100;
        } else if (key == 50){
            isOpenBraceOrSemicolon = true;
            return 0;
        } else if (key == 51 && isOpenBraceOrSemicolon){
            return 0;
        } else if (key == 51){
            System.out.println("In line "+ lineCounter + ", " + string + " seen! " + "; expected.\n");
            return -100;
        }
        if (cs >= 0 && cs != 15 && cs != 14){
            if (afterEq){
//                if (key == 17) cs = 10;
//                if (key == 12) cs = 4;
                cs = statementTransitionTable[cs][key];
                afterEq = false;
            } else{
                cs = statementTransitionTable[cs][key];
            }
        }
        if (cs == -8 && ls == 10){
            if (key == 12)
                cs = 4;
        }
        if (key == 8){
            afterEq = true;
        }
        if (cs < 0){
            errorHandler(cs, string);
            return -100;
        }
        isOpenBraceOrSemicolon = key == 10;
        return cs;
    }

    private boolean isParenthesis = false;
    public int expressionHandler(String string, int cs){
        int key = expressionKeywordValueGenerator(string);
        if (string.equals(";") && isBoolExpression){
            isBoolExpression = false;
            scs = 0;
            return 0;
        }
        if (key < 0){
            System.out.println(string + " : invalid token.\n");
            return -100;
        } else if (key == 0){
            isParenthesis = true;
            parenthesis++;
        } else if (key == 1){
            parenthesis--;
        }
        if (parenthesis == 1 && !isBoolExpression){
            if (!oneTime){
                oneTime = true;
                return 0;
            }
        } else if (parenthesis == 0 && isParenthesis){
            scs = 0;
            isParenthesis = false;
            return 0;
        }
        if (cs >= 0 && cs != 15 && cs != 14)
            cs = expressionTransitionTable[cs][key];
        if (cs < 0){
            errorHandler(cs, string);
            return -100;
        }
        return cs;
    }

    public int statementKeywordValueGenerator(String string){
        if (string.equals("int")) return 0;
        else if (string.equals("char")) return 1;
        else if (string.equals("bool")) return 2;
        else if (string.equals("while")) return 3;
        else if (string.equals("if")) return 4;
        else if (string.matches("\\w+")){
            if ((int)string.toCharArray()[0] > 57)return 5;
            else return 17;
        }
        else if (string.equals("(")) return 6;
        else if (string.equals(")")) return 7;
        else if (string.equals("=")) return 8;
        else if (string.equals("++") || string.equals("--")) return 16;
        else if (string.equals("+") || string.equals("-") || string.equals("*") ||
                 string.equals("/") || string.equals("%")) return 9;
        else if (string.equals(";")) return 10;
        else if (string.equals(",")) return 11;
        else if (string.toCharArray()[0] == '\'') return 12;
        else if (string.equals("+=") || string.equals("-=") || string.equals("*=") ||
                 string.equals("/=") || string.equals("%=")) return 13;
        
        else if (string.equals("{")) return 50; // is not in state machine
        else if (string.equals("}")) return 51; // is not in state machine
        return -1;
    }

    public int expressionKeywordValueGenerator(String token){
        if (token.equals("(")) return 0;
        else if (token.equals(")")) return 1;
        else if (token.equals("true") || token.equals("false")) return 7;
        else if (token.matches("\\w+")){
            if ((int)token.toCharArray()[0] > 57)return 2;
            else return 3;
        }
        else if (token.equals("'")) return 4;
        else if (token.equals("||") || token.equals("&&")) return 5;

        else if (token.equals("==") || token.equals("!=") || token.equals(">=") || token.equals("<=") ||
                 token.equals("<") || token.equals(">")) return 6;
        else if (token.equals("+") || token.equals("-") || token.equals("*") ||
                 token.equals("%") || token.equals("/")) return 8;
        return -1;
    }

    private boolean isVariable(String string){
        if (string.matches("^([a − z][A − Z]) + ([a − z][A − Z][0 − 9])∗")) return true;
        return false;
    }

    private void errorHandler(int state, String seenString){
        switch (state){
            case -1:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "keyword or variable expected.\n"); //state 0
                break;
            case -2:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "variable expected.\n"); //state 1, 5, 8
                break;
            case -3:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "= or ; or , expected.\n"); //state 2, 6, 9
                break;
            case -4:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "variable or character or parenthesis expected.\n"); // state 3
                break;
            case -5:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "; or parenthesis expected.\n"); // state 4
                break;
            case -6:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "variable expected.\n"); //state 5
                break;
            case -7:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "; expected.\n"); //state 7, 13
                break;
            case -8:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "variable or number or parenthesis expected.\n"); //state 10
                break;
            case -9:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "; or operator or parenthesis expected.\n"); //state 11
                break;
            case -10:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "operator or ++ or -- or = or += ... expected.\n"); //state 12
                break;
            case -11:
                System.out.println("handle nashode"); //state 14, 15
                break;
            case -12:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "variable or number or parenthesis or character expected.\n"); //Estate 0
                break;
            case -13:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "logical operation or parenthesis expected.\n"); //Estate 1
                break;
            case -14:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or conditional operation expected.\n"); //Estate 2
                break;
            case -15:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or variable or number expected.\n"); //Estate 4, 9
                break;
            case -16:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or conditional or logical operation expected.\n"); //Estate 3
                break;
            case -17:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or variable or number or boolean value or character expected.\n"); //Estate 5
                break;
            case -18:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or operation or logical operation expected.\n"); //Estate 6, 7
                break;
            case -19:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or logical operation expected.\n"); //Estate 8
                break;
            case -20:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or conditional operation expected.\n"); //Estate 10
                break;
            case -21:
                System.out.println("In line "+ lineCounter + ", " + seenString + " seen! " + "parenthesis or variable or character expected.\n"); //Estate 11
                break;
            default:
                System.out.println("Undefined error");
                break;
            }
    }

    public boolean isSyntaxOK() {
        return syntaxIsOK;
    }
}
