package main;

import main.ast.node.Program;
import main.compileError.CompileErrorException;
//import main.visitor.astPrinter.ASTPrinter;
import main.visitor.CodeGeneration.CodeGeneration;
import main.visitor.nameAnalyser.NameAnalyser;
import org.antlr.v4.runtime.*;
import parsers.actonLexer;
import parsers.actonParser;
import main.visitor.VisitorImpl;
import java.io.IOException;

// Visit https://stackoverflow.com/questions/26451636/how-do-i-use-antlr-generated-parser-and-lexer
public class Acton {
    public static void main(String[] args) throws IOException {

        CharStream reader = CharStreams.fromFileName(args[1]);
        actonLexer lexer = new actonLexer(reader);

        CommonTokenStream tokens = new CommonTokenStream(lexer);
        actonParser parser = new actonParser(tokens);
        Program program = parser.program().p; // program is starting production rule

        try{
            NameAnalyser nameAnalyser = new NameAnalyser();
            nameAnalyser.visit(program);
            if( nameAnalyser.numOfErrors() > 0 )
                throw new CompileErrorException();
        }// symbol is done!
        catch(CompileErrorException compileError){ }

        try { //
            VisitorImpl the_visitor = new VisitorImpl();
            program.accept(the_visitor);
        }catch (Exception e){ e.printStackTrace(); }


        try{
            CodeGeneration codeGeneration = new CodeGeneration();
            codeGeneration.visit(program);
        }catch (Exception e){}
    }
}