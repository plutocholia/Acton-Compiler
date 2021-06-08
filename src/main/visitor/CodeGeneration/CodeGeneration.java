package main.visitor.CodeGeneration;

import main.ast.node.*;
import main.ast.node.Program;
import main.ast.node.declaration.*;
import main.ast.node.declaration.handler.*;
import main.ast.node.declaration.VarDeclaration;
import main.ast.node.expression.*;
import main.ast.node.expression.operators.UnaryOperator;
import main.ast.node.expression.values.BooleanValue;
import main.ast.node.expression.values.IntValue;
import main.ast.node.expression.values.StringValue;
import main.ast.node.statement.*;
import main.ast.type.Type;
import main.ast.type.actorType.ActorType;
import main.ast.type.arrayType.ArrayType;
import main.ast.type.noType.NoType;
import main.ast.type.primitiveType.BooleanType;
import main.ast.type.primitiveType.IntType;
import main.ast.type.primitiveType.StringType;
import main.symbolTable.SymbolTable;
import main.symbolTable.*;
import main.symbolTable.itemException.ItemAlreadyExistsException;
import main.symbolTable.itemException.ItemNotFoundException;
import main.symbolTable.symbolTableVariableItem.SymbolTableActorVariableItem;
import main.symbolTable.symbolTableVariableItem.SymbolTableKnownActorItem;
import main.symbolTable.symbolTableVariableItem.SymbolTableLocalVariableItem;
import main.symbolTable.symbolTableVariableItem.SymbolTableVariableItem;

import javax.swing.*;
import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import main.visitor.Visitor;
import main.visitor.ArgsDoNotMatch;


public class CodeGeneration implements Visitor {

    private boolean in_main         = false;
    private boolean in_actor        = false;
    private boolean in_handler      = false;
    private boolean in_for          = false;
    private boolean in_handler_call = false;
    private boolean in_var_acc      = false;
    private boolean isInitHandler   = false;
    private boolean in_arrcall      = false;

    // CODE GENERATION STUFF
    private boolean in_var_dec      = false;
    private boolean in_assign       = false;
    private boolean is_left_val     = false;

    private final String outputPath = "./output/";

    private HashMap<String, Integer> curr_actor_vars;
    private HashMap<String, Integer> curr_msghndlr_vars;
    private HashMap<String, Integer> main_vars;
    private HashMap<String, ActorDeclaration> actor_decs = new HashMap<>();

    private Identifier curr_id;

    public String code_actor = "";
    private String name_actor;

    public String code_msg = "";
    private String name_msg;

    public String code_main = "";
    private String name_main = "Main";

    public String code_default = "";
    private String name_default = "DefaultActor";


    // labeling stuff
    private  int label = 0;
    private String get_label(){
        return "Label" + this.label++;
    }


    private Identifier left;
    private boolean is_inc_or_dec   = false;

    // -------------------------------------------------------------------------------------------------

    protected void visitStatement( Statement stat ) {
        if( stat == null )
            return;
        else if( stat instanceof MsgHandlerCall )
            this.visit( ( MsgHandlerCall ) stat );
        else if( stat instanceof Block )
            this.visit( ( Block ) stat );
        else if( stat instanceof Conditional )
            this.visit( ( Conditional ) stat );
        else if( stat instanceof For )
            this.visit( ( For ) stat );
        else if( stat instanceof Break )
            this.visit( ( Break ) stat );
        else if( stat instanceof Continue )
            this.visit( ( Continue ) stat );
        else if( stat instanceof Print )
            this.visit( ( Print ) stat );
        else if( stat instanceof Assign )
            this.visit( ( Assign ) stat );
    }

    protected void visitExpr( Expression expr ) {
        if( expr == null )
            return;
        else if( expr instanceof UnaryExpression )
            this.visit( ( UnaryExpression ) expr );
        else if( expr instanceof BinaryExpression )
            this.visit( ( BinaryExpression ) expr );
        else if( expr instanceof ArrayCall )
            this.visit( ( ArrayCall ) expr );
        else if( expr instanceof ActorVarAccess )
            this.visit((ActorVarAccess) expr);
        else if( expr instanceof Identifier )
            this.visit( ( Identifier ) expr );
        else if( expr instanceof Self )
            this.visit( ( Self ) expr );
        else if( expr instanceof Sender )
            this.visit( ( Sender ) expr );
        else if( expr instanceof BooleanValue )
            this.visit( ( BooleanValue ) expr );
        else if( expr instanceof IntValue )
            this.visit( ( IntValue ) expr );
        else if( expr instanceof StringValue )
            this.visit( ( StringValue ) expr );
    }

    private void jasminFileCreator(String code, String className) {
        String the_dir = this.outputPath + className + ".j";
        try(FileWriter fw = new FileWriter(the_dir, false);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)) {
            out.print(code);

        }catch (Exception exception){
            exception.printStackTrace();
        }
    }

    private String getILZ(Identifier id){
        if(id.getType() instanceof IntType)
            return "I";
        else if (id.getType() instanceof BooleanType)
            return "Z";
        else if(id.getType() instanceof StringType)
            return "Ljava/lang/String;";
        else if(id.getType() instanceof ArrayType)
            return "[I";
        return "L" + id.getType() + ";";
    }

    private String generate_command_for(String cmd, int index) {
        String result;
        switch (cmd) {
            case "iload":
            case "aload":
            case "istore":
            case "astore":
                result =  index > 3 ? (cmd + " " + Integer.toString(index)) : (cmd + "_" + Integer.toString(index));
                break;
            case "iconst":
                result =  ("iconst_" + Integer.toString(index));
                break;
            case "bipush":
                result =  ("bipush " + Integer.toString(index));
                break;
            default:
                result = "SHIT in generate_command_for";
        }
        return result;
    }

    private void create_slot_msgvars(HandlerDeclaration handlerDeclaration){
        this.curr_msghndlr_vars = new HashMap<>();
        int slot_index = 0;
        this.curr_msghndlr_vars.put("self", slot_index);
        if(this.name_msg != "initial")
            this.curr_msghndlr_vars.put("sender", ++slot_index);
        for(VarDeclaration argDeclaration: handlerDeclaration.getArgs())
            this.curr_msghndlr_vars.put(argDeclaration.getIdentifier().getName(), ++slot_index);
        for(VarDeclaration localVariable: handlerDeclaration.getLocalVars())
            this.curr_msghndlr_vars.put(localVariable.getIdentifier().getName(), ++slot_index);
    }

    private void create_slot_main(Main mainActors){
        this.main_vars = new HashMap<>();
        int slot_index = 0;
        this.main_vars.put("self", slot_index);
        for(ActorInstantiation mainActor : mainActors.getMainActors())
            this.main_vars.put(mainActor.getIdentifier().getName(), ++slot_index);
    }

    private String gen_variable_loading_command (Identifier identifier, String className) {
        if (this.curr_msghndlr_vars.containsKey(identifier.getName()) && !this.in_var_acc) {
            int index = curr_msghndlr_vars.get(identifier.getName());
            if (identifier.getType() instanceof IntType || identifier.getType() instanceof BooleanType)
                return (index > 3 ? "iload " : "iload_") + Integer.toString(index);
            else
                return (index > 3 ? "aload " : "aload_") + Integer.toString(index);
        }
        else {
            return "aload_0\ngetfield " + className + "/" + identifier.getName() + " " + getILZ(identifier);
        }
    }

    private String gen_variable_loading_command (Identifier identifier, String className, int index) {
        if (this.curr_msghndlr_vars.containsKey(identifier.getName()) && !this.in_var_acc) {
            if (identifier.getType() instanceof IntType || identifier.getType() instanceof BooleanType)
                return (index > 3 ? "iload " : "iload_") + Integer.toString(index);
            else
                return (index > 3 ? "aload " : "aload_") + Integer.toString(index);
        }
        else {
            return "aload_0\ngetfield " + className + "/" + identifier.getName() + " " + getILZ(identifier);
        }
    }

    private String gen_variable_loading_command_known_var(Identifier identifier, String className, int index) {
        if (identifier.getType() instanceof IntType || identifier.getType() instanceof BooleanType)
            return (index > 3 ? "iload " : "iload_") + Integer.toString(index);
        else
            return (index > 3 ? "aload " : "aload_") + Integer.toString(index);
    }

    private void code_msghandler_jasmin(HandlerDeclaration handlerDeclaration){
        String msg_class_name = this.name_actor + "_" + this.name_msg;
        this.name_msg = handlerDeclaration.getName().getName();
        this.code_msg += ".class public " +  msg_class_name + "\n" +
                ".super Message\n";

        this.code_msg += "\n";
        // Fields for Acton_function.j
        for(VarDeclaration argDecleration : handlerDeclaration.getArgs())
            this.code_msg += ".field private " + argDecleration.getIdentifier().getName() + " " +
                    this.getILZ(argDecleration.getIdentifier())+ "\n";
        this.code_msg += ".field private receiver L"+ this.name_actor + ";\n" +
                ".field private sender LActor;\n";

        this.code_msg += "\n";

        // Constructor for A_foo.j
        this.code_msg += ".method public <init>(L" + this.name_actor + ";LActor;";
        for(VarDeclaration argDecleration : handlerDeclaration.getArgs())
            this.code_msg +=  this.getILZ(argDecleration.getIdentifier());
        this.code_msg += ")V\n";

        this.code_msg += ".limit stack 2\n" +
                ".limit locals " + (handlerDeclaration.getArgs().size() + 3) + "\n";

        this.code_msg +=
                "aload_0\n" +
                        "invokespecial Message/<init>()V\n" +
                        "aload_0\n" +
                        "aload_1\n" +
                        "putfield "+ msg_class_name +"/receiver L"+ this.name_actor +";\n" +
                        "aload_0\n" +
                        "aload_2\n" +
                        "putfield " + msg_class_name + "/sender LActor;\n";

        int _tcnt = 3;
        for(VarDeclaration arg : handlerDeclaration.getArgs())
            this.code_msg +=
                    "aload_0\n" +
                            this.gen_variable_loading_command(arg.getIdentifier(), this.name_actor,  _tcnt++) + "\n" +
                            "putfield "+ msg_class_name +"/"+ arg.getIdentifier().getName() + " " +
                            this.getILZ(arg.getIdentifier()) + "\n";

        this.code_msg += "return\n.end method\n";
        this.code_msg += "\n";

        this.code_msg +=
                ".method public execute()V\n" +
                        ".limit stack 3\n" +
                        ".limit locals 1\n";

        this.code_msg +=
                "aload_0\n" +
                        "getfield "+ msg_class_name + "/receiver L"+this.name_actor+";\n" +
                        "aload_0\n" +
                        "getfield "+ msg_class_name + "/sender LActor;\n";

        for(VarDeclaration arg : handlerDeclaration.getArgs()) {
            this.code_msg += "aload_0\n" + "getfield "+ msg_class_name + "/" + arg.getIdentifier().getName()
                    +" " + this.getILZ(arg.getIdentifier()) + "\n";

        }

        this.code_msg += "invokevirtual "+ this.name_actor+"/"+ this.name_msg +"(LActor;";
        for(VarDeclaration arg : handlerDeclaration.getArgs())
            this.code_msg += this.getILZ(arg.getIdentifier());
        this.code_msg += ")V\n";

        this.code_msg += "return\n" + ".end method\n";

        System.out.printf("msghandler %s is added\n", handlerDeclaration.getName().getName());
        this.jasminFileCreator(this.code_msg, this.name_actor + "_" + this.name_msg);
        this.code_msg = "";
    }

    private int store(boolean isMsgHndlr, String name) {
        int index = 0;
        if (isMsgHndlr) {
            if (this.curr_msghndlr_vars.containsKey(name))
                return this.curr_msghndlr_vars.get(name);
            else {
                index = this.curr_msghndlr_vars.size();
                this.curr_msghndlr_vars.put(name, index);
            }
        }
        else {
            if (this.main_vars.containsKey(name))
                return this.main_vars.get(name);
            else {
                index = this.main_vars.size();
                this.main_vars.put(name, index);
            }
        }
        return index;
    }

    private void code_main_jasmin(Main main) {

        this.code_main += ".class public Main\n" +
                ".super java/lang/Object\n" +
                "\n" +
                ".method public <init>()V\n" +
                ".limit stack 1\n" +
                ".limit locals 1\n" +
                "aload_0\n" +
                "invokespecial java/lang/Object/<init>()V\n" +
                "return\n" +
                ".end method\n" +
                "\n" +
                ".method public static main([Ljava/lang/String;)V\n" +
                ".limit stack 16\n" +
                ".limit locals 16\n";

        for(ActorInstantiation mainActor : main.getMainActors()) {
            int new_index = store(false, mainActor.getIdentifier().getName());
            this.code_main += "new " +
                    mainActor.getType().toString() +
                    "\n" +
                    "dup\n" +
                    iconst_or_bipush(this.actor_decs.get(mainActor.getType().toString()).getQueueSize()) +
                    "\n" +
                    "invokespecial " +
                    mainActor.getType().toString() +
                    "/" +
                    "<init>(I)V\n" +
                    (new_index > 3 ? "astore " : "astore_") +
                    Integer.toString(new_index) + "\n";
        }

        for(ActorInstantiation mainActor : main.getMainActors()) {
            int index = this.main_vars.get(mainActor.getIdentifier().getName());
            this.code_main += (index > 3 ? "aload " : "aload_") + Integer.toString(index) + "\n";

            for(Identifier knownActor : mainActor.getKnownActors()){
                int index_knownactor = this.main_vars.get(knownActor.getName());
                this.code_main += (index_knownactor > 3 ? "aload " : "aload_") + Integer.toString(index_knownactor) + "\n";
            }
            this.code_main += "invokevirtual "
                    + mainActor.getType().toString() +
                    "/" +
                    "setKnownActors(";
            for(Identifier knownActor : mainActor.getKnownActors())
                this.code_main += getILZ(knownActor);
            this.code_main += ")V\n";
        }

        for(ActorInstantiation mainActor : main.getMainActors())
            if (this.actor_decs.get(mainActor.getType().toString()).getInitHandler() != null) {
                int index = this.main_vars.get(mainActor.getIdentifier().getName());
                this.code_main += (index > 3 ? "aload " : "aload_") +
                        Integer.toString(index) +
                        "\n" +
                        "invokevirtual " +
                        mainActor.getType().toString() +
                        "/" +
                        "initial()V\n";
            }

        for(ActorInstantiation mainActor : main.getMainActors()) {
            int index = this.main_vars.get(mainActor.getIdentifier().getName());
            this.code_main += (index > 3 ? "aload " : "aload_") +
                    Integer.toString(index) +
                    "\n" +
                    "invokevirtual " +
                    mainActor.getType().toString() +
                    "/start()V\n";
        }
        this.code_main += "return\n.end method";
        this.jasminFileCreator(this.code_main, "main");
        this.code_main = "";
    }

    private String iconst_or_bipush(int constant) {
        return (constant > 5 ? "bipush " : "iconst_") + Integer.toString(constant);
    }

    private String putfield_cmd(Identifier identifier, String classname) {
        return "putfield " + classname + "/" + identifier.getName() + " " + getILZ(identifier);
    }

    private String store_cmd(Identifier identifier) {
        int index = 0;
        String cmd = "";
        if (identifier.getType() instanceof IntType || identifier.getType() instanceof BooleanType)
            cmd = "istore";
        else
            cmd = "astore";
        if (this.curr_msghndlr_vars.containsKey(identifier.getName())) {
            index = this.curr_msghndlr_vars.get(identifier.getName());
            return (index > 3 ? cmd + " " : cmd + "_") + index;
        }
        return "NotFound";
    }

    private String code_default_jasmin(){
       return ".class public DefaultActor\n" +
                ".super java/lang/Thread\n" +
                "\n" +
                ".method public <init>()V\n" +
                ".limit stack 1\n" +
                ".limit locals 1\n" +
                "aload_0\n" +
                "invokespecial java/lang/Thread/<init>()V\n" +
                "return\n" +
                ".end method\n\n";
    }

    private void add_send_msg_to_default(HandlerDeclaration handlerDeclaration){
        this.code_default += ".method public send_" + handlerDeclaration.getName().getName() + "(LActor;";
        for(VarDeclaration arg : handlerDeclaration.getArgs())
            this.code_default += this.getILZ(arg.getIdentifier());
        this.code_default += ")V\n";
        this.code_default += ".limit stack 2\n" +
                ".limit locals 3\n" +
                "getstatic java/lang/System/out Ljava/io/PrintStream;\n" +
                "ldc \"there is no msghandler named "+handlerDeclaration.getName().getName()+" in sender\"\n" +
                "invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V\n" +
                "return\n" +
                ".end method\n\n";
    }

    private String inc_or_dec_cmd(Identifier identifier, boolean is_inc, boolean is_pre) {
        String cmd = "";
        if (this.curr_msghndlr_vars.containsKey(identifier.getName())) {
            int index = this.curr_msghndlr_vars.get(identifier.getName());
            int sign = is_inc ? 1 : -1;
            if (is_pre)
                cmd += "iinc " + Integer.toString(index) + " " + Integer.toString(sign) +
                        "\n" + gen_variable_loading_command(identifier,this.name_actor);
            else
                cmd += gen_variable_loading_command(identifier, this.name_actor) + "\n" +
                        "iinc " + Integer.toString(index) + " " + Integer.toString(sign);
        }
        else {
            String add_or_sub = is_inc ? "iadd" : "isub";
            if (is_pre)
                cmd += "aload_0\ndup\n" + "getfield " +
                        this.name_actor + "/" + identifier.getName() + " " + this.getILZ(identifier) +
                        "\n" + "iconst_1\n" + add_or_sub + "\ndup_x1\n" +
                        putfield_cmd(identifier, this.name_actor);
            else
                cmd += "aload_0\ndup\n" + "getfield " +
                        this.name_actor + "/" + identifier.getName() + " " + this.getILZ(identifier) +
                        "\n" + "dup_x1\niconst_1\n" + add_or_sub + "\n" +
                        putfield_cmd(identifier, this.name_actor);
        }
        return cmd;
    }

    // ------------------------------------------------------------------------------------------------------

    @Override
    public void visit(Program program) {
        this.code_default += this.code_default_jasmin();

        for(ActorDeclaration actorDeclaration : program.getActors())
            actorDeclaration.accept(this);
        program.getMain().accept(this);

        System.out.println("defalut code is added\n");
        this.jasminFileCreator(this.code_default, this.name_default);
    }

    @Override
    public void visit(ActorDeclaration actorDeclaration) {

        this.in_actor = true;
        this.name_actor = actorDeclaration.getName().getName();

        this.actor_decs.put(actorDeclaration.getName().getName(), actorDeclaration);

        this.code_actor += ".class public "+ actorDeclaration.getName().getName() + "\n";
        this.code_actor += ".super Actor\n";
        this.code_actor += "\n";

        for(VarDeclaration var : actorDeclaration.getKnownActors())
            this.code_actor += ".field " + var.getIdentifier().getName() + " " +this.getILZ(var.getIdentifier()) + "\n";
        for(VarDeclaration var : actorDeclaration.getActorVars())
            this.code_actor += ".field " + var.getIdentifier().getName() + " " +this.getILZ(var.getIdentifier()) + "\n";
        this.code_actor += "\n";
//
        this.code_actor += ".method public <init>(I)V\n" +
                ".limit stack 2\n" +
                ".limit locals 2\n" +
                "aload_0\n" +
                "iload_1\n" +
                "invokespecial Actor/<init>(I)V\n" +
                "return\n" +
                ".end method\n";
        this.code_actor += "\n";
//
        this.code_actor += ".method public setKnownActors(";
        for(VarDeclaration var : actorDeclaration.getKnownActors())
            this.code_actor += this.getILZ(var.getIdentifier());
        this.code_actor += ")V\n";
        this.code_actor += ".limit stack 2\n" +
                ".limit locals " + (1 + actorDeclaration.getKnownActors().size()) + "\n";

        int _tcnt = 1;
        for(VarDeclaration var : actorDeclaration.getKnownActors())
            this.code_actor += "aload_0\n" +
                    this.gen_variable_loading_command_known_var(var.getIdentifier(), this.name_actor, _tcnt++) + "\n" +
                    "putfield " + this.name_actor + "/" + var.getIdentifier().getName() + " " +
                    this.getILZ(var.getIdentifier()) + "\n";
        this.code_actor += "return\n" +
                ".end method\n";
        this.code_actor += "\n";



        // ---------------------- VISITING STUFF -----------------------------------
        visitExpr(actorDeclaration.getName());
        visitExpr(actorDeclaration.getParentName());

        for(VarDeclaration varDeclaration: actorDeclaration.getKnownActors())
            varDeclaration.accept(this);
        for(VarDeclaration varDeclaration: actorDeclaration.getActorVars())
            varDeclaration.accept(this);
        if(actorDeclaration.getInitHandler() != null) {
            this.isInitHandler = true;
            actorDeclaration.getInitHandler().accept(this);
            this.isInitHandler = false;
        }
        for(MsgHandlerDeclaration msgHandlerDeclaration: actorDeclaration.getMsgHandlers())
            msgHandlerDeclaration.accept(this);

        this.in_actor = false;


        // Generating the Fucking file :/
        System.out.printf("actor %s is added\n", actorDeclaration.getName().getName());
        this.jasminFileCreator(this.code_actor, this.name_actor);
        this.code_actor = "";
    }

    @Override
    public void visit(HandlerDeclaration handlerDeclaration) {
        this.in_handler = true;
        this.name_msg = handlerDeclaration.getName().getName();
        String msg_class_name = this.name_actor + "_" + this.name_msg;

        // Creating Slot
        this.create_slot_msgvars(handlerDeclaration);

        // Generating code for Acton_function.j
        if(handlerDeclaration.getName().getName() != "initial") {
            this.code_msghandler_jasmin(handlerDeclaration);
            this.add_send_msg_to_default(handlerDeclaration);

            // Actor.j stuff:
            this.code_actor += ".method public " + "send_" + this.name_msg + "(LActor;";
            for (VarDeclaration var : handlerDeclaration.getArgs())
                this.code_actor += this.getILZ(var.getIdentifier());
            this.code_actor += ")V\n";
            this.code_actor += ".limit stack " + (5 + handlerDeclaration.getArgs().size()) + "\n"+
                    ".limit locals " + (handlerDeclaration.getArgs().size() + 2) + "\n";
            this.code_actor += "aload_0\n" +
                    "new " + msg_class_name + "\n" +
                    "dup\n" +
                    "aload_0\n" +
                    "aload_1\n";

            int _tcnt = 2;
            for(VarDeclaration var: handlerDeclaration.getArgs())
                this.code_actor += this.gen_variable_loading_command(var.getIdentifier(), this.name_actor, _tcnt++) + "\n";

            this.code_actor += "invokespecial " + msg_class_name + "/<init>/(L" + this.name_actor + ";LActor;";
            for(VarDeclaration var: handlerDeclaration.getArgs())
                this.code_actor += this.getILZ(var.getIdentifier());
            this.code_actor += ")V\n";
            this.code_actor += "invokevirtual "+ this.name_actor+ "/send(LMessage;)V\n";
            this.code_actor += "return\n" +
                    ".end method\n";
            this.code_actor += "\n";

            this.code_actor += ".method public "+ this.name_msg+ "(LActor;";
            for(VarDeclaration arg : handlerDeclaration.getArgs())
                this.code_actor += this.getILZ(arg.getIdentifier());
            this.code_actor += ")V\n";
        }
        else{ // initial stuff
            this.code_actor += ".method public initial(";
            for(VarDeclaration arg : handlerDeclaration.getArgs())
                this.code_actor += this.getILZ(arg.getIdentifier());
            this.code_actor += ")V\n";
        }

        this.code_actor += ".limit stack 16\n" +
                ".limit locals " + (this.curr_msghndlr_vars.size()) + "\n";


       //  VISITING
        for(VarDeclaration argDeclaration: handlerDeclaration.getArgs()) {
            argDeclaration.accept(this);
        }
        for(VarDeclaration localVariable: handlerDeclaration.getLocalVars()) {
            localVariable.accept(this);
        }
        for(Statement statement  : handlerDeclaration.getBody())
            visitStatement(statement);


        this.code_actor += "return\n" +
                ".end method\n";
        this.code_actor += "\n";

        this.in_handler = false;
    }

    @Override
    public void visit(VarDeclaration varDeclaration) {
        this.in_var_dec = true;
        visitExpr(varDeclaration.getIdentifier());
        this.in_var_dec = false;
    }

    @Override
    public void visit(Main mainActors) {
        this.in_main = true;

        // Creating Slot for main
        this.create_slot_main(mainActors);

        // generating code
        this.code_main_jasmin(mainActors);

        // VISITING
        for(ActorInstantiation mainActor : mainActors.getMainActors())
            mainActor.accept(this);

        this.in_main = false;
    }

    @Override
    public void visit(ActorInstantiation actorInstantiation) {

        visitExpr(actorInstantiation.getIdentifier());
        for(Identifier knownActor : actorInstantiation.getKnownActors())
            visitExpr(knownActor);
        for(Expression initArg : actorInstantiation.getInitArgs())
            visitExpr(initArg);
    }

    @Override
    public void visit(UnaryExpression unaryExpression) {

        switch (unaryExpression.getUnaryOperator().name()) {
            case "preinc":
                this.is_inc_or_dec = true;
                visitExpr(unaryExpression.getOperand());
                this.is_inc_or_dec = false;
                this.code_actor += this.inc_or_dec_cmd(this.curr_id, true, true) + "\n";
                break;
            case "predec":
                this.is_inc_or_dec = true;
                visitExpr(unaryExpression.getOperand());
                this.is_inc_or_dec = false;
                this.code_actor += this.inc_or_dec_cmd(this.curr_id, false, true) + "\n";
                break;
            case "postinc":
                this.is_inc_or_dec = true;
                visitExpr(unaryExpression.getOperand());
                this.is_inc_or_dec = false;
                this.code_actor += this.inc_or_dec_cmd(this.curr_id, true, false) + "\n";
                break;
            case "postdec":
                this.is_inc_or_dec = true;
                visitExpr(unaryExpression.getOperand());
                this.is_inc_or_dec = false;
                this.code_actor += this.inc_or_dec_cmd(this.curr_id, false, false) + "\n";
                break;
            case "minus":
                visitExpr(unaryExpression.getOperand());
                this.code_actor += "ineg\n";
                break;
            case "not":
                visitExpr(unaryExpression.getOperand());
                String first_label = this.get_label();
                String second_label = this.get_label();
                this.code_actor += "ifne " + first_label + "\n" + "iconst_1\n" +
                        "goto " + second_label + "\n" + first_label + ":\n" +
                        "iconst_0\n" + second_label + ":\n";
                break;
        }
    }

    @Override
    public void visit(BinaryExpression binaryExpression) {

        visitExpr(binaryExpression.getLeft());
        visitExpr(binaryExpression.getRight());

        String first_label = "";
        String second_label = "";

        switch (binaryExpression.getBinaryOperator().name()) {
            case "add":
                this.code_actor += "iadd\n";
                break;
            case "sub":
                this.code_actor += "isub\n";
                break;
            case "mult":
                this.code_actor += "imult\n";
                break;
            case "div":
                this.code_actor += "idiv\n";
                break;
            case "mod":
                this.code_actor += "irem\n";
                break;
            case "and":
                this.code_actor += "iand\n";
                break;
            case "or":
                this.code_actor += "ior\n";
                break;
            case "eq":
                first_label = this.get_label();
                second_label = this.get_label();
                this.code_actor += "if_icmpne " + first_label + "\n" + "iconst_1\n" +
                        "goto " + second_label + "\n" + first_label + ":\n" +
                        "iconst_0\n" + second_label + ":\n";
                break;
            case "neq":
                first_label = this.get_label();
                second_label = this.get_label();
                this.code_actor += "if_icmpeq " + first_label + "\n" + "iconst_1\n" +
                        "goto " + second_label + "\n" + first_label + ":\n" +
                        "iconst_0\n" + second_label + ":\n";
                break;
            case "gt":
                first_label = this.get_label();
                second_label = this.get_label();
                this.code_actor += "if_icmple " + first_label + "\n" + "iconst_1\n" +
                        "goto " + second_label + "\n" + first_label + ":\n" +
                        "iconst_0\n" + second_label + ":\n";
                break;
            case "lt":
                first_label = this.get_label();
                second_label = this.get_label();
                this.code_actor += "if_icmpge " + first_label + "\n" + "iconst_1\n" +
                        "goto " + second_label + "\n" + first_label + ":\n" +
                        "iconst_0\n" + second_label + ":\n";
                break;
        }
    }

    @Override
    public void visit(ArrayCall arrayCall) {

        this.in_arrcall = true;
        visitExpr(arrayCall.getArrayInstance());
        this.in_arrcall = false;

        this.code_actor += this.gen_variable_loading_command(this.curr_id, this.name_actor) + "\n";
        visitExpr(arrayCall.getIndex());
        if (this.in_assign && !this.is_left_val)
            this.code_actor += "iaload\n";
    }

    @Override
    public void visit(ActorVarAccess actorVarAccess) {
        this.in_var_acc = true;
        visitExpr(actorVarAccess.getSelf());
        visitExpr(actorVarAccess.getVariable());
        this.in_var_acc = false;

    }

    @Override
    public void visit(Identifier identifier) {
        this.curr_id = identifier;

        // CODE GENERATION STUFF
        if (!this.in_var_dec && !this.is_left_val && !this.in_arrcall && !this.is_inc_or_dec) {
            if (this.in_handler && !in_handler_call) {
                if (this.curr_msghndlr_vars.containsKey(identifier.getName()) && !this.in_var_acc) {
                    if (identifier.getType() instanceof IntType || identifier.getType() instanceof BooleanType) {
                        // TODO: iload index
                        this.code_actor += (
                                this.generate_command_for(
                                        "iload", this.curr_msghndlr_vars.get(identifier.getName())) + "\n");
                    } else {
                        // TODO: aload index
                        this.code_actor += (
                                this.generate_command_for(
                                        "aload", this.curr_msghndlr_vars.get(identifier.getName())) + "\n");
                    }
                } else {
                    this.code_actor += String.format("aload_0\ngetfield %s/%s %s\n", this.name_actor, identifier.getName(),
                            this.getILZ(identifier));
                }
            } else if (this.in_main) {
                // TODO: aload index
            }
        }
        else if(this.is_left_val){

        }
    }

    @Override
    public void visit(Self self) {
    }

    @Override
    public void visit(Sender sender) {
        this.code_actor += "aload_1\n";
        this.curr_id = new Identifier("Acton");
    }

    @Override
    public void visit(BooleanValue value) {

        this.code_actor += "icosnt_" + (value.getConstant() ? "1" : "0") + "\n";
    }

    @Override
    public void visit(IntValue value) {
        this.code_actor += (value.getConstant() > 5 ? "bipush " : "iconst_") +
                Integer.toString(value.getConstant()) + "\n";
    }

    @Override
    public void visit(StringValue value) {

        this.code_actor += "ldc " + value.getConstant() + "\n";
    }

    @Override
    public void visit(Block block) {
        if(block == null)
            return;
        for(Statement statement : block.getStatements())
            visitStatement(statement);
    }

    @Override
    public void visit(Conditional conditional) {
        visitExpr(conditional.getExpression());
        visitStatement(conditional.getThenBody());
        visitStatement(conditional.getElseBody());
    }

    @Override
    public void visit(For loop) {
        this.in_for = true;
        if(loop.getInitialize() != null)
            visitStatement(loop.getInitialize());

        if (loop.getCondition() != null)
            visitExpr(loop.getCondition());

        if (loop.getUpdate() != null)
            visitStatement(loop.getUpdate());

        visitStatement(loop.getBody());
        this.in_for = false;
    }

    @Override
    public void visit(Break breakLoop) {

    }

    @Override
    public void visit(Continue continueLoop) {

    }

    @Override
    public void visit(MsgHandlerCall msgHandlerCall) {

        visitExpr(msgHandlerCall.getInstance());
        Identifier id = this.curr_id;
        if(msgHandlerCall.getInstance() instanceof Sender)
            this.code_actor += "aload_0\n";

        this.in_handler_call = true;
        visitExpr(msgHandlerCall.getMsgHandlerName());
        this.in_handler_call = false;
        for (Expression argument : msgHandlerCall.getArgs())
            visitExpr(argument);


        this.code_actor += "invokevirtual "+ id.getName() + "/" + "send_" +
                msgHandlerCall.getMsgHandlerName().getName() + "(LActor;";

        for(Expression exp : msgHandlerCall.getArgs()) {
            Identifier tempid = new Identifier("xxxx123");
            tempid.setType(exp.getType());
            this.code_actor += this.getILZ(tempid);
        }
        this.code_actor += ")V\n";


        this.in_handler_call = false;

    }

    @Override
    public void visit(Print print) {
        if(print == null)
            return;
        code_actor += "getstatic java/lang/System/out Ljava/io/PrintStream;\n";
        visitExpr(print.getArg());
        String jasmineType = "";
        if (print.getArg().getType() instanceof IntType)
            jasmineType = "I";
        else if (print.getArg().getType() instanceof BooleanType)
            jasmineType = "Z";
        else
            jasmineType = "Ljava/lang/String;";
        code_actor += "invokevirtual java/io/PrintStream/println(" + jasmineType + ")V\n";
    }

    @Override
    public void visit(Assign assign) {
        this.in_assign = true;

        if(assign.getlValue() instanceof  ArrayCall){
            this.is_left_val = true;
            visitExpr(assign.getlValue());
            this.is_left_val = false;

            visitExpr(assign.getrValue());

            this.code_actor += "iastore\n";
        }
        else {

            this.is_left_val = true;
            visitExpr(assign.getlValue());
            this.left = this.curr_id;
            this.is_left_val = false;

            if (!this.curr_msghndlr_vars.containsKey(curr_id.getName()) && !(assign.getlValue() instanceof ActorVarAccess))
                this.code_actor += "aload_0\n";
            visitExpr(assign.getrValue());
            if (this.curr_msghndlr_vars.containsKey(left.getName()) && !(assign.getlValue() instanceof ActorVarAccess))
                this.code_actor += store_cmd(left) + "\n";
            else
                code_actor += putfield_cmd(left, name_actor) + "\n";
        }

        this.in_assign = false;
    }

}