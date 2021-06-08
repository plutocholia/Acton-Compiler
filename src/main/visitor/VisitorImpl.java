package main.visitor;
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;


public class VisitorImpl implements Visitor {


    private SymbolTableActorItem cur_actor_sym;
    private SymbolTableHandlerItem cur_handler_sym;
    private SymbolTableMainItem cur_main_sym;
    private boolean in_main         = false;
    private boolean in_actor        = false;
    private boolean in_handler      = false;
    private boolean in_for          = false;
    private boolean in_handler_call = false;
    private boolean in_var_acc      = false;
    private boolean isInitHandler   = false;


    // CODE GENERATION STUFF
    private boolean in_var_dec      = false;
    private boolean in_assign       = false;
    private boolean is_left_val     = false;
    private HashMap<String, Integer> curr_actor_vars;
    private HashMap<String, Integer> curr_msghndlr_vars;
    private HashMap<String, Integer> main_vars;


    public String code_actor;
    public String code_msg;
    public String code_main;

    // -------------------------------------------------------------------------------------------------

    protected void visitStatement( Statement stat )
    {
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

    protected void visitExpr( Expression expr )
    {
        if( expr == null )
            return;
        else if( expr instanceof UnaryExpression )
            this.visit( ( UnaryExpression ) expr );
        else if( expr instanceof BinaryExpression )
            this.visit( ( BinaryExpression ) expr );
        else if( expr instanceof ArrayCall )
            this.visit( ( ArrayCall ) expr );
        else if( expr instanceof ActorVarAccess )
            this.visit( ( ActorVarAccess ) expr );
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

    private Type type_getter_from_handler(Identifier id) throws ItemNotFoundException{
        Type the_type = null;
        try {
            SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.cur_handler_sym.getHandlerSymbolTable().get(
                    SymbolTableVariableItem.STARTKEY + id.getName());
//            System.out.printf("##### %d %s ######## \n", init_item.getIndex(), init_item.getName());
            the_type = init_item.getVarDeclaration().getType();
        }catch (Exception e){
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_act(Identifier id) throws ItemNotFoundException{
        Type the_type = null;
        try{
            SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.cur_actor_sym.getActorSymbolTable().get(
                    SymbolTableVariableItem.STARTKEY + id.getName());
            the_type = init_item.getVarDeclaration().getType();
        } catch (ItemNotFoundException e){
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_main(Identifier id) throws ItemNotFoundException{
        Type the_type = null;
        try{
//            SymbolTableMainItem mainItem = (SymbolTableMainItem) SymbolTable.root.get(
//                    SymbolTableMainItem.STARTKEY + "main"
//            );
            SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.cur_main_sym.getMainSymbolTable().get(
                    SymbolTableVariableItem.STARTKEY + id.getName());
            the_type = init_item.getVarDeclaration().getType();
        }catch (ItemNotFoundException e){
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_whole_actor(Identifier id) throws ItemNotFoundException{
        Type the_type = null;
        try{
            the_type = this.type_getter_from_handler(id);
        }catch (ItemNotFoundException e){
            try{
                the_type = this.type_getter_from_act(id);
            }catch (ItemNotFoundException e1){
                throw  new ItemNotFoundException();
            }
        }
        return the_type;
    }

    private Type type_getter_from_actor_items(Identifier id) throws ItemNotFoundException{
        Type the_type = null;
        try {
            SymbolTableActorItem  actorItem = (SymbolTableActorItem) SymbolTable.root.get(
                    SymbolTableActorItem.STARTKEY + id.getName()
            );
            if(actorItem.getActorDeclaration().getName().getType() instanceof NoType)
                the_type = new NoType();
            else
                the_type = new ActorType(id);
        }catch (ItemNotFoundException e){
            throw new ItemNotFoundException();
        }
        return the_type;
    }

    private Type type_getter_from_actor_handlers(Identifier handler_id, Identifier actor_id, ArrayList<Expression> args)
            throws Exception{
        Type the_type = null;

        SymbolTableActorItem  actorItem = (SymbolTableActorItem) SymbolTable.root.get(
                SymbolTableActorItem.STARTKEY + actor_id.getName()
        );
        SymbolTableHandlerItem temp = (SymbolTableHandlerItem) actorItem.getActorSymbolTable().get(
                SymbolTableHandlerItem.STARTKEY + handler_id.getName());
        the_type = actor_id.getType();

        if(temp.getHandlerDeclaration().getArgs().size() != args.size()){
            throw new ArgsDoNotMatch();
        }

        for(int i = 0; i < args.size(); i++){
            if((!args.get(i).getType().toString().equals(
                    temp.getHandlerDeclaration().getArgs().get(i).getType().toString()) &&
                    !(args.get(i).getType() instanceof NoType)
            )
            ){
                throw new ArgsDoNotMatch();
            }
        }

//        Type the_type = null;
//        SymbolTableHandlerItem temp = (SymbolTableHandlerItem) this.cur_actor_sym.getActorSymbolTable().get(
//                SymbolTableHandlerItem.STARTKEY + id.getName());
//        Identifier temp_id = new Identifier(this.cur_actor_sym.getActorDeclaration().getName().getName());
//        the_type = new ActorType(temp_id);
        return the_type;
    }

    private ArrayList<VarDeclaration> get_known_actors_from_actor(Identifier actor){
        ArrayList<VarDeclaration> the_known_actors = null;

        try{
            SymbolTableActorItem  actorItem = (SymbolTableActorItem) SymbolTable.root.get(
                    SymbolTableActorItem.STARTKEY + actor.getName()
            );
            the_known_actors = actorItem.getActorDeclaration().getKnownActors();
        }catch (ItemNotFoundException e){
            System.out.printf("There is no such %s\n", actor.getName());
        }

        return the_known_actors;
    }

    private ArrayList<VarDeclaration> get_initial_vars_from_actor(Identifier actor){
        ArrayList<VarDeclaration> the_actor_vars = null;

        try{
            SymbolTableActorItem  actorItem = (SymbolTableActorItem) SymbolTable.root.get(
                    SymbolTableActorItem.STARTKEY + actor.getName()
            );
            try {
                the_actor_vars = actorItem.getActorDeclaration().getInitHandler().getArgs();
            }catch (NullPointerException e404){
                the_actor_vars = null;
            }
        }catch (ItemNotFoundException e){
            System.out.printf("There is no such %s\n", actor.getName());
        }

        return the_actor_vars;
    }

    private Type type_getter_from_actorvars(Identifier id) throws ItemNotFoundException{
        ArrayList<VarDeclaration> the_vars = this.cur_actor_sym.getActorDeclaration().getActorVars();
        for(VarDeclaration var : the_vars) {
            if (id.getName().equals(var.getIdentifier().getName()))
                return var.getType();
        }
        throw  new ItemNotFoundException();
    }

    private Type type_getter(Identifier id) {

        Type the_type = null;
        try {
            the_type = this.type_getter_from_whole_actor(id);
        } catch (ItemNotFoundException e) {
            try {
                the_type = this.type_getter_from_main(id);
            } catch (ItemNotFoundException e1) {
                try {
                    the_type = this.type_getter_from_actor_items(id);
                } catch (ItemNotFoundException e2) {
                    the_type = new NoType();
                }
            }
        }
//        System.out.printf("from  : %s ==> %s\n", id.getName(), the_type);
        return the_type;
    }

    private boolean isLeftValue (Expression expression) {
        return expression instanceof ArrayCall || expression instanceof Identifier || expression instanceof ActorVarAccess;
    }

    private String findParent(String actorName) {
        //returns "null" if not found

        try {
            if ( ((SymbolTableActorItem)SymbolTable.root.get(SymbolTableActorItem.STARTKEY + actorName)).getParentName() != null )
                return ((SymbolTableActorItem)SymbolTable.root.get(SymbolTableActorItem.STARTKEY + actorName)).getParentName();
            else
                return "null";
        } catch (ItemNotFoundException e) {
//            System.out.println("hereeeeeeeee");
            return "null";
        }
    }

    private boolean isSubType(ActorType subType, ActorType supType) {
        // if A extends B then A is supType and B is subType

        String subName = subType.toString();
        String supName = supType.toString();
        while (true) {
            if (findParent(supName).equals(subName))
                return true;
            else if ( findParent(supName).equals("null") ||
                    findParent(supName).equals(supType.toString()) )
                return false;
            else
                supName = findParent(supName);
        }
    }

    private void gen_file(String code, String file_name){}


    // ------------------------------------------------------------------------------------------------------

    @Override
    public void visit(Program program) {
        for(ActorDeclaration actorDeclaration : program.getActors())
            actorDeclaration.accept(this);
        program.getMain().accept(this);

    }

    @Override
    public void visit(ActorDeclaration actorDeclaration) {
        visitExpr(actorDeclaration.getName());
        visitExpr(actorDeclaration.getParentName());

        try {
            this.cur_actor_sym = (SymbolTableActorItem)  SymbolTable.root.get(SymbolTableActorItem.STARTKEY + actorDeclaration.getName().getName());
            this.in_actor = true;
        } catch (Exception e) {e.printStackTrace();}

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
    }

    @Override
    public void visit(HandlerDeclaration handlerDeclaration) {
        try {
            this.cur_handler_sym = (SymbolTableHandlerItem)  this.cur_actor_sym.getActorSymbolTable().get(SymbolTableHandlerItem.STARTKEY + handlerDeclaration.getName().getName());
            this.in_handler = true;
        } catch (ItemNotFoundException e) {e.printStackTrace();}

        // VISITING
        this.curr_msghndlr_vars = new HashMap<>();
        int slot_index = 0;
        this.curr_msghndlr_vars.put("self", slot_index);
        for(VarDeclaration argDeclaration: handlerDeclaration.getArgs()) {
            argDeclaration.accept(this);
            this.curr_msghndlr_vars.put(argDeclaration.getIdentifier().getName(), ++slot_index);
        }
        for(VarDeclaration localVariable: handlerDeclaration.getLocalVars()) {
            localVariable.accept(this);
            this.curr_msghndlr_vars.put(localVariable.getIdentifier().getName(), ++slot_index);
        }
        for(Statement statement : handlerDeclaration.getBody())
            visitStatement(statement);

        for (HashMap.Entry<String, Integer> entry : this.curr_msghndlr_vars.entrySet()) {
            String key = entry.getKey();
            Integer value = entry.getValue();
//            System.out.println("name: " + key + " index: " + value);
        }

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
        try {
            this.cur_main_sym = (SymbolTableMainItem) SymbolTable.root.get(
                    SymbolTableMainItem.STARTKEY + "main"
            );
            this.in_main = true;
        } catch (ItemNotFoundException e) {e.printStackTrace();}

        // VISITING
        this.main_vars = new HashMap<>();
        int slot_index = 0;
        this.main_vars.put("self", slot_index);
        for(ActorInstantiation mainActor : mainActors.getMainActors()) {
            mainActor.accept(this);
            this.main_vars.put(mainActor.getIdentifier().getName(), ++slot_index);
        }

//        for (HashMap.Entry<String, Integer> entry : this.main_vars.entrySet()) {
//            String key = entry.getKey();
//            Integer value = entry.getValue();
//            System.out.println("name: " + key + " index: " + value);
//        }
        this.in_main = false;
    }

    @Override
    public void visit(ActorInstantiation actorInstantiation) {

        visitExpr(actorInstantiation.getIdentifier());
        for(Identifier knownActor : actorInstantiation.getKnownActors())
            visitExpr(knownActor);
        for(Expression initArg : actorInstantiation.getInitArgs())
            visitExpr(initArg);

        if(!(actorInstantiation.getIdentifier().getType() instanceof NoType)) {
            // Check Knownactor
            ArrayList<VarDeclaration> known_actors = this.get_known_actors_from_actor(new Identifier(
                    actorInstantiation.getIdentifier().getType().toString()));
            if (known_actors != null) {
                if(known_actors.size() != actorInstantiation.getKnownActors().size()){
                    System.out.printf("Line:%d:knownactors do not match with definition\n",
                            actorInstantiation.getLine());
                }
                else {
                    for (int i = 0; i < known_actors.size(); i++) {
                        if (!known_actors.get(i).getType().toString().equals(
                                actorInstantiation.getKnownActors().get(i).getType().toString()) &&
                                !(actorInstantiation.getKnownActors().get(i).getType() instanceof NoType)
                        ) if(!(this.isSubType(
                                new ActorType(new Identifier(known_actors.get(i).getType().toString())),
                                new ActorType(
                                        new Identifier(actorInstantiation.getKnownActors().get(i).getType().toString()))
                        ))) {
                            System.out.printf("Line:%d:knownactors do not match with definition\n",
                                    actorInstantiation.getLine());
                            break;
                        }
                    }
                }
            }
            // Check Initial
            ArrayList<VarDeclaration> initial_args = this.get_initial_vars_from_actor(new Identifier(
                    actorInstantiation.getIdentifier().getType().toString()));
            if(initial_args != null){
                if(initial_args.size() != actorInstantiation.getInitArgs().size()){
                    System.out.printf("Line:%d:arguments do not match with definition\n",
                            actorInstantiation.getLine());
                }
                else{
                    for(int i = 0; i < initial_args.size(); i++){
                        if(!initial_args.get(i).getType().toString().equals(
                                actorInstantiation.getInitArgs().get(i).getType().toString()) &&
                                !(actorInstantiation.getInitArgs().get(i).getType() instanceof NoType ))
                        {
                            System.out.printf("Line:%d:arguments do not match with definition\n",
                                    actorInstantiation.getLine());
                            break;
                        }
                    }
                }
            }
            else{
                if(actorInstantiation.getInitArgs().size() != 0 )
                    System.out.printf("Line:%d:arguments do not match with definition\n",
                            actorInstantiation.getLine());
            }
        }
    }

    @Override
    public void visit(UnaryExpression unaryExpression) {

        // VISITING
        visitExpr(unaryExpression.getOperand());
        //System.out.println(unaryExpression.getOperand().getType());

        if (unaryExpression.getOperand().getType() instanceof NoType)
            unaryExpression.setType(new NoType());
        else {
            if (unaryExpression.getUnaryOperator().name().equals("minus")
                    && unaryExpression.getOperand().getType() instanceof IntType)
                unaryExpression.setType(new IntType());
            else if (unaryExpression.getUnaryOperator().name().equals("not")
                    && unaryExpression.getOperand().getType() instanceof BooleanType)
                unaryExpression.setType(new BooleanType());
            else if (unaryExpression.getUnaryOperator().name().equals("preinc")
                    || unaryExpression.getUnaryOperator().name().equals("postinc")
                    || unaryExpression.getUnaryOperator().name().equals("predec")
                    || unaryExpression.getUnaryOperator().name().equals("postdec")) {
                if (unaryExpression.getOperand().getType() instanceof IntType) {
                    if (isLeftValue(unaryExpression.getOperand()))
                        unaryExpression.setType(new IntType());
                    else {
                        if(unaryExpression.getUnaryOperator().name().equals("preinc") || unaryExpression.getUnaryOperator().name().equals("postinc"))
                            System.out.println("Line:" + unaryExpression.getLine() + ":lvalue required as increment operand");
                        else
                            System.out.println("Line:" + unaryExpression.getLine() + ":lvalue required as decrement operand");
                        unaryExpression.setType(new NoType());
                    }
                } else {
                    System.out.printf("Line:%d:unsupported operand type for %s\n", unaryExpression.getLine(), unaryExpression.getUnaryOperator());
                    if (!isLeftValue(unaryExpression.getOperand())) {
                        if(unaryExpression.getUnaryOperator().name().equals("preinc") || unaryExpression.getUnaryOperator().name().equals("postinc"))
                            System.out.println("Line:" + unaryExpression.getLine() + ":lvalue required as increment operand");
                        else
                            System.out.println("Line:" + unaryExpression.getLine() + ":lvalue required as decrement operand");
                    }
                    unaryExpression.setType(new NoType());
                }
            } else {
                System.out.printf("Line:%d:unsupported operand type for %s\n", unaryExpression.getLine(), unaryExpression.getUnaryOperator());
                unaryExpression.setType(new NoType());
            }
        }
    }

    @Override
    public void visit(BinaryExpression binaryExpression) {

        visitExpr(binaryExpression.getLeft());
        visitExpr(binaryExpression.getRight());

        if ( (binaryExpression.getLeft().getType() instanceof BooleanType
                || binaryExpression.getLeft().getType() instanceof StringType
                || binaryExpression.getRight().getType() instanceof BooleanType
                || binaryExpression.getRight().getType() instanceof StringType)
                && ( binaryExpression.getBinaryOperator().name().equals("add")
                || binaryExpression.getBinaryOperator().name().equals("sub")
                || binaryExpression.getBinaryOperator().name().equals("mult")
                || binaryExpression.getBinaryOperator().name().equals("div")
                || binaryExpression.getBinaryOperator().name().equals("mod") )
        ) {
            binaryExpression.setType(new NoType());
            System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
        }
        else if (binaryExpression.getRight().getType() instanceof NoType ||
                binaryExpression.getLeft().getType() instanceof NoType) {
            binaryExpression.setType(new NoType());
        }
        else {
            switch (binaryExpression.getBinaryOperator().name()) {
                case "add":
                case "sub":
                case "mult":
                case "div":
                case "mod":
                    if (binaryExpression.getLeft().getType() instanceof IntType &&
                            binaryExpression.getRight().getType() instanceof IntType) {
                        binaryExpression.setType(new IntType());
                    } else {
                        System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                        binaryExpression.setType(new NoType());
                    }
                    break;
                case "lt":
                case "gt":
                    if (binaryExpression.getLeft().getType() instanceof IntType &&
                            binaryExpression.getRight().getType() instanceof IntType) {
                        binaryExpression.setType(new BooleanType());
                    } else {
                        System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                        binaryExpression.setType(new NoType());
                    }
                    break;
                case "and":
                case "or":
                    if (binaryExpression.getLeft().getType() instanceof BooleanType &&
                            binaryExpression.getRight().getType() instanceof BooleanType) {
                        binaryExpression.setType(new BooleanType());
                    } else {
                        System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                        binaryExpression.setType(new NoType());
                    }
                    break;
                case "eq":
                case "neq":
                    if (binaryExpression.getLeft().getType() instanceof IntType &&
                            binaryExpression.getRight().getType() instanceof IntType) {
                        binaryExpression.setType(new BooleanType());
                    } else if (binaryExpression.getLeft().getType() instanceof BooleanType &&
                            binaryExpression.getRight().getType() instanceof BooleanType) {
                        binaryExpression.setType(new BooleanType());
                    } else if (binaryExpression.getLeft().getType() instanceof StringType &&
                            binaryExpression.getRight().getType() instanceof StringType) {
                        binaryExpression.setType(new BooleanType());
                    } else if (binaryExpression.getLeft().getType() instanceof ArrayType &&
                            binaryExpression.getRight().getType() instanceof ArrayType) {
                        if (((ArrayType) binaryExpression.getLeft().getType()).getSize() == ((ArrayType) binaryExpression.getRight().getType()).getSize()) {
                            binaryExpression.setType(new BooleanType());
                        } else {
                            System.out.println("Line:" + binaryExpression.getLine() + ":operation assign requires equal array sizes");
                            binaryExpression.setType(new NoType());
                        }
                    } else if (binaryExpression.getLeft().getType() instanceof ActorType &&
                            binaryExpression.getRight().getType() instanceof ActorType) {
                        Type tmp1Type = null;
                        Type tmp2Type = null;
                        try {
                            tmp1Type = this.type_getter_from_whole_actor((Identifier) binaryExpression.getLeft());
                        } catch (ItemNotFoundException e) {
                            //System.out.println("Should never be here");
                        }
                        try {
                            tmp2Type = this.type_getter_from_whole_actor((Identifier) binaryExpression.getRight());
                        } catch (ItemNotFoundException e) {
                            //System.out.println("Should never be here");
                        }
                        assert tmp1Type != null;
                        assert tmp2Type != null;
                        if (((ActorType) tmp1Type).toString().equals(((ActorType) tmp2Type).toString())) {
                            binaryExpression.setType(new BooleanType());
                        } else {
                            binaryExpression.setType(new NoType());
                            System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                        }
                    } else {
                        binaryExpression.setType(new NoType());
                        System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                    }
                    break;
                case "assign":
                    if (binaryExpression.getLeft().getType() instanceof IntType &&
                            binaryExpression.getRight().getType() instanceof IntType)
                        binaryExpression.setType(new IntType());
                    else if (binaryExpression.getLeft().getType() instanceof BooleanType &&
                            binaryExpression.getRight().getType() instanceof BooleanType)
                        binaryExpression.setType(new BooleanType());
                    else if (binaryExpression.getLeft().getType() instanceof StringType &&
                            binaryExpression.getRight().getType() instanceof StringType)
                        binaryExpression.setType(new StringType());
                    else if (binaryExpression.getLeft().getType() instanceof ArrayType &&
                            binaryExpression.getRight().getType() instanceof ArrayType) {
                        if (((ArrayType) binaryExpression.getLeft().getType()).getSize() == ((ArrayType) binaryExpression.getRight().getType()).getSize()) {
                            binaryExpression.setType(new ArrayType(((ArrayType) binaryExpression.getLeft().getType()).getSize()));
                        } else {
                            System.out.println("Line:" + binaryExpression.getLine() + ":operation assign requires equal array sizes");
                            binaryExpression.setType(new NoType());
                        }
                    } else if (binaryExpression.getLeft().getType() instanceof ActorType &&
                            binaryExpression.getRight().getType() instanceof ActorType) {
                        if ( binaryExpression.getLeft().getType().toString().equals(binaryExpression.getRight().getType().toString())
                                || isSubType((ActorType) binaryExpression.getLeft().getType(), (ActorType) binaryExpression.getRight().getType()))
                            binaryExpression.setType(new ActorType(  ((ActorType) binaryExpression.getLeft().getType()).getName() ) );
                        else {
                            binaryExpression.setType(new NoType());
                            System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                        }
                    } else {
                        binaryExpression.setType(new NoType());
                        System.out.println("Line:" + binaryExpression.getLine() + ":unsupported operand type for " + binaryExpression.getBinaryOperator().name());
                    }
                    break;
            }
        }
    }

    @Override
    public void visit(ArrayCall arrayCall) {
        visitExpr(arrayCall.getArrayInstance());
        visitExpr(arrayCall.getIndex());
        if (arrayCall.getArrayInstance().getType() instanceof NoType
                || arrayCall.getIndex().getType() instanceof NoType) {
            arrayCall.setType(new NoType());
        }
        else if ( !(arrayCall.getIndex().getType() instanceof IntType) ) {
            arrayCall.setType(new NoType());
            System.out.println("Line:"+ arrayCall.getIndex().getLine() +":array index must be Integer type.");
        }
        else if ( !(arrayCall.getArrayInstance().getType() instanceof ArrayType) ) {
            arrayCall.setType(new NoType());
            System.out.println("Line:"+ arrayCall.getArrayInstance().getLine() +":array instance must be Array type");
        }
        else
            arrayCall.setType(new IntType());
    }

    @Override
    public void visit(ActorVarAccess actorVarAccess) {
        if(actorVarAccess == null)
            return;
        this.in_var_acc = true;
        actorVarAccess.getSelf().setLine(actorVarAccess.getLine());
        visitExpr(actorVarAccess.getSelf());
//        System.out.printf("############# %s\n", actorVarAccess.getSelf().getType());
        visitExpr(actorVarAccess.getVariable());
        this.in_var_acc = false;
        if(actorVarAccess.getSelf().getType() instanceof NoType)
            actorVarAccess.setType(new NoType());
        else
            actorVarAccess.setType(actorVarAccess.getVariable().getType());
    }

    @Override
    public void visit(Identifier identifier) {

        if(this.in_main){
            // if we are in main
            if(this.in_var_acc){

            }
            else {
                Type the_type = null;
                try {
                    // try to get the type,
                    // if the type exists check whether it's Valid Actor
                    the_type = this.type_getter_from_main(identifier);
                    try {
                        Identifier temp_id = new Identifier(the_type.toString());
                        if(!temp_id.getName().equals("notype")){
                            Type temp_type = this.type_getter_from_actor_items(temp_id);
                        }
                    } catch (ItemNotFoundException e1) {
                        System.out.printf("Line:%d:actor %s is not declared\n", identifier.getLine(), the_type.toString());
                        // set Symbol :/
                        SymbolTableVariableItem init_item = (SymbolTableVariableItem) this.cur_main_sym.getMainSymbolTable().get(
                                SymbolTableVariableItem.STARTKEY + identifier.getName());
                        init_item.getVarDeclaration().setType(new NoType());
                        the_type = new NoType();
                    }
                } catch (ItemNotFoundException e) {
                    System.out.printf("Line:%d:variable %s is not declared\n", identifier.getLine(), identifier.getName());
                    the_type = new NoType();
                }
                identifier.setType(the_type);
//            System.out.printf("In the main : %s ===> %s\n", identifier.getName(), identifier.getType());
            }
        }

        else if(this.in_actor) {
            Type the_type = null;
            if (this.in_handler) {
                if(this.in_handler_call) {
//                    try {
//                        the_type = this.type_getter_from_actor_handlers(identifier);
//                    } catch (ItemNotFoundException e) {
//                        System.out.printf("Line:%d: there is no msghandler name %s in actor %s\n",
//                                identifier.getLine(), identifier.getName(), this.cur_actor_sym.getActorDeclaration().getName().getName());
//                        the_type = new NoType();
//                    }
                    the_type = new NoType();
                }
                else if(this.in_var_acc){
//                    the_type = new NoType();
                    try{
                        the_type = this.type_getter_from_actorvars(identifier);
                    }
                    catch (ItemNotFoundException e100){
                        System.out.printf("Line:%d:variable %s is not declared\n", identifier.getLine(), identifier.getName());
                        the_type = new NoType();
                    }
                }
                else {
                    try {
                        //Exists in the whole actor
                        the_type = this.type_getter_from_whole_actor(identifier);
                        if(the_type instanceof ActorType) {
                            try{
                                Type exist_temp = this.type_getter_from_actor_items(new Identifier(the_type.toString()));
                            }
                            catch (ItemNotFoundException e8){
//                                System.out.printf("Line:%d:actor %s is not declared\n", identifier.getLine(), the_type.toString());
                                the_type = new NoType();
                            }
                        }
                    } catch (ItemNotFoundException e1) {
                        System.out.printf("Line:%d:variable %s is not declared\n", identifier.getLine(), identifier.getName());
                        the_type = new NoType();
                    }
                }
            }
            else {
                try {
                    the_type = this.type_getter_from_act(identifier);
                    if(the_type instanceof ActorType) {
                        try{
                            Type exist_temp = this.type_getter_from_actor_items(new Identifier(the_type.toString()));
                        }
                        catch (ItemNotFoundException e8){
                            System.out.printf("Line:%d:actor %s is not declared\n", identifier.getLine(), the_type.toString());
                            the_type = new NoType();
                        }
                    }
                } catch (ItemNotFoundException e2) {
                    System.out.printf("Line:%d:variable %s is not declared\n", identifier.getLine(), identifier.getName());
                    the_type = new NoType();
                }
            }
            identifier.setType(the_type);
//            System.out.printf("In the actor : %s ===> %s\n", identifier.getName(), identifier.getType());
        }

        else{
            Type the_type = null;
            try {
                the_type = this.type_getter_from_actor_items(identifier);
            }
            catch (ItemNotFoundException e3) {
                System.out.printf("Line:%d:actor %s is not declared\n", identifier.getLine(), identifier.getName());
                the_type = new NoType();
            }
            identifier.setType(the_type);
//            System.out.printf("In the decs : %s ===> %s\n", identifier.getName(), identifier.getType());
        }


        // CODE GENERATION STUFF
        if (!this.in_var_dec && !this.is_left_val) {

            if (this.in_handler) {
                if (this.curr_msghndlr_vars.containsKey(identifier.getName())) {
                    if (identifier.getType() instanceof IntType || identifier.getType() instanceof BooleanType) {
                        // TODO: iload index
                    }
                    else {
                        // TODO: aload index
                    }
                } else {
                    // TODO: getfiled
                }
            }
            else if (this.in_main) {
                // TODO: aload index
            }
        }
    }

    @Override
    public void visit(Self self) {
        if(this.in_main){
            System.out.printf("Line:%d:self doesn't refer to any actor\n", self.getLine());
            self.setType(new NoType());
        }
        else{
            self.setType(new ActorType(new Identifier(this.cur_actor_sym.getActorDeclaration().getName().getName())));
        }
    }

    @Override
    public void visit(Sender sender) {
        if(this.in_main){
            sender.setType(new NoType());
            System.out.printf("Line:%d:sender doesn't refer to any actor\n", sender.getLine());
        }else {
            Identifier tmp = new Identifier("sender");
            sender.setType(new ActorType(tmp));
        }
        if (isInitHandler)
            System.out.println("Line:"+ sender.getLine() +":no sender in initial msghandler");
    }

    @Override
    public void visit(BooleanValue value) {
        value.setType(new BooleanType());
    }

    @Override
    public void visit(IntValue value) {
        value.setType(new IntType());
    }

    @Override
    public void visit(StringValue value) {
        value.setType(new StringType());
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
        if (conditional.getExpression() != null && !(conditional.getExpression().getType() instanceof BooleanType)
                && !(conditional.getExpression().getType() instanceof NoType))
            System.out.println("Line:"+conditional.getExpression().getLine() + ":condition type must be boolean");
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

        if ( loop.getCondition() != null && !(loop.getCondition().getType() instanceof BooleanType)
                && !(loop.getCondition().getType() instanceof NoType) )
            System.out.println("Line:"+ loop.getLine() +":condition type must be Boolean");

        if (loop.getUpdate() != null)
            visitStatement(loop.getUpdate());

        visitStatement(loop.getBody());
        this.in_for = false;
    }

    @Override
    public void visit(Break breakLoop) {

        if(!this.in_for)
            System.out.printf("Line:%d:break statement not within loop\n", breakLoop.getLine());
    }

    @Override
    public void visit(Continue continueLoop) {
        if(!this.in_for)
            System.out.printf("Line:%d:continue statement not within loop\n", continueLoop.getLine());
    }

    @Override
    public void visit(MsgHandlerCall msgHandlerCall) {

        if(msgHandlerCall == null) {
            return;
        }
        try {
            visitExpr(msgHandlerCall.getInstance());
            this.in_handler_call = true;
            visitExpr(msgHandlerCall.getMsgHandlerName());
            this.in_handler_call = false;
            for (Expression argument : msgHandlerCall.getArgs())
                visitExpr(argument);
        }
        catch(NullPointerException npe) {
            System.out.println("null pointer exception occurred");
        }
        this.in_handler_call = false;
        // ERROR HANDLING
//        System.out.printf("START MSG CALL %s------------------------------------\n", msgHandlerCall.getInstance());
        //Check whether the Instance type is an ActorType as the same as the MsgHandlerName
//        System.out.printf("################# %s\n", msgHandlerCall.getInstance().getType().toString());
        if(!(msgHandlerCall.getInstance().getType().toString().equals("sender"))) {
            if ((msgHandlerCall.getInstance().getType() instanceof ActorType)) {
                Type the_type = null;
                try { // Check if the Instance has the msg handler or not!
                    the_type = this.type_getter_from_actor_handlers(
                            (Identifier) msgHandlerCall.getMsgHandlerName(),
                            (Identifier) ((ActorType) msgHandlerCall.getInstance().getType()).getName(),
                            msgHandlerCall.getArgs());
                } catch (Exception e) { // if not! : Error
                    if (e instanceof ArgsDoNotMatch) {
                        System.out.printf("Line:%d:arguments do not match with definition\n",
                                msgHandlerCall.getLine(), ((Identifier) msgHandlerCall.getMsgHandlerName()).getName(),
                                (msgHandlerCall.getInstance().getType())
                        );
                    } else {
                        System.out.printf("Line:%d:there is no msghandler name %s in actor %s\n",
                                msgHandlerCall.getLine(), ((Identifier) msgHandlerCall.getMsgHandlerName()).getName(),
                                (msgHandlerCall.getInstance().getType())
                        );
                    }
                }
            } else {
                if (msgHandlerCall.getInstance().getType() instanceof NoType) {
                    //TODO:NEW ERROR
//                System.out.printf("Line:%d:variable %s is not clearly defined as a valid actor!\n",
//                        msgHandlerCall.getLine(), ((Identifier)msgHandlerCall.getInstance()).getName());
                } else {
                    System.out.printf("Line:%d:variable %s is not callable\n", msgHandlerCall.getLine(),
                            ((Identifier) msgHandlerCall.getInstance()).getName());
                }
            }
        }

//        System.out.printf("END OF MSG CALL---------------------------------------\n");
    }

    @Override
    public void visit(Print print) {
        if(print == null)
            return;
        visitExpr(print.getArg());
        if( !( print.getArg().getType() instanceof IntType ||
                print.getArg().getType() instanceof StringType ||
                print.getArg().getType() instanceof BooleanType ||
                print.getArg().getType() instanceof ArrayType  ||
                print.getArg().getType() instanceof NoType ) ) {
            System.out.println("Line:" + print.getLine() +":unsupported type for print");
        }

    }

    @Override
    public void visit(Assign assign) {
        this.in_assign = true;
        if ( !isLeftValue(assign.getlValue()) )
            System.out.println("Line:" + assign.getLine() +":left side of assignment must be a valid lvalue");

        this.is_left_val = true;
        visitExpr(assign.getlValue());
        this.is_left_val = false;
        visitExpr(assign.getrValue());
        if ( (assign.getlValue().getType().toString().equals("sender") && assign.getrValue().getType() instanceof ActorType)
                || (assign.getrValue().getType().toString().equals("sender") && assign.getlValue().getType() instanceof ActorType) ) {}
        else {
            if (!(assign.getlValue().getType() instanceof NoType || assign.getrValue().getType() instanceof NoType)) {
                if (assign.getlValue().getType() instanceof ArrayType &&
                        assign.getrValue().getType() instanceof ArrayType) {
                    if (((ArrayType) assign.getlValue().getType()).getSize() != ((ArrayType) assign.getrValue().getType()).getSize()) {
                        System.out.println("Line:" + assign.getLine() + ":operation assign requires equal array sizes");
                    }
                } else if (assign.getlValue().getType() instanceof ActorType &&
                        assign.getrValue().getType() instanceof ActorType) {
                    if (!assign.getlValue().getType().toString().equals(assign.getrValue().getType().toString())) {
                        if (!isSubType((ActorType) assign.getlValue().getType(), (ActorType) assign.getrValue().getType()))
                            System.out.println("Line:" + assign.getLine() + ":unsupported operand type for assign");
                    }
                } else if (!assign.getlValue().getType().toString().equals(assign.getrValue().getType().toString()))
                    System.out.println("Line:" + assign.getLine() + ":unsupported operand type for assign");
            }
        }
        this.in_assign = false;
    }
}