%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 25 Jul 19   */

/* Copyright (c) 2019 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */
/* 30 Jul 13 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"
#include "codegen.h"
#include <string.h>

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;
void dbuginyacc();
int getval(TOKEN consttok);
TOKEN makenil(TOKEN nil);

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%%

program    :PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON lblock DOT 
                { parseresult = makeprogram($2,makeprogn($3,$4),$7);}
           ;
  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  assignment
             |  FOR assignment TO expr DO statement {$$ = makefor(1,$1,$2,$3,$4,$5,$6); }
             |  funcall
             |  REPEAT statement_list UNTIL expr {$$ = makerepeat($1,$2,$3,$4);}
             | WHILE expr DO statement {$$ = makewhile($1,$2,$3,$4);}
             | label
             | GOTO NUMBER {$$ = dogoto($1,$2);}
             ;
  statement_list : statement SEMICOLON statement_list {$$ = makeprogn($2,cons($1,$3));}
             | statement {$$ = cons($1,NULL);}
             |           {$$ = NULL;}
             ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
  assignment :  variable ASSIGN expr           { $$ = binop($2, $1, $3); }
             ;
  expr       :  expr compare_op simple_expr    { $$ = binop($2, $1, $3); }
             |  simple_expr 
             ;
  term       :  term TIMES factor              { $$ = binop($2, $1, $3); }
             |  factor
             ;
  factor     : unsigned_constant
             | variable
             | funcall
             | LPAREN expr RPAREN             { $$ = $2; }
             | NOT funcall
             ;
  id_list    : IDENTIFIER COMMA id_list {$$ = cons($1,$3);}
             | IDENTIFIER {$$ = cons($1,NULL);}
             ;
  lblock     : LABEL numgroup SEMICOLON cblock {$$ = $4;}
             | cblock
             ;
  numgroup   : numlist {instlabel($1);}
             ;
  numlist    : NUMBER numlist   {$$ = cons($1,$2);}
             | COMMA numlist    {$$ = $2;}
             |                  {$$ = NULL;}
             ;
  cblock     : CONST cdef_list tblock {$$ = $3;}
             | tblock
             ;
  cdef_list  : cdef SEMICOLON cdef_list 
             | cdef SEMICOLON
             ;
  cdef       : IDENTIFIER EQ constant {instconst($1,$3);}
             ;
  tblock     : TYPE tdef_list vblock { $$ = $3;}
             | vblock
             ;
  tdef_list  : tdef SEMICOLON tdef_list
             | tdef SEMICOLON
             ;
  tdef       : IDENTIFIER EQ type {insttype($1,$3);}
             ;
  vblock     : VAR varspecs block {$$ = $3;}
             | block
             ;          
  varspecs   : vargroup SEMICOLON varspecs
             | vargroup SEMICOLON
             ;
  vargroup   : id_list COLON type {instvars($1,$3);}
             ;
  block      : BEGINBEGIN statement endpart { $$ = makeprogn($1,cons($2, $3)); }
             ;
  constant   : IDENTIFIER | NUMBER | STRING
             ;
  type       : simpletype
             | ARRAY LBRACKET simple_type_list RBRACKET OF type {$$ = instarray($3,$6);}
             | RECORD field_list END {$$ = instrec($1,$2);}
             | POINT IDENTIFIER  {$$ = instpoint($1,$2);}
             ;
  fields     : id_list COLON type {$$ = instfields($1,$3);}
             ;
  field_list : fields SEMICOLON field_list {$$ = nconc($1,$3);}
             | fields  {$$ = nconc(NULL,$1);}
             ;
  variable   : IDENTIFIER {$$ = findid($1);}
             | variable LBRACKET expr_list RBRACKET {$$ = arrayref($1,$2,$3,$4);}
             | variable DOT IDENTIFIER {$$ = reducedot($1,$2,$3);}
             | variable POINT {$$ = dopoint($1,$2);}
             ;
  simpletype : IDENTIFIER {$$ = findtype($1);}
             | LPAREN id_list RPAREN {$$ = instenum($2);}
             | constant DOTDOT constant {$$ = makesubrange($2,getval($1),getval($3));}
             ;
  simple_type_list : simpletype COMMA simple_type_list {$$ = cons($1,$3);}
             | simpletype {$$ = cons($1,NULL);}
             ;
  funcall    : IDENTIFIER LPAREN expr RPAREN {$$ = makefuncall($2,$1,$3);}
             ;
  unsigned_constant : IDENTIFIER | STRING | NIL {$$ = makenil($1);} | NUMBER
                    ;
  sign       : PLUS | MINUS
             ;
  simple_expr: sign term {$$ = binop($1,$2,NULL);}
             | term
             | simple_expr plus_op term {$$ = binop($2,$1,$3);}
             ;
  compare_op : EQ | LT | GT | NE | LE | GE | IN
             ;
  plus_op    : PLUS | MINUS | OR
             ;
  expr_list  : expr COMMA expr_list {$$ = cons($1,$3);}
             | expr {$$ = cons($1,NULL);}
             ;
  label      : NUMBER COLON statement {$$ = dolabel($1,$2,$3);}
             ;

%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        31             /* set bits here for debugging, 0 = off  */
#define DB_CONS       0             /* bit to trace cons */
#define DB_NCONS      0             /*bit to trace ncons*/
#define DB_BINOP      5             /* bit to trace binop */
#define DB_MAKEIF     21            /* bit to trace makeif */
#define DB_MAKEPROGN  0            /* bit to trace makeprogn */
#define DB_MAKEPROGRAM 0            /* bit to trace makeprogram*/
#define DB_MAKEINTC 0             /* bit to trace makeint*/
#define DB_MAKELABEL 0            /* bit to trace makelabel*/
#define DB_MAKEFOR   0             /* bit to trace makefor*/
#define DB_MAKEFUNCALL 2           /*bit to trace makefuncall*/
#define DB_INSTVARS 0              /*bit to trace instvars*/
#define DB_INSTCONST 0             /*bit to trace instconst*/
#define DB_INSTLABEL  0             /*bit to trace instlabvel*/
#define DB_INSTFIELDS 0            /*bit to trace instfields*/
#define DB_INSTREC    0            /*bit to trace instrec*/
#define DB_INSTYPE     0           /*bit to trace instrec*/
#define DB_INSTENUM     0           /*bit to trace instenum*/
#define DB_INSTARRAY    0          /*bit to trace instarray*/
#define DB_INSTPOINT    0         /*bit to trace instpoint*/
#define DB_FINDID 0                /*bit to trace findid*/
#define DB_FINDTYPE 0             /*bit to trace findtype*/
#define DB_MAKEREPEAT 0           /*bit to trace makerepeat*/
#define DB_MAKEFLOAT 0              /*bit to trace makefloat*/
#define DB_MAKEFIX   0              /*bit to trace makefix*/
#define DB_MAKESUB   0              /*bit to tace makesubrange*/
#define  DB_INHERIT 0               /*bit to trace inherit*/
#define DB_DOPOINT   0             /*bit to trace do point*/
#define DB_DOLABEL    0            /*bit to trace do label*/
#define DB_DOGOTO     0            /*bit to trace dogoto*/
#define DB_REDUCEDOT  0            /*bit to trace reducedot*/
#define DB_ARRAYREF   0            /*bit to trace arrayref*/
#define DB_PARSERES  23             /* bit to trace parseresult */

  int labelnumber = 0;  /* sequential counter for internal label numbers */
  int labels[MAXBLOCKS] = {}; /* array for user labels */ 
   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

/* nconc concatenates two token lists, destructively, by making the last link
   of lista point to listb.
   (nconc '(a b) '(c d e))  =  (a b c d e)  */
/* nconc is useful for putting together two fieldlist groups to
   make them into a single list in a record declaration. */
/* nconc should return lista, or listb if lista is NULL. */
TOKEN nconc(TOKEN lista, TOKEN listb)
  { 
    if (lista == NULL){
      if (DEBUG & DB_NCONS){printf("lista a is null: ");printf("ncons\n"); dbugprinttok(listb);}
      return listb;
    }
    TOKEN posa = lista;
    /* reach the end of list a*/
    while (posa->link != NULL){
      posa = posa->link;
    }
    /* link the end of lista tok and its symbolentry */
    posa->link = listb;
    posa->symentry->link = listb->symentry;
    if (DEBUG & DB_NCONS)
       { printf("ncons\n");
         dbugprinttok(lista);
         dbugprinttok(listb);
       };
    return lista;
  }
/*Assigns operand type based on children*/
void opinheritance(TOKEN op,TOKEN children){
  /* it is safe to assume that at this point both children shoyld be same type*/
  op->basicdt = children->basicdt;
  if (DEBUG & DB_INHERIT){
    printf("op inheritance\n");
    dbugprinttok(op);
    dbugprinttok(children);
  }
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { 
    /*same type*/
    if ( rhs!=NULL && rhs->basicdt==lhs->basicdt){
      op->operands = lhs;          /* link operands to operator       */
      lhs->link = rhs;             /* link second operand to first    */
      rhs->link = NULL;                           /* terminate operand list          */
    }
    /*different types*/
    else {
      /*coerce rhs according to what lhs is*/
      if (op->whichval == ASSIGNOP){
        if (lhs->basicdt == REAL){
          rhs = makefloat(rhs);
        }
        else{
          rhs = makefix(rhs);
        }
        op->operands = lhs;
        lhs->link = rhs;
      }
      /*NOTE: there has to be a better way to implement this */
      else if (op->whichval == MINUSOP){
        op->operands = lhs;
        lhs->link = rhs;
      }
      /*TODO: make it work with more operators
      - maybe use a switch table and helper function next time*/
      else if (op->whichval == PLUSOP ||
        op->whichval == TIMESOP  ){
          TOKEN coerce,floatop;
          /*TODO: you might have to deal with different types, right now only
          works on INTS TO FLOATS*/
          coerce = lhs->basicdt < rhs->basicdt ? lhs:rhs;
          floatop = makefloat(coerce);
          /*NOTE: possible memory leak if makefloat gets const*/
          op->operands = coerce == lhs ? floatop:lhs;
          if (lhs == coerce){
            (floatop->link = rhs);
          }
          else {
            lhs->link = floatop;
          }
        }
    }
    opinheritance(op,op->operands);
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(op->operands);
         dbugprinttok(rhs);
         ppexpr(op);
       };
    return op;
  }

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

/* */
TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
        //  printf("printing tree---------------\n");
        //  ppexpr(tok);
        //  printf("----------------------------\n");
       };
     opinheritance(tok,statements);
     return tok;
   }

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements)
  { 
    name->link = args;
    args->link = statements; /*args is a progn with the args as the operands*/
    if (DEBUG & DB_MAKEPROGRAM)
       { printf("makeprogram\n");
         dbugprinttok(name);
         dbugprinttok(args);
         dbugprinttok(statements);
       };
    /* create program op*/
    TOKEN program = makeop(PROGRAMOP);
    program -> operands = name;
    return program;
  }

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement)
  { 
    /* increment labelnumber and create label and numbertok
        assign numbertok to label as operand */
    int j = labelnumber++;
    TOKEN numtok = makeintc(j);
    TOKEN label = makelabel();
    label->operands = numtok;

    /* link label to assignment tok */
    asg->link= label;

    /* make if statement */
    TOKEN expression_i = copytok(asg->operands); /* copy token for i */

    /* make <= operand and if statement */
    TOKEN leopToken = makeop(LEOP);
    tokc = makeprogn(tokc,statement);
    leopToken = binop(leopToken,expression_i,endexpr); /*expression*/
    tokb = makeif(tokb,leopToken,tokc,NULL); /*tokb is if operator*/

    /* build increment logic */
    TOKEN inclogic = makeop(ASSIGNOP);
    TOKEN plus = makeop(PLUSOP);    
    TOKEN funcall_i = copytok(asg->operands);
    funcall_i->link=binop(plus,copytok(asg->operands),makeintc(1));
    inclogic->operands = funcall_i;
    
    /*connect everything here*/
    inclogic->link = makegoto(j);
    /* add the assig link at the end of statement chain */
    TOKEN current = statement;
    while (current->link!=NULL){
      current = current->link;
    }
    current->link = inclogic;

    label->link= tokb;
    tok = makeprogn(tok,asg);

    if (DEBUG & DB_MAKEFOR)
      { printf("makefor\n");
        dbugprinttok(tok);
        dbugprinttok(tokb);
        dbugprinttok(tokc);
        dbugprinttok(statement);
      };
    return tok;
  }

/* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr)
  {
    int j = labelnumber++;
    TOKEN numtok = makeintc(j);
    TOKEN label = makelabel();
    label->operands = numtok;

    label->link = statements;
    TOKEN makeif_statements = copytok(statements);
    tokb = makeif(tokb,expr,makeif_statements,NULL);
    TOKEN curr = statements;
    while (curr->link != NULL){
      curr = curr->link;
    }
    curr->link = tokb;
    makeif_statements->link = makegoto(j);
    tok = makeprogn(tok,label); /* create progn, will be returned tok */
    if (DEBUG & DB_MAKEREPEAT)
    { printf("makerepeat\n");
      dbugprinttok(label);
      dbugprinttok(tok);
      dbugprinttok(tokb);
    };
    return tok;

  }

/* makeintc makes a new integer number token with num as its value */
TOKEN makeintc(int j){
  TOKEN tok = talloc();
  tok->tokentype = NUMBERTOK;
  tok->intval = j;
  tok->basicdt = INTEGER;
  if (DEBUG & DB_MAKEINTC)
    { printf("makeintc\n");
      dbugprinttok(tok);
    };
  return tok;
}

/* makefloat forces the item tok to be floating, by floating a constant
   or by inserting a FLOATOP operator */
TOKEN makefloat(TOKEN tok){
  TOKEN floatop = talloc();
  /*NOTE: this might not be the best way to check for symbol. ask ta*/
  if (tok->symentry != NULL && tok->symentry->kind == CONSTSYM || tok->tokentype == NUMBERTOK){
    floatop->tokentype = NUMBERTOK;
    floatop->realval = tok->intval;
    floatop->basicdt = REAL;
  }
  else{
    floatop->tokentype = OPERATOR;
    floatop->whichval = FLOATOP;
    floatop->basicdt = REAL;
    floatop->operands = tok;
  }
  if (DEBUG & DB_MAKEFLOAT)
  { printf("makefloat\n");
    dbugprinttok(tok);
  };
  return floatop;
}

/* makefix forces the item tok to be integer, by truncating a constant
   or by inserting a FIXOP operator */
TOKEN makefix(TOKEN tok){
  TOKEN fixop = talloc();
  if (tok->symentry != NULL && tok->symentry->kind == CONSTSYM){
    fixop->tokentype = NUMBERTOK;
    fixop->intval = tok->realval;
    fixop->basicdt = INTEGER;
  }
  else{
    fixop->tokentype = OPERATOR;
    fixop->whichval = FIXOP;
    fixop->basicdt = INTEGER;
    fixop->operands = tok;
  }
  if (DEBUG & DB_MAKEFIX)
  { printf("makefix\n");
    dbugprinttok(tok);
  };
  return fixop;
}

/* makelabel makes a new label, using labelnumber++ */
TOKEN makelabel(){
  TOKEN label = talloc();
  label->tokentype = OPERATOR;
  label->whichval = LABELOP;
  label->basicdt = INTEGER;
  if (DEBUG & DB_MAKELABEL)
    { printf("makelabel\n");
      dbugprinttok(label);
    };
  return label;
}
int specialfun(TOKEN fn, TOKEN args)
  { 
    char writeln[] = "writeln";
    char writelni[] = "writelni";
    char writelnf[] = "writelnf";
    char newfn[] = "new";
    /* writeln function, only change the string name*/
    if (!strcmp(fn->stringval,writeln)){
      if (args->basicdt == INTEGER){
        strcpy(fn->stringval,writelni);
      }
      if(args->basicdt == REAL){
        strcpy(fn->stringval,writelnf);
      }
      return 0;
    }
    /*new fn rearranges flag in makefuncall*/
    if (!strcmp(fn->stringval,newfn)){
      return 1;
    }
    return 0;
  } 
/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args)
  { 
    int newfun;
    TOKEN temp;
    SYMBOL sym;
    /*recycle tok and make it into funcallop*/
    tok->tokentype=OPERATOR;
    tok->whichval=FUNCALLOP;
    /* check if fn is a special fn like writeln or new*/
    if ((newfun= specialfun(fn,args))){
      sym = args->symtype; /*pointersym*/
      dbprsymbol(sym);
      sym = sym->datatype; /*typesym*/
      dbprsymbol(sym);
      temp = args; /* temp now holds the name of the args*/
      args = makeintc(sym->datatype->size); /*recordsym->size*/
    }
    fn = findtype(fn); /*find type for function and its basic id*/
    /*link function to its arguments*/
    fn->link = args;
    /*add opperands to funcop*/
    tok->operands=fn;
    opinheritance(tok,fn);
    if (DEBUG & DB_MAKEFUNCALL)
    { printf("makefuncall\n");
      dbugprinttok(fn);
      dbugprinttok(tok);
      dbugprinttok(args);
      if(newfun){printf("newfun was made\n");}
      ppexpr(tok);
    }
    /* only new fun needs this exception*/
    if (newfun){
      TOKEN asgn = makeop(ASSIGNOP);
      asgn->operands = temp;
      temp->link = tok;
      opinheritance(asgn,temp);
      return asgn;
    }

    return tok;
  }

/* makegoto makes a GOTO operator to go to the specified label.
   The label number is put into a number token. */
TOKEN makegoto(int label)
  {
    TOKEN goto_tok = talloc();
    goto_tok->tokentype=OPERATOR;
    goto_tok->whichval=GOTOOP;
    goto_tok->basicdt=INTEGER;
    goto_tok->operands=makeintc(label);

    return goto_tok;
  }

/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum)
  {
    TOKEN newTok = talloc();
    newTok->tokentype=OPERATOR;
    newTok->basicdt=INTEGER;
    newTok->whichval=opnum;
    return newTok;
  }

TOKEN makenil(TOKEN nil){
  nil->tokentype = NUMBERTOK;
  nil->basicdt = POINTER;
  nil->intval = 0;
  return nil;
}

/* instvars will install variables in symbol table.
   typetok is a token containing symbol table pointer for type. */
void  instvars(TOKEN idlist, TOKEN typetok)
  { 
    SYMBOL sym, typesym; int align;
    typesym = typetok->symtype;
    align = alignsize(typesym);
    while ( idlist != NULL ) /* for each id */
    { sym = insertsym(idlist->stringval); sym->kind = VARSYM;
    sym->offset = /* "next" */
                  wordaddress(blockoffs[blocknumber],
                              align);
    sym->size = typesym->size; blockoffs[blocknumber] = /* "next" */
    sym->offset + sym->size; sym->datatype = typesym;
    sym->basicdt = typesym->basicdt;
    idlist = idlist->link;};

    if (DEBUG & DB_INSTVARS)
    { printf("instvars called\n");
      dbugprinttok(idlist);
      dbugprinttok(typetok);
      dbprsymbol(typesym);
    }
  }

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high)
  {
    SYMBOL sym;
    sym = makesym("subrange");
    sym->kind = SUBRANGE;
    sym->basicdt = INTEGER;
    sym->lowbound = low;
    sym->highbound = high;
    sym->size = basicsizes[INTEGER];
    tok->symtype = sym;
    if (DEBUG & DB_MAKESUB)
    { printf("makesubrange\n");
      dbugprinttok(tok);
      dbprsymbol(sym);
      printf("low: %d\n", low);
      printf("high: %d\n",high);
    }
    return tok;
  }

/* makearef makes an array reference operation.
   off is be an integer constant token
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok)
  {
    
    return var;
  }

  /* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement)
  { 
    /*create label*/
    int j = labelnumber++;
    TOKEN numtok = makeintc(j);
    TOKEN label = makelabel();
    label->operands = numtok;

    tokb = makeif(tokb,expr,statement,NULL);
    /* add goto to end of statements*/ 
    TOKEN pos = statement->operands;
    while (pos->link != NULL){
      pos = pos->link;
    }
    pos->link = makegoto(j);

    label->link = tokb;
    tok = makeprogn(tok,label);
    if (DEBUG & DB_MAKESUB)
      { printf("makewhile\n");
        dbugprinttok(tok);
        dbugprinttok(expr);
        dbugprinttok(tokb);
        dbugprinttok(statement);
      }

    return tok;
  }

/* arrayref processes an array reference a[i]
   subs is a list of subscript expressions.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb)
  { 
    
    SYMBOL type;
    TOKEN offsettok = NULL;
    int off, datasize,lowbound;
    /* turn tok into the aref tok*/
    tok->tokentype = OPERATOR;
    tok->whichval = AREFOP;
    
    arr = findtype(arr);
    lowbound = ((arr->symtype)->datatype)->lowbound;
    type = ((arr->symtype)->datatype)->datatype;
    arr ->symtype = type; /*point directly to the datatype*/

    off = 0;
    datasize = type->size;
    lowbound = (-1 * lowbound) * datasize;
    printf("first tok of subs\n");
    dbugprinttok(subs);

    while (subs != NULL){
      subs = findtype(subs);
      printf("subs intval %d\n",subs->intval);
      if (subs->tokentype == NUMBERTOK){
        if(offsettok!= NULL){
          offsettok->operands->intval += ((subs->symentry->size)*(subs->intval));
        }
        else{
          int index = subs->intval;
          off += index * datasize;
          off += lowbound;
          printf("off = %d\n",off);
        }
      }
      /* token is a var i.e i*/
      else if (subs->tokentype == IDENTIFIERTOK){
        if (offsettok == NULL){
          TOKEN timestok = makeop(TIMESOP);
          timestok -> operands = makeintc(datasize);
          timestok->operands->link = subs;

          offsettok = makeop(PLUSOP);
          offsettok->operands = makeintc(lowbound);
          offsettok->operands->link = timestok;
        }
      }
      subs = subs->link;
    }
    tok->operands = arr;
    tok->symtype = type;
    tok->basicdt = type->basicdt;
    tokb =  offsettok == NULL ? fillintc(tokb,off):offsettok; /*CHANGETHIS*/
    arr->link = tokb;

    if (DEBUG & DB_ARRAYREF){
      printf("arrayref\n");
      dbugprinttok(tok);
      dbugprinttok(arr);
      dbugprinttok(tokb);
      dbprsymbol(type);
      ppexpr(tok);
    }
    return tok;
  }

/* instconst installs a constant in the symbol table */
void  instconst(TOKEN idtok, TOKEN consttok)
  { 
    SYMBOL sym,typ;
    sym = insertsym(idtok->stringval);
    sym->kind = CONSTSYM;
    sym->basicdt = consttok->basicdt;
    /*sym->datatype = typ;*/
    /* this only covers reals and ints. Needs to be changed!!! */
    if (consttok->basicdt == REAL){
      sym->constval.realnum = consttok->realval;
      sym->size = basicsizes[REAL];
    }
    else{
      sym->constval.intnum = consttok->intval;
      sym->size = basicsizes[INTEGER];
    }
    
    if (DEBUG & DB_INSTCONST){
      printf("instconst\n");
      dbugprinttok(idtok);
      dbugprinttok(consttok);
      dbprsymbol(sym);
    }
  }

/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num){
  /* num has all other label toks numbers linked */
  TOKEN pos = num;
  int start = labelnumber;
  while(pos != NULL){
    labels[labelnumber++] = pos->intval;
    pos = pos->link;
  }
  if (DEBUG & DB_INSTLABEL)
    { printf("instlabel\n");
      for (start; start < labelnumber; start ++){
        printf("label value: %d\n",labels[start]);
      }
    }
}
/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void  insttype(TOKEN typename, TOKEN typetok)
  {
    SYMBOL toinsertsym;
    toinsertsym = searchins(typename->stringval);
    toinsertsym->kind = TYPESYM;
    toinsertsym->datatype = typetok->symtype;
    toinsertsym->size = typetok->symtype->size;
    if (DEBUG & DB_INSTYPE){
      printf("insttype\n");
      dbugprinttok(typetok);
      dbprsymbol(typetok->symtype);
    }
  }

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type.  rectok is just a trash token to be
   used to return the result in its symtype */
TOKEN instrec(TOKEN rectok, TOKEN argstok)
  {
    int align,totalsize = 0;
    SYMBOL recsym = symalloc(),symentries;
    /*fix up the record symbol*/
    recsym->kind = RECORDSYM;
    recsym->datatype = argstok->symentry; /*symentry should have all fields linked*/
    /*find size and then pad it*/
    while (argstok != NULL){
      symentries = argstok->symentry;
      /*get offset now that all fields are connected
      totalsize is "base address"*/
      align = alignsize(symentries->datatype); 
      symentries->offset = wordaddress(totalsize,align);
      /*update for next position*/
      totalsize = symentries->size + symentries->offset;
      argstok = argstok->link;
    }
    totalsize = wordaddress(totalsize,RECORDALIGN*2);
    /*RECORDALIGN * 2 = 16*/
    if (totalsize < (RECORDALIGN*2)) (totalsize = RECORDALIGN*2);
    recsym->size = totalsize;
    rectok->symtype = recsym;

    if (DEBUG & DB_INSTREC){
      printf("instrec\n");
      printf("symentries size: %d\n", recsym->size);
      dbugprinttok(rectok);
      dbugprinttok(argstok);
      dbprsymbol(rectok->symtype);
    }
    return rectok;
  }

/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok)
  {
    SYMBOL sym,typesym,prevsym = NULL;
    TOKEN pos = idlist;
    int align;
    typesym = typetok->symtype;
    align = alignsize(typesym);

    /*go through fields and creat a sym. Assign its correspoding fields*/
    while (pos != NULL){
      /*get sym and link the previous sym if it isnt null*/
      sym = makesym(pos->stringval);
      if (prevsym != NULL) (prevsym->link  = sym);
      /*TODO: check whether to add kind to the sym, if so what kind?*/
      sym->datatype = typetok->symtype;
      sym->size = typesym->size; 
      sym->datatype = typesym;
      sym->basicdt = typesym->basicdt;
      printf("BASICDT OF FILED FROM TYPESYM %d \n",sym->basicdt);           

      prevsym = sym;
      pos->symentry = sym;
      pos = pos->link;
    }
    if (DEBUG & DB_INSTFIELDS){
      printf("instfields\n");
      TOKEN dbuglist = idlist;
      while (dbuglist != NULL){
        dbugprinttok(dbuglist);
        dbuglist = dbuglist->link;
      }
      dbugprinttok(typetok);
    }
    return idlist;
  }

/* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist)
  {
    int low,high;
    TOKEN subtoken;
    low = 0;
    high = 0;
    subtoken = idlist;
    /*go trough id and creat a const, keep count of lo-hi bound*/
    while (idlist != NULL){
      instconst(idlist,makeintc(high));
      high++;
      idlist = idlist->link;
    }
    return makesubrange(subtoken,low,high-1);
  }
/* instpoint will install a pointer type in symbol table, 
  tok contains pointer to symentry*/
TOKEN instpoint(TOKEN tok, TOKEN typename)
  {
    SYMBOL pointer;
    /*doesnt install into symbol table. THIS MIGHT BNE WRONG.*/
    pointer = makesym(typename->stringval);
    pointer->kind = POINTERSYM;
    pointer->size = basicsizes[POINTER];
    /* assign pointer to name of the type pointed to */
    pointer->datatype = searchins(typename->stringval);
    pointer->basicdt = POINTER;
    tok->symtype = pointer;
     if (DEBUG & DB_INSTPOINT){
      printf("instpoint\n");
      dbugprinttok(tok);
      dbugprinttok(typename);
      dbprsymbol(pointer);
    }

    return tok;
  }
/* helpe function that calculates total size for instarray*/
int gettotalsize(int lo, int hi, int size)
  {
    if (DEBUG & DB_INSTARRAY){
      printf("gettotalsize\n");
      printf("lo = %d, hi = %d, size of type = %d\n",lo,hi,size);
    }
    return (hi - lo + 1) * size;

  }
/*extract int value from tok*/
int getval(TOKEN consttok)
  {return consttok->intval;}

/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok)
  {
    SYMBOL arraysym,subrange,typesym; 
    /*first array*/
    subrange = bounds->symtype;
    arraysym = makesym(typetok->stringval);
    arraysym->kind = ARRAYSYM;
    arraysym->lowbound = subrange->lowbound;
    arraysym->highbound = subrange->highbound;
    /* it is a array of array, get the next arraysym*/
    if (bounds->link != NULL){
      typesym = (instarray(bounds->link,typetok))->symtype;
      arraysym->datatype = typesym;
      arraysym->size = gettotalsize(subrange->lowbound,subrange->highbound,typesym->size);
      printf("size of array: %d\n", arraysym->size);
      typetok->symtype = arraysym;
    }
    /*only array to type reference*/
    else{
      typesym = typetok->symtype;
      arraysym->datatype = typesym;
      arraysym->size = gettotalsize(subrange->lowbound,subrange->highbound,typesym->size);
      printf("size of array: %d\n", arraysym->size);
      typetok->symtype = arraysym;
    }

    if (DEBUG & DB_INSTARRAY){
      printf("instarray\n");
      dbugprinttok(typetok);
      dbprsymbol(arraysym);
      printf("array low = %d\n", arraysym->lowbound);
      printf("array high = %d\n", arraysym->highbound);
    }

    return typetok;
  }
/* helps in smashing for const toks,determines the typ of val to assign */
/* TODO: change this to handle other basicdt*/
void assignval(TOKEN tok, SYMBOL sym){
  if (tok->basicdt == REAL){
    tok->realval = sym->constval.realnum;
  }
  else {
    tok->intval = sym->constval.intnum;
  }
}
/* findid finds an identifier in the symbol table, sets up symbol table
   pointers, changes a constant to its number equivalent */
TOKEN findid(TOKEN tok)
  { 
    SYMBOL sym, typ;
    sym = searchst(tok->stringval);
    tok->symentry = sym;
    typ = sym->datatype;
    tok->symtype = typ;
    /* constants dont have datatype, smash tok into a number tok */ 
    if (sym->kind==CONSTSYM) {
      tok->tokentype = NUMBERTOK;
      /*TODO: this might be wrong*/
      tok->basicdt = sym->basicdt;
      assignval(tok,sym); /* figures out what number value to assign*/
    }
    else if (typ->kind == BASICTYPE || typ->kind == POINTERSYM){
      tok->basicdt = typ->basicdt;
    }
    if (DEBUG & DB_FINDID){
      printf("findid\n");
      dbugprinttok(tok);
      dbprsymbol(sym);
      /* doesnt print typ if its null*/
      dbprsymbol(typ);
    }
    return tok;
  }

/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN tok)
  { 
    SYMBOL typ;
    typ = searchins(tok->stringval);
    /*TODO: check how this affects other things MIGHT NEED
    TO IMPLEMENT IN INTSARRAY INSTEAD*/
    if (typ->kind == TYPESYM ||typ->kind==FUNCTIONSYM ){
      typ = typ->datatype;
    }
    tok->symtype=typ;
    tok->basicdt=typ->basicdt;
    if (DEBUG & DB_FINDTYPE){
      printf("findtype\n");
      dbugprinttok(tok);
      dbprsymbol(typ);
    }
    return tok;
  }

/* copytok makes a new token that is a copy of origtok */
TOKEN copytok(TOKEN origtok){
  TOKEN newtok = talloc();
  newtok->tokentype=origtok->tokentype;
  newtok->basicdt=origtok->basicdt;
  newtok->symtype=origtok->symtype;
  newtok->symentry=origtok->symentry;
  newtok->tokenval=origtok->tokenval;
  return newtok;
}
/* dopoint handles a ^ operator.  john^ becomes (^ john) with type record
   tok is a (now) unused token that is recycled. */
TOKEN dopoint(TOKEN var, TOKEN tok)
  { 
    printf("inside dopoint\n");
    dbugprinttok(var);
    dbprsymbol(var->symtype);
    /*smash tok into pointer op*/
    tok->tokentype = OPERATOR;
    tok->whichval = POINTEROP;
    tok->basicdt = POINTER;
    tok->operands = var;
    /*aref is already a pointer reference*/
    if (var->tokentype == OPERATOR && var->whichval == AREFOP){
      tok->symtype = var->symtype;
    }
    else {
    /*find type of var*/
      var = findtype(var);
                    /*  varsym ->  pointersym  -> typesym -> recordsym  */
      tok->symtype = (((var->symtype)->datatype)->datatype)->datatype;
    }
    opinheritance(tok,var);
    if (DEBUG & DB_DOPOINT){
      printf("dopoint\n");
      dbugprinttok(var);
      dbugprinttok(tok);
      dbprsymbol(var->symtype);
    }
    return tok;
  }

/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement)
  {
    /* find internal label in labels array*/
    int internallabel,labeltokval;
    dbugprinttok(labeltok);
    labeltokval = labeltok->intval;
    internallabel = 0;
    while ((labels[internallabel] != labeltokval) && (internallabel < MAXBLOCKS)){
      internallabel++;
    }
    /* update labeltok*/
    labeltok->tokentype = OPERATOR;
    labeltok->whichval = LABELOP;
    labeltok->operands = makeintc(internallabel);
    labeltok->link = statement;

    if (DEBUG & DB_DOLABEL){
      printf("dolabel\n");
      dbugprinttok(labeltok);
      dbugprinttok(labeltok->operands);
      dbugprinttok(statement);
    }
    
    return makeprogn(tok,labeltok);
  }

  /* dogoto is the action for a goto statement.
   tok is a (now) unused token that is recycled. */
TOKEN dogoto(TOKEN tok, TOKEN labeltok)
  {

        /* find internal label in labels array*/
    int internallabel,labeltokval;
    dbugprinttok(labeltok);
    labeltokval = labeltok->intval;
    internallabel = 0;
    while ((labels[internallabel] != labeltokval) && (internallabel < MAXBLOCKS)){
      internallabel++;
    }
    /*smash tok into goto tok*/
    tok->tokentype = OPERATOR;
    tok->whichval = GOTOOP;
    tok->operands = fillintc(labeltok,internallabel);

     if (DEBUG & DB_DOGOTO){
       printf("dogoto\n");
       dbugprinttok(tok);
       dbugprinttok(labeltok);
    }
    return tok;
  }

/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field)
  { 
    printf("INSIDE REDUCE DOT\n");
    if (DEBUG & DB_REDUCEDOT){
      dbugprinttok(var);
      dbprsymbol(var->operands->symtype);
      dbugprinttok(dot);
      dbugprinttok(field);
      ppexpr(var);
    }
    /*var is already an a ref*/
    if (var->tokentype == OPERATOR && var->whichval == AREFOP){
      printf("TOK IS AREF\n");
      /*get offset for that field and update aref, pass the Point*/
      field = addoffs(var->operands,field);
      dbugprinttok(field);
      var->operands->link->intval += field->intval;
      /*update basicdt for aref*/
      opinheritance(var,var->operands);
      if (DEBUG & DB_REDUCEDOT){
        printf("reducedot\n");
        dbugprinttok(var);
        dbugprinttok(var->operands);
        dbugprinttok(field);
        printf("basicdt of aref: %d\n",var->basicdt);
      }
      return var;
    }

    /*aref tok*/
    dot->tokentype = OPERATOR;
    dot->whichval = AREFOP;
    dot->operands = var; /*var is pointer operand*/
    var->link = addoffs(var,field);
    dot->symtype = var->symtype;

    opinheritance(dot,var);
    
    if (DEBUG & DB_REDUCEDOT){
      printf("reducedot\n");
      dbugprinttok(var);
      dbugprinttok(dot);
      dbprsymbol(dot->symtype);
      dbugprinttok(field);
      dbprsymbol(var->symtype);
      ppexpr(dot);
    }
    return dot;
  }
/* addoffs adds offset, off, to an aref expression, exp */
TOKEN addoffs(TOKEN exp, TOKEN off)
  {
    printf("ADDOFFS\n");
    SYMBOL field;
    int found = 0;
    /*symptype points to recordsym, datatype points to beggining of fields*/
    dbprsymbol(exp->symtype);
    field = (exp->symtype)->datatype;
    dbprsymbol(field);
    /* go through field list */
    while (field != NULL && !found){
      printf("SYMBOL FIELD\n");
      dbprsymbol(field);
      /* if field list matches smash off into an int tok*/
      if (!strcmp(field->namestring,off->stringval)){
        off = fillintc(off,field->offset);
        exp -> basicdt = field->basicdt; /*use the basicdt from the field*/
        printf("basic dt of field: %d\n",field->basicdt);
        /*if the reference end up at the beggining of another record,
        change pointer type to this recordsym*/
        if (field->datatype->kind == RECORDSYM){
          printf("INSIDE IF FIELD\n");
          exp->symtype = field->datatype;
          dbprsymbol(exp->symtype);
        }
        found++;
        return off;
      }
      field = field->link;
    }
    
    return off;
  }

/* fillintc smashes tok, making it into an INTEGER constant with value num */
TOKEN fillintc(TOKEN tok, int num)
  {
    tok->tokentype = NUMBERTOK;
    tok->intval = num;
    tok->basicdt = INTEGER;
    return tok;
  }



int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}

int main(void)          /*  */
  { 
    yydebug = 0;
    int res;
    initsyms();
    res = yyparse();
    printstlevel(1);       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     
    // gencode(parseresult, blockoffs[blocknumber], labelnumber);
    
  }
