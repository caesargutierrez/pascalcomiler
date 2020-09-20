/* codgen.c       Generate Assembly Code for x86         07 May 18   */

/* Copyright (c) 2018 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "symtab.h"
#include "lexan.h"
#include "genasm.h"
#include "codegen.h"
#include "pprint.h"

void genc(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */
// TODO: Make the regs into a double array to keep track of lru and occupancy
int wordregs[RMAX] = {0}; /* table for word registers, already initialized to all 0*/
int floatregs[FBASE] = {0}; /* fbase is size since 32 - 16*/
int jmptable[]  = {0, NEOP, EQOP , GEOP, LTOP ,GTOP, LEOP};

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */


/* helper function to get the load reg in genfun*/
int getloadreg(int basicdt){
  /*  */
  if (basicdt == STRINGTYPE){
    return RDI;
  }
  else if(basicdt == INTEGER){
    return EDI;
  }
  else{
    return XMM0;
  }
}
/* get result rax for the functions return type*/
int getresultreg(int basicdt){
  return basicdt == INTEGER ? EAX:XMM0;
}

int genfun(TOKEN code){
  int loadreg,j,resreg;
  TOKEN args;
  code = code->operands;/* function name*/
  args = code->link; /* argument */
  loadreg = getloadreg(args->basicdt); /* use data type of arguments to determine load reg */
  if (loadreg==RDI && args->basicdt == STRINGTYPE){ 
    j = nextlabel++;
    asmlitarg(j, loadreg); /* arg of function to call*/
    makeblit(args->stringval,j); /* put it in literals table*/
  }else if ((resreg = genarith(args))!= XMM0){ /* resreg for a float has to be xmm0*/
    asmrr(loadreg==EDI ? MOVL:MOVSD,resreg,loadreg); /*load result*/
  }
  asmcall(code->stringval);
  resreg = getresultreg(code->basicdt); /* get result reg depending on the function return type*/
  used(resreg);
  return resreg;
}

/* test if there is a function call within code: 1 if true, else 0 */
int funcallin(TOKEN code){
  return code->tokentype == OPERATOR && code->whichval == FUNCALLOP;
}

/* get the asm instruction for the opcode, if not an opcode then return 0 */
int getoperation(TOKEN optoken){
  int result = 0;
  int opcode = optoken->whichval;
  int dt = optoken->basicdt;
  switch(opcode){
    case PLUSOP:
      result = ADDL;
      break;
    case TIMESOP: 
      result = dt == INTEGER ? IMULL:MULSD;
      break;
    case MINUSOP:
      /* its a negation*/
      if (optoken->operands->link == NULL){
        result = dt == INTEGER ? NEGL:NEGSD;
      }
      /* regular subtract operation*/
      else {
        result = dt == INTEGER ? SUBL:SUBSD;
      }
      break;
  }
  return result;
}

/* Reset lru counter for registers*/
void resetregs(){
  if(DEBUGGEN){printf("RESETING REGISTERS\n");}
  for (int i = RBASE; i < RMAX; i++){
    wordregs[i] = 0;
  }
  for (int i = 0; i < FBASE; i++){
    floatregs[i] = 0;
  }
}
/* Find the jmp code through the jumppr table*/
int getjmpc(int oper){
  for (int i = JNE; i <= JLE; i++){
    if (oper == jmptable[i]){
      return i;
    }
  }
  return 0;
}
/* Mark a register unused */
void unused(int reg)
  { 
        /* mark float reg as unused*/
    if (reg >= FBASE && reg <= FMAX ){
      floatregs[reg - FBASE] = 0;
    }
    /* mark word reg as unused */
    if (reg >= RBASE && reg <= RMAX){
      wordregs[reg] = 0;
    }
  }
/* Mark a register used */
// TODO: CHECK IF REG IS OCCUPIED AND STORE ITS VALUE SOMEWHERE
void used(int reg)
  {
    /* mark word reg as used */
    if (RBASE >= reg && reg <= RMAX){
      wordregs[reg] = 1;
    }
    /* mark float reg as used*/
    if (FBASE >= reg && reg <= FMAX){
      floatregs[reg - FBASE] = 1;
    }
  }

void gencode(TOKEN pcode, int varsize, int maxlabel)
  {  TOKEN name, code;
     name = pcode->operands;
     code = name->link->link;
     nextlabel = maxlabel + 1;
     stkframesize = asmentry(name->stringval,varsize);
     genc(code);
     asmexit(name->stringval);
  }

/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind)
  { 
    // TODO: merge both arrays to use a single loop with different starting points
    /* word */
    if (kind == WORD){
      int base; 
      // TODO: fix so it can handle when we run out of gen purpose regs
      for (int i = RBASE; i < RMAX; i++){
        /* reg is empty */
        if (wordregs[i] == 0){
          wordregs[i]++;
          return i;
        }
      }
    }
    /* float */
    else {
      for (int i = 0; i < FBASE; i++){
        /* reg is empty*/
        if (floatregs[i] == 0){
            floatregs[i]++;
            if(DEBUGGEN){printf("returning float reg # %d\n",FBASE + i);}
            return (FBASE + i); /* fbase begins at 16*/ 
        }
      }
    }
  }

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  {  /*reg1,reg2  ->reg2, reg2 is destreg*/
     int num,reg1, reg2, off,j;
     if (DEBUGGEN)
       { printf("genarith\n");
	 dbugprinttok(code);
       };
      switch ( code->tokentype )
       { /*Immeadiate*/
         case NUMBERTOK:  
           switch (code->basicdt)
             { case INTEGER:
		 num = code->intval;
		 reg2 = getreg(WORD);
		 if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE )
		   asmimmed(MOVL, num, reg2);
		 break;
	       case REAL:
         j = nextlabel++;
         reg2 = getreg(FLOAT);
         makeflit(code->realval,j);
         asmldflit(MOVSD,j,reg2);
		 break;
	       }
	   break;
       case IDENTIFIERTOK:
       /*TODO: check what type it is to determine offset, this assumes code is  var*/
       off = (code->symentry->offset) - stkframesize; /* offset of var*/
       reg2 = getreg(code->basicdt == INTEGER ? WORD:FLOAT); 
       asmld(code->basicdt == INTEGER ? MOVL:MOVSD, off, reg2, code->stringval);
	   break;
    //  TODO: remove repeated code. ex: reg2 has same call!!
       case OPERATOR:
       num = getoperation(code); /* num will hold the type of operation, 0 if its cmp*/
       if (num){
         /*handle negation of float or word */
         if (num == NEGSD){
           reg2 = genarith(code->operands);
           reg1 = getreg(FLOAT);
           asmfneg(reg2,reg1);
           unused(reg1); /* negation reg isnt needed again*/
         }else if (num == NEGL){
           reg2 = genarith(code->operands);
           asmr(num,reg2);
         }else{
           /* regular arith operation */
          reg2 = genarith(code->operands); /*lhs*/
          if(funcallin(code->operands->link)){
            asmsttemp(reg2);
            unused(reg2);
          }
          reg1 = genarith(code->operands->link); /*rhs*/
          if(funcallin(code->operands->link)){
            reg2 = getreg(FLOAT);
            asmldtemp(reg2);
          }
          asmrr(num,reg1,reg2);
          unused(reg1); /* free up reg1 */
         }
       }
       /*FLOATOP AND FIXOP need different asm instruction*/
       else if (code->whichval == FLOATOP){
         /*freg is the one needed later*/
         reg1 = genarith(code->operands);
         reg2 = getreg(FLOAT); 
         asmfloat(reg1,reg2);
       }
       else if(code->whichval == FUNCALLOP){
        reg2 = genfun(code);
       }
       /*assume its a cmp op*/
       else{
        reg2 = genarith(code->operands); /* load up lhs to a reg */
        reg1 = genarith(code->operands->link); /* load up rhs to a reg*/
        asmrr(CMPL,reg1,reg2);
       }
	   break;
       };
     return reg2;
    }

/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
  {  TOKEN tok, lhs, rhs;
     int reg, offs, jmpc,j;
     SYMBOL sym;
     if (DEBUGGEN)
       { printf("genc\n");
	 dbugprinttok(code);
       };
     if ( code->tokentype != OPERATOR )
        { printf("Bad code token");
	  dbugprinttok(code);
	};
     switch ( code->whichval )
       { case PROGNOP:
	   tok = code->operands;
	   while ( tok != NULL )
	     {  genc(tok);
		tok = tok->link;
	      };
	   break;
	 case ASSIGNOP:                   /* Trivial version: handles I := e */
     lhs = code->operands;
	   rhs = lhs->link;
	   reg = genarith(rhs);              /* generate rhs into a register */
	   sym = lhs->symentry;              /* assumes lhs is a simple var  */
	   offs = sym->offset - stkframesize; /* net offset of the var   */
           switch (code->basicdt)            /* store value into lhs  */
             { case INTEGER:
                 asmst(MOVL, reg, offs, lhs->stringval);
                 resetregs(); /* have a clean reg use for next operation*/
                 break;
               case REAL:
                 asmst(MOVSD,reg,offs,lhs->stringval);
                 resetregs();
                 break;
               case POINTER:
                asmst(MOVQ,reg,offs,lhs->stringval);
                 resetregs();
             };
           break;
	 case FUNCALLOP:
     reg = genfun(code);
     resetregs();
	   break;
	 case GOTOOP:
     tok = code->operands;
     j = tok->intval;
     asmjump(JMP,j);
	   break;
	 case LABELOP:
      tok = code->operands;
      asmlabel(tok->intval);
      break;
   case IFOP:
      tok = code->operands;
      reg = genarith(tok); /*generate cmp*/
      jmpc = getjmpc(tok->whichval);
      j = nextlabel++;
      asmjump(jmpc,j);
      resetregs(); /*clean regs for else/then statements*/
      if (tok->link->link != NULL){genc(tok->link->link);}/*else statement is after then*/
      asmjump(JMP,nextlabel);
      asmlabel(j); /*label for then statement*/
      j = nextlabel++;
      genc(tok->link); /* then statement*/
      asmlabel(j); /* fallthrough label*/
      resetregs(); /* have a clean reg use for next operation*/
	   break;
	 };
  }
