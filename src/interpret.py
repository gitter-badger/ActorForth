from typing import TextIO

from dataclasses import dataclass

from continuation import Continuation, Stack

from parser import Parser

from af_types import Type, TypeSignature, TAtom, make_atom, TAny 

from af_types.af_int import *
from af_types.af_bool import *

from compiler import *
import compiler


@dataclass(frozen = True)
class Location:
    filename : str = "Unknown"
    linenum : int = 0
    column : int = 0


@dataclass(order = True)
class Symbol:
    s_id : str
    location : Location 
    type : Type 
    
    @property
    def size(self) -> int:
        return len(self.s_id)

    def __eq__(self, symbol = None) -> bool:
        if type(symbol) is Symbol:
            return symbol.s_id == self.s_id
        return symbol == self.s_id   


def interpret(cont: Continuation, input_stream: TextIO, filename: Optional[str] = None, prompt: Optional[str] = None) -> Continuation:    
    p = Parser()
    p.open_handle(input_stream, filename)

    interpret_mode = True

    if prompt: print(prompt,end='',flush=True)    
    for s_id, linenum, column in p.tokens():
        symbol = Symbol(s_id, Location(p.filename,linenum,column), TAtom)

        if p.filename != "stdin":
            print(s_id)
        tos = cont.stack.tos()
        found = False
        if tos is not Stack.Empty:
            # We first look for an atom specialized for the type/value on TOS.
            cont.op, sig, flags, found = Type.op(symbol.s_id, cont, tos.type.name)

        if not found:
            # If Stack is empty or no specialized atom exists then search the global dictionary.
            cont.op, sig, flags, found = Type.op(symbol.s_id, cont)
        
        try:
            if found:
                #print("Executing %s:" % cont.op)
                cont.op(cont)
                print(cont)
            else:
                # No idea what this is so make an atom on the stack.
                #print("New Atom: '%s'" % symbol.s_id)
                make_atom(cont, symbol.s_id)
                print(cont)
                
        except Exception as x:
            print("Exception %s" % x)
            print("Interpreting symbol %s" % symbol)
            print(cont)
            
            # See what happens if we just keep going...
            #break
            raise
        if prompt: print(prompt,end='',flush=True)    

    return cont
