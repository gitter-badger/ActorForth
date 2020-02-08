#
#   af_types.py     - Types for our language.
#

from typing import Dict, List, Tuple, Callable, Any
from enum import Enum
from dataclasses import dataclass

from stack import Stack

@dataclass(frozen = True)
class Location:
    filename : str = "Unknown"
    linenum : int = 0
    column : int = 0


class Type:

    types : Dict[str, List[Tuple[str,Callable[[Stack, str],None]]]] = {}

    def __init__(self, typename: str = "Unknown"):
        self.name = typename
        if not Type.types.get(self.name):
            Type.types[self.name] = []

    @property
    def forth_dict(self) -> List[Tuple[str,Callable[[Stack, str],None]]]:
        return Type.types[self.name]

    def __eq__(self, type: object):
        if isinstance(type, Type):
            return self.name == type.name
        return False

    def __str__(self) -> str:
        #return "Type('%s')" % self.name
        return self.name

    def __repr__(self) -> str:
        return self.__str__()

TAtom = Type("Atom")
TInt = Type("Int")


@dataclass
class StackObject:
    value: Any
    type: Type 

@dataclass
class TypeSignature:
    stack_in : List[Type]
    stack_out : List[Type]

    def match_in(self, types: List[Type]) -> bool:
        return True

    def match_out(self, types: List[Type]) -> bool:
        return True


@dataclass(order = True)
class Symbol:
    s_id : str
    location : Location 
    type : Type 
    
    @property
    def size(self):
        return len(self.s_id)

    def __eq__(self, symbol = None):
        if type(symbol) is Symbol:
            return symbol.s_id == self.s_id
        return symbol == self.s_id


def op_int(s: Stack, s_id: str) -> None:
    print("op_int(s_id = '%s')\n" % s_id )
    i = int(s.pop().value)
    s.push(StackObject(i,TInt))
op_int.sig=TypeSignature([TAtom],[TInt])

def op_atom(s: Stack, s_id: str) -> None:
    print("op_atom(s_id = '%s')\n" % s_id) 
    s.push(StackObject(s_id,TAtom))
op_atom.sig=TypeSignature([],[TAtom])

def op_plus(s: Stack, s_id: str) -> None:
    print("op_plus(s_id = '%s')\n" % s_id) 
    op1 = s.pop().value
    op2 = s.pop().value
    s.push(StackObject(op1+op2,TInt))
op_plus.sig=TypeSignature([TInt,TInt],[TInt])    

def op_print(s: Stack, s_id: str) -> None:
    print("op_print(s_id = '%s')\n" % s_id) 
    op1 = s.pop().value
    print("'%s'" % op1)
op_print.sig=TypeSignature([TInt],[])


forth_dict : List[Tuple[str,Callable[[Stack, str],None]]] = []

forth_dict.insert(0,('int',op_int))
forth_dict.insert(0,('print',op_print))

TInt.forth_dict.insert(0,('+',op_plus))