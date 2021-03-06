"""
continuation.py - the ultimate Context of all state and computation centers here.

INTRO 3 : The Continuation contains all state of the system except for the
          word dictionaries. (TODO: Later all but the global 'Any' dictionaries)
          may be moved into the Continuation as well.)
"""

from typing import Optional

from dataclasses import dataclass

from stack import Stack, KStack
from af_types import AF_Continuation, Symbol, TAny
from operation import Operation, op_nop


@dataclass
class Continuation(AF_Continuation):
    """
    INTRO 3.1 :  Continuation consists of the Stack, (Soon a Return Stack
                 will be added) the current Symbol being interpreted, and
                 the Operation that was discovered for this context to
                 operate on the Symbol.
    """
    stack : Stack
    symbol : Optional[Symbol] = None
    op : Operation = Operation("nop",op_nop)

    """
    INTRO 3.2 : We also track a Debug state.
    """

    debug : bool = True
    cdepth : int = 0        # Depth of calls for debug tab output.


    """
    INTRO 3.3 : When a Continuation is executed it looks at the Type of the
                object on top of the stack (tos) and makes that the context
                by which it will executed. If the stack is empty it will
                default to the global 'Any' type word dictionary.
    """
    def execute(self) -> None:
        # Assume that we're an empty stack and will use the TAny op_handler.
        type_context = TAny
        tos = self.stack.tos()
        if tos != KStack.Empty:
            # Make the tos type's op_handler our context instead.
            type_context = tos.type

        """
            INTRO 3.4 : Execute the operation according to our context.
                        All Type handlers take a Continuation and return nothing.
                        (See af_types/__init__.py for the default handler.)

                        Continue to aftype.py for INTRO stage 4.
        """
        handler = type_context.handler()
        return handler(self)


    def __str__(self) -> str:
        result = "Cont:\n\tsym=%s\n\t op=%s" % (self.symbol, self.op)
        if self.debug:
            result += "\n\tDebug : On (Call Depth:%s)" % self.cdepth

            content = ""
            if self.stack.is_empty():
                content += "empty"
            else:
                for n, s in enumerate(self.stack.contents()[::-1]):
                    content += "%s) val=%s,  type=%s\n\t\t" % (n, s.value, s.type.name)
            content += "\n"

            result += "\n\tStack =\t%s " % (content)
        return result
