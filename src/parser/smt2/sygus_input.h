/*********************                                                        */
/*! \file sygus_input.h
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SYGUS_INPUT_H
#define __CVC4__PARSER__SYGUS_INPUT_H

#include "parser/antlr_input.h"
#include "parser/smt2/generated/Smt2Lexer.h"
#include "parser/smt2/generated/Smt2Parser.h"

// extern void Smt2ParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class Smt2;

class SygusInput : public AntlrInput {
  typedef AntlrInput super;

  /** The ANTLR3 SMT2 lexer for the input. */
  pSmt2Lexer d_pSmt2Lexer;

  /** The ANTLR3 SMT2 parser for the input. */
  pSmt2Parser d_pSmt2Parser;

  /** Which (variant of the) input language we're using */
  InputLanguage d_lang;

  /**
   * Initialize the class. Called from the constructors once the input
   * stream is initialized.
   */
  void init();

public:

  /**
   * Create an input.
   *
   * @param inputStream the input stream to use
   */
  SygusInput(AntlrInputStream& inputStream);

  /** Destructor. Frees the lexer and the parser. */
  virtual ~SygusInput();

  /** Get the language that this Input is reading. */
  InputLanguage getLanguage() const throw() {
    return language::input::LANG_SYGUS;
  }

protected:

  /**
   * Parse a command from the input. Returns <code>NULL</code> if
   * there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseCommand();

  /**
   * Parse an expression from the input. Returns a null
   * <code>Expr</code> if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr parseExpr();

};/* class SygusInput */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SYGUS_INPUT_H */
