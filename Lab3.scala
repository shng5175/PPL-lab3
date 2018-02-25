package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._

  /*
   * CSCI 3155: Lab 3
   * <Sherry Nguyen>
   *
   * Partner: <Ariel Riggan>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => {
        if (s == "") 0
        else try s.toDouble catch {
          case _: Throwable => Double.NaN
        }
      }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case N(0) => false
      case N(_) => true
      case S("") => false
      case S(_) => true
      case Undefined => false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
      // of the function (from the input program).
      case Function(_, _, _) => "function"
      case B(b) => if(b) "true" else "false"
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case Undefined => "undefined"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case _ => bop match {
        case Lt => toNumber(v1) < toNumber(v2)
        case Le => toNumber(v1) <= toNumber(v2)
        case Gt => toNumber(v1) > toNumber(v2)
        case Ge => toNumber(v1) >= toNumber(v2)
        case _ => ??? // delete this line when done
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {

      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e

      /* Base Cases */
      case Binary(bop, e1, e2) => bop match {
          case Plus => (eval(env, e1), eval(env, e2)) match {
            case (S(s), e2) => S(s + toStr(e2))
            case (e1, S(s)) => S(toStr(e1) + s)
            case (e1, e2) => N(toNumber(e1) + toNumber(e2))
          }

          case Minus => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))

          case Times => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))

          case Div => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))

          /* === */
          case Eq => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            (v1,v2) match{
              case (Function(_,_,_), _) => throw DynamicTypeError(v1)
              case (_,Function(_,_,_))=> throw DynamicTypeError(v2)
              case _ => B(v1 == eval(env, e2))
            }
          }

          /* !== */
          case Ne =>
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            (v1,v2) match{
              case (Function(_,_,_), _) => throw DynamicTypeError(v1)
              case (_,Function(_,_,_))=> throw DynamicTypeError(v2)
              case _ => B(v1 != eval(env, e2))
            }

          /* < */
          case Lt => (eval(env, e1), eval(env, e2)) match {
            case (S(_), S(_)) => B(toStr(eval(env, e1)) < toStr(eval(env, e2)))
            case (_, _) => B(toNumber(eval(env, e1)) < toNumber(eval(env, e2)))
          }

          /* <= */
          case Le => (eval(env, e1), eval(env, e2)) match {
            case (S(_), S(_)) => B(toStr(eval(env, e1)) <= toStr(eval(env, e2)))
            case (_, _) => B(toNumber(eval(env, e1)) <= toNumber(eval(env, e2)))
          }

          /* > */
          case Gt => (eval(env, e1), eval(env, e2)) match {
            case (S(_), S(_)) => B(toStr(eval(env, e1)) > toStr(eval(env, e2)))
            case (_, _) => B(toNumber(eval(env, e1)) > toNumber(eval(env, e2)))
          }

          /* >= */
          case Ge => (eval(env, e1), eval(env, e2)) match {
            case (S(_), S(_)) => B(toStr(eval(env, e1)) >= toStr(eval(env, e2)))
            case (_, _) => B(toNumber(eval(env, e1)) >= toNumber(eval(env, e2)))
          }

          case And => {
            if (toBoolean(eval(env, e1)) == false)
              eval(env, e1)
            else
              eval(env, e2)
          }

          case Or => {
            if(toBoolean(eval(env, e1)) == true)
              eval(env, e1)
            else eval(env, e2)
          }

          case Seq =>
            eval(env, e1)
            eval(env, e2)
        }

      case Unary(uop, x) =>
        val v1 = eval(env,x)
        if(x==DynamicTypeError) throw DynamicTypeError(x)
        else {
          uop match {
            case Neg => N(-toNumber(v1))
            case Not => B(!toBoolean(v1))
          }
        }

      case ConstDecl(x, e1, e2) => eval(extend(env, x, eval(env, e1)), e2)

      case If(bool, e1, e2) => if(toBoolean(eval(env, bool))) eval(env, e1) else eval(env, e2)

      /* Inductive Cases */
      case Print(e1) => println(toStr(eval(env, e1))); Undefined

      case Var(x) => lookup(env, x)


      // ****** Your cases here

      case Call(e1, e2) => if(e2==DynamicTypeError) throw DynamicTypeError(e2) else eval(env,e1) match {
        case Function(p, x, body) => p match {
          case None => eval(extend(env, x, eval(env, e2)), body)
          case Some(s) => eval(extend(extend(env, x, eval(env, e2)), s, Function(Some(s), x, body)), body)
        }
        case _ => throw DynamicTypeError(e1)
      }
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(x) => loop(x, n+1)
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1,v,x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1,v,x), substitute(e2,v,x))
      case If(e1, e2, e3) => If(substitute(e1,v,x), substitute(e2,v,x), substitute(e3,v,x))
      case Call(e1, e2) => Call(substitute(e1,v,x), substitute(e2,v,x))
      case Var(y) => if (y == x) v else Var(y)
      case Function(None, y, e1) => if (y == x) Function(None, y, e1) else Function(None, y, substitute(e1,v,x))
      case Function(Some(y1), y2, e1) =>  if (y2 == x || y1 == x) Function(Some(y1), y2, e1) else Function(Some(y1),y2,substitute(e1,v,x))
      case ConstDecl(y, e1, e2) => if (y == x) ConstDecl(y,substitute(e1,v,x),e2) else ConstDecl(y,substitute(e1,v,x), substitute(e2,v,x))
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      // ****** Your cases here
      case Unary(Neg,e1) if(isValue(e1))=>  N(-toNumber(e1))
      case Unary(Not,e1) if(isValue(e1))=> B(!toBoolean(e1))

      case Binary(bop,e1,e2) if(isValue(e1) && isValue(e2))=>
        bop match {
          case Seq => e2
          case Plus=>
            (e1,e2) match{
              case (S(e1), e2) => S(e1+toStr(e2))
              case (e1, S(e2)) => S(toStr(e1)+e2)
              case (_, _) => N(toNumber(e1)+toNumber(e2))
            }
          //arithmetic
          case Minus=> N(toNumber(e1)-toNumber(e2))
          case Div=> N(toNumber(e1)/toNumber(e2))
          case Times=>N(toNumber(e1)*toNumber(e2))

          //Inequalities
          case Lt | Le | Gt | Ge => B(inequalityVal(bop, e1, e2))
          case Eq | Ne =>{
            (e1,e2) match{
              case (_,Function(_,_,_))=> throw DynamicTypeError(e2)
              case (Function(_,_,_), _)=> throw DynamicTypeError(e1)
              case (v1,v2)=> bop match {
                case Eq=> B(e1==e2)
                case Ne=> B(e1!=e2)
              }
            }
          }
          //And/or
          case And => toBoolean(e1) match{
            case true=> e2
            case false=> e1
          }
          case Or => toBoolean(e1) match{
            case true=> e1
            case false=> e2
          }
        }
      case Print(e1) if(isValue(e1))=> {
        print(e1)
        Undefined
      }
      case If(e1,e2,e3) if(isValue(e1))=> toBoolean(e1) match{
        case true => e2
        case false => e3
      }

      case ConstDecl(x,e1,e2) if(isValue(e1))=> substitute(e2,e1,x)
      case Call(e1, e2) if(isValue(e1) && isValue(e2)) => {
        e1 match {
          case Function(name, x, body)=> name match{
            case None=> substitute(body, e2, x)
            case Some(f)=> substitute(substitute(body,e2,x), e1, f)
          }
          case _ => throw DynamicTypeError(e1)
        }
      }
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      // ****** Your cases here
      case Unary(uop, e1) =>
        val v1 = step(e1)
        if (v1!=DynamicTypeError) {
          uop match {
            case Neg => Unary(Neg, step(e1))
            case Not => Unary(Not, step(e1))
          }
        }
        else throw DynamicTypeError(e1)
      case Binary(bop, e1, e2) if(isValue(e1))=> {
        if (step(e2) == DynamicTypeError) throw DynamicTypeError(e2)
        else {
          bop match {
            case Plus | Minus | Times | Div | Lt | Le | Gt | Ge => Binary(bop, e1, step(e2))
            case Eq | Ne => e1 match {
              case Function(_, _, _) => ???
              case _ => Binary(bop, e1, step(e2))
            }
          }
        }
      }
      case Binary(bop, e1, e2)=> if(step(e1)==DynamicTypeError) throw DynamicTypeError(e1) else Binary(bop, step(e1), e2)
      case Print(e1) => if(step(e1)==DynamicTypeError) throw DynamicTypeError(e1) else Print(step(e1))
      case If(e1,e2,e3) => if(step(e1)==DynamicTypeError) throw DynamicTypeError(e1) else If(step(e1),e2,e3)
      case ConstDecl(x, e1, e2)=> if (step(e1)==DynamicTypeError) throw DynamicTypeError(e1) else ConstDecl(x, step(e1), e2)
      case Call(e1,e2) if(isValue(e1))=> if (step(e2)==DynamicTypeError) throw DynamicTypeError(e2) else Call(e1, step(e2))
      case Call(e1,e2) => if(step(e1)==DynamicTypeError) throw DynamicTypeError(e1) else Call(step(e1),e2)
      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}