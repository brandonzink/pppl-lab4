package jsy.student

import jsy.lab4.{Lab4Like, ast}

import scala.None

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * Brandon Zink
   * 
   * Partner: Cameron Connor
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
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => Nil
    case h1 :: (t1 @ (_ :: _)) => h1 :: compressRec(t1.dropWhile(_ == h1))
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]) {
    (h, acc) => if (acc.isEmpty || acc.head != h) h :: acc else acc
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => if (f(h).isDefined)
      f(h).get :: t
      else h :: mapFirst(t)(f)
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(loop(f(acc, d), l), r)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b1, _) = foldLeft(t)((true, None: Option[Int])){
      (acc, d) => acc match {
        case (b2, None) => (b2, Some(d))
        case (b2, Some(x)) => if (x < d)
          (b2, Some(d))
          else (false, Some(d))
      }
    }
    b1
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if fields exists { case (_, t) => hasFunctionTyp(t) } => true
    case _ => false
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => lookup(env, x)
      case Decl(mode, x, e1, e2) => typeof(extend(env, x, typeof(env, e1)), e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e1)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (t1, _) => err(t1, e1) // FIXME possible
        case (_, t2) => err(t2, e2)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e1)) match {
        case (TNumber, TNumber) => TNumber
        case (t1, _) => err(t1, e1)
        case (_, t2) => err(t2, e2)
      }
      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (t1, _) if hasFunctionTyp(t1) => err(t1, e1)
        case (_, t2) if hasFunctionTyp(t2) => err(t2, e2)
        case (t1, t2) => if (t1 == t2) TBool else err(t2, e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (t1, _) if t1 != TNumber && t1 != TString => err(t1, e1)
        case (_, t2) if t2 != TNumber && t2 != TString => err(t2, e2)
      }
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (t1, _) if t1 != TBool => err(t1, e1)
        case (_, t2) if t2 != TBool => err(t2, e2)
      }
      case Binary(Seq, _, e2) =>
        typeof(env, e2)
      case If(e1, e2, e3) => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
        case (TBool, t2, t3) if t2 == t3 => typeof(env, e2)
        case _ => err(typeof(env, e1), e1) // FIXME
      }
      case Function(fname, params, tann, e1) =>
        val envp = params.foldLeft(env)({case (accEnv, (n, t)) => extend(accEnv, n, t.t)})
        (fname, tann) match {
          // TypeFunction
          case (None, None) =>
            val bodyType = typeof(envp, e1)
            TFunction(params, bodyType)
          // TypeFunctionAnn
          case (None, Some(t)) =>
            val bodyType = typeof(envp, e1)
            if (t == bodyType) TFunction(params, bodyType)
            else err(bodyType, e1)
          // TypeRecFunction
          case (Some(x), Some(t)) =>
            val recEnv = extend(envp, x, t)
            val recTyp = typeof(recEnv, e1)
            if (t == recTyp) TFunction(params, recTyp)
            else err(recTyp, e1)
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            case ((x, MTyp(_, t)), ei) => if (typeof(env, ei) != t) err(t, ei)
          }
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map({case (k, v) => (k, typeof(env, v))}))
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) =>
          fields.get(f) match {
            case Some(tp) => tp
            case None => err(typeof(env, e1), e1)
        }
        case tgot => err(tgot, e1)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => if (s1.compareTo(s2) == -1) true else false
        case Le => if (s1.compareTo(s2) == 1) false else true
        case Gt => if (s1.compareTo(s2) == 1) true else false
        case Ge => if (s1.compareTo(s2) == -1) false else true
      }
      case (N(n1), N(n2)) => bop match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case Some(ep) => loop(ep, n+1)
      case None => e
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
        // FIXME possible in these cases respect non-free vars instead of subing on all exprs
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else Var(y)
      case Decl(mode, y, e1, e2) =>
        if (y == x)
          Decl(mode, y, subst(e1), e2)
        else
          Decl(mode, y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>
        p match {
          case Some(p1) if !(x == p1 || params.exists({case (xi, _) => xi == x})) =>
            Function(p, params, tann, substitute(e1, esub, x))
          case _ => e
        }
      case Call(e1, args) =>
        Call(subst(e1), args map subst)
      case Obj(fields) =>
        Obj(fields.mapValues(f => subst(f)))
      case GetField(e1, f) =>
        if (x != f) GetField(subst(e1), f)
        else e
    }
    subst(e)
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => ???
        case Binary(bop, e1, e2) => ???
        case If(e1, e2, e3) => ???

        case Var(y) =>
          ???
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          ???

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => ???
            case Some(x) => ???
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            ???
          }
          ???
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => if (isValue(e)) false else true
    case MName => ???
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, N(n)) => N(-n)
      case Unary(Not, B(b)) => B(!b)
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(bop @ (Plus|Minus|Times|Div), N(n1), N(n2)) => bop match {
        case Plus => N(n1 + n2)
        case Minus => N(n1 - n2)
        case Times => N(n1 * n2)
        case Div => N(n1 / n2)
      }
      case Binary(bop @ (Lt|Gt|Le|Lt), v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (S(s1), S(s2)) => B(inequalityVal(bop, S(s1), S(s2)))
        case (N(n1), N(n2)) => B(inequalityVal(bop, N(n1), N(n2)))
      }
      case Binary(And, B(b), e2) => if (b) e2 else B(false)
      case Binary(Or, B(b), e2) => if (b) B(true) else e2
      case Binary(bop @ (Eq|Ne), v1, v2) if isValue(v1) && isValue(v2) => bop match {
        case Eq => B(v1 == v2)
        case Ne => B(v1 != v2)
      }
      case If(B(b), e2, e3) => if (b) e2 else e3
      case Decl(mode, x, e1, e2) if !isRedex(mode, e1) => substitute(e2, e1, x)
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall({case ((_, MTyp(m,_)),exp) => !isRedex(m, exp)})) {
              val e1p = pazip.foldRight(e1) {
                (pa,acc) => pa match {
                  case ((x, MTyp(m,t)), arg) => substitute(acc, arg, x)
                }
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1)
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                case (pi @ (x1, MTyp(m, t)), exp) =>
                  if (isRedex(m, exp)) { Some((pi, step(exp))) }
                  else None
              }
              Call(v1, pazipp.map{case (_, arg) => arg})
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */
      case GetField(e1, f) => e1 match {
        case Obj(fields) => fields.get(f) match {
          case Some(ep) => ep
        }
        case _ => throw StuckError(e)
      }
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) =>
        Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) if !isValue(e2) =>
        Binary(bop, step(e1), e2)
      case If(e1, e2, e3) =>
        If(step(e1), e2, e3)
      case Decl(mode, x, e1, e2) if isRedex(mode, e1) =>
        Decl(mode, x, step(e1), e2)
        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) =>
        Call(v1, args.map({case a if !isValue(a) => step(a)}))
      case Call(e1, args) =>
        Call(step(e1), args)
      case Obj(fields) =>
        Obj(fields.mapValues({case v if !isValue(v) => step(v)}))
      case GetField(e1, f) => e1 match {
        case Obj(fp) => fp.get(f) match {
          case Some(v) => v
          case None => throw StuckError(e)
        }
        case ep => GetField(step(ep), f)
      }
      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

