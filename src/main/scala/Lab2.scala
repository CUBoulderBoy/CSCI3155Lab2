object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * Jeremy Granger
   * 
   * Partner: Christopher Jordan
   * Collaborators: None
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => Double.NaN
      case N(n) => n
      case B(b) => if (b) 1.0 else 0.0
      case S(s) => try {s.toDouble } catch {case e: Exception => Double.NaN}
      case Var(x) => toNumber(get(emp, x))
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => false
      case null => false
      case B(b) => b
      case N(n) => if ((n == 0) || (n == Double.NaN)) false else true
      case S(s) => if (s.isEmpty) false else true
      case Var(x) => toBoolean(get(emp, x))
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => "undefined"
      case B(b) => if (b) "true" else "false"
      case N(n) => if (n % 1 == 0) n.toInt.toString else n.toString
      case S(s) => s
      case Var(x) => toStr(get(emp, x))
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)
    
    e match {
    	/* Base Cases */
      	case Undefined => Undefined 
    	case N(n) => N(n)
    	case B(b) => B(b)
    	case S(s) => S(s)
    	
    	/* Var Passing Cases */
    	case Binary(b, Var(v1), Var(v2)) => eval(Binary(b, get(env, v1), get(env, v2)))
    	case Binary(b, Var(v), e2) => eval(Binary(b, get(env, v), e2))
    	case Binary(b, e1, Var(v)) => eval(Binary(b, e1, get(env, v)))
    	
    	/* Unary Cases */
    	case Unary(Not, e) => B(! toBoolean(e))
    	case Unary(Neg, e) => N(- toNumber(e))
      
    	/* AndOr Cases */
    	case Binary(And, e1, e2) => {
    		val a = toBoolean(e1)
    		val b = toBoolean(e2)
    		if (a && b) e1 else {
    			if (!a) e1 else e2
    		}
    	}
    	case Binary(Or, e1, e2) => {
    		val a = toBoolean(e1)
    		val b = toBoolean(e2)
    		if (a) e1 else {
    			if (b) e2 else e1
    		}
    	}
      
    	/* Arithmetic Cases */
    	case Binary(Plus, e1, e2) => e match {
    		case Binary(Plus, S(s), e2) => S(s + toStr(e2))
    		case Binary(Plus, e1, S(s)) => S(toStr(e1) + s)
    		case _ => N(toNumber(e1) + toNumber(e2))
    	}
    	case Binary(Minus, e1, e2) => N(toNumber(e1) - toNumber(e2))
    	case Binary(Times, e1, e2) => N(toNumber(e1) * toNumber(e2))
    	case Binary(Div, en, ed) => {
    		if (toNumber(ed) > 0) N(toNumber(en) / toNumber(ed))
    		else if (toNumber(en) < 0) N(Double.NegativeInfinity)
    		else N(Double.PositiveInfinity)
    	}
      
    	/* Comparison Cases */
    	case Binary(Eq, e1, e2) => B(toNumber(e1) == toNumber(e2))
    	case Binary(Ne, e1, e2) => B(toNumber(e1) != toNumber(e2))
    	case Binary(Lt, e1, e2) => e match {
    	  	case Binary(Lt, N(n), e2) => B(n < toNumber(e2))
    	  	case Binary(Lt, e1, N(n)) => B(toNumber(e1) < n)
    	  	case Binary(Lt, S(s1), S(s2)) => B(s1 < s2)
    	}
    	case Binary(Le, e1, e2) => B(toNumber(e1) <= toNumber(e2))
    	case Binary(Gt, e1, e2) => B(toNumber(e1) > toNumber(e2))
    	case Binary(Ge, e1, e2) => B(toNumber(e1) >= toNumber(e2))
    	case Binary(seq, e1, e2) => {
    		val _= eval(env, e1)
    		eval(env, e2)
    	}
      
    	/* If Case */
    	case If(e1, e2, e3) => {
    	  if(toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)
    	}
    	
    	/* Inductive Cases */
    	/* Constant Cases */
    	case ConstDecl(x, e1, e2) => {
    		eval(extend(env, x, e1), e2)
    	}
    	
    	case Print(e1) => println(pretty(eToVal(e1))); Undefined

    	case _ => throw new UnsupportedOperationException
    }
  }
    
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = {
    println("\nExpression:\n  " + e)
    eval(emp, e)
  }

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(pretty(v))
  }

}

