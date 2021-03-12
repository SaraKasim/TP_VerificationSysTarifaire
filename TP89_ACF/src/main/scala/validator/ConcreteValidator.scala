package validator.Kasim

import bank._


// Automatic conversion of bank.message to tp89.messages and Nat to bank.Nat
object Converter{
  implicit def bank2message(m:bank.message):tp89.message=
    m match {
    case bank.Pay((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Pay((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Ack((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Ack((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Cancel((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i)))) => tp89.Cancel((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))))
  }
  
  implicit def trans2bankTrans(l:List[((Nat.nat,(Nat.nat,Nat.nat)),Nat.nat)]): List[((bank.Nat.nat,(bank.Nat.nat,bank.Nat.nat)),bank.Nat.nat)]=
    l match {
    case Nil => Nil
    case ((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))::r => ((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p))::trans2bankTrans(r)
  }
}

import Converter._


/* The object to complete */
class ConcreteValidator extends TransValidator{
var bdd:List[((Nat.nat, (Nat.nat, Nat.nat)), tp89.state[Nat.nat])] = List()

  // TODO
  def process(m:message):Unit={ bdd= tp89.traiterMessage(m,bdd) }

  // TODO
  def getValidTrans= tp89.export(bdd)

}

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def `Product_Type.equal_prod`[A : equal, B : equal]: equal[(A, B)] =
    new equal[(A, B)] {
    val `HOL.equal` = (a: (A, B), b: (A, B)) =>
      Product_Type.equal_proda[A, B](a, b)
  }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Code_Numeral {

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

} /* object Code_Numeral */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
}

} /* object Product_Type */

object table {

abstract sealed class option[A]
final case class Somea[A](a: A) extends option[A]
final case class Nonea[A]() extends option[A]

def assoc[A : HOL.equal, B](uu: A, x1: List[(A, B)]): option[B] = (uu, x1) match
  {
  case (uu, Nil) => Nonea[B]()
  case (x1, (x, y) :: xs) =>
    (if (HOL.eq[A](x, x1)) Somea[B](y) else assoc[A, B](x1, xs))
}

def modify[A : HOL.equal, B](x: A, y: B, xa2: List[(A, B)]): List[(A, B)] =
  (x, y, xa2) match {
  case (x, y, Nil) => List((x, y))
  case (x, y, (z, u) :: r) =>
    (if (HOL.eq[A](x, z)) (x, y) :: r else (z, u) :: modify[A, B](x, y, r))
}

} /* object table */

object Lista {

def member[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => HOL.eq[A](x, y) || member[A](xs, y)
}

} /* object Lista */

object tp89 {

abstract sealed class state[A]
final case class Validated[A](a: A) extends state[A]
final case class InProgressC[A](a: A) extends state[A]
final case class InProgressM[A](a: A) extends state[A]
final case class Canceled[A]() extends state[A]

abstract sealed class message
final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
  message
final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
  message
final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

def export(x0: List[((Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat])]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  =
  x0 match {
  case Nil => Nil
  case (tid, x) :: xs => (x match {
                            case Validated(y) => (tid, y) :: export(xs)
                            case InProgressC(_) => export(xs)
                            case InProgressM(_) => export(xs)
                            case Canceled() => export(xs)
                          })
}

def returnAllKeys(x0: List[((Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat])]):
      List[(Nat.nat, (Nat.nat, Nat.nat))]
  =
  x0 match {
  case Nil => Nil
  case (tid, idState) :: bdd => tid :: returnAllKeys(bdd)
}

def traiterMessagePay(tid: (Nat.nat, (Nat.nat, Nat.nat)), n: Nat.nat,
                       bdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                                   state[Nat.nat])]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat])]
  =
  (if (Lista.member[(Nat.nat, (Nat.nat, Nat.nat))](returnAllKeys(bdd), tid))
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat]](tid, bdd) match
       {
       case table.Somea(Validated(_)) => bdd
       case table.Somea(InProgressC(x)) =>
         (if (Nat.less_nat(x, n))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         state[Nat.nat]](tid, InProgressC[Nat.nat](n), bdd)
           else bdd)
       case table.Somea(InProgressM(x)) =>
         (if (Nat.less_nat(x, n))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         state[Nat.nat]](tid, Validated[Nat.nat](n), bdd)
           else bdd)
       case table.Somea(Canceled()) => bdd
     case table.Nonea() => bdd })
    else (tid, InProgressC[Nat.nat](n)) :: bdd)

def traiterMessageAck(tid: (Nat.nat, (Nat.nat, Nat.nat)), n: Nat.nat,
                       bdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                                   state[Nat.nat])]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat])]
  =
  (if (Lista.member[(Nat.nat, (Nat.nat, Nat.nat))](returnAllKeys(bdd), tid))
    (table.assoc[(Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat]](tid, bdd) match
       {
       case table.Somea(Validated(_)) => bdd
       case table.Somea(InProgressC(x)) =>
         (if (Nat.less_nat(x, n))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         state[Nat.nat]](tid, InProgressM[Nat.nat](n), bdd)
           else bdd)
       case table.Somea(InProgressM(x)) =>
         (if (Nat.less_nat(x, n))
           table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                         state[Nat.nat]](tid, InProgressM[Nat.nat](n), bdd)
           else bdd)
       case table.Somea(Canceled()) => bdd
        case table.Nonea() => bdd
     })
    else (tid, InProgressC[Nat.nat](n)) :: bdd)

def traiterMessage(x0: message,
                    bdd: List[((Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat])]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), state[Nat.nat])]
  =
  (x0, bdd) match {
  case (Pay(tid, x), bdd) => traiterMessagePay(tid, x, bdd)
  case (Ack(tid, x), bdd) => traiterMessageAck(tid, x, bdd)
  case (Cancel(tid), bdd) =>
    table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
                  state[Nat.nat]](tid, Canceled[Nat.nat](), bdd)
}

} /* object tp89 */
