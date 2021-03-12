theory tp89
  imports Main "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)
 "table"
begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

type_synonym transaction= "transid * nat"

datatype 'a state = Validated 'a | InProgressC 'a| InProgressM 'a | Canceled

type_synonym transBdd = "(transid, nat state) table" 

fun returnAllKeys::"transBdd \<Rightarrow> transid list"
  where 
"returnAllKeys [] = []"
|"returnAllKeys ((tid , idState)#bdd) = tid#(returnAllKeys bdd)"

fun traiterMessagePay:: "transid \<Rightarrow> nat \<Rightarrow> transBdd \<Rightarrow> transBdd"
  where 
"traiterMessagePay tid n bdd = (if (List.member (returnAllKeys bdd) tid) then
(let tidState = assoc tid bdd in 
(case tidState of Some(Validated x) \<Rightarrow> bdd |
                  Some(InProgressC x) \<Rightarrow> (if (n > x) then modify tid (InProgressC n) bdd else bdd) |
                  Some(InProgressM x) \<Rightarrow> (if (n > x) then modify tid (Validated n) bdd else bdd)|
                  Some(Canceled) \<Rightarrow> bdd | None \<Rightarrow> bdd)) 

 else ((tid, (InProgressC n))#bdd))"

fun traiterMessageAck:: "transid \<Rightarrow> nat \<Rightarrow> transBdd \<Rightarrow> transBdd"
  where 
"traiterMessageAck  tid n bdd = (if (List.member (returnAllKeys bdd) tid) then
(let tidState = assoc tid bdd in 
(case tidState of Some(Validated x) \<Rightarrow> bdd |
                  Some(InProgressC x) \<Rightarrow> (if (n > x) then modify tid (InProgressM n) bdd else bdd) |
                  Some(InProgressM x) \<Rightarrow> (if (n > x) then modify tid (InProgressM n) bdd else bdd)|
                  Some(Canceled) \<Rightarrow> bdd | None \<Rightarrow> bdd)) 

 else ((tid, (InProgressC n))#bdd))"

fun traiterMessage :: "message \<Rightarrow> transBdd \<Rightarrow> transBdd"
  where 
"traiterMessage (Pay tid x) bdd = (traiterMessagePay tid x bdd)"
|"traiterMessage (Ack tid x) bdd = (traiterMessageAck tid x bdd)"
|"traiterMessage (Cancel tid) bdd = modify tid (Canceled) bdd"

fun export :: "transBdd \<Rightarrow> transaction list"
  where 
"export [] = []"
|"export ((tid, x)#xs) = (case x of Validated y \<Rightarrow> ((tid, y)#(export xs)) | _ \<Rightarrow>(export xs)) "

fun traiterMessageList :: "message list \<Rightarrow> transBdd \<Rightarrow> transBdd"
where
"traiterMessageList [] t = t"
|"traiterMessageList (x#xs) t = traiterMessageList xs (traiterMessage x t)"

(* Toutes les transactions validees ont un montant strictement superieur a 0*)
lemma prop1:"(List.member (export (traiterMessageList msgL [])) (tid, val)) \<longrightarrow> (val>0)"
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
sorry

fun returnTransId::"transaction list \<Rightarrow> transid list"
  where 
"returnTransId [] = []"
|"returnTransId ((tid , idState)#x) = tid#(returnTransId x)"

lemma prop2:"(List.distinct(returnTransId (export (traiterMessageList msgL []) )) )"
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
  sorry

lemma prop3:" (List.member (traiterMessage (Cancel tid) ((traiterMessageList msgL []))) (tid, Canceled))"
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
sorry

lemma prop4:"List.member msgL (Cancel tid) \<longrightarrow> \<not>(List.member (export (traiterMessageList msgL [])) (tid,x))"
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
  sorry

lemma prop5:"((List.member msgL (Pay tid amc))\<and>(List.member msgL (Ack tid amm))
               \<and>(amc>0)\<and>(amc \<ge> amm)\<and>\<not>(List.member msgL (Cancel tid)))
               \<longrightarrow> (List.member (export (traiterMessageList msgL [])) (tid,x))"
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
  sorry

lemma prop6:"\<forall>x. List.member (export (traiterMessageList msgL [])) (tid,x)
             \<longrightarrow>((List.member msgL (Pay tid amc))\<and>(List.member msgL (Ack tid amm)) \<and> (amc \<ge> amm))"
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
  sorry

fun returnVal::"transBdd \<Rightarrow> nat list"
  where 
"returnVal [] = []"
|"returnVal ((tid, idState)#bdd)  = (case idState of Validated x \<Rightarrow> x#returnVal bdd
                                                    |InProgressC x \<Rightarrow> x#returnVal bdd
                                                    |InProgressM x \<Rightarrow> x#returnVal bdd
                                                    | Canceled \<Rightarrow> returnVal bdd ) "

lemma prop7M:" List.member msgL (Ack tid x) \<longrightarrow> (\<forall>y. (y<x) \<and> List.member  (returnVal(traiterMessageList msgL [])) y)   "
  nitpick
  sorry

lemma prop7C:" List.member msgL (Pay tid x) \<longrightarrow> (\<forall>y. (y<x) \<and> List.member  (returnVal(traiterMessageList msgL [])) y)   "
  nitpick
  sorry

lemma prop8:"(List.member (export (traiterMessageList messages [])) (transid,n))
            \<longrightarrow> (\<not>(List.member Msg (Cancel transid))) \<longrightarrow> (List.member (export (traiterMessageList (List.append messages Msg) [])) (transid,n)) "
nitpick [timeout=20]
quickcheck [narrowing, timeout=20, size=9]
  sorry

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

