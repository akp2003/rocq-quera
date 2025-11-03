From Stdlib Require Import String Ascii Unicode.Utf8 Lia.
Open Scope string_scope.
    
Definition endswith e s := 
    match Nat.leb (length e) (length s) with
    | true => substring (length s - length e) (length e) s =? e
    | false => false
    end.

Lemma length_correct1 s1 s2 : length s1 + length s2 = length (s1 ++ s2).
Proof.
    induction s1.
    - simpl. easy.
    - simpl. lia.
Defined.

Lemma substring_correct3 s n : substring (length s) n s = "".
Proof.
    induction n.
    - induction s. easy. easy.
    - induction s. easy. auto.
Defined.

Lemma append_empty_l s : "" ++ s = s. auto. Defined.

Lemma substring_correct4 s : substring 0 (length s) s = s.
Proof.
    induction s. 
    easy. simpl.
    rewrite IHs.
    reflexivity.
Defined.

Lemma substring_succ s n m a :
 substring n m s = substring (S n) m (String a s). auto.
Defined.

Lemma endswith_correct1 s1 s2 : endswith s2 (s1 ++ s2) = true.
Proof.
    unfold endswith.
    simpl.
    erewrite (Compare_dec.leb_correct _ _ _).
    induction s1.
    - induction s2. auto.
      rewrite append_empty_l in *.
      rewrite PeanoNat.Nat.sub_diag. 
      rewrite substring_correct4.
      apply String.eqb_refl.
    - rewrite <-length_correct1 in *.
      replace (_ + _ - _) with (length (String a s1)) by lia.
      replace (_ + _ - _) with (length s1) in IHs1 by lia.
      simpl. exact IHs1.
      Unshelve.
      rewrite <-length_correct1.
      lia.  
Defined.

Lemma app_assoc s1 s2 s3 : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof.
  induction s1; simpl; f_equal; auto.
Defined.

Fixpoint rep a n :=
    match n with
    | 0 => EmptyString
    | S n' => String a (rep a n')
    end.

Lemma rep_correct1 a n : length (rep a n) = n.
Proof.
  induction n.
  easy.
  simpl. lia.
Defined.

Lemma rep_correct2 a n : rep a (S n) = String a (rep a n). auto. Defined.

Lemma rep_correct3 a n i : 0 <= i < n → get i (rep a n) = Some a.
Proof.
  revert i.
  induction n.
  - easy.
  - intros. destruct i.
    reflexivity.
    simpl. rewrite IHn.
    reflexivity.
    lia.
Defined.

Theorem Wow n : 
    {s | (get 0 s = Some "W"%char) /\ 
    (∀i, 0<i<=n → (get i s = Some "o"%char)) /\
    (endswith "w!" s = true)}.
Proof.
    exists ("W" ++ (rep "o" n) ++ "w!").
    assert (length ("W" ++ (rep "o" n) ++ "w!") = n+3).
    1 : {
    induction n.
      + easy.
      + simpl in *.
        rewrite IHn.
        reflexivity. }
    repeat split.
    - intros.
      induction i.
      easy. simpl.
      rewrite <-append_correct1.
      apply rep_correct3.
      lia.
      rewrite rep_correct1.
      lia.
    - rewrite app_assoc,(endswith_correct1 _ "w!").
      reflexivity.
Defined.


Definition answer n := proj1_sig (Wow n).

From Corelib Require Import Extraction.
Require Import ExtrHaskellString.
Require Import ExtrHaskellNatNum.
Extraction Language Haskell.
Extract Inductive Datatypes.nat => "Prelude.Integer" ["0" "succ"]
"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extraction answer.
Extraction "Desktop/haskell/code.hs" answer.

(* Add this in the end of your haskell file and change your module name to Main

main = do
       input1 <- Prelude.getLine
       let x = (Prelude.read input1 :: Prelude.Integer)
       Prelude.print (answer x)
       
*)