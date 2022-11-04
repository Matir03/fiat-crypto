Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.ZArith.ZArith Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)

Module QF.
  Section QF.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {r : F} {r_nqr : forall x : F, ~Feq (Fmul x x) r}.
    
    Local Infix "=" := Feq : type_scope.
    Local Notation "0" := Fzero. Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Notation "- x" := (Fopp x). 
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ -1" := (Finv x) (at level 20).
    
    Definition QF : Type := F * F.

    Definition eq (x y : QF) := fst x = fst y /\ snd x = snd y.
    Local Infix "=" := eq : type_scope.  

    Definition QF_of_F (x : F) : QF := (x, 0).
    Coercion QF_of_F: F >-> QF.

    Definition zero : QF := (0, 0).
    Definition one : QF := (1, 0).
    Definition opp (x : QF) := (-fst x, -snd x).
    Definition add (x y : QF) := (fst x + fst y, snd x + snd y).
    Definition sub (x y : QF) := (fst x - fst y, snd x - snd y).
    Definition mul (x y : QF) :=
        let (a, b) := x in
        let (c, d) := y in
        (a*c + b*d*r, a*d + b*c).
    Definition conj (x : QF) := (fst x, -snd x).
    Definition norm (x : QF) := let (a, b) := x in a*a - r*b*b.
    Definition inv (x : QF) := mul (conj x) ((norm x)^-1).
    Definition div (x y : QF) := mul x (inv y).

    Lemma QF_neq {a b c d : F} (h : ~eq (a, b) (c, d)) : ~Feq a c \/ ~Feq b d.
    Proof.
      pose proof (Feq_dec a c) as h1.
      pose proof (Feq_dec b d) as h2.
      destruct h1; destruct h2.
      destruct h; split; cbv; assumption.
      all: tauto.
    Qed.

    Lemma norm_nonzero {x : QF} (h : ~eq x 0) : ~Feq (norm x) 0.
    Proof.
      destruct x as (a, b).
      cbv. intro.
      pose proof (QF_neq h) as hn.
      destruct hn.
      all: apply (r_nqr (a/b)); fsatz.
    Qed.

    Global Instance QF_field : @Algebra.Hierarchy.field QF eq zero one opp add sub mul inv div.
    Proof.
      repeat match goal with 
      | [x : QF |- _] => destruct x
      | [h : eq _ _ |- _] => destruct h
      | _ => fsatz
      | _ => progress cbv [zero one opp add sub mul inv div QF_of_F norm conj fst snd] in *
      | _ => split; intros
      | [h : ~eq _ _ |- _] => pose proof (norm_nonzero h)
      | [ |- ~ _] => intro
      end.
      all: setoid_subst_rel Feq; fsatz.   
    Qed.
        
  End QF.
End QF.

Notation QF := QF.QF.
Declare Scope QF_scope.
Delimit Scope QF_scope with QF.
Bind Scope QF_scope with QF.QF.

Module F2.    
  Definition F2 (p : positive) := @QF (F p).

  Section Field.
    Context {p : positive} {prime_p : prime p}
           {r : F p} {r_nqr : forall x : F p, (x * x <> r)%F}.

    Definition Fp := F p.
    Definition Fp2 := F2 p.
    
    Definition F2_of_F : Fp -> Fp2 := @QF.QF_of_F Fp F.zero.
    Coercion F2_of_F: Fp >-> Fp2.

    Definition eq := @QF.eq Fp Logic.eq.
    Definition zero : Fp2 := @QF.zero Fp 0%F.
    Definition one : Fp2 := @QF.one Fp 0%F 1%F. 
    Definition opp : Fp2 -> Fp2 := @QF.opp Fp F.opp.
    Definition add : Fp2 -> Fp2 -> Fp2 := @QF.add Fp F.add.
    Definition sub : Fp2 -> Fp2 -> Fp2 := @QF.sub Fp F.sub.
    Definition mul : Fp2 -> Fp2 -> Fp2 := @QF.mul Fp F.add F.mul r.
    Definition inv : Fp2 -> Fp2 := @QF.inv Fp F.zero F.opp F.add F.sub F.mul F.inv r.
    Definition div : Fp2 -> Fp2 -> Fp2 := @QF.div Fp F.zero F.opp F.add F.sub F.mul F.inv r.

    Global Instance field_Fp2 : @Algebra.Hierarchy.field Fp2 eq zero one opp add sub mul inv div.
    Proof.
      eapply QF.QF_field.
      Unshelve.
      assumption.
    Qed.
  End Field.
  
  Local Open Scope F_scope.

  Section SquareRoots.
    Context {p : positive} {prime_p : prime p} {p_odd : 2 < p}
      {r : F p} {r_nqr : forall x : F p, x * x <> r}.
    
    Definition legendre (a : F p) := a ^ (Z.to_N (p / 2)).

    Lemma euler_criterion (a : F p) (a_nonzero : a <> 0) :
      (legendre a = 1) <-> (exists b, b*b = a).
    Admitted.

    Lemma legendre_multiplicative (a b : F p) :
      legendre (a * b) = legendre a * legendre b. 
    Admitted.

    Lemma legendre_square_one (a : F p) {a_nonzero : a <> 0} :
      legendre (a * a) = 1.
    Admitted.

    Lemma legendre_zero_zero :
      legendre 0 = 0.
    Admitted.

    Lemma legendre_pm_one {a : F p} (a_nonzero : a <> 0) :
      legendre a = 1 \/ legendre a = F.opp 1.
    Admitted.

    Lemma euler_criterion' (a : F p) (a_nonzero : a <> 0) :
      (legendre a = F.opp 1) <-> (~exists b, b*b = a).
    Admitted.

    Lemma r_nonzero :
      r <> 0.
    Proof.
      intro.
      apply (r_nqr 0).
      fsatz.
    Admitted.

    Lemma legendre_r_minus_one :
      legendre r = F.opp 1.
    Proof.
      pose proof r_nonzero.
      pose proof @legendre_pm_one r H as pm_one.
      destruct pm_one.
      rewrite euler_criterion in H0.
      destruct H0.
      exfalso.
      eapply r_nqr.
      all: eassumption.
    Admitted.
    
    Lemma sqrt_exists (x : F p) : exists y : F2 p, @F2.mul p r y y = (x, 0%F).
    Proof.
      pose proof (@F.Decidable_square p prime_p p_odd x).
      destruct H.
      {
        destruct e.
        exists (x0, 0%F).
        unfold mul.
        unfold QF.mul.
        f_equal; fsatz.
      }
      rewrite <- euler_criterion' in n.
      pose proof r_nonzero.
      pose proof legendre_r_minus_one.
      pose proof legendre_multiplicative r (x/r).
      assert (r * (x/r) = x) by fsatz.
      rewrite H2 in H1.
      rewrite n in H1.
      rewrite H0 in H1.
      assert (legendre (x/r) = 1) by fsatz.
      rewrite euler_criterion in H3.
      destruct H3.
      exists (0, x0).
      unfold mul.
      unfold QF.mul.
      f_equal.
      fsatz.
      fsatz.
      intro.
      rewrite H4 in H3.
      rewrite legendre_zero_zero in H3.
      fsatz.
      intro.
      destruct n.
      exists 0.
      fsatz.
    Admitted.
      
  End SquareRoots.
End F2.