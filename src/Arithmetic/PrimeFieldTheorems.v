Require Export Crypto.Spec.ModularArithmetic.
Require Export Crypto.Arithmetic.ModularArithmeticTheorems.
Require Export Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

Require Import Coq.nsatz.Nsatz.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.ModularArithmeticPre.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.ZArith.ZArith Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Decidable.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Algebra.Hierarchy Crypto.Algebra.Field.

Existing Class prime.
Local Open Scope F_scope.

Module F.
  Section Field.
    Context (q:positive) {prime_q:prime q}.
    Lemma inv_spec : F.inv 0%F = (0%F : F q)
                     /\ (prime q -> forall x : F q, x <> 0%F -> (F.inv x * x)%F = 1%F).
    Proof using Type. change (@F.inv q) with (proj1_sig (@F.inv_with_spec q)); destruct (@F.inv_with_spec q); eauto. Qed.

    Lemma inv_0 : F.inv 0%F = F.of_Z q 0. Proof using Type. destruct inv_spec; auto. Qed.
    Lemma inv_nonzero (x:F q) : (x <> 0 -> F.inv x * x%F = 1)%F. Proof using Type*. destruct inv_spec; auto. Qed.

    Global Instance field_modulo : @Algebra.Hierarchy.field (F q) Logic.eq 0%F 1%F F.opp F.add F.sub F.mul F.inv F.div.
    Proof using Type*.
      repeat match goal with
             | _ => solve [ solve_proper
                          | apply F.commutative_ring_modulo
                          | apply inv_nonzero
                          | cbv [F.zero F.one not]; pose proof prime_ge_2 q prime_q;
                            rewrite F.eq_to_Z_iff, !F.to_Z_of_Z, !Zmod_small; lia ]
             | _ => split
             end.
    Qed.
  End Field.

  Section NumberThoery.
    Context {q:positive} {prime_q:prime q} {two_lt_q: 2 < q}
    {char_ge_3:@Ring.char_ge (F q) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.


    (* TODO: move to PrimeFieldTheorems *)
    Lemma to_Z_1 : @F.to_Z q 1 = 1%Z.
    Proof using two_lt_q. simpl. rewrite Zmod_small; lia. Qed.

    Lemma Fq_inv_fermat (x:F q) : F.inv x = x ^ Z.to_N (q - 2)%Z.
    Proof using Type*.
      destruct (dec (x = 0%F)) as [?|Hnz].
      { subst x; rewrite inv_0, F.pow_0_l; trivial.
        change (0%N) with (Z.to_N 0%Z); rewrite Z2N.inj_iff; lia. }
      erewrite <-Algebra.Field.inv_unique; try reflexivity.
      rewrite F.eq_to_Z_iff, F.to_Z_mul, F.to_Z_pow, Z2N.id, to_Z_1 by lia.
      apply (fermat_inv q _ (F.to_Z x)); rewrite F.mod_to_Z; eapply F.to_Z_nonzero; trivial.
    Qed.

    Definition legendre (a : F q) := a ^ (Z.to_N (q / 2)).

    Lemma legendre_multiplicative (a b : F q) :
      legendre (a * b) = legendre a * legendre b. 
    Proof. apply F.pow_mul_l. Qed.
    
    Lemma euler_criterion (a : F q) (a_nonzero : a <> 0) :
      (legendre a = 1) <-> (exists b, b*b = a).
    Proof using Type*.
      unfold legendre.
      pose proof F.to_Z_nonzero_range a; pose proof (odd_as_div q).
      specialize_by (destruct (Z.prime_odd_or_2 _ prime_q); try lia; trivial).
      rewrite F.eq_to_Z_iff, !F.to_Z_pow, !to_Z_1, !Z2N.id by lia.
      rewrite F.square_iff, <-(euler_criterion (q/2)) by (trivial || lia); reflexivity.
    Qed.

    Lemma legendre_square_one (a : F q) {a_nonzero : a <> 0} :
      legendre (a * a) = 1.
    Proof.
      rewrite euler_criterion.
      - exists a. fsatz.
      - fsatz.
    Qed.

    Lemma legendre_pm_one {a : F q} (a_nonzero : a <> 0) :
      legendre a = 1 \/ legendre a = F.opp 1.
    Proof.
      eapply only_two_square_roots_choice.
      {
        erewrite <- legendre_multiplicative.
        eapply legendre_square_one.
        assumption.
      }
      fsatz.
    Qed.

    Lemma euler_criterion' (a : F q) (a_nonzero : a <> 0) :
      (legendre a = F.opp 1) <-> (~exists b, b*b = a).
    Proof.
      split.
      {
        intros.
        intro hb.
        destruct hb.
        rewrite <- H0 in H.
        rewrite legendre_square_one in H; fsatz.
      }
      intro.
      pose proof (legendre_pm_one a_nonzero).
      destruct H0.
      - exfalso. apply H. rewrite <- euler_criterion; assumption.
      - assumption.
    Qed.
    
    Global Instance Decidable_square : forall (x:F q), Decidable (exists y, y*y = x).
    Proof.
      intro x; destruct (dec (x = 0)).
      { left. abstract (exists 0; subst; apply Ring.mul_0_l). }
      { eapply Decidable_iff_to_impl; [eapply euler_criterion; assumption | exact _]. }
    Defined.
  End NumberThoery.

  Section SquareRootsPrime3Mod4.
    Context {q:positive} {prime_q: prime q} {q_3mod4 : q mod 4 = 3}.

    Add Field _field2 : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
                          (morphism (F.ring_morph q),
                           constants [F.is_constant],
                           div (F.morph_div_theory q),
                           power_tac (F.power_theory q) [F.is_pow_constant]).

    Definition sqrt_3mod4 (a : F q) : F q := a ^ Z.to_N (q / 4 + 1).

    Global Instance Proper_sqrt_3mod4 : Proper (eq ==> eq ) sqrt_3mod4.
    Proof using Type. repeat intro; subst; reflexivity. Qed.

    Lemma two_lt_q_3mod4 : 2 < q.
    Proof using Type*.
      pose proof (prime_ge_2 q _) as two_le_q.
      destruct (Zle_lt_or_eq _ _ two_le_q) as [H|H]; [exact H|].
      rewrite <-H in q_3mod4; discriminate.
    Qed.
    Local Hint Resolve two_lt_q_3mod4 : core.

    Lemma sqrt_3mod4_correct (x:F q) :
      ((exists y, y*y = x) <-> (sqrt_3mod4 x)*(sqrt_3mod4 x) = x)%F.
    Proof using Type*.
      cbv [sqrt_3mod4]; intros.
      destruct (F.eq_dec x 0);
      repeat match goal with
             | |- _ => progress unfold legendre
             | |- _ => progress subst
             | |- _ => progress rewrite ?F.pow_0_l, <-?F.pow_add_r
             | |- _ => progress rewrite <-?Z2N.inj_0, <-?Z2N.inj_add by Z.zero_bounds
             | |- _ => rewrite <-@euler_criterion by auto
             | |- ?x ^ (?f _) = ?a <-> ?x ^ (?f _) = ?a => do 3 f_equiv; [ ]
             | |- _ => rewrite !Zmod_odd in *; repeat (break_match; break_match_hyps); lia
             | |- _ => rewrite Z.rem_mul_r in * by lia
             | |- (exists x, _) <-> ?B => assert B by field; solve [intuition eauto]
             | |- (?x ^ Z.to_N ?a = 1) <-> _ =>
               transitivity (x ^ Z.to_N a * x ^ Z.to_N 1 = x);
                 [ rewrite F.pow_1_r, Algebra.Field.mul_cancel_l_iff by auto; reflexivity | ]
             | |- (_ <> _)%N => rewrite Z2N.inj_iff by Z.zero_bounds
             | |- (?a <> 0)%Z => assert (0 < a) by Z.zero_bounds; lia
             | |- (_ = _)%Z => replace 4 with (2 * 2)%Z in * by ring;
                                 rewrite <-Z.div_div by Z.zero_bounds;
                                 rewrite Z.add_diag, Z.mul_add_distr_l, Z.mul_div_eq by lia
             end.
    Qed.
  End SquareRootsPrime3Mod4.

  Section SquareRootsPrime5Mod8.
    Context {q:positive} {prime_q: prime q} {q_5mod8 : q mod 8 = 5}.
    Local Open Scope F_scope.
    Add Field _field3 : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
                          (morphism (F.ring_morph q),
                           constants [F.is_constant],
                           div (F.morph_div_theory q),
                           power_tac (F.power_theory q) [F.is_pow_constant]).

    (* Any nonsquare element raised to (q-1)/4 (real implementations use 2 ^ ((q-1)/4) )
       would work for sqrt_minus1 *)
    Context (sqrt_minus1 : F q) (sqrt_minus1_valid : sqrt_minus1 * sqrt_minus1 = F.opp 1).

    Lemma two_lt_q_5mod8 : 2 < q.
    Proof using prime_q q_5mod8.
      pose proof (prime_ge_2 q _) as two_le_q.
      destruct (Zle_lt_or_eq _ _ two_le_q) as [H|H]; [exact H|].
      rewrite <-H in *. discriminate.
    Qed.
    Local Hint Resolve two_lt_q_5mod8 : core.

    Definition sqrt_5mod8 (a : F q) : F q :=
      let b := a ^ Z.to_N (q / 8 + 1) in
      if dec (b ^ 2 = a)
      then b
      else sqrt_minus1 * b.

    Global Instance Proper_sqrt_5mod8 : Proper (eq ==> eq ) sqrt_5mod8.
    Proof using Type. repeat intro; subst; reflexivity. Qed.

    Lemma eq_b4_a2 (x : F q) (Hex:exists y, y*y = x) :
      ((x ^ Z.to_N (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2.
    Proof using prime_q q_5mod8.
      pose proof two_lt_q_5mod8.
      assert (0 <= q/8)%Z by (apply Z.div_le_lower_bound; rewrite ?Z.mul_0_r; lia).
      assert (Z.to_N (q / 8 + 1) <> 0%N) by
          (intro Hbad; change (0%N) with (Z.to_N 0%Z) in Hbad; rewrite Z2N.inj_iff in Hbad; lia).
      destruct (dec (x = 0)); [subst; rewrite !F.pow_0_l by (trivial || lazy_decide); reflexivity|].
      rewrite !F.pow_pow_l.

      replace (Z.to_N (q / 8 + 1) * (2*2))%N with (Z.to_N (q / 2 + 2))%N.
      2: { (* this is a boring but gnarly proof :/ *)
        change (2*2)%N with (Z.to_N 4).
        rewrite <- Z2N.inj_mul by Z.zero_bounds.
        apply Z2N.inj_iff; try Z.zero_bounds.
        rewrite <- Z.mul_cancel_l with (p := 2) by lia.
        ring_simplify.
        rewrite Z.mul_div_eq by lia.
        rewrite Z.mul_div_eq by lia.
        rewrite (Zmod_div_mod 2 8 q) by
            (try lia; apply Zmod_divide; lia || auto).
        rewrite q_5mod8.
        replace (5 mod 2)%Z with 1%Z by auto.
        ring.
      }

      rewrite Z2N.inj_add, F.pow_add_r by Z.zero_bounds.
      replace (x ^ Z.to_N (q / 2)) with (F.of_Z q 1) by
          (symmetry; apply @euler_criterion; eauto).
      change (Z.to_N 2) with 2%N; ring.
    Qed.

    Lemma mul_square_sqrt_minus1 : forall x, sqrt_minus1 * x * (sqrt_minus1 * x) = F.opp (x * x).
    Proof using prime_q sqrt_minus1_valid.
      intros x.
      transitivity (F.opp 1 * (x * x)); [ | field].
      rewrite <-sqrt_minus1_valid.
      field.
    Qed.

    Lemma eq_b4_a2_iff (x : F q) : x <> 0 ->
      ((exists y, y*y = x) <-> ((x ^ Z.to_N (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2).
    Proof using Type*.
      split; try apply eq_b4_a2.
      intro Hyy.
      rewrite !@F.pow_2_r in *.
      destruct (Field.only_two_square_roots_choice _ x (x * x) Hyy eq_refl); clear Hyy;
        [ eexists; eassumption | ].
      match goal with H : ?a * ?a = F.opp _ |- _ => exists (sqrt_minus1 * a);
        rewrite mul_square_sqrt_minus1; rewrite H end.
      field.
    Qed.

    Lemma sqrt_5mod8_correct : forall x,
      ((exists y, y*y = x) <-> (sqrt_5mod8 x)*(sqrt_5mod8 x) = x).
    Proof using Type*.
      cbv [sqrt_5mod8]; intros x.
      destruct (F.eq_dec x 0).
      {
        repeat match goal with
             | |- _ => progress subst
             | |- _ => progress rewrite ?F.pow_0_l
             | |- (_ <> _)%N => rewrite <-Z2N.inj_0, Z2N.inj_iff by Z.zero_bounds
             | |- (?a <> 0)%Z => assert (0 < a) by Z.zero_bounds; lia
             | |- _ => congruence
             end.
        break_match;
          match goal with |- _ <-> ?G => assert G by field end; intuition eauto.
      } {
        rewrite eq_b4_a2_iff by auto.
        rewrite !@F.pow_2_r in *.
        break_match.
        intuition (f_equal; eauto).
        split; intro A. {
          destruct (Field.only_two_square_roots_choice _ x (x * x) A eq_refl) as [B | B];
            clear A; try congruence.
          rewrite mul_square_sqrt_minus1, B; field.
        } {
          rewrite mul_square_sqrt_minus1 in A.
          transitivity (F.opp x * F.opp x); [ | field ].
          f_equal; rewrite <-A at 3; field.
        }
      }
    Qed.
  End SquareRootsPrime5Mod8.

  Module Iso.
    Section IsomorphicRings.
      Context {q:positive} {prime_q:prime q} {two_lt_q:2 < Z.pos q}.
      Context
        {H : Type} {eq : H -> H -> Prop} {zero one : H}
        {opp : H -> H} {add sub mul : H -> H -> H}
        {phi : F q -> H} {phi' : H -> F q}
        {phi'_phi : forall A : F q, Logic.eq (phi' (phi A)) A}
        {phi'_iff : forall a b : H, iff (Logic.eq (phi' a) (phi' b)) (eq a b)}
        {phi'_zero : Logic.eq (phi' zero) F.zero} {phi'_one : Logic.eq (phi' one) F.one}
        {phi'_opp : forall a : H, Logic.eq (phi' (opp a)) (F.opp (phi' a))}
        {phi'_add : forall a b : H, Logic.eq (phi' (add a b)) (F.add (phi' a) (phi' b))}
        {phi'_sub : forall a b : H, Logic.eq (phi' (sub a b)) (F.sub (phi' a) (phi' b))}
        {phi'_mul : forall a b : H, Logic.eq (phi' (mul a b)) (F.mul (phi' a) (phi' b))}.
      (* TODO: revive this once we figure out how to spec the pow impl
      Definition inv (x:H) := pow x (NtoP (Z.to_N (q - 2)%Z)).
      Definition div x y := mul (inv y) x.

      Lemma ring :
        @Algebra.Hierarchy.ring H eq zero one opp add sub mul
        /\ @Ring.is_homomorphism (F q) Logic.eq F.one F.add F.mul H eq one add mul phi
        /\ @Ring.is_homomorphism H eq one add mul (F q) Logic.eq F.one F.add F.mul phi'.
      Proof using phi'_add phi'_iff phi'_mul phi'_one phi'_opp phi'_phi phi'_sub phi'_zero. eapply @Ring.ring_by_isomorphism; assumption || exact _. Qed.
      Local Instance _iso_ring : Algebra.Hierarchy.ring := proj1 ring.
      Local Instance _iso_hom1 : Ring.is_homomorphism := proj1 (proj2 ring).
      Local Instance _iso_hom2 : Ring.is_homomorphism := proj2 (proj2 ring).

      Let inv_proof : forall a : H, phi' (inv a) = F.inv (phi' a).
      Proof.
        intros.
        cbv [inv]. rewrite (Fq_inv_fermat(q:=q)(two_lt_q:=two_lt_q)).
        rewrite <-Z_nat_N at 1 2.
        rewrite (ScalarMult.homomorphism_scalarmult(phi:=phi')(MUL_is_scalarmult:=pow_is_scalarmult)(mul_is_scalarmult:=F.pow_is_scalarmult)).
        reflexivity.
        assumption.
      Qed.

      Let div_proof : forall a b : H, phi' (mul (inv b) a) = phi' a / phi' b.
      Proof.
        intros.
        rewrite phi'_mul, inv_proof, Algebra.Hierarchy.field_div_definition, Algebra.Hierarchy.commutative.
        reflexivity.
      Qed.

      Lemma field_and_iso :
        @Algebra.Hierarchy.field H eq zero one opp add sub mul inv div
        /\ @Ring.is_homomorphism (F q) Logic.eq F.one F.add F.mul H eq one add mul phi
        /\ @Ring.is_homomorphism H eq one add mul (F q) Logic.eq F.one F.add F.mul phi'.
      Proof using Type*. eapply @Field.field_and_homomorphism_from_redundant_representation;
               assumption || exact _ || exact inv_proof || exact div_proof. Qed.
      *)
    End IsomorphicRings.
  End Iso.
End F.
