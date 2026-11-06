From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes check_reject_clean_starved_c.
Import ListNotations.
Open Scope Z_scope.

Lemma crs_djb2_cons : forall h (c : byte) r,
  djb2 h (zb (c :: r)) = djb2 ((33 * h + bv_unsigned c) mod 2 ^ 64) (zb r).
Proof. reflexivity. Qed.

Lemma crs_read1 : forall m p (c : byte) r,
  bytes_at rsegs m p (c :: r) -> ov_read_bytes rsegs m (wa p) 1 = Some [c].
Proof.
  intros m p c r HB. rewrite <- (Z.add_0_r p) at 1.
  rewrite (bytes_at_read rsegs m p _ 0 1 HB) by (cbn; lia). reflexivity.
Qed.

Lemma crs_tail : forall m p (c : byte) r,
  bytes_at rsegs m p (c :: r) -> bytes_at rsegs m (p + 1) r.
Proof.
  intros m p c r HB. apply (proj1 (bytes_at_app rsegs m p [c] r)) in HB. destruct HB as [_ HB]. exact HB.
Qed.

Ltac crsu_has_cmp x := idtac; match x with context [Z.eqb _ _] => idtac | context [Z.ltb _ _] => idtac
  | context [Z.leb _ _] => idtac end.

Ltac crsu_is_binop f :=
  lazymatch f with
  | Z.add => idtac | Z.sub => idtac | Z.mul => idtac | Z.modulo => idtac | Z.div => idtac | Z.pow => idtac
  | Z.lxor => idtac | Z.lor => idtac | Z.land => idtac | Z.shiftr => idtac | Z.shiftl => idtac
  | Z.eqb => idtac | Z.ltb => idtac | Z.leb => idtac
  end.

Ltac crsu_fold_lits :=
  repeat match goal with
  | |- context [?f ?a ?b] => crsu_is_binop f; is_Zlit_zb a; is_Zlit_zb b;
                             let v := eval vm_compute in (f a b) in change (f a b) with v
  end.

Ltac crsu_solve_c :=
  unfold bv_eqb, bv_ltu, bv_leu;
  rewrite ?unsigned_lit_wrap;
  repeat (cbn [Z.b2z]; crsu_fold_lits;
          match goal with
          | |- context [Z.eqb ?a ?b] => assert_fails (crsu_has_cmp a); assert_fails (crsu_has_cmp b);
                                         destruct (Z.eqb_spec a b)
          | |- context [Z.ltb ?a ?b] => assert_fails (crsu_has_cmp a); assert_fails (crsu_has_cmp b);
                                         destruct (Z.ltb_spec a b)
          | |- context [Z.leb ?a ?b] => assert_fails (crsu_has_cmp a); assert_fails (crsu_has_cmp b);
                                         destruct (Z.leb_spec a b)
          end);
  cbn [Z.b2z]; crsu_fold_lits;
  first [reflexivity | exfalso; Z.div_mod_to_equations; lia].

Ltac crsu_br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; crsu_solve_c); cbv beta iota
  end.

Lemma crsu_sltiu : forall p, 1 <= p < 2 ^ 64 -> v_sltiu (Z_to_bv 64 p) 1 = Z_to_bv 64 0.
Proof.
  intros p Hp. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec p 1); [lia | reflexivity].
Qed.

Lemma crs_hash_val : forall h (c : byte), 0 <= h < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 h)) 5 + h + bv_unsigned (zxb c)) =
  Z_to_bv 64 ((33 * h + bv_unsigned c) mod 2 ^ 64).
Proof.
  intros h c Hh.
  assert (Hc : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  unfold zxb. rewrite (unsigned_lit h) by lia. rewrite (unsigned_lit (bv_unsigned c)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply bv_eq. rewrite !unsigned_lit_wrap. rewrite Zmod_mod. f_equal. change (2 ^ 5) with 32. lia.
Qed.

Local Ltac crsu_iter IH :=
  lazymatch goal with
  | HB : bytes_at rsegs ?m ?p (?c :: ?r), HE : _ + Z.of_nat (length (_ :: _)) = ?E, Hh : 0 <= ?h < 2 ^ 64 |- _ =>
      pose proof (crs_read1 m p c r HB) as RD;
      pose proof (bytes_at_bound rsegs m p (c :: r) HB) as BB;
      pose proof (crs_tail m p c r HB) as HB';
      cbn [length] in HE, BB;
      rewrite crs_djb2_cons;
      step; crsu_br false;
      step; rewrite (crsu_sltiu p ltac:(lia));
      step; step; crsu_br false;
      step; crsu_br false;
      do 8 step;
      rewrite (crs_hash_val h c Hh);
      replace (Z.of_nat (length (c :: r)) + -1) with (Z.of_nat (length r)) by (cbn [length]; lia);
      destruct r as [|c' r];
      [ assert (HE1 : E = p + 1) by (cbn in HE; lia); clear HE; subst E;
        change (Z.of_nat (length (@nil byte))) with 0;
        crsu_br false;
        apply evt_done; cbv beta; eexists _, _; reflexivity
      | assert (Hl : 1 <= Z.of_nat (length (c' :: r)) < 2 ^ 64) by (cbn [length] in *; lia);
        crsu_br true;
        eapply IH; [exact HB' | congruence | lia | cbn [length] in *; lia | assumption | apply Z.mod_pos_bound; lia] ]
  end.

(* The two inline fuzz_pick loops of the #102 ubsan check_reject_clean_starved 0x13c3c: 0x13c94..0x13cc8 (the took pick)
   and 0x13d64..0x13d98 (the pretty starved write's pick), each with its UBSan pointer-overflow check to the trap 0x13e90.
   The third pick (the compact starved write's) is the out-of-line `jal fuzz_pick` at 0x13e50 (fuzz_pick_c). *)
Lemma crsu_l1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D E : Z) (tl : list byte) (p h : Z) (a5 a6 : word),
  bytes_at rsegs m p tl -> tl <> [] -> 0 < D <= p -> p + Z.of_nat (length tl) = E -> E < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a5' a6' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (djb2 h (zb tl))) (Z_to_bv 64 1)
                     (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 0)
                     a5' a6' a7 s2 (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13cc8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) (Z_to_bv 64 1) (Z_to_bv 64 p) (Z_to_bv 64 p)
             (Z_to_bv 64 (Z.of_nat (length tl))) a5 a6 a7 s2 (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c94) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D E tl.
  induction tl as [|c r IH]; intros p h a5 a6 HB HNE HD HE HEb Hh; [congruence|].
  crsu_iter IH.
Qed.

Lemma crsu_l2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D E : Z) (tl : list byte) (p h : Z) (a6 a7 : word),
  bytes_at rsegs m p tl -> tl <> [] -> 0 < D <= p -> p + Z.of_nat (length tl) = E -> E < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a6' a7' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (djb2 h (zb tl))) (Z_to_bv 64 1)
                     (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 0)
                     a6' a7' s2 (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13d98) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 h) (Z_to_bv 64 1) (Z_to_bv 64 p) (Z_to_bv 64 p)
             (Z_to_bv 64 (Z.of_nat (length tl))) a6 a7 s2 (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d64) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D E tl.
  induction tl as [|c r IH]; intros p h a6 a7 HB HNE HD HE HEb Hh; [congruence|].
  crsu_iter IH.
Qed.
