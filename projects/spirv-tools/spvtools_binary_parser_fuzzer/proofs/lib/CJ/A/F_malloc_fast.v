(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma swrap_word x : Z_to_bv 64 (bv_swrap 32 x) = wz (sxv x).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma sxv_testbit_lo' v i : 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma sxv_cases' v : let u := v mod 2^32 in
  (u < 2^31 /\ sxv v = u) \/ (2^31 <= u /\ sxv v = u + 2^64 - 2^32).
Proof.
  cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
  destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.

Lemma testbit_31_mod32 v : Z.testbit v 31 = (2^31 <=? v mod 2^32).
Proof.
  rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
  pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  destruct (Z.leb_spec (2^31) (v mod 2^32)).
  - replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sxv_testbit_hi v i : 31 <= i < 64 -> Z.testbit (sxv v) i = Z.testbit v 31.
Proof.
  intros Hi. rewrite testbit_31_mod32. rewrite Z.testbit_eqb by lia.
  assert (P31 : 2^31 <= 2^i) by (apply Z.pow_le_mono_r; lia).
  assert (P63 : 2^i <= 2^63) by (apply Z.pow_le_mono_r; lia).
  assert (E64 : 2^64 = 2^(64-i) * 2^i) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E2 : 2^(64-i) = 2 * 2^(64-i-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (P1 : 1 <= 2^(64-i-1)) by (apply Z.pow_le_mono_r with (b:=0) in Hi || idtac; apply (Z.pow_le_mono_r 2 0); lia).
  destruct (sxv_cases' v) as [[Hu E]|[Hu E]]; rewrite E.
  - rewrite Z.div_small by lia. cbn. symmetry. apply Z.leb_gt. lia.
  - pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
    replace ((v mod 2^32 + 2^64 - 2^32) / 2^i) with (2^(64-i) - 1) by (Z.div_mod_to_equations; nia).
    rewrite E2. replace (2 * 2^(64-i-1) - 1) with (1 + (2^(64-i-1) - 1) * 2) by lia.
    rewrite Z.mod_add by lia. cbn. symmetry. apply Z.leb_le. lia.
Qed.

Lemma sxv_testbit_high v i : 64 <= i -> Z.testbit (sxv v) i = false.
Proof.
  intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma sxv_land a b : Z.land (sxv a) (sxv b) = sxv (Z.land a b).
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
  - rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
  - rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
  - rewrite !sxv_testbit_high by lia. reflexivity.
Qed.

Lemma sxv_idem v : sxv (sxv v) = sxv v.
Proof. apply sxv_congr. apply sxv_mod32. Qed.

Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.

Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

Lemma negw_and_lowbit v : 0 <= v < 2^32 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv v)))))) (bv_unsigned (wz (sxv v))))
  = wz (sxv (lowbit v)).
Proof.
  intros Hv. rewrite swrap_word. rewrite !wz_unsigned by apply sxv_range.
  rewrite sxv_land. unfold lowbit, wz. f_equal.
  rewrite (Z.land_comm v (- v)).
  transitivity (sxv (Z.land (sxv (0 - sxv v)) (sxv v))); [rewrite sxv_land, sxv_idem; reflexivity|].
  transitivity (sxv (Z.land (sxv (- v)) (sxv v))); [| rewrite sxv_land, sxv_idem; reflexivity].
  f_equal. f_equal. apply sxv_congr.
  rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. replace (0 - v) with (- v) by lia. reflexivity.
Qed.

Definition DB32 : Z := 124511785.
Definition dbi (k : Z) : Z := ((2 ^ k * DB32) mod 2^32) / 2^27.

Definition debruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes asegs DEBRUIJN 32 with Some bs => bs | None => [] end).

Lemma le4_avail_sub a b : 0 <= b <= a -> a < 2^32 ->
  le4 (wz (sxv (sxv a - sxv b))) = le4 (wz (a - b)).
Proof.
  intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.
End AC_1.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.
Section AC_2. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition mfc_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 gw s0v rav : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (G avail k ctr : Z) (prev next memw : word) (freed mword secret initd : Z) (junk : list byte)
   : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a3 a5 t3 t4 t5 t6 m3 m',
    ms' = MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 MLOCK) a1 (wz k) a3 (wz (sxv ctr)) a5 gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17014) fc None m' (seg_rom asegs)
    /\ m3 = write_to_mem m (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m3 m' /\ wmono asegs m3 m'
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (G + 24, G + 28)]%Z m m' /\ wmono asegs m m'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]
    /\ rw_cells asegs m' CTX [C8 (wz secret); C4 (wz initd); C4 (wz ctr)]
    /\ rw_cells asegs m' MLOCK [C4 (wz 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 (wz k); C8 gw; C8 (wz (sxv ctr)); C8 (wz k); CB 16 (skipn 32 junk); C8 s0v; C8 rav].

Definition mfe_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (sc : Z) : machine_state -> Prop :=
  fun ms' => exists a4 junk m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 s1 a0 a1 a2 (Z_to_bv 64 CTX) a4 (Z_to_bv 64 sc) gw a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x16fa8) fc None m' (seg_rom asegs)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 48 junk; C8 s0; C8 ra]
    /\ length junk = 48%nat
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Definition mfa_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a7 gw ra : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (G avail k ctr : Z) (prev next memw : word) (freed mword secret initd : Z)
   : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a3 a5 t3 t4 t5 t6 (junk : list byte) m1 m3 m',
    ms' = MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 s1
                  (Z_to_bv 64 MLOCK) a1 (wz k) a3 (wz (sxv ctr)) a5 gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17014) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono asegs m m1
    /\ m3 = write_to_mem m1 (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m3 m' /\ wmono asegs m3 m'
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (G + 24, G + 28)]%Z m m' /\ wmono asegs m m'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]
    /\ rw_cells asegs m' CTX [C8 (wz secret); C4 (wz initd); C4 (wz ctr)]
    /\ rw_cells asegs m' MLOCK [C4 (wz 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 (wz k); C8 gw; C8 (wz (sxv ctr)); C8 (wz k); CB 16 (skipn 32 junk); C8 s0; C8 ra].
End AC_2.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.
