(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Definition assert_integrity_entry := 0x19380.
Definition assert_state_entry := 0x19570.
Definition vsb_indent_entry := 0x195c4.
Definition extendsize_entry := 0x19e44.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition assert_integrity_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' a2' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma assert_integrity_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (v : vsb_rec) (fin : bool),
  a0 = Z_to_bv 64 S ->
  rw_cells rsegs m S (vsb_cells v) -> vsb_inv v fin -> 4096 <= S -> S mod 8 = 0 ->
  mem_inv rsegs m ->
  evt rsegs (assert_integrity_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 assert_integrity_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until fin. intros -> VSBC VINV Slo S8 MI. unfold assert_integrity_entry.
  (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]). unfold vsb_cells in VSBC.
  pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K1; zify_cond K1. { exfalso. klia K1. } clear K1.
  zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
  zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. vm_compute. congruence. } clear K2.
  zstep. zstep. if_cases K3; zify_cond K3. { exfalso. klia K3. } clear K3.
  zstep. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. unsign K4. klia K4. } clear K4.
  zstep.
  apply evt_done. unfold assert_integrity_post. eexists _, _, _, _. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. exact MI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition assert_state_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a0' a2' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma assert_state_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (v : vsb_rec) (fin : bool),
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (if fin then 0x20000 else 0) ->
  rw_cells rsegs m S (vsb_cells v) -> vsb_inv v fin -> 4096 <= S -> S mod 8 = 0 ->
  mem_inv rsegs m ->
  evt rsegs (assert_state_post ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 assert_state_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until fin. intros -> -> VSBC VINV Slo S8 MI. unfold assert_state_entry.
  (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]). unfold vsb_cells in VSBC.
  pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K1; zify_cond K1. { exfalso. klia K1. } clear K1.
  zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
  zstep. zstep. zstep.
  zstep. if_cases K2; zify_cond K2.
  { exfalso. revert K2. rewrite Vfl. unfold VSB_FLAGS_FIN, VSB_FLAGS_LIVE. destruct fin; vm_compute; congruence. }
  clear K2.
  zstep.
  apply evt_done. unfold assert_state_post. eexists _, _, _. split; [destruct fin; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. exact MI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vsb_indent_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma vsb_indent_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (v : vsb_rec) (fin : bool) (lo : Z),
  a0 = Z_to_bv 64 S ->
  rw_cells rsegs m S (vsb_cells v) -> vsb_inv v fin -> 4096 <= S -> S mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
  (S + 40 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= S) ->
  mem_inv rsegs m ->
  evt rsegs (vsb_indent_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vsb_indent_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros -> VSBC VINV Slo S8 ST LO SEP MI. unfold vsb_indent_entry.
  (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]). unfold vsb_cells in VSBC. rewrite Vind in VSBC.
  pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep.
  zstep. zstep. if_cases KT; zify_cond KT. { exfalso. rewrite (land7_of_mod8 S) in KT by lia. klia KT. } clear KT.
  zstep. zstep. if_cases KI; zify_cond KI. 2:{ exfalso. dead KI. } clear KI.
  zstep. zstep. zstep. zstep.
  try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold vsb_indent_post. eexists _, _, _. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_pagemask64 : forall x, 0 <= x < 2^64 ->
  Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  rewrite E. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  destruct (Z.ltb_spec i 12) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia.
    destruct (Z.testbit x i); cbn; rewrite ?Bool.andb_false_r; reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.ltb_spec i 64) as [Hlt2|Hge2].
    + cbn. rewrite Bool.andb_true_r. reflexivity.
    + cbn. rewrite Bool.andb_false_r. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.

Section ExtLoop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sz : Z).
  Hypothesis SZ : 17 <= sz <= 4095.
  Notation AT pc xa1 xa3 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) xa1 (Z_to_bv 64 4611686018427387904) xa3 a4 a5 a6 a7
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  #[using="SZ"] Lemma extsize_loop : forall (k : nat) (ns : Z) (xa3 : word),
    0 < ns -> sz <= ns * 2 ^ Z.of_nat k -> ns <= 8192 -> ns < sz ->
    evt rsegs (fun ms => exists xa3', ms = AT 0x19e88 (Z_to_bv 64 (vsb_dbl k ns sz)) xa3')
              (AT 0x19e64 (Z_to_bv 64 ns) xa3).
  Proof.
    induction k as [|k IH]; intros ns xa3 Hns Hsz Hle Hlt.
    - rewrite Z.pow_0_r in Hsz. lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hsz by lia.
      cbn [vsb_dbl]. rewrite (proj2 (Z.ltb_lt ns sz)) by lia.
      change (if true then vsb_dbl k (2 * ns) sz else ns) with (vsb_dbl k (2 * ns) sz).
      (* [comment removed for export] *)
      zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. klia KT. } clear KT.
      zstep. zstep. if_cases K; zify_cond K;
        replace (Z.shiftl ns 1) with (2 * ns) in K by (rewrite Z.shiftl_mul_pow2 by lia; lia); unsign K; shl1_to_mul.
      + apply IH; [lia | nia | klia K | klia K].
      + zstep. replace (vsb_dbl k (2 * ns) sz) with (2 * ns).
        2:{ destruct k; cbn [vsb_dbl]; [reflexivity|]. rewrite (proj2 (Z.ltb_ge _ _)) by klia K. reflexivity. }
        apply evt_done. eexists. reflexivity.
  Qed.
End ExtLoop.

Definition extendsize_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (sz : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (vsb_extendsize sz)) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma extendsize_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sz : Z),
  a0 = Z_to_bv 64 sz -> 16 <= sz <= 2^40 -> mem_inv rsegs m ->
  evt rsegs (extendsize_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc sz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 extendsize_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until sz. intros -> SZ MI. unfold extendsize_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof ((vsb_extendsize_spec sz ltac:(lia))) as dR_4; dand3 dR_4 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec sz ltac:(lia)) as (NS1 & NS2 & NS3) ]).
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases KR; zify_cond KR; unsign KR.
  - (* [comment removed for export] *)
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unsign KT. klia KT. } clear KT.
    zstep. zstep. rewrite land_pagemask64 by lia.
    assert (EV : vsb_extendsize sz = (sz + 4095) / 4096 * 4096).
    { unfold vsb_extendsize. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    rewrite <- EV.
    zstep. if_cases KA; zify_cond KA. { exfalso. unsign KA. klia KA. } clear KA.
    zstep. zstep.
    apply evt_done. unfold extendsize_post. eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact MI.
  - (* [comment removed for export] *)
    zstep. zstep. if_cases KS; zify_cond KS; unsign KS.
    + (* [comment removed for export] *)
      zstep. zstep. if_cases KB; zify_cond KB. 2:{ exfalso. unsign KB. klia KB. } clear KB.
      assert (EV : vsb_extendsize sz = 16).
      { unfold vsb_extendsize. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [vsb_dbl].
        rewrite (proj2 (Z.ltb_ge 16 sz)) by klia KS. reflexivity. }
      zstep. zstep.
      apply evt_done. unfold extendsize_post. rewrite EV. eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact MI.
    + (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply evt_cut; [apply (extsize_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m sz ltac:(klia KS) 9 16); cbn; klia KS|].
      cbv beta. intros ms1 (xa3' & ->).
      assert (EV : vsb_extendsize sz = vsb_dbl 9 16 sz).
      { unfold vsb_extendsize. rewrite (proj2 (Z.ltb_lt _ _)) by klia KR. reflexivity. }
      rewrite <- EV.
      (* [comment removed for export] *)
      zstep. if_cases KA; zify_cond KA. { exfalso. unsign KA. klia KA. } clear KA.
      zstep. zstep.
      apply evt_done. unfold extendsize_post. eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact MI.
Qed.
