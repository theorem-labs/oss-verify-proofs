(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac ANodeA7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma page_down_id : forall x, 0 <= x < 2^64 -> x mod 4096 = 0 -> Z.land x 18446744073709547520 = x.
Proof.
  intros x Hx M. change 18446744073709547520 with (2^64 - 2^12).
  rewrite StrFun.land_align_down by lia. change (2^12) with 4096. lia.
Qed.

Definition mapcb_entry : Z := 0x749e0.
Definition mapordie_entry : Z := 0x74b2c.
Definition mapfixed_body : Z := 0x6c7a8.
Definition mapfixed_resume : Z := 0x6c854.
(* [comment removed for export] *)
Definition mapfixed_ordie : Z := 0x6c79c.
Definition mapfixed_onfatal : Z := 0x6c920.
Definition mapfixed_mid (tol : Z) : Z := if tol =? 0 then mapfixed_ordie else mapfixed_onfatal.
(* [comment removed for export] *)
Definition map_ret : Z := 0x74a0c.

(* [comment removed for export] *)
Definition mapfixed_thunk (tol : Z) : Z := if tol =? 0 then mapordie_entry else mapcb_entry.

(* [comment removed for export] *)
Definition mapfixed_frame (scr : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C4 (wz 50); CB 44 scr; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition map_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition mapcb_frame (scr : list byte) (s4 s3 s2 : word) (fa size : Z) (s1 s0 ra : word) : list cell :=
  [C4 (wz 50); CB 44 scr; C8 s4; C8 s3; C8 s2; C8 (wz fa); C8 (wz size); C8 (wz map_ret); C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma a6_rw_cells_join : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] [X1 [X2 X3]]] [[W2 B2] [Y1 [Y2 Y3]]]. split; [split|].
  - apply Cells.cells_wf_app. split; assumption.
  - rewrite Cells.cells_bytes_app. apply Mem.bytes_at_app. split; [exact B1|]. rewrite Cells.cells_bytes_length by exact W1. exact B2.
  - rewrite Cells.cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [L|G]; [apply X3; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Y3. lia.
Qed.
Lemma a6_rw_cells_split : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[W B] [X1 [X2 X3]]]. apply Cells.cells_wf_app in W. destruct W as [W1 W2].
  rewrite Cells.cells_bytes_app in B. apply Mem.bytes_at_app in B. destruct B as [B1 B2]. rewrite Cells.cells_bytes_length in B2 by exact W1.
  rewrite Cells.cells_size_app in X2, X3.
  split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply X3. lia.
  - replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply X3. lia.
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition mapfixed_core_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo tol fa size name : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 368 -> alloc_ceiling <= lo ->
    bv_unsigned sp <= 2^47 ->
    a0 = wz fa -> a1 = wz size -> a2 = wz name -> 0 <= tol <= 1 ->
    1 <= size <= 2^44 -> size mod 4096 = 0 -> 0 <= fa -> fa + size <= 2^47 -> fa mod 4096 = 0 ->
    0 <= name < 2^47 ->   (* [comment removed for export] *)
    ro_cells rsegs m 0xa9170 [C8 (wz PSC)] -> ro_cells rsegs m PSC [C8 (wz 4096)] ->
    ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)] ->
    (forall (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -96) (mapfixed_frame scr s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 368, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp + -96) ->
        Q (MSsvc (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -96)) gp tp t0' t1' t2' (wz size) (wz tol)
                      (wz fa) (wz size) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fa) (wz name) (wz PSC) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz (mapfixed_mid tol)) fc None m (seg_rom rsegs)).

Theorem mapfixed_core_ok : mapfixed_core_stmt.
Proof.
  unfold mapfixed_core_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH A0 A1 A2 TOL SZ SZM FA0 FAH FAM NM GPS CPS GCF CDP K.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  change (CF + 260) with 1339372 in CDP.
  unfold mapfixed_resume, mmap_ecall_pc, mapfixed_frame, CF, PSC in *. subst a0 a1 a2.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (TC : tol = 0 \/ tol = 1) by lia.
  unfold mapfixed_mid, mapfixed_ordie, mapfixed_onfatal.
  destruct TC as [-> | ->]; cbn [Z.eqb Pos.eqb].
  all: do 3 amz.
  all: carve_frame 96%nat ST.
  all: do 7 amz. (* [comment removed for export] *)
  all: do 6 amz. (* [comment removed for export] *)
  all: amz; amz; if_true. (* [comment removed for export] *)
  all: amz; amz; amz; if_false. (* [comment removed for export] *)
  all: amz; amz; amz; amz. (* [comment removed for export] *)
  all: rewrite (page_mask_id size) by lia.
  all: amz; if_true. (* [comment removed for export] *)
  all: amz. (* [comment removed for export] *)
  all: rewrite (page_down_id fa) by lia.
  all: amz; amz. (* [comment removed for export] *)
  all: amz; amz; amz; amz. (* [comment removed for export] *)
  all: carve_frame 272%nat ST.
  all: do 8 amz.
  (* [comment removed for export] *)
  all: amz; amz; amz; (let Kn := fresh "Kn" in if_cases Kn; zify_cond Kn); [ | amz; amz; amz; amz; amz; amz; if_true ].
  all: do 10 amz.
  all: release_frame FR0 ST (bv_unsigned sp + -96).
  all: do 7 amz. (* [comment removed for export] *)
  all: amz. (* [comment removed for export] *)
  all: step_ecall.
  all: eapply K; eassumption.
Qed.

(* [comment removed for export] *)
Definition mapfixed_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo tol fa size name : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 368 -> alloc_ceiling <= lo ->
    bv_unsigned sp <= 2^47 ->
    a1 = wz fa -> a2 = wz size -> a3 = wz name -> tol = 0 ->
    1 <= size <= 2^44 -> size mod 4096 = 0 -> 0 <= fa -> fa + size <= 2^47 -> fa mod 4096 = 0 ->
    0 <= name < 2^47 ->
    ro_cells rsegs m 0xa9170 [C8 (wz PSC)] -> ro_cells rsegs m PSC [C8 (wz 4096)] ->
    ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)] ->
    (forall (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -96) (mapfixed_frame scr s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 368, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp + -96) ->
        Q (MSsvc (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -96)) gp tp t0' t1' t2' (wz size) (wz tol)
                      (wz fa) (wz size) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fa) (wz name) (wz PSC) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz (mapfixed_thunk tol)) fc None m (seg_rom rsegs)).

Theorem mapfixed_pre_ok : mapfixed_pre_stmt.
Proof.
  unfold mapfixed_pre_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH A1 A2 A3 TOL SZ SZM FA0 FAH FAM NM GPS CPS GCF CDP K.
  subst tol a1 a2 a3. unfold mapfixed_thunk, mapordie_entry. cbn [Z.eqb].
  do 4 amz. (* [comment removed for export] *)
  change 0x6c79c with (mapfixed_mid 0).
  eapply (mapfixed_core_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ a4 a5 a6 a7 _ _ _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo 0 fa size name).
  all: try eassumption. all: try reflexivity. 1: lia.
Qed.

(* [comment removed for export] *)
Definition map_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo fa size name : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 400 -> alloc_ceiling <= lo ->
    bv_unsigned sp <= 2^47 ->
    a1 = wz fa -> a2 = wz size -> a3 = wz name ->
    1 <= size <= 2^44 -> size mod 4096 = 0 -> 0 <= fa -> fa + size <= 2^47 -> fa mod 4096 = 0 ->
    0 <= name < 2^47 ->
    ro_cells rsegs m 0xa9170 [C8 (wz PSC)] -> ro_cells rsegs m PSC [C8 (wz 4096)] ->
    ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)] ->
    (forall (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -128) (mapcb_frame scr s4 s3 s2 fa size s1 s0 ra) ->
        munch [(bv_unsigned sp - 400, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp + -128) ->
        Q (MSsvc (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -128)) gp tp t0' t1' t2' (wz size) (wz 1)
                      (wz fa) (wz size) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fa) (wz name) (wz PSC) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz mapcb_entry) fc None m (seg_rom rsegs)).

Theorem map_pre_ok : map_pre_stmt.
Proof.
  unfold map_pre_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH A1 A2 A3 SZ SZM FA0 FAH FAM NM GPS CPS GCF CDP K.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  change (CF + 260) with 1339372 in CDP.
  unfold mapcb_entry, map_ret, map_frame, CF, PSC in *. subst a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 5 amz. (* [comment removed for export] *)
  do 5 amz. (* [comment removed for export] *)
  amz.      (* [comment removed for export] *)
  change 0x6c920 with (mapfixed_mid 1).
  eapply (mapfixed_core_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ a4 a5 a6 a7 _ _ _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ lo 1 fa size name).
  all: try eassumption. all: try reflexivity.
  all: rewrite ?unsigned_lit by (clear - CV LOLE LO0 SPH SPR; lia).
  all: try (clear - CV LOLE LO0 SPH SPR; lia).
  all: try eassumption.
  intros t0c t1c t2c a6c t3c t4c t5c t6c scr m2 FRM MU2 WM2 MI2 ST2.
  rewrite ?unsigned_lit in MU2 by (clear - CV LOLE LO0 SPH SPR; lia).
  lazymatch type of MU2 with munch ?W ?mi ?mc =>
    apply (rw_cells_transport rsegs W mi mc _ _) in FR; [| exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; slia] end.
  replace (bv_unsigned sp + -32 + -96) with (bv_unsigned sp + -128) in * by lia.
  eapply (K t0c t1c t2c a6c t3c t4c t5c t6c scr m2); [ | | exact (wmono_trans _ _ _ _ WM WM2) | exact MI2 | exact ST2].
  { unfold mapcb_frame, map_ret. unfold mapfixed_frame in FRM.
    change ([C4 (wz 50); CB 44 scr; C8 s4; C8 s3; C8 s2; C8 (wz fa); C8 (wz size); C8 (wz 0x74a0c); C8 s2; C8 s1; C8 s0; C8 ra])
      with ([C4 (wz 50); CB 44 scr; C8 s4; C8 s3; C8 s2; C8 (wz fa); C8 (wz size); C8 (wz 0x74a0c)] ++ [C8 s2; C8 s1; C8 s0; C8 ra]).
    apply a6_rw_cells_join; [exact FRM|]. cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -128 + Z.of_nat 96) with (bv_unsigned sp + -32) by lia. exact FR. }
  eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia.
Qed.


(* [comment removed for export] *)
Definition mapfixed_post_stmt : Prop :=
  forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo size tol res : Z) (scr : list byte)
         (s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp + -96) -> lo <= usp - 96 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    0 <= size < 2^64 -> 0 <= tol <= 1 ->
    rw_cells rsegs m (usp + -96) (mapfixed_frame scr s4v s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 144) [C8 (wz 0)] ->
    ((tol = 1 /\ bv_unsigned a0 = 2^64 - 12 /\ res = 0) \/ (1 <= bv_unsigned a0 <= 2^64 - 4097 /\ res = bv_unsigned a0)) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 96, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz res) a1' a2' a3' a4' a5' a6' a7'
                   s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz mapfixed_resume) (wz (usp + -96)) gp tp t0 t1 t2 (wz size) (wz tol) a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz mmap_after_pc) fc None m (seg_rom rsegs)).

Theorem mapfixed_post_ok : mapfixed_post_stmt.
Proof.
  unfold mapfixed_post_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH SZ TOL FR RA GCF CML RC K.
  pose proof alloc_ceiling_val as CV.
  change (CF + 144) with 1339256 in CML.
  unfold mapfixed_resume, mmap_after_pc, mapfixed_frame, CF, PSC in *.
  pose proof (munch_refl [(usp - 96, usp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range _ a0) as A0R.
  amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  destruct RC as [(-> & A0V & ->)|[A0V ->]].
  - (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. br_not_taken. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    rewrite A0V in FR. change (bv_swrap 32 (0 - (2 ^ 64 - 12))) with 12 in FR.
    amz. amz. (* [comment removed for export] *)
    rewrite A0V. change (Z.b2z (18446744073709547520 <? 2 ^ 64 - 12)) with 1.
    amz. if_true. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. amz. if_false. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    do 9 amz. (* [comment removed for export] *)
    release_frame FR ST usp. apply evt_done. eapply K; eassumption.
  - (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? bv_unsigned a0)) with 0 by (symmetry; apply b2z_ltb_false; lia).
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. br_taken. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    replace (Z.b2z (18446744073709547520 <? bv_unsigned a0)) with 0 by (symmetry; apply b2z_ltb_false; lia).
    amz. if_false. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. if_true. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    do 9 amz. (* [comment removed for export] *)
    release_frame FR ST usp. apply evt_done. rewrite <- (Z_to_bv_bv_unsigned a0). eapply K; eassumption.
Qed.

(* [comment removed for export] *)
Definition map_post_stmt : Prop :=
  forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo size fa res : Z) (scr : list byte)
         (s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp + -128) -> lo <= usp - 128 -> alloc_ceiling <= lo -> usp <= 2^47 ->
    0 <= size < 2^64 ->
    rw_cells rsegs m (usp + -128) (mapcb_frame scr s4v s3v s2v fa size s1v s0v ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 144) [C8 (wz 0)] ->
    (1 <= bv_unsigned a0 <= 2^64 - 4097 /\ res = bv_unsigned a0) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 128, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz res) a1' a2' a3' a4' a5' a6' a7'
                   s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz mapfixed_resume) (wz (usp + -128)) gp tp t0 t1 t2 (wz size) (wz 1) a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz mmap_after_pc) fc None m (seg_rom rsegs)).

Theorem map_post_ok : map_post_stmt.
Proof.
  unfold map_post_stmt. intros until Q.
  intros MI ST LOLE CEIL SPH SZ FRC RA GCF CML RC K.
  pose proof alloc_ceiling_val as CV.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct RC as [A0V ->].
  (* [comment removed for export] *)
  unfold mapcb_frame in FRC.
  change ([C4 (wz 50); CB 44 scr; C8 s4v; C8 s3v; C8 s2v; C8 (wz fa); C8 (wz size); C8 (wz map_ret); C8 s2v; C8 s1v; C8 s0v; C8 ra0])
    with (mapfixed_frame scr s4v s3v s2v (wz fa) (wz size) (wz map_ret) ++ map_frame s2v s1v s0v ra0) in FRC.
  apply a6_rw_cells_split in FRC. destruct FRC as [FRM FRA].
  cbn [mapfixed_frame cells_size csize Nat.add] in FRA. replace (usp + -128 + Z.of_nat 96) with (usp + -32) in FRA by lia.
  replace (usp + -128) with (usp + -32 + -96) in * by lia.
  eapply evt_cut; [eapply (mapfixed_post_ok gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (usp + -32) lo size 1
      (bv_unsigned a0) scr s4v s3v s2v (wz fa) (wz size) (wz map_ret)
      (fun s => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         s = MS (mkR (wz map_ret) (wz (usp + -32)) gp tp t0' t1' t2' (wz size) (wz fa) (wz (bv_unsigned a0)) a1' a2' a3' a4' a5' a6' a7'
                     s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz map_ret) fc None m' (seg_rom rsegs)
         /\ munch [(usp + -32 - 96, usp + -32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -32)))|].
  all: try eassumption. all: try reflexivity.
  all: try (clear - CV LOLE LO0 SPH SZ; lia).
  1: { right. split; [exact A0V| reflexivity]. }
  { intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 MU1 WM1 MI1 ST1.
    replace (ret_pc (wz map_ret)) with (wz map_ret : word) by (symmetry; apply ret_pc_even; [unfold map_ret; lia| reflexivity]).
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. exact (conj MU1 (conj WM1 (conj MI1 ST1))). }
  intros ms1 PO. destruct_exs PO. destruct PO as (-> & MU1 & WM1 & MI1 & ST1).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  unfold map_frame, map_ret in *.
  lazymatch type of MU1 with munch ?W ?mi ?mc =>
    apply (rw_cells_transport rsegs W mi mc _ _) in FRA; [| exact MU1 | exact WM1 | cbn [disjoint_from]; simpl_sizes; slia] end.
  rewrite (Z_to_bv_bv_unsigned a0).
  amz. br_not_taken. (* [comment removed for export] *)
  do 4 amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  release_frame FRA ST1 usp. apply evt_done. rewrite <- (Z_to_bv_bv_unsigned a0).
  eapply K; [ | exact WM1 | exact MI1 | exact ST1].
  eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia.
Qed.

End CEIL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
