(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit3 W_posix_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.
Ltac zl_has_var c := match c with context [?x] => is_var x end.
Ltac zlits :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with
      | context [Z_to_bv 64 ?e] =>
          lazymatch e with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
          tryif zl_has_var e then fail else idtac;
          let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 e)) in
          replace (Z_to_bv 64 e) with (Z_to_bv 64 v) by (symmetry; apply zlit_fold; vm_compute; reflexivity)
      end
  end.
Local Tactic Notation "zrun" integer(n) := do n (zstep; try brc; zlits).

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tm2p_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (B : Z) : machine_state -> Prop :=
  leafA_post [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
             (Z_to_bv 64 1) (fun m' => rw_cells ctasegs m' B [C8 (Z_to_bv 64 0)]).

Lemma OPENSSL_tm_to_posix_epoch_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (pa pb : bptr) (A B : Z) (junk8 : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  In (pa, A, 56) (OW ++ LB) -> A mod 8 = 0 -> ro_cells ctasegs m A (tm_cells epoch_tm) ->
  In (pb, B, 8) (OW ++ LB) -> B mod 8 = 0 -> (B + 8 <= A \/ A + 56 <= B)%Z -> rw_cells ctasegs m B [CB 8%nat junk8] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B ->
  evt ctasegs (tm2p_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m B)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_TM_TO_POSIX_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until junk8. intros HEAP ST MI CEIL LO HINA ALA TM HINB ALB HAB OUT -> ->.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HINA) as (A0 & _ & _ & AC & AI). cbn [blk_addr blk_size fst snd] in A0, AC, AI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HINB) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  ablock HEAP HINA ACCA OFFA. ablock HEAP HINB ACCB OFFB.
  unfold OPENSSL_TM_TO_POSIX_A, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z) by (cbn [offshW]; alia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by alia.
  assert (SEPB : B + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B) by alia.
  unfold tm_cells, epoch_tm in TM. cbn [t_sec t_min t_hour t_mday t_mon t_year Z.sub] in TM.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. ab_shload 4.
  zstep. setreg 6%Z (Z_to_bv 64 70) ltac:(symmetry; apply sx32_small; lia). zrun 1.
  (* [comment removed for export] *)
  zrun 3. ab_shload 4.
  zstep. setreg 17%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia). zrun 1.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  zrun 3. ab_shload 4.
  zstep. setreg 13%Z (Z_to_bv 64 1) ltac:(symmetry; apply sx32_small; lia). zrun 1.     (* [comment removed for export] *)
  (* [comment removed for export] *)
  zrun 3. ab_shload 4.
  zstep. setreg 14%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia). zrun 1.     (* [comment removed for export] *)
  (* [comment removed for export] *)
  zrun 2. ab_shload 4.
  zstep. setreg 16%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia). zrun 1.     (* [comment removed for export] *)
  (* [comment removed for export] *)
  zrun 16.
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 14.
  (* [comment removed for export] *)
  zrun 40. zrun 26.
  zstep. zstep.
  (* [comment removed for export] *)
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. unfold tm2p_postA, leafA_post.
  do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

End WithRT.
