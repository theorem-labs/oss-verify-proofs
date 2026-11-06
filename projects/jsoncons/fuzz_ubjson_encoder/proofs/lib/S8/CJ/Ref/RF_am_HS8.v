(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import TacS8 ImageS8 ZBridgeS8 SysStepS8 SFModelS8 ArrS8 ITreeS8 NodesS8 DecodeS8.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import F_malloc_freeS8 MallocTreeS8 MallocModel_BS8 F_ntf_AS8 F_ntf_BS8 MallocKit_BS8 MallocKit_B3S8 F_am_AS8 F_am_KS8 F_am_CS8 F_am_FS8 F_am_GS8 F_am_HS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import ProgS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require KStepS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Ref Require Import RMallocRepS8 RMallocTreeS8 RMallocKit_BS8 RMallocKit_B3S8 RF_mm_syscallsS8 RF_ntf_AS8 RF_am_AS8 RF_am_KS8 RF_am_CS8 RF_am_FS8 RF_am_GS8.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8b8) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e87c) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in C6.

  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (rid : N) (off : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
  0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
                                   (Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x9e8a0) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e87c) fc None m (seg_rom rsegs)).
Proof.
  intros until off. intros MR CNT BRK C0 C1b.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in C6.

  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma ram_brk0_node :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x9e8bc) fc None m (seg_rom rsegs) /\ 0 <= r < 2^64))
       (MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x9e8b8) fc None m (seg_rom rsegs)).
Proof.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x9e8b8 + 4)%Z with 0x9e8bc%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

Lemma ram_brk_node_at (pc : Z) :
  (pc = 0x9e8a0 \/ pc = 0x9e8dc) -> forall cur req, req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom rsegs)))
       (MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.

Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur < 2^64 -> cur mod 4096 = 0 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9e8dc) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8bc) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC. change (963664 + 920) with 964584 in MU. change (963664 + 928) with 964592 in MU.

  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.

  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur -> cur + 8192 < 2^64 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x9e900) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
                                   (Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8e0) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros C0 C1b TC.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC.

  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9e98c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e900) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC.
  change (963664 + 40) with 963704 in MU. change (963664 + 48) with 963712 in MU. change (963664 + 920) with 964584 in MU. change (963664 + 928) with 964592 in MU.

  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9e98c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8a4) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.

  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e914) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells rsegs m RCTX cs)
      by (eapply RMallocKit_BS8.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (963664 + 912) with 964576 in TC.
  change (963664 + 920) with 964584 in MU, MU0. change (963664 + 928) with 964592 in MU, MU0.

  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
    - unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (963664 + 912) with 964576.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells rsegs ?mX 964576 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    F fc (m : word -> option byte) (st : mstate) (old : Z),
  rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8a4) fc None m (seg_rom rsegs)).
Proof.
  intros until old. intros MR CNT O0 O1 MI.
  pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.

  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.

Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
  rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
  rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e92c) fc None m' (seg_rom rsegs)
        /\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rmrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9e8e0) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.

  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.
End CEIL_WRAP_1.

