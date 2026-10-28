(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 junk; C8 CAN; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk usegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono usegs m0 m ->
  evt usegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom usegs)
      /\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp) /\ rmrep st' m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a34) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  unfold RSSP_GUARD, rta_frame in *. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WMs.
  (* [comment removed for export] *)
  st1. Local Ltac2 Set LiaHints.tbl := fun () => "00?0>10224819587.701089863043.70 13327157379.7016198329987.7121747491971.7125941134723.7029399778947.71414905987.72  43930219544.6244959024930.635511746513.65 57760626819.7159739554179.7067629104515.717339497859.70 00000100200300400500600700800900?00H00I00J00K00LSSSSSSSSSS4LOLES2LO4LOLESSSS".
st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : ATOP <= lo.

#[using="MR MSL MASK CLO"] Lemma rfin_walk :
  forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
  bv_unsigned gw = G ->
  rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk usegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a3' : word) m' k,
      0 <= k < 32 /\ lowbit mask = 2 ^ k /\
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15374) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  Local Ltac2 Set LiaHints.tbl := fun () => "00K0>17993233322.7725069531951.8828155396397.7835740630868.7837189765311.7241414005484.7344012953868.7244977710417.7546580470096.774812602655.88 49234157850.8849702956586.8851804930461.7351804930461.7554129087508.6854129087508.7554133478837.7654335149469.7154545175883.8859249210124.7659249210134.8559251192621.7759314873579.7860348278314.7768007544114.789536526552.72 9536526552.75 00000500I00M00Q00U00V00W00\00`00d00n01201601:01@01F01L01R01f01j01n02202802@02F02G02HS3CLOS3CLO2HG2LO2GC2Hk2HBS2HkS2P2S2HkSSS3Hk'S2LOS2HBS2HG2Hk2HBS2HBS2HkS2HkS4MASKS4MASKS4MASKS4MASKS3CLO2HG2LO2GC2Hk2HBS2HkS2HkS2HkS2P21HS2P23P32S4MASKSS".
destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
  assert (P2 : 0 < 2 ^ k <= mask).
  { destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  unfold rta_frame, RSSP_GUARD in *. atop_facts.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl usegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells usegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr usegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tauto ];
    rewrite HG in H;
    pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.
  (* [comment removed for export] *)
  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | atop_facts; lia | lia | exact MU | exact WM]. }
  cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
  do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FIN.
End CANSEC1.
