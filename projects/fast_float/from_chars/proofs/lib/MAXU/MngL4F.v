(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv CatExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngMeta AXG_ffstep AXF_ff3 AXG_ffpost MngL4 MngL4free MngRel AXG_fgrp AXG_fgrpU MngL4grp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section FA.
Variable cfg : SpuriousCfg.
Variable HTOP : Z.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem free_contract_null_k : forall hs regs m md (k : Z) ret K,
  Heap HTOP hs m md -> md_ok md -> getr regs 10 = Z_to_bv 64 0 -> getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
  stk SEGS m (sp_of regs - FNEED) (sp_of regs) ->
  (forall (fx' : FPState) regs' m'' md' hs',
     @fp_csr fx' = @fp_csr fx -> Heap HTOP hs' m'' md' -> md_ok md' -> AllocNodesCfg.vm_only md md' -> (U md' <= U md)%Z ->
     (forall a, ~ outside U_KEEP a -> m'' (wa a) = m (wa a)) ->
     blocks_same (blocks hs) (blocks hs') -> callee_saved regs regs' ->
     munch (owned hs ++ owned hs' ++ [(0, 0 + k); (sp_of regs - FNEED, sp_of regs)]) m m'' ->
     stk SEGS m'' (sp_of regs - FNEED) (sp_of regs) ->
     realizes_cfg SEGS cfg (mkCfg (@mkst fx' regs' ret m'' (seg_rom SEGS)) md') K) ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x52f88) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs regs m md k ret K HP MD Ha0 Hra Hret ST CONT.
  resume4 MD. step. step.
  replace (bv_eqb (getr regs 10) (Z_to_bv 64 0)) with true by (rewrite Ha0; reflexivity). cbv beta iota.
  step.
  apply evt_exit_rz. intros fx' r' HR' Hfc.
  rewrite Hra, (ret_pc_even_w ret Hret).
  apply (CONT fx' r' m md hs Hfc HP MD (AllocNodesCfg.vm_only_refl md) ltac:(lia) (fun a _ => eq_refl)).
  - intros y. tauto.
  - unfold callee_saved. repeat split; rewrite HR'; getr_leaf4; reflexivity.
  - apply munch_refl.
  - exact ST.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem free_contract_live : forall hs regs m md p k ret K g am i fr,
  free_entry HTOP hs regs m md p k ret g am i fr -> getr regs 4 = wa 0x77990 ->
  free_cont cfg HTOP hs regs m md p k ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x52f88) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs regs m md p k ret K g am i fr FE HR4 CONT.
  assert (CASES : (am_freed am <> 0 /\ Z.lor (am_freed am) (am_avail am) + bit i <> ones (am_last am)) \/
                  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am))).
  { destruct (Z.eq_dec (am_freed am) 0) as [E|E]; [right; left; exact E|].
    destruct (Z.eq_dec (Z.lor (am_freed am) (am_avail am) + bit i) (ones (am_last am))) as [A|A]; [right; right; exact A | left; split; assumption]. }
  destruct CASES as [(Hf0 & Hnall)|Hnt].
  - exact (free_contract_fast cfg HTOP hs regs m md p k ret K g am i fr FE Hf0 Hnall CONT).
  - pose proof FE as FE0. entry_facts8 FE0 regs m hs g am i fr.
    destruct (free_ntf_run (hs_L hs) (hs_s hs) regs m (seg_rom SEGS) g am i fr H0 HF Hk Hctx HP10 E1 E2 E4
                (ex_intro _ (hs_can hs) (conj E3 E5)) Rsp8 AL' HSTK8 HFP8 HAP Hnt)
      as (R & m2 & mi & s' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnt3 & _).
    pose proof H0 as (HW & _ & _).
    destruct mi as [[r len]|].
    + pose proof (free_ntf_some (hs_s hs) g am i fr s' r len HW HF Hnt Hnt3) as Hit.
      exact (free_contract_grpU cfg HTOP hs regs m md p k ret K g am i fr s' r len _ FE HR4 Hnt Hit CONT).
    + pose proof (free_ntf_none (hs_s hs) g am i fr s' HW HF Hnt Hnt3) as Hit.
      exact (free_contract_grp0 cfg HTOP hs regs m md p k ret K g am i fr s' FE HR4 Hnt Hit CONT).
Qed.

End FA.

(* [comment removed for export] *)
Theorem free_contract_L4 : forall (cfg : SpuriousCfg) (HTOP : Z) (GP : word),
  free_contract SEGS cfg HS (Heap HTOP) blocks owned GP (wa 0x77990) HTOP U_KEEP 0x52f88 FNEED.
Proof.
  intros cfg HTOP GP. unfold free_contract.
  intros fx0 regs m md hs p k ret K HP MD Ha0 Hpk Hra Hret HGP HTP AL Hsp47 HT ST CONT.
  destruct (Z.eq_dec p 0) as [->|Hp0].
  - apply (@free_contract_null_k cfg HTOP fx0 hs regs m md k ret K HP MD Ha0 Hra Hret ST).
    intros fx' regs' m'' md' hs' Hfc HP' MD' Hvm HU HKP Hbs Hcs HMU ST'.
    exact (CONT fx' regs' m'' md' hs' Hfc HP' MD' Hvm HU HKP Hbs Hcs HMU ST').
  - destruct Hpk as [E|Hb]; [exfalso; exact (Hp0 E)|].
    destruct (block_of hs (p, k) Hb) as (b0 & Hb0 & Eb).
    pose proof HP as [(HW & _ & _) _ _ _ _ _ _ _ _ _ _ _].
    destruct (in_user_blocks_inv _ _ Hb0) as (g & am & i & fr & Hu & Hi & Hfr & Hk & ->).
    unfold block_range in Eb. cbn [fst snd] in Eb. injection Eb as Ep Ek.
    assert (HF : In (g, am, i, fr) (frames (hs_s hs))).
    { apply frames_intro; [exact HW | | exact Hi | exact Hfr].
      apply (used_metas_iff (hs_s hs) g am (proj1 (inv_keys HW))). exact Hu. }
    apply (@free_contract_live cfg HTOP fx0 hs regs m md p k ret K g am i fr).
    + unfold free_entry. exact (conj HP (conj MD (conj Ha0 (conj Hra (conj Hret (conj AL (conj Hsp47 (conj HT (conj ST (conj HF (conj Hk (conj Ep Ek)))))))))))).
    + exact HTP.
    + unfold free_cont, free_k. intros fx' regs' m'' md' hs' Hfc HP' MD' Hvm HU HKP Hbd Hcs HMU ST'.
      apply (CONT fx' regs' m'' md' hs' Hfc HP' MD' Hvm HU HKP); [|exact Hcs | exact HMU | exact ST'].
      replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0). exact Hbd.
Qed.

(* [comment removed for export] *)
Theorem heap_ok_L4 : forall (cfg : SpuriousCfg) (HTOP : Z) (GP : word), 0x99000 <= HTOP ->
  malloc_contract SEGS cfg HS (Heap HTOP) blocks owned GP (wa 0x77990) HTOP U_KEEP 0x530c8 MNEED ->
  U_heap_ok cfg (HI HTOP) GP (wa 0x77990) HTOP STATIC_P.
Proof.
  intros cfg HTOP GP HT MC. unfold U_heap_ok, heap_ok, U_IMG_LO, U_IMG_END, U_PC_MALLOC, U_MNEED, U_PC_FREE, U_FNEED.
  split; [split; [lia | exact static_in_image]|].
  split; [exact MC|].
  split; [exact (free_contract_L4 cfg HTOP GP)|].
  split; [exact (heap_frame_L4 HTOP) | exact (heap_blocks_ok_L4 HTOP)].
Qed.
