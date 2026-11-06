(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv CatExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngCtx.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ffstep AXF_ff3 AXG_ffpost AXG_free MngL4.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx.MngMeta OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ffpost OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_free OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngL4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Lemma stk_ok_of_stk : forall m (sp : word), 1024 <= bv_unsigned sp ->
  stk SEGS m (bv_unsigned sp - 1024) (bv_unsigned sp) -> stk_ok SEGS m sp 1024.
Proof.
  intros m sp Hsp (H1 & H2 & H) a n Ha1 Ha2. rewrite <- (wa_u a).
  replace (bv_unsigned a) with (bv_unsigned sp - 1024 + (bv_unsigned a - (bv_unsigned sp - 1024))) by ring.
  apply (store_ok_of_bytes SEGS m (bv_unsigned sp - 1024) 1024); [|lia | lia].
  intros j Hj. pose proof (H (bv_unsigned sp - 1024 + j) ltac:(lia)) as (Hw & _). change (Mem.wa (bv_unsigned sp - 1024 + j)) with (wa (bv_unsigned sp - 1024 + j)) in Hw.
  exact Hw.
Qed.

Section FC.
Variable cfg : SpuriousCfg.
Variable HTOP : Z.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition free_entry (hs : HS) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) (p k : Z) (ret : word)
    g am i fr : Prop :=
  Heap HTOP hs m md /\ md_ok md /\
  getr regs 10 = Z_to_bv 64 p /\ getr regs 1 = ret /\ (bv_unsigned ret mod 2 = 0)%Z /\
  (sp_of regs mod 16 = 0)%Z /\ (sp_of regs <= 2^47)%Z /\ (HTOP <= sp_of regs - FNEED)%Z /\
  stk SEGS m (sp_of regs - FNEED) (sp_of regs) /\
  In (g, am, i, fr) (frames (hs_s hs)) /\ fr_kind fr = FUser /\
  p = loc_addr (hs_L hs) (LMem (frame_ptr am i fr)) /\ k = fr_n fr.

Definition free_cont (hs : HS) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) (p k : Z) (ret : word) (K : TSet) : Prop :=
  free_k cfg HTOP fx regs m md hs p k ret K.

(* [comment removed for export] *)
#[using="Type"] Lemma frame_1024 : forall (m m' : word -> option byte) (sp : Z) (P : Z -> Prop),
  (forall x, 0 <= x < 2^64 -> ~ (sp - 1024 <= x < sp) -> P x -> m' (wa x) = m (wa x)) ->
  forall x, 0 <= x < 2^64 -> ~ (sp - FNEED <= x < sp) -> P x -> m' (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m m' sp P H x Hx Hs HP. apply H; [exact Hx | unfold FNEED in Hs; lia | exact HP]. Qed.

Ltac entry_facts FE regs m hs g am i fr :=
  destruct FE as (HP & MD & Ha0 & Hra & Hret & AL & Hsp47 & HT & ST & HF & Hk & Ep & Ek);
  pose proof HP as [H0 Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap];
  pose proof Henv as (E1 & E2 & Edb & E3 & E4 & E5 & E6 & Eer & Eew);
  assert (Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47) by (unfold sp_of, FNEED in *; lia);
  assert (HSTK : stk_ok SEGS m (getr regs 2) 1024)
    by (apply stk_ok_of_stk; [unfold sp_of, FNEED in *; lia | apply (stk_split SEGS m (sp_of regs - FNEED) (sp_of regs - 1024) (sp_of regs) ST); unfold FNEED; lia]);
  assert (HFP : forall rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024)
    by (intros rg Hrg; pose proof (HHT rg Hrg); unfold sp_of, FNEED in *; lia);
  assert (HP10 : getr regs 10 = wa (loc_addr (hs_L hs) (LMem (frame_ptr am i fr)))) by (rewrite Ha0, Ep; reflexivity).

#[using="Type"] Theorem free_contract_fast : forall hs regs m md p k ret K g am i fr,
  free_entry hs regs m md p k ret g am i fr ->
  am_freed am <> 0 -> Z.lor (am_freed am) (am_avail am) + bit i <> ones (am_last am) ->
  free_cont hs regs m md p k ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x511d0) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs regs m md p k ret K g am i fr FE Hf0 Hnall CONT. entry_facts FE regs m hs g am i fr.
  assert (AL' : bv_unsigned (getr regs 2) mod 16 = 0) by (unfold sp_of in AL; exact AL).
  destruct (free_fast_step (hs_L hs) (hs_s hs) regs m (seg_rom SEGS) g am i fr H0 HF Hk Hf0 Hnall Hctx HP10 E1 E2
              Rsp AL' HSTK HFP HAP) as (R & m' & Hms & Hcs & Hit & H0' & Hfr & Hgr).
  exact (free_contract_step cfg HTOP fx regs m md hs p k ret K g am i fr _ R m' HP MD Hra Hret AL Hsp47 HT ST HF Hk Ep Ek Hms Hcs Hit
              eq_refl H0' Hgr (frame_1024 _ _ _ _ Hfr) CONT).
Qed.

#[using="Type"] Theorem free_contract_null : forall hs regs m md (k : Z) ret K,
  Heap HTOP hs m md -> md_ok md -> getr regs 10 = Z_to_bv 64 0 -> getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
  stk SEGS m (sp_of regs - FNEED) (sp_of regs) ->
  (forall (fx' : FPState) regs' m'' md' hs',
     @fp_csr fx' = @fp_csr fx -> Heap HTOP hs' m'' md' -> md_ok md' ->
     blocks_same (blocks hs) (blocks hs') -> callee_saved regs regs' ->
     munch (owned hs ++ owned hs' ++ [(0, 0 + k); (sp_of regs - FNEED, sp_of regs)]) m m'' ->
     stk SEGS m'' (sp_of regs - FNEED) (sp_of regs) ->
     realizes_cfg SEGS cfg (mkCfg (@mkst fx' regs' ret m'' (seg_rom SEGS)) md') K) ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x511d0) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs regs m md k ret K HP MD Ha0 Hra Hret ST CONT.
  resume4 MD. step. step.
  replace (bv_eqb (getr regs 10) (Z_to_bv 64 0)) with true by (rewrite Ha0; reflexivity). cbv beta iota.
  step.
  apply evt_exit_rz. intros fx' r' HR' Hfc.
  rewrite Hra, (ret_pc_even_w ret Hret).
  apply (CONT fx' r' m md hs Hfc HP MD).
  - intros y. tauto.
  - unfold callee_saved. repeat split; rewrite HR'; getr_leaf4; reflexivity.
  - apply munch_refl.
  - exact ST.
Qed.

(* [comment removed for export] *)
End FC.
