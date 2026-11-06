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
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain MallocWfKf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngWk MngU MngRz2 MngBud MngRb MngLive.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngMWP MngMWQ MngMW0 AXG_ffstep MngL4 MngL4grp MngL4M AXG_am8 AXG_mwc AXG_mwk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma heap_rgeoA : forall HTOP hs m md, Heap HTOP hs m md -> MngRz2.LINK HTOP FORB_P (hs_L hs) (kf_of (hs_s hs)) md ->
  rgeoA HTOP (hs_L hs) (hs_s hs) /\ rdisj (hs_L hs) (hs_s hs).
Proof.
  intros HTOP hs m md HH HL. destruct HH as [_ _ _ _ _ _ Hap Htop _ _ _ _ Hrap]. split.
  - intros r rg Hr Hl. destruct (lk_rgeo _ _ _ _ _ HL r rg Hr Hl) as (G1 & G2 & G3 & G4 & G5).
    destruct (rg_kind rg) eqn:Hk.
    + destruct (Hrap r rg Hr Hl ltac:(rewrite Hk; discriminate)) as (R1 & R2 & R3 & _). auto.
    + destruct (Hrap r rg Hr Hl ltac:(rewrite Hk; discriminate)) as (R1 & R2 & R3 & _). auto.
    + (* [comment removed for export] *)
      assert (Hin : In (LMem (SP r 0), rg_len rg) (footprint (hs_s hs))).
      { unfold footprint. right. apply in_or_app. right. apply in_flat_map. exists r. split.
        - apply in_seq. split; [lia|]. cbn. unfold region_of in Hr. apply nth_error_Some. congruence.
        - rewrite Hr, Hk, Hl. left. reflexivity. }
      pose proof (Hap _ Hin ltac:(discriminate)) as D. pose proof (Htop _ Hin) as T.
      unfold crange in D. cbn [fst snd loc_addr] in D, T. rewrite Z.add_0_r in D, T. auto.
  - intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2. exact (lk_rdisj _ _ _ _ _ HL r1 r2 rg1 rg2 Hne H1 H2 L1 L2).
Qed.

Section MC.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

(* [comment removed for export] *)
Hypothesis DIRWK : forall {fx : FPState}, @direct_wk_stmt fx.

Variable HTOP : Z.

(* [comment removed for export] *)
#[using="Hoff DIRWK"] Lemma malloc_core : forall (fx : FPState) regs m md hs n ret K,
  Heap0 (hs_L hs) (hs_s hs) m -> ly_ctx (hs_L hs) = 0x97c98 -> rgeoA HTOP (hs_L hs) (hs_s hs) -> rdisj (hs_L hs) (hs_s hs) ->
  2^20 <= HTOP -> MENV m ->
  (st_init_done (hs_s hs) = true \/ AMI (hs_L hs) m (sp_of regs)) ->
  WF (hs_s hs) -> MngRz2.LINK HTOP FORB_P (hs_L hs) (kf_of (hs_s hs)) md ->
  (forall tr p0 s' L' m' md',
     yields (malloc n (hs_s hs)) tr (Some p0, s') ->
     Heap0 L' s' m' -> lext (hs_L hs) L' (hs_s hs) -> rgeo HTOP L' s' ->
     mframe (sp_of regs) MNEED (hs_L hs) (hs_s hs) L' s' m m' -> stk_ok SEGS m' (getr regs 2) MNEED ->
     MngRz2.LINK HTOP FORB_P L' (kf_of s') md' ->
     Heap HTOP (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) m' md' /\
     loc_addr L' (LMem p0) mod 16 = 0 /\
     blocks_add (blocks hs) (blocks (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs))) (loc_addr L' (LMem p0), n) /\
     ~ In (loc_addr L' (LMem p0), n) (blocks hs) /\
     munch (owned hs ++ owned (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) ++
            [(loc_addr L' (LMem p0), loc_addr L' (LMem p0) + n); (sp_of regs - MNEED, sp_of regs)]) m m' /\
     (forall a, ~ outside U_KEEP a -> m' (wa a) = m (wa a)) /\
     stk SEGS m' (sp_of regs - MNEED) (sp_of regs)) ->
  U md + MCHARGE n <= UBOUND ->
  getr regs 10 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
  getr regs 1 = ret -> bv_unsigned ret mod 2 = 0 ->
  sp_of regs mod 16 = 0 -> sp_of regs <= 2^47 -> HTOP <= sp_of regs - MNEED ->
  stk SEGS m (sp_of regs - MNEED) (sp_of regs) ->
  malloc_k cfg HTOP fx regs m md hs n ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x530c8) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins (fun (Hoff DIRWK : LiaFast.U) => LiaFast.u0).
  intros fx regs m md hs n ret K H0 Hctx HgA Hdj HT20 Hme Hini HW HL HPOST HU Ha0 Hn Hra Hret Hsp16 Hsp47 Htop Hstk Hcont.
  assert (HTOPB : HTOP <= 2 ^ 47) by (unfold MNEED in *; lia).
  assert (HSTK : stk_ok SEGS m (getr regs 2) MNEED) by (apply stk_ok_of_stk8; [unfold sp_of, MNEED in *; lia | exact Hstk]).
  assert (HUS : forall c, 0 <= c < 48 -> usage_of (hs_s hs) c < 2^40).
  { apply (usage_small_of_link HTOP FORB_P (hs_L hs) (hs_s hs) md HW HL).
    unfold MCHARGE, UBOUND in HU. change (Um md) with (U md). lia. }
  destruct (lk_brk0 _ _ _ _ _ HL) as (Bk1 & Bk2 & _ & Bk3).
  pose proof (malloc_wk (fx := fx) DIRWK HTOP (seg_rom SEGS) (hs_L hs) (hs_s hs) m regs n
                (conj H0 (conj HUS (conj Hctx (conj HgA (conj Hdj (conj HTOPB (conj HT20 (conj Hme (conj Ha0 (conj Hsp16 (conj Hsp47
                   (conj Htop (conj HSTK (conj Bk1 (conj Bk2 (conj Bk3 Hini)))))))))))))))) Hn) as W.
  apply wk_yields in W.
  set (UB0 := U md + MCHARGE n).
  assert (HB : BI UB0 (kf_of (hs_s hs)) md (MCHARGE n)) by (unfold BI, UB0, MCHARGE, UBOUND in *; change (Um md) with (U md); lia).
  apply (tree_rz_B SEGS cfg Hoff FORB_P HTOP HTOPB fx (seg_rom SEGS) UB0 (malloc n (hs_s hs)) (hs_L hs) regs (wa 0x530c8) m
           (kf_of (hs_s hs)) md (MCHARGE n) _ kq K W (malloc_kf (hs_s hs) n) (malloc_reqs_ok (hs_s hs) n HW ltac:(lia))
           (malloc_safe (hs_s hs) n HW ltac:(lia)) (rb_malloc n (hs_s hs) ltac:(lia)) HL HB).
  intros L' r regs' pc' m' x' md' B' (HQ & tr & Hy) HQK HL' HB' Hvm.
  destruct HQ as (p0 & s' & -> & -> & Hcs & HR10 & H0' & Hlext & Hrg & Hmf & Hsk).
  unfold kq in HQK. cbn [snd] in HQK. subst x'.
  destruct (HPOST tr p0 s' L' m' md' Hy H0' Hlext Hrg Hmf Hsk HL') as (HP & Hal & Hba & Hnb & Hmu & Hkp & Hst).
  assert (MD : md_ok md') by exact (conj (lk_halt _ _ _ _ _ HL') (lk_lazy _ _ _ _ _ HL')).
  assert (HU' : U md' <= U md + MCHARGE n) by (destruct HB' as (B1 & B2 & B3); unfold UB0 in *; change (Um md') with (U md') in B1; lia).
  exact (malloc_finish cfg HTOP fx regs m md hs n ret K regs' m' md' _ (loc_addr L' (LMem p0)) MD Hra Hret Hcs HR10 Hal HP Hvm HU'
           Hkp Hba Hnb Hmu Hst Hcont).
Qed.

(* [comment removed for export] *)
#[using="Hoff DIRWK"] Theorem malloc_contract_L4 : forall GP, 0x99000 <= HTOP ->
  malloc_contract SEGS cfg HS (Heap HTOP) blocks owned GP (wa 0x77990) HTOP U_KEEP 0x530c8 MNEED.
Proof. LiaFast.lf_pins (fun (Hoff DIRWK : LiaFast.U) => LiaFast.u0).
  intros GP HIMG fx regs m md hs n ret K HH Hmd HU Ha0 Hn Hra Hret Hgp Htp Hsp16 Hsp47 Htop Hstk Hcont.
  pose proof (LINK_of_v _ _ _ _ (hp_link _ _ _ _ HH) Hmd) as HL.
  destruct (heap_rgeoA HTOP hs m md HH HL) as (HgA & Hdj).
  pose proof HH as [H0 Hctx Henv Hkro _ _ _ _ _ HT20 Hpg Hini _]. pose proof H0 as (HW & _ & _).
  apply (malloc_core fx regs m md hs n ret K H0 Hctx HgA Hdj HT20 (conj (ex_intro _ (hs_can hs) Henv) (conj Hpg Hkro)) (or_introl Hini) HW HL);
    try assumption.
  intros tr p0 s' L' m' md' Hy H0' Hlext Hrg Hmf Hsk HL'.
  exact (malloc_heap_post HTOP hs m md regs n tr p0 s' L' m' md' HH Hn Hy H0' Hlext Hrg Hmf Hsk HL' Hsp47 Htop).
Qed.

(* [comment removed for export] *)
#[using="Hoff DIRWK"] Theorem malloc_contract_init_L4 : forall GP, 0x99000 <= HTOP ->
  malloc_contract_init SEGS cfg HS (Heap HTOP) blocks owned GP (wa 0x77990) HTOP U_KEEP (HeapI HTOP) INIT 0x530c8 MNEED.
Proof. LiaFast.lf_pins (fun (Hoff DIRWK : LiaFast.U) => LiaFast.u0).
  intros GP HIMG fx regs m md hs n ret K HH Hmd HU Ha0 Hn Hra Hret Hgp Htp Hsp16 Hsp47 Htop Hstk HINIsp Hcont.
  pose proof (LINK_of_v _ _ _ _ (hq_link _ _ _ _ HH) Hmd) as HL.
  pose proof HH as [Hs H0 Hctx Henv Hkro _ HT20 Hpg Hini Himg]. pose proof H0 as (HW & _ & _).
  assert (HgA : rgeoA HTOP (hs_L hs) (hs_s hs)) by (intros r rg E; rewrite Hs in E; destruct r; discriminate E).
  assert (Hdj : rdisj (hs_L hs) (hs_s hs)) by (intros r1 r2 rg1 rg2 _ E; rewrite Hs in E; destruct r1; discriminate E).
  assert (HAMI : AMI (hs_L hs) m (sp_of regs)).
  { exists (hs_auxv hs), (hs_rnd hs), (hs_typs hs). split; [exact Hini|]. split.
    - apply HINIsp. unfold INIT. cbn [outside]. intros (N1 & _). apply N1. split; [lia|]. pose proof (Nat2Z.is_nonneg (length (hs_typs hs))). lia.
    - apply HINIsp. unfold INIT. cbn [outside]. intros (_ & N2 & _). apply N2. split; lia. }
  apply (malloc_core fx regs m md hs n ret K H0 Hctx HgA Hdj HT20 (conj (ex_intro _ (hs_can hs) Henv) (conj Hpg Hkro)) (or_intror HAMI) HW HL);
    try assumption.
  intros tr p0 s' L' m' md' Hy H0' Hlext Hrg Hmf Hsk HL'.
  exact (malloc_heap_post_init HTOP hs m md regs n tr p0 s' L' m' md' HH Hn Hy H0' Hlext Hrg Hmf Hsk HL' Hsp47 Htop).
Qed.
End MC.
