(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv CatExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngOwn AXG_ffstep AXF_ff3 MngL4.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngOwn OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngL4 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MC.
Variable cfg : SpuriousCfg.
Variable HTOP : Z.

(* [comment removed for export] *)
Definition malloc_k (fx : FPState) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) (hs : HS) (n : Z) (ret : word) (K : TSet) : Prop :=
  forall (fx' : FPState) regs' m'' md' hs' (p : Z),
    @fp_csr fx' = @fp_csr fx -> Heap HTOP hs' m'' md' -> md_ok md' -> AllocNodesCfg.vm_only md md' -> (U md' <= U md + MCHARGE n)%Z ->
    (forall a, ~ outside P_KEEP a -> m'' (wa a) = m (wa a)) ->
    getr regs' 10 = Z_to_bv 64 p -> (p mod 16 = 0)%Z ->
    blocks_add (blocks hs) (blocks hs') (p, n) -> ~ In (p, n) (blocks hs) ->
    callee_saved regs regs' ->
    munch (owned hs ++ owned hs' ++ [(p, p + n); (sp_of regs - MNEED, sp_of regs)]) m m'' ->
    stk SEGS m'' (sp_of regs - MNEED) (sp_of regs) ->
    realizes_cfg SEGS cfg (mkCfg (@mkst fx' regs' ret m'' (seg_rom SEGS)) md') K.

(* [comment removed for export] *)
#[using="Type"] Theorem malloc_finish : forall (fx : FPState) regs m md hs n ret K R m' md' hs' p,
  md_ok md' -> getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> callee_same R regs ->
  getr R 10 = Z_to_bv 64 p -> (p mod 16 = 0)%Z ->
  Heap HTOP hs' m' md' -> AllocNodesCfg.vm_only md md' -> (U md' <= U md + MCHARGE n)%Z ->
  (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) ->
  blocks_add (blocks hs) (blocks hs') (p, n) -> ~ In (p, n) (blocks hs) ->
  munch (owned hs ++ owned hs' ++ [(p, p + n); (sp_of regs - MNEED, sp_of regs)]) m m' ->
  stk SEGS m' (sp_of regs - MNEED) (sp_of regs) ->
  malloc_k fx regs m md hs n ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx R (wa 0x52ce0) m' (seg_rom SEGS)) md') K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fx regs m md hs n ret K R m' md' hs' p MD Hra Hret Hcs HR10 Hal HP' Hvm HU HKP Hba Hnb HMU ST CONT.
  destruct MD as [Hh Hl].
  resume4 (conj Hh Hl). change (wa 339168) with (Z_to_bv 64 339168).
  step.
  apply evt_exit_rz. intros fx' r' HR' Hfc.
  assert (C1 : getr R 1 = getr regs 1).
  { pose proof (Hcs 1%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])) as C. match type of Hra with getr _ ?r = _ =>
      replace (Z_to_bv 5 (Z.of_nat 1)) with r in C by (apply bv_eq; reflexivity) end. exact C. }
  rewrite C1, Hra, (ret_pc_even_w ret Hret).
  apply (CONT fx' r' m' md' hs' p Hfc HP' (conj Hh Hl) Hvm HU HKP); [| exact Hal | exact Hba | exact Hnb | | exact HMU | exact ST].
  - rewrite HR'. getr_leaf4. exact HR10.
  - Ltac cs1m HR' Hcs n := rewrite HR'; getr_leaf4;
      let C := fresh "C" in pose proof (Hcs n ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])) as C;
      match goal with |- getr _ ?r = _ => replace r with (Z_to_bv 5 (Z.of_nat n)) by (apply bv_eq; reflexivity) end; exact C.
    unfold callee_saved.
    split; [cs1m HR' Hcs 2%nat|]. split; [cs1m HR' Hcs 3%nat|]. split; [cs1m HR' Hcs 4%nat|]. split; [cs1m HR' Hcs 8%nat|].
    split; [cs1m HR' Hcs 9%nat|]. split; [cs1m HR' Hcs 18%nat|]. split; [cs1m HR' Hcs 19%nat|]. split; [cs1m HR' Hcs 20%nat|].
    split; [cs1m HR' Hcs 21%nat|]. split; [cs1m HR' Hcs 22%nat|]. split; [cs1m HR' Hcs 23%nat|]. split; [cs1m HR' Hcs 24%nat|].
    split; [cs1m HR' Hcs 25%nat|]. split; [cs1m HR' Hcs 26%nat|]. cs1m HR' Hcs 27%nat.
Qed.
End MC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fp_off_image : forall HTOP L s md, rgeo HTOP L s -> MngRz2.LINK HTOP FORB_P L (MallocWfKf.kf_of s) md ->
  forall rg, In rg (footprint s) -> fst rg <> LCtx 0 ->
    ranges_disjoint (crange L rg) (0x10000, 0x87000) /\ 0 <= loc_addr L (fst rg) /\ loc_addr L (fst rg) + snd rg <= HTOP.
Proof.
  intros HTOP L s md HG HL rg Hin Hnc. unfold footprint in Hin. destruct Hin as [<-|Hin]; [exfalso; apply Hnc; reflexivity|].
  apply in_app_iff in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as (a & <- & Ha).
    destruct (MngRz2.lk_areas _ _ _ _ _ HL a Ha) as (rga & E & Lv & K & O1 & O2 & O3).
    destruct (HG (prid a) rga E Lv) as (G1 & G2 & G3). unfold ranges_disjoint, crange in *. cbn [fst snd] in *.
    destruct a as [r o]. cbn [loc_addr prid poff] in *. unfold PGSZ in *. lia.
  - apply in_flat_map in Hin as (k & Hk & Hin). destruct (region_of s k) as [rgk|] eqn:Ek; [|destruct Hin].
    destruct (rg_kind rgk) eqn:Kk; try destruct Hin. destruct (rg_live rgk) eqn:Lk; [|destruct Hin].
    destruct Hin as [<-|[]]. destruct (HG k rgk Ek Lk) as (G1 & G2 & G3).
    unfold ranges_disjoint, crange in *. cbn [fst snd loc_addr] in *. unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Lemma static_kept : forall HTOP sp0 K L s L' s' md' m m', mframe sp0 K L s L' s' m m' -> rgeo HTOP L' s' ->
  MngRz2.LINK HTOP FORB_P L' (MallocWfKf.kf_of s') md' -> ly_ctx L' = 0x95ed8 -> 0x97000 <= sp0 - K ->
  forall x, 0x10000 <= x < 0x97000 -> ~ (0x95ed8 <= x < 0x96278) -> m' (wa x) = m (wa x).
Proof.
  intros HTOP sp0 K L s L' s' md' m m' HMF HG HL Hctx HSP x Hx Hnc.
  destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
  destruct (HMF x ltac:(lia) E) as [A|[((rg & Hrg & Hxr) & _)|(r & rg & Er & Lr & Kr & Bx)]].
  - lia.
  - destruct (loc_eq_dec (fst rg) (LCtx 0)) as [C|C].
    + pose proof (footprint_ctx_len s' rg Hrg C) as Hlen. rewrite C in Hxr. cbn [loc_addr] in Hxr. rewrite Hctx, Hlen in Hxr.
      unfold CTX_SIZE in Hxr. lia.
    + destruct (fp_off_image HTOP L' s' md' HG HL rg Hrg C) as (D & _ & _). unfold ranges_disjoint, crange in D. cbn [fst snd] in D. lia.
  - destruct (HG r rg Er Lr) as (_ & _ & D). unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

(* [comment removed for export] *)
Lemma in_regs_owned : forall hs x, in_regs (hs_L hs) (hs_s hs) x -> ~ outside (owned hs) x.
Proof.
  intros hs x (r & rg & Er & Lr & Kr & Bx) Ho. unfold owned in Ho. apply outside_app2 in Ho as [_ Ho]. apply outside_app2 in Ho as [_ Ho].
  unfold regs_ivl in Ho. rewrite outside_filter, outside_flat_map in Ho.
  assert (Hr : In r (seq 0 (length (st_regions (hs_s hs))))).
  { apply in_seq. split; [lia|]. apply nth_error_Some. unfold region_of in Er. rewrite Er. discriminate. }
  specialize (Ho r Hr). rewrite Er, Lr in Ho. destruct (rg_kind rg); [| | exact (Kr eq_refl)]; cbn [outside] in Ho; lia.
Qed.

(* [comment removed for export] *)
Lemma old_block_range : forall L L' s b, WF s -> lext L L' s -> In b (user_blocks s) -> block_range L' b = block_range L b.
Proof.
  intros L L' s b HW (_ & _ & _ & HR) Hb.
  destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hu & Hi & Hfr & Kf & ->).
  apply (used_metas_usedX s g am HW) in Hu as Ux.
  destruct (used_group_region [] None U0 s g am HW Ux) as (rg & Hr & _).
  assert (Hlt : (prid (am_mem am) < length (st_regions s))%nat) by (apply nth_error_Some; unfold region_of in Hr; rewrite Hr; discriminate).
  unfold block_range. cbn [fst snd]. f_equal. unfold frame_ptr, slot_start, padd.
  destruct (am_mem am) as [rr oo] eqn:Em. cbn [loc_addr prid poff] in *. rewrite (HR rr Hlt). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma segs_none_above : forall a, 0x97000 <= a -> find_segment SEGS a 1 = None.
Proof.
  intros a Ha. apply find_segment_none_above; [|lia].
  assert (H : forallb (fun sg => Z.leb (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) 0x97000) SEGS = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros sg Hsg. rewrite forallb_forall in H. specialize (H sg Hsg). apply Z.leb_le in H. lia.
Qed.

Lemma stk_of_ok : forall m (sp : word) K, stk_ok SEGS m sp K -> 0x97000 <= bv_unsigned sp - K -> 0 <= K ->
  stk SEGS m (bv_unsigned sp - K) (bv_unsigned sp).
Proof.
  intros m sp K HS H1 HK.
  pose proof (u64_range sp) as R.
  replace (bv_unsigned sp) with (bv_unsigned sp - K + Z.of_nat (Z.to_nat K)) at 2 by lia.
  apply stk_of_store_ok; [| lia | lia |].
  - apply HS; rewrite ?wa_u, ?u_wa_small by lia; lia.
  - intros a Ha. apply segs_none_above. lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_frame : forall n (m m' : word -> option byte) (a : Z), 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) -> store_ok SEGS m' (wa a) n = store_ok SEGS m (wa a) n.
Proof.
  induction n as [|n IH]; intros m m' a Ha Hn H; [reflexivity|].
  cbn [store_ok].
  assert (EW : wview SEGS m' (wa a) = wview SEGS m (wa a)) by (unfold wview; rewrite (H a) by lia; reflexivity).
  rewrite EW. destruct (wview SEGS m (wa a)); [|reflexivity].
  replace (wa a + 1)%bv with (wa (a + 1)) by (rewrite wa_add1; reflexivity). apply IH; [lia | lia | intros x Hx; apply H; lia].
Qed.

Section MP.
Variable HTOP : Z.

#[using="Type"] Theorem malloc_heap_post_core : forall hs m (regs : bvmap 5 word) n tr p0 s' L' m' md',
  WF (hs_s hs) -> ly_ctx (hs_L hs) = 0x95ed8 -> env m (hs_can hs) -> KRO m -> page_env m -> 2^20 <= HTOP ->
  (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) -> 1 <= n <= 2^26 ->
  yields (malloc n (hs_s hs)) tr (Some p0, s') ->
  Heap0 L' s' m' -> lext (hs_L hs) L' (hs_s hs) -> rgeo HTOP L' s' ->
  mframe (sp_of regs) MNEED (hs_L hs) (hs_s hs) L' s' m m' ->
  stk_ok SEGS m' (getr regs 2) MNEED ->
  MngRz2.LINK HTOP FORB_P L' (MallocWfKf.kf_of s') md' ->
  sp_of regs <= 2^47 -> HTOP <= sp_of regs - MNEED ->
  Heap HTOP (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) m' md' /\
  loc_addr L' (LMem p0) mod 16 = 0 /\
  blocks_add (blocks hs) (blocks (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs))) (loc_addr L' (LMem p0), n) /\
  ~ In (loc_addr L' (LMem p0), n) (blocks hs) /\
  munch (owned hs ++ owned (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) ++
         [(loc_addr L' (LMem p0), loc_addr L' (LMem p0) + n); (sp_of regs - MNEED, sp_of regs)]) m m' /\
  (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) /\
  stk SEGS m' (sp_of regs - MNEED) (sp_of regs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m regs n tr p0 s' L' m' md' HW Hctx Henv Hkro Hpg HT20 Hb1 Hn Hy H0' HLX HRG HMF HSK HLK Hsp47 HT.
  set (hs' := mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)).
  pose proof H0' as (HW' & HR' & HM').
  assert (Hctx' : ly_ctx L' = 0x95ed8) by (destruct HLX as (E & _); rewrite E; exact Hctx).
  assert (HSPI : 0x97000 <= sp_of regs - MNEED) by (clear - HT HT20; lia).
  pose proof (static_kept HTOP (sp_of regs) MNEED (hs_L hs) (hs_s hs) L' s' md' m m' HMF HRG HLK Hctx' HSPI) as KS.
  (* [comment removed for export] *)
  pose proof (malloc_blocks (hs_s hs) n tr (Some p0) s' HW ltac:(lia) Hy) as (l1 & l2 & El' & El & Hal & Hnew).
  (* [comment removed for export] *)
  assert (Hb0 : In (p0, n) (user_blocks s')) by (rewrite El'; apply in_app_iff; right; left; reflexivity).
  destruct (in_user_blocks_inv s' (p0, n) Hb0) as (g0 & am0 & i0 & fr0 & Hu0 & Hi0 & Hfr0 & Kf0 & Eb0).
  injection Eb0 as Ep0 En0.
  assert (HF0 : In (g0, am0, i0, fr0) (frames s')).
  { apply frames_intro; [exact HW' | | exact Hi0 | exact Hfr0]. apply (used_metas_iff s' g0 am0 (proj1 (inv_keys HW'))). exact Hu0. }
  apply (used_metas_usedX s' g0 am0 HW') in Hu0 as Ux0.
  destruct (used_group_region [] None U0 s' g0 am0 HW' Ux0) as (rg0 & Hr0 & Hkd0 & Hlv0 & _).
  (* [comment removed for export] *)
  assert (FR : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x97000 -> a + Z.of_nat k <= 0x95ed8 \/ 0x96278 <= a ->
                 rdn SEGS m' (wa a) k = rdn SEGS m (wa a) k).
  { intros a k Ha Hk Hnc. apply rdn_frame; [lia | lia |]. intros x Hx. apply KS; lia. }
  (* [comment removed for export] *)
  assert (MO : map (block_range L') (l1 ++ l2) = map (block_range (hs_L hs)) (l1 ++ l2)).
  { apply map_ext_in. intros b Hb. apply (old_block_range (hs_L hs) L' (hs_s hs) b HW HLX). rewrite El. exact Hb. }
  assert (Eblk : blocks hs = map (block_range (hs_L hs)) (l1 ++ l2)) by (unfold blocks; rewrite El; reflexivity).
  assert (Eblk' : blocks hs' = map (block_range L') (l1 ++ (p0, n) :: l2)) by (unfold blocks, hs'; cbn [hs_L hs_s]; rewrite El'; reflexivity).
  assert (Hb1' : forall b, In b (user_blocks s') -> 1 <= snd b).
  { intros b Hb. rewrite El' in Hb. apply in_app_iff in Hb as [Hb|[<-|Hb]]; [| cbn; lia |];
      apply Hb1; rewrite El; apply in_app_iff; [left|right]; exact Hb. }
  split.
  { (* [comment removed for export] *)
    apply Heap_intro. unfold hs'. cbn [hs_L hs_s hs_can].
    split; [exact H0'|]. split; [exact Hctx'|].
    split.
    { destruct Henv as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
      split; [rewrite FR by (cbn; lia); exact E1|]. split; [intros sc Hsc; rewrite FR by (cbn; lia); exact (E2 sc Hsc)|].
      split; [intros j Hj; rewrite FR by (cbn; lia); exact (E3 j Hj)|].
      split; [exact E4|]. split; [rewrite FR by (cbn; lia); exact E5|]. split; [rewrite FR by (cbn; lia); exact E6|].
      split; [rewrite FR by (cbn; lia); exact E7|].
      split; [intros j Hj; destruct (E8 j Hj) as (b0 & Hb00); exists b0; unfold mrd in *; rewrite KS by (unfold ERRNO; lia); exact Hb00|].
      intros d k0 Hd Hk0. rewrite (store_ok_frame k0 m m' (ERRNO + d)) by (first [unfold ERRNO; lia | intros x Hx; apply KS; unfold ERRNO in *; lia]).
      exact (E9 d k0 Hd Hk0). }
    split.
    { destruct Hkro as ((K1 & K2 & K3) & (K4 & K5 & K6)).
      split; (split; [assumption | split; [assumption|]]); intros j Hj; change (Mem.wa j) with (wa j);
        rewrite (KS j ltac:(lia) ltac:(lia)); first [ exact (K3 j Hj) | exact (K6 j Hj) ]. }
    split; [exact (LINKv_of HTOP L' s' md' HLK)|].
    split; [intros g am Mg Ha; exact (inv_pcg HW' g am Mg Ha)|].
    split; [intros rg Hrg Hnc; exact (proj1 (fp_off_image HTOP L' s' md' HRG HLK rg Hrg Hnc))|].
    split.
    { intros rg Hrg. destruct (loc_eq_dec (fst rg) (LCtx 0)) as [C|C].
      - pose proof (footprint_ctx_len s' rg Hrg C) as Hlen. rewrite C, Hlen. cbn [loc_addr]. rewrite Hctx'. unfold CTX_SIZE. lia.
      - exact (proj2 (proj2 (fp_off_image HTOP L' s' md' HRG HLK rg Hrg C))). }
    split; [exact Hb1'|]. split; [exact HT20|].
    split; [unfold page_env in *; rewrite FR by (cbn; lia); exact Hpg|].
    split; [exact (inited_of_areas s' HW' (areas_of_frame s' g0 am0 i0 fr0 HW' HF0))|].
    intros r rg Er Lr Kr. destruct (HRG r rg Er Lr) as (G1 & G2 & G3). split; [exact G3|]. split; [unfold PGSZ in G1; lia|].
    split; [exact G2|]. intros r' rg' Hne Er' Lr'. exact (MngRz2.lk_rdisj _ _ _ _ _ HLK r r' rg rg' (not_eq_sym Hne) Er Er' Lr Lr'). }
  split.
  { (* [comment removed for export] *)
    assert (Epr : prid p0 = prid (am_mem am0)).
    { rewrite Ep0. unfold frame_ptr, slot_start, padd. destruct (am_mem am0); reflexivity. }
    destruct (MngRz2.lk_rgeo _ _ _ _ _ HLK (prid (am_mem am0)) rg0 Hr0 Hlv0) as (_ & Al & _).
    destruct p0 as [rp op]. cbn [loc_addr prid poff] in *. rewrite Epr. unfold UNIT, PGSZ in *.
    rewrite Z.add_mod by lia.
    assert (A16 : ly_reg L' (prid (am_mem am0)) mod 16 = 0).
    { pose proof (Z.div_mod (ly_reg L' (prid (am_mem am0))) 4096 ltac:(lia)) as D. rewrite Al in D.
      rewrite D. rewrite Z.add_0_r. replace (4096 * (ly_reg L' (prid (am_mem am0)) / 4096)) with ((256 * (ly_reg L' (prid (am_mem am0)) / 4096)) * 16) by ring.
      apply Z_mod_mult. }
    rewrite A16, Hal. reflexivity. }
  assert (BA : forall y, In y (blocks hs') <-> y = (loc_addr L' (LMem p0), n) \/ In y (blocks hs)).
  { intros y. rewrite Eblk', Eblk, <- MO. rewrite !map_app. cbn [map]. rewrite !in_app_iff. cbn [In].
    split.
    - intros [H|[H|H]]; [right; left; exact H | left; rewrite <- H; reflexivity | right; right; exact H].
    - intros [H|[H|H]]; [right; left; rewrite H; reflexivity | left; exact H | right; right; exact H]. }
  split; [exact BA|].
  split.
  { (* [comment removed for export] *)
    intros Hin. rewrite Eblk, <- MO in Hin. apply in_map_iff in Hin as (b & Eb & Hb).
    pose proof (user_blocks_disjoint s' L' HW' (proj1 HR')) as PW. rewrite El', map_app_cons in PW.
    assert (Hbb : In (block_range L' b) (map (block_range L') (l1 ++ l2))) by (apply in_map; exact Hb).
    rewrite map_app in Hbb.
    destruct (pairwise_app_cons _ _ _ _ PW (block_range L' b) Hbb) as [D|D];
      unfold ranges_disjoint, block_range in D, Eb; cbn [fst snd] in D;
      pose proof (f_equal fst Eb) as E1; pose proof (f_equal snd Eb) as E2; cbn [fst snd] in E1, E2; lia. }
  split.
  { (* [comment removed for export] *)
    intros x Hx. destruct (decide (m' x = m x)) as [E|E]; [exact E|]. exfalso.
    pose proof (u64_range x) as Rx. rewrite <- (wa_u x) in E.
    apply outside_app' in Hx as (Ho1 & Ho2). apply outside_app' in Ho2 as (Ho2 & Ho3). cbn [outside] in Ho3.
    destruct Ho3 as (Hop & Hos & _).
    destruct (HMF (bv_unsigned x) ltac:(lia) E) as [A|[((rg & Hrg & Hxr) & Hnu)|HRx]].
    - lia.
    - refine (owned_in0 hs' (bv_unsigned x) rg Hb1' Hrg Hxr _ Ho2).
      intros b Hb Hxb. apply BA in Hb as [->|Hb]; [cbn [fst snd] in Hxb; lia|].
      rewrite Eblk in Hb. apply in_map_iff in Hb as (b0 & <- & Hbo). apply Hnu. exists b0. split; [rewrite El; exact Hbo|].
      unfold block_range in Hxb. cbn [fst snd] in Hxb. exact Hxb.
    - exact (in_regs_owned hs' (bv_unsigned x) HRx Ho2). }
  split.
  { intros a Ha. destruct (keep_static a Ha) as (A1 & A2). exact (KS a A1 A2). }
  unfold sp_of in *. exact (stk_of_ok m' (getr regs 2) MNEED HSK HSPI ltac:(unfold MNEED; lia)).
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem malloc_heap_post : forall hs m md (regs : bvmap 5 word) n tr p0 s' L' m' md',
  Heap HTOP hs m md -> 1 <= n <= 2^26 ->
  yields (malloc n (hs_s hs)) tr (Some p0, s') ->
  Heap0 L' s' m' -> lext (hs_L hs) L' (hs_s hs) -> rgeo HTOP L' s' ->
  mframe (sp_of regs) MNEED (hs_L hs) (hs_s hs) L' s' m m' ->
  stk_ok SEGS m' (getr regs 2) MNEED ->
  MngRz2.LINK HTOP FORB_P L' (MallocWfKf.kf_of s') md' ->
  sp_of regs <= 2^47 -> HTOP <= sp_of regs - MNEED ->
  Heap HTOP (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) m' md' /\
  loc_addr L' (LMem p0) mod 16 = 0 /\
  blocks_add (blocks hs) (blocks (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs))) (loc_addr L' (LMem p0), n) /\
  ~ In (loc_addr L' (LMem p0), n) (blocks hs) /\
  munch (owned hs ++ owned (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) ++
         [(loc_addr L' (LMem p0), loc_addr L' (LMem p0) + n); (sp_of regs - MNEED, sp_of regs)]) m m' /\
  (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) /\
  stk SEGS m' (sp_of regs - MNEED) (sp_of regs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md regs n tr p0 s' L' m' md' HP. pose proof HP as [(HW & _ & _) Hctx Henv Hkro _ _ _ _ Hb1 HT20 Hpg _ _].
  exact (malloc_heap_post_core hs m regs n tr p0 s' L' m' md' HW Hctx Henv Hkro Hpg HT20 Hb1).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem malloc_heap_post_init : forall hs m md (regs : bvmap 5 word) n tr p0 s' L' m' md',
  HeapI HTOP hs m md -> 1 <= n <= 2^26 ->
  yields (malloc n (hs_s hs)) tr (Some p0, s') ->
  Heap0 L' s' m' -> lext (hs_L hs) L' (hs_s hs) -> rgeo HTOP L' s' ->
  mframe (sp_of regs) MNEED (hs_L hs) (hs_s hs) L' s' m m' ->
  stk_ok SEGS m' (getr regs 2) MNEED ->
  MngRz2.LINK HTOP FORB_P L' (MallocWfKf.kf_of s') md' ->
  sp_of regs <= 2^47 -> HTOP <= sp_of regs - MNEED ->
  Heap HTOP (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) m' md' /\
  loc_addr L' (LMem p0) mod 16 = 0 /\
  blocks_add (blocks hs) (blocks (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs))) (loc_addr L' (LMem p0), n) /\
  ~ In (loc_addr L' (LMem p0), n) (blocks hs) /\
  munch (owned hs ++ owned (mkHS L' s' (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)) ++
         [(loc_addr L' (LMem p0), loc_addr L' (LMem p0) + n); (sp_of regs - MNEED, sp_of regs)]) m m' /\
  (forall a, ~ outside P_KEEP a -> m' (wa a) = m (wa a)) /\
  stk SEGS m' (sp_of regs - MNEED) (sp_of regs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md regs n tr p0 s' L' m' md' HP. pose proof HP as [Hs (HW & _ & _) Hctx Henv Hkro _ HT20 Hpg _ _].
  refine (malloc_heap_post_core hs m regs n tr p0 s' L' m' md' HW Hctx Henv Hkro Hpg HT20 _).
  intros b Hb. rewrite Hs, user_blocks_init in Hb. destruct Hb.
Qed.
End MP.
