(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 MngNtfPre MngNtfC MngCtx MngCtx2 MngShape MngTake MngTakeX MngOwn AXG_as1 AXG_as5 AXG_am1 AXG_amr0 AXG_amr AXG_am8 AXG_ag0 AXG_ag1 AXG_ag3p AXG_ag5 AXG_ag6 AXG_ag7 AXG_ag8 AXG_ag9 AXG_ag10 AXG_ag11 AXG_ag12 AXG_ag13 AXG_asq AXF_efz AXF_efbz.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTake OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngOwn OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am8 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag3p OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag6 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag8 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag9 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag10 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag11 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag12 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag13 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asq OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_efbz.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma GROWX_unshift : forall UB0 sp0 K d L s m L' s' m', GROWX UB0 (sp0 - d) (K - d) L s m L' s' m' -> 0 <= d ->
  GROWX UB0 sp0 K L s m L' s' m'.
Proof.
  intros UB0 sp0 K d L s m L' s' m' (E & RM & G & S & CH) Hd. split; [exact E|]. split; [exact RM|]. split; [exact G|]. split; [exact S|].
  intros x Hx Hne. destruct (CH x Hx Hne) as [[A|B]|C]; [left; left; lia | left; right; exact B | right; exact C].
Qed.

Lemma store_ok1_wview : forall m a, store_ok SEGS m a 1 = true -> wview SEGS m a <> None.
Proof. intros m a H. cbn [store_ok] in H. destruct (wview SEGS m a); [discriminate | discriminate]. Qed.

(* [comment removed for export] *)
Lemma stk_ok_join : forall m m' sp0 K d, stk_ok SEGS m' (wa (sp0 - d)) (K - d) -> stk_ok SEGS m (wa sp0) K ->
  (forall x, sp0 - d <= x < sp0 -> m' (wa x) = m (wa x)) -> 0 <= d <= K -> K <= sp0 <= 2^47 -> stk_ok SEGS m' (wa sp0) K.
Proof.
  intros m m' sp0 K d S1 S0 Heq Hd Hsp a n H1 H2. rewrite u_wa_small in H1, H2 by lia.
  apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a); unfold bv_modulus in *; cbn in *; lia|].
  intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - d)) as [Lt|Ge].
  - apply store_ok1_wview. apply S1; rewrite u_wa_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia.
  - assert (E : m' x = m x) by (rewrite <- (wa_u x); apply Heq; lia).
    assert (W : wview SEGS m x <> None) by (apply store_ok1_wview; apply S0; rewrite u_wa_small by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    unfold wview in *. rewrite E. exact W.
Qed.

(* [comment removed for export] *)
Lemma in_user_block_ext : forall X R U s s' L L' x, Inv X R U s -> XNU X s -> lext L L' s -> ub_same s s' ->
  List.NoDup (keys s') -> in_user_block L s x -> in_user_block L' s' x.
Proof.
  intros X R U s s' L L' x HI HXU HE UB ND' (b & Hb & Hx).
  assert (ND : List.NoDup (keys s)) by exact (proj1 (inv_keys HI)).
  exists b. split; [rewrite (ub_same_user_blocks s s' ND ND' UB); exact Hb|].
  destruct (in_user_blocks_inv s b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
  apply (used_metas_usedX_X X R U s g am HI HXU) in Hg.
  pose proof (used_group_prid_lt X R U s g am HI Hg) as Hlt.
  cbn [fst snd] in *. unfold frame_ptr in *. rewrite !loc_padd in *.
  assert (E : loc_addr L' (LMem (slot_start am i)) = loc_addr L (LMem (slot_start am i))).
  { destruct (slot_start am i) as [r o] eqn:Es. cbn [loc_addr]. rewrite (proj2 (proj2 (proj2 HE)) r); [reflexivity|].
    rewrite <- (prid_slot_start am i), Es in Hlt. exact Hlt. }
  rewrite E. exact Hx.
Qed.


(* [comment removed for export] *)
Lemma bview_byte_range : forall (m : word -> option byte) x z, bview SEGS m x = Some z -> 0 <= z < 256.
Proof.
  intros m x z E. unfold bview in E. destruct ((0 <=? x) && (x <? 2^64)); [|discriminate].
  destruct (wview SEGS m (wa x)); [|discriminate]. destruct (ov_read_bytes SEGS m (wa x) 1) as [[|bb [|]]|]; try discriminate.
  injection E as <-. pose proof (bv_unsigned_in_range 8 bb) as Rb. unfold bv_modulus in Rb. cbn in Rb. lia.
Qed.

Lemma rdn1_of_bview : forall (L : layout) (m : word -> option byte) x z, bview SEGS m x = Some z -> 0 <= z < 256 -> 0 <= x < 2^64 ->
  rdn SEGS m (wa x) 1 = Some (word_to_le_bytes 1 (wa z)).
Proof.
  intros L m x z E Hz Hx. set (c := MCell (LCtx (x - ly_ctx L)) 1 (VZ z)).
  assert (Hc : cell_holds L (bview SEGS m) c).
  { unfold cell_holds, c. cbn [mc_loc mc_w mc_val loc_addr sval_num]. intros j Hj. assert (j = 0%nat) as -> by lia.
    replace (ly_ctx L + (x - ly_ctx L) + Z.of_nat 0) with x by lia. rewrite E. f_equal. unfold le_byte. cbn.
    rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity. }
  pose proof (holds_rdn SEGS L m c Hc ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as HRd.
  unfold c in HRd. cbn [mc_loc mc_w mc_val loc_addr sval_num] in HRd. replace (ly_ctx L + (x - ly_ctx L)) with x in HRd by lia. exact HRd.
Qed.

Lemma rdn2_of_bview : forall (L : layout) (m : word -> option byte) x z1 z2, bview SEGS m x = Some z1 -> bview SEGS m (x + 1) = Some z2 ->
  0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= x -> x + 2 <= 2^64 -> rdn SEGS m (wa x) 2 = Some (word_to_le_bytes 2 (wa (z1 + 256 * z2))).
Proof.
  intros L m x z1 z2 E1 E2 Hz1 Hz2 Hx Hx2. set (c := MCell (LCtx (x - ly_ctx L)) 2 (VZ (z1 + 256 * z2))).
  assert (Hc : cell_holds L (bview SEGS m) c).
  { unfold cell_holds, c. cbn [mc_loc mc_w mc_val loc_addr sval_num]. intros j Hj.
    assert (j = 0%nat \/ j = 1%nat) as [-> | ->] by lia.
    - replace (ly_ctx L + (x - ly_ctx L) + Z.of_nat 0) with x by lia. rewrite E1. f_equal. unfold le_byte. cbn.
      rewrite Z.shiftr_0_r. rewrite (Z.mod_small (z1 + 256 * z2)) by lia.
      replace (z1 + 256 * z2) with (z1 + z2 * 256) by ring. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
    - replace (ly_ctx L + (x - ly_ctx L) + Z.of_nat 1) with (x + 1) by lia. rewrite E2. f_equal. unfold le_byte. cbn.
      rewrite (Z.mod_small (z1 + 256 * z2)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
      replace (z1 + 256 * z2) with (z1 + z2 * 256) by ring. rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
      symmetry. apply Z.mod_small. lia. }
  pose proof (holds_rdn SEGS L m c Hc ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as HRd.
  unfold c in HRd. cbn [mc_loc mc_w mc_val loc_addr sval_num] in HRd. replace (ly_ctx L + (x - ly_ctx L)) with x in HRd by lia. exact HRd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_wk_f {fx : FPState} (FORB : list (Z * Z)) (fuel : nat) : Prop :=
  forall UB0 HTOP X U L s m (regs : bvmap 5 word) rom sp0 K sc req,
  CUT HTOP X None U L s m sp0 K -> markers_hold L s (bview SEGS m) -> KAS sc <= K ->
  0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= fuel)%nat ->
  getr regs 2 = wa sp0 -> getr regs 10 = wa sc -> getr regs 11 = wa req ->
  (forall c, 0 <= c < 48 -> usage_of s c < 2^40) ->
  DBT m -> TABS m -> rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  (st_init_done s = true \/ AMI L m sp0) ->
  (forall x, UB0 x -> in_user_block L s x) ->
  wk SEGS FORB HTOP rom L regs (wa 0x522f0) m (alloc_slot fuel sc req s) (as_qpost UB0 HTOP X U L s m regs sp0 K sc req).

Lemma as_wk_of_f : forall {fx : FPState}, (forall FORB, (forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB ->
    ranges_disjoint (a, n) (0x10000, 0x87000)) -> forall fuel, as_wk_f FORB fuel) -> as_wk_stmt.
Proof.
  intros fx H FORB HFORB fuel UB0 HTOP X U L s m regs rom sp0 K sc req C MK HK Hsc Hreq Hfit Hf R2 R10 R11 UB Mdb TB Mpg B1 B2 B3 Hin UBI.
  exact (H FORB HFORB fuel UB0 HTOP X U L s m regs rom sp0 K sc req C MK HK Hsc Hreq Hfit Hf R2 R10 R11 UB Mdb TB Mpg B1 B2 B3 Hin UBI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ag_npost (UB0 : Z -> Prop) (HTOP : Z) (X : list sptr) (U : Z -> Z) (L : layout) (s2 : astate) (m2 : word -> option byte)
    (R : bvmap 5 word) (sp0 K sc : Z) (mt : sptr) (ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 : Z) : @wpost (Z * astate) :=
  fun L' r R' pc m' => exists s', r = (0, s') /\ pc = wa 0x52b8c /\ getr R' 10 = wa 0 /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa sv0 /\ getr R' 9 = wa sv1 /\ getr R' 18 = wa sv2 /\
    getr R' 19 = wa sv3 /\ getr R' 20 = wa sv4 /\ getr R' 21 = wa sv5 /\ getr R' 22 = wa sv6 /\ getr R' 23 = wa sv7 /\
    getr R' 24 = wa sv8 /\ getr R' 25 = wa sv9 /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (Inv X (Some (mt, 0)) U s' -> CUT HTOP X (Some (mt, 0)) U L' s' m' sp0 K /\ GROWX UB0 sp0 K L s2 m2 L' s' m') /\
    markers_hold L' s' (bview SEGS m') /\ active_hd s' sc = Some mt /\ UGROW s2 s' sc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEST.
Context {fx : FPState}.

#[using="Type"] Theorem seg_nest : forall HTOP X U L s4 m4 rom sp0 K mt g amg idx j sc cnt0 (R R0 : bvmap 5 word) req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9,
  CUT HTOP (mt :: X) (Some (g, idx)) U L s4 m4 sp0 K -> usedX (mt :: X) s4 g amg -> am_sc amg = j -> active_hd s4 j = Some g ->
  active_hd s4 sc = None -> 0 <= sc <= 23 -> sc < j <= 24 -> 2 <= cnt0 <= 32 -> 16 + class_size sc * cnt0 <= class_size j ->
  class_size sc * cnt0 <= 2032 -> usage_of s4 sc <= 2^60 ->
  as_frame R0 m4 sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 ->
  getr R 1 = wa 0x526d0 -> getr R 2 = wa (sp0 + -144) -> getr R 8 = wa sc -> getr R 9 = wa (loc_addr L (LMem mt)) -> getr R 10 = wa idx ->
  getr R 18 = wa j -> getr R 19 = wa cnt0 -> getr R 20 = wa 613952 -> getr R 21 = wa (8 * sc + 614184) -> getr R 22 = wa 614096 ->
  getr R 23 = wa (8 * sc + 614096) -> getr R 24 = wa (class_size sc) -> getr R 25 = wa 98984 ->
  exists R' hb, 0 <= hb <= 255 /\
    msteps SEGS (mkst R (wa 0x52b8c) m4 rom)
      (mkst R' (wa 0x52b8c) (nn_mem m4 idx (loc_addr L (LMem (am_mem amg))) (loc_addr L (LMem (slot_start amg idx))) (loc_addr L (LMem mt))
                               sc cnt0 (usage_of s4 sc) hb) rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa sv0 /\ getr R' 9 = wa sv1 /\ getr R' 10 = wa 0 /\
    getr R' 18 = wa sv2 /\ getr R' 19 = wa sv3 /\ getr R' 20 = wa sv4 /\ getr R' 21 = wa sv5 /\ getr R' 22 = wa sv6 /\
    getr R' 23 = wa sv7 /\ getr R' 24 = wa sv8 /\ getr R' 25 = wa sv9 /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X U L s4 m4 rom sp0 K mt g amg idx j sc cnt0 R R0 req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9
    C4 Ug Scg Hhd Hhsc Hsc Hj Hcnt Hfit Hsc0 Hus F R1 R2 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25.
  pose proof C4 as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_sp3 _ _ _ _ _ _ _ N) as Hsp3. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1. pose proof (nc_env _ _ _ _ _ _ _ N) as HENV.
  pose proof (nc_repr _ _ _ _ _ _ _ N) as HRx. pose proof HRx as (HL & HPW & HCS & HFM).
  pose proof (layout_of_geo HTOP HTB (mt :: X) (Some (g, idx)) U s4 L HI Hctx HG HD) as HLg.
  pose proof (XNU_of_XNM (mt :: X) s4 HX) as XU.
  assert (KS4 : KS s4) by exact (KS_of_Inv (mt :: X) (Some (g, idx)) U s4 HI).
  assert (P4 : PCUT HTOP L [] s4 m4 sp0 K) by exact (PCUT_of_CUT HTOP (mt :: X) (Some (g, idx)) U L s4 m4 sp0 K C4).
  (* [comment removed for export] *)
  destruct (inv_reserved HI g idx eq_refl) as (am0 & Ug0 & Hidx & Hfr & _).
  pose proof (usedX_fun _ _ _ _ _ Ug0 Ug) as E0. subst am0.
  pose proof (inv_groups HI g amg Ug) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
  pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns). pose proof Gm as (Mlast & _ & Hlen_sl & _).
  pose proof (usedX_MT _ _ _ _ Ug) as [Mg _].
  assert (Hstr : stride_of amg = class_size j).
  { destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
    unfold stride_of. rewrite Scg. destruct C26 as [C|C]; [rewrite C|].
    - destruct (am_last amg =? 0); reflexivity.
    - destruct (am_last amg =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
  (* [comment removed for export] *)
  destruct (used_group_region (mt :: X) (Some (g, idx)) U s4 g amg HI Ug) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
  destruct (HG _ rg Hr Hl) as (G1 & G2 & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  pose proof (size_classes_range sc ltac:(clear - Hsc; lia)) as Hun. pose proof (class_units sc) as Ecs.
  pose proof (class_units j) as Ecj.
  assert (SZJ : forall k, (k <= 24)%nat -> nth k size_classes 0 <= 146) by (intros k Hk; do 25 (destruct k as [|k]; [cbn; lia|]); lia).
  set (sz := znth j size_classes) in *.
  assert (Hsz : 1 <= sz <= 146).
  { pose proof (size_classes_range j ltac:(clear - Hj Hsc; lia)) as H1. pose proof (SZJ (Z.to_nat j) ltac:(clear - Hj Hsc; lia)) as H2.
    unfold sz. unfold znth in *. clear - H1 H2. lia. }
  assert (Hsize : 16 <= class_size sc <= 1016) by (rewrite Ecs in *; clear - Hun Hsc0 Hcnt; nia).
  set (memv := loc_addr L (LMem (am_mem amg))). set (st := loc_addr L (LMem (slot_start amg idx))). set (mta := loc_addr L (LMem mt)).
  set (Gv := loc_addr L (LMem g)).
  assert (Est : st = ly_reg L (prid (am_mem amg)) + poff (am_mem amg) + 16 + stride_of amg * idx).
  { unfold st, slot_start. rewrite loc_padd. destruct (am_mem amg) as [rr oo]. cbn [loc_addr prid poff]. unfold UNIT. ring. }
  assert (Emem : memv = ly_reg L (prid (am_mem amg)) + poff (am_mem amg)) by (unfold memv; destruct (am_mem amg) as [rr oo]; reflexivity).
  assert (Hspan : stride_of amg * idx + stride_of amg <= stride_of amg * (am_last amg + 1)) by nia.
  assert (Hgx : poff (am_mem amg) + 16 + stride_of amg * (am_last amg + 1) - 4 + 4 <= rg_len rg) by (unfold group_extent, UNIT, IB in Hext; lia).
  assert (Hst : 4096 <= st) by (rewrite Est; clear - G1 Ho Sp Hidx; unfold PGSZ in *; nia).
  assert (Hend : st + 16 + class_size sc * cnt0 <= sp0 - K) by (rewrite Est; clear - G3 HT Hgx Hfit Hstr Hspan Ho; nia).
  assert (Hstr16 : stride_of amg = 16 * sz) by (rewrite Hstr, Ecj; reflexivity).
  assert (Hslot : st + stride_of amg - 4 <= sp0 - K) by (rewrite Est; clear - G3 HT Hgx Hspan Ho; nia).
  assert (Dst : st + 16 + class_size sc * cnt0 <= 0x10000 \/ 0x97000 <= st - 4) by (rewrite Est; clear - G4 Hgx Hfit Hstr Hspan Ho Sp Hidx; nia).
  assert (Dslot : st + stride_of amg - 4 <= 0x10000 \/ 0x97000 <= st - 4) by (rewrite Est; clear - G4 Hgx Hspan Ho Sp Hidx; nia).
  assert (Hal : st mod 16 = 0).
  { pose proof (used_group_aligned (mt :: X) (Some (g, idx)) U s4 HI 64 g amg Ug ltac:(lia)) as A1.
    pose proof (stride_mod16 _ _ _ _ _ _ HI Ug) as A2. rewrite Est. unfold PGSZ in G2.
    apply Z.div_exact in A1; [|lia]. apply Z.div_exact in A2; [|lia]. apply Z.div_exact in G2; [|lia].
    replace (ly_reg L (prid (am_mem amg)) + poff (am_mem amg) + 16 + stride_of amg * idx)
      with ((ly_reg L (prid (am_mem amg)) / 4096 * 256 + poff (am_mem amg) / 16 + 1 + stride_of amg / 16 * idx) * 16) by lia.
    apply Z_mod_mult. }
  (* [comment removed for export] *)
  assert (Kg : In g (keys s4)) by exact (MT_keys s4 g _ Mg).
  destruct (nc_mplace _ _ _ _ _ _ _ N g Kg) as (Pg1 & Pg2 & Pg3 & Pg4). fold Gv in Pg1, Pg2, Pg3, Pg4.
  assert (Hmt0 : MT s4 mt = Some MRaw \/ MT s4 mt = Some (MFree None None)) by exact (HX mt (or_introl eq_refl)).
  assert (Kmt : In mt (keys s4)) by (destruct Hmt0 as [E'|E']; exact (MT_keys s4 mt _ E')).
  destruct (nc_mplace _ _ _ _ _ _ _ N mt Kmt) as (Pm1 & Pm2 & Pm3 & Pm4). fold mta in Pm1, Pm2, Pm3, Pm4.
  assert (SLMETA : forall q, In q (keys s4) -> loc_addr L (LMem q) + 40 <= st - 4 \/ st + stride_of amg <= loc_addr L (LMem q)).
  { intros q Kq. destruct (key_slot_range HTOP (mt :: X) (Some (g, idx)) U s4 L q HI HG Kq) as (ag & j' & rr & rga & Hag & Hj' & Eag & Epr & Hrr & Hlv & Hkda & A1 & A2 & A3 & A4).
    assert (Hne : rr <> prid (am_mem amg)) by (intros E; rewrite E in Hrr; rewrite Hr in Hrr; injection Hrr as <-; exact (Hkda Hkd)).
    pose proof (HD rr (prid (am_mem amg)) rga rg Hne Hrr Hr Hlv Hl) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
    rewrite A4, Est. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2 A3 Hj' Hgx Hspan Ho Sp Hidx. nia. }
  pose proof (SLMETA g Kg) as Dg. fold Gv in Dg. pose proof (SLMETA mt Kmt) as Dm. fold mta in Dm.
  (* [comment removed for export] *)
  assert (Lc : forall o, loc_addr L (LCtx o) = 614104 + o) by (intros o; cbn [loc_addr]; rewrite Hctx; reflexivity).
  assert (LP : forall q d, loc_addr L (LMem (padd q d)) = loc_addr L (LMem q) + d) by (intros q d; rewrite loc_padd; reflexivity).
  assert (RDC : forall c, In c (ctx_cells s4) -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
             rdn SEGS m4 (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))))
    by (intros c Hc Hv Hw; exact (nc_ctx_rd L s4 m4 sp0 K c N Hc Hv Hw)).
  assert (RDI : forall c, In c (image s4) -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
             rdn SEGS m4 (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))))
    by (intros c Hc Hv Hw; exact (pc_rd HTOP L [] s4 m4 sp0 K c P4 Hc (fun H => H) Hv Hw)).
  pose proof (inv_ctx HI) as (C1 & C2' & C3' & C4' & C5 & C6 & C7 & C8 & C9 & _).
  assert (MA : rdn SEGS m4 (wa (8 * j + 614184)) 8 = Some (word_to_le_bytes 8 (wa Gv))).
  { pose proof (RDC _ (act_in_ctx s4 (Z.to_nat j) ltac:(clear - Hj Hsc; lia)) ltac:(intros z E; cbn [act_cell mc_val] in E; destruct (nth (Z.to_nat j) (st_active s4) None); discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val act_cell] in H. rewrite Lc in H. unfold CTX_active in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (80 + 8 * j)) with (8 * j + 614184) in H by ring.
    change (nth (Z.to_nat j) (st_active s4) None) with (active_hd s4 j) in H. rewrite Hhd in H. exact H. }
  assert (Mact : rdn SEGS m4 (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (RDC _ (act_in_ctx s4 (Z.to_nat sc) ltac:(clear - Hsc; lia)) ltac:(intros z E; cbn [act_cell mc_val] in E; destruct (nth (Z.to_nat sc) (st_active s4) None); discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val act_cell] in H. rewrite Lc in H. unfold CTX_active in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (80 + 8 * sc)) with (8 * sc + 614184) in H by ring.
    change (nth (Z.to_nat sc) (st_active s4) None) with (active_hd s4 sc) in H. rewrite Hhsc in H. exact H. }
  assert (Musg : rdn SEGS m4 (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa (usage_of s4 sc)))).
  { pose proof (RDC _ (usage_in_ctx s4 (Z.to_nat sc) ltac:(clear - Hsc; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_usage in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (464 + 8 * sc)) with (8 * sc + 614568) in H by ring. exact H. }
  assert (Mctr : rdn SEGS m4 (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa (st_mmap_counter s4)))).
  { pose proof (RDC (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s4))) ltac:(unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ])
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_mmap_counter in H. exact H. }
  assert (MS : forall c, In c (meta_slot_cells g (Some (MUsed amg))) -> In c (image s4)) by (intros c Hc; exact (In_image_used s4 g amg c KS4 Mg (or_introl Hc))).
  assert (MMEM : rdn SEGS m4 (wa (Gv + 16)) 8 = Some (word_to_le_bytes 8 (wa memv))).
  { pose proof (RDI _ (MS _ ltac:(cbn [meta_slot_cells In]; right; right; left; reflexivity)) ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite LP in H. exact H. }
  assert (MBITS : rdn SEGS m4 (wa (Gv + 32)) 8 = Some (word_to_le_bytes 8 (wa (gbits (am_last amg) j (am_maplen amg))))).
  { pose proof (RDI _ (MS _ ltac:(cbn [meta_slot_cells In]; right; right; right; right; right; left; reflexivity)) ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite LP in H. unfold meta_bits in H. rewrite Scg in H. exact H. }
  assert (Msz : rdn SEGS m4 (wa (2 * j + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz))).
  { destruct HENV as (_ & H & _). replace (2 * j + 98984) with (98984 + 2 * j) by ring. exact (H j ltac:(clear - Hj Hsc; lia)). }
  (* [comment removed for export] *)
  assert (FRg : In (LMem (SP (prid (am_mem amg)) 0), rg_len rg) (footprint s4)) by (apply footprint_region_In; assumption).
  assert (MAPPED : forall x, memv <= x < memv + group_extent amg + IB -> exists z, bview SEGS m4 x = Some z /\ 0 <= z < 256).
  { intros x Hx. pose proof (proj1 (Forall_forall _ _) HFM _ FRg x) as Hm. cbn [fst snd loc_addr] in Hm.
    destruct (bview SEGS m4 x) as [z|] eqn:E; [exists z; split; [reflexivity | exact (bview_byte_range m4 x z E)]|].
    exfalso. apply Hm; [rewrite Emem in Hx; unfold group_extent, UNIT, IB in *; lia | reflexivity]. }
  assert (RSt : 16 <= st - memv /\ st + stride_of amg <= memv + group_extent amg + IB) by (rewrite Est, Emem; unfold group_extent, UNIT, IB; clear - Hspan Sp Hidx; nia).
  assert (HDR : exists h3 h16, 0 <= h3 <= 255 /\ 0 <= h16 <= 65535 /\
             rdn SEGS m4 (wa (st - 3)) 1 = Some (word_to_le_bytes 1 (wa h3)) /\ rdn SEGS m4 (wa (st - 2)) 2 = Some (word_to_le_bytes 2 (wa h16))).
  { destruct (ss_hdr (nth_slot amg idx)) as [[a b]|] eqn:EH.
    - pose proof (Gsl idx Hidx) as (_ & Hhr & _). destruct (Hhr a b EH) as (Ra & Rb).
      assert (C3 : In (MCell (LMem (padd (slot_start amg idx) (-3))) 1 (VZ a)) (image s4)).
      { apply (In_image_used s4 g amg _ KS4 Mg). right. unfold group_cells. apply in_app_iff. right.
        apply in_flat_map. exists idx. split; [apply In_zseq; lia|]. unfold slot_cells. rewrite EH. right. left. reflexivity. }
      assert (C16 : In (MCell (LMem (padd (slot_start amg idx) (-2))) 2 (VZ b)) (image s4)).
      { apply (In_image_used s4 g amg _ KS4 Mg). right. unfold group_cells. apply in_app_iff. right.
        apply in_flat_map. exists idx. split; [apply In_zseq; lia|]. unfold slot_cells. rewrite EH. right. right. left. reflexivity. }
      pose proof (RDI _ C3 ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as R3'.
      pose proof (RDI _ C16 ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as R16'.
      cbn [mc_loc mc_w mc_val sval_num] in R3', R16'. rewrite LP in R3', R16'. fold st in R3', R16'.
      exists a, b. split; [lia|]. split; [lia|]. split; [exact R3' | exact R16'].
    - destruct (MAPPED (st - 3) ltac:(clear - RSt Sp; lia)) as (z3 & E3 & Rz3).
      destruct (MAPPED (st - 2) ltac:(clear - RSt Sp; lia)) as (z1 & E1 & Rz1).
      destruct (MAPPED (st - 2 + 1) ltac:(clear - RSt Sp; lia)) as (z2 & E2 & Rz2).
      exists z3, (z1 + 256 * z2). split; [lia|]. split; [lia|].
      split; [apply (rdn1_of_bview L); [exact E3 | clear - Rz3; lia | clear - Hst Hslot Sp HK1 Hsp2; lia]|].
      apply (rdn2_of_bview L); [exact E1 | exact E2 | clear - Rz1; lia | clear - Rz2; lia | clear - Hst; lia | clear - Hst Hslot Sp HK1 Hsp2; lia]. }
  destruct HDR as (h3 & h16 & Hh3 & Hh16 & Mh3 & Mh16).
  assert (Mck : rdn SEGS m4 (wa (st - 4)) 1 = Some (word_to_le_bytes 1 (wa 0))).
  { assert (Cc : In (MCell (LMem (padd (slot_start amg idx) (-4))) 1 (VZ 0)) (image s4)).
    { apply (In_image_used s4 g amg _ KS4 Mg). right. unfold group_cells. apply in_app_iff. right.
      apply in_flat_map. exists idx. split; [apply In_zseq; lia|]. unfold slot_cells. left. reflexivity. }
    pose proof (RDI _ Cc ltac:(intros zz Hzz; discriminate) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite LP in H. exact H. }
  assert (MWIN : forall d kk, 0 <= d -> d + Z.of_nat kk <= stride_of amg + 4 -> store_ok SEGS m4 (wa (st - 4 + d)) kk = true).
  { intros d kk Hd Hkk. apply (store_ok_of_bytes SEGS m4 (st - 4) (stride_of amg + 4)); [|lia|lia].
    intros jj Hjj. destruct (MAPPED (st - 4 + jj) ltac:(clear - Hjj RSt Sp; unfold IB in *; lia)) as (z & E & _).
    unfold bview in E. destruct ((0 <=? st - 4 + jj) && (st - 4 + jj <? 2^64)); [|discriminate].
    destruct (wview SEGS m4 (wa (st - 4 + jj))); [discriminate | discriminate]. }
  destruct (MAPPED (st + 8) ltac:(clear - RSt Sp; unfold IB in *; lia)) as (hb & Ehb & Rhb).
  (* [comment removed for export] *)
  assert (Hml : 0 <= am_maplen amg <= 2^40).
  { split; [exact Gml|]. destruct (Z_lt_le_dec 0 (am_maplen amg)) as [Pos|Nz]; [|lia].
    destruct (Gmp Pos) as (r0 & rg0 & Em0 & Hr0 & _ & _ & Len0 & _).
    assert (Erg : rg0 = rg) by (rewrite Em0 in Hr; cbn [prid] in Hr; rewrite Hr in Hr0; injection Hr0 as <-; reflexivity). subst rg0.
    clear - Len0 G1 G3 HTB. unfold PGSZ in *. lia. }
  assert (Hml' : am_maplen amg <> 0 -> am_last amg <> 0).
  { destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. intros Hnz. destruct (C26 ltac:(lia)) as [C|C]; [contradiction | exact C]. }
  assert (Estf : ef_st memv sz idx = st) by (unfold ef_st; rewrite Est, Emem, Hstr16; ring).
  destruct (seg_nenf R m4 rom idx j Gv sz (st_mmap_counter s4) (am_last amg) (am_maplen amg) memv h3 h16 R1 R10 R18 R22 R25
              ltac:(clear - Hidx; lia) ltac:(clear - Mlast; lia) ltac:(clear - Hj Hsc; lia) Hml Hml' ltac:(clear - Pg1 Pg2 HK1 Hsp2; lia) Pg4
              ltac:(clear - Hsz; lia) ltac:(rewrite Emem; clear - G1 Ho; unfold PGSZ in *; lia)
              ltac:(rewrite Emem; rewrite Hstr16 in Hgx; clear - Hgx G3 HTB Ho Hsz; nia) ltac:(clear - C9; lia) Hh3 Hh16
              MA Msz Mctr MBITS MMEM
              ltac:(replace (memv + 16 * sz * idx + 12) with (st - 4) by (rewrite Est, Emem, Hstr16; ring); exact Mck)
              ltac:(replace (memv + 16 * sz * idx + 13) with (st - 3) by (rewrite Est, Emem, Hstr16; ring); exact Mh3)
              ltac:(replace (memv + 16 * sz * idx + 14) with (st - 2) by (rewrite Est, Emem, Hstr16; ring); exact Mh16)
              ltac:(rewrite Estf; intros d k Hd Hk; apply MWIN; [exact Hd | rewrite Hstr16; lia])
              ltac:(rewrite Estf; rewrite Hstr16 in Dg; clear - Dg; lia))
    as (R5 & Hms5 & Q10 & Q1 & Q18 & QK).
  rewrite Estf, efb_whole in Hms5. rewrite Estf in Q10.
  set (m5 := efw m4 idx memv st) in *.
  assert (OUT5 : forall x, 0 <= x < 2^64 -> ~ (st - 3 <= x < st) -> m5 (wa x) = m4 (wa x)).
  { intros x Hx Hn. unfold m5, efw. rewrite !MngWb.wbytes_out by (cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite ?u_wa_small by lia; lia). reflexivity. }
  assert (G5 : mem_grows m4 m5) by (unfold m5, efw; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (TR5 : forall x n, 0 <= x -> x + Z.of_nat n <= 2^64 -> (x + Z.of_nat n <= st - 3 \/ st <= x) -> rdn SEGS m5 (wa x) n = rdn SEGS m4 (wa x) n).
  { intros x n H1 H2 H3. apply rdn_frame_n; [exact H1 | exact H2 |]. intros y Hy. apply OUT5; clear - Hy H1 H2 H3; lia. }
  assert (F5 : as_frame R0 m5 sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9).
  { apply (as_frame_mem R0 m4); [exact F | |]; intros x Hx; apply OUT5; clear - Hx Hst Hslot Dslot HK1 Hsp2 Sp; lia. }
  (* [comment removed for export] *)
  assert (RAW : forall d, d = 0 \/ d = 8 \/ d = 32 -> rdn SEGS m5 (wa (mta + d)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { intros d Hd. rewrite TR5 by (clear - Hd Dm Pm1 Pm2 HK1 Hsp2 Sp; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (Hc : In (MCell (LMem (padd mt d)) 8 (VZ 0)) (image s4)).
    { destruct Hmt0 as [E0|E0]; apply (msc_key_in_image s4 mt _ _ KS4 E0); cbn [meta_slot_cells optr];
        destruct Hd as [->|[->| ->]]; cbn [In]; unfold META_prev, META_next, META_bits; repeat first [ (left; reflexivity) | right ]. }
    pose proof (RDI _ Hc ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite LP in H. exact H. }
  assert (Mh5 : rdn SEGS m5 (wa (st + -3)) 1 = Some (word_to_le_bytes 1 (wa idx))).
  { unfold m5, efw. replace (st + -3) with (st - 3) by ring.
    pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 1 (wa idx))
                  (wbytes (wbytes m4 (wa (st - 3)) (word_to_le_bytes 1 (wa idx))) (wa (st - 2)) (word_to_le_bytes 2 (wa ((st - memv - 16) / 16))))
                  (wa (st - 3))) as H.
    rewrite length_N_to_le_bytes in H. apply H. rewrite u_wa_small by (clear - Hst Hslot Sp HK1 Hsp2; lia). clear - Hst Hslot Sp HK1 Hsp2. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  assert (Musg5 : rdn SEGS m5 (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa (usage_of s4 sc)))) by (rewrite TR5 by (clear - Dslot Hsc Hst Sp; cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Musg).
  assert (Mact5 : rdn SEGS m5 (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (rewrite TR5 by (clear - Dslot Hsc Hst Sp; cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Mact).
  assert (Mhb5 : rdn SEGS m5 (wa (st + 8)) 1 = Some (word_to_le_bytes 1 (wa hb))).
  { rewrite TR5 by (clear - Hst Hslot Sp HK1 Hsp2; cbn [Z.of_nat Pos.of_succ_nat]; lia). apply (rdn1_of_bview L); [exact Ehb | exact Rhb | clear - Hst Hslot Sp HK1 Hsp2; lia]. }
  destruct (key_slot_range HTOP (mt :: X) (Some (g, idx)) U s4 L mt HI HG Kmt) as (ar & j' & rr & rga & Har & Hj' & Ear & Epr & Hrr & Hlv & Hkda & A1' & A2' & A3' & A4').
  fold mta in A4'.
  assert (Wmt : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m5 (wa (mta + 0 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m4 m5 _ G5).
    refine (pc_wr HTOP L [] s4 m4 sp0 K (LMem ar, PGSZ) P4 _ (mta + 0) 40 _ _ _ _ d k Hd Hk).
    - right. apply in_app_iff. left. apply (in_map (fun a0 => (LMem a0, PGSZ))). exact Har.
    - cbn [fst snd]. rewrite A4'. unfold AREA_HDR, META_SIZE. clear - Hj'; lia.
    - cbn [fst snd]. rewrite A4'. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - Hj'; lia.
    - clear - Pm1; lia.
    - clear - Pm2 HK1 Hsp2; lia. }
  assert (WC : forall o n, 0 <= o -> o + n <= 928 -> forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m5 (wa (614104 + o + d)) k = true).
  { intros o n Ho' Hn d k Hd Hk. apply (store_ok_mono SEGS k m4 m5 _ G5).
    refine (pc_wr HTOP L [] s4 m4 sp0 K (LCtx 0, CTX_SIZE) P4 (or_introl eq_refl) (614104 + o) n _ _ _ _ d k Hd Hk);
      cbn [fst snd]; rewrite ?Lc; unfold CTX_SIZE; clear - Ho' Hn; lia. }
  assert (Husg : 0 <= usage_of s4 sc <= 2^60).
  { split; [|exact Hus]. unfold usage_of, znth. destruct (nth_in_or_default (Z.to_nat sc) (st_usage s4) 0) as [E|E]; [exact (C5 _ E) | rewrite E; lia]. }
  destruct (seg_ntail R5 m5 rom sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 R0 mta st cnt0 (usage_of s4 sc) hb idx F5
              ltac:(regk QK 2%nat; exact R2) ltac:(regk QK 8%nat; exact R8) ltac:(regk QK 9%nat; exact R9) Q10
              ltac:(regk QK 19%nat; exact R19) ltac:(regk QK 20%nat; exact R20) ltac:(regk QK 21%nat; exact R21)
              ltac:(regk QK 23%nat; exact R23) ltac:(regk QK 24%nat; exact R24)
              Pm1 Pm3 Pm4 Hst Hal ltac:(clear - Hcnt; lia) Husg
              ltac:(clear - Rhb; lia) ltac:(clear - Hidx Mlast; lia) ltac:(clear - Hend HK1; lia) Dst
              ltac:(destruct Dm as [Dm|Dm]; [left; exact Dm | right; rewrite Hstr in Dm; clear - Dm Hfit Hsize Hcnt; nia])
              ltac:(clear - Pm2 HK1; lia) ltac:(clear - Hsize; lia)
              (RAW 32 ltac:(lia)) (RAW 0 ltac:(lia)) (RAW 8 ltac:(lia)) Mh5 Musg5 Mact5 Mhb5 Wmt
              ltac:(intros d k Hd Hk; replace (st + -4 + d) with (st - 4 + d) by ring; apply (store_ok_mono SEGS k m4 m5 _ G5); apply MWIN; [exact Hd | rewrite Hstr; clear - Hk Hfit; lia])
              ltac:(intros d k Hd Hk; replace (8 * sc + 614568 + d) with (614104 + (464 + 8 * sc) + d) by ring; apply (WC (464 + 8 * sc) 8); clear - Hd Hk Hsc; lia)
              ltac:(intros d k Hd Hk; replace (8 * sc + 614184 + d) with (614104 + (80 + 8 * sc) + d) by ring; apply (WC (80 + 8 * sc) 8); clear - Hd Hk Hsc; lia)
              ltac:(clear - Hsp1 HK1; lia))
    as (R6 & Hms6 & S1 & S2 & S8 & S9 & S10 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & SK).
  exists R6, hb. split; [clear - Rhb; lia|]. split; [exact (msteps_trans SEGS _ _ _ Hms5 Hms6)|].
  repeat (split; [assumption|]).
  intros k Hk. rewrite (SK k Hk). exact (QK k ltac:(clear - Hk; klist Hk)).
Qed.
End NEST.
