(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfArith.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfSlot OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS MngGM
                        AXF_eez AXG_ntfm AXG_ntfg AXG_nQ AXG_nD AXG_nM AXG_nN AXG_nF AXG_ntfP AXG_ntfE AXG_ntfDm AXG_ntfD AXG_ntfF MngMk_c1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition mi_base (L : layout) (mi : option (nat * Z)) : Z := match mi with Some (k, _) => ly_reg L k | None => 0 end.
Definition mi_len (mi : option (nat * Z)) : Z := match mi with Some (_, len) => len | None => 0 end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma keep_trans : forall R3 R2 R1 : bvmap 5 word, keep_regs R3 R2 -> keep_regs R2 R1 -> keep_regs R3 R1.
Proof. intros R3 R2 R1 A B n Hn. rewrite (A n Hn). exact (B n Hn). Qed.

Lemma keep_of_exit : forall R' R ra s0 s1 s2 s3 sp0 b l, ntf_exit R' R ra s0 s1 s2 s3 sp0 b l -> keep_regs R' R.
Proof. intros R' R ra s0 s1 s2 s3 sp0 b l H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.

Lemma ntf_exit_keep : forall R' R2 R1 ra s0 s1 s2 s3 sp0 b l, ntf_exit R' R2 ra s0 s1 s2 s3 sp0 b l -> keep_regs R2 R1 ->
  ntf_exit R' R1 ra s0 s1 s2 s3 sp0 b l.
Proof.
  intros R' R2 R1 ra s0 s1 s2 s3 sp0 b l (E1 & E2 & E8 & E9 & E18 & E19 & E10 & E11 & Ek) Hk.
  repeat (split; [assumption|]). exact (keep_trans R' R2 R1 Ek Hk).
Qed.

Lemma NC_unshift : forall L X EXC s m sp0 K d, NC L X EXC s m (sp0 - d) (K - d) -> stk_ok SEGS m (wa sp0) K -> sp0 <= 2^47 -> sp0 mod 16 = 0 ->
  0 <= d -> NC L X EXC s m sp0 K.
Proof.
  intros L X EXC s m sp0 K d N HS H1 H2 Hd. destruct N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  replace (sp0 - d - (K - d)) with (sp0 - K) in * by ring.
  constructor; try assumption. lia.
Qed.

Lemma FRM_widen : forall L s sp0 K d m m', 0 <= d -> FRM L s (sp0 - d) (K - d) m m' -> FRM L s sp0 K m m'.
Proof.
  intros L s sp0 K d m m' Hd F x Hx Hne. destruct (F x Hx Hne) as [A|A]; [left; lia | right; exact A].
Qed.

(* [comment removed for export] *)
Lemma FRM_below : forall L s sp0 K m m' x, FRM L s sp0 K m m' -> (forall c, In c (image s) -> cplace L (sp0 - K) c) -> 2^20 <= sp0 - K -> 0 <= K ->
  0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> x < sp0 /\ (x < 0x95e40 \/ 0x95e48 <= x).
Proof.
  intros L s sp0 K m m' x F HC HK HK0 Hx Hne. destruct (F x Hx Hne) as [A|(c & Hc & Hin)].
  - lia.
  - pose proof (HC c Hc) as (P1 & P2 & P3). unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia.
Qed.

Lemma frame_keep_inner : forall L s3 sp0 K m3 m4 (R3 R4 : bvmap 5 word) canary ra s0 s1 s2 s3v,
  ntf_frame R3 m3 sp0 canary ra s0 s1 s2 s3v -> FRM L s3 (sp0 - 96) (K - 96) m3 m4 ->
  (forall c, In c (image s3) -> cplace L (sp0 - K) c) -> 2^20 <= sp0 - K -> 96 <= K -> mem_grows m3 m4 ->
  getr R4 2 = getr R3 2 -> getr R4 9 = getr R3 9 -> ntf_frame R4 m4 sp0 canary ra s0 s1 s2 s3v.
Proof.
  intros L s3 sp0 K m3 m4 R3 R4 canary ra s0 s1 s2 s3v F FR HC HK HK96 Hg E2 E9.
  pose proof F as [_ _ Rsp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  apply (ntf_frame_keep R3 R4 m3 m4 sp0 canary ra s0 s1 s2 s3v F E2 E9 Hg).
  intros x Hx. destruct (decide (m4 (wa x) = m3 (wa x))) as [E|E]; [exact E|]. exfalso.
  replace (sp0 - 96 - (K - 96)) with (sp0 - K) in FR by ring.
  assert (HC' : forall c, In c (image s3) -> cplace L (sp0 - 96 - (K - 96)) c) by (replace (sp0 - 96 - (K - 96)) with (sp0 - K) by ring; exact HC).
  destruct (FRM_below L s3 (sp0 - 96) (K - 96) m3 m4 x FR HC' ltac:(lia) ltac:(lia) ltac:(lia) E) as (B1 & B2). lia.
Qed.

Lemma loc_SP0 : forall L r, loc_addr L (LMem (SP r 0)) = ly_reg L r.
Proof. intros L r. cbn. ring. Qed.

Lemma metas_usg_seq_rec : forall s sA sc l, st_metas (s_rec sc (s_seq (s_usg s sA sc l))) = st_metas sA.
Proof.
  intros s sA sc l. unfold s_rec, s_seq, s_usg.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; reflexivity.
Qed.

Lemma ra_usg_seq_rec : forall s sA sc l, st_regions (s_rec sc (s_seq (s_usg s sA sc l))) = st_regions sA /\ st_areas (s_rec sc (s_seq (s_usg s sA sc l))) = st_areas sA.
Proof.
  intros s sA sc l. unfold s_rec, s_seq, s_usg.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; split; reflexivity.
Qed.

Lemma EXC_z_keep : forall X s s' EXC, EXC_z X s EXC -> (forall x, In x X -> MT s' x = MT s x) -> EXC_z X s' EXC.
Proof.
  intros X s s' EXC H HZ l Hl. destruct (H l Hl) as (x & a & Hx & Mx & El). exists x, a. split; [exact Hx|]. split; [rewrite HZ by exact Hx; exact Mx | exact El].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NTF.
Context {fx : FPState}.

Definition NTF_C (f : nat) : Prop :=
  forall L X EXC U s m R rom sp0 K g i am,
    NC L X EXC s m sp0 K -> getr R 2 = wa sp0 -> getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa i ->
    Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c <= 2^40) ->
    ((am_prev am, am_next am) <> (None, None) -> active_hd s (am_sc am) <> Some g -> am_freed am <> 0) ->
    (fneed (am_sc am) <= f)%nat -> 1024 + 96 * Z.of_nat (fneed (am_sc am)) <= K ->
    exists R' m' mi s',
      msteps SEGS (mkst R (wa 0x518d0) m rom) (mkst R' (wa 0x51ca0) m' rom) /\
      ntf_exit R' R (bv_unsigned (getr R 1)) (bv_unsigned (getr R 8)) (bv_unsigned (getr R 9)) (bv_unsigned (getr R 18))
               (bv_unsigned (getr R 19)) sp0 (mi_base L mi) (mi_len mi) /\
      0 <= mi_base L mi <= 2^64-1 /\ 0 <= mi_len mi <= 2^64-1 /\
      nontrivial_free f g i s = IRet (mi, s') /\ NC L X EXC s' m' sp0 K /\ RS L s' s /\
      (forall x, In x X -> MT s' x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\ MKS s' s /\
      st_regions s' = st_regions s /\ st_areas s' = st_areas s.


#[using="Type"] Lemma HMP_of : forall L X EXC s m sp0 K, NC L X EXC s m sp0 K -> forall q, In q (keys s) ->
  1 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= sp0 - K /\
  (loc_addr L (LMem q) + 40 <= 0x10000 \/ 0x97000 <= loc_addr L (LMem q)) /\ loc_addr L (LMem q) mod 8 = 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros L X EXC s m sp0 K N. exact (nc_mplace _ _ _ _ _ _ _ N). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma gm_place : forall L X EXC s m sp0 K g a, NC L X EXC s m sp0 K -> MT s g = Some (MUsed a) ->
  1 <= loc_addr L (LMem (am_mem a)) /\ loc_addr L (LMem (am_mem a)) + 8 <= sp0 - K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m sp0 K g a N Mg. pose proof N as [_ _ _ HK _ _ _ _ _ _ _ HC _ _].
  set (CH := MCell (LMem (am_mem a)) 8 (VP g)).
  assert (CHi : In CH (image s)).
  { rewrite image_parts. apply in_app_iff. right. apply in_app_iff. right. apply (group_in_gpart s g a CH Mg (proj1 HK)). left. reflexivity. }
  pose proof (HC CH CHi) as (Q1 & Q2 & _). unfold CH in Q1, Q2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in Q1, Q2. split; assumption.
Qed.

#[using="Type"] Theorem ntf_grest_map : forall L X EXC U s sA m R rom sp0 K canary ra s0 s1 s2 s3 g i am f,
  NC L X EXC sA m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 18 = wa 0x95ed8 ->
  Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c) -> DQP X U s g am sA ->
  am_maplen am <> 0 -> (0 <= am_sc am < 48 -> 0 <= usage_of s (am_sc am) <= 2^60) -> 0 <= meta_bits am <= 2^64-1 ->
  exists R' m' s5, msteps SEGS (mkst R (wa 0x51af8) m rom) (mkst R' (wa 0x51ca0) m' rom) /\
    ntf_exit R' R ra s0 s1 s2 s3 sp0 (mi_base L (Some (prid (am_mem am), am_maplen am * 4096))) (mi_len (Some (prid (am_mem am), am_maplen am * 4096))) /\
    0 <= mi_base L (Some (prid (am_mem am), am_maplen am * 4096)) <= 2^64-1 /\ 0 <= mi_len (Some (prid (am_mem am), am_maplen am * 4096)) <= 2^64-1 /\
    g_rest f g s (am_sc am) sA = IRet (Some (prid (am_mem am), am_maplen am * 4096), s5) /\
    NC L X EXC s5 m' sp0 K /\ RS L s5 sA /\ (forall x, In x X -> MT s5 x = MT sA x) /\ mem_grows m m' /\ FRM L sA sp0 K m m' /\ MKS s5 sA /\
    st_regions s5 = st_regions sA /\ st_areas s5 = st_areas sA.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC U s sA m R rom sp0 K canary ra s0 s1 s2 s3 g i am f N F R10 R18 HI Hu HU DQ Hml Rus RW.
  destruct DQ as (HI1 & MgA & EusA & _ & _ & _ & _ & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. apply memb_false_notIn in NXg.
  destruct (masks_range_inv _ _ _ s g am HI Hu) as (RA & RF & Rl & Rs & Rm).
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & Gmp & _).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [left | right]; exact C).
  destruct (Gmp ltac:(lia)) as (r & rg & Emem & _).
  pose proof (inv_ctx HI1) as (_ & ClU & ClM & _ & _ & _ & _ & Cseq & _).
  set (am1 := am_set_links None None am) in *.
  destruct (seg_map L X EXC s sA m R rom sp0 K canary ra s0 s1 s2 s3 g am1 N F R10 R18 MgA Hscr Rl ltac:(clear - Rm Hml; unfold am1; cbn; lia) ltac:(exact (proj2 RW))
              (eq_sym EusA) ltac:(intros H48; change (am_sc am1) with (am_sc am) in *; unfold usage_of; rewrite EusA; pose proof (Rus (conj (proj1 Rs) H48)) as HR; unfold usage_of in HR; clear - HR; lia) ClU ClM Cseq)
    as (R3 & m3 & Hms3 & N3 & F3 & HRS3 & HZ3 & Hg3 & FR3 & R3_10 & R3_11 & R3_12 & R3_18 & Hk3).
  set (s4 := s_rec (am_sc am1) (s_seq (s_usg s sA (am_sc am1) (am_last am1)))) in *.
  assert (M4g : MT s4 g = Some (MUsed am1)) by (rewrite HZ3; exact MgA).
  pose proof (NC_add_zombie L X EXC s4 m3 sp0 K g am1 N3 M4g) as N3z.
  assert (EX4 : EXC_z X s4 EXC) by exact (nc_exc _ _ _ _ _ _ _ N3).
  assert (HI4 : Inv (g :: X) None U s4) by exact (seq_rec_Inv (g :: X) None U _ (am_sc am) (usg_Inv X U s g i am sA HI Hu HU HI1 EusA)).
  destruct (gm_place L X EXC sA m sp0 K g am1 N MgA) as (B1 & B2). pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  assert (RB : 0 <= loc_addr L (LMem (am_mem am1)) <= 2^64-1) by (clear - B1 B2 Hsp2 HK1; lia).
  assert (RLN : 0 <= am_maplen am1 * 4096 <= 2^64-1) by (clear - RW Rl Rs Rm; unfold am1; cbn; unfold meta_bits in RW; lia).
  destruct (ntf_fm L X EXC U s4 m3 R3 rom sp0 K canary ra s0 s1 s2 s3 g am1 (loc_addr L (LMem (am_mem am1))) (am_maplen am1 * 4096)
              N3z EX4 F3 R3_10 R3_11 R3_12 R3_18 M4g NXg RB RLN HI4)
    as (R4 & m4 & s5 & Hms4 & Hex4 & Hfm & N4 & HRS4 & HZ4 & Hg4 & FR4 & MK4 & RG4 & AR4).
  assert (EB : loc_addr L (LMem (am_mem am1)) = mi_base L (Some (prid (am_mem am), am_maplen am * 4096))).
  { unfold am1. cbn [am_mem am_set_links mi_base]. rewrite Emem. apply loc_SP0. }
  exists R4, m4, s5. split; [eapply msteps_trans; [exact Hms3 | exact Hms4]|].
  split; [refine (ntf_exit_keep R4 R3 R _ _ _ _ _ _ _ _ _ Hk3); rewrite <- EB; exact Hex4|].
  split; [rewrite <- EB; exact RB|]. split; [exact RLN|].
  split; [exact (g_rest_map f g s sA (am_sc am) am1 s5 MgA Hml Hfm)|].
  split; [exact N4|]. split; [exact (RS_trans L sA s4 s5 HRS4 HRS3)|].
  split; [intros x Hx; rewrite (HZ4 x Hx); exact (HZ3 x)|].
  split; [exact (mem_grows_trans _ _ _ Hg3 Hg4)|].
  split; [exact (FRM_trans L sA s4 sp0 K m m3 m4 HRS3 FR3 FR4)|].
  split; [exact (MKS_trans s5 s4 sA MK4 (MKS_metas s4 sA (metas_usg_seq_rec s sA (am_sc am1) (am_last am1))))|].
  destruct (ra_usg_seq_rec s sA (am_sc am1) (am_last am1)) as [E1 E2]. split; [rewrite RG4; exact E1 | rewrite AR4; exact E2].
Qed.


#[using="Type"] Theorem ntf_grest_nest : forall f, NTF_C f -> forall L X EXC U s sA m R rom sp0 K canary ra s0 s1 s2 s3 g i am,
  NC L X EXC sA m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 18 = wa 0x95ed8 ->
  Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c <= 2^40) -> DQP X U s g am sA ->
  am_maplen am = 0 -> (0 <= am_sc am < 48 -> 0 <= usage_of s (am_sc am) <= 2^60) -> 0 <= meta_bits am <= 2^64-1 ->
  (fneed (am_sc am) <= S f)%nat -> 1024 + 96 * Z.of_nat (fneed (am_sc am)) <= K ->
  exists R' m' mi s5, msteps SEGS (mkst R (wa 0x51af8) m rom) (mkst R' (wa 0x51ca0) m' rom) /\
    ntf_exit R' R ra s0 s1 s2 s3 sp0 (mi_base L mi) (mi_len mi) /\ 0 <= mi_base L mi <= 2^64-1 /\ 0 <= mi_len mi <= 2^64-1 /\
    g_rest f g s (am_sc am) sA = IRet (mi, s5) /\
    NC L X EXC s5 m' sp0 K /\ RS L s5 sA /\ (forall x, In x X -> MT s5 x = MT sA x) /\ mem_grows m m' /\ FRM L sA sp0 K m m' /\ MKS s5 sA /\
    st_regions s5 = st_regions sA /\ st_areas s5 = st_areas sA.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f IH L X EXC U s sA m R rom sp0 K canary ra s0 s1 s2 s3 g i am N F R10 R18 HI Hu HU DQ Hml Rus RW Hf HK.
  destruct DQ as (HI1 & MgA & EusA & _ & _ & C1 & Mo1 & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg]. apply memb_false_notIn in NXg.
  destruct (masks_range_inv _ _ _ s g am HI Hu) as (RA & RF & Rl & Rs & Rm).
  pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _ & Gns).
  destruct (Gns Hml) as (N63 & pg & amp & idx & fr & Up & Hidx & Hfr & Kfr & Emem & Hscp & N63p & _).
  assert (Hsc : 0 <= am_sc am < 48) by (destruct Gcl as [(C & _) | (C & _)]; [exfalso; exact (N63 C) | exact C]).
  pose proof (usedX_MT _ _ _ _ Up) as [Mp NXp].
  destruct (masks_range_inv _ _ _ s pg amp HI Up) as (_ & _ & RPl & RPs & _).
  assert (Hpg : pg <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ Up Hu) as E; rewrite E in Hscp; lia).
  assert (UpA : usedX (g :: X) sA pg amp).
  { apply usedX_intro.
    - rewrite memb_cons, NXp. replace (sptr_eqb pg g) with false by (symmetry; apply sptr_eqb_neq; exact Hpg). reflexivity.
    - rewrite (Mo1 pg); [exact Mp | | exact Hpg]. intros a Ha. pose proof (usedX_fun _ _ _ _ _ Ha Up) as ->. lia. }
  assert (Hscp48 : 0 <= am_sc amp < 48).
  { pose proof (inv_groups HI pg amp Up) as (_ & _ & _ & Gclp & _). destruct Gclp as [(C & _) | (C & _)]; [exfalso; exact (N63p C) | exact C]. }
  assert (FN : Z.of_nat (fneed (am_sc am)) = 48 - am_sc am).
  { unfold fneed. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z2Nat.id by lia. reflexivity. }
  assert (FNp : Z.of_nat (fneed (am_sc amp)) = 48 - am_sc amp).
  { unfold fneed. replace (am_sc amp <? 48) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z2Nat.id by lia. reflexivity. }
  pose proof (inv_ctx HI1) as (_ & ClU & _).
  set (am1 := am_set_links None None am) in *.
  destruct (seg_ns L X EXC (fun c => U c + contrib X s c g) s sA m R rom sp0 K canary ra s0 s1 s2 s3 g am1 pg amp idx fr
              N F R10 R18 MgA NXg Hml Hsc Rl ltac:(exact (proj2 RW)) (eq_sym EusA)
              ltac:(change (am_sc am1) with (am_sc am); unfold usage_of; rewrite EusA; pose proof (Rus Hsc) as HR; unfold usage_of in HR; clear - HR; lia)
              ClU HI1 UpA Hidx Hfr Kfr Emem ltac:(clear - FN HK Hsc; lia))
    as (R3 & m3 & Hms3 & N3 & F3 & HRS3 & HZ3 & Hg3 & FR3 & Hff & MpU & Hgrp & R3_1 & R3_2 & R3_8 & R3_9 & R3_10 & R3_11 & R3_18 & R3_19 & Hk3).
  set (v := usage_of s (am_sc am) - (am_last am + 1)).
  assert (Es2 : s_usg s sA (am_sc am1) (am_last am1) = set_usage (zset (am_sc am) v (st_usage sA)) sA).
  { unfold s_usg. replace (am_sc am1 <? 48) with true by (symmetry; apply Z.ltb_lt; change (am_sc am1) with (am_sc am); lia). reflexivity. }
  set (sU := s_usg s sA (am_sc am1) (am_last am1)) in *.
  set (amp' := upd_slot amp idx (mkSlot (ss_hdr (nth_slot amp idx)) None)).
  set (sF := s_ff sU pg amp idx) in *.
  assert (HI2 : Inv (g :: X) None U sU) by exact (usg_Inv X U s g i am sA HI Hu (fun c => proj1 (HU c)) HI1 EusA).
  assert (Up2 : usedX (g :: X) sU pg amp) by (rewrite Es2; exact UpA).
  assert (Hno : forall c ac, usedX (g :: X) sU c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start amp idx).
  { intros c ac Hc Hmlc Emc. rewrite Es2 in Hc. pose proof (usedX_cons_inv _ _ _ _ _ Hc) as [Hcg _].
    destruct (C1 c ac Hc) as (ac0 & H0 & E0 & _).
    apply (same_mem_contra X _ U s c ac0 g am HI H0 Hu Hcg). rewrite <- E0, Emc. symmetry. exact Emem. }
  assert (HI3 : Inv (g :: X) (Some (pg, idx)) U sF) by exact (forget_Inv (g :: X) U sU pg amp idx fr HI2 Up2 Hidx Hfr Hno).
  assert (Up3 : usedX (g :: X) sF pg amp').
  { apply usedX_intro; [exact (proj2 (usedX_MT _ _ _ _ UpA)) | apply MT_upd_same]. }
  pose proof (upd_slot_fields amp idx (mkSlot (ss_hdr (nth_slot amp idx)) None)) as (Fm & Fl & Fsc & Fml & _ & _ & _). fold amp' in Fm, Fl, Fsc, Fml.
  assert (HR2' : (am_prev amp', am_next amp') <> (None, None) -> active_hd sF (am_sc amp') <> Some pg -> am_freed amp' <> 0).
  { intros Hl Hnh. replace (am_freed amp') with (am_freed amp) by (unfold amp'; destruct amp; reflexivity).
    replace (am_prev amp', am_next amp') with (am_prev amp, am_next amp) in Hl by (unfold amp'; destruct amp; reflexivity).
    rewrite Fsc in Hnh. replace (active_hd sF (am_sc amp)) with (active_hd sU (am_sc amp)) in Hnh by reflexivity.
    apply (proj2 (proj2 (ring_facts _ _ _ _ _ _ HI2 Up2 ltac:(lia) ltac:(lia)))); [exact Hl | exact Hnh | intros; discriminate]. }
  assert (Hf' : (fneed (am_sc amp') <= f)%nat).
  { rewrite Fsc. apply Nat2Z.inj_le. rewrite FNp. pose proof (proj1 (Nat2Z.inj_le _ _) Hf) as E. rewrite FN, Nat2Z.inj_succ in E. clear - E Hscp. lia. }
  assert (HK' : 1024 + 96 * Z.of_nat (fneed (am_sc amp')) <= K - 96) by (rewrite Fsc, FNp; clear - FN HK Hscp; lia).
  assert (R3_2' : getr R3 2 = wa (sp0 - 96)) by exact R3_2.
  destruct (IH L (g :: X) (LMem (am_mem am1) :: EXC) U sF m3 R3 rom (sp0 - 96) (K - 96) pg idx amp' N3 R3_2' R3_10 R3_11 HI3 Up3 HU HR2' Hf' HK')
    as (R4 & m4 & mi & sI & Hms4 & Hex4 & Rb4 & Rl4 & Ht4 & N4 & HRS4 & HZ4 & Hg4 & FR4 & MK4 & RG4 & AR4).
  pose proof Hex4 as (E4_1 & E4_2 & E4_8 & E4_9 & E4_18 & E4_19 & E4_10 & E4_11 & _).
  rewrite R3_1 in E4_1. rewrite R3_9 in E4_9. rewrite R3_18 in E4_18. rewrite R3_19 in E4_19.
  pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2. pose proof (nc_sp3 _ _ _ _ _ _ _ N) as Hsp3.
  pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  pose proof (HMP_of _ _ _ _ _ _ _ N g ltac:(eapply MT_keys; exact MgA)) as (G1 & G2 & _ & _).
  rewrite u_wa_small in E4_1, E4_9, E4_18, E4_19 by (clear - G1 G2 Hsp2 HK1; lia).
  destruct (seg_nr R4 m4 rom sp0 (loc_addr L (LMem g)) (mi_base L mi) (mi_len mi) E4_1 ltac:(rewrite E4_2; f_equal; ring) E4_9 E4_10 E4_11 E4_18 E4_19
              ltac:(clear - Hsp1 Hsp2 HK1; lia) Hsp3 ltac:(clear - G1 G2 Hsp2 HK1; lia) Rb4 Rl4)
    as (R5 & Hms5 & R5_2 & R5_9 & R5_10 & R5_11 & R5_12 & R5_18 & Hk5).
  assert (HSTK4 : stk_ok SEGS m4 (wa sp0) K) by exact (stk_ok_grows SEGS m m4 (wa sp0) K (nc_stk _ _ _ _ _ _ _ N) (mem_grows_trans _ _ _ Hg3 Hg4)).
  pose proof (NC_unshift L (g :: X) (LMem (am_mem am1) :: EXC) sI m4 sp0 K 96 N4 HSTK4 Hsp2 Hsp3 ltac:(lia)) as N4'.
  assert (HC3 : forall c, In c (image sF) -> cplace L (sp0 - K) c).
  { pose proof (nc_cells _ _ _ _ _ _ _ N3) as HC3. replace (sp0 - 96 - (K - 96)) with (sp0 - K) in HC3 by ring. exact HC3. }
  assert (F5 : ntf_frame R5 m4 sp0 canary ra s0 s1 s2 s3).
  { apply (frame_keep_inner L sF sp0 K m3 m4 R3 R5 canary ra s0 s1 s2 s3 F3 FR4 HC3 Hsp1 ltac:(lia) Hg4); [rewrite R5_2, R3_2; f_equal; ring | rewrite R5_9, R3_9; reflexivity]. }
  assert (M3g : MT sF g = Some (MUsed am1)).
  { unfold sF, s_ff. rewrite MT_set_other by exact (fun E => Hpg (eq_sym E)). rewrite Es2. exact MgA. }
  assert (M4g : MT sI g = Some (MUsed am1)) by (rewrite (HZ4 g (or_introl eq_refl)); exact M3g).
  assert (EX4 : EXC_z X sI EXC).
  { apply (EXC_z_keep X sA sI EXC (nc_exc _ _ _ _ _ _ _ N)). intros x Hx. rewrite (HZ4 x (or_intror Hx)). exact (HZ3 x Hx). }
  assert (HI4 : Inv (g :: X) None U sI).
  { pose proof (nontrivial_free_spec f (g :: X) U sF pg idx amp' (fun r => Inv (g :: X) None U (snd r)) HI3 Up3 (fun c => proj1 (HU c)) HR2' Hf'
                  (fun r H => proj1 H)) as A. rewrite Ht4 in A. exact A. }
  destruct (ntf_fm L X EXC U sI m4 R5 rom sp0 K canary ra s0 s1 s2 s3 g am1 (mi_base L mi) (mi_len mi) N4' EX4 F5 R5_10 R5_11 R5_12 R5_18 M4g NXg Rb4 Rl4 HI4)
    as (R6 & m6 & s5 & Hms6 & Hex6 & Hfm & N6 & HRS6 & HZ6 & Hg6 & FR6 & MK6 & RG6 & AR6).
  exists R6, m6, mi, s5.
  split; [eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5 | exact Hms6]|].
  split; [refine (ntf_exit_keep R6 R5 R _ _ _ _ _ _ _ _ Hex6 _); exact (keep_trans R5 R4 R Hk5 (keep_trans R4 R3 R (keep_of_exit _ _ _ _ _ _ _ _ _ _ Hex4) Hk3))|].
  split; [exact Rb4|]. split; [exact Rl4|].
  split; [exact (g_rest_nest f g s sA (am_sc am) am1 pg idx amp mi sI s5 MgA Hml ltac:(lia) Hff MpU Hgrp Ht4 Hfm)|].
  split; [exact N6|].
  split; [exact (RS_trans L sA sI s5 HRS6 (RS_trans L sA sF sI HRS4 HRS3))|].
  split; [intros x Hx; rewrite (HZ6 x Hx), (HZ4 x (or_intror Hx)); exact (HZ3 x Hx)|].
  split; [exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ Hg3 Hg4) Hg6)|].
  split; [apply (FRM_trans L sA sI sp0 K m m4 m6 (RS_trans L sA sF sI HRS4 HRS3)); [|exact FR6];
          exact (FRM_trans L sA sF sp0 K m m3 m4 HRS3 FR3 (FRM_widen L sF sp0 K 96 m3 m4 ltac:(lia) FR4))|].
  split.
  { apply (MKS_trans s5 sI sA MK6). apply (MKS_trans sI sF sA MK4).
    apply (MKS_trans sF sU sA).
    - unfold sF, s_ff. apply (MKS_setm_same sU pg amp); [rewrite Es2; exact (proj1 (usedX_MT _ _ _ _ UpA)) | exact (mm_forget amp idx fr _ ltac:(lia) Hfr Kfr)].
    - apply MKS_metas. rewrite Es2. reflexivity. }
  rewrite RG6, RG4, AR6, AR4. unfold sF, s_ff. rewrite Es2. split; reflexivity.
Qed.


#[using="Type"] Theorem ntf_group : forall f, NTF_C f -> forall L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g i am,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  Inv X (Some (g, i)) U s -> usedX X s g am -> (forall c, 0 <= U c <= 2^40) ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = true ->
  (0 <= am_sc am < 48 -> 0 <= usage_of s (am_sc am) <= 2^60) -> 0 <= meta_bits am <= 2^64-1 ->
  (fneed (am_sc am) <= S f)%nat -> 1024 + 96 * Z.of_nat (fneed (am_sc am)) <= K ->
  exists R' m' mi s', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51ca0) m' rom) /\
    ntf_exit R' R ra s0 s1 s2 s3 sp0 (mi_base L mi) (mi_len mi) /\ 0 <= mi_base L mi <= 2^64-1 /\ 0 <= mi_len mi <= 2^64-1 /\
    nontrivial_free (S f) g i s = IRet (mi, s') /\
    NC L X EXC s' m' sp0 K /\ RS L s' s /\ (forall x, In x X -> MT s' x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\ MKS s' s /\
    st_regions s' = st_regions s /\ st_areas s' = st_areas s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f IH L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g i am N F R10 R12 R18 HI Hu HU Hcond Rus RW Hf HK.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  destruct (ntf_deq L X EXC U s m R rom sp0 K canary ra s0 s1 s2 s3 g am i N F R10 R12 R18 HI Hu Hcond)
    as (R2 & m2 & sA & Hms2 & Hdq & N2 & F2 & HRS2 & HZ2 & Hg2 & FR2 & R2_10 & R2_18 & Hk2 & DQ & MK2 & RG2 & AR2).
  assert (EG : forall mi s', g_rest f g s (am_sc am) sA = IRet (mi, s') -> nontrivial_free (S f) g i s = IRet (mi, s')).
  { intros mi s' E. rewrite (ntf_g_unfold f g i s am Mg Hcond). unfold bind. rewrite Hdq. exact E. }
  destruct (Z.eq_dec (am_maplen am) 0) as [Hml|Hml].
  - destruct (ntf_grest_nest f IH L X EXC U s sA m2 R2 rom sp0 K canary ra s0 s1 s2 s3 g i am N2 F2 R2_10 R2_18 HI Hu HU DQ Hml Rus RW Hf HK)
      as (R3 & m3 & mi & s5 & Hms3 & Hex3 & Rb3 & Rl3 & Ht3 & N3 & HRS3 & HZ3 & Hg3 & FR3 & MK3 & RG3 & AR3).
    exists R3, m3, mi, s5. split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|].
    split; [exact (ntf_exit_keep R3 R2 R _ _ _ _ _ _ _ _ Hex3 Hk2)|]. split; [exact Rb3|]. split; [exact Rl3|].
    split; [exact (EG mi s5 Ht3)|]. split; [exact N3|]. split; [exact (RS_trans L s sA s5 HRS3 HRS2)|].
    split; [intros x Hx; rewrite (HZ3 x Hx); exact (HZ2 x Hx)|]. split; [exact (mem_grows_trans _ _ _ Hg2 Hg3)|].
    split; [exact (FRM_trans L s sA sp0 K m m2 m3 HRS2 FR2 FR3)|]. split; [exact (MKS_trans s5 sA s MK3 MK2)|].
    rewrite RG3, AR3, RG2, AR2. split; reflexivity.
  - destruct (ntf_grest_map L X EXC U s sA m2 R2 rom sp0 K canary ra s0 s1 s2 s3 g i am f N2 F2 R2_10 R2_18 HI Hu (fun c => proj1 (HU c)) DQ Hml Rus RW)
      as (R3 & m3 & s5 & Hms3 & Hex3 & Rb3 & Rl3 & Ht3 & N3 & HRS3 & HZ3 & Hg3 & FR3 & MK3 & RG3 & AR3).
    exists R3, m3, (Some (prid (am_mem am), am_maplen am * 4096)), s5. split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|].
    split; [exact (ntf_exit_keep R3 R2 R _ _ _ _ _ _ _ _ Hex3 Hk2)|]. split; [exact Rb3|]. split; [exact Rl3|].
    split; [exact (EG _ s5 Ht3)|]. split; [exact N3|]. split; [exact (RS_trans L s sA s5 HRS3 HRS2)|].
    split; [intros x Hx; rewrite (HZ3 x Hx); exact (HZ2 x Hx)|]. split; [exact (mem_grows_trans _ _ _ Hg2 Hg3)|].
    split; [exact (FRM_trans L s sA sp0 K m m2 m3 HRS2 FR2 FR3)|]. split; [exact (MKS_trans s5 sA s MK3 MK2)|].
    rewrite RG3, AR3, RG2, AR2. split; reflexivity.
Qed.

#[using="Type"] Theorem ntf_contract : forall f, NTF_C f.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction f as [|f IH]; intros L X EXC U s m R rom sp0 K g i am N R2 R10 R11 HI Hu HU HR2g Hf HK.
  { exfalso. unfold fneed in Hf. destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E|]; lia. }
  destruct (ntf_facts L X EXC U s m sp0 K g i am N HI Hu (fun c _ => HU c))
    as (Mg & NXg & Hi & Rl & Hscr & Rml & RW & RA & RF & TBa & TBf & Hnk & Rus & Rbn & H63).
  destruct Hscr as [E63|Hsc].
  - destruct (H63 E63) as (Cl0 & Cml & Cav & Cfr & Ei0). subst i.
    destruct (seg_dec63 L X EXC s m R rom sp0 K g am N R2 R10 R11 Mg E63 Cl0 Cml ltac:(exact (proj2 RW)) Cav Cfr)
      as (R1 & m1 & canary & Hms1 & N1 & F1 & FR1 & Hg1 & R1_10 & R1_12 & R1_18 & Hk1).
    assert (Hcond : (Z.lor (am_freed am) (am_avail am) + bit 0 =? ones (am_last am)) && okay_to_free s g am = true).
    { rewrite Cav, Cfr, Cl0. unfold okay_to_free. rewrite E63. reflexivity. }
    assert (R1_12' : getr R1 12 = wa (am_sc am)) by (rewrite E63; exact R1_12).
    destruct (ntf_group f IH L X EXC U s m1 R1 rom sp0 K canary _ _ _ _ _ g 0 am N1 F1 R1_10 R1_12' R1_18 HI Hu HU Hcond Rus RW Hf HK)
      as (R' & m' & mi & s' & Hms & Hex & Rb & Rln & Ht & N' & HRS & HZ & Hg & FR & MK & RGx & ARx).
    exists R', m', mi, s'. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|].
    split; [exact (ntf_exit_keep R' R1 R _ _ _ _ _ _ _ _ Hex Hk1)|]. split; [exact Rb|]. split; [exact Rln|].
    split; [exact Ht|]. split; [exact N'|]. split; [exact HRS|]. split; [exact HZ|]. split; [exact (mem_grows_trans _ _ _ Hg1 Hg)|].
    split; [exact (FRM_trans L s s sp0 K m m1 m' (RS_refl L s) FR1 FR)|]. split; [exact MK|]. split; [exact RGx | exact ARx].
  - destruct (seg_dec L X EXC s m R rom sp0 K g am i N R2 R10 R11 Mg ltac:(clear - Hi Rl; lia) Rl Hsc Rml ltac:(exact (proj2 RW)) RA RF TBa TBf Hnk
                ltac:(pose proof (Rus Hsc) as HR; clear - HR; lia) Rbn)
      as (R1 & m1 & canary & Hms1 & N1 & F1 & FR1 & Hg1 & R1_10 & R1_12 & R1_11 & R1_13 & Hk1 & R1_18).
    destruct ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am) eqn:Hcond.
    + destruct (ntf_group f IH L X EXC U s m1 R1 rom sp0 K canary _ _ _ _ _ g i am N1 F1 R1_10 R1_12 (R1_18 eq_refl) HI Hu HU Hcond Rus RW Hf HK)
        as (R' & m' & mi & s' & Hms & Hex & Rb & Rln & Ht & N' & HRS & HZ & Hg & FR & MK & RGx & ARx).
      exists R', m', mi, s'. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|].
      split; [exact (ntf_exit_keep R' R1 R _ _ _ _ _ _ _ _ Hex Hk1)|]. split; [exact Rb|]. split; [exact Rln|].
      split; [exact Ht|]. split; [exact N'|]. split; [exact HRS|]. split; [exact HZ|]. split; [exact (mem_grows_trans _ _ _ Hg1 Hg)|].
      split; [exact (FRM_trans L s s sp0 K m m1 m' (RS_refl L s) FR1 FR)|]. split; [exact MK|]. split; [exact RGx | exact ARx].
    + destruct (ntf_else L X EXC U s m1 R1 rom sp0 K canary _ _ _ _ _ g am i f N1 F1 R1_10 R1_11 R1_12 R1_13 HI Hu HR2g Hcond)
        as (R' & m' & s' & Hms & Hex & Ht & N' & HRS & HZ & Hg & FR & MK & RGx & ARx).
      exists R', m', None, s'. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|].
      split; [exact (ntf_exit_keep R' R1 R _ _ _ _ _ _ _ _ Hex Hk1)|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [exact Ht|]. split; [exact N'|]. split; [exact HRS|]. split; [exact HZ|]. split; [exact (mem_grows_trans _ _ _ Hg1 Hg)|].
      split; [exact (FRM_trans L s s sp0 K m m1 m' (RS_refl L s) FR1 FR)|]. split; [exact MK|]. split; [exact RGx | exact ARx].
Qed.

End NTF.
