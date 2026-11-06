(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM AXF_eez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition EXC_z (X : list sptr) (s : astate) (EXC : list loc) : Prop :=
  forall l, In l EXC -> exists x a, In x X /\ MT s x = Some (MUsed a) /\ l = LMem (am_mem a).

Lemma EXC_ok_of_z : forall X s EXC, List.NoDup (keys s) -> EXC_z X s EXC -> EXC_ok s EXC.
Proof.
  intros X s EXC ND H l Hl. destruct (H l Hl) as (x & a & _ & Hx & ->).
  exists (MCell (LMem (am_mem a)) 8 (VP x)). split; [|split; reflexivity].
  apply (group_in_gpart s x a _ Hx ND). left. reflexivity.
Qed.

(* [comment removed for export] *)
Record NC (L : layout) (X : list sptr) (EXC : list loc) (s : astate) (m : word -> option byte) (sp0 K : Z) : Prop := {
  nc_repr : repr_x L s (bview SEGS m) EXC ;
  nc_exc : EXC_z X s EXC ;
  nc_zu : forall x, In x X -> exists a, MT s x = Some (MUsed a) ;
  nc_ks : KS s ;
  nc_ctx : ly_ctx L = 0x97c98 ;
  nc_env : nenv m ;
  nc_stk : stk_ok SEGS m (wa sp0) K ;
  nc_K : 1024 <= K ;
  nc_sp1 : 2^20 <= sp0 - K ;
  nc_sp2 : sp0 <= 2^47 ;
  nc_sp3 : sp0 mod 16 = 0 ;
  nc_cells : forall c, In c (image s) -> cplace L (sp0 - K) c ;
  nc_mplace : forall q, In q (keys s) -> 1 <= loc_addr L (LMem q) /\ loc_addr L (LMem q) + 40 <= sp0 - K /\
                (loc_addr L (LMem q) + 40 <= 0x10000 \/ 0x99000 <= loc_addr L (LMem q)) /\ loc_addr L (LMem q) mod 8 = 0 ;
  nc_mdisj : forall q1 q2, In q1 (keys s) -> In q2 (keys s) -> q1 <> q2 ->
                loc_addr L (LMem q1) + 40 <= loc_addr L (LMem q2) \/ loc_addr L (LMem q2) + 40 <= loc_addr L (LMem q1)
}.

Lemma NC_exc_ok : forall L X EXC s m sp0 K, NC L X EXC s m sp0 K -> EXC_ok s EXC.
Proof. intros L X EXC s m sp0 K N. apply (EXC_ok_of_z X); [exact (proj1 (nc_ks _ _ _ _ _ _ _ N)) | exact (nc_exc _ _ _ _ _ _ _ N)]. Qed.

(* [comment removed for export] *)
Definition wide (L : layout) (c : mcell) : Prop := (0x97c98 <= loc_addr L (mc_loc c) < 0x98038) \/ (4 <= mc_w c)%nat.

Lemma wide_range : forall L c c0, cell_range L c0 = cell_range L c -> wide L c -> wide L c0.
Proof.
  intros L c c0 E W. unfold cell_range in E. injection E as E1 E2. apply Nat2Z.inj in E2. unfold wide in *. rewrite E1, E2. exact W.
Qed.

(* [comment removed for export] *)
Definition FRM (L : layout) (s : astate) (sp0 K : Z) (m m' : word -> option byte) : Prop :=
  forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> (sp0 - K <= x < sp0) \/ exists c, In c (image s) /\ wide L c /\ in_rng (cell_range L c) x.

Lemma FRM_refl : forall L s sp0 K m, FRM L s sp0 K m m.
Proof. intros L s sp0 K m x _ H. exfalso. exact (H eq_refl). Qed.

Lemma FRM_trans : forall L s1 s2 sp0 K m1 m2 m3, RS L s2 s1 -> FRM L s1 sp0 K m1 m2 -> FRM L s2 sp0 K m2 m3 -> FRM L s1 sp0 K m1 m3.
Proof.
  intros L s1 s2 sp0 K m1 m2 m3 HRS F1 F2 x Hx H.
  destruct (decide (m3 (wa x) = m2 (wa x))) as [E|E].
  - rewrite E in H. exact (F1 x Hx H).
  - destruct (F2 x Hx E) as [A|(c & Hc & Hw & Hin)]; [left; exact A|]. right.
    destruct (RS_range L s2 s1 c HRS Hc) as (c0 & H0 & Er). exists c0. split; [exact H0|]. split; [exact (wide_range L c c0 Er Hw)|].
    unfold in_rng in *. rewrite Er. exact Hin.
Qed.

(* [comment removed for export] *)
Ltac wide_tac Hctx := unfold wide; cbn [mc_loc mc_w loc_addr] in *; first [ (right; cbn; lia) | (left; rewrite ?Hctx; unfold CTX_usage, CTX_active, CTX_seq, CTX_unmap_seq, CTX_free_meta_head, CTX_secret, CTX_bounces in *; try (clear; lia); lia) ].

(* [comment removed for export] *)
Lemma FRM_static : forall L s sp0 K m m' x, FRM L s sp0 K m m' -> (forall c, In c (image s) -> cplace L (sp0 - K) c) -> 2^20 <= sp0 - K ->
  0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m' (wa x) = m (wa x).
Proof.
  intros L s sp0 K m m' x F HC Hsp Hx Hnc. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|].
  exfalso. destruct (F x ltac:(lia) E) as [A|(c & Hc & _ & Hin)]; [lia|].
  pose proof (HC c Hc) as (P1 & P2 & P3). unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia.
Qed.

Lemma nenv_keep : forall L s sp0 K m m', nenv m -> FRM L s sp0 K m m' -> (forall c, In c (image s) -> cplace L (sp0 - K) c) -> 2^20 <= sp0 - K ->
  nenv m'.
Proof.
  intros L s sp0 K m m' (E1 & E2 & can & Rc & E3) F HC Hsp. split; [|split].
  - rewrite (rdn_frame_n m m' 416600 8) by (try lia; intros x Hx; apply (FRM_static L s sp0 K m m' x F HC Hsp); lia). exact E1.
  - intros sc Hsc. rewrite (rdn_frame_n m m' (98984 + 2 * sc) 2) by (try lia; intros x Hx; apply (FRM_static L s sp0 K m m' x F HC Hsp); lia).
    exact (E2 sc Hsc).
  - exists can. split; [exact Rc|].
    rewrite (rdn_frame_n m m' 621568 8) by (try lia; intros x Hx; apply (FRM_static L s sp0 K m m' x F HC Hsp); lia). exact E3.
Qed.

(* [comment removed for export] *)
Lemma ntf_frame_keep : forall R R' m m' sp0 canary ra s0 s1 s2 s3,
  ntf_frame R m sp0 canary ra s0 s1 s2 s3 -> getr R' 2 = getr R 2 -> getr R' 9 = getr R 9 -> mem_grows m m' ->
  (forall x, (sp0 - 48 <= x < sp0 \/ 0x97c00 <= x < 0x97c08) -> m' (wa x) = m (wa x)) ->
  ntf_frame R' m' sp0 canary ra s0 s1 s2 s3.
Proof.
  intros R R' m m' sp0 canary ra s0 s1 s2 s3 F E2 E9 Hg Hx.
  destruct F as [R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd]. constructor.
  - rewrite E2. exact R2.
  - rewrite E9. exact R9.
  - exact Rsp.
  - exact Asp.
  - exact (stk_ok_grows SEGS m m' (wa sp0) 1024 HSTK Hg).
  - exact Rcan. - exact Rra. - exact Rs0. - exact Rs1. - exact Rs2. - exact Rs3.
  - rewrite (rdn_frame_n m m' (sp0 + -8) 8) by (try lia; intros x H; apply Hx; lia). exact Mra.
  - rewrite (rdn_frame_n m m' (sp0 + -16) 8) by (try lia; intros x H; apply Hx; lia). exact Ms0.
  - rewrite (rdn_frame_n m m' (sp0 + -24) 8) by (try lia; intros x H; apply Hx; lia). exact Ms1.
  - rewrite (rdn_frame_n m m' (sp0 + -32) 8) by (try lia; intros x H; apply Hx; lia). exact Ms2.
  - rewrite (rdn_frame_n m m' (sp0 + -40) 8) by (try lia; intros x H; apply Hx; lia). exact Ms3.
  - rewrite (rdn_frame_n m m' (sp0 + -48) 8) by (try lia; intros x H; apply Hx; lia). exact Mcan.
  - rewrite (rdn_frame_n m m' (0 + 0x97c00) 8) by (try lia; intros x H; apply Hx; lia). exact Mgd.
Qed.

(* [comment removed for export] *)
Lemma FRM_keeps_frame : forall L s sp0 K m m' x, FRM L s sp0 K m m' -> (forall c, In c (image s) -> cplace L (sp0 - K) c) -> 2^20 <= sp0 - K ->
  (forall y, sp0 - 48 <= y < sp0 -> m' (wa y) = m (wa y)) ->
  (sp0 - 48 <= x < sp0 \/ 0x97c00 <= x < 0x97c08) -> m' (wa x) = m (wa x).
Proof.
  intros L s sp0 K m m' x F HC Hsp Hst [A|A]; [exact (Hst x A)|]. apply (FRM_static L s sp0 K m m' x F HC Hsp); lia.
Qed.

(* [comment removed for export] *)
Lemma NC_next : forall L X EXC s s' m m' sp0 K,
  NC L X EXC s m sp0 K -> repr_x L s' (bview SEGS m') EXC -> RS L s' s -> KS s' ->
  (forall x, In x X -> MT s' x = MT s x) -> mem_grows m m' -> FRM L s sp0 K m m' -> keys s' = keys s -> NC L X EXC s' m' sp0 K.
Proof.
  intros L X EXC s s' m m' sp0 K N HR' HRS HK' HZ Hg F Hkeys. destruct N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  constructor.
  - exact HR'.
  - intros l Hl. destruct (HEX l Hl) as (x & a & Hx & Ma & El). exists x, a. split; [exact Hx|]. split; [rewrite HZ by exact Hx; exact Ma | exact El].
  - intros x Hx. rewrite (HZ x Hx). exact (HZU x Hx).
  - exact HK'.
  - exact Hctx.
  - exact (nenv_keep L s sp0 K m m' Henv F HC Hsp1).
  - exact (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg).
  - exact HK1. - exact Hsp1. - exact Hsp2. - exact Hsp3.
  - exact (cplace_RS L (sp0 - K) s' s HRS HC).
  - rewrite Hkeys. exact HMP.
  - rewrite Hkeys. exact HMD.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma REST_vs_gcells : forall L s g a c c', KS s -> MT s g = Some (MUsed a) -> PW L s -> In c (REST s g) -> In c' (group_cells g a) ->
  ranges_disjoint (cell_range L c) (cell_range L c').
Proof.
  intros L s g a c c' HK Hg HPW Hc Hc'. assert (Hk : In g (keys s)) by (eapply MT_keys; exact Hg).
  pose proof (image_decomp_key s g HK Hk) as P. rewrite Hg in P.
  pose proof (PW_perm L _ _ P HPW) as HP.
  apply (pw_cross L (REST s g) (meta_slot_cells g (Some (MUsed a)) ++ group_cells g a) c c' HP Hc). apply in_app_iff. right. exact Hc'.
Qed.

Lemma front_vs_gpart_loc : forall L s c c', PW L s -> In c (ctx_cells s ++ areas_cells s (st_areas s)) -> In c' (gpart s) -> mc_loc c <> mc_loc c'.
Proof.
  intros L s c c' HPW Hc Hc'. unfold PW in HPW. rewrite image_parts, app_assoc in HPW.
  pose proof (pw_cross L _ _ c c' HPW Hc Hc') as D.
  assert (W1 : (1 <= mc_w c)%nat) by (apply (image_cell_width s c); rewrite image_parts, app_assoc; apply in_app_iff; left; exact Hc).
  assert (W2 : (1 <= mc_w c')%nat) by (apply (image_cell_width s c'); rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact Hc').
  exact (loc_neq_of_disj L c c' D W1 W2).
Qed.

(* [comment removed for export] *)
Lemma NC_next' : forall L X EXC X' EXC' s s' m m' sp0 K,
  NC L X EXC s m sp0 K -> repr_x L s' (bview SEGS m') EXC' -> EXC_z X' s' EXC' -> (forall x, In x X' -> exists a, MT s' x = Some (MUsed a)) ->
  RS L s' s -> KS s' -> mem_grows m m' -> FRM L s sp0 K m m' -> keys s' = keys s -> NC L X' EXC' s' m' sp0 K.
Proof.
  intros L X EXC X' EXC' s s' m m' sp0 K N HR' HEX' HZU' HRS HK' Hg F Hkeys. destruct N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  constructor; try assumption.
  - exact (nenv_keep L s sp0 K m m' Henv F HC Hsp1).
  - exact (stk_ok_grows SEGS m m' (wa sp0) K HSTK Hg).
  - exact (cplace_RS L (sp0 - K) s' s HRS HC).
  - rewrite Hkeys. exact HMP.
  - rewrite Hkeys. exact HMD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hdr_not_exc : forall L X EXC s pg amp, EXC_z X s EXC -> PW L s -> List.NoDup (keys s) ->
  MT s pg = Some (MUsed amp) -> ~ In pg X -> ~ In (LMem (am_mem amp)) EXC.
Proof.
  intros L X EXC s pg amp HEX HPW ND Mp NXp Hin. destruct (HEX _ Hin) as (x & ax & Hx & Mx & El).
  assert (Hne : pg <> x) by (intros ->; exact (NXp Hx)).
  set (c1 := MCell (LMem (am_mem amp)) 8 (VP pg)). set (c2 := MCell (LMem (am_mem ax)) 8 (VP x)).
  assert (H1 : In c1 (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; apply (group_in_gpart s pg amp c1 Mp ND); left; reflexivity).
  assert (H2 : In c2 (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; apply (group_in_gpart s x ax c2 Mx ND); left; reflexivity).
  assert (Hc : c1 <> c2) by (unfold c1, c2; intros E; injection E as _ E2; exact (Hne E2)).
  pose proof (pairwise_map_In _ (cell_range L) _ _ _ HPW H1 H2 Hc) as [D|D];
    unfold ranges_disjoint, cell_range, c1, c2 in D; cbn [fst snd mc_loc mc_w Z.of_nat Pos.of_succ_nat] in D; rewrite <- El in D; lia.
Qed.

Lemma rx_group_rd : forall L s m EXC q a c, repr_x L s (bview SEGS m) EXC -> EXC_ok s EXC -> List.NoDup (keys s) ->
  MT s q = Some (MUsed a) -> In c (group_cells q a) -> ~ In (mc_loc c) EXC -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn SEGS m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof.
  intros L s m EXC q a c HR HEO ND Mq Hc Hn Hv Hw.
  assert (Hi : In c (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact (group_in_gpart s q a c Mq ND Hc)).
  exact (repr_x_rdn SEGS L s m EXC c HR Hi Hn Hv Hw).
Qed.

Lemma gcell_not_exc : forall L s EXC q a c, PW L s -> EXC_ok s EXC -> List.NoDup (keys s) -> MT s q = Some (MUsed a) ->
  In c (group_cells q a) -> mc_w c <> 8%nat -> ~ In (mc_loc c) EXC.
Proof. intros L s EXC q a c HPW HEO ND Mq Hc Hw. apply (not_exc_group L s EXC c HPW HEO); [exact (group_in_gpart s q a c Mq ND Hc) | exact Hw]. Qed.

(* [comment removed for export] *)
Lemma not_exc_w : forall L s EXC c, PW L s -> EXC_ok s EXC -> In c (image s) -> mc_w c <> 8%nat -> ~ In (mc_loc c) EXC.
Proof.
  intros L s EXC c HPW HEO Hc Hw. rewrite image_parts, app_assoc in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - exact (not_exc_front L s EXC c HPW HEO Hc).
  - exact (not_exc_group L s EXC c HPW HEO Hc Hw).
Qed.

(* [comment removed for export] *)
Lemma msc_lmem : forall q x c, In c (meta_slot_cells q x) -> exists p, mc_loc c = LMem p.
Proof. intros q x c H. destruct x as [[pr nx| |a]|]; cbn [meta_slot_cells In] in H; repeat (destruct H as [<-|H]; [eexists; reflexivity|]); destruct H. Qed.

Lemma areas_lmem : forall s l c, In c (areas_cells s l) -> exists p, mc_loc c = LMem p.
Proof.
  intros s l. induction l as [|a t IH]; intros c H; [destruct H|]. cbn [areas_cells] in H. apply in_app_iff in H as [H|H]; [|exact (IH c H)].
  unfold area_cells in H. apply in_app_iff in H as [H|H].
  - cbn [In] in H. repeat (destruct H as [<-|H]; [eexists; reflexivity|]). destruct H.
  - apply in_flat_map in H as (k & _ & H). exact (msc_lmem _ _ c H).
Qed.

Lemma gpart_lmem : forall s c, In c (gpart s) -> exists p, mc_loc c = LMem p.
Proof.
  intros s c H. unfold gpart in H. apply in_flat_map in H as ([q aq] & _ & H). cbn [fst snd] in H. unfold group_cells in H.
  apply in_app_iff in H as [H|H].
  - cbn [In] in H. destruct H as [<-|[<-|[]]]; [eexists; reflexivity | destruct (am_maplen aq =? 0); eexists; reflexivity].
  - apply in_flat_map in H as (j & _ & H). unfold slot_cells in H. apply in_app_iff in H as [H|H]; [destruct H as [<-|[]]; eexists; reflexivity|].
    apply in_app_iff in H as [H|H].
    + destruct (ss_hdr (nth_slot aq j)) as [[h3 h16]|]; [cbn [In] in H; destruct H as [<-|[<-|[]]]; eexists; reflexivity | destruct H].
    + destruct (ss_fr (nth_slot aq j)) as [fj|]; [|destruct H]. destruct (fr_off fj =? 0); [destruct H|].
      cbn [In] in H. destruct H as [<-|[<-|[<-|[]]]]; eexists; reflexivity.
Qed.

Lemma lctx_in_ctx : forall s c o, In c (image s) -> mc_loc c = LCtx o -> In c (ctx_cells s).
Proof.
  intros s c o H E. rewrite image_parts in H. apply in_app_iff in H as [H|H]; [exact H|]. exfalso.
  apply in_app_iff in H as [H|H]; [destruct (areas_lmem s _ c H) as (p & Ep) | destruct (gpart_lmem s c H) as (p & Ep)]; rewrite E in Ep; discriminate.
Qed.

Lemma cells_disj : forall L s c1 c2, PW L s -> In c1 (image s) -> In c2 (image s) -> c1 <> c2 ->
  ranges_disjoint (cell_range L c1) (cell_range L c2).
Proof.
  intros L s c1 c2 HPW H1 H2 Hne. destruct (pairwise_map_In _ (cell_range L) _ _ _ HPW H1 H2 Hne) as [D|D]; [exact D|].
  apply ranges_disjoint_sym'. exact D.
Qed.
