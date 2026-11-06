(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngNtfM MngNtfS MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_am1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt10z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt100z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition anext_cell (a : sptr) (o : option sptr) : mcell := MCell (LMem (padd a 8)) 8 (optr o).

Lemma area_cells_next_cov : forall s a n n' c, In c (area_cells s a n') -> In c (area_cells s a n) \/ c = anext_cell a n'.
Proof.
  intros s a n n' c H. unfold area_cells in H |- *. apply in_app_iff in H as [H|H].
  - cbn [In] in H. destruct H as [<-|[<-|[<-|[]]]].
    + left. apply in_app_iff. left. cbn. tauto.
    + right. reflexivity.
    + left. apply in_app_iff. left. cbn. tauto.
  - left. apply in_app_iff. right. exact H.
Qed.

Lemma areas_cells_snoc_cov : forall s l p c, In c (areas_cells s (l ++ [p])) ->
  In c (areas_cells s l) \/ In c (area_cells s p None) \/ (exists a, l <> [] /\ a = last l (SP 0%nat 0) /\ c = anext_cell a (Some p)).
Proof.
  intros s l p. induction l as [|a t IH]; intros c H.
  - cbn in H. rewrite app_nil_r in H. right. left. exact H.
  - cbn [app areas_cells] in H. apply in_app_iff in H as [H|H].
    + destruct t as [|b t'].
      * cbn [hd_error app] in H. destruct (area_cells_next_cov s a None (Some p) c H) as [H2|H2].
        -- left. cbn [areas_cells hd_error]. apply in_app_iff. left. exact H2.
        -- right. right. exists a. split; [discriminate|]. split; [reflexivity | exact H2].
      * left. cbn [areas_cells app hd_error]. apply in_app_iff. left. exact H.
    + destruct (IH c H) as [H2|[H2|(a' & Hne & Ea & Ec)]].
      * left. cbn [areas_cells]. apply in_app_iff. right. exact H2.
      * right. left. exact H2.
      * right. right. exists a'. split; [discriminate|]. split; [|exact Ec]. rewrite Ea. destruct t as [|b t']; [exfalso; exact (Hne eq_refl)|].
        reflexivity.
Qed.

Lemma areas_cells_snoc_rev : forall s l p c, In c (areas_cells s l) ->
  In c (areas_cells s (l ++ [p])) \/ (exists a, l <> [] /\ a = last l (SP 0%nat 0) /\ c = anext_cell a None).
Proof.
  intros s l p. induction l as [|a t IH]; intros c H; [destruct H|].
  cbn [areas_cells] in H. apply in_app_iff in H as [H|H].
  - destruct t as [|b t'].
    + cbn [hd_error] in H. destruct (area_cells_next_cov s a (Some p) None c H) as [H2|H2].
      * left. cbn [app areas_cells hd_error]. apply in_app_iff. left. exact H2.
      * right. exists a. split; [discriminate|]. split; [reflexivity | exact H2].
    + left. cbn [app areas_cells hd_error]. apply in_app_iff. left. exact H.
  - destruct (IH c H) as [H2|(a' & Hne & Ea & Ec)].
    + left. cbn [app areas_cells]. apply in_app_iff. right. exact H2.
    + right. exists a'. split; [discriminate|]. split; [|exact Ec]. rewrite Ea. destruct t as [|b t']; [exfalso; exact (Hne eq_refl)|]. reflexivity.
Qed.

Lemma In_areas_cells_snoc_new : forall s l p c, In c (area_cells s p None) -> In c (areas_cells s (l ++ [p])).
Proof.
  intros s l p c H. induction l as [|a t IH]; cbn [app areas_cells].
  - cbn [hd_error]. rewrite app_nil_r. exact H.
  - apply in_app_iff. right. exact IH.
Qed.

Lemma In_areas_cells_snoc_next : forall s l p, l <> [] -> In (anext_cell (last l (SP 0%nat 0)) (Some p)) (areas_cells s (l ++ [p])).
Proof.
  intros s l p Hne. induction l as [|a t IH]; [exfalso; exact (Hne eq_refl)|].
  destruct t as [|b t'].
  - cbn [app areas_cells hd_error last]. apply in_app_iff. left. unfold area_cells. apply in_app_iff. left. cbn. tauto.
  - cbn [app areas_cells]. apply in_app_iff. right. replace (last (a :: b :: t') (SP 0%nat 0)) with (last (b :: t') (SP 0%nat 0)) by reflexivity.
    apply IH. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZP (m : word -> option byte) (a : Z) : Prop := forall x, a <= x < a + PGSZ -> m (wa x) = Some (Z_to_bv 8 0).

Lemma nth_le_0 : forall n k, nth k (Z_to_le_bytes n 0) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  induction n as [|n IH]; intros k; [destruct k; reflexivity|]. cbn [Z_to_le_bytes]. change (Z.shiftr 0 8) with 0.
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH.
Qed.

Lemma zero_cell_holds : forall L m c a, ZP m a -> 0 <= a -> a + PGSZ <= 2^64 ->
  a <= loc_addr L (mc_loc c) -> loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= a + PGSZ -> (mc_w c <= 8)%nat ->
  (forall z, mc_val c <> VLo5 z) -> sval_num L (mc_val c) = 0 -> cell_holds L (bview SEGS m) c.
Proof.
  intros L m c a HZ Ha1 Ha2 H1 H2 Hw Hv Hz. apply holds_of_mem; [exact Hv | exact Hw | lia | lia|].
  intros k Hk. rewrite HZ by lia. rewrite Hz. change (wa 0) with (Z_to_bv 64 0).
  f_equal. unfold word_to_le_bytes. rewrite u_wa_small by lia. symmetry. apply nth_le_0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma new_page_no_key : forall X R U s p, Inv X R U s -> ~ In p (st_areas s) -> poff p mod PGSZ = 0 ->
  forall q, In q (keys s) -> forall k, 0 <= k < 101 -> q <> padd p (AREA_HDR + META_SIZE * k).
Proof.
  intros X R U s p HI Hnp Hal q Hq k Hk E. pose proof (inv_keys HI) as (_ & KP & _). destruct (KP q Hq) as (a & j & Ha & Hj & Eq).
  pose proof (handed_range X R U s a HI) as Hh.
  pose proof (inv_areas HI) as (_ & A2 & _). destruct (A2 a Ha) as (r & o & rg & -> & Ho & _).
  rewrite Eq in E. destruct p as [rp op]. cbn [padd prid poff] in *. injection E as E1 E2. subst rp.
  assert (o = op).
  { unfold PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *. apply Z.mod_divide in Ho; [|lia]. apply Z.mod_divide in Hal; [|lia].
    destruct Ho as (k1 & ->). destruct Hal as (k2 & ->). assert (k1 = k2) by nia. subst. reflexivity. }
  subst op. exact (Hnp Ha).
Qed.

Lemma open_take_avail : forall p s, st_avail_meta (open_st p s) = padd p AREA_HDR.
Proof. reflexivity. Qed.

Lemma mlookup_open_take : forall p s q, mlookup (st_metas (s_take (open_st p s))) q =
  if sptr_eqb q (padd p AREA_HDR) then Some MRaw else mlookup (st_metas s) q.
Proof.
  intros p s q. unfold s_take, upd_meta. cbn [st_metas set_metas set_avail_meta set_avail_meta_count open_st set_areas set_area_head set_area_tail
    set_avail_meta_areas set_avail_meta_area_count]. rewrite open_take_avail.
  destruct (sptr_eqb q (padd p AREA_HDR)) eqn:E.
  - apply sptr_eqb_eq in E. subst q. apply mlookup_mupdate_same.
  - apply mlookup_mupdate_other. intros ->. rewrite sptr_eqb_refl in E. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM3.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition ac_cell (v : Z) : mcell := MCell (LCtx CTX_avail_meta_area_count) 8 (VZ v).
Definition head_cell (o : option sptr) : mcell := MCell (LCtx CTX_meta_area_head) 8 (optr o).
Definition tail_cell (o : option sptr) : mcell := MCell (LCtx CTX_meta_area_tail) 8 (optr o).
Definition ama_cell (v : sptr) : mcell := MCell (LCtx CTX_avail_meta_areas) 8 (VP v).

Definition s_opn (p : sptr) (s : astate) : astate := s_take (open_st p s).

#[using="Type"] Lemma open_cov_ctx : forall p s c, In c (ctx_cells (s_opn p s)) ->
  In c (ctx_cells s) \/ c = am_cell (padd (padd p AREA_HDR) META_SIZE) \/ c = amc_cell (METAS_PER_AREA - 1) \/
  c = ac_cell (st_avail_meta_area_count s - 1) \/ c = head_cell (match st_area_head s with None => Some p | h => h end) \/
  c = tail_cell (Some p) \/ c = ama_cell (padd p 4096).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p s c Hc. unfold s_opn, s_take, upd_meta, open_st in Hc. unfold ctx_cells in Hc.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_metas set_avail_meta set_avail_meta_count set_areas set_area_head set_area_tail set_avail_meta_areas
      set_avail_meta_area_count] in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  destruct (st_areas s ++ [p]) as [|a0 t0] eqn:Ea; [exfalso; destruct (st_areas s); discriminate|].
  cbn [In andb] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; solve [memb])
                                        | (right; left; reflexivity) | (right; right; left; reflexivity) | (right; right; right; left; reflexivity)
                                        | (right; right; right; right; left; reflexivity) | (right; right; right; right; right; left; reflexivity)
                                        | (right; right; right; right; right; right; reflexivity) ] |]).
  destruct Hc.
Qed.

#[using="Type"] Lemma open_rev_ctx : forall p s c, In c (ctx_cells s) ->
  In c (ctx_cells (s_opn p s)) \/ ((mc_loc c = LCtx CTX_avail_meta \/ mc_loc c = LCtx CTX_avail_meta_count \/ mc_loc c = LCtx CTX_avail_meta_area_count \/
     mc_loc c = LCtx CTX_meta_area_head \/ mc_loc c = LCtx CTX_meta_area_tail \/ mc_loc c = LCtx CTX_avail_meta_areas) /\ mc_w c = 8%nat).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p s c Hc. unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells, s_opn, s_take, upd_meta, open_st; apply in_app_iff; left;
       cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
            st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_metas set_avail_meta
            set_avail_meta_count set_areas set_area_head set_area_tail set_avail_meta_areas set_avail_meta_area_count In]; solve [memb])
     | (right; split; [cbn [mc_loc]; first [ (left; reflexivity) | (right; left; reflexivity) | (right; right; left; reflexivity)
                                        | (right; right; right; left; reflexivity) | (right; right; right; right; left; reflexivity)
                                        | (right; right; right; right; right; reflexivity) ] | reflexivity]) ] |]).
  destruct Hc.
Qed.

#[using="Type"] Lemma open_areas_ext : forall p s l, ~ In (padd p AREA_HDR) (keys s) -> areas_cells (s_opn p s) l = areas_cells s l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p s l Hk. apply areas_cells_ext. intros q. unfold s_opn. rewrite mlookup_open_take. destruct (sptr_eqb q (padd p AREA_HDR)) eqn:E; [|reflexivity].
  apply sptr_eqb_eq in E. subst q. destruct (mlookup (st_metas s) (padd p AREA_HDR)) as [x|] eqn:E2; [|reflexivity].
  exfalso. apply Hk. unfold keys. exact (mlookup_In_keys _ _ _ E2).
Qed.

#[using="Type"] Lemma open_used : forall p s, ~ In (padd p AREA_HDR) (keys s) -> used_metas (s_opn p s) = used_metas s.
Proof. LiaFast.lf_pins LiaFast.u0. intros p s Hk. unfold s_opn, s_take. rewrite open_take_avail. rewrite used_metas_raw_new; [reflexivity | exact Hk]. Qed.

#[using="Type"] Lemma open_cov : forall p s c, ~ In (padd p AREA_HDR) (keys s) -> In c (image (s_opn p s)) ->
  In c (image s) \/ In c (ctx_cells (s_opn p s)) /\ ~ In c (ctx_cells s) \/ In c (area_cells (s_opn p s) p None) \/
  (exists a, st_areas s <> [] /\ a = last (st_areas s) (SP 0%nat 0) /\ c = anext_cell a (Some p)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p s c Hk Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
  - destruct (in_dec mcell_eq_dec c (ctx_cells s)) as [H|H]; [left; apply ctx_in_image; exact H | right; left; split; assumption].
  - replace (st_areas (s_opn p s)) with (st_areas s ++ [p]) in Hc by reflexivity.
    destruct (areas_cells_snoc_cov (s_opn p s) (st_areas s) p c Hc) as [H|[H|H]].
    + left. unfold image. apply in_app_iff. right. apply in_app_iff. left. rewrite open_areas_ext in H by exact Hk. exact H.
    + right. right. left. exact H.
    + right. right. right. exact H.
  - left. unfold image. apply in_app_iff. right. apply in_app_iff. right. rewrite open_used in Hc by exact Hk. exact Hc.
Qed.

#[using="Type"] Lemma open_rev : forall p s c, ~ In (padd p AREA_HDR) (keys s) -> In c (image s) ->
  In c (image (s_opn p s)) \/ In c (ctx_cells s) /\ ~ In c (ctx_cells (s_opn p s)) \/
  (exists a, st_areas s <> [] /\ a = last (st_areas s) (SP 0%nat 0) /\ c = anext_cell a None).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p s c Hk Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
  - destruct (in_dec mcell_eq_dec c (ctx_cells (s_opn p s))) as [H|H]; [left; apply ctx_in_image; exact H | right; left; split; assumption].
  - rewrite <- (open_areas_ext p s _ Hk) in Hc. destruct (areas_cells_snoc_rev (s_opn p s) (st_areas s) p c Hc) as [H|H].
    + left. unfold image. apply in_app_iff. right. apply in_app_iff. left. exact H.
    + right. right. exact H.
  - left. unfold image. apply in_app_iff. right. apply in_app_iff. right. rewrite open_used by exact Hk. exact Hc.
Qed.
End AM3.
