(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits AxMalloc MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        AXG_ntfm AXG_ntfg AXG_nQ AXG_tam AXG_as1 AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma as_frame_move : forall R R' m m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  (forall k, In k [2;8;18;20;21;22;23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  (forall x, sp0 - 96 <= x < sp0 -> m' (wa x) = m (wa x)) -> (forall x, 613952 <= x < 613960 -> m' (wa x) = m (wa x)) ->
  as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9.
Proof.
  intros R R' m m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F KK H1 H2.
  apply (as_frame_mem R' m m'); [|exact H1 | exact H2].
  destruct F. constructor; try assumption.
  all: match goal with |- getr ?Rx ?r = _ =>
         first [ (rewrite (kp_lit Rx R _ KK 2%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
               | (rewrite (kp_lit Rx R _ KK 8%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
               | (rewrite (kp_lit Rx R _ KK 18%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
               | (rewrite (kp_lit Rx R _ KK 20%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
               | (rewrite (kp_lit Rx R _ KK 21%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
               | (rewrite (kp_lit Rx R _ KK 22%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
               | (rewrite (kp_lit Rx R _ KK 23%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption) ] end.
Qed.

Ltac litr2 H := match type of H with getr _ ?r = _ => match goal with |- getr _ ?r0 = _ => replace r0 with r by (apply bv_eq; reflexivity) end end; rewrite H.

(* [comment removed for export] *)
Lemma frame_regs_upd : forall R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R' (Z_to_bv 5 (Z.of_nat 2)) = getr R (Z_to_bv 5 (Z.of_nat 2)) ->
  getr R' (Z_to_bv 5 (Z.of_nat 18)) = getr R (Z_to_bv 5 (Z.of_nat 18)) ->
  getr R' 8 = wa sc -> getr R' 20 = wa 613952 -> getr R' 21 = wa (8 * sc + 614184) -> getr R' 22 = wa 614096 ->
  getr R' 23 = wa (8 * sc + 614096) ->
  forall k, In k [2;8;18;20;21;22;23]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k)).
Proof.
  intros R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F K2 K18 Q8 Q20 Q21 Q22 Q23 k Hk.
  destruct F as [R2 R8 R18 R20 R21 R22 R23]. cbn [In] in Hk.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
  - exact K2.
  - litr2 Q8. symmetry. exact R8.
  - exact K18.
  - litr2 Q20. symmetry. exact R20.
  - litr2 Q21. symmetry. exact R21.
  - litr2 Q22. symmetry. exact R22.
  - litr2 Q23. symmetry. exact R23.
Qed.

(* [comment removed for export] *)
Definition act_mem (m : word -> option byte) (sc A : Z) : word -> option byte := wbytes m (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa A)).

Lemma nc_act : forall L s m sp0 K sc nx, NC L [] [] s m sp0 K -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  let m' := act_mem m sc (loc_addr L (LMem nx)) in
  NC L [] [] (s_head s sc (Some nx)) m' sp0 K /\ RS L (s_head s sc (Some nx)) s /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
  keys (s_head s sc (Some nx)) = keys s /\
  (forall x, 0 <= x < 2^64 -> ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> m' (wa x) = m (wa x)).
Proof.
  intros L s m sp0 K sc nx N Rsc Hlen m'.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (Hlk : (k < length (st_active s))%nat) by (rewrite Hlen; lia).
  set (s' := s_head s sc (Some nx)).
  assert (HRS : RS L s' s) by (apply RS_ctx_only; reflexivity).
  assert (HKs' : KS s') by (apply KS_set_active; exact HK).
  assert (Ks' : keys s' = keys s) by reflexivity.
  set (cn := act_cell k (Some nx)).
  assert (Ecn : loc_addr L (mc_loc cn) = 8 * sc + 614184) by (unfold cn, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (Hm' : m' = wbytes m (wa (8 * sc + 614184)) (word_to_le_bytes (mc_w cn) (wa (sval_num L (mc_val cn))))) by reflexivity.
  assert (HR' : repr_x L s' (bview SEGS m') []).
  { rewrite Hm'. apply (repr_x_wcell L s s' m [] cn (8 * sc + 614184) HR eq_refl eq_refl HRS).
    - intros c Hc. exact (cov_set_active s k (Some nx) c Hlk Hc).
    - apply act_cell_in_image; [lia | exact Hlk].
    - intros z E. discriminate.
    - cbn. lia.
    - exact Ecn.
    - lia.
    - cbn [cn act_cell mc_w Z.of_nat Pos.of_succ_nat]. lia. }
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> m' (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m', act_mem. rewrite MngWb.wbytes_out by side. reflexivity. }
  assert (Hgr : mem_grows m m') by (unfold m', act_mem; apply wbytes_grows).
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. exists (act_cell k (nth k (st_active s) None)). split; [exact (act_in_ctx_img s k ltac:(lia))|]. split; [wide_tac Hctx|].
    unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active.
    destruct (decide (8 * sc + 614184 <= x < 8 * sc + 614192)) as [A|A]; [lia|]. exfalso. apply Hne. apply MOUT; assumption. }
  split; [exact (NC_next L [] [] s s' m m' sp0 K N HR' HRS HKs' ltac:(intros x []) Hgr FR Ks')|].
  split; [exact HRS|]. split; [exact Hgr|]. split; [exact FR|]. split; [exact Ks'|]. exact MOUT.
Qed.

Section AS2.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_ta0 : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa 0 -> active_hd s sc = None ->
  exists R', msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x524d0) m rom) /\
    try_avail sc s = IRet (0, s) /\ as_frame R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 N F R12 Hhd.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta0z.ta0_pre R m sc) by (destruct F; constructor; assumption).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta0z.ta0_pta0 R m rom sc P ltac:(constructor)) as (R' & Hms & _ & Kk).
  exists R'. split; [exact Hms|]. split; [exact (ta_none s sc Hhd)|]. split.
  - apply (as_frame_move R R' m m); [exact F| |intros; reflexivity|intros; reflexivity].
    intros k Hk. apply Kk. clear - Hk. cbn [In] in *. tauto.
  - intros k Hk. apply Kk. clear - Hk. cbn [In] in *. tauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_tad1 : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (loc_addr L (LMem g)) -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am = 0 -> am_next am = Some g ->
  exists R' m', msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x524d0) m' rom) /\
    try_avail sc s = IRet (0, s_dq1 s g sc am) /\ NC L [] [] (s_dq1 s g sc am) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_dq1 s g sc am) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am N F R12 Rsc Hlen Hhd Mg Hav Hfr Hnx.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tad1z.tad1_pre R m sc G).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3 Rsc; lia).
    all: first [ (pose proof (rx_avail L s m [] HR HEO HK g am Mg) as E; rewrite Hav in E; exact E)
               | (pose proof (rx_freed L s m [] HR HEO HK g am Mg) as E; rewrite Hfr in E; exact E)
               | (pose proof (rx_next L s m [] HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m [] HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; pose proof (rx_act_wr L s m [] HR HEO Hctx k ltac:(lia) d n Hd Hn) as E; rewrite Ek in E;
                  replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring; exact E)
               | (clear - Hsp1 HK1 Rsc; lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tad1z.tad1_ptad1 R m rom sc G P ltac:(constructor)) as (R' & Hms & Q8 & Q10 & Q11 & Q12 & Q20 & Q21 & Q22 & Q23 & Qk).
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tad1z.tad1_mem_ptad1 m R sc G) with (dq1m m G sc) in Hms.
  set (m' := dq1m m G sc).
  set (s' := s_dq1 s g sc am).
  set (S1 := set_active (lupd (st_active s) k None) s).
  assert (Es' : s' = set_meta S1 g (MUsed (unl am))) by reflexivity.
  assert (HKS1 : KS S1) by (apply KS_set_active; exact HK).
  assert (M1g : MT S1 g = Some (MUsed am)) by exact Mg.
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS1 | exact Kg]).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; apply MT_set_same).
  assert (Ks' : keys s' = keys s) by (rewrite Es', keys_set_meta by exact Kg; reflexivity).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S1); [|apply RS_ctx_only; reflexivity].
    apply (RS_set_used L S1 g am (unl am) HKS1 M1g). unfold unl. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (Hlk : (k < length (st_active s))%nat) by (rewrite Hlen; lia).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  set (CA := act_cell k None).
  assert (ECA : loc_addr L (mc_loc CA) = 8 * sc + 614184) by (unfold CA, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CP; CN; CA]).
  { constructor; [|constructor; [|constructor; [|constructor]]]; apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CP CN CA act_cell] in *; rewrite ?loc_padd, ?ECA; unfold META_prev, META_next; fold G.
    all: cbn [loc_addr] in *; rewrite ?Hctx in *; unfold CTX_active in *; rewrite ?Ek in *.
    all: try (clear - HGr Rsc; lia).
    all: intros n Hn; unfold m'.
    - apply dq1_mem_G0; assumption.
    - apply dq1_mem_G8; assumption.
    - replace (614104 + (80 + 8 * sc) + Z.of_nat n) with (8 * sc + 614184 + Z.of_nat n) by ring. apply dq1_mem_ACT; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply dq1_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (G <= a < G + 16) \/ (8 * sc + 614184 <= a < 8 * sc + 614192)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (8 * sc + 614184 <= a < 8 * sc + 614192)) as [A2|A2]; [right; exact A2|].
    exfalso. apply Ha. unfold m'. apply dq1_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') [] [CP; CN; CA] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. unfold unl in Hc. destruct (cov_setm_links S1 g am None None c HKS1 M1g Hc) as [Hc1|[E|E]].
      + destruct (cov_set_active s k None c Hlk Hc1) as [Hc2|E]; [left; exact Hc2 | right; rewrite E; right; right; left; reflexivity].
      + right. rewrite E. left. reflexivity.
      + right. rewrite E. right. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + assert (Ea : nth k (st_active s') None = None) by (rewrite Es'; cbn [st_active set_meta set_metas]; unfold S1; cbn [st_active set_active]; apply nth_lupd_same; exact Hlk).
        pose proof (act_in_ctx_img s' k ltac:(lia)) as E. rewrite Ea in E. exact E.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|A].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CA. split; [right; right; left; reflexivity|]. unfold in_rng, cell_range. rewrite ECA. unfold CA, act_cell. cbn [mc_w fst snd Z.of_nat Pos.of_succ_nat]. clear - A; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|A].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
    - exists (act_cell k (nth k (st_active s) None)). split; [exact (act_in_ctx_img s k ltac:(lia))|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active. clear - A; lia. }
  exists R', m'. split; [exact Hms|]. split; [exact (ta_dq1 s sc g am Hhd Mg Hav Hfr Hnx Hlen Rsc)|].
  split; [exact (NC_next L [] [] s s' m m' sp0 K N REPR HRS HKs' ltac:(intros x []) Hgrow FR Ks')|].
  split.
  { apply (as_frame_move R R' m m'); [exact F | | |].
    - exact (frame_regs_upd R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F ltac:(apply Qk; cbn; tauto) ltac:(apply Qk; cbn; tauto) Q8 Q20 Q21 Q22 Q23).
    - intros x Hx. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
      destruct (CHG x ltac:(clear - Hx Hsp1 Hsp2 HK1; lia) E) as [A|A]; clear - A Hx G2 HK1 Rsc Hsp1 Hsp2 G1 G3; lia.
    - intros x Hx. destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
      destruct (CHG x ltac:(clear - Hx; lia) E) as [A|A]; clear - A Hx G1 G3 Rsc; lia. }
  split; [exact HRS|]. split; [exact Hgrow|]. split; [exact FR|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_tar : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am nx,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (loc_addr L (LMem g)) -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am <> 0 -> 0 <= am_freed am <= 2^32-1 ->
  am_next am = Some nx -> In nx (keys s) ->
  exists R' m', msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x523b8) m' rom) /\
    try_avail sc s = ta_m1 sc nx (s_head s sc (Some nx)) /\ NC L [] [] (s_head s sc (Some nx)) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_head s sc (Some nx)) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\ getr R' 10 = wa (loc_addr L (LMem nx)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am nx N F R12 Rsc Hlen Hhd Mg Hav Hfr Rfr Hnx Knx.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *. set (NX := loc_addr L (LMem nx)).
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  destruct (HMP nx Knx) as (X1 & X2 & X3 & X4). fold NX in X1, X2, X3, X4.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  pose proof (rx_freed L s m [] HR HEO HK g am Mg) as MFR.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tarz.tar_pre R m sc G (am_freed am) NX).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - X1 X2 Hsp2 HK1; lia); try (clear - Rfr Hfr; lia).
    all: first [ (pose proof (rx_avail L s m [] HR HEO HK g am Mg) as E; rewrite Hav in E; exact E)
               | (pose proof (rx_next L s m [] HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (intros d n Hd Hn; pose proof (rx_act_wr L s m [] HR HEO Hctx k ltac:(lia) d n Hd Hn) as E; rewrite Ek in E;
                  replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring; exact E)
               | (clear - G1 G3 Rsc; lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tarz.tar_ptar R m rom sc G (am_freed am) NX P) as (R' & Hms & Q8 & Q10 & Q12 & Q20 & Q21 & Q22 & Q23 & Qk).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tar.RES_ptar fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tarz.VALS_tar sc G (am_freed am) NX) 34 (am_freed am) eq_refl eq_refl) by lia. apply ext4_ne0. lia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tarz.tar_mem_ptar m R sc G (am_freed am) NX) with (act_mem m sc NX) in Hms.
  destruct (nc_act L s m sp0 K sc nx N Rsc Hlen) as (N' & HRS & Hgr & FR & Ks' & MOUT).
  exists R', (act_mem m sc NX). split; [exact Hms|]. split; [exact (ta_rot s sc g am nx Hhd Mg Hav Hfr Hnx)|].
  split; [exact N'|]. split.
  { apply (as_frame_move R R' m (act_mem m sc NX)); [exact F | | |].
    - exact (frame_regs_upd R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F ltac:(apply Qk; cbn; tauto) ltac:(apply Qk; cbn; tauto) Q8 Q20 Q21 Q22 Q23).
    - intros x Hx. apply MOUT; [clear - Hx Hsp1 Hsp2 HK1; lia | clear - Hx Hsp1 HK1 Rsc; lia].
    - intros x Hx. apply MOUT; [clear - Hx; lia | clear - Hx Rsc; lia]. }
  split; [exact HRS|]. split; [exact Hgr|]. split; [exact FR|]. split; [exact Q10|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

End AS2.
