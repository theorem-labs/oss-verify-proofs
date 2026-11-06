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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        AXF_eez AXG_ntfm AXG_ntfg.
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

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.
Ltac wgrow := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Ltac memb := first [ AxSymRun3.memb_refl | repeat first [ (left; reflexivity) | right ] ].      (* [comment removed for export] *)
Ltac cellr := unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite ?loc_padd; unfold META_prev, META_next, META_freed, META_avail.

(* [comment removed for export] *)
Definition keep_regs (R' R : bvmap 5 word) : Prop :=
  forall n, In n [3;4;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat n)) = getr R (Z_to_bv 5 (Z.of_nat n)).

Lemma keep_of_list : forall (R' R : bvmap 5 word) (l : list nat), (forall k, In k l -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  forallb (fun n => existsb (Nat.eqb n) l) [3;4;20;21;22;23;24;25;26;27]%nat = true -> keep_regs R' R.
Proof.
  intros R' R l H B n Hn. apply H. rewrite forallb_forall in B. specialize (B n Hn). apply existsb_exists in B as (k & Hk & E).
  apply Nat.eqb_eq in E. subst k. exact Hk.
Qed.

Lemma frame_regs : forall (R R' : bvmap 5 word) m sp0 canary ra s0 s1 s2 s3, ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R' 2 = wa (sp0 + -96) -> getr R' 9 = wa 613952 -> getr R' 2 = getr R 2 /\ getr R' 9 = getr R 9.
Proof. intros R R' m sp0 canary ra s0 s1 s2 s3 F E2 E9. rewrite E2, E9, (nf_R2 _ _ _ _ _ _ _ _ _ F), (nf_R9 _ _ _ _ _ _ _ _ _ F). split; [f_equal; ring | reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DQ0.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dq0 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  MT s g = Some (MUsed am) -> (am_sc am = 63 \/ 0 <= am_sc am < 48) -> am_next am = None ->
  exists R', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m rom) /\
    deq_part g (am_sc am) am s = IRet (tt, s) /\ ntf_frame R' m sp0 canary ra s0 s1 s2 s3 /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am N F R10 R12 R18 Mg Hsc Hnx.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq0z.dq0_pre R m G (am_sc am) sp0).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - Hsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia).
    all: first [ (rewrite R2; f_equal; ring) | (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E) | (clear - Hsp1 HK1; lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq0z.dq0_pdq0 R m rom G (am_sc am) sp0 P ltac:(constructor)) as (R' & Hms & P2 & P9 & P10 & P12 & P13 & P18 & Poth).
  exists R'. split; [exact Hms|]. split; [apply deq0; exact Hnx|]. split.
  { destruct (frame_regs R R' m sp0 canary ra s0 s1 s2 s3 F P2 P9) as [E2 E9].
    apply (ntf_frame_keep R R' m m sp0 canary ra s0 s1 s2 s3 F E2 E9 (mem_grows_refl m)). intros; reflexivity. }
  split; [exact P10|]. split; [exact P18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End DQ0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DQ1M.
Variables (m : word -> option byte) (G sc : Z).
Hypothesis HG : 1 <= G /\ G + 40 <= 2^47.
Hypothesis HGo : G + 40 <= 0x10000 \/ 0x97000 <= G.
Hypothesis Hsc : 0 <= sc < 48.

Definition dq1m := wbytes (wbytes (wbytes m (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="HG Hsc"] Lemma dq1_mem_out : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> dq1m (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG Hsc : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2. unfold dq1m. do 3 peel. reflexivity. Qed.
#[using="HG HGo Hsc"] Lemma dq1_mem_G0 : forall k, (k < 8)%nat -> dq1m (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HGo Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq1m. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG Hsc"] Lemma dq1_mem_G8 : forall k, (k < 8)%nat -> dq1m (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq1m. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HGo Hsc"] Lemma dq1_mem_ACT : forall k, (k < 8)%nat -> dq1m (wa (8 * sc + 614184 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HGo Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq1m. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma dq1_mem_grows : mem_grows m dq1m.
Proof. LiaFast.lf_pins LiaFast.u0. unfold dq1m. wgrow. Qed.
End DQ1M.

Section DQ1.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dq1 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= am_sc am < 48 -> length (st_active s) = 48%nat ->
  am_next am = Some g -> active_hd s (am_sc am) = Some g ->
  exists R' m', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m' rom) /\
    deq_part g (am_sc am) am s = IRet (tt, s_dq1 s g (am_sc am) am) /\ NC L X EXC (s_dq1 s g (am_sc am) am) m' sp0 K /\
    ntf_frame R' m' sp0 canary ra s0 s1 s2 s3 /\ RS L (s_dq1 s g (am_sc am) am) s /\
    (forall x, In x X -> MT (s_dq1 s g (am_sc am) am) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am N F R10 R12 R18 Mg NXg Rsc Hlen Hnx Hhd.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq1z.dq1_pre R m G sc sp0).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3 Rsc; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E; rewrite Ek in E; unfold active_hd in Hhd; fold sc k in Hhd; rewrite Hhd in E;
                  replace (8 * sc + 614184) with (614184 + 8 * sc) by ring; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; pose proof (rx_act_wr L s m EXC HR HEO Hctx k ltac:(lia) d n Hd Hn) as E; rewrite Ek in E;
                  replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring; exact E)
               | (clear - Hsp1 HK1 Rsc; lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq1z.dq1_pdq1 R m rom G sc sp0 P ltac:(constructor)) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P18 & Poth).
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq1z.dq1_mem_pdq1 m R G sc sp0) with (dq1m m G sc) in Hms.
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
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CP; CN; CA] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
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
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. rewrite MT_set_other by (intros ->; exact (NXg Hx)). reflexivity. }
  exists R', m'. split; [exact Hms|]. split; [exact (deq1 g s am Mg Hlen Hnx Rsc Hhd)|].
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split.
  { destruct (frame_regs R R' m sp0 canary ra s0 s1 s2 s3 F P2 P9) as [E2 E9].
    apply (ntf_frame_keep R R' m m' sp0 canary ra s0 s1 s2 s3 F E2 E9 Hgrow).
    intros x Hx. apply (FRM_keeps_frame L s sp0 K m m' x FR HC Hsp1); [|exact Hx].
    intros y Hy. destruct (decide (m' (wa y) = m (wa y))) as [E|E]; [exact E|]. exfalso.
    destruct (CHG y ltac:(clear - Hy Hsp1 Hsp2 HK1; lia) E) as [A|A]; clear - A Hy G2 HK1 Rsc Hsp1; lia. }
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow|]. split; [exact FR|].
  split; [exact P10|]. split; [exact P18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End DQ1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DQ3M.
Variables (m : word -> option byte) (G PR NX : Z).
Hypothesis HG : 1 <= G /\ G + 40 <= 2^47.
Hypothesis HPR : 1 <= PR /\ PR + 40 <= 2^47.
Hypothesis HNX : 1 <= NX /\ NX + 40 <= 2^47.
Hypothesis DGP : G + 40 <= PR \/ PR + 40 <= G.
Hypothesis DGN : G + 40 <= NX \/ NX + 40 <= G.
Hypothesis DPN : PR = NX \/ PR + 40 <= NX \/ NX + 40 <= PR.

Definition dq3m := wbytes (wbytes (wbytes (wbytes m (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="HG HPR HNX"] Lemma dq3_mem_out : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (PR + 8 <= x < PR + 16) -> ~ (NX <= x < NX + 8) -> dq3m (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG HPR HNX : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3. unfold dq3m. do 4 peel. reflexivity. Qed.
#[using="HG HPR HNX DGP DGN DPN"] Lemma dq3_mem_G0 : forall k, (k < 8)%nat -> dq3m (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq3m. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG"] Lemma dq3_mem_G8 : forall k, (k < 8)%nat -> dq3m (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq3m. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX DGP DGN DPN"] Lemma dq3_mem_NX0 : forall k, (k < 8)%nat -> dq3m (wa (NX + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa PR)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq3m. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX DGP DGN DPN"] Lemma dq3_mem_PR8 : forall k, (k < 8)%nat -> dq3m (wa (PR + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa NX)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq3m. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma dq3_mem_grows : mem_grows m dq3m.
Proof. LiaFast.lf_pins LiaFast.u0. unfold dq3m. wgrow. Qed.
End DQ3M.

(* [comment removed for export] *)
Lemma frame_keep_heap : forall L s sp0 K m m' (R R' : bvmap 5 word) canary ra s0 s1 s2 s3,
  FRM L s sp0 K m m' -> (forall c, In c (image s) -> cplace L (sp0 - K) c) -> 2^20 <= sp0 - K -> 1024 <= K -> sp0 <= 2^47 ->
  (forall x, 0 <= x < 2^64 -> m' (wa x) <> m (wa x) -> x < sp0 - K) ->
  ntf_frame R m sp0 canary ra s0 s1 s2 s3 -> getr R' 2 = wa (sp0 + -96) -> getr R' 9 = wa 613952 -> mem_grows m m' ->
  ntf_frame R' m' sp0 canary ra s0 s1 s2 s3.
Proof.
  intros L s sp0 K m m' R R' canary ra s0 s1 s2 s3 FR HC Hsp1 HK1 Hsp2 Hlow F P2 P9 Hg.
  destruct (frame_regs R R' m sp0 canary ra s0 s1 s2 s3 F P2 P9) as [E2 E9].
  apply (ntf_frame_keep R R' m m' sp0 canary ra s0 s1 s2 s3 F E2 E9 Hg).
  intros x Hx. apply (FRM_keeps_frame L s sp0 K m m' x FR HC Hsp1); [|exact Hx].
  intros y Hy. destruct (decide (m' (wa y) = m (wa y))) as [E|E]; [exact E|]. exfalso.
  pose proof (Hlow y ltac:(lia) E). lia.
Qed.

Section DQ3.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dq3 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am pr ampr nx amnx h,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= am_sc am < 48 -> length (st_active s) = 48%nat ->
  am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx ->
  MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) -> ~ In pr X -> ~ In nx X ->
  active_hd s (am_sc am) = Some h -> h <> g -> In h (keys s) ->
  exists R' m', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m' rom) /\
    deq_part g (am_sc am) am s = IRet (tt, s_dq3 s g am pr ampr nx amnx) /\ NC L X EXC (s_dq3 s g am pr ampr nx amnx) m' sp0 K /\
    ntf_frame R' m' sp0 canary ra s0 s1 s2 s3 /\ RS L (s_dq3 s g am pr ampr nx amnx) s /\
    (forall x, In x X -> MT (s_dq3 s g am pr ampr nx amnx) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am pr ampr nx amnx h N F R10 R12 R18 Mg NXg Rsc Hlen Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx NXpr NXnx Hhd Hhg Kh.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kpr : In pr (keys s)) by (eapply MT_keys; exact Mpr).
  assert (Knx : In nx (keys s)) by (eapply MT_keys; exact Mnx).
  set (G := loc_addr L (LMem g)) in *. set (PR := loc_addr L (LMem pr)) in *. set (NX := loc_addr L (LMem nx)) in *. set (H := loc_addr L (LMem h)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP pr Kpr) as (P1 & P2' & P3 & P4). destruct (HMP nx Knx) as (X1 & X2 & X3 & X4).
  destruct (HMP h Kh) as (H1 & H2 & H3 & H4).
  pose proof (HMD g pr Kg Kpr (fun E => Hprg (eq_sym E))) as DGP. pose proof (HMD g nx Kg Knx (fun E => Hnxg (eq_sym E))) as DGN.
  pose proof (HMD pr nx Kpr Knx Hprnx) as DPN. pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGH.
  fold G PR NX H in G1, G2, G3, G4, P1, P2', P3, P4, X1, X2, X3, X4, H1, H2, H3, H4, DGP, DGN, DPN, DGH.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.dq3_pre R m G sc sp0 NX PR H).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3 Rsc; lia).
    all: try (clear - P1 P2' Hsp2 HK1; lia). all: try (clear - X1 X2 Hsp2 HK1; lia). all: try (clear - H1 H2 Hsp2 HK1; lia).
    all: try (clear - P2' HK1; lia). all: try (clear - X2 HK1; lia). all: try (clear - DGP; lia). all: try (clear - DGN; lia).
    all: try (clear - P3 Rsc; lia). all: try (clear - X3 Rsc; lia). all: try (clear - Hsp1 HK1 Rsc; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E)
               | (pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E; rewrite Ek in E; unfold active_hd in Hhd; fold sc k in Hhd; rewrite Hhd in E;
                  replace (8 * sc + 614184) with (614184 + 8 * sc) by ring; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (PR + 8 + d) with (PR + (8 + d)) by ring; apply (rx_msc_wr L s m EXC HR HEO HK pr _ Mpr); lia)
               | (intros d n Hd Hn; replace (NX + 0 + d) with (NX + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK nx _ Mnx); lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.dq3_pdq3 R m rom G sc sp0 NX PR H P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3.RES_pdq3 fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.VALS_dq3 G sc sp0 NX PR H)).
    assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | clear - G1 G2 Hsp2 HK1; lia]).
    assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | clear - X1 X2 Hsp2 HK1; lia]).
    assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | clear - H1 H2 Hsp2 HK1; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z32, ?Z35, ?Z37;
      rewrite ?br_eq_z, ?br_ne_z; rewrite ?(Z.mod_small G), ?(Z.mod_small NX), ?(Z.mod_small H) by lia.
    - apply negb_true_iff. apply Z.eqb_neq. clear - DGH; lia.
    - apply negb_true_iff. apply Z.eqb_neq. clear - DGH; lia.
    - apply Z.eqb_neq. clear - DGN; lia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.dq3_mem_pdq3 m R G sc sp0 NX PR H) with (dq3m m G PR NX) in Hms.
  set (m' := dq3m m G PR NX).
  set (ampr' := am_set_links (am_prev ampr) (Some nx) ampr). set (amnx' := am_set_links (Some pr) (am_next amnx) amnx).
  set (S1 := set_meta s pr (MUsed ampr')). set (S2 := set_meta S1 nx (MUsed amnx')).
  assert (Es' : s_dq3 s g am pr ampr nx amnx = set_meta S2 g (MUsed (unl am))) by reflexivity.
  set (s' := s_dq3 s g am pr ampr nx amnx) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kpr).
  assert (M1nx : MT S1 nx = Some (MUsed amnx)) by (unfold S1; rewrite MT_set_other by congruence; exact Mnx).
  assert (HKS2 : KS S2) by (apply KS_set_meta; [exact HKS1 | rewrite K1; exact Knx]).
  assert (K2 : keys S2 = keys s) by (unfold S2; rewrite keys_set_meta by (rewrite K1; exact Knx); exact K1).
  assert (M2g : MT S2 g = Some (MUsed am)) by (unfold S2, S1; rewrite !MT_set_other by congruence; exact Mg).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS2 | rewrite K2; exact Kg]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (rewrite K2; exact Kg); exact K2).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; apply MT_set_same).
  assert (Ms'nx : MT s' nx = Some (MUsed amnx')) by (rewrite Es'; rewrite MT_set_other by congruence; unfold S2; apply MT_set_same).
  assert (Ms'pr : MT s' pr = Some (MUsed ampr')) by (rewrite Es'; unfold S2; rewrite !MT_set_other by congruence; unfold S1; apply MT_set_same).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S2); [apply (RS_set_used L S2 g am (unl am) HKS2 M2g); unfold unl; rewrite gc_links; reflexivity|].
    apply (RS_trans L s S1); [apply (RS_set_used L S1 nx amnx amnx' HKS1 M1nx); unfold amnx'; rewrite gc_links; reflexivity|].
    apply (RS_set_used L s pr ampr ampr' HK Mpr). unfold ampr'. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (HPr : 1 <= PR /\ PR + 40 <= 2^47) by (clear - P1 P2' Hsp2 HK1; lia).
  assert (HNr : 1 <= NX /\ NX + 40 <= 2^47) by (clear - X1 X2 Hsp2 HK1; lia).
  assert (DPN' : PR = NX \/ PR + 40 <= NX \/ NX + 40 <= PR) by (clear - DPN; lia).
  set (CPN := MCell (LMem (padd pr META_next)) 8 (optr (Some nx))).
  set (CNP := MCell (LMem (padd nx META_prev)) 8 (optr (Some pr))).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CPN; CNP; CP; CN]).
  { constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CPN CNP CP CN] in *; rewrite ?loc_padd; unfold META_prev, META_next; fold G PR NX.
    all: try (clear - HGr HPr HNr; lia).
    all: intros n Hn; unfold m'.
    - apply dq3_mem_PR8; assumption.
    - apply dq3_mem_NX0; assumption.
    - apply dq3_mem_G0; assumption.
    - apply dq3_mem_G8; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply dq3_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (G <= a < G + 16) \/ (PR + 8 <= a < PR + 16) \/ (NX <= a < NX + 8)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (PR + 8 <= a < PR + 16)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (NX <= a < NX + 8)) as [A3|A3]; [right; right; exact A3|].
    exfalso. apply Ha. unfold m'. apply dq3_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CPN; CNP; CP; CN] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. unfold unl in Hc. destruct (cov_setm_links S2 g am None None c HKS2 M2g Hc) as [Hc1|[E|E]].
      2:{ right. rewrite E. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      destruct (cov_setm_links S1 nx amnx (Some pr) (am_next amnx) c HKS1 M1nx Hc1) as [Hc2|[E|E]].
      2:{ right. rewrite E. right. left. reflexivity. }
      2:{ left. rewrite E. apply (In_image_used s nx amnx _ HK Mnx). left. cbn [meta_slot_cells In]. memb. }
      destruct (cov_setm_links s pr ampr (am_prev ampr) (Some nx) c HK Mpr Hc2) as [Hc3|[E|E]].
      + left. exact Hc3.
      + left. rewrite E. apply (In_image_used s pr ampr _ HK Mpr). left. cbn [meta_slot_cells In]. memb.
      + right. rewrite E. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
      + apply (In_image_used s' pr ampr' _ HKs' Ms'pr). left. unfold ampr'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' nx amnx' _ HKs' Ms'nx). left. unfold amnx'. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|A]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [right; right; left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; right; right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CPN. split; [left; reflexivity|]. unfold CPN. cellr. fold PR. clear - A; lia.
      + exists CNP. split; [right; left; reflexivity|]. unfold CNP. cellr. fold NX. clear - A; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|A]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
    - exists (MCell (LMem (padd pr META_next)) 8 (optr (am_next ampr))). split; [apply (In_image_used s pr ampr _ HK Mpr); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold PR. clear - A; lia.
    - exists (MCell (LMem (padd nx META_prev)) 8 (optr (am_prev amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold NX. clear - A; lia. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. unfold S2, S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXpr Hx) | intros ->; exact (NXnx Hx) | intros ->; exact (NXg Hx)]. }
  exists R', m'. split; [exact Hms|]. split; [exact (deq3 g s am Mg Hlen pr ampr nx amnx h Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx Rsc Hhd Hhg)|].
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split.
  { apply (frame_keep_heap L s sp0 K m m' R R' canary ra s0 s1 s2 s3 FR HC Hsp1 HK1 Hsp2); [|exact F | exact P2 | exact P9 | exact Hgrow].
    intros x Hx E. destruct (CHG x Hx E) as [A|[A|A]]; clear - A G2 P2' X2; lia. }
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow|]. split; [exact FR|].
  split; [exact P10|]. split; [exact P18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End DQ3.

Section DQ3S.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dq3s : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am h amh hd,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= am_sc am < 48 -> length (st_active s) = 48%nat ->
  am_next am = Some h -> am_prev am = Some h -> h <> g -> MT s h = Some (MUsed amh) -> ~ In h X ->
  active_hd s (am_sc am) = Some hd -> hd <> g -> In hd (keys s) ->
  exists R' m', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m' rom) /\
    deq_part g (am_sc am) am s = IRet (tt, s_dq3s s g am h amh) /\ NC L X EXC (s_dq3s s g am h amh) m' sp0 K /\
    ntf_frame R' m' sp0 canary ra s0 s1 s2 s3 /\ RS L (s_dq3s s g am h amh) s /\
    (forall x, In x X -> MT (s_dq3s s g am h amh) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am h amh hd N F R10 R12 R18 Mg NXg Rsc Hlen Hnx Hpr Hhg Mh NXh Hhd Hdg Khd.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kh : In h (keys s)) by (eapply MT_keys; exact Mh).
  set (G := loc_addr L (LMem g)) in *. set (HX := loc_addr L (LMem h)) in *. set (H := loc_addr L (LMem hd)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP h Kh) as (X1 & X2 & X3 & X4). destruct (HMP hd Khd) as (H1 & H2 & H3 & H4).
  pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGN. pose proof (HMD g hd Kg Khd (fun E => Hdg (eq_sym E))) as DGH.
  fold G HX H in G1, G2, G3, G4, X1, X2, X3, X4, H1, H2, H3, H4, DGN, DGH.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.dq3_pre R m G sc sp0 HX HX H).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3 Rsc; lia).
    all: try (clear - X1 X2 Hsp2 HK1; lia). all: try (clear - H1 H2 Hsp2 HK1; lia).
    all: try (clear - X2 HK1; lia). all: try (clear - DGN; lia).
    all: try (clear - X3 Rsc; lia). all: try (clear - Hsp1 HK1 Rsc; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E)
               | (pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E; rewrite Ek in E; unfold active_hd in Hhd; fold sc k in Hhd; rewrite Hhd in E;
                  replace (8 * sc + 614184) with (614184 + 8 * sc) by ring; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (HX + 8 + d) with (HX + (8 + d)) by ring; apply (rx_msc_wr L s m EXC HR HEO HK h _ Mh); lia)
               | (intros d n Hd Hn; replace (HX + 0 + d) with (HX + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK h _ Mh); lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.dq3_pdq3 R m rom G sc sp0 HX HX H P) as (R' & Hms & P2 & P9 & P10 & P11 & P12 & P13 & P14 & P18 & Poth).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3.RES_pdq3 fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.VALS_dq3 G sc sp0 HX HX H)).
    assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | clear - G1 G2 Hsp2 HK1; lia]).
    assert (Z35 : bv_unsigned (ev E 35) = HX) by (apply zatom; [reflexivity | reflexivity | clear - X1 X2 Hsp2 HK1; lia]).
    assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | clear - H1 H2 Hsp2 HK1; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z32, ?Z35, ?Z37;
      rewrite ?br_eq_z, ?br_ne_z; rewrite ?(Z.mod_small G), ?(Z.mod_small HX), ?(Z.mod_small H) by lia.
    - apply negb_true_iff. apply Z.eqb_neq. clear - DGH; lia.
    - apply negb_true_iff. apply Z.eqb_neq. clear - DGH; lia.
    - apply Z.eqb_neq. clear - DGN; lia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq3z.dq3_mem_pdq3 m R G sc sp0 HX HX H) with (dq3m m G HX HX) in Hms.
  set (m' := dq3m m G HX HX).
  set (amh' := am_set_links (Some h) (Some h) amh).
  set (S1 := set_meta s h (MUsed amh')).
  assert (Es' : s_dq3s s g am h amh = set_meta S1 g (MUsed (unl am))) by reflexivity.
  set (s' := s_dq3s s g am h amh) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kh).
  assert (M1g : MT S1 g = Some (MUsed am)) by (unfold S1; rewrite MT_set_other by congruence; exact Mg).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS1 | rewrite K1; exact Kg]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (rewrite K1; exact Kg); exact K1).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; apply MT_set_same).
  assert (Ms'h : MT s' h = Some (MUsed amh')) by (rewrite Es'; rewrite MT_set_other by congruence; unfold S1; apply MT_set_same).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S1); [apply (RS_set_used L S1 g am (unl am) HKS1 M1g); unfold unl; rewrite gc_links; reflexivity|].
    apply (RS_set_used L s h amh amh' HK Mh). unfold amh'. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (HNr : 1 <= HX /\ HX + 40 <= 2^47) by (clear - X1 X2 Hsp2 HK1; lia).
  assert (DPN' : HX = HX \/ HX + 40 <= HX \/ HX + 40 <= HX) by (left; reflexivity).
  set (CPN := MCell (LMem (padd h META_next)) 8 (optr (Some h))).
  set (CNP := MCell (LMem (padd h META_prev)) 8 (optr (Some h))).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CPN; CNP; CP; CN]).
  { constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CPN CNP CP CN] in *; rewrite ?loc_padd; unfold META_prev, META_next; fold G HX.
    all: try (clear - HGr HNr; lia).
    all: intros n Hn; unfold m'.
    - apply dq3_mem_PR8; assumption.
    - apply dq3_mem_NX0; assumption.
    - apply dq3_mem_G0; assumption.
    - apply dq3_mem_G8; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply dq3_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (G <= a < G + 16) \/ (HX + 8 <= a < HX + 16) \/ (HX <= a < HX + 8)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (HX + 8 <= a < HX + 16)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (HX <= a < HX + 8)) as [A3|A3]; [right; right; exact A3|].
    exfalso. apply Ha. unfold m'. apply dq3_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CPN; CNP; CP; CN] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. unfold unl in Hc. destruct (cov_setm_links S1 g am None None c HKS1 M1g Hc) as [Hc1|[E|E]].
      2:{ right. rewrite E. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      destruct (cov_setm_links s h amh (Some h) (Some h) c HK Mh Hc1) as [Hc3|[E|E]].
      + left. exact Hc3.
      + right. rewrite E. right. left. reflexivity.
      + right. rewrite E. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|A]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [right; right; left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; right; right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CPN. split; [left; reflexivity|]. unfold CPN. cellr. fold HX. clear - A; lia.
      + exists CNP. split; [right; left; reflexivity|]. unfold CNP. cellr. fold HX. clear - A; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|A]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
    - exists (MCell (LMem (padd h META_next)) 8 (optr (am_next amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold HX. clear - A; lia.
    - exists (MCell (LMem (padd h META_prev)) 8 (optr (am_prev amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold HX. clear - A; lia. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. unfold S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXh Hx) | intros ->; exact (NXg Hx)]. }
  exists R', m'. split; [exact Hms|]. split; [exact (deq3s g s am Mg Hlen h amh hd Hnx Hpr Hhg Mh Rsc Hhd Hdg)|].
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split.
  { apply (frame_keep_heap L s sp0 K m m' R R' canary ra s0 s1 s2 s3 FR HC Hsp1 HK1 Hsp2); [|exact F | exact P2 | exact P9 | exact Hgrow].
    intros x Hx E. destruct (CHG x Hx E) as [A|[A|A]]; clear - A G2 X2; lia. }
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow|]. split; [exact FR|].
  split; [exact P10|]. split; [exact P18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End DQ3S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DQ2M.
Variables (m : word -> option byte) (G sc PR NX FN AV : Z).
Hypothesis HG : 1 <= G /\ G + 40 <= 2^47.
Hypothesis HPR : 1 <= PR /\ PR + 40 <= 2^47.
Hypothesis HNX : 1 <= NX /\ NX + 40 <= 2^47.
Hypothesis HGo : G + 40 <= 0x10000 \/ 0x97000 <= G.
Hypothesis HNo : NX + 40 <= 0x10000 \/ 0x97000 <= NX.
Hypothesis HPo : PR + 40 <= 0x10000 \/ 0x97000 <= PR.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis DGP : G + 40 <= PR \/ PR + 40 <= G.
Hypothesis DGN : G + 40 <= NX \/ NX + 40 <= G.
Hypothesis DPN : PR = NX \/ PR + 40 <= NX \/ NX + 40 <= PR.

Definition dq2m := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR)))
  (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa NX))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)))
  (wa (NX + 28)) (word_to_le_bytes 4 (wa FN))) (wa (NX + 24)) (word_to_le_bytes 4 (wa AV)).

#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_out : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (PR + 8 <= x < PR + 16) -> ~ (NX <= x < NX + 8) ->
  ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> ~ (NX + 24 <= x < NX + 32) -> dq2m (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3 H4 H5. unfold dq2m. do 7 peel. reflexivity. Qed.
#[using="HNX Hsc"] Lemma dq2_mem_AV : forall k, (k < 4)%nat -> dq2m (wa (NX + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa AV)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HNX Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_FN : forall k, (k < 4)%nat -> dq2m (wa (NX + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa FN)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_G8 : forall k, (k < 8)%nat -> dq2m (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_G0 : forall k, (k < 8)%nat -> dq2m (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_ACT : forall k, (k < 8)%nat -> dq2m (wa (8 * sc + 614184 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa NX)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. do 4 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_NX0 : forall k, (k < 8)%nat -> dq2m (wa (NX + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa PR)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. do 5 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma dq2_mem_PR8 : forall k, (k < 8)%nat -> dq2m (wa (PR + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa NX)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold dq2m. do 6 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma dq2_mem_grows : mem_grows m dq2m.
Proof. LiaFast.lf_pins LiaFast.u0. unfold dq2m. wgrow. Qed.
End DQ2M.

Section DQ2.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dq2 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am pr ampr nx amnx,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= am_sc am < 48 -> length (st_active s) = 48%nat ->
  am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx ->
  MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) -> ~ In pr X -> ~ In nx X ->
  active_hd s (am_sc am) = Some g -> am_avail amnx = 0 -> 0 <= am_aidx amnx <= 31 -> 0 <= am_freed amnx <= 2^32-1 ->
  exists R' m', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m' rom) /\
    deq_part g (am_sc am) am s = IRet (tt, s_dq2 s g (am_sc am) am pr ampr nx amnx) /\ NC L X EXC (s_dq2 s g (am_sc am) am pr ampr nx amnx) m' sp0 K /\
    ntf_frame R' m' sp0 canary ra s0 s1 s2 s3 /\ RS L (s_dq2 s g (am_sc am) am pr ampr nx amnx) s /\
    (forall x, In x X -> MT (s_dq2 s g (am_sc am) am pr ampr nx amnx) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am pr ampr nx amnx N F R10 R12 R18 Mg NXg Rsc Hlen Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx NXpr NXnx
    Hhd Hav Raidx Rnfr.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO. pose proof HR as (_ & HPW & _).
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kpr : In pr (keys s)) by (eapply MT_keys; exact Mpr).
  assert (Knx : In nx (keys s)) by (eapply MT_keys; exact Mnx).
  set (G := loc_addr L (LMem g)) in *. set (PR := loc_addr L (LMem pr)) in *. set (NX := loc_addr L (LMem nx)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP pr Kpr) as (P1 & P2' & P3 & P4). destruct (HMP nx Knx) as (X1 & X2 & X3 & X4).
  pose proof (HMD g pr Kg Kpr (fun E => Hprg (eq_sym E))) as DGP. pose proof (HMD g nx Kg Knx (fun E => Hnxg (eq_sym E))) as DGN.
  pose proof (HMD pr nx Kpr Knx Hprnx) as DPN.
  fold G PR NX in G1, G2, G3, G4, P1, P2', P3, P4, X1, X2, X3, X4, DGP, DGN, DPN.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  (* [comment removed for export] *)
  set (NMEM := loc_addr L (LMem (am_mem amnx))).
  set (CH := MCell (LMem (am_mem amnx)) 8 (VP nx)).
  assert (CHg : In CH (gpart s)) by (apply (group_in_gpart s nx amnx CH Mnx (proj1 HK)); left; reflexivity).
  assert (CHi : In CH (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact CHg).
  pose proof (HC CH CHi) as (M1 & M2 & _). unfold CH in M1, M2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in M1, M2. fold NMEM in M1, M2.
  set (CI := if am_maplen amnx =? 0 then MCell (LMem (padd (am_mem amnx) 8)) 1 (VLo5 (am_aidx amnx)) else MCell (LMem (padd (am_mem amnx) 8)) 4 (VZ (am_aidx amnx))).
  assert (CIg : In CI (gpart s)) by (apply (group_in_gpart s nx amnx CI Mnx (proj1 HK)); right; left; reflexivity).
  assert (CIi : In CI (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact CIg).
  assert (ECI : loc_addr L (mc_loc CI) = NMEM + 8) by (unfold CI; destruct (am_maplen amnx =? 0); cbn [mc_loc]; rewrite loc_padd; reflexivity).
  assert (WCI : (1 <= mc_w CI)%nat) by (unfold CI; destruct (am_maplen amnx =? 0); cbn; lia).
  pose proof (HC CI CIi) as (I1 & I2 & _). rewrite ECI in I1, I2.
  pose proof (gpart_vs_msc L s g _ CI HPW HK Mg CIg WCI) as DIG. pose proof (gpart_vs_msc L s pr _ CI HPW HK Mpr CIg WCI) as DIP.
  pose proof (gpart_vs_msc L s nx _ CI HPW HK Mnx CIg WCI) as DIN.
  pose proof (ctx_vs_gpart L s _ CI HPW (act_in_ctx s k ltac:(lia)) CIg) as DIA.
  rewrite ECI in DIG, DIP, DIN. fold G PR NX in DIG, DIP, DIN.
  unfold ranges_disjoint, cell_range, act_cell in DIA. cbn [fst snd mc_loc mc_w loc_addr Z.of_nat Pos.of_succ_nat] in DIA. rewrite ECI, Hctx, Ek in DIA. unfold CTX_active in DIA.
  set (WI := Z.of_nat (mc_w CI)) in *. assert (WI1 : 1 <= WI) by (unfold WI; lia).
  destruct (rx_aidx L s m EXC nx amnx HR HEO HK Mnx Raidx) as (AIDXB & RAB & MAB & EAB).
  set (NFR := am_freed amnx).
  set (SPAN := 2 ^ (Z.land AIDXB 31 + 1) - 1).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.dq2_pre R m G sc sp0 NX PR NMEM AIDXB NFR).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3 Rsc; lia).
    all: try (clear - P1 P2' Hsp2 HK1; lia). all: try (clear - X1 X2 Hsp2 HK1; lia). all: try (clear - M1 M2 Hsp2 HK1; lia).
    all: try (clear - P2' HK1; lia). all: try (clear - X2 HK1; lia). all: try (clear - I2 WI1 HK1; lia). all: try (clear - DGP; lia). all: try (clear - DGN; lia).
    all: try (clear - P3 Rsc; lia). all: try (clear - X3 Rsc; lia). all: try (clear - Hsp1 HK1 Rsc; lia). all: try (clear - DPN; lia).
    all: try (clear - DIG WI1; lia). all: try (clear - DIP WI1; lia). all: try (clear - DIN WI1; lia). all: try (clear - DIA WI1; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E)
               | (pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E; rewrite Ek in E; unfold active_hd in Hhd; fold sc k in Hhd; rewrite Hhd in E;
                  replace (8 * sc + 614184) with (614184 + 8 * sc) by ring; exact E)
               | (pose proof (rx_avail L s m EXC HR HEO HK nx amnx Mnx) as E; rewrite Hav in E; exact E)
               | exact (rx_mem L s m EXC HR HEO HK nx amnx Mnx)
               | exact (rx_freed L s m EXC HR HEO HK nx amnx Mnx)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (PR + 8 + d) with (PR + (8 + d)) by ring; apply (rx_msc_wr L s m EXC HR HEO HK pr _ Mpr); lia)
               | (intros d n Hd Hn; replace (NX + 0 + d) with (NX + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK nx _ Mnx); lia)
               | (intros d n Hd Hn; replace (NX + 24 + d) with (NX + (24 + d)) by ring; apply (rx_msc_wr L s m EXC HR HEO HK nx _ Mnx); lia)
               | (intros d n Hd Hn; pose proof (rx_act_wr L s m EXC HR HEO Hctx k ltac:(lia) d n Hd Hn) as E; rewrite Ek in E;
                  replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring; exact E) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.dq2_pdq2 R m rom G sc sp0 NX PR NMEM AIDXB NFR P) as (R' & Hms & P2 & P5 & P9 & P10 & P11 & P13 & P18 & Poth).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2.RES_pdq2 fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)).
    assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | clear - G1 G2 Hsp2 HK1; lia]).
    assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | clear - X1 X2 Hsp2 HK1; lia]).
    assert (Z39 : bv_unsigned (ev E 39) = NFR) by (apply zatom; [reflexivity | reflexivity | clear - Rnfr; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z32, ?Z35, ?Z39;
      rewrite ?br_eq_z, ?br_ne_z; rewrite ?(Z.mod_small G), ?(Z.mod_small NX) by lia.
    - rewrite (Z.mod_small NFR (2^64)) by (clear - Rnfr; lia). rewrite (aor_same NFR Rnfr). reflexivity.
    - apply Z.eqb_neq. clear - DGN; lia. }
  set (FN := Z.ldiff NFR SPAN). set (AV := Z.land NFR SPAN).
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.dq2_mem_pdq2 m R G sc sp0 NX PR NMEM AIDXB NFR) with (dq2m m G sc PR NX FN AV) in Hms.
  set (m' := dq2m m G sc PR NX FN AV).
  set (ampr' := am_set_links (am_prev ampr) (Some nx) ampr). set (amnx' := am_set_links (Some pr) (am_next amnx) amnx).
  set (S1 := set_meta s pr (MUsed ampr')). set (S2 := set_meta S1 nx (MUsed amnx')).
  set (S3 := set_active (lupd (st_active S2) k (Some nx)) S2). set (S4 := set_meta S3 g (MUsed (unl am))).
  assert (ESPAN : ones (am_aidx amnx') = SPAN) by (unfold SPAN, ones; rewrite EAB; reflexivity).
  assert (Eact : act_meta amnx' = am_set_avail AV (am_set_freed FN amnx')).
  { unfold act_meta. rewrite ESPAN. reflexivity. }
  assert (Es' : s_dq2 s g sc am pr ampr nx amnx = set_meta S4 nx (MUsed (am_set_avail AV (am_set_freed FN amnx')))) by (rewrite <- Eact; reflexivity).
  set (s' := s_dq2 s g sc am pr ampr nx amnx) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kpr).
  assert (M1nx : MT S1 nx = Some (MUsed amnx)) by (unfold S1; rewrite MT_set_other by congruence; exact Mnx).
  assert (HKS2 : KS S2) by (apply KS_set_meta; [exact HKS1 | rewrite K1; exact Knx]).
  assert (K2 : keys S2 = keys s) by (unfold S2; rewrite keys_set_meta by (rewrite K1; exact Knx); exact K1).
  assert (HKS3 : KS S3) by (apply KS_set_active; exact HKS2).
  assert (M3g : MT S3 g = Some (MUsed am)) by (change (MT S3 g) with (MT S2 g); unfold S2, S1; rewrite !MT_set_other by congruence; exact Mg).
  assert (HKS4 : KS S4) by (apply KS_set_meta; [exact HKS3 | change (keys S3) with (keys S2); rewrite K2; exact Kg]).
  assert (K4 : keys S4 = keys s) by (unfold S4; rewrite keys_set_meta by (change (keys S3) with (keys S2); rewrite K2; exact Kg); change (keys S3) with (keys S2); exact K2).
  assert (M4nx : MT S4 nx = Some (MUsed amnx')) by (unfold S4; rewrite MT_set_other by congruence; change (MT S3 nx) with (MT S2 nx); unfold S2; apply MT_set_same).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS4 | rewrite K4; exact Knx]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (rewrite K4; exact Knx); exact K4).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; rewrite MT_set_other by congruence; unfold S4; apply MT_set_same).
  assert (Ms'nx : MT s' nx = Some (MUsed (am_set_avail AV (am_set_freed FN amnx')))) by (rewrite Es'; apply MT_set_same).
  assert (Ms'pr : MT s' pr = Some (MUsed ampr')).
  { rewrite Es'. rewrite MT_set_other by congruence. unfold S4. rewrite MT_set_other by congruence. change (MT S3 pr) with (MT S2 pr).
    unfold S2. rewrite MT_set_other by congruence. unfold S1. apply MT_set_same. }
  assert (Hlk2 : (k < length (st_active S2))%nat) by (change (st_active S2) with (st_active s); rewrite Hlen; lia).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S4); [apply (RS_set_used L S4 nx amnx' _ HKS4 M4nx); rewrite gc_avail, gc_freed; reflexivity|].
    apply (RS_trans L s S3); [apply (RS_set_used L S3 g am (unl am) HKS3 M3g); unfold unl; rewrite gc_links; reflexivity|].
    apply (RS_trans L s S2); [apply RS_ctx_only; reflexivity|].
    apply (RS_trans L s S1); [apply (RS_set_used L S1 nx amnx amnx' HKS1 M1nx); unfold amnx'; rewrite gc_links; reflexivity|].
    apply (RS_set_used L s pr ampr ampr' HK Mpr). unfold ampr'. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (HPr : 1 <= PR /\ PR + 40 <= 2^47) by (clear - P1 P2' Hsp2 HK1; lia).
  assert (HNr : 1 <= NX /\ NX + 40 <= 2^47) by (clear - X1 X2 Hsp2 HK1; lia).
  assert (DPN' : PR = NX \/ PR + 40 <= NX \/ NX + 40 <= PR) by (clear - DPN; lia).
  set (CPN := MCell (LMem (padd pr META_next)) 8 (optr (Some nx))).
  set (CNP := MCell (LMem (padd nx META_prev)) 8 (optr (Some pr))).
  set (CA := act_cell k (Some nx)).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  set (CAV := MCell (LMem (padd nx META_avail)) 4 (VZ AV)).
  set (CFN := MCell (LMem (padd nx META_freed)) 4 (VZ FN)).
  assert (ECA : loc_addr L (mc_loc CA) = 8 * sc + 614184) by (unfold CA, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CPN; CNP; CA; CP; CN; CAV; CFN]).
  { repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CPN CNP CA CP CN CAV CFN act_cell] in *; rewrite ?loc_padd, ?ECA; unfold META_prev, META_next, META_avail, META_freed; fold G PR NX.
    all: cbn [loc_addr] in *; rewrite ?Hctx in *; unfold CTX_active in *; rewrite ?Ek in *.
    all: try (clear - HGr HPr HNr Rsc; lia).
    all: intros n Hn; unfold m'.
    - apply dq2_mem_PR8; assumption.
    - apply dq2_mem_NX0; assumption.
    - replace (614104 + (80 + 8 * sc) + Z.of_nat n) with (8 * sc + 614184 + Z.of_nat n) by ring. apply dq2_mem_ACT; assumption.
    - apply dq2_mem_G0; assumption.
    - apply dq2_mem_G8; assumption.
    - apply dq2_mem_AV; assumption.
    - apply dq2_mem_FN; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply dq2_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) ->
     (G <= a < G + 16) \/ (PR + 8 <= a < PR + 16) \/ (NX <= a < NX + 8) \/ (8 * sc + 614184 <= a < 8 * sc + 614192) \/ (NX + 24 <= a < NX + 32)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (PR + 8 <= a < PR + 16)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (NX <= a < NX + 8)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (8 * sc + 614184 <= a < 8 * sc + 614192)) as [A4|A4]; [right; right; right; left; exact A4|].
    destruct (decide (NX + 24 <= a < NX + 32)) as [A5|A5]; [right; right; right; right; exact A5|].
    exfalso. apply Ha. unfold m'. apply dq2_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CPN; CNP; CA; CP; CN; CAV; CFN] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. destruct (cov_avail_freed S4 nx amnx' AV FN c HKS4 M4nx Hc) as [Hc1|[E|E]].
      2:{ right. rewrite E. right. right. right. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. right. right. right. left. reflexivity. }
      unfold S4, unl in Hc1. destruct (cov_setm_links S3 g am None None c HKS3 M3g Hc1) as [Hc2|[E|E]].
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. right. left. reflexivity. }
      destruct (cov_set_active S2 k (Some nx) c Hlk2 Hc2) as [Hc3|E].
      2:{ right. rewrite E. right. right. left. reflexivity. }
      destruct (cov_setm_links S1 nx amnx (Some pr) (am_next amnx) c HKS1 M1nx Hc3) as [Hc4|[E|E]].
      2:{ right. rewrite E. right. left. reflexivity. }
      2:{ left. rewrite E. apply (In_image_used s nx amnx _ HK Mnx). left. cbn [meta_slot_cells In]. memb. }
      destruct (cov_setm_links s pr ampr (am_prev ampr) (Some nx) c HK Mpr Hc4) as [Hc5|[E|E]].
      + left. exact Hc5.
      + left. rewrite E. apply (In_image_used s pr ampr _ HK Mpr). left. cbn [meta_slot_cells In]. memb.
      + right. rewrite E. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
      + apply (In_image_used s' pr ampr' _ HKs' Ms'pr). left. unfold ampr'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. unfold amnx'. cbn [meta_slot_cells In am_set_links am_set_avail am_set_freed am_prev]. memb.
      + assert (Ea : nth k (st_active s') None = Some nx).
        { rewrite Es'. change (st_active (set_meta S4 nx (MUsed (am_set_avail AV (am_set_freed FN amnx'))))) with (lupd (st_active S2) k (Some nx)).
          apply nth_lupd_same. exact Hlk2. }
        pose proof (act_in_ctx_img s' k ltac:(lia)) as E. rewrite Ea in E. exact E.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. cbn [meta_slot_cells In am_set_avail am_set_freed am_avail]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. cbn [meta_slot_cells In am_set_avail am_set_freed am_freed]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|[A|[A|A]]]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [right; right; right; left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; right; right; right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CPN. split; [left; reflexivity|]. unfold CPN. cellr. fold PR. clear - A; lia.
      + exists CNP. split; [right; left; reflexivity|]. unfold CNP. cellr. fold NX. clear - A; lia.
      + exists CA. split; [right; right; left; reflexivity|]. unfold in_rng, cell_range. rewrite ECA. unfold CA, act_cell. cbn [mc_w fst snd Z.of_nat Pos.of_succ_nat]. clear - A; lia.
      + destruct (Z_lt_le_dec a (NX + 28)) as [B|B].
        * exists CAV. split; [right; right; right; right; right; left; reflexivity|]. unfold CAV. cellr. fold NX. clear - A B; lia.
        * exists CFN. split; [right; right; right; right; right; right; left; reflexivity|]. unfold CFN. cellr. fold NX. clear - A B; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|[A|[A|A]]]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
    - exists (MCell (LMem (padd pr META_next)) 8 (optr (am_next ampr))). split; [apply (In_image_used s pr ampr _ HK Mpr); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold PR. clear - A; lia.
    - exists (MCell (LMem (padd nx META_prev)) 8 (optr (am_prev amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold NX. clear - A; lia.
    - exists (act_cell k (nth k (st_active s) None)). split; [exact (act_in_ctx_img s k ltac:(lia))|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active. clear - A; lia.
    - destruct (Z_lt_le_dec x (NX + 28)) as [B|B].
      + exists (MCell (LMem (padd nx META_avail)) 4 (VZ (am_avail amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold NX. clear - A B; lia.
      + exists (MCell (LMem (padd nx META_freed)) 4 (VZ (am_freed amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold NX. clear - A B; lia. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. rewrite MT_set_other by (intros ->; exact (NXnx Hx)). unfold S4. rewrite MT_set_other by (intros ->; exact (NXg Hx)).
    change (MT S3 x) with (MT S2 x). unfold S2, S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXpr Hx) | intros ->; exact (NXnx Hx)]. }
  exists R', m'. split; [exact Hms|]. split; [exact (deq2 g s am Mg Hlen pr ampr nx amnx Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx Rsc Hhd Hav)|].
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split.
  { apply (frame_keep_heap L s sp0 K m m' R R' canary ra s0 s1 s2 s3 FR HC Hsp1 HK1 Hsp2); [|exact F | exact P2 | exact P9 | exact Hgrow].
    intros x Hx E. destruct (CHG x Hx E) as [A|[A|[A|[A|A]]]]; clear - A G2 P2' X2 Rsc Hsp1 HK1; lia. }
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow|]. split; [exact FR|].
  split; [exact P10|]. split; [exact P18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End DQ2.

Section DQ2S.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dq2s : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am nx amnx,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 12 = wa (am_sc am) -> getr R 18 = wa 0x95ed8 ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= am_sc am < 48 -> length (st_active s) = 48%nat ->
  am_next am = Some nx -> am_prev am = Some nx -> nx <> g -> MT s nx = Some (MUsed amnx) -> ~ In nx X ->
  active_hd s (am_sc am) = Some g -> am_avail amnx = 0 -> 0 <= am_aidx amnx <= 31 -> 0 <= am_freed amnx <= 2^32-1 ->
  exists R' m', msteps SEGS (mkst R (wa 0x519e4) m rom) (mkst R' (wa 0x51af8) m' rom) /\
    deq_part g (am_sc am) am s = IRet (tt, s_dq2s s g (am_sc am) am nx amnx) /\ NC L X EXC (s_dq2s s g (am_sc am) am nx amnx) m' sp0 K /\
    ntf_frame R' m' sp0 canary ra s0 s1 s2 s3 /\ RS L (s_dq2s s g (am_sc am) am nx amnx) s /\
    (forall x, In x X -> MT (s_dq2s s g (am_sc am) am nx amnx) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    getr R' 10 = wa (loc_addr L (LMem g)) /\ getr R' 18 = wa 0x95ed8 /\ keep_regs R' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am nx amnx N F R10 R12 R18 Mg NXg Rsc Hlen Hnx Hpr Hnxg Mnx NXnx
    Hhd Hav Raidx Rnfr.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO. pose proof HR as (_ & HPW & _).
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Knx : In nx (keys s)) by (eapply MT_keys; exact Mnx).
  set (G := loc_addr L (LMem g)) in *. set (NX := loc_addr L (LMem nx)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP nx Knx) as (X1 & X2 & X3 & X4).
  pose proof (HMD g nx Kg Knx (fun E => Hnxg (eq_sym E))) as DGN.
  fold G NX in G1, G2, G3, G4, X1, X2, X3, X4, DGN.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  (* [comment removed for export] *)
  set (NMEM := loc_addr L (LMem (am_mem amnx))).
  set (CH := MCell (LMem (am_mem amnx)) 8 (VP nx)).
  assert (CHg : In CH (gpart s)) by (apply (group_in_gpart s nx amnx CH Mnx (proj1 HK)); left; reflexivity).
  assert (CHi : In CH (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact CHg).
  pose proof (HC CH CHi) as (M1 & M2 & _). unfold CH in M1, M2. cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat] in M1, M2. fold NMEM in M1, M2.
  set (CI := if am_maplen amnx =? 0 then MCell (LMem (padd (am_mem amnx) 8)) 1 (VLo5 (am_aidx amnx)) else MCell (LMem (padd (am_mem amnx) 8)) 4 (VZ (am_aidx amnx))).
  assert (CIg : In CI (gpart s)) by (apply (group_in_gpart s nx amnx CI Mnx (proj1 HK)); right; left; reflexivity).
  assert (CIi : In CI (image s)) by (rewrite image_parts; apply in_app_iff; right; apply in_app_iff; right; exact CIg).
  assert (ECI : loc_addr L (mc_loc CI) = NMEM + 8) by (unfold CI; destruct (am_maplen amnx =? 0); cbn [mc_loc]; rewrite loc_padd; reflexivity).
  assert (WCI : (1 <= mc_w CI)%nat) by (unfold CI; destruct (am_maplen amnx =? 0); cbn; lia).
  pose proof (HC CI CIi) as (I1 & I2 & _). rewrite ECI in I1, I2.
  pose proof (gpart_vs_msc L s g _ CI HPW HK Mg CIg WCI) as DIG.
  pose proof (gpart_vs_msc L s nx _ CI HPW HK Mnx CIg WCI) as DIN.
  pose proof (ctx_vs_gpart L s _ CI HPW (act_in_ctx s k ltac:(lia)) CIg) as DIA.
  rewrite ECI in DIG, DIN. fold G NX in DIG, DIN.
  unfold ranges_disjoint, cell_range, act_cell in DIA. cbn [fst snd mc_loc mc_w loc_addr Z.of_nat Pos.of_succ_nat] in DIA. rewrite ECI, Hctx, Ek in DIA. unfold CTX_active in DIA.
  set (WI := Z.of_nat (mc_w CI)) in *. assert (WI1 : 1 <= WI) by (unfold WI; lia).
  destruct (rx_aidx L s m EXC nx amnx HR HEO HK Mnx Raidx) as (AIDXB & RAB & MAB & EAB).
  set (NFR := am_freed amnx).
  set (SPAN := 2 ^ (Z.land AIDXB 31 + 1) - 1).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.dq2_pre R m G sc sp0 NX NX NMEM AIDXB NFR).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3 Rsc; lia).
    all: try (clear - X1 X2 Hsp2 HK1; lia). all: try (clear - M1 M2 Hsp2 HK1; lia).
    all: try (clear - X2 HK1; lia). all: try (clear - I2 WI1 HK1; lia). all: try (clear - DGN; lia).
    all: try (clear - X3 Rsc; lia). all: try (clear - Hsp1 HK1 Rsc; lia). all: try (clear; lia).
    all: try (clear - DIG WI1; lia). all: try (clear - DIN WI1; lia). all: try (clear - DIA WI1; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E)
               | (pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E; rewrite Ek in E; unfold active_hd in Hhd; fold sc k in Hhd; rewrite Hhd in E;
                  replace (8 * sc + 614184) with (614184 + 8 * sc) by ring; exact E)
               | (pose proof (rx_avail L s m EXC HR HEO HK nx amnx Mnx) as E; rewrite Hav in E; exact E)
               | exact (rx_mem L s m EXC HR HEO HK nx amnx Mnx)
               | exact (rx_freed L s m EXC HR HEO HK nx amnx Mnx)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (NX + 8 + d) with (NX + (8 + d)) by ring; apply (rx_msc_wr L s m EXC HR HEO HK nx _ Mnx); lia)
               | (intros d n Hd Hn; replace (NX + 0 + d) with (NX + d) by ring; apply (rx_msc_wr L s m EXC HR HEO HK nx _ Mnx); lia)
               | (intros d n Hd Hn; replace (NX + 24 + d) with (NX + (24 + d)) by ring; apply (rx_msc_wr L s m EXC HR HEO HK nx _ Mnx); lia)
               | (intros d n Hd Hn; pose proof (rx_act_wr L s m EXC HR HEO Hctx k ltac:(lia) d n Hd Hn) as E; rewrite Ek in E;
                  replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring; exact E) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.dq2_pdq2 R m rom G sc sp0 NX NX NMEM AIDXB NFR P) as (R' & Hms & P2 & P5 & P9 & P10 & P11 & P13 & P18 & Poth).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2.RES_pdq2 fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.VALS_dq2 G sc sp0 NX NX NMEM AIDXB NFR)).
    assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | clear - G1 G2 Hsp2 HK1; lia]).
    assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | clear - X1 X2 Hsp2 HK1; lia]).
    assert (Z39 : bv_unsigned (ev E 39) = NFR) by (apply zatom; [reflexivity | reflexivity | clear - Rnfr; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z32, ?Z35, ?Z39;
      rewrite ?br_eq_z, ?br_ne_z; rewrite ?(Z.mod_small G), ?(Z.mod_small NX) by lia.
    - rewrite (Z.mod_small NFR (2^64)) by (clear - Rnfr; lia). rewrite (aor_same NFR Rnfr). reflexivity.
    - apply Z.eqb_neq. clear - DGN; lia. }
  set (FN := Z.ldiff NFR SPAN). set (AV := Z.land NFR SPAN).
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dq2z.dq2_mem_pdq2 m R G sc sp0 NX NX NMEM AIDXB NFR) with (dq2m m G sc NX NX FN AV) in Hms.
  set (m' := dq2m m G sc NX NX FN AV).
  set (amnx' := am_set_links (Some nx) (Some nx) amnx).
  set (S2 := set_meta s nx (MUsed amnx')).
  set (S3 := set_active (lupd (st_active S2) k (Some nx)) S2). set (S4 := set_meta S3 g (MUsed (unl am))).
  assert (ESPAN : ones (am_aidx amnx') = SPAN) by (unfold SPAN, ones; rewrite EAB; reflexivity).
  assert (Eact : act_meta amnx' = am_set_avail AV (am_set_freed FN amnx')).
  { unfold act_meta. rewrite ESPAN. reflexivity. }
  assert (Es' : s_dq2s s g sc am nx amnx = set_meta S4 nx (MUsed (am_set_avail AV (am_set_freed FN amnx')))) by (rewrite <- Eact; reflexivity).
  set (s' := s_dq2s s g sc am nx amnx) in *.
  assert (HKS2 : KS S2) by (apply KS_set_meta; [exact HK | exact Knx]).
  assert (K2 : keys S2 = keys s) by (unfold S2; rewrite keys_set_meta by exact Knx; reflexivity).
  assert (HKS3 : KS S3) by (apply KS_set_active; exact HKS2).
  assert (M3g : MT S3 g = Some (MUsed am)) by (change (MT S3 g) with (MT S2 g); unfold S2; rewrite !MT_set_other by congruence; exact Mg).
  assert (HKS4 : KS S4) by (apply KS_set_meta; [exact HKS3 | change (keys S3) with (keys S2); rewrite K2; exact Kg]).
  assert (K4 : keys S4 = keys s) by (unfold S4; rewrite keys_set_meta by (change (keys S3) with (keys S2); rewrite K2; exact Kg); change (keys S3) with (keys S2); exact K2).
  assert (M4nx : MT S4 nx = Some (MUsed amnx')) by (unfold S4; rewrite MT_set_other by congruence; change (MT S3 nx) with (MT S2 nx); unfold S2; apply MT_set_same).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS4 | rewrite K4; exact Knx]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (rewrite K4; exact Knx); exact K4).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; rewrite MT_set_other by congruence; unfold S4; apply MT_set_same).
  assert (Ms'nx : MT s' nx = Some (MUsed (am_set_avail AV (am_set_freed FN amnx')))) by (rewrite Es'; apply MT_set_same).
  assert (Hlk2 : (k < length (st_active S2))%nat) by (change (st_active S2) with (st_active s); rewrite Hlen; lia).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S4); [apply (RS_set_used L S4 nx amnx' _ HKS4 M4nx); rewrite gc_avail, gc_freed; reflexivity|].
    apply (RS_trans L s S3); [apply (RS_set_used L S3 g am (unl am) HKS3 M3g); unfold unl; rewrite gc_links; reflexivity|].
    apply (RS_trans L s S2); [apply RS_ctx_only; reflexivity|].
    apply (RS_set_used L s nx amnx amnx' HK Mnx). unfold amnx'. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (HNr : 1 <= NX /\ NX + 40 <= 2^47) by (clear - X1 X2 Hsp2 HK1; lia).
  assert (DPN' : NX = NX \/ NX + 40 <= NX \/ NX + 40 <= NX) by (left; reflexivity).
  set (CPN := MCell (LMem (padd nx META_next)) 8 (optr (Some nx))).
  set (CNP := MCell (LMem (padd nx META_prev)) 8 (optr (Some nx))).
  set (CA := act_cell k (Some nx)).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  set (CAV := MCell (LMem (padd nx META_avail)) 4 (VZ AV)).
  set (CFN := MCell (LMem (padd nx META_freed)) 4 (VZ FN)).
  assert (ECA : loc_addr L (mc_loc CA) = 8 * sc + 614184) by (unfold CA, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CPN; CNP; CA; CP; CN; CAV; CFN]).
  { repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CPN CNP CA CP CN CAV CFN act_cell] in *; rewrite ?loc_padd, ?ECA; unfold META_prev, META_next, META_avail, META_freed; fold G NX.
    all: cbn [loc_addr] in *; rewrite ?Hctx in *; unfold CTX_active in *; rewrite ?Ek in *.
    all: try (clear - HGr HNr Rsc; lia).
    all: intros n Hn; unfold m'.
    - apply dq2_mem_PR8; assumption.
    - apply dq2_mem_NX0; assumption.
    - replace (614104 + (80 + 8 * sc) + Z.of_nat n) with (8 * sc + 614184 + Z.of_nat n) by ring. apply dq2_mem_ACT; assumption.
    - apply dq2_mem_G0; assumption.
    - apply dq2_mem_G8; assumption.
    - apply dq2_mem_AV; assumption.
    - apply dq2_mem_FN; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply dq2_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) ->
     (G <= a < G + 16) \/ (NX + 8 <= a < NX + 16) \/ (NX <= a < NX + 8) \/ (8 * sc + 614184 <= a < 8 * sc + 614192) \/ (NX + 24 <= a < NX + 32)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (NX + 8 <= a < NX + 16)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (NX <= a < NX + 8)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (8 * sc + 614184 <= a < 8 * sc + 614192)) as [A4|A4]; [right; right; right; left; exact A4|].
    destruct (decide (NX + 24 <= a < NX + 32)) as [A5|A5]; [right; right; right; right; exact A5|].
    exfalso. apply Ha. unfold m'. apply dq2_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CPN; CNP; CA; CP; CN; CAV; CFN] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. destruct (cov_avail_freed S4 nx amnx' AV FN c HKS4 M4nx Hc) as [Hc1|[E|E]].
      2:{ right. rewrite E. right. right. right. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. right. right. right. left. reflexivity. }
      unfold S4, unl in Hc1. destruct (cov_setm_links S3 g am None None c HKS3 M3g Hc1) as [Hc2|[E|E]].
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. right. left. reflexivity. }
      destruct (cov_set_active S2 k (Some nx) c Hlk2 Hc2) as [Hc3|E].
      2:{ right. rewrite E. right. right. left. reflexivity. }
      destruct (cov_setm_links s nx amnx (Some nx) (Some nx) c HK Mnx Hc3) as [Hc4|[E|E]].
      + left. exact Hc4.
      + right. rewrite E. right. left. reflexivity.
      + right. rewrite E. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. unfold amnx'. cbn [meta_slot_cells In am_set_links am_set_avail am_set_freed am_next]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. unfold amnx'. cbn [meta_slot_cells In am_set_links am_set_avail am_set_freed am_prev]. memb.
      + assert (Ea : nth k (st_active s') None = Some nx).
        { rewrite Es'. change (st_active (set_meta S4 nx (MUsed (am_set_avail AV (am_set_freed FN amnx'))))) with (lupd (st_active S2) k (Some nx)).
          apply nth_lupd_same. exact Hlk2. }
        pose proof (act_in_ctx_img s' k ltac:(lia)) as E. rewrite Ea in E. exact E.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. cbn [meta_slot_cells In am_set_avail am_set_freed am_avail]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. cbn [meta_slot_cells In am_set_avail am_set_freed am_freed]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|[A|[A|A]]]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [right; right; right; left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; right; right; right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CPN. split; [left; reflexivity|]. unfold CPN. cellr. fold NX. clear - A; lia.
      + exists CNP. split; [right; left; reflexivity|]. unfold CNP. cellr. fold NX. clear - A; lia.
      + exists CA. split; [right; right; left; reflexivity|]. unfold in_rng, cell_range. rewrite ECA. unfold CA, act_cell. cbn [mc_w fst snd Z.of_nat Pos.of_succ_nat]. clear - A; lia.
      + destruct (Z_lt_le_dec a (NX + 28)) as [B|B].
        * exists CAV. split; [right; right; right; right; right; left; reflexivity|]. unfold CAV. cellr. fold NX. clear - A B; lia.
        * exists CFN. split; [right; right; right; right; right; right; left; reflexivity|]. unfold CFN. cellr. fold NX. clear - A B; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|[A|[A|A]]]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
    - exists (MCell (LMem (padd nx META_next)) 8 (optr (am_next amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold NX. clear - A; lia.
    - exists (MCell (LMem (padd nx META_prev)) 8 (optr (am_prev amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold NX. clear - A; lia.
    - exists (act_cell k (nth k (st_active s) None)). split; [exact (act_in_ctx_img s k ltac:(lia))|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active. clear - A; lia.
    - destruct (Z_lt_le_dec x (NX + 28)) as [B|B].
      + exists (MCell (LMem (padd nx META_avail)) 4 (VZ (am_avail amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold NX. clear - A B; lia.
      + exists (MCell (LMem (padd nx META_freed)) 4 (VZ (am_freed amnx))). split; [apply (In_image_used s nx amnx _ HK Mnx); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold NX. clear - A B; lia. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. rewrite MT_set_other by (intros ->; exact (NXnx Hx)). unfold S4. rewrite MT_set_other by (intros ->; exact (NXg Hx)).
    change (MT S3 x) with (MT S2 x). unfold S2. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXnx Hx)]. }
  exists R', m'. split; [exact Hms|]. split; [exact (deq2s g s am Mg Hlen nx amnx Hnx Hpr Hnxg Mnx Rsc Hhd Hav)|].
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split.
  { apply (frame_keep_heap L s sp0 K m m' R R' canary ra s0 s1 s2 s3 FR HC Hsp1 HK1 Hsp2); [|exact F | exact P2 | exact P9 | exact Hgrow].
    intros x Hx E. destruct (CHG x Hx E) as [A|[A|[A|[A|A]]]]; clear - A G2 X2 Rsc Hsp1 HK1; lia. }
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow|]. split; [exact FR|].
  split; [exact P10|]. split; [exact P18|].
  apply (keep_of_list R' R _ Poth). reflexivity.
Qed.
End DQ2S.
