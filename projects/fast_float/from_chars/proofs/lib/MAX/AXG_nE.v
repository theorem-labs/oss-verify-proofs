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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez AXG_ntfm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_decz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ntfm.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.
Ltac wgrow := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Ltac memb := first [ AxSymRun3.memb_refl | repeat first [ (left; reflexivity) | right ] ].      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section E12.
Context {fx : FPState}.

#[using="Type"] Theorem seg_e12 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa (bv_swrap 32 (2^i)) -> getr R 12 = wa (am_sc am) ->
  getr R 13 = wa (bv_swrap 32 (Z.lor (am_avail am) (am_freed am))) ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= i <= 31 -> 0 <= am_sc am < 48 ->
  0 <= am_avail am <= 2^32-1 -> 0 <= am_freed am <= 2^32-1 ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false ->
  (Z.lor (am_freed am) (am_avail am) <> 0 \/ (Z.lor (am_freed am) (am_avail am) = 0 /\ active_hd s (am_sc am) = Some g)) ->
  exists R' m', msteps SEGS (mkst R (wa 0x51a2c) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 0 0 /\
    nontrivial_free (S f) g i s = IRet (None, ntf_e12 s g am i) /\ NC L X EXC (ntf_e12 s g am i) m' sp0 K /\
    RS L (ntf_e12 s g am i) s /\ (forall x, In x X -> MT (ntf_e12 s g am i) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f N F R10 R11 R12 R13 Mg NXg Ri Rsc Rav Rfr Hcond CASE.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (sc := am_sc am) in *.
  set (HV := onum L (nth (Z.to_nat sc) (st_active s) None) mod 2^64).
  assert (MH : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa HV))).
  { pose proof (rx_act L s m EXC HR HEO Hctx (Z.to_nat sc) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia.
    replace (8 * sc + 614184) with (614184 + 8 * sc) by ring. rewrite H. f_equal. f_equal. apply wa_eqm. unfold HV. rewrite Z.mod_mod by lia. reflexivity. }
  assert (RH : 0 <= HV <= 2^64-1) by (unfold HV; pose proof (Z.mod_pos_bound (onum L (nth (Z.to_nat sc) (st_active s) None)) (2^64) ltac:(lia)); lia).
  assert (Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed am)))) by exact (rx_freed L s m EXC HR HEO HK g am Mg).
  assert (WG : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 28 + d)) k = true).
  { intros d k Hd Hk. replace (G + 28 + d) with (G + (28 + d)) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (EP : ee_pre R m G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3).
  { constructor; try assumption; try lia. }
  destruct (ee12_arm R m rom G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3 HV EP RH MH) as (R' & Hms & EXIT).
  { rewrite Z.lor_comm. destruct CASE as [C|(C & Hhd)]; [left; exact C | right; split; [exact C|]].
    unfold HV. unfold active_hd in Hhd. fold sc in Hhd. rewrite Hhd. cbn [onum]. fold G. apply Z.mod_small. lia. }
  set (m' := ee12_mem m G (am_freed am) i).
  set (s' := ntf_e12 s g am i).
  set (fnew := Z.lor (am_freed am) (bit i)).
  set (CF := MCell (LMem (padd g META_freed)) 4 (VZ fnew)).
  assert (Hgrow : mem_grows m m') by (unfold m', ee12_mem; wgrow).
  assert (OUT : forall x, 0 <= x < 2^64 -> ~ (G + 28 <= x < G + 32) -> m' (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m', ee12_mem. peel. reflexivity. }
  assert (AT : forall k, (k < 4)%nat -> m' (wa (G + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa fnew)) (Z_to_bv 8 0))).
  { intros k Hk. unfold m', ee12_mem, fnew, bit. apply wbytes_at_wa; cbn [length word_to_le_bytes Z_to_le_bytes]; lia. }
  assert (Es' : s' = set_meta s g (MUsed (am_set_freed fnew am))) by reflexivity.
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; assumption).
  assert (Mg' : MT s' g = Some (MUsed (am_set_freed fnew am))) by (rewrite Es'; apply MT_set_same).
  assert (HRS : RS L s' s) by (rewrite Es'; apply (RS_set_used L s g am _ HK Mg); rewrite gc_freed; reflexivity).
  assert (CF0img : In (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))) (image s)).
  { apply (In_image_used s g am _ HK Mg). left. cbn [meta_slot_cells In]. memb. }
  assert (ECF : loc_addr L (mc_loc CF) = G + 28) by (unfold CF; cbn [mc_loc]; rewrite loc_padd; reflexivity).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CF]).
  { constructor; [|constructor]. apply holds_of_mem.
    - unfold CF. intros z E. discriminate.
    - unfold CF. cbn. lia.
    - rewrite ECF. lia.
    - rewrite ECF. unfold CF. cbn [mc_w]. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - intros k Hk. rewrite ECF. unfold CF in *. cbn [mc_w mc_val sval_num] in *. exact (AT k Hk). }
  assert (CHG : forall a, bview SEGS m' a <> bview SEGS m a -> G + 28 <= a < G + 32).
  { intros a Ha. pose proof (bview_ne_range m m' a Ha) as Ra.
    destruct (decide (G + 28 <= a < G + 32)) as [A|A]; [exact A|]. exfalso. apply Ha. apply bview_ext. apply OUT; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CF] HR eq_refl eq_refl HRS (fun a H => bview_grow_n m m' a Hgrow H)).
    - intros c Hc. rewrite Es' in Hc. destruct (cov_setm s g am _ c HK Mg Hc) as [H|[H|H]].
      + left. exact H.
      + destruct (msc_freed_cov g am fnew c H) as [H'|H']; [left; apply (In_image_used s g am c HK Mg); left; exact H' | right; rewrite H'; left; reflexivity].
      + left. rewrite gc_freed in H. apply (In_image_used s g am c HK Mg). right. exact H.
    - intros c [<-|[]]. rewrite Es'. apply (In_image_setm_new s g am _ _ HK Mg). left. cbn [meta_slot_cells In am_set_freed am_freed]. memb.
    - exact HNew.
    - intros a Ha. left. exists CF. split; [left; reflexivity|]. pose proof (CHG a Ha). unfold in_rng, cell_range. rewrite ECF. unfold CF. cbn [fst snd mc_w Z.of_nat Pos.of_succ_nat]. lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [exact CF0img|]. split; [wide_tac Hctx|].
    destruct (decide (G + 28 <= x < G + 32)) as [A|A].
    - unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_freed. fold G. lia.
    - exfalso. apply Hne. apply OUT; assumption. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. apply MT_set_other. intros ->. exact (NXg Hx). }
  exists R', m'. split; [exact Hms|]. split; [exact EXIT|]. split.
  { apply (ntf_e12_itree f g i s am Mg Hcond). destruct CASE as [C|(C & Hhd)]; [left; exact C | right; split; [exact C | split; [lia | exact Hhd]]]. }
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR ltac:(rewrite Es'; apply keys_set_meta; exact Kg))|].
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End E12.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section E3M.
Variables (m : word -> option byte) (G sc fr i : Z).
Hypothesis HG : 1 <= G /\ G + 40 <= 2^47.
Hypothesis HGo : G + 40 <= 0x10000 \/ 0x97000 <= G.
Hypothesis Hsc : 0 <= sc < 48.

#[using="HG Hsc"] Lemma e3_mem_out : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> ~ (G + 28 <= x < G + 32) ->
  ee3_mem m G sc fr i (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG Hsc : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3. unfold ee3_mem. do 4 peel. reflexivity. Qed.

#[using="HG HGo Hsc"] Lemma e3_mem_G0 : forall k, (k < 8)%nat -> ee3_mem m G sc fr i (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HGo Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee3_mem. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HGo Hsc"] Lemma e3_mem_G8 : forall k, (k < 8)%nat -> ee3_mem m G sc fr i (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HGo Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee3_mem. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HGo Hsc"] Lemma e3_mem_ACT : forall k, (k < 8)%nat -> ee3_mem m G sc fr i (wa (8 * sc + 614184 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HGo Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee3_mem. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG Hsc"] Lemma e3_mem_G28 : forall k, (k < 4)%nat -> ee3_mem m G sc fr i (wa (G + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (Z.lor fr (2^i)))) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee3_mem. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma e3_mem_grows : mem_grows m (ee3_mem m G sc fr i).
Proof. LiaFast.lf_pins LiaFast.u0. unfold ee3_mem. wgrow. Qed.
End E3M.

Section E3.
Context {fx : FPState}.

#[using="Type"] Theorem seg_e3 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa (bv_swrap 32 (2^i)) -> getr R 12 = wa (am_sc am) ->
  getr R 13 = wa (bv_swrap 32 (Z.lor (am_avail am) (am_freed am))) ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= i <= 31 -> 0 <= am_sc am < 48 ->
  0 <= am_avail am <= 2^32-1 -> 0 <= am_freed am <= 2^32-1 -> length (st_active s) = 48%nat ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false ->
  Z.lor (am_freed am) (am_avail am) = 0 -> am_prev am = None -> am_next am = None -> active_hd s (am_sc am) = None ->
  exists R' m', msteps SEGS (mkst R (wa 0x51a2c) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 0 0 /\
    nontrivial_free (S f) g i s = IRet (None, ntf_e3 s g am i) /\ NC L X EXC (ntf_e3 s g am i) m' sp0 K /\
    RS L (ntf_e3 s g am i) s /\ (forall x, In x X -> MT (ntf_e3 s g am i) x = MT s x) /\ mem_grows m m' /\ FRM L s sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f N F R10 R11 R12 R13 Mg NXg Ri Rsc Rav Rfr Hlen Hcond Hm0 Hpr Hnx Hhd.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (MA : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as H. rewrite Ek in H. unfold active_hd in Hhd. fold sc k in Hhd. rewrite Hhd in H.
    replace (8 * sc + 614184) with (614184 + 8 * sc) by ring. exact H. }
  assert (MP : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as H; rewrite Hpr in H; exact H).
  assert (MN : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as H; rewrite Hnx in H; exact H).
  assert (WG0 : forall d n, 0 <= d -> d + Z.of_nat n <= 16 -> store_ok SEGS m (wa (G + 0 + d)) n = true).
  { intros d n Hd Hn. replace (G + 0 + d) with (G + d) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (WA : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) n = true).
  { intros d n Hd Hn. pose proof (rx_act_wr L s m EXC HR HEO Hctx k ltac:(lia) d n Hd Hn) as H. rewrite Ek in H.
    replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring. exact H. }
  assert (Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed am)))) by exact (rx_freed L s m EXC HR HEO HK g am Mg).
  assert (WG : forall d n, 0 <= d -> d + Z.of_nat n <= 4 -> store_ok SEGS m (wa (G + 28 + d)) n = true).
  { intros d n Hd Hn. replace (G + 28 + d) with (G + (28 + d)) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (EP : ee_pre R m G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3) by (constructor; try assumption; try lia).
  destruct (ee3_arm R m rom G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3 EP MA MP MN WG0 WA ltac:(lia) ltac:(rewrite Z.lor_comm; exact Hm0))
    as (R' & Hms & EXIT).
  set (m' := ee3_mem m G sc (am_freed am) i).
  set (fnew := Z.lor (am_freed am) (bit i)).
  set (am1 := am_set_freed fnew (am_set_links (Some g) (Some g) am)).
  set (S1 := set_meta s g (MUsed am1)).
  assert (Es' : ntf_e3 s g am i = set_active (lupd (st_active S1) k (Some g)) S1) by reflexivity.
  set (s' := ntf_e3 s g am i) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (M1g : MT S1 g = Some (MUsed am1)) by apply MT_set_same.
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_active; exact HKS1).
  assert (Ms'g : MT s' g = Some (MUsed am1)) by (rewrite Es', MT_set_active; exact M1g).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S1); [apply RS_ctx_only; reflexivity|].
    apply (RS_set_used L s g am am1 HK Mg). unfold am1. rewrite gc_freed, gc_links. reflexivity. }
  assert (Hlen1 : (k < length (st_active S1))%nat) by (change (st_active S1) with (st_active s); rewrite Hlen; lia).
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by lia.
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr (Some g))).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr (Some g))).
  set (CF := MCell (LMem (padd g META_freed)) 4 (VZ fnew)).
  set (CA := act_cell k (Some g)).
  assert (ECA : loc_addr L (mc_loc CA) = 8 * sc + 614184) by (unfold CA, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CP; CN; CF; CA]).
  { constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CP CN CF CA act_cell] in *; rewrite ?loc_padd, ?ECA; unfold META_prev, META_next, META_freed; fold G.
    all: cbn [loc_addr] in *; rewrite ?Hctx in *; unfold CTX_active in *; rewrite ?Ek in *.
    all: try lia.
    all: intros n Hn; unfold m'.
    - apply e3_mem_G0; assumption.
    - apply e3_mem_G8; assumption.
    - apply e3_mem_G28; assumption.
    - replace (614104 + (80 + 8 * sc) + Z.of_nat n) with (8 * sc + 614184 + Z.of_nat n) by ring. apply e3_mem_ACT; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply e3_mem_grows).
  assert (CHG : forall a, bview SEGS m' a <> bview SEGS m a -> (G <= a < G + 16) \/ (8 * sc + 614184 <= a < 8 * sc + 614192) \/ (G + 28 <= a < G + 32)).
  { intros a Ha. pose proof (bview_ne_range m m' a Ha) as Ra.
    destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (8 * sc + 614184 <= a < 8 * sc + 614192)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (G + 28 <= a < G + 32)) as [A3|A3]; [right; right; exact A3|].
    exfalso. apply Ha. apply bview_ext. unfold m'. apply e3_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CP; CN; CF; CA] HR eq_refl eq_refl HRS (fun a H => bview_grow_n m m' a Hgrow H)).
    - intros c Hc. rewrite Es' in Hc. destruct (cov_set_active S1 k (Some g) c Hlen1 Hc) as [H1|E].
      + destruct (cov_links_freed s g am (Some g) (Some g) fnew c HK Mg H1) as [H2|[E|[E|E]]].
        * left. exact H2.
        * right. rewrite E. left. reflexivity.
        * right. rewrite E. right. left. reflexivity.
        * right. rewrite E. right. right. left. reflexivity.
      + right. rewrite E. right. right. right. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_prev]. memb.
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_next]. memb.
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_freed]. memb.
      + rewrite Es'. apply act_cell_in_image; [lia | exact Hlen1].
    - exact HNew.
    - intros a Ha. left. destruct (CHG a Ha) as [A|[A|A]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [left; reflexivity|]. unfold in_rng, cell_range, CP. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_prev. fold G. lia.
        * exists CN. split; [right; left; reflexivity|]. unfold in_rng, cell_range, CN. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_next. fold G. lia.
      + exists CA. split; [right; right; right; left; reflexivity|]. unfold in_rng, cell_range. rewrite ECA. unfold CA, act_cell. cbn [mc_w fst snd Z.of_nat Pos.of_succ_nat]. lia.
      + exists CF. split; [right; right; left; reflexivity|]. unfold in_rng, cell_range, CF. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_freed. fold G. lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right.
    destruct (decide (G <= x < G + 16)) as [A1|A1].
    { destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      - exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_prev. fold G. lia.
      - exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_next. fold G. lia. }
    destruct (decide (8 * sc + 614184 <= x < 8 * sc + 614192)) as [A2|A2].
    { exists (MCell (LCtx (CTX_active + 8 * Z.of_nat k)) 8 (optr (nth k (st_active s) None))). split; [exact (act_in_ctx_img s k ltac:(lia))|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active. lia. }
    destruct (decide (G + 28 <= x < G + 32)) as [A3|A3].
    { exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_freed. fold G. lia. }
    exfalso. apply Hne. unfold m'. apply e3_mem_out; assumption. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es', MT_set_active. unfold S1. apply MT_set_other. intros ->. exact (NXg Hx). }
  exists R', m'. split; [exact Hms|]. split; [exact EXIT|]. split.
  { apply (ntf_e3_itree f g i s am Mg Hcond Hm0 ltac:(lia) Hpr Hnx Hhd). }
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR ltac:(rewrite Es', keys_set_active; unfold S1; apply keys_set_meta; exact Kg))|].
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End E3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section E4M.
Variables (m : word -> option byte) (G fr i H HP : Z).
Hypothesis HG : 1 <= G /\ G + 40 <= 2^47.
Hypothesis HH : 1 <= H /\ H + 40 <= 2^47.
Hypothesis HHP : 1 <= HP /\ HP + 40 <= 2^47.
Hypothesis DGH : G + 40 <= H \/ H + 40 <= G.
Hypothesis DGHP : G + 40 <= HP \/ HP + 40 <= G.
Hypothesis DHHP : H = HP \/ H + 40 <= HP \/ HP + 40 <= H.

#[using="HG HH HHP"] Lemma e4_mem_out : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (H <= x < H + 8) -> ~ (HP + 8 <= x < HP + 16) -> ~ (G + 28 <= x < G + 32) ->
  ee4_mem m G fr i H HP (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG HH HHP : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3 H4. unfold ee4_mem. do 5 peel. reflexivity. Qed.

#[using="HG HH HHP DGH DGHP DHHP"] Lemma e4_mem_G8 : forall k, (k < 8)%nat -> ee4_mem m G fr i H HP (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa H)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HH HHP DGH DGHP DHHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee4_mem. do 4 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HH HHP DGH DGHP DHHP"] Lemma e4_mem_G0 : forall k, (k < 8)%nat -> ee4_mem m G fr i H HP (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa HP)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HH HHP DGH DGHP DHHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee4_mem. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HH HHP DGH DGHP DHHP"] Lemma e4_mem_HP8 : forall k, (k < 8)%nat -> ee4_mem m G fr i H HP (wa (HP + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HH HHP DGH DGHP DHHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee4_mem. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HH HHP DGH DGHP DHHP"] Lemma e4_mem_H0 : forall k, (k < 8)%nat -> ee4_mem m G fr i H HP (wa (H + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HH HHP DGH DGHP DHHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee4_mem. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG"] Lemma e4_mem_G28 : forall k, (k < 4)%nat -> ee4_mem m G fr i H HP (wa (G + 28 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 4 (wa (Z.lor fr (2^i)))) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG : LiaFast.U) => LiaFast.u0). intros k Hk. unfold ee4_mem. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma e4_mem_grows : mem_grows m (ee4_mem m G fr i H HP).
Proof. LiaFast.lf_pins LiaFast.u0. unfold ee4_mem. wgrow. Qed.
End E4M.

Ltac cellr c := unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite ?loc_padd; unfold META_prev, META_next, META_freed.

Section E4.
Context {fx : FPState}.

#[using="Type"] Theorem seg_e4 : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f h amh hp amhp,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa (bv_swrap 32 (2^i)) -> getr R 12 = wa (am_sc am) ->
  getr R 13 = wa (bv_swrap 32 (Z.lor (am_avail am) (am_freed am))) ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= i <= 31 -> 0 <= am_sc am < 48 ->
  0 <= am_avail am <= 2^32-1 -> 0 <= am_freed am <= 2^32-1 ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false ->
  Z.lor (am_freed am) (am_avail am) = 0 -> am_prev am = None -> am_next am = None ->
  active_hd s (am_sc am) = Some h -> h <> g -> MT s h = Some (MUsed amh) -> am_prev amh = Some hp -> hp <> g -> hp <> h ->
  MT s hp = Some (MUsed amhp) -> ~ In h X -> ~ In hp X ->
  exists R' m', msteps SEGS (mkst R (wa 0x51a2c) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 0 0 /\
    nontrivial_free (S f) g i s = IRet (None, ntf_e4 s g am i h amh hp amhp) /\ NC L X EXC (ntf_e4 s g am i h amh hp amhp) m' sp0 K /\
    RS L (ntf_e4 s g am i h amh hp amhp) s /\ (forall x, In x X -> MT (ntf_e4 s g am i h amh hp amhp) x = MT s x) /\
    mem_grows m m' /\ FRM L s sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f h amh hp amhp N F R10 R11 R12 R13 Mg NXg Ri Rsc Rav Rfr Hcond Hm0 Hpr Hnx
    Hhd Hhg Mh Hhp Hhpg Hhph Mhp NXh NXhp.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kh : In h (keys s)) by (eapply MT_keys; exact Mh).
  assert (Khp : In hp (keys s)) by (eapply MT_keys; exact Mhp).
  set (G := loc_addr L (LMem g)) in *. set (H := loc_addr L (LMem h)) in *. set (HP := loc_addr L (LMem hp)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP h Kh) as (H1 & H2 & H3 & H4). destruct (HMP hp Khp) as (P1 & P2 & P3 & P4).
  pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGH. pose proof (HMD g hp Kg Khp (fun E => Hhpg (eq_sym E))) as DGHP.
  pose proof (HMD h hp Kh Khp (fun E => Hhph (eq_sym E))) as DHHP.
  fold G H HP in G1, G2, G3, G4, H1, H2, H3, H4, P1, P2, P3, P4, DGH, DGHP, DHHP.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (MA : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H))).
  { pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E. rewrite Ek in E. unfold active_hd in Hhd. fold sc k in Hhd. rewrite Hhd in E.
    replace (8 * sc + 614184) with (614184 + 8 * sc) by ring. exact E. }
  assert (MP : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E).
  assert (MN : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E).
  assert (MH : rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP))) by (pose proof (rx_prev L s m EXC HR HEO HK h amh Mh) as E; rewrite Hhp in E; exact E).
  assert (WG0 : forall d n, 0 <= d -> d + Z.of_nat n <= 16 -> store_ok SEGS m (wa (G + 0 + d)) n = true).
  { intros d n Hd Hn. replace (G + 0 + d) with (G + d) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (WH : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (H + 0 + d)) n = true).
  { intros d n Hd Hn. replace (H + 0 + d) with (H + d) by ring. apply (rx_msc_wr L s m EXC HR HEO HK h _ Mh); lia. }
  assert (WHP : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) n = true).
  { intros d n Hd Hn. replace (HP + 8 + d) with (HP + (8 + d)) by ring. apply (rx_msc_wr L s m EXC HR HEO HK hp _ Mhp); lia. }
  assert (Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed am)))) by exact (rx_freed L s m EXC HR HEO HK g am Mg).
  assert (WG : forall d n, 0 <= d -> d + Z.of_nat n <= 4 -> store_ok SEGS m (wa (G + 28 + d)) n = true).
  { intros d n Hd Hn. replace (G + 28 + d) with (G + (28 + d)) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (EP : ee_pre R m G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3) by (constructor; try assumption; try lia).
  destruct (ee4_arm R m rom G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3 H HP EP
              ltac:(clear - H1 H2 Hsp2 HK1; lia) ltac:(clear - P1 P2 Hsp2 HK1; lia) MA MP MN MH WG0 WH WHP
              ltac:(clear - H2 HK1; lia) ltac:(clear - P2 HK1; lia) DGH DGHP ltac:(clear - H3; lia) ltac:(clear - P3; lia)
              ltac:(clear - H3 Rsc; lia) ltac:(clear - P3 Rsc; lia) ltac:(clear - G3 Rsc; lia) ltac:(rewrite Z.lor_comm; exact Hm0)
              ltac:(clear - DGH; lia)) as (R' & Hms & EXIT).
  set (m' := ee4_mem m G (am_freed am) i H HP).
  set (fnew := Z.lor (am_freed am) (bit i)).
  set (am1 := am_set_freed fnew (am_set_links (Some hp) (Some h) am)).
  set (amhp' := am_set_links (am_prev amhp) (Some g) amhp).
  set (amh' := am_set_links (Some g) (am_next amh) amh).
  set (S1 := set_meta s g (MUsed am1)). set (S2 := set_meta S1 hp (MUsed amhp')).
  assert (Es' : ntf_e4 s g am i h amh hp amhp = set_meta S2 h (MUsed amh')) by reflexivity.
  set (s' := ntf_e4 s g am i h amh hp amhp) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kg).
  assert (M1g : MT S1 g = Some (MUsed am1)) by apply MT_set_same.
  assert (M1hp : MT S1 hp = Some (MUsed amhp)) by (unfold S1; rewrite MT_set_other by exact Hhpg; exact Mhp).
  assert (HKS2 : KS S2) by (apply KS_set_meta; [exact HKS1 | rewrite K1; exact Khp]).
  assert (K2 : keys S2 = keys s) by (unfold S2; rewrite keys_set_meta by (rewrite K1; exact Khp); exact K1).
  assert (M2h : MT S2 h = Some (MUsed amh)) by (unfold S2, S1; rewrite !MT_set_other by congruence; exact Mh).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS2 | rewrite K2; exact Kh]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (rewrite K2; exact Kh); exact K2).
  assert (Ms'g : MT s' g = Some (MUsed am1)) by (rewrite Es'; unfold S2; rewrite !MT_set_other by congruence; exact M1g).
  assert (Ms'hp : MT s' hp = Some (MUsed amhp')) by (rewrite Es'; unfold S2; rewrite MT_set_other by congruence; apply MT_set_same).
  assert (Ms'h : MT s' h = Some (MUsed amh')) by (rewrite Es'; apply MT_set_same).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S2); [apply (RS_set_used L S2 h amh amh' HKS2 M2h); unfold amh'; rewrite gc_links; reflexivity|].
    apply (RS_trans L s S1); [apply (RS_set_used L S1 hp amhp amhp' HKS1 M1hp); unfold amhp'; rewrite gc_links; reflexivity|].
    apply (RS_set_used L s g am am1 HK Mg). unfold am1. rewrite gc_freed, gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by lia. assert (HHr : 1 <= H /\ H + 40 <= 2^47) by lia. assert (HPr : 1 <= HP /\ HP + 40 <= 2^47) by lia.
  assert (DHHP' : H = HP \/ H + 40 <= HP \/ HP + 40 <= H) by lia.
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr (Some hp))).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr (Some h))).
  set (CF := MCell (LMem (padd g META_freed)) 4 (VZ fnew)).
  set (CHN := MCell (LMem (padd hp META_next)) 8 (optr (Some g))).
  set (CHP := MCell (LMem (padd h META_prev)) 8 (optr (Some g))).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CP; CN; CF; CHN; CHP]).
  { constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CP CN CF CHN CHP] in *; rewrite ?loc_padd; unfold META_prev, META_next, META_freed; fold G H HP.
    all: try lia.
    all: intros n Hn; unfold m'.
    - apply e4_mem_G0; assumption.
    - apply e4_mem_G8; assumption.
    - apply e4_mem_G28; assumption.
    - apply e4_mem_HP8; assumption.
    - apply e4_mem_H0; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply e4_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (G <= a < G + 16) \/ (H <= a < H + 8) \/ (HP + 8 <= a < HP + 16) \/ (G + 28 <= a < G + 32)).
  { intros a Ra Ha.
    destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (H <= a < H + 8)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (HP + 8 <= a < HP + 16)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (G + 28 <= a < G + 32)) as [A4|A4]; [right; right; right; exact A4|].
    exfalso. apply Ha. unfold m'. apply e4_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CP; CN; CF; CHN; CHP] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. destruct (cov_setm_links S2 h amh (Some g) (am_next amh) c HKS2 M2h Hc) as [Hc1|[E|E]].
      2:{ right. rewrite E. right. right. right. right. left. reflexivity. }
      2:{ left. rewrite E. apply (In_image_used s h amh _ HK Mh). left. cbn [meta_slot_cells In]. memb. }
      destruct (cov_setm_links S1 hp amhp (am_prev amhp) (Some g) c HKS1 M1hp Hc1) as [Hc2|[E|E]].
      2:{ left. rewrite E. apply (In_image_used s hp amhp _ HK Mhp). left. cbn [meta_slot_cells In]. memb. }
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      destruct (cov_links_freed s g am (Some hp) (Some h) fnew c HK Mg Hc2) as [Hc3|[E|[E|E]]].
      + left. exact Hc3.
      + right. rewrite E. left. reflexivity.
      + right. rewrite E. right. left. reflexivity.
      + right. rewrite E. right. right. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_prev]. memb.
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_next]. memb.
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_freed]. memb.
      + apply (In_image_used s' hp amhp' _ HKs' Ms'hp). left. unfold amhp'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_prev]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|[A|A]]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [left; reflexivity|]. unfold CP. cellr CP. fold G. lia.
        * exists CN. split; [right; left; reflexivity|]. unfold CN. cellr CN. fold G. lia.
      + exists CHP. split; [right; right; right; right; left; reflexivity|]. unfold CHP. cellr CHP. fold H. lia.
      + exists CHN. split; [right; right; right; left; reflexivity|]. unfold CHN. cellr CHN. fold HP. lia.
      + exists CF. split; [right; right; left; reflexivity|]. unfold CF. cellr CF. fold G. lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|[A|A]]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr c. fold G. lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr c. fold G. lia.
    - exists (MCell (LMem (padd h META_prev)) 8 (optr (am_prev amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr c. fold H. lia.
    - exists (MCell (LMem (padd hp META_next)) 8 (optr (am_next amhp))). split; [apply (In_image_used s hp amhp _ HK Mhp); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr c. fold HP. lia.
    - exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr c. fold G. lia. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. unfold S2, S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXg Hx) | intros ->; exact (NXhp Hx) | intros ->; exact (NXh Hx)]. }
  exists R', m'. split; [exact Hms|]. split; [exact EXIT|]. split.
  { apply (ntf_e4_itree f g i s am Mg Hcond Hm0 ltac:(lia) Hpr Hnx h amh hp amhp Hhd Hhg Mh Hhp Hhpg Hhph Mhp). }
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End E4.

Section E4S.
Context {fx : FPState}.

#[using="Type"] Theorem seg_e4s : forall L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f h amh,
  NC L X EXC s m sp0 K -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa (bv_swrap 32 (2^i)) -> getr R 12 = wa (am_sc am) ->
  getr R 13 = wa (bv_swrap 32 (Z.lor (am_avail am) (am_freed am))) ->
  MT s g = Some (MUsed am) -> ~ In g X -> 0 <= i <= 31 -> 0 <= am_sc am < 48 ->
  0 <= am_avail am <= 2^32-1 -> 0 <= am_freed am <= 2^32-1 ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false ->
  Z.lor (am_freed am) (am_avail am) = 0 -> am_prev am = None -> am_next am = None ->
  active_hd s (am_sc am) = Some h -> h <> g -> MT s h = Some (MUsed amh) -> am_prev amh = Some h -> ~ In h X ->
  exists R' m', msteps SEGS (mkst R (wa 0x51a2c) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 0 0 /\
    nontrivial_free (S f) g i s = IRet (None, ntf_e4s s g am i h amh) /\ NC L X EXC (ntf_e4s s g am i h amh) m' sp0 K /\
    RS L (ntf_e4s s g am i h amh) s /\ (forall x, In x X -> MT (ntf_e4s s g am i h amh) x = MT s x) /\
    mem_grows m m' /\ FRM L s sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m R rom sp0 K canary ra s0 s1 s2 s3 g am i f h amh N F R10 R11 R12 R13 Mg NXg Ri Rsc Rav Rfr Hcond Hm0 Hpr Hnx
    Hhd Hhg Mh Hhp NXh.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kh : In h (keys s)) by (eapply MT_keys; exact Mh).
  set (G := loc_addr L (LMem g)) in *. set (H := loc_addr L (LMem h)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP h Kh) as (H1 & H2 & H3 & H4).
  pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGH.
  fold G H in G1, G2, G3, G4, H1, H2, H3, H4, DGH.
  set (sc := am_sc am) in *.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (MA : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H))).
  { pose proof (rx_act L s m EXC HR HEO Hctx k ltac:(lia)) as E. rewrite Ek in E. unfold active_hd in Hhd. fold sc k in Hhd. rewrite Hhd in E.
    replace (8 * sc + 614184) with (614184 + 8 * sc) by ring. exact E. }
  assert (MP : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (pose proof (rx_prev L s m EXC HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E).
  assert (MN : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0))) by (pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E).
  assert (MH : rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa H))) by (pose proof (rx_prev L s m EXC HR HEO HK h amh Mh) as E; rewrite Hhp in E; exact E).
  assert (WG0 : forall d n, 0 <= d -> d + Z.of_nat n <= 16 -> store_ok SEGS m (wa (G + 0 + d)) n = true).
  { intros d n Hd Hn. replace (G + 0 + d) with (G + d) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (WH : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (H + 0 + d)) n = true).
  { intros d n Hd Hn. replace (H + 0 + d) with (H + d) by ring. apply (rx_msc_wr L s m EXC HR HEO HK h _ Mh); lia. }
  assert (WHP : forall d n, 0 <= d -> d + Z.of_nat n <= 8 -> store_ok SEGS m (wa (H + 8 + d)) n = true).
  { intros d n Hd Hn. replace (H + 8 + d) with (H + (8 + d)) by ring. apply (rx_msc_wr L s m EXC HR HEO HK h _ Mh); lia. }
  assert (Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa (am_freed am)))) by exact (rx_freed L s m EXC HR HEO HK g am Mg).
  assert (WG : forall d n, 0 <= d -> d + Z.of_nat n <= 4 -> store_ok SEGS m (wa (G + 28 + d)) n = true).
  { intros d n Hd Hn. replace (G + 28 + d) with (G + (28 + d)) by ring. apply (rx_msc_wr L s m EXC HR HEO HK g _ Mg); lia. }
  assert (EP : ee_pre R m G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3) by (constructor; try assumption; try lia).
  destruct (ee4_arm R m rom G i sc (am_avail am) (am_freed am) sp0 canary ra s0 s1 s2 s3 H H EP
              ltac:(clear - H1 H2 Hsp2 HK1; lia) ltac:(clear - H1 H2 Hsp2 HK1; lia) MA MP MN MH WG0 WH WHP
              ltac:(clear - H2 HK1; lia) ltac:(clear - H2 HK1; lia) DGH DGH ltac:(clear - H3; lia) ltac:(clear - H3; lia)
              ltac:(clear - H3 Rsc; lia) ltac:(clear - H3 Rsc; lia) ltac:(clear - G3 Rsc; lia) ltac:(rewrite Z.lor_comm; exact Hm0)
              ltac:(clear - DGH; lia)) as (R' & Hms & EXIT).
  set (m' := ee4_mem m G (am_freed am) i H H).
  set (fnew := Z.lor (am_freed am) (bit i)).
  set (am1 := am_set_freed fnew (am_set_links (Some h) (Some h) am)).
  set (amh' := am_set_links (Some g) (Some g) amh).
  set (S1 := set_meta s g (MUsed am1)).
  assert (Es' : ntf_e4s s g am i h amh = set_meta S1 h (MUsed amh')) by reflexivity.
  set (s' := ntf_e4s s g am i h amh) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kg).
  assert (M1g : MT S1 g = Some (MUsed am1)) by apply MT_set_same.
  assert (M1h : MT S1 h = Some (MUsed amh)) by (unfold S1; rewrite MT_set_other by congruence; exact Mh).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS1 | rewrite K1; exact Kh]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (rewrite K1; exact Kh); exact K1).
  assert (Ms'g : MT s' g = Some (MUsed am1)) by (rewrite Es'; rewrite MT_set_other by congruence; exact M1g).
  assert (Ms'h : MT s' h = Some (MUsed amh')) by (rewrite Es'; apply MT_set_same).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S1); [apply (RS_set_used L S1 h amh amh' HKS1 M1h); unfold amh'; rewrite gc_links; reflexivity|].
    apply (RS_set_used L s g am am1 HK Mg). unfold am1. rewrite gc_freed, gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia). assert (HHr : 1 <= H /\ H + 40 <= 2^47) by (clear - H1 H2 Hsp2 HK1; lia).
  assert (DHHP' : H = H \/ H + 40 <= H \/ H + 40 <= H) by (left; reflexivity).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr (Some h))).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr (Some h))).
  set (CF := MCell (LMem (padd g META_freed)) 4 (VZ fnew)).
  set (CHN := MCell (LMem (padd h META_next)) 8 (optr (Some g))).
  set (CHP := MCell (LMem (padd h META_prev)) 8 (optr (Some g))).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CP; CN; CF; CHN; CHP]).
  { constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CP CN CF CHN CHP] in *; rewrite ?loc_padd; unfold META_prev, META_next, META_freed; fold G H.
    all: try (clear - HGr HHr; lia).
    all: intros n Hn; unfold m'.
    - apply e4_mem_G0; assumption.
    - apply e4_mem_G8; assumption.
    - apply e4_mem_G28; assumption.
    - apply e4_mem_HP8; assumption.
    - apply e4_mem_H0; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply e4_mem_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (G <= a < G + 16) \/ (H <= a < H + 8) \/ (H + 8 <= a < H + 16) \/ (G + 28 <= a < G + 32)).
  { intros a Ra Ha.
    destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (H <= a < H + 8)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (H + 8 <= a < H + 16)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (G + 28 <= a < G + 32)) as [A4|A4]; [right; right; right; exact A4|].
    exfalso. apply Ha. unfold m'. apply e4_mem_out; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') EXC).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') EXC [CP; CN; CF; CHN; CHP] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. destruct (cov_setm_links S1 h amh (Some g) (Some g) c HKS1 M1h Hc) as [Hc1|[E|E]].
      2:{ right. rewrite E. right. right. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      destruct (cov_links_freed s g am (Some h) (Some h) fnew c HK Mg Hc1) as [Hc3|[E|[E|E]]].
      + left. exact Hc3.
      + right. rewrite E. left. reflexivity.
      + right. rewrite E. right. left. reflexivity.
      + right. rewrite E. right. right. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_prev]. memb.
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_next]. memb.
      + apply (In_image_used s' g am1 _ HKs' Ms'g). left. unfold am1. cbn [meta_slot_cells In am_set_freed am_set_links am_freed]. memb.
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_prev]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|[A|A]]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [left; reflexivity|]. unfold CP. cellr CP. fold G. clear - A B; lia.
        * exists CN. split; [right; left; reflexivity|]. unfold CN. cellr CN. fold G. clear - A B; lia.
      + exists CHP. split; [right; right; right; right; left; reflexivity|]. unfold CHP. cellr CHP. fold H. clear - A; lia.
      + exists CHN. split; [right; right; right; left; reflexivity|]. unfold CHN. cellr CHN. fold H. clear - A; lia.
      + exists CF. split; [right; right; left; reflexivity|]. unfold CF. cellr CF. fold G. clear - A; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|[A|A]]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr c. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr c. fold G. clear - A B; lia.
    - exists (MCell (LMem (padd h META_prev)) 8 (optr (am_prev amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr c. fold H. clear - A; lia.
    - exists (MCell (LMem (padd h META_next)) 8 (optr (am_next amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr c. fold H. clear - A; lia.
    - exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr c. fold G. clear - A; lia. }
  assert (ZOMB : forall x, In x X -> MT s' x = MT s x).
  { intros x Hx. rewrite Es'. unfold S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXg Hx) | intros ->; exact (NXh Hx)]. }
  exists R', m'. split; [exact Hms|]. split; [exact EXIT|]. split.
  { apply (ntf_e4s_itree f g i s am Mg Hcond Hm0 ltac:(clear - Rsc; lia) Hpr Hnx h amh Hhd Hhg Mh Hhp). }
  split; [exact (NC_next L X EXC s s' m m' sp0 K N REPR HRS HKs' ZOMB Hgrow FR Ks')|].
  split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End E4S.
