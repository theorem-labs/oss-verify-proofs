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
                        AXG_ntfm AXG_ntfg AXG_nQ AXG_tam AXG_as1 AXG_as2 AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section TDM.
Variables (m : word -> option byte) (G sc PR NX : Z).
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

Definition tdm := wbytes (wbytes (wbytes (wbytes (wbytes m (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR)))
  (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa NX))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma tdm_out : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (PR + 8 <= x < PR + 16) -> ~ (NX <= x < NX + 8) ->
  ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> tdm (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3 H4. unfold tdm. do 5 peel. reflexivity. Qed.
#[using="HG Hsc"] Lemma tdm_G8 : forall k, (k < 8)%nat -> tdm (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG Hsc : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tdm. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma tdm_G0 : forall k, (k < 8)%nat -> tdm (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tdm. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HGo HNo HPo Hsc DGP DGN DPN"] Lemma tdm_ACT : forall k, (k < 8)%nat -> tdm (wa (8 * sc + 614184 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa NX)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tdm. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma tdm_NX0 : forall k, (k < 8)%nat -> tdm (wa (NX + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa PR)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tdm. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN"] Lemma tdm_PR8 : forall k, (k < 8)%nat -> tdm (wa (PR + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa NX)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (HG HPR HNX HGo HNo HPo Hsc DGP DGN DPN : LiaFast.U) => LiaFast.u0). intros k Hk. unfold tdm. do 4 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma tdm_grows : mem_grows m tdm.
Proof. LiaFast.lf_pins LiaFast.u0. unfold tdm. wgrow. Qed.
End TDM.

Section AS3.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma tadn_run : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am pr ampr nx amnx,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (loc_addr L (LMem g)) -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am = 0 ->
  am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
  exists R', msteps SEGS (mkst R (wa 0x52350) m rom)
                (mkst R' (wa 0x523b8) (tdm m (loc_addr L (LMem g)) sc (loc_addr L (LMem pr)) (loc_addr L (LMem nx))) rom) /\
    getr R' 10 = wa (loc_addr L (LMem nx)) /\
    getr R' 8 = wa sc /\ getr R' 20 = wa 613952 /\ getr R' 21 = wa (8 * sc + 614184) /\ getr R' 22 = wa 614096 /\ getr R' 23 = wa (8 * sc + 614096) /\
    (forall k, In k [1;2;3;4;9;18;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am pr ampr nx amnx N F R12 Rsc Hlen Hhd Mg Hav Hfr Hnx Hpr Hnxg Hprg Mpr Mnx.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kpr : In pr (keys s)) by (eapply MT_keys; exact Mpr).
  assert (Knx : In nx (keys s)) by (eapply MT_keys; exact Mnx).
  set (G := loc_addr L (LMem g)) in *. set (PR := loc_addr L (LMem pr)) in *. set (NX := loc_addr L (LMem nx)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP pr Kpr) as (P1 & P2 & P3 & P4). destruct (HMP nx Knx) as (X1 & X2 & X3 & X4).
  pose proof (HMD g pr Kg Kpr (fun E => Hprg (eq_sym E))) as DGP. pose proof (HMD g nx Kg Knx (fun E => Hnxg (eq_sym E))) as DGN.
  fold G PR NX in G1, G2, G3, G4, P1, P2, P3, P4, X1, X2, X3, X4, DGP, DGN.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tadnz.tadn_pre R m sc G NX PR).
  { pose proof F as [R2 R8 R18 R20 R21 R22 R23 Rsp Asp Rsc' Rreq Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 Rs7 Rs8 Rs9 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Ms5 Ms6 Ms7 Ms8 Ms9 Mcan Mgd].
    constructor; try assumption; try (clear - Rsc; lia); try (clear - G1 G2 Hsp2 HK1; lia); try (clear - P1 P2 Hsp2 HK1; lia); try (clear - X1 X2 Hsp2 HK1; lia).
    all: try (clear - DGP; lia). all: try (clear - DGN; lia).
    all: try (clear - G3 Rsc; lia). all: try (clear - P3 Rsc; lia). all: try (clear - X3 Rsc; lia).
    all: first [ (pose proof (rx_avail L s m [] HR HEO HK g am Mg) as E; rewrite Hav in E; exact E)
               | (pose proof (rx_freed L s m [] HR HEO HK g am Mg) as E; rewrite Hfr in E; exact E)
               | (pose proof (rx_next L s m [] HR HEO HK g am Mg) as E; rewrite Hnx in E; exact E)
               | (pose proof (rx_prev L s m [] HR HEO HK g am Mg) as E; rewrite Hpr in E; exact E)
               | (pose proof (rx_act L s m [] HR HEO Hctx k ltac:(lia)) as E; rewrite Ek in E; unfold active_hd in Hhd; fold k in Hhd; rewrite Hhd in E;
                  replace (8 * sc + 614184) with (614184 + 8 * sc) by ring; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s m [] HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (PR + 8 + d) with (PR + (8 + d)) by ring;
                  apply (rx_msc_wr L s m [] HR HEO HK pr _ Mpr); lia)
               | (intros d n Hd Hn; replace (NX + 0 + d) with (NX + d) by ring;
                  apply (rx_msc_wr L s m [] HR HEO HK nx _ Mnx); lia)
               | (intros d n Hd Hn; pose proof (rx_act_wr L s m [] HR HEO Hctx k ltac:(lia) d n Hd Hn) as E; rewrite Ek in E;
                  replace (8 * sc + 614184 + d) with (614184 + 8 * sc + d) by ring; exact E) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tadnz.tadn_ptadn R m rom sc G NX PR P) as (R' & Hms & Q8 & Q10 & Q11 & Q12 & Q20 & Q21 & Q22 & Q23 & Qk).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tadn.RES_ptadn fst snd]. set (E := Ez R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tadnz.VALS_tadn sc G NX PR)).
    assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | clear - G1 G2 Hsp2 HK1; lia]).
    assert (Z34 : bv_unsigned (ev E 34) = NX) by (apply zatom; [reflexivity | reflexivity | clear - X1 X2 Hsp2 HK1; lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33, ?Z34;
      rewrite ?br_eq_z, ?br_ne_z; rewrite ?(Z.mod_small G), ?(Z.mod_small NX) by lia.
    apply Z.eqb_neq. clear - DGN; lia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_tadnz.tadn_mem_ptadn m R sc G NX PR) with (tdm m G sc PR NX) in Hms.
  exists R'. split; [exact Hms|]. split; [exact Q10|]. split; [exact Q8|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|]. split; [exact Q23|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tadn_frame : forall L s m R R' sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 G PR NX,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 -> 0 <= sc < 48 ->
  1 <= G /\ G + 40 <= sp0 - K -> 1 <= PR /\ PR + 40 <= sp0 - K -> 1 <= NX /\ NX + 40 <= sp0 - K ->
  (G + 40 <= 0x10000 \/ 0x97000 <= G) -> (PR + 40 <= 0x10000 \/ 0x97000 <= PR) -> (NX + 40 <= 0x10000 \/ 0x97000 <= NX) ->
  getr R' 8 = wa sc -> getr R' 20 = wa 613952 -> getr R' 21 = wa (8 * sc + 614184) -> getr R' 22 = wa 614096 -> getr R' 23 = wa (8 * sc + 614096) ->
  (forall k, In k [1;2;3;4;9;18;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) ->
  (forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (PR + 8 <= x < PR + 16) -> ~ (NX <= x < NX + 8) ->
     ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> tdm m G sc PR NX (wa x) = m (wa x)) ->
  as_frame R' (tdm m G sc PR NX) sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R R' sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 G PR NX N F Rsc HG HP HN HGo HPo HNo Q8 Q20 Q21 Q22 Q23 Qk MOUT.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  apply (as_frame_move R R' m (tdm m G sc PR NX)); [exact F | | |].
  - exact (frame_regs_upd R R' m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F ltac:(apply Qk; cbn; tauto) ltac:(apply Qk; cbn; tauto) Q8 Q20 Q21 Q22 Q23).
  - intros x Hx. apply MOUT; clear - Hx HG HP HN Hsp1 Hsp2 HK1 Rsc; lia.
  - intros x Hx. apply MOUT; clear - Hx HG HP HN HGo HPo HNo Hsp1 Hsp2 HK1 Rsc; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_tadn : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am pr ampr nx amnx,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (loc_addr L (LMem g)) -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am = 0 ->
  am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx -> MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
  exists R' m', msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x523b8) m' rom) /\
    try_avail sc s = ta_m1 sc nx (s_tdn s g sc am pr ampr nx amnx) /\ NC L [] [] (s_tdn s g sc am pr ampr nx amnx) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_tdn s g sc am pr ampr nx amnx) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\ getr R' 10 = wa (loc_addr L (LMem nx)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am pr ampr nx amnx N F R12 Rsc Hlen Hhd Mg Hav Hfr Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx.
  destruct (tadn_run L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am pr ampr nx amnx N F R12 Rsc Hlen Hhd Mg Hav Hfr Hnx Hpr Hnxg Hprg Mpr Mnx)
    as (R' & Hms & Q10 & Q8 & Q20 & Q21 & Q22 & Q23 & Qk).
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kpr : In pr (keys s)) by (eapply MT_keys; exact Mpr).
  assert (Knx : In nx (keys s)) by (eapply MT_keys; exact Mnx).
  set (G := loc_addr L (LMem g)) in *. set (PR := loc_addr L (LMem pr)) in *. set (NX := loc_addr L (LMem nx)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP pr Kpr) as (P1 & P2 & P3 & P4). destruct (HMP nx Knx) as (X1 & X2 & X3 & X4).
  pose proof (HMD g pr Kg Kpr (fun E => Hprg (eq_sym E))) as DGP. pose proof (HMD g nx Kg Knx (fun E => Hnxg (eq_sym E))) as DGN.
  pose proof (HMD pr nx Kpr Knx Hprnx) as DPN.
  fold G PR NX in G1, G2, G3, G4, P1, P2, P3, P4, X1, X2, X3, X4, DGP, DGN, DPN.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  set (m' := tdm m G sc PR NX) in *.
  set (ampr' := am_set_links (am_prev ampr) (Some nx) ampr). set (amnx' := am_set_links (Some pr) (am_next amnx) amnx).
  set (S1 := set_meta s pr (MUsed ampr')). set (S2 := set_meta S1 nx (MUsed amnx')).
  set (S3 := set_active (lupd (st_active S2) k (Some nx)) S2).
  assert (Es' : s_tdn s g sc am pr ampr nx amnx = set_meta S3 g (MUsed (unl am))) by reflexivity.
  set (s' := s_tdn s g sc am pr ampr nx amnx) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kpr).
  assert (M1nx : MT S1 nx = Some (MUsed amnx)) by (unfold S1; rewrite MT_set_other by congruence; exact Mnx).
  assert (HKS2 : KS S2) by (apply KS_set_meta; [exact HKS1 | rewrite K1; exact Knx]).
  assert (K2 : keys S2 = keys s) by (unfold S2; rewrite keys_set_meta by (rewrite K1; exact Knx); exact K1).
  assert (HKS3 : KS S3) by (apply KS_set_active; exact HKS2).
  assert (M3g : MT S3 g = Some (MUsed am)) by (change (MT S3 g) with (MT S2 g); unfold S2, S1; rewrite !MT_set_other by congruence; exact Mg).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS3 | change (keys S3) with (keys S2); rewrite K2; exact Kg]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (change (keys S3) with (keys S2); rewrite K2; exact Kg); change (keys S3) with (keys S2); exact K2).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; apply MT_set_same).
  assert (Ms'nx : MT s' nx = Some (MUsed amnx')).
  { rewrite Es'. rewrite MT_set_other by congruence. change (MT S3 nx) with (MT S2 nx). unfold S2. apply MT_set_same. }
  assert (Ms'pr : MT s' pr = Some (MUsed ampr')).
  { rewrite Es'. rewrite MT_set_other by congruence. change (MT S3 pr) with (MT S2 pr).
    unfold S2. rewrite MT_set_other by congruence. unfold S1. apply MT_set_same. }
  assert (Hlk2 : (k < length (st_active S2))%nat) by (change (st_active S2) with (st_active s); rewrite Hlen; lia).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S3); [apply (RS_set_used L S3 g am (unl am) HKS3 M3g); unfold unl; rewrite gc_links; reflexivity|].
    apply (RS_trans L s S2); [apply RS_ctx_only; reflexivity|].
    apply (RS_trans L s S1); [apply (RS_set_used L S1 nx amnx amnx' HKS1 M1nx); unfold amnx'; rewrite gc_links; reflexivity|].
    apply (RS_set_used L s pr ampr ampr' HK Mpr). unfold ampr'. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (HPr : 1 <= PR /\ PR + 40 <= 2^47) by (clear - P1 P2 Hsp2 HK1; lia).
  assert (HNr : 1 <= NX /\ NX + 40 <= 2^47) by (clear - X1 X2 Hsp2 HK1; lia).
  assert (DPN' : PR = NX \/ PR + 40 <= NX \/ NX + 40 <= PR) by (clear - DPN; lia).
  set (CPN := MCell (LMem (padd pr META_next)) 8 (optr (Some nx))).
  set (CNP := MCell (LMem (padd nx META_prev)) 8 (optr (Some pr))).
  set (CA := act_cell k (Some nx)).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  assert (ECA : loc_addr L (mc_loc CA) = 8 * sc + 614184) by (unfold CA, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CPN; CNP; CA; CP; CN]).
  { repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CPN CNP CA CP CN act_cell] in *; rewrite ?loc_padd, ?ECA; unfold META_prev, META_next; fold G PR NX.
    all: cbn [loc_addr] in *; rewrite ?Hctx in *; unfold CTX_active in *; rewrite ?Ek in *.
    all: try (clear - HGr HPr HNr Rsc; lia).
    all: intros n Hn; unfold m'.
    - apply tdm_PR8; assumption.
    - apply tdm_NX0; assumption.
    - replace (614104 + (80 + 8 * sc) + Z.of_nat n) with (8 * sc + 614184 + Z.of_nat n) by ring. apply tdm_ACT; assumption.
    - apply tdm_G0; assumption.
    - apply tdm_G8; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply tdm_grows).
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (PR + 8 <= x < PR + 16) -> ~ (NX <= x < NX + 8) ->
     ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> m' (wa x) = m (wa x)).
  { intros x Hx H1 H2 H3 H4. unfold m'. apply tdm_out; assumption. }
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) ->
     (G <= a < G + 16) \/ (PR + 8 <= a < PR + 16) \/ (NX <= a < NX + 8) \/ (8 * sc + 614184 <= a < 8 * sc + 614192)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (PR + 8 <= a < PR + 16)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (NX <= a < NX + 8)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (8 * sc + 614184 <= a < 8 * sc + 614192)) as [A4|A4]; [right; right; right; exact A4|].
    exfalso. apply Ha. apply MOUT; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') [] [CPN; CNP; CA; CP; CN] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. unfold unl in Hc. destruct (cov_setm_links S3 g am None None c HKS3 M3g Hc) as [Hc2|[E|E]].
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
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      + apply (In_image_used s' pr ampr' _ HKs' Ms'pr). left. unfold ampr'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' nx _ _ HKs' Ms'nx). left. unfold amnx'. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + assert (Ea : nth k (st_active s') None = Some nx).
        { rewrite Es'. change (st_active (set_meta S3 g (MUsed (unl am)))) with (lupd (st_active S2) k (Some nx)).
          apply nth_lupd_same. exact Hlk2. }
        pose proof (act_in_ctx_img s' k ltac:(lia)) as E. rewrite Ea in E. exact E.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|[A|A]]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [right; right; right; left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; right; right; right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CPN. split; [left; reflexivity|]. unfold CPN. cellr. fold PR. clear - A; lia.
      + exists CNP. split; [right; left; reflexivity|]. unfold CNP. cellr. fold NX. clear - A; lia.
      + exists CA. split; [right; right; left; reflexivity|]. unfold in_rng, cell_range. rewrite ECA. unfold CA, act_cell. cbn [mc_w fst snd Z.of_nat Pos.of_succ_nat]. clear - A; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|[A|A]]].
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
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active. clear - A; lia. }
  exists R', m'. split; [exact Hms|]. split; [exact (ta_dqn s sc g am Hhd Mg Hav Hfr Hlen Rsc pr ampr nx amnx Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx)|].
  split; [exact (NC_next L [] [] s s' m m' sp0 K N REPR HRS HKs' ltac:(intros x []) Hgrow FR Ks')|].
  split; [exact (tadn_frame L s m R R' sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 G PR NX N F Rsc ltac:(clear - G1 G2; lia) ltac:(clear - P1 P2; lia)
                   ltac:(clear - X1 X2; lia) G3 P3 X3 Q8 Q20 Q21 Q22 Q23 Qk MOUT)|].
  split; [exact HRS|]. split; [exact Hgrow|]. split; [exact FR|]. split; [exact Q10|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_tad2 : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am h amh,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (loc_addr L (LMem g)) -> 0 <= sc < 48 -> length (st_active s) = 48%nat ->
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am = 0 ->
  am_next am = Some h -> am_prev am = Some h -> h <> g -> MT s h = Some (MUsed amh) ->
  exists R' m', msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x523b8) m' rom) /\
    try_avail sc s = ta_m1 sc h (s_td2 s g sc am h amh) /\ NC L [] [] (s_td2 s g sc am h amh) m' sp0 K /\
    as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\ RS L (s_td2 s g sc am h amh) s /\
    mem_grows m m' /\ FRM L s sp0 K m m' /\ getr R' 10 = wa (loc_addr L (LMem h)) /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am h amh N F R12 Rsc Hlen Hhd Mg Hav Hfr Hnx Hpr Hhg Mh.
  destruct (tadn_run L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am h amh h amh N F R12 Rsc Hlen Hhd Mg Hav Hfr Hnx Hpr Hhg Hhg Mh Mh)
    as (R' & Hms & Q10 & Q8 & Q20 & Q21 & Q22 & Q23 & Qk).
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  assert (Kh : In h (keys s)) by (eapply MT_keys; exact Mh).
  set (G := loc_addr L (LMem g)) in *. set (H := loc_addr L (LMem h)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP h Kh) as (X1 & X2 & X3 & X4).
  pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGN.
  fold G H in G1, G2, G3, G4, X1, X2, X3, X4, DGN.
  set (k := Z.to_nat sc).
  assert (Ek : Z.of_nat k = sc) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
  set (m' := tdm m G sc H H) in *.
  set (amh' := am_set_links (Some h) (Some h) amh).
  set (S1 := set_meta s h (MUsed amh')).
  set (S3 := set_active (lupd (st_active S1) k (Some h)) S1).
  assert (Es' : s_td2 s g sc am h amh = set_meta S3 g (MUsed (unl am))) by reflexivity.
  set (s' := s_td2 s g sc am h amh) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s) by (apply keys_set_meta; exact Kh).
  assert (HKS3 : KS S3) by (apply KS_set_active; exact HKS1).
  assert (M3g : MT S3 g = Some (MUsed am)) by (change (MT S3 g) with (MT S1 g); unfold S1; rewrite !MT_set_other by congruence; exact Mg).
  assert (HKs' : KS s') by (rewrite Es'; apply KS_set_meta; [exact HKS3 | change (keys S3) with (keys S1); rewrite K1; exact Kg]).
  assert (Ks' : keys s' = keys s) by (rewrite Es'; rewrite keys_set_meta by (change (keys S3) with (keys S1); rewrite K1; exact Kg); change (keys S3) with (keys S1); exact K1).
  assert (Ms'g : MT s' g = Some (MUsed (unl am))) by (rewrite Es'; apply MT_set_same).
  assert (Ms'h : MT s' h = Some (MUsed amh')).
  { rewrite Es'. rewrite MT_set_other by congruence. change (MT S3 h) with (MT S1 h). unfold S1. apply MT_set_same. }
  assert (Hlk1 : (k < length (st_active S1))%nat) by (change (st_active S1) with (st_active s); rewrite Hlen; lia).
  assert (HRS : RS L s' s).
  { rewrite Es'. apply (RS_trans L s S3); [apply (RS_set_used L S3 g am (unl am) HKS3 M3g); unfold unl; rewrite gc_links; reflexivity|].
    apply (RS_trans L s S1); [apply RS_ctx_only; reflexivity|].
    apply (RS_set_used L s h amh amh' HK Mh). unfold amh'. rewrite gc_links. reflexivity. }
  assert (HGr : 1 <= G /\ G + 40 <= 2^47) by (clear - G1 G2 Hsp2 HK1; lia).
  assert (HNr : 1 <= H /\ H + 40 <= 2^47) by (clear - X1 X2 Hsp2 HK1; lia).
  assert (DPN' : H = H \/ H + 40 <= H \/ H + 40 <= H) by (left; reflexivity).
  set (CPN := MCell (LMem (padd h META_next)) 8 (optr (Some h))).
  set (CNP := MCell (LMem (padd h META_prev)) 8 (optr (Some h))).
  set (CA := act_cell k (Some h)).
  set (CP := MCell (LMem (padd g META_prev)) 8 (optr None)).
  set (CN := MCell (LMem (padd g META_next)) 8 (optr None)).
  assert (ECA : loc_addr L (mc_loc CA) = 8 * sc + 614184) by (unfold CA, act_cell; cbn [mc_loc loc_addr]; rewrite Hctx, Ek; unfold CTX_active; ring).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) [CPN; CNP; CA; CP; CN]).
  { repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CPN CNP CA CP CN act_cell] in *; rewrite ?loc_padd, ?ECA; unfold META_prev, META_next; fold G H.
    all: cbn [loc_addr] in *; rewrite ?Hctx in *; unfold CTX_active in *; rewrite ?Ek in *.
    all: try (clear - HGr HNr Rsc; lia).
    all: intros n Hn; unfold m'.
    - apply tdm_PR8; assumption.
    - apply tdm_NX0; assumption.
    - replace (614104 + (80 + 8 * sc) + Z.of_nat n) with (8 * sc + 614184 + Z.of_nat n) by ring. apply tdm_ACT; assumption.
    - apply tdm_G0; assumption.
    - apply tdm_G8; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply tdm_grows).
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (G <= x < G + 16) -> ~ (H + 8 <= x < H + 16) -> ~ (H <= x < H + 8) ->
     ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> m' (wa x) = m (wa x)).
  { intros x Hx H1 H2 H3 H4. unfold m'. apply tdm_out; assumption. }
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) ->
     (G <= a < G + 16) \/ (H + 8 <= a < H + 16) \/ (H <= a < H + 8) \/ (8 * sc + 614184 <= a < 8 * sc + 614192)).
  { intros a Ra Ha. destruct (decide (G <= a < G + 16)) as [A1|A1]; [left; exact A1|].
    destruct (decide (H + 8 <= a < H + 16)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (H <= a < H + 8)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (8 * sc + 614184 <= a < 8 * sc + 614192)) as [A4|A4]; [right; right; right; exact A4|].
    exfalso. apply Ha. apply MOUT; assumption. }
  assert (REPR : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_next L s s' (bview SEGS m) (bview SEGS m') [] [CPN; CNP; CA; CP; CN] HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
    - intros c Hc. rewrite Es' in Hc. unfold unl in Hc. destruct (cov_setm_links S3 g am None None c HKS3 M3g Hc) as [Hc2|[E|E]].
      2:{ right. rewrite E. right. right. right. left. reflexivity. }
      2:{ right. rewrite E. right. right. right. right. left. reflexivity. }
      destruct (cov_set_active S1 k (Some h) c Hlk1 Hc2) as [Hc3|E].
      2:{ right. rewrite E. right. right. left. reflexivity. }
      destruct (cov_setm_links s h amh (Some h) (Some h) c HK Mh Hc3) as [Hc5|[E|E]].
      + left. exact Hc5.
      + right. rewrite E. right. left. reflexivity.
      + right. rewrite E. left. reflexivity.
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_next]. memb.
      + apply (In_image_used s' h amh' _ HKs' Ms'h). left. unfold amh'. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + assert (Ea : nth k (st_active s') None = Some h).
        { rewrite Es'. change (st_active (set_meta S3 g (MUsed (unl am)))) with (lupd (st_active S1) k (Some h)).
          apply nth_lupd_same. exact Hlk1. }
        pose proof (act_in_ctx_img s' k ltac:(lia)) as E. rewrite Ea in E. exact E.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_prev]. memb.
      + apply (In_image_used s' g (unl am) _ HKs' Ms'g). left. unfold unl. cbn [meta_slot_cells In am_set_links am_next]. memb.
    - exact HNew.
    - intros a Ha. left. pose proof (bview_ne_range m m' a Ha) as Ra.
      assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
      destruct (CHG a Ra Ha') as [A|[A|[A|A]]].
      + destruct (Z_lt_le_dec a (G + 8)) as [B|B].
        * exists CP. split; [right; right; right; left; reflexivity|]. unfold CP. cellr. fold G. clear - A B; lia.
        * exists CN. split; [right; right; right; right; left; reflexivity|]. unfold CN. cellr. fold G. clear - A B; lia.
      + exists CPN. split; [left; reflexivity|]. unfold CPN. cellr. fold H. clear - A; lia.
      + exists CNP. split; [right; left; reflexivity|]. unfold CNP. cellr. fold H. clear - A; lia.
      + exists CA. split; [right; right; left; reflexivity|]. unfold in_rng, cell_range. rewrite ECA. unfold CA, act_cell. cbn [mc_w fst snd Z.of_nat Pos.of_succ_nat]. clear - A; lia. }
  assert (FR : FRM L s sp0 K m m').
  { intros x Hx Hne. right. destruct (CHG x Hx Hne) as [A|[A|[A|A]]].
    - destruct (Z_lt_le_dec x (G + 8)) as [B|B].
      + exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
      + exists (MCell (LMem (padd g META_next)) 8 (optr (am_next am))). split; [apply (In_image_used s g am _ HK Mg); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
        cellr. fold G. clear - A B; lia.
    - exists (MCell (LMem (padd h META_next)) 8 (optr (am_next amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold H. clear - A; lia.
    - exists (MCell (LMem (padd h META_prev)) 8 (optr (am_prev amh))). split; [apply (In_image_used s h amh _ HK Mh); left; cbn [meta_slot_cells In]; memb|]. split; [wide_tac Hctx|].
      cellr. fold H. clear - A; lia.
    - exists (act_cell k (nth k (st_active s) None)). split; [exact (act_in_ctx_img s k ltac:(lia))|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range, act_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat loc_addr]. rewrite Hctx, Ek. unfold CTX_active. clear - A; lia. }
  exists R', m'. split; [exact Hms|]. split; [exact (ta_dq2 s sc g am Hhd Mg Hav Hfr Hlen Rsc h amh Hnx Hpr Hhg Mh)|].
  split; [exact (NC_next L [] [] s s' m m' sp0 K N REPR HRS HKs' ltac:(intros x []) Hgrow FR Ks')|].
  split; [exact (tadn_frame L s m R R' sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 G H H N F Rsc ltac:(clear - G1 G2; lia) ltac:(clear - X1 X2; lia)
                   ltac:(clear - X1 X2; lia) G3 X3 X3 Q8 Q20 Q21 Q22 Q23 Qk MOUT)|].
  split; [exact HRS|]. split; [exact Hgrow|]. split; [exact FR|]. split; [exact Q10|].
  intros k' Hk'. apply Qk. clear - Hk'. cbn [In] in *. tauto.
Qed.

End AS3.
