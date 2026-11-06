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
                        AXF_mb0z AXG_mfmem AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_tkz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_tkz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

(* [comment removed for export] *)
Record as_frame (R : bvmap 5 word) (m : word -> option byte) (sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : Z) : Prop := {
  af_R2 : getr R 2 = wa (sp0 + -144) ; af_R8 : getr R 8 = wa sc ; af_R18 : getr R 18 = wa req ;
  af_R20 : getr R 20 = wa 613952 ; af_R21 : getr R 21 = wa (8 * sc + 614184) ; af_R22 : getr R 22 = wa 614096 ;
  af_R23 : getr R 23 = wa (8 * sc + 614096) ;
  af_Rsp : 2^20 <= sp0 <= 2^47 ; af_Asp : sp0 mod 16 = 0 ; af_Rsc : 0 <= sc <= 47 ; af_Rreq : 0 <= req <= 2^26 ;
  af_Rcan : 0 <= can <= 2^64-1 ;
  af_Rra : 0 <= ra <= 2^64-1 ; af_Rs0 : 0 <= s0 <= 2^64-1 ; af_Rs1 : 0 <= s1 <= 2^64-1 ; af_Rs2 : 0 <= s2 <= 2^64-1 ;
  af_Rs3 : 0 <= s3 <= 2^64-1 ; af_Rs4 : 0 <= s4 <= 2^64-1 ; af_Rs5 : 0 <= s5 <= 2^64-1 ; af_Rs6 : 0 <= s6 <= 2^64-1 ;
  af_Rs7 : 0 <= s7 <= 2^64-1 ; af_Rs8 : 0 <= s8 <= 2^64-1 ; af_Rs9 : 0 <= s9 <= 2^64-1 ;
  af_Mra : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  af_Ms0 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  af_Ms1 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  af_Ms2 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  af_Ms3 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  af_Ms4 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s4)) ;
  af_Ms5 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s5)) ;
  af_Ms6 : rdn SEGS m (wa (sp0 + -64)) 8 = Some (word_to_le_bytes 8 (wa s6)) ;
  af_Ms7 : rdn SEGS m (wa (sp0 + -72)) 8 = Some (word_to_le_bytes 8 (wa s7)) ;
  af_Ms8 : rdn SEGS m (wa (sp0 + -80)) 8 = Some (word_to_le_bytes 8 (wa s8)) ;
  af_Ms9 : rdn SEGS m (wa (sp0 + -88)) 8 = Some (word_to_le_bytes 8 (wa s9)) ;
  af_Mcan : rdn SEGS m (wa (sp0 + -96)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  af_Mgd : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa can))
}.

(* [comment removed for export] *)
Lemma as_frame_mem : forall R m m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  (forall x, sp0 - 96 <= x < sp0 -> m' (wa x) = m (wa x)) -> (forall x, 613952 <= x < 613960 -> m' (wa x) = m (wa x)) ->
  as_frame R m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9.
Proof.
  intros R m m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F H1 H2. destruct F.
  constructor; try assumption.
  all: rewrite (rdn_frame_n m m'); first [assumption | (cbn [Z.of_nat Pos.of_succ_nat]; lia) | (intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; first [apply H1 | apply H2]; lia)].
Qed.

Section AS1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_mem0 (m : word -> option byte) (regs : bvmap 5 word) (sp0 can : Z) : word -> option byte :=
  OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_sp0z.sp0_mem_psp0 m regs 0 0 0 can sp0.

#[using="Type"] Theorem seg_ap : forall L s m regs rom sp0 K sc req,
  NC L [] [] s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 10 = wa sc -> getr regs 11 = wa req ->
  0 <= sc <= 47 -> 0 <= req <= 2^26 -> length (st_active s) = 48%nat -> (forall q, active_hd s sc = Some q -> In q (keys s)) ->
  exists R can, msteps SEGS (mkst regs (wa 0x522f0) m rom) (mkst R (wa 0x52350) (as_mem0 m regs sp0 can) rom) /\
    getr R 12 = wa (onum L (active_hd s sc)) /\
    as_frame R (as_mem0 m regs sp0 can) sp0 sc req can (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
      (bv_unsigned (getr regs 22)) (bv_unsigned (getr regs 23)) (bv_unsigned (getr regs 24)) (bv_unsigned (getr regs 25)) /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, 0 <= x < 2^64 -> ~ (sp0 - 96 <= x < sp0) -> as_mem0 m regs sp0 can (wa x) = m (wa x)) /\
    mem_grows m (as_mem0 m regs sp0 can).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m regs rom sp0 K sc req N R2 R10 R11 Rsc Rreq Hlen Hhk.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  destruct Henv as (Mgot & Mtab & (can & Rcan & Mcan)).
  set (hd := onum L (active_hd s sc)).
  assert (Mhd : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa hd))).
  { pose proof (rx_act L s m [] HR HEO Hctx (Z.to_nat sc) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
    replace (8 * sc + 614184) with (614184 + 8 * sc) by ring. exact E. }
  assert (Rhd : 0 <= hd <= 2^64-1).
  { unfold hd, onum. destruct (active_hd s sc) as [q|]; [|lia].
    destruct (HMP q (Hhk q eq_refl)) as (Q1 & Q2 & _). lia. }
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_sp0z.sp0_pre regs m sc req hd can sp0).
  { constructor; try assumption; try lia.
    all: try (apply (stk_ok_mono' m (wa sp0) K 1024); [exact HSTK | lia]). }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_sp0z.sp0_psp0 regs m rom sc req hd can sp0 P ltac:(constructor)) as (R & Hms & Q2 & Q8 & Q10 & Q11 & Q12 & Q18 & Q20 & Q21 & Q22 & Q23 & Qk).
  exists R, can. split; [exact Hms|]. split; [exact Q12|].
  pose proof (u64_range (getr regs 1)) as W1. pose proof (u64_range (getr regs 8)) as W8. pose proof (u64_range (getr regs 9)) as W9.
  pose proof (u64_range (getr regs 18)) as W18. pose proof (u64_range (getr regs 19)) as W19. pose proof (u64_range (getr regs 20)) as W20.
  pose proof (u64_range (getr regs 21)) as W21. pose proof (u64_range (getr regs 22)) as W22. pose proof (u64_range (getr regs 23)) as W23.
  pose proof (u64_range (getr regs 24)) as W24. pose proof (u64_range (getr regs 25)) as W25.
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (sp0 - 96 <= x < sp0) -> as_mem0 m regs sp0 can (wa x) = m (wa x)).
  { intros x Hx Hn. unfold as_mem0, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_sp0z.sp0_mem_psp0. do 12 (rewrite MngWb.wbytes_out by side). reflexivity. }
  split.
  - constructor; try assumption; try lia.
    all: try (rewrite Q21; f_equal; ring). all: try (rewrite Q23; f_equal; ring).
    all: try (apply u64_range).
    all: try (rewrite (rdn_frame_n m); [exact Mcan | lia | lia | intros x Hx; apply MOUT; lia]).
    all: unfold as_mem0, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_sp0z.sp0_mem_psp0.
    all: repeat (rewrite rdn_wbytes_disjoint; [| side | side]).
    all: first [ (apply rdn_wbytes_hit8; side) | (rewrite wa_u; apply rdn_wbytes_hit8; side) ].
  - split; [intros k Hk; cbn [In] in Hk; repeat (destruct Hk as [<-|Hk]; [apply Qk; cbn; tauto|]); destruct Hk|].
    split; [exact MOUT|].
    unfold as_mem0, OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_sp0z.sp0_mem_psp0. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kp_lit : forall (R regs : bvmap 5 word) (l : list nat),
  (forall k, In k l -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  forall k r, In k l -> Z_to_bv 5 (Z.of_nat k) = r -> getr R r = getr regs r.
Proof. LiaFast.lf_pins LiaFast.u0. intros R regs l K k r Hk <-. exact (K k Hk). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition s_take (s : astate) (g : sptr) (am : ameta) : astate :=
  set_meta s g (MUsed (am_set_avail (am_avail am - lowbit (am_avail am)) am)).

#[using="Type"] Lemma set_freed_same : forall am, am_set_freed (am_freed am) am = am.
Proof. LiaFast.lf_pins LiaFast.u0. intros []. reflexivity. Qed.

#[using="Type"] Theorem seg_tk : forall L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am,
  NC L [] [] s m sp0 K -> as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 12 = wa (loc_addr L (LMem g)) -> MT s g = Some (MUsed am) -> 1 <= am_avail am <= 2^32-1 ->
  (forall j, 0 <= j < 32 -> rdn SEGS m (wa (90368 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))) ->
  exists R' m', msteps SEGS (mkst R (wa 0x52350) m rom) (mkst R' (wa 0x52b50) m' rom) /\
    getr R' 10 = wa (ctz32 (am_avail am)) /\
    NC L [] [] (s_take s g am) m' sp0 K /\ as_frame R' m' sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 /\
    RS L (s_take s g am) s /\ mem_grows m m' /\ FRM L s sp0 K m m' /\
    (forall k, In k [1;3;4;9;19;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall j, 0 <= j < 32 -> rdn SEGS m' (wa (90368 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 g am N F R12 Mg Rav Mdb.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z [] s [] (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  set (avail := am_avail am) in *.
  assert (MAV : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail))) by exact (rx_avail L s m [] HR HEO HK g am Mg).
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta1az.ta1a_pre R m G avail) by (constructor; try assumption; lia).
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta1az.ta1a_pta1a R m rom G avail P1) as (R1 & M1 & A10 & A11 & K1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta1a.RES_pta1a fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom R (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta1az.VALS_ta1a G avail) 33 avail eq_refl eq_refl) by lia. apply ext4_ne0. lia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_ta1az.ta1a_mem_pta1a m R G avail) with m in M1.
  destruct (lowbit_pow avail ltac:(lia)) as (LP & Rj).
  assert (P2 : AXF_tkz.tk_pre R1 m G avail (ctz32 avail)).
  { constructor; try assumption; try lia.
    - rewrite db_mach_ok by lia. pose proof (db_table_ok (ctz32 avail) Rj) as (D1 & _). exact D1.
    - rewrite db_mach_ok by lia. pose proof (db_table_ok (ctz32 avail) Rj) as (D1 & D2).
      rewrite Z.add_comm, Mdb by lia. rewrite D2. reflexivity.
    - intros d k Hd Hk. replace (G + 24 + d) with (G + d + 24 - 24 + 24) by ring.
      replace (G + d + 24 - 24 + 24) with (G + (24 + d)) by ring. apply (rx_msc_wr L s m [] HR HEO HK g _ Mg); lia.
    - rewrite db_mach_ok by lia. pose proof (db_table_ok (ctz32 avail) Rj) as (D1 & _). clear - D1 G3 G1. lia. }
  destruct (AXF_tkz.tk_arm R1 m rom G avail (ctz32 avail) P2) as (R2 & M2 & B10 & K2).
  set (m' := mb0_mem m G avail).
  set (s' := s_take s g am).
  set (cn := MCell (LMem (padd g META_avail)) 4 (VZ (avail - lowbit avail))).
  assert (HKs' : KS s') by (apply KS_set_meta; [exact HK | exact Kg]).
  assert (Ks' : keys s' = keys s) by (apply keys_set_meta; exact Kg).
  assert (HRS : RS L s' s) by (apply (RS_set_used L s g am _ HK Mg); rewrite gc_avail; reflexivity).
  assert (Ms'g : MT s' g = Some (MUsed (am_set_avail (avail - lowbit avail) am))) by apply MT_set_same.
  assert (Hcn : In cn (image s')).
  { apply (In_image_used s' g _ cn HKs' Ms'g). left. cbn [meta_slot_cells]. right. right. right. left. reflexivity. }
  assert (HR' : repr_x L s' (bview SEGS m') []).
  { apply (repr_x_wcell L s s' m [] cn (G + 24) HR eq_refl eq_refl HRS).
    - intros c Hc. unfold s', s_take in Hc. rewrite <- (set_freed_same am) in Hc.
      destruct (cov_avail_freed s g am (avail - lowbit avail) (am_freed am) c HK Mg Hc) as [H|[H|H]].
      + left. exact H.
      + right. exact H.
      + left. rewrite H. pose proof (rx_freed L s m [] HR HEO HK g am Mg) as _.
        apply (In_image_used s g am _ HK Mg). left. cbn [meta_slot_cells]. right. right. right. right. left. reflexivity.
    - exact Hcn.
    - intros z E. discriminate.
    - cbn. lia.
    - unfold cn. cbn [mc_loc]. rewrite loc_padd. unfold META_avail. reflexivity.
    - lia.
    - unfold cn. cbn [mc_w Z.of_nat Pos.of_succ_nat]. lia. }
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (G + 24 <= x < G + 28) -> m' (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m', mb0_mem. rewrite MngWb.wbytes_out by side. reflexivity. }
  assert (Hgr : mem_grows m m') by apply mb0_mem_grows.
  assert (HFRM : FRM L s sp0 K m m').
  { intros x Hx Hne. right. exists (MCell (LMem (padd g META_avail)) 4 (VZ avail)). split; [|split; [unfold wide; right; cbn; lia|]].
    - apply (In_image_used s g am _ HK Mg). left. cbn [meta_slot_cells]. right. right. right. left. reflexivity.
    - unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_avail. fold G.
      destruct (Z_lt_le_dec x (G + 24)) as [A|A]; [exfalso; apply Hne; apply MOUT; [exact Hx | lia]|].
      destruct (Z_lt_le_dec x (G + 28)) as [B|B]; [lia|]. exfalso; apply Hne; apply MOUT; [exact Hx | lia]. }
  exists R2, m'. split; [exact (msteps_trans SEGS _ _ _ M1 M2)|]. split; [exact B10|].
  split; [apply (NC_next L [] [] s s' m m' sp0 K N HR' HRS HKs' ltac:(intros x []) Hgr HFRM Ks')|].
  split.
  { apply (as_frame_mem R2 m m'); [| intros x Hx; apply MOUT; lia | intros x Hx; apply MOUT; [lia | clear - Hx G1 G3; lia]].
    assert (KK : forall k, In k [2;8;18;20;21;22;23]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk. rewrite (K2 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])), (K1 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). reflexivity. }
    destruct F. constructor; try assumption.
    all: match goal with |- getr ?Rx ?r = _ =>
           first [ (rewrite (kp_lit Rx R _ KK 2%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
                 | (rewrite (kp_lit Rx R _ KK 8%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
                 | (rewrite (kp_lit Rx R _ KK 18%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
                 | (rewrite (kp_lit Rx R _ KK 20%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
                 | (rewrite (kp_lit Rx R _ KK 21%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
                 | (rewrite (kp_lit Rx R _ KK 22%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption)
                 | (rewrite (kp_lit Rx R _ KK 23%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)); assumption) ] end. }
  split; [exact HRS|]. split; [exact Hgr|]. split; [exact HFRM|]. split.
  - intros k Hk. rewrite (K2 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])), (K1 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). reflexivity.
  - intros j Hj. rewrite (rdn_frame_n m m'); [exact (Mdb j Hj) | lia | cbn; lia | intros x Hx; apply MOUT; [lia | clear - Hx G1 G3 Hj; lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem seg_ep : forall R m rom sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9,
  as_frame R m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  exists R', msteps SEGS (mkst R (wa 0x52b50) m rom) (mkst R' (wa 0x52b8c) m rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1 /\ getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\
    getr R' 20 = wa s4 /\ getr R' 21 = wa s5 /\ getr R' 22 = wa s6 /\ getr R' 23 = wa s7 /\ getr R' 24 = wa s8 /\ getr R' 25 = wa s9 /\
    (forall k, In k [3; 4; 10; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F.
  assert (P : AXF_taez.tae_pre R m can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sp0) by (destruct F; constructor; assumption).
  destruct (AXF_taez.tae_ptae R m rom can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sp0 P ltac:(constructor)) as (R' & Hms & P1 & P2 & P8 & P9 & _ & _ & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & Pk).
  exists R'. split; [exact Hms|].
  do 12 (split; [assumption|]).
  intros k Hk. apply Pk. clear - Hk. cbn [In] in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma lowbit_lowbit : forall a, 0 < a < 2^32 -> lowbit (lowbit a) = lowbit a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a Ha. destruct (lowbit_pow a Ha) as (LP & Rj). rewrite LP.
  set (j := ctz32 a) in *.
  assert (B1 : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (B2 : 2 ^ j < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  destruct (lowbit_pow (2 ^ j) (conj B1 B2)) as (LP2 & _). rewrite LP2. f_equal.
  exact (ctz32_bit j ltac:(lia)).
Qed.

#[using="Type"] Lemma alloc_slot_take : forall fuel sc req s g am,
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> 1 <= am_avail am <= 2^32-1 ->
  alloc_slot (S fuel) sc req s = IRet (ctz32 (am_avail am), s_take s g am).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fuel sc req s g am Hhd Mg Rav. unfold active_hd in Hhd. unfold MT in Mg.
  cbn [alloc_slot]. unfold try_avail, get_head, getm, setm, modify, bind, ret, get. cbn [ibind fst snd].
  rewrite Hhd. cbn [ibind]. rewrite Mg. cbn [ibind].
  replace (negb (am_avail am =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; lia).
  cbn [ibind].
  destruct (lowbit_pow (am_avail am) ltac:(lia)) as (LP & Rj).
  replace (negb (lowbit (am_avail am) =? 0)) with true.
  2:{ symmetry. apply negb_true_iff. apply Z.eqb_neq. rewrite LP. pose proof (Z.pow_pos_nonneg 2 (ctz32 (am_avail am)) ltac:(lia) ltac:(lia)). lia. }
  unfold ctz32 at 1. rewrite lowbit_lowbit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_as : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.

(* [comment removed for export] *)
Ltac litr H := match type of H with getr _ ?r = _ => match goal with |- getr _ ?r0 = _ => replace r0 with r by (apply bv_eq; reflexivity) end end; rewrite H.

#[using="Type"] Theorem as_take_step : forall L s m regs rom sp0 K sc req fuel g am,
  NC L [] [] s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 10 = wa sc -> getr regs 11 = wa req ->
  0 <= sc <= 47 -> 0 <= req <= 2^26 -> length (st_active s) = 48%nat ->
  active_hd s sc = Some g -> MT s g = Some (MUsed am) -> 1 <= am_avail am <= 2^32-1 ->
  (forall j, 0 <= j < 32 -> rdn SEGS m (wa (90368 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))) ->
  exists R m', msteps SEGS (mkst regs (wa 0x522f0) m rom) (mkst R (wa 0x52b8c) m' rom) /\
    getr R 10 = wa (ctz32 (am_avail am)) /\
    (forall k, In k callee_as -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    alloc_slot (S fuel) sc req s = IRet (ctz32 (am_avail am), s_take s g am) /\
    NC L [] [] (s_take s g am) m' sp0 K /\ RS L (s_take s g am) s /\ mem_grows m m' /\ FRM L s sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m regs rom sp0 K sc req fuel g am N R2 R10 R11 Rsc Rreq Hlen Hhd Mg Rav Mdb.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  destruct (seg_ap L s m regs rom sp0 K sc req N R2 R10 R11 Rsc Rreq Hlen ltac:(intros q Hq; rewrite Hhd in Hq; injection Hq as <-; exact Kg))
    as (R1 & can & M1 & A12 & F1 & K1 & MO1 & G1).
  set (m1 := as_mem0 m regs sp0 can) in *.
  (* [comment removed for export] *)
  assert (HFRM1 : FRM L s sp0 K m m1).
  { intros x Hx Hne. left. destruct (Z_lt_le_dec x (sp0 - 96)) as [A|A]; [exfalso; apply Hne; apply MO1; [exact Hx | lia]|].
    destruct (Z_lt_le_dec x sp0) as [B|B]; [lia|]. exfalso; apply Hne; apply MO1; [exact Hx | lia]. }
  assert (HR1 : repr_x L s (bview SEGS m1) []).
  { apply (repr_x_same L s (bview SEGS m) (bview SEGS m1) [] HR (fun x E => bview_grow_n m m1 x G1 E)).
    intros a Ha c Hc _ Hin. apply Ha.
    pose proof (bview_ne_range m m1 a Ha) as Ra.
    pose proof (HC c Hc) as (P1 & P2 & _). unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin.
    apply MngWb.bview_ext. apply MO1; [exact Ra | clear - Hin P2 HK1; lia]. }
  assert (N1 : NC L [] [] s m1 sp0 K).
  { apply (NC_next L [] [] s s m m1 sp0 K N HR1 (RS_refl L s) HK ltac:(intros x []) G1 HFRM1 eq_refl). }
  assert (Mdb1 : forall j, 0 <= j < 32 -> rdn SEGS m1 (wa (90368 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))).
  { intros j Hj. rewrite (rdn_frame_n m m1); [exact (Mdb j Hj) | lia | cbn; lia | intros x Hx; apply MO1; [lia | clear - Hx Hj Hsp1 HK1; cbn in Hx; lia]]. }
  assert (A12' : getr R1 12 = wa (loc_addr L (LMem g))) by (rewrite A12, Hhd; reflexivity).
  destruct (seg_tk L s m1 R1 rom sp0 K sc req can _ _ _ _ _ _ _ _ _ _ _ g am N1 F1 A12' Mg Rav Mdb1)
    as (R2' & m2 & M2 & B10 & N2 & F2 & HRS & G2 & HFRM2 & K2 & _).
  destruct (seg_ep R2' m2 rom sp0 sc req can _ _ _ _ _ _ _ _ _ _ _ F2)
    as (R3 & M3 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K3).
  exists R3, m2. split; [exact (msteps_trans SEGS _ _ _ M1 (msteps_trans SEGS _ _ _ M2 M3))|].
  split; [match goal with |- getr ?Rx ?r = _ => rewrite (kp_lit Rx R2' _ K3 10%nat r ltac:(cbn; tauto) ltac:(apply bv_eq; reflexivity)) end; exact B10|].
  split.
  { assert (KK : forall k, In k [3;4;26;27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk. rewrite (K3 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])), (K2 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])),
        (K1 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ])). reflexivity. }
    intros k Hk. cbn [callee_as In] in Hk.
    repeat (destruct Hk as [<-|Hk];
      [ first [ (litr E1; apply wa_u) | (litr E2; symmetry; exact R2) | (litr E8; apply wa_u) | (litr E9; apply wa_u)
              | (litr E18; apply wa_u) | (litr E19; apply wa_u) | (litr E20; apply wa_u) | (litr E21; apply wa_u)
              | (litr E22; apply wa_u) | (litr E23; apply wa_u) | (litr E24; apply wa_u) | (litr E25; apply wa_u)
              | (apply KK; cbn; tauto) ] |]).
    destruct Hk. }
  split; [exact (alloc_slot_take fuel sc req s g am Hhd Mg Rav)|].
  split; [exact N2|]. split; [exact HRS|]. split; [exact (mem_grows_trans _ _ _ G1 G2)|].
  exact (FRM_trans L s s sp0 K m m1 m2 (RS_refl L s) HFRM1 HFRM2).
Qed.

End AS1.
