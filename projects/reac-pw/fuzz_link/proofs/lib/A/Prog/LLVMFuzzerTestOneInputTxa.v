(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 619 of its 674 lines of code are new or changed and 349 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the state after a text_of call of the body (0x82e24, 0x82e34, 0x837d8), from
   text_of's post as lib/A/Prog/LLVMFuzzerTestOneInputTxo.v lf_text_of_call states it (for
   op_decide and op_write).

   lf_text_of_after: the cut carried to the return state (LLVMFuzzerTestOneInputArmK.v ak_cut_callee; text_of's
   write set is the cursor and the out slot, which miss the cut's footprint), the own list grown by the fresh
   block if text_of made one (`tx_nb`), the counters raised by one event, one wild trace and at most
   TEXT_OF_LIVE live bytes, the cursor advanced, the out slot's word, and the answer as
   LLVMFuzzerTestOneInputDec.v's dec_ans.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the block a text_of call added to the own list, or none *)
Definition tx_nb (own1 : Z) (nb : list (Z * Z)) : Prop :=
  (own1 = 0 /\ nb = []) \/ (exists k, own1 <> 0 /\ 4096 <= own1 /\ 1 <= k <= TEXT_OF_LIVE /\ nb = [(own1, k)]).

(* the answer, tied to the block text_of made: a texts entry when own1 = 0, else that block *)
Definition tx_ans (B : asyms) (segs : list Segment) (own1 : Z) (nb : list (Z * Z)) (ly : alayout) (S : astate)
    (m : word -> option byte) (s : Z) (t : list byte) : Prop :=
  (own1 = 0 /\ nb = [] /\ dec_ans_l s t) \/
  (exists k, own1 <> 0 /\ s = own1 /\ nb = [(own1, k)] /\ In (own1, k) (ablocks B ly S) /\
     Z.of_nat (length t) + 1 <= k <= TEXT_OF_LIVE /\ acstr_at segs m s t).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* a block appended to a pairwise-disjoint list is apart from every earlier block *)
Lemma tx_fresh_apart : forall ly2 S2 (W2 : world SEGS) mem2 md2 bl b,
  AR SEGS B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = bl ++ [b] ->
  forall c, In c bl -> zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)).
Proof.
  intros ly2 S2 W2 mem2 md2 bl b HAR Hbl c Hc.
  destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (HP & _).
  rewrite Hbl, !map_app in HP. cbn [map] in HP.
  apply pairwise_app_inv in HP as (HP & _ & _).
  apply (pairwise_In zdisjoint _ _ _ (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) bl)
    [(fst b, req_size (snd b))] eq_refl HP); [|left; reflexivity].
  apply in_map_iff. exists c. split; [reflexivity | exact Hc].
Qed.

Lemma tx_fresh_notin : forall ly2 S2 (W2 : world SEGS) mem2 md2 bl b,
  AR SEGS B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = bl ++ [b] -> ~ In b bl.
Proof.
  intros ly2 S2 W2 mem2 md2 bl b HAR Hbl Hin.
  pose proof (tx_fresh_apart ly2 S2 W2 mem2 md2 bl b HAR Hbl b Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. unfold req_size in D. destruct (snd b =? 0) eqn:E;
    [lia | apply Z.eqb_neq in E].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst b) (snd b) HAR ltac:(rewrite Hbl; apply in_or_app; right; left;
    destruct b; reflexivity)) as (_ & _ & _ & _ & _ & _ & Hn). lia.
Qed.

Lemma lf_text_of_after : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 (ms3 : machine_state) md3
    (regs : bvmap 5 word) P N o ly2 S2 W2 regs2 mem2 md2 (ms2 : machine_state) mo',
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_P) = Some P ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_N) = Some N ->
  (exists q, 0 <= q <= c_n cx /\ P = c_p cx + q /\ N = c_n cx - q) ->
  (o = LS_T128 \/ o = LS_T130) ->
  spZ regs = lf_sp1 cx -> aarg regs 0 = lf_sp1 cx + LS_P -> aarg regs 1 = lf_sp1 cx + o ->
  ms_mem ms2 = mem2 ->
  JRN cx fp ly2 S2 W2 mem2 md2 (k + 1) -> frames S2 = frames S3 ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (spZ regs - TEXT_OF_AK) (spZ regs)
    (fun a => inFP (text_of_awr regs (rdW W3 (ms_mem ms3))) a) ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 ->
  text_of_ledpost B S3 S2 ->
  text_of_apostA SEGS PCAP_RLO PCAP_RHI B regs (rdW W3 (ms_mem ms3)) regs2 (rdW W2 mem2)
    (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  exists own1 s t adv nb,
    getr regs2 10 = w64 s /\ s <> 0 /\
    ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ own) (ev + 1) mo' (S wl) (lv + TEXT_OF_LIVE) (k + 1)
      ly2 S2 W2 ms2 md2 /\
    arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) /\
    rdword (aview SEGS (w_H W2) mem2) (lf_sp1 cx + LS_P) = Some (P + adv) /\
    rdword (aview SEGS (w_H W2) mem2) (lf_sp1 cx + LS_N) = Some (N - adv) /\
    (exists q, 0 <= q <= c_n cx /\ P + adv = c_p cx + q /\ N - adv = c_n cx - q) /\
    rdword (aview SEGS (w_H W2) mem2) (lf_sp1 cx + o) = Some own1 /\
    tx_nb own1 nb /\
    (own1 = 0 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) /\
    (own1 <> 0 -> ablocks B ly2 S2 = ablocks B ly3 S3 ++ nb /\ own1 = s) /\
    (forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2)) /\
    (forall c b, In c (ablocks B ly3 S3) -> In b nb -> zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) /\
    lf_call B cx TEXT_OF_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2
      (fun a => inFP (text_of_awr regs (rdW W3 (ms_mem ms3))) a) /\
    dec_ans B ly2 S2 (rdW W2 mem2) s t /\ tx_ans B SEGS own1 nb ly2 S2 (rdW W2 mem2) s t.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 regs P N o ly2 S2 W2 regs2 mem2 md2 ms2 mo'
    HB HJ HC HP HN (q & Hq & EP & EN) Ho Hsp Ha0 Ha1 Hms2 HJ2 Hfr2 Hfd Hfs HK HSH HLED HPA.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & _). unfold LF_MFRAME in R. exact R. }
  unfold LLVMF_STK in *.
  pose proof HC as (_ & HFR & _ & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (Hkev & Hbb & Hfa & _ & _ & _ & _ & Hwl & _ & _ & Hbl & Hinc & _ & Hro & _).
  pose proof HBLK as (Hmd & Hmk & _).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HP) as RP.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HN) as RN.
  destruct (HPA P N ltac:(rewrite Ha0; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HP))
    ltac:(rewrite Ha0; replace (lf_sp1 cx + LS_P + 8) with (lf_sp1 cx + LS_N) by (unfold LS_P, LS_N; lia);
          exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HN)) RP RN)
    as (own1 & s & t & Hs10 & Hs0 & Hcs & Hlen & Hslot & Hown1r & (adv & Hadv & Hc0 & Hc1 & _) & H0 & H1).
  (* the block list after the call *)
  assert (HBL : exists nb, tx_nb own1 nb /\
      (own1 = 0 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) /\
      (own1 <> 0 -> ablocks B ly2 S2 = ablocks B ly3 S3 ++ nb /\ own1 = s)).
  { destruct (Z.eq_dec own1 0) as [E | E].
    - exists []. split; [left; split; [exact E | reflexivity]|].
      split; [intros _; exact (proj1 (H0 E)) | intros E'; contradiction].
    - destruct (H1 E) as (Es & H4096 & k1 & Hk1 & Hk1t & Hbl2). exists [(own1, k1)].
      split; [right; exists k1; split; [exact E|]; split; [exact H4096|]; split; [lia | reflexivity]|].
      split; [intros E'; contradiction | intros _; split; [exact Hbl2 | exact Es]]. }
  destruct HBL as (nb & Hnb & Hnb0 & Hnb1).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2)).
  { intros c Hc. destruct (Z.eq_dec own1 0) as [E | E].
    - exact (Permutation_in c (Permutation_sym (Hnb0 E)) Hc).
    - rewrite (proj1 (Hnb1 E)). apply in_or_app. left. exact Hc. }
  assert (Hapart : forall c b, In c (ablocks B ly3 S3) -> In b nb ->
            zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))).
  { intros c b Hc Hb. destruct Hnb as [(_ & ->) | (k1 & E & _ & _ & ->)]; [destruct Hb|].
    destruct Hb as [<- | []].
    exact (tx_fresh_apart ly2 S2 W2 mem2 md2 (ablocks B ly3 S3) (own1, k1) HAR2 (proj1 (Hnb1 E)) c Hc). }
  (* the write set: the cursor and the out slot, on the real frame above the slots *)
  assert (HEw : forall a, inFP (text_of_awr regs (rdW W3 (ms_mem ms3))) a ->
             lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_T130 + 8).
  { intros a (r & Hr & Hra). unfold text_of_awr in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; rewrite ?Ha0, ?Ha1 in Hra;
      unfold LS_P, LS_T128, LS_T130 in *; lia. }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  assert (HCALL : lf_call B cx TEXT_OF_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2)
                    (fun a => inFP (text_of_awr regs (rdW W3 (ms_mem ms3))) a)).
  { rewrite Hms2. unfold lf_call. rewrite Hsp in HK. split; [unfold TEXT_OF_AK, TEXT_OF_AFRAME, ASTACK; lia|].
    split; [unfold TEXT_OF_AK, TEXT_OF_AFRAME, ASTACK; lia|]. split; [exact HK | exact HSH]. }
  (* the live bytes after the call *)
  assert (Hbb2 : blocks_bytes S2 <= blocks_bytes (c_S cx) + (lv + TEXT_OF_LIVE)).
  { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly3 S3) in *.
    destruct (Z.eq_dec own1 0) as [E | E].
    - rewrite (bsum_perm _ _ (Hnb0 E)). unfold TEXT_OF_LIVE. lia.
    - rewrite (proj1 (Hnb1 E)), bsum_app. destruct Hnb as [(E' & _) | (k1 & _ & _ & Hk1 & ->)]; [contradiction|].
      cbn [bsum fold_right fst snd]. unfold bsum in *. cbn. unfold TEXT_OF_LIVE in *. lia. }
  assert (Hwl2 : (length (wild_part (as_universe B) (st_depot S2)) <=
                  length (wild_part (as_universe B) (st_depot (c_S cx))) + S wl)%nat)
    by (unfold text_of_ledpost in HLED; lia).
  assert (Hbl2 : lf_bl B cx (nb ++ own) T3 ly2 S2).
  { destruct (Z.eq_dec own1 0) as [E | E].
    - destruct Hnb as [(_ & ->) | (k1 & E' & _)]; [|contradiction]. cbn [app].
      exact (lf_bl_perm B cx own T3 ly3 S3 ly2 S2 Hbl (Hnb0 E)).
    - destruct Hnb as [(E' & _) | (k1 & _ & _ & _ & Hnbe)]; [contradiction|]. rewrite Hnbe in *. cbn [app].
      exact (lf_bl_cons B cx own T3 ly3 S3 ly2 S2 (own1, k1) Hbl (proj1 (Hnb1 E))). }
  destruct (ak_cut_callee SK B MT MS la_nul LAWS MT_LE HSEGS TB cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
    ms3 md3 (nb ++ own) (ev + 1) mo' (S wl) (lv + TEXT_OF_LIVE) (k + 1) ly2 S2 W2 ms2 md2 TEXT_OF_AK
    (fun a => inFP (text_of_awr regs (rdW W3 (ms_mem ms3))) a) HMSE HLAN HPB HC
    ltac:(rewrite Hms2; exact HJ2) Hfr2 ltac:(rewrite Hms2; exact HAR2) HCALL)
    as (HC2 & HRO2).
  - intros a HEa Hfp.
    destruct (ak_cut_fp_place SK B MT MS la_nul LAWS HSEGS TB cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
      ms3 md3 HMSE HLAN HPB HAR3 HC a Hfp) as [Hlo | [Hsl | Hsv]];
      pose proof (HEw a HEa) as Ha; unfold lf_slots_fp, lf_saved_fp, AMF_BLOCK, LS_P, LS_T130 in *; lia.
  - intros a HEa Hro'. pose proof (HEw a HEa) as Ha. pose proof (in_roP_low a Hro') as L.
    unfold LS_P, LS_T130, kLowMemEnd in *. lia.
  - exact Hfd.
  - exact Hfs.
  - exact (Hsub _ Hmd).
  - exact (Hsub _ Hmk).
  - lia.
  - exact Hbb2.
  - exact Hwl2.
  - exact Hbl2.
  - intros c Hc. exact (Hsub c (Hinc c Hc)).
  - exists own1, s, t, adv, nb.
    rewrite Hms2 in HRO2.
    split; [exact Hs10|]. split; [exact Hs0|]. split; [exact HC2|]. split; [exact HRO2|].
    rewrite Ha0 in Hc0, Hc1. rewrite Ha1 in Hslot.
    assert (Hpbnd : c_p cx + c_n cx <= alloc_ceiling).
    { pose proof HPRE as (_ & _ & _ & _ & Hpn & _).
      destruct Hpn as [(Hn0 & Hpe) | (Hnp & _)].
      - unfold c_n in *. rewrite Hn0, Hpe. unfold A_EMPTY. lia.
      - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (HPB ltac:(unfold c_n in *; lia))) as (_ & _ & Hc & _).
        unfold req_size in Hc. destruct (c_n cx =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]. }
    split; [exact (rdword_of_val_mem SEGS (w_H W2) mem2 _ _ Hc0 ltac:(lia))|].
    split; [replace (lf_sp1 cx + LS_N) with (lf_sp1 cx + LS_P + 8) by (unfold LS_P, LS_N; lia);
            exact (rdword_of_val_mem SEGS (w_H W2) mem2 _ _ Hc1 ltac:(lia))|].
    split; [exists (q + adv); lia|].
    split; [exact (rdword_of_val_mem SEGS (w_H W2) mem2 _ _ Hslot Hown1r)|].
    split; [exact Hnb|]. split; [exact Hnb0|]. split; [exact Hnb1|]. split; [exact Hsub|]. split; [exact Hapart|].
    split; [rewrite <- Hms2; exact HCALL|].
    split.
    { apply (dec_of_text_of B TB HSEGS W3 (ms_mem ms3) W2 mem2 ly2 S2 (ablocks B ly3 S3) s t own1 Hro HRO2 Hs0
        Hcs Hlen).
      + intros E. destruct (H0 E) as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi | exact Hr].
      + intros E. destruct (H1 E) as (Es & H4096 & k1 & Hk1 & Hk1t & Hbl2'). split; [exact Es|]. split; [exact H4096|].
        exists k1. split; [exact Hk1|]. split; [exact Hk1t | exact Hbl2']. }
    destruct (Z.eq_dec own1 0) as [E | E].
    + left. split; [exact E|].
      split; [destruct Hnb as [(_ & ->) | (k1 & E' & _)]; [reflexivity | contradiction]|].
      destruct (H0 E) as (_ & Hw & _).
      exact (dec_l_of_text_of B TB HSEGS W3 (ms_mem ms3) W2 mem2 s t Hro HRO2 Hcs Hw).
    + right. destruct (H1 E) as (Es & H4096 & k1 & Hk1 & Hk1t & Hbl2'). exists k1.
      split; [exact E|]. split; [symmetry; exact Es|].
      split; [destruct Hnb as [(E' & _) | (k2 & _ & _ & _ & Hnbe)]; [contradiction|];
              rewrite (proj1 (Hnb1 E)) in Hbl2'; rewrite Hnbe in Hbl2'; apply app_inv_head in Hbl2';
              injection Hbl2' as <-; exact Hnbe|].
      split; [rewrite Hbl2'; apply in_or_app; right; left; reflexivity|].
      split; [unfold TEXT_OF_LIVE in *; lia | exact Hcs].
Qed.

(* ==========================================================================
   An aleaf callee (no allocator) with its write set on the real frame above the slots, or none
   ========================================================================== *)
Lemma lf_leaf_after : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 (ms3 : machine_state) md3
    K (E : Z -> Prop) ly2 S2 W2 (ms2 : machine_state) md2 k',
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  0 <= K <= LLVMF_STK - 448 ->
  (forall a, E a -> lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_T130 + 8) ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k' -> k' <= ev -> frames S2 = frames S3 ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms2) (lf_sp1 cx - K) (lf_sp1 cx) E ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k' ly2 S2 W2 ms2 md2 /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)) /\
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 K E ly2 S2 W2 ms2 md2 k'
    HB HJ HC HK HE HJ2 Hk' Hfr2 Hfd Hfs HKP HSH HS2 HP.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    (ms_mem ms2) md2 k' HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & _). unfold LF_MFRAME in R. exact R. }
  unfold LLVMF_STK in *.
  pose proof HC as (_ & _ & _ & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (_ & Hbb & _ & _ & _ & _ & _ & Hwl & _ & _ & Hbl & Hinc & _).
  pose proof HBLK as (Hmd & Hmk & _).
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  assert (HCALL : lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E)
    by (split; [lia|]; split; [lia|]; split; [exact HKP | exact HSH]).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in c (Permutation_sym HP) Hc)).
  destruct (ak_cut_callee SK B MT MS la_nul LAWS MT_LE HSEGS TB cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
    ms3 md3 own ev mo wl lv k' ly2 S2 W2 ms2 md2 K E HMSE HLAN HPB HC HJ2 Hfr2 HAR2 HCALL) as (HC2 & HRO2).
  - intros a HEa Hfp.
    destruct (ak_cut_fp_place SK B MT MS la_nul LAWS HSEGS TB cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
      ms3 md3 HMSE HLAN HPB HAR3 HC a Hfp) as [Hlo | [Hsl | Hsv]];
      pose proof (HE a HEa) as Ha; unfold lf_slots_fp, lf_saved_fp, AMF_BLOCK, LS_P, LS_T130 in *; lia.
  - intros a HEa Hro'. pose proof (HE a HEa) as Ha. pose proof (in_roP_low a Hro') as L.
    unfold LS_P, LS_T130, kLowMemEnd in *. lia.
  - exact Hfd.
  - exact Hfs.
  - exact (Hsub _ Hmd).
  - exact (Hsub _ Hmk).
  - exact Hk'.
  - rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP), <- (blocks_bytes_bsum B ly3 S3). exact Hbb.
  - rewrite HS2. exact Hwl.
  - exact (lf_bl_perm B cx own T3 ly3 S3 ly2 S2 Hbl HP).
  - intros c Hc. exact (Hsub c (Hinc c Hc)).
  - split; [exact HC2|]. split; [exact HRO2 | exact HCALL].
Qed.

(* ==========================================================================
   The frees of the body's own text blocks
   ========================================================================== *)
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

Lemma la_slack_img_b : forallb (fun a => existsb (fun s => (Z.of_N (seg_base s) <=? a) &&
    (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) [LA_LONG_ALIAS + 301; LA_LONG_ALIAS + 302;
    LA_LONG_ALIAS + 303] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma la_slack_img : forall a, LA_LONG_ALIAS + 301 <= a < LA_LONG_ALIAS + 304 -> in_img SEGS a.
Proof.
  intros a Ha. rewrite HSEGS. pose proof la_slack_img_b as K. rewrite forallb_forall in K.
  assert (Hin : In a [LA_LONG_ALIAS + 301; LA_LONG_ALIAS + 302; LA_LONG_ALIAS + 303]).
  { assert (a = LA_LONG_ALIAS + 301 \/ a = LA_LONG_ALIAS + 302 \/ a = LA_LONG_ALIAS + 303) as [-> | [-> | ->]] by lia;
      cbn; tauto. }
  specialize (K a Hin). apply existsb_exists in K as (s & Hs & Hk).
  apply andb_prop in Hk as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists s. split; [exact Hs | lia].
Qed.

(* the bytes of a heap block apart from the call's two blocks, its FILE block and its input miss the cut's
   footprint *)
Lemma ak_cut_fp_not_blk : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W (ms : machine_state) mdl b,
  MS = link_amf -> la_nul = LA_NUL -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S)) ->
  AR SEGS B ly S W (ms_mem ms) mdl ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl ->
  In b (ablocks B ly S) ->
  (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
     zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) ->
  forall a, fst b <= a < fst b + req_size (snd b) -> ~ lf_cut_fp MS la_nul cx fp md mk T3 a.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl [p n] HMS HLA HPB HAR
    (HJ & Hfr & _ & _ & _ & _ & Hjbk & Hblk & _) Hb HD a Ha Hfp.
  cbn [fst snd] in *.
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLA) as (HIMG & HREL).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (H16 & H4096 & Hc & Happ & _ & _ & Hn).
  destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR ltac:(left; exists p, n; split; [exact Hb | lia])) as (_ & Hni).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _).
  pose proof HJ as Hrow. eapply ajournal_gx_row in Hrow. destruct Hrow as (Hc0 & H47 & Hlo & Hhi).
  assert (Hs1 : spZ (c_regs cx) - 416 - 31 <= lf_sp1 cx).
  { unfold lf_sp1, lf_sp1_of, LF_MFRAME.
    pose proof (Z.div_mod (spZ (c_regs cx) - 416) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 416) 32 ltac:(lia)).
    lia. }
  unfold LLVMF_STK in Hlo. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  assert (GAP : forall x, 0x7fff7000 <= x < 0x10007fff8000 -> ~ (p <= x < p + req_size n)) by lia.
  assert (IMG : forall x, lf_img_fp MS la_nul x -> x <> a) by (intros x Hx ->; exact (Hni (proj1 (HIMG a Hx)))).
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> in_img SEGS x).
  { intros x [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HREL x Hr)]. }
  assert (DJ : forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
                 ~ (fst c <= a < fst c + req_size (snd c))).
  { intros c Hc' Hac. pose proof (HD c Hc') as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
  unfold lf_cut_fp in Hfp.
  destruct Hfp as [Hf | [Hf | [Hf | [Hf | [Hf | [Hf | Hf]]]]]].
  - unfold lf_saved_fp in Hf. lia.
  - unfold lf_header_fp in Hf. pose proof LF_frame_slot as (FB & _).
    destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (HP & _).
    pose proof (pairwise_In zdisjoint _ (p, req_size n) (frame_addr ly LF_CID fp, fs_frame_bytes LF_CID) _ _ eq_refl HP
      ltac:(apply in_map_iff; exists (p, n); split; [reflexivity | exact Hb])
      ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | rewrite Hfr; left; reflexivity])) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold lf_F in Hf. rewrite <- (Hfa LF_CID fp) in Hf. rewrite FB in *.
    destruct Hf as [Hf | Hf]; lia.
  - unfold lf_fshadow_fp, lf_SH, shadow_of_addr, SHADOW_OFF in Hf.
    destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HS). rewrite Forall_forall in HS.
    pose proof (HS (LF_CID, fp) ltac:(rewrite Hfr; left; reflexivity)) as (F1 & F2). cbn [fst snd] in F1, F2.
    unfold lf_F in Hf. rewrite <- (Hfa LF_CID fp) in Hf. apply (GAP a); [|lia].
    pose proof (Z.div_le_mono (frame_addr ly LF_CID fp) alloc_ceiling 8 ltac:(lia) ltac:(pose proof LF_frame_slot as (FB & _); lia)).
    lia.
  - unfold lf_slots_fp in Hf. lia.
  - unfold lf_jbk_fp in Hf.
    destruct Hf as [[Hf | [Hf | (f & m & Hin & Hf)]] | [Hf | [Hf | Hf]]].
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + destruct Hgi as [(_ & ->) | (f0 & _ & -> & _)]; [destruct Hin|].
      destruct Hin as [E | []]. injection E as <- <-.
      apply (DJ (f0, AMF_BLOCK) ltac:(right; right; left; left; reflexivity)). cbn [fst snd].
      unfold req_size, AMF_BLOCK in *. cbn. lia.
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + exact (Hni (RO a Hf)).
    + apply (DJ (c_p cx, c_n cx) ltac:(right; right; right; split; [lia | reflexivity])). cbn [fst snd].
      unfold req_size. destruct (c_n cx =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
  - unfold lf_blocks_fp in Hf. pose proof Hblk as (Hmd & Hmk & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmd) as (_ & Hd4 & Hcd & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmk) as (_ & Hk4 & Hck & _).
    unfold req_size, MD_SIZE, MK_SIZE in Hcd, Hck. cbn in Hcd, Hck.
    destruct Hf as [(x & Hx & Ex) | (x & Hx & Ex)]; subst a;
      (apply (GAP (shadow_of_addr SHADOW_OFF x)); [|exact Ha]);
      unfold shadow_of_addr, SHADOW_OFF, MD_SIZE, MK_SIZE in *; lia.
  - unfold lf_data_fp in Hf.
    destruct Hf as [Hf | [Hf | [Hf | [Hf | [Hf | Hf]]]]].
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + exact (IMG a ltac:(unfold lf_img_fp; tauto) eq_refl).
    + destruct (Z_lt_le_dec a (LA_LONG_ALIAS + 301)) as [L | L].
      * exact (IMG a ltac:(unfold lf_img_fp; right; right; left; lia) eq_refl).
      * exact (Hni (la_slack_img a ltac:(lia))).
    + apply (DJ (md, MD_SIZE) ltac:(left; reflexivity)). cbn [fst snd]. unfold req_size, MD_SIZE in *. cbn. lia.
    + apply (DJ (mk, MK_SIZE) ltac:(right; left; reflexivity)). cbn [fst snd]. unfold req_size, MK_SIZE in *. cbn. lia.
    + exact (Hni (RO a Hf)).
Qed.

Lemma in_remove1 : forall (c b : Z * Z) l1 l2, In c (l1 ++ b :: l2) -> c <> b -> In c (l1 ++ l2).
Proof.
  intros c b l1 l2 H Hne. apply in_app_iff in H as [H | [H | H]]; apply in_app_iff;
    [left; exact H | congruence | right; exact H].
Qed.

Lemma zdisjoint_self_ne : forall c b : Z * Z, 1 <= req_size (snd b) ->
  zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)) -> c <> b.
Proof. intros c b H D E. subst c. unfold zdisjoint in D. cbn [fst snd] in D. lia. Qed.

(* a free at a site of LLVMFuzzerTestOneInput of one of its own blocks b, other than its two blocks, its FILE
   block and its input: the rule applied (Free.v aj_gx_free_w at the instance hypothesis AFREE4W) and the cut
   carried to the return with b out of the own list *)
Lemma lf_free_blk_step : forall (fy : YK11.FPState) cx fp md mk kbs mbs gbs T3 o1 b o2 ev mo wl lv k ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (o1 ++ b :: o2) ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  In b (ablocks B ly3 S3) -> ~ In b (ablocks B (c_ly cx) (c_S cx)) ->
  (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
     zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 (fst b) -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     aregs_preserved regs regs2 ->
     ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (o1 ++ o2) (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
       (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ->
     arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) ->
     lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun a => fst b <= a < fst b + req_size (snd b)) ->
     (forall c, In c (ablocks B ly3 S3) -> c <> b -> In c (ablocks B ly2 S2)) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp md mk kbs mbs gbs T3 o1 [pa n] o2 ev mo wl lv k ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB HC Hb Hnb HD Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  cbn [fst snd] in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  pose proof HC as (HJ & Hfr & HSAV & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (Hkev & Hbb & Hfa & _ & Hfd & Hfs & _ & Hwl & _ & _ & Hbl & Hinc & _).
  pose proof HBLK as (Hmd & Hmk & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  unfold LLVMF_STK in *.
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  destruct (lf_saved_ra_s0 cx W3 ms3 HSAV) as (H8 & H16w).
  assert (Hra : raZ regs = link_text + rao)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- (lv_text LV). apply ret_ok_codeptr_v.
    - unfold LF_FREE_RAS, link_text in *. cbn in Hsite. lia.
    - unfold LF_FREE_RAS, link_text in Hsite. cbn in Hsite.
      destruct Hsite as [E | [E | [E | [E | [E | [E | [E | []]]]]]]];
        (assert (rao = 0x82e70 - 0x821cc \/ rao = 0x82e78 - 0x821cc \/ rao = 0x83758 - 0x821cc \/
                 rao = 0x83760 - 0x821cc \/ rao = 0x838dc - 0x821cc \/ rao = 0x83b8c - 0x821cc \/
                 rao = 0x83b94 - 0x821cc) as Er by lia);
        destruct Er as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity. }
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k regs HB HJ H8 H16w ltac:(lia) Hs0 Hra4) as (HCH & _).
  pose proof (lf_free_trace SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB
    LF_TRACE_FREE ltac:(rewrite Hra; exact Hsite)) as HTR.
  replace (pa_sigma LS___interceptor_trampoline_free) with (pc_wrap_free (as_code B))
    by (rewrite (lv_sigma LV), (ts_code B TB); reflexivity).
  eapply SRr_bind.
  { apply (@aj_gx_free_w fy rc SK SEGS B MT LAWS pa_segs_low (AFREE4W fy) G_HARNESS 0 [] W3 regs (ms_mem ms3)
      LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 md3 k pa n (getr regs 1) (lf_chain cx) HJ Hb R10).
    - rewrite Hsp. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D. rewrite D.
      replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. unfold LLVMF_STK, ASTACK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact HGP.
    - rewrite R4. exact HTP.
    - reflexivity.
    - exact Hret.
    - unfold EV_LIB in *. lia.
    - exact HCH.
    - exact HTR.
    - intros Hin. contradiction.
    - apply MT_OK. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & Hl1 & Hl2) & Hfr2 & HK & _ & HW & Hio).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (same_io_fds_fs md3 md2 Hio) as (Hfd2 & Hfs2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & _ & _ & _ & _ & _ & Hn).
  assert (Hr1 : 1 <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> c <> (pa, n) -> In c (ablocks B ly2 S2))
    by (intros c Hc Hne; rewrite Hl2; rewrite Hl1 in Hc; exact (in_remove1 c (pa, n) l1 l2 Hc Hne)).
  assert (HKP : akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (lf_sp1 cx - ASTACK) (lf_sp1 cx)
                  (fun a => pa <= a < pa + req_size n)).
  { rewrite <- Hsp. apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK). intros a Ha; exact Ha. }
  assert (HCALL : lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun a => pa <= a < pa + req_size n)).
  { split; [unfold ASTACK; lia|]. split; [unfold ASTACK; lia|]. split; [exact HKP|].
    exact (ashadow_kept_of_AR B LAWS ly3 S3 W3 (ms_mem ms3) md3 ly2 S2 W2 mem2 md2 HAR3 HAR2). }
  assert (Hne : forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
                  c <> (pa, n))
    by (intros c Hc; exact (zdisjoint_self_ne c (pa, n) Hr1 (HD c Hc))).
  destruct (ak_cut_callee SK B MT MS la_nul LAWS MT_LE HSEGS TB cx fp md mk kbs mbs gbs T3 (o1 ++ (pa, n) :: o2) ev mo
    wl lv k ly3 S3 W3 ms3 md3 (o1 ++ o2) (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
    (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ASTACK (fun a => pa <= a < pa + req_size n)
    HMSE HLAN HPB HC HJ2 ltac:(rewrite Hfr2; reflexivity) HAR2 HCALL) as (HC2 & HRO2).
  - intros a Ha. exact (ak_cut_fp_not_blk cx fp md mk kbs mbs gbs T3 _ ev mo wl lv k ly3 S3 W3 ms3 md3 (pa, n)
      HMSE HLAN HPB HAR3 HC Hb HD a Ha).
  - intros a Ha Hro.
    destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR3 ltac:(left; exists pa, n; split; [exact Hb | exact Ha]))
      as (_ & Hni).
    apply Hni. destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
    exact (proj2 (lf_img_facts B MS la_nul HSEGS TB HMSE HLAN) a Hr).
  - rewrite Hfd2. exact eq_refl.
  - rewrite Hfs2. exact eq_refl.
  - exact (Hsub _ Hmd (Hne _ ltac:(left; reflexivity))).
  - exact (Hsub _ Hmk (Hne _ ltac:(right; left; reflexivity))).
  - lia.
  - rewrite (blocks_bytes_bsum B ly2 S2), Hl2. rewrite (blocks_bytes_bsum B ly3 S3), Hl1 in Hbb.
    rewrite bsum_app in *. rewrite bsum_cons in Hbb. cbn [snd] in Hbb. lia.
  - lia.
  - exact (lf_bl_remove B cx o1 o2 T3 ly3 S3 ly2 S2 (pa, n) l1 l2 Hbl Hl1 Hl2).
  - intros c Hc. exact (Hsub c (Hinc c Hc) (Hne c ltac:(right; right; left; exact Hc))).
  - exact (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HRO2 HCALL Hsub).
Qed.

(* a free of NULL at a site of LLVMFuzzerTestOneInput (text_of answered with a texts string) *)
Lemma lf_free_null_step : forall (fy : YK11.FPState) cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 0 -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     aregs_preserved regs regs2 ->
     ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
       (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ->
     arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) ->
     lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun _ => False) ->
     Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB HC Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  pose proof HC as (HJ & Hfr & HSAV & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (Hkev & Hbb & Hfa & _ & Hfd & Hfs & _ & Hwl & _ & _ & Hbl & Hinc & _).
  pose proof HBLK as (Hmd & Hmk & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  unfold LLVMF_STK in *.
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  destruct (lf_saved_ra_s0 cx W3 ms3 HSAV) as (H8 & H16w).
  assert (Hra : raZ regs = link_text + rao)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold LF_FREE_RAS, link_text in *; cbn in Hsite; lia).
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- (lv_text LV). apply ret_ok_codeptr_v.
    - unfold LF_FREE_RAS, link_text in *. cbn in Hsite. lia.
    - unfold LF_FREE_RAS, link_text in Hsite. cbn in Hsite.
      destruct Hsite as [E | [E | [E | [E | [E | [E | [E | []]]]]]]];
        (assert (rao = 0x82e70 - 0x821cc \/ rao = 0x82e78 - 0x821cc \/ rao = 0x83758 - 0x821cc \/
                 rao = 0x83760 - 0x821cc \/ rao = 0x838dc - 0x821cc \/ rao = 0x83b8c - 0x821cc \/
                 rao = 0x83b94 - 0x821cc) as Er by lia);
        destruct Er as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; reflexivity. }
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k regs HB HJ H8 H16w ltac:(lia) Hs0 Hra4) as (HCH & _).
  pose proof (lf_free_trace SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB
    LF_TRACE_FREE ltac:(rewrite Hra; exact Hsite)) as HTR.
  replace (pa_sigma LS___interceptor_trampoline_free) with (pc_wrap_free (as_code B))
    by (rewrite (lv_sigma LV), (ts_code B TB); reflexivity).
  eapply SRr_bind.
  { apply (@aj_gx_free_null_w fy rc SK SEGS B MT LAWS pa_segs_low (AFREENULL4W fy) G_HARNESS 0 [] W3 regs (ms_mem ms3)
      LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 md3 k (getr regs 1) (lf_chain cx) HJ R10).
    - rewrite Hsp. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D. rewrite D.
      replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. unfold LLVMF_STK, ASTACK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact HGP.
    - rewrite R4. exact HTP.
    - reflexivity.
    - exact Hret.
    - unfold EV_LIB in *. lia.
    - exact HCH.
    - exact HTR.
    - apply MT_OK. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & HPerm & Hfr2 & HK & _ & HW & Hio).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (same_io_fds_fs md3 md2 Hio) as (Hfd2 & Hfs2).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in c (Permutation_sym HPerm) Hc)).
  assert (HKP : akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (lf_sp1 cx - ASTACK) (lf_sp1 cx) (fun _ => False)).
  { rewrite <- Hsp. apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK). intros a Ha; exact Ha. }
  assert (HCALL : lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 (fun _ => False)).
  { split; [unfold ASTACK; lia|]. split; [unfold ASTACK; lia|]. split; [exact HKP|].
    exact (ashadow_kept_of_AR B LAWS ly3 S3 W3 (ms_mem ms3) md3 ly2 S2 W2 mem2 md2 HAR3 HAR2). }
  destruct (ak_cut_callee SK B MT MS la_nul LAWS MT_LE HSEGS TB cx fp md mk kbs mbs gbs T3 own ev mo
    wl lv k ly3 S3 W3 ms3 md3 own (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
    (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ASTACK (fun _ => False)
    HMSE HLAN HPB HC HJ2 ltac:(rewrite Hfr2; reflexivity) HAR2 HCALL) as (HC2 & HRO2).
  - intros a [].
  - intros a [].
  - rewrite Hfd2. exact eq_refl.
  - rewrite Hfs2. exact eq_refl.
  - exact (Hsub _ Hmd).
  - exact (Hsub _ Hmk).
  - lia.
  - rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B ly3 S3). exact Hbb.
  - lia.
  - exact (lf_bl_perm B cx own T3 ly3 S3 ly2 S2 Hbl HPerm).
  - intros c Hc. exact (Hsub c (Hinc c Hc)).
  - exact (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HRO2 HCALL HPerm).
Qed.

(* either free of a text_of out slot: none (NULL) or the fresh block tx_nb names *)
Lemma lf_free_tx_step : forall (fy : YK11.FPState) cx fp md mk kbs mbs gbs T3 o1 nb o2 own1 ev mo wl lv k ly3 S3 W3
    (ms3 : machine_state) md3 (regs : bvmap 5 word) rao mo' (Q : world SEGS -> config -> Prop),
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (o1 ++ nb ++ o2) ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  tx_nb own1 nb ->
  (forall b, In b nb -> In b (ablocks B ly3 S3) /\ ~ In b (ablocks B (c_ly cx) (c_S cx)) /\
     (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
        zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))) ->
  k + 1 <= EV_LIB ->
  getr regs 10 = w64 own1 -> spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_FREE_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2, wle W3 W2 ->
     aregs_preserved regs regs2 ->
     ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (o1 ++ o2) (ev + 1) mo' wl lv (k + 1) ly2 S2 W2
       (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 ->
     arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) ->
     (exists E : Z -> Prop, lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E /\
        (forall a, E a -> a < alloc_ceiling)) ->
     (forall c, In c (ablocks B ly3 S3) -> ~ In c nb -> In c (ablocks B ly2 S2)) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_free)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp md mk kbs mbs gbs T3 o1 nb o2 own1 ev mo wl lv k ly3 S3 W3 ms3 md3 regs rao mo' Q
    HB HC Hnb Hblk Hk R10 Hsp Hs0 R3 R4 R1 Hsite K.
  destruct Hnb as [(-> & ->) | (k1 & Hne & H4096 & Hk1 & ->)].
  - cbn [app] in HC.
    apply (lf_free_null_step fy cx fp md mk kbs mbs gbs T3 (o1 ++ o2) ev mo wl lv k ly3 S3 W3 ms3 md3 regs rao mo' Q
      HB HC Hk R10 Hsp Hs0 R3 R4 R1 Hsite).
    intros W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HRO2 HCALL HPerm.
    apply (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HRO2).
    + exists (fun _ => False). split; [exact HCALL | intros a []].
    + intros c Hc _. exact (Permutation_in c (Permutation_sym HPerm) Hc).
  - destruct (Hblk (own1, k1) ltac:(left; reflexivity)) as (Hb & Hnb & HD).
    cbn [app] in HC.
    apply (lf_free_blk_step fy cx fp md mk kbs mbs gbs T3 o1 (own1, k1) o2 ev mo wl lv k ly3 S3 W3 ms3 md3 regs rao mo' Q
      HB HC Hb Hnb HD Hk R10 Hsp Hs0 R3 R4 R1 Hsite).
    intros W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HRO2 HCALL Hsub.
    apply (K W2 ly2 S2 regs2 mem2 md2 Hle HP HC2 HRO2).
    + exists (fun a => fst (own1, k1) <= a < fst (own1, k1) + req_size (snd (own1, k1))). split; [exact HCALL|].
      intros a Ha. pose proof HC as (HJ & _).
      destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
        (ms_mem ms3) md3 k HB HJ) as (_ & _ & _ & _ & _ & _ & HAR3).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & _ & Hc & _). cbn [fst snd] in *. lia.
    + intros c Hc Hcn. apply (Hsub c Hc). intros E. apply Hcn. left. symmetry. exact E.
Qed.

End a.
