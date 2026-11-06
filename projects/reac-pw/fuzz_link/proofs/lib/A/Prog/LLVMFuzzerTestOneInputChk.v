(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 331 of its 389 lines of code are new or changed and 1274 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the arm cut at any frame shadow, and the calls of leaf callees that write
   nothing, generic over the register file and the arm's own facts (shared; used for op_read, from the
   op_write proofs).

   Donors (lifted, not re-derived):
   - chk_cut, chk_cut_run, chk_cut_fp_place, chk_cut_callee: ArmK.v ak_cut, ak_cut_run, ak_cut_fp_place,
     ak_cut_callee, with the frame's shadow a parameter sh (112 values; ak_cut is chk_cut at LF_SH0, chk_cut_ak).
     op_read keeps two frame objects in scope across its checks, so its shadow is not LF_SH0 there.
   - chk_leaf_after: Txa.v lf_leaf_after at any sh.
   - chk_leaf0: the call of an aleaf callee with no write set and no event (check_socket, index_of,
     check_refused), as the write arms' walk makes it in op_write (Op1E.v w_as, w_lx, w_jr: ArmR.v ar_leaf_call, then
     lf_leaf_after), here with the registers and the arm's facts left to the caller.
   - chk_bne_any, chk_beq_any, chk_index_of_range, chk_val_mem1, chk_grows_of_present: Op1E.v w_bne_any,
     w_index_of_range; Op1F.v w_beq_any, w_val_mem1,
     w_grows_of_present.
   - chk_name_byte0: the first byte of a selector's name, its value and its shadow, as Op1F.v w_sl reads it
     (Nm.v lf_name_core).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputArmR
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputNm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   Small facts (Op1E.v, Op1F.v)
   ========================================================================== *)

(* the a0 test of a bnez / beqz against zero *)
Lemma chk_bne_any : forall (E : env) n,
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned (ew E n) =? 0).
Proof.
  intros E n. rewrite branch_ne_U, U_SOff, U_lit by lia. unfold zcanon, M64. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite (Z.mod_small (bv_unsigned (ew E n))) by lia. rewrite ?Z.mod_0_l by lia. reflexivity.
Qed.

Lemma chk_beq_any : forall (E : env) n,
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned (ew E n) =? 0).
Proof.
  intros E n. rewrite branch_eq_U, U_SOff, U_lit by lia. unfold zcanon, M64. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite (Z.mod_small (bv_unsigned (ew E n))) by lia. reflexivity.
Qed.

(* index_of answers a table index *)
Lemma chk_tab_ix : forallb (fun e => (0 <=? snd e) && (snd e <? 2 ^ 31)) lf_tab = true.
Proof. vm_compute. reflexivity. Qed.
Lemma chk_index_of_range : forall x, 0 <= index_of lf_tab x < 2 ^ 31.
Proof.
  assert (H : forall tab, forallb (fun e => (0 <=? snd e) && (snd e <? 2 ^ 31)) tab = true ->
    forall x, 0 <= index_of tab x < 2 ^ 31).
  { intros tab. induction tab as [|[n ix] tab IH]; intros Hf x; cbn [index_of]; [lia|].
    cbn [forallb snd] in Hf. apply andb_prop in Hf as [Hh Hf]. apply andb_prop in Hh as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. destruct (bl_eqb n x); [lia | exact (IH Hf x)]. }
  exact (H lf_tab chk_tab_ix).
Qed.

(* presence growth as a mem_grows *)
Lemma chk_grows_of_present : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in Hx |- *. destruct (H x) eqn:Eh; [exact Hx|].
  destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Ha : apresent H m (bv_unsigned x))
    by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Eh | exists b; exact Em]).
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma chk_val_mem1 : forall segs m a b, mbyte segs m a = Some b -> val_mem segs m a 1 (bv_unsigned b).
Proof.
  intros segs m a b Hb k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

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
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.

#[local] Abbreviation BASEF cx :=
  (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* ==========================================================================
   The cut at any frame shadow
   ========================================================================== *)

Definition chk_cut (cx : lcx) (fp md mk : Z) (kbs mbs gbs : list byte) (T3 own : list (Z * Z))
    (ev mo : Z) (wl : nat) (lv k : Z) (sh : list Z) (ly : alayout) (S : astate) (W : world SEGS)
    (ms : machine_state) (mdl : Model) : Prop :=
  JRN cx fp ly S W (ms_mem ms) mdl k /\ frames S = [(LF_CID, fp)] /\
  lf_saved cx W ms /\ lf_header cx fp W ms /\ lf_fshadow cx fp W ms sh /\ lf_slots cx md mk fp W ms /\
  lf_jbk B MT MS la_nul cx fp k ev mo wl lv ly S W ms mdl T3 own /\
  lf_blocks B cx md mk T3 ly S (rdW W (ms_mem ms)) /\
  lf_data cx md mk kbs mbs gbs (rdW W (ms_mem ms)).

Lemma chk_cut_ak : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl,
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly S W ms mdl <->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k LF_SH0 ly S W ms mdl.
Proof. intros. reflexivity. Qed.

(* a register-only stretch (ArmK.v ak_cut_run) *)
Lemma chk_cut_run : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms ms' mdl mdl',
  (length sh = 112)%nat ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms mdl ->
  JRN cx fp ly S W (ms_mem ms') mdl' k ->
  kagree SEGS (fun _ => False) (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  mem_grows (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  m_fds mdl' = m_fds mdl -> m_fs mdl' = m_fs mdl ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms' mdl'.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms ms' mdl mdl' Hl
    (_ & Hfr & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat) HJ' KA GA Fd Fs.
  destruct (lf_cut_keep_sh B MT MS la_nul (fun _ => False) cx fp k ev mo wl lv md mk kbs mbs gbs T3 own ly S W ms
    mdl W ms' mdl' sh KA (wcarry_on_grows _ _ _ GA) Fd Fs (fun a _ H => H) Hl Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  repeat (split; [eassumption|]). exact Hdat'.
Qed.

(* where a cut's bytes lie (ArmK.v ak_cut_fp_place) *)
Lemma chk_cut_fp_place : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms mdl,
  MS = link_amf -> la_nul = LA_NUL -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly S)) ->
  AR SEGS B ly S W (ms_mem ms) mdl ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms mdl ->
  forall a, lf_cut_fp MS la_nul cx fp md mk T3 a ->
    a < alloc_ceiling + AMF_BLOCK \/ lf_slots_fp cx a \/ lf_saved_fp cx a.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly S W ms mdl HMS HLA HPB HAR
    (_ & Hfr & _ & _ & _ & _ & Hjbk & Hblk & _) a Ha.
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLA) as (HIMG & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & Hinc & _).
  pose proof Hblk as (Hmd & Hmk & _).
  assert (IMG : forall x, lf_img_fp MS la_nul x -> x < kLowMemEnd).
  { intros x Hx. destruct (HIMG x Hx) as (Hi & _). pose proof (pa_segs_low x Hi). lia. }
  assert (BLK : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + Z.max n AMF_BLOCK ->
                  x < alloc_ceiling + AMF_BLOCK).
  { intros p n x Hin Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hn).
    unfold req_size in Hc. destruct (n =? 0) eqn:E; unfold AMF_BLOCK in *; lia. }
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> x < kLowMemEnd)
    by (intros x Hx; exact (proj2 (in_roP_low x Hx))).
  assert (SH : forall x, 0 <= x < alloc_ceiling -> shadow_of_addr SHADOW_OFF x < alloc_ceiling)
    by (intros x Hx; unfold shadow_of_addr, SHADOW_OFF; lia).
  assert (Hmdb : md + MD_SIZE <= alloc_ceiling /\ 0 <= md).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmd) as (_ & H4 & Hc & _). unfold req_size, MD_SIZE in *.
    cbn in Hc. lia. }
  assert (Hmkb : mk + MK_SIZE <= alloc_ceiling /\ 0 <= mk).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hmk) as (_ & H4 & Hc & _). unfold req_size, MK_SIZE in *.
    cbn in Hc. lia. }
  assert (HF : lf_F cx fp + fs_frame_bytes LF_CID <= alloc_ceiling /\ 4096 <= lf_F cx fp).
  { destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HS).
    rewrite Forall_forall in HS. pose proof (HS (LF_CID, fp) ltac:(rewrite Hfr; left; reflexivity)) as (H1 & H2).
    cbn [fst snd] in H1, H2. unfold lf_F. rewrite <- (Hfa LF_CID fp). split; [exact H2 | exact H1]. }
  pose proof LF_frame_slot as (FB & _).
  assert (HAMF : AMF_BLOCK = 1304) by reflexivity.
  unfold lf_cut_fp in Ha.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]].
  - right; right; exact Ha.
  - left. unfold lf_header_fp in Ha. rewrite FB in *. destruct Ha as [Ha | Ha]; lia.
  - left. unfold lf_fshadow_fp, lf_SH in Ha. rewrite FB in *. pose proof (SH (lf_F cx fp) ltac:(lia)).
    unfold shadow_of_addr in *. lia.
  - right; left; exact Ha.
  - left. unfold lf_jbk_fp in Ha.
    destruct Ha as [[Ha | [Ha | (f & n & Hin & Hf)]] | [Ha | [Ha | Ha]]].
    + pose proof (IMG a ltac:(unfold lf_img_fp; tauto)). lia.
    + pose proof (IMG a ltac:(unfold lf_img_fp; tauto)). lia.
    + apply (BLK f n a (Hinc _ Hin)). lia.
    + pose proof (IMG a ltac:(unfold lf_img_fp; tauto)). lia.
    + pose proof (RO a Ha). lia.
    + apply (BLK (c_p cx) (c_n cx) a (HPB ltac:(lia))). lia.
  - left. unfold lf_blocks_fp in Ha.
    destruct Ha as [(x & Hx & ->) | (x & Hx & ->)]; pose proof (SH x ltac:(lia)); lia.
  - left. unfold lf_data_fp in Ha.
    destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]];
      try (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS, kLowMemEnd in *; lia).
    pose proof (RO a Ha). lia.
Qed.

(* the cut across a callee (ArmK.v ak_cut_callee), at any frame shadow *)
Lemma chk_cut_callee : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3
    own' ev' mo' wl' lv' k' ly2 S2 W2 ms2 md2 K (E : Z -> Prop),
  MS = link_amf -> la_nul = LA_NUL -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  (length sh = 112)%nat ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k' -> frames S2 = frames S3 ->
  AR SEGS B ly2 S2 W2 (ms_mem ms2) md2 ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> ~ lf_cut_fp MS la_nul cx fp md mk T3 a) ->
  (forall a, E a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  k' <= ev' -> blocks_bytes S2 <= blocks_bytes (c_S cx) + lv' ->
  (length (wild_part (as_universe B) (st_depot S2)) <=
     length (wild_part (as_universe B) (st_depot (c_S cx))) + wl')%nat ->
  lf_bl B cx own' T3 ly2 S2 -> incl T3 (ablocks B ly2 S2) ->
  chk_cut cx fp md mk kbs mbs gbs T3 own' ev' mo' wl' lv' k' sh ly2 S2 W2 ms2 md2 /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 own' ev' mo' wl' lv' k' ly2 S2 W2 ms2 md2
    K E HMS HLA HPB Hl (HJ & Hfr & Hsv & Hhd & Hfs & Hsl & Hjbk & Hblk & Hdat) HJ2 Hfr2 HAR2 HC HE HEro Hfd Hfs2
    Hmd2 Hmk2 Hk' Hbb Hwl Hbl Hinc.
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLA) as (HIMG & HREL).
  pose proof Hjbk as (_ & _ & Hfa & _).
  pose proof Hblk as (Hmd3 & Hmk3 & _).
  assert (HinF : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (HX : forall a, E a -> ~ (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/
     lf_slots_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a))
    by exact HE.
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2))).
  { pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
    exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E HREL HC
      (fun a Hr He => HEro a He Hr) Hro). }
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  pose proof (lf_la_slack_any HSEGS (rdW W2 (ms_mem ms2))) as Hsl2.
  pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hla3 & _).
  pose proof (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E HIMG HC
    ltac:(intros HEa; apply (HX _ HEa); right; right; right; right; left; unfold lf_jbk_fp; right; left; lia) Hla3)
    as Hla2.
  split; [|exact HRO2].
  split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|].
  split; [exact (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC
                   ltac:(intros a Ha HEa; apply (HX a HEa); left; exact Ha) Hsv)|].
  split; [exact (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HC HinF Hfa
                   ltac:(intros a Ha HEa; apply (HX a HEa); right; left; exact Ha) Hhd)|].
  split; [exact (lf_fshadow_callee_sh B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E sh HC HinF Hfa Hl
                   ltac:(intros a Ha HEa; apply (HX a HEa); right; right; left; exact Ha) Hfs)|].
  split; [exact (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp HC
                   ltac:(intros a Ha HEa; apply (HX a HEa); right; right; right; left; exact Ha) Hsl)|].
  split.
  { apply (lf_jbk_restate B MT MS la_nul MT_LE cx fp k ev mo wl lv ly3 S3 T3 own k' ev' mo' wl' lv' ly2 S2 W2 ms2 md2 own');
      try assumption.
    - apply (lf_jbk_callee B MT MS la_nul cx fp k ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E HIMG HREL HC).
      + intros a Ha HEa. apply (HX a HEa). right; right; right; right; left. unfold lf_jbk_fp, lf_jbk_fp_c in *.
        destruct Ha as [Ha | Ha]; [left; exact Ha | right; right; right; exact Ha].
      + exact (fun a Hr He => HEro a He Hr).
      + exact HPB.
      + exact Hfd.
      + exact Hfs2.
      + exact Hla2.
      + exact Hjbk.
    - intros c q. exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ2)). }
  split.
  { apply (lf_blocks_restate B cx md mk T3 ly3 S3 ly2 S2 _ ltac:(exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3
      (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 HC Hmd2 Hmk2 Hblk)) Hmd2 Hmk2). }
  apply (lf_data_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk kbs mbs gbs HIMG HC
    Hmd3 Hmk3 (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 _ md mk HAR2 Hmd2 Hmk2)).
  - intros a Ha HEa. apply (HX a HEa). right; right; right; right; right; right.
    unfold lf_data_fp_ro, lf_data_fp in *.
    destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]; [tauto | tauto | | tauto | tauto |].
    + right; right; left. lia.
    + right; right; right; right; right. right. unfold LA_ODD, PCAP_RLO, PCAP_RHI in *. lia.
  - exact Hodd2.
  - exact Htx2.
  - exact Hsl2.
  - exact Hdat.
Qed.

(* an aleaf callee (no allocator) with its write set on the real frame above the slots, or none (Txa.v
   lf_leaf_after), at any frame shadow *)
Lemma chk_leaf_after : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 (ms3 : machine_state) md3
    K (E : Z -> Prop) ly2 S2 W2 (ms2 : machine_state) md2 k',
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k -> (length sh = 112)%nat ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 ->
  0 <= K <= LLVMF_STK - 448 ->
  (forall a, E a -> lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_T130 + 8) ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k' -> k' <= ev -> frames S2 = frames S3 ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms2) (lf_sp1 cx - K) (lf_sp1 cx) E ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k' sh ly2 S2 W2 ms2 md2 /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)) /\
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E.
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 K E ly2 S2 W2 ms2 md2 k'
    HB HJ Hl HC HK HE HJ2 Hk' Hfr2 Hfd Hfs HKP HSH HS2 HP.
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
  destruct (chk_cut_callee cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3
    ms3 md3 own ev mo wl lv k' ly2 S2 W2 ms2 md2 K E HMSE HLAN HPB Hl HC HJ2 Hfr2 HAR2 HCALL) as (HC2 & HRO2).
  - intros a HEa Hfp.
    destruct (chk_cut_fp_place cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3
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
   The call of an aleaf callee with no write set and no event (check_socket, index_of, check_refused):
   ArmR.v ar_leaf_call, then chk_leaf_after, as Op1E.v w_as / w_lx / w_jr make it; the caller states the
   registers of the call and gets the cut, the cursor and the callee's Post at the return
   ========================================================================== *)
Lemma chk_leaf0 : forall (fy : YK11.FPState) pc K Pre Rd Wr Post,
  @aleaf_rd fy rc SK SEGS PCAP_RLO PCAP_RHI B pc K 0 [] Pre Rd Wr Post ->
  forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 (W3 : world SEGS) (ms3 : machine_state) md3 P N
    (Q : world SEGS -> config -> Prop),
  BASEF cx -> (length sh = 112)%nat ->
  chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 ->
  lf_cur cx W3 ms3 P N ->
  0 <= K <= LLVMF_STK - 448 -> k <= EV_LIB ->
  YK0s.ret_ok (getr (ms_regs ms3) 1) -> 4096 <= raZ (ms_regs ms3) ->
  getr (ms_regs ms3) 3 = w64 (as_gp B) -> getr (ms_regs ms3) 4 = w64 (as_tp B) ->
  spZ (ms_regs ms3) = lf_sp1 cx ->
  (forall a, ~ inFP (Wr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a) ->
  (forall a, Rd (ms_regs ms3) (rdW W3 (ms_mem ms3)) a -> akb SEGS B ly3 S3 (lf_sp1 cx - K) (lf_sp1 cx) a) ->
  Pre (ms_regs ms3) (rdW W3 (ms_mem ms3)) ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
     chk_cut cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly2 S2 W2
       (@mkst fy regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) md2 ->
     arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) ->
     lf_cur cx W2 (@mkst fy regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) P N ->
     aregs_preserved (ms_regs ms3) regs2 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
     lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2
       (fun a => inFP (Wr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a) ->
     Post (ms_regs ms3) (rdW W3 (ms_mem ms3)) regs2 (rdW W2 mem2) ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (@cfg_at fy SEGS pc (ms_regs ms3) (ms_mem ms3) md3) Q.
Proof.
  intros fy pc K Pre Rd Wr Post HL cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 P N Q
    HB Hl HC Hcur HK Hk Hret Hra Hgp Htp Hsp HW HR Hpre HQ.
  pose proof HC as (HJ & _ & _ & _ & _ & _ & Hjbk & _ & _).
  pose proof Hjbk as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy pc K 0 [] Pre Rd Wr Post
    HL cx fp ly3 S3 W3 (ms_mem ms3) md3 k (ms_regs ms3) Q HB HJ HRO Hret Hra Hgp Htp Hsp HK ltac:(lia) ltac:(lia)
    ltac:(apply Forall_nil) (fun a Ha => False_ind _ (HW a Ha)) (fun a Ha => False_ind _ (HW a Ha)) HR Hpre).
  intros W2 ly2 S2 regs2 mem2 md2 Hle2 HJ2 HP2 HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2 Hpost.
  rewrite Z.add_0_r in HJ2.
  set (ms2 := @mkst fy regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)).
  change mem2 with (ms_mem ms2) in HJ2, HKP2, HSK2.
  destruct (chk_leaf_after cx fp md mk kbs mbs gbs T3 own ev mo wl lv k sh ly3 S3 W3 ms3 md3 K _ ly2 S2 W2 ms2 md2 k
    HB HJ Hl HC HK (fun a Ha => False_ind _ (HW a Ha)) HJ2 Hkev HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2)
    as (HC2 & HRO2 & HCALL2).
  pose proof (lf_cur_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 _ P N HCALL2 (fun a _ H => HW a H) Hcur) as Hcur2.
  exact (HQ W2 ly2 S2 regs2 mem2 md2 HC2 HRO2 Hcur2 HP2 HPERM2 HCALL2 Hpost).
Qed.

(* ==========================================================================
   The first byte of a selector's name (Op1F.v w_sl, from Nm.v lf_name_core): its byte, its value as a 1-byte
   val_mem, zero exactly for the empty name, and its shadow addressable
   ========================================================================== *)
Lemma chk_name_byte0 : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs s x,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  w_name s (Some x) ->
  acstr_at SEGS (rdW W mem) s x /\ 4096 <= s <= 2 ^ 47 - 2 /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 1 /\
  exists c0, mbyte SEGS (rdW W mem) s = Some c0 /\ val_mem SEGS (rdW W mem) s 1 (bv_unsigned c0) /\
    0 <= bv_unsigned c0 < 256 /\ (bv_unsigned c0 = 0 <-> x = []).
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs s x HB HJ HRO HD Hnm.
  destruct (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
    cx fp ly S W mem mdl k md mk kbs mbs gbs s x HB HJ HRO HD Hnm)
    as (Ncs & Nl & Ns0 & Nam & Nra & Nhv & Ntail & Ntop & Nimg).
  pose proof Ncs as ((_ & _ & Nby) & Nnz).
  pose proof (Nby 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hb0. rewrite Z.add_0_r in Hb0.
  destruct (nth_error (x ++ [zb 0]) 0) as [c0|] eqn:Ec0; [|apply nth_error_None in Ec0; rewrite length_app in Ec0;
    cbn [length] in Ec0; lia].
  pose proof (bv_unsigned_in_range _ c0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
  split; [exact Ncs|].
  split.
  { destruct Hnm as [(_ & Hn) | [(kk & Hk & -> & _) | (j & Hj & -> & _)]]; [discriminate | unfold LA_G_NAMES; lia|].
    rewrite w_odd_ptrs. do 6 (destruct j as [|j]; [cbn; lia|]). lia. }
  split; [rewrite <- ard_aview; apply (md_ra_sub _ s (Z.of_nat (length x) + 1)); [exact Nra | lia | lia]|].
  exists c0. split; [exact Hb0|]. split; [exact (chk_val_mem1 _ _ _ _ Hb0)|]. split; [exact Rb0|].
  split.
  - intros Hc. destruct x as [|c x']; [reflexivity|]. exfalso. cbn [app nth_error] in Ec0. injection Ec0 as <-.
    apply Nnz. left. apply bv_eq. rewrite Hc. reflexivity.
  - intros ->. cbn [app nth_error] in Ec0. injection Ec0 as <-. reflexivity.
Qed.

End a.
