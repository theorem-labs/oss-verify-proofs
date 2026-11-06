(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 508 of its 558 lines of code are new or changed and 1282 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm: the loop's exit (+0x924 .. +0x938): n_mark := 0 and the
   call of reac_served_unmark_all (0x8310c) on the marks block, to the cut u_ua_inv at its return (+0x93c).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C
  LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp3T
  LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputMqPost LLVMFuzzerTestOneInputOp3U.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_all_c reac_served_mark_c
  mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh remember_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis UNMARK_ALL : forall fy : YK11.FPState,
  @reac_served_unmark_all_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* a byte of a block the operation loop holds (the model block, the marks block) lies in no footprint of the cut but
   lf_data's *)
Lemma u_blk_out : forall cx fp k2 ev mo wl lv md mk T3 own ly3 S3 (W3 : world SEGS) ms3 md3 b n a,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  ((b, n) = (md, MD_SIZE) \/ (b, n) = (mk, MK_SIZE)) -> b <= a < b + n ->
  0 <= a < 2 ^ 64 /\
  ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_fshadow_fp cx fp 112 a /\ ~ lf_slots_fp cx a /\
  ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ in_img SEGS a /\ a < alloc_ceiling.
Proof.
  intros cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 b n a HB HJ Hfr Hjbk Hblk Hbn Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
    & Bamm & Bamk).
  assert (Bin : In (b, n) (ablocks B ly3 S3) /\ ~ In (b, n) T3 /\ off_img b n /\ amem_range b n /\
                (0 < c_n cx -> apart b n (c_p cx) (c_n cx)) /\ req_size n = n /\ n <= 8856).
  { destruct Hbn as [E | E]; injection E as -> ->.
    - repeat split; try assumption; try reflexivity; unfold MD_SIZE; lia.
    - split; [exact Bmk|]. split; [exact BkT|]. split; [exact Bkt|]. split; [exact Bamk|].
      split; [exact Bpk|]. split; [reflexivity | unfold MK_SIZE; lia]. }
  destruct Bin as (Hbin & HbT & Hboff & Hbam & Hbp & Rn & Hn8).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b n HAR3 Hbin) as (_ & Bb4096 & Bbceil & _).
  rewrite Rn in Bbceil.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  pose proof (Fsep b n Hbin) as Dfm. unfold zdisjoint in Dfm. cbn [fst snd] in Dfm. rewrite Rn in Dfm.
  assert (HNI : ~ in_img SEGS a).
  { apply (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 a HAR3). left. exists b, n. split; [exact Hbin|].
    rewrite Rn. exact Ha. }
  assert (HSH : lf_SH cx fp = shadow_of_addr SHADOW_OFF (lf_F cx fp)) by reflexivity.
  assert (Sh : forall x, 4096 <= x <= alloc_ceiling ->
    kLowMemEnd + 512 <= SHADOW_OFF + x / 8 /\ SHADOW_OFF + x / 8 + 0x100000 <= kHighMemBeg).
  { intros x (Hx1 & Hx2).
    assert (D1 : 4096 / 8 <= x / 8) by (apply Z.div_le_mono; [lia | exact Hx1]).
    assert (D2 : x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; [lia | lia]).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. clear - D1 D2. lia. }
  assert (Hamb : (b + n <= 2147450879) \/ (17594333495296 <= b)).
  { unfold amem_range in Hbam. destruct Hbam as [Bl | Bh]; [left; exact Bl | right; exact (proj1 Bh)]. }
  unfold LLVMF_STK in *.
  split; [clia|].
  split; [unfold lf_saved_fp; clia|].
  split; [unfold lf_header_fp; change (fs_frame_bytes LF_CID) with 1024; try rewrite HFa; clia|].
  split; [unfold lf_fshadow_fp; rewrite HSH; unfold shadow_of_addr;
          pose proof (Sh (lf_F cx fp) ltac:(clia)); unfold kLowMemEnd, kHighMemBeg in *; clia|].
  split; [unfold lf_slots_fp; clia|]. split; [unfold lf_cur_fp; clia|].
  split.
  { intros [Hj | [Hj | [Hj | Hj]]].
    - destruct Hj as [Hj | [Hj | (f & m & Hfm & Hj)]].
      + apply HNI. apply (proj1 (IMG a ltac:(right; right; right; left; exact Hj))).
      + apply HNI. apply (proj1 (IMG a ltac:(right; right; right; right; left; exact Hj))).
      + assert (HfmT : In (f, m) (ablocks B ly3 S3)) by exact (Hinc _ Hfm).
        assert (Hne : (f, m) <> (b, n)) by (intros E; rewrite E in Hfm; exact (HbT Hfm)).
        pose proof (sep_blocks _ _ LAWS _ _ _ _ _ f m b n HAR3 HfmT Hbin Hne) as D. unfold zdisjoint in D.
        cbn [fst snd] in D. rewrite Rn in D.
        assert (Hm : m = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfm; [destruct Hfm|].
          destruct Hfm as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst m. unfold req_size, AMF_BLOCK in D. cbn in D. unfold AMF_BLOCK in Hj. clia.
    - apply HNI. apply (proj1 (IMG a ltac:(right; right; right; right; right; left; exact Hj))).
    - apply HNI. destruct Hj as [(s & Hs & _ & Hsr) | Hr]; [exists s; split; [exact Hs | exact Hsr]|].
      exact (RIMG a Hr).
    - assert (Hn0 : 0 < c_n cx) by clia. specialize (Hbp Hn0). unfold apart in Hbp. clia. }
  split.
  { intros [(x & Hx & ->) | (x & Hx & ->)]; unfold MD_SIZE, MK_SIZE in Hx.
    - destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
      change (req_size MD_SIZE) with 8856 in Bmceil.
      pose proof (Sh x ltac:(clia)). unfold shadow_of_addr, kLowMemEnd, kHighMemBeg in *. clia.
    - destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4 & Bkceil & _).
      change (req_size MK_SIZE) with 516 in Bkceil.
      pose proof (Sh x ltac:(clia)). unfold shadow_of_addr, kLowMemEnd, kHighMemBeg in *. clia. }
  split; [intros Hro; apply HNI; destruct Hro as [(s & Hs & _ & Hsr) | Hr]; [exists s; split; [exact Hs | exact Hsr]|];
          exact (RIMG a Hr)|].
  split; [exact HNI | clia].
Qed.

Definition LU_ua : Z := AF_LLVMFuzzerTestOneInput + 0x93c.   (* 0x83110, reac_served_unmark_all's return *)

(* +0x93c: reac_served_unmark_all has returned; the operation's journal budgets are those of operation i + 1 *)
Definition u_ua_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  0 <= i <= 47 /\
  lf_shape fy LU_ua ms3 /\ getr (ms_regs ms3) 18 = w64 mk /\ lf_core cx ms3 /\ u_regs cx md fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly3 S3 W3 ms3 md3 T3 [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * (i + 1) /\ requests_are kbs mbs.

(* the two strings reac_served_unmark_all compares against *)
Lemma u_x_img : (kp_kstr_b tfibsegs Tfib_owned_static TFIB_ERRNO LA_S_SERVED (map bv_unsigned S_SERVED)
  && kp_kstr_b tfibsegs Tfib_owned_static TFIB_ERRNO LA_S_EMPTY [])%bool = true.
Proof. vm_compute. reflexivity. Qed.

Definition u_x_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CZero 1)].
Definition u_x_rg_nm : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 4 [].
Definition u_x_rg_sl : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0x90 0x90 [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))].
Definition u_x_facts : facts :=
  mkFacts [(21%nat, mkAF 4096 (2 ^ 47) 2)] [] [].
Definition u_x_ss : sstate := mkSS LU_exit sr_atoms [u_x_rg_sh; u_x_rg_nm; u_x_rg_sl] None u_x_facts.

(* reac_served_unmark_all's read set, as akb (the table part as lib/A/Prog/LLVMFuzzerTestOneInputMq.v mq_ard_akb) *)
Lemma ux_ard_akb : forall ly S (W : world SEGS) mem mdl kbs (regs : bvmap 5 word) lyc Sc slo shi,
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  gx_ok SEGS B G_HARNESS ->
  anlk_at SEGS (rdW W mem) LA_G_NL kbs -> aiftab_at SEGS (rdW W mem) LA_G_NL kbs lf_tab -> lf_ifp (rdW W mem) 64 ->
  forall a, reac_served_unmark_all_ard SEGS regs (rdW W mem) a -> akb SEGS B lyc Sc slo shi a.
Proof.
  intros ly S W mem mdl kbs regs lyc Sc slo shi HAR HRO HGX Hnl Htab Hifp a Ha.
  pose proof (kp_ard_here B TB HSEGS) as KA. unfold kp_ard_b in KA.
  repeat match type of KA with (_ && _)%bool = true => apply andb_prop in KA as [KA ?] end.
  match goal with H : forallb _ (seq 1 4) = true |- _ => rename H into KAodd end.
  assert (HE0 : TFIB_ERRNO = 0x631b6c) by reflexivity.
  assert (AG : forall x, (LA_G_NL <= x < LA_G_NL + NK_SIZE \/ LA_G_NAMES <= x < LA_G_NAMES + G_NAMES_SIZE) ->
                 akb SEGS B lyc Sc slo shi x).
  { intros x Hx. apply (kp_akb_G B TB lyc Sc slo shi x HGX);
      [| unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE in Hx; lia].
    unfold inG, G_HARNESS. unfold LA_G_NAMES, G_NAMES_SIZE, NK_SIZE in Hx.
    destruct Hx as [Hx | Hx].
    - apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    - apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold LA_G_NAMES in *. lia. }
  unfold reac_served_unmark_all_ard, amk_tab_rd in Ha.
  destruct Ha as [Hx | (bs & tab & i & n2 & ix & p & Hbs & Htb & Hnth & Hp & Hs & Hx)].
  - apply AG. left. unfold rd_ivl in Hx. unfold NK_IF_NAME, NK_SIZE in *. lia.
  - assert (Ebs : bs = kbs).
    { destruct Hbs as ((Hb1 & _) & L1). destruct Hnl as ((Hb2 & _) & L2).
      apply (abytes_unique SEGS _ _ _ _ Hb1 Hb2). lia. }
    subst bs.
    destruct Htb as (Hn1 & _ & Ht1). destruct Htab as (Hn2 & H80 & Ht2).
    assert (Hi64 : (i < 64)%nat).
    { assert (HL : length tab = 64%nat) by (rewrite <- lf_tab_len; apply Nat2Z.inj; congruence).
      rewrite <- HL. apply nth_error_Some. rewrite Hnth. discriminate. }
    destruct (nth_error lf_tab i) as [[n0 ix0]|] eqn:Hn0;
      [| exfalso; apply nth_error_None in Hn0; rewrite lf_tab_len in Hn0; lia].
    destruct (Ht2 i n0 ix0 Hn0) as (_ & p0 & Hp0 & _ & Hs0 & _).
    assert (Rp : 0 <= p < 2 ^ 64).
    { destruct Hs as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
    assert (Rp0 : 0 <= p0 < 2 ^ 64).
    { destruct Hs0 as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
    pose proof (kp_vm8_mod _ _ _ _ _ Hp Hp0) as E. rewrite !Z.mod_small in E by lia. subst p0.
    pose proof (kp_acstr_unique _ _ _ _ _ Hs Hs0) as En. subst n0.
    destruct (mq_tab_ptr B TB HSEGS ly S W mem mdl kbs i n2 ix0 p HAR HRO
                (conj Hn2 (conj H80 Ht2)) Hifp Hn0 Hp Rp) as [(Hi60 & Ep & Hl4) | (Hi60 & Hp16 & l & Hk & En & Hj)].
    + apply AG. right. unfold LA_G_NAMES, G_NAMES_SIZE in *. lia.
    + set (j := (i - 59)%nat) in *.
      pose proof (proj1 (forallb_forall _ _) KAodd j ltac:(apply in_seq; unfold j; lia)) as Hx'. cbv beta zeta in Hx'.
      rewrite Hj in Hx'. cbn [fst snd] in Hx'. subst n2. rewrite length_map in Hx.
      exact (kp_akbs_of_b B lyc Sc slo shi p (Datatypes.S (length l)) a Hx' ltac:(lia)).
Qed.

(* reac_served_unmark_all's Pre at 0x8310c, from the cut's pieces (the shape of lib/A/Prog/LLVMFuzzerTestOneInputMq.v
   lf_amq_common, with no FILE range and the callee's own frame bound) *)
Lemma ux_pre : forall cx ly S (W : world SEGS) mem mdl md mk kbs gbs T3 (regs : bvmap 5 word),
  AR SEGS B ly S W mem mdl ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_blocks B cx md mk T3 ly S (rdW W mem) ->
  anlk_at SEGS (rdW W mem) LA_G_NL kbs -> nlk_wf kbs -> aiftab_at SEGS (rdW W mem) LA_G_NL kbs lf_tab ->
  nk_open kbs = 0 -> nk_opened kbs + 64 < 2 ^ 31 -> nk_closed kbs + 64 < 2 ^ 31 ->
  lf_ifp (rdW W mem) 64 -> lf_gnames_at 64 (rdW W mem) ->
  amarks_at SEGS (rdW W mem) mk gbs -> marks_wf gbs ->
  alloc_ceiling <= spZ regs - REAC_SERVED_UNMARK_ALL_AK ->
  aarg regs 0 = mk ->
  reac_served_unmark_all_apre SEGS B regs (rdW W mem).
Proof.
  intros cx ly S W mem mdl md mk kbs gbs T3 regs HAR HRO HBL Hnl Hwf Htab Hop0 Hop Hcl Hifp Hgn Hmk Hkwf HK Ha0.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct HBL as (Hmdin & Hmkin & Hmdc & Hmkc & HmdT & HmkT & Hmd16 & Hmk16 & Hmdt & Hmkt & Hapmm & _ & _
    & Hramd & Hramk & Hammd & Hammk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR Hmkin) as (_ & Hmk4096 & Hmkceil & Hmkapp & _).
  change (req_size MK_SIZE) with 516 in Hmkceil, Hmkapp.
  pose proof (ts_errno B TB) as HE. pose proof (ts_tp B TB) as HTP.
  assert (HE0 : TFIB_ERRNO = 0x631b6c) by reflexivity.
  assert (HAK : REAC_SERVED_UNMARK_ALL_AK = 8768) by reflexivity.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in Hmkt.
  pose proof u_x_img as KI. apply andb_prop in KI as [KS KE].
  assert (KS' : kp_kstr_b SEGS (as_owned_static B) (as_errno B) LA_S_SERVED (map bv_unsigned S_SERVED) = true)
    by (rewrite HSEGS, (ts_owned B TB), (ts_errno B TB); exact KS).
  assert (KE' : kp_kstr_b SEGS (as_owned_static B) (as_errno B) LA_S_EMPTY [] = true)
    by (rewrite HSEGS, (ts_owned B TB), (ts_errno B TB); exact KE).
  destruct (mq_rt_kstr B TB ly S W mem mdl regs REAC_SERVED_UNMARK_ALL_AK LA_S_SERVED _ HAR HRO KS'
    ltac:(unfold LA_G_NL; lia)) as (SS1 & SS2).
  destruct (mq_rt_kstr B TB ly S W mem mdl regs REAC_SERVED_UNMARK_ALL_AK LA_S_EMPTY _ HAR HRO KE'
    ltac:(unfold LA_G_NL; lia)) as (SE1 & SE2).
  rewrite mq_byte_list in SS1, SS2. cbn [map] in SE1, SE2.
  unfold reac_served_unmark_all_apre. exists kbs, lf_tab.
  split.
  { destruct (zsh_gnl_ard B TB SEGS ly S W mem mdl HAR) as (Gra & Ghv).
    unfold amk_nlk_ok. split; [exact Hnl|]. split; [exact Hwf|]. split; [exact Hop0|].
    split; [unfold MARKS_MAX; lia|]. split; [unfold MARKS_MAX; lia|]. split; [exact Htab|]. split; [exact Gra | exact Ghv]. }
  split.
  { destruct (zsh_errno_ard B TB SEGS ly S W mem mdl HAR) as (Era & _).
    unfold amk_errno_ok. rewrite HE, HTP. split; [reflexivity|].
    split; [intros i Hi; apply (mq_writable HSEGS); right; right; right; lia|].
    split; [rewrite <- HE; exact Era|].
    split; [unfold apart_frame; left; lia|].
    split; [unfold apart_gnl, LA_G_NL, NK_SIZE; right; lia|].
    split; [unfold apart; right; lia|].
    intros _. rewrite Ha0. unfold apart, MK_SIZE. lia. }
  split.
  { intros i n2 ix p Hnth Hp Hpr.
    destruct (mq_tab_rt B TB HSEGS ly S W mem mdl kbs regs REAC_SERVED_UNMARK_ALL_AK i n2 ix p HAR HRO Htab Hifp Hgn HK
      Hnth Hp Hpr) as (Hrt & Hp0 & Hloc).
    split; [exact Hrt|].
    split; [unfold apart_gnl; destruct Hloc as [Hl | Hl]; [left | right]; unfold LA_G_NL, NK_SIZE, LA_G_NAMES in *; lia|].
    split; [unfold apart; right; destruct Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
    split; [unfold apart; left; lia|].
    intros _. rewrite Ha0. unfold apart, MK_SIZE.
    destruct Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE, YImgTop.IMG_TOP in *; lia. }
  split.
  { intros _. rewrite Ha0.
    split.
    { unfold amarks_blk_ok. split; [lia|].
      split; [unfold amem_range, MK_SIZE; unfold in_app, kLowShadowBeg, ASAN_CEIL in Hmkapp; lia|].
      split; [exact Hramk|].
      split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ mk MK_SIZE mk MK_SIZE HAR Hmkin);
              change (req_size MK_SIZE) with 516; unfold MK_SIZE; lia|].
      split; [intros b Hb; rewrite ard_aview; apply (mq_blk_tail_vis16 SEGS B ly S W mem mdl mk MK_SIZE b HAR Hmkin);
              replace (round_up MK_SIZE 16) with 528 by reflexivity; unfold MK_SIZE in *; lia|].
      unfold apart_frame, MK_SIZE. left. lia. }
    split; [unfold apart_gnl, LA_G_NL, NK_SIZE, MK_SIZE; lia|].
    split; [unfold apart, MK_SIZE; lia|].
    split; [unfold apart; left; lia|].
    exists gbs. split; [exact Hmk | exact Hkwf]. }
  split; [exact SS1|]. split; [exact SS2|]. split; [exact SE1 | exact SE2].
Qed.

Lemma u_xc : forall POST i,
  FROM POST (u_ua_inv i) -> FROM POST (u_x_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HUA cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HXI.
  destruct HXI as (md & mk & P & N & kbs & mbs & gbs & T3 & Hsh & R18 & HU & Hns & Hrq).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
    & Bamm & Bamk).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4 & Bkceil & _).
  change (req_size MK_SIZE) with 516 in Bkceil.
  pose proof Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & Dare & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  pose proof Dmd as (_ & ML).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMK & _).
  assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc8); rewrite Hc8;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  assert (MS8 : shadow_of_addr SHADOW_OFF (md + MD_N_MARK) = shadow_of_addr SHADOW_OFF md + 1106).
  { unfold shadow_of_addr, MD_N_MARK. pose proof (Z.div_mod md 8 ltac:(lia)) as D. rewrite Hmd8, Z.add_0_r in D.
    replace (md + 8852) with (4 + (md / 8 + 1106) * 8) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia. }
  assert (Shm : shadow_of_addr SHADOW_OFF md = SHADOW_OFF + md / 8) by reflexivity.
  assert (Mdv : 0 <= md / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 mk])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 mk).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ [Z_to_bv 64 mk] 0). }
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E18 : ew E 18 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF md + 1106))
    by (rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl), R18, MS8; reflexivity).
  assert (E21 : ew E 21 = Z_to_bv 64 (md + MD_N_MARK)) by (rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E u_x_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_exit)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold u_x_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold u_x_rg_sh, u_x_rg_nm, u_x_rg_sl.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite E18, unsigned_lit_small by (rewrite Shm; unfold SHADOW_OFF; clia).
        split; [rewrite Shm; unfold SHADOW_OFF; clia|]. split; [rewrite Shm; unfold SHADOW_OFF; clia|].
        split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros ii Hii. rewrite Z.add_0_r.
        replace (shadow_of_addr SHADOW_OFF md + 1106 + ii) with (shadow_of_addr SHADOW_OFF md + (1106 + ii)) by lia.
        apply (u_blk_shadow0 _ md 8856 (1106 + ii) Hmd8 eq_refl); [exact Bram | lia].
      + rewrite E21, unsigned_lit_small by (unfold MD_N_MARK; clia).
        split; [unfold MD_N_MARK; clia|]. split; [unfold MD_N_MARK; clia|]. split; [|apply Forall_nil].
        intros o Ho. destruct Dmd as ((_ & Hw) & HLm). unfold MD_SIZE in HLm.
        replace (md + MD_N_MARK + o) with (md + Z.of_nat (Z.to_nat (MD_N_MARK + o))) by (unfold MD_N_MARK; lia).
        apply Hw. unfold MD_N_MARK; lia.
      + rewrite E9, unsigned_lit_small by (unfold LLVMF_STK in *; clia).
        split; [unfold LLVMF_STK in *; clia|]. split; [unfold LLVMF_STK in *; clia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (u_slot_chunk E cx W3 ms3 0x90 _ mk); [|exact SMK].
        rewrite (lf_sv_off E 32 mk 0 E32) by clia. rewrite Z.add_0_r. reflexivity.
    - apply pairwise_disjoint_of_extents.
      unfold u_x_rg_sh, u_x_rg_nm, u_x_rg_sl, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (u_base E 18 _ E18) by (rewrite Shm; unfold SHADOW_OFF; clia).
      rewrite (u_base E 21 _ E21) by (unfold MD_N_MARK; clia).
      rewrite (u_base E 9 _ E9) by (unfold LLVMF_STK in *; clia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite Shm. pose proof (Z.div_mod md 8 ltac:(lia)) as DM. rewrite Hmd8, Z.add_0_r in DM.
      unfold MD_N_MARK, SHADOW_OFF, LLVMF_STK in *.
      unfold amem_range in Bamm.
      destruct Bamm as [Bl | Bh];
        [assert (Bl' : md + 8856 <= 2147450879) by exact Bl | assert (Bh' : 17594333495296 <= md) by exact (proj1 Bh)];
        repeat split; clia.
    - split; [|split; exact I]. cbn [u_x_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21. rewrite !unsigned_lit_small by (unfold MD_N_MARK; clia).
      assert (M4 : (md + MD_N_MARK) mod 2 ^ 2 = 0).
      { unfold MD_N_MARK. rewrite Zmod_divides in Bm16 by lia. destruct Bm16 as (c & Hc). rewrite Hc.
        replace (16 * c + 8852) with ((4 * c + 2213) * 4) by lia. change (2 ^ 2) with 4. apply Z_mod_mult. }
      unfold MD_N_MARK in *. repeat match goal with |- _ /\ _ => split end; first [exact I | clia]. }
  rewrite (lf_shape_eta fy LU_exit ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_exit)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { cbn [ss_mem u_x_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi u_x_rg_sh] in Ha. lia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_x_rg_nm base_val] in Ha.
      rewrite E21, unsigned_lit_small in Ha by (unfold MD_N_MARK; clia).
      apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Bmd Bmc). unfold MD_N_MARK, MD_SIZE in *. lia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi u_x_rg_sl] in Ha. lia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  assert (U21 : bv_unsigned (ew E 21) = md + MD_N_MARK)
    by (rewrite E21; apply unsigned_lit_small; unfold MD_N_MARK; clia).
  set (X := fun a => md + MD_N_MARK <= a mod 2 ^ 64 < md + MD_N_MARK + 4).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem u_x_ss) _ _ X HFrA). intros a (r & Hr & Hw). unfold X.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem u_x_ss In] in Hr. destruct Hr as [<- | [<- | [<- | []]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_x_rg_sh u_x_rg_nm u_x_rg_sl base_val] in Hw; rewrite ?U21 in Hw; clia. }
  assert (XB : forall a, X a -> 0 <= a < 2 ^ 64 -> md <= a < md + MD_SIZE)
    by (intros a Ha R; unfold X in Ha; rewrite Z.mod_small in Ha by exact R; unfold MD_N_MARK, MD_SIZE in *; clia).
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a) -> ~ X a).
  { intros a Hf HXa.
    pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk ltac:(tauto)) as (R & _).
    destruct (u_blk_out cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 md MD_SIZE a HB HJ0 Hfr Hjbk Hblk
      (or_introl eq_refl) (XB a HXa R)) as (_ & N1 & N2 & N3 & N4 & N5 & N6 & N7 & _). tauto. }
  pose proof (lf_saved_keep X cx W3 ms3 W3 msA KA (fun a Ha => NX a ltac:(tauto)) Hsv) as Hsv'.
  pose proof (lf_header_keep X cx fp W3 ms3 W3 msA KA (fun a Ha => NX a ltac:(tauto)) Hhd) as Hhd'.
  pose proof (lf_fshadow_keep X cx fp W3 ms3 W3 msA LF_SH0 KA ltac:(intros a Ha; apply NX; tauto) Hfs) as Hfs'.
  pose proof (lf_slots_keep X cx md mk fp W3 ms3 W3 msA KA (fun a Ha => NX a ltac:(tauto)) Hsl) as Hsl'.
  pose proof (lf_cur_keep X cx W3 ms3 W3 msA P N KA (fun a Ha => NX a ltac:(tauto)) Hcur) as Hcur'.
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs
    (fun a Ha => NX a ltac:(tauto)) Hjbk) as Hjbk'.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA (fun a Ha => NX a ltac:(tauto)) Hblk) as Hblk'.
  lazymatch type of HS with st_ok _ _ ?ssx _ => set (ssA := ssx) in HS end.
  assert (RG : forall k r, nth_error (ss_mem ssA) k = Some r -> region_ok SEGS E (rdW W3 (ms_mem msA)) r)
    by (intros kk r Hk; exact (st_ok_region_nth E ssA (restrict (w_H W3) msA) kk r HS Hk)).
  assert (AZ : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_N_MARK + 0) lf_z4).
  { apply (u_word4 E _ _ (md + MD_N_MARK) 0 (SLit 0) lf_z4 (RG 1%nat _ eq_refl)).
    1: cbn [base_val YP09.r_base]; exact U21.
    1: cbn; left; reflexivity.
    1: reflexivity.
    1: reflexivity.
    all: unfold MD_N_MARK, MD_SIZE in *; clia. }
  rewrite Z.add_0_r in AZ.
  pose proof Hjbk' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROA & _).
  destruct (lf_odd_texts_of_ro B TB HSEGS W3 (ms_mem msA) HROA) as (HoddA & _).
  destruct (ux_store X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    ltac:(intros a Ra HXa; unfold X in HXa; rewrite Z.mod_small in HXa by exact Ra; exact HXa)
    Bmt Bap ltac:(lia) ltac:(unfold MD_SIZE; lia) ltac:(lia) ltac:(unfold MK_SIZE; lia) HoddA
    (lf_la_slack_any HSEGS _) AZ Hdat)
    as (DkA & DtabA & DmdA & DmkA & DifpA & DgnA & DgwA & DlaA).
  pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  (* the call of reac_served_unmark_all at 0x8310c *)
  pmkst HS.
  assert (Hpc : ss_pc ssA = pa_sigma LS_reac_served_unmark_all) by reflexivity.
  rewrite Hpc, (lv_sigma LV).
  replace (link_sigma LS_reac_served_unmark_all) with REAC_SERVED_UNMARK_ALL_A by reflexivity.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10.
  try rewrite (img_env_codeptr E HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4. rewrite E32 in Q10.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9.
  rewrite E32 in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
  rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  pose proof (lv_text LV) as HBASE.
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite Q2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
  assert (Ra0 : aarg (ms_regs msA) 0 = mk)
    by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; unfold MK_SIZE in *; clia).
  assert (HK8 : 0 <= REAC_SERVED_UNMARK_ALL_AK <= LLVMF_STK - 448)
    by (rewrite REAC_SERVED_UNMARK_ALL_AK_val; unfold LLVMF_STK; lia).
  assert (HKs : alloc_ceiling <= spZ (ms_regs msA) - REAC_SERVED_UNMARK_ALL_AK)
    by (rewrite Rsp, REAC_SERVED_UNMARK_ALL_AK_val; unfold LLVMF_STK in *; clia).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 REAC_SERVED_UNMARK_ALL_A) (ms_mem msA) (seg_rom SEGS)) md4)
    with (@cfg_at fy SEGS REAC_SERVED_UNMARK_ALL_A (ms_regs msA) (ms_mem msA) md4).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (UNMARK_ALL fy).
  - exact HB.
  - exact HJ.
  - exact HROA.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite Q3. exact Gp.
  - rewrite Q4. exact Tp.
  - exact Rsp.
  - exact HK8.
  - lia.
  - pose proof Hjbk' as (Jk & _). unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
  - apply (ar_side_room S3 fp _ Hfr). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold reac_served_unmark_all_awr in Hin. rewrite Ra0 in Hin. unfold aivl in Hin.
    replace (mk =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; lia).
    destruct Hin as [<- | [<- | []]]; cbn in Hr.
    + apply ar_ajw_G. unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold LA_G_NL, NK_N_SENT in *. lia.
    + apply (ar_ajw_blk B cx fp ly3 S3 mk MK_SIZE a Bmk Bkc). unfold MK_SIZE in *. clia.
  - intros a (r & Hin & Hr). unfold reac_served_unmark_all_awr in Hin. rewrite Ra0 in Hin. unfold aivl in Hin.
    replace (mk =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; lia).
    destruct Hin as [<- | [<- | []]]; cbn in Hr.
    + apply (ar_not_ro_G HSEGS a). unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold LA_G_NL, NK_N_SENT in *. lia.
    + intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
      unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE in *. clia.
  - intros a Ha. exact (ux_ard_akb ly3 S3 W3 (ms_mem msA) md4 kbs (ms_regs msA) ly3 S3 _ _ HARA HROA HGX
      DkA DtabA DifpA a Ha).
  - exact (ux_pre cx ly3 S3 W3 (ms_mem msA) md4 md mk kbs gbs T3 (ms_regs msA) HARA HROA Hblk' DkA Dwf DtabA Dop
      ltac:(lia) ltac:(lia) DifpA DgnA DmkA Dkwf HKs Ra0).
  - (* the return, +0x93c *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (reac_served_unmark_all_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (HE : forall a, Er a -> (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (mk <= a < mk + MK_SIZE)).
    { intros a (r & Hin & Hr). unfold reac_served_unmark_all_awr in Hin. rewrite Ra0 in Hin. unfold aivl in Hin.
      replace (mk =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; lia).
      destruct Hin as [<- | [<- | []]]; cbn in Hr; [left | right]; unfold LA_G_NL, NK_N_SENT, MK_SIZE in *; lia. }
    assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
    assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
    (* reac_served_unmark_all's post, a0 = the marks block *)
    destruct Hpost as (_ & Hpost). rewrite Ra0 in Hpost.
    pose proof (Hpost ltac:(lia) kbs lf_tab gbs DkA DtabA DmkA) as RM. clear Hpost. cbv zeta in RM.
    destruct RM as ((gbs' & Hmk2 & Hkwf2 & Hn2)
      & (kbs' & Dk2 & Dwf2 & Hch & Hend & Hnif & Htab2 & Hnx & Hsent & Hns2 & Hop2 & Hmis2 & Hoc2 & Hopd)).
    assert (MA2 : marks_are gbs' (u_mbs_um mbs)).
    { split; [rewrite Hn2, (u_um_n_mark mbs ML); reflexivity|].
      rewrite (u_um_marks mbs ML). unfold mk_names. rewrite Hn2. reflexivity. }
    destruct (ux_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk (u_mbs_um mbs) T3 _ P N ly3 S3 W3 msA md4 ly2 S2 W2 ms2 md2
      REAC_SERVED_UNMARK_ALL_AK Er kbs' gbs'
      HB Hfr HJ HJ2 ltac:(lia) ltac:(rewrite REAC_SERVED_UNMARK_ALL_AK_val; unfold LLVMF_STK in *; clia)
      Hkp Hsk Pmd Pmk Hfd2 Hfs2 HE
      Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' DmdA DifpA DgnA DgwA DlaA
      Dk2 Dwf2 Htab2 Hop2 ltac:(rewrite Hmis2; exact Dmis) ltac:(lia) (u_um_wf mbs ML Dmwf) Hmk2 Hkwf2 MA2)
      as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
    pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
      ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
    assert (Hjbk4 : lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1))
      LF_LIVE_HELD ly2 S2 W2 ms2 md2 T3 [(md, MD_SIZE); (mk, MK_SIZE)]).
    { destruct Hjbk3 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Jrest).
      split; [unfold lf_ev, LF_EV_OP in *; lia|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|].
      split; [exact J5|]. split; [exact J6|]. split; [apply MT_LE|].
      split; [unfold lf_wl, LF_WILD_OP in *; rewrite Z2Nat.inj_add by lia; lia | exact Jrest]. }
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    apply (HUA cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, kbs', (u_mbs_um mbs), gbs', T3.
    split; [exact Hi|].
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1. unfold LU_ua, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    cbn [ms_regs ms2 mkst].
    split; [rewrite P18, Q18; reflexivity|].
    split.
    { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
      rewrite R8, R9. repeat split; assumption. }
    split.
    { unfold u_regs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P21, P22, P24, P25, P26, P27, Q19, Q21, Q22, Q24,
        Q25, Q26, Q27. repeat split; assumption. }
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hcur2|].
    split; [exact Hjbk4|]. split; [exact (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2)|].
    split; [exact Hdat2|].
    split; [unfold MARKS_MAX in Hopd; lia|].
    pose proof Dk2 as (_ & KL2).
    apply u_requests_are; [exact KL2 | exact (u_um_len mbs ML) | exact Dwf2 | exact (u_um_wf mbs ML Dmwf) |].
    rewrite Hsent, (u_um_reqs mbs ML Dmwf), Hrq.
    assert (S0 : nk_sent kbs = []) by (unfold nk_sent; rewrite Hns; reflexivity).
    rewrite S0. reflexivity.
Qed.

End a.
