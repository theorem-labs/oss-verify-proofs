(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 294 of its 345 lines of code are new or changed and 1281 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   the inlined `remember` of the name t into the model (+0x1178 .. +0x11fc; listing
   (internal path) (internal record, sha256 e84d6f0c6974)), part 1: the cuts and
   the facts the runs use.

     +0x1178 .. +0x1198  n := m->n_mark (the instrumented 4-byte load), s2 := m + MD_MARK, s10 := n; n <= 0 -> +0x11c0
     +0x119c .. +0x11b4  the loop: strcmp(s2, name) (the wrapper at 0x83978); 0 -> +0x11f4; s10--, s2 += 16
     +0x11b8 .. +0x11bc  31 < n -> +0x11f4 (32 names kept)
     +0x11c0 .. +0x11f0  the append: m->n_mark := n + 1, snprintf(m + MD_MARK + 16 n, 16, "%s", name) (0x839c4)
     +0x11f4 .. +0x11fc  s10 := F + 0x20, s6 := m, -> +0xc0c

   o2_l_inv j: the loop head at turn j (+0x119c); o2_a_inv: the append (+0x11c0), every slot differs from the name.

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
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C LLVMFuzzerTestOneInputOp2R LLVMFuzzerTestOneInputDec
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp2D LLVMFuzzerTestOneInputOp2Nm
  LLVMFuzzerTestOneInputOp2V LLVMFuzzerTestOneInputOp2Ml.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSnp rememberPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LO2_l : Z := AF_LLVMFuzzerTestOneInput + 0x119c.   (* 0x83970, the loop head *)
Definition LO2_a : Z := AF_LLVMFuzzerTestOneInput + 0x11c0.   (* 0x83994, the append *)

(* the runner's state at +0x1178: the two slots it loads (atom 32 = m) and the count word (atom 33 = n) *)
Definition o2m_c8 (o : Z) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 v).
Definition o2m_fr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x58 0xa0 0x58 0x58 [o2m_c8 0x58 (SOff 32 8340); o2m_c8 0x98 (SOff 32 8852)].
Definition o2m_cnt : YP09.region :=
  YP09.mkRegion (Some 32%nat) 8852 8856 8852 8852 [YP09.mkChunk 8852 (CVal 4 (SOff 33 0))].
Definition o2m_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47 - 8856) 4);
           (27%nat, mkAF o5_RSB o5_RSB 0); (33%nat, mkAF 0 32 0)] [] [].
Definition o2m_ss : sstate := mkSS LO2_m sr_atoms [o2m_fr; o2m_cnt] None o2m_facts.
Definition o2m_SH : list shent := [mkSHE 32 0 8856].

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

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the facts the remember cuts share *)
Definition o2_rm (i md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z))
    (cx : lcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    : Prop :=
  getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 21 = w64 (md_n_mark mbs) /\
  getr (ms_regs ms3) 22 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK)) /\
  o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\
  getr (ms_regs ms3) 23 = w64 (m_rc (o2_MM (Some t) kbs gbs)) /\
  md_reqs mbs = m_reqs (o2_MM (Some t) kbs gbs) /\
  m_marks (o2_MM (Some t) kbs gbs) = remember (mk_names gbs) t.

(* +0x119c: the loop at turn j; the slots before j differ from the name *)
Definition o2_l_inv (i j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_l ms3 /\
  o2_rm i md mk P N s t kbs mbs gbs T3 cx fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 18 = w64 (md + MD_MARK + MARK_LEN * j) /\
  getr (ms_regs ms3) 26 = w64 (md_n_mark mbs - j) /\
  0 <= j < md_n_mark mbs /\ (forall k, 0 <= k < j -> o2l_slot mbs k <> t).

(* +0x11c0: the append; no slot holds the name, and a slot is free *)
Definition o2_a_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_a ms3 /\
  o2_rm i md mk P N s t kbs mbs gbs T3 cx fp k2 ly3 S3 W3 ms3 md3 /\
  0 <= md_n_mark mbs <= 31 /\ (forall k, 0 <= k < md_n_mark mbs -> o2l_slot mbs k <> t).

(* lf_data_nm across a run or a callee whose changed bytes inside the data are bytes of the model block *)
Lemma o2m_data_md : forall X m m' cx md mk kbs mbs gbs mbs', kagree SEGS X m m' ->
  wcarry_on m m' (lf_data_fp_w md mk) ->
  (forall a, lf_data_fp md mk a -> X a -> md <= a < md + MD_SIZE) ->
  off_img md MD_SIZE -> off_img mk MK_SIZE -> apart md MD_SIZE mk MK_SIZE ->
  amodel_at SEGS m' md mbs' -> model_wf mbs' ->
  lf_data_nm cx md mk kbs mbs gbs m -> lf_data_nm cx md mk kbs mbs' gbs m'.
Proof.
  intros X m m' cx md mk kbs mbs gbs mbs' HK HW HX Hmdt Hmkt Hap Hmd' Hmwf'
    (Hnl & Hwf & Hif & Ho & Hmi & Hoc & Hmd & Hmwf & Hmk & Hkwf & Hifp & Hgn & Hgw & Hodd & Htx & Hla).
  unfold apart in Hap. unfold off_img in Hmdt, Hmkt.
  assert (CV : LA_G_NL = 6146752 /\ NK_SIZE = 271992 /\ LA_G_NAMES = 6486720 /\ G_NAMES_SIZE = 512 /\
               LA_LONG_ALIAS = 6487360 /\ MD_SIZE = 8856 /\ MK_SIZE = 516 /\ YImgTop.IMG_LO = 65536 /\
               YImgTop.IMG_TOP = 6635520)
    by (repeat split; reflexivity).
  assert (XR : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a).
  { intros a Ha HXa. pose proof (lf_roP_bounds a Ha) as Hlo.
    pose proof (HX a ltac:(unfold lf_data_fp; right; right; right; right; right; exact Ha) HXa). lia. }
  assert (Hodd' := lf_odd_at_keep X m m' HK XR Hodd). assert (Htx' := lf_texts_at_keep X m m' HK XR Htx).
  assert (XG : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a)
    by (intros a Ha HXa; pose proof (HX a ltac:(left; exact Ha) HXa); lia).
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a)
    by (intros a Ha HXa; pose proof (HX a ltac:(right; left; exact Ha) HXa); lia).
  assert (XL : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 304 -> ~ X a)
    by (intros a Ha HXa; pose proof (HX a ltac:(right; right; left; exact Ha) HXa); lia).
  assert (XK : forall a, mk <= a < mk + MK_SIZE -> ~ X a)
    by (intros a Ha HXa; pose proof (HX a ltac:(right; right; right; right; left; exact Ha) HXa); lia).
  assert (XO : forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a)
    by (intros a Ha; apply XR; right; unfold LA_ODD, PCAP_RLO, PCAP_RHI in *; lia).
  assert (Hsl' : lf_la_slack m').
  { destruct Hla as (_ & _ & (sl & Hsl & Hs)). exists sl. split; [|exact Hs].
    apply (au8arr_keep SEGS X m m' _ sl HK); [| |exact Hsl]; rewrite Hs; change (Z.of_nat 3) with 3; intros i Hi.
    - replace (LA_LONG_ALIAS + 301 + i) with (LA_LONG_ALIAS + (301 + i)) by lia.
      apply (wcarry_on_sub m m' (lf_data_fp_w md mk) LA_LONG_ALIAS 304 HW); [|lia].
      intros j Hj. unfold lf_data_fp_w. right; right; left. lia.
    - apply XL. lia. }
  assert (WS : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) -> wcarry SEGS m m' a n)
    by (intros a n Ha; exact (wcarry_on_sub m m' _ a n HW Ha)).
  assert (Hifp' : lf_ifp m' 64) by exact (lf_ifp_keep_ro X m m' 64 HK ltac:(lia) XG XO Hifp).
  assert (Hnl' : anlk_at SEGS m' LA_G_NL kbs).
  { apply (anlk_keep SEGS X m m' _ kbs HK); [|intros i Hi; apply XG; lia | exact Hnl].
    apply WS. intros i Hi. unfold lf_data_fp_w. left. lia. }
  assert (Hif' : aiftab_at SEGS m' LA_G_NL kbs lf_tab)
    by exact (lf_aiftab_keep_ro X m m' kbs HK XG XN Hifp Hifp' Hodd' Hif).
  assert (Hmk' : amarks_at SEGS m' mk gbs).
  { apply (amarks_keep SEGS X m m' _ gbs HK); [|intros i Hi; apply XK; lia | exact Hmk].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; right. lia. }
  assert (Hgw' : lf_gnames_w m').
  { apply (lf_gnames_w_keep X m m' HK); [|exact XN | exact Hgw].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; left. unfold G_NAMES_SIZE in *. lia. }
  assert (Hla' : lf_la_at m').
  { apply (lf_la_at_keep_ns X m m' HK); [|intros a Ha; apply XL; lia | exact Hsl' | exact Hla].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; left. lia. }
  exact (conj Hnl' (conj Hwf (conj Hif' (conj Ho (conj Hmi (conj Hoc (conj Hmd' (conj Hmwf' (conj Hmk' (conj Hkwf
    (conj Hifp' (conj (lf_gnames_at_keep X m m' 64 HK ltac:(lia) XN Hgn) (conj Hgw'
    (conj Hodd' (conj Htx' Hla'))))))))))))))).
Qed.

(* the slot the loop's strcmp reads is a C string inside its 16 bytes (rememberPost.v amk_slot_cstr) *)
Lemma o2m_slot_cstr : forall (m : word -> option byte) md mbs j,
  amodel_at SEGS m md mbs -> model_wf mbs -> 0 <= j < md_n_mark mbs ->
  acstr_at SEGS m (md + MD_MARK + MARK_LEN * j) (o2l_slot mbs j) /\ (length (o2l_slot mbs j) < 16)%nat.
Proof.
  intros m md mbs j ((HAB & _) & HL) (_ & _ & _ & _ & _ & (R & T)) Hj.
  specialize (T j Hj). unfold MARKS_MAX in R. unfold MD_SIZE in HL.
  unfold o2l_slot. unfold MD_MARK, MARK_LEN in *. change (Z.to_nat 16) with 16%nat in T.
  destruct HAB as (Hp & Hpl & Hnth).
  assert (LS : length (slice mbs (8340 + 16 * j) 16) = 16%nat) by (rewrite lw_slice_length by lia; reflexivity).
  set (sl := slice mbs (8340 + 16 * j) 16) in *.
  destruct (rp_cstr_split sl ltac:(lia)) as (rest & E & Nn).
  assert (LC : (length (cstr sl ++ [zb 0]) <= 16)%nat).
  { rewrite <- LS. rewrite E at 2. rewrite app_assoc, !length_app. lia. }
  split; [|rewrite length_app in LC; cbn [length] in LC; lia].
  split; [|exact Nn].
  split; [lia|]. split; [lia|].
  intros k Hk.
  assert (Hk' : nth_error (cstr sl ++ [zb 0]) k = nth_error sl k).
  { rewrite E at 2. rewrite app_assoc. symmetry. apply nth_error_app1. exact Hk. }
  rewrite Hk'. unfold sl. rewrite lw_slice_nth by lia.
  replace (md + 8340 + 16 * j + Z.of_nat k) with (md + Z.of_nat (Z.to_nat (8340 + 16 * j) + k)) by lia.
  rewrite <- Hnth by lia. reflexivity.
Qed.

(* the count word m->n_mark, as the +0x118c load reads it *)
Lemma o2m_nmark_val : forall (m : word -> option byte) md mbs,
  amodel_at SEGS m md mbs -> val_mem SEGS m (md + MD_N_MARK) 4 (md_n_mark mbs).
Proof.
  intros m md mbs ((HAB & _) & HL). unfold MD_SIZE in HL.
  unfold md_n_mark, fld_u32. change (rdn mbs MD_N_MARK 4) with (rdn mbs MD_N_MARK (Z.of_nat 4)).
  apply val_mem_of_abytes; [exact HAB | unfold MD_N_MARK; lia | unfold MD_N_MARK; lia].
Qed.

(* the shadow byte address of md + o, as the code computes it ((md + o) >> 3 + s11) *)
Lemma o2m_shx_val : forall E k o md, bv_unsigned (ew E k) = md -> bv_unsigned (ew E 27) = o5_RSB ->
  0 <= md -> 0 <= o -> md + o < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff k o) (SLit 3)) (SOff 27 0)) =
    Z_to_bv 64 (shadow_of_addr SHADOW_OFF (md + o)).
Proof.
  intros E k o md Uk U27 H0 Ho H47. apply o5_sv_of_U.
  - rewrite !U_SAlu, !U_SOff, U_SLit. rewrite Uk, U27. cbn [zalu_raw].
    unfold zcanon, M64, o5_RSB, shadow_of_addr, SHADOW_OFF.
    replace (Z.land (3 mod 2 ^ 64) 63) with 3 by reflexivity.
    rewrite (Z.mod_small (md + o) (2 ^ 64)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (0 <= (md + o) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite (Z.mod_small ((md + o) / 8) (2 ^ 64)) by lia.
    rewrite Z.add_0_r. rewrite (Z.mod_small 2147450880 (2 ^ 64)) by lia.
    rewrite Z.mod_small by lia. lia.
  - unfold shadow_of_addr, SHADOW_OFF.
    assert (0 <= (md + o) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Lemma o2_mh : forall POST i,
  FROM POST (o2_a_inv i) -> FROM POST (o2_l_inv i 0) -> FROM POST (o2_m_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HA0 HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HMI.
  destruct HMI as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R22 & R26 & HM
    & Hare & R23 & Hrq & Hmm).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_lt as CL.
  destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)
    as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
  pose proof (o5_aj_AR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
  pose proof Hblk as (Hmdin & Hmkin & Hmdc & Hmkc & HmdT & HmkT & Hmd16 & Hmk16 & Hmdoff & Hmkoff & Hapmm & Hapmi & Hapki
    & Hramd & Hramk & Hammd & Hammk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Hmdin) as (_ & Hmd4096 & Hmdceil & _).
  change (req_size MD_SIZE) with 8856 in Hmdceil.
  pose proof Hdatn as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & _).
  pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
  set (n := md_n_mark mbs) in *.
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & SMARK0 & _ & _ & _ & _ & _ & _ & SNMARK & _).
  unfold lf_slot, lf_at in SMARK0, SNMARK. apply o5_vm_of_rd in SMARK0, SNMARK.
  unfold LS_MARK0, LS_NMARK in SMARK0, SNMARK.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md; Z_to_bv 64 n])) in *.
  assert (EL : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r).
  { intros n0 r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n0 r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 md) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
    by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; clear - Hsp146 Hsp1r H470; lia).
  assert (U27 : bv_unsigned (ew E 27) = o5_RSB)
    by (rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl), R27; unfold w64, o5_RSB, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = md) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2m_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_m)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2m_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, o2m_fr, o2m_cnt, o2m_c8;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [clear - Hsp146; lia|]. split; [clear - Hsp146 Hsp1r H470; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x58 8 (SOff 32 8340) (md + MD_MARK));
            [ cbn [sv_denot]; rewrite U32; unfold MD_MARK; reflexivity | unfold MD_MARK; cbn; lia | cbn; lia | exact SMARK0 ].
        * apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x98 8 (SOff 32 8852) (md + MD_N_MARK));
            [ cbn [sv_denot]; rewrite U32; unfold MD_N_MARK; reflexivity | unfold MD_N_MARK; cbn; lia | cbn; lia | exact SNMARK ].
      + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; clear - Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ md 8852 4 (SOff 33 0) n);
          [ cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        exact (o2m_nmark_val _ md mbs Dmd).
    - apply pairwise_disjoint_of_extents. unfold o2m_fr, o2m_cnt, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hmdceil Hsp1r Hceil0 CL. unfold LLVMF_STK in *. lia.
    - split; [|split; exact I]. cbn [o2m_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U32, U27, U33. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I;
        clear - Hsp146 Hsp1r H470 Hsp132 Hmd4096 Hmdceil Hmd16 Wnm CL Hceil0; unfold o5_RSB, LLVMF_STK in *; try lia. }
  rewrite (lf_shape_eta fy LO2_m ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok SEGS o5_Bx o2m_SH E (rdW W3 (ms_mem ms3))).
  { unfold sh_ok, o2m_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    unfold o5_Bx. rewrite !U_SOff, U32, U27. unfold zcanon, M64.
    rewrite !Z.add_0_r, !Z.mod_small by (unfold o5_RSB; lia). replace (8856 - 0) with MD_SIZE by reflexivity.
    split; [exact Hramd|]. intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.max_r in Ha by (unfold MD_SIZE; lia).
    unfold amem_range, o5_RSB, MD_SIZE in *. lia. }
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK o5_span; [apply ar_awr_nowin; vm_compute; reflexivity|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => set (EA := E1) in * end.
  assert (EWA : forall n0, (n0 < 512)%nat -> ew EA n0 = ew E n0)
    by (intros n0 Hn0; unfold EA; repeat (rewrite ew_ewset_other by lia); reflexivity).
  pose proof (ar_kagree_nowin _ _ _ _ HFrA ltac:(vm_compute; reflexivity)) as KA.
  assert (S33 : sv_denot EA (SOff 33 0) = Z_to_bv 64 n).
  { rewrite (lf_sv_off EA 33 n 0 ltac:(rewrite EWA by lia; exact E33) ltac:(lia) ltac:(lia)). rewrite Z.add_0_r.
    reflexivity. }
  psrr_branch_tok RUN BR HS SHOK o5_span.
  all: rewrite S33 in Hc; cbn [sv_denot] in Hc; rewrite (u_bge0 n ltac:(lia)) in Hc.
  1: apply Z.leb_le in Hc.
  2: apply Z.leb_gt in Hc.
  1: paj_run_to_tok RUNTO HS HJ SHOK o5_span LO2_a; [apply ar_awr_nowin; vm_compute; reflexivity|].
  2: paj_run_to_tok RUNTO HS HJ SHOK o5_span LO2_l; [apply ar_awr_nowin; vm_compute; reflexivity|].
  all: rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  all: pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB0.
  all: assert (KAB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)))
        by (intros a0 Ha0; rewrite (KB0 a0 Ha0), (KA a0 Ha0); reflexivity).
  all: assert (GAB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
  all: lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
  all: assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
  all: assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
  all: lazymatch type of HS with st_ok_pi _ _ ?EBx ?ssx _ => set (EB := EBx) in *; set (ssB := ssx) in * end.
  all: assert (EWB : forall n0, (n0 < 512)%nat -> ew EB n0 = ew E n0)
        by (intros n0 Hn0; unfold EB; repeat (rewrite ew_ewset_other by lia); try (rewrite EWA by lia); reflexivity).
  all: assert (HAB : env_agree 32 (Ereg (ms_regs ms3) []) EB)
        by (split; [intros n0 Hn0; rewrite EWB by lia; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia);
                    rewrite !ew_Ereg_lt by lia; reflexivity | unfold EB; reflexivity]).
  all: assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
        getr (ms_regs msB) r = getr (ms_regs ms3) r)
        by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HAB Hr)).
  all: prreg HS (18%bv : bv 5) Q18; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22;
       prreg HS (26%bv : bv 5) Q26.
  all: assert (V32 : bv_unsigned (ew EB 32) = md) by (rewrite EWB by lia; exact U32).
  all: assert (V27 : bv_unsigned (ew EB 27) = o5_RSB) by (rewrite EWB by lia; exact U27).
  all: assert (V33 : ew EB 33 = Z_to_bv 64 n) by (rewrite EWB by lia; exact E33).
  all: assert (HM5 : o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 msB md5)
        by (apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs
              gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msB md5 HM SH_M_len KAB (fun a _ H => H) GAB Fd5 Fs5);
            rewrite KR by (vm_compute; reflexivity); reflexivity).
  all: assert (RM : o2_rm i md mk P N s t kbs mbs gbs T3 cx fp k2 ly3 S3 W3 msB md5).
  1,3: (split; [rewrite KR by (vm_compute; reflexivity); exact R20|]; split; [exact Hw|]; split; [exact Hlt|];
    split; [rewrite Q21, V33; reflexivity|];
    split; [rewrite Q22;
            replace (ew EB 27) with (Z_to_bv 64 (bv_unsigned (ew EB 27) + 0))
              by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned);
            transitivity (sv_denot EB (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 8852) (SLit 3)) (SOff 27 0))); [reflexivity|];
            exact (o2m_shx_val EB 32 8852 md V32 V27 ltac:(clear - Hmd4096; lia) ltac:(lia)
              ltac:(clear - Hmdceil CL; unfold MD_SIZE in *; lia))|];
    split; [exact HM5|]; split; [exact Hare|];
    split; [rewrite KR by (vm_compute; reflexivity); exact R23|]; split; [exact Hrq | exact Hmm]).

  1: { apply (HA0 cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
       exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
       split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|]. split; [exact RM|].
       split; [lia|]. intros k Hk. lia. }
  { apply (HL cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|]. split; [exact RM|].
    split; [rewrite Q18, V32; unfold w64, MD_MARK, MARK_LEN; f_equal; lia|].
    split; [rewrite Q26, V33; unfold w64; f_equal; lia|].
    split; [lia|]. intros k Hk. lia. }
Qed.

End a.
