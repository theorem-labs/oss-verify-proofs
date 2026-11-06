(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 553 of its 607 lines of code are new or changed and 350 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm: one turn of the per-mark loop (+0x76c .. +0x8d0):
   the frame object F + 0x20 put in scope, model_read (0x82fd8), the bcmp wrapper (0x82ff0), model_write
   (0x83008), the object out of scope again, and the loop test.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
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
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Definition LU_mr : Z := AF_LLVMFuzzerTestOneInput + 0x808.   (* 0x82fdc, model_read's return *)

(* the runner's state at the loop head: the frame's shadow, its window the 32 bytes of F + 0x20 *)
Definition u_fs_rg : YP09.region := YP09.mkRegion (Some 19%nat) 0 112 4 36 [].
Definition u_l_facts : facts := mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2)] [] [].
Definition u_l_ss : sstate := mkSS LU_body sr_atoms [u_fs_rg] None u_l_facts.

(* the frame's shadow with the object F + 0x20 in scope *)
Definition SH_Z : list Z := firstn 4 LF_SH0 ++ repeat 0 32 ++ skipn 36 LF_SH0.

Lemma SH_Z_len : length SH_Z = 112%nat. Proof. reflexivity. Qed.
Lemma SH_Z_nth : forall i, (i < 112)%nat -> nth i SH_Z 0 = if ((4 <=? i) && (i <? 36))%nat then 0 else nth i LF_SH0 0.
Proof. intros i Hi. do 112 (destruct i as [|i]; [reflexivity|]). lia. Qed.

(* a byte of the frame's shadow is in no footprint of the cut but lf_fshadow's *)
Lemma u_fs_out : forall cx fp k2 ev mo wl lv md mk T3 own ly3 S3 (W3 : world SEGS) ms3 md3 a,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_SH cx fp <= a < lf_SH cx fp + 128 ->
  ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_slots_fp cx a /\
  ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\ ~ lf_data_fp md mk a.
Proof.
  intros cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & _ & _ & Bamm
    & Bamk).
  pose proof (Fsep md MD_SIZE Bmd) as DmF. pose proof (Fsep mk MK_SIZE Bmk) as DkF.
  unfold zdisjoint in DmF, DkF. cbn [fst snd] in DmF, DkF. change (req_size MD_SIZE) with 8856 in DmF.
  change (req_size MK_SIZE) with 516 in DkF.
  assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg).
  { rewrite HFS. assert (D1 : 4096 / 8 <= lf_F cx fp / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : lf_F cx fp / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. lia. }
  (* the image is below the frame's shadow, the stack above it; a block of the state is not in the shadow *)
  assert (NI : forall x, x < YImgTop.IMG_TOP -> ~ (lf_SH cx fp <= x < lf_SH cx fp + 128))
    by (intros x Hx; unfold YImgTop.IMG_TOP, kLowMemEnd in *; lia).
  assert (NB : forall b n x, In (b, n) (ablocks B ly3 S3) -> b <= x < b + req_size n -> ~ (lf_SH cx fp <= x < lf_SH cx fp + 128)).
  { intros b n x Hbn Hx. destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b n HAR3 Hbn) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> x < YImgTop.IMG_TOP) by exact lf_roP_below_top.
  assert (SHD : forall p n x, p mod 8 = 0 -> zdisjoint (p, n) (lf_F cx fp, 1024) -> p <= x < p + n ->
    ~ (lf_SH cx fp + 0 <= shadow_of_addr SHADOW_OFF x < lf_SH cx fp + 128)).
  { intros p n x Hp8 Hd Hx. rewrite HFS. unfold shadow_of_addr, zdisjoint in *. cbn [fst snd] in Hd.
    pose proof (Z.div_mod (lf_F cx fp) 8 ltac:(lia)) as DF.
    assert (F8 : lf_F cx fp mod 8 = 0).
    { pose proof (Z.div_mod (lf_F cx fp) 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D. rewrite D.
      replace (32 * (lf_F cx fp / 32)) with ((4 * (lf_F cx fp / 32)) * 8) by lia. apply Z_mod_mult. }
    rewrite F8, Z.add_0_r in DF.
    destruct Hd as [Hd | Hd].
    - assert (Hx8 : x / 8 < lf_F cx fp / 8) by (apply Z.div_lt_upper_bound; lia). lia.
    - pose proof (Z.div_mod p 8 ltac:(lia)) as DP. rewrite Hp8, Z.add_0_r in DP.
      assert (H1 : lf_F cx fp / 8 + 128 <= p / 8) by lia.
      assert (H2 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia. }
  assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc8); rewrite Hc8;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  assert (Hmk8 : mk mod 8 = 0) by (rewrite Zmod_divides in Bk16 by lia; destruct Bk16 as (c & Hc8); rewrite Hc8;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  unfold LLVMF_STK in *.
  split; [unfold lf_saved_fp; clia|].
  split.
  { unfold lf_header_fp. change (fs_frame_bytes LF_CID) with 1024.
    unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *. clia. }
  split; [unfold lf_slots_fp; clia|]. split; [unfold lf_cur_fp; clia|].
  split.
  { intros [Hj | [Hj | [Hj | Hj]]].
    - destruct Hj as [Hj | [Hj | (f & n & Hfn & Hj)]].
      + rewrite HMS in Hj. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Hj.
        apply (NI a); [unfold YImgTop.IMG_TOP; clia | exact Ha].
      + rewrite HMS in Hj. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Hj.
        apply (NI a); [unfold YImgTop.IMG_TOP; clia | exact Ha].
      + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n. apply (NB f AMF_BLOCK a HfnT); [change (req_size AMF_BLOCK) with 1304; unfold AMF_BLOCK in Hj; clia | exact Ha].
    - rewrite HLN in Hj. apply (NI a); [unfold LA_NUL, LA_LONG_ALIAS, YImgTop.IMG_TOP in *; clia | exact Ha].
    - exact (NI a (RO a Hj) Ha).
    - assert (Hn : 0 < c_n cx) by clia.
      pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn) as Hpb.
      apply (NB _ _ a Hpb); [unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); clia | exact Ha]. }
  split.
  { intros [(x & Hx & ->) | (x & Hx & ->)].
    - exact (SHD md MD_SIZE x Hmd8 DmF Hx ltac:(clia)).
    - exact (SHD mk MK_SIZE x Hmk8 DkF Hx ltac:(clia)). }
  intros [Hd | [Hd | [Hd | [Hd | [Hd | Hd]]]]].
  - apply (NI a); [unfold LA_G_NL, NK_SIZE, YImgTop.IMG_TOP in *; clia | exact Ha].
  - apply (NI a); [unfold LA_G_NAMES, G_NAMES_SIZE, YImgTop.IMG_TOP in *; clia | exact Ha].
  - apply (NI a); [unfold LA_LONG_ALIAS, YImgTop.IMG_TOP in *; clia | exact Ha].
  - apply (NB md MD_SIZE a Bmd); [change (req_size MD_SIZE) with 8856; unfold MD_SIZE in Hd; clia | exact Ha].
  - apply (NB mk MK_SIZE a Bmk); [change (req_size MK_SIZE) with 516; unfold MK_SIZE in Hd; clia | exact Ha].
  - exact (NI a (RO a Hd) Ha).
Qed.

(* the frame's shadow after a run that stored v at shadow indices [lo, hi) *)
Lemma u_fsh_upd : forall cx fp (W : world SEGS) ms ms' (X : Z -> Prop) sh sh' lo hi v,
  lf_fshadow cx fp W ms sh -> kagree SEGS X (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  length sh' = length sh ->
  (forall i, (i < length sh)%nat -> ~ (lo <= Z.of_nat i < hi) -> ~ X (lf_SH cx fp + Z.of_nat i) /\ nth i sh' 0 = nth i sh 0) ->
  (forall i, (i < length sh)%nat -> lo <= Z.of_nat i < hi ->
     aview SEGS (w_H W) (ms_mem ms') (lf_SH cx fp + Z.of_nat i) = Some v /\ nth i sh' 0 = v) ->
  lf_fshadow cx fp W ms' sh'.
Proof.
  intros cx fp W ms ms' X sh sh' lo hi v Hf KA Hl Hout Hin i Hi. rewrite Hl in Hi.
  destruct (Z_lt_le_dec (Z.of_nat i) lo) as [H1 | H1]; [|destruct (Z_lt_le_dec (Z.of_nat i) hi) as [H2 | H2]].
  - destruct (Hout i Hi ltac:(lia)) as (NX & Ne). rewrite Ne.
    rewrite (aview_of_kagree SEGS X _ _ _ _ _ KA NX). exact (Hf i Hi).
  - destruct (Hin i Hi ltac:(lia)) as (Hv & Ne). rewrite Ne. exact Hv.
  - destruct (Hout i Hi ltac:(lia)) as (NX & Ne). rewrite Ne.
    rewrite (aview_of_kagree SEGS X _ _ _ _ _ KA NX). exact (Hf i Hi).
Qed.


(* +0x808: model_read has returned; the object F + 0x20 is in scope and holds the alias model_read read *)
Definition u_r_inv (i j : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (nm : list byte) (reqs0 : list (list byte))
    (K0 : kstate),
  lf_shape fy LU_mr ms3 /\
  getr (ms_regs ms3) 23 = w64 (md + MD_MARK + MARK_LEN * j) /\ getr (ms_regs ms3) 20 = w64 j /\
  getr (ms_regs ms3) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK)) /\
  u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_Z cx fp k2 ly3 S3 W3 ms3 md3 /\
  0 <= j < md_n_mark mbs /\ nk_n_sent kbs = 0 /\
  nth_error (mk_names gbs) (Z.to_nat j) = Some nm /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (md + MD_MARK + MARK_LEN * j) nm /\ (length nm < 16)%nat /\
  unmark_walk lf_tab (skipn (Z.to_nat j) (mk_names gbs)) reqs0 K0 = unmark lf_tab (mk_names gbs) [] (nk_kstate kbs) /\
  md_reqs mbs = r_reqs (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) /\
  md_kstate mbs kbs = r_state (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0) /\
  getr (ms_regs ms3) 10 = w64 (norm_rc (r_rc (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0))) /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_WA) (r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX reqs0 K0)) /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_WA) 256 /\
  0 <= k_sock K0 < 2 ^ 31 /\ 0 <= k_send K0 < 2 ^ 31 /\ 0 <= k_end K0 < 2 ^ 31.

(* a byte a run stored as a one-byte literal *)
Lemma u_byte_lit : forall (E : env) H (mem : word -> option byte) r base off z,
  region_ok SEGS E (mrestrict H mem) r -> base_val E (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CVal 1 (SLit z))) (YP09.r_chunks r) -> 0 <= z < 256 ->
  aview SEGS H mem (base + off) = Some z.
Proof.
  intros E H mem r base off z (_ & _ & _ & HC) Hb Hin Hz.
  rewrite Forall_forall in HC. specialize (HC _ Hin). rewrite Hb in HC.
  destruct (HC 0 ltac:(cbn; lia)) as (b & Hcb & Hmb). cbn [c_off YP09.c_val cbyte] in Hcb, Hmb.
  injection Hcb as <-. rewrite Z.add_0_r in Hmb. unfold aview. rewrite Hmb. cbn [option_map]. f_equal.
  unfold byte_of_word. rewrite Z_to_bv_unsigned. cbn [sv_denot]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
  rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite Z.shiftr_0_r. apply Z.mod_small. lia.
Qed.

(* a present range as an abuf *)
Lemma u_abuf : forall H (mem : word -> option byte) a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> apresent H mem x) -> abuf SEGS (mrestrict H mem) a n.
Proof.
  intros H mem a n H0 H1 H2 HP. exists (abytes_of SEGS (mrestrict H mem) a (Z.to_nat n)).
  rewrite abytes_of_length. split; [lia|]. split.
  - apply abytes_of_abytes; [lia | lia|]. intros k Hk.
    destruct (HP (a + Z.of_nat k) ltac:(lia)) as (Hh & b & Hb). exists b. unfold mbyte, mrestrict. rewrite Hh, Hb.
    reflexivity.
  - rewrite abytes_of_length. intros k Hk. apply (apresent_writable SEGS). apply HP. lia.
Qed.

(* the object F + 0x20 in scope: its 256 bytes addressable, their shadow visible *)
Lemma u_buf_shadow : forall cx fp (W : world SEGS) ms,
  lf_fshadow cx fp W ms SH_Z -> lf_F cx fp mod 32 = 0 -> 4096 <= lf_F cx fp -> lf_F cx fp + 1024 <= alloc_ceiling ->
  range_addressable (ard SEGS (rdW W (ms_mem ms))) SHADOW_OFF (lf_F cx fp + LO_WA) 256 /\
  shadow_hull_vis (ard SEGS (rdW W (ms_mem ms))) (lf_F cx fp + LO_WA) 256.
Proof.
  intros cx fp W ms Hfs' F32 F4 Fc.
  pose proof asan_consts as ((C1a & C1b) & _).
  set (F := lf_F cx fp) in *.
  assert (Fm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
  assert (SHF : lf_SH cx fp = SHADOW_OFF + F / 8) by reflexivity.
  assert (S4 : lf_SH cx fp mod 4 = 0).
  { rewrite SHF. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D.
    assert (Q : F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia;
      apply Z.div_mul; lia).
    rewrite Q. unfold SHADOW_OFF. replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia.
    apply Z_mod_mult. }
  split.
  - intros x Hx. unfold LO_WA in Hx. exists 0. split; [|left; reflexivity].
    rewrite ard_aview. unfold shadow_of_addr.
    assert (Hix : 4 <= x / 8 - F / 8 < 36).
    { pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite Fm8, Z.add_0_r in DF.
      assert (A1 : F / 8 + 4 <= x / 8) by (apply Z.div_le_lower_bound; lia).
      assert (A2 : x / 8 < F / 8 + 36) by (apply Z.div_lt_upper_bound; lia). lia. }
    replace (SHADOW_OFF + x / 8) with (lf_SH cx fp + Z.of_nat (Z.to_nat (x / 8 - F / 8))) by (rewrite SHF; lia).
    rewrite (Hfs' (Z.to_nat (x / 8 - F / 8)) ltac:(rewrite SH_Z_len; lia)).
    rewrite SH_Z_nth by lia. destruct (Nat.leb_spec 4 (Z.to_nat (x / 8 - F / 8))), (Nat.ltb_spec (Z.to_nat (x / 8 - F / 8)) 36);
      try lia. reflexivity.
  - intros s Hs. rewrite ard_aview. unfold shadow_addr, LO_WA in Hs.
    pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite Fm8, Z.add_0_r in DF.
    assert (A1 : (F + 32) / 8 = F / 8 + 4) by (rewrite DF at 1; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia;
      apply Z.div_mul; lia).
    assert (A2 : (F + 32 + 256 - 1) / 8 = F / 8 + 35)
      by (rewrite DF at 1; replace (8 * (F / 8) + 32 + 256 - 1) with (7 + (F / 8 + 35) * 8) by lia;
          rewrite Z.div_add by lia; reflexivity).
    rewrite A1, A2 in Hs.
    replace (SHADOW_OFF + (F / 8 + 4)) with (lf_SH cx fp + 4) in Hs by (rewrite SHF; lia).
    replace (SHADOW_OFF + (F / 8 + 35)) with (lf_SH cx fp + 35) in Hs by (rewrite SHF; lia).
    assert (Hl : lf_SH cx fp <= (lf_SH cx fp + 4) / 8 * 8)
      by (pose proof (Z.div_mod (lf_SH cx fp) 8 ltac:(lia)) as DS; pose proof (Z.mod_pos_bound (lf_SH cx fp) 8 ltac:(lia));
          assert (lf_SH cx fp mod 8 = 0 \/ lf_SH cx fp mod 8 = 4) by (rewrite <- (Z.mod_mod (lf_SH cx fp) 8) by lia;
            clear - S4; lia); lia).
    assert (Hu : (lf_SH cx fp + 35) / 8 * 8 + 8 <= lf_SH cx fp + 43)
      by (pose proof (Z.div_mod (lf_SH cx fp + 35) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (lf_SH cx fp + 35) 8 ltac:(lia)); lia).
    replace s with (lf_SH cx fp + Z.of_nat (Z.to_nat (s - lf_SH cx fp))) by lia.
    rewrite (Hfs' (Z.to_nat (s - lf_SH cx fp)) ltac:(rewrite SH_Z_len; lia)). discriminate.
Qed.

Lemma u_head : forall POST i j,
  FROM POST (u_r_inv i j) -> FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i j HR cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HL.
  destruct HL as (md & mk & P & N & kbs & mbs & gbs & T3 & Hsh & R23 & R20 & R18 & HU & Hj & Hns & HUW).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg /\ lf_SH cx fp mod 4 = 0).
  { rewrite HFS. assert (D1 : 4096 / 8 <= lf_F cx fp / 8) by (apply Z.div_le_mono; clia).
    assert (D2 : lf_F cx fp / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; clia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    pose proof (Z.div_mod (lf_F cx fp) 32 ltac:(clia)) as D. rewrite F32, Z.add_0_r in D.
    assert (Q : lf_F cx fp / 8 = 4 * (lf_F cx fp / 32)) by (rewrite D at 1; replace (32 * (lf_F cx fp / 32)) with
      ((4 * (lf_F cx fp / 32)) * 8) by clia; apply Z.div_mul; clia).
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. split; [clia|]. split; [clia|].
    rewrite Q. replace (2147450880 + 4 * (lf_F cx fp / 32)) with ((536862720 + lf_F cx fp / 32) * 4) by clia.
    apply Z_mod_mult. }
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp) by (rewrite E19; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E u_l_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_body)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold u_l_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, u_fs_rg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [unfold kLowMemEnd in *; clia|]. split; [unfold kHighMemBeg in *; clia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. clia.
    - cbn. split; exact I.
    - split; [|split; exact I]. cbn [u_l_facts f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
      unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. split; [clia|]. split; [exact (proj2 (proj2 SHB))|]. clia. }
  rewrite (lf_shape_eta fy LU_body ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_body)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { cbn [ss_mem u_l_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_fs_rg base_val] in Ha. rewrite U19 in Ha.
    left. split; [|clia]. right; right; right. exists LF_CID, fp. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID / 8) with 128.
    unfold shadow_addr. rewrite <- HFS. clia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  set (X := fun a => lf_SH cx fp + 4 <= a mod 2 ^ 64 < lf_SH cx fp + 36).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem u_l_ss) _ _ X HFrA). intros a (r & Hr & Hw). unfold X.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem u_l_ss In] in Hr. destruct Hr as [<- | []].
    cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_fs_rg base_val] in Hw. rewrite U19 in Hw. clia. }
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> X a ->
     lf_SH cx fp + 4 <= a < lf_SH cx fp + 36 /\
     ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_slots_fp cx a /\
     ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\ ~ lf_data_fp md mk a).
  { intros a Hf HXa. pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
      LAWS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk Hf) as R.
    unfold X in HXa. rewrite Z.mod_small in HXa by exact (proj1 R). split; [exact HXa|].
    exact (u_fs_out cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk ltac:(clia)). }
  pose proof (lf_saved_keep X cx W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (NX a ltac:(tauto) HXa)) Ha) Hsv) as Hsv'.
  pose proof (lf_header_keep X cx fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (NX a ltac:(tauto) HXa))) Ha) Hhd) as Hhd'.
  pose proof (lf_slots_keep X cx md mk fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))) Ha) Hsl) as Hsl'.
  pose proof (lf_cur_keep X cx W3 ms3 W3 msA P N KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))) Ha) Hcur) as Hcur'.
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hjbk) as Hjbk'.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))))) Ha) Hblk) as Hblk'.
  pose proof (lf_data_keep X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    (fun a Ha HXa => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))))) Ha) Hdat) as Hdat'.
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
  assert (RG0 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 0 (ss_mem ssA) u_fs_rg))
    by exact (st_ok_region_nth E ssA (restrict (w_H W3) msA) 0 _ HS eq_refl).
  assert (Hfs' : lf_fshadow cx fp W3 msA SH_Z).
  { apply (u_fsh_upd cx fp W3 ms3 msA X LF_SH0 SH_Z 4 36 0 Hfs KA); [reflexivity | |].
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0. split; [|rewrite (SH_Z_nth i0 Hi0); destruct (Nat.leb_spec 4 i0), (Nat.ltb_spec i0 36);
        cbn [andb]; try reflexivity; clia].
      unfold X. rewrite Z.mod_small by (unfold kHighMemBeg in *; clia). clia.
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0. split; [|rewrite (SH_Z_nth i0 Hi0); destruct (Nat.leb_spec 4 i0), (Nat.ltb_spec i0 36);
        cbn [andb]; try reflexivity; clia].
      apply (u_byte_lit E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) 0 RG0).
      + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
      + assert (Hc : forall k, 4 <= k < 36 -> In (YP09.mkChunk k (CVal 1 (SLit 0))) (YP09.r_chunks (nth 0 (ss_mem ssA) u_fs_rg))).
        { intros k Hk. cbn [nth ss_mem ssA setpc YP09.r_chunks].
          assert (Hk' : k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/
            k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
            k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/
            k = 34 \/ k = 35) by clia.
          repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst k. cbn [In]. tauto. }
        apply Hc. clia.
      + clia. }
  (* the call of model_read at 0x82fd8 *)
  pmkst HS.
  assert (Hpc : ss_pc ssA = pa_sigma LS_model_read) by reflexivity.
  rewrite Hpc, (lv_sigma LV).
  replace (link_sigma LS_model_read) with MODEL_READ_A by reflexivity.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
  try rewrite (img_env_codeptr E HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl), R22 in Q10.
  rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl), R23 in Q11. rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl), R26 in Q14.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9.
  rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21.
  rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  pose proof (lv_text LV) as HBASE.
  pose proof Hblk' as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
    & Bamm & Bamk).
  pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) md4 md MD_SIZE HARA Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  pose proof Hdat as (_ & _ & _ & _ & _ & _ & _ & Dmwf0 & _).
  pose proof Dmwf0 as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
  assert (Hj32 : 0 <= j <= 31) by clia.
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite Q2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
  assert (Ra0 : aarg (ms_regs msA) 0 = md) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; clia).
  assert (Ra1 : aarg (ms_regs msA) 1 = md + MD_MARK + MARK_LEN * j)
    by (rewrite ar_aarg1, Q11; unfold w64; apply unsigned_lit_small; unfold MD_MARK, MARK_LEN, MD_SIZE in *; clia).
  assert (Ra2 : aarg (ms_regs msA) 2 = 0) by (rewrite ar_aarg2, Q12; reflexivity).
  assert (Ra3 : aarg (ms_regs msA) 3 = 0) by (rewrite ar_aarg3, Q13; reflexivity).
  assert (Ra4 : aarg (ms_regs msA) 4 = lf_F cx fp + LO_WA)
    by (rewrite ar_aarg4, Q14; unfold w64; apply unsigned_lit_small; unfold LO_WA; clia).
  assert (Ra5 : aarg (ms_regs msA) 5 = 256) by (rewrite ar_aarg5, Q15; reflexivity).
  pose proof Hjbk' as (Jk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem msA) md4 k2 HB HJ Hfr) as (HFa2 & _ & _ & _ & _ & Fpres2 & Fshp2 & Fsep2).
  pose proof (Fsep2 md MD_SIZE Bmd) as DmF. unfold zdisjoint in DmF. cbn [fst snd] in DmF.
  change (req_size MD_SIZE) with 8856 in DmF.
  pose proof Hdat' as (Dk & Dwf & Dtab & _ & _ & _ & Dmd & Dmwf & _ & _ & (Dmn & Dmm) & _).
  destruct (u_mark_slot SEGS _ md mbs j Dmd Dmwf Hj) as (Hnm & Hnmc & Hnml).
  set (nm := cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN)) in *.
  assert (HK8 : 0 <= MODEL_READ_AK <= LLVMF_STK - 448) by (rewrite MODEL_READ_AK_val; unfold LLVMF_STK; lia).
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) MODEL_READ_AK HB HJ Hblk' Rsp HK8)
    as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  set (F := lf_F cx fp) in *.
  assert (BUFI : forall x, F + LO_WA <= x < F + LO_WA + 256 -> ~ in_img SEGS x /\ apresent (w_H W3) (ms_mem msA) x)
    by (intros x Hx; destruct (Fpres2 x ltac:(unfold LO_WA in *; clia)) as (P1 & P2); exact (conj P2 P1)).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 MODEL_READ_A) (ms_mem msA) (seg_rom SEGS)) md4)
    with (@cfg_at fy SEGS MODEL_READ_A (ms_regs msA) (ms_mem msA) md4).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (MODEL_READ fy).
  - exact HB.
  - exact HJ.
  - exact HRO.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite Q3. exact Gp.
  - rewrite Q4. exact Tp.
  - exact Rsp.
  - exact HK8.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
  - apply (ar_side_room S3 fp _ Hfr). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
    replace (F + LO_WA =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; unfold LO_WA; clia).
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Bmd Bmc). unfold MD_SIZE in *. clia.
    + cbn in Hr. clia.
    + apply (ar_ajw_frame B); [rewrite HFa2; change (fs_frame_bytes LF_CID) with 1024; unfold LO_WA in *; clia|].
      intros Hs. unfold LLVMF_STK, LO_WA in *. clia.
  - intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
    replace (F + LO_WA =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; unfold LO_WA; clia).
    intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in *. clia.
    + cbn in Hr. clia.
    + destruct (BUFI a ltac:(clia)) as (NI & _). apply NI.
      destruct Hro as [(s & Hs & _ & Hsr) | Hr2]; [exists s; split; [exact Hs | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2).
  - (* the read set *)
    intros a [(H1 & s & Hs & Ha) | (bs & i0 & p & s & Hbs & Hi0 & Hp & Hs & Ha)].
    + rewrite Ra1 in Hs, Ha. pose proof (kp_acstr_unique _ _ _ _ _ Hs Hnmc) as Es. subst s.
      apply (lf_blk_akb B ly3 S3 _ _ md MD_SIZE a Bmd). change (req_size MD_SIZE) with 8856.
      unfold MD_MARK, MARK_LEN in *. clia.
    + exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs _ _ HB HJ HRO Hdat' bs i0 p s a Hbs Hi0 Hp Hs Ha).
  - (* the Pre *)
    destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & _).
    assert (Fm8 : F mod 8 = 0).
    { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D. rewrite D.
      replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
    assert (SHF : lf_SH cx fp = SHADOW_OFF + F / 8) by reflexivity.
    destruct (u_buf_shadow cx fp W3 msA Hfs' F32 F4 Fc) as (BRA & BHV).
    exists mbs, kbs, lf_tab, (Some nm).
    rewrite Ra0, Ra1, Ra2, Ra3, Ra4, Ra5.
    split; [exact Dmd|]. split; [exact Dmwf|]. split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dtab|].
    split; [split; [unfold MD_MARK, MARK_LEN in *; clia | exact Hnmc]|].
    split; [intros Hc; exfalso; apply Hc; reflexivity|].
    split; [intros _ _; apply u_abuf; [unfold LO_WA; clia | lia | unfold LO_WA in *; clia |];
      intros x Hx; exact (proj2 (BUFI x Hx))|].
    split; [exact M1|]. split; [exact M2|].
    split.
    { intros s Hs. injection Hs as <-.
      destruct (lf_md_sub SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) MODEL_READ_AK
        (md + MD_MARK + MARK_LEN * j) (Z.of_nat (length nm) + 1) HB HJ Hblk' Rsp HK8
        ltac:(unfold MD_MARK, MARK_LEN; clia) ltac:(unfold MD_MARK, MARK_LEN, MD_SIZE; clia) ltac:(clia))
        as (S1 & S2 & S3' & S4).
      split; [unfold MD_MARK, MARK_LEN in *; clia|]. split; [clia|]. split; [exact S3'|]. split; [exact S1|].
      split; [exact S2|]. split; [exact S4|].
      intros a0 Ha0.
      apply (lf_md_tail SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk T3 (md + MD_MARK + MARK_LEN * j) (Z.of_nat (length nm) + 1)
        HB HJ Hblk' ltac:(unfold MD_MARK, MARK_LEN; clia) ltac:(unfold MD_MARK, MARK_LEN, MD_SIZE; clia) ltac:(clia)).
      replace (Z.of_nat (length nm) + 1 - 1) with (Z.of_nat (length nm)) by lia. exact Ha0. }
    split.
    { intros i0 n2 ix p Hn Hp Rp.
      exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs (ms_regs msA) MODEL_READ_AK HB HJ HRO Hdat' Rsp HK8
        i0 n2 ix p Hn Hp Rp)). }
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].
    split; [exact M8|]. split; [exact M9|].
    split; [intros Hc; exfalso; apply Hc; reflexivity|].
    split; [intros _; unfold apart_frame; left; rewrite Rsp; rewrite MODEL_READ_AK_val; unfold LO_WA, LLVMF_STK in *; clia|].
    split; [rewrite (ts_errno B TB); unfold apart, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO,
      MD_SIZE in *; clia|].
    split; [intros Hc; exfalso; apply Hc; reflexivity|].
    split; [intros _ _; apply md_apart_of_disj; [lia | lia|]; intros x H1 H2;
      exact (proj1 (BUFI x H2) (md_errno_img B TB HSEGS x H1))|].
    split; [intros Hc; exfalso; apply Hc; reflexivity|].
    split.
    { intros _ _.
      split.
      { assert (Ap : apart (F + LO_WA) 256 LA_G_NL NK_SIZE).
        { apply md_apart_of_disj; [lia | unfold NK_SIZE; lia|]. intros x H1 H2.
          apply (proj1 (BUFI x H1)). apply (proj1 (IMG x ltac:(left; exact H2))). }
        unfold apart in Ap. unfold apart_gnl. exact Ap. }
      split; [unfold apart, LO_WA, MD_SIZE in *; clia|].
      split.
      { intros i0 n2 ix p Hn Hp.
        pose proof (lf_tab_names_short) as Hsn. rewrite forallb_forall in Hsn.
        specialize (Hsn (n2, ix) (nth_error_In _ _ Hn)). apply Nat.leb_le in Hsn. cbn [fst] in Hsn.
        destruct (Z_lt_le_dec p 0) as [Hp0 | Hp0]; [unfold apart, LO_WA in *; clia|].
        destruct (Z_lt_le_dec p (2 ^ 64)) as [Hp1 | Hp1]; [|unfold apart, LO_WA in *; clia].
        destruct (lf_tab_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) md4 k2 md mk kbs mbs gbs HB HJ HRO Hdat' i0 n2 ix p Hn Hp ltac:(lia))
          as (_ & _ & _ & _ & _ & _ & _ & C7).
        apply md_apart_of_disj; [lia | lia|]. intros x H1 H2.
        exact (proj1 (BUFI x H1) (proj1 (C7 x ltac:(lia)))). }
      split; [destruct Fapp as (Fa1 & Fa2); unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
        kHighMemEnd, ASAN_CEIL, LO_WA in *; clia|].
      split; [exact BRA | exact BHV]. }
    split.
    { intros s Hs. injection Hs as <-. split; [intros Hc; exfalso; apply Hc; reflexivity|].
      intros _ _. unfold apart, LO_WA, MD_MARK, MARK_LEN in *. clia. }
    intros Hc; exfalso; apply Hc; reflexivity.
  - (* the return, +0x808 *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (model_read_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (LC : lf_call B cx MODEL_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
    { split; [lia|]. split; [rewrite MODEL_READ_AK_val; unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
    assert (HE : forall a, Er a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)).
    { intros a (r & Hin & Hr). unfold model_read_awr in Hin. rewrite Ra0, Ra2, Ra3, Ra4, Ra5 in Hin. unfold aivl in Hin.
      replace (F + LO_WA =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; unfold LO_WA; clia).
      destruct Hin as [<- | [<- | [<- | []]]]; cbn in Hr; [left; exact Hr | lia | right; unfold LO_WA in *; fold F; clia]. }
    pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
    assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
    assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
    pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msA)) md mk HAR2 Pmd Pmk) as WC.
    (* model_read's post *)
    specialize (Hpost mbs kbs lf_tab (Some nm)). rewrite Ra0, Ra1, Ra2, Ra3, Ra4, Ra5 in Hpost.
    destruct (Hpost Dmd Dk Dtab ltac:(split; [unfold MD_MARK, MARK_LEN in *; clia | exact Hnmc]))
      as (Hrc & (mbs' & Hmd2 & Hmwf2 & Hnx2 & Hso2 & Hse2 & Hrq2 & Hnr2 & Hnm2 & Hmm2) & _ & Hal & _ & Hab).
    clear Hpost.
    destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp MODEL_READ_AK ly3 S3 ly2 S2 W3 msA md4 W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs' T3 _ P N SH_Z
      HB HJ Hfr LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(rewrite SH_Z_len; lia) Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat'
      Hmd2 Hmwf2 Hnm2 Hmm2) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
    pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
      ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
    pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    destruct (u_mark_slot SEGS _ md mbs' j Hmd2 Hmwf2 ltac:(rewrite Hnm2; exact Hj)) as (Hnm' & Hnmc' & _).
    rewrite Hmm2, Hnm in Hnm'. injection Hnm' as Enm. rewrite <- Enm in Hnmc'.
    apply (HR cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, kbs, mbs', gbs, T3, nm, (md_reqs mbs), (md_kstate mbs kbs).
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1. unfold LU_mr, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    cbn [ms_regs ms2 mkst].
    split; [rewrite P23, Q23; exact R23|]. split; [rewrite P20, Q20; exact R20|]. split; [rewrite P18, Q18; exact R18|].
    split.
    { split; [exact Hi|]. split.
      { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
        rewrite R8, R9. repeat split; assumption. }
      split.
      { unfold u_regs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P21, P22, P24, P25, P26, P27, Q19, Q21, Q22, Q24,
          Q25, Q26, Q27. repeat split; assumption. }
      split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hcur2|].
      split; [exact Hjbk3|]. split; [exact Hblk3|]. split; [exact Hdat2 | exact Hop]. }
    split; [rewrite Hnm2; exact Hj|]. split; [exact Hns|].
    split; [rewrite Dmm; exact Hnm|]. split; [exact Hnmc'|]. split; [exact Hnml|].
    split; [exact HUW|].
    assert (RQ : forall X : rres -> Prop, X (read_model lf_tab (Some nm) 0 256 (md_reqs mbs) (md_kstate mbs kbs)) ->
      X (Rres (norm_rc (r_rc (read_core lf_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs))))
              (r_kind (read_core lf_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))
              (r_alias (read_core lf_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))
              (r_reqs (read_core lf_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))
              (r_state (read_core lf_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)))))
      by (intros X0 HX0; exact HX0).
    cbn [read_model r_rc r_kind r_alias r_reqs r_state] in Hrc, Hnx2, Hso2, Hse2, Hrq2, Hal.
    split; [exact Hrq2|].
    split.
    { destruct (u_read_ce lf_tab (Some nm) 0 ALIAS_MAX (md_reqs mbs) (md_kstate mbs kbs)) as (Ce & Ee).
      apply u_md_kstate_of; [exact Hnx2 | exact Hso2 | exact Hse2 | rewrite Ce; reflexivity | rewrite Ee; reflexivity]. }
    split; [exact Hrc|].
    split; [exact (Hal ltac:(unfold LO_WA; clia) ltac:(lia))|].
    split; [exact (Hab ltac:(unfold LO_WA; clia) ltac:(lia))|].
    pose proof Dwf as (_ & _ & _ & _ & _ & _ & _ & _ & Wend & _).
    pose proof Dmwf as (_ & _ & Wso & Wse & _).
    unfold md_kstate. cbn [k_sock k_send k_end]. split; [exact Wso|]. split; [exact Wse | exact Wend].
Qed.

End a.
