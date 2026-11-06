(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module paths and module names changed; 144 of its 177 lines of code are new or changed and 453 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm (operation
   byte mod 6 = 2, +0x6a8 .. +0xcd8, +0x1120 .. +0x11fc; listing (internal path)
   (internal record, sha256 e84d6f0c6974)): the arm's own cuts after kernel (Op2K.v o2_k_inv at +0xad4).
   They are inside the arm's segment, so they are this walk's and not the interface's.

     o2_n_inv i   +0xb54   model_begin is done, the name t is not empty; the frame object is not yet in scope
     o2_r_inv i   +0xc04   model_read(m, t, F + 0x160, 32, F + 0x1a0, 256) has returned; the object is in scope
     o2_m_inv i   +0x1178  the inlined remember of t into the model is next
     o2_u_inv i   +0xc0c   the model's answer is in s7; the object goes out of scope next
     o2_q_inv i   +0xc9c   mark_quietly(mk, name) is next: s7 = the model's answer, the frame's shadow LF_SH0

   The model's answer is Op2Lib.v o2_mm over the name, the marks the marks block holds (mk_names gbs), no request
   owed and the kernel state model_begin left (nk_kstate kbs: g_nl is not written before mark_quietly). From
   +0xb54 on the model's marks may lead the marks block's by the remembered name, so the cuts carry Mq.v's
   lf_data_nm (lf_data but marks_are) and the model's marks as an equation.
   Registers at every cut: s3 = the frame's shadow, s4 = the name, s6 = m (but inside remember), s8 = 2^64 - 8,
   s9 = i, s10 = F + 0x20 (but inside remember), s11 = the shadow base.

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
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputSel
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.
Definition LO2_n : Z := AF_LLVMFuzzerTestOneInput + 0xb54.    (* 0x83328 *)
Definition LO2_r : Z := AF_LLVMFuzzerTestOneInput + 0xc04.    (* 0x833d8 *)
Definition LO2_u : Z := AF_LLVMFuzzerTestOneInput + 0xc0c.    (* 0x833e0 *)
Definition LO2_m : Z := AF_LLVMFuzzerTestOneInput + 0x1178.   (* 0x8394c *)
Definition LO2_q : Z := AF_LLVMFuzzerTestOneInput + 0xc9c.    (* 0x83470 *)

(* the frame's shadow with the object F + 0x160 (32 bytes, shadow 0x2c .. 0x2f) and F + 0x1a0 (256 bytes, shadow
   0x34 .. 0x53) in scope (+0xb54 .. +0xbe0) *)
Definition SH_M : list Z :=
  repeat 241 4 ++ repeat 248 32 ++ repeat 242 8 ++ repeat 0 4 ++ repeat 242 4 ++ repeat 0 32
  ++ repeat 242 8 ++ repeat 248 5 ++ repeat 242 5 ++ repeat 248 5 ++ repeat 243 5.
Lemma SH_M_len : length SH_M = 112%nat. Proof. reflexivity. Qed.

(* the model's answer to a mark of nm *)
Definition o2_MM (nm : option (list byte)) (kbs gbs : list byte) : mres :=
  o2_mm lf_tab nm (mk_names gbs) [] (nk_kstate kbs).
(* model_read's answer to the non-empty name t *)
Definition o2_RR (t kbs : list byte) : rres :=
  read_model lf_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variables LF_MO_SET LF_MO_OP : Z.

(* lf_data_nm across a step: lf_data_keep (Keep.v) without marks_are, which it only passes through *)
Lemma lf_data_nm_keep : forall X m m' cx md mk kbs mbs gbs, kagree SEGS X m m' ->
  wcarry_on m m' (lf_data_fp_w md mk) -> (forall a, lf_data_fp md mk a -> ~ X a) ->
  lf_data_nm cx md mk kbs mbs gbs m -> lf_data_nm cx md mk kbs mbs gbs m'.
Proof.
  intros X m m' cx md mk kbs mbs gbs HK HW HX
    (Hnl & Hwf & Hif & Ho & Hmi & Hoc & Hmd & Hmwf & Hmk & Hkwf & Hifp & Hgn & Hgw & Hodd & Htx & Hla).
  assert (XR : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ X a)
    by (intros a Ha; apply HX; right; right; right; right; right; exact Ha).
  assert (Hodd' := lf_odd_at_keep X m m' HK XR Hodd). assert (Htx' := lf_texts_at_keep X m m' HK XR Htx).
  assert (Hsl' : lf_la_slack m').
  { destruct Hla as (_ & _ & (sl & Hsl & Hs)). exists sl. split; [|exact Hs].
    apply (au8arr_keep SEGS X m m' _ sl HK); [| |exact Hsl]; rewrite Hs; change (Z.of_nat 3) with 3; intros i Hi.
    - replace (LA_LONG_ALIAS + 301 + i) with (LA_LONG_ALIAS + (301 + i)) by lia.
      apply (wcarry_on_sub m m' (lf_data_fp_w md mk) LA_LONG_ALIAS 304 HW); [|lia].
      intros j Hj. unfold lf_data_fp_w. right; right; left. lia.
    - apply HX. unfold lf_data_fp. right; right; left. lia. }
  assert (XG : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) by (intros a Ha; apply HX; left; exact Ha).
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a)
    by (intros a Ha; apply HX; right; left; exact Ha).
  assert (XL : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> ~ X a)
    by (intros a Ha; apply HX; right; right; left; lia).
  assert (XO : forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a)
    by (intros a Ha; apply HX; right; right; right; right; right; right; unfold LA_ODD, PCAP_RLO, PCAP_RHI in *; lia).
  assert (WS : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) -> wcarry SEGS m m' a n)
    by (intros a n Ha; exact (wcarry_on_sub m m' _ a n HW Ha)).
  assert (Hifp' : lf_ifp m' 64) by exact (lf_ifp_keep_ro X m m' 64 HK ltac:(lia) XG XO Hifp).
  assert (Hnl' : anlk_at SEGS m' LA_G_NL kbs).
  { apply (anlk_keep SEGS X m m' _ kbs HK); [|intros i Hi; apply XG; lia | exact Hnl].
    apply WS. intros i Hi. unfold lf_data_fp_w. left. lia. }
  assert (Hif' : aiftab_at SEGS m' LA_G_NL kbs lf_tab)
    by exact (lf_aiftab_keep_ro X m m' kbs HK XG XN Hifp Hifp' Hodd' Hif).
  assert (Hmd' : amodel_at SEGS m' md mbs).
  { apply (amodel_keep SEGS X m m' _ mbs HK); [|intros i Hi; apply HX; right; right; right; left; lia | exact Hmd].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; left. lia. }
  assert (Hmk' : amarks_at SEGS m' mk gbs).
  { apply (amarks_keep SEGS X m m' _ gbs HK); [|intros i Hi; apply HX; right; right; right; right; left; lia | exact Hmk].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; right. lia. }
  assert (Hgw' : lf_gnames_w m').
  { apply (lf_gnames_w_keep X m m' HK); [|exact XN | exact Hgw].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; left. unfold G_NAMES_SIZE in *. lia. }
  assert (Hla' : lf_la_at m').
  { apply (lf_la_at_keep_ns X m m' HK); [|exact XL | exact Hsl' | exact Hla].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; left. lia. }
  exact (conj Hnl' (conj Hwf (conj Hif' (conj Ho (conj Hmi (conj Hoc (conj Hmd' (conj Hmwf (conj Hmk' (conj Hkwf
    (conj Hifp' (conj (lf_gnames_at_keep X m m' 64 HK ltac:(lia) XN Hgn) (conj Hgw'
    (conj Hodd' (conj Htx' Hla'))))))))))))))).
Qed.

(* the registers the arm keeps from the loop *)
Definition o2_kregs (cx : lcx) (fp i : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

(* what every cut after model_begin carries; sh is the frame's shadow *)
Definition o2_mem2 (i md mk P N : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)) (sh : list Z)
    (cx : lcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    : Prop :=
  0 <= i <= 47 /\ lf_core cx ms3 /\ o2_kregs cx fp i ms3 /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 sh /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3
    T3 [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data_nm cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * i /\ nk_n_sent kbs = 0.

(* +0xb54: the name t is not empty, model_begin is done *)
Definition o2_n_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_n ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 18 = w64 (lf_F cx fp + LO_B160) /\ getr (ms_regs ms3) 21 = w64 (md + MD_N_MARK) /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\ md_reqs mbs = [] /\ md_kstate mbs kbs = nk_kstate kbs.

(* +0xc04: model_read has answered (a0); its kind and alias are in the two objects, which are in scope *)
Definition o2_r_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_r ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 18 = w64 (lf_F cx fp + LO_B160) /\ getr (ms_regs ms3) 21 = w64 (lf_F cx fp + LO_B1A0) /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\
  getr (ms_regs ms3) 10 = w64 (r_rc (o2_RR t kbs)) /\
  md_reqs mbs = r_reqs (o2_RR t kbs) /\ md_kstate mbs kbs = r_state (o2_RR t kbs) /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B160) (r_kind (o2_RR t kbs)) /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B1A0) (r_alias (o2_RR t kbs)) /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B160) KIND_CAP /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B1A0) ALIAS_MAX.

(* +0x1178: the model's answer is in s7 but for the name it remembers next *)
Definition o2_m_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_m ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\
  getr (ms_regs ms3) 23 = w64 (m_rc (o2_MM (Some t) kbs gbs)) /\
  md_reqs mbs = m_reqs (o2_MM (Some t) kbs gbs) /\
  m_marks (o2_MM (Some t) kbs gbs) = remember (mk_names gbs) t.

(* +0xc0c: the model's answer is in s7 and the model holds its marks and requests *)
Definition o2_u_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_u ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 23 = w64 (m_rc (o2_MM (Some t) kbs gbs)) /\
  md_reqs mbs = m_reqs (o2_MM (Some t) kbs gbs) /\ md_marks mbs = m_marks (o2_MM (Some t) kbs gbs).

(* +0xc9c: mark_quietly(mk, name) is next *)
Definition o2_q_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (nm : option (list byte)) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_q ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s nm /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 23 = w64 (m_rc (o2_MM nm kbs gbs)) /\
  md_reqs mbs = m_reqs (o2_MM nm kbs gbs) /\ md_marks mbs = m_marks (o2_MM nm kbs gbs).

End b.
End a.
