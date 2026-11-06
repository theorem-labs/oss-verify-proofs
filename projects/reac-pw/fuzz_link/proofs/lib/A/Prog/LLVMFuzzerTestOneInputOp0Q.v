(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 762 of its 827 lines of code are new or changed and 1267 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: the checks after the library's read,
   +0xed8 .. +0xf1c: `mv s2, a0; jal check_socket`; the name: `beqz s6` (NULL), its shadow-checked first byte
   (`bnez` to the slow check at +0x1364), `beqz` (empty), `jal index_of`, `bnez a0`; the refused block +0xf0c:
   `check_refused([s1 + 0x70], g_nl.opened)`. From the cut r_a_inv to the cut r_c LR_c.
   The stretch's states are r_cm (Op0Cut.v); r_leaf calls a leaf callee that writes nothing (Chk.v chk_leaf0) and
   restates the cut at its return; the calls and branches follow op_write's (Op1E.v w_as, w_lx, w_xj, w_jr),
   whose code is the same.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import check_socket_c index_of_c check_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputMb
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputNm LLVMFuzzerTestOneInputArmH LLVMFuzzerTestOneInputOp1E
  LLVMFuzzerTestOneInputChk LLVMFuzzerTestOneInputOp0Cut LLVMFuzzerTestOneInputOp0T LLVMFuzzerTestOneInputOp0A
  LLVMFuzzerTestOneInputOp3K LLVMFuzzerTestOneInputOp1C LLVMFuzzerTestOneInputOp1F.
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

#[local] Abbreviation BASEF cx :=
  (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
(* explicit at fx: a lemma that binds another FP state fy must not let instance resolution pick it *)
Local Notation FROM := (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Notation RCM := (r_cm SK B MT MS la_nul LF_MO_SET LF_MO_OP).
#[local] Notation RC := (r_c SK B MT MS la_nul LF_MO_SET LF_MO_OP).

(* the registers the stretch keeps *)
Lemma r_regs6_keep : forall cx fp i s kc ac t1 t2 want rc0 ms3 ms2,
  d4_keepL W_R3 (ms_regs ms3) (ms_regs ms2) ->
  lf_core cx ms3 -> r_regs6 cx fp i s kc ac t1 t2 want rc0 ms3 ->
  lf_core cx ms2 /\ r_regs6 cx fp i s kc ac t1 t2 want rc0 ms2.
Proof.
  intros cx fp i s kc ac t1 t2 want rc0 ms3 ms2 K Hc Hr.
  destruct Hc as (C2 & C8 & C9 & C3 & C4).
  destruct Hr as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  kreg K 2 (2%bv : bv 5) K2. kreg K 3 (3%bv : bv 5) K3. kreg K 4 (4%bv : bv 5) K4. kreg K 8 (8%bv : bv 5) K8.
  kreg K 9 (9%bv : bv 5) K9. kreg K 18 (18%bv : bv 5) K18. kreg K 19 (19%bv : bv 5) K19.
  kreg K 20 (20%bv : bv 5) K20. kreg K 21 (21%bv : bv 5) K21. kreg K 22 (22%bv : bv 5) K22.
  kreg K 23 (23%bv : bv 5) K23. kreg K 24 (24%bv : bv 5) K24. kreg K 25 (25%bv : bv 5) K25.
  kreg K 26 (26%bv : bv 5) K26. kreg K 27 (27%bv : bv 5) K27.
  split; [unfold lf_core; rewrite K2, K8, K9, K3, K4 | unfold r_regs6;
    rewrite K18, K19, K20, K21, K22, K23, K24, K25, K26, K27]; repeat split; assumption.
Qed.

(* the arm's buffers across a run that writes nothing *)
Lemma r_ext_run : forall cx fp md mk T3 ly3 S3 (W3 : world SEGS) ms3 ms4 kbs nm kc ac t1 t2 nb1 nb2,
  kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  r_ext B cx fp md mk T3 ly3 S3 W3 ms3 kbs nm kc ac t1 t2 nb1 nb2 ->
  r_ext B cx fp md mk T3 ly3 S3 W3 ms4 kbs nm kc ac t1 t2 nb1 nb2.
Proof.
  intros cx fp md mk T3 ly3 S3 W3 ms3 ms4 kbs nm kc ac t1 t2 nb1 nb2 KA GA (Hb & H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (fun a n => wcarry_of_grows SEGS _ _ a n GA) as WC.
  assert (CS : forall p v, acstr_at SEGS (rdW W3 (ms_mem ms3)) p v -> acstr_at SEGS (rdW W3 (ms_mem ms4)) p v)
    by (intros p v H; exact (acstr_keep SEGS _ _ _ _ _ KA (fun j _ H' => H') H)).
  assert (BF : forall p n, abuf SEGS (rdW W3 (ms_mem ms3)) p n -> abuf SEGS (rdW W3 (ms_mem ms4)) p n)
    by (intros p n H; exact (abuf_keep SEGS _ _ _ _ _ KA (WC p n) (fun j _ H' => H') H)).
  assert (AU : forall p bs, au8arr SEGS (rdW W3 (ms_mem ms3)) p bs -> au8arr SEGS (rdW W3 (ms_mem ms4)) p bs)
    by (intros p bs H; exact (au8arr_keep SEGS _ _ _ _ _ KA (WC p _) (fun j _ H' => H') H)).
  split; [exact Hb|].
  split; [intros Hk; destruct (H1 Hk) as (A1 & A2 & A3); exact (conj (CS _ _ A1) (conj (BF _ _ A2) (AU _ _ A3)))|].
  split; [intros Hk; destruct (H2 Hk) as (A1 & A2 & A3); exact (conj (CS _ _ A1) (conj (BF _ _ A2) (AU _ _ A3)))|].
  split; [destruct H3 as (A1 & A2); exact (conj (CS _ _ A1) (fun Hk => BF _ _ (A2 Hk)))|].
  split; [destruct H4 as (A1 & A2); exact (conj (CS _ _ A1) (fun Hk => BF _ _ (A2 Hk)))|].
  split; [exact (lf_slot_keep (fun _ => False) cx W3 ms3 W3 ms4 LS_NIF _ KA (fun j _ H => H) H5) | exact H6].
Qed.

(* the arm's buffers across a callee that writes nothing *)
Lemma r_ext_callee : forall cx fp md mk T3 K (E : Z -> Prop) ly3 S3 ly2 S2 (W3 : world SEGS) ms3 md3 k
    (W2 : world SEGS) ms2 md2 k' kbs nm kc ac t1 t2 nb1 nb2,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k -> JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k' ->
  frames S3 = [(LF_CID, fp)] -> frames S2 = frames S3 ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E -> (forall a, ~ E a) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) -> 0 <= kc < 40 -> 0 <= ac < 40 ->
  r_ext B cx fp md mk T3 ly3 S3 W3 ms3 kbs nm kc ac t1 t2 nb1 nb2 ->
  r_ext B cx fp md mk T3 ly2 S2 W2 ms2 kbs nm kc ac t1 t2 nb1 nb2.
Proof.
  intros cx fp md mk T3 K E ly3 S3 ly2 S2 W3 ms3 md3 k W2 ms2 md2 k' kbs nm kc ac t1 t2 nb1 nb2
    HB HJ3 HJ2 Hfr Hfr2 LC NE HP Hkc Hac (Hb & X1 & X2 & X3 & X4 & X5 & X6).
  pose proof (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
  assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in _ (Permutation_sym HP) Hc)).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k HB HJ3 Hfr) as (HFa & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly2 S2 W2 (ms_mem ms2) md2 k' HB HJ2 ltac:(rewrite Hfr2; exact Hfr)) as (_ & _ & _ & _ & _ & Fp2 & _).
  pose proof Hb as (Hnb1 & Hnb2 & Hbin & Hbap).
  assert (RQ : forall c, 0 <= c -> req_size (c + 1) = c + 1)
    by (intros c Hc; unfold req_size; destruct (c + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]).
  (* a buffer of a text block *)
  assert (TBL : forall t c nb, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> 1 <= c -> In (t, c + 1) (ablocks B ly3 S3)).
  { intros t c nb Hnb Hinc Hc1. destruct Hnb as [(E0 & _) | (_ & _ & ->)]; [lia|].
    exact (proj1 (Hbin (t, c + 1) (Hinc _ (or_introl eq_refl)))). }
  assert (BLX : forall t c, In (t, c + 1) (ablocks B ly3 S3) -> 0 <= c ->
      forall j, 0 <= j <= c -> ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E (t + j))
    by (intros t c Hin Hc j Hj; apply (lfx_blk B ly3 S3 ly2 S2 _ _ E t (c + 1) (t + j) Hin ltac:(lia) (NE _))).
  assert (BLW : forall t c, In (t, c + 1) (ablocks B ly3 S3) -> 0 <= c ->
      wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) t c).
  { intros t c Hin Hc ii Hii _. apply (apresent_writable SEGS).
    destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 t (c + 1) HAR2 (Psub _ Hin)) as (_ & _ & _ & _ & Hp & _).
    apply (proj1 (Hp (t + ii) ltac:(rewrite RQ by lia; lia))). }
  assert (FX : forall x, lf_F cx fp <= x < lf_F cx fp + 1024 ->
      ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E x).
  { intros x Hx. apply (lfx_frm B ly3 S3 ly2 S2 _ _ E LF_CID fp x ltac:(rewrite Hfr; left; reflexivity));
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFa; change (fs_frame_bytes LF_CID) with 1024; lia|].
    exact (NE x). }
  assert (FW : forall x n, lf_F cx fp <= x -> x + n <= lf_F cx fp + 1024 ->
      wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) x n).
  { intros x n Hx1 Hx2 ii Hii _. apply (apresent_writable SEGS). exact (proj1 (Fp2 (x + ii) ltac:(lia))). }
  split.
  { split; [exact Hnb1|]. split; [exact Hnb2|]. split; [|exact Hbap].
    intros b Hbb. destruct (Hbin b Hbb) as (A1 & A2 & A3). exact (conj (Psub _ A1) (conj A2 A3)). }
  split.
  { intros H1k. destruct (X1 H1k) as (A1 & A2 & A3).
    pose proof (TBL t1 kc nb1 Hnb1 ltac:(intros x Hx; apply in_or_app; left; exact Hx) H1k) as Hin.
    pose proof (r_kind_len lf_tab nm kc ac [] (nk_kstate kbs) H1k) as Lk.
    split; [|split].
    - apply (acstr_keep SEGS _ _ _ _ _ KG); [|exact A1]. intros j Hj. apply (BLX t1 kc Hin ltac:(lia)).
      unfold r_LR, read_lib in *. lia.
    - apply (abuf_keep SEGS _ _ _ _ _ KG (BLW t1 kc Hin ltac:(lia))); [|exact A2].
      intros j Hj. apply (BLX t1 kc Hin ltac:(lia)). lia.
    - apply (au8arr_keep SEGS _ _ _ _ _ KG); [ | | exact A3].
      + intros j Hj. cbn [length] in Hj. replace j with 0 by lia. rewrite Z.add_0_r.
        intros _. apply (apresent_writable SEGS).
        destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 t1 (kc + 1) HAR2 (Psub _ Hin)) as (_ & _ & _ & _ & Hp & _).
        apply (proj1 (Hp (t1 + kc) ltac:(rewrite RQ by lia; lia))).
      + intros j Hj. cbn [length] in Hj. replace j with 0 by lia. rewrite Z.add_0_r.
        apply (BLX t1 kc Hin ltac:(lia)). lia. }
  split.
  { intros H1k. destruct (X2 H1k) as (A1 & A2 & A3).
    pose proof (TBL t2 ac nb2 Hnb2 ltac:(intros x Hx; apply in_or_app; right; exact Hx) H1k) as Hin.
    pose proof (r_alias_len lf_tab nm kc ac [] (nk_kstate kbs) H1k) as Lk.
    split; [|split].
    - apply (acstr_keep SEGS _ _ _ _ _ KG); [|exact A1]. intros j Hj. apply (BLX t2 ac Hin ltac:(lia)).
      unfold r_LR, read_lib in *. lia.
    - apply (abuf_keep SEGS _ _ _ _ _ KG (BLW t2 ac Hin ltac:(lia))); [|exact A2].
      intros j Hj. apply (BLX t2 ac Hin ltac:(lia)). lia.
    - apply (au8arr_keep SEGS _ _ _ _ _ KG); [ | | exact A3].
      + intros j Hj. cbn [length] in Hj. replace j with 0 by lia. rewrite Z.add_0_r.
        intros _. apply (apresent_writable SEGS).
        destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 t2 (ac + 1) HAR2 (Psub _ Hin)) as (_ & _ & _ & _ & Hp & _).
        apply (proj1 (Hp (t2 + ac) ltac:(rewrite RQ by lia; lia))).
      + intros j Hj. cbn [length] in Hj. replace j with 0 by lia. rewrite Z.add_0_r.
        apply (BLX t2 ac Hin ltac:(lia)). lia. }
  split.
  { destruct X3 as (A1 & A2).
    pose proof (r_kind_fit lf_tab nm kc ac [] (nk_kstate kbs) Hkc) as Lk.
    split.
    - apply (acstr_keep SEGS _ _ _ _ _ KG); [|exact A1]. intros j Hj. apply FX.
      unfold r_RR, read_model in *; cbn [r_kind] in *. unfold LO_B2E0. lia.
    - intros H1k.
      apply (abuf_keep SEGS _ _ _ _ _ KG (FW (lf_F cx fp + LO_B2E0) kc ltac:(unfold LO_B2E0; lia) ltac:(unfold LO_B2E0; lia))); [|exact (A2 H1k)].
      intros j Hj. apply FX. unfold LO_B2E0. lia. }
  split.
  { destruct X4 as (A1 & A2).
    pose proof (r_alias_fit lf_tab nm kc ac [] (nk_kstate kbs) Hac) as Lk.
    split.
    - apply (acstr_keep SEGS _ _ _ _ _ KG); [|exact A1]. intros j Hj. apply FX.
      unfold r_RR, read_model in *; cbn [r_alias] in *. unfold LO_B330. lia.
    - intros H1k.
      apply (abuf_keep SEGS _ _ _ _ _ KG (FW (lf_F cx fp + LO_B330) ac ltac:(unfold LO_B330; lia) ltac:(unfold LO_B330; lia))); [|exact (A2 H1k)].
      intros j Hj. apply FX. unfold LO_B330. lia. }
  split; [|exact X6].
  pose proof (proj1 (proj2 LC)) as HKs.
  unfold lf_slot, lf_at in *.
  apply (d4_slot_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E _ _ LC);
    [unfold LS_NIF; lia | | intros j _ HEa; exact (NE _ HEa) | exact X5].
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ3) as (Hs1 & _). unfold LS_NIF. lia.
Qed.

(* a state of the stretch moved along a run that writes nothing and keeps the registers *)
Lemma r_cm_run : forall (Q Q' : machine_state -> option (list byte) -> Prop) i cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4,
  RCM Q i cx fp k2 ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  d4_keepL W_R3 (ms_regs ms3) (ms_regs ms4) ->
  kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall nm, Q ms3 nm -> Q' ms4 nm) ->
  RCM Q' i cx fp k2 ly3 S3 W3 ms4 md4.
Proof.
  intros Q Q' i cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 HC HJ4 KR KA GA Fd Fs HQ.
  destruct HC as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext & Hq).
  destruct (r_regs6_keep cx fp i s kc ac t1 t2 _ _ ms3 ms4 KR Hcore Hreg) as (Hcore4 & Hreg4).
  exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
  split; [exact Hreg4|]. split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
  split; [exact Hcore4|].
  split; [exact (chk_cut_run SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 ms4 md3 md4
            SH_R_len Hcut HJ4 KA GA Fd Fs)|].
  split; [exact (lf_cur_keep (fun _ => False) cx W3 ms3 W3 ms4 P N KA (fun a _ H => H) Hcur)|].
  split; [exact Hop|]. split; [exact Hob|]. split; [exact Href|]. split; [exact Hsent|]. split; [exact Hns|].
  split; [exact Hks|]. split; [exact Hrq|]. split; [exact Hmk|].
  split; [exact (r_ext_run cx fp md mk T3 ly3 S3 W3 ms3 ms4 kbs nm kc ac t1 t2 nb1 nb2 KA GA Hext) | exact (HQ nm Hq)].
Qed.

(* the call of a leaf callee that writes nothing, from a state of the stretch at the call to the state of the stretch
   at its return *)
Lemma r_leaf : forall (fy : YK11.FPState) pc K Pre Rd Wr Post,
  @aleaf_rd fy rc SK SEGS PCAP_RLO PCAP_RHI B pc K 0 [] Pre Rd Wr Post ->
  forall (Q Q' : machine_state -> option (list byte) -> Prop) ret i cx fp k2 ly3 S3 W3 (ms3 : machine_state) md3
    POST,
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  RCM Q i cx fp k2 ly3 S3 W3 ms3 md3 ->
  0 <= K <= LLVMF_STK - 448 ->
  getr (ms_regs ms3) 1 = Z_to_bv 64 (link_text + ret) ->
  AF_LLVMFuzzerTestOneInput <= ret < AF_LLVMFuzzerTestOneInput + 0x1460 ->
  YK0s.ret_ok (getr (ms_regs ms3) 1) ->
  (forall a, ~ inFP (Wr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a) ->
  (forall a, Rd (ms_regs ms3) (rdW W3 (ms_mem ms3)) a -> akb SEGS B ly3 S3 (lf_sp1 cx - K) (lf_sp1 cx) a) ->
  Pre (ms_regs ms3) (rdW W3 (ms_mem ms3)) ->
  (forall nm ms2 (W2 : world SEGS), Q ms3 nm ->
     Post (ms_regs ms3) (rdW W3 (ms_mem ms3)) (ms_regs ms2) (rdW W2 (ms_mem ms2)) -> Q' ms2 nm) ->
  pa_val A_TEXT = link_text ->
  FROM POST (RC ret Q' i) ->
  SRr SEGS W3 (mkCfg (@mkst fy (ms_regs ms3) (Z_to_bv 64 pc) (ms_mem ms3) (seg_rom SEGS)) md3) (POST cx).
Proof.
  intros fy pc K Pre Rd Wr Post HL Q Q' ret i cx fp k2 ly3 S3 W3 ms3 md3 POST HB Hfx HJ Hfr HC HK R1 Hret Hrok HW HR
    Hpre HQ HBASE HF.
  destruct HC as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext & Hq).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hcut as (_ & _ & _ & _ & _ & _ & Hjbk & _ & _).
  pose proof Hjbk as (Hkev & _).
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (Rsp : spZ (ms_regs ms3) = lf_sp1 cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  change (mkCfg (@mkst fy (ms_regs ms3) (Z_to_bv 64 pc) (ms_mem ms3) (seg_rom SEGS)) md3)
    with (@cfg_at fy SEGS pc (ms_regs ms3) (ms_mem ms3) md3).
  apply (chk_leaf0 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    fy pc K Pre Rd Wr Post HL cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 md3 P N (POST cx)
    HB SH_R_len Hcut Hcur HK ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia) Hrok
    ltac:(unfold raZ; rewrite R1; rewrite unsigned_lit_small by (unfold link_text, AF_LLVMFuzzerTestOneInput in *; lia);
          unfold link_text, AF_LLVMFuzzerTestOneInput in *; lia)
    ltac:(rewrite R3; exact Gp) ltac:(rewrite R4; exact Tp) Rsp HW HR Hpre).
  intros W2 ly2 S2 regs2 mem2 md2 HC2 HRO2 Hcur2 HP2 HPERM2 HCALL2 Hpost.
  set (ms2 := @mkst fy regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) in *.
  pose proof HC2 as (HJ2 & Hfr2 & _).
  pose proof (d4_keep_pres W_R3 _ _ W_R3_saved HP2) as KT.
  destruct (r_regs6_keep cx fp i s kc ac t1 t2 _ _ ms3 ms2 KT Hcore Hreg) as (Hcore2 & Hreg2).
  apply (HF cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 Hfr2).
  split.
  { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite R1, <- HBASE. repeat split; reflexivity. }
  exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
  split; [exact Hreg2|]. split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
  split; [exact Hcore2|]. split; [exact HC2|]. split; [exact Hcur2|].
  split; [exact Hop|]. split; [exact Hob|]. split; [exact Href|]. split; [exact Hsent|]. split; [exact Hns|].
  split; [exact Hks|]. split; [exact Hrq|]. split; [exact Hmk|].
  split; [|exact (HQ nm ms2 W2 Hq Hpost)].
  exact (r_ext_callee cx fp md mk T3 K _ ly3 S3 ly2 S2 W3 ms3 md3 k2 W2 ms2 md2 k2 kbs nm kc ac t1 t2 nb1 nb2
    HB HJ HJ2 Hfr ltac:(rewrite Hfr2, Hfr; reflexivity) HCALL2 (fun a H => HW a H) HPERM2 Hkc Hac Hext).
Qed.

(* the refused block's entry state: the slot window [s1 + 0x70, s1 + 0xf8) (the count of sockets opened before the
   read as atom 34, g_nl + 0x40000 as atom 32) and g_nl.opened as atom 33 *)
Definition f_slot_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x70 0xf8 0x70 0x70
    [YP09.mkChunk 0x70 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0))].
Definition f_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] [].
Definition f_ss (pc : Z) : sstate := mkSS pc sr_atoms [f_slot_rg; w_op_rg] None f_facts.

(* check_socket, check_refused and index_of, as proved (check_socket_c.v, check_refused_c.v,
   index_of_c.v), the hypotheses of the top file *)
Hypothesis CSOCK : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREF : forall fy : YK11.FPState, @check_refused_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis INDEX_OF : forall fy : YK11.FPState, @index_of_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

(* +0xed8 .. +0xedc: `mv s2, a0; jal check_socket` (0x86734), to its return +0xee0 *)
Lemma r_as : forall POST i,
  FROM POST (RC LR_q (fun _ _ => True) i) -> FROM POST (r_a_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HA.
  destruct HA as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hsh & Hreg &
    R10 & Hnm & Hkc & Hac & Hi & Hcore & HC & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hbufs & Hk1 &
    Hk2 & Hw1 & Hw2 & NIF & RRC).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  rewrite (lf_shape_eta fy LR_a ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_a) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_a)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS EL
    ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk)) as KR.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  assert (GA : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))) by exact HGA.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (18%bv : bv 5) Q18.
  ew_reg EL 10%nat (10%bv : bv 5) Q18. rewrite R10 in Q18. rewrite HBASE in Q1.
  pose proof (chk_cut_run SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 msA md3 mdA
    SH_R_len HC HJ KA GA FdA FsA) as HCA.
  pose proof HCA as (HJA & _ & _ & _ & _ & _ & _ & _ & HdatA).
  pose proof HdatA as (Dk & Dwf & Dtab & Dop & Dmis & Doc & _).
  assert (HM : RCM (fun _ _ => True) i cx fp k2 ly3 S3 W3 msA mdA).
  { kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4. kreg KR 8 (8%bv : bv 5) K8.
    kreg KR 9 (9%bv : bv 5) K9. kreg KR 19 (19%bv : bv 5) K19. kreg KR 20 (20%bv : bv 5) K20.
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 23 (23%bv : bv 5) K23.
    kreg KR 24 (24%bv : bv 5) K24. kreg KR 25 (25%bv : bv 5) K25. kreg KR 26 (26%bv : bv 5) K26.
    kreg KR 27 (27%bv : bv 5) K27.
    exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
    split.
    { unfold r_regs6. rewrite Q18, K19, K20, K21, K22, K23, K24, K25, K26, K27. repeat split; assumption. }
    split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
    split; [unfold lf_core; rewrite K2, K8, K9, K3, K4; repeat split; assumption|].
    split; [exact HCA|].
    split; [exact (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur)|].
    split; [exact Hop|]. split; [exact Hob|]. split; [exact Href|]. split; [exact Hsent|]. split; [exact Hns|].
    split; [exact Hks|]. split; [exact Hrq|]. split; [exact Hmk|].
    split; [|exact I].
    exact (r_ext_run cx fp md mk T3 ly3 S3 W3 ms3 msA kbs nm kc ac t1 t2 nb1 nb2 KA GA
      (conj Hbufs (conj Hk1 (conj Hk2 (conj Hw1 (conj Hw2 (conj NIF RRC))))))). }
  replace (pa_sigma LS_check_socket) with CHECK_SOCKET_A by (rewrite (lv_sigma LV); reflexivity).
  apply (r_leaf fy CHECK_SOCKET_A CHECK_SOCKET_AK (check_socket_apre SEGS) (fun _ _ _ => False) check_socket_awr
    check_socket_apost (proj2 (aleaf_rd_none (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B CHECK_SOCKET_A CHECK_SOCKET_AK 0 []
      (check_socket_apre SEGS) check_socket_awr check_socket_apost) (CSOCK fy))
    (fun _ _ => True) (fun _ _ => True) LR_q i cx fp k2 ly3 S3 W3 msA mdA POST HB Hfx HJA Hfr HM).
  - unfold CHECK_SOCKET_AK, CHECK_SOCKET_AFRAME, LLVMF_STK. lia.
  - rewrite Q1. reflexivity.
  - unfold LR_q. lia.
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a (r & [] & _).
  - intros a [].
  - exists kbs'. exact (conj Dk (conj Dop (conj Doc Dmis))).
  - intros _ _ _ _ _. exact I.
  - exact HBASE.
  - exact HL.
Qed.

(* +0xf0c .. +0xf18: `ld a0, 0xf0(s1); lw a1, 0x218(a0); ld a0, 0x70(s1); jal check_refused` (0x8688c), to +0xf1c:
   the count of sockets opened before the read (the slot s1 + 0x70) and after it (g_nl.opened) agree *)
Lemma r_jr : forall POST i,
  FROM POST (RC LR_c (fun _ _ => True) i) -> FROM POST (RC LR_f (fun _ nm => r_refused nm) i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  pose proof HM as HM0.
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext & Hrf).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  assert (Hs32 : lf_sp1 cx mod 32 = 0) by (unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
    apply Z_mod_mult).
  pose proof Hcut as (_ & _ & _ & _ & _ & Hsl & _ & _ & Hdat).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & HSG & _).
  pose proof Hdat as (Dk & Dwf & _).
  pose proof Dk as ((Hbk & _) & HLk).
  pose proof Hext as (_ & _ & _ & _ & _ & NIF & _).
  pose proof Dwf as (_ & _ & _ & _ & _ & ROP & _).
  pose proof (Href Hrf) as Heq.
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite (lf_shape_eta fy LR_f ms3 Hsh).
  set (ex := [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (nk_opened kbs'); Z_to_bv 64 (nk_opened kbs)]).
  set (E := Eimg (Ereg (ms_regs ms3) ex)).
  assert (E9 : ew E 9 = getr (ms_regs ms3) 9)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 (LA_G_NL + 0x40000))
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ ex 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_opened kbs'))
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ ex 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (nk_opened kbs))
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ ex 2)).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E (f_ss LR_f)
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_f)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold f_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok.
      + unfold f_slot_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, HU9. split; [unfold LLVMF_STK in *; lia|]. split; [unfold LLVMF_STK in *; lia|].
        split; [intros oo Hoo; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x70 8 (SOff 34 0) (nk_opened kbs));
            [cbn [sv_denot]; rewrite E34, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
          exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ NIF).
        * apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0xf0 8 (SOff 32 0) (LA_G_NL + 0x40000));
            [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold LA_G_NL; rewrite Z_to_bv_bv_unsigned; reflexivity
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold LA_G_NL; lia | change (Z.of_N 8) with 8; lia |].
          exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSG).
      + unfold w_op_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite (u_base E 32 _ E32) by (unfold LA_G_NL; lia).
        split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros oo Hoo; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ _ 0x218 4 (SOff 33 0) (nk_opened kbs'));
          [rewrite (lf_sv_off E 33 _ 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia |].
        replace (LA_G_NL + 0x40000 + 0x218) with (LA_G_NL + NK_OPENED) by (unfold NK_OPENED; lia).
        exact (val_mem_of_abytes SEGS _ LA_G_NL kbs' NK_OPENED 4 Hbk ltac:(unfold NK_OPENED; lia)
          ltac:(unfold NK_OPENED, NK_SIZE in *; lia)).
    - apply pairwise_disjoint_of_extents.
      unfold f_slot_rg, w_op_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite E9, HU9, E32. rewrite unsigned_lit_small by (unfold LA_G_NL; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    - split; [|split; [exact I | exact I]].
      cbn [f_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, HU9, E32, E33, E34. rewrite !unsigned_lit_small by (unfold LA_G_NL; lia).
      change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_f)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) ex) n)
    by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
  clearbody E.
  paj_run_tok RUN HS HJ SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [f_ss f_slot_rg w_op_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
     apply awr_ok_x_cons; [cbn [f_ss f_slot_rg w_op_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
     apply awr_ok_x_nil |].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R3 HS EL W_R3_low ltac:(d4chk)) as KR.
  assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
      cbn [f_ss f_slot_rg w_op_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (r_cm_run (fun _ nm => r_refused nm) (fun _ _ => True) i cx fp k2 ly3 S3 W3 ms3 md3 msA mdA HM0 HJ KR KA
    HGA FdA FsA (fun _ _ => I)) as HMA.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  try rewrite E34 in Q10. try rewrite E33 in Q11. rewrite HBASE in Q1.
  replace (pa_sigma LS_check_refused) with CHECK_REFUSED_A by (rewrite (lv_sigma LV); reflexivity).
  apply (r_leaf fy CHECK_REFUSED_A CHECK_REFUSED_AK check_refused_apre (fun _ _ _ => False) check_refused_awr
    check_refused_apost (proj2 (aleaf_rd_none (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B CHECK_REFUSED_A CHECK_REFUSED_AK
      0 [] check_refused_apre check_refused_awr check_refused_apost) (CREF fy))
    (fun _ _ => True) (fun _ _ => True) LR_c i cx fp k2 ly3 S3 W3 msA mdA POST HB Hfx HJ Hfr HMA).
  - unfold CHECK_REFUSED_AK, CHECK_REFUSED_AFRAME, LLVMF_STK. lia.
  - rewrite Q1. reflexivity.
  - unfold LR_c. lia.
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a (r & [] & _).
  - intros a [].
  - unfold check_refused_apre. rewrite Q10, Q11, Heq. reflexivity.
  - intros _ _ _ _ _. exact I.
  - exact HBASE.
  - exact HL.
Qed.

Definition LR_x : Z := AF_LLVMFuzzerTestOneInput + 0xf08.      (* 0x836dc index_of has returned *)
Definition r_xQ (ms : machine_state) (nm : option (list byte)) : Prop :=
  exists x, nm = Some x /\ getr (ms_regs ms) 10 = w64 (index_of lf_tab x).

(* +0xf08 `bnez a0, +0xf1c`: the name is in the table (on) or not (to the refused block) *)
Lemma r_xj : forall POST i,
  FROM POST (RC LR_c (fun _ _ => True) i) -> FROM POST (RC LR_f (fun _ nm => r_refused nm) i) ->
  FROM POST (RC LR_x r_xQ i).
Proof.
  intros POST i HLC HLF cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  pose proof HM as HM0.
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (x & Hx & R10)).
  pose proof HB as (HPRE & Hfrm & HGX & _).
  rewrite (lf_shape_eta fy LR_x ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_x) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_x)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  assert (E10 : ew E 10 = w64 (index_of lf_tab x))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact R10).
  pose proof (chk_index_of_range x) as Rix.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* taken: index_of <> 0 *)
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_c; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    apply (HLC cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    exact (r_cm_run r_xQ (fun _ _ => True) i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB HM0 HJ
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
      (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs (fun _ _ => I)).
  - (* not taken: index_of = 0, to the refused block *)
    rewrite chk_bne_any, E10 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_f; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    apply (HLF cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    apply (r_cm_run r_xQ (fun _ nm => r_refused nm) i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB HM0 HJ
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
      (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs).
    intros nm' (x' & Hx' & R10'). right; right. intros y Hy. rewrite Hy in Hx'. injection Hx' as <-.
    rewrite R10 in R10'. apply (f_equal bv_unsigned) in R10'. unfold w64 in R10'.
    rewrite !unsigned_lit_small in R10' by (pose proof (chk_index_of_range y); lia). lia.
Qed.

(* a state of the stretch with its name pinned: the fact Q' of a callee's return may then use the name's facts *)
Lemma r_cm_pin : forall (Q : machine_state -> option (list byte) -> Prop) i cx fp k2 ly3 S3 W3 ms3 md3,
  RCM Q i cx fp k2 ly3 S3 W3 ms3 md3 ->
  exists nm s, getr (ms_regs ms3) 22 = w64 s /\ w_name s nm /\ Q ms3 nm /\
    RCM (fun ms n => n = nm /\ Q ms n) i cx fp k2 ly3 S3 W3 ms3 md3.
Proof.
  intros Q i cx fp k2 ly3 S3 W3 ms3 md3 HM.
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext & Hq).
  exists nm, s. split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hreg)))))|]. split; [exact Hnm|]. split; [exact Hq|].
  exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
  exact (conj Hreg (conj Hnm (conj Hkc (conj Hac (conj Hi (conj Hcore (conj Hcut (conj Hcur (conj Hop (conj Hob
    (conj Href (conj Hsent (conj Hns (conj Hks (conj Hrq (conj Hmk (conj Hext (conj eq_refl Hq)))))))))))))))))).
Qed.

Definition LR_n : Z := AF_LLVMFuzzerTestOneInput + 0xf00.      (* 0x836d4 mv a0, s6; jal index_of *)
Definition r_nQ (ms : machine_state) (nm : option (list byte)) : Prop := exists x, nm = Some x /\ x <> [].

(* +0xf00 .. +0xf04: `mv a0, s6; jal index_of` (0x86784), to its return +0xf08 *)
Lemma r_lx : forall POST i,
  FROM POST (RC LR_x r_xQ i) -> FROM POST (RC LR_n r_nQ i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  destruct (r_cm_pin r_nQ i cx fp k2 ly3 S3 W3 ms3 md3 HM) as (nm & s & R22 & Hnm & (x & Hx & Hx0) & HMp).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  rewrite (lf_shape_eta fy LR_n ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_n) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_n)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R3 HS EL W_R3_low ltac:(d4chk)) as KR.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (r_cm_run _ _ i cx fp k2 ly3 S3 W3 ms3 md3 msA mdA HMp HJ KR KA HGA FdA FsA (fun _ H => H)) as HMA.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  ew_reg EL 22%nat (22%bv : bv 5) Q10. rewrite R22 in Q10. rewrite HBASE in Q1.
  pose proof HMA as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s' & nm' & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    _ & _ & _ & _ & Hcore & Hcut & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hn' & _)).
  subst nm'.
  pose proof Hcore as (R2 & _ & _ & R3 & R4).
  pose proof Hcut as (HJA & _ & _ & _ & _ & _ & HjbkA & HblkA & HdatA).
  pose proof HjbkA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HdatA as (Dk & Dwf & Dtab & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msA) mdA k2 HB HJA) as (Hs1 & Hs16 & Hlo & H47').
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HK8 : 0 <= INDEX_OF_AK <= LLVMF_STK - 448) by (rewrite INDEX_OF_AK_val; unfold LLVMF_STK; lia).
  pose proof (w_name_range s nm Hnm) as Rs.
  assert (Ra0 : aarg (ms_regs msA) 0 = s) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; lia).
  rewrite Hx in Hnm.
  destruct (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs' mbs gbs s x HB HJA HRO HdatA Hnm) as (Ncs & _ & Ns0 & _).
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk T3 (ms_regs msA) INDEX_OF_AK HB HJA HblkA Rsp HK8)
    as (M1 & M2 & _).
  replace (pa_sigma LS_index_of) with INDEX_OF_A by (rewrite (lv_sigma LV); reflexivity).
  apply (r_leaf fy INDEX_OF_A INDEX_OF_AK (index_of_apre SEGS) (index_of_ard SEGS) index_of_awr (index_of_apost SEGS)
    (INDEX_OF fy) _ r_xQ LR_x i cx fp k2 ly3 S3 W3 msA mdA POST HB Hfx HJA Hfr HMA HK8).
  - rewrite Q1. reflexivity.
  - unfold LR_x. lia.
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a (r & [] & _).
  - intros a (u & Hu & Ha). rewrite Ra0 in Hu, Ha.
    pose proof (kp_acstr_unique _ _ _ _ _ Hu Ncs) as Eu. subst u.
    exact (lf_name_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs' mbs gbs s x ly3 S3 _ _ a HB HJA HRO HdatA Hnm Ha).
  - exists kbs', lf_tab, x. rewrite Ra0.
    split; [exact Dk|]. split; [exact Dtab|]. split; [exact M1|]. split; [exact M2|].
    split; [lia|]. split; [exact Ncs|].
    split; [exact (lf_name_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs' mbs gbs s x (ms_regs msA) INDEX_OF_AK HB HJA HRO HdatA Rsp HK8
      Hnm)|].
    intros i0 n2 ix p Hn Hp Rp.
    exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs' mbs gbs (ms_regs msA) INDEX_OF_AK HB HJA HRO HdatA Rsp HK8
      i0 n2 ix p Hn Hp Rp)).
  - intros n ms2 W2 (-> & _) Hpost. exists x. split; [exact Hx|].
    exact (Hpost kbs' lf_tab x Dk Dtab ltac:(rewrite Ra0; exact Ncs)).
  - exact HBASE.
  - exact HL.
Qed.

(* the name check's entry state: the slot s1 + 0xf8 (the shadow base, atom 32) and the name's first byte (atom 33) *)
Definition q_shb_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xf8 0x100 0xf8 0xf8 [YP09.mkChunk 0xf8 (CVal 8 (SOff 32 0))].
Definition q_nm_rg : YP09.region := YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition q_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 4096 (2 ^ 47 - 2) 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 255 0)] [] [].
Definition q_ss (pc : Z) : sstate := mkSS pc sr_atoms [q_shb_rg; q_nm_rg] None q_facts.

(* +0xee0 .. +0xefc: `beqz s6` (NULL, to the refused block); the instrumented check of the name's first byte
   (`srli a0, s6, 3; ld a1, 0xf8(s1); add; lb; bnez` to the slow check, decided by the runner from the shadow entry);
   `lbu a0, 0(s6); beqz a0` (empty, to the refused block); else on to +0xf00 *)
Lemma r_ns : forall POST i,
  FROM POST (RC LR_f (fun _ nm => r_refused nm) i) -> FROM POST (RC LR_n r_nQ i) ->
  FROM POST (RC LR_q (fun _ _ => True) i).
Proof.
  intros POST i HLF HLN cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  destruct (r_cm_pin _ i cx fp k2 ly3 S3 W3 ms3 md3 HM) as (nm & s & R22 & Hnm & _ & HMp).
  pose proof HB as (HPRE & Hfrm & HGX & HLN0 & HMS & _).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  pose proof (w_name_range s nm Hnm) as Rs.
  rewrite (lf_shape_eta fy LR_q ms3 Hsh).
  destruct nm as [x|].
  2:{ (* NULL: s = 0, to the refused block *)
    assert (Hs0 : s = 0).
    { destruct Hnm as [(Hs & _) | [(k & _ & _ & Hn) | (j & _ & _ & Hn)]]; [exact Hs | discriminate | discriminate]. }
    subst s.
    pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_q) as HS.
    assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_q)) (ms_mem ms3) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
    remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
    assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
      by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
    clear HEdef.
    assert (E22 : ew E 22 = w64 0)
      by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 22 22%bv eq_refl); exact R22).
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    - paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_f; [apply awr_ok_x_nil|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
      assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
      apply (HLF cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
      split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
      apply (r_cm_run _ (fun _ nm => r_refused nm) i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB HMp HJ
        (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
        (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs).
      intros n (-> & _). left. reflexivity.
    - exfalso. rewrite chk_beq_any, E22 in Hc. vm_compute in Hc. discriminate Hc. }
  (* a name: the runner decides `beqz s6` (atom 22 is at least 4096) and the shadow check *)
  pose proof HMp as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s' & nm' & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hnm' & Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext &
    (Hpin & _)).
  subst nm'.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (_ & _ & _ & _ & R22' & _).
  pose proof Hcut as (_ & _ & _ & _ & _ & Hsl & HjbkC & _ & HdatC).
  pose proof HjbkC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & HSB & _).
  destruct (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 md mk kbs' mbs gbs s' x HB HJ HRO HdatC Hnm')
    as (Ncs & Nl & Ns0 & Nam & Nra & Nhv & Ntail & Ntop & Nimg).
  pose proof Ncs as ((_ & _ & Nby) & Nnz).
  pose proof (Nby 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hb0. rewrite Z.add_0_r in Hb0.
  destruct (nth_error (x ++ [zb 0]) 0) as [c0|] eqn:Ec0; [|apply nth_error_None in Ec0; rewrite length_app in Ec0;
    cbn [length] in Ec0; lia].
  set (b0 := bv_unsigned c0).
  pose proof (bv_unsigned_in_range _ c0) as Rb0. change (bv_modulus 8) with 256 in Rb0. fold b0 in Rb0.
  assert (Hs4096 : 4096 <= s' /\ s' <= 2 ^ 47 - 2).
  { destruct Hnm' as [(_ & Hn) | [(k & Hk & -> & _) | (j & Hj & -> & _)]]; [discriminate | unfold LA_G_NAMES; lia|].
    rewrite w_odd_ptrs. do 6 (destruct j as [|j]; [cbn; lia|]). lia. }
  pose proof (pa_segs_low s' (proj1 (Nimg s' ltac:(lia)))) as Hslow.
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47).
  assert (Hs32 : lf_sp1 cx mod 32 = 0) by (unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
    apply Z_mod_mult).
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 b0])).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 b0]) n)
    by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
  assert (E9 : ew E 9 = getr (ms_regs ms3) 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
  assert (E22 : ew E 22 = Z_to_bv 64 s')
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 22 22%bv eq_refl), R22'; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E (q_ss LR_q)
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_q)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold q_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok.
      + unfold q_shb_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, HU9. split; [unfold LLVMF_STK in *; lia|]. split; [unfold LLVMF_STK in *; lia|].
        split; [intros oo Hoo; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0xf8 8 (SOff 32 0) SHADOW_OFF);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold SHADOW_OFF; rewrite Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | change (Z.of_N 8) with 8; lia |].
        exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSB).
      + unfold q_nm_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite (u_base E 22 s' E22) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ s' 0 1 (SOff 33 0) b0);
          [rewrite (lf_sv_off E 33 b0 0 E33) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (chk_val_mem1 _ _ _ _ Hb0).
    - apply pairwise_disjoint_of_extents.
      unfold q_shb_rg, q_nm_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite E9, HU9, E22. rewrite (unsigned_lit_small s') by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kLowMemEnd, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    - split; [|split; [exact I | exact I]].
      cbn [q_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, HU9, E22, E32, E33. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF, LLVMF_STK in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (RA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF s' 1)
    by (rewrite <- ard_aview; apply (md_ra_sub _ s' (Z.of_nat (length x) + 1)); [exact Nra | lia | lia]).
  assert (SHOK : sh_ok pa_segs (SOff 32 0) [mkSHE 22 0 1] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_q)) (ms_mem ms3) (seg_rom SEGS))))).
  { unfold sh_ok. constructor; [|constructor]. unfold shent_ok, app_apart.
    cbn [she_m she_lo she_hi ms_mem mkst].
    rewrite (U_atom E 22 s' E22) by lia. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia).
    split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
    intros a Ha. unfold YImgTop.IMG_TOP, SHADOW_OFF in *. lia. }
  paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1);
    [apply awr_ok_x_cons; [cbn [q_ss q_shb_rg q_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
     apply awr_ok_x_cons; [cbn [q_ss q_shb_rg q_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
     apply awr_ok_x_nil |].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
      cbn [q_shb_rg q_nm_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  - (* the name's first byte is 0: the empty name, to the refused block *)
    rewrite chk_beq_any in Hc. repeat rewrite ew_ewset_other in Hc by lia. rewrite E33 in Hc.
    rewrite unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc.
    assert (Hx0 : x = []).
    { destruct x as [|c x']; [reflexivity|]. exfalso. cbn [app nth_error] in Ec0. injection Ec0 as <-.
      apply Nnz. left. apply bv_eq. unfold b0 in Hc. rewrite Hc. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LR_f;
      [apply awr_ok_x_cons; [cbn [q_ss q_shb_rg q_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
       apply awr_ok_x_cons; [cbn [q_ss q_shb_rg q_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
       apply awr_ok_x_nil |].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    assert (KB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msB))).
    { intros a _. unfold mbyte. rewrite (HFrB (Z_to_bv 64 a)); [reflexivity|].
      intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
        cbn [q_shb_rg q_nm_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    w_mk_el EL EL2.
    apply (HLF cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    apply (r_cm_run _ (fun _ nm => r_refused nm) i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB HMp HJ
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) _ W_R3 HS EL2 W_R3_low ltac:(d4chk))
      (fun a H => eq_trans (KB a H) (KA a H)) (fun a H => HGB a (HGA a H)) Fd Fs).
    intros n (-> & _). right; left. rewrite Hx0. reflexivity.
  - (* a nonempty name: on to `mv a0, s6; jal index_of` *)
    rewrite chk_beq_any in Hc. repeat rewrite ew_ewset_other in Hc by lia. rewrite E33 in Hc.
    rewrite unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
    assert (Hx0 : x <> []).
    { intros ->. cbn [app nth_error] in Ec0. injection Ec0 as <-. apply Hc. unfold b0. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LR_n;
      [apply awr_ok_x_cons; [cbn [q_ss q_shb_rg q_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
       apply awr_ok_x_cons; [cbn [q_ss q_shb_rg q_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
       apply awr_ok_x_nil |].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    assert (KB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msB))).
    { intros a _. unfold mbyte. rewrite (HFrB (Z_to_bv 64 a)); [reflexivity|].
      intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
        cbn [q_shb_rg q_nm_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    w_mk_el EL EL2.
    apply (HLN cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    apply (r_cm_run _ r_nQ i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB HMp HJ
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) _ W_R3 HS EL2 W_R3_low ltac:(d4chk))
      (fun a H => eq_trans (KB a H) (KA a H)) (fun a H => HGB a (HGA a H)) Fd Fs).
    intros n (-> & _). exists x. split; [reflexivity | exact Hx0].
Qed.

(* the whole check stretch, +0xed8 .. +0xf1c *)
Lemma r_checks : forall POST i,
  FROM POST (RC LR_c (fun _ _ => True) i) -> FROM POST (r_a_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HC.
  pose proof (r_jr POST i HC) as HF.
  exact (r_as POST i (r_ns POST i HF (r_lx POST i (r_xj POST i HC HF)))).
Qed.

End a.
