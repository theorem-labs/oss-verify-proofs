(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 1006 of its 1085 lines of code are new or changed and 1253 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: the checks of the answer, +0xf1c .. +0xf7c
   (listing (internal path) (internal record, sha256 e84d6f0c6974)):
     +0xf1c  beqz s7; mv a0, s7; mv a1, s5; jal check_bounds (0x868ac)        r_bk   (kind, kc)
     +0xf2c  ld s6, 0xe8(s1); beqz s10; mv a0, s10; mv a1, s11; jal check_bounds;
     +0xf40  mv a4, s10; j; +0xf48 ld a4, 0x80(s1)                           r_bv, r_ba (alias, ac)
     +0xf4c  ld s11, 0xf8(s1); ld s5, 0x98(s1); ld a2, 0x88(s1); beqz s7; mv a2, s7; mv a0, s2; mv a1, s4;
             ld a3, 0x88(s1); ld a5, 0x80(s1); jal check_read (0x86930)       r_cr
     +0xf74  mv a0, s6; jal check_requests (0x869a8)                          r_cq
   (fuzz_link.c op_read: `if (kind) check_bounds(kind, kc); if (alias) check_bounds(alias, ac);
   check_read(rc, want, kind ? kind : wk, wk, alias ? alias : wa, wa); check_requests(&g_nl, m);`).
   From the cut r_c LR_c (Op0Q.v r_checks) to the cut r_v LR_e at check_requests' return. From +0xf2c on, s6 holds m,
   not the name: the states are r_vm, with the registers s5, s6, s11 and a4 in the stretch's fact Q.
   check_read's Pre is link_spec.v read_agree: the library's answer and the model's are one, the model's code its
   norm_rc. check_requests' Pre is Op3Lib.v u_requests_are of the two request lists being one list.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import index_of_c check_bounds_c check_read_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputMb
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputArmH LLVMFuzzerTestOneInputOp1E LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputChk LLVMFuzzerTestOneInputOp0Cut
  LLVMFuzzerTestOneInputOp0T LLVMFuzzerTestOneInputOp0Z LLVMFuzzerTestOneInputOp0A LLVMFuzzerTestOneInputOp0Q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* a text buffer the library filled: its cap bytes, a NUL among them, and the guard byte after them *)
Lemma r_atbuf : forall segs m t c s,
  abuf segs m t c -> acstr_at segs m t s -> Z.of_nat (length s) < c -> au8arr segs m (t + c) [zb GUARD_BYTE] ->
  exists bs, atbuf_at segs m t c bs /\ In (zb 0) bs.
Proof.
  intros segs m t c s (junk & Hl & (H0 & H1 & Hb) & Hw) ((C0 & C1 & Cb) & _) Hs ((G0 & G1 & Gb) & Gw).
  cbn [length] in G1, Gw.
  exists junk. split.
  - split; [|exact Hl]. split.
    + split; [exact H0|]. rewrite length_app. cbn [length]. split; [lia|].
      intros i Hi.
      destruct (Nat.lt_ge_cases i (length junk)) as [Hlt | Hge].
      * rewrite nth_error_app1 by exact Hlt. exact (Hb i Hlt).
      * assert (Ei : i = length junk) by lia. subst i.
        rewrite nth_error_app2 by lia. rewrite Nat.sub_diag.
        pose proof (Gb 0%nat ltac:(cbn; lia)) as G. rewrite Z.add_0_r in G. rewrite Hl. exact G.
    + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      destruct (Z_lt_le_dec i c) as [Hlt | Hge]; [apply Hw; lia|].
      replace (t + i) with (t + c + 0) by lia. apply Gw. lia.
  - pose proof (Cb (length s) ltac:(rewrite length_app; cbn [length]; lia)) as C.
    rewrite nth_error_app2 in C by lia. rewrite Nat.sub_diag in C. cbn in C.
    pose proof (Hb (length s) ltac:(lia)) as B. rewrite C in B.
    exact (nth_error_In _ _ (eq_sym B)).
Qed.

(* check_read's Pre on the codes: the library's code and the model's, its norm_rc *)
Lemma r_same_rc : forall rc, - 2 ^ 32 < rc < 2 ^ 32 ->
  (w64 (norm_rc rc) = w64 RC_FAILS -> w64 rc <> w64 0) /\ (w64 (norm_rc rc) <> w64 RC_FAILS -> w64 rc = w64 (norm_rc rc)).
Proof.
  intros rc R. unfold norm_rc. destruct (0 <? rc) eqn:E.
  - apply Z.ltb_lt in E. split; [|intros H; exfalso; apply H; reflexivity].
    intros _ H. apply (f_equal bv_unsigned) in H. unfold w64 in H. rewrite !Z_to_bv_unsigned in H.
    unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H. rewrite !Z.mod_small in H by lia. lia.
  - split; [|intros _; reflexivity]. intros H. exfalso. apply Z.ltb_ge in E.
    apply (f_equal bv_unsigned) in H. unfold w64, RC_FAILS in H. rewrite !Z_to_bv_unsigned in H.
    unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
    rewrite (Z.mod_small 1000000) in H by lia.
    destruct (Z.eq_dec rc 0) as [-> | Hn]; [cbn in H; lia|].
    assert (Em : rc mod 2 ^ 64 = rc + 2 ^ 64) by (symmetry; apply (Z.mod_unique rc (2 ^ 64) (-1)); lia).
    rewrite Em in H. lia.
Qed.

(* the decide lane's string facts (Dec.v astr_rt_ok) give the strcmp wrapper's (check_read_c.v astrcmp_arg) *)
Lemma r_arg_of_rt : forall segs regs K m p s,
  model_decide_c.astr_rt_ok segs regs K m p s -> astrcmp_arg segs regs K m p s.
Proof.
  intros segs regs K m p s (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [lia|].
  split; [unfold amem_range in *; destruct H3 as [H3 | [H3 H3']]; [left; lia | right; split; lia]|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H7 | exact H6].
Qed.

(* the shadow hull of a shorter string at the same start *)
Lemma r_hull_sub : forall (rd : Z -> option Z) a n n', shadow_hull_vis rd a n -> 1 <= n' -> n' <= n ->
  shadow_hull_vis rd a n'.
Proof.
  intros rd a n n' H H1 H2 s Hs. apply H. unfold shadow_addr in *. split; [lia|].
  pose proof (Z.div_le_mono (a + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_mono (SHADOW_OFF + (a + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* +0xf4c's slots: [s1 + 0x80] wa (atom 32), [s1 + 0x88] wk (atom 33), [s1 + 0x98] m + MD_N_MARK (atom 34),
   [s1 + 0xe8] m (atom 35), [s1 + 0xf8] the shadow base (atom 36) *)
Definition v_slot_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x80 0x100 0x80 0x80
    [YP09.mkChunk 0x80 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x88 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0x98 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xe8 (CVal 8 (SOff 35 0));
     YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))].
Definition v_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 64 - 1) 0); (35%nat, mkAF 0 (2 ^ 64 - 1) 0); (36%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition v_ss (pc : Z) : sstate := mkSS pc sr_atoms [v_slot_rg] None v_facts.

Definition LR_k : Z := AF_LLVMFuzzerTestOneInput + 0xf2c.      (* 0x83700 after the kind's check *)
Definition LR_b2 : Z := AF_LLVMFuzzerTestOneInput + 0xf40.     (* 0x83714 the alias's check_bounds has returned *)
Definition LR_g : Z := AF_LLVMFuzzerTestOneInput + 0xf4c.      (* 0x83720 the alias pointer chosen *)
Definition LR_r : Z := AF_LLVMFuzzerTestOneInput + 0xf74.      (* 0x83748 check_read has returned *)
Definition LR_e : Z := AF_LLVMFuzzerTestOneInput + 0xf7c.      (* 0x83750 check_requests has returned *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
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
(* check_bounds, check_read and check_requests, as proved (check_bounds_c.v, check_read_c.v,
   check_requests_c.v) *)
Hypothesis CBND : forall fy : YK11.FPState, @check_bounds_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREAD : forall fy : YK11.FPState, @check_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREQ : forall fy : YK11.FPState, @check_requests_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx :=
  (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Notation RCM := (r_cm SK B MT MS la_nul LF_MO_SET LF_MO_OP).
#[local] Notation RC := (r_c SK B MT MS la_nul LF_MO_SET LF_MO_OP).

(* a run over v_ss's slots writes nothing *)
Lemma v_kagree : forall E rs (m m' : word -> option byte), rs = [v_slot_rg] -> frame_of E rs m m' ->
  kagree SEGS (fun _ => False) m m'.
Proof.
  intros E rs m m' -> HFr a _. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [v_slot_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Lemma v_entry : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem pc v32 v33 v34 v35 v36,
  2 ^ 46 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> bv_unsigned (getr regs 9) mod 32 = 0 ->
  0 <= v32 < 2 ^ 64 -> 0 <= v33 < 2 ^ 64 -> 0 <= v34 < 2 ^ 64 -> 0 <= v35 < 2 ^ 64 -> 0 <= v36 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + 0x80) 8 v32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + 0x88) 8 v33 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + 0x98) 8 v34 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + 0xe8) 8 v35 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + 0xf8) 8 v36 ->
  st_ok_pi (fx := fy) SEGS VAL
    (Eimg (Ereg regs [Z_to_bv 64 v32; Z_to_bv 64 v33; Z_to_bv 64 v34; Z_to_bv 64 v35; Z_to_bv 64 v36])) (v_ss pc)
    (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fy W regs mem pc v32 v33 v34 v35 v36 H9 H32 Hv32 Hv33 Hv34 Hv35 Hv36 Hm32 Hm33 Hm34 Hm35 Hm36.
  set (E := Eimg (Ereg regs [Z_to_bv 64 v32; Z_to_bv 64 v33; Z_to_bv 64 v34; Z_to_bv 64 v35; Z_to_bv 64 v36])).
  assert (E9 : ew E 9 = getr regs 9)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 v32; Z_to_bv 64 v33; Z_to_bv 64 v34;
      Z_to_bv 64 v35; Z_to_bv 64 v36] (Z_to_bv 64 0))
    by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ j)).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. cbn [nth Nat.add] in E32, E33, E34, E35, E36.
  rewrite restrict_mkst_fx. unfold v_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]; unfold region_ok.
    unfold v_slot_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E9. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    + apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0x80 8 (SOff 32 0) v32);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia | exact Hm32].
    + apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0x88 8 (SOff 33 0) v33);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia | exact Hm33].
    + apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0x98 8 (SOff 34 0) v34);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia | exact Hm34].
    + apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0xe8 8 (SOff 35 0) v35);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia | exact Hm35].
    + apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0xf8 8 (SOff 36 0) v36);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia | exact Hm36].
  - apply pairwise_disjoint_of_extents.
    unfold v_slot_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. fold E. rewrite E9.
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [v_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E9, E32, E33, E34, E35, E36. rewrite !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ==========================================================================
   The stretch's states from +0xf2c on
   ========================================================================== *)

(* the registers every state of the stretch keeps: s2 the library's code, s3 the frame's shadow, s4 the model's
   code, s7 kind, s8 = -8, s9 = i, s10 alias *)
Definition r_vregs (cx : lcx) (fp i t1 t2 want rc0 : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 18 = w64 rc0 /\ getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 20 = w64 want /\ getr (ms_regs ms3) 23 = w64 t1 /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\ getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 t2.

(* a state of the stretch: the cut, the counts, the buffers, and a fact Q of the state at the frame (cx, fp), the
   model m, the caps kc, ac and the buffers kind, alias *)
Definition r_vm (Q : lcx -> Z -> Z -> Z -> Z -> Z -> Z -> machine_state -> Prop) (i : Z) (cx : lcx) (fp k2 : Z)
    (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N : Z) (kbs kbs' mbs gbs : list byte) (T3 : list (Z * Z)) (nm : option (list byte))
    (kc ac t1 t2 : Z) (nb1 nb2 : list (Z * Z)),
  r_vregs cx fp i t1 t2 (r_rc (r_RR nm kc ac kbs)) (r_rc (r_LR nm kc ac kbs)) ms3 /\
  0 <= kc < 40 /\ 0 <= ac < 40 /\ 0 <= i <= 47 /\ lf_core cx ms3 /\
  chk_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 SH_R ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs' <= 64 * i + 1 /\ nk_sent kbs' = md_reqs mbs /\
  r_ext B cx fp md mk T3 ly3 S3 W3 ms3 kbs nm kc ac t1 t2 nb1 nb2 /\
  Q cx fp md kc ac t1 t2 ms3.

Definition r_v (pc : Z) (Q : lcx -> Z -> Z -> Z -> Z -> Z -> Z -> machine_state -> Prop) (i : Z) (cx : lcx)
    (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) : Prop :=
  lf_shape fy pc ms3 /\ r_vm Q i cx fp k2 ly3 S3 W3 ms3 md3.

(* s5, s6, s11 from +0xf2c to +0xf4c, and from check_read's return on *)
Definition r_q3 (cx : lcx) (fp md kc ac t1 t2 : Z) (ms : machine_state) : Prop :=
  getr (ms_regs ms) 21 = w64 kc /\ getr (ms_regs ms) 22 = w64 md /\ getr (ms_regs ms) 27 = w64 ac.
Definition r_q3b (cx : lcx) (fp md kc ac t1 t2 : Z) (ms : machine_state) : Prop :=
  r_q3 cx fp md kc ac t1 t2 ms /\ t2 <> 0.
Definition r_q4 (cx : lcx) (fp md kc ac t1 t2 : Z) (ms : machine_state) : Prop :=
  r_q3 cx fp md kc ac t1 t2 ms /\
  getr (ms_regs ms) 14 = w64 (if t2 =? 0 then lf_F cx fp + LO_B330 else t2).
Definition r_q5 (cx : lcx) (fp md kc ac t1 t2 : Z) (ms : machine_state) : Prop :=
  getr (ms_regs ms) 21 = w64 (md + MD_N_MARK) /\ getr (ms_regs ms) 22 = w64 md /\
  getr (ms_regs ms) 27 = w64 SHADOW_OFF.

#[local] Notation RVM := r_vm.
#[local] Notation RV := r_v.

Lemma r_vregs_keep : forall cx fp i t1 t2 want rc0 ms3 ms2,
  d4_keepL W_R3 (ms_regs ms3) (ms_regs ms2) ->
  lf_core cx ms3 -> r_vregs cx fp i t1 t2 want rc0 ms3 ->
  lf_core cx ms2 /\ r_vregs cx fp i t1 t2 want rc0 ms2.
Proof.
  intros cx fp i t1 t2 want rc0 ms3 ms2 K Hc Hr.
  destruct Hc as (C2 & C8 & C9 & C3 & C4).
  destruct Hr as (R18 & R19 & R20 & R23 & R24 & R25 & R26).
  kreg K 2 (2%bv : bv 5) K2. kreg K 3 (3%bv : bv 5) K3. kreg K 4 (4%bv : bv 5) K4. kreg K 8 (8%bv : bv 5) K8.
  kreg K 9 (9%bv : bv 5) K9. kreg K 18 (18%bv : bv 5) K18. kreg K 19 (19%bv : bv 5) K19.
  kreg K 20 (20%bv : bv 5) K20. kreg K 23 (23%bv : bv 5) K23. kreg K 24 (24%bv : bv 5) K24.
  kreg K 25 (25%bv : bv 5) K25. kreg K 26 (26%bv : bv 5) K26.
  split; [unfold lf_core; rewrite K2, K8, K9, K3, K4 | unfold r_vregs; rewrite K18, K19, K20, K23, K24, K25, K26];
    repeat split; assumption.
Qed.

(* a state of the stretch from its parts, moved along a run that writes nothing *)
Lemma r_vm_step : forall (Q' : lcx -> Z -> Z -> Z -> Z -> Z -> Z -> machine_state -> Prop) i cx fp k2 ly3 S3 W3
    ms3 md3 ms4 md4 md mk P N kbs kbs' mbs gbs T3 nm kc ac t1 t2 nb1 nb2,
  r_vregs cx fp i t1 t2 (r_rc (r_RR nm kc ac kbs)) (r_rc (r_LR nm kc ac kbs)) ms3 ->
  0 <= kc < 40 -> 0 <= ac < 40 -> 0 <= i <= 47 -> lf_core cx ms3 ->
  chk_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 (nb2 ++ nb1 ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 2) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) (LF_LIVE_HELD + 2 * 40) k2 SH_R ly3 S3 W3 ms3 md3 ->
  lf_cur cx W3 ms3 P N -> nk_opened kbs' <= 64 * i + 1 -> nk_sent kbs' = md_reqs mbs ->
  r_ext B cx fp md mk T3 ly3 S3 W3 ms3 kbs nm kc ac t1 t2 nb1 nb2 ->
  JRN cx fp ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  d4_keepL [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26] (ms_regs ms3) (ms_regs ms4) ->
  kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  Q' cx fp md kc ac t1 t2 ms4 ->
  RVM Q' i cx fp k2 ly3 S3 W3 ms4 md4.
Proof.
  intros Q' i cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 md mk P N kbs kbs' mbs gbs T3 nm kc ac t1 t2 nb1 nb2
    Hreg Hkc Hac Hi Hcore Hcut Hcur Hop Hrq Hext HJ4 KR KA GA Fd Fs Hq.
  assert (Hcr4 : lf_core cx ms4 /\ r_vregs cx fp i t1 t2 (r_rc (r_RR nm kc ac kbs)) (r_rc (r_LR nm kc ac kbs)) ms4).
  { destruct Hcore as (C2 & C8 & C9 & C3 & C4).
    destruct Hreg as (R18 & R19 & R20 & R23 & R24 & R25 & R26).
    kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
    kreg KR 8 (8%bv : bv 5) K8. kreg KR 9 (9%bv : bv 5) K9. kreg KR 18 (18%bv : bv 5) K18.
    kreg KR 19 (19%bv : bv 5) K19. kreg KR 20 (20%bv : bv 5) K20. kreg KR 23 (23%bv : bv 5) K23.
    kreg KR 24 (24%bv : bv 5) K24. kreg KR 25 (25%bv : bv 5) K25. kreg KR 26 (26%bv : bv 5) K26.
    split; [unfold lf_core; rewrite K2, K8, K9, K3, K4 | unfold r_vregs; rewrite K18, K19, K20, K23, K24, K25, K26];
      repeat split; assumption. }
  destruct Hcr4 as (Hcore4 & Hreg4).
  exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, nm, kc, ac, t1, t2, nb1, nb2.
  split; [exact Hreg4|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
  split; [exact Hcore4|].
  split; [exact (chk_cut_run SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 ms4 md3 md4
            SH_R_len Hcut HJ4 KA GA Fd Fs)|].
  split; [exact (lf_cur_keep (fun _ => False) cx W3 ms3 W3 ms4 P N KA (fun a _ H => H) Hcur)|].
  split; [exact Hop|]. split; [exact Hrq|].
  split; [exact (r_ext_run B cx fp md mk T3 ly3 S3 W3 ms3 ms4 kbs nm kc ac t1 t2 nb1 nb2 KA GA Hext)|].
  exact Hq.
Qed.

(* a state of the stretch moved along a run that writes nothing and keeps the registers r_vregs names; the fact Q'
   of the new state from Q and the registers *)
Lemma r_vm_run : forall Q Q' i cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4,
  RVM Q i cx fp k2 ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  d4_keepL W_R3 (ms_regs ms3) (ms_regs ms4) \/
    d4_keepL [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26] (ms_regs ms3) (ms_regs ms4) ->
  kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall md kc ac t1 t2 want rc0, r_vregs cx fp i t1 t2 want rc0 ms3 -> Q cx fp md kc ac t1 t2 ms3 ->
     Q' cx fp md kc ac t1 t2 ms4) ->
  RVM Q' i cx fp k2 ly3 S3 W3 ms4 md4.
Proof.
  intros Q Q' i cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 HC HJ4 KR KA GA Fd Fs HQ.
  destruct HC as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hrq & Hext & Hq).
  assert (KR' : d4_keepL [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26] (ms_regs ms3) (ms_regs ms4)).
  { destruct KR as [KR | KR]; [|exact KR]. intros r Hr. apply KR. cbn in Hr |- *. tauto. }
  exact (r_vm_step Q' i cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 md mk P N kbs kbs' mbs gbs T3 nm kc ac t1 t2 nb1 nb2
    Hreg Hkc Hac Hi Hcore Hcut Hcur Hop Hrq Hext HJ4 KR' KA GA Fd Fs (HQ md kc ac t1 t2 _ _ Hreg Hq)).
Qed.

(* the call of a leaf callee that writes nothing, from a state of the stretch at the call to the state of the stretch
   at its return (Op0Q.v r_leaf at r_vm) *)
Lemma r_vleaf : forall (fy : YK11.FPState) pc K Pre Rd Wr Post,
  @aleaf_rd fy rc SK SEGS PCAP_RLO PCAP_RHI B pc K 0 [] Pre Rd Wr Post ->
  forall Q Q' ret i cx fp k2 ly3 S3 W3 (ms3 : machine_state) md3 POST,
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  RVM Q i cx fp k2 ly3 S3 W3 ms3 md3 ->
  0 <= K <= LLVMF_STK - 448 ->
  getr (ms_regs ms3) 1 = Z_to_bv 64 (link_text + ret) ->
  AF_LLVMFuzzerTestOneInput <= ret < AF_LLVMFuzzerTestOneInput + 0x1460 ->
  YK0s.ret_ok (getr (ms_regs ms3) 1) ->
  (forall a, ~ inFP (Wr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a) ->
  (forall a, Rd (ms_regs ms3) (rdW W3 (ms_mem ms3)) a -> akb SEGS B ly3 S3 (lf_sp1 cx - K) (lf_sp1 cx) a) ->
  Pre (ms_regs ms3) (rdW W3 (ms_mem ms3)) ->
  (forall md kc ac t1 t2 (ms2 : machine_state), Q cx fp md kc ac t1 t2 ms3 ->
     d4_keepL W_R3 (ms_regs ms3) (ms_regs ms2) -> Q' cx fp md kc ac t1 t2 ms2) ->
  pa_val A_TEXT = link_text ->
  FROM POST (RV ret Q' i) ->
  SRr SEGS W3 (mkCfg (@mkst fy (ms_regs ms3) (Z_to_bv 64 pc) (ms_mem ms3) (seg_rom SEGS)) md3) (POST cx).
Proof.
  intros fy pc K Pre Rd Wr Post HL Q Q' ret i cx fp k2 ly3 S3 W3 ms3 md3 POST HB Hfx HJ Hfr HC HK R1 Hret Hrok HW HR
    Hpre HQ HBASE HF.
  destruct HC as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hrq & Hext & Hq).
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
  destruct (r_vregs_keep cx fp i t1 t2 _ _ ms3 ms2 KT Hcore Hreg) as (Hcore2 & Hreg2).
  apply (HF cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 Hfr2).
  split.
  { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite R1, <- HBASE. repeat split; reflexivity. }
  exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, nm, kc, ac, t1, t2, nb1, nb2.
  split; [exact Hreg2|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
  split; [exact Hcore2|]. split; [exact HC2|]. split; [exact Hcur2|].
  split; [exact Hop|]. split; [exact Hrq|].
  split; [|exact (HQ md kc ac t1 t2 ms2 Hq KT)].
  exact (r_ext_callee SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp md mk T3 K _ ly3 S3 ly2 S2 W3 ms3 md3 k2 W2 ms2 md2 k2 kbs nm kc ac t1 t2 nb1 nb2
    HB HJ HJ2 Hfr ltac:(rewrite Hfr2, Hfr; reflexivity) HCALL2 (fun a H => HW a H) HPERM2 Hkc Hac Hext).
Qed.


(* ==========================================================================
   The checks' facts
   ========================================================================== *)

(* check_bounds(t, c) of a text buffer the library filled (check_bounds_c.v's Pre and read set) *)
Lemma r_bnd_pre : forall cx fp ly3 S3 W3 mem md3 k2 (regs : bvmap 5 word) t c s,
  BASEF cx -> JRN cx fp ly3 S3 W3 mem md3 k2 ->
  In (t, c + 1) (ablocks B ly3 S3) -> 1 <= c < 40 ->
  abuf SEGS (rdW W3 mem) t c -> acstr_at SEGS (rdW W3 mem) t s -> Z.of_nat (length s) <= c - 1 ->
  au8arr SEGS (rdW W3 mem) (t + c) [zb GUARD_BYTE] ->
  aarg regs 0 = t -> aarg regs 1 = c -> spZ regs = lf_sp1 cx ->
  check_bounds_apre SEGS regs (rdW W3 mem) /\
  (forall a, check_bounds_ard regs (rdW W3 mem) a -> akb SEGS B ly3 S3 (lf_sp1 cx - CHECK_BOUNDS_AK) (lf_sp1 cx) a).
Proof.
  intros cx fp ly3 S3 W3 mem md3 k2 regs t c s HB HJ Hin Hc Hbuf Hs Hl Hg Ha0 Ha1 Hsp.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H16 & H4096 & Hceil & Happ & _).
  assert (RQ : req_size (c + 1) = c + 1)
    by (unfold req_size; destruct (c + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
  rewrite RQ in Hceil, Happ.
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    mem md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  destruct (r_atbuf SEGS (rdW W3 mem) t c s Hbuf Hs ltac:(lia) Hg) as (bs & Hbs & Hz).
  split.
  - unfold check_bounds_apre. rewrite Ha0, Ha1. exists bs.
    split; [lia|]. split; [lia|]. split; [exact Hbs|]. split; [exact Hz|].
    split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *; lia|].
    split; [rewrite ard_aview; apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem md3 t (c + 1) t (c + 1) HAR Hin);
            rewrite ?RQ; lia|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem md3 t (c + 1) t c HAR Hin);
            rewrite ?RQ; lia|].
    unfold apart_frame. left. rewrite Hsp. unfold CHECK_BOUNDS_AK, CHECK_BOUNDS_AFRAME, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. unfold check_bounds_ard, rd_ivl in Ha. rewrite Ha0, Ha1 in Ha.
    right; left. exists t, (c + 1). split; [exact Hin | rewrite RQ; lia].
Qed.

(* a byte of the frame is one a callee may read *)
Lemma r_fobj_akb : forall cx fp ly3 S3 W3 mem md3 k2 slo shi a,
  BASEF cx -> JRN cx fp ly3 S3 W3 mem md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_F cx fp <= a < lf_F cx fp + 1024 -> akb SEGS B ly3 S3 slo shi a.
Proof.
  intros cx fp ly3 S3 W3 mem md3 k2 slo shi a HB HJ Hfr Ha.
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 mem md3 k2 HB HJ Hfr) as (HFa & _).
  right; right; right. exists LF_CID, fp. split; [rewrite Hfr; left; reflexivity|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID) with 1024. lia.
Qed.

(* a string in wk or wa (shadow bytes 92 .. 96, 102 .. 106 of SH_R are 0), as the strcmp wrapper asks *)
Lemma r_fobj_arg : forall cx fp ly3 S3 W3 ms3 md3 k2 (regs : bvmap 5 word) K lo off s,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_fshadow cx fp W3 ms3 SH_R ->
  (lo = 92 /\ off = LO_B2E0) \/ (lo = 102 /\ off = LO_B330) ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + off) s -> Z.of_nat (length s) <= 39 ->
  alloc_ceiling <= spZ regs - K ->
  astrcmp_arg SEGS regs K (rdW W3 (ms_mem ms3)) (lf_F cx fp + off) s.
Proof.
  intros cx fp ly3 S3 W3 ms3 md3 k2 regs K lo off s HB HJ Hfr Hfs Hlo Hs Hl HK.
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & _).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (Hoff : off = 8 * lo /\ 92 <= lo <= 102)
    by (destruct Hlo as [(-> & ->) | (-> & ->)]; unfold LO_B2E0, LO_B330; lia).
  destruct Hoff as (Hoff & Hlo').
  destruct (r_buf_shadow cx fp W3 ms3 SH_R lo 5 Hfs SH_R_len F32 F4 Fc ltac:(lia) ltac:(lia) ltac:(lia)) as (RA & HV).
  { intros j Hj. destruct Hlo as [(-> & _) | (-> & _)]; change (Z.to_nat 92) with 92%nat in Hj;
      change (Z.to_nat 102) with 102%nat in Hj; change (Z.to_nat (92 + 5)) with 97%nat in Hj;
      change (Z.to_nat (102 + 5)) with 107%nat in Hj.
    - assert (Hj' : (j = 92 \/ j = 93 \/ j = 94 \/ j = 95 \/ j = 96)%nat) by lia.
      repeat (destruct Hj' as [-> | Hj']; [reflexivity|]). subst j. reflexivity.
    - assert (Hj' : (j = 102 \/ j = 103 \/ j = 104 \/ j = 105 \/ j = 106)%nat) by lia.
      repeat (destruct Hj' as [-> | Hj']; [reflexivity|]). subst j. reflexivity. }
  change (8 * 5) with 40 in RA, HV. rewrite <- Hoff in RA, HV.
  set (F := lf_F cx fp) in *.
  assert (Hm : (F + off + Z.of_nat (length s)) mod 8 = Z.of_nat (length s) mod 8).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D.
    rewrite D, Hoff. replace (32 * (F / 32) + 8 * lo + Z.of_nat (length s))
      with (Z.of_nat (length s) + (4 * (F / 32) + lo) * 8) by lia.
    apply Z_mod_plus_full. }
  split; [lia|]. split; [lia|].
  split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *; lia|].
  split; [rewrite ard_aview; intros x Hx; apply RA; lia|].
  split; [rewrite ard_aview; apply (r_hull_sub _ _ 40); [exact HV | lia | lia]|].
  split; [unfold apart_frame; left; unfold LO_B2E0, LO_B330 in *; lia|].
  intros a Ha. rewrite ard_aview. apply dec_aview_present.
  pose proof (Z.mod_pos_bound (Z.of_nat (length s)) 8 ltac:(lia)).
  apply (proj1 (Fpres a ltac:(unfold LO_B2E0, LO_B330 in *; lia))).
Qed.

(* check_read's Pre and read set: the library's answer is the model's (link_spec.v read_agree), its strings in the
   buffers or, at a zero cap, wk and wa *)
Lemma r_cread_pre : forall cx fp ly3 S3 W3 ms3 md3 k2 (regs : bvmap 5 word) md mk kbs nm kc ac t1 t2 nb1 nb2 T3,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_fshadow cx fp W3 ms3 SH_R -> 0 <= kc < 40 -> 0 <= ac < 40 ->
  r_ext B cx fp md mk T3 ly3 S3 W3 ms3 kbs nm kc ac t1 t2 nb1 nb2 ->
  spZ regs = lf_sp1 cx ->
  getr regs 10 = w64 (r_rc (r_LR nm kc ac kbs)) -> getr regs 11 = w64 (r_rc (r_RR nm kc ac kbs)) ->
  aarg regs 2 = (if t1 =? 0 then lf_F cx fp + LO_B2E0 else t1) -> aarg regs 3 = lf_F cx fp + LO_B2E0 ->
  aarg regs 4 = (if t2 =? 0 then lf_F cx fp + LO_B330 else t2) -> aarg regs 5 = lf_F cx fp + LO_B330 ->
  check_read_apre SEGS regs (rdW W3 (ms_mem ms3)) /\
  (forall a, check_read_ard SEGS regs (rdW W3 (ms_mem ms3)) a ->
     akb SEGS B ly3 S3 (lf_sp1 cx - CHECK_READ_AK) (lf_sp1 cx) a).
Proof.
  intros cx fp ly3 S3 W3 ms3 md3 k2 regs md mk kbs nm kc ac t1 t2 nb1 nb2 T3 HB HJ Hfr Hfs Hkc Hac
    (Hbufs & X1 & X2 & (WK & _) & (WA & _) & _ & RRC) Hsp R10 R11 A2 A3 A4 A5.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  pose proof Hbufs as (Hnb1 & Hnb2 & Hbin & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlw & H47).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (HK : alloc_ceiling <= spZ regs - CHECK_READ_AK)
    by (rewrite Hsp; unfold CHECK_READ_AK, CHECK_READ_AFRAME, ESTACK, LLVMF_STK in *; lia).
  set (F := lf_F cx fp) in *.
  set (sk := r_kind (r_RR nm kc ac kbs)). set (sa := r_alias (r_RR nm kc ac kbs)).
  assert (EK : r_kind (r_LR nm kc ac kbs) = sk) by reflexivity.
  assert (EA : r_alias (r_LR nm kc ac kbs) = sa) by reflexivity.
  rewrite EK in X1. rewrite EA in X2.
  pose proof (r_kind_fit lf_tab nm kc ac [] (nk_kstate kbs) Hkc) as Lk.
  pose proof (r_alias_fit lf_tab nm kc ac [] (nk_kstate kbs) Hac) as La.
  change (r_kind (read_core lf_tab nm kc ac [] (nk_kstate kbs))) with sk in Lk.
  change (r_alias (read_core lf_tab nm kc ac [] (nk_kstate kbs))) with sa in La.
  (* a string of the read, in its buffer or in the frame *)
  assert (STR : forall t c nb lo off str, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> c < 40 ->
      (lo = 92 /\ off = LO_B2E0) \/ (lo = 102 /\ off = LO_B330) ->
      acstr_at SEGS (rdW W3 (ms_mem ms3)) (F + off) str ->
      (1 <= c -> acstr_at SEGS (rdW W3 (ms_mem ms3)) t str /\ abuf SEGS (rdW W3 (ms_mem ms3)) t c /\
        au8arr SEGS (rdW W3 (ms_mem ms3)) (t + c) [zb GUARD_BYTE]) ->
      Z.of_nat (length str) <= 39 -> (1 <= c -> Z.of_nat (length str) <= c - 1) ->
      acstr_at SEGS (rdW W3 (ms_mem ms3)) (if t =? 0 then F + off else t) str /\
      astrcmp_arg SEGS regs CHECK_READ_AK (rdW W3 (ms_mem ms3)) (if t =? 0 then F + off else t) str /\
      (forall a, (if t =? 0 then F + off else t) <= a <= (if t =? 0 then F + off else t) + Z.of_nat (length str) ->
         akb SEGS B ly3 S3 (lf_sp1 cx - CHECK_READ_AK) (lf_sp1 cx) a)).
  { intros t c nb lo off str Hnb Hinc Hc40 Hlo Hf Hb L39 Lc.
    assert (Hoff : F + off + 40 <= F + 1024) by (destruct Hlo as [(_ & ->) | (_ & ->)]; unfold LO_B2E0, LO_B330; lia).
    destruct (Z.eqb_spec t 0) as [E0 | E0].
    - split; [exact Hf|]. split; [exact (r_fobj_arg cx fp ly3 S3 W3 ms3 md3 k2 regs CHECK_READ_AK lo off str
        HB HJ Hfr Hfs Hlo Hf L39 HK)|].
      intros a Ha. apply (r_fobj_akb cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 _ _ a HB HJ Hfr).
      destruct Hlo as [(_ & ->) | (_ & ->)]; unfold LO_B2E0, LO_B330 in *; lia.
    - destruct Hnb as [(_ & E1 & _) | (H1 & H4 & ->)]; [contradiction|].
      destruct (Hb H1) as (Hs & _ & _).
      assert (Hin : In (t, c + 1) (ablocks B ly3 S3)) by exact (proj1 (Hbin (t, c + 1) (Hinc _ (or_introl eq_refl)))).
      pose proof (Lc H1) as Lc1.
      split; [exact Hs|].
      split; [apply r_arg_of_rt; apply (dec_blk_rt B LAWS ly3 S3 W3 (ms_mem ms3) md3 regs CHECK_READ_AK t (c + 1) str
          HAR Hin); [unfold text_of_c.TEXT_OF_LIVE; lia | exact Hs | exact HK]|].
      intros a Ha. right; left. exists t, (c + 1). split; [exact Hin|].
      unfold req_size. destruct (c + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]. }
  destruct (STR t1 kc nb1 92 LO_B2E0 sk Hnb1 ltac:(intros x Hx; apply in_or_app; left; exact Hx) ltac:(lia)
    ltac:(left; split; reflexivity) WK X1 ltac:(lia) ltac:(lia)) as (K1 & K1a & K1r).
  destruct (STR 0 0 [] 92 LO_B2E0 sk ltac:(left; repeat split) ltac:(intros x []) ltac:(lia) ltac:(left; split; reflexivity) WK
    ltac:(lia) ltac:(lia) ltac:(lia)) as (K2 & K2a & K2r).
  destruct (STR t2 ac nb2 102 LO_B330 sa Hnb2 ltac:(intros x Hx; apply in_or_app; right; exact Hx) ltac:(lia)
    ltac:(right; split; reflexivity) WA X2 ltac:(lia) ltac:(lia)) as (K3 & K3a & K3r).
  destruct (STR 0 0 [] 102 LO_B330 sa ltac:(left; repeat split) ltac:(intros x []) ltac:(lia) ltac:(right; split; reflexivity) WA
    ltac:(lia) ltac:(lia) ltac:(lia)) as (K4 & K4a & K4r).
  cbn [Z.eqb] in K2, K2a, K2r, K4, K4a, K4r.
  split.
  - unfold check_read_apre. rewrite R10, R11.
    assert (Em : r_rc (r_RR nm kc ac kbs) = norm_rc (r_rc (r_LR nm kc ac kbs))) by reflexivity.
    rewrite Em. destruct (r_same_rc _ RRC) as (C1 & C2).
    split; [exact C1|]. split; [exact C2|].
    intros _. exists sk, sk, sa, sa. rewrite A2, A3, A4, A5.
    repeat (split; [eassumption|]). split; reflexivity.
  - intros a (_ & Ha). unfold check_read_str in Ha.
    destruct Ha as [(x & Hx & Ha) | [(x & Hx & Ha) | [(x & Hx & Ha) | (x & Hx & Ha)]]];
      [rewrite A2 in Hx, Ha | rewrite A3 in Hx, Ha | rewrite A4 in Hx, Ha | rewrite A5 in Hx, Ha].
    + rewrite (kp_acstr_unique _ _ _ _ _ Hx K1) in Ha. exact (K1r a Ha).
    + rewrite (kp_acstr_unique _ _ _ _ _ Hx K2) in Ha. exact (K2r a Ha).
    + rewrite (kp_acstr_unique _ _ _ _ _ Hx K3) in Ha. exact (K3r a Ha).
    + rewrite (kp_acstr_unique _ _ _ _ _ Hx K4) in Ha. exact (K4r a Ha).
Qed.

(* ==========================================================================
   The stretch, from its end back
   ========================================================================== *)

(* +0xf74 .. +0xf78: `mv a0, s6; jal check_requests` (0x869a8), to its return +0xf7c: the requests the library sent
   are the ones the model owes *)
Lemma r_cq : forall POST i, FROM POST (RV LR_e r_q5 i) -> FROM POST (RV LR_r r_q5 i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  pose proof HM as HM0.
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hrq & Hext & (Q21 & Q22 & Q27)).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlw & H47).
  rewrite (lf_shape_eta fy LR_r ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_r) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_r)) (ms_mem ms3) (seg_rom SEGS)))))
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
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  ew_reg EL 22%nat (22%bv : bv 5) Q10. rewrite Q22 in Q10. rewrite HBASE in Q1.
  assert (HMA : RVM r_q5 i cx fp k2 ly3 S3 W3 msA mdA).
  { apply (r_vm_run r_q5 r_q5 i cx fp k2 ly3 S3 W3 ms3 md3 msA mdA HM0 HJ (or_introl KR) KA HGA FdA FsA).
    intros md' kc' ac' t1' t2' want' rc' _ (A21 & A22 & A27).
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 27 (27%bv : bv 5) K27.
    unfold r_q5. rewrite K21, K22, K27. exact (conj A21 (conj A22 A27)). }
  pose proof (chk_cut_run SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 msA md3 mdA
    SH_R_len Hcut HJ KA HGA FdA FsA) as HCA.
  pose proof HCA as (HJA & _ & _ & _ & _ & _ & _ & HblkA & HdatA).
  pose proof HJA as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  pose proof HblkA as (BmdA & _).
  pose proof HdatA as (Dk & Dwf & _ & _ & _ & _ & Dmd & Dmwf & _).
  pose proof Dk as (_ & KL). pose proof Dmd as (_ & ML).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) mdA md MD_SIZE HARA BmdA) as (_ & Bm4096 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  kreg KR 2 (2%bv : bv 5) K2.
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HKr : CHECK_REQUESTS_AK = 8272) by reflexivity.
  assert (Ha0 : aarg (ms_regs msA) 0 = md)
    by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; unfold alloc_ceiling in *; lia).
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk T3 (ms_regs msA) CHECK_REQUESTS_AK HB HJA HblkA Rsp
    ltac:(rewrite HKr; unfold LLVMF_STK; lia)) as (_ & _ & M3 & M4 & M5 & _ & _ & M8 & M9).
  replace (pa_sigma LS_check_requests) with CHECK_REQUESTS_A by (rewrite (lv_sigma LV); reflexivity).
  apply (r_vleaf fy CHECK_REQUESTS_A CHECK_REQUESTS_AK (check_requests_apre SEGS) check_requests_ard
    check_requests_awr check_requests_apost (CREQ fy) r_q5 r_q5 LR_e i cx fp k2 ly3 S3 W3 msA mdA POST HB Hfx HJ Hfr
    HMA).
  - rewrite HKr. unfold LLVMF_STK. lia.
  - rewrite Q1. reflexivity.
  - unfold LR_e. lia.
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a (r & [] & _).
  - intros a Ha. unfold check_requests_ard, rd_ivl in Ha. rewrite Ha0 in Ha. right; left. exists md, MD_SIZE.
    split; [exact BmdA|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in Ha. lia.
  - unfold check_requests_apre. exists kbs', mbs. rewrite Ha0.
    destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem msA) mdA HARA) as (Gra & Ghv).
    split; [exact Dk|]. split; [exact Dmd|]. split; [exact Dwf|]. split; [exact Dmwf|].
    split; [exact (u_requests_are kbs' mbs KL ML Dwf Dmwf Hrq)|].
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact Gra|]. split; [exact Ghv|].
    split; [exact M9 | exact M8].
  - intros md' kc' ac' t1' t2' ms2 (A21 & A22 & A27) K'.
    kreg K' 21 (21%bv : bv 5) K21. kreg K' 22 (22%bv : bv 5) K22. kreg K' 27 (27%bv : bv 5) K27.
    unfold r_q5. rewrite K21, K22, K27. exact (conj A21 (conj A22 A27)).
  - exact HBASE.
  - exact HL.
Qed.

(* +0xf40 .. +0xf44: `mv a4, s10; j +0xf4c`: the alias pointer is the buffer *)
Lemma r_ba : forall POST i, FROM POST (RV LR_g r_q4 i) -> FROM POST (RV LR_b2 r_q3b i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  pose proof HB as (HPRE & Hfrm & HGX & _).
  rewrite (lf_shape_eta fy LR_b2 ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_b2) as HS.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_b2)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_g; [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
  assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
  pose proof (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk)) as KR.
  prreg HS (14%bv : bv 5) Q14. ew_reg EL 26%nat (26%bv : bv 5) Q14.
  apply (HL cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
  split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
  apply (r_vm_run r_q3b r_q4 i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB HM HJ (or_introl KR)
    (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs).
  intros md kc ac t1 t2 want rc0 (_ & _ & _ & _ & _ & _ & R26) ((A21 & A22 & A27) & Ht2).
  kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 27 (27%bv : bv 5) K27.
  split; [unfold r_q3; rewrite K21, K22, K27; exact (conj A21 (conj A22 A27))|].
  rewrite Q14, R26. destruct (Z.eqb_spec t2 0); [contradiction | reflexivity].
Qed.

(* at check_read's call (+0xf70): its six arguments, s5 and s11 reloaded *)
Definition r_qc (cx : lcx) (fp md kc ac t1 t2 : Z) (ms : machine_state) : Prop :=
  r_q5 cx fp md kc ac t1 t2 ms /\
  getr (ms_regs ms) 10 = getr (ms_regs ms) 18 /\ getr (ms_regs ms) 11 = getr (ms_regs ms) 20 /\
  getr (ms_regs ms) 12 = w64 (if t1 =? 0 then lf_F cx fp + LO_B2E0 else t1) /\
  getr (ms_regs ms) 13 = w64 (lf_F cx fp + LO_B2E0) /\
  getr (ms_regs ms) 14 = w64 (if t2 =? 0 then lf_F cx fp + LO_B330 else t2) /\
  getr (ms_regs ms) 15 = w64 (lf_F cx fp + LO_B330).

(* the call of check_read (0x86930) at +0xf70, to its return +0xf74 *)
Lemma r_cr_call : forall POST i, FROM POST (RV LR_r r_q5 i) ->
  forall (fy : YK11.FPState) cx fp k2 ly3 S3 W3 (ms3 : machine_state) md3,
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  RVM r_qc i cx fp k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 1 = Z_to_bv 64 (link_text + LR_r) ->
  SRr SEGS W3 (mkCfg (@mkst fy (ms_regs ms3) (Z_to_bv 64 (pa_sigma LS_check_read)) (ms_mem ms3) (seg_rom SEGS)) md3)
    (POST cx).
Proof.
  intros POST i HL fy cx fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HM R1.
  pose proof HM as HM0.
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hrq & Hext & (_ & Q10 & Q11 & Q12 & Q13 & Q14 & Q15)).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & _).
  pose proof Hreg as (R18 & R19 & R20 & R23 & R24 & R25 & R26).
  pose proof Hcut as (_ & _ & _ & _ & HfsC & _).
  pose proof Hext as (Hbufs & _).
  pose proof Hbufs as (Hnb1 & Hnb2 & Hbin & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlw & H47).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & _).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (Rsp : spZ (ms_regs ms3) = lf_sp1 cx)
    by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (TR : forall t c nb, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> 0 <= t < 2 ^ 64).
  { intros t c nb Hnb Hinc. destruct Hnb as [(_ & -> & _) | (H1 & H4 & ->)]; [lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (proj1 (Hbin (t, c + 1) (Hinc _ (or_introl eq_refl)))))
      as (_ & _ & Hc & _).
    unfold req_size in Hc. destruct (c + 1 =? 0); unfold alloc_ceiling in *; lia. }
  pose proof (TR t1 kc nb1 Hnb1 ltac:(intros x Hx; apply in_or_app; left; exact Hx)) as T1r.
  pose proof (TR t2 ac nb2 Hnb2 ltac:(intros x Hx; apply in_or_app; right; exact Hx)) as T2r.
  assert (FR : forall off, 0 <= off <= 1024 -> 0 <= lf_F cx fp + off < 2 ^ 64)
    by (intros off Ho; unfold alloc_ceiling in *; lia).
  assert (A2 : aarg (ms_regs ms3) 2 = (if t1 =? 0 then lf_F cx fp + LO_B2E0 else t1)).
  { rewrite ar_aarg2, Q12. apply unsigned_lit_small. destruct (t1 =? 0); [apply FR; unfold LO_B2E0; lia | exact T1r]. }
  assert (A3 : aarg (ms_regs ms3) 3 = lf_F cx fp + LO_B2E0)
    by (rewrite ar_aarg3, Q13; apply unsigned_lit_small; apply FR; unfold LO_B2E0; lia).
  assert (A4 : aarg (ms_regs ms3) 4 = (if t2 =? 0 then lf_F cx fp + LO_B330 else t2)).
  { rewrite ar_aarg4, Q14. apply unsigned_lit_small. destruct (t2 =? 0); [apply FR; unfold LO_B330; lia | exact T2r]. }
  assert (A5 : aarg (ms_regs ms3) 5 = lf_F cx fp + LO_B330)
    by (rewrite ar_aarg5, Q15; apply unsigned_lit_small; apply FR; unfold LO_B330; lia).
  destruct (r_cread_pre cx fp ly3 S3 W3 ms3 md3 k2 (ms_regs ms3) md mk kbs nm kc ac t1 t2 nb1 nb2 T3 HB HJ Hfr HfsC
    Hkc Hac Hext Rsp ltac:(rewrite Q10; exact R18) ltac:(rewrite Q11; exact R20) A2 A3 A4 A5) as (Hpre & Hrd).
  replace (pa_sigma LS_check_read) with CHECK_READ_A by (rewrite (lv_sigma LV); reflexivity).
  apply (r_vleaf fy CHECK_READ_A CHECK_READ_AK (check_read_apre SEGS) (check_read_ard SEGS) check_read_awr
    check_read_apost (CREAD fy) r_qc r_q5 LR_r i cx fp k2 ly3 S3 W3 ms3 md3 POST HB Hfx HJ Hfr HM0).
  - unfold CHECK_READ_AK, CHECK_READ_AFRAME, ESTACK, LLVMF_STK. lia.
  - exact R1.
  - unfold LR_r. lia.
  - rewrite R1, <- HBASE. apply ret_ok_codeptr_v; [unfold LR_r, AF_LLVMFuzzerTestOneInput; lia | reflexivity].
  - intros a (r & [] & _).
  - exact Hrd.
  - exact Hpre.
  - intros md' kc' ac' t1' t2' ms2 ((A21 & A22 & A27) & _) K'.
    kreg K' 21 (21%bv : bv 5) K21. kreg K' 22 (22%bv : bv 5) K22. kreg K' 27 (27%bv : bv 5) K27.
    unfold r_q5. rewrite K21, K22, K27. exact (conj A21 (conj A22 A27)).
  - exact HBASE.
  - exact HL.
Qed.

(* +0xf4c .. +0xf70: `ld s11, 0xf8(s1); ld s5, 0x98(s1); ld a2, 0x88(s1); beqz s7; mv a2, s7; mv a0, s2; mv a1, s4;
   ld a3, 0x88(s1); ld a5, 0x80(s1); jal check_read` *)
Lemma r_cr : forall POST i, FROM POST (RV LR_r r_q5 i) -> FROM POST (RV LR_g r_q4 i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hrq & Hext & ((Q21 & Q22 & Q27) & Q14)).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R23 & R24 & R25 & R26).
  pose proof Hcut as (_ & _ & _ & _ & _ & Hsl & _ & HblkC & _).
  pose proof Hsl as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17
    & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29).
  pose proof Hext as (Hbufs & _). pose proof Hbufs as (Hnb1 & _ & Hbin & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlw & H47).
  assert (Hs32 : lf_sp1 cx mod 32 = 0) by (unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
    apply Z_mod_mult).
  pose proof alloc_ceiling_value as ((Cmin0 & Cmax0) & _).
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & _).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HblkC as (BmdC & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 BmdC) as (_ & Bm4096 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  assert (RNG : forall x, 0 <= x <= alloc_ceiling -> 0 <= x < 2 ^ 64) by (intros x Hx; unfold alloc_ceiling in *; lia).
  assert (T1r : 0 <= t1 < 2 ^ 64).
  { destruct Hnb1 as [(_ & -> & _) | (H1 & H4 & ->)]; [lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (proj1 (Hbin (t1, kc + 1) ltac:(left; reflexivity))))
      as (_ & _ & Hc & _).
    unfold req_size in Hc. destruct (kc + 1 =? 0); apply RNG; lia. }
  pose proof (v_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_g (lf_F cx fp + LO_B330) (lf_F cx fp + LO_B2E0)
    (md + MD_N_MARK) md SHADOW_OFF
    ltac:(rewrite HU9; unfold LLVMF_STK in *; lia) ltac:(rewrite HU9; exact Hs32)
    ltac:(apply RNG; unfold LO_B330; lia) ltac:(apply RNG; unfold LO_B2E0; lia)
    ltac:(apply RNG; unfold MD_N_MARK, MD_SIZE in *; lia) ltac:(apply RNG; lia) ltac:(unfold SHADOW_OFF; lia)
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S13))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S14))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S16))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S26))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S28))) as HS.
  set (ex := [Z_to_bv 64 (lf_F cx fp + LO_B330); Z_to_bv 64 (lf_F cx fp + LO_B2E0); Z_to_bv 64 (md + MD_N_MARK);
    Z_to_bv 64 md; Z_to_bv 64 SHADOW_OFF]) in HS.
  set (E := Eimg (Ereg (ms_regs ms3) ex)) in HS.
  rewrite (lf_shape_eta fy LR_g ms3 Hsh).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_g)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) ex) n)
    by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
  assert (E23 : ew E 23 = w64 t1)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 23 23%bv eq_refl); exact R23).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j ex (Z_to_bv 64 0))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ ex j)).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. unfold ex in E32, E33, E34, E35, E36.
  cbn [nth Nat.add] in E32, E33, E34, E35, E36.
  clearbody E. clear EX.
  assert (WK : forall msA mdA, JRN cx fp ly3 S3 W3 (ms_mem msA) mdA k2 ->
      d4_keepL [2; 3; 4; 8; 9; 14; 18; 19; 20; 22; 23; 24; 25; 26] (ms_regs ms3) (ms_regs msA) ->
      kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA)) ->
      mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA)) ->
      m_fds mdA = m_fds md3 -> m_fs mdA = m_fs md3 ->
      getr (ms_regs msA) 1 = Z_to_bv 64 (link_text + LR_r) ->
      getr (ms_regs msA) 10 = ew E 18 -> getr (ms_regs msA) 11 = ew E 20 ->
      getr (ms_regs msA) 12 = w64 (if t1 =? 0 then lf_F cx fp + LO_B2E0 else t1) ->
      getr (ms_regs msA) 13 = ew E 33 -> getr (ms_regs msA) 15 = ew E 32 ->
      getr (ms_regs msA) 21 = ew E 34 -> getr (ms_regs msA) 27 = ew E 36 ->
      SRr SEGS W3 (mkCfg (@mkst fy (ms_regs msA) (Z_to_bv 64 (pa_sigma LS_check_read)) (ms_mem msA) (seg_rom SEGS)) mdA)
        (POST cx)).
  { intros msA mdA HJA KR KA GA FdA FsA Q1 Q10 Q11 Q12 Q13 Q15 Q21' Q27'.
    apply (r_cr_call POST i HL fy cx fp k2 ly3 S3 W3 msA mdA HB Hfx HJA Hfr); [|exact Q1].
    apply (r_vm_step r_qc i cx fp k2 ly3 S3 W3 ms3 md3 msA mdA md mk P N kbs kbs' mbs gbs T3 nm kc ac t1 t2 nb1 nb2
      Hreg Hkc Hac Hi Hcore Hcut Hcur Hop Hrq Hext HJA
      ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) KA GA FdA FsA).
    kreg KR 14 (14%bv : bv 5) K14. kreg KR 18 (18%bv : bv 5) K18. kreg KR 20 (20%bv : bv 5) K20.
    kreg KR 22 (22%bv : bv 5) K22.
    rewrite EL in Q10, Q11 by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat _ _ 18 18%bv eq_refl) in Q10. rewrite (ew_Ereg_nat _ _ 20 20%bv eq_refl) in Q11.
    rewrite E33 in Q13. rewrite E32 in Q15. rewrite E34 in Q21'. rewrite E36 in Q27'.
    unfold r_qc, r_q5. rewrite Q21', Q27', K22, Q22, Q10, Q11, Q12, Q13, Q15, K14, Q14, K18, K20.
    repeat split; reflexivity. }
  paj_run_tok RUN HS HJ SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [v_ss v_slot_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (v_kagree _ _ _ _ eq_refl HFrB) as KB.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* taken: kind NULL, a2 := wk *)
    rewrite chk_beq_any, E23 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply Z.eqb_eq in Hc. subst t1.
    paj_run_tok RUN HS HJ SHOK (0, 0);
      [apply awr_ok_x_cons; [cbn [v_ss v_slot_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 14; 18; 19; 20; 22; 23; 24; 25; 26] HS EL
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk))
      as KR.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
    assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (15%bv : bv 5) Q15. prreg HS (21%bv : bv 5) Q21'.
    prreg HS (27%bv : bv 5) Q27'. rewrite HBASE in Q1. rewrite E33 in Q12.
    pose proof (v_kagree _ _ _ _ eq_refl HFrA) as KA'.
    apply (WK msA mdA HJ KR ltac:(intros a Ha; rewrite (KA' a Ha); exact (KB a Ha))
      ltac:(intros x Hx; exact (HGA x (HGB x Hx))) FdA FsA ltac:(rewrite Q1; reflexivity)
      Q10 Q11 Q12 Q13 Q15 Q21' Q27').
  - (* not taken: a2 := kind *)
    rewrite chk_beq_any, E23 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0);
      [apply awr_ok_x_cons; [cbn [v_ss v_slot_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 14; 18; 19; 20; 22; 23; 24; 25; 26] HS EL
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk))
      as KR.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
    assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (15%bv : bv 5) Q15. prreg HS (21%bv : bv 5) Q21'.
    prreg HS (27%bv : bv 5) Q27'. rewrite HBASE in Q1. rewrite E23 in Q12.
    pose proof (v_kagree _ _ _ _ eq_refl HFrA) as KA'.
    apply (WK msA mdA HJ KR ltac:(intros a Ha; rewrite (KA' a Ha); exact (KB a Ha))
      ltac:(intros x Hx; exact (HGA x (HGB x Hx))) FdA FsA ltac:(rewrite Q1; reflexivity)
      Q10 Q11 ltac:(rewrite Q12; destruct (Z.eqb_spec t1 0); [contradiction | reflexivity]) Q13 Q15 Q21' Q27').
Qed.



(* +0xf2c .. +0xf3c: `ld s6, 0xe8(s1)` (m); `beqz s10`: NULL to +0xf48 `ld a4, 0x80(s1)` (wa) and on to +0xf4c; else
   `mv a0, s10; mv a1, s11; jal check_bounds` (0x868ac), to its return +0xf40 *)
Lemma r_bv : forall POST i,
  FROM POST (RV LR_b2 r_q3b i) -> FROM POST (RV LR_g r_q4 i) -> FROM POST (RC LR_k (fun _ _ => True) i).
Proof.
  intros POST i HLB HLG cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext & _).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  assert (Hreg' : r_vregs cx fp i t1 t2 (r_rc (r_RR nm kc ac kbs)) (r_rc (r_LR nm kc ac kbs)) ms3)
    by (unfold r_vregs; repeat split; assumption).
  assert (Hop' : nk_opened kbs' <= 64 * i + 1) by lia.
  assert (Hrq' : nk_sent kbs' = md_reqs mbs) by (rewrite Hsent, Hrq; reflexivity).
  pose proof Hcut as (_ & _ & _ & _ & _ & Hsl & _ & HblkC & _).
  pose proof Hsl as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17
    & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29).
  pose proof Hext as (Hbufs & _). pose proof Hbufs as (_ & Hnb2 & Hbin & _).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlw & H47).
  assert (Hs32 : lf_sp1 cx mod 32 = 0) by (unfold lf_sp1, lf_sp1_of; rewrite Z.mul_comm; change (2 ^ 5) with 32;
    apply Z_mod_mult).
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & _).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HblkC as (BmdC & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 BmdC) as (_ & Bm4096 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (RNG : forall x, 0 <= x <= alloc_ceiling -> 0 <= x < 2 ^ 64) by (intros x Hx; unfold alloc_ceiling in *; lia).
  assert (T2r : 0 <= t2 < 2 ^ 64).
  { destruct Hnb2 as [(_ & -> & _) | (H1 & H4 & ->)]; [lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (proj1 (Hbin (t2, ac + 1)
      ltac:(apply in_or_app; right; left; reflexivity)))) as (_ & _ & Hc & _).
    unfold req_size in Hc. destruct (ac + 1 =? 0); apply RNG; lia. }
  pose proof (v_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_k (lf_F cx fp + LO_B330) (lf_F cx fp + LO_B2E0)
    (md + MD_N_MARK) md SHADOW_OFF
    ltac:(rewrite HU9; unfold LLVMF_STK in *; lia) ltac:(rewrite HU9; exact Hs32)
    ltac:(apply RNG; unfold LO_B330; lia) ltac:(apply RNG; unfold LO_B2E0; lia)
    ltac:(apply RNG; unfold MD_N_MARK, MD_SIZE in *; lia) ltac:(apply RNG; lia) ltac:(unfold SHADOW_OFF; lia)
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S13))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S14))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S16))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S26))
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S28))) as HS.
  set (ex := [Z_to_bv 64 (lf_F cx fp + LO_B330); Z_to_bv 64 (lf_F cx fp + LO_B2E0); Z_to_bv 64 (md + MD_N_MARK);
    Z_to_bv 64 md; Z_to_bv 64 SHADOW_OFF]) in HS.
  set (E := Eimg (Ereg (ms_regs ms3) ex)) in HS.
  rewrite (lf_shape_eta fy LR_k ms3 Hsh).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_k)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) ex) n)
    by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
  assert (E26 : ew E 26 = w64 t2)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 26 26%bv eq_refl); exact R26).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j ex (Z_to_bv 64 0))
    by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ ex j)).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 3%nat ltac:(lia)) as E35.
  unfold ex in E32, E35. cbn [nth Nat.add] in E32, E35.
  clearbody E. clear EX.
  paj_run_tok RUN HS HJ SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [v_ss v_slot_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (v_kagree _ _ _ _ eq_refl HFrB) as KB.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* taken: alias NULL, a4 := wa *)
    rewrite chk_beq_any, E26 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply Z.eqb_eq in Hc. subst t2.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_g;
      [apply awr_ok_x_cons; [cbn [v_ss v_slot_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                            | apply awr_ok_x_nil] |].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (d4_keep_run_pi fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] HS EL
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk))
      as KR.
    pose proof (v_kagree _ _ _ _ eq_refl HFrA) as KA'.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
    assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
    prreg HS (14%bv : bv 5) Q14. prreg HS (22%bv : bv 5) Q22'.
    apply (HLG cx fy fp k2 ly3 S3 W3 msA mdA HB Hfx HJ Hfr).
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msA HS eq_refl)|].
    apply (r_vm_step r_q4 i cx fp k2 ly3 S3 W3 ms3 md3 msA mdA md mk P N kbs kbs' mbs gbs T3 nm kc ac t1 0 nb1 nb2
      Hreg' Hkc Hac Hi Hcore Hcut Hcur Hop' Hrq' Hext HJ ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
      ltac:(intros a Ha; rewrite (KA' a Ha); exact (KB a Ha)) ltac:(intros x Hx; exact (HGA x (HGB x Hx))) FdA FsA).
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 27 (27%bv : bv 5) K27.
    split; [unfold r_q3; rewrite K21, Q22', E35, K27; repeat split; first [assumption | reflexivity]|].
    rewrite Q14, E32. reflexivity.
  - (* not taken: the alias buffer *)
    rewrite chk_beq_any, E26 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0);
      [apply awr_ok_x_cons; [cbn [v_ss v_slot_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                            | apply awr_ok_x_nil] |].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] HS EL
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk))
      as KR.
    pose proof (v_kagree _ _ _ _ eq_refl HFrA) as KA'.
    assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA)))
      by (intros a Ha; rewrite (KA' a Ha); exact (KB a Ha)).
    assert (GA : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))) by (intros x Hx; exact (HGA x (HGB x Hx))).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
    assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (22%bv : bv 5) Q22'.
    rewrite EL in Q10, Q11 by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat _ _ 26 26%bv eq_refl), R26 in Q10. rewrite (ew_Ereg_nat _ _ 27 27%bv eq_refl), R27 in Q11.
    rewrite E35 in Q22'. rewrite HBASE in Q1.
    kreg KR 2 (2%bv : bv 5) K2. kreg KR 21 (21%bv : bv 5) K21. kreg KR 27 (27%bv : bv 5) K27.
    assert (HMA : RVM r_q3b i cx fp k2 ly3 S3 W3 msA mdA).
    { apply (r_vm_step r_q3b i cx fp k2 ly3 S3 W3 ms3 md3 msA mdA md mk P N kbs kbs' mbs gbs T3 nm kc ac t1 t2 nb1 nb2
        Hreg' Hkc Hac Hi Hcore Hcut Hcur Hop' Hrq' Hext HJ ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
        KA GA FdA FsA).
      split; [unfold r_q3; rewrite K21, Q22', K27; repeat split; first [assumption | reflexivity] | exact Hc]. }
    pose proof (r_ext_run B cx fp md mk T3 ly3 S3 W3 ms3 msA kbs nm kc ac t1 t2 nb1 nb2 KA GA Hext) as (_ & _ & X2 & _).
    destruct Hnb2 as [(_ & E0 & _) | (H1 & H4 & E2)]; [contradiction|]. subst nb2.
    destruct (X2 H1) as (Xs & Xb & Xg).
    assert (Hin2 : In (t2, ac + 1) (ablocks B ly3 S3))
      by exact (proj1 (Hbin _ ltac:(apply in_or_app; right; left; reflexivity))).
    pose proof (r_alias_len lf_tab nm kc ac [] (nk_kstate kbs) H1) as La.
    assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx)
      by (unfold spZ; rewrite K2, R2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
    assert (Ha0 : aarg (ms_regs msA) 0 = t2) by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; lia).
    assert (Ha1 : aarg (ms_regs msA) 1 = ac) by (rewrite ar_aarg1, Q11; apply unsigned_lit_small; lia).
    destruct (r_bnd_pre cx fp ly3 S3 W3 (ms_mem msA) mdA k2 (ms_regs msA) t2 ac (r_alias (r_LR nm kc ac kbs))
      HB HJ Hin2 ltac:(lia) Xb Xs ltac:(unfold r_LR, read_lib; lia) Xg Ha0 Ha1 Rsp) as (Hpre & Hrd).
    replace (pa_sigma LS_check_bounds) with CHECK_BOUNDS_A by (rewrite (lv_sigma LV); reflexivity).
    apply (r_vleaf fy CHECK_BOUNDS_A CHECK_BOUNDS_AK (check_bounds_apre SEGS) check_bounds_ard check_bounds_awr
      check_bounds_apost (CBND fy) r_q3b r_q3b LR_b2 i cx fp k2 ly3 S3 W3 msA mdA POST HB Hfx HJ Hfr HMA).
    + unfold CHECK_BOUNDS_AK, CHECK_BOUNDS_AFRAME, ESTACK, LLVMF_STK. lia.
    + rewrite Q1. reflexivity.
    + unfold LR_b2. lia.
    + rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
    + intros a (r & [] & _).
    + exact Hrd.
    + exact Hpre.
    + intros md' kc' ac' t1' t2' ms2 ((A21 & A22 & A27) & Ht2) K'.
      kreg K' 21 (21%bv : bv 5) K21'. kreg K' 22 (22%bv : bv 5) K22'. kreg K' 27 (27%bv : bv 5) K27'.
      split; [unfold r_q3; rewrite K21', K22', K27'; exact (conj A21 (conj A22 A27)) | exact Ht2].
    + exact HBASE.
    + exact HLB.
Qed.

(* +0xf1c .. +0xf28: `beqz s7` (NULL, to +0xf2c); else `mv a0, s7; mv a1, s5; jal check_bounds` (0x868ac), to its
   return +0xf2c *)
Lemma r_bk : forall POST i, FROM POST (RC LR_k (fun _ _ => True) i) -> FROM POST (RC LR_c (fun _ _ => True) i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr (Hsh & HM).
  pose proof HM as HM0.
  destruct HM as (md & mk & P & N & kbs & kbs' & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hreg & Hnm &
    Hkc & Hac & Hi & Hcore & Hcut & Hcur & Hop & Hob & Href & Hsent & Hns & Hks & Hrq & Hmk & Hext & _).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof Hext as (Hbufs & _). pose proof Hbufs as (Hnb1 & _ & Hbin & _).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof alloc_ceiling_value as ((Cmin & Cmax) & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlw & H47).
  assert (T1r : 0 <= t1 < 2 ^ 64).
  { destruct Hnb1 as [(_ & -> & _) | (H1 & H4 & ->)]; [lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (proj1 (Hbin (t1, kc + 1) ltac:(left; reflexivity))))
      as (_ & _ & Hc & _).
    unfold req_size in Hc. destruct (kc + 1 =? 0); unfold alloc_ceiling in *; lia. }
  rewrite (lf_shape_eta fy LR_c ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_c) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_c)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  assert (E23 : ew E 23 = w64 t1)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 23 23%bv eq_refl); exact R23).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* taken: kind NULL *)
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_k; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    apply (HL cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    exact (r_cm_run SK B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ _ => True) (fun _ _ => True) i cx fp k2
      ly3 S3 W3 ms3 md3 msB mdB HM0 HJ
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
      (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs (fun _ H => H)).
  - (* not taken: the kind buffer *)
    rewrite chk_beq_any, E23 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R3 HS EL W_R3_low ltac:(d4chk)) as KR.
    pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
    assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    ew_reg EL 23%nat (23%bv : bv 5) Q10. ew_reg EL 21%nat (21%bv : bv 5) Q11. rewrite R23 in Q10.
    rewrite R21 in Q11. rewrite HBASE in Q1.
    pose proof (r_cm_run SK B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP _ (fun _ _ => True) i cx fp k2 ly3 S3 W3
      ms3 md3 msA mdA HM0 HJ KR KA HGA FdA FsA (fun _ H => H)) as HMA.
    pose proof (r_ext_run B cx fp md mk T3 ly3 S3 W3 ms3 msA kbs nm kc ac t1 t2 nb1 nb2 KA HGA Hext) as (_ & X1 & _).
    destruct Hnb1 as [(_ & E0 & _) | (H1 & H4 & E1)]; [contradiction|]. subst nb1.
    destruct (X1 H1) as (Xs & Xb & Xg).
    assert (Hin1 : In (t1, kc + 1) (ablocks B ly3 S3)) by exact (proj1 (Hbin _ ltac:(left; reflexivity))).
    pose proof (r_kind_len lf_tab nm kc ac [] (nk_kstate kbs) H1) as Lk.
    kreg KR 2 (2%bv : bv 5) K2.
    assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx)
      by (unfold spZ; rewrite K2, R2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
    assert (Ha0 : aarg (ms_regs msA) 0 = t1) by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; lia).
    assert (Ha1 : aarg (ms_regs msA) 1 = kc) by (rewrite ar_aarg1, Q11; apply unsigned_lit_small; lia).
    destruct (r_bnd_pre cx fp ly3 S3 W3 (ms_mem msA) mdA k2 (ms_regs msA) t1 kc (r_kind (r_LR nm kc ac kbs))
      HB HJ Hin1 ltac:(lia) Xb Xs ltac:(unfold r_LR, read_lib; lia) Xg Ha0 Ha1 Rsp) as (Hpre & Hrd).
    replace (pa_sigma LS_check_bounds) with CHECK_BOUNDS_A by (rewrite (lv_sigma LV); reflexivity).
    apply (r_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE fy
      CHECK_BOUNDS_A CHECK_BOUNDS_AK (check_bounds_apre SEGS) check_bounds_ard check_bounds_awr check_bounds_apost
      (CBND fy) (fun _ _ => True) (fun _ _ => True) LR_k i cx fp k2 ly3 S3 W3 msA mdA POST HB Hfx HJ Hfr HMA).
    + unfold CHECK_BOUNDS_AK, CHECK_BOUNDS_AFRAME, ESTACK, LLVMF_STK. lia.
    + rewrite Q1. reflexivity.
    + unfold LR_k. lia.
    + rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
    + intros a (r & [] & _).
    + exact Hrd.
    + exact Hpre.
    + intros _ _ _ _ _. exact I.
    + exact HBASE.
    + exact HL.
Qed.

(* the whole stretch, +0xf1c .. +0xf7c *)
Lemma r_verify : forall POST i,
  FROM POST (RV LR_e r_q5 i) -> FROM POST (RC LR_c (fun _ _ => True) i).
Proof.
  intros POST i HE.
  pose proof (r_cr POST i (r_cq POST i HE)) as HG.
  exact (r_bk POST i (r_bv POST i (r_ba POST i HG) HG)).
Qed.

End a.
