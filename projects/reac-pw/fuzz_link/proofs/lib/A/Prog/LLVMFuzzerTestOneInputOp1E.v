(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 662 of its 721 lines of code are new or changed and 1273 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write from reac_link_alias_write's return (+0x1098) to the join before
   check_write (+0x10e8):
     +0x1098  mv s7, a0; jal check_socket                               w_as (from w_a_inv to w_s_inv)
     +0x10a0  beqz s5 -> +0x10d8; the name's first byte (instrumented): 0 -> +0x10d8; mv a0, s6; jal wrapper_strlen
                                                                        w_sl (to w_r_inv / w_l_inv)
     +0x10c4  0xff < strlen -> +0x10d8; mv a0, s5; jal index_of         w_lx (to w_r_inv / w_x_inv)
     +0x10d4  index_of <> 0 -> +0x10e8                                  w_xj (to w_j_inv / w_r_inv)
     +0x10d8  a1 := g_nl.opened ([s1 + 0xf0] + 0x218); a0 := s4; jal check_refused   w_jr (to w_j_inv)
   The cuts are one predicate w_c at each pc, with the path's fact Q.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c model_write_c index_of_c reac_link_alias_write_c nl_talk_c check_socket_c check_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMdl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputNm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1C.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1D.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LW_sret : Z := AF_LLVMFuzzerTestOneInput + 0x10a0.   (* 0x83874, check_socket's return *)
Definition LW_lret : Z := AF_LLVMFuzzerTestOneInput + 0x10c4.   (* 0x83898, wrapper_strlen's return *)
Definition LW_xret : Z := AF_LLVMFuzzerTestOneInput + 0x10d4.   (* 0x838a8, index_of's return *)
Definition LW_r : Z := AF_LLVMFuzzerTestOneInput + 0x10d8.      (* 0x838ac, the refused block *)
Definition LW_j : Z := AF_LLVMFuzzerTestOneInput + 0x10e8.      (* 0x838bc, before check_write *)

(* the registers after +0x1098: s4 = g_nl.opened before the library call, s2 = the model's code, s7 = the
   library's code *)
Definition W_R3 : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma W_R3_saved : forall r, In r W_R3 -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.
Lemma W_R3_low : forall r, In r W_R3 -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.
Definition W_R4 : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27].
Lemma W_R4_saved : forall r, In r W_R4 -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.
Lemma W_R4_low : forall r, In r W_R4 -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.

(* the refused block's entry state: the slot [s1 + 0xf0] as atom 32, g_nl.opened as atom 33 *)
Definition w_op_rg : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x218 0x21c 0x218 0x218 [YP09.mkChunk 0x218 (CVal 4 (SOff 33 0))].
Definition w_r_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (33%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] [].
Definition w_r_ss : sstate := mkSS LW_r sr_atoms [d4_slot LS_GNL40; w_op_rg] None w_r_facts.

(* the a0 test of a bnez *)
Lemma w_bne_any : forall (E : env) n,
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (bv_unsigned (ew E n) =? 0).
Proof.
  intros E n. rewrite branch_ne_U, U_SOff, U_lit by lia. unfold zcanon, M64. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite (Z.mod_small (bv_unsigned (ew E n))) by lia. rewrite ?Z.mod_0_l by lia. reflexivity.
Qed.

(* index_of answers a table index *)
Lemma w_tab_ix : forallb (fun e => (0 <=? snd e) && (snd e <? 2 ^ 31)) lf_tab = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w_index_of_range : forall x, 0 <= index_of lf_tab x < 2 ^ 31.
Proof.
  assert (H : forall tab, forallb (fun e => (0 <=? snd e) && (snd e <? 2 ^ 31)) tab = true ->
    forall x, 0 <= index_of tab x < 2 ^ 31).
  { intros tab. induction tab as [|[n ix] tab IH]; intros Hf x; cbn [index_of]; [lia|].
    cbn [forallb snd] in Hf. apply andb_prop in Hf as [Hh Hf]. apply andb_prop in Hh as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. destruct (bl_eqb n x); [lia | exact (IH Hf x)]. }
  exact (H lf_tab w_tab_ix).
Qed.

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
(* index_of, as proved (index_of_c.v) *)
Hypothesis INDEX_OF : forall fy : YK11.FPState, @index_of_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
(* check_socket, as proved (check_socket_c.v) *)
Hypothesis CSOCK : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
(* check_refused, as proved (check_refused_c.v) *)
Hypothesis CREF : forall fy : YK11.FPState, @check_refused_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Definition w_regs3 (cx : lcx) (fp i s s6v o0 : Z) (nm : option (list byte)) (t : list byte) (K0 : kstate)
    (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 21 = w64 s /\
  getr (ms_regs ms3) 22 = w64 s6v /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 20 = w64 o0 /\
  getr (ms_regs ms3) 18 = w64 (w_rc (write_model lf_tab nm (Some t) [] K0)) /\
  getr (ms_regs ms3) 23 = w64 (w_rc (write_lib lf_tab nm (Some t) [] K0)) /\
  - 2 ^ 31 <= w_rc (write_lib lf_tab nm (Some t) [] K0) < 2 ^ 31.

(* op_write's cut at pc after the library call, with the path's fact Q *)
Definition w_c (pc : Z) (Q : machine_state -> option (list byte) -> list byte -> Prop) (i : Z) (cx : lcx)
    (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) : Prop :=
  exists (md mk P N s s6v own1 o0 : Z) (nm : option (list byte)) (t : list byte) (K0 : kstate)
    (kbs mbs gbs : list byte) (T3 nb : list (Z * Z)),
  0 <= i <= 47 /\ lf_shape fy pc ms3 /\ lf_core cx ms3 /\ w_regs3 cx fp i s s6v o0 nm t K0 ms3 /\ w_name s nm /\
  0 <= o0 <= 64 * i /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 1) (lf_mo LF_MO_SET LF_MO_OP i) (S (lf_wl i)) (LF_LIVE_HELD + TEXT_OF_LIVE) k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\
  o0 <= nk_opened kbs <= o0 + 1 /\ (w_refused nm t -> nk_opened kbs = o0) /\
  dec_ans B ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\ tx_ans B SEGS own1 nb ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_T130) = Some own1 /\ tx_nb own1 nb /\
  (own1 <> 0 -> own1 = s6v) /\ w_fresh B cx md mk T3 ly3 S3 nb /\
  nk_sent kbs = md_reqs mbs /\ Q ms3 nm t.

Definition w_j_inv := w_c LW_j (fun _ _ _ => True).
Definition w_r_inv := w_c LW_r (fun _ nm t => w_refused nm t).

(* the refused block's entry state *)
Lemma w_r_entry : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem o,
  2 ^ 46 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> bv_unsigned (getr regs 9) mod 32 = 0 ->
  0 <= o < 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + LS_GNL40) 8 (LA_G_NL + 0x40000) ->
  val_mem SEGS (mrestrict (w_H W) mem) (LA_G_NL + NK_OPENED) 4 o ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 o])) w_r_ss
    (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (BASE + LW_r)) mem (seg_rom SEGS))).
Proof.
  intros fy W regs mem o H9 H32 Ho Hv1 Hv2.
  set (E := Eimg (Ereg regs [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 o])).
  assert (E9 : ew E 9 = getr regs 9)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 (LA_G_NL + 0x40000))
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 o)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  rewrite restrict_mkst_fx. unfold w_r_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok.
    + unfold d4_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E. rewrite E9. unfold LS_GNL40. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0xf0 8 (SOff 32 0) (LA_G_NL + 0x40000));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold LA_G_NL; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold LA_G_NL; lia | change (Z.of_N 8) with 8; lia |].
      exact Hv1.
    + unfold w_op_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (u_base E 32 _ E32) by (unfold LA_G_NL; lia).
      split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0x218 4 (SOff 33 0) o);
        [rewrite (lf_sv_off E 33 _ 0 E33) by lia; rewrite Z.add_0_r; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | change (Z.of_N 4) with 4; lia |].
      replace (LA_G_NL + 0x40000 + 0x218) with (LA_G_NL + NK_OPENED) by (unfold NK_OPENED; lia). exact Hv2.
  - apply pairwise_disjoint_of_extents.
    unfold d4_slot, w_op_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. fold E. rewrite E9, E32. rewrite unsigned_lit_small by (unfold LA_G_NL; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL, LS_GNL40.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; [exact I | exact I]].
    cbn [w_r_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E9, E32, E33. rewrite !unsigned_lit_small by (unfold LA_G_NL; lia).
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the registers a cut after +0x1098 keeps across a run or a callee *)
Lemma w_regs3_keep : forall cx fp i s s6v o0 nm t K0 ms3 ms2,
  (forall r, In r W_R3 -> getr (ms_regs ms2) (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)) ->
  lf_core cx ms3 -> w_regs3 cx fp i s s6v o0 nm t K0 ms3 -> lf_core cx ms2 /\ w_regs3 cx fp i s s6v o0 nm t K0 ms2.
Proof.
  intros cx fp i s s6v o0 nm t K0 ms3 ms2 K Hc Hr.
  destruct Hc as (C2 & C8 & C9 & C3 & C4).
  destruct Hr as (R19 & R21 & R22 & R24 & R25 & R26 & R27 & R20 & R18 & R23 & RRNG).
  kreg K 2 (2%bv : bv 5) K2. kreg K 3 (3%bv : bv 5) K3. kreg K 4 (4%bv : bv 5) K4. kreg K 8 (8%bv : bv 5) K8.
  kreg K 9 (9%bv : bv 5) K9. kreg K 18 (18%bv : bv 5) K18. kreg K 19 (19%bv : bv 5) K19.
  kreg K 20 (20%bv : bv 5) K20. kreg K 21 (21%bv : bv 5) K21. kreg K 22 (22%bv : bv 5) K22.
  kreg K 23 (23%bv : bv 5) K23. kreg K 24 (24%bv : bv 5) K24. kreg K 25 (25%bv : bv 5) K25.
  kreg K 26 (26%bv : bv 5) K26. kreg K 27 (27%bv : bv 5) K27.
  split; [unfold lf_core; rewrite K2, K8, K9, K3, K4 | unfold w_regs3;
    rewrite K19, K21, K22, K24, K25, K26, K27, K20, K18, K23]; repeat split; first [assumption | lia].
Qed.

(* +0x10d8 .. +0x10e4: a0 := [s1 + 0xf0] = g_nl + 0x40000, a1 := g_nl.opened, a0 := s4, jal check_refused *)
Lemma w_jr : forall POST i,
  FROM POST (w_j_inv i) -> FROM POST (w_r_inv i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HRI.
  destruct HRI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & Ho0 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & Hrf).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27 & R20 & R18 & R23 & RRNG).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  assert (Hs32 : lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (_ & R32 & _). exact R32. }
  pose proof HC as (_ & _ & _ & _ & _ & Hsl & _ & _ & Hdat).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSG & _).
  pose proof Hdat as (Dk & _).
  pose proof Dk as ((Hbk & _) & HLk).
  rewrite <- (Href Hrf) in Hob.
  assert (Hopr : 0 <= nk_opened kbs < 2 ^ 31) by (rewrite (Href Hrf); lia).
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite (lf_shape_eta fy LW_r ms3 Hsh).
  pose proof (w_r_entry fy W3 (ms_regs ms3) (ms_mem ms3) (nk_opened kbs) ltac:(rewrite HU9; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU9; exact Hs32) Hopr ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSG))
    (val_mem_of_abytes SEGS _ LA_G_NL kbs NK_OPENED 4 Hbk ltac:(unfold NK_OPENED; lia)
      ltac:(unfold NK_OPENED, NK_SIZE in *; lia))) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  set (ex := [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (nk_opened kbs)]) in HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) ex))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_r)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) ex))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) ex)) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) ex) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_opened kbs))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) ex 1)).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [w_r_ss d4_slot w_op_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
     apply awr_ok_x_cons; [cbn [w_r_ss d4_slot w_op_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
     apply awr_ok_x_nil |].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R3 HS EL W_R3_low ltac:(d4chk)) as KR.
  assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
      cbn [w_r_ss d4_slot w_op_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  pose proof (d4_dec_run B ly3 S3 _ _ s6v t KA HD) as HDA.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H)) as HTXA.
  pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msA) _ _ KA HSL) as HSLA.
  clear HD HTX HSL Hcur.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  ew_reg EL 20%nat (20%bv : bv 5) Q10. rewrite R20 in Q10. try rewrite E33 in Q11. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & _ & _ & _ & _ & HjbkA & _ & _).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  replace (pa_sigma LS_check_refused) with CHECK_REFUSED_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 CHECK_REFUSED_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS CHECK_REFUSED_A (ms_regs msA) (ms_mem msA) mdA).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_REFUSED_A
    CHECK_REFUSED_AK 0 [] check_refused_apre (fun _ _ _ => False) check_refused_awr check_refused_apost
    (proj2 (aleaf_rd_none (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B CHECK_REFUSED_A CHECK_REFUSED_AK 0 []
      check_refused_apre check_refused_awr check_refused_apost) (CREF fy))
    cx fp ly3 S3 W3 (ms_mem msA) mdA _ (ms_regs msA) (POST cx) HB HJA HRO);
    [ rewrite Q1, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
    | unfold raZ; rewrite Q1; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
    | rewrite K3, R3; exact Gp
    | rewrite K4, R4; exact Tp
    | exact Rsp
    | unfold CHECK_REFUSED_AK, CHECK_REFUSED_AFRAME, LLVMF_STK; lia
    | lia
    | unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
    | apply Forall_nil
    | intros a (r & [] & _)
    | intros a (r & [] & _)
    | intros a []
    | unfold check_refused_apre; rewrite Q10, Q11, (Href Hrf); reflexivity
    | ].
  intros W2 ly2 S2 regs2 mem2 md2 Hle2 HJ2 HP2 HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2 _.
  rewrite Z.add_0_r in HJ2.
  set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly3 S3 W3 msA mdA CHECK_REFUSED_AK
    (fun a => inFP (check_refused_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) ly2 S2 W2 ms2 md2 _
    HB HJA HCA ltac:(unfold CHECK_REFUSED_AK, CHECK_REFUSED_AFRAME, LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ2
    ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2)
    as (HC2 & HRO2 & HCALL2).
  assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in _ (Permutation_sym HPERM2) Hc)).
  pose proof (lf_cur_callee B cx CHECK_REFUSED_AK ly3 S3 ly2 S2 W3 msA W2 ms2 _ P N HCALL2
    (fun a _ H => match H with ex_intro _ r (conj Hr _) => Hr end) HcurA) as Hcur2.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly2 S2 _ _ _ s6v t HTXA Psub
    (lf_call_kagree B cx CHECK_REFUSED_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ HCALL2)
    (fun k a Hb Ha => lfx_blk B ly3 S3 ly2 S2 _ _ _ own1 k a Hb Ha (fun H => match H with ex_intro _ r (conj Hr _) => Hr end)))
    as HTX2.
  assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
  { apply (d4_slot_callee B cx CHECK_REFUSED_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ _ own1 HCALL2);
      [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLA].
    intros j Hj (r & [] & _). }
  pose proof (d4_keep_pres W_R3 _ _ W_R3_saved HP2) as KT.
  pose proof (d4_keep_trans W_R3 _ _ _ KR KT) as K2T.
  destruct (w_regs3_keep cx fp i s s6v o0 nm t K0 ms3 ms2 K2T Hcore Hreg) as (Hcore2 & Hreg2).
  apply (HL cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx ltac:(pose proof HC2 as (HJx & _); exact HJx)
    ltac:(pose proof HC2 as (_ & Hfx2 & _); exact Hfx2)).
  exists md, mk, P, N, s, s6v, own1, o0, nm, t, K0, kbs, mbs, gbs, T3, nb.
  split; [exact Hi|].
  split.
  { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite Q1, <- HBASE. unfold LW_j, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
  split; [exact Hcore2|]. split; [exact Hreg2|]. split; [exact Hnm|]. split; [exact Ho0|].
  split; [exact HC2|]. split; [exact Hcur2|]. split; [rewrite (Href Hrf); lia|]. split; [exact Href|].
  split; [exact (tx_ans_dec B own1 nb ly2 S2 _ s6v t HTX2)|].
  split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
  split; [exact (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub Hfresh)|].
  split; [exact Hsr | exact I].
Qed.

(* a cut moved along a stretch that writes nothing and keeps the registers *)
Lemma w_c_move : forall pc pc' (Q Q' : machine_state -> option (list byte) -> list byte -> Prop)
    i cx fy fp k2 ly3 S3 W3 ms3 md3 ms4 md4,
  w_c pc Q i cx fy fp k2 ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  lf_shape fy pc' ms4 ->
  d4_keepL W_R3 (ms_regs ms3) (ms_regs ms4) ->
  kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall nm t, Q ms3 nm t -> Q' ms4 nm t) ->
  w_c pc' Q' i cx fy fp k2 ly3 S3 W3 ms4 md4.
Proof.
  intros pc pc' Q Q' i cx fy fp k2 ly3 S3 W3 ms3 md3 ms4 md4 HW HJ4 Hsh4 KR KA HGA Fd Fs HQ.
  destruct HW as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & Ho0 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & Hq).
  destruct (w_regs3_keep cx fp i s s6v o0 nm t K0 ms3 ms4 KR Hcore Hreg) as (Hcore4 & Hreg4).
  exists md, mk, P, N, s, s6v, own1, o0, nm, t, K0, kbs, mbs, gbs, T3, nb.
  split; [exact Hi|]. split; [exact Hsh4|]. split; [exact Hcore4|]. split; [exact Hreg4|].
  split; [exact Hnm|]. split; [exact Ho0|].
  split; [exact (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 ms4 md3 md4 HC HJ4
            KA (fun x Hx => HGA x Hx) Fd Fs)|].
  split; [exact (lf_cur_keep (fun _ => False) cx W3 ms3 W3 ms4 P N KA (fun a _ H => H) Hcur)|].
  split; [exact Hob|]. split; [exact Href|].
  split; [exact (d4_dec_run B ly3 S3 _ _ s6v t KA HD)|].
  split; [exact (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H))|].
  split; [exact (d4_slot_run W3 (ms_mem ms3) (ms_mem ms4) _ _ KA HSL)|].
  split; [exact Hnb|]. split; [exact Hown|]. split; [exact Hfresh|]. split; [exact Hsr | exact (HQ nm t Hq)].
Qed.

Definition w_x_inv := w_c LW_xret (fun ms nm t => Z.of_nat (length t) <= 255 /\
  exists x, nm = Some x /\ x <> [] /\ getr (ms_regs ms) 10 = w64 (index_of lf_tab x)).

(* +0x10d4 `bnez a0, +0x10e8`: the name is in the table (to the join) or not (to the refused block) *)
Lemma w_xj : forall POST i,
  FROM POST (w_j_inv i) -> FROM POST (w_r_inv i) -> FROM POST (w_x_inv i).
Proof.
  intros POST i HLJ HLR cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HXI.
  pose proof HXI as HXI0.
  destruct HXI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hl255 & x & Hx & Hx0 & R10)).
  pose proof HB as (HPRE & Hfrm & HGX & _).
  rewrite (lf_shape_eta fy LW_xret ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LW_xret) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_xret)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  assert (E10 : ew E 10 = w64 (index_of lf_tab x))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact R10).
  pose proof (w_index_of_range x) as Rix.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* taken: index_of <> 0, to the join *)
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LW_j; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    apply (HLJ cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    apply (w_c_move LW_xret LW_j _ (fun _ _ _ => True) i cx fy fp k2 ly3 S3 W3 ms3 md3 msB mdB HXI0 HJ
      (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
      (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs (fun _ _ _ => I)).
  - (* not taken: index_of = 0, to the refused block *)
    rewrite w_bne_any, E10 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LW_r; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
    apply (HLR cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    apply (w_c_move LW_xret LW_r _ (fun _ nm t => w_refused nm t) i cx fy fp k2 ly3 S3 W3 ms3 md3 msB mdB HXI0 HJ
      (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
      (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs).
    intros nm' t' (_ & x' & Hx' & _ & R10').
    right; right; right. intros y Hy. rewrite Hy in Hx'. injection Hx' as <-.
    rewrite R10 in R10'. apply (f_equal bv_unsigned) in R10'. unfold w64 in R10'.
    rewrite !unsigned_lit_small in R10' by (pose proof (w_index_of_range y); lia). lia.
Qed.

Definition w_l_inv := w_c LW_lret (fun ms nm t => (exists x, nm = Some x /\ x <> []) /\
  getr (ms_regs ms) 10 = w64 (Z.of_nat (length t))).

(* +0x10c4 `addi a1, zero, 0xff; bltu a1, a0, +0x10d8`, then `mv a0, s5; jal index_of` (0x838a4) *)
Lemma w_lx : forall POST i,
  FROM POST (w_r_inv i) -> FROM POST (w_x_inv i) -> FROM POST (w_l_inv i).
Proof.
  intros POST i HLR HLX cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HLI.
  pose proof HLI as HLI0.
  destruct HLI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & Ho0 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & ((x & Hx & Hx0) & R10)).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27 & R20 & R18 & R23 & RRNG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  pose proof HC as (_ & _ & _ & _ & _ & _ & HjbkC & _ & _).
  pose proof HjbkC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO3 & _).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (dec_rt_ok B LAWS TB HSEGS ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) 0 s6v t HAR3 HRO3
    ltac:(unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by (unfold LLVMF_STK in *; lia);
          unfold LLVMF_STK in *; lia) HD) as (_ & _ & Tlen & _).
  rewrite (lf_shape_eta fy LW_lret ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LW_lret) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_lret)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  assert (E10 : ew E 10 = w64 (Z.of_nat (length t)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl); exact R10).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  assert (Rlen : 0 <= Z.of_nat (length t) < 2 ^ 64) by lia.
  assert (U10 : forall (b : bool), branch_taken BC_LTU (sv_denot E (SLit 255)) (sv_denot E (SOff 10 0)) = b ->
    (255 <? Z.of_nat (length t)) = b).
  { intros b Hb. rewrite branch_ltu_U, U_lit, U_SOff, E10 in Hb by lia. unfold zcanon, M64, w64 in Hb.
    rewrite unsigned_lit_small, Z.add_0_r, Z.mod_small in Hb by lia. exact Hb. }
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* taken: 0xff < strlen, to the refused block *)
    apply U10, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LW_r; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (Fd : m_fds mdB = m_fds md3) by (subst mdB mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs mdB = m_fs md3) by (subst mdB mdA; rewrite !lf_wvb_fs; reflexivity).
    apply (HLR cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
    apply (w_c_move LW_lret LW_r _ (fun _ nm t => w_refused nm t) i cx fy fp k2 ly3 S3 W3 ms3 md3 msB mdB HLI0 HJ
      (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)
      (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
      (fun a H => eq_trans (KB a H) (KA a H)) (fun a H => HGB a (HGA a H)) Fd Fs).
    intros nm' t' (_ & R10'). right; right; left. unfold ALIAS_MAX.
    destruct (Z_lt_le_dec (Z.of_nat (length t')) (2 ^ 64)) as [Hlt | Hge]; [|lia].
    rewrite R10 in R10'. apply (f_equal bv_unsigned) in R10'. unfold w64 in R10'.
    rewrite !unsigned_lit_small in R10' by lia. lia.
  - (* not taken: strlen <= 0xff, mv a0, s5; jal index_of *)
    apply U10, Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_frame_nil _ _ _ HFrB) as KB0.
    assert (KB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)))
      by exact (fun a H => eq_trans (KB0 a H) (KA a H)).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
    assert (FdB : m_fds mdB = m_fds md3) by (subst mdB mdA; rewrite !lf_wvb_fds; reflexivity).
    assert (FsB : m_fs mdB = m_fs md3) by (subst mdB mdA; rewrite !lf_wvb_fs; reflexivity).
    pose proof (d4_keep_run fy W3 _ _ msB (ms_regs ms3) _ W_R3 HS EL W_R3_low ltac:(d4chk)) as KR.
    pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msB md3 mdB HC HJ KB
      (fun x Hx => HGB x (HGA x Hx)) FdB FsB) as HCB.
    pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as HcurB.
    pose proof (d4_dec_run B ly3 S3 _ _ s6v t KB HD) as HDB.
    pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KB (fun _ _ _ _ H => H)) as HTXB.
    pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msB) _ _ KB HSL) as HSLB.
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    ew_reg EL 21%nat (21%bv : bv 5) Q10. rewrite R21 in Q10. rewrite HBASE in Q1.
    pose proof HCB as (HJB & HfrB & _ & _ & _ & _ & HjbkB & HblkB & HdatB).
    pose proof HjbkB as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
    pose proof HdatB as (Dk & Dwf & Dtab & _).
    kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
    destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
    assert (Rsp : spZ (ms_regs msB) = lf_sp1 cx).
    { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
    assert (HK8 : 0 <= INDEX_OF_AK <= LLVMF_STK - 448) by (rewrite INDEX_OF_AK_val; unfold LLVMF_STK; lia).
    pose proof (w_name_range s nm Hnm) as Rs.
    assert (Ra0 : aarg (ms_regs msB) 0 = s) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; lia).
    rewrite Hx in Hnm.
    destruct (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
      cx fp ly3 S3 W3 (ms_mem msB) mdB k2 md mk kbs mbs gbs s x HB HJB HRO HdatB Hnm) as (Ncs & _ & Ns0 & _).
    destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
      cx fp ly3 S3 W3 (ms_mem msB) mdB k2 md mk T3 (ms_regs msB) INDEX_OF_AK HB HJB HblkB Rsp HK8)
      as (M1 & M2 & _).
    replace (pa_sigma LS_index_of) with INDEX_OF_A by (rewrite (lv_sigma LV); reflexivity).
    change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 INDEX_OF_A) (ms_mem msB) (seg_rom SEGS)) mdB)
      with (@cfg_at fy SEGS INDEX_OF_A (ms_regs msB) (ms_mem msB) mdB).
    eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
    + exact (INDEX_OF fy).
    + exact HB.
    + exact HJB.
    + exact HRO.
    + rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
    + rewrite K3, R3. exact Gp.
    + rewrite K4, R4. exact Tp.
    + exact Rsp.
    + exact HK8.
    + lia.
    + unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
    + apply Forall_nil.
    + intros a (r & [] & _).
    + intros a (r & [] & _).
    + intros a (u & Hu & Ha). rewrite Ra0 in Hu, Ha.
      pose proof (kp_acstr_unique _ _ _ _ _ Hu Ncs) as Eu. subst u.
      exact (lf_name_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msB) mdB k2 md mk kbs mbs gbs s x ly3 S3 _ _ a HB HJB HRO HdatB Hnm Ha).
    + exists kbs, lf_tab, x. rewrite Ra0.
      split; [exact Dk|]. split; [exact Dtab|]. split; [exact M1|]. split; [exact M2|].
      split; [lia|]. split; [exact Ncs|].
      split; [exact (lf_name_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msB) mdB k2 md mk kbs mbs gbs s x (ms_regs msB) INDEX_OF_AK HB HJB HRO HdatB Rsp HK8
        Hnm)|].
      intros i0 n2 ix p Hn Hp Rp.
      exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msB) mdB k2 md mk kbs mbs gbs (ms_regs msB) INDEX_OF_AK HB HJB HRO HdatB Rsp HK8
        i0 n2 ix p Hn Hp Rp)).
    + intros W2 ly2 S2 regs2 mem2 md2 Hle2 HJ2 HP2 HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2 Hpost.
      rewrite Z.add_0_r in HJ2.
      set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
      pose proof (Hpost kbs lf_tab x Dk Dtab ltac:(rewrite Ra0; exact Ncs)) as Hix. clear Hpost.
      destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
        cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly3 S3 W3 msB mdB INDEX_OF_AK
        (fun a => inFP (index_of_awr (ms_regs msB) (rdW W3 (ms_mem msB))) a) ly2 S2 W2 ms2 md2 _
        HB HJB HCB HK8 ltac:(intros a (r & [] & _)) HJ2
        ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2)
        as (HC2 & HRO2 & HCALL2).
      assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
        by (intros c Hc'; exact (Permutation_in _ (Permutation_sym HPERM2) Hc')).
      pose proof (lf_cur_callee B cx INDEX_OF_AK ly3 S3 ly2 S2 W3 msB W2 ms2 _ P N HCALL2
        (fun a _ H => match H with ex_intro _ r (conj Hr _) => Hr end) HcurB) as Hcur2.
      pose proof (tx_ans_keep B own1 nb ly3 S3 ly2 S2 _ _ _ s6v t HTXB Psub
        (lf_call_kagree B cx INDEX_OF_AK ly3 S3 ly2 S2 W3 (ms_mem msB) W2 (ms_mem ms2) _ HCALL2)
        (fun k a Hb Ha => lfx_blk B ly3 S3 ly2 S2 _ _ _ own1 k a Hb Ha
          (fun H => match H with ex_intro _ r (conj Hr _) => Hr end))) as HTX2.
      assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
      { apply (d4_slot_callee B cx INDEX_OF_AK ly3 S3 ly2 S2 W3 (ms_mem msB) W2 (ms_mem ms2) _ _ own1 HCALL2);
          [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLB].
        intros j Hj (r & [] & _). }
      pose proof (d4_keep_pres W_R3 _ _ W_R3_saved HP2) as KT.
      pose proof (d4_keep_trans W_R3 _ _ _ KR KT) as K2T.
      destruct (w_regs3_keep cx fp i s s6v o0 (Some x) t K0 ms3 ms2 K2T Hcore ltac:(rewrite <- Hx; exact Hreg))
        as (Hcore2 & Hreg2).
      apply (HLX cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx ltac:(pose proof HC2 as (HJx & _); exact HJx)
        ltac:(pose proof HC2 as (_ & Hfx2 & _); exact Hfx2)).
      exists md, mk, P, N, s, s6v, own1, o0, (Some x), t, K0, kbs, mbs, gbs, T3, nb.
      split; [exact Hi|].
      split.
      { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        rewrite Q1, <- HBASE. unfold LW_xret, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
      split; [exact Hcore2|]. split; [exact Hreg2|]. split; [exact Hnm|]. split; [exact Ho0|].
      split; [exact HC2|]. split; [exact Hcur2|]. split; [exact Hob|]. split; [rewrite <- Hx; exact Href|].
      split; [exact (tx_ans_dec B own1 nb ly2 S2 _ s6v t HTX2)|].
      split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
      split; [exact (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub Hfresh)|].
      split; [exact Hsr|].
      split; [lia|]. exists x. split; [reflexivity|]. split; [exact Hx0|]. exact Hix.
Qed.

Definition w_s_inv := w_c LW_sret (fun _ _ _ => True).

(* +0x1098 .. +0x109c: `mv s7, a0; jal check_socket` (0x83870), to its return +0x10a0 *)
Lemma w_as : forall POST i,
  FROM POST (w_s_inv i) -> FROM POST (w_a_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HAI.
  destruct HAI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & R20 & Ho0 & R18 & R10 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & RRNG).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  rewrite (lf_shape_eta fy LW_aret ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LW_aret) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_aret)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R4 HS EL W_R4_low ltac:(d4chk)) as KR.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  pose proof (d4_dec_run B ly3 S3 _ _ s6v t KA HD) as HDA.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H)) as HTXA.
  pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msA) _ _ KA HSL) as HSLA.
  clear HD HTX HSL Hcur.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23.
  ew_reg EL 10%nat (10%bv : bv 5) Q23. rewrite R10 in Q23. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & _ & _ & _ & _ & HjbkA & _ & HdatA).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HdatA as (Dk & _ & _ & Dop & Dmis & Doc & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  replace (pa_sigma LS_check_socket) with CHECK_SOCKET_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 CHECK_SOCKET_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS CHECK_SOCKET_A (ms_regs msA) (ms_mem msA) mdA).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_SOCKET_A
    CHECK_SOCKET_AK 0 [] (check_socket_apre SEGS) (fun _ _ _ => False) check_socket_awr check_socket_apost
    (proj2 (aleaf_rd_none (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B CHECK_SOCKET_A CHECK_SOCKET_AK 0 []
      (check_socket_apre SEGS) check_socket_awr check_socket_apost) (CSOCK fy))
    cx fp ly3 S3 W3 (ms_mem msA) mdA _ (ms_regs msA) (POST cx) HB HJA HRO);
    [ rewrite Q1, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
    | unfold raZ; rewrite Q1; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
    | rewrite K3, R3; exact Gp
    | rewrite K4, R4; exact Tp
    | exact Rsp
    | unfold CHECK_SOCKET_AK, CHECK_SOCKET_AFRAME, LLVMF_STK; lia
    | lia
    | unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
    | apply Forall_nil
    | intros a (r & [] & _)
    | intros a (r & [] & _)
    | intros a []
    | exists kbs; split; [exact Dk|]; split; [exact Dop|]; split; [exact Doc | exact Dmis]
    | ].
  intros W2 ly2 S2 regs2 mem2 md2 Hle2 HJ2 HP2 HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2 _.
  rewrite Z.add_0_r in HJ2.
  set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly3 S3 W3 msA mdA CHECK_SOCKET_AK
    (fun a => inFP (check_socket_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) ly2 S2 W2 ms2 md2 _
    HB HJA HCA ltac:(unfold CHECK_SOCKET_AK, CHECK_SOCKET_AFRAME, LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ2
    ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2)
    as (HC2 & HRO2 & HCALL2).
  assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in _ (Permutation_sym HPERM2) Hc)).
  pose proof (lf_cur_callee B cx CHECK_SOCKET_AK ly3 S3 ly2 S2 W3 msA W2 ms2 _ P N HCALL2
    (fun a _ H => match H with ex_intro _ r (conj Hr _) => Hr end) HcurA) as Hcur2.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly2 S2 _ _ _ s6v t HTXA Psub
    (lf_call_kagree B cx CHECK_SOCKET_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ HCALL2)
    (fun k a Hb Ha => lfx_blk B ly3 S3 ly2 S2 _ _ _ own1 k a Hb Ha (fun H => match H with ex_intro _ r (conj Hr _) => Hr end)))
    as HTX2.
  assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
  { apply (d4_slot_callee B cx CHECK_SOCKET_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ _ own1 HCALL2);
      [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLA].
    intros j Hj (r & [] & _). }
  pose proof (d4_keep_pres W_R4 _ _ W_R4_saved HP2) as KT.
  pose proof (d4_keep_trans W_R4 _ _ _ KR KT) as K2T.
  pose proof (ar_pres _ _ HP2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P23 & _).
  apply (HL cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx ltac:(pose proof HC2 as (HJx & _); exact HJx)
    ltac:(pose proof HC2 as (_ & Hfx2 & _); exact Hfx2)).
  exists md, mk, P, N, s, s6v, own1, o0, nm, t, K0, kbs, mbs, gbs, T3, nb.
  split; [exact Hi|].
  split.
  { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite Q1, <- HBASE. unfold LW_sret, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
  kreg K2T 2 (2%bv : bv 5) Z2. kreg K2T 3 (3%bv : bv 5) Z3. kreg K2T 4 (4%bv : bv 5) Z4. kreg K2T 8 (8%bv : bv 5) Z8.
  kreg K2T 9 (9%bv : bv 5) Z9. kreg K2T 19 (19%bv : bv 5) Z19. kreg K2T 20 (20%bv : bv 5) Z20.
  kreg K2T 21 (21%bv : bv 5) Z21. kreg K2T 22 (22%bv : bv 5) Z22. kreg K2T 24 (24%bv : bv 5) Z24.
  kreg K2T 25 (25%bv : bv 5) Z25. kreg K2T 26 (26%bv : bv 5) Z26. kreg K2T 27 (27%bv : bv 5) Z27.
  kreg K2T 18 (18%bv : bv 5) Z18.
  split; [unfold lf_core; cbn [ms_regs ms2 mkst]; rewrite Z2, Z8, Z9, Z3, Z4; repeat split; assumption|].
  split; [unfold w_regs3; cbn [ms_regs ms2 mkst]; rewrite Z19, Z21, Z22, Z24, Z25, Z26, Z27, Z20, Z18, P23, Q23;
          repeat split; first [assumption | lia]|].
  split; [exact Hnm|]. split; [exact Ho0|].
  split; [exact HC2|]. split; [exact Hcur2|]. split; [exact Hob|]. split; [exact Href|].
  split; [exact (tx_ans_dec B own1 nb ly2 S2 _ s6v t HTX2)|].
  split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
  split; [exact (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub Hfresh)|].
  split; [exact Hsr | exact I].
Qed.

End a.
