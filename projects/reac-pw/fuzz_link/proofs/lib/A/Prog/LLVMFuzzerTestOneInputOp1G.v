(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 496 of its 545 lines of code are new or changed and 1283 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write from the join (+0x10e8) to the loop tail (+0x1110):
     +0x10e8  mv a0, s7; mv a1, s2; jal check_write (0x838c4)              w_jq (w_j_inv to w_q_inv)
     +0x10f4  ld s6, 0xe8(s1); mv a0, s6; jal check_requests (0x838d0)
     +0x1100  ld a0, 0x130(s1); jal wrapper_free (0x838d8)
     +0x1108  ld s7, 0xf0(s1); ld s5, 0x98(s1)                           w_qt (w_q_inv to lf_tail_inv)
   check_write's Pre is link_spec's same_rc of the library's and the model's codes (write_model = norm_rc of
   write_lib, the library's code a 32-bit number); check_requests' Pre is Op3Lib.v u_requests_are of the two
   request lists being one list; the free is Txa.v lf_free_tx_step (the allocator's afree04 rules, W1).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c model_write_c index_of_c reac_link_alias_write_c nl_talk_c check_socket_c check_refused_c check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1E.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkStrS YC88.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LW_q : Z := AF_LLVMFuzzerTestOneInput + 0x10f4.   (* 0x838c8, check_write's return *)

(* check_write's Pre: the harness compares the library's code with the model's (norm_rc of it) *)
Lemma w_same_rc : forall rc, - 2 ^ 31 <= rc < 2 ^ 31 ->
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

(* the registers of the stretch after check_write: s6 is reloaded at +0x10f4, s5 and s7 at +0x1108 *)
Definition W_R5 : list Z := [2; 3; 4; 8; 9; 19; 24; 25; 26; 27].
Definition W_R6 : list Z := [2; 3; 4; 8; 9; 19; 22; 24; 25; 26; 27].
Lemma W_R5_low : forall r, In r W_R5 -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.
Lemma W_R6_low : forall r, In r W_R6 -> Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r).
Proof. intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. Qed.
Lemma W_R6_saved : forall r, In r W_R6 -> acallee_saved r.
Proof. intros r Hr. unfold acallee_saved. cbn in Hr. lia. Qed.

(* +0x1108's state: the slots [s1 + 0xf0] (g_nl + 0x40000, atom 32) and [s1 + 0x98] (m + MD_N_MARK, atom 33) *)
Definition w_slot33 (off : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 33 0))].
Definition w_t_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition w_t_ss (pc : Z) : sstate := mkSS pc sr_atoms [d4_slot LS_GNL40; w_slot33 LS_NMARK] None w_t_facts.

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
(* check_requests, as proved (check_requests_c.v) *)
Hypothesis CREQ : forall fy : YK11.FPState, @check_requests_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
(* the allocator's free rules and the free sites' traces (Free.v, open item W1) *)
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.
(* check_write, as proved (check_write_c.v) *)
Hypothesis CWRITE : forall fy : YK11.FPState, @check_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Definition w_q_inv := w_c SK B MT MS la_nul LF_MO_SET LF_MO_OP LW_q (fun _ _ _ => True).

Lemma w_jq : forall POST i,
  FROM POST (w_q_inv i) -> FROM POST (w_j_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HJI.
  destruct HJI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & Ho0 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & _).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27 & R20 & R18 & R23 & RRNG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  rewrite (lf_shape_eta fy LW_j ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LW_j) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_j)) (ms_mem ms3) (seg_rom SEGS)))))
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
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  pose proof (d4_dec_run B ly3 S3 _ _ s6v t KA HD) as HDA.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H)) as HTXA.
  pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msA) _ _ KA HSL) as HSLA.
  clear HD HTX HSL Hcur.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  ew_reg EL 23%nat (23%bv : bv 5) Q10. ew_reg EL 18%nat (18%bv : bv 5) Q11.
  rewrite R23 in Q10. rewrite R18 in Q11. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & _ & _ & _ & _ & HjbkA & _ & _).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  replace (pa_sigma LS_check_write) with CHECK_WRITE_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 CHECK_WRITE_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS CHECK_WRITE_A (ms_regs msA) (ms_mem msA) mdA).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_WRITE_A
    CHECK_RC_AK 0 [] check_rc_apre (fun _ _ _ => False) check_rc_awr check_rc_apost
    (proj2 (aleaf_rd_none (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B CHECK_WRITE_A CHECK_RC_AK 0 []
      check_rc_apre check_rc_awr check_rc_apost) (CWRITE fy))
    cx fp ly3 S3 W3 (ms_mem msA) mdA _ (ms_regs msA) (POST cx) HB HJA HRO);
    [ rewrite Q1, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
    | unfold raZ; rewrite Q1; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
    | rewrite K3, R3; exact Gp
    | rewrite K4, R4; exact Tp
    | exact Rsp
    | unfold CHECK_RC_AK, CHECK_RC_AFRAME, LLVMF_STK; lia
    | lia
    | unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
    | apply Forall_nil
    | intros a (r & [] & _)
    | intros a (r & [] & _)
    | intros a []
    | | ].
  { unfold check_rc_apre, same_rc_aregs. rewrite Q10, Q11.
    unfold write_model, write_lib in *. cbn [w_rc] in *. exact (w_same_rc _ RRNG). }
  intros W2 ly2 S2 regs2 mem2 md2 Hle2 HJ2 HP2 HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2 _.
  rewrite Z.add_0_r in HJ2.
  set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly3 S3 W3 msA mdA CHECK_RC_AK
    (fun a => inFP (check_rc_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) ly2 S2 W2 ms2 md2 _
    HB HJA HCA ltac:(unfold CHECK_RC_AK, CHECK_RC_AFRAME, LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ2
    ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2)
    as (HC2 & HRO2 & HCALL2).
  assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; exact (Permutation_in _ (Permutation_sym HPERM2) Hc)).
  pose proof (lf_cur_callee B cx CHECK_RC_AK ly3 S3 ly2 S2 W3 msA W2 ms2 _ P N HCALL2
    (fun a _ H => match H with ex_intro _ r (conj Hr _) => Hr end) HcurA) as Hcur2.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly2 S2 _ _ _ s6v t HTXA Psub
    (lf_call_kagree B cx CHECK_RC_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ HCALL2)
    (fun k a Hb Ha => lfx_blk B ly3 S3 ly2 S2 _ _ _ own1 k a Hb Ha (fun H => match H with ex_intro _ r (conj Hr _) => Hr end)))
    as HTX2.
  assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
  { apply (d4_slot_callee B cx CHECK_RC_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ _ own1 HCALL2);
      [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLA].
    intros j Hj (r & [] & _). }
  pose proof (d4_keep_pres W_R3 _ _ W_R3_saved HP2) as KT.
  pose proof (d4_keep_trans W_R3 _ _ _ KR KT) as K2T.
  destruct (w_regs3_keep XM_LIB XN_LIB la_nul cx fp i s s6v o0 nm t K0 ms3 ms2 K2T Hcore Hreg) as (Hcore2 & Hreg2).
  apply (HL cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx ltac:(pose proof HC2 as (HJx & _); exact HJx)
    ltac:(pose proof HC2 as (_ & Hfx2 & _); exact Hfx2)).
  exists md, mk, P, N, s, s6v, own1, o0, nm, t, K0, kbs, mbs, gbs, T3, nb.
  split; [exact Hi|].
  split.
  { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite Q1, <- HBASE. unfold LW_q, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
  split; [exact Hcore2|]. split; [exact Hreg2|]. split; [exact Hnm|]. split; [exact Ho0|].
  split; [exact HC2|]. split; [exact Hcur2|]. split; [exact Hob|]. split; [exact Href|].
  split; [exact (tx_ans_dec B own1 nb ly2 S2 _ s6v t HTX2)|].
  split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
  split; [exact (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub Hfresh)|].
  split; [exact Hsr | exact I].
Qed.

Lemma w_t_entry : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem pc v32 v33,
  2 ^ 46 <= bv_unsigned (getr regs 9) <= 2 ^ 47 -> bv_unsigned (getr regs 9) mod 32 = 0 ->
  0 <= v32 < 2 ^ 64 -> 0 <= v33 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + LS_GNL40) 8 v32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 9) + LS_NMARK) 8 v33 ->
  st_ok_pi (fx := fy) SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 v32; Z_to_bv 64 v33])) (w_t_ss pc)
    (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fy W regs mem pc v32 v33 H9 H32 Hv32 Hv33 Hm32 Hm33.
  set (E := Eimg (Ereg regs [Z_to_bv 64 v32; Z_to_bv 64 v33])).
  assert (E9 : ew E 9 = getr regs 9)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 v32)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 v33)
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  rewrite restrict_mkst_fx. unfold w_t_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok.
    + unfold d4_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E. rewrite E9. unfold LS_GNL40. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0xf0 8 (SOff 32 0) v32);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
      exact Hm32.
    + unfold w_slot33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E. rewrite E9. unfold LS_NMARK. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (bv_unsigned (getr regs 9)) 0x98 8 (SOff 33 0) v33);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
      exact Hm33.
  - apply pairwise_disjoint_of_extents.
    unfold d4_slot, w_slot33, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. fold E. rewrite E9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LS_GNL40, LS_NMARK.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; [exact I | exact I]].
    cbn [w_t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E9, E32, E33. rewrite !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Lemma w_qt : forall POST i,
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (w_q_inv i).
Proof.
  intros POST i HT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HQI.
  destruct HQI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & Ho0 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & _).
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
  pose proof HC as (_ & _ & _ & _ & _ & Hsl & _ & HblkC & _).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSM & HSG & _).
  pose proof HblkC as (BmdC & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR BmdC) as (_ & Bm4096 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (HU9 : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx)
    by (rewrite R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HSM) as Rmd.
  (* ---- +0x10f4 .. +0x10fc: s6 := [s1 + 0xe8] = m, a0 := s6, jal check_requests ---- *)
  rewrite (lf_shape_eta fy LW_q ms3 Hsh).
  pose proof (d4_entry_l fy W3 (ms_regs ms3) (ms_mem ms3) LW_q LS_M md ltac:(rewrite HU9; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU9; exact Hs32) ltac:(unfold LS_M; lia) Rmd ltac:(vm_compute; reflexivity)
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HSM))) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md]))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_q)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md]))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 md]) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 md)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R5 HS EL W_R5_low ltac:(d4chk)) as KRA.
  assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
    lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H)) as HTXA.
  pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msA) _ _ KA HSL) as HSLA.
  clear HTX HSL Hcur HD.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (22%bv : bv 5) Q22.
  try rewrite E32 in Q10. try rewrite E32 in Q22. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & _ & _ & _ & _ & HjbkA & HblkA & HdatA).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJA as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  pose proof HblkA as (BmdA & BmkA & _).
  pose proof HdatA as (Dk & Dwf & _ & _ & _ & _ & Dmd & Dmwf & _).
  pose proof Dk as (_ & KL). pose proof Dmd as (_ & ML).
  kreg KRA 2 (2%bv : bv 5) K2. kreg KRA 3 (3%bv : bv 5) K3. kreg KRA 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HKr : CHECK_REQUESTS_AK = 8272) by reflexivity.
  assert (Ha0 : aarg (ms_regs msA) 0 = md) by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; lia).
  destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
    cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk T3 (ms_regs msA) CHECK_REQUESTS_AK HB HJA HblkA Rsp
    ltac:(rewrite HKr; unfold LLVMF_STK; lia)) as (_ & _ & M3 & M4 & M5 & _ & _ & M8 & M9).
  replace (pa_sigma LS_check_requests) with CHECK_REQUESTS_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 CHECK_REQUESTS_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS CHECK_REQUESTS_A (ms_regs msA) (ms_mem msA) mdA).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_REQUESTS_A
    CHECK_REQUESTS_AK 0 [] _ _ _ _ (CREQ fy) cx fp ly3 S3 W3 (ms_mem msA) mdA k2 (ms_regs msA) (POST cx) HB HJA HRO).
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite K3, R3. exact Gp.
  - rewrite K4, R4. exact Tp.
  - exact Rsp.
  - rewrite HKr. unfold LLVMF_STK. lia.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia.
  - apply (ar_side_room S3 fp _ HfrA). vm_compute. reflexivity.
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a Ha. unfold check_requests_ard, rd_ivl in Ha. rewrite Ha0 in Ha. right; left. exists md, MD_SIZE.
    split; [exact BmdA|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in Ha. lia.
  - unfold check_requests_apre. exists kbs, mbs. rewrite Ha0.
    destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem msA) mdA HARA) as (Gra & Ghv).
    split; [exact Dk|]. split; [exact Dmd|]. split; [exact Dwf|]. split; [exact Dmwf|].
    split; [exact (u_requests_are kbs mbs KL ML Dwf Dmwf Hsr)|].
    split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact Gra|]. split; [exact Ghv|].
    split; [exact M9 | exact M8].
  - intros W2 ly2 S2 regs2 mem2 md2 Hle2 HJ2 HP2 HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2 _.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
      cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly3 S3 W3 msA mdA CHECK_REQUESTS_AK
      (fun a => inFP (check_requests_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) ly2 S2 W2 ms2 md2 _
      HB HJA HCA ltac:(rewrite HKr; unfold LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ2
      ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR2 HFD2 HFS2 HKP2 HSK2 HS2 HPERM2)
      as (HC2 & HRO2 & HCALL2).
    assert (Psub2 : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
      by (intros c Hc; exact (Permutation_in _ (Permutation_sym HPERM2) Hc)).
    pose proof (lf_cur_callee B cx CHECK_REQUESTS_AK ly3 S3 ly2 S2 W3 msA W2 ms2 _ P N HCALL2
      (fun a _ H => match H with ex_intro _ r (conj Hr _) => Hr end) HcurA) as Hcur2.
    assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
    { apply (d4_slot_callee B cx CHECK_REQUESTS_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) _ _ own1 HCALL2);
        [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLA].
      intros j Hj (r & [] & _). }
    pose proof (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub2 Hfresh) as Hfresh2.
    pose proof (d4_keep_pres W_R6 _ _ W_R6_saved HP2) as KT2.
    pose proof HC2 as (HJ2c & _).
    (* ---- +0x1100 .. +0x1104: a0 := [s1 + 0x130], jal wrapper_free ---- *)
    assert (HPC2 : getr (ms_regs msA) 1 = Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x1100)))
      by (rewrite Q1, HBASE; reflexivity).
    unfold ms2. rewrite HPC2.
    kreg KT2 9 (9%bv : bv 5) T9. kreg KRA 9 (9%bv : bv 5) A9.
    assert (HU92 : bv_unsigned (getr regs2 9) = lf_sp1 cx)
      by (rewrite T9, A9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W2) mem2) HSL2) as Rown1.
    clear HS SHOK.
    pose proof (d4_entry_l fy W2 regs2 mem2 (AF_LLVMFuzzerTestOneInput + 0x1100) LS_T130 own1
      ltac:(rewrite HU92; unfold LLVMF_STK in *; lia) ltac:(rewrite HU92; exact Hs32) ltac:(unfold LS_T130; lia) Rown1
      ltac:(vm_compute; reflexivity) ltac:(rewrite HU92; exact (val_mem_of_rdword SEGS (w_H W2) mem2 _ _ HSL2))) as HS.
    assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs2 [Z_to_bv 64 own1]))
      (mrestrict (w_H W2) (ms_mem (@mkst fy regs2 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x1100))) mem2
        (seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
    assert (HEI2 : img_env pa_val A_LIM (Eimg (Ereg regs2 [Z_to_bv 64 own1]))) by apply Eimg_env.
    remember (Eimg (Ereg regs2 [Z_to_bv 64 own1])) as E2 eqn:HEdef.
    assert (EL2 : forall n, (n < A_TEXT)%nat -> ew E2 n = ew (Ereg regs2 [Z_to_bv 64 own1]) n)
      by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
    assert (E232 : ew E2 32 = Z_to_bv 64 own1)
      by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
    clear HEdef.
    paj_run_tok RUN HS HJ2 SHOK (0, 0);
      [apply awr_ok_x_cons; [cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                            | apply awr_ok_x_nil] |].
    rename ms into msF, HF into HFF, HFr into HFrF, HG into HGF.
    pose proof (d4_keep_run fy W2 _ _ msF regs2 _ W_R6 HS EL2 W_R6_low ltac:(d4chk)) as KRF.
    assert (KF : kagree SEGS (fun _ => False) (rdW W2 mem2) (rdW W2 (ms_mem msF))).
    { intros a _. unfold mbyte. rewrite (HFrF (Z_to_bv 64 a)); [reflexivity|].
      intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
      lia. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
    assert (FdF : m_fds mdF = m_fds md2) by (subst mdF; rewrite !lf_wvb_fds; reflexivity).
    assert (FsF : m_fs mdF = m_fs md2) by (subst mdF; rewrite !lf_wvb_fs; reflexivity).
    pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly2 S2 W2 ms2 msF md2 mdF
      HC2 HJ2 KF (fun x Hx => HGF x Hx) FdF FsF) as HCF.
    pose proof (lf_cur_keep (fun _ => False) cx W2 ms2 W2 msF P N KF (fun a _ H => H) Hcur2) as HcurF.
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1F. prreg HS (10%bv : bv 5) Q10F.
    try rewrite E232 in Q10F. rewrite HBASE in Q1F.
    pose proof (d4_keep_trans W_R6 _ _ _ KT2 KRF) as KAF.
    kreg KAF 2 (2%bv : bv 5) F2. kreg KAF 3 (3%bv : bv 5) F3. kreg KAF 4 (4%bv : bv 5) F4. kreg KAF 8 (8%bv : bv 5) F8.
    kreg KRA 8 (8%bv : bv 5) A8.
    rewrite K2, R2 in F2. rewrite K3 in F3. rewrite K4 in F4. rewrite A8, R8 in F8.
    apply (lf_free_tx_step SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE LV MT_OK
      AFREE4W AFREENULL4W LF_TRACE_FREE fy cx fp md mk kbs mbs gbs T3 [] nb [(md, MD_SIZE); (mk, MK_SIZE)] own1 _ _ _ _ _
      ly2 S2 W2 msF mdF (ms_regs msF) 5904 (lf_mo LF_MO_SET LF_MO_OP i) (POST cx) HB HCF Hnb
      (fun b Hb => proj1 Hfresh2 b Hb)).
    { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia. }
    { exact Q10F. }
    { unfold spZ. rewrite F2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
    { unfold s0Z. rewrite F8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
    { rewrite F3. exact R3. }
    { rewrite F4. exact R4. }
    { exact Q1F. }
    { unfold LF_FREE_RAS, link_text. right; right; right; right; left. reflexivity. }
    intros W9 ly9 S9 regs9 mem9 md9 Hle9 HP9 HC9 HRO9 (E9 & HCALL9 & HE9) Hsub9.
    set (ms9 := @mkst fy regs9 (getr (ms_regs msF) 1) mem9 (seg_rom SEGS)).
    pose proof (d4_keep_pres W_R6 _ _ W_R6_saved HP9) as KT9.
    pose proof (d4_keep_trans W_R6 _ _ _ KAF KT9) as KA9.
    pose proof (lf_cur_callee B cx ASTACK ly2 S2 ly9 S9 W2 msF W9 ms9 E9 P N HCALL9
      (fun a Ha HEa => ltac:(pose proof (HE9 a HEa); unfold lf_cur_fp in Ha; unfold LS_P, LS_N, LLVMF_STK in *; lia))
      HcurF) as Hcur9.
    pose proof HC9 as (HJ9 & _ & _ & _ & _ & HSL9 & _ & _ & _).
    pose proof HSL9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSG9 & _). pose proof HSL9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNM9 & _).
    (* ---- +0x1108 .. +0x110c: s7 := [s1 + 0xf0], s5 := [s1 + 0x98]; +0x1110 the loop tail ---- *)
    assert (HPC9 : getr (ms_regs msF) 1 = Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x1108)))
      by (rewrite Q1F, HBASE; reflexivity).
    unfold ms9. rewrite HPC9.
    kreg KA9 9 (9%bv : bv 5) T99.
    assert (HU99 : bv_unsigned (getr regs9 9) = lf_sp1 cx)
      by (rewrite T99, A9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W9) mem9) HSG9) as Rg.
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W9) mem9) HNM9) as Rn.
    clear HS SHOK.
    pose proof (w_t_entry fy W9 regs9 mem9 (AF_LLVMFuzzerTestOneInput + 0x1108) (LA_G_NL + 0x40000) (md + MD_N_MARK)
      ltac:(rewrite HU99; unfold LLVMF_STK in *; lia) ltac:(rewrite HU99; exact Hs32) Rg Rn
      ltac:(rewrite HU99; exact (val_mem_of_rdword SEGS (w_H W9) mem9 _ _ HSG9))
      ltac:(rewrite HU99; exact (val_mem_of_rdword SEGS (w_H W9) mem9 _ _ HNM9))) as HS.
    assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs9 [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (md + MD_N_MARK)]))
      (mrestrict (w_H W9) (ms_mem (@mkst fy regs9 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x1108))) mem9
        (seg_rom SEGS))))) by (unfold sh_ok; apply Forall_nil).
    assert (HEI9 : img_env pa_val A_LIM (Eimg (Ereg regs9 [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (md + MD_N_MARK)])))
      by apply Eimg_env.
    remember (Eimg (Ereg regs9 [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (md + MD_N_MARK)])) as E9x eqn:HEdef.
    assert (EL9 : forall n, (n < A_TEXT)%nat ->
      ew E9x n = ew (Ereg regs9 [Z_to_bv 64 (LA_G_NL + 0x40000); Z_to_bv 64 (md + MD_N_MARK)]) n)
      by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
    assert (E932 : ew E9x 32 = Z_to_bv 64 (LA_G_NL + 0x40000))
      by (rewrite EL9 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs9 _ 0)).
    assert (E933 : ew E9x 33 = Z_to_bv 64 (md + MD_N_MARK))
      by (rewrite EL9 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs9 _ 1)).
    clear HEdef.
    paj_run_to_tok RUNTO HS HJ9 SHOK (0, 0) LF_tail;
      [apply awr_ok_x_cons; [cbn [w_t_ss d4_slot w_slot33 ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
       apply awr_ok_x_cons; [cbn [w_t_ss d4_slot w_slot33 ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia|];
       apply awr_ok_x_nil |].
    rename ms into msZ, HF into HFZ, HFr into HFrZ, HG into HGZ.
    pose proof (d4_keep_run_pi fy W9 _ _ msZ regs9 _ W_R6 HS EL9 W_R6_low ltac:(d4chk)) as KRZ.
    assert (KZ : kagree SEGS (fun _ => False) (rdW W9 mem9) (rdW W9 (ms_mem msZ))).
    { intros a _. unfold mbyte. rewrite (HFrZ (Z_to_bv 64 a)); [reflexivity|].
      intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
        cbn [w_t_ss d4_slot w_slot33 ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdZ := mdx) in * end.
    assert (FdZ : m_fds mdZ = m_fds md9) by (subst mdZ; rewrite !lf_wvb_fds; reflexivity).
    assert (FsZ : m_fs mdZ = m_fs md9) by (subst mdZ; rewrite !lf_wvb_fs; reflexivity).
    pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly9 S9 W9 ms9 msZ md9 mdZ
      HC9 HJ9 KZ (fun x Hx => HGZ x Hx) FdZ FsZ) as HCZ.
    pose proof (lf_cur_keep (fun _ => False) cx W9 ms9 W9 msZ P N KZ (fun a _ H => H) Hcur9) as HcurZ.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssZ := ssx) in HS end.
    assert (Q21 : getr (ms_regs msZ) 21 = Z_to_bv 64 (md + MD_N_MARK)).
    { rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W9) E9x ssZ msZ 21%bv HS).
      replace (sr_get (ss_regs ssZ) 21%bv) with (SOff 33 0) by (vm_compute; reflexivity).
      cbn [sv_denot]. rewrite E933, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    assert (Q23 : getr (ms_regs msZ) 23 = Z_to_bv 64 (LA_G_NL + 0x40000)).
    { rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W9) E9x ssZ msZ 23%bv HS).
      replace (sr_get (ss_regs ssZ) 23%bv) with (SOff 32 0) by (vm_compute; reflexivity).
      cbn [sv_denot]. rewrite E932, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    (* ---- the cut at LF_tail ---- *)
    pose proof HCZ as (_ & _ & _ & _ & _ & _ & HJBKZ & _).
    pose proof HJBKZ as (HkZ & _ & _ & _ & _ & _ & _ & HwlZ & _ & _ & HblZ & _).
    destruct (proj2 Hfresh) as (ly0 & S0 & Hbl0 & Hbb0).
    pose proof (ak_cut_counters SK B MT MS la_nul MT_LE cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly9 S9 W9 msZ mdZ
      (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD HCZ) as HCZ'.
    specialize (HCZ' ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia)
      ltac:(rewrite (lf_bl_bytes_eq B cx _ T3 ly0 S0 ly9 S9 Hbl0 HblZ); exact Hbb0)
      ltac:(unfold lf_wl, LF_WILD_OP in *; rewrite Z2Nat.inj_add by lia; cbn [Z.to_nat Pos.to_nat]; lia)).
    clear HCZ.
    destruct HCZ' as (HJZ & HFRZ & HSAVZ & HHDRZ & HFSHZ & HSLZ & HJBKZ' & HBLKZ & HDATAZ).
    pose proof (d4_keep_trans W_R6 _ _ _ KA9 KRZ) as KAZ.
    kreg KAZ 2 (2%bv : bv 5) Z2. kreg KAZ 3 (3%bv : bv 5) Z3. kreg KAZ 4 (4%bv : bv 5) Z4.
    kreg KAZ 8 (8%bv : bv 5) Z8. kreg KAZ 9 (9%bv : bv 5) Z9. kreg KAZ 19 (19%bv : bv 5) Z19.
    kreg KAZ 22 (22%bv : bv 5) Z22. kreg KAZ 24 (24%bv : bv 5) Z24. kreg KAZ 25 (25%bv : bv 5) Z25.
    kreg KAZ 26 (26%bv : bv 5) Z26. kreg KAZ 27 (27%bv : bv 5) Z27.
    kreg KRA 19 (19%bv : bv 5) A19. kreg KRA 24 (24%bv : bv 5) A24. kreg KRA 25 (25%bv : bv 5) A25.
    kreg KRA 26 (26%bv : bv 5) A26. kreg KRA 27 (27%bv : bv 5) A27.
    apply (HT cx fy fp (k2 + 1) ly9 S9 W9 msZ mdZ HB Hfx HJZ HFRZ).
    exists md, mk, P, N, kbs, mbs, gbs, T3.
    split; [exact Hi|].
    split; [exact (lf_shape_of_st_ok fy W9 _ _ msZ HS eq_refl)|].
    split; [split; [rewrite Z2, K2; exact R2|]; split; [rewrite Z8, A8; exact R8|]; split; [rewrite Z9, A9; exact R9|];
            split; [rewrite Z3, K3; exact R3 | rewrite Z4, K4; exact R4]|].
    split; [split; [rewrite Z19, A19; exact R19|]; split; [rewrite Q21; reflexivity|];
            split; [rewrite Z22, Q22; reflexivity|]; split; [rewrite Q23; reflexivity|];
            split; [rewrite Z24, A24; exact R24|]; split; [rewrite Z25, A25; exact R25|];
            split; [rewrite Z26, A26; exact R26 | rewrite Z27, A27; exact R27]|].
    split; [exact HSAVZ|]. split; [exact HHDRZ|]. split; [exact HFSHZ|]. split; [exact HSLZ|].
    split; [exact HcurZ|].
    split; [exact HJBKZ'|]. split; [exact HBLKZ|]. split; [exact HDATAZ|].
    lia.
Qed.

End a.
