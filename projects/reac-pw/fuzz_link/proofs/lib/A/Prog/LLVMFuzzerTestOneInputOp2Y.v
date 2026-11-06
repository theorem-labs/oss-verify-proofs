(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 657 of its 712 lines of code are new or changed and 1277 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm
   after mark_quietly returns (+0xcac, listing (internal path)
   (internal record, sha256 e84d6f0c6974)): `mv s2, a0; jal check_socket` (0x83484), `mv a0, s2; mv a1, s7; jal
   check_mark` (0x83490), `mv a0, s5; mv a1, s6; jal check_marks` (0x8349c), `mv a0, s6; jal check_requests`
   (0x834a4), `j +0x1108`, `ld s7, 0xf0(s1)`, `ld s5, 0x98(s1)`, +0x1110 = LF_tail.
   `o2_y_inv pc r`: the cut at each of those pcs, the library's code in register r (a0 at +0xcac, s2 after), the
   model's in s7, same_rc of the two (Op2Lib.v o2_agree); `o2y_exit`: +0xcac to LF_tail.
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
  LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputMqPost LLVMFuzzerTestOneInputOp3U
  LLVMFuzzerTestOneInputOp3X LLVMFuzzerTestOneInputOp5C LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2V.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_all_c reac_served_mark_c
  mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh remember_c
  check_socket_c check_marks_c check_requests_c check_mark_c check_write_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.

(* the kstate words the library's codes are bounded by *)
Definition o2_kb3 (K : kstate) : Prop :=
  0 <= k_sock K < 2 ^ 31 /\ 0 <= k_send K < 2 ^ 31 /\ 0 <= k_end K < 2 ^ 31.

Lemma o2_talk_after_k : forall K, o2_kb3 K -> o2_kb3 (talk_after K).
Proof.
  intros K (H1 & H2 & H3). unfold o2_kb3, talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn; lia|].
  destruct (negb (k_send K =? 0)); [cbn; lia|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; cbn; lia.
Qed.

Lemma o2_rstate_k : forall tab nm kc ac reqs K, o2_kb3 K -> o2_kb3 (r_state (read_core tab nm kc ac reqs K)).
Proof.
  intros tab nm kc ac reqs K HK. unfold read_core. destruct nm as [s|]; [|exact HK].
  destruct (Nat.eqb (length s) 0); [exact HK|]. cbv zeta.
  destruct (index_of tab s =? 0); [exact HK|]. cbn [r_state]. exact (o2_talk_after_k K HK).
Qed.

(* the library's code of a mark *)
Lemma o2_lib_rc_range : forall tab nm marks reqs K, o2_kb3 K ->
  - 2 ^ 32 < m_rc (mark_lib tab nm marks reqs K) < 2 ^ 32.
Proof.
  intros tab nm marks reqs K HK. pose proof HK as (H1 & H2 & H3).
  assert (EI : E_INVAL = 22) by reflexivity.
  unfold mark_lib, mark_core. destruct nm as [s|]; [|cbn [m_rc]; lia].
  destruct (Nat.eqb (length s) 0); [cbn [m_rc]; lia|]. cbv zeta.
  pose proof (o2_rstate_k tab (Some s) KIND_CAP ALIAS_MAX reqs K HK) as (R1 & R2 & R3).
  pose proof (u_read_rc_range tab (Some s) KIND_CAP ALIAS_MAX reqs K H1 H2 H3) as RR.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [m_rc];
    first [ lia
          | (apply o2_write_rc_range; assumption)
          | (match goal with |- context [decide ?k ?a] => pose proof (o2_decide_range k a); lia end) ].
Qed.

(* check_mark's Pre from the two codes in a0 and a1 *)
Lemma o2_same_w : forall got want, - 2 ^ 63 <= got < 2 ^ 63 -> same_rc got want = true ->
  (w64 want = w64 RC_FAILS -> w64 got <> w64 0) /\ (w64 want <> w64 RC_FAILS -> w64 got = w64 want).
Proof.
  intros got want Hg H. unfold same_rc in H. destruct (Z.eqb_spec want RC_FAILS) as [->|Hne].
  - split; [|intros C; exfalso; exact (C eq_refl)].
    intros _ E. apply negb_true_iff, Z.eqb_neq in H. apply H.
    apply (f_equal bv_unsigned) in E. unfold w64 in E. rewrite !Z_to_bv_unsigned in E.
    unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E. rewrite Zmod_0_l in E.
    apply Z.mod_divide in E; [|lia]. destruct E as (q & Hq). lia.
  - apply Z.eqb_eq in H. subst got. split; [|intros _; reflexivity].
    intros E C. rewrite E in C. apply (f_equal bv_unsigned) in C. vm_compute in C. discriminate C.
Qed.

(* the runner's entry state at +0xcd4: the slots 0x98(s1) = m + MD_N_MARK and 0xf0(s1) = g_nl + 0x40000 *)
Definition o2y_rg : YP09.region := YP09.mkRegion (Some 9%nat) 0x98 0xf8 0x98 0x98
  [YP09.mkChunk 0x98 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 33 0))].
Definition o2y_ss : sstate := mkSS (AFL + 0xcd4) sr_atoms [o2y_rg] None (mkFacts [] [] []).

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
(* check_socket, check_mark, check_marks, check_requests, as their lanes prove them (check_socket_c.v,
   check_mark_c.v, check_marks_c.v, check_requests_c.v) *)
Hypothesis CS : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CM : forall fy : YK11.FPState, @check_mark_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CMK : forall fy : YK11.FPState, @check_marks_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CR : forall fy : YK11.FPState, @check_requests_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).

(* the registers of the exit cuts: s3, s5 = the marks block, s6 = m, s8 .. s11 *)
Definition o2_yregs (cx : lcx) (md mk fp i : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 21 = w64 mk /\
  getr (ms_regs ms3) 22 = w64 md /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

(* the exit cut at pc: mark_quietly has returned (the data hold their relations again, the counters are operation
   i + 1's), the library's code got is in register r, the model's want in s7, same_rc of them *)
Definition o2_y_inv (pc : Z) (r : bv 5) (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout)
    (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N got want : Z) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  0 <= i <= 47 /\
  lf_shape fy pc ms3 /\ lf_core cx ms3 /\ o2_yregs cx md mk fp i ms3 /\
  getr (ms_regs ms3) r = w64 got /\ getr (ms_regs ms3) 23 = w64 want /\
  - 2 ^ 63 <= got < 2 ^ 63 /\ same_rc got want = true /\
  lf_saved cx W3 ms3 /\ lf_header cx fp W3 ms3 /\ lf_fshadow cx fp W3 ms3 LF_SH0 /\
  lf_slots cx md mk fp W3 ms3 /\ lf_cur cx W3 ms3 P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly3 S3 W3 ms3 md3 T3 [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) /\
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) /\
  nk_opened kbs <= 64 * (i + 1) /\ requests_are kbs mbs.

(* +0xcd4 `j +0x1108`, +0x1108 `ld s7, 0xf0(s1)`, +0x110c `ld s5, 0x98(s1)`, +0x1110 = LF_tail *)
Lemma o2y_tail : forall POST i,
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_y_inv (AFL + 0xcd4) 18%bv i).
Proof.
  intros POST i NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HY.
  destruct HY as (md & mk & P & N & got & want & kbs & mbs & gbs & T3 & Hi & Hsh & Hcore & Hreg & Rg & Rw & Hgr & Hsr
    & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop & Hrq).
  pose proof HB as (_ & _ & HGX & _).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_lt as CL.
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (_ & _ & _ & _ & _ & _ & HAR3).
  pose proof Hblk as (Bmd & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & Hm4 & Hmc & _).
  change (req_size MD_SIZE) with 8856 in Hmc.
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNM & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & SG40 & _).
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (md + MD_N_MARK); Z_to_bv 64 (LA_G_NL + 0x40000)])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 (md + MD_N_MARK)).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra _ [Z_to_bv 64 (md + MD_N_MARK); Z_to_bv 64 (LA_G_NL + 0x40000)] 0). }
  assert (E33 : ew E 33 = Z_to_bv 64 (LA_G_NL + 0x40000)).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra _ [Z_to_bv 64 (md + MD_N_MARK); Z_to_bv 64 (LA_G_NL + 0x40000)] 1). }
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2y_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xcd4))) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2y_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold o2y_rg. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by (unfold LLVMF_STK in *; clia).
      split; [unfold LLVMF_STK in *; clia|]. split; [unfold LLVMF_STK in *; clia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (u_slot_chunk E cx W3 ms3 0x98 _ (md + MD_N_MARK)); [|exact SNM].
        rewrite (lf_sv_off E 32 (md + MD_N_MARK) 0 E32) by (unfold MD_N_MARK; clia). rewrite Z.add_0_r. reflexivity.
      + apply (u_slot_chunk E cx W3 ms3 0xf0 _ (LA_G_NL + 0x40000)); [|exact SG40].
        rewrite (lf_sv_off E 33 (LA_G_NL + 0x40000) 0 E33) by (unfold LA_G_NL; clia). rewrite Z.add_0_r. reflexivity.
    - apply pairwise_disjoint_of_extents. unfold o2y_rg, extent_of_region. cbn [map].
      cbn [zpairwise_disjoint zall_disjoint]. tauto.
    - split; [|split; exact I]. exact I. }
  rewrite (lf_shape_eta fy (AFL + 0xcd4) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xcd4))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LF_tail; [apply ar_awr_nowin; vm_compute; reflexivity|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
  rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
  rewrite E32 in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite E33 in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
  apply (NEXT cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJ Hfr).
  exists md, mk, P, N, kbs, mbs, gbs, T3.
  split; [exact Hi|].
  split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
  split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
  split; [unfold lf_lregs; rewrite Q19, Q21, Q22, Q23, Q24, Q25, Q26, Q27;
    repeat split; try assumption; reflexivity|].
  split; [exact (lf_saved_keep _ cx W3 ms3 W3 msB KB (fun a _ H => H) Hsv)|].
  split; [exact (lf_header_keep _ cx fp W3 ms3 W3 msB KB (fun a _ H => H) Hhd)|].
  split; [exact (lf_fshadow_keep _ cx fp W3 ms3 W3 msB LF_SH0 KB (fun a _ H => H) Hfs)|].
  split; [exact (lf_slots_keep _ cx md mk fp W3 ms3 W3 msB KB (fun a _ H => H) Hsl)|].
  split; [exact (lf_cur_keep _ cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur)|].
  split; [exact (lf_jbk_keep B MT MS la_nul _ cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msB md4 KB Fd Fs
    (fun a _ H => H) Hjbk)|].
  split; [exact (lf_blocks_keep B _ _ _ cx md mk T3 ly3 S3 KB (fun a _ H => H) Hblk)|].
  split; [exact (lf_data_keep _ _ _ cx md mk kbs mbs gbs KB (wcarry_on_grows _ _ _ HGB) (fun a _ H => H) Hdat)|].
  exact Hop.
Qed.

(* the callee-saved registers of the cut, across a no-write leaf call *)
Ltac o2y_sv := unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia) |
    (vm_compute; right; right; right; right; right; split; discriminate) ].
Ltac o2y_pr PR := repeat split; rewrite PR by o2y_sv; assumption.

(* +0xccc `mv a0, s6; jal check_requests` (0x834a4), then +0xcd4 *)
Lemma o2y_cr : forall POST i, FROM POST (o2_y_inv (AFL + 0xcd4) 18%bv i) -> FROM POST (o2_y_inv (AFL + 0xccc) 18%bv i).
Proof.
  intros POST i NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HY.
  destruct HY as (md & mk & P & N & got & want & kbs & mbs & gbs & T3 & Hi & Hsh & Hcore & Hreg & Rg & Rw & Hgr & Hsr
    & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop & Hreq).
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xccc) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xccc)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xccc))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (o5c_reg_atom_call fy W3 _ ssB _ msB _ r HS HA Hr)).
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hcur.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hreg as (L19 & L21 & L22 & L24 & L25 & L26 & L27).
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xcd4))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4828). rewrite (codeptr_val _ 4828 HEI). reflexivity. }
  assert (R10 : getr (ms_regs msB) 10 = getr (ms_regs ms3) 22).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 10%bv) with (SOff 22 0). cbn [sv_denot]. rewrite (proj1 HA 22%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 22 22%bv eq_refl). }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite Hms. clear Hms.
  rewrite pa_sigma_check_requests, (lv_text LV).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (link_text + AF_check_requests)) (ms_mem msB) (seg_rom SEGS)) md4)
    with (cfg_at SEGS CHECK_REQUESTS_A (ms_regs msB) (ms_mem msB) md4).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  pose proof Hjbk' as (J1 & _ & Jfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hblk' as (Bmd & Bmk & _ & _ & _ & _ & _ & _ & Bmdt & _ & _ & _ & _ & Bramd & _ & Bammd & _).
  pose proof Hdat' as (Dk & Dwf & _ & _ & _ & _ & Dmd & Dmwf & _).
  assert (Hsp : spZ (ms_regs msB) = lf_sp1 cx).
  { unfold spZ. rewrite (KR 2%bv eq_refl), C2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in Hlo. clia. }
  assert (Ha0 : aarg (ms_regs msB) 0 = md).
  { rewrite ar_aarg0, R10, L22. unfold w64. apply unsigned_lit_small.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & H4 & Hc & _). unfold req_size, MD_SIZE in *.
    cbn in Hc. clia. }
  assert (HKr : CHECK_REQUESTS_AK = 8272) by reflexivity.
  assert (Hev : k2 + 0 <= EV_LIB).
  { pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia. }
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_REQUESTS_A
    CHECK_REQUESTS_AK 0 [] _ _ _ _ (CR fy)
    cx fp ly3 S3 W3 (ms_mem msB) md4 k2 (ms_regs msB) (POST cx) HB HJ HRO).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; clia | reflexivity].
  - unfold raZ. rewrite R1, (lv_text LV).
    rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; clia).
    unfold link_text, AF_LLVMFuzzerTestOneInput; clia.
  - rewrite (KR 3%bv eq_refl), C3. exact HGP.
  - rewrite (KR 4%bv eq_refl), C4. exact HTP.
  - exact Hsp.
  - rewrite HKr. unfold LLVMF_STK. clia.
  - clia.
  - exact Hev.
  - exact (ar_side_room S3 fp [] Hfr eq_refl).
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a Ha. unfold check_requests_ard, rd_ivl in Ha. rewrite Ha0 in Ha. right; left. exists md, MD_SIZE.
    split; [exact Bmd|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in Ha. clia.
  - unfold check_requests_apre. exists kbs, mbs. rewrite Ha0.
    destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem msB) md4 HAR3) as (Gra & Ghv).
    split; [exact Dk|]. split; [exact Dmd|]. split; [exact Dwf|]. split; [exact Dmwf|]. split; [exact Hreq|].
    split; [exact Bramd|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ md MD_SIZE md MD_SIZE HAR3 Bmd);
            change (req_size MD_SIZE) with 8856; unfold MD_SIZE; clia|].
    split; [exact Bammd|]. split; [exact Gra|]. split; [exact Ghv|].
    split; [unfold apart_frame; left; rewrite Hsp, HKr;
            destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & _ & Hc & _);
            unfold req_size, MD_SIZE, LLVMF_STK in *; cbn in Hc; clia|].
    unfold apart_gnl, LA_G_NL, NK_SIZE, MD_SIZE. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in Bmdt.
    clia.
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm _.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    replace (k2 + 0) with k2 in HJ2 by clia.
    destruct (o5c_leaf_cut SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msB md4 ly2 S2 W2 ms2 md2
      CHECK_REQUESTS_AK HB Hfr HJ HJ2 ltac:(rewrite HKr; clia) ltac:(rewrite HKr; unfold LLVMF_STK in *; clia)
      Hkp Hsk Hs2 Hperm Hfd2 Hfs2 Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2).
    assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 18 ->
      getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr Hn. cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr r Hr). apply KR.
      assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
        bv_unsigned r = 9 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
        bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
        bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
      destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]];
        (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity. }
    assert (P18 : getr (ms_regs ms2) 18 = getr (ms_regs ms3) 18).
    { cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr 18%bv ltac:(o2y_sv)). apply KR; vm_compute; reflexivity. }
    apply (NEXT cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, got, want, kbs, mbs, gbs, T3.
    split; [exact Hi|].
    split.
    { unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
      split; [rewrite R1; reflexivity|]. repeat split; reflexivity. }
    split; [o2y_pr PR|]. split; [o2y_pr PR|].
    split; [rewrite P18; exact Rg|]. split; [rewrite PR by o2y_sv; exact Rw|].
    split; [exact Hgr|]. split; [exact Hsr|].
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
    split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. split; [exact Hop | exact Hreq].
Qed.

(* +0xcc0 `mv a0, s5; mv a1, s6; jal check_marks` (0x8349c), then +0xccc *)
Lemma o2y_cmk : forall POST i, FROM POST (o2_y_inv (AFL + 0xccc) 18%bv i) -> FROM POST (o2_y_inv (AFL + 0xcc0) 18%bv i).
Proof.
  intros POST i NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HY.
  destruct HY as (md & mk & P & N & got & want & kbs & mbs & gbs & T3 & Hi & Hsh & Hcore & Hreg & Rg & Rw & Hgr & Hsr
    & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop & Hreq).
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xcc0) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xcc0)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xcc0))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (o5c_reg_atom_call fy W3 _ ssB _ msB _ r HS HA Hr)).
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hcur.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hreg as (L19 & L21 & L22 & L24 & L25 & L26 & L27).
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xccc))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4820). rewrite (codeptr_val _ 4820 HEI). reflexivity. }
  assert (R10 : getr (ms_regs msB) 10 = getr (ms_regs ms3) 21).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 10%bv) with (SOff 21 0). cbn [sv_denot]. rewrite (proj1 HA 21%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 21 21%bv eq_refl). }
  assert (R11 : getr (ms_regs msB) 11 = getr (ms_regs ms3) 22).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 11%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 11%bv) with (SOff 22 0). cbn [sv_denot]. rewrite (proj1 HA 22%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 22 22%bv eq_refl). }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite Hms. clear Hms.
  rewrite pa_sigma_check_marks, (lv_text LV).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (link_text + AF_check_marks)) (ms_mem msB) (seg_rom SEGS)) md4)
    with (cfg_at SEGS CHECK_MARKS_A (ms_regs msB) (ms_mem msB) md4).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  pose proof Hjbk' as (J1 & _ & Jfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hblk' as (Bmd & Bmk & _ & _ & _ & _ & Bm16 & Bk16 & Bmdt & Bmkt & _ & _ & _ & Bramd & Bramk & Bammd & Bammk).
  pose proof Hdat' as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & Dmk & Dkwf & Dare & _).
  assert (Hsp : spZ (ms_regs msB) = lf_sp1 cx).
  { unfold spZ. rewrite (KR 2%bv eq_refl), C2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in Hlo. clia. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & Hm4 & Hmc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & Hk4 & Hkc & _).
  change (req_size MD_SIZE) with 8856 in Hmc. change (req_size MK_SIZE) with 516 in Hkc.
  assert (Ha0 : aarg (ms_regs msB) 0 = mk).
  { rewrite ar_aarg0, R10, L21. unfold w64. apply unsigned_lit_small. clia. }
  assert (Ha1 : aarg (ms_regs msB) 1 = md).
  { rewrite ar_aarg1, R11, L22. unfold w64. apply unsigned_lit_small. clia. }
  assert (HKr : CHECK_MARKS_AK = 8224) by reflexivity.
  assert (Hev : k2 + 0 <= EV_LIB).
  { pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia. }
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_MARKS_A
    CHECK_MARKS_AK 0 [] _ _ _ _ (CMK fy)
    cx fp ly3 S3 W3 (ms_mem msB) md4 k2 (ms_regs msB) (POST cx) HB HJ HRO).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; clia | reflexivity].
  - unfold raZ. rewrite R1, (lv_text LV).
    rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; clia).
    unfold link_text, AF_LLVMFuzzerTestOneInput; clia.
  - rewrite (KR 3%bv eq_refl), C3. exact HGP.
  - rewrite (KR 4%bv eq_refl), C4. exact HTP.
  - exact Hsp.
  - rewrite HKr. unfold LLVMF_STK. clia.
  - clia.
  - exact Hev.
  - exact (ar_side_room S3 fp [] Hfr eq_refl).
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a Ha. unfold check_marks_ard, rd_ivl in Ha. rewrite Ha0, Ha1 in Ha. right; left.
    destruct Ha as [Ha | Ha].
    + exists mk, MK_SIZE. split; [exact Bmk|]. change (req_size MK_SIZE) with 516. unfold MK_SIZE in Ha. clia.
    + exists md, MD_SIZE. split; [exact Bmd|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in Ha. clia.
  - unfold check_marks_apre. exists gbs, mbs. rewrite Ha0, Ha1.
    pose proof Dmwf as (_ & _ & _ & _ & _ & Dmm).
    pose proof (Z.div_mod mk 16 ltac:(lia)) as DK. pose proof (Z.div_mod md 16 ltac:(lia)) as DM.
    rewrite Bk16, Z.add_0_r in DK. rewrite Bm16, Z.add_0_r in DM.
    split; [exact Dmk|]. split; [exact Dmd|]. split; [exact Dkwf|]. split; [exact Dmm|]. split; [exact Dare|].
    split; [exact Bramk|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ mk MK_SIZE mk MK_SIZE HAR3 Bmk);
            change (req_size MK_SIZE) with 516; unfold MK_SIZE; clia|].
    split; [exact Bammk|]. split; [exact Bramd|].
    split; [rewrite ard_aview; apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ md MD_SIZE md MD_SIZE HAR3 Bmd);
            change (req_size MD_SIZE) with 8856; unfold MD_SIZE; clia|].
    split; [exact Bammd|].
    split; [unfold apart_frame; left; rewrite Hsp, HKr; unfold MK_SIZE, LLVMF_STK in *; clia|].
    split; [unfold apart_frame; left; rewrite Hsp, HKr; unfold MD_SIZE, LLVMF_STK in *; clia|].
    split.
    + intros b Hb. rewrite ard_aview. apply (mq_blk_tail_vis16 SEGS B ly3 S3 W3 (ms_mem msB) md4 mk MK_SIZE b HAR3 Bmk).
      replace (round_up MK_SIZE 16) with 528 by reflexivity. unfold MK_SIZE in *. clia.
    + intros b Hb. exfalso. unfold MD_SIZE in Hb. clia.
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm _.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    replace (k2 + 0) with k2 in HJ2 by clia.
    destruct (o5c_leaf_cut SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msB md4 ly2 S2 W2 ms2 md2
      CHECK_MARKS_AK HB Hfr HJ HJ2 ltac:(rewrite HKr; clia) ltac:(rewrite HKr; unfold LLVMF_STK in *; clia)
      Hkp Hsk Hs2 Hperm Hfd2 Hfs2 Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2).
    assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 18 ->
      getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr Hn. cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr r Hr). apply KR.
      assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
        bv_unsigned r = 9 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
        bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
        bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
      destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]];
        (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity. }
    assert (P18 : getr (ms_regs ms2) 18 = getr (ms_regs ms3) 18).
    { cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr 18%bv ltac:(o2y_sv)). apply KR; vm_compute; reflexivity. }
    apply (NEXT cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, got, want, kbs, mbs, gbs, T3.
    split; [exact Hi|].
    split.
    { unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
      split; [rewrite R1; reflexivity|]. repeat split; reflexivity. }
    split; [o2y_pr PR|]. split; [o2y_pr PR|].
    split; [rewrite P18; exact Rg|]. split; [rewrite PR by o2y_sv; exact Rw|].
    split; [exact Hgr|]. split; [exact Hsr|].
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
    split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. split; [exact Hop | exact Hreq].
Qed.

(* +0xcb4 `mv a0, s2; mv a1, s7; jal check_mark` (0x83490), then +0xcc0 *)
Lemma o2y_cm : forall POST i, FROM POST (o2_y_inv (AFL + 0xcc0) 18%bv i) -> FROM POST (o2_y_inv (AFL + 0xcb4) 18%bv i).
Proof.
  intros POST i NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HY.
  destruct HY as (md & mk & P & N & got & want & kbs & mbs & gbs & T3 & Hi & Hsh & Hcore & Hreg & Rg & Rw & Hgr & Hsr
    & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop & Hreq).
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xcb4) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xcb4)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xcb4))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (o5c_reg_atom_call fy W3 _ ssB _ msB _ r HS HA Hr)).
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hcur.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hreg as (L19 & L21 & L22 & L24 & L25 & L26 & L27).
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xcc0))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4808). rewrite (codeptr_val _ 4808 HEI). reflexivity. }
  assert (R10 : getr (ms_regs msB) 10 = getr (ms_regs ms3) 18).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 10%bv) with (SOff 18 0). cbn [sv_denot]. rewrite (proj1 HA 18%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 18 18%bv eq_refl). }
  assert (R11 : getr (ms_regs msB) 11 = getr (ms_regs ms3) 23).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 11%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 11%bv) with (SOff 23 0). cbn [sv_denot]. rewrite (proj1 HA 23%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 23 23%bv eq_refl). }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite Hms. clear Hms.
  rewrite pa_sigma_check_mark, (lv_text LV).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (link_text + AF_check_mark)) (ms_mem msB) (seg_rom SEGS)) md4)
    with (cfg_at SEGS CHECK_MARK_A (ms_regs msB) (ms_mem msB) md4).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  pose proof Hjbk' as (J1 & _ & Jfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).

  assert (Hsp : spZ (ms_regs msB) = lf_sp1 cx).
  { unfold spZ. rewrite (KR 2%bv eq_refl), C2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in Hlo. clia. }

  assert (HKr : CHECK_RC_AK = 16) by reflexivity.
  assert (Hev : k2 + 0 <= EV_LIB).
  { pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia. }
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_MARK_A
    CHECK_RC_AK 0 [] _ _ _ _ (o5c_aleaf_rd SK B fy _ _ _ _ _ _ _ (CM fy))
    cx fp ly3 S3 W3 (ms_mem msB) md4 k2 (ms_regs msB) (POST cx) HB HJ HRO).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; clia | reflexivity].
  - unfold raZ. rewrite R1, (lv_text LV).
    rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; clia).
    unfold link_text, AF_LLVMFuzzerTestOneInput; clia.
  - rewrite (KR 3%bv eq_refl), C3. exact HGP.
  - rewrite (KR 4%bv eq_refl), C4. exact HTP.
  - exact Hsp.
  - rewrite HKr. unfold LLVMF_STK. clia.
  - clia.
  - exact Hev.
  - exact (ar_side_room S3 fp [] Hfr eq_refl).
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a Ha. destruct Ha.
  - unfold check_rc_apre, same_rc_aregs. rewrite R10, R11, Rg, Rw. exact (o2_same_w got want Hgr Hsr).
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm _.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    replace (k2 + 0) with k2 in HJ2 by clia.
    destruct (o5c_leaf_cut SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msB md4 ly2 S2 W2 ms2 md2
      CHECK_RC_AK HB Hfr HJ HJ2 ltac:(rewrite HKr; clia) ltac:(rewrite HKr; unfold LLVMF_STK in *; clia)
      Hkp Hsk Hs2 Hperm Hfd2 Hfs2 Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2).
    assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 18 ->
      getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr Hn. cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr r Hr). apply KR.
      assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
        bv_unsigned r = 9 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
        bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
        bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
      destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]];
        (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity. }
    assert (P18 : getr (ms_regs ms2) 18 = getr (ms_regs ms3) 18).
    { cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr 18%bv ltac:(o2y_sv)). apply KR; vm_compute; reflexivity. }
    apply (NEXT cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, got, want, kbs, mbs, gbs, T3.
    split; [exact Hi|].
    split.
    { unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
      split; [rewrite R1; reflexivity|]. repeat split; reflexivity. }
    split; [o2y_pr PR|]. split; [o2y_pr PR|].
    split; [rewrite P18; exact Rg|]. split; [rewrite PR by o2y_sv; exact Rw|].
    split; [exact Hgr|]. split; [exact Hsr|].
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
    split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. split; [exact Hop | exact Hreq].
Qed.

(* +0xcac `mv s2, a0; jal check_socket` (0x83484), then +0xcb4 *)
Lemma o2y_cs : forall POST i, FROM POST (o2_y_inv (AFL + 0xcb4) 18%bv i) -> FROM POST (o2_y_inv (AFL + 0xcac) 10%bv i).
Proof.
  intros POST i NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HY.
  destruct HY as (md & mk & P & N & got & want & kbs & mbs & gbs & T3 & Hi & Hsh & Hcore & Hreg & Rg & Rw & Hgr & Hsr
    & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop & Hreq).
  pose proof HB as (_ & _ & HGX & _).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  rewrite (lf_shape_eta fy (AFL + 0xcac) ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (o5c_entry fy W3 (ms_regs ms3) (ms_mem ms3) (AFL + 0xcac)) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + (AFL + 0xcac))) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (o5c_reg_atom_call fy W3 _ ssB _ msB _ r HS HA Hr)).
  destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KB (wcarry_on_grows _ _ _ HGB) Fd Fs (fun a _ H => H) Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur) as Hcur'.
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hcur.
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hreg as (L19 & L21 & L22 & L24 & L25 & L26 & L27).
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xcb4))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4796). rewrite (codeptr_val _ 4796 HEI). reflexivity. }
  assert (R18 : getr (ms_regs msB) 18 = getr (ms_regs ms3) 10).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 18%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 18%bv) with (SOff 10 0). cbn [sv_denot]. rewrite (proj1 HA 10%nat ltac:(lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat _ _ 10 10%bv eq_refl). }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite Hms. clear Hms.
  rewrite pa_sigma_check_socket, (lv_text LV).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (link_text + AF_check_socket)) (ms_mem msB) (seg_rom SEGS)) md4)
    with (cfg_at SEGS CHECK_SOCKET_A (ms_regs msB) (ms_mem msB) md4).
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msB) md4 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  pose proof Hjbk' as (J1 & _ & Jfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof Hdat' as (Dk & _ & _ & Dop & Dmis & Doc & _).
  assert (Hsp : spZ (ms_regs msB) = lf_sp1 cx).
  { unfold spZ. rewrite (KR 2%bv eq_refl), C2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in Hlo. clia. }

  assert (HKr : CHECK_SOCKET_AK = 16) by reflexivity.
  assert (Hev : k2 + 0 <= EV_LIB).
  { pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia. }
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_SOCKET_A
    CHECK_SOCKET_AK 0 [] _ _ _ _ (o5c_aleaf_rd SK B fy _ _ _ _ _ _ _ (CS fy))
    cx fp ly3 S3 W3 (ms_mem msB) md4 k2 (ms_regs msB) (POST cx) HB HJ HRO).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold AFL, AF_LLVMFuzzerTestOneInput; clia | reflexivity].
  - unfold raZ. rewrite R1, (lv_text LV).
    rewrite unsigned_lit_small by (unfold link_text, AFL, AF_LLVMFuzzerTestOneInput; clia).
    unfold link_text, AF_LLVMFuzzerTestOneInput; clia.
  - rewrite (KR 3%bv eq_refl), C3. exact HGP.
  - rewrite (KR 4%bv eq_refl), C4. exact HTP.
  - exact Hsp.
  - rewrite HKr. unfold LLVMF_STK. clia.
  - clia.
  - exact Hev.
  - exact (ar_side_room S3 fp [] Hfr eq_refl).
  - intros a (r & Hr & _). destruct Hr.
  - intros a (r & Hr & _). destruct Hr.
  - intros a [].
  - exists kbs. split; [exact Dk|]. split; [exact Dop|]. split; [exact Doc | exact Dmis].
  - intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm _.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    replace (k2 + 0) with k2 in HJ2 by clia.
    destruct (o5c_leaf_cut SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N ly3 S3 W3 msB md4 ly2 S2 W2 ms2 md2
      CHECK_SOCKET_AK HB Hfr HJ HJ2 ltac:(rewrite HKr; clia) ltac:(rewrite HKr; unfold LLVMF_STK in *; clia)
      Hkp Hsk Hs2 Hperm Hfd2 Hfs2 Hsv' Hhd' Hfs' Hsl' Hcur' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2).
    assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 18 ->
      getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr Hn. cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr r Hr). apply KR.
      assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
        bv_unsigned r = 9 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
        bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
        bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
      destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]];
        (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity. }
    assert (P18 : getr (ms_regs ms2) 18 = getr (ms_regs ms3) 10).
    { cbn [ms2 ms_regs mkst]. rewrite (o5c_pres _ _ Hpr 18%bv ltac:(o2y_sv)). exact R18. }
    apply (NEXT cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, got, want, kbs, mbs, gbs, T3.
    split; [exact Hi|].
    split.
    { unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
      split; [rewrite R1; reflexivity|]. repeat split; reflexivity. }
    split; [o2y_pr PR|]. split; [o2y_pr PR|].
    split; [rewrite P18; exact Rg|]. split; [rewrite PR by o2y_sv; exact Rw|].
    split; [exact Hgr|]. split; [exact Hsr|].
    split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
    split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. split; [exact Hop | exact Hreq].
Qed.

(* +0xcac to LF_tail *)
Lemma o2y_exit : forall POST i,
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_y_inv (AFL + 0xcac) 10%bv i).
Proof. intros POST i H. exact (o2y_cs POST i (o2y_cm POST i (o2y_cmk POST i (o2y_cr POST i (o2y_tail POST i H))))). Qed.

End a.
