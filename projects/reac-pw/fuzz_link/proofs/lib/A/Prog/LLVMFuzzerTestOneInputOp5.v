(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 745 of its 802 lines of code are new or changed and 347 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_refused,
   operation byte mod 6 = 5, entry +0x958 (listing (internal path)
   (internal record, sha256 e84d6f0c6974)). The arm reads the selector byte (0 when the cursor is empty, +0x9a4),
   writes model_begin's counters, builds mark_quietly's two arguments by `(b & 1) - 1` and `sign(b << 62)` (the marks
   block or NULL, .str.1 or NULL: the deliberate misuse test), calls mark_quietly (0x831f8), check_mark with -22
   (0x83200) and check_requests (0x83208), and joins the loop tail +0x1110.
   lf_op5 : the walk from the arm's cut to the loop tail's cut, at the same operation index i.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputMqCall LLVMFuzzerTestOneInputMqPost LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputOp5C
  LLVMFuzzerTestOneInputOp5M LLVMFuzzerTestOneInputOp5E.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c check_write_c check_mark_c check_requests_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The symbolic states of op_refused
   ========================================================================== *)

Definition o5_RSB : Z := 0x7fff8000.
Definition o5_Bx : sv := SOff 27 0.
Definition o5_span : Z * Z := (o5_RSB, o5_RSB + 2 ^ 44 - 1).
(* the shadow address of the model's byte o, as the spill slots hold it: s11 + ((md + o) >> 3) *)
Definition o5_shx (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 o) (SLit 3)) (SOff 27 0).
Definition o5_c8 (o : Z) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 v).
(* the spill slots op_refused reads (+0x60 .. +0xe0) and the cursor it moves (+0x118, +0x120) *)
Definition o5_fr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x60 0x128 0x118 0x128
    [o5_c8 0x60 (SLit LA_STR1); o5_c8 0x90 (SOff 34 0); o5_c8 0xa0 (o5_shx 8336); o5_c8 0xa8 (o5_shx 8);
     o5_c8 0xb0 (o5_shx 4); o5_c8 0xc0 (SOff 23 0x2000); o5_c8 0xc8 (o5_shx 0); o5_c8 0xd0 (SOff 22 8336);
     o5_c8 0xd8 (SOff 22 8); o5_c8 0xe0 (SOff 22 4); o5_c8 0x118 (SOff 33 0); o5_c8 0x120 (SOff 32 0)].
(* the model's four counters: socket_errno, send_errno, next (+0 .. +12) and n_req (+8336) *)
Definition o5_md0 : YP09.region := YP09.mkRegion (Some 22%nat) 0 12 0 12 [].
Definition o5_md1 : YP09.region := YP09.mkRegion (Some 22%nat) 8336 8340 8336 8340 [].
(* g_nl's two errno words (s7 + 0x20c, + 0x210) and its n_sent word (s7 + 0x22a8) *)
Definition o5_gn : YP09.region :=
  YP09.mkRegion (Some 23%nat) 0x20c 0x22ac 0x22a8 0x22ac
    [YP09.mkChunk 0x20c (CVal 4 (SOff 35 0)); YP09.mkChunk 0x210 (CVal 4 (SOff 36 0))].
(* the selector byte at the cursor *)
Definition o5_in : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition o5_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (22%nat, mkAF 4096 (2 ^ 47 - 8856) 4); (23%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (27%nat, mkAF o5_RSB o5_RSB 0); (33%nat, mkAF 1 (2 ^ 47 - 1) 0); (37%nat, mkAF 0 255 0)] [] [].
Definition o5_rs : smem := [o5_fr; o5_md0; o5_md1; o5_gn].
Definition o5_ss : sstate := mkSS LF_op5 sr_atoms o5_rs None o5_facts.
Definition o5_SH : list shent := [mkSHE 22 0 8856].
Definition o5_SHn : list shent := [mkSHE 22 0 8856; mkSHE 33 0 1].
(* the extra atoms: the cursor's length and pointer, the marks block, g_nl's two errno words, the byte *)
Definition o5_extra (N1 P1 mk serr sderr b2 : Z) : list word :=
  [Z_to_bv 64 N1; Z_to_bv 64 P1; Z_to_bv 64 mk; Z_to_bv 64 serr; Z_to_bv 64 sderr; Z_to_bv 64 b2].

Lemma o5_sv_of_U : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof.
  intros E e v HU Hv. apply bv_eq. rewrite Z_to_bv_unsigned. unfold U in HU. rewrite HU.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

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
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

#[local] Abbreviation FROM POST GI :=
  (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation ARM op i := (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP op i).
#[local] Abbreviation TAIL i := (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).

Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* mark_quietly's two arms (lib/A/Prog/mark_quietly_c.v), check_mark and check_requests (their lanes) *)
Hypothesis MQO : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_open fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B MT (mo_malloc MT AMF_BLOCK) LF_CTX
    (fun _ => True) (mq_ledpost B).
Hypothesis MQA : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_again fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CM : forall fx0 : YK11.FPState, @check_mark_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CR : forall fx0 : YK11.FPState, @check_requests_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.

(* the symbolic state holds at the arm's entry *)
Lemma o5_entry : forall (fy : YK11.FPState) (ms : machine_state) (W : world SEGS) sp1 md N1 P1 mk serr sderr b2,
  ms_pc_val ms = w64 (BASE + LF_op5) -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = @fp_regs fy -> ms_fcsr ms = @fp_csr fy ->
  getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 9 = w64 sp1 ->
  getr (ms_regs ms) 22 = w64 md -> getr (ms_regs ms) 23 = w64 (LA_G_NL + 0x40000) ->
  getr (ms_regs ms) 27 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= md <= 2 ^ 47 - 8856 -> md mod 16 = 0 -> md + 8856 <= sp1 -> (md + 8856 <= 0x10000 \/ 0x654000 <= md) ->
  0 <= N1 < 2 ^ 64 -> 1 <= P1 <= 2 ^ 47 - 1 -> 0 <= mk < 2 ^ 64 ->
  0 <= serr < 2 ^ 32 -> 0 <= sderr < 2 ^ 32 -> 0 <= b2 <= 255 ->
  (forall o, 0x118 <= o < 0x128 -> writable_at SEGS (rdW W (ms_mem ms)) (sp1 + o)) ->
  (forall o, 0 <= o < 12 -> writable_at SEGS (rdW W (ms_mem ms)) (md + o)) ->
  (forall o, 8336 <= o < 8340 -> writable_at SEGS (rdW W (ms_mem ms)) (md + o)) ->
  (forall o, 0x22a8 <= o < 0x22ac -> writable_at SEGS (rdW W (ms_mem ms)) (LA_G_NL + 0x40000 + o)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0x60) 8 LA_STR1 ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0x90) 8 mk ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xa0) 8 (shadow_of_addr SHADOW_OFF (md + MD_N_REQ)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xa8) 8 (shadow_of_addr SHADOW_OFF (md + MD_NEXT)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xb0) 8 (shadow_of_addr SHADOW_OFF (md + MD_SEND_ERRNO)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xc0) 8 (LA_G_NL + 0x42000) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xc8) 8 (shadow_of_addr SHADOW_OFF md) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xd0) 8 (md + MD_N_REQ) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xd8) 8 (md + MD_NEXT) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xe0) 8 (md + MD_SEND_ERRNO) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0x118) 8 P1 ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0x120) 8 N1 ->
  val_mem SEGS (rdW W (ms_mem ms)) (LA_G_NL + NK_SOCKET_ERRNO) 4 serr ->
  val_mem SEGS (rdW W (ms_mem ms)) (LA_G_NL + NK_SEND_ERRNO) 4 sderr ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms) (o5_extra N1 P1 mk serr sderr b2))) o5_ss (restrict (w_H W) ms).
Proof.
  intros fy ms W sp1 md N1 P1 mk serr sderr b2 Hpc Hresv Hsvc Hrom Hfrg Hfcsr R2 R9 R22 R23 R27
    Hs1a Hs1b Hs1c Hmda Hmdb Hmds1 Hmdoff HN1 HP1 Hmk Hse Hsd Hb2 W1 W2 W3 W4
    V60 V90 VA0 VA8 VB0 VC0 VC8 VD0 VD8 VE0 V118 V120 VSE VSD.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (EIT : IMG_TOP = 0x654000) by reflexivity.
  assert (Hms : restrict (w_H W) ms =
    @mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + LF_op5)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
  { destruct ms; cbn in *; subst; reflexivity. }
  rewrite Hms.
  set (E := Eimg (Ereg (ms_regs ms) (o5_extra N1 P1 mk serr sderr b2))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms) (o5_extra N1 P1 mk serr sderr b2)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms) r).
  { intros n r Hr. pose proof (u5_range r) as Hr5. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
    unfold A_TEXT. lia. }
  assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = w64 sp1) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E22 : ew E 22 = w64 md) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = w64 (LA_G_NL + 0x40000)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 N1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 P1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 mk) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 serr) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 sderr) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
  assert (E37 : ew E 37 = Z_to_bv 64 b2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = md) by (rewrite E22; unfold w64; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = LA_G_NL + 0x40000)
    by (rewrite E23; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
  assert (U27 : bv_unsigned (ew E 27) = o5_RSB) by (rewrite E27; unfold w64, o5_RSB, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = P1) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = b2) by (rewrite E37; apply unsigned_lit_small; lia).
  (* the denotation of the model's shadow-address expressions *)
  assert (SHX : forall o, 0 <= o <= 8856 ->
            sv_denot E (o5_shx o) = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (md + o))).
  { intros o Ho. apply o5_sv_of_U; [| unfold shadow_of_addr, SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ]].
    - unfold o5_shx. rewrite !U_SAlu, U_SOff, U_SOff, U_SLit. rewrite U22, U27. cbn [zalu_raw].
      unfold zcanon, M64, o5_RSB, shadow_of_addr, SHADOW_OFF.
      replace (Z.land (3 mod 2 ^ 64) 63) with 3 by reflexivity.
      rewrite (Z.mod_small (md + o) (2 ^ 64)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite (Z.mod_small ((md + o) / 8) (2 ^ 64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      rewrite Z.add_0_r. rewrite (Z.mod_small 2147450880 (2 ^ 64)) by lia.
      rewrite Z.mod_small by (split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia] |];
        assert ((md + o) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia); lia).
      lia.
    - assert ((md + o) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (OFF : forall n x v, ew E n = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + v < 2 ^ 64 -> sv_denot E (SOff n v) = Z_to_bv 64 (x + v)).
  { intros n x v Hn Hx Hxv. cbn [sv_denot]. rewrite Hn. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (LIT : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
  { intros n v Hn Hv. cbn [sv_denot]. rewrite Hn. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (SHR : forall o, 0 <= o <= 8856 -> 0 <= shadow_of_addr SHADOW_OFF (md + o) < 2 ^ (8 * Z.of_N 8)).
  { intros o Ho. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold shadow_of_addr, SHADOW_OFF.
    assert ((md + o) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= (md + o) / 8) by (apply Z.div_pos; lia). lia. }
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold o5_rs, o5_fr, o5_md0, o5_md1, o5_gn, o5_c8.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      fold E.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (W1 o Ho)|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ sp1 0x60 8 (SLit LA_STR1) LA_STR1); [reflexivity | unfold LA_STR1; zside | zside | exact V60].
      * apply (chunk_ok_val SEGS E _ sp1 0x90 8 (SOff 34 0) mk); [exact (LIT 34%nat mk E34 Hmk) | zside | zside | exact V90].
      * apply (chunk_ok_val SEGS E _ sp1 0xa0 8 (o5_shx 8336) (shadow_of_addr SHADOW_OFF (md + MD_N_REQ))); [exact (SHX 8336 ltac:(lia)) | exact (SHR 8336 ltac:(lia)) | zside | exact VA0].
      * apply (chunk_ok_val SEGS E _ sp1 0xa8 8 (o5_shx 8) (shadow_of_addr SHADOW_OFF (md + MD_NEXT))); [exact (SHX 8 ltac:(lia)) | exact (SHR 8 ltac:(lia)) | zside | exact VA8].
      * apply (chunk_ok_val SEGS E _ sp1 0xb0 8 (o5_shx 4) (shadow_of_addr SHADOW_OFF (md + MD_SEND_ERRNO))); [exact (SHX 4 ltac:(lia)) | exact (SHR 4 ltac:(lia)) | zside | exact VB0].
      * apply (chunk_ok_val SEGS E _ sp1 0xc0 8 (SOff 23 0x2000) (LA_G_NL + 0x42000));
          [ rewrite (OFF 23%nat (LA_G_NL + 0x40000) 0x2000 E23) by (unfold LA_G_NL; lia); f_equal; lia
          | unfold LA_G_NL; zside | zside | exact VC0].
      * apply (chunk_ok_val SEGS E _ sp1 0xc8 8 (o5_shx 0) (shadow_of_addr SHADOW_OFF md)); [replace (shadow_of_addr SHADOW_OFF md) with (shadow_of_addr SHADOW_OFF (md + 0)) by (rewrite Z.add_0_r; reflexivity); exact (SHX 0 ltac:(lia)) | replace (shadow_of_addr SHADOW_OFF md) with (shadow_of_addr SHADOW_OFF (md + 0)) by (rewrite Z.add_0_r; reflexivity); exact (SHR 0 ltac:(lia)) | zside | exact VC8].
      * apply (chunk_ok_val SEGS E _ sp1 0xd0 8 (SOff 22 8336) (md + MD_N_REQ));
          [exact (OFF 22%nat md 8336 E22 ltac:(lia) ltac:(lia)) | unfold MD_N_REQ; zside | zside | exact VD0].
      * apply (chunk_ok_val SEGS E _ sp1 0xd8 8 (SOff 22 8) (md + MD_NEXT));
          [exact (OFF 22%nat md 8 E22 ltac:(lia) ltac:(lia)) | unfold MD_NEXT; zside | zside | exact VD8].
      * apply (chunk_ok_val SEGS E _ sp1 0xe0 8 (SOff 22 4) (md + MD_SEND_ERRNO));
          [exact (OFF 22%nat md 4 E22 ltac:(lia) ltac:(lia)) | unfold MD_SEND_ERRNO; zside | zside | exact VE0].
      * apply (chunk_ok_val SEGS E _ sp1 0x118 8 (SOff 33 0) P1); [exact (LIT 33%nat P1 E33 ltac:(lia)) | zside | zside | exact V118].
      * apply (chunk_ok_val SEGS E _ sp1 0x120 8 (SOff 32 0) N1); [exact (LIT 32%nat N1 E32 HN1) | zside | zside | exact V120].
    + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (W2 o Ho) | constructor].
    + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (W3 o Ho) | constructor].
    + rewrite U23. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; exact (W4 o Ho)|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (LA_G_NL + 0x40000) 0x20c 4 (SOff 35 0) serr);
          [exact (LIT 35%nat serr E35 ltac:(lia)) | zside | zside |].
        replace (LA_G_NL + 0x40000 + 0x20c) with (LA_G_NL + NK_SOCKET_ERRNO) by (unfold NK_SOCKET_ERRNO; lia). exact VSE.
      * apply (chunk_ok_val SEGS E _ (LA_G_NL + 0x40000) 0x210 4 (SOff 36 0) sderr);
          [exact (LIT 36%nat sderr E36 ltac:(lia)) | zside | zside |].
        replace (LA_G_NL + 0x40000 + 0x210) with (LA_G_NL + NK_SEND_ERRNO) by (unfold NK_SEND_ERRNO; lia). exact VSD.
  - apply pairwise_disjoint_of_extents.
    unfold o5_rs, o5_fr, o5_md0, o5_md1, o5_gn, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U22, U23.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold LA_G_NL. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [o5_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite U2, U9, U22, U23, U27, U33, U37.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold o5_RSB, LA_G_NL in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | idtac].
Qed.

(* the call's stack: the entry sp, the realigned s1 and the window above the allocator's ceiling *)
Lemma o5_geo : forall cx, BASEF cx ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 432 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0 /\
  2 ^ 46 <= lf_sp1 cx.
Proof.
  intros cx HB. pose proof HB as (HPRE & _).
  destruct HPRE as ((_ & _ & _ & _ & _ & Hstk & _) & _).
  destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  unfold LLVMF_STK in *.
  destruct (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME; lia) Hal) as (Hr & H32 & _).
  unfold lf_sp1. unfold LF_MFRAME in Hr. unfold LLVMF_STK. lia.
Qed.

(* the allocator state inside a journal *)
Lemma o5_aj_AR : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B lyc Sc W memc mdc.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (_ & _ & (memS & HJ & _) & _).
  exact (proj1 HJ).
Qed.

Lemma o5_vm_of_rd : forall (W : world SEGS) mem a v,
  rdword (aview SEGS (w_H W) mem) a = Some v -> val_mem SEGS (rdW W mem) a 8 v.
Proof.
  intros W mem a v Hw. exact (val_mem_of_rdword SEGS (w_H W) mem a v Hw).
Qed.

(* a cell of a region of a symbolic state, as a value in memory *)
Lemma o5_chunk_val : forall (H : word -> bool) E ss ms i r j off (n : N) e v,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
  intros H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
  pose proof (st_ok_mem_ok SEGS E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
  pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
  apply (val_of_chunk_ok SEGS E _ _ off n e v); [|exact He | exact Hv | exact Hn].
  exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

Lemma val_mem1_of_mbyte' : forall (m : word -> option byte) a b, mbyte SEGS m a = Some b ->
  val_mem SEGS m a 1 (bv_unsigned b).
Proof.
  intros m a b Hb k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb. f_equal.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  match goal with |- _ = Z_to_bv 8 ?x => replace x with (bv_unsigned b mod 256)
    by (transitivity ((bv_unsigned b mod 256) mod 256); [symmetry; apply Z.mod_mod; lia | reflexivity]) end.
  rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the static write obligation of a run over o5_rs: the cursor slots (the journal's window), the model's four
   counters (a block this call allocated) and g_nl's n_sent (a byte of G) *)
Ltac o5_awr1 U9 U22 U23 Hmdin Hmdc md :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  first
    [ rewrite U9 in Ha; left; split; [left; unfold LLVMF_STK; lia | lia]
    | rewrite U22 in Ha; left; split; [right; right; left; exists md, MD_SIZE; split; [exact Hmdin|];
        split; [exact Hmdc|]; change (req_size MD_SIZE) with 8856; lia | lia]
    | rewrite U23 in Ha; right; left; unfold inG, G_HARNESS; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
        unfold LA_G_NL, NK_SIZE in *; lia
    | lia ].

Ltac o5_awr :=
  lazymatch goal with
  | U9 : bv_unsigned (ew ?E 9) = _, U22 : bv_unsigned (ew ?E 22) = _, U23 : bv_unsigned (ew ?E 23) = _,
    Hmdin : In (?md, MD_SIZE) (ablocks _ _ _), Hmdc : ~ In (?md, MD_SIZE) (ablocks _ _ _) |- _ =>
    cbn [ss_mem];
    repeat (apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val o5_fr o5_md0 o5_md1 o5_gn o5_in];
                                  o5_awr1 U9 U22 U23 Hmdin Hmdc md | ]);
    apply awr_ok_x_nil
  end.

(* ==========================================================================
   Helpers for the state at mark_quietly's call
   ========================================================================== *)

(* a register the runs left as its entry atom *)
Lemma o5_reg_keep : forall (fy : YK11.FPState) E ss pc (H : word -> bool) ms regs0 (r : bv 5),
  st_ok (fx := fy) SEGS E (setpc ss pc) (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
  ew E (Z.to_nat (bv_unsigned r)) = getr regs0 r ->
  getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fy E ss pc H ms regs0 r HS Hsr Hew. rewrite (st_ok_restrict_reg SEGS H E _ ms r HS). cbn [setpc ss_regs].
  rewrite Hsr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hew.
Qed.

(* the run's frame as a kagree, its windows inside the cursor slots and model_begin's ranges *)
Lemma o5_kag_run : forall E rs (m m' : word -> option byte) sp1 md,
  frame_of E rs m m' ->
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 22) = md -> bv_unsigned (ew E 23) = LA_G_NL + 0x40000 ->
  (forall r, In r rs -> In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)
     [(Some 9%nat, 280, 296); (Some 22%nat, 0, 12); (Some 22%nat, 8336, 8340); (Some 23%nat, 8872, 8876);
      (Some 33%nat, 0, 0)]) ->
  kagree SEGS (fun a => (sp1 + 0x118 <= a mod 2 ^ 64 < sp1 + 0x128) \/ lf_mb_rng md (a mod 2 ^ 64)) m m'.
Proof.
  intros E rs m m' sp1 md HF U9 U22 U23 HW a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr & Hw). apply Ha. rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw.
  change (bv_modulus 64) with (2 ^ 64) in Hw.
  pose proof (HW r Hr) as HWr. destruct r as [rb rlo rhi rwlo rwhi rcs]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in *.
  unfold lf_mb_rng, MD_N_REQ, NK_N_SENT.
  cbn [In] in HWr. destruct HWr as [E1 | [E1 | [E1 | [E1 | [E1 | []]]]]]; injection E1 as E2 E3 E4; subst rb rwlo rwhi;
    cbn [base_val] in Hw; rewrite ?U9, ?U22, ?U23 in Hw; unfold LA_G_NL in *; lia.
Qed.

Lemma o5_kag_trans : forall (X : Z -> Prop) m1 m2 m3, kagree SEGS X m1 m2 -> kagree SEGS X m2 m3 -> kagree SEGS X m1 m3.
Proof. intros X m1 m2 m3 K1 K2 a Ha. rewrite (K2 a Ha), (K1 a Ha). reflexivity. Qed.

(* a word of four bytes a run stored, as abytes (Op3K.v u_word4) *)
Lemma o5_word4 : forall (E : env) (m : word -> option byte) r base off e bs,
  region_ok SEGS E m r -> base_val E (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CVal 4 e)) (YP09.r_chunks r) ->
  length bs = 4%nat -> sv_denot E e = Z_to_bv 64 (bytes_le_to_Z bs) ->
  0 <= base + off -> base + off + 4 <= 2 ^ 64 ->
  abytes SEGS m (base + off) bs.
Proof.
  intros E m r base off e bs (_ & _ & _ & HC) Hb Hin Hl He H0 H1.
  rewrite Forall_forall in HC. specialize (HC _ Hin). rewrite Hb in HC.
  apply (abytes_of_word4 m (base + off) (sv_denot E e) bs Hl He H0 H1).
  intros i Hi. destruct (HC i ltac:(cbn; lia)) as (b & Hcb & Hmb). cbn [c_off YP09.c_val cbyte] in Hcb, Hmb.
  injection Hcb as <-. exact Hmb.
Qed.

(* a spill slot a run left, as the frame's slot *)
Lemma o5_slot : forall (E : env) (H : word -> bool) mem r base off e v,
  region_ok SEGS E (mrestrict H mem) r -> base_val E (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mem) (base + off) = Some v.
Proof.
  intros E H mem r base off e v (_ & _ & _ & HC) Hb Hin He Hv.
  rewrite Forall_forall in HC. specialize (HC _ Hin). rewrite Hb in HC.
  apply rdword_of_val_mem; [|exact Hv].
  exact (val_of_chunk_ok SEGS E _ base off 8 e v HC He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

(* the sign extension of a small 32-bit word *)
Lemma o5_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
  intros E n v Hn Hv. apply o5_sv_of_U; [|lia].
  rewrite U_SExt, U_SOff, Hn, unsigned_lit_small by lia. rewrite Z.add_0_r.
  unfold zcanon, M64. change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ 32)) by lia.
  rewrite swrap32_id by lia. apply Z.mod_small. lia.
Qed.

(* a0 on the empty path: mk & -1 *)
Lemma o5_and_ones : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 18446744073709551615)) = Z_to_bv 64 v.
Proof.
  intros E n v Hn Hv. apply o5_sv_of_U; [|lia].
  rewrite U_SAlu, U_SOff, U_SLit, Hn, unsigned_lit_small by lia. rewrite Z.add_0_r. cbn [zalu_raw].
  unfold zcanon, M64. rewrite (Z.mod_small v) by lia.
  change (18446744073709551615 mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* a0 on the byte path: ((b & 1) - 1) & mk *)
Lemma o5_a0 : forall E b v, ew E 37 = Z_to_bv 64 b -> 0 <= b <= 255 -> ew E 34 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 37 0) (SLit 1)) (SLit (-1))) (SOff 34 0)) =
    Z_to_bv 64 (if Z.odd b then 0 else v).
Proof.
  intros E b v Hb Hbr Hv Hvr. apply o5_sv_of_U; [|destruct (Z.odd b); lia].
  rewrite !U_SAlu, !U_SOff, !U_SLit, Hb, Hv, !unsigned_lit_small by lia. rewrite !Z.add_0_r. cbn [zalu_raw].
  unfold zcanon, M64.
  change (1 mod 2 ^ 64) with (Z.ones 1). rewrite (Z.mod_small b) by lia. rewrite Z.land_ones by lia.
  change (2 ^ 1) with 2. rewrite (Z.mod_small (b mod 2)) by (pose proof (Z.mod_pos_bound b 2); lia).
  change (-1 mod 2 ^ 64) with (2 ^ 64 - 1). rewrite (Z.mod_small v) by lia.
  rewrite Zmod_odd. destruct (Z.odd b).
  - change ((1 + (2 ^ 64 - 1)) mod 2 ^ 64) with 0. rewrite Z.land_0_l. reflexivity.
  - change ((0 + (2 ^ 64 - 1)) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* a1 on the byte path: sign(b << 62) & .str.1, by the 256 values of b *)
Definition o5_a1_f (b : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_AND
    (zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_SLL (zcanon b) (zcanon 62))) (zcanon 63)))
    (zcanon 135104)).
Lemma o5_a1_tab : forallb (fun b => Z.eqb (o5_a1_f b) (if Z.testbit b 1 then LA_STR1 else 0))
  (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o5_a1 : forall E b, ew E 37 = Z_to_bv 64 b -> 0 <= b <= 255 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SOff 37 0) (SLit 62)) (SLit 63)) (SLit 135104)) =
    Z_to_bv 64 (if Z.testbit b 1 then LA_STR1 else 0).
Proof.
  intros E b Hb Hbr. apply o5_sv_of_U; [|destruct (Z.testbit b 1); unfold LA_STR1; lia].
  rewrite !U_SAlu, !U_SOff, !U_SLit, Hb, unsigned_lit_small by lia. rewrite Z.add_0_r.
  pose proof (proj1 (forallb_forall _ _) o5_a1_tab b) as Ht.
  assert (Hin : In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia. }
  specialize (Ht Hin). apply Z.eqb_eq in Ht. unfold o5_a1_f in Ht.
  exact Ht.
Qed.

Lemma o5_beqz : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
  intros E n v Hn Hv. rewrite branch_eq_U, U_SOff, U_SLit, Hn, unsigned_lit_small by lia.
  rewrite Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma lf_op5 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 5 i).
Proof.
intros POST i Hi NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HG.
destruct HG as (md & mk & P & N & kbs & mbs & gbs & T3 & b & _ & _ & Hsh & Hcore & Hlr & Hsav & Hhdr & Hfsh & Hslots
  & HN1 & Hb & Hbm & Hcur & HPN & Hjbk & Hblk & Hdata & Hop).
pose proof Hsh as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr).
replace (lf_op_pc 5) with LF_op5 in Hpc by reflexivity.
pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
pose proof Hlr as (R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HB as (HPRE & Hfz & HGX & Hlanul & HMS & _).
destruct (o5_geo cx HB) as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
pose proof (o5_aj_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
pose proof Hblk as (Hmdin & Hmkin & Hmdc & Hmkc & HmdT & HmkT & Hmd16 & Hmk16 & Hmdoff & Hmkoff & Hapmm & Hapmi & Hapki
  & Hramd & Hramk & Hammd & Hammk).
destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Hmdin) as (_ & Hmd4096 & Hmdceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Hmkin) as (_ & Hmk4096 & Hmkceil & _).
change (req_size MD_SIZE) with 8856 in Hmdceil. change (req_size MK_SIZE) with 516 in Hmkceil.
unfold LLVMF_STK in Hceil0.
pose proof Hjbk as (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15).
pose proof Hdata as (Hnl & Hnwf & Hif & Hop0 & Hmis & Hoc & Hmdat & Hmwf & Hmkat & Hkwf & Hare & Hifp & Hgn & Hgw & Hodd
  & Htx & Hla).
pose proof Hcur as (HcP & HcN & q1 & Hq1 & EP1 & EN1).
destruct HPN as (q0 & Hq0 & EP0 & EN0).
set (serr := nk_socket_errno kbs). set (sderr := nk_send_errno kbs).
assert (Hnl' := Hnl). destruct Hnl' as ((Hkab & Hkaw) & Hklen).
assert (VSE : val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_SOCKET_ERRNO) 4 serr).
{ exact (val_mem_u32 SEGS _ LA_G_NL kbs NK_SOCKET_ERRNO Hkab ltac:(unfold NK_SOCKET_ERRNO; lia)
    ltac:(unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia)). }
assert (VSD : val_mem SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_SEND_ERRNO) 4 sderr).
{ exact (val_mem_u32 SEGS _ LA_G_NL kbs NK_SEND_ERRNO Hkab ltac:(unfold NK_SEND_ERRNO; lia)
    ltac:(unfold NK_SEND_ERRNO, NK_SIZE in *; lia)). }
assert (Hserr : 0 <= serr < 2 ^ 31 /\ 0 <= sderr < 2 ^ 31).
{ unfold nlk_wf in Hnwf. subst serr sderr. lia. }
assert (Hcn : 0 < c_n cx) by lia.
pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
  cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hcn) as Hinb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR3 Hinb) as (_ & Hcp4096 & Hcpceil & _).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
  cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ) as (_ & _ & _ & _ & _ & Hwin & _).
unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hmdoff, Hmkoff.
(* the selector byte: 0 when the cursor is empty *)
assert (Hb2 : exists b2z, 0 <= b2z <= 255 /\ (1 <= N - 1 -> val_mem SEGS (rdW W3 (ms_mem ms3)) (P + 1) 1 b2z) /\
                         (N - 1 = 0 -> b2z = 0)).
{ destruct (Z.eq_dec (N - 1) 0) as [E0|E0].
  - exists 0. split; [lia|]. split; [intros; lia | intros; reflexivity].
  - destruct J14 as (Hp0 & Hpl1 & Hpl2).
    assert (Hix : (Z.to_nat (q0 + 1) < length (c_pl cx))%nat) by (unfold c_n in *; lia).
    pose proof (Hpl2 _ Hix) as Hm.
    destruct (nth_error (c_pl cx) (Z.to_nat (q0 + 1))) as [bb|] eqn:Enth; [|apply nth_error_None in Enth; lia].
    exists (bv_unsigned bb). split; [pose proof (bv_unsigned_in_range _ bb) as Hbb; change (bv_modulus 8) with 256 in Hbb; lia|].
    split; [|intros; lia]. intros _.
    replace (P + 1) with (c_p cx + Z.of_nat (Z.to_nat (q0 + 1))) by lia.
    apply val_mem1_of_mbyte'. exact Hm. }
destruct Hb2 as (b2z & Hb2r & Hb2v & Hb20).
assert (HS : st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms3) (o5_extra (N - 1) (P + 1) mk serr sderr b2z))) o5_ss
  (restrict (w_H W3) ms3)).
{ pose proof Hslots as (S18 & S20 & S28 & S30 & SF & SFK & SB1A0 & SODD & SMARK0 & SSTR1 & SB160 & SWA & SB330 & SB2E0
    & SMK & SNMARK & SSHN & SSHX & SSHS & SJT & SG42 & SSHM & SNREQ & SNEXT & SSE & SM & SG40 & SSHB & SF0).
  unfold lf_slot, lf_at in *.
  assert (Wfr : forall o, 0x118 <= o < 0x128 -> writable_at SEGS (rdW W3 (ms_mem ms3)) (lf_sp1 cx + o)).
  { intros o Ho. apply (apresent_writable SEGS). apply Hwin. unfold LLVMF_STK. lia. }
  assert (Wmd0 : forall o, 0 <= o < 12 -> writable_at SEGS (rdW W3 (ms_mem ms3)) (md + o)).
  { intros o Ho. destruct Hmdat as ((_ & Hmw) & Hml). apply Hmw. unfold MD_SIZE in *. lia. }
  assert (Wmd1 : forall o, 8336 <= o < 8340 -> writable_at SEGS (rdW W3 (ms_mem ms3)) (md + o)).
  { intros o Ho. destruct Hmdat as ((_ & Hmw) & Hml). apply Hmw. unfold MD_SIZE in *. lia. }
  assert (Wgn : forall o, 0x22a8 <= o < 0x22ac -> writable_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + 0x40000 + o)).
  { intros o Ho. replace (LA_G_NL + 0x40000 + o) with (LA_G_NL + (0x40000 + o)) by lia. apply Hkaw.
    unfold NK_SIZE in *. lia. }
  apply o5_vm_of_rd in SSTR1, SMK, SSHN, SSHX, SSHS, SG42, SSHM, SNREQ, SNEXT, SSE, HcP, HcN.
  unfold LS_STR1, LS_MK, LS_SH_NREQ, LS_SH_NEXT, LS_SH_SE, LS_GNL42, LS_SH_M, LS_NREQ, LS_NEXT, LS_SE, LS_P, LS_N
    in SSTR1, SMK, SSHN, SSHX, SSHS, SG42, SSHM, SNREQ, SNEXT, SSE, HcP, HcN.
  apply (o5_entry fy ms3 W3 (lf_sp1 cx) md (N - 1) (P + 1) mk serr sderr b2z); first [assumption | lia]. }
remember (Eimg (Ereg (ms_regs ms3) (o5_extra (N - 1) (P + 1) mk serr sderr b2z))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hr. pose proof (u5_range r) as Hr5. subst E. rewrite Eimg_low; [exact (ew_Ereg_nat _ _ n r Hr)|].
  unfold A_TEXT. lia. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (o5_extra (N - 1) (P + 1) mk serr sderr b2z) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low; [exact (ew_Ereg_extra _ _ j)|]. unfold A_TEXT. lia. }
assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = md) by (rewrite (ER 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = LA_G_NL + 0x40000)
  by (rewrite (ER 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (ER 27%nat 27%bv eq_refl), R27; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (N - 1)) by exact (EX 0%nat ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = N - 1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (P + 1)) by exact (EX 1%nat ltac:(lia)).
assert (U33 : bv_unsigned (ew E 33) = P + 1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (paj_run_x (fx := fy) SK B LAWS G_HARNESS HGX 0 []) as RUN.
pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
pose proof HJ as HJ0.
assert (E34 : ew E 34 = Z_to_bv 64 mk) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 serr) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 sderr) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 b2z) by exact (EX 5%nat ltac:(lia)).
assert (KL : Z.of_nat (length kbs) = NK_SIZE) by exact Hklen.
assert (Bmd : md + 8856 <= 2 ^ 64) by lia.
destruct (Z.eq_dec (N - 1) 0) as [HN0 | HN0].
- (* the cursor is empty after the operation byte *)
  assert (SHOK : sh_ok SEGS o5_Bx o5_SH E (rdW W3 (ms_mem ms3))).
  { unfold sh_ok, o5_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    unfold o5_Bx. rewrite !U_SOff, U22, U27. unfold zcanon, M64.
    rewrite !Z.add_0_r, !Z.mod_small by (unfold SHADOW_OFF; lia). replace (8856 - 0) with MD_SIZE by reflexivity.
    split; [exact Hramd|]. intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.max_r in Ha by (unfold MD_SIZE; lia).
    unfold amem_range, SHADOW_OFF, MD_SIZE in *. lia. }
  paj_run_tok RUN HS HJ SHOK o5_span; [o5_awr|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  psrr_branch_tok RUN BR HS SHOK o5_span.
  + paj_run_tok RUN HS HJ SHOK o5_span; [o5_awr|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    pose proof (o5_kag_run E _ _ _ (lf_sp1 cx) md HFrA U9 U22 U23
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) as KA.
    pose proof (o5_kag_run E _ _ _ (lf_sp1 cx) md HFrB U9 U22 U23
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) as KB.
    pose proof (o5_kag_trans _ _ _ _ KA KB) as KX.
    assert (GB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
    pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
    rewrite pa_sigma_mark_quietly, (lv_text HV) in Hms.
    assert (EA : link_text + AF_mark_quietly = MARK_QUIETLY_A) by reflexivity. rewrite EA in Hms.
    assert (KR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs msB) r = getr (ms_regs ms3) r).
    { intros r Hr. apply (o5_reg_keep fy E _ _ _ msB (ms_regs ms3) r HS).
      - assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
          bv_unsigned r = 9 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
          bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
          bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
        destruct Hr' as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|E']]]]]]]]]]]]]];
          (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'; vm_compute; reflexivity.
      - apply ER. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5. lia. }
    assert (R1' : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0xa28))).
    { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs].
      change (sr_get _ 1%bv) with (SOff A_TEXT 4144). rewrite (codeptr_val _ 4144 HEI). reflexivity. }
    assert (A0 : aarg (ms_regs msB) 0 = mk).
    { rewrite ar_aarg0, (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HS). cbn [setpc ss_regs].
      change (sr_get _ 10%bv) with (SAlu ALU_AND (SOff 34 0) (SLit 18446744073709551615)).
      rewrite (o5_and_ones E 34 mk E34 ltac:(lia)). apply unsigned_lit_small. lia. }
    assert (A1 : aarg (ms_regs msB) 1 = 0).
    { rewrite ar_aarg1, (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 11%bv HS). cbn [setpc ss_regs].
      change (sr_get _ 11%bv) with (SLit 0). reflexivity. }
    pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _). cbn [setpc ss_mem ms_mem restrict] in Hrs.
    apply Forall_cons_iff in Hrs as (RGf & Hrs). apply Forall_cons_iff in Hrs as (RGm0 & Hrs).
    apply Forall_cons_iff in Hrs as (RGm1 & Hrs). apply Forall_cons_iff in Hrs as (RGg & _).
    assert (Bs22 : base_val E (Some 22%nat) = md) by exact U22.
    assert (Bs23 : base_val E (Some 23%nat) = LA_G_NL + 0x40000) by exact U23.
    assert (Bs9 : base_val E (Some 9%nat) = lf_sp1 cx) by exact U9.
    assert (A1b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4)).
    { replace (md + MD_SOCKET_ERRNO) with (md + 0) by (unfold MD_SOCKET_ERRNO; lia).
      apply (o5_word4 E _ _ md 0 (SExt true 32 (SOff 35 0)) _ RGm0 Bs22).
      - cbn. right; right; left. reflexivity.
      - apply lf_slice_length; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia.
      - rewrite (o5_sext E 35 serr E35 ltac:(lia)). reflexivity.
      - lia.
      - lia. }
    assert (A2b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4)).
    { apply (o5_word4 E _ _ md MD_SEND_ERRNO (SExt true 32 (SOff 36 0)) _ RGm0 Bs22).
      - cbn. right; left. reflexivity.
      - apply lf_slice_length; unfold NK_SEND_ERRNO, NK_SIZE in *; lia.
      - rewrite (o5_sext E 36 sderr E36 ltac:(lia)). reflexivity.
      - unfold MD_SEND_ERRNO; lia.
      - unfold MD_SEND_ERRNO; lia. }
    assert (A3b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_NEXT) lf_z4).
    { apply (o5_word4 E _ _ md MD_NEXT (SLit 0) _ RGm0 Bs22).
      - cbn. left. reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold MD_NEXT; lia.
      - unfold MD_NEXT; lia. }
    assert (A4b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_N_REQ) lf_z4).
    { apply (o5_word4 E _ _ md MD_N_REQ (SLit 0) _ RGm1 Bs22).
      - cbn. left. reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold MD_N_REQ; lia.
      - unfold MD_N_REQ; lia. }
    assert (A5b : abytes SEGS (rdW W3 (ms_mem msB)) (LA_G_NL + NK_N_SENT) lf_z4).
    { replace (LA_G_NL + NK_N_SENT) with ((LA_G_NL + 0x40000) + 8872) by (unfold NK_N_SENT; lia).
      apply (o5_word4 E _ _ (LA_G_NL + 0x40000) 8872 (SLit 0) _ RGg Bs23).
      - cbn. left. reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold LA_G_NL; lia.
      - unfold LA_G_NL; lia. }
    assert (Hcur' : lf_cur cx W3 msB (P + 1) (N - 1)).
    { unfold lf_cur, lf_slot, lf_at, LS_P, LS_N. split; [|split].
      - apply (o5_slot E (w_H W3) (ms_mem msB) _ (lf_sp1 cx) 0x118 (SOff 33 0) (P + 1) RGf Bs9).
        + cbn. repeat (first [left; reflexivity | right]).
        + cbn [sv_denot]. rewrite E33, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
        + lia.
      - apply (o5_slot E (w_H W3) (ms_mem msB) _ (lf_sp1 cx) 0x120 (SOff 32 0) (N - 1) RGf Bs9).
        + cbn. repeat (first [left; reflexivity | right]).
        + cbn [sv_denot]. rewrite E32, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
        + lia.
      - exists (q0 + 1). lia. }
    apply (o5_at_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS HV MT_LE MT_OK
      MQO MQA CM CR POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3 msB md4 _ (P + 1) (N - 1) None
      Hi NEXT HB Hfx HJ0 Hfr Hcore Hlr Hsav Hhdr Hfsh Hslots Hjbk Hblk Hdata Hop HJ Hms KR R1' ltac:(right; exact A0)
      ltac:(left; split; [exact A1 | reflexivity]) KX).
    * intros a Ha Hr. rewrite !(Z.mod_small a) in Ha by exact Hr. unfold lf_cur_fp. exact Ha.
    * exact GB.
    * exact Fd.
    * exact Fs.
    * exact A1b.
    * exact A2b.
    * exact A3b.
    * exact A4b.
    * exact A5b.
    * exact Hcur'.
  + exfalso. rewrite (o5_beqz E 32 (N - 1) E32 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. exact (Hc HN0).
- (* the cursor holds the selector byte at P + 1 *)
  assert (HN2 : 1 <= N - 1) by lia.
  pose proof (Hb2v HN2) as Vb2.
  assert (HSn : st_ok_pi (fx := fy) SEGS pa_val E (mkSS LF_op5 sr_atoms (o5_in :: o5_rs) None o5_facts)
                  (restrict (w_H W3) ms3)).
  { apply (st_ok_pi_add_region E o5_ss (restrict (w_H W3) ms3) o5_in HS).
    - vm_compute. reflexivity.
    - unfold region_ok, o5_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (P + 1) 0 1 (SOff 37 0) b2z).
      + cbn [sv_denot]. rewrite E37. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      + lia.
      + rewrite Z.add_0_r. exact Vb2.
    - apply all_disjoint_of_extents. unfold o5_rs, o5_in, o5_fr, o5_md0, o5_md1, o5_gn, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U33, ?U9, ?U22, ?U23.
      cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
      pose proof HPRE as (_ & _ & _ & _ & Hinp0 & _).
      destruct Hinp0 as [(Hn0 & _) | (_ & Hinp0)]; [lia|].
      assert (Hne : (c_p cx, c_n cx) <> (md, MD_SIZE)).
      { intros Ec. rewrite Ec in Hinp0. exact (Hmdc Hinp0). }
      pose proof (sep_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) md MD_SIZE HAR3 Hinb Hmdin Hne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hrq in D. change (req_size MD_SIZE) with 8856 in D.
      pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR3 Hinb) as Hoff.
      rewrite Hrq in Hoff. unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
      unfold LA_G_NL, MD_SIZE in *. repeat split.
      all: unfold zdisj; cbn [YP09.r_base YP09.r_lo YP09.r_hi o5_fr o5_md0 o5_md1 o5_gn base_val fst snd];
           rewrite ?U9, ?U22, ?U23; unfold LA_G_NL in *; lia. }
  assert (HP1' : c_p cx <= P + 1 < c_p cx + c_n cx) by lia.
  assert (SHOKn : sh_ok SEGS o5_Bx o5_SHn E (rdW W3 (ms_mem ms3))).
  { unfold sh_ok, o5_SHn. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
      unfold o5_Bx. rewrite !U_SOff, U22, U27. unfold zcanon, M64.
      rewrite !Z.add_0_r, !Z.mod_small by (unfold SHADOW_OFF; lia). replace (8856 - 0) with MD_SIZE by reflexivity.
      split; [exact Hramd|]. intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.max_r in Ha by (unfold MD_SIZE; lia).
      unfold amem_range, SHADOW_OFF, MD_SIZE in *. lia.
    - unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
      unfold o5_Bx. rewrite !U_SOff, U33, U27. unfold zcanon, M64.
      rewrite !Z.add_0_r, !Z.mod_small by (unfold SHADOW_OFF; lia). replace (1 - 0) with 1 by reflexivity.
      split.
      + rewrite ard_aview. apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) (P + 1) 1 HAR3 Hinb).
        all: try rewrite Hrq; lia.
      + intros a Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR3 Hinb) as (_ & _ & _ & Hcpapp & _).
        rewrite Hrq in Hcpapp. pose proof (ASAN_CEIL_range) as (CR1 & _).
        cbn [Z.max] in Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Hcpapp. unfold ASAN_CEIL, SHADOW_OFF in *.
        clear - Hcpapp Ha CR1 HP1' . lia. }
  paj_run_tok RUN HSn HJ SHOKn o5_span; [o5_awr|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  psrr_branch_tok RUN BR HSn SHOKn o5_span.
  + exfalso. rewrite (o5_beqz E 32 (N - 1) E32 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. exact (HN0 Hc).
  + paj_run_tok RUN HSn HJ SHOKn o5_span; [o5_awr|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    lazymatch type of HSn with st_ok _ ?E2 _ _ => set (E' := E2) in * end.
    assert (EW : forall n, (n < 512)%nat -> ew E' n = ew E n)
      by (intros n Hn; unfold E'; repeat (rewrite ew_ewset_other by lia); reflexivity).
    assert (HEI' : img_env pa_val A_LIM E')
      by (unfold E'; repeat (apply img_env_ewset_hi; [|unfold A_LIM; lia]); exact HEI).
    assert (U9' : bv_unsigned (ew E' 9) = lf_sp1 cx) by (rewrite EW by lia; exact U9).
    assert (U22' : bv_unsigned (ew E' 22) = md) by (rewrite EW by lia; exact U22).
    assert (U23' : bv_unsigned (ew E' 23) = LA_G_NL + 0x40000) by (rewrite EW by lia; exact U23).
    assert (E32' : ew E' 32 = Z_to_bv 64 (N - 1)) by (rewrite EW by lia; exact E32).
    assert (E33' : ew E' 33 = Z_to_bv 64 (P + 1)) by (rewrite EW by lia; exact E33).
    assert (E34' : ew E' 34 = Z_to_bv 64 mk) by (rewrite EW by lia; exact E34).
    assert (E35' : ew E' 35 = Z_to_bv 64 serr) by (rewrite EW by lia; exact E35).
    assert (E36' : ew E' 36 = Z_to_bv 64 sderr) by (rewrite EW by lia; exact E36).
    assert (E37' : ew E' 37 = Z_to_bv 64 b2z) by (rewrite EW by lia; exact E37).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    pose proof (o5_kag_run E _ _ _ (lf_sp1 cx) md HFrA U9 U22 U23
      ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) as KA.
    assert (KB : kagree SEGS (fun a => (lf_sp1 cx + 0x118 <= a mod 2 ^ 64 < lf_sp1 cx + 0x128) \/
                                     lf_mb_rng md (a mod 2 ^ 64)) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msB))).
    { first
        [ exact (o5_kag_run E' _ _ _ (lf_sp1 cx) md HFrB U9' U22' U23'
            ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr))
        | exact (o5_kag_run E _ _ _ (lf_sp1 cx) md HFrB U9 U22 U23
            ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) ]. }
    pose proof (o5_kag_trans _ _ _ _ KA KB) as KX.
    assert (GB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
    pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HSn eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
    rewrite pa_sigma_mark_quietly, (lv_text HV) in Hms.
    assert (EA : link_text + AF_mark_quietly = MARK_QUIETLY_A) by reflexivity. rewrite EA in Hms.
    assert (KR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs msB) r = getr (ms_regs ms3) r).
    { intros r Hr. apply (o5_reg_keep fy E' _ _ _ msB (ms_regs ms3) r HSn).
      - assert (Hr' : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/
          bv_unsigned r = 9 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
          bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
          bv_unsigned r = 27) by (unfold acallee_saved in Hr; lia).
        destruct Hr' as [E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|[E'r|E'r]]]]]]]]]]]]]];
          (replace r with (Z_to_bv 5 (bv_unsigned r)) by apply Z_to_bv_bv_unsigned); rewrite E'r; vm_compute; reflexivity.
      - pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
        rewrite EW by lia. apply ER. lia. }
    assert (R1' : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0xa28))).
    { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HSn). cbn [setpc ss_regs].
      change (sr_get _ 1%bv) with (SOff A_TEXT 4144). rewrite (codeptr_val _ 4144 HEI'). reflexivity. }
    assert (A0 : aarg (ms_regs msB) 0 = if Z.odd b2z then 0 else mk).
    { rewrite ar_aarg0, (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HSn). cbn [setpc ss_regs].
      change (sr_get _ 10%bv) with
        (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 37 0) (SLit 1)) (SLit (-1))) (SOff 34 0)).
      rewrite (o5_a0 E' b2z mk E37' ltac:(lia) E34' ltac:(lia)). apply unsigned_lit_small. destruct (Z.odd b2z); lia. }
    assert (A1 : aarg (ms_regs msB) 1 = if Z.testbit b2z 1 then LA_STR1 else 0).
    { rewrite ar_aarg1, (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 11%bv HSn). cbn [setpc ss_regs].
      change (sr_get _ 11%bv) with
        (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL (SOff 37 0) (SLit 62)) (SLit 63)) (SLit 135104)).
      rewrite (o5_a1 E' b2z E37' ltac:(lia)). apply unsigned_lit_small. destruct (Z.testbit b2z 1); unfold LA_STR1; lia. }
    pose proof (st_ok_mem_ok SEGS E' _ _ HSn) as (_ & Hrs & _). cbn [setpc ss_mem ms_mem restrict] in Hrs.
    apply Forall_cons_iff in Hrs as (RGi & Hrs). apply Forall_cons_iff in Hrs as (RGf & Hrs).
    apply Forall_cons_iff in Hrs as (RGm0 & Hrs). apply Forall_cons_iff in Hrs as (RGm1 & Hrs).
    apply Forall_cons_iff in Hrs as (RGg & _).
    assert (Bs22 : base_val E' (Some 22%nat) = md) by exact U22'.
    assert (Bs23 : base_val E' (Some 23%nat) = LA_G_NL + 0x40000) by exact U23'.
    assert (Bs9 : base_val E' (Some 9%nat) = lf_sp1 cx) by exact U9'.
    assert (A1b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4)).
    { replace (md + MD_SOCKET_ERRNO) with (md + 0) by (unfold MD_SOCKET_ERRNO; lia).
      apply (o5_word4 E' _ _ md 0 (SExt true 32 (SOff 35 0)) _ RGm0 Bs22).
      - cbn. right; right; left. reflexivity.
      - apply lf_slice_length; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia.
      - rewrite (o5_sext E' 35 serr E35' ltac:(lia)). reflexivity.
      - lia.
      - lia. }
    assert (A2b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4)).
    { apply (o5_word4 E' _ _ md MD_SEND_ERRNO (SExt true 32 (SOff 36 0)) _ RGm0 Bs22).
      - cbn. right; left. reflexivity.
      - apply lf_slice_length; unfold NK_SEND_ERRNO, NK_SIZE in *; lia.
      - rewrite (o5_sext E' 36 sderr E36' ltac:(lia)). reflexivity.
      - unfold MD_SEND_ERRNO; lia.
      - unfold MD_SEND_ERRNO; lia. }
    assert (A3b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_NEXT) lf_z4).
    { apply (o5_word4 E' _ _ md MD_NEXT (SLit 0) _ RGm0 Bs22).
      - cbn. left. reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold MD_NEXT; lia.
      - unfold MD_NEXT; lia. }
    assert (A4b : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_N_REQ) lf_z4).
    { apply (o5_word4 E' _ _ md MD_N_REQ (SLit 0) _ RGm1 Bs22).
      - cbn. left. reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold MD_N_REQ; lia.
      - unfold MD_N_REQ; lia. }
    assert (A5b : abytes SEGS (rdW W3 (ms_mem msB)) (LA_G_NL + NK_N_SENT) lf_z4).
    { replace (LA_G_NL + NK_N_SENT) with ((LA_G_NL + 0x40000) + 8872) by (unfold NK_N_SENT; lia).
      apply (o5_word4 E' _ _ (LA_G_NL + 0x40000) 8872 (SLit 0) _ RGg Bs23).
      - cbn. left. reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold LA_G_NL; lia.
      - unfold LA_G_NL; lia. }
    assert (Hcur' : lf_cur cx W3 msB (P + 2) (N - 2)).
    { unfold lf_cur, lf_slot, lf_at, LS_P, LS_N. split; [|split].
      - apply (o5_slot E' (w_H W3) (ms_mem msB) _ (lf_sp1 cx) 0x118 (SOff 33 1) (P + 2) RGf Bs9).
        + cbn. repeat (first [left; reflexivity | right]).
        + cbn [sv_denot]. rewrite E33', unsigned_lit_small by lia. f_equal. lia.
        + lia.
      - apply (o5_slot E' (w_H W3) (ms_mem msB) _ (lf_sp1 cx) 0x120 (SOff 32 (-1)) (N - 2) RGf Bs9).
        + cbn. repeat (first [left; reflexivity | right]).
        + cbn [sv_denot]. rewrite E32', unsigned_lit_small by lia. f_equal. lia.
        + lia.
      - exists (q0 + 2). lia. }
    set (nm := if Z.testbit b2z 1 then Some (@nil byte) else None).
    apply (o5_at_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS HV MT_LE MT_OK
      MQO MQA CM CR POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3 msB md4
      (fun a => (lf_sp1 cx + 0x118 <= a mod 2 ^ 64 < lf_sp1 cx + 0x128) \/ lf_mb_rng md (a mod 2 ^ 64)) (P + 2) (N - 2) nm
      Hi NEXT HB Hfx HJ0 Hfr Hcore Hlr Hsav Hhdr Hfsh Hslots Hjbk Hblk Hdata Hop HJ Hms KR R1').
    * rewrite A0. destruct (Z.odd b2z); [left | right]; reflexivity.
    * rewrite A1. unfold nm. destruct (Z.testbit b2z 1); [right | left]; split; reflexivity.
    * exact KX.
    * intros a Ha Hr. rewrite !(Z.mod_small a) in Ha by exact Hr. unfold lf_cur_fp. exact Ha.
    * exact GB.
    * exact Fd.
    * exact Fs.
    * exact A1b.
    * exact A2b.
    * exact A3b.
    * exact A4b.
    * exact A5b.
    * exact Hcur'.
Qed.

End b.
End a.
