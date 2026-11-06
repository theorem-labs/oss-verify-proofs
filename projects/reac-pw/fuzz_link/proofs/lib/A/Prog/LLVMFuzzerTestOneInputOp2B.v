(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 676 of its 725 lines of code are new or changed and 1283 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   from kernel's return (Op2K.v o2_k_inv, +0xad4) through model_begin's five stores (the shape of op_refused's,
   Op5.v: the spill slots hold the model's shadow addresses, the checks are the SH entry of the model block) and the two tests
   of the name (listing (internal path) (internal record, sha256 e84d6f0c6974)):

     +0xad4 .. +0xb30   m + 0 := g_nl.socket_errno, m + 4 := g_nl.send_errno, m + 8 := 0, m + 8336 := 0,
                        g_nl.n_sent := 0, s2 := F + 0x160 (the slot LS_B160)
     +0xb34             s7 := -22
     +0xb38  beqz s4    NULL name -> +0xc9c
     +0xb3c .. +0xb48   the instrumented check of the name's first byte (the SH entry of the name)
     +0xb4c  lbu, beqz  empty name -> +0xc9c; otherwise +0xb54

   o2_kb : forall POST i, FROM POST (o2_q_inv i) -> FROM POST (o2_n_inv i) -> FROM POST (o2_k_inv i).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c LLVMFuzzerTestOneInputOp5 LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2K LLVMFuzzerTestOneInputOp2Cut
  LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputMdl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the spill slots the stretch reads: F + 0x160 (s10 + 0x140) and model_begin's eight *)
Definition o2b_fr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x68 0xe8 0x68 0x68
    [o5_c8 0x68 (SOff 26 0x140); o5_c8 0xa0 (o5_shx 8336); o5_c8 0xa8 (o5_shx 8); o5_c8 0xb0 (o5_shx 4);
     o5_c8 0xc0 (SOff 23 0x2000); o5_c8 0xc8 (o5_shx 0); o5_c8 0xd0 (SOff 22 8336); o5_c8 0xd8 (SOff 22 8);
     o5_c8 0xe0 (SOff 22 4)].
(* the name's first byte (atom 37) *)
Definition o2b_nm : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition o2b_rs (nn : bool) : smem :=
  if nn then [o2b_fr; o5_md0; o5_md1; o5_gn; o2b_nm] else [o2b_fr; o5_md0; o5_md1; o5_gn].
Definition o2b_facts (nn : bool) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (22%nat, mkAF 4096 (2 ^ 47 - 8856) 4); (23%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (27%nat, mkAF o5_RSB o5_RSB 0); (20%nat, if nn then mkAF 0x10000 (2 ^ 47 - 1) 0 else mkAF 0 0 0);
           (37%nat, mkAF 0 255 0)] [] [].
Definition o2b_ss (nn : bool) : sstate := mkSS LO2_kret sr_atoms (o2b_rs nn) None (o2b_facts nn).
Definition o2b_SH (nn : bool) : list shent := if nn then [mkSHE 22 0 8856; mkSHE 20 0 1] else [mkSHE 22 0 8856].
(* the extra atoms 32 .. 37: three unused, g_nl's two errno words (o5_gn's 35, 36), the name's first byte *)
Definition o2b_extra (serr sderr b0 : Z) : list word :=
  [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 serr; Z_to_bv 64 sderr; Z_to_bv 64 b0].

Ltac o2b_awr1 U9 U22 U23 Hmdin Hmdc md :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  first
    [ rewrite U9 in Ha; left; split; [left; unfold LLVMF_STK; lia | lia]
    | rewrite U22 in Ha; left; split; [right; right; left; exists md, MD_SIZE; split; [exact Hmdin|];
        split; [exact Hmdc|]; change (req_size MD_SIZE) with 8856; lia | lia]
    | rewrite U23 in Ha; right; left; unfold inG, G_HARNESS; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
        unfold LA_G_NL, NK_SIZE in *; lia
    | lia ].

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

(* the symbolic state holds at kernel's return *)
Lemma o2b_entry : forall (fy : YK11.FPState) (ms : machine_state) (W : world SEGS) sp1 md wa s serr sderr b0
    (nn : bool),
  ms_pc_val ms = w64 (BASE + LO2_kret) -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = @fp_regs fy -> ms_fcsr ms = @fp_csr fy ->
  getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 9 = w64 sp1 ->
  getr (ms_regs ms) 22 = w64 md -> getr (ms_regs ms) 23 = w64 (LA_G_NL + 0x40000) ->
  getr (ms_regs ms) 26 = w64 wa -> getr (ms_regs ms) 27 = w64 SHADOW_OFF -> getr (ms_regs ms) 20 = w64 s ->
  2 ^ 46 <= sp1 -> sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= md <= 2 ^ 47 - 8856 -> md mod 16 = 0 -> md + 8856 <= sp1 -> (md + 8856 <= 0x10000 \/ 0x654000 <= md) ->
  0 <= wa -> wa + 0x140 < 2 ^ 64 ->
  0 <= serr < 2 ^ 32 -> 0 <= sderr < 2 ^ 32 -> 0 <= b0 <= 255 ->
  (nn = false -> s = 0) ->
  (nn = true -> 0x10000 <= s < 0x654000 /\ (s + 1 <= LA_G_NL + 0x4020c \/ LA_G_NL + 0x422ac <= s) /\
     val_mem SEGS (rdW W (ms_mem ms)) s 1 b0) ->
  (forall o, 0 <= o < 12 -> writable_at SEGS (rdW W (ms_mem ms)) (md + o)) ->
  (forall o, 8336 <= o < 8340 -> writable_at SEGS (rdW W (ms_mem ms)) (md + o)) ->
  (forall o, 0x22a8 <= o < 0x22ac -> writable_at SEGS (rdW W (ms_mem ms)) (LA_G_NL + 0x40000 + o)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0x68) 8 (wa + 0x140) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xa0) 8 (shadow_of_addr SHADOW_OFF (md + MD_N_REQ)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xa8) 8 (shadow_of_addr SHADOW_OFF (md + MD_NEXT)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xb0) 8 (shadow_of_addr SHADOW_OFF (md + MD_SEND_ERRNO)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xc0) 8 (LA_G_NL + 0x42000) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xc8) 8 (shadow_of_addr SHADOW_OFF md) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xd0) 8 (md + MD_N_REQ) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xd8) 8 (md + MD_NEXT) ->
  val_mem SEGS (rdW W (ms_mem ms)) (sp1 + 0xe0) 8 (md + MD_SEND_ERRNO) ->
  val_mem SEGS (rdW W (ms_mem ms)) (LA_G_NL + NK_SOCKET_ERRNO) 4 serr ->
  val_mem SEGS (rdW W (ms_mem ms)) (LA_G_NL + NK_SEND_ERRNO) 4 sderr ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms) (o2b_extra serr sderr b0))) (o2b_ss nn) (restrict (w_H W) ms).
Proof.
  intros fy ms W sp1 md wa s serr sderr b0 nn Hpc Hresv Hsvc Hrom Hfrg Hfcsr R2 R9 R22 R23 R26 R27 R20
    Hs1a Hs1b Hs1c Hmda Hmdb Hmds1 Hmdoff Hwa0 Hwa1 Hse Hsd Hb0 Hnn0 Hnn1 W1 W2 W3
    V68 VA0 VA8 VB0 VC0 VC8 VD0 VD8 VE0 VSE VSD.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hms : restrict (w_H W) ms =
    @mkst fy (ms_regs ms) (Z_to_bv 64 (BASE + LO2_kret)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
  { destruct ms; cbn in *; subst; reflexivity. }
  rewrite Hms.
  set (E := Eimg (Ereg (ms_regs ms) (o2b_extra serr sderr b0))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms) (o2b_extra serr sderr b0)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms) r).
  { intros n r Hr. pose proof (u5_range r) as Hr5. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
    unfold A_TEXT. lia. }
  assert (E2 : ew E 2 = w64 sp1) by (rewrite (ER 2%nat 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = w64 sp1) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E20 : ew E 20 = w64 s) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (E22 : ew E 22 = w64 md) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = w64 (LA_G_NL + 0x40000)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = w64 wa) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 SHADOW_OFF) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  assert (E35 : ew E 35 = Z_to_bv 64 serr) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 sderr) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
  assert (E37 : ew E 37 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = md) by (rewrite E22; unfold w64; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = LA_G_NL + 0x40000)
    by (rewrite E23; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
  assert (U27 : bv_unsigned (ew E 27) = o5_RSB) by (rewrite E27; unfold w64, o5_RSB, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = b0) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = s).
  { rewrite E20; unfold w64; apply unsigned_lit_small. destruct nn; [destruct (Hnn1 eq_refl) as (Hs & _); lia|].
    rewrite (Hnn0 eq_refl). lia. }
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
  assert (RFR : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) o2b_fr).
  { unfold region_ok, o2b_fr, o5_c8.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E.
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 0x68 8 (SOff 26 0x140) (wa + 0x140));
        [exact (OFF 26%nat wa 0x140 E26 ltac:(lia) ltac:(lia)) | zside | zside | exact V68].
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
        [exact (OFF 22%nat md 4 E22 ltac:(lia) ltac:(lia)) | unfold MD_SEND_ERRNO; zside | zside | exact VE0]. }
  assert (RM0 : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) o5_md0).
  { unfold region_ok, o5_md0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (W1 o Ho) | constructor]. }
  assert (RM1 : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) o5_md1).
  { unfold region_ok, o5_md1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (W2 o Ho) | constructor]. }
  assert (RGN : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) o5_gn).
  { unfold region_ok, o5_gn. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite U23. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; exact (W3 o Ho)|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (LA_G_NL + 0x40000) 0x20c 4 (SOff 35 0) serr);
        [exact (LIT 35%nat serr E35 ltac:(lia)) | zside | zside |].
      replace (LA_G_NL + 0x40000 + 0x20c) with (LA_G_NL + NK_SOCKET_ERRNO) by (unfold NK_SOCKET_ERRNO; lia). exact VSE.
    * apply (chunk_ok_val SEGS E _ (LA_G_NL + 0x40000) 0x210 4 (SOff 36 0) sderr);
        [exact (LIT 36%nat sderr E36 ltac:(lia)) | zside | zside |].
      replace (LA_G_NL + 0x40000 + 0x210) with (LA_G_NL + NK_SEND_ERRNO) by (unfold NK_SEND_ERRNO; lia). exact VSD. }
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - destruct nn; vm_compute; reflexivity.
  - destruct nn; cbn [o2b_rs ss_mem o2b_ss].
    + destruct (Hnn1 eq_refl) as (Hs & Hsg & Vs).
      repeat apply Forall_cons; try apply Forall_nil; try assumption.
      unfold region_ok, o2b_nm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      fold E. rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ s 0 1 (SOff 37 0) b0); [exact (LIT 37%nat b0 E37 ltac:(lia)) | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vs.
    + repeat apply Forall_cons; try apply Forall_nil; assumption.
  - apply pairwise_disjoint_of_extents. destruct nn.
    + destruct (Hnn1 eq_refl) as (Hs & Hsg & Vs).
      cbn [o2b_rs ss_mem o2b_ss map]. unfold o2b_fr, o5_md0, o5_md1, o5_gn, o2b_nm, extent_of_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U22, U23, U20.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LA_G_NL in *. repeat split; lia.
    + cbn [o2b_rs ss_mem o2b_ss map]. unfold o2b_fr, o5_md0, o5_md1, o5_gn, extent_of_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U22, U23.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LA_G_NL. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    destruct nn; cbn [o2b_facts o2b_ss ss_facts f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; fold E;
      rewrite U2, U9, U22, U23, U27, U20, U37; rewrite ?Z.pow_0_r, ?Z.mod_1_r; unfold o5_RSB, LA_G_NL in *.
    + destruct (Hnn1 eq_refl) as (Hs & _). repeat match goal with |- _ /\ _ => split end; first [exact I | lia | idtac].
    + rewrite (Hnn0 eq_refl). repeat match goal with |- _ /\ _ => split end; first [exact I | lia | idtac].
Qed.

(* the stretch's static write obligation: the model's four counters (a block this call allocated) and g_nl's
   n_sent (a byte of G); the spill region and the name write nothing *)
Ltac o2b_awr :=
  lazymatch goal with
  | U9 : bv_unsigned (ew ?E 9) = _, U22 : bv_unsigned (ew ?E 22) = _, U23 : bv_unsigned (ew ?E 23) = _,
    Hmdin : In (?md, MD_SIZE) (ablocks _ _ _), Hmdc : ~ In (?md, MD_SIZE) (ablocks _ _ _) |- _ =>
    cbn [ss_mem o2b_ss o2b_rs];
    repeat (apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val o2b_fr o5_md0 o5_md1 o5_gn o2b_nm];
                                  o2b_awr1 U9 U22 U23 Hmdin Hmdc md | ]);
    apply awr_ok_x_nil
  end.

(* the run's frame as a kagree, its windows inside model_begin's ranges *)
Lemma o2b_kag_run : forall E rs (m m' : word -> option byte) sp1 md,
  frame_of E rs m m' ->
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 22) = md -> bv_unsigned (ew E 23) = LA_G_NL + 0x40000 ->
  (forall r, In r rs -> In (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)
     [(Some 9%nat, 0x68, 0x68); (Some 22%nat, 0, 12); (Some 22%nat, 8336, 8340); (Some 23%nat, 8872, 8876);
      (Some 20%nat, 0, 0)]) ->
  kagree SEGS (fun a => lf_mb_rng md (a mod 2 ^ 64)) m m'.
Proof.
  intros E rs m m' sp1 md HF U9 U22 U23 HW a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr & Hw). apply Ha. rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw.
  change (bv_modulus 64) with (2 ^ 64) in Hw.
  pose proof (HW r Hr) as HWr. destruct r as [rb rlo rhi rwlo rwhi rcs]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in *.
  unfold lf_mb_rng, MD_N_REQ, NK_N_SENT.
  cbn [In] in HWr. destruct HWr as [E1 | [E1 | [E1 | [E1 | [E1 | []]]]]]; injection E1 as E2 E3 E4; subst rb rwlo rwhi;
    cbn [base_val] in Hw; rewrite ?U9, ?U22, ?U23 in Hw; unfold LA_G_NL in *; lia.
Qed.

(* the cut's memory after model_begin's five stores (Op3K.v u_kret) *)
Lemma o2b_mem_after : forall i cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 msX mdX md mk P N kbs mbs gbs T3,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 -> lf_slots cx md mk fp W3 ms3 ->
  lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) -> nk_next kbs = 0 ->
  kagree SEGS (fun a => lf_mb_rng md (a mod 2 ^ 64)) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
  m_fds mdX = m_fds md3 -> m_fs mdX = m_fs md3 ->
  abytes SEGS (rdW W3 (ms_mem msX)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4) ->
  abytes SEGS (rdW W3 (ms_mem msX)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4) ->
  abytes SEGS (rdW W3 (ms_mem msX)) (md + MD_NEXT) lf_z4 ->
  abytes SEGS (rdW W3 (ms_mem msX)) (md + MD_N_REQ) lf_z4 ->
  abytes SEGS (rdW W3 (ms_mem msX)) (LA_G_NL + NK_N_SENT) lf_z4 ->
  lf_saved cx W3 msX /\ lf_header cx fp W3 msX /\ lf_fshadow cx fp W3 msX LF_SH0 /\ lf_slots cx md mk fp W3 msX /\
  lf_cur cx W3 msX P N /\
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 msX mdX T3
    [(md, MD_SIZE); (mk, MK_SIZE)] /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem msX)) /\
  lf_data cx md mk (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs) gbs (rdW W3 (ms_mem msX)) /\
  nk_n_sent (lf_kbs_mb kbs) = 0 /\ nk_opened (lf_kbs_mb kbs) = nk_opened kbs /\
  md_reqs (lf_mbs_mb kbs mbs) = [] /\ md_kstate (lf_mbs_mb kbs mbs) (lf_kbs_mb kbs) = nk_kstate (lf_kbs_mb kbs).
Proof.
  intros i cx fp k2 ly3 S3 W3 ms3 md3 msX mdX md mk P N kbs mbs gbs T3 HB HJ Hfr Hsv Hhd Hfs Hsl Hcur Hjbk Hblk Hdat
    Hnx KA GA Fd Fs A1 A2 A3 A4 A5.
  set (X := fun a => lf_mb_rng md (a mod 2 ^ 64)) in *.
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & _).
  pose proof (fun a (HXa : X a) => u_mb_notX SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    LAWS TB HSEGS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk HXa) as NX.
  assert (N1 : forall a, lf_saved_fp cx a -> ~ X a) by (intros a Ha HXa; destruct (NX a HXa) as (Z1 & _); exact (Z1 Ha)).
  assert (N2 : forall a, lf_header_fp cx fp a -> ~ X a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & Z1 & _); exact (Z1 Ha)).
  assert (N3 : forall a, lf_fshadow_fp cx fp 112 a -> ~ X a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & _ & Z1 & _); exact (Z1 Ha)).
  assert (N4 : forall a, lf_slots_fp cx a -> ~ X a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & _ & _ & Z1 & _); exact (Z1 Ha)).
  assert (N5 : forall a, lf_cur_fp cx a -> ~ X a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & _ & _ & _ & Z1 & _); exact (Z1 Ha)).
  assert (N6 : forall a, lf_jbk_fp MS la_nul cx T3 a -> ~ X a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & _ & _ & _ & _ & Z1 & _); exact (Z1 Ha)).
  assert (N7 : forall a, lf_blocks_fp md mk a -> ~ X a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & _ & _ & _ & _ & _ & Z1 & _); exact (Z1 Ha)).
  assert (ND : forall a, lf_data_fp md mk a -> X a -> lf_mb_rng md a)
    by (intros a Ha HXa; destruct (NX a HXa) as (_ & _ & _ & _ & _ & _ & _ & Z1); exact (Z1 Ha)).
  clear NX.
  destruct (lf_data_mb X _ _ cx md mk kbs mbs gbs HSEGS KA (wcarry_on_grows _ _ _ GA) ND Bmt Bkt Bap A1 A2 A3 A4 A5
    Hdat) as (Hdat' & Hns' & Hnr' & Hop' & _).
  pose proof Hdat as (Dk & _ & _ & _ & _ & _ & Dmd & _).
  pose proof Dk as (_ & KL). pose proof Dmd as (_ & ML).
  pose proof (lf_mbs_mb_sock kbs mbs KL ML) as Msock. pose proof (lf_mbs_mb_send kbs mbs KL ML) as Msend.
  pose proof (lf_mbs_mb_next kbs mbs KL ML) as Mnext.
  pose proof (lf_kbs_mb_fields kbs KL) as (_ & _ & _ & _ & _ & Knx & Knc & Ken & Kso & Kse).
  split; [exact (lf_saved_keep X cx W3 ms3 W3 msX KA N1 Hsv)|].
  split; [exact (lf_header_keep X cx fp W3 ms3 W3 msX KA N2 Hhd)|].
  split; [exact (lf_fshadow_keep X cx fp W3 ms3 W3 msX LF_SH0 KA N3 Hfs)|].
  split; [exact (lf_slots_keep X cx md mk fp W3 ms3 W3 msX KA N4 Hsl)|].
  split; [exact (lf_cur_keep X cx W3 ms3 W3 msX P N KA N5 Hcur)|].
  split; [exact (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msX mdX KA Fd Fs N6 Hjbk)|].
  split; [exact (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA N7 Hblk)|].
  split; [exact Hdat'|]. split; [exact Hns'|]. split; [exact Hop'|].
  split; [unfold md_reqs; rewrite Hnr'; reflexivity|].
  unfold md_kstate, nk_kstate. rewrite Mnext, Knx, Hnx, Msock, Msend, Kso, Kse. reflexivity.
Qed.

Lemma o2_kb : forall POST i,
  FROM POST (o2_q_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (o2_n_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (o2_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HQ HN cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HK.
  destruct HK as (md & mk & P & N & s & nm & kbs & mbs & gbs & T3 & Hsh & R20 & Hnm & HM & Hnx).
  destruct HM as (Hi & Hcore & Hlr & Hsav & Hhdr & Hfsh & Hslots & Hcur & Hjbk & Hblk & Hdata & Hop).
  pose proof Hsh as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hlr as (R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & Hfz & HGX & Hlanul & HMS & _).
  destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
  pose proof (o5_aj_AR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
  pose proof Hblk as (Hmdin & Hmkin & Hmdc & Hmkc & HmdT & HmkT & Hmd16 & Hmk16 & Hmdoff & Hmkoff & Hapmm & Hapmi & Hapki
    & Hramd & Hramk & Hammd & Hammk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Hmdin) as (_ & Hmd4096 & Hmdceil & _).
  change (req_size MD_SIZE) with 8856 in Hmdceil.
  unfold LLVMF_STK in Hceil0.
  pose proof Hjbk as (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15).
  pose proof Hdata as (Hnl & Hnwf & Hif & Hop0 & Hmis & Hoc & Hmdat & Hmwf & Hmkat & Hkwf & Hare & Hifp & Hgn & Hgw & Hodd
    & Htx & Hla).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
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
  unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hmdoff.
  pose proof Hslots as (S18 & S20 & S28 & S30 & SF & SFK & SB1A0 & SODD & SMARK0 & SSTR1 & SB160 & SWA & SB330 & SB2E0
    & SMK & SNMARK & SSHN & SSHX & SSHS & SJT & SG42 & SSHM & SNREQ & SNEXT & SSE & SM & SG40 & SSHB & SF0).
  unfold lf_slot, lf_at in SB160, SSHN, SSHX, SSHS, SG42, SSHM, SNREQ, SNEXT, SSE.
  apply o5_vm_of_rd in SB160, SSHN, SSHX, SSHS, SG42, SSHM, SNREQ, SNEXT, SSE.
  unfold LS_B160, LS_SH_NREQ, LS_SH_NEXT, LS_SH_SE, LS_GNL42, LS_SH_M, LS_NREQ, LS_NEXT, LS_SE
    in SB160, SSHN, SSHX, SSHS, SG42, SSHM, SNREQ, SNEXT, SSE.
  assert (Wmd0 : forall o, 0 <= o < 12 -> writable_at SEGS (rdW W3 (ms_mem ms3)) (md + o)).
  { intros o Ho. destruct Hmdat as ((_ & Hmw) & Hml). apply Hmw. unfold MD_SIZE in *. lia. }
  assert (Wmd1 : forall o, 8336 <= o < 8340 -> writable_at SEGS (rdW W3 (ms_mem ms3)) (md + o)).
  { intros o Ho. destruct Hmdat as ((_ & Hmw) & Hml). apply Hmw. unfold MD_SIZE in *. lia. }
  assert (Wgn : forall o, 0x22a8 <= o < 0x22ac -> writable_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + 0x40000 + o)).
  { intros o Ho. replace (LA_G_NL + 0x40000 + o) with (LA_G_NL + (0x40000 + o)) by lia. apply Hkaw.
    unfold NK_SIZE in *. lia. }
  assert (V68 : val_mem SEGS (rdW W3 (ms_mem ms3)) (lf_sp1 cx + 0x68) 8 ((lf_F cx fp + LO_WA) + 0x140)).
  { replace ((lf_F cx fp + LO_WA) + 0x140) with (lf_F cx fp + LO_B160) by (unfold LO_WA, LO_B160; lia). exact SB160. }
  rewrite (lf_shape_eta fy LO2_kret ms3 Hsh).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  pose proof HJ as HJ0.
  (* the cut +0xc9c of a NULL or empty name, from the state a run ends in *)
  assert (CLOSEQ : forall (msB : machine_state) mdB nm',
    ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msB) mdB k2 ->
    lf_shape fy LO2_q msB ->
    (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
       getr (ms_regs msB) r = getr (ms_regs ms3) r) ->
    getr (ms_regs msB) 23 = w64 (- E_INVAL) ->
    w_name s nm' -> (nm' = None \/ nm' = Some []) ->
    kagree SEGS (fun a => lf_mb_rng md (a mod 2 ^ 64)) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
    m_fds mdB = m_fds md3 -> m_fs mdB = m_fs md3 ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4) ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4) ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_NEXT) lf_z4 ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_N_REQ) lf_z4 ->
    abytes SEGS (rdW W3 (ms_mem msB)) (LA_G_NL + NK_N_SENT) lf_z4 ->
    SRr SEGS W3 (mkCfg msB mdB) (POST cx)).
  { intros msB mdB nm' HJB HshB KR R23B Hnm' Hnm0' KX GX FdB FsB A1 A2 A3 A4 A5.
    destruct (o2b_mem_after i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB md mk P N kbs mbs gbs T3 HB HJ0 Hfr Hsav Hhdr Hfsh
      Hslots Hcur Hjbk Hblk Hdata Hnx KX GX FdB FsB A1 A2 A3 A4 A5)
      as (Hsv' & Hhd' & Hfs' & Hsl' & Hcur' & Hjbk' & Hblk' & Hdat' & Hns' & Hop' & REQ0 & KSEQ).
    apply (HQ cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJB Hfr).
    exists md, mk, P, N, s, nm', (lf_kbs_mb kbs), (lf_mbs_mb kbs mbs), gbs, T3.
    assert (MM : o2_MM nm' (lf_kbs_mb kbs) gbs = Mres (- E_INVAL) (mk_names gbs) [] (nk_kstate (lf_kbs_mb kbs)))
      by (destruct Hnm0' as [-> | ->]; reflexivity).
    pose proof Hdat' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Dmm) & _).
    split; [exact HshB|].
    split; [rewrite (KR 20%bv ltac:(sel_inbv)); exact R20|]. split; [exact Hnm'|].
    split; [rewrite (KR 22%bv ltac:(sel_inbv)); exact R22|]. split; [rewrite (KR 26%bv ltac:(sel_inbv)); exact R26|].
    split.
    { split; [exact Hi|]. split.
      { unfold lf_core. rewrite !KR by sel_inbv. exact Hcore. }
      split; [unfold o2_kregs; rewrite !KR by sel_inbv; repeat split; assumption|].
      split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|]. split; [exact Hcur'|].
      split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact (lf_data_nm_of _ _ _ _ _ _ _ Hdat')|].
      split; [rewrite Hop'; exact Hop | exact Hns']. }
    rewrite MM. cbn [m_rc m_reqs m_marks]. split; [exact R23B|]. split; [exact REQ0 | symmetry; exact Dmm]. }
  (* the cut +0xb54 of a name that is not empty *)
  assert (CLOSEN : forall (msB : machine_state) mdB t',
    ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msB) mdB k2 ->
    lf_shape fy LO2_n msB ->
    (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
       getr (ms_regs msB) r = getr (ms_regs ms3) r) ->
    getr (ms_regs msB) 18 = w64 (lf_F cx fp + LO_B160) ->
    w_name s (Some t') -> (0 < length t')%nat ->
    kagree SEGS (fun a => lf_mb_rng md (a mod 2 ^ 64)) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
    m_fds mdB = m_fds md3 -> m_fs mdB = m_fs md3 ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4) ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4) ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_NEXT) lf_z4 ->
    abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_N_REQ) lf_z4 ->
    abytes SEGS (rdW W3 (ms_mem msB)) (LA_G_NL + NK_N_SENT) lf_z4 ->
    SRr SEGS W3 (mkCfg msB mdB) (POST cx)).
  { intros msB mdB t' HJB HshB KR R18B Hnm' Hlt KX GX FdB FsB A1 A2 A3 A4 A5.
    destruct (o2b_mem_after i cx fp k2 ly3 S3 W3 ms3 md3 msB mdB md mk P N kbs mbs gbs T3 HB HJ0 Hfr Hsav Hhdr Hfsh
      Hslots Hcur Hjbk Hblk Hdata Hnx KX GX FdB FsB A1 A2 A3 A4 A5)
      as (Hsv' & Hhd' & Hfs' & Hsl' & Hcur' & Hjbk' & Hblk' & Hdat' & Hns' & Hop' & REQ0 & KSEQ).
    apply (HN cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJB Hfr).
    exists md, mk, P, N, s, t', (lf_kbs_mb kbs), (lf_mbs_mb kbs mbs), gbs, T3.
    pose proof Hdat' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dare & _).
    split; [exact HshB|].
    split; [rewrite (KR 20%bv ltac:(sel_inbv)); exact R20|]. split; [exact Hnm'|]. split; [exact Hlt|].
    split; [exact R18B|]. split; [rewrite (KR 21%bv ltac:(sel_inbv)); exact R21|].
    split; [rewrite (KR 22%bv ltac:(sel_inbv)); exact R22|]. split; [rewrite (KR 26%bv ltac:(sel_inbv)); exact R26|].
    split.
    { split; [exact Hi|]. split.
      { unfold lf_core. rewrite !KR by sel_inbv. exact Hcore. }
      split; [unfold o2_kregs; rewrite !KR by sel_inbv; repeat split; assumption|].
      split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|]. split; [exact Hcur'|].
      split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact (lf_data_nm_of _ _ _ _ _ _ _ Hdat')|].
      split; [rewrite Hop'; exact Hop | exact Hns']. }
    split; [exact Dare|]. split; [exact REQ0 | exact KSEQ]. }
  destruct Hnm as [(Hs0 & Hnm0) | Hnn].
  - (* NULL: beqz s4 -> +0xc9c *)
    subst s nm.
    assert (HS : st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms3) (o2b_extra serr sderr 0))) (o2b_ss false)
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_kret)) (ms_mem ms3) (seg_rom SEGS)))).
    { apply (o2b_entry fy (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_kret)) (ms_mem ms3) (seg_rom SEGS)) W3
        (lf_sp1 cx) md (lf_F cx fp + LO_WA) 0 serr sderr 0 false);
        cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst];
        first [reflexivity | assumption | unfold LO_WA, LLVMF_STK, LF_MFRAME in *; lia | intros; discriminate | idtac].
    }
    set (E := Eimg (Ereg (ms_regs ms3) (o2b_extra serr sderr 0))) in HS.
    assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
    assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
    { intros n r Hr. pose proof (u5_range r) as Hr5. subst E. rewrite Eimg_low; [exact (ew_Ereg_nat _ _ n r Hr)|].
      unfold A_TEXT. lia. }
    assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
    assert (U22 : bv_unsigned (ew E 22) = md) by (rewrite (ER 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
    assert (U23 : bv_unsigned (ew E 23) = LA_G_NL + 0x40000)
      by (rewrite (ER 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
    assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
      by (rewrite (ER 27%nat 27%bv eq_refl), R27; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
    assert (SHOK : sh_ok SEGS o5_Bx (o2b_SH false) E (rdW W3 (ms_mem ms3))).
    { unfold sh_ok, o2b_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
      unfold o5_Bx. rewrite !U_SOff, U22, U27. unfold zcanon, M64.
      rewrite !Z.add_0_r, !Z.mod_small by (unfold SHADOW_OFF; lia). replace (8856 - 0) with MD_SIZE by reflexivity.
      split; [exact Hramd|]. intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.max_r in Ha by (unfold MD_SIZE; lia).
      unfold amem_range, SHADOW_OFF, MD_SIZE in *. lia. }
    paj_run_tok RUN HS HJ SHOK o5_span; [o2b_awr|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    psrr_branch_tok RUN BR HS SHOK o5_span.
    + (* s4 = 0: +0xc9c *)
      paj_run_to_tok RUNTO HS HJ SHOK o5_span LO2_q; [o2b_awr|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ => set (E' := E2) in *; set (ssB := ss2) in * end.
      assert (EW : forall n, (n < 512)%nat -> ew E' n = ew E n)
        by (intros n Hn; unfold E'; repeat (rewrite ew_ewset_other by lia); reflexivity).
      assert (U9' : bv_unsigned (ew E' 9) = lf_sp1 cx) by (rewrite EW by lia; exact U9).
      assert (U22' : bv_unsigned (ew E' 22) = md) by (rewrite EW by lia; exact U22).
      assert (U23' : bv_unsigned (ew E' 23) = LA_G_NL + 0x40000) by (rewrite EW by lia; exact U23).
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
      assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
      pose proof (o2b_kag_run E _ _ _ (lf_sp1 cx) md HFrA U9 U22 U23
        ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) as KA.
      assert (KB : kagree SEGS (fun a => lf_mb_rng md (a mod 2 ^ 64)) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msB))).
      { first
          [ exact (o2b_kag_run E' _ _ _ (lf_sp1 cx) md HFrB U9' U22' U23'
              ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr))
          | exact (o2b_kag_run E _ _ _ (lf_sp1 cx) md HFrB U9 U22 U23
              ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) ]. }
      pose proof (o5_kag_trans _ _ _ _ KA KB) as KX.
      assert (GX : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
      assert (RG : forall k r, nth_error (ss_mem ssB) k = Some r -> region_ok SEGS E' (rdW W3 (ms_mem msB)) r)
        by (intros k r Hk; exact (st_ok_pi_region_nth E' ssB (restrict (w_H W3) msB) k r HS Hk)).
      assert (B22 : base_val E' (Some 22%nat) = md) by exact U22'.
      assert (B23 : base_val E' (Some 23%nat) = LA_G_NL + 0x40000) by exact U23'.
      pose proof Hdata as (Dk & _ & _ & _ & _ & _ & Dmd & _). pose proof Dk as (_ & KL).
      assert (E35' : ew E' 35 = Z_to_bv 64 serr) by (rewrite EW by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra _ _ 3)).
      assert (E36' : ew E' 36 = Z_to_bv 64 sderr) by (rewrite EW by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra _ _ 4)).
      assert (Bmd : md + 8856 <= 2 ^ 64) by lia.
      eapply (CLOSEQ msB md4 None HJ (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)).
      * intros r Hr. apply (lf_reg_atom fy W3 E' ssB msB (ms_regs ms3) r HS).
        { split; [intros n Hn; rewrite EW by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                  rewrite !ew_Ereg_lt by lia; reflexivity | unfold E'; reflexivity]. }
        repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr.
      * rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 23%bv HS).
        replace (sr_get (ss_regs ssB) 23%bv) with (SLit 18446744073709551594) by (vm_compute; reflexivity).
        apply bv_eq. reflexivity.
      * left. split; reflexivity.
      * left. reflexivity.
      * exact KX.
      * exact GX.
      * exact Fd.
      * exact Fs.
      * replace (md + MD_SOCKET_ERRNO) with (md + 0) by (unfold MD_SOCKET_ERRNO; lia).
        apply (o5_word4 E' _ _ md 0 (SExt true 32 (SOff 35 0)) _ (RG 1%nat _ eq_refl) B22).
        -- cbn. right; right; left. reflexivity.
        -- apply lf_slice_length; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia.
        -- rewrite (o5_sext E' 35 serr E35' ltac:(lia)). reflexivity.
        -- lia.
        -- lia.
      * apply (o5_word4 E' _ _ md MD_SEND_ERRNO (SExt true 32 (SOff 36 0)) _ (RG 1%nat _ eq_refl) B22).
        -- cbn. right; left. reflexivity.
        -- apply lf_slice_length; unfold NK_SEND_ERRNO, NK_SIZE in *; lia.
        -- rewrite (o5_sext E' 36 sderr E36' ltac:(lia)). reflexivity.
        -- unfold MD_SEND_ERRNO; lia.
        -- unfold MD_SEND_ERRNO; lia.
      * apply (o5_word4 E' _ _ md MD_NEXT (SLit 0) _ (RG 1%nat _ eq_refl) B22).
        -- cbn. left. reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- unfold MD_NEXT; lia.
        -- unfold MD_NEXT; lia.
      * apply (o5_word4 E' _ _ md MD_N_REQ (SLit 0) _ (RG 2%nat _ eq_refl) B22).
        -- cbn. left. reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- unfold MD_N_REQ; lia.
        -- unfold MD_N_REQ; lia.
      * replace (LA_G_NL + NK_N_SENT) with ((LA_G_NL + 0x40000) + 8872) by (unfold NK_N_SENT; lia).
        apply (o5_word4 E' _ _ (LA_G_NL + 0x40000) 8872 (SLit 0) _ (RG 3%nat _ eq_refl) B23).
        -- cbn. left. reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- unfold LA_G_NL; lia.
        -- unfold LA_G_NL; lia.
    + (* s4 <> 0: refuted *)
      exfalso. rewrite (o5_beqz E 20 0 ltac:(rewrite (ER 20%nat 20%bv eq_refl); exact R20) ltac:(lia)) in Hc.
      discriminate Hc.
  - (* a name: its first byte b0 *)
    assert (Hw0 : exists t, nm = Some t) by (destruct Hnn as [(k & _ & _ & ->) | (j & _ & _ & ->)]; eexists; reflexivity).
    destruct Hw0 as (t & ->).
    assert (Hw : w_name s (Some t)) by (right; exact Hnn).
    assert (HK0 : alloc_ceiling <= spZ (ms_regs ms3) - 0).
    { unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. pose proof alloc_ceiling_lt. lia. }
    destruct (o2_name_rt B TB HSEGS ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) 0 s t HAR3 J13 Hgn HK0 Hw)
      as (Hac & Hrt & Hs16 & Hl11 & Hloc).
    pose proof Hrt as (Hs0 & _ & _ & Hsra & _).
    set (b0 := bv_unsigned (nth 0 (t ++ [zb 0]) (zb 0))).
    assert (Vb0 : val_mem SEGS (rdW W3 (ms_mem ms3)) s 1 b0).
    { apply val_mem1_of_mbyte'. destruct Hac as ((_ & _ & Hab) & _).
      pose proof (Hab 0%nat ltac:(rewrite length_app; cbn; lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
      destruct t; reflexivity. }
    assert (Hb0 : 0 <= b0 <= 255) by (pose proof (bv_unsigned_in_range _ (nth 0 (t ++ [zb 0]) (zb 0))) as Hr;
      change (bv_modulus 8) with 256 in Hr; unfold b0; lia).
    assert (Hb00 : b0 = 0 <-> t = []).
    { destruct Hac as (_ & Hnz). unfold b0. destruct t as [|c t'].
      - split; [reflexivity|]. intros _. reflexivity.
      - cbn [app nth]. split; [|discriminate]. intros Hc. exfalso. apply Hnz. left.
        apply bv_eq. rewrite Hc. reflexivity. }
    assert (Hsb : 0x10000 <= s < 0x654000) by (clear - Hs16 Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia).
    assert (Hsg : s + 1 <= LA_G_NL + 0x4020c \/ LA_G_NL + 0x422ac <= s)
      by (clear - Hs16 Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia).
    assert (HS : st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms3) (o2b_extra serr sderr b0))) (o2b_ss true)
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_kret)) (ms_mem ms3) (seg_rom SEGS)))).
    { assert (A1 : 2 ^ 46 <= lf_sp1 cx /\ lf_sp1 cx <= 2 ^ 47 /\ lf_sp1 cx mod 32 = 0)
        by (clear - Hsp146 Hsp1r H470 Hsp132; lia).
      assert (A2 : 4096 <= md <= 2 ^ 47 - 8856 /\ md + 8856 <= lf_sp1 cx).
      { pose proof alloc_ceiling_lt as CL. clear - Hmd4096 Hmdceil CL Hceil0 Hsp1r. lia. }
      assert (A3 : 0 <= lf_F cx fp + LO_WA /\ lf_F cx fp + LO_WA + 0x140 < 2 ^ 64).
      { pose proof alloc_ceiling_lt as CL. clear - F4 Fc CL. unfold LO_WA. lia. }
      assert (A4 : 0 <= serr < 2 ^ 32 /\ 0 <= sderr < 2 ^ 32) by (clear - Hserr; lia).
      destruct A1 as (A1a & A1b & A1c). destruct A2 as (A2a & A2b). destruct A3 as (A3a & A3b). destruct A4 as (A4a & A4b).
      exact (o2b_entry fy (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_kret)) (ms_mem ms3) (seg_rom SEGS)) W3
        (lf_sp1 cx) md (lf_F cx fp + LO_WA) s serr sderr b0 true eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        R2 R9 R22 R23 R26 R27 R20 A1a A1b A1c A2a Hmd16 A2b Hmdoff A3a A3b A4a A4b Hb0
        (fun H => ltac:(discriminate H)) (fun _ => conj Hsb (conj Hsg Vb0)) Wmd0 Wmd1 Wgn V68 SSHN SSHX SSHS SG42 SSHM
        SNREQ SNEXT SSE VSE VSD). }
    set (E := Eimg (Ereg (ms_regs ms3) (o2b_extra serr sderr b0))) in HS.
    assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
    assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
    { intros n r Hr. pose proof (u5_range r) as Hr5. subst E. rewrite Eimg_low; [exact (ew_Ereg_nat _ _ n r Hr)|].
      unfold A_TEXT. lia. }
    assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
    assert (U20 : bv_unsigned (ew E 20) = s)
      by (rewrite (ER 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; clear - Hsb; lia).
    assert (U22 : bv_unsigned (ew E 22) = md) by (rewrite (ER 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
    assert (U23 : bv_unsigned (ew E 23) = LA_G_NL + 0x40000)
      by (rewrite (ER 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; unfold LA_G_NL; lia).
    assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
      by (rewrite (ER 27%nat 27%bv eq_refl), R27; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
    assert (SHOK : sh_ok SEGS o5_Bx (o2b_SH true) E (rdW W3 (ms_mem ms3))).
    { unfold sh_ok, o2b_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
        unfold o5_Bx. rewrite !U_SOff, U22, U27. unfold zcanon, M64.
        rewrite !Z.add_0_r, !Z.mod_small by (unfold SHADOW_OFF; lia). replace (8856 - 0) with MD_SIZE by reflexivity.
        split; [exact Hramd|]. intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.max_r in Ha by (unfold MD_SIZE; lia).
        unfold amem_range, SHADOW_OFF, MD_SIZE in *. lia.
      - unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
        unfold o5_Bx. rewrite !U_SOff, U20, U27. unfold zcanon, M64.
        rewrite !Z.add_0_r, !Z.mod_small by (clear - Hsb; unfold SHADOW_OFF; lia).
        replace (1 - 0) with 1 by reflexivity.
        split; [try rewrite <- ard_aview; apply (md_ra_sub _ s (Z.of_nat (length t) + 1)); [exact Hsra | clear; lia | clear; lia]|].
        intros a Ha. cbn [Z.max] in Ha. clear - Ha Hsb. unfold SHADOW_OFF in *. lia. }
    paj_run_tok RUN HS HJ SHOK o5_span; [o2b_awr|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    assert (E37 : ew E 37 = Z_to_bv 64 b0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra _ _ 5)).
    lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => set (EA := E1) in * end.
    assert (EWA : forall n, (n < 512)%nat -> ew EA n = ew E n)
      by (intros n Hn; unfold EA; repeat (rewrite ew_ewset_other by lia); reflexivity).
    assert (E37A : ew EA 37 = Z_to_bv 64 b0) by (rewrite EWA by lia; exact E37).
    assert (U9A : bv_unsigned (ew EA 9) = lf_sp1 cx) by (rewrite EWA by lia; exact U9).
    assert (U22A : bv_unsigned (ew EA 22) = md) by (rewrite EWA by lia; exact U22).
    assert (U23A : bv_unsigned (ew EA 23) = LA_G_NL + 0x40000) by (rewrite EWA by lia; exact U23).
    psrr_branch_tok RUN BR HS SHOK o5_span.
    all: rewrite (o5_beqz EA 37 b0 E37A ltac:(lia)) in Hc.
    2: (paj_run_to_tok RUNTO HS HJ SHOK o5_span LO2_n; [o2b_awr|]).
    1: (paj_run_to_tok RUNTO HS HJ SHOK o5_span LO2_q; [o2b_awr|]).
    all: rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    all: lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 _ => set (E' := E2) in *; set (ssB := ss2) in * end.
    all: assert (EW : forall n, (n < 512)%nat -> ew E' n = ew E n)
        by (intros n Hn; unfold E'; repeat (rewrite ew_ewset_other by lia); try (rewrite EWA by lia); reflexivity).
    all: assert (U9' : bv_unsigned (ew E' 9) = lf_sp1 cx) by (rewrite EW by lia; exact U9).
    all: assert (U22' : bv_unsigned (ew E' 22) = md) by (rewrite EW by lia; exact U22).
    all: assert (U23' : bv_unsigned (ew E' 23) = LA_G_NL + 0x40000) by (rewrite EW by lia; exact U23).
    all: lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    all: assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    all: assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    all: pose proof (o2b_kag_run E _ _ _ (lf_sp1 cx) md HFrA U9 U22 U23
        ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) as KA.
    all: assert (KB : kagree SEGS (fun a => lf_mb_rng md (a mod 2 ^ 64)) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msB)))
      by (first
          [ exact (o2b_kag_run E' _ _ _ (lf_sp1 cx) md HFrB U9' U22' U23'
              ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr))
          | exact (o2b_kag_run E _ _ _ (lf_sp1 cx) md HFrB U9 U22 U23
              ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; tauto|]); destruct Hr)) ]).
    all: pose proof (o5_kag_trans _ _ _ _ KA KB) as KX.
    all: assert (GX : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
    all: assert (RG : forall k r, nth_error (ss_mem ssB) k = Some r -> region_ok SEGS E' (rdW W3 (ms_mem msB)) r)
        by (intros k r Hk; exact (st_ok_pi_region_nth E' ssB (restrict (w_H W3) msB) k r HS Hk)).
    all: assert (B22 : base_val E' (Some 22%nat) = md) by exact U22'.
    all: assert (B23 : base_val E' (Some 23%nat) = LA_G_NL + 0x40000) by exact U23'.
    all: pose proof Hdata as (Dk & _ & _ & _ & _ & _ & Dmd & _).
    all: pose proof Dk as (_ & KL).
    all: assert (E35' : ew E' 35 = Z_to_bv 64 serr) by (rewrite EW by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra _ _ 3)).
    all: assert (E36' : ew E' 36 = Z_to_bv 64 sderr) by (rewrite EW by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        exact (ew_Ereg_extra _ _ 4)).
    all: assert (Bmd : md + 8856 <= 2 ^ 64) by lia.
    all: assert (A1 : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4)).
    all: try (replace (md + MD_SOCKET_ERRNO) with (md + 0) by (unfold MD_SOCKET_ERRNO; lia);
        apply (o5_word4 E' _ _ md 0 (SExt true 32 (SOff 35 0)) _ (RG 1%nat _ eq_refl) B22);
        [ cbn; right; right; left; reflexivity
        | apply lf_slice_length; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia
        | rewrite (o5_sext E' 35 serr E35' ltac:(lia)); reflexivity | lia | lia ]).
    all: assert (A2 : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4))
      by (apply (o5_word4 E' _ _ md MD_SEND_ERRNO (SExt true 32 (SOff 36 0)) _ (RG 1%nat _ eq_refl) B22);
        [ cbn; right; left; reflexivity
        | apply lf_slice_length; unfold NK_SEND_ERRNO, NK_SIZE in *; lia
        | rewrite (o5_sext E' 36 sderr E36' ltac:(lia)); reflexivity | unfold MD_SEND_ERRNO; lia | unfold MD_SEND_ERRNO; lia ]).
    all: assert (A3 : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_NEXT) lf_z4)
      by (apply (o5_word4 E' _ _ md MD_NEXT (SLit 0) _ (RG 1%nat _ eq_refl) B22);
        [ cbn; left; reflexivity | reflexivity | reflexivity | unfold MD_NEXT; lia | unfold MD_NEXT; lia ]).
    all: assert (A4 : abytes SEGS (rdW W3 (ms_mem msB)) (md + MD_N_REQ) lf_z4)
      by (apply (o5_word4 E' _ _ md MD_N_REQ (SLit 0) _ (RG 2%nat _ eq_refl) B22);
        [ cbn; left; reflexivity | reflexivity | reflexivity | unfold MD_N_REQ; lia | unfold MD_N_REQ; lia ]).
    all: assert (A5 : abytes SEGS (rdW W3 (ms_mem msB)) (LA_G_NL + NK_N_SENT) lf_z4)
      by (replace (LA_G_NL + NK_N_SENT) with ((LA_G_NL + 0x40000) + 8872) by (unfold NK_N_SENT; lia);
        apply (o5_word4 E' _ _ (LA_G_NL + 0x40000) 8872 (SLit 0) _ (RG 3%nat _ eq_refl) B23);
        [ cbn; left; reflexivity | reflexivity | reflexivity | unfold LA_G_NL; lia | unfold LA_G_NL; lia ]).
    all: assert (KR : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv;
        27%bv] -> getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; apply (lf_reg_atom fy W3 E' ssB msB (ms_regs ms3) r HS);
        [ split; [intros n Hn; rewrite EW by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                  rewrite !ew_Ereg_lt by lia; reflexivity | unfold E'; reflexivity]
        | repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr ]).
    + (* b0 = 0: the empty name, +0xc9c *)
      apply Z.eqb_eq in Hc. assert (Ht : t = []) by (apply Hb00; exact Hc). subst t.
      apply (CLOSEQ msB md4 (Some []) HJ (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)
        ltac:(intros r Hr; apply KR; repeat (destruct Hr as [<- | Hr]; [sel_inbv|]); destruct Hr));
        [ | exact Hw | right; reflexivity | exact KX | exact GX | exact Fd | exact Fs | exact A1 | exact A2 | exact A3
          | exact A4 | exact A5 ].
      rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 23%bv HS).
      replace (sr_get (ss_regs ssB) 23%bv) with (SLit 18446744073709551594) by (vm_compute; reflexivity).
      apply bv_eq. reflexivity.
    + (* b0 <> 0: +0xb54 *)
      apply Z.eqb_neq in Hc.
      apply (CLOSEN msB md4 t HJ (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl) KR);
        [ | exact Hw | | exact KX | exact GX | exact Fd | exact Fs | exact A1 | exact A2 | exact A3 | exact A4 | exact A5 ].
      * rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msB 18%bv HS).
        replace (sr_get (ss_regs ssB) 18%bv) with (SOff 26 320) by (vm_compute; reflexivity).
        cbn [sv_denot]. rewrite EW by lia. rewrite (ER 26%nat 26%bv eq_refl), R26. unfold w64.
        rewrite unsigned_lit_small by (pose proof alloc_ceiling_lt; unfold LO_WA; lia). f_equal. unfold LO_WA, LO_B160. lia.
      * destruct t; [exfalso; apply Hc; apply Hb00; reflexivity | cbn; lia].
Qed.

End a.
