(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 363 of its 413 lines of code are new or changed and 354 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: model_begin's five stores (+0xdb4 .. +0xe18)
   and s5 := kc, s11 := ac (+0xe04, +0xe08), from the cut r_k_inv to the cut r_b_inv at +0xe1c. The stores reach
   the model through its spill slots (s6 holds the name), so the runner's state holds the model's address as atom
   35. The stretch's facts are op_unmark's (Op3K.v: u_sh_rg, u_gnl_rg, u_gns_rg, u_mb_notX, u_word4) and
   Mb.v's lf_data_mb.
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
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputArmK
  LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputOp0Cut LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the runner's state at +0xdb4: the registers, four more atoms (32: the shadow byte of m, 33 / 34: g_nl's two
   errnos, 35: m), and the regions the stretch reads and writes *)
Definition b_slot_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xa0 0xf0 0xa0 0xa0
    [YP09.mkChunk 0xa0 (CVal 8 (SOff 32 1042)); YP09.mkChunk 0xa8 (CVal 8 (SOff 32 1));
     YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 23 8192));
     YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xd0 (CVal 8 (SOff 35 8336));
     YP09.mkChunk 0xd8 (CVal 8 (SOff 35 8)); YP09.mkChunk 0xe0 (CVal 8 (SOff 35 4));
     YP09.mkChunk 0xe8 (CVal 8 (SOff 35 0))].
Definition b_md0_rg : YP09.region := YP09.mkRegion (Some 35%nat) 0 12 0 12 [].
Definition b_mdnr_rg : YP09.region := YP09.mkRegion (Some 35%nat) 8336 8340 8336 8340 [].
Definition b_rgs : smem := [b_slot_rg; u_sh_rg; b_md0_rg; b_mdnr_rg; u_gnl_rg; u_gns_rg].
Definition b_facts : facts :=
  mkFacts [(23%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition b_ss : sstate := mkSS LR_kret sr_atoms b_rgs None b_facts.
Definition b_extra (md : Z) (kbs : list byte) : list word :=
  [Z_to_bv 64 (shadow_of_addr SHADOW_OFF md); Z_to_bv 64 (nk_socket_errno kbs); Z_to_bv 64 (nk_send_errno kbs);
   Z_to_bv 64 md].

(* a register a stretch left as `x & 0xff` of its entry value *)
Lemma b_and255 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 255)) = Z_to_bv 64 v.
Proof.
  intros E n v H Hv. apply bv_eq. rewrite (unsigned_lit_small v) by lia.
  change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 255)))) with (U E (SAlu ALU_AND (SOff n 0) (SLit 255))).
  rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

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
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the runner's entry state at +0xdb4 holds at an r_k_inv cut *)
Lemma b_entry : forall (fy : YK11.FPState) i cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 md mk P N kbs mbs gbs T3
    s kc ac,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  r_regs cx md fp i s kc ac ms3 ->
  r_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 ->
  st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms3) (b_extra md kbs))) b_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_kret)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
  intros fy i cx fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 s kc ac HB HJ Hreg HU.
  destruct HU as (Hi & Hcore & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof Hblk as (Bmd & Bmk & _ & _ & _ & _ & Bm16 & Bk16 & Bmt & Bkt & Bap & _ & _ & Bram & Brak & Bamm & Bamk).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4096 & Bmceil & Bmapp & Bmpres & _).
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & Dare & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  pose proof Hsl as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17
    & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29).
  set (E := Eimg (Ereg (ms_regs ms3) (b_extra md kbs))).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (b_extra md kbs) (Z_to_bv 64 0)).
  { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E23 : ew E 23 = Z_to_bv 64 (LA_G_NL + 0x40000)) by (rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
  assert (E32 : ew E 32 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF md)) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_socket_errno kbs)) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (nk_send_errno kbs)) by exact (EX 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = Z_to_bv 64 md) by exact (EX 3%nat ltac:(lia)).
  unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *. unfold MD_SIZE in *.
  assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc); rewrite Hc;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  assert (Hdiv1 : forall c, 0 <= c < 8 -> (md + c) / 8 = md / 8).
  { intros c Hc. pose proof (Z.div_mod md 8 ltac:(lia)) as D. rewrite Hmd8, Z.add_0_r in D.
    rewrite D. replace (8 * (md / 8) + c) with (c + md / 8 * 8) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia. }
  assert (Hdiv8 : forall k, (md + 8 * k) / 8 = md / 8 + k).
  { intros k. replace (md + 8 * k) with (md + k * 8) by lia. apply Z.div_add. lia. }
  assert (Hm64 : 0 <= md /\ md + 8856 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in *; lia).
  assert (Hsh64 : 0 <= SHADOW_OFF + md / 8 /\ SHADOW_OFF + md / 8 + 1107 <= 2 ^ 64)
    by (split; [unfold SHADOW_OFF; pose proof (Z.div_pos md 8); lia | unfold SHADOW_OFF;
        pose proof (Z.div_le_upper_bound md 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia]).
  assert (Hshm : shadow_of_addr SHADOW_OFF md = SHADOW_OFF + md / 8) by reflexivity.
  rewrite restrict_mkst_fx. unfold b_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold b_rgs, b_slot_rg, u_sh_rg, b_md0_rg, b_mdnr_rg, u_gnl_rg, u_gns_rg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + (* the spill slots at s1 *)
      rewrite (u_base E 9 (lf_sp1 cx) E9) by (unfold LLVMF_STK in *; lia).
      split; [unfold LLVMF_STK in *; lia|]. split; [unfold LLVMF_STK in *; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (u_slot_chunk E cx W3 ms3 0xa0 _ (shadow_of_addr SHADOW_OFF (md + MD_N_REQ))); [|exact S17].
        rewrite (lf_sv_off E 32 _ 1042 E32) by lia. f_equal. unfold shadow_of_addr, MD_N_REQ.
        replace (md + 8336) with (md + 8 * 1042) by lia. rewrite (Hdiv8 1042). lia.
      * apply (u_slot_chunk E cx W3 ms3 0xa8 _ (shadow_of_addr SHADOW_OFF (md + MD_NEXT))); [|exact S18].
        rewrite (lf_sv_off E 32 _ 1 E32) by lia. f_equal. unfold shadow_of_addr, MD_NEXT.
        replace (md + 8) with (md + 8 * 1) by lia. rewrite (Hdiv8 1). lia.
      * apply (u_slot_chunk E cx W3 ms3 0xb0 _ (shadow_of_addr SHADOW_OFF (md + MD_SEND_ERRNO))); [|exact S19].
        rewrite (lf_sv_off E 32 _ 0 E32) by lia. f_equal. unfold shadow_of_addr, MD_SEND_ERRNO.
        rewrite (Hdiv1 4) by lia. lia.
      * apply (u_slot_chunk E cx W3 ms3 0xc0 _ (LA_G_NL + 0x42000)); [|exact S21].
        rewrite (lf_sv_off E 23 _ 8192 E23) by (unfold LA_G_NL; lia). f_equal; lia.
      * apply (u_slot_chunk E cx W3 ms3 0xc8 _ (shadow_of_addr SHADOW_OFF md)); [|exact S22].
        rewrite (lf_sv_off E 32 _ 0 E32) by lia. f_equal; lia.
      * apply (u_slot_chunk E cx W3 ms3 0xd0 _ (md + MD_N_REQ)); [|exact S23].
        rewrite (lf_sv_off E 35 md 8336 E35) by lia. reflexivity.
      * apply (u_slot_chunk E cx W3 ms3 0xd8 _ (md + MD_NEXT)); [|exact S24].
        rewrite (lf_sv_off E 35 md 8 E35) by lia. reflexivity.
      * apply (u_slot_chunk E cx W3 ms3 0xe0 _ (md + MD_SEND_ERRNO)); [|exact S25].
        rewrite (lf_sv_off E 35 md 4 E35) by lia. reflexivity.
      * apply (u_slot_chunk E cx W3 ms3 0xe8 _ md); [|exact S26].
        rewrite (lf_sv_off E 35 md 0 E35) by lia. rewrite Z.add_0_r. reflexivity.
    + (* the model's shadow, all zero *)
      rewrite (u_base E 32 _ E32) by (unfold shadow_of_addr; lia).
      split; [unfold shadow_of_addr; lia|]. split; [unfold shadow_of_addr; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros ii Hii. rewrite Z.add_0_r.
      apply (u_blk_shadow0 _ md 8856 ii Hmd8 eq_refl); [exact Bram | lia].
    + (* m + 0 .. m + 12 *)
      rewrite (u_base E 35 md E35) by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. destruct Dmd as ((_ & Hw) & HL). unfold MD_SIZE in HL. apply Hw. lia.
    + (* m + MD_N_REQ *)
      rewrite (u_base E 35 md E35) by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. destruct Dmd as ((_ & Hw) & HL). unfold MD_SIZE in HL. apply Hw. lia.
    + (* g_nl's two errnos *)
      rewrite (u_base E 23 _ E23) by (unfold LA_G_NL; lia).
      split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; lia|].
      destruct Dk as ((Hb & _) & HL).
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0x20c 4 (SOff 33 0) (nk_socket_errno kbs));
          [rewrite (lf_sv_off E 33 _ 0 E33); [rewrite Z.add_0_r; reflexivity | | ];
           unfold nk_socket_errno, fld_u32; pose proof (u_rdn4_range kbs NK_SOCKET_ERRNO); lia
          | unfold nk_socket_errno, fld_u32; pose proof (u_rdn4_range kbs NK_SOCKET_ERRNO); cbn; lia | cbn; lia |].
        replace (LA_G_NL + 262144 + 0x20c) with (LA_G_NL + NK_SOCKET_ERRNO) by (unfold NK_SOCKET_ERRNO; lia).
        exact (val_mem_of_abytes SEGS _ LA_G_NL kbs NK_SOCKET_ERRNO 4 Hb ltac:(unfold NK_SOCKET_ERRNO; lia)
          ltac:(unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia)).
      * apply (chunk_ok_val SEGS E _ _ 0x210 4 (SOff 34 0) (nk_send_errno kbs));
          [rewrite (lf_sv_off E 34 _ 0 E34); [rewrite Z.add_0_r; reflexivity | | ];
           unfold nk_send_errno, fld_u32; pose proof (u_rdn4_range kbs NK_SEND_ERRNO); lia
          | unfold nk_send_errno, fld_u32; pose proof (u_rdn4_range kbs NK_SEND_ERRNO); cbn; lia | cbn; lia |].
        replace (LA_G_NL + 262144 + 0x210) with (LA_G_NL + NK_SEND_ERRNO) by (unfold NK_SEND_ERRNO; lia).
        exact (val_mem_of_abytes SEGS _ LA_G_NL kbs NK_SEND_ERRNO 4 Hb ltac:(unfold NK_SEND_ERRNO; lia)
          ltac:(unfold NK_SEND_ERRNO, NK_SIZE in *; lia)).
    + (* g_nl.n_sent *)
      rewrite (u_base E 23 _ E23) by (unfold LA_G_NL; lia).
      split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [|apply Forall_nil].
      intros o Ho. assert (Hw : forall (m' : word -> option byte) a, LA_G_NL <= a < LA_G_NL + 271992 ->
        writable_at SEGS m' a) by (rewrite HSEGS; exact LA_G_NL_writable).
      apply Hw. unfold LA_G_NL in *. lia.
  - apply pairwise_disjoint_of_extents.
    unfold b_rgs, b_slot_rg, u_sh_rg, b_md0_rg, b_mdnr_rg, u_gnl_rg, u_gns_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (u_base E 9 (lf_sp1 cx) E9) by (unfold LLVMF_STK in *; lia).
    rewrite (u_base E 32 _ E32) by (unfold shadow_of_addr; lia).
    rewrite (u_base E 35 md E35) by lia.
    rewrite (u_base E 23 _ E23) by (unfold LA_G_NL; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_of_addr, LA_G_NL, LLVMF_STK, IMG_TOP in *.
    pose proof (Z.div_le_upper_bound md 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos md 8 ltac:(lia) ltac:(lia)).
    assert (Hlow : md + 8856 <= kLowMemEnd - 1 -> SHADOW_OFF + md / 8 >= kLowMemEnd) by (unfold SHADOW_OFF; lia).
    assert (Hhigh : kHighMemBeg <= md -> SHADOW_OFF + md / 8 + 1107 <= kHighMemBeg).
    { intros Hh. unfold SHADOW_OFF. rewrite C3. pose proof (Z.div_le_upper_bound (md + 8856) 8 (kHighMemEnd)
        ltac:(lia) ltac:(lia)). rewrite C4 in *. replace (md + 8856) with (md + 1107 * 8) in * by lia.
      rewrite Z.div_add in * by lia. lia. }
    assert (Hmc : md + 8856 <= alloc_ceiling) by (unfold req_size in Bmceil; destruct (Z.eqb_spec 8856 0); lia).
    unfold off_img, YImgTop.IMG_LO, SHADOW_OFF, YImgTop.IMG_TOP in *.
    destruct Bamm as [Bl | Bh].
    + specialize (Hlow Bl). destruct Bmt as [Bt | Bt]; repeat split; lia.
    + specialize (Hhigh (proj1 Bh)). destruct Bmt as [Bt | Bt]; repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    pose proof Dwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wse & Wsd & _).
    rewrite E23, E33, E34, E35. rewrite !unsigned_lit_small by (unfold LA_G_NL; lia).
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    assert (M16 : md mod 2 ^ 4 = 0) by exact Bm16.
    unfold LA_G_NL in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Lemma r_begin : forall POST i,
  FROM POST (r_b_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HK.
  destruct HK as (md & mk & P & N & kbs & mbs & gbs & T3 & s & nm & kc & ac & Hsh & Hreg & Hnm & Hkc & Hac & HU & Hnx).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (b_entry fy i cx fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 s kc ac HB HJ Hreg HU) as HS.
  pose proof HU as (Hi & Hcore & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4096 & Bmceil & _).
  set (E := Eimg (Ereg (ms_regs ms3) (b_extra md kbs))) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (b_extra md kbs) (Z_to_bv 64 0)).
  { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). apply ew_Ereg_extra. }
  assert (E23 : ew E 23 = Z_to_bv 64 (LA_G_NL + 0x40000)) by (rewrite (EL 23%nat 23%bv ltac:(clia) eq_refl); exact R23).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_socket_errno kbs)) by exact (EX 1%nat ltac:(clia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (nk_send_errno kbs)) by exact (EX 2%nat ltac:(clia)).
  assert (E35 : ew E 35 = Z_to_bv 64 md) by exact (EX 3%nat ltac:(clia)).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (Bm64 : md + 8856 <= 2 ^ 64) by clia.
  rewrite (lf_shape_eta fy LR_kret ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_kret)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LR_b.
  { (* the writes: the model's four fields, g_nl.n_sent *)
    cbn [ss_mem b_ss]. unfold b_rgs.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_wlo YP09.r_whi b_slot_rg] in Ha; clia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_wlo YP09.r_whi u_sh_rg] in Ha; clia|].
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base b_md0_rg base_val] in Ha. rewrite E35 in Ha.
      rewrite unsigned_lit_small in Ha by clia.
      left. split; [|clia]. right; right; left. exists md, MD_SIZE. split; [exact Bmd|]. split; [exact Bmc|].
      unfold req_size, MD_SIZE. cbn. clia. }
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base b_mdnr_rg base_val] in Ha. rewrite E35 in Ha.
      rewrite unsigned_lit_small in Ha by clia.
      left. split; [|clia]. right; right; left. exists md, MD_SIZE. split; [exact Bmd|]. split; [exact Bmc|].
      unfold req_size, MD_SIZE. cbn. clia. }
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_wlo YP09.r_whi u_gnl_rg] in Ha; clia|].
    apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_gns_rg base_val] in Ha. rewrite E23 in Ha.
    rewrite unsigned_lit_small in Ha by (unfold LA_G_NL; clia).
    unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold LA_G_NL, NK_SIZE in *. clia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  set (X := fun a => lf_mb_rng md (a mod 2 ^ 64)).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem b_ss) _ _ X HFrA). intros a (r & Hr & Hw). unfold X.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem b_ss] in Hr. unfold b_rgs in Hr. cbn [In] in Hr. unfold lf_mb_rng, MD_N_REQ, NK_N_SENT.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base b_slot_rg u_sh_rg b_md0_rg b_mdnr_rg u_gnl_rg u_gns_rg base_val]
        in Hw; try clia.
    - rewrite E35, unsigned_lit_small in Hw by clia. clia.
    - rewrite E35, unsigned_lit_small in Hw by clia. clia.
    - rewrite E23, unsigned_lit_small in Hw by (unfold LA_G_NL; clia). unfold LA_G_NL in *. clia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssA := ssx) in HS end.
  assert (RG : forall k r, nth_error (ss_mem ssA) k = Some r -> region_ok SEGS E (rdW W3 (ms_mem msA)) r)
    by (intros k r Hk; exact (st_ok_pi_region_nth E ssA (restrict (w_H W3) msA) k r HS Hk)).
  pose proof Hdat as (Dk & _ & _ & _ & _ & _ & Dmd & _).
  pose proof Dk as (_ & KL). pose proof Dmd as (_ & ML).
  assert (A1 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4)).
  { replace (md + MD_SOCKET_ERRNO) with (md + 0) by (unfold MD_SOCKET_ERRNO; clia).
    pose proof (u_rdn4_range kbs NK_SOCKET_ERRNO) as Rv.
    apply (u_word4 E _ _ md 0 (SOff 33 0) _ (RG 2%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E35. apply unsigned_lit_small. clia.
    - cbn. right; right; left. reflexivity.
    - apply lf_slice_length; unfold NK_SOCKET_ERRNO, NK_SIZE in *; clia.
    - rewrite (lf_sv_off E 33 _ 0 E33) by (unfold nk_socket_errno, fld_u32; clia). rewrite Z.add_0_r. reflexivity.
    - clia.
    - clia. }
  assert (A2 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4)).
  { pose proof (u_rdn4_range kbs NK_SEND_ERRNO) as Rv.
    apply (u_word4 E _ _ md MD_SEND_ERRNO (SOff 34 0) _ (RG 2%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E35. apply unsigned_lit_small. clia.
    - cbn. right; left. reflexivity.
    - apply lf_slice_length; unfold NK_SEND_ERRNO, NK_SIZE in *; clia.
    - rewrite (lf_sv_off E 34 _ 0 E34) by (unfold nk_send_errno, fld_u32; clia). rewrite Z.add_0_r. reflexivity.
    - unfold MD_SEND_ERRNO; clia.
    - unfold MD_SEND_ERRNO; clia. }
  assert (A3 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_NEXT) lf_z4).
  { apply (u_word4 E _ _ md MD_NEXT (SLit 0) _ (RG 2%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E35. apply unsigned_lit_small. clia.
    - cbn. left. reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold MD_NEXT; clia.
    - unfold MD_NEXT; clia. }
  assert (A4 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_N_REQ) lf_z4).
  { apply (u_word4 E _ _ md MD_N_REQ (SLit 0) _ (RG 3%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E35. apply unsigned_lit_small. clia.
    - cbn. left. reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold MD_N_REQ; clia.
    - unfold MD_N_REQ; clia. }
  assert (A5 : abytes SEGS (rdW W3 (ms_mem msA)) (LA_G_NL + NK_N_SENT) lf_z4).
  { replace (LA_G_NL + NK_N_SENT) with ((LA_G_NL + 0x40000) + 8872) by (unfold NK_N_SENT; clia).
    apply (u_word4 E _ _ (LA_G_NL + 0x40000) 8872 (SLit 0) _ (RG 5%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E23. apply unsigned_lit_small. unfold LA_G_NL; clia.
    - cbn. left. reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold LA_G_NL; clia.
    - unfold LA_G_NL; clia. }
  pose proof (fun a (HXa : X a) => u_mb_notX SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    LAWS TB HSEGS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk HXa) as NX.
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
  pose proof (lf_saved_keep X cx W3 ms3 W3 msA KA N1 Hsv) as Hsv'.
  pose proof (lf_header_keep X cx fp W3 ms3 W3 msA KA N2 Hhd) as Hhd'.
  pose proof (lf_fshadow_keep X cx fp W3 ms3 W3 msA LF_SH0 KA N3 Hfs) as Hfs'.
  pose proof (lf_slots_keep X cx md mk fp W3 ms3 W3 msA KA N4 Hsl) as Hsl'.
  pose proof (lf_cur_keep X cx W3 ms3 W3 msA P N KA N5 Hcur) as Hcur'.
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs N6 Hjbk)
    as Hjbk'.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA N7 Hblk) as Hblk'.
  destruct (lf_data_mb X _ _ cx md mk kbs mbs gbs HSEGS KA (wcarry_on_grows _ _ _ HGA) ND Bmt Bkt Bap A1 A2 A3 A4 A5
    Hdat) as (Hdat' & Hns' & Hnr' & Hop' & Hreq').
  pose proof (lf_mbs_mb_sock kbs mbs KL ML) as Msock. pose proof (lf_mbs_mb_send kbs mbs KL ML) as Msend.
  pose proof (lf_mbs_mb_next kbs mbs KL ML) as Mnext.
  pose proof (lf_kbs_mb_fields kbs KL) as (_ & _ & _ & _ & _ & Knx & Knc & Ken & Kso & Kse).
  assert (KSEQ : md_kstate (lf_mbs_mb kbs mbs) (lf_kbs_mb kbs) = nk_kstate (lf_kbs_mb kbs)).
  { unfold md_kstate, nk_kstate. rewrite Mnext, Knx, Hnx, Msock, Msend, Kso, Kse. reflexivity. }
  assert (REQ0 : md_reqs (lf_mbs_mb kbs mbs) = []) by (unfold md_reqs; rewrite Hnr'; reflexivity).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
  rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18.
  rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19. rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20.
  rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26.
  assert (E18 : ew E 18 = Z_to_bv 64 kc) by (rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl); exact R18).
  assert (E20 : ew E 20 = Z_to_bv 64 ac) by (rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
  assert (AND : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
    alu64 ALU_AND (ew E n) (Z_to_bv 64 255) = Z_to_bv 64 v).
  { intros n v Hn Hv. rewrite <- (b_and255 E n v Hn Hv). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity. }
  rewrite (AND 18%nat kc E18 ltac:(lia)) in Q21. rewrite (AND 20%nat ac E20 ltac:(lia)) in Q27.
  apply (HL cx fy fp k2 ly3 S3 W3 msA md4 HB Hfx HJ Hfr).
  exists md, mk, P, N, (lf_kbs_mb kbs), (lf_mbs_mb kbs mbs), gbs, T3, s, nm, kc, ac.
  split; [exact (lf_shape_of_st_ok fy W3 _ _ msA HS eq_refl)|].
  split.
  { unfold r_regs2. rewrite Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
    repeat split; first [assumption | reflexivity]. }
  split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|].
  split.
  { split; [exact Hi|]. split.
    { unfold lf_core in *. rewrite Q2, Q8, Q9, Q3, Q4. exact Hcore. }
    split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|]. split; [exact Hcur'|].
    split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdat'|]. rewrite Hop'. exact Hop. }
  split; [exact Hns'|]. split; [exact REQ0|]. split; [exact KSEQ | exact Hreq'].
Qed.
End a.
