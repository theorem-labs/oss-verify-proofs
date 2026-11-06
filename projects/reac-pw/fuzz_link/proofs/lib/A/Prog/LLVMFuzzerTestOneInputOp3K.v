(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 778 of its 834 lines of code are new or changed and 348 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm: model_begin's five stores and the n_mark test
   (+0x6f0 .. +0x768), from the cut u_k_inv to the loop head u_l_inv 0 or the exit cut u_x_inv.
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
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


(* the runner's state at +0x6f0: the registers, four more atoms (32: the shadow byte of m, 33 / 34: g_nl's two
   errnos, 35: m->n_mark), and the regions the stretch reads and writes *)
Definition u_slot_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x58 0xe8 0x58 0x58
    [YP09.mkChunk 0x58 (CVal 8 (SOff 22 8340)); YP09.mkChunk 0xa0 (CVal 8 (SOff 32 1042));
     YP09.mkChunk 0xa8 (CVal 8 (SOff 32 1)); YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0));
     YP09.mkChunk 0xc0 (CVal 8 (SOff 23 8192)); YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0));
     YP09.mkChunk 0xd0 (CVal 8 (SOff 22 8336)); YP09.mkChunk 0xd8 (CVal 8 (SOff 22 8));
     YP09.mkChunk 0xe0 (CVal 8 (SOff 22 4))].
Definition u_sh_rg : YP09.region := YP09.mkRegion (Some 32%nat) 0 1107 0 0 [YP09.mkChunk 0 (CZero 1107)].
Definition u_md0_rg : YP09.region := YP09.mkRegion (Some 22%nat) 0 12 0 12 [].
Definition u_mdnr_rg : YP09.region := YP09.mkRegion (Some 22%nat) 8336 8340 8336 8340 [].
Definition u_nm_rg : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition u_gnl_rg : YP09.region :=
  YP09.mkRegion (Some 23%nat) 0x20c 0x214 0 0 [YP09.mkChunk 0x20c (CVal 4 (SOff 33 0)); YP09.mkChunk 0x210 (CVal 4 (SOff 34 0))].
Definition u_gns_rg : YP09.region := YP09.mkRegion (Some 23%nat) 0x22a8 0x22ac 0x22a8 0x22ac [].
Definition u_mb_rgs : smem := [u_slot_rg; u_sh_rg; u_md0_rg; u_mdnr_rg; u_nm_rg; u_gnl_rg; u_gns_rg].
Definition u_nm_sh : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 27 0).
Definition u_mb_facts : facts :=
  mkFacts [(21%nat, mkAF 4096 (2 ^ 47) 2); (22%nat, mkAF 4096 (2 ^ 47) 4);
           (23%nat, mkAF (LA_G_NL + 0x40000) (LA_G_NL + 0x40000) 0);
           (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF 0 32 0)] []
    [(u_nm_sh, SOff 32 1106)].
Definition u_mb_ss : sstate := mkSS LU_kret sr_atoms u_mb_rgs None u_mb_facts.
Definition u_mb_extra (md : Z) (kbs mbs : list byte) : list word :=
  [Z_to_bv 64 (shadow_of_addr SHADOW_OFF md); Z_to_bv 64 (nk_socket_errno kbs); Z_to_bv 64 (nk_send_errno kbs);
   Z_to_bv 64 (md_n_mark mbs)].

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
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* every shadow byte of a block the walk holds is 0 (each granule of it lies in the block) *)
Lemma u_blk_shadow0 : forall (m : word -> option byte) p n i, p mod 8 = 0 -> n mod 8 = 0 ->
  range_addressable (ard SEGS m) SHADOW_OFF p n -> 0 <= i < n / 8 ->
  mbyte SEGS m (shadow_of_addr SHADOW_OFF p + i) = Some (Z_to_bv 8 0).
Proof.
  intros m p n i Hp Hn HR Hi.
  destruct (HR (p + 8 * i + 7) ltac:(clia)) as (s & Hs & Hok).
  assert (Hx : shadow_of_addr SHADOW_OFF (p + 8 * i + 7) = shadow_of_addr SHADOW_OFF p + i).
  { unfold shadow_of_addr. pose proof (Z.div_mod p 8 ltac:(lia)). rewrite Hp in *.
    replace (p + 8 * i + 7) with ((p / 8 + i) * 8 + 7) by clia.
    rewrite Z.div_add_l by lia. cbn. clia. }
  rewrite Hx in Hs. unfold saddr_ok in Hok.
  assert (M : (p + 8 * i + 7) mod 8 = 7).
  { pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp, Z.add_0_r in D.
    replace (p + 8 * i + 7) with (7 + (p / 8 + i) * 8) by clia. rewrite Z_mod_plus_full. reflexivity. }
  assert (Hs0 : s = 0) by (destruct Hok as [H0 | H1]; [exact H0 | clia]).
  subst s. unfold ard in Hs. destruct (mbyte SEGS m (shadow_of_addr SHADOW_OFF p + i)) as [b|] eqn:Eb; [|discriminate].
  cbn [option_map] in Hs. injection Hs as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* a spill slot of the frame as a chunk of the runner's region based at s1 *)
Lemma u_slot_chunk : forall (E : env) cx (W3 : world SEGS) ms3 off e v,
  sv_denot E e = Z_to_bv 64 v -> lf_slot cx W3 ms3 off v ->
  YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (lf_sp1 cx) (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E cx W3 ms3 off e v He Hs. unfold lf_slot, lf_at in Hs.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) Hs) as Hr.
  apply (chunk_ok_val SEGS E _ (lf_sp1 cx) off 8 e v He); [cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hs).
Qed.

Lemma u_base : forall (E : env) n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v.
Proof. intros E n v H Hv. cbn [base_val]. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma u_ewU : forall (E : env) n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Lemma u_rdn4_range : forall bs off, 0 <= rdn bs off 4 < 2 ^ 32.
Proof.
  intros bs off. unfold rdn. pose proof (bytes_le_to_Z_nonneg (slice bs off 4)) as H0.
  pose proof (bytes_le_to_Z_bound (slice bs off 4)) as H1.
  assert (L : (length (slice bs off 4) <= 4)%nat) by (unfold slice; rewrite length_firstn; lia).
  assert (Pw : 2 ^ (8 * Z.of_nat (length (slice bs off 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

(* the runner's entry state at +0x6f0 holds at a u_k_inv cut *)
Lemma u_mb_entry : forall (fy : YK11.FPState) i cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3 md mk P N kbs mbs gbs T3,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) ->
  u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 ms3 md3 ->
  st_ok_pi (fx := fy) SEGS pa_val (Eimg (Ereg (ms_regs ms3) (u_mb_extra md kbs mbs))) u_mb_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_kret)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
  intros fy i cx fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 HB HJ R23 HU.
  destruct HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
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
  set (E := Eimg (Ereg (ms_regs ms3) (u_mb_extra md kbs mbs))).
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (u_mb_extra md kbs mbs) (Z_to_bv 64 0)).
  { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (E21 : ew E 21 = Z_to_bv 64 (md + MD_N_MARK)) by (rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 md) by (rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (LA_G_NL + 0x40000)) by (rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
  assert (E32 : ew E 32 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF md)) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_socket_errno kbs)) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (nk_send_errno kbs)) by exact (EX 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = Z_to_bv 64 (md_n_mark mbs)) by exact (EX 3%nat ltac:(lia)).
  unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *. unfold MD_SIZE in *.
  assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc); rewrite Hc;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  assert (Hshm : shadow_of_addr SHADOW_OFF md = SHADOW_OFF + md / 8) by reflexivity.
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
  rewrite restrict_mkst_fx. unfold u_mb_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold u_mb_rgs, u_slot_rg, u_sh_rg, u_md0_rg, u_mdnr_rg, u_nm_rg, u_gnl_rg, u_gns_rg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + (* the spill slots at s1 *)
      rewrite (u_base E 9 (lf_sp1 cx) E9) by (unfold LLVMF_STK in *; lia).
      split; [unfold LLVMF_STK in *; lia|]. split; [unfold LLVMF_STK in *; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (u_slot_chunk E cx W3 ms3 0x58 _ (md + MD_MARK)); [|exact S9].
        rewrite (lf_sv_off E 22 md 8340 E22) by lia. reflexivity.
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
        rewrite (lf_sv_off E 22 md 8336 E22) by lia. reflexivity.
      * apply (u_slot_chunk E cx W3 ms3 0xd8 _ (md + MD_NEXT)); [|exact S24].
        rewrite (lf_sv_off E 22 md 8 E22) by lia. reflexivity.
      * apply (u_slot_chunk E cx W3 ms3 0xe0 _ (md + MD_SEND_ERRNO)); [|exact S25].
        rewrite (lf_sv_off E 22 md 4 E22) by lia. reflexivity.
    + (* the model's shadow, all zero *)
      rewrite (u_base E 32 _ E32) by (unfold shadow_of_addr; lia).
      split; [unfold shadow_of_addr; lia|]. split; [unfold shadow_of_addr; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros ii Hii. rewrite Z.add_0_r.
      apply (u_blk_shadow0 _ md 8856 ii Hmd8 eq_refl); [exact Bram | lia].
    + (* m + 0 .. m + 12 *)
      rewrite (u_base E 22 md E22) by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. destruct Dmd as ((_ & Hw) & HL). unfold MD_SIZE in HL. apply Hw. lia.
    + (* m + MD_N_REQ *)
      rewrite (u_base E 22 md E22) by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. destruct Dmd as ((_ & Hw) & HL). unfold MD_SIZE in HL. apply Hw. lia.
    + (* m + MD_N_MARK *)
      rewrite (u_base E 21 (md + MD_N_MARK) E21) by (unfold MD_N_MARK; lia).
      split; [unfold MD_N_MARK; lia|]. split; [unfold MD_N_MARK; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 35 0) (md_n_mark mbs));
        [rewrite (lf_sv_off E 35 _ 0 E35); [rewrite Z.add_0_r; reflexivity | | ];
         unfold md_n_mark, fld_u32; pose proof (u_rdn4_range mbs MD_N_MARK); lia
        | unfold md_n_mark, fld_u32; pose proof (u_rdn4_range mbs MD_N_MARK); cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. destruct Dmd as ((Hb & _) & HL).
      exact (val_mem_of_abytes SEGS _ md mbs MD_N_MARK 4 Hb ltac:(unfold MD_N_MARK; lia)
        ltac:(unfold MD_N_MARK, MD_SIZE in *; lia)).
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
    unfold u_mb_rgs, u_slot_rg, u_sh_rg, u_md0_rg, u_mdnr_rg, u_nm_rg, u_gnl_rg, u_gns_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (u_base E 9 (lf_sp1 cx) E9) by (unfold LLVMF_STK in *; lia).
    rewrite (u_base E 32 _ E32) by (unfold shadow_of_addr; lia).
    rewrite (u_base E 22 md E22) by lia.
    rewrite (u_base E 21 (md + MD_N_MARK) E21) by (unfold MD_N_MARK; lia).
    rewrite (u_base E 23 _ E23) by (unfold LA_G_NL; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_of_addr, MD_N_MARK, LA_G_NL, LLVMF_STK, IMG_TOP in *.
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
  - assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl); exact R27).
    split; [|split; [exact I|]].
    + cbn [u_mb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      pose proof Dwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wse & Wsd & _).
      pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
      rewrite E21, E22, E23, E33, E34, E35. rewrite !unsigned_lit_small by (unfold LA_G_NL, MD_N_MARK; lia).
      rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      assert (M4 : (md + MD_N_MARK) mod 2 ^ 2 = 0).
      { unfold MD_N_MARK. rewrite Zmod_divides in Bm16 by lia. destruct Bm16 as (c & Hc). rewrite Hc.
        replace (16 * c + 8852) with ((4 * c + 2213) * 4) by lia. change (2 ^ 2) with 4. apply Z_mod_mult. }
      assert (M16 : md mod 2 ^ 4 = 0) by exact Bm16.
      unfold MD_N_MARK, LA_G_NL in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    + cbn [u_mb_facts f_alias alias_ok]. split; [|exact I]. unfold u_nm_sh.
      assert (Hdv : (md + 8852) / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; lia).
      rewrite (denot_shadow_cell E 21 27 (md + MD_N_MARK) SHADOW_OFF E21
        ltac:(unfold MD_N_MARK; clia) E27 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold MD_N_MARK, SHADOW_OFF in *; clia)).
      rewrite (lf_sv_off E 32 _ 1106 E32) by lia. f_equal. unfold shadow_of_addr, MD_N_MARK.
      pose proof (Z.div_mod md 8 ltac:(lia)) as D. rewrite Hmd8, Z.add_0_r in D.
      replace (md + 8852) with (4 + (md / 8 + 1106) * 8) by lia. rewrite Z.div_add by lia.
      rewrite Z.div_small by lia. lia.
Qed.

(* the run's frame as a kagree over the 2 ^ 64-wrapped addresses *)
Lemma u_kagree_frame : forall E rs (m m' : word -> option byte) (X : Z -> Prop),
  frame_of E rs m m' -> (forall a, in_wrange E rs (bv_unsigned (Z_to_bv 64 a)) -> X a) -> kagree SEGS X m m'.
Proof. intros E rs m m' X HF HX a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros H. exact (Ha (HX a H)). Qed.

(* a word of four bytes a run stored, as abytes *)
Lemma u_word4 : forall (E : env) (m : word -> option byte) r base off e bs,
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

Lemma u_bge0 : forall n, 0 <= n < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 0) (Z_to_bv 64 n) = (n <=? 0).
Proof.
  intros n Hn. rewrite YO0c.branch_ge. rewrite !unsigned_lit_small by lia.
  unfold YO0b.s64. destruct (Z.ltb_spec 0 (2 ^ 63)); [|lia]. destruct (Z.ltb_spec n (2 ^ 63)); [|lia].
  destruct (Z.ltb_spec 0 n), (Z.leb_spec n 0); reflexivity || lia.
Qed.

(* the five bytes ranges model_begin writes, apart from every other footprint of the cut *)
Lemma u_mb_out : forall cx fp k2 ev mo wl lv md mk T3 own ly3 S3 (W3 : world SEGS) ms3 md3 a,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_mb_rng md a ->
  0 <= a < 2 ^ 64 /\
  ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_fshadow_fp cx fp 112 a /\ ~ lf_slots_fp cx a /\
  ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
    & Bamm & Bamk).
  unfold off_img, YImgTop.IMG_LO in Bmt, Bkt.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4096 & Bmceil & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4096 & Bkceil & _).
  assert (Rmd : req_size MD_SIZE = MD_SIZE) by reflexivity. assert (Rmk : req_size MK_SIZE = MK_SIZE) by reflexivity.
  rewrite Rmd in Bmceil. rewrite Rmk in Bkceil.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  (* the side frame: apart from the md block, under the ceiling *)
  pose proof (al_sep _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 HAR3) as (Hsep & Hfs).
  destruct (pairwise_app_inv _ _ _ Hsep) as (_ & _ & Hx).
  assert (Dfm : zdisjoint (md, MD_SIZE) (frame_addr ly3 LF_CID fp, 1024)).
  { pose proof (Hx (md, req_size MD_SIZE) (frame_addr ly3 LF_CID fp, fs_frame_bytes LF_CID)
      ltac:(apply (in_map (fun b => (fst b, req_size (snd b))) _ _ Bmd))
      ltac:(apply (in_map (fun f => (frame_addr ly3 (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hin))) as D.
    exact D. }
  rewrite Forall_forall in Hfs. specialize (Hfs (LF_CID, fp) Hin). cbn [fst snd] in Hfs.
  change (fs_frame_bytes LF_CID) with 1024 in Hfs.
  assert (HF : lf_F cx fp = frame_addr ly3 LF_CID fp) by (unfold lf_F; rewrite Hfa; reflexivity).
  assert (HSH : lf_SH cx fp = shadow_of_addr SHADOW_OFF (lf_F cx fp)) by reflexivity.
  unfold zdisjoint in Dfm. cbn [fst snd] in Dfm.
  (* the image *)
  unfold lf_mb_rng, MD_N_REQ, NK_N_SENT in Ha.
  unfold lf_saved_fp, lf_header_fp, lf_fshadow_fp, lf_slots_fp, lf_cur_fp, lf_blocks_fp, MD_SIZE, MK_SIZE in *.
  change (fs_frame_bytes LF_CID) with 1024.
  rewrite HSH, HF. unfold shadow_of_addr.
  assert (Sh : forall x, 4096 <= x <= alloc_ceiling ->
    kLowMemEnd + 512 <= SHADOW_OFF + x / 8 /\ SHADOW_OFF + x / 8 + 0x100000 <= kHighMemBeg).
  { intros x (Hx1 & Hx2).
    assert (D1 : 4096 / 8 <= x / 8) by (apply Z.div_le_mono; [lia | exact Hx1]).
    assert (D2 : x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; [lia | lia]).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. clear - D1 D2. lia. }
  unfold amem_range in Bamm. unfold LLVMF_STK in *.
  destruct Ha as [Ha | [Ha | Ha]].
  - (* md + [0, 12) *)
    split; [clia|]. split; [clia|]. split; [clia|].
    split; [pose proof (Sh (frame_addr ly3 LF_CID fp) ltac:(clia)); unfold kLowMemEnd, kHighMemBeg in *; clia|].
    split; [clia|]. split; [clia|].
    split.
    { intros [Hj | [Hj | [Hj | Hj]]].
      - destruct Hj as [Hj | [Hj | (f & n & Hfn & Hj)]].
        + rewrite HMS in Hj. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Hj.
          unfold YImgTop.IMG_TOP in Bmt. clia.
        + rewrite HMS in Hj. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Hj.
          unfold YImgTop.IMG_TOP in Bmt. clia.
        + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
          assert (Hne : (f, n) <> (md, 8856)) by (intros E; rewrite E in Hfn; exact (BmT Hfn)).
          pose proof (sep_blocks _ _ LAWS _ _ _ _ _ f n md 8856 HAR3 HfnT Bmd Hne) as D. unfold zdisjoint in D.
          cbn [fst snd] in D. rewrite Rmd in D.
          assert (Hn : n = AMF_BLOCK).
          { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
            destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
          subst n. unfold req_size, AMF_BLOCK in D. cbn in D. unfold AMF_BLOCK in Hj. clia.
      - rewrite HLN in Hj. unfold LA_NUL, LA_LONG_ALIAS, YImgTop.IMG_TOP in *. clia.
      - pose proof (lf_roP_bounds a Hj). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clia.
      - assert (Hn : 0 < c_n cx) by clia. specialize (Bpl Hn). unfold apart in Bpl. clia. }
    split.
    { intros [(x & Hx1 & Hx2) | (x & Hx1 & Hx2)]; subst a.
      - pose proof (Sh x ltac:(clia)). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. clia.
      - pose proof (Sh x ltac:(clia)). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. clia. }
    intros Hro. pose proof (lf_roP_bounds a Hro). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clia.
  - (* md + [8336, 8340) *)
    split; [clia|]. split; [clia|]. split; [clia|].
    split; [pose proof (Sh (frame_addr ly3 LF_CID fp) ltac:(clia)); unfold kLowMemEnd, kHighMemBeg in *; clia|].
    split; [clia|]. split; [clia|].
    split.
    { intros [Hj | [Hj | [Hj | Hj]]].
      - destruct Hj as [Hj | [Hj | (f & n & Hfn & Hj)]].
        + rewrite HMS in Hj. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Hj.
          unfold YImgTop.IMG_TOP in Bmt. clia.
        + rewrite HMS in Hj. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Hj.
          unfold YImgTop.IMG_TOP in Bmt. clia.
        + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
          assert (Hne : (f, n) <> (md, 8856)) by (intros E; rewrite E in Hfn; exact (BmT Hfn)).
          pose proof (sep_blocks _ _ LAWS _ _ _ _ _ f n md 8856 HAR3 HfnT Bmd Hne) as D. unfold zdisjoint in D.
          cbn [fst snd] in D. rewrite Rmd in D.
          assert (Hn : n = AMF_BLOCK).
          { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
            destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
          subst n. unfold req_size, AMF_BLOCK in D. cbn in D. unfold AMF_BLOCK in Hj. clia.
      - rewrite HLN in Hj. unfold LA_NUL, LA_LONG_ALIAS, YImgTop.IMG_TOP in *. clia.
      - pose proof (lf_roP_bounds a Hj). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clia.
      - assert (Hn : 0 < c_n cx) by clia. specialize (Bpl Hn). unfold apart in Bpl. clia. }
    split.
    { intros [(x & Hx1 & Hx2) | (x & Hx1 & Hx2)]; subst a.
      - pose proof (Sh x ltac:(clia)). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. clia.
      - pose proof (Sh x ltac:(clia)). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. clia. }
    intros Hro. pose proof (lf_roP_bounds a Hro). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clia.
  - (* g_nl.n_sent *)
    assert (Ga : in_img SEGS a) by (apply (proj1 (IMG a ltac:(left; unfold NK_SIZE; clia)))).
    assert (Fni : forall x, frame_addr ly3 LF_CID fp <= x < frame_addr ly3 LF_CID fp + 1024 -> ~ in_img SEGS x).
    { intros x Hxx. apply (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 x HAR3). right; left.
      exists LF_CID, fp. split; [exact Hin|]. change (fs_frame_bytes LF_CID) with 1024. exact Hxx. }
    unfold LA_G_NL in *.
    split; [clia|]. split; [clia|].
    split; [intros Hh; destruct Hh as [Hh | Hh]; apply (Fni a); [clia | exact Ga | clia | exact Ga]|].
    split; [pose proof (Sh (frame_addr ly3 LF_CID fp) ltac:(clia)); unfold kLowMemEnd, kHighMemBeg in *; clia|].
    split; [clia|]. split; [clia|].
    split.
    { intros [Hj | [Hj | [Hj | Hj]]].
      - destruct Hj as [Hj | [Hj | (f & n & Hfn & Hj)]].
        + rewrite HMS in Hj. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Hj.
          clia.
        + rewrite HMS in Hj. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Hj. clia.
        + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
          assert (Hn : n = AMF_BLOCK).
          { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
            destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
          subst n. apply (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 a HAR3); [|exact Ga].
          left. exists f, AMF_BLOCK. split; [exact HfnT|]. unfold req_size, AMF_BLOCK in *. cbn. clia.
      - rewrite HLN in Hj. unfold LA_NUL, LA_LONG_ALIAS in *. clia.
      - exact (ar_not_ro_G HSEGS a ltac:(unfold inG, G_HARNESS; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
          unfold NK_SIZE, LA_G_NL; clia) Hj).
      - assert (Hn : 0 < c_n cx) by clia.
        pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn) as Hpb.
        apply (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 a HAR3); [|exact Ga].
        left. exists (c_p cx), (c_n cx). split; [exact Hpb|]. unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); clia. }
    split.
    { intros [(x & Hx1 & Hx2) | (x & Hx1 & Hx2)]; subst a.
      - pose proof (Sh x ltac:(clia)). unfold kLowMemEnd in *. clia.
      - pose proof (Sh x ltac:(clia)). unfold kLowMemEnd in *. clia. }
    exact (ar_not_ro_G HSEGS a ltac:(unfold inG, G_HARNESS; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
      unfold NK_SIZE, LA_G_NL; clia)).
Qed.

(* every footprint of the cut lies in [0, 2 ^ 64) *)
Lemma u_fp_range : forall cx fp k2 ev mo wl lv md mk T3 own ly3 S3 (W3 : world SEGS) ms3 md3 a,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
   lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) ->
  0 <= a < 2 ^ 64 /\ (a < alloc_ceiling \/ lf_sp1 cx + 0x18 <= a).
Proof.
  intros cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4096 & Bmceil & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4096 & Bkceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil. change (req_size MK_SIZE) with 516 in Bkceil.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (al_sep _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 HAR3) as (_ & Hfs).
  rewrite Forall_forall in Hfs. specialize (Hfs (LF_CID, fp) Hin). cbn [fst snd] in Hfs.
  change (fs_frame_bytes LF_CID) with 1024 in Hfs.
  assert (HF : lf_F cx fp = frame_addr ly3 LF_CID fp) by (unfold lf_F; rewrite Hfa; reflexivity).
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> 0 <= x < 2 ^ 64 /\ (x < alloc_ceiling \/ lf_sp1 cx + 0x18 <= x)).
  { intros x Hx. pose proof (lf_roP_below_top x Hx) as Ht. unfold YImgTop.IMG_TOP in Ht.
    destruct Hx as [(s & _ & _ & Hs) | Hs]; [pose proof (N2Z.is_nonneg (seg_base s)); clia | unfold PCAP_RLO in Hs; clia]. }
  assert (DV : forall x, 0 <= x <= 2 ^ 47 -> 0 <= x / 8 <= 2 ^ 44).
  { intros x Hx. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  unfold LLVMF_STK in *.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]].
  - unfold lf_saved_fp in Ha. clia.
  - unfold lf_header_fp in Ha. rewrite HF in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. clia.
  - unfold lf_fshadow_fp, lf_SH, shadow_of_addr in Ha. rewrite HF in Ha.
    pose proof (DV (frame_addr ly3 LF_CID fp) ltac:(clia)). unfold SHADOW_OFF in Ha. clia.
  - unfold lf_slots_fp in Ha. clia.
  - unfold lf_cur_fp in Ha. clia.
  - destruct Ha as [Hj | [Hj | [Hj | Hj]]].
    + destruct Hj as [Hj | [Hj | (f & n & Hfn & Hj)]].
      * rewrite HMS in Hj. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Hj. clia.
      * rewrite HMS in Hj. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Hj. clia.
      * destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 f n HAR3 (Hinc _ Hfn)) as (_ & Hf4 & Hfc & _).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n. change (req_size AMF_BLOCK) with 1304 in Hfc. unfold AMF_BLOCK in Hj. clia.
    + rewrite HLN in Hj. unfold LA_NUL, LA_LONG_ALIAS in Hj. clia.
    + exact (RO a Hj).
    + assert (Hn : 0 < c_n cx) by clia.
      pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn) as Hpb.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hpb) as (_ & Hp4 & Hpc & _).
      unfold req_size in Hpc. destruct (Z.eqb_spec (c_n cx) 0); clia.
  - destruct Ha as [(x & Hx & ->) | (x & Hx & ->)]; unfold shadow_of_addr, MD_SIZE, MK_SIZE in *;
      pose proof (DV x ltac:(clia)); unfold SHADOW_OFF; clia.
  - destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]];
      try (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS, MD_SIZE, MK_SIZE in *; clia).
    exact (RO a Ha).
Qed.

Lemma u_rng_mod : forall md a, 0 <= a < 2 ^ 64 -> lf_mb_rng md (a mod 2 ^ 64) -> lf_mb_rng md a.
Proof. intros md a Ha H. rewrite Z.mod_small in H by exact Ha. exact H. Qed.

(* the ranges model_begin writes miss every footprint of the cut but lf_data's *)
Lemma u_mb_notX : forall cx fp k2 ev mo wl lv md mk T3 own ly3 S3 (W3 : world SEGS) ms3 md3 a,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_mb_rng md (a mod 2 ^ 64) ->
  ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_fshadow_fp cx fp 112 a /\ ~ lf_slots_fp cx a /\
  ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\
  (lf_data_fp md mk a -> lf_mb_rng md a).
Proof.
  intros cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Ha.
  assert (G : (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) ->
     lf_mb_rng md a /\ ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_fshadow_fp cx fp 112 a /\
     ~ lf_slots_fp cx a /\ ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a).
  { intros Hf. pose proof (u_fp_range cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Hf)
      as R. pose proof (u_rng_mod md a (proj1 R) Ha) as Ha'.
    destruct (u_mb_out cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Ha')
      as (_ & N1 & N2 & N3 & N4 & N5 & N6 & N7 & _).
    tauto. }
  repeat split.
  - intros H. exact (proj1 (proj2 (G ltac:(tauto))) H).
  - intros H. exact (proj1 (proj2 (proj2 (G ltac:(tauto)))) H).
  - intros H. exact (proj1 (proj2 (proj2 (proj2 (G ltac:(tauto))))) H).
  - intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (G ltac:(tauto)))))) H).
  - intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (G ltac:(tauto))))))) H).
  - intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (G ltac:(tauto)))))))) H).
  - intros H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (G ltac:(tauto)))))))) H).
  - intros H. exact (proj1 (G ltac:(tauto))).
Qed.

Lemma u_kret : forall POST i,
  FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i 0) ->
  FROM POST (u_x_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (u_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL HX cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HK.
  destruct HK as (md & mk & P & N & kbs & mbs & gbs & T3 & Hsh & R23 & HU & Hnx).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (u_mb_entry fy i cx fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 HB HJ R23 HU) as HS.
  pose proof HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4096 & Bmceil & _).
  set (E := Eimg (Ereg (ms_regs ms3) (u_mb_extra md kbs mbs))) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (u_mb_extra md kbs mbs) (Z_to_bv 64 0)).
  { intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; clia). apply ew_Ereg_extra. }
  assert (E22 : ew E 22 = Z_to_bv 64 md) by (rewrite (EL 22%nat 22%bv ltac:(clia) eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (LA_G_NL + 0x40000)) by (rewrite (EL 23%nat 23%bv ltac:(clia) eq_refl); exact R23).
  assert (E33 : ew E 33 = Z_to_bv 64 (nk_socket_errno kbs)) by exact (EX 1%nat ltac:(clia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (nk_send_errno kbs)) by exact (EX 2%nat ltac:(clia)).
  assert (E35 : ew E 35 = Z_to_bv 64 (md_n_mark mbs)) by exact (EX 3%nat ltac:(clia)).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  assert (Bm64 : md + 8856 <= 2 ^ 64) by clia.
  rewrite (lf_shape_eta fy LU_kret ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_kret)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { (* the writes: the model's four fields, g_nl.n_sent *)
    cbn [ss_mem u_mb_ss]. unfold u_mb_rgs.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_wlo YP09.r_whi u_slot_rg] in Ha; clia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_wlo YP09.r_whi u_sh_rg] in Ha; clia|].
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_md0_rg base_val] in Ha. rewrite E22 in Ha.
      rewrite unsigned_lit_small in Ha by clia.
      left. split; [|clia]. right; right; left. exists md, MD_SIZE. split; [exact Bmd|]. split; [exact Bmc|].
      unfold req_size, MD_SIZE. cbn. clia. }
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_mdnr_rg base_val] in Ha. rewrite E22 in Ha.
      rewrite unsigned_lit_small in Ha by clia.
      left. split; [|clia]. right; right; left. exists md, MD_SIZE. split; [exact Bmd|]. split; [exact Bmc|].
      unfold req_size, MD_SIZE. cbn. clia. }
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_wlo YP09.r_whi u_nm_rg] in Ha; clia|].
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
  { apply (u_kagree_frame E (ss_mem u_mb_ss) _ _ X HFrA). intros a (r & Hr & Hw). unfold X.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem u_mb_ss] in Hr. unfold u_mb_rgs in Hr. cbn [In] in Hr. unfold lf_mb_rng, MD_N_REQ, NK_N_SENT.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_slot_rg u_sh_rg u_md0_rg u_mdnr_rg u_nm_rg u_gnl_rg u_gns_rg base_val]
        in Hw; try clia.
    - rewrite E22, unsigned_lit_small in Hw by clia. clia.
    - rewrite E22, unsigned_lit_small in Hw by clia. clia.
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
    - cbn [base_val YP09.r_base]. rewrite E22. apply unsigned_lit_small. clia.
    - cbn. right; right; left. reflexivity.
    - apply lf_slice_length; unfold NK_SOCKET_ERRNO, NK_SIZE in *; clia.
    - rewrite (lf_sv_off E 33 _ 0 E33) by (unfold nk_socket_errno, fld_u32; clia). rewrite Z.add_0_r. reflexivity.
    - clia.
    - clia. }
  assert (A2 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4)).
  { pose proof (u_rdn4_range kbs NK_SEND_ERRNO) as Rv.
    apply (u_word4 E _ _ md MD_SEND_ERRNO (SOff 34 0) _ (RG 2%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E22. apply unsigned_lit_small. clia.
    - cbn. right; left. reflexivity.
    - apply lf_slice_length; unfold NK_SEND_ERRNO, NK_SIZE in *; clia.
    - rewrite (lf_sv_off E 34 _ 0 E34) by (unfold nk_send_errno, fld_u32; clia). rewrite Z.add_0_r. reflexivity.
    - unfold MD_SEND_ERRNO; clia.
    - unfold MD_SEND_ERRNO; clia. }
  assert (A3 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_NEXT) lf_z4).
  { apply (u_word4 E _ _ md MD_NEXT (SLit 0) _ (RG 2%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E22. apply unsigned_lit_small. clia.
    - cbn. left. reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold MD_NEXT; clia.
    - unfold MD_NEXT; clia. }
  assert (A4 : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_N_REQ) lf_z4).
  { apply (u_word4 E _ _ md MD_N_REQ (SLit 0) _ (RG 3%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E22. apply unsigned_lit_small. clia.
    - cbn. left. reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold MD_N_REQ; clia.
    - unfold MD_N_REQ; clia. }
  assert (A5 : abytes SEGS (rdW W3 (ms_mem msA)) (LA_G_NL + NK_N_SENT) lf_z4).
  { replace (LA_G_NL + NK_N_SENT) with ((LA_G_NL + 0x40000) + 8872) by (unfold NK_N_SENT; clia).
    apply (u_word4 E _ _ (LA_G_NL + 0x40000) 8872 (SLit 0) _ (RG 6%nat _ eq_refl)).
    - cbn [base_val YP09.r_base]. rewrite E23. apply unsigned_lit_small. unfold LA_G_NL; clia.
    - cbn. left. reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold LA_G_NL; clia.
    - unfold LA_G_NL; clia. }
  pose proof (fun a (HXa : X a) => u_mb_notX cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk HXa)
    as NX.
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
  (* close the three write windows: the rest of the stretch writes nothing *)
  pose proof (ar_close1 fy E _ _ 2%nat _ HS eq_refl ltac:(vm_compute; reflexivity)) as HS'. clear HS RG.
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem list_upd] in HS'.
  pose proof (ar_close1 fy E _ _ 3%nat _ HS' eq_refl ltac:(vm_compute; reflexivity)) as HS. clear HS'.
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem list_upd] in HS.
  pose proof (ar_close1 fy E _ _ 6%nat _ HS eq_refl ltac:(vm_compute; reflexivity)) as HS'. clear HS.
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem list_upd] in HS'. rename HS' into HS.
  assert (MK0 : md_n_mark (lf_mbs_mb kbs mbs) = md_n_mark mbs) by (apply lf_mbs_mb_n_mark; assumption).
  pose proof Hdat' as (_ & Dwf' & _ & _ & _ & _ & _ & Dmwf' & _ & _ & (Dmn & Dmm) & _).
  pose proof Dmwf' as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
  assert (Rnm : 0 <= md_n_mark mbs <= 32) by (rewrite <- MK0; clia).
  assert (Rv35 : 0 <= md_n_mark mbs < 2 ^ 64) by clia.
  pose proof (lf_mbs_mb_sock kbs mbs KL ML) as Msock. pose proof (lf_mbs_mb_send kbs mbs KL ML) as Msend.
  pose proof (lf_mbs_mb_next kbs mbs KL ML) as Mnext.
  pose proof (lf_kbs_mb_fields kbs KL) as (_ & _ & _ & _ & _ & Knx & Knc & Ken & Kso & Kse).
  assert (KSEQ : md_kstate (lf_mbs_mb kbs mbs) (lf_kbs_mb kbs) = nk_kstate (lf_kbs_mb kbs)).
  { unfold md_kstate, nk_kstate. rewrite Mnext, Knx, Hnx, Msock, Msend, Kso, Kse. reflexivity. }
  assert (REQ0 : md_reqs (lf_mbs_mb kbs mbs) = []) by (unfold md_reqs; rewrite Hnr'; reflexivity).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x760 taken: n_mark = 0, to +0x924 *)
    rewrite (lf_sv_off E 35 _ 0 E35 Rv35 ltac:(clia)) in Hc. rewrite Z.add_0_r in Hc.
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (u_bge0 (md_n_mark mbs) ltac:(clia)) in Hc. apply Z.leb_le in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LU_exit; [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md4) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md4) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk _ _ gbs T3 _ ly3 S3 W3 msA md4
      W3 msB md5 KB (wcarry_on_grows _ _ _ HGB) Fd5 Fs5 (fun a _ H => H) Hsv' Hhd' Hfs' Hsl' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfs2 & Hsl2 & Hjbk2 & Hblk2 & Hdat2).
    pose proof (lf_cur_keep (fun _ => False) cx W3 msA W3 msB P N KB (fun a _ H => H) Hcur') as Hcur2.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
    prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (E32 : ew E 32 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF md)) by exact (EX 0%nat ltac:(lia)).
    assert (S18 : getr (ms_regs msB) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK))).
    { rewrite Q18, E32. unfold shadow_of_addr, w64, MD_N_MARK.
      assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc8); rewrite Hc8;
        replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
      pose proof (Z.div_mod md 8 ltac:(lia)) as D. rewrite Hmd8, Z.add_0_r in D.
      assert (Dv : (md + 8852) / 8 = md / 8 + 1106).
      { rewrite D at 1. replace (8 * (md / 8) + 8852) with (4 + (md / 8 + 1106) * 8) by lia.
        rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
      rewrite Dv. rewrite unsigned_lit_small; [f_equal; lia|].
      split; [unfold SHADOW_OFF; pose proof (Z.div_pos md 8 ltac:(lia) ltac:(lia)); lia|].
      assert (md / 8 <= 2 ^ 61) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF; lia. }
    assert (UM : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs) gbs T3 LF_SH0
      cx fp k2 ly3 S3 W3 msB md5).
    { split; [exact Hi|]. split.
      { unfold lf_core in *. rewrite Q2, Q8, Q9, Q3, Q4. exact Hcore. }
      split.
      { unfold u_regs in *. rewrite Q19, Q21, Q22, Q24, Q25, Q26, Q27. exact Hreg. }
      split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
      split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. rewrite Hop'. exact Hop. }
    apply (HX cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, (lf_kbs_mb kbs), (lf_mbs_mb kbs mbs), gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    split; [exact S18|]. split; [exact UM|]. split; [exact Hns'|].
    rewrite REQ0, Dmm. unfold md_marks. rewrite MK0. replace (md_n_mark mbs) with 0 by clia. reflexivity.
  - (* +0x760 not taken: n_mark > 0, to the loop head +0x76c *)
    rewrite (lf_sv_off E 35 _ 0 E35 Rv35 ltac:(clia)) in Hc. rewrite Z.add_0_r in Hc.
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (u_bge0 (md_n_mark mbs) ltac:(clia)) in Hc. apply Z.leb_gt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LU_body; [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md4) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md4) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    destruct (lf_cut_keep B MT MS la_nul (fun _ => False) cx fp k2 _ _ _ _ md mk _ _ gbs T3 _ ly3 S3 W3 msA md4
      W3 msB md5 KB (wcarry_on_grows _ _ _ HGB) Fd5 Fs5 (fun a _ H => H) Hsv' Hhd' Hfs' Hsl' Hjbk' Hblk' Hdat')
      as (Hsv2 & Hhd2 & Hfs2 & Hsl2 & Hjbk2 & Hblk2 & Hdat2).
    pose proof (lf_cur_keep (fun _ => False) cx W3 msA W3 msB P N KB (fun a _ H => H) Hcur') as Hcur2.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
    prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (E32 : ew E 32 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF md)) by exact (EX 0%nat ltac:(lia)).
    assert (S18 : getr (ms_regs msB) 18 = w64 (shadow_of_addr SHADOW_OFF (md + MD_N_MARK))).
    { rewrite Q18, E32. unfold shadow_of_addr, w64, MD_N_MARK.
      assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc8); rewrite Hc8;
        replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
      pose proof (Z.div_mod md 8 ltac:(lia)) as D. rewrite Hmd8, Z.add_0_r in D.
      assert (Dv : (md + 8852) / 8 = md / 8 + 1106).
      { rewrite D at 1. replace (8 * (md / 8) + 8852) with (4 + (md / 8 + 1106) * 8) by lia.
        rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
      rewrite Dv. rewrite unsigned_lit_small; [f_equal; lia|].
      split; [unfold SHADOW_OFF; pose proof (Z.div_pos md 8 ltac:(lia) ltac:(lia)); lia|].
      assert (md / 8 <= 2 ^ 61) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF; lia. }
    assert (UM : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs) gbs T3 LF_SH0
      cx fp k2 ly3 S3 W3 msB md5).
    { split; [exact Hi|]. split.
      { unfold lf_core in *. rewrite Q2, Q8, Q9, Q3, Q4. exact Hcore. }
      split.
      { unfold u_regs in *. rewrite Q19, Q21, Q22, Q24, Q25, Q26, Q27. exact Hreg. }
      split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
      split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|]. rewrite Hop'. exact Hop. }
    prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23.
    apply (HL cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, (lf_kbs_mb kbs), (lf_mbs_mb kbs mbs), gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)|].
    split; [rewrite Q23, E22; unfold w64; rewrite unsigned_lit_small by clia; f_equal; unfold MD_MARK, MARK_LEN; clia|].
    split; [rewrite Q20; reflexivity|].
    split; [exact S18|]. split; [exact UM|].
    split; [rewrite MK0; clia|]. split; [exact Hns'|].
    rewrite REQ0, KSEQ. unfold unmark. reflexivity.
Qed.

End a.
