(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- the walk of LLVMFuzzerTestOneInput (fuzz_pcap.asan-ubsan of libreac v1.9.0, pin
   sha256 9e66f771f22af67a..., 0x80818, listing offset PP_entry = 0x90 of lib/B/Prog/PcapList.v) from the copy of
   the file to the first record, a Theorem Labs lane of the walk (lib/B/Prog/PcapEntryDefs.v, "The walks"): the stretches
     A      PP_K1 0x809b8 -> fuzz_dup's NULL test (PP_dup0 0x809bc, PP_dupnull 0x809c0) -> __asan_memcpy (jal 0x809d8)
            -> g_file := file (0x809dc) -> `ps` in scope (0x809e0 .. 0x809e8) -> __asan_memset (jal 0x809fc)
            -> pcap_source_open (jal 0x80a0c) -> PP_K2 0x80a10;
     M      PP_K2 -> the spills 0x80a20 .. 0x80a28 -> g_file_len >= 4 (0x80a2c) -> rd32 (jal 0x80a38) -> PP_KM 0x80a3c;
     B_acc  PP_KM (s3 = 0) -> the header checks 0x80a40 .. 0x80a7c -> PP_ref 0x80a80 -> ps.swapped check 0x80ab0 ->
            cap (0x80ab4 .. 0x80abc) -> malloc (jal 0x80ac8) -> PP_K3 0x80acc;
     B_ref  PP_K2 (g_file_len < 4: 0x80a58, 0x80a5c) or PP_KM (s3 = -1) -> PP_ref -> ps.f = NULL (0x80a84, 0x80a88) ->
            free (jal 0x80a90) -> 0x80a94, j 0x80a98 -> PP_K12r 0x80eac;
     C      PP_K3 -> PP_bufnull 0x80ad0 -> `ts` in scope, ts := ~0 (0x80ad4 .. 0x80afc) -> pcap_source_next (jal 0x80b00)
            -> PP_KD 0x80b04.
   Each cut lemma has lib/B/Prog/PcapEntryPhases.v's form `pe_from SK B MT KS POST GI_next -> pe_from SK B MT KS POST
   GI_self` at that file's waypoint invariants GI_*. The refused arm reaches PP_ref from two cuts (PP_K2 when
   g_file_len < 4, PP_KM when the open was refused), so it gets a cut of its own, GI_REF below (local to this file):
   pe_from_REF proves B_ref's tail from it.

   No stretch here passes a UBSan guard (PcapEntryDefs.PE_GUARDS: the 18 guards are at 0x80954 .. 0x809a4, before
   PP_K1, and at 0x80b80 and after, after PP_KD) or an __asan_report_* call (the five report calls are at 0x80e00 and
   0x8104c .. 0x8105c; nothing between 0x809b8 and 0x80b04 branches to them). The abort() branches of these stretches
   (0x809c0, 0x80a54, 0x80a60, 0x80a7c, 0x80a88, 0x80ab0, 0x80ad0) are each refuted by the facts of the cut before them,
   so no run reaches PP_abort (__asan_handle_no_return, abort) from here.

   Rule 24: no released or cold proof walks this function on an asan-ubsan image (index v5 2026-10-28T21:58:24Z /
   23:22:17Z, a search of the proof index for LLVMFuzzerTestOneInput rc=0, no row names libreac/fuzz_pcap; the released fuzz_pcap
   harness walks lib/U/Prog/Slot/USegE.v etc. are for the v1.8 UBSAN image: CONFIRMED by a Theorem Labs lane, 23:47Z). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81 PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame PaGxSites Rd32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryKit.
(* cut C (PP_K3 -> PP_KD) dispatches pcap_source_next through a Theorem Labs lane's call-site lift. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryCalls.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE01 YI01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapSourceClose.
Import ListNotations.
Module BCLO := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceClose.
Unset Lia Cache. Unset Nia Cache.
(* lib/A/AE2f.v (cgif's text) turns zify's euclidean-division handling off for every file that reaches it
   (a Theorem Labs lane 00:36Z); this file needs it for the shadow address pSH = SHADOW_OFF + F / 8. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation SIGMA := (pa_sigma).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Local Notation rd W3 ms3 := (mrestrict (w_H W3) (ms_mem ms3)).

(* ---- the refused arm at PP_ref (0x80a80, `beqz s3` not taken): a cut local to this file ---- *)
(* Reached from PP_K2 when g_file_len < 4 (0x80a2c taken, 0x80a5c `beq s3,s5` taken with s5 = -1) and from PP_KM when
   the open answered -1 (0x80a50 / 0x80a7c). The open's answer r = -1 is in s3 (0x80a10), the copy in s2, &ps in s4;
   the side-stack result, the frame's shadow and the frame were spilled (0x80a20 .. 0x80a28), which the leave reads back
   (GI_K12r). The copy is the only block the call holds; ps.f is NULL and no stream is open. *)
Definition GI_REF (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut B cx fp PP_ref PSH_ps k 4 acc (PA_K2r MT cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = false /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 19 = w64 (-1) /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  pslot cx W3 ms3 PS_FK (pF cx fp) /\ pslot cx W3 ms3 PS_SH (pSH cx fp) /\ pslot cx W3 ms3 PS_F (pF cx fp) /\
  p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* ---- the cut statements ---- *)
(* A: PP_K1 -> PP_K2. *)
Definition pe_from_K1_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K2 B MT KS) -> pe_from SK B MT KS POST (GI_K1 B MT KS).
(* M, and B_ref's entry from PP_K2: PP_K2 -> PP_KM (g_file_len >= 4) or PP_ref (g_file_len < 4). *)
Definition pe_from_K2_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_KM B MT KS) -> pe_from SK B MT KS POST GI_REF ->
  pe_from SK B MT KS POST (GI_K2 B MT KS).
(* B_acc, and B_ref's entry from PP_KM: PP_KM -> PP_K3 (accepted) or PP_ref (refused). *)
Definition pe_from_KM_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K3 B MT KS) -> pe_from SK B MT KS POST GI_REF ->
  pe_from SK B MT KS POST (GI_KM B MT KS).
(* B_ref's tail: PP_ref -> free -> PP_K12r. *)
Definition pe_from_REF_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K12r B MT KS) -> pe_from SK B MT KS POST GI_REF.
(* C: PP_K3 -> PP_KD. *)
Definition pe_from_K3_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_KD B MT KS) -> pe_from SK B MT KS POST (GI_K3 B MT KS).

(* The lane's whole stretch, from PP_K1 to the two exits PP_KD and PP_K12r, composed from the cut statements. *)
Lemma pe_from_open_compose :
  pe_from_K1_stmt -> pe_from_K2_stmt -> pe_from_KM_stmt -> pe_from_REF_stmt -> pe_from_K3_stmt ->
  forall POST, pe_from SK B MT KS POST (GI_KD B MT KS) -> pe_from SK B MT KS POST (GI_K12r B MT KS) ->
  pe_from SK B MT KS POST (GI_K1 B MT KS).
Proof.
  intros H1 H2 HM HR H3 POST HD H12.
  pose proof (HR POST H12) as HREF.
  apply H1. apply H2; [|exact HREF]. apply HM; [|exact HREF]. apply H3. exact HD.
Qed.

(* ==== the proofs ==== *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.

(* The machine state of a cut, rebuilt from its components. *)
Lemma ms_eta : forall ms : machine_state, ms_resv ms = None -> ms_svc_pending ms = None -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr -> ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

(* The spill-slot base s1 of the body, and the frame, in the allocator's picture: s1 lies in the stack, far above
   the allocator's ceiling, and the frame lies under it (pe_base's afn_pre and the journal's own window). *)
Lemma pe_sp1_bounds : forall cx fp k ly3 S3 W3 memq md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 memq md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  alloc_ceiling + 32368 <= c_sp1 cx /\ c_sp1 cx mod 32 = 0 /\
  spZ (PcapEntryDefs.c_regs cx) - 288 <= c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 /\
  frame_addr ly3 PE_CID fp = pF cx fp /\
  4096 <= pF cx fp /\ pF cx fp + PE_FRAME <= alloc_ceiling /\ in_app (pF cx fp) PE_FRAME.
Proof.
intros cx fp k ly3 S3 W3 memq md3 HB HJ Hfrs.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esp1 & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLS : LLVMF_STK = 32768) by reflexivity.
destruct HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memq md3 PE_CID fp HAR Hin) as (Hf4096 & Hfceil & Hfapp).
assert (EFA : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (EPE : fs_frame_bytes PE_CID = PE_FRAME) by (vm_compute; reflexivity).
rewrite EFA in Hf4096, Hfceil, Hfapp. rewrite EPE in Hfceil, Hfapp.
assert (Hsp1 : spZ (PcapEntryDefs.c_regs cx) - 288 <= c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0).
{ rewrite Esp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z_div_mod_eq_full (spZ (PcapEntryDefs.c_regs cx) - 256) 32) as D.
  pose proof (Z.mod_pos_bound (spZ (PcapEntryDefs.c_regs cx) - 256) 32 ltac:(lia)) as M.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
split; [lia|]. split; [exact (proj2 Hsp1)|]. split; [exact (proj1 Hsp1)|].
split; [exact EFA|]. split; [exact Hf4096|]. split; [exact Hfceil | exact Hfapp].
Qed.

(* ---- B_ref's tail ---- *)
Definition SB_E : Z := 0x7fff8000.
Definition ref_regions : smem :=
  [YP09.mkRegion (Some 20%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0))];
   YP09.mkRegion (Some 9%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 33 0))]].
Definition ref_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB_E SB_E 0)] [] [].
Definition ss_ref0 : sstate := mkSS PP_ref sr_atoms ref_regions None ref_facts.
Definition ref_extra (sh : Z) : list word := map (Z_to_bv 64) [SB_E; sh].

Lemma ref_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pregs cx ms3 ->
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) ->
  pslot cx W3 ms3 PS_SH (pSH cx fp) ->
  p_psnull cx fp W3 ms3 ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (ref_extra (pSH cx fp)))) ss_ref0
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_ref)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs Hpregs R20 SSH Hnull.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
set (E := Eimg (Ereg (ms_regs ms3) (ref_extra (pSH cx fp)))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (ref_extra (pSH cx fp))) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (Usp : bv_unsigned (ew E 2) = c_sp1 cx) by (rewrite E2, Rsp; apply unsigned_lit_small; lia).
assert (Us1 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; apply unsigned_lit_small; lia).
assert (HPS : pPS cx fp = pF cx fp + PO_PS) by reflexivity.
assert (HpFk : 0 <= pF cx fp < kHighMemEnd) by (unfold kHighMemEnd, PE_FRAME in *; lia).
assert (HSHb : 0 <= pSH cx fp < 2 ^ (8 * Z.of_N 8)).
{ unfold pSH, shadow_of_addr.
  pose proof (shadow_addr_bounds (pF cx fp) HpFk) as HB2. unfold shadow_addr in HB2.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold SHADOW_OFF in *.
  unfold kLowMemEnd, kHighShadowEnd in HB2. lia. }
assert (Ups : bv_unsigned (ew E 20) = pPS cx fp)
  by (rewrite E20, R20; apply unsigned_lit_small; unfold pPS, PO_PS, PE_FRAME in *; lia).
rewrite restrict_mkst_fx. unfold ss_ref0. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ref_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  * cbn [base_val]. fold E. rewrite Ups. split; [unfold pPS, PO_PS, PE_FRAME in *; lia|].
    split; [unfold pPS, PO_PS, PE_FRAME in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pPS cx fp) 0 8 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Hnull.
  * cbn [base_val]. fold E. rewrite Us1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (c_sp1 cx) 40 8 (SOff 33 0) (pSH cx fp));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | exact HSHb | zside |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SSH).
+ apply pairwise_disjoint_of_extents.
  unfold ref_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  fold E. rewrite Ups, Us1. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold pPS, PO_PS, PE_FRAME in *. repeat split; lia.
+ split; [|split; [exact I | exact I]].
  cbn [ref_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32, !unsigned_lit_small by (unfold SB_E; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SB_E; lia |
    (rewrite <- Z.land_ones by lia; idtac)].
Qed.

(* pe_base's gx side condition and the free-site trace, projected. *)
Lemma pb_HG : forall cx, pe_base SK B MT KS cx -> gx_ok SEGS B pe_G.
Proof.
intros cx H. unfold pe_base in H.
destruct H as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&HG&_). exact HG.
Qed.
Lemma pb_ftr : forall cx (regsT : bvmap 5 word), pe_base SK B MT KS cx ->
  In (raZ regsT - BASE) PE_FREE_SITES ->
  In (call_trace0 (pc_free_ra0 (as_code B)) regsT (pch cx)) (as_universe B).
Proof.
intros cx regsT H. unfold pe_base in H.
destruct H as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hftr). exact (Hftr regsT).
Qed.

(* The chain at a body call (sp = s1, s0 = sp0): it is pe_base's `pch cx` (cgif's rt_chain, ported). The reader rd is
   the call-state view; the saved ra and caller s0 come from psaved, the memory above sp0 from the journal. *)
Lemma pe_chain : forall cx fp regsT ly3 S3 W3 memq md3 k (rd : reader),
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 memq md3 k ->
  ly_top ly3 = ly_top (c_ly cx) ->
  rd = aview SEGS (w_H W3) memq ->
  getr regsT 8 = w64 (spZ (PcapEntryDefs.c_regs cx)) ->
  spZ regsT = c_sp1 cx ->
  4096 <= raZ regsT ->
  rdword rd (spZ (PcapEntryDefs.c_regs cx) - 8) = Some (raZ (PcapEntryDefs.c_regs cx)) ->
  rdword rd (spZ (PcapEntryDefs.c_regs cx) - 16) = Some (s0Z (PcapEntryDefs.c_regs cx)) ->
  chain_pre ly3 rd regsT (pch cx).
Proof.
intros cx fp regsT ly3 S3 W3 memq md3 k rd HB HJ Etop Erd Rs0 Rsp Hra4 Hra8 Hs016.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 memq md3 HB HJ ltac:(
  destruct HJ as (_&_&(memS & HJi & _)&_); pose proof HJi as (_&_&_&_&_&Hfrs0&_);
  (* frames S3 = own ++ frames (c_S cx); own = [(PE_CID,fp)], frames c_S = [] *)
  rewrite Hfrs0; pose proof HB as (HPRE0 & _); pose proof HPRE0 as (HAR0 & _);
  pose proof HB as (_&_&_&_&_&_&Hfe&_); rewrite Hfe; reflexivity))
  as (Hs1lo & Hs1al & Hsp1 & _).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & Hra0 & Hra04 & _ & _ & Hstk & _ & Hch0 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp0al8 : spZ (PcapEntryDefs.c_regs cx) mod 8 = 0)
  by (rewrite (Z.mod_divide _ 8 ltac:(lia)); apply (Z.divide_trans 8 16); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hal16]]).
assert (Hagree : forall a, spZ (PcapEntryDefs.c_regs cx) <= a < 2 ^ 64 ->
  rd a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ destruct HJ as (_ & _ & (memS & HJi & Hag) & _).
  pose proof HJi as (_&_&_&_&_&_&_&_&F1&_).
  intros a Ha. rewrite Erd.
  rewrite (F1 a ltac:(lia) ltac:(rewrite Z.add_0_r; lia)).
  apply aview_eq_of. apply Hag.
  rewrite unsigned_lit_small by lia. apply inGb_false. intros HGa.
  destruct (pb_HG cx HB a HGa) as [Hi _].
  pose proof (pa_img_range a Hi). unfold pcap_img_end, YImgTop.IMG_TOP in *. lia. }
assert (Hac : achain (c_ly cx) rd (c_sp1 cx) (spZ (PcapEntryDefs.c_regs cx)) (pch cx)).
{ unfold pch.
  destruct (Z.ltb_spec (spZ (PcapEntryDefs.c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
  - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) rd (spZ (PcapEntryDefs.c_regs cx))
             (s0Z (PcapEntryDefs.c_regs cx)) (raZ (PcapEntryDefs.c_regs cx)) [] (c_sp1 cx) Hch0);
      [lia | intros a Ha; apply Hagree; lia
       | exact Hra8 | exact Hs016
       | lia | lia | exact Hsp0al8 | lia | lia ].
  - left. split; [right; left; lia | reflexivity]. }
apply (achain_ly_top (c_ly cx) ly3) in Hac; [|exact Etop].
apply (achain_chain_pre ly3 rd (c_sp1 cx) (spZ (PcapEntryDefs.c_regs cx)) (pch cx) regsT Hac);
  [ rewrite Rsp; lia
  | unfold s0Z; rewrite Rs0; apply unsigned_lit_small; unfold spZ;
    pose proof (bv_unsigned_in_range 64 (getr (PcapEntryDefs.c_regs cx) 2)) as Hr2;
    change (bv_modulus 64) with (2 ^ 64) in Hr2; lia
  | exact Hra4 ].
Qed.

(* ---- M: PP_K2 0x80a10 -> PP_KM 0x80a3c (g_file_len >= 4, rd32) / PP_ref 0x80a80 (g_file_len < 4) ---- *)
(* The symbolic state at PP_K2. s8 holds the listing's hi atom (A_HI 8, since `auipc s8` 0x809a8), so the listing's
   PLdHi of g_file_len (`ld a0,0x498(s8)` 0x80a14) reads object 4 itself. Atoms: the registers, 32 = |F|
   (g_file_len's word), 33 = the first input byte d (PS_D's word). Regions: the spill slots
   [s1 + 0x10, s1 + 0x30), written by the three spills 0x80a20 .. 0x80a28 (PS_D, between them, is not written), and
   g_file_len (object 4), read only. *)
Definition k2_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 16 48 16 48 [YP09.mkChunk PS_D (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]].
Definition k2_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_k2 : sstate :=
  mkSS PP_K2 (sr_set sr_atoms (24%bv : bv 5) (SOff (A_HI 8) 0)) k2_regions None k2_facts.
Definition k2_extra (cx : ecx) : list word := map (Z_to_bv 64) [p_nF cx; p_d cx].

Lemma k2_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pe_body cx fp PP_K2 W3 ms3 PSH_ps ->
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) ->
  pslot cx W3 ms3 PS_D (p_d cx) ->
  pval W3 ms3 (pa_val (A_OBJ 4)) 8 (p_nF cx) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (k2_extra cx))) ss_k2 (restrict (w_H W3) ms3) /\
  sh_ok SEGS EBx [] (Eimg (Ereg (ms_regs ms3) (k2_extra cx))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs HBody R24 SD Hlen.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HBody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & (Rsp & Rs0 & Rs1 & Rgp & Rtp) & _).
pose proof (pa_val_range (A_HI 8)) as Rh8. pose proof (pa_val_range (A_OBJ 4)) as Rv4.
pose proof (pa_obj_img 4 ltac:(lia)) as Ro4. unfold pcap_img_end, YImgTop.IMG_TOP in Ro4.
pose proof (p_sizes cx) as (HnF & _). pose proof (p_d_range cx) as Hd.
assert (Hn26 : c_n cx < 2 ^ 26) by (pose proof HB as (_ & _ & _ & _ & Hn & _); destruct Hn as [[-> _] | [? _]]; lia).
set (E := Eimg (Ereg (ms_regs ms3) (k2_extra cx))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (k2_extra cx)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact Rs1).
assert (E32 : ew E 32 = Z_to_bv 64 (p_nF cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (U4 : bv_unsigned (ew E (A_OBJ 4)) = pa_val (A_OBJ 4))
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K2)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3; cbn in Hpc, Hrv, Hsv, Hrom, Hfreg, Hfcsr |- *; subst; reflexivity. }
assert (HS0 : st_ok_pi SEGS pa_val E (mkSS PP_K2 sr_atoms k2_regions None k2_facts) (restrict (w_H W3) ms3)).
{ rewrite Hms at 1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold k2_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
    + rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; unfold LLVMF_STK in *; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_D 8 (SOff 33 0) (p_d cx));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SD).
    + rewrite U4. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 4)) 0 8 (SOff 32 0) (p_nF cx));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
      rewrite Z.add_0_r. exact Hlen.
  - apply pairwise_disjoint_of_extents.
    unfold k2_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    fold E. rewrite U9, U4. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold LLVMF_STK in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [k2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite U9. change (2 ^ 5) with 32.
    unfold LLVMF_STK in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
(* pin s8 to the listing's hi atom, so the PLdHi of g_file_len runs *)
assert (HS8 : sv_denot E (SOff (A_HI 8) 0) = getr (ms_regs (restrict (w_H W3) ms3)) 24).
{ cbn [restrict ms_regs]. rewrite R24. cbn [sv_denot]. subst E.
  rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
exact (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff (A_HI 8) 0) HS0 eq_refl HS8).
Qed.

(* A spill slot the run's slot region holds: its chunk at od is the word of atom n. *)
Lemma k2_slot : forall E (W3 : world SEGS) (ms : machine_state) cx cs lo hi wlo whi od (n : nat) v,
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = c_sp1 cx -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> pslot cx W3 ms od v.
Proof.
intros E W3 ms cx cs lo hi wlo whi od n v HR H9 Hin Hn Hv. unfold pslot.
apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms) (c_sp1 cx + od) v); [|exact Hv].
exact (field_of_region E _ 9%nat (c_sp1 cx) cs lo hi wlo whi od 8 (SOff n 0) v HR H9 Hin
         ltac:(cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
         ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)).
Qed.

(* The first four bytes of an array. *)
Lemma k2_copy4 : forall m base l, garr8 SEGS m base l -> 4 <= Z.of_nat (length l) ->
  garr8 SEGS m base [nth 0 l 0; nth 1 l 0; nth 2 l 0; nth 3 l 0].
Proof.
intros m base l Hg Hn j Hj. cbn [length] in Hj.
destruct j as [|[|[|[|j]]]];
  [exact (Hg 0%nat ltac:(lia)) | exact (Hg 1%nat ltac:(lia)) | exact (Hg 2%nat ltac:(lia)) | exact (Hg 3%nat ltac:(lia)) | lia].
Qed.

(* The magic: rd32(file, 0) reads the copy's first four bytes little-endian (a1 = 0), which is PST.pcap_magic of F
   (lib/B/Prog/Rd32.v trd32_val; the copy's bytes are p_C cx = map bv_unsigned (p_F cx)). *)
Lemma k2_magic : forall cx,
  Rd32.trd32_val (Z_to_bv 64 0) (nth 0 (p_C cx) 0) (nth 1 (p_C cx) 0) (nth 2 (p_C cx) 0) (nth 3 (p_C cx) 0) =
  p_magic cx.
Proof.
intros cx.
assert (Hn : forall i, nth i (p_C cx) 0 = PST.pcap_byte (p_F cx) i)
  by (intros i; exact (map_nth (fun x : byte => bv_unsigned x) (p_F cx) (Z_to_bv 8 0) i)).
rewrite !Hn. unfold Rd32.trd32_val, p_magic, PST.pcap_magic.
replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (symmetry; apply bv_eqb_eq; reflexivity).
reflexivity.
Qed.

(* The awr side condition of a run from a state of this stretch (the slot window at s1, g_file_len read only), and
   what the run keeps (every byte outside [s1 + 0x10, s1 + 0x30)). *)
Local Ltac k2_awr cx U9 :=
  apply awr_ok_x_of0; cbn [ss_mem];
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (PcapEntryDefs.c_regs cx));
  [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil].
Local Ltac k2_kept cx HFr U9 :=
  intros a Ha Hn;
  refine (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => c_sp1 cx + 16 <= x < c_sp1 cx + 48) HFr _ a Ha Hn);
  intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia|]);
  destruct Hin.

Lemma pe_from_K2 : pe_from_K2_stmt.
Proof.
unfold pe_from_K2_stmt. intros POST HKM HREF.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HI as (b & Hbody & Hn26 & Hfds & Hfs & R18 & R20 & R22 & R23 & R24 & R25 & R26 & SD & SSHB & SF0
  & Hglob & Hcopy & Harm).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (destruct Harm as [(_ & _ & _ & _ & h & Hperm & _) | (_ & _ & _ & _ & Hperm & _)];
      apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
assert (WF : forall l x (m : Model), m_fds (with_vm_backing l x m) = m_fds m /\ m_fs (with_vm_backing l x m) = m_fs m)
  by (intros l x [fd [mp lz mt] io fs pr li tm]; split; reflexivity).
unfold LLVMF_STK in Hspc, Hpres.
destruct (k2_entry cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr Hbody R24 SD (proj2 Hglob)) as [HS SHOK].
remember (Eimg (Ereg (ms_regs ms3) (k2_extra cx))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (k2_extra cx)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (p_nF cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (Eh8 : ew E (A_HI 8) = Z_to_bv 64 (pa_val (A_HI 8)))
  by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 (pF cx fp)) by (rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (pSH cx fp)) by (rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R25).
assert (E26 : ew E 26 = Z_to_bv 64 (pF cx fp)) by (rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R26).
assert (HSHb : 0 <= pSH cx fp < 2 ^ 64).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos (pF cx fp) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (pF cx fp) 8 (2 ^ 61) ltac:(lia) ltac:(unfold PE_FRAME in Hf1; lia)). lia. }
pose proof (p_d_range cx) as Hd.
assert (HpFb : 0 <= pF cx fp < 2 ^ 64) by (unfold PE_FRAME in Hf1; lia).
clear HEdef.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* 0x80a10 .. 0x80a28: s3 := r, a0 := g_file_len (PLdHi of object 4), a1 := 4, s5 := -1, the three spills;
   the run stops at the bltu 0x80a2c *)
paj_run_tok RUN HS HJ SHOK Espan; [k2_awr cx U9|].
assert (UN1 : mk W3 (ms_mem ms3) (ms_mem ms) (c_sp1 cx + 16) (c_sp1 cx + 48)) by (k2_kept cx HFr U9).
clear HF HFr HG. rename ms into ms1. rename mat into mat1.
psrr_branch_tok RUN BR HS SHOK Espan.
- (* 0x80a2c taken, g_file_len < 4: 0x80a58 a1 := 0, then `beq s3,s5` 0x80a5c *)
  cbn [branch_taken sv_denot] in Hc. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, bv_ltu_unsigned in Hc.
  rewrite !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hlt4.
  (* a good file has at least 24 bytes, so this one is not good, and the open refused it: r = -1 *)
  assert (Hng : p_good cx = false).
  { unfold p_good, PST.pcap_good. apply andb_false_iff. left. apply Z.leb_gt. unfold p_nF in Hlt4. lia. }
  destruct Harm as [(Hg & _) | (_ & R10 & Hk & Hacc & Hperm & Hnull & Hsn)]; [rewrite Hng in Hg; discriminate Hg|].
  paj_run_tok RUN HS HJ SHOK Espan; [k2_awr cx U9|].
  assert (UN2 : mk W3 (ms_mem ms1) (ms_mem ms) (c_sp1 cx + 16) (c_sp1 cx + 48)) by (k2_kept cx HFr U9).
  clear HF HFr HG. rename ms into ms2. rename mat into mat2.
  psrr_branch_tok RUN BR HS SHOK Espan.
  + (* 0x80a5c taken (s3 = r = -1 = s5): PP_ref *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Espan PP_ref; [k2_awr cx U9|].
    assert (UN3 : mk W3 (ms_mem ms2) (ms_mem ms) (c_sp1 cx + 16) (c_sp1 cx + 48)) by (k2_kept cx HFr U9).
    clear HF HFr HG.
    assert (UN : mk W3 (ms_mem ms3) (ms_mem ms) (c_sp1 cx + 16) (c_sp1 cx + 48))
      by (apply (mk_trans W3 _ (ms_mem ms2)); [apply (mk_trans W3 _ (ms_mem ms1)); [exact UN1 | exact UN2] | exact UN3]).
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
    rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
    rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
    rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
    rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
    rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
    rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10 in Q19.
    rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q20.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
      cbn [ms_mem restrict mkst] in HR0 end.
    apply (HREF cx fp k acc ly3 S3 W3 _ _ HB HJ Hfr Hmo).
    pmkst HS.
    exists b.
    split.
    { split.
      { eapply (pe_body_keep cx fp PP_K2 PP_ref W3 ms3 _ PSH_ps (c_sp1 cx + 16) (c_sp1 cx + 48) Hbody);
        try reflexivity; try (cbn [ms_regs mkst]; first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9]);
        [ cbn [ms_mem mkst]; exact UN | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
      split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
      split; [repeat rewrite (proj1 (WF _ _ _)); exact Hfds | repeat rewrite (proj2 (WF _ _ _)); exact Hfs]. }
    split; [exact Hn26|]. split; [exact Hng|].
    split; [cbn [ms_regs mkst]; exact Q18|]. split; [cbn [ms_regs mkst]; exact Q19|].
    split; [cbn [ms_regs mkst]; exact Q20|].
    split; [exact (k2_slot E W3 _ cx _ _ _ _ _ PS_FK 23 (pF cx fp) HR0 U9 ltac:(cbn; tauto) E23 HpFb)|].
    split; [exact (k2_slot E W3 _ cx _ _ _ _ _ PS_SH 25 (pSH cx fp) HR0 U9 ltac:(cbn; tauto) E25 HSHb)|].
    split; [exact (k2_slot E W3 _ cx _ _ _ _ _ PS_F 26 (pF cx fp) HR0 U9 ltac:(cbn; tauto) E26 HpFb)|].
    split.
    { unfold p_psnull, pval in *. cbn [ms_mem mkst].
      apply (val_mem_keep W3 _ _ _ _ _ _ _ Hnull UN); unfold pPS, PO_PS, PE_FRAME in *; cbn [Z.of_nat]; lia. }
    cbn [ms_mem mkst]. exact (asource_none_keep B KS ASIL W3 _ _ _ _ Hsn UN ltac:(lia)).
  + (* 0x80a5c not taken: the abort 0x80a60 (j 0x81034), refuted: s3 = r = -1 (the refused arm of GI_K2) = s5 *)
    exfalso. cbn [branch_taken sv_denot] in Hc.
    rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10 in Hc. vm_compute in Hc. discriminate Hc.
- (* 0x80a2c not taken, g_file_len >= 4: 0x80a30 a0 := b, 0x80a34 a1 := 0, the call of rd32 0x80a38 *)
  cbn [branch_taken sv_denot] in Hc. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, bv_ltu_unsigned in Hc.
  rewrite !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hge4.
  paj_run_tok RUN HS HJ SHOK Espan; [k2_awr cx U9|].
  assert (UN2 : mk W3 (ms_mem ms1) (ms_mem ms) (c_sp1 cx + 16) (c_sp1 cx + 48)) by (k2_kept cx HFr U9).
  clear HF HFr HG.
  assert (UN : mk W3 (ms_mem ms3) (ms_mem ms) (c_sp1 cx + 16) (c_sp1 cx + 48))
    by (apply (mk_trans W3 _ (ms_mem ms1)); [exact UN1 | exact UN2]).
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q10, Q18.
  rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q19.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q20.
  rewrite (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), R22 in Q22.
  change 288%nat with (A_HI 8) in Q24. rewrite Eh8 in Q24.
  pose proof (st_ok_region_nth E _ _ 0%nat _ HS ltac:(cbn; reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
  assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
  (* the copy's first four bytes, kept by the runs *)
  assert (HC4 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) b
                  [nth 0 (p_C cx) 0; nth 1 (p_C cx) 0; nth 2 (p_C cx) 0; nth 3 (p_C cx) 0]).
  { pose proof (garr8_keep W3 _ _ _ _ b (p_C cx) Hcopy UN ltac:(lia) ltac:(rewrite p_lens; lia)
      ltac:(rewrite p_lens; lia)) as HCk.
    exact (k2_copy4 _ b (p_C cx) HCk ltac:(rewrite p_lens; lia)). }
  pmkst HS. rewrite pa_sigma_rd32.
  eapply SRr_bind.
  { exact (rd32_call B LAWS TL LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) b b (p_nF cx)
      (nth 0 (p_C cx) 0) (nth 1 (p_C cx) 0) (nth 2 (p_C cx) 0) (nth 3 (p_C cx) 0) HJ
      ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
      Q10
      ltac:(rewrite Usp; lia)
      ltac:(rewrite Usp; unfold Rd32.RD32_FRAME, LLVMF_STK; lia)
      ltac:(rewrite Usp; lia)
      Hb3 ltac:(lia) ltac:(lia) HC4). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hsame & Hfr2).
  assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
    by exact HP2.
  assert (UNc : mk W3 (ms_mem ms) mem2 (c_sp1 cx - 16) (c_sp1 cx))
    by (intros a Ha Hn; apply Hfr2; [exact Ha | unfold Rd32.RD32_FRAME; rewrite Usp; exact Hn]).
  assert (UNa : mk W3 (ms_mem ms3) mem2 (c_sp1 cx - 16) (c_sp1 cx + 48))
    by (apply (mk_trans W3 _ (ms_mem ms));
        [apply (mk_mono W3 _ _ (c_sp1 cx + 16) (c_sp1 cx + 48)); [lia | lia | exact UN]
        | apply (mk_mono W3 _ _ (c_sp1 cx - 16) (c_sp1 cx)); [lia | lia | exact UNc]]).
  destruct (same_but_materialized_fs _ _ Hsame) as (Hfd2 & Hfs2).
  set (ms4 := mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)).
  assert (UNa4 : mk W3 (ms_mem ms3) (ms_mem ms4) (c_sp1 cx - 16) (c_sp1 cx + 48)) by exact UNa.
  assert (UNc4 : mk W3 (ms_mem ms) (ms_mem ms4) (c_sp1 cx - 16) (c_sp1 cx)) by exact UNc.
  apply (HKM cx fp k acc ly3 S3 W3 ms4 md2 HB HJ2 Hfr Hmo).
  exists b.
  split.
  { eapply (pe_body_keep cx fp PP_K2 PP_KM W3 ms3 ms4 PSH_ps (c_sp1 cx - 16) (c_sp1 cx + 48) Hbody);
    try reflexivity;
    [ cbn [ms_pc_val ms4 mkst]; rewrite Q1; reflexivity
    | cbn [ms_regs ms4 mkst]; exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2)
    | cbn [ms_regs ms4 mkst]; exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8)
    | cbn [ms_regs ms4 mkst]; exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9)
    | cbn [ms_regs ms4 mkst]; exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3)
    | cbn [ms_regs ms4 mkst]; exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4)
    | exact UNa4 | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
  split; [exact Hn26|]. split; [exact Hge4|].
  split; [rewrite Hfd2; repeat rewrite (proj1 (WF _ _ _)); exact Hfds|].
  split; [rewrite Hfs2; repeat rewrite (proj2 (WF _ _ _)); exact Hfs|].
  split; [cbn [ms_regs ms4 mkst]; rewrite Ha0, Q11, k2_magic; reflexivity|].
  split; [cbn [ms_regs ms4 mkst]; exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18)|].
  split; [cbn [ms_regs ms4 mkst]; exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) Q20)|].
  split; [cbn [ms_regs ms4 mkst]; refine (eq_trans (P 21 ltac:(unfold acallee_saved; lia)) (eq_trans Q21 _));
          rewrite <- (w64_mod64 (-1)); reflexivity|].
  split; [cbn [ms_regs ms4 mkst]; exact (eq_trans (P 22 ltac:(unfold acallee_saved; lia)) Q22)|].
  split; [cbn [ms_regs ms4 mkst]; exact (eq_trans (P 24 ltac:(unfold acallee_saved; lia)) Q24)|].
  assert (Hsl : forall off v, pslot cx W3 ms off v -> 16 <= off <= 40 -> pslot cx W3 ms4 off v)
    by (intros off v Hs Ho; apply (pslot_keep cx W3 ms ms4 _ _ off v Hs UNc4); lia).
  split; [apply (Hsl PS_D (p_d cx)); [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_D 33 (p_d cx) HR0 U9
            ltac:(cbn; tauto) E33 ltac:(lia)) | unfold PS_D; lia]|].
  split; [apply (pslot_keep cx W3 ms3 ms4 _ _ PS_SHB SHADOW_OFF SSHB UNa4); unfold PS_SHB; lia|].
  split; [apply (pslot_keep cx W3 ms3 ms4 _ _ PS_F0 (pF cx fp) SF0 UNa4); unfold PS_F0; lia|].
  split; [apply (Hsl PS_FK (pF cx fp)); [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_FK 23 (pF cx fp) HR0 U9
            ltac:(cbn; tauto) E23 HpFb) | unfold PS_FK; lia]|].
  split; [apply (Hsl PS_F (pF cx fp)); [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_F 26 (pF cx fp) HR0 U9
            ltac:(cbn; tauto) E26 HpFb) | unfold PS_F; lia]|].
  split; [apply (Hsl PS_SH (pSH cx fp)); [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_SH 25 (pSH cx fp) HR0 U9
            ltac:(cbn; tauto) E25 HSHb) | unfold PS_SH; lia]|].
  split; [exact (p_glob_keep cx W3 ms3 ms4 _ _ b Hglob UNa4 ltac:(lia))|].
  split; [exact (garr8_keep W3 _ _ _ _ b (p_C cx) Hcopy UNa4 ltac:(lia) ltac:(rewrite p_lens; lia)
                  ltac:(rewrite p_lens; lia))|].
  destruct Harm as [(Hg & R10 & Hk & Hacc & h & Hperm & (Hpo1 & Hpo2) & Hsrc)
                   | (Hg & R10 & Hk & Hacc & Hperm & Hnull & Hsn)].
  + (* accepted: r = 0, the stream open at 24 *)
    left. split; [exact Hg|].
    split; [cbn [ms_regs ms4 mkst]; exact (eq_trans (P 19 ltac:(unfold acallee_saved; lia)) (eq_trans Q19 R10))|].
    split; [exact Hk|]. split; [exact Hacc|]. exists h. split; [exact Hperm|].
    assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3) as (_ & Hh4096 & Hhceil & _).
    pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as [_ Hrq2].
    split.
    { unfold p_psopen, pval in *. split.
      - apply (val_mem_keep W3 _ _ _ _ _ _ _ Hpo1 UNa4); unfold pPS, PO_PS, PE_FRAME in *; cbn [Z.of_nat]; lia.
      - apply (val_mem_keep W3 _ _ _ _ _ _ _ Hpo2 UNa4); unfold pPS, PO_PS, PE_FRAME in *; cbn [Z.of_nat]; lia. }
    exact (asource_at_keep B KS ASIL W3 _ _ _ _ h b (p_C cx) 24 Hsrc UNa4 ltac:(lia) ltac:(lia)
             ltac:(unfold SRC_FILE_BLOCK in *; lia) ltac:(lia) ltac:(rewrite p_lens; lia)).
  + (* refused: r = -1, ps.f NULL, no stream *)
    right. split; [exact Hg|].
    split; [cbn [ms_regs ms4 mkst]; exact (eq_trans (P 19 ltac:(unfold acallee_saved; lia)) (eq_trans Q19 R10))|].
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split.
    { unfold p_psnull, pval in *.
      apply (val_mem_keep W3 _ _ _ _ _ _ _ Hnull UNa4); unfold pPS, PO_PS, PE_FRAME in *; cbn [Z.of_nat]; lia. }
    exact (asource_none_keep B KS ASIL W3 _ _ _ _ Hsn UNa4 ltac:(lia)).
Qed.

(* ---- B_ref, split at the return of free (0x80a94): the free itself (pe_from_REF_free_stmt, PP_ref 0x80a80 ->
   jal __wrap_free 0x80a90) needs the Kit's afree_call; the tail after it (pe_from_REFA, 0x80a94 `ld s9,0x28(s1)`,
   0x80a98 `j 0x80eac` -> PP_K12r) is proved here. ---- *)
Definition PP_REFA : Z := Eval compute in ((Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x27c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z.   (* 0x80a94, `ld s9,0x28(s1)`: the return of free (jal 0x80a90) *)
(* After free gave the copy back: the call holds no block (L = []), one more event (k <= 4 + 1), the meter within
   PA_K12 (PA_K2r + mo_free <= PA_K12, PcapEntryPhases.PA_refused_le); the leave's slots and no stream. *)
Definition GI_REFA (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  p_cut B cx fp PP_REFA PSH_ps k 5 acc (PA_K12 MT cx) [] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  pslot cx W3 ms3 PS_FK (pF cx fp) /\ pslot cx W3 ms3 PS_SH (pSH cx fp) /\ pslot cx W3 ms3 PS_F (pF cx fp) /\
  asource_none SEGS KS (rd W3 ms3).
Definition pe_from_REFA_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K12r B MT KS) -> pe_from SK B MT KS POST GI_REFA.
Definition pe_from_REF_free_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST GI_REFA -> pe_from SK B MT KS POST GI_REF.
Lemma pe_from_REF_of_parts : pe_from_REFA_stmt -> pe_from_REF_free_stmt -> pe_from_REF_stmt.
Proof. intros HA HF POST H12. apply HF. apply HA. exact H12. Qed.

(* The symbolic state at PP_REFA: atom 32 = the frame's shadow SH (PS_SH's word, read at 0x80a94). One region, the
   slot PS_SH, read only. *)
Definition refa_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_SH (PS_SH + 8) 0 0 [YP09.mkChunk PS_SH (CVal 8 (SOff 32 0))]].
Definition refa_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_refa : sstate := mkSS PP_REFA sr_atoms refa_regions None refa_facts.
Definition refa_extra (cx : ecx) (fp : Z) : list word := map (Z_to_bv 64) [pSH cx fp].

Lemma refa_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pe_body cx fp PP_REFA W3 ms3 PSH_ps ->
  pslot cx W3 ms3 PS_SH (pSH cx fp) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (refa_extra cx fp))) ss_refa (restrict (w_H W3) ms3) /\
  sh_ok SEGS EBx [] (Eimg (Ereg (ms_regs ms3) (refa_extra cx fp))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs HBody SSH.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HBody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & (Rsp & Rs0 & Rs1 & Rgp & Rtp) & _).
set (E := Eimg (Ereg (ms_regs ms3) (refa_extra cx fp))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (refa_extra cx fp)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact Rs1).
assert (E32 : ew E 32 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (HpFk : 0 <= pF cx fp < kHighMemEnd) by (unfold kHighMemEnd, PE_FRAME in *; lia).
assert (HSHb : 0 <= pSH cx fp < 2 ^ (8 * Z.of_N 8)).
{ unfold pSH, shadow_of_addr.
  pose proof (shadow_addr_bounds (pF cx fp) HpFk) as HB2. unfold shadow_addr in HB2.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold SHADOW_OFF in *.
  unfold kLowMemEnd, kHighShadowEnd in HB2. lia. }
split; [|apply Forall_nil].
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_REFA)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3; cbn in Hpc, Hrv, Hsv, Hrom, Hfreg, Hfcsr |- *; subst; reflexivity. }
rewrite Hms at 1. rewrite restrict_mkst_fx. unfold ss_refa. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold refa_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
  rewrite U9. unfold PS_SH in *. split; [lia|]. split; [unfold LLVMF_STK in *; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (c_sp1 cx) 40 8 (SOff 32 0) (pSH cx fp));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact HSHb | zside |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SSH).
- apply pairwise_disjoint_of_extents. unfold refa_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [refa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U9. change (2 ^ 5) with 32. unfold LLVMF_STK in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Local Ltac refa_awr :=
  apply awr_ok_x_of0; cbn [ss_mem];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil].
Local Ltac refa_kept cx HFr U9 :=
  intros a Ha Hn;
  refine (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => c_sp1 cx <= x < c_sp1 cx) HFr _ a Ha Hn);
  intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia|]);
  destruct Hin.

Lemma pe_from_REFA : pe_from_REFA_stmt.
Proof.
unfold pe_from_REFA_stmt. intros POST H12.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HI as ((Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & SFK & SSH & SF & Hsn).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
assert (WF : forall l x (m : Model), m_fds (with_vm_backing l x m) = m_fds m /\ m_fs (with_vm_backing l x m) = m_fs m)
  by (intros l x [fd [mp lz mt] io fs pr li tm]; split; reflexivity).
unfold LLVMF_STK in Hspc, Hpres.
destruct (refa_entry cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr Hbody SSH) as [HS SHOK].
remember (Eimg (Ereg (ms_regs ms3) (refa_extra cx fp))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (refa_extra cx fp)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
clear HEdef.
pose proof (bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
(* 0x80a94 `ld s9,0x28(s1)` (s9 := SH), 0x80a98 `j 0x80eac`: the run stops at PP_K12r; it writes nothing *)
paj_run_to_tok RUNTO HS HJ SHOK Espan PP_K12r; [refa_awr|].
assert (UN : mk W3 (ms_mem ms3) (ms_mem ms) (c_sp1 cx) (c_sp1 cx)) by (refa_kept cx HFr U9).
clear HF HFr HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (25%bv : bv 5) Q25.
rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
apply (H12 cx fp k acc ly3 S3 W3 _ _ HB HJ Hfr Hmo).
pmkst HS.
split.
{ exists PSH_ps. split; [right; reflexivity|].
  split.
  { eapply (pe_body_keep cx fp PP_REFA PP_K12r W3 ms3 _ PSH_ps (c_sp1 cx) (c_sp1 cx) Hbody);
    try reflexivity; try (cbn [ms_regs mkst]; first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9]);
    [ cbn [ms_mem mkst]; exact UN | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
  split; [change EV_LIB with 10; lia|]. split; [exact Hacc|]. split; [exact Hperm|].
  split; [repeat rewrite (proj1 (WF _ _ _)); exact Hfds | repeat rewrite (proj2 (WF _ _ _)); exact Hfs]. }
split; [exact Hn26|].
split; [cbn [ms_regs mkst]; rewrite Q25; rewrite ?E32; reflexivity|].
split; [apply (pslot_keep cx W3 ms3 _ (c_sp1 cx) (c_sp1 cx) PS_FK _ SFK); [exact UN | unfold PS_FK; lia | unfold PS_FK; lia | unfold PS_FK; lia]|].
split; [apply (pslot_keep cx W3 ms3 _ (c_sp1 cx) (c_sp1 cx) PS_F _ SF); [exact UN | unfold PS_F; lia | unfold PS_F; lia | unfold PS_F; lia]|].
exact (asource_none_keep B KS ASIL W3 _ _ _ _ Hsn UN ltac:(lia)).
Qed.


(* ---- B_acc and B_ref out of PP_KM (0x80a3c) ---- *)
(* The symbolic start at PP_KM. s8 is the listing's high-part atom A_HI 8 (hi 8, `auipc s8` 0x809a8), so that
   `ld a1,0x498(s8)` (0x80a3c, the listing's PLdHi of object 4) reads g_file_len. Atoms: the registers, and 32 =
   g_file_len = |F|, 33 = d (`ld a1,0x18(s1)` 0x80ab4), 34 = ps.swapped (`lw a0,8(s4)` 0x80a9c). Regions: g_file_len
   (object 4); on the accepted arm also the spill slots [s1 + 0x18, s1 + 0x80) (PS_D read, PS_CAP written at 0x80abc)
   and ps.swapped at s4 + 8 (p_psopen). No shadow check in the stretch: the shadow base is the literal EBx (PcapEntryKit.v). *)
Definition km_regs := sr_set sr_atoms (24%bv : bv 5) (SOff (A_HI 8) 0).
Definition km_glen : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition kma_regions : smem :=
  [km_glen;
   YP09.mkRegion (Some 9%nat) 24 128 120 128 [YP09.mkChunk 24 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 20%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 34 0))]].
Definition kmr_regions : smem := [km_glen].
Definition km_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_kma : sstate := mkSS PP_KM km_regs kma_regions None km_facts.
Definition ss_kmr : sstate := mkSS PP_KM km_regs kmr_regions None km_facts.
Definition km_extra (cx : ecx) : list word := map (Z_to_bv 64) [p_nF cx; p_d cx; p_swz cx].

Lemma km_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 b (acc : bool),
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  c_n cx < 2 ^ 26 -> pregs cx ms3 ->
  ms_pc_val ms3 = w64 (BASE + PP_KM) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) -> getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) ->
  p_glob cx W3 ms3 b -> pslot cx W3 ms3 PS_D (p_d cx) ->
  (if acc then pval W3 ms3 (pPS cx fp + 8) 4 (p_swz cx) else True) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (km_extra cx))) (if acc then ss_kma else ss_kmr)
    (restrict (w_H W3) ms3).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 b acc HB HJ Hfrs Hn26 Hpregs Hpc Hrv Hsv Hrom Hfr Hfc R20 R24 (_ & Hglen) SD HSW.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hin) as Hoff.
rewrite EFA in Hoff. change (fs_frame_bytes PE_CID) with 128 in Hoff.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
pose proof (pa_obj_img 4 ltac:(lia)) as Ho4. unfold pcap_img_end, YImgTop.IMG_TOP in Ho4.
pose proof (pa_val_range (A_HI 8)) as Rh8.
pose proof (p_d_range cx) as Hd. pose proof (p_sizes cx) as (HnF & _ & _).
assert (Hsw : 0 <= p_swz cx <= 1) by (unfold p_swz, PST.pcap_sw; destruct (_ =? _); lia).
set (E := Eimg (Ereg (ms_regs ms3) (km_extra cx))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (km_extra cx)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (E20 : ew E 20 = getr (ms_regs ms3) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 20 20%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (p_nF cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (p_swz cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (Eo4 : ew E (A_OBJ 4) = Z_to_bv 64 (pa_val (A_OBJ 4)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eh8 : ew E (A_HI 8) = Z_to_bv 64 (pa_val (A_HI 8)))
  by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (Us1 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; apply unsigned_lit_small; lia).
assert (Ups : bv_unsigned (ew E 20) = pPS cx fp)
  by (rewrite E20, R20; apply unsigned_lit_small; unfold pPS, PO_PS, PE_FRAME in *; lia).
assert (Uo4 : bv_unsigned (ew E (A_OBJ 4)) = pa_val (A_OBJ 4)) by (rewrite Eo4; apply unsigned_lit_small; lia).
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KM)) (ms_mem ms3) (seg_rom SEGS)).
{ rewrite <- Hrom. change (Z_to_bv 64 (BASE + PP_KM)) with (w64 (BASE + PP_KM)). rewrite <- Hpc.
  exact (ms_eta ms3 Hrv Hsv Hfr Hfc). }
(* the start with s8 = the atom A_HI 8, from the plain register atoms *)
assert (HSA : forall rs, regions_wf rs = true -> Forall (region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  pairwise_disjoint E rs -> st_ok_pi SEGS pa_val E (mkSS PP_KM km_regs rs None km_facts) (restrict (w_H W3) ms3)).
{ intros rs Hwf Hrs Hdis.
  apply (st_ok_pi_set_reg E (mkSS PP_KM sr_atoms rs None km_facts) (restrict (w_H W3) ms3) (24%bv : bv 5)
    (SOff (A_HI 8) 0)).
  - rewrite Hms, restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hrs
    | exact Hdis |].
    split; [|split; [exact I | exact I]].
    cbn [km_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Us1. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [ms_regs restrict sv_denot]. rewrite Eh8, Z.add_0_r, Z_to_bv_bv_unsigned. exact R24. }
assert (RG : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) km_glen).
{ unfold km_glen, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Uo4. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 4)) 0 8 (SOff 32 0) (p_nF cx));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
  rewrite Z.add_0_r. exact Hglen. }
destruct acc.
- unfold ss_kma. apply HSA.
  + vm_compute. reflexivity.
  + unfold kma_regions. apply Forall_cons; [exact RG|].
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Us1. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; unfold LLVMF_STK; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (c_sp1 cx) 24 8 (SOff 33 0) (p_d cx));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SD).
    * rewrite Ups. split; [unfold pPS, PO_PS, PE_FRAME in *; lia|].
      split; [unfold pPS, PO_PS, PE_FRAME in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (pPS cx fp) 8 4 (SOff 34 0) (p_swz cx));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | zside |].
      exact HSW.
  + apply pairwise_disjoint_of_extents.
    unfold kma_regions, km_glen, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Uo4, Us1, Ups. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold pPS, PO_PS, PE_FRAME in *. destruct Hoff as [Hoff | Hoff]; repeat split; lia.
- unfold ss_kmr. apply HSA.
  + vm_compute. reflexivity.
  + unfold kmr_regions. apply Forall_cons; [exact RG | apply Forall_nil].
  + cbn [pairwise_disjoint all_disjoint kmr_regions]. tauto.
Qed.

Lemma km_U : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
intros E n z H. unfold U. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

Lemma km_wvb : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. destruct m as [fd [mp lz mt] io fs pr li tm]. split; reflexivity. Qed.

(* Two run tactics of lib/B/Prog/PcapSourceOpenB.v (ro_awr, frame_same), restated here: a read-only stretch's write
   obligation, and its memory unchanged. *)
Ltac ro_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?G ?XO ?OUT ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' G XO OUT stk spx fp b0 bc lyx own) end;
  apply awr_ok_x_of0;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].
Ltac frame_same HF EQ :=
  lazymatch type of HF with frame_of _ _ (ms_mem ?a) (ms_mem ?b) =>
    assert (EQ : ms_mem b = ms_mem a) by
      (apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality; intros x; apply HF; intros (r & Hin' & Hr); vm_compute in Hin';
       repeat (destruct Hin' as [<- | Hin']; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hin') end.

Ltac km_awr U9 dd :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?G ?XO ?OUT ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' G XO OUT stk spx fp b0 bc lyx own) end;
  apply awr_ok_x_of0;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 9%nat) (d := dd);
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |] ].

(* The stretch's memory: unchanged outside [lo, hi), from a run's frame and the previous runs'. *)
Ltac km_mk_step HFr U9 lo hi UN :=
  let UNs := fresh "UNs" in
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => lo <= a < hi) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9 in Hrr; lia|]);
          destruct Hin)) as UNs;
  let UN2 := fresh "UN" in
  lazymatch type of UN with mk ?W ?m0 ?m1 _ _ =>
  lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
    assert (UN2 : mk W m0 m2 lo hi)
      by (apply (mk_trans W m0 m1 m2 lo hi UN); intros x Hx Hn; apply UNs; [exact Hx | exact Hn]) end end;
  clear UN UNs; rename UN2 into UN;
  lazymatch goal with HJx : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    repeat rewrite wvb_collapse in HJx end.

Ltac km_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* At the malloc call: the premises of HMAL from the run's state. *)
Ltac km_call HMAL HA0 HS HJ UN DCAP U9 EW Eh8 Hregs R18 R20 :=
  lazymatch type of U9 with bv_unsigned (ew ?E 9) = c_sp1 ?cx =>
  lazymatch type of HS with st_ok _ _ ?ssx (restrict (w_H ?W) ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    let HR1 := fresh "HR1" in let VCAP := fresh "VCAP" in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
    cbn [ms_mem restrict mkst] in HR1;
    pose proof (field_of_region E _ 9%nat (c_sp1 cx) _ _ _ _ _ 120 8%N (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (p_cap cx)
      HR1 U9 ltac:(cbn; tauto) DCAP ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold p_cap; lia)
      ltac:(cbn; lia)) as VCAP;
    change (N.to_nat 8) with 8%nat in VCAP;
    let Hf1 := fresh "Hf1" in let Hpc1 := fresh "Hpc1" in let Hsv1 := fresh "Hsv1" in
    let Hrv1 := fresh "Hrv1" in let Hfc1 := fresh "Hfc1" in let Hrom1 := fresh "Hrom1" in
    pose proof HS as (Hf1 & Hpc1 & Hsv1 & Hrv1 & Hfc1 & Hrom1 & _);
    cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom setpc ss_pc ss_resv resv_denot]
      in Hf1, Hpc1, Hsv1, Hrv1, Hfc1, Hrom1;
    let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in
    let Q8 := fresh "Q8" in let Q9 := fresh "Q9" in let Q18 := fresh "Q18" in let Q20 := fresh "Q20" in
    let Q24 := fresh "Q24" in
    prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18;
    prreg HS (20%bv : bv 5) Q20; prreg HS (24%bv : bv 5) Q24;
    rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2;
    rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3;
    rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4;
    rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8;
    rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9;
    rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q18;
    rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q20;
    rewrite Eh8 in Q24;
    apply HMAL;
      [ exact HJ | exact (proj1 (km_wvb _ _ _)) | exact (proj2 (km_wvb _ _ _)) | exact UN
      | unfold pslot; exact (rdword_of_val_mem SEGS (w_H W) _ _ _ VCAP ltac:(lia))
      | exact Hpc1 | exact Hrv1 | exact Hsv1 | exact Hrom1 | exact Hf1 | exact Hfc1
      | unfold pregs; rewrite Q2, Q8, Q9, Q3, Q4; exact Hregs
      | rewrite Q1; reflexivity
      | exact HA0 | rewrite Q18; exact R18 | rewrite Q20; exact R20 | exact Q24 ]
  end end.

(* ---- the malloc call of B_acc (jal 0x80ac8): a cut local to this file, at __wrap_malloc's entry ---- *)
(* Reached from the accepted arm's four paths (magic 0xa1b2c3d4 / 0xd4c3b2a1, d = 0 / d <> 0): a0 = bn, ra = PP_K3
   (0x80acc), cap spilled in PS_CAP (0x80abc); the rest is GI_KM's accepted arm (s3 is dead). pe_from_KMC_stmt is the
   call and its return into GI_K3 (malloc, through the allocator call of PcapEntryKit.v). *)
Definition GI_KMC (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h : Z,
  ms_pc_val ms3 = Z_to_bv 64 (SIGMA PS___interceptor_trampoline_malloc) /\ ms_resv ms3 = None /\
  ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  pregs cx ms3 /\ psaved cx W3 ms3 /\ pheader cx fp W3 ms3 /\ pshadow cx fp W3 ms3 PSH_ps /\
  garr8 SEGS (rd W3 ms3) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  k <= 2 /\ acc <= PA_K2g MT cx /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK)]) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 1 = w64 (BASE + PP_K3) /\ getr (ms_regs ms3) 10 = w64 (p_bn cx) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\ pslot cx W3 ms3 PS_FK (pF cx fp) /\
  pslot cx W3 ms3 PS_F (pF cx fp) /\ pslot cx W3 ms3 PS_SH (pSH cx fp) /\
  pslot cx W3 ms3 PS_CAP (p_cap cx) /\
  p_glob cx W3 ms3 b /\ p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24.

Definition pe_from_KMC_stmt : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K3 B MT KS) -> pe_from SK B MT KS POST GI_KMC.

Lemma km_swrap32 : forall m, 0 <= m < 2 ^ 32 ->
  bv_swrap 32 m mod 2 ^ 64 = (if m <? 2 ^ 31 then m else m + (2 ^ 64 - 2 ^ 32)).
Proof.
intros m Hm. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec m (2 ^ 31)); lia.
Qed.

(* `xor` then `seqz` (0x80a6c / 0x80a70, 0x80aa8 / 0x80aac): 1 exactly for equal words. *)
Lemma km_seqz : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  (if zcanon (Z.lxor x y) <? zcanon 1 then 1 else 0) = (if x =? y then 1 else 0).
Proof.
intros x y Hx Hy.
assert (Ec : zcanon (Z.lxor x y) = Z.lxor x y).
{ unfold zcanon, M64. apply Z.mod_small. exact (Z_lxor_range x y Hx Hy). }
rewrite Ec. change (zcanon 1) with 1.
destruct (Z.eqb_spec x y) as [<- | Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- assert (Hnz : Z.lxor x y <> 0) by (intros H0; apply Hne; apply Z.lxor_eq_0_iff; exact H0).
  assert (Hnn : 0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia).
  destruct (Z.ltb_spec (Z.lxor x y) 1); [lia | reflexivity].
Qed.

Lemma km_good : forall cx,
  p_good cx = ((24 <=? p_nF cx) && ((p_magic cx =? 0xA1B2C3D4) || (p_magic cx =? 0xD4C3B2A1)))%bool.
Proof. intros cx. reflexivity. Qed.
Lemma km_swz : forall cx, p_swz cx = if p_magic cx =? 0xD4C3B2A1 then 1 else 0.
Proof. intros cx. reflexivity. Qed.

Lemma pe_from_KM_of_KMC : pe_from_KMC_stmt -> pe_from_KM_stmt.
Proof.
intros HKMC. unfold pe_from_KM_stmt. intros POST HK3 HREF.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof HJ as HJ0.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct HI as (b & Hbody & Hn26 & Hn4 & Hfds & Hfs & R10 & R18 & R20 & R21 & R22 & R24 & SD & SSHB & SF0 & SFK & SF
  & SSH & Hglob & Hcopy & Harm).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof (pb_HG cx HB) as HGX.
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_d_range cx) as Hd. pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
assert (Hmag : 0 <= p_magic cx < 2 ^ 32).
{ unfold p_magic, PST.pcap_magic, PST.pcap_byte.
  repeat match goal with |- context [bv_unsigned ?x] =>
    lazymatch goal with H : 0 <= bv_unsigned x < _ |- _ => fail | _ => idtac end;
    let H := fresh "Hbyte" in pose proof (bv_unsigned_in_range 8 x) as H; change (bv_modulus 8) with 256 in H end.
  lia. }
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
remember (Eimg (Ereg (ms_regs ms3) (km_extra cx))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; subst E; rewrite Eimg_low by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = w64 (p_nF cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = w64 (p_d cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = w64 (p_swz cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (U10 : U E (SOff 10 0) = bv_swrap 32 (p_magic cx) mod 2 ^ 64)
  by (apply km_U; rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R10).
assert (U21 : U E (SOff 21 0) = 2 ^ 64 - 1)
  by (rewrite (km_U E 21 (-1)) by (rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R21); reflexivity).
assert (U22 : U E (SOff 22 0) = 24)
  by (rewrite (km_U E 22 24) by (rewrite (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R22); reflexivity).
assert (U32 : U E (SOff 32 0) = p_nF cx)
  by (rewrite (km_U E 32 (p_nF cx) E32); apply Z.mod_small; lia).
assert (Eh8 : ew E 288 = Z_to_bv 64 (pa_val (A_HI 8)))
  by (change 288%nat with (A_HI 8); subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
destruct Harm as [(Hgood & R19 & Hk & Hacc & h & Hperm & Hpso & Hsrc)
                 | (Hgood & R19 & Hk & Hacc & Hperm & Hnull & Hsn)].
- (* accepted *)
  pose proof Hgood as Hgood0. rewrite km_good in Hgood. apply andb_true_iff in Hgood as [H24 Hmg]. apply Z.leb_le in H24.
  apply orb_true_iff in Hmg. rewrite !Z.eqb_eq in Hmg.
  assert (Hm31 : 2 ^ 31 <= p_magic cx) by (destruct Hmg as [-> | ->]; lia).
  assert (U10a : U E (SOff 10 0) = p_magic cx + (2 ^ 64 - 2 ^ 32))
    by (rewrite U10, km_swrap32 by exact Hmag; destruct (Z.ltb_spec (p_magic cx) (2 ^ 31)); lia).
  assert (U19 : U E (SOff 19 0) = 0)
    by (rewrite (km_U E 19 0) by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R19); reflexivity).
  assert (Hsw01 : 0 <= p_swz cx <= 1) by (rewrite km_swz; destruct (_ =? _); lia).
  assert (U33 : U E (SOff 33 0) = p_d cx) by (rewrite (km_U E 33 (p_d cx) E33); apply Z.mod_small; lia).
  assert (U34 : U E (SOff 34 0) = p_swz cx) by (rewrite (km_U E 34 (p_swz cx) E34); apply Z.mod_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
    by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
  pose proof (km_entry cx fp k ly3 S3 W3 ms3 md3 b true HB HJ Hfr Hn26 Hregs Hpc Hrv Hsv Hrom Hfreg Hfcsr
    R20 R24 Hglob SD (proj2 Hpso)) as HS.
  cbv beta iota in HS. rewrite <- HEdef in HS.
  assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  clear HEdef.
  assert (DCAP : sv_denot E (SAlu ALU_SLL (SOff 33 0) (SLit 3)) = w64 (p_cap cx)).
  { rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U33, U_SLit.
    change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
    unfold zcanon, M64, p_cap. rewrite Z.mod_small; lia. }
  (* malloc (jal 0x80ac8) from the four paths that reach it: bn in a0, cap in PS_CAP, the return PP_K3 in ra *)
  assert (HMAL : forall (ms' : machine_state) mdq,
    ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms') mdq k ->
    m_fds mdq = m_fds md3 -> m_fs mdq = m_fs md3 ->
    mk W3 (ms_mem ms3) (ms_mem ms') (c_sp1 cx + 120) (c_sp1 cx + 128) ->
    pslot cx W3 ms' PS_CAP (p_cap cx) ->
    ms_pc_val ms' = Z_to_bv 64 (SIGMA PS___interceptor_trampoline_malloc) -> ms_resv ms' = None ->
    ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
    pregs cx ms' -> getr (ms_regs ms') 1 = w64 (BASE + PP_K3) -> getr (ms_regs ms') 10 = w64 (p_bn cx) ->
    getr (ms_regs ms') 18 = w64 b -> getr (ms_regs ms') 20 = w64 (pPS cx fp) ->
    getr (ms_regs ms') 24 = w64 (pa_val (A_HI 8)) ->
    SRr SEGS W3 (mkCfg ms' mdq) (POST cx)).
  { intros ms' mdq HJ' Hfd' Hfs' UNq SCAP Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' Hpr' Q1 Q10 Q18 Q20 Q24.
    apply (HKMC POST HK3 cx fp k acc ly3 S3 W3 ms' mdq HB HJ' Hfr Hmo).
    destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ0 Hfr)
      as (_ & HAR3 & _ & Hspc & Hsp47 & _ & _ & _ & _ & _ & _ & Hinp & _).
    assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
    assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR3 Hb3) as (_ & Hb4096 & Hbceil & _).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR3 Hh3) as (_ & Hh4096 & Hhceil & _).
    pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
    change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
    pose proof Hpr' as (Rsp' & Rs0' & Rs1' & Rgp' & Rtp').
    pose proof (pe_body_keep cx fp PP_KM (SIGMA PS___interceptor_trampoline_malloc - BASE) W3 ms3 ms'
      PSH_ps (c_sp1 cx + 120) (c_sp1 cx + 128) Hbody
      ltac:(rewrite Hpc'; unfold w64; f_equal; lia) Hrv' Hsv' Hrom' Hfr' Hfc'
      ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) UNq
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hf4096 Hfceil Hinp)
      as (_ & _ & _ & _ & _ & _ & _ & Hsav' & Hhd' & Hsh' & _ & Hinb').
    exists b, h.
    split; [exact Hpc'|]. split; [exact Hrv'|]. split; [exact Hsv'|]. split; [exact Hrom'|].
    split; [exact Hfr'|]. split; [exact Hfc'|]. split; [exact Hpr'|].
    split; [exact Hsav'|]. split; [exact Hhd'|]. split; [exact Hsh'|]. split; [exact Hinb'|].
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [rewrite Hfd'; exact Hfds|]. split; [rewrite Hfs'; exact Hfs|].
    split; [exact Hn26|]. split; [exact Hgood0|].
    split; [exact Q1|]. split; [exact Q10|]. split; [exact Q18|]. split; [exact Q20|]. split; [exact Q24|].
    split; [exact (pslot_keep cx W3 ms3 ms' _ _ PS_D _ SD UNq ltac:(unfold PS_D; lia) ltac:(unfold PS_D; lia)
                     ltac:(unfold PS_D; lia))|].
    split; [exact (pslot_keep cx W3 ms3 ms' _ _ PS_SHB _ SSHB UNq ltac:(unfold PS_SHB; lia) ltac:(unfold PS_SHB; lia)
                     ltac:(unfold PS_SHB; lia))|].
    split; [exact (pslot_keep cx W3 ms3 ms' _ _ PS_F0 _ SF0 UNq ltac:(unfold PS_F0; lia) ltac:(unfold PS_F0; lia)
                     ltac:(unfold PS_F0; lia))|].
    split; [exact (pslot_keep cx W3 ms3 ms' _ _ PS_FK _ SFK UNq ltac:(unfold PS_FK; lia) ltac:(unfold PS_FK; lia)
                     ltac:(unfold PS_FK; lia))|].
    split; [exact (pslot_keep cx W3 ms3 ms' _ _ PS_F _ SF UNq ltac:(unfold PS_F; lia) ltac:(unfold PS_F; lia)
                     ltac:(unfold PS_F; lia))|].
    split; [exact (pslot_keep cx W3 ms3 ms' _ _ PS_SH _ SSH UNq ltac:(unfold PS_SH; lia) ltac:(unfold PS_SH; lia)
                     ltac:(unfold PS_SH; lia))|].
    split; [exact SCAP|].
    split; [exact (p_glob_keep cx W3 ms3 ms' _ _ b Hglob UNq ltac:(lia))|].
    split.
    { destruct Hpso as (P1 & P2). unfold pval in *. unfold pPS, PO_PS, PE_FRAME in *.
      split; [apply (val_mem_keep W3 _ _ _ _ _ _ _ P1 UNq) | apply (val_mem_keep W3 _ _ _ _ _ _ _ P2 UNq)];
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    apply (asource_at_keep B KS ASIL W3 _ _ _ _ _ _ _ _ Hsrc UNq);
      rewrite ?p_lens; unfold SRC_FILE_BLOCK; lia. }
  pose proof (mk_refl W3 (ms_mem ms3) (c_sp1 cx + 120) (c_sp1 cx + 128)) as UN.
  paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
  km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
  (* 0x80a40 `bltu a1,s6`: a good file has g_file_len >= 24 *)
  psrr_branch_tok RUN BR HS SHOK Espan.
  { exfalso. rewrite branch_ltu_U, U32, U22 in Hc. apply Z.ltb_lt in Hc. lia. }
  rewrite branch_ltu_U, U32, U22 in Hc. clear Hc.
  paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
  km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
  (* 0x80a4c `bne a0,a1`: the magic against 0xa1b2c3d4 *)
  psrr_branch_tok RUN BR HS SHOK Espan.
  + rewrite branch_ne_U, U10a, U_SLit in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold zcanon, M64 in Hc.
    assert (HSW : p_magic cx = 0xD4C3B2A1) by (destruct Hmg as [Hm | Hm]; [rewrite Hm in Hc; lia | exact Hm]).
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* 0x80a7c `bne s3,s5` (abort 0x81034): s5 = 0 for the swapped magic, = s3 *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    { exfalso. rewrite branch_ne_U, U19, !U_SAlu, U10a, !U_SLit in Hc. cbn [zalu_raw] in Hc.
      rewrite km_seqz in Hc by (unfold zcanon, M64; lia). rewrite HSW in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* PP_ref 0x80a80 `beqz s3`: the accept arm 0x80a9c *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    2: { exfalso. rewrite branch_eq_U, U19, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* 0x80ab0 `bne a0,a1` (abort 0x81034): ps.swapped = p_swz = 1 = (magic == 0xd4c3b2a1) *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    { exfalso. rewrite branch_ne_U, U_SExt, U34, !U_SAlu, U10a, !U_SLit in Hc. cbn [zalu_raw] in Hc.
      rewrite km_seqz in Hc by (unfold zcanon, M64; lia). rewrite km_swz, HSW in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* 0x80ac0 `bnez a1`: d <> 0 (bn = cap) or d = 0 (bn = 1, 0x80ac4) *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    * rewrite branch_ne_U, U33, U_SLit in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold zcanon, M64 in Hc.
      paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
      km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
      km_rreg HS (10%bv : bv 5) Q10. rewrite DCAP in Q10.
      lazymatch type of Q10 with getr (ms_regs ?m) _ = _ =>
        assert (HA0 : getr (ms_regs m) 10 = w64 (p_bn cx))
          by (rewrite Q10; unfold p_bn, p_cap in *; f_equal; lia) end.
      clear Q10.
      km_call HMAL HA0 HS HJ UN DCAP U9 EW Eh8 Hregs R18 R20.
    * rewrite branch_ne_U, U33, U_SLit in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold zcanon, M64 in Hc.
      paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
      km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
      km_rreg HS (10%bv : bv 5) Q10.
      lazymatch type of Q10 with getr (ms_regs ?m) _ = _ =>
        assert (HA0 : getr (ms_regs m) 10 = w64 (p_bn cx))
          by (rewrite Q10; cbn [sv_denot]; unfold w64, p_bn, p_cap; f_equal; lia) end.
      clear Q10.
      km_call HMAL HA0 HS HJ UN DCAP U9 EW Eh8 Hregs R18 R20.
  + rewrite branch_ne_U, U10a, U_SLit in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold zcanon, M64 in Hc.
    assert (HLE : p_magic cx = 0xA1B2C3D4) by lia.
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* 0x80a50 `beqz s3` (else `j` 0x80a54 to abort 0x81034): s3 = r = 0 *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    2: { exfalso. rewrite branch_eq_U, U19, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* 0x80ab0 `bne a0,a1` (abort 0x81034): ps.swapped = p_swz = 0 = (magic == 0xd4c3b2a1) *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    { exfalso. rewrite branch_ne_U, U_SExt, U34, U_SLit in Hc. rewrite km_swz, HLE in Hc.
      vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
    km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
    (* 0x80ac0 `bnez a1`: d <> 0 (bn = cap) or d = 0 (bn = 1, 0x80ac4) *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    * rewrite branch_ne_U, U33, U_SLit in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold zcanon, M64 in Hc.
      paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
      km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
      km_rreg HS (10%bv : bv 5) Q10. rewrite DCAP in Q10.
      lazymatch type of Q10 with getr (ms_regs ?m) _ = _ =>
        assert (HA0 : getr (ms_regs m) 10 = w64 (p_bn cx))
          by (rewrite Q10; unfold p_bn, p_cap in *; f_equal; lia) end.
      clear Q10.
      km_call HMAL HA0 HS HJ UN DCAP U9 EW Eh8 Hregs R18 R20.
    * rewrite branch_ne_U, U33, U_SLit in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold zcanon, M64 in Hc.
      paj_run_tok RUN HS HJ SHOK Espan; [km_awr U9 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx))|].
      km_mk_step HFr U9 (c_sp1 cx + 120) (c_sp1 cx + 128) UN. clear HF HFr HG.
      km_rreg HS (10%bv : bv 5) Q10.
      lazymatch type of Q10 with getr (ms_regs ?m) _ = _ =>
        assert (HA0 : getr (ms_regs m) 10 = w64 (p_bn cx))
          by (rewrite Q10; cbn [sv_denot]; unfold w64, p_bn, p_cap; f_equal; lia) end.
      clear Q10.
      km_call HMAL HA0 HS HJ UN DCAP U9 EW Eh8 Hregs R18 R20.

- (* refused *)
  assert (U19 : U E (SOff 19 0) = 2 ^ 64 - 1)
    by (rewrite (km_U E 19 (-1)) by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R19); reflexivity).
  (* B_ref's entry: PP_ref with GI_REF's facts; the stretch writes nothing, so the memory is ms3's *)
  assert (HREFk : forall (ms' : machine_state) md',
    ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
    m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 -> ms_mem ms' = ms_mem ms3 ->
    ms_pc_val ms' = w64 (BASE + PP_ref) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
    ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr -> pregs cx ms' ->
    getr (ms_regs ms') 18 = w64 b -> getr (ms_regs ms') 19 = w64 (-1) -> getr (ms_regs ms') 20 = w64 (pPS cx fp) ->
    SRr SEGS W3 (mkCfg ms' md') (POST cx)).
  { intros ms' md' HJ' Hfd' Hfs' EM Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' Hpr' Q18 Q19 Q20.
    apply (HREF cx fp k acc ly3 S3 W3 ms' md' HB HJ' Hfr Hmo).
    exists b.
    split; [|split; [exact Hn26 | split; [exact Hgood |]]].
    { split; [|split; [exact Hk | split; [exact Hacc | split; [exact Hperm |
        split; [rewrite Hfd'; exact Hfds | rewrite Hfs'; exact Hfs]]]]].
      split; [exact Hpc'|]. split; [exact Hrv'|]. split; [exact Hsv'|]. split; [exact Hrom'|].
      split; [exact Hfr'|]. split; [exact Hfc'|]. split; [exact Hpr'|].
      unfold psaved, pheader, pshadow. rewrite EM.
      split; [exact Hsav|]. split; [exact Hhd|]. split; [exact Hsh|]. split; [exact Hshlen | exact Hinb]. }
    split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|].
    unfold pslot, p_psnull, pval. rewrite EM.
    split; [exact SFK|]. split; [exact SSH|]. split; [exact SF|]. split; [exact Hnull | exact Hsn]. }
  pose proof (km_entry cx fp k ly3 S3 W3 ms3 md3 b false HB HJ Hfr Hn26 Hregs Hpc Hrv Hsv Hrom Hfreg Hfcsr
    R20 R24 Hglob SD I) as HS.
  cbv beta iota in HS. rewrite <- HEdef in HS.
  assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK Espan;
    [ apply awr_ok_x_of0; unfold ss_kmr, kmr_regions, km_glen; cbn [ss_mem];
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil] |].
  frame_same HF EQ1. clear HF HFr HG.
  (* 0x80a40 `bltu a1,s6`: g_file_len < 24 *)
  psrr_branch_tok RUN BR HS SHOK Espan.
  + rewrite branch_ltu_U, U32, U22 in Hc. apply Z.ltb_lt in Hc. rename Hc into H24.
    paj_run_tok RUN HS HJ SHOK Espan; [ro_awr|].
    frame_same HF EQ2. clear HF HFr HG.
    (* 0x80a7c `bne s3,s5`: s3 = s5 = -1 *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    * rewrite branch_ne_U, U19, U21, Z.eqb_refl in Hc. discriminate Hc.
    * paj_run_tok RUN HS HJ SHOK Espan; [ro_awr|].
      frame_same HF EQ3. clear HF HFr HG.
      repeat rewrite wvb_collapse in HJ.
      pose proof HS as (Hf1 & Hpc1 & Hsv1 & Hrv1 & Hfc1 & Hrom1 & _).
      cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot]
        in Hf1, Hpc1, Hsv1, Hrv1, Hfc1, Hrom1.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
      prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
      prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
      rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
      rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
      rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
      rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
      rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
      rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q18.
      rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q19.
      rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q20.
      apply HREFk;
        [ exact HJ | exact (proj1 (km_wvb _ _ _)) | exact (proj2 (km_wvb _ _ _)) | congruence
        | exact Hpc1 | exact Hrv1 | exact Hsv1 | exact Hrom1 | exact Hf1 | exact Hfc1
        | unfold pregs; rewrite Q2, Q8, Q9, Q3, Q4; exact Hregs
        | rewrite Q18; exact R18 | rewrite Q19; exact R19 | rewrite Q20; exact R20 ].
  + rewrite branch_ltu_U, U32, U22 in Hc. apply Z.ltb_ge in Hc. rename Hc into H24.
    paj_run_tok RUN HS HJ SHOK Espan; [ro_awr|].
    frame_same HF EQ2. clear HF HFr HG.
    (* 0x80a4c `bne a0,a1`: the magic against 0xa1b2c3d4 *)
    psrr_branch_tok RUN BR HS SHOK Espan.
    * rewrite branch_ne_U, U10, U_SLit, km_swrap32 in Hc by exact Hmag.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HnLE. unfold zcanon, M64 in HnLE.
      paj_run_tok RUN HS HJ SHOK Espan; [ro_awr|].
      frame_same HF EQ3. clear HF HFr HG.
      (* 0x80a7c `bne s3,s5`: s5 = -1 unless the magic is 0xd4c3b2a1, which a bad file does not have *)
      psrr_branch_tok RUN BR HS SHOK Espan.
      -- rewrite branch_ne_U, U19, !U_SAlu, U10, !U_SLit in Hc. cbn [zalu_raw] in Hc.
         rewrite km_seqz in Hc by (unfold zcanon, M64; apply Z.mod_pos_bound; lia).
         rewrite km_swrap32 in Hc by exact Hmag.
         destruct (Z.eqb_spec (if p_magic cx <? 2 ^ 31 then p_magic cx else p_magic cx + (2 ^ 64 - 2 ^ 32))
           (zcanon 18446744072984179361)) as [Heq | Hne].
         ++ exfalso. unfold zcanon, M64 in Heq. rewrite km_good in Hgood.
            destruct (Z.ltb_spec (p_magic cx) (2 ^ 31)); [lia|].
            replace (p_magic cx) with 0xD4C3B2A1 in Hgood by lia.
            rewrite (proj2 (Z.leb_le 24 (p_nF cx)) ltac:(lia)) in Hgood. discriminate Hgood.
         ++ vm_compute in Hc. discriminate Hc.
      -- paj_run_tok RUN HS HJ SHOK Espan; [ro_awr|].
         frame_same HF EQ4. clear HF HFr HG.
         repeat rewrite wvb_collapse in HJ.
         pose proof HS as (Hf1 & Hpc1 & Hsv1 & Hrv1 & Hfc1 & Hrom1 & _).
         cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv resv_denot]
           in Hf1, Hpc1, Hsv1, Hrv1, Hfc1, Hrom1.
         prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
         prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
         prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
         rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
         rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
         rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
         rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
         rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
         rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q18.
         rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q19.
         rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q20.
         apply HREFk;
           [ exact HJ | exact (proj1 (km_wvb _ _ _)) | exact (proj2 (km_wvb _ _ _)) | congruence
           | exact Hpc1 | exact Hrv1 | exact Hsv1 | exact Hrom1 | exact Hf1 | exact Hfc1
           | unfold pregs; rewrite Q2, Q8, Q9, Q3, Q4; exact Hregs
           | rewrite Q18; exact R18 | rewrite Q19; exact R19 | rewrite Q20; exact R20 ].
    * (* the magic is 0xa1b2c3d4 and g_file_len >= 24: a good file, not the refused arm *)
      exfalso. rewrite branch_ne_U, U10, U_SLit, km_swrap32 in Hc by exact Hmag.
      apply negb_false_iff, Z.eqb_eq in Hc. unfold zcanon, M64 in Hc. rewrite km_good in Hgood.
      destruct (Z.ltb_spec (p_magic cx) (2 ^ 31)); [lia|].
      replace (p_magic cx) with 0xA1B2C3D4 in Hgood by lia.
      rewrite (proj2 (Z.leb_le 24 (p_nF cx)) ltac:(lia)) in Hgood. discriminate Hgood.
Qed.

(* ---- the return of malloc (0x80acc) into GI_K3, from the allocator rule's post at GI_KMC's state ---- *)
(* amalloc04_rule (lib/Reusable/YC5d.v) states what the call keeps as acall_kept: the stack outside the callee's
   window, the blocks outside the new one, the image outside the owned statics and errno, the frames. The facts GI_K3
   reads are carried byte by byte. *)
Lemma km_pw_mid : forall {X} (R : X -> X -> Prop) l1 x l2 y, pairwise R (l1 ++ x :: l2) -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros x l2 y H Hin; cbn in H.
- destruct H as [HF _]. rewrite Forall_forall in HF. exact (HF y Hin).
- exact (IH x l2 y (proj2 H) Hin).
Qed.
Lemma km_pw_pre : forall {X} (R : X -> X -> Prop) l1 x l2 y, pairwise R (l1 ++ x :: l2) -> In y l1 -> R y x.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros x l2 y H Hin; [destruct Hin|]. cbn in H.
destruct Hin as [<- | Hin].
- destruct H as [HF _]. rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
- exact (IH x l2 y (proj2 H) Hin).
Qed.
Lemma km_rd : forall H H2 (m m2 : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v ->
  (forall x, a <= x < a + 8 -> aview SEGS H2 m2 x = aview SEGS H m x) -> rdword (aview SEGS H2 m2) a = Some v.
Proof.
intros H H2 m m2 a v Hv Hk. rewrite (rdword_ext (aview SEGS H m) (aview SEGS H2 m2) a); [exact Hv|].
intros j Hj. apply Hk. lia.
Qed.
Lemma km_vm : forall H H2 (m m2 : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H2 m2 x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H2 m2) a n v.
Proof.
intros H H2 m m2 a n v Hv Hk. eapply BCL.vm_frame; [|exact Hv].
intros x Hx. apply (mbyte_of_aview SEGS). apply Hk. exact Hx.
Qed.
Lemma km_ga : forall H H2 (m m2 : word -> option byte) a l,
  garr8 SEGS (mrestrict H m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H2 m2 x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H2 m2) a l.
Proof.
intros H H2 m m2 a l Hg Hk. apply (garr8_frame SEGS _ _ _ _ Hg).
intros x Hx. apply (mbyte_of_aview SEGS). apply Hk. exact Hx.
Qed.

Lemma km_k3 : forall POST, pe_from SK B MT KS POST (GI_K3 B MT KS) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  GI_KMC cx fp k acc ly3 S3 W3 ms3 md3 ->
  forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved (ms_regs ms3) regs2 -> getr regs2 10 = w64 res -> frames S2 = frames S3 -> 4096 <= res ->
  ablocks B ly2 S2 = ablocks B ly3 S3 ++ [(res, p_bn cx)] ->
  acall_kept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (c_sp1 cx - ASTACK) (c_sp1 cx)
    (fun a => res <= a < res + req_size (p_bn cx)) ->
  mo_le MT S3 S2 (mo_malloc MT (p_bn cx)) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
intros POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI ly2 S2 W2 regs2 mem2 md2 res HJ2 HP H10 Hfrs2 Hres
  Hbl HK HMO2 Hfd2 Hfs2.
destruct HI as (b & h & Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hinb & Hk & Hacc & Hperm
  & Hfds & Hfs & Hn26 & Hgood & R1 & R10 & R18 & R20 & R24 & SD & SSHB & SF0 & SFK & SF & SSH & SCAP & Hglob & Hpso
  & Hsrc).
destruct HK as (K1 & K2 & K3 & K4 & _ & _).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR3 & Hal16 & Hspc & Hsp47 & _ & _ & Hf4096 & Hfceil & _ & HEF & Hinp & Hs1r & Hs1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
unfold LLVMF_STK in Hspc.
assert (HAR2 : AR SEGS B ly2 S2 W2 mem2 md2 /\ ly_F ly2 = ly_F (c_ly cx)).
{ destruct HJ2 as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HA & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). exact (conj HA EF). }
destruct HAR2 as (HAR2 & HEF2).
(* the blocks: the copy, the FILE and the new buffer, apart *)
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hu2 : In (res, p_bn cx) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR3 Hb3) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR3 Hh3) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (p_bn cx) HAR2 Hu2) as (_ & Hu4096 & Huceil & Huapp & _ & Hpw & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrq3a Hrq3].
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
assert (Hapart : forall p n, In (p, n) (ablocks B ly3 S3) -> p + req_size n <= res \/ res + req_size (p_bn cx) <= p).
{ intros p n Hin. rewrite Hbl, map_app in Hpw. cbn [map] in Hpw.
  exact (km_pw_pre zdisjoint _ (res, req_size (p_bn cx)) [] (p, req_size n) Hpw
           (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (p, n) Hin)). }
(* the frame and the new buffer, apart *)
assert (HFa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
assert (HFa2 : frame_addr ly2 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF2; reflexivity).
assert (HFapart : pF cx fp + PE_FRAME <= res \/ res + req_size (p_bn cx) <= pF cx fp).
{ destruct (al_sep _ _ LAWS ly2 S2 W2 mem2 md2 HAR2) as (Hsep & _).
  rewrite Hbl, Hfrs2, Hfr, map_app in Hsep. cbn [map fst snd] in Hsep. rewrite HFa2 in Hsep.
  rewrite <- app_assoc in Hsep. cbn [app] in Hsep.
  pose proof (km_pw_mid zdisjoint _ (res, req_size (p_bn cx)) [(pF cx fp, fs_frame_bytes PE_CID)]
    (pF cx fp, fs_frame_bytes PE_CID) Hsep ltac:(left; reflexivity)) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. change (fs_frame_bytes PE_CID) with 128 in Hz. unfold PE_FRAME. lia. }
(* what the call keeps, by kind *)
set (V3 := aview SEGS (w_H W3) (ms_mem ms3)). set (V2 := aview SEGS (w_H W2) mem2).
assert (KS1 : forall x, c_sp1 cx <= x < 2 ^ 64 -> V2 x = V3 x) by (intros x Hx; apply K1; lia).
assert (KFR : forall x, pF cx fp <= x < pF cx fp + PE_FRAME -> V2 x = V3 x).
{ intros x Hx. apply (K4 PE_CID fp x); [rewrite Hfr; left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd];
  rewrite HFa; change (fs_frame_bytes PE_CID) with 128; unfold PE_FRAME in Hx; lia | unfold PE_FRAME in *; lia]. }
assert (KSH : forall x, pSH cx fp <= x < pSH cx fp + 16 -> V2 x = V3 x).
{ intros x Hx. apply (K4 PE_CID fp x); [rewrite Hfr; left; reflexivity | right; unfold in_zr, shadow_addr; cbn [fst snd];
  rewrite HFa; change (fs_frame_bytes PE_CID / 8) with 16; unfold pSH, shadow_of_addr in Hx; lia |].
  intros Hx2. unfold pSH, shadow_of_addr, SHADOW_OFF in Hx.
  exact (fshadow_not_app (pF cx fp) 16 res (req_size (p_bn cx)) x ltac:(lia) ltac:(unfold PE_FRAME in *; lia)
           Huapp ltac:(lia) Hx2). }
assert (KBL : forall p n x, In (p, n) (ablocks B ly3 S3) -> p <= x < p + req_size n -> V2 x = V3 x).
{ intros p n x Hin Hx. replace x with (p + (x - p)) by lia.
  apply (K2 p n (x - p) Hin); [lia|]. pose proof (Hapart p n Hin). lia. }
assert (KIMG : forall x, inG pe_G x -> V2 x = V3 x).
{ intros x Hx. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGdis & _).
  destruct (HGX x Hx) as (Hi & Hno). destruct (HGdis x Hx) as (_ & _ & Hne & _). exact (K3 x Hi Hno Hne). }
assert (KENV : forall x, asrc_env_addr KS x -> V2 x = V3 x).
{ intros x Hx. destruct (asil_env _ _ _ _ ASIL x Hx) as (Hi & Hns & Hne). exact (K3 x Hi Hns Hne). }
assert (Hsl : forall off v, 16 <= off <= 144 -> pslot cx W3 ms3 off v ->
  pslot cx W2 (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) off v).
{ intros off v Hoff Hv. unfold pslot in *. cbn [ms_mem mkst]. apply (km_rd _ _ _ _ _ _ Hv). intros x Hx. apply KS1. lia. }
apply (HK3 cx fp (k + 1) (acc + mo_malloc MT (p_bn cx)) ly2 S2 W2 (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 ltac:(rewrite Hfrs2; exact Hfr)
  (mle_station MT _ _ _ _ _ MTL Hmo HMO2)).
exists b, h, res.
split.
{ split.
  { (* pe_body at PP_K3 *)
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
    split; [exact R1|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp). unfold pregs. cbn [ms_regs mkst].
      exact (conj (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) Rsp)
              (conj (eq_trans (HP 8 ltac:(unfold acallee_saved; lia)) Rs0)
              (conj (eq_trans (HP 9 ltac:(unfold acallee_saved; lia)) Rs1)
              (conj (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) Rgp)
                    (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) Rtp))))). }
    split.
    { destruct Hsav as (S1 & S2'). unfold psaved. cbn [ms_mem mkst]. split.
      - apply (km_rd _ _ _ _ _ _ S1). intros x Hx. apply KS1. lia.
      - intros j Hj. apply (km_rd _ _ _ _ _ _ (S2' j Hj)). intros x Hx. apply KS1. lia. }
    split.
    { destruct Hhd as (H1 & H2 & H3 & H4). unfold pheader. cbn [ms_mem mkst].
      split; [|split; [|split]].
      - apply (km_rd _ _ _ _ _ _ H1). intros x Hx. apply KFR. unfold PE_FRAME. lia.
      - apply (km_rd _ _ _ _ _ _ H2). intros x Hx. apply KFR. unfold PE_FRAME. lia.
      - apply (km_rd _ _ _ _ _ _ H3). intros x Hx. apply KFR. unfold PE_FRAME. lia.
      - apply (km_rd _ _ _ _ _ _ H4). intros x Hx. apply KFR. unfold PE_FRAME, PE_FLAGPTR in *. lia. }
    split.
    { unfold pshadow in *. cbn [ms_mem mkst]. intros i Hi.
      assert (Hl : length PSH_ps = 16%nat) by reflexivity. rewrite Hl in Hi.
      fold V2. rewrite (KSH (pSH cx fp + Z.of_nat i) ltac:(lia)). exact (Hsh i ltac:(rewrite Hl; exact Hi)). }
    split; [reflexivity|].
    cbn [ms_mem mkst].
    pose proof HB as (_ & _ & _ & _ & Hinput & _).
    destruct Hinput as [(Hn0 & _) | (Hnpos & Hinc)].
    - unfold c_n in Hn0. destruct (c_pl cx) as [|x l]; [apply garr8_nil | cbn in Hn0; lia].
    - assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hinc).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrqn].
      apply (km_ga _ _ _ _ _ _ Hinb). intros x Hx. apply (KBL _ _ x Hin3). rewrite length_map in Hx. unfold c_n in *. lia. }
  split; [lia|]. split; [unfold PA_K3; lia|].
  split; [rewrite Hbl; rewrite (Permutation_app_tail [(res, p_bn cx)] Hperm), <- app_assoc; apply Permutation_refl|].
  split; [rewrite Hfd2; exact Hfds | rewrite Hfs2; exact Hfs]. }
split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hres|].
cbn [ms_regs mkst].
split; [exact H10|].
split; [exact (eq_trans (HP 18 ltac:(unfold acallee_saved; lia)) R18)|].
split; [exact (eq_trans (HP 20 ltac:(unfold acallee_saved; lia)) R20)|].
split; [exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) R24)|].
split; [apply Hsl; [unfold PS_D; lia | exact SD]|].
split; [apply Hsl; [unfold PS_SHB; lia | exact SSHB]|].
split; [apply Hsl; [unfold PS_F0; lia | exact SF0]|].
split; [apply Hsl; [unfold PS_FK; lia | exact SFK]|].
split; [apply Hsl; [unfold PS_F; lia | exact SF]|].
split; [apply Hsl; [unfold PS_SH; lia | exact SSH]|].
split; [apply Hsl; [unfold PS_CAP; lia | exact SCAP]|].
split.
{ destruct Hglob as (G1 & G2). unfold p_glob, pval in *. cbn [ms_mem mkst].
  split; [apply (km_vm _ _ _ _ _ _ _ G1) | apply (km_vm _ _ _ _ _ _ _ G2)]; intros x Hx; apply KIMG;
    change (Z.of_nat 8) with 8 in Hx; unfold pe_G, inG;
    [apply Exists_cons_tl; constructor | constructor]; unfold in_zr; cbn [fst snd]; lia. }
split.
{ destruct Hpso as (P1 & P2). unfold p_psopen, pval in *. cbn [ms_mem mkst].
  split; [apply (km_vm _ _ _ _ _ _ _ P1) | apply (km_vm _ _ _ _ _ _ _ P2)]; intros x Hx; apply KFR;
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; unfold pPS, PO_PS, PE_FRAME in *; lia. }
cbn [ms_mem mkst].
apply (BCL.asource_at_frame KS (mrestrict (w_H W3) (ms_mem ms3))); [|exact Hsrc].
intros x Hx. apply (mbyte_of_aview SEGS). fold V2 V3.
destruct Hx as [Hx | [Hx | Hx]].
- exact (KBL h SRC_FILE_BLOCK x Hh3 ltac:(change (req_size SRC_FILE_BLOCK) with 1304; unfold SRC_FILE_BLOCK in Hx; lia)).
- rewrite p_lens in Hx. exact (KBL b (p_nF cx) x Hb3 ltac:(lia)).
- exact (KENV x Hx).
Qed.


(* The malloc call of B_acc (jal 0x80ac8 -> __wrap_malloc, returns to PP_K3 0x80acc), through the Kit's amalloc_call;
   km_k3 rebuilds GI_K3 from its post. (km_k3 and its helpers: a Theorem Labs lane's draft, finished here.) *)
Lemma pe_from_KMC : pe_from_KMC_stmt.
Proof.
unfold pe_from_KMC_stmt. intros POST HK3.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof HI as HI0.
destruct HI as (b & h & Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hinb & Hk & Hacc & Hperm
  & Hfds & Hfs & Hn26 & Hgood & R1 & R10 & R18 & R20 & R24 & SD & SSHB & SF0 & SFK & SF & SSH & SCAP & Hglob & Hpso
  & Hsrc).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR3 & Hal16 & Hspc & Hsp47 & _ & _ & Hf4096 & Hfceil & _ & HEF & Hinp & Hs1r & Hs1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof HB as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
unfold LLVMF_STK in Hspc.
assert (Hn : 0 <= p_bn cx < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
assert (Hlive : blocks_bytes S3 + p_bn cx <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ Hperm), bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  cbn [bsum fold_right fst snd]. unfold LIVE_LIB, SRC_FILE_BLOCK in *. lia. }
set (o := c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)).
assert (Hsp' : spZ (ms_regs ms3) = spZ (PcapEntryDefs.c_regs cx) + o)
  by (subst o; unfold spZ at 1; rewrite Rsp; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Ho16 : o mod 16 = 0).
{ subst o. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r.
  - apply (Z.divide_trans 16 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hs1al]].
  - apply Z.mod_divide; [lia | exact Hal16]. }
assert (Hra' : raZ (ms_regs ms3) = BASE + PP_K3).
{ pose proof pa_B_ok as (HB0 & HB40 & HB4).
  unfold raZ; rewrite R1; unfold w64; rewrite unsigned_lit_small by (unfold PP_K3; lia); reflexivity. }
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms3) 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold PP_K3; lia | reflexivity]).
assert (Hnev : st_nev S3 < EV_MAX).
{ destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & Hnv & _). unfold EV_LIB in *. lia. }
assert (Hch : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (ms_regs ms3) (pch cx)).
{ apply (pe_chain cx fp (ms_regs ms3) ly3 S3 W3 (ms_mem ms3) md3 k _ HB HJ).
  - destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop.
  - reflexivity.
  - exact Rs0.
  - unfold spZ. rewrite Rsp. unfold w64. apply unsigned_lit_small. lia.
  - rewrite Hra'. pose proof pa_base_lo as HBlo. unfold PP_K3. lia.
  - destruct Hsav as (S1 & _). exact S1.
  - destruct Hsav as (_ & S2). pose proof (S2 0 ltac:(lia)) as S20. cbn in S20. rewrite Z.sub_0_r in S20.
    exact S20. }
assert (Htr : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms3) (pch cx)) (as_universe B)).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTRm & _).
  apply HTRm. rewrite Hra'. unfold PE_MALLOC_SITES, PP_K3. cbn. right. left. lia. }
assert (Hmok : mo_ok MT S3 (mo_malloc MT (p_bn cx))).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMOK & HNEED & _).
  apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT (p_bn cx)) MTL HMOK Hmo
    (mo_malloc_nonneg MT MTL (p_bn cx) ltac:(lia))).
  pose proof (PA_K12_need MT MTL cx) as HN. pose proof (PA_refused_le MT MTL cx) as HR.
  pose proof (mo_free_nonneg MT MTL) as HF0.
  pose proof (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as HM0.
  unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g in *. lia. }
rewrite (ms_eta ms3 Hrv Hsv Hfreg Hfcsr), Hpc, Hrom, (pal_malloc _ TL).
eapply SRr_bind.
{ exact (amalloc_call B MT LAWS AMALLOC4 W3 (ms_regs ms3) (ms_mem ms3) LLVMF_STK (spZ (PcapEntryDefs.c_regs cx))
    [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 md3 k (p_bn cx) o
    (getr (ms_regs ms3) 1) (pch cx) HJ R10 Hn Hlive Hsp' Ho16 ltac:(subst o; lia)
    ltac:(subst o; unfold ASTACK, LLVMF_STK; lia)
    (eq_trans Rgp Hgp0) (eq_trans Rtp Htp0) eq_refl Hraw Hnev Hch Htr Hmok). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & H10 & Hfrs2 & Hres & Hbl & HK & HMO2
  & Hfd2 & Hfs2).
replace (spZ (PcapEntryDefs.c_regs cx) + o) with (c_sp1 cx) in HK by (subst o; lia).
exact (km_k3 POST HK3 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI0 ly2 S2 W2 regs2 mem2 md2 res HJ2 HP H10 Hfrs2
         Hres Hbl HK HMO2 Hfd2 Hfs2).
Qed.

Lemma pe_from_KM : pe_from_KM_stmt.
Proof. exact (pe_from_KM_of_KMC pe_from_KMC). Qed.


(* ---- the free of B_ref (jal 0x80a90 -> __wrap_free, returns to PP_REFA 0x80a94): a cut local to this file at
   __wrap_free's entry, and the call through the Kit's afree_call ---- *)
(* a0 = the copy b, ra = PP_REFA; the rest is GI_REF's state (the copy is the only block the call holds). *)
Definition GI_REFC (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  ms_pc_val ms3 = Z_to_bv 64 (SIGMA PS___interceptor_trampoline_free) /\ ms_resv ms3 = None /\
  ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  pregs cx ms3 /\ psaved cx W3 ms3 /\ pheader cx fp W3 ms3 /\ pshadow cx fp W3 ms3 PSH_ps /\
  garr8 SEGS (rd W3 ms3) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  k <= 4 /\ acc <= PA_K2r MT cx /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 1 = w64 (BASE + PP_REFA) /\ getr (ms_regs ms3) 10 = w64 b /\
  pslot cx W3 ms3 PS_FK (pF cx fp) /\ pslot cx W3 ms3 PS_SH (pSH cx fp) /\ pslot cx W3 ms3 PS_F (pF cx fp) /\
  asource_none SEGS KS (rd W3 ms3).

Lemma pe_from_REFC : forall POST, pe_from SK B MT KS POST GI_REFA -> pe_from SK B MT KS POST GI_REFC.
Proof.
intros POST HRA cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
destruct HI as (b & Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hinb & Hk & Hacc & Hperm
  & Hfds & Hfs & Hn26 & R1 & R10 & SFK & SSH & SF & Hsn).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR3 & Hal16 & Hspc & Hsp47 & _ & _ & Hf4096 & Hfceil & _ & HEF & Hinp & Hs1r & Hs1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof HB as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
unfold LLVMF_STK in Hspc.
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hfresh : ~ In (b, p_nF cx) (ablocks B (c_ly cx) (c_S cx)))
  by exact (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ b (p_nF cx) HAR3 Hperm).
set (o := c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)).
assert (Hsp' : spZ (ms_regs ms3) = spZ (PcapEntryDefs.c_regs cx) + o)
  by (subst o; unfold spZ at 1; rewrite Rsp; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Ho16 : o mod 16 = 0).
{ subst o. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r.
  - apply (Z.divide_trans 16 32); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hs1al]].
  - apply Z.mod_divide; [lia | exact Hal16]. }
pose proof pa_base_lo as HBlo. pose proof pa_B_ok as (HB0 & HB40 & HB4).
assert (Hra' : raZ (ms_regs ms3) = BASE + PP_REFA)
  by (unfold raZ; rewrite R1; unfold w64; rewrite unsigned_lit_small by (unfold PP_REFA; lia); reflexivity).
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms3) 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold PP_REFA; lia | reflexivity]).
assert (Hnev : st_nev S3 < EV_MAX).
{ destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & Hnv & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hev0 & _). unfold EV_LIB in *. lia. }
assert (Hch : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (ms_regs ms3) (pch cx)).
{ apply (pe_chain cx fp (ms_regs ms3) ly3 S3 W3 (ms_mem ms3) md3 k _ HB HJ).
  - destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop.
  - reflexivity.
  - exact Rs0.
  - unfold spZ. rewrite Rsp. unfold w64. apply unsigned_lit_small. lia.
  - rewrite Hra'. unfold PP_REFA. lia.
  - destruct Hsav as (S1 & _). exact S1.
  - destruct Hsav as (_ & S2). pose proof (S2 0 ltac:(lia)) as S20. cbn in S20. rewrite Z.sub_0_r in S20.
    exact S20. }
assert (Htr : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms3) (pch cx)) (as_universe B)).
{ apply (pb_ftr cx (ms_regs ms3) HB). rewrite Hra'. unfold PE_FREE_SITES, PP_REFA. cbn. left. lia. }
assert (Hmok : mo_ok MT S3 (mo_free MT)).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMOK & HNEED & _).
  apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK Hmo (mo_free_nonneg MT MTL)).
  pose proof (PA_K12_need MT MTL cx) as HN. pose proof (PA_refused_le MT MTL cx) as HR. lia. }
rewrite (ms_eta ms3 Hrv Hsv Hfreg Hfcsr), Hpc, Hrom, (pal_free _ TL).
eapply SRr_bind.
{ exact (afree_call B MT LAWS AFREE4 W3 (ms_regs ms3) (ms_mem ms3) LLVMF_STK (spZ (PcapEntryDefs.c_regs cx))
    [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 md3 k b (p_nF cx) o
    (getr (ms_regs ms3) 1) (pch cx) HJ Hb3 R10 Hsp' Ho16 ltac:(subst o; lia)
    ltac:(subst o; unfold ASTACK, LLVMF_STK; lia)
    (eq_trans Rgp Hgp0) (eq_trans Rtp Htp0) eq_refl Hraw Hnev Hch Htr
    (fun Hin => False_ind _ (Hfresh Hin)) Hmok). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & (l1 & l2 & Hl3 & Hl2) & Hfrs2 & HK & HMO2
  & Hfd2 & Hfs2).
replace (spZ (PcapEntryDefs.c_regs cx) + o) with (c_sp1 cx) in HK by (subst o; lia).
destruct HK as (K1 & K2 & K3 & K4 & _ & _).
(* the copy, apart from every other block and from the frame *)
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR3 Hb3)
  as (_ & Hb4096 & Hbceil & Hbapp & _ & Hpw & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrq0 Hrq1].
assert (Hapart : forall p m, In (p, m) (ablocks B ly3 S3) -> (p, m) <> (b, p_nF cx) ->
  p + req_size m <= b \/ b + req_size (p_nF cx) <= p).
{ intros p m Hin Hne. rewrite Hl3 in Hin, Hpw. rewrite map_app in Hpw. cbn [map fst snd] in Hpw.
  apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
  - pose proof (km_pw_pre zdisjoint _ (b, req_size (p_nF cx)) _ (p, req_size m) Hpw
      (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (p, m) Hin)) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - exfalso. apply Hne. symmetry. exact Heq.
  - pose proof (km_pw_mid zdisjoint _ (b, req_size (p_nF cx)) _ (p, req_size m) Hpw
      (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (p, m) Hin)) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia. }
assert (HFa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
assert (HFapart : pF cx fp + PE_FRAME <= b \/ b + req_size (p_nF cx) <= pF cx fp).
{ destruct (al_sep _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 HAR3) as (Hsep & _).
  rewrite Hl3, Hfr, map_app in Hsep. cbn [map fst snd] in Hsep. rewrite HFa in Hsep.
  rewrite <- app_assoc in Hsep. cbn [app] in Hsep.
  pose proof (km_pw_mid zdisjoint _ _ _ (pF cx fp, fs_frame_bytes PE_CID) Hsep
    ltac:(apply in_or_app; right; left; reflexivity)) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. change (fs_frame_bytes PE_CID) with 128 in Hz. unfold PE_FRAME. lia. }
(* what the call keeps, by kind *)
set (V3 := aview SEGS (w_H W3) (ms_mem ms3)). set (V2 := aview SEGS (w_H W2) mem2).
assert (KS1 : forall x, c_sp1 cx <= x < 2 ^ 64 -> V2 x = V3 x) by (intros x Hx; apply K1; lia).
assert (KFR : forall x, pF cx fp <= x < pF cx fp + PE_FRAME -> V2 x = V3 x).
{ intros x Hx. apply (K4 PE_CID fp x); [rewrite Hfr; left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd];
  rewrite HFa; change (fs_frame_bytes PE_CID) with 128; unfold PE_FRAME in Hx; lia | unfold PE_FRAME in *; lia]. }
assert (KSH : forall x, pSH cx fp <= x < pSH cx fp + 16 -> V2 x = V3 x).
{ intros x Hx. apply (K4 PE_CID fp x); [rewrite Hfr; left; reflexivity | right; unfold in_zr, shadow_addr; cbn [fst snd];
  rewrite HFa; change (fs_frame_bytes PE_CID / 8) with 16; unfold pSH, shadow_of_addr in Hx; lia |].
  intros Hx2. unfold pSH, shadow_of_addr, SHADOW_OFF in Hx.
  exact (fshadow_not_app (pF cx fp) 16 b (req_size (p_nF cx)) x ltac:(lia) ltac:(unfold PE_FRAME in *; lia)
           Hbapp ltac:(lia) Hx2). }
assert (KBL : forall p m x, In (p, m) (ablocks B ly3 S3) -> (p, m) <> (b, p_nF cx) -> p <= x < p + req_size m ->
  V2 x = V3 x).
{ intros p m x Hin Hne Hx. replace x with (p + (x - p)) by lia.
  apply (K2 p m (x - p) Hin); [lia|]. pose proof (Hapart p m Hin Hne). lia. }
assert (KENV : forall x, asrc_env_addr KS x -> V2 x = V3 x).
{ intros x Hx. destruct (asil_env _ _ _ _ ASIL x Hx) as (Hi & Hns & Hne). exact (K3 x Hi Hns Hne). }
assert (Hsl : forall off v, 16 <= off <= 144 -> pslot cx W3 ms3 off v ->
  pslot cx W2 (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) off v).
{ intros off v Hoff Hv. unfold pslot in *. cbn [ms_mem mkst]. apply (km_rd _ _ _ _ _ _ Hv). intros x Hx. apply KS1. lia. }
apply (HRA cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)) md2
  HB HJ2 ltac:(rewrite Hfrs2; exact Hfr) (mle_station MT _ _ _ _ _ MTL Hmo HMO2)).
split.
{ split.
  { (* pe_body at PP_REFA *)
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
    split; [exact R1|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold pregs. cbn [ms_regs mkst].
      exact (conj (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) Rsp)
              (conj (eq_trans (HP 8 ltac:(unfold acallee_saved; lia)) Rs0)
              (conj (eq_trans (HP 9 ltac:(unfold acallee_saved; lia)) Rs1)
              (conj (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) Rgp)
                    (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) Rtp))))). }
    split.
    { destruct Hsav as (S1 & S2'). unfold psaved. cbn [ms_mem mkst]. split.
      - apply (km_rd _ _ _ _ _ _ S1). intros x Hx. apply KS1. lia.
      - intros j Hj. apply (km_rd _ _ _ _ _ _ (S2' j Hj)). intros x Hx. apply KS1. lia. }
    split.
    { destruct Hhd as (H1 & H2 & H3 & H4). unfold pheader. cbn [ms_mem mkst].
      split; [|split; [|split]].
      - apply (km_rd _ _ _ _ _ _ H1). intros x Hx. apply KFR. unfold PE_FRAME. lia.
      - apply (km_rd _ _ _ _ _ _ H2). intros x Hx. apply KFR. unfold PE_FRAME. lia.
      - apply (km_rd _ _ _ _ _ _ H3). intros x Hx. apply KFR. unfold PE_FRAME. lia.
      - apply (km_rd _ _ _ _ _ _ H4). intros x Hx. apply KFR. unfold PE_FRAME, PE_FLAGPTR in *. lia. }
    split.
    { unfold pshadow in *. cbn [ms_mem mkst]. intros i Hi.
      assert (Hl : length PSH_ps = 16%nat) by reflexivity. rewrite Hl in Hi.
      fold V2. rewrite (KSH (pSH cx fp + Z.of_nat i) ltac:(lia)). exact (Hsh i ltac:(rewrite Hl; exact Hi)). }
    split; [reflexivity|].
    cbn [ms_mem mkst].
    pose proof HB as (_ & _ & _ & _ & Hinput & _).
    destruct Hinput as [(Hn0 & _) | (Hnpos & Hinc)].
    - unfold c_n in Hn0. destruct (c_pl cx) as [|x l]; [apply garr8_nil | cbn in Hn0; lia].
    - assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hinc).
      assert (Hne : (c_p cx, c_n cx) <> (b, p_nF cx)) by (intros Heq; rewrite Heq in Hinc; exact (Hfresh Hinc)).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrqn].
      apply (km_ga _ _ _ _ _ _ Hinb). intros x Hx. apply (KBL _ _ x Hin3 Hne). rewrite length_map in Hx.
      unfold c_n in *. lia. }
  split; [lia|]. split; [pose proof (PA_refused_le MT MTL cx); lia|].
  split.
  { rewrite Hl3 in Hperm. pose proof (Permutation_app_inv l1 l2 _ [] _ Hperm) as HP2.
    rewrite app_nil_r in HP2. rewrite Hl2, app_nil_r. exact HP2. }
  split; [rewrite Hfd2; exact Hfds | rewrite Hfs2; exact Hfs]. }
split; [exact Hn26|].
split; [apply Hsl; [unfold PS_FK; lia | exact SFK]|].
split; [apply Hsl; [unfold PS_SH; lia | exact SSH]|].
split; [apply Hsl; [unfold PS_F; lia | exact SF]|].
cbn [ms_mem mkst].
apply (BCL.asource_none_frame KS (mrestrict (w_H W3) (ms_mem ms3))); [|exact Hsn].
intros x Hx. apply (mbyte_of_aview SEGS). exact (KENV x Hx).
Qed.


(* B_ref's run from PP_ref (0x80a80) to __wrap_free: `beqz s3` not taken (s3 = -1), `ld a0,0(s4)` (ps.f = 0,
   p_psnull), `bnez a0` to abort 0x81034 not taken, `mv a0,s2`, `jal __wrap_free` (0x80a90). Nothing is written. *)
Lemma pe_from_REF_run : forall POST, pe_from SK B MT KS POST GI_REFC -> pe_from SK B MT KS POST GI_REF.
Proof.
intros POST HRC cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct HI as (b & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & Hgood & R18 & R19 & R20 & SFK & SSH & SF
  & Hnull & Hsn).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR3 & Hal16 & Hspc & Hsp47 & _ & _ & Hf4096 & Hfceil & _ & HEF & Hinp & Hs1r & Hs1al).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LLVMF_STK in Hspc.
pose proof (ref_entry cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr Hregs R20 SSH Hnull) as HS.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
remember (Eimg (Ereg (ms_regs ms3) (ref_extra (pSH cx fp)))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; subst E; rewrite Eimg_low by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (U19 : U E (SOff 19 0) = 2 ^ 64 - 1)
  by (rewrite (km_U E 19 (-1)) by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R19);
      reflexivity).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
clear HEdef.
rewrite (ms_eta ms3 Hrv Hsv Hfreg Hfcsr), Hpc, Hrom.
change (w64 (BASE + PP_ref)) with (Z_to_bv 64 (BASE + PP_ref)).
(* PP_ref 0x80a80 `beqz s3`: s3 = -1, so the refused tail 0x80a84 *)
psrr_branch_tok RUN BR HS SHOK Espan.
{ exfalso. rewrite branch_eq_U, U19, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
pose proof (mk_refl W3 (ms_mem ms3) (c_sp1 cx) (c_sp1 cx)) as UN.
paj_run_tok RUN HS HJ SHOK Espan; [ro_awr|].
km_mk_step HFr U9 (c_sp1 cx) (c_sp1 cx) UN. clear HF HFr HG.
(* 0x80a88 `bnez a0` (abort 0x81034): a0 = ps.f = 0 (the region's literal), so the engine decides it not taken *)
(* at __wrap_free (jal 0x80a90): a0 = s2 = b, ra = PP_REFA *)
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?W) ?msx) =>
  pose proof HS as (Hf1 & Hpc1 & Hsv1 & Hrv1 & Hfc1 & Hrom1 & _);
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom setpc ss_pc ss_resv resv_denot]
    in Hf1, Hpc1, Hsv1, Hrv1, Hfc1, Hrom1;
  prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10;
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2;
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3;
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4;
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8;
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9;
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q10;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
    apply (HRC cx fp k acc ly3 S3 W3 msx mdq HB HJ Hfr Hmo);
    pose proof (pe_body_keep cx fp PP_ref (SIGMA PS___interceptor_trampoline_free - BASE) W3 ms3 msx
      PSH_ps (c_sp1 cx) (c_sp1 cx) Hbody
      ltac:(rewrite Hpc1; unfold w64; f_equal; lia) Hrv1 Hsv1 Hrom1 Hf1 Hfc1
      ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) UN
      ltac:(lia) ltac:(lia) ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) Hf4096 Hfceil Hinp)
      as (_ & _ & _ & _ & _ & _ & Hpr' & Hsav' & Hhd' & Hsh' & _ & Hinb');
    exists b;
    split; [exact Hpc1|]; split; [exact Hrv1|]; split; [exact Hsv1|]; split; [exact Hrom1|];
    split; [exact Hf1|]; split; [exact Hfc1|]; split; [exact Hpr'|];
    split; [exact Hsav'|]; split; [exact Hhd'|]; split; [exact Hsh'|]; split; [exact Hinb'|];
    split; [exact Hk|]; split; [exact Hacc|]; split; [exact Hperm|];
    split; [rewrite (proj1 (km_wvb _ _ _)); exact Hfds|]; split; [rewrite (proj2 (km_wvb _ _ _)); exact Hfs|];
    split; [exact Hn26|];
    split; [rewrite Q1; reflexivity|];
    split; [rewrite Q10; exact R18|];
    split; [exact (pslot_keep cx W3 ms3 msx _ _ PS_FK _ SFK UN ltac:(unfold PS_FK; lia) ltac:(unfold PS_FK; lia)
                     ltac:(unfold PS_FK; lia))|];
    split; [exact (pslot_keep cx W3 ms3 msx _ _ PS_SH _ SSH UN ltac:(unfold PS_SH; lia) ltac:(unfold PS_SH; lia)
                     ltac:(unfold PS_SH; lia))|];
    split; [exact (pslot_keep cx W3 ms3 msx _ _ PS_F _ SF UN ltac:(unfold PS_F; lia) ltac:(unfold PS_F; lia)
                     ltac:(unfold PS_F; lia))|];
    exact (asource_none_keep B KS ASIL W3 _ _ _ _ Hsn UN ltac:(lia))
  end
end.
Qed.

Lemma pe_from_REF_free : pe_from_REF_free_stmt.
Proof. intros POST HA. exact (pe_from_REF_run POST (pe_from_REFC POST HA)). Qed.

Lemma pe_from_REF : pe_from_REF_stmt.
Proof. exact (pe_from_REF_of_parts pe_from_REFA pe_from_REF_free). Qed.


(* ---- C: PP_K3 0x80acc -> pcap_source_next (jal 0x80b00) -> PP_KD 0x80b04 ---- *)
(* The stretch's symbolic start. Atoms beside the registers: 32 = the shadow base SB_E (the word of PS_SHB), 33 = the frame F, 34 = its shadow SH, 35 = cap, 36 = the input's first byte d.
   Regions: the spill slots [s1+16, s1+152) with the seven words the cut states (the run writes PS_TSP 0x80afc
   and PS_BUF 0x80acc inside the same window), the timestamp cell F + PO_TS (sd a0,0(a3) 0x80ae8) and the one
   shadow byte of `ts` (sb zero,0xc(a0) 0x80ae0).
   The run reads and writes NO shadow cell through a check (this image checks `ts` nowhere in 0x80acc..0x80b00),
   so the token list is empty and the token band is the null page, disjoint from all three regions. *)
Definition k3_span : Z * Z := (0, 4095).
Definition k3_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 16 152 16 152
     [YP09.mkChunk PS_FK (CVal 8 (SOff 33 0)); YP09.mkChunk PS_D (CVal 8 (SOff 36 0));
      YP09.mkChunk PS_F (CVal 8 (SOff 33 0)); YP09.mkChunk PS_SH (CVal 8 (SOff 34 0));
      YP09.mkChunk PS_SHB (CVal 8 (SOff 32 0)); YP09.mkChunk PS_CAP (CVal 8 (SOff 35 0));
      YP09.mkChunk PS_F0 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 33%nat) PO_TS (PO_TS + 8) PO_TS (PO_TS + 8) [];
   YP09.mkRegion (Some 34%nat) 12 13 12 13 []].
Definition k3_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 140737479966720 0);
           (32%nat, mkAF SB_E SB_E 0); (33%nat, mkAF 4096 140737479966592 5);
           (34%nat, mkAF SB_E (SB_E + 2 ^ 44) 0); (35%nat, mkAF 0 2040 0); (36%nat, mkAF 0 255 0)] [] [].
Definition ss_k3 : sstate := mkSS PP_K3 sr_atoms k3_regions None k3_facts.
Definition k3_extra (cx : ecx) (fp : Z) : list word :=
  map (Z_to_bv 64) [SB_E; pF cx fp; pSH cx fp; p_cap cx; p_d cx].

Lemma k3_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 buf,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pe_body cx fp PP_K3 W3 ms3 PSH_ps ->
  getr (ms_regs ms3) 10 = w64 buf -> 4096 <= buf -> buf + p_bn cx <= alloc_ceiling ->
  pslot cx W3 ms3 PS_FK (pF cx fp) -> pslot cx W3 ms3 PS_D (p_d cx) ->
  pslot cx W3 ms3 PS_F (pF cx fp) -> pslot cx W3 ms3 PS_SH (pSH cx fp) ->
  pslot cx W3 ms3 PS_SHB SHADOW_OFF -> pslot cx W3 ms3 PS_CAP (p_cap cx) ->
  pslot cx W3 ms3 PS_F0 (pF cx fp) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (k3_extra cx fp))) ss_k3 (restrict (w_H W3) ms3) /\
  sh_ok SEGS EBx [] (Eimg (Ereg (ms_regs ms3) (k3_extra cx fp))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 buf HB HJ Hfrs Hbody R10 Hbuf0 Hbuf1 Q16 Q24 Q32 Q40 Q72 Q120 Q144.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & _).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hin) as (HFal & HFapp & HFpres & HFSpres).
rewrite EFA in HFal, HFapp, HFpres, HFSpres.
change (fs_frame_bytes PE_CID) with 128 in HFpres, HFSpres.
pose proof (p_sizes cx) as (HnF & Hcapr & Hbnr). pose proof (p_d_range cx) as Hdr.
assert (HSH : pSH cx fp = SB_E + pF cx fp / 8) by reflexivity.
unfold PE_FRAME in Hfceil.
assert (HpF47 : pF cx fp + 128 <= 140737479966720) by lia.
assert (HSHd : 0 <= pF cx fp / 8 <= 17592186044416)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hs1r : 70368744177664 <= c_sp1 cx <= 140737488355328) by (unfold LLVMF_STK in *; lia).
set (E := Eimg (Ereg (ms_regs ms3) (k3_extra cx fp))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (k3_extra cx fp)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact Rs1).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pF cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (p_cap cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 4)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SB_E) by (rewrite E32; apply unsigned_lit_small; unfold SB_E; lia).
assert (U33 : bv_unsigned (ew E 33) = pF cx fp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pSH cx fp)
  by (rewrite E34; apply unsigned_lit_small; rewrite HSH; unfold SB_E in *; lia).
assert (U35 : bv_unsigned (ew E 35) = p_cap cx) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = p_d cx) by (rewrite E36; apply unsigned_lit_small; lia).
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K3)) (ms_mem ms3) (seg_rom SEGS))
  by (destruct ms3; cbn in Hpc, Hrv, Hsv, Hrom, Hfreg, Hfcsr |- *; subst; reflexivity).
split; [|apply Forall_nil].
rewrite Hms at 1. rewrite restrict_mkst_fx. unfold ss_k3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold k3_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + fold E. rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; unfold LLVMF_STK; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_FK 8 (SOff 33 0) (pF cx fp));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q16).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_D 8 (SOff 36 0) (p_d cx));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q24).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_F 8 (SOff 33 0) (pF cx fp));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q32).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_SH 8 (SOff 34 0) (pSH cx fp));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite HSH; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB_E in *; lia | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q40).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_SHB 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q72).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_CAP 8 (SOff 35 0) (p_cap cx));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q120).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_F0 8 (SOff 33 0) (pF cx fp));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Q144).
  + fold E. rewrite U33. split; [unfold PO_TS; lia|]. split; [unfold PO_TS; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (pF cx fp + o) ltac:(unfold PO_TS in *; lia))).
  + fold E. rewrite U34. split; [rewrite HSH; unfold SB_E in *; lia|].
    split; [rewrite HSH; unfold SB_E in *; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    destruct (HFSpres o ltac:(change (128 / 8) with 16; lia)) as [Hp _].
    unfold shadow_addr in Hp. rewrite HSH. unfold SB_E, SHADOW_OFF in *. exact Hp.
- apply pairwise_disjoint_of_extents.
  unfold k3_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  fold E. rewrite U9, U33, U34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HSH. unfold PO_TS, SB_E in *. unfold LLVMF_STK in *.
  assert (HFlo : pF cx fp + 128 <= 2147450880 \/ 17592186044416 <= pF cx fp).
  { destruct Hfapp as (_ & [HL | (HH & _)]);
    [left; unfold kLowShadowBeg, SHADOW_OFF, PE_FRAME in *; lia
    | right; unfold kHighMemBeg in HH; lia]. }
  destruct HFlo as [HFlo | HFlo];
  [ assert (Hq : pF cx fp / 8 <= 268435456) by (apply Z.div_le_upper_bound; lia)
  | assert (Hq : 2199023255552 <= pF cx fp / 8) by (apply Z.div_le_lower_bound; lia) ];
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [k3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U9, U32, U33, U34, U35, U36.
  assert (U10 : bv_unsigned (ew E 10) = buf)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 10 10%bv eq_refl), R10;
        apply unsigned_lit_small; lia).
  rewrite U10.
  change (2 ^ 5) with 32. change (2 ^ 46) with 70368744177664.
  change (2 ^ 47) with 140737488355328. change (2 ^ 44) with 17592186044416.
  rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  assert (HF32 : pF cx fp mod 32 = 0) by exact HFal.
  rewrite HSH. unfold SB_E in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
Qed.

(* ---- what cut C needs beyond this file's helpers ---------------------------------------------------------- *)
(* The model and memory facts of the call (k3_nxF, k3_chain_lh, k3_lh_fit, k3_present, k3_vm4) live in a Theorem Labs lane's
   PcapEntryCalls.v; the ones below are the lib/B twins of lib/A/Prog/PcapHarnessTail.v's tail_geo, aro_now, meta_now,
   pch_achain, ablocks_nodup / notin_prefix and hfoot / foot_kept, at this image's frame. *)

(* Cut C's own Section hypotheses: the read-only window lies below the open-file-list head (PcapBase's class, as
   every pcap walk takes it), and pcap_source_next's contract at this image's entry and stack datum.
   TAKEN FROM: tpcap_source_next_specX — lib/A/Prog/PcapSourceNextSpec.v (a Theorem Labs lane), through PcapEntryCalls' AN. *)
Context {HRO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* This image's pcap_source_next window: PcapEntryDefs.v, "Stack room at a call of the body", bounds every callee
   of the body by 32368 bytes below s1 (the asan-ubsan pcap_source_next asks 272 + 64 + AFREAD_STK). The cut is
   stated for any window inside that bound, so it does not depend on the figure's owner. *)
Variable NSTK : Z.
Hypothesis HNSTK : 0 <= NSTK <= 32368.
Hypothesis HNEXT : AN.tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NSTK B MT KS
  (BASE + AF_pcap_source_next).

(* The stack geometry of the body, from pe_base alone. *)
Lemma k3_geo : forall cx, pe_base SK B MT KS cx ->
  spZ (PcapEntryDefs.c_regs cx) mod 16 = 0 /\ c_sp1 cx mod 32 = 0 /\
  spZ (PcapEntryDefs.c_regs cx) - 288 <= c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 /\
  alloc_ceiling <= ly_stk_lo (c_ly cx) /\ ly_stk_lo (c_ly cx) + LLVMF_STK <= spZ (PcapEntryDefs.c_regs cx) /\
  spZ (PcapEntryDefs.c_regs cx) <= ly_stk_hi (c_ly cx) /\ ly_stk_hi (c_ly cx) <= 2 ^ 47 /\
  spZ (PcapEntryDefs.c_regs cx) <= ly_top (c_ly cx) /\ ly_top (c_ly cx) <= ly_stk_hi (c_ly cx).
Proof.
intros cx HB.
pose proof HB as ((_ & _ & _ & _ & _ & Hstk & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof Hstk as (Hal & Hs0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
assert (Hsp : spZ (PcapEntryDefs.c_regs cx) - 288 <= c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 /\
              c_sp1 cx mod 32 = 0).
{ rewrite Hsp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z.div_mod (spZ (PcapEntryDefs.c_regs cx) - 256) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ (PcapEntryDefs.c_regs cx) - 256) 32 ltac:(lia)) as M.
  split; [lia | rewrite Z.mul_comm; apply Z_mod_mult]. }
repeat split; try assumption; try lia.
Qed.

(* The harness's journal is W_journalG's ajournal_gx over pe_G: a donor journal from a start memory memS that
   agrees with c_mem outside g_file / g_file_len. Those two globals are image bytes, so memS and c_mem agree on
   every byte above the allocator's ceiling, and on every byte outside pe_G. *)
Lemma k3_aview_memS : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> 0 <= a < 2 ^ 64 ->
  ~ inG pe_G a -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a Hag Ha HnG. apply (aview_gagree SEGS pe_G _ _ _ a Hag).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma k3_gagree_high : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a Hag Ha. pose proof asan_consts as (C1 & _).
apply (k3_aview_memS cx memS a Hag ltac:(lia)).
pose proof (pa_obj_img 4 ltac:(lia)) as O4. pose proof (pa_obj_img 2 ltac:(lia)) as O2.
unfold pcap_img_end, YImgTop.IMG_TOP in O4, O2.
unfold pe_G. intros HG.
apply inG_cons in HG as [HG|HG]; [|apply inG_cons in HG as [HG|HG]; [|exact (inG_nil a HG)]];
  unfold in_zr in HG; cbn [fst snd] in HG; lia.
Qed.

(* The read-only data at a state of the walk: pe_base's arodata_okP at c_mem, moved to the inner journal's start
   memory (pe_base keeps the read-only bytes out of pe_G) and along the journal. *)
Lemma k3_aro : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _ & _ & _ & _ & _ & _ & _ & _ & HGX & HGD & _).
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ|].
intros a Hro Ho He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
pose proof (pa_img_range a Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
rewrite (k3_aview_memS cx memS a Hag ltac:(lia)); [exact (Hrod a Hro Ho He)|].
intros HaG. exact (proj1 (HGD a HaG) Hro).
Qed.

(* The stream's meta region at a state of the walk (PSourceMeta.asrc_meta_inv_kept through the inner journal). *)
Lemma k3_meta : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly3 (mrestrict (w_H W3) mem3) (c_M cx).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & _ & _ &
  _ & _ & _ & HGX & HGD & _).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [rewrite Eextra; exact HX|]. split; [exact Himg|].
split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
  pose proof (pa_img_range x Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
  rewrite <- (k3_aview_memS cx memS x Hag ltac:(lia)).
  + apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
  + intros HxG. destruct (HGD x HxG) as (_ & Hnm & _). apply Hnm. lia.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  rewrite <- (k3_aview_memS cx memS a Hag ltac:(lia)).
  + apply F5.
    * apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    * intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi. pose proof (Himg a Hi). lia.
  + intros HaG. pose proof (proj1 (HGX a HaG)) as Hi. pose proof (Himg a Hi). lia.
Qed.

(* The call chain the harness hands to a callee: its own frame record, when it lies below the stack top. *)
Lemma k3_achain : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (PcapEntryDefs.c_regs cx) - 8) = Some (raZ (PcapEntryDefs.c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (PcapEntryDefs.c_regs cx) - 16) = Some (s0Z (PcapEntryDefs.c_regs cx)) ->
  achain ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (PcapEntryDefs.c_regs cx)) (pch cx).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag R8 R16.
pose proof (k3_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hlo & Hhi & H47 & Htop & Htop2).
unfold LLVMF_STK in Hlo.
pose proof HB as ((_ & _ & Hra4 & _ & _ & _ & _ & Hch & _) & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top (c_ly cx)); [exact Etop|].
assert (H8 : spZ (PcapEntryDefs.c_regs cx) mod 8 = 0).
{ pose proof (Z.div_mod (spZ (PcapEntryDefs.c_regs cx)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
  apply Z.mod_divide; [lia|]. exists (2 * (spZ (PcapEntryDefs.c_regs cx) / 16)). lia. }
pose proof asan_consts as (C1 & _).
assert (Hc0 : alloc_ceiling <= spZ (PcapEntryDefs.c_regs cx)) by lia.
assert (Ht64 : ly_top (c_ly cx) <= 2 ^ 64) by (change (2 ^ 47) with 140737488355328 in H47;
  change (2 ^ 64) with 18446744073709551616; lia).
unfold pch. destruct (Z.ltb_spec (spZ (PcapEntryDefs.c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
- assert (HK : forall a, spZ (PcapEntryDefs.c_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
    by (intros a Ha; rewrite <- (k3_gagree_high cx memS a Hag ltac:(lia)); apply F1; lia).
  refine (achain_push _ _ _ _ _ _ _ _ Hch Ht64 HK R8 R16 Hra4 Hc0 H8 _ _); lia.
- left. split; [right; left; lia | reflexivity].
Qed.



(* NoDup of the live blocks (they are pairwise disjoint and each has a positive size). *)
Lemma k3_nodup_of_split : forall {X} (l : list X),
  (forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False) -> List.NoDup l.
Proof.
intros X l. induction l as [|a t IH]; intros H; [apply List.NoDup_nil|]. apply List.NoDup_cons.
- intros Hin. apply List.in_split in Hin as (t1 & t2 & ->). apply (H [] a t1 t2). reflexivity.
- apply IH. intros l1 x l2 l3 E. apply (H (a :: l1) x l2 l3). rewrite E. reflexivity.
Qed.

Lemma k3_ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply k3_nodup_of_split. intros l1 x l2 l3 E.
pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md x x l1 l2 l3 HAR E) as D.
assert (Hin : In x (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct x as [p n].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R _].
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

Lemma k3_notin_prefix : forall {X} (l L M : list X) x,
  List.NoDup l -> Permutation l (L ++ M) -> List.In x M -> ~ List.In x L.
Proof.
intros X l L M x Hnd Hp HxM. apply (Permutation_NoDup Hp) in Hnd. clear Hp l.
induction L as [|a L IH]; intros Hin; [destruct Hin|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hna Hnd].
destruct Hin as [-> | Hin]; [apply Hna; apply in_or_app; right; exact HxM | exact (IH Hnd Hin)].
Qed.

(* The shadow index of `ts`: ts in scope sets byte 12 only. *)
Lemma k3_psh_ts : forall i, (i < 16)%nat -> i <> 12%nat -> nth i PSH_ts 0 = nth i PSH_ps 0.
Proof. intros i Hi Hne. do 16 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.

(* The bytes of the body every cut from PP_KD on states and pcap_source_next may not write: the saved registers, the
   spill slots, the frame's header, its shadow, the input, and the two globals. *)
Definition k3_foot (cx : ecx) (fp a : Z) : Prop :=
  (spZ (PcapEntryDefs.c_regs cx) - 104 <= a < spZ (PcapEntryDefs.c_regs cx)) \/
  (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/
  (pSH cx fp <= a < pSH cx fp + 16) \/ (c_p cx <= a < c_p cx + c_n cx) \/
  (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) \/ (pa_val (A_OBJ 4) <= a < pa_val (A_OBJ 4) + 8).

(* A keep relation over a footprint, from its pointwise form (aview equality is decidable). *)
Lemma k3_mkw_of_foot : forall (W3 W4 : world SEGS) m m' (Fo : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> Fo a -> aview SEGS (w_H W4) m' a = aview SEGS (w_H W3) m a) ->
  mkw W3 W4 m m' (fun a => ~ Fo a).
Proof.
intros W3 W4 m m' Fo H a Ha Hn.
assert (Hdec : forall x y : option Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (Hdec (aview SEGS (w_H W4) m' a) (aview SEGS (w_H W3) m a)) as [e | ne]; [exact e|].
exfalso. apply Hn. intros Hf. exact (ne (H a Ha Hf)).
Qed.

(* ---- C itself ---- *)
Lemma pe_from_K3 : pe_from_K3_stmt.
Proof.
unfold pe_from_K3_stmt. intros POST HKD.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HGI.
destruct HGI as (b & h & buf & Hcut & Hn26 & Hgood & Hbuf4096 & R10 & R18 & R20 & R24 & QD & QSHB & QF0 & QFK
  & QF & QSH & QCAP & Hglob & Hps & Hsrc).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (p_sizes cx) as (HnF & Hcapr & Hbnr).
pose proof (k3_geo cx HB) as (Hal16 & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Htop & Htop2).
unfold LLVMF_STK in Hslo. change (2 ^ 47) with 140737488355328 in H47.
(* the three blocks of the cut *)
assert (Hbin : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hhin : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hfbin : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR3 Hbin) as (_ & Hb0 & Hb1 & Hbapp & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR3 Hhin) as (_ & Hh0 & Hh1 & Hhapp & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR3 Hfbin)
  as (_ & Hu0 & Hu1 & Huapp & Hupres & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
change (req_size SRC_FILE_BLOCK) with 1304 in Hh1, Hhapp.
assert (ERS : req_size (p_bn cx) = p_bn cx)
  by (unfold req_size; destruct (Z.eqb_spec (p_bn cx) 0) as [E0|_]; [lia | reflexivity]).
rewrite ERS in Hu1, Huapp, Hupres.
assert (HG : gx_ok SEGS B pe_G) by exact (pb_HG cx HB).
destruct (k3_entry cx fp k ly3 S3 W3 ms3 md3 buf HB HJ Hfrs Hbody R10 Hbuf4096 Hu1 QFK QD QF QSH QSHB QCAP QF0)
  as [HS SHOK].
set (E := Eimg (Ereg (ms_regs ms3) (k3_extra cx fp))) in HS, SHOK.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
unfold PE_FRAME in Hfceil, Hfapp.
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as (Hfa64 & _ & _).
rewrite EFA in Hfa64.
assert (HpF8 : 0 <= pF cx fp / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HSH : pSH cx fp = 2147450880 + pF cx fp / 8) by reflexivity.
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hshlen & Hinp).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (k3_extra cx fp)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pF cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pSH cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (p_cap cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) _ 4)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small;
      change (2 ^ 64) with 18446744073709551616; lia).
assert (U33 : bv_unsigned (ew E 33) = pF cx fp)
  by (rewrite E33; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
assert (U34 : bv_unsigned (ew E 34) = pSH cx fp)
  by (rewrite E34; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
pose proof (bpaj_run_x B LAWS pe_G HG 0 []) as RUN.
(* 0x80acc .. 0x80afc, the stores and loads of the stretch; the NULL test 0x80ad0 (beqz a0 -> 0x81034, PP_bufnull)
   is decided by the run itself from atom 10's fact 4096 <= buf (k3_facts, GI_K3's `4096 <= buf`): decide_cond2
   finds the ranges [4096, ..] and [0, 0] apart, so the branch is not taken and the run stops at the call. *)
paj_run_tok RUN HS HJ SHOK k3_span.
{ apply awr_ok_x_of0. unfold ss_k3, k3_regions. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (PcapEntryDefs.c_regs cx));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen E _ _ LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token]
            (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(PE_CID, fp)] 33%nat (pF cx fp));
    [reflexivity | exact U33 | |].
  - cbn [YP09.r_wlo YP09.r_whi]. unfold PO_TS. intros a Ha. right. right. right.
    exists PE_CID, fp. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes PE_CID) with 128. lia.
  - eapply (awr_ok_cons_gen E _ _ LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token]
              (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(PE_CID, fp)] 34%nat (pSH cx fp));
      [reflexivity | exact U34 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists PE_CID, fp. split; [left; reflexivity|]. right.
    unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA.
    change (fs_frame_bytes PE_CID / 8) with 16.
    unfold pSH, shadow_of_addr, SHADOW_OFF in *. lia. }
(* ---- the state at the call 0x80b00 ---- *)
(* What the run kept: everything outside its three windows. *)
set (RW := fun a => (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/ (pF cx fp + 96 <= a < pF cx fp + 104) \/
                    (pSH cx fp + 12 <= a < pSH cx fp + 13)).
assert (RUNK : mkw W3 W3 (ms_mem ms3) (ms_mem ms) RW).
{ intros a Ha Hn. refine (kept_of_frame (segs := SEGS) E (ss_mem ss_k3) (w_H W3) (ms_mem ms3) (ms_mem ms) RW HFr _ a Ha Hn).
  intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U33, ?U34 in Hrr; unfold RW;
     first [left; lia | right; left; lia | right; right; lia]|]).
  destruct Hinw. }
pose proof (st_ok_region_nth E _ _ 0%nat _ HS ltac:(cbn; reflexivity)) as HR0.
pose proof (st_ok_region_nth E _ _ 1%nat _ HS ltac:(cbn; reflexivity)) as HR1.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS ltac:(cbn; reflexivity)) as HR2.
cbn [ms_mem restrict] in HR0, HR1, HR2.
(* where things sit *)
assert (HFlo : pF cx fp + 128 <= 2147446784 \/ 17594333495296 <= pF cx fp).
{ destruct Hfapp as (_ & [HL | (HH & _)]); [left; unfold kLowShadowBeg in HL; lia | right; unfold kHighMemBeg in HH; lia]. }
assert (Wapp : forall q n a, in_app q n -> q <= a < q + n -> ~ (pSH cx fp <= a < pSH cx fp + 16)).
{ intros q n a (Hq & Happ) Ha. rewrite HSH. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
assert (Hsf : forall i, 0 <= i < 16 -> ~ (pF cx fp <= pSH cx fp + i < pF cx fp + 128)).
{ intros i Hi Hbad. rewrite HSH in Hbad. destruct HFlo; lia. }
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as Hfoff.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfoff. rewrite EFA in Hfoff.
change (fs_frame_bytes PE_CID) with 128 in Hfoff.
assert (Himg : forall a, in_img SEGS a -> 0x10000 <= a < (symaddr ImgPages.AsanUbsan.top)).
{ intros a Ha. pose proof (pa_img_range a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. exact Hr. }
pose proof (pa_obj_img 2 ltac:(lia)) as O2. pose proof (pa_obj_img 4 ltac:(lia)) as O4.
unfold pcap_img_end, YImgTop.IMG_TOP in O2, O4.
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hfin) as (_ & _ & HFpres & _).
rewrite EFA in HFpres. change (fs_frame_bytes PE_CID) with 128 in HFpres.
assert (E10 : ew E 10 = Z_to_bv 64 buf) by (rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10; reflexivity).
(* the body at the call: saved registers, header, shadow (ts now in scope), input *)
assert (F1 : psaved cx W3 ms).
{ destruct Hsaved as (S8 & Sj). split.
  - apply (rdword_keepw W3 W3 _ _ RW _ _ S8 RUNK);
      [lia | change (2 ^ 64) with 18446744073709551616; lia | intros j Hj; unfold RW; rewrite HSH; lia].
  - intros j Hj. apply (rdword_keepw W3 W3 _ _ RW _ _ (Sj j Hj) RUNK);
      [lia | change (2 ^ 64) with 18446744073709551616; lia | intros i Hi; unfold RW; rewrite HSH; lia]. }
assert (F2 : pheader cx fp W3 ms).
{ destruct Hhdr as (H1 & H2 & H3 & H4). unfold pheader.
  split; [|split; [|split]];
  [ apply (rdword_keepw W3 W3 _ _ RW _ _ H1 RUNK) | apply (rdword_keepw W3 W3 _ _ RW _ _ H2 RUNK)
  | apply (rdword_keepw W3 W3 _ _ RW _ _ H3 RUNK) | apply (rdword_keepw W3 W3 _ _ RW _ _ H4 RUNK) ];
  unfold PE_FLAGPTR; try (change (2 ^ 64) with 18446744073709551616); try lia;
  intros j Hj; unfold RW; intros [X|[X|X]]; first [lia | apply (Hsf 12); lia]. }
assert (F3 : pshadow cx fp W3 ms PSH_ts).
{ intros i Hi. change (length PSH_ts) with 16%nat in Hi.
  destruct (Nat.eq_dec i 12) as [-> | Hne].
  - change (nth 12 PSH_ts 0) with 0. cbn [Z.of_nat].
    apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms) _ 0); [|lia].
    exact (field_of_region E _ 34%nat (pSH cx fp) _ 12 13 12 13 12 1%N (SLit 0) 0 HR2 U34
             ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
  - rewrite (k3_psh_ts i Hi Hne).
    rewrite (RUNK (pSH cx fp + Z.of_nat i)); [exact (Hsh i ltac:(rewrite Hshlen; unfold PE_NSH; lia))
      | change (2 ^ 64) with 18446744073709551616; rewrite HSH; lia |].
    unfold RW. intros [X|[X|X]]; [rewrite HSH in X; lia | apply (Hsf (Z.of_nat i)); lia | lia]. }
assert (F4 : garr8 SEGS (rd W3 ms) (c_p cx) (map (fun x : byte => bv_unsigned x) (c_pl cx))).
{ destruct (Z.eq_dec (c_n cx) 0) as [Hn0|Hn0].
  - unfold c_n in Hn0. destruct (c_pl cx) as [|x l]; [apply garr8_nil | cbn in Hn0; lia].
  - assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin0]] & _); [lia|].
      apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin0. }
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hpin) as (_ & Hp0 & Hp1 & Hpapp & _).
    pose proof (req_size_pos (c_n cx) ltac:(unfold c_n; lia)) as [_ Hrqp].
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ PE_CID fp HAR3 Hpin Hfin) as Dpf.
    unfold zdisjoint in Dpf. cbn [fst snd] in Dpf. rewrite EFA in Dpf. change (fs_frame_bytes PE_CID) with 128 in Dpf.
    apply (garr8_keepw W3 W3 _ _ RW _ _ Hinp RUNK); rewrite ?length_map; try fold (c_n cx);
      [lia | change (2 ^ 64) with 18446744073709551616; lia |].
    intros j Hj. unfold RW. intros [X|[X|X]]; [lia | lia |].
    apply (Wapp (c_p cx) (req_size (c_n cx)) (c_p cx + j) Hpapp); lia. }
(* the slots at the call, from the run's slot region *)
assert (F5 : pslots cx fp W3 ms /\ pslot cx W3 ms PS_BUF buf).
{ assert (BpF : 0 <= pF cx fp < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
  split; [|exact (k2_slot E W3 ms cx _ _ _ _ _ PS_BUF 10 buf HR0 U9 ltac:(cbn; tauto) E10
                    ltac:(change (2 ^ 64) with 18446744073709551616; lia))].
  split; [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_F0 33 (pF cx fp) HR0 U9 ltac:(cbn; tauto) E33 BpF)|].
  split; [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_D 36 (p_d cx) HR0 U9 ltac:(cbn; tauto) E36
                   ltac:(pose proof (p_d_range cx); change (2 ^ 64) with 18446744073709551616; lia))|].
  split; [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_SHB 32 SHADOW_OFF HR0 U9 ltac:(cbn; tauto) E32
                   ltac:(unfold SHADOW_OFF; change (2 ^ 64) with 18446744073709551616; lia))|].
  split; [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_SH 34 (pSH cx fp) HR0 U9 ltac:(cbn; tauto) E34
                   ltac:(rewrite HSH; change (2 ^ 64) with 18446744073709551616; lia))|].
  split; [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_F 33 (pF cx fp) HR0 U9 ltac:(cbn; tauto) E33 BpF)|].
  split; [exact (k2_slot E W3 ms cx _ _ _ _ _ PS_FK 33 (pF cx fp) HR0 U9 ltac:(cbn; tauto) E33 BpF)|].
  split.
  - unfold pslot. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms) (c_sp1 cx + PS_TSP) (pF cx fp + PO_TS));
      [|unfold PO_TS; change (2 ^ 64) with 18446744073709551616; lia].
    exact (field_of_region E _ 9%nat (c_sp1 cx) _ 16 152 16 152 88 8%N (SOff 33 96) (pF cx fp + 96) HR0 U9
             ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite U33; reflexivity)
             ltac:(change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616; lia) ltac:(cbn; lia)).
  - exact (k2_slot E W3 ms cx _ _ _ _ _ PS_CAP 35 (p_cap cx) HR0 U9 ltac:(cbn; tauto) E35
             ltac:(change (2 ^ 64) with 18446744073709551616; lia)). }
(* the globals, ps's two fields the open set, and the stream, kept by the run *)
assert (F6 : p_glob cx W3 ms b).
{ apply (p_glob_keepw cx W3 W3 ms3 ms RW b Hglob RUNK);
    intros j Hj; unfold RW; rewrite HSH; intros [X|[X|X]]; lia. }
assert (F7 : p_psopen cx fp W3 ms h).
{ destruct Hps as (P1 & P2). unfold p_psopen, pval, pPS, PO_PS in *. split.
  - apply (val_mem_keepw W3 W3 _ _ RW _ _ _ P1 RUNK); cbn [Z.of_nat];
      [lia | change (2 ^ 64) with 18446744073709551616; lia |].
    intros j Hj. unfold RW. intros [X|[X|X]]; first [lia | apply (Hsf 12); lia].
  - apply (val_mem_keepw W3 W3 _ _ RW _ _ _ P2 RUNK); cbn [Z.of_nat];
      [lia | change (2 ^ 64) with 18446744073709551616; lia |].
    intros j Hj. unfold RW. intros [X|[X|X]]; first [lia | apply (Hsf 12); lia]. }
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ PE_CID fp HAR3 Hhin Hfin) as Dhf.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ PE_CID fp HAR3 Hbin Hfin) as Dbf.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ PE_CID fp HAR3 Hfbin Hfin) as Duf.
unfold zdisjoint in Dhf, Dbf, Duf. cbn [fst snd] in Dhf, Dbf, Duf. rewrite EFA in Dhf, Dbf, Duf.
change (fs_frame_bytes PE_CID) with 128 in Dhf, Dbf, Duf. change (req_size SRC_FILE_BLOCK) with 1304 in Dhf.
rewrite ERS in Duf.
assert (F8 : asource_at SEGS KS (rd W3 ms) h b (p_C cx) 24).
{ apply (asource_at_keepw B KS ASIL W3 W3 _ _ RW _ _ _ _ Hsrc RUNK); rewrite ?p_lens;
    [ intros j Hj; unfold RW; unfold SRC_FILE_BLOCK in Hj; intros [X|[X|X]]; [lia | lia |];
      apply (Wapp h 1304 (h + j) Hhapp); [lia | lia]
    | intros j Hj; unfold RW; intros [X|[X|X]]; [lia | lia |];
      apply (Wapp b (req_size (p_nF cx)) (b + j) Hbapp); [lia | lia]
    | intros a Ha; pose proof (Himg a (proj1 (asil_env _ _ _ _ ASIL a Ha))); unfold RW; rewrite HSH; lia
    | lia | unfold SRC_FILE_BLOCK; lia | lia | lia ]. }
assert (F9 : val_mem SEGS (rd W3 ms) (pF cx fp + 96) 8 (2 ^ 64 - 1)).
{ exact (field_of_region E _ 33%nat (pF cx fp) _ 96 104 96 104 96 8%N (SLit 18446744073709551615) (2 ^ 64 - 1) HR1 U33
           ltac:(cbn; tauto) ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616; lia)
           ltac:(cbn; lia)). }
(* the values ps's other fields hold (GI_K3 does not state them), and the record buffer's bytes *)
assert (Ppres : forall a, pF cx fp <= a < pF cx fp + 128 -> YO0d.present (rd W3 ms) a).
{ intros a Ha. apply k3_present. eapply apresent_grows; [exact HG0 | exact (proj1 (HFpres a Ha))]. }
assert (Pps : forall j, 12 <= j < 24 -> YO0d.present (rd W3 ms) (pPS cx fp + j))
  by (intros j Hj; apply Ppres; unfold pPS, PO_PS; lia).
destruct (k3_vm4 (rd W3 ms) (pPS cx fp + 12) (Pps 12 ltac:(lia))
  ltac:(replace (pPS cx fp + 12 + 1) with (pPS cx fp + 13) by lia; exact (Pps 13 ltac:(lia)))
  ltac:(replace (pPS cx fp + 12 + 2) with (pPS cx fp + 14) by lia; exact (Pps 14 ltac:(lia)))
  ltac:(replace (pPS cx fp + 12 + 3) with (pPS cx fp + 15) by lia; exact (Pps 15 ltac:(lia))))
  as (lol & Hlol & Vlol).
destruct (k3_vm4 (rd W3 ms) (pPS cx fp + 16) (Pps 16 ltac:(lia))
  ltac:(replace (pPS cx fp + 16 + 1) with (pPS cx fp + 17) by lia; exact (Pps 17 ltac:(lia)))
  ltac:(replace (pPS cx fp + 16 + 2) with (pPS cx fp + 18) by lia; exact (Pps 18 ltac:(lia)))
  ltac:(replace (pPS cx fp + 16 + 3) with (pPS cx fp + 19) by lia; exact (Pps 19 ltac:(lia))))
  as (lvt & Hlvt & Vlvt).
destruct (val_mem2 SEGS (rd W3 ms) (pPS cx fp + 20) (Pps 20 ltac:(lia))
  ltac:(replace (pPS cx fp + 20 + 1) with (pPS cx fp + 21) by lia; exact (Pps 21 ltac:(lia))))
  as (lvid & Hlvid & Vlvid).
destruct (garr8_of_present SEGS (rd W3 ms) (pPS cx fp + 22) 2
  ltac:(intros a Ha; apply Ppres; unfold pPS, PO_PS in *; cbn [Z.of_nat] in Ha; lia)) as (pad & Hpadl & Hpad).
destruct (garr8_of_present SEGS (rd W3 ms) buf (Z.to_nat (p_bn cx))
  ltac:(intros a Ha; rewrite Z2Nat.id in Ha by lia; apply k3_present; eapply apresent_grows;
        [exact HG0 | exact (proj1 (Hupres a Ha))])) as (bj & Hbjl & Hbj).
(* the harness's journal at the call, opened *)
pose proof HJ as (HSTK1 & _ & (memS1 & HJi1 & Hag1) & _). rewrite !Z.add_0_r in HJi1.
(* the call state's registers *)
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in Q2.
rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in Q8.
rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in Q9.
rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q10, Q20.
rewrite E10 in Q11, Q19. rewrite E35 in Q12. rewrite U33 in Q13.
rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in Q24.
rewrite pa_sigma_pcap_source_next.
(* ---- pcap_source_next (jal 0x80b00): ps = &ps, buf, cap, ts = &ts, from position 24 ---- *)
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
assert (Usp : spZ (ms_regs ms) = c_sp1 cx)
  by (unfold spZ; rewrite Q2; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
assert (Hps8 : pPS cx fp mod 8 = 0) by (unfold pPS, PO_PS; exact (mod64_mod8 _ Hfa64)).
assert (Hts8 : (pF cx fp + 96) mod 8 = 0).
{ apply Z.mod_divide in Hfa64; [|lia]. destruct Hfa64 as [q Hq]. apply Z.mod_divide; [lia|]. exists (8 * q + 12). lia. }
assert (Hf8 : pF cx fp mod 8 = 0).
{ apply Z.mod_divide in Hfa64; [|lia]. destruct Hfa64 as [q Hq]. apply Z.mod_divide; [lia|]. exists (8 * q). lia. }
assert (HL3 : List.NoDup [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)])
  by exact (List.NoDup_app_remove_l _ _ (Permutation_NoDup Hperm (k3_ablocks_nodup _ _ _ _ _ HAR3))).
assert (Hne_uh : (buf, p_bn cx) <> (h, SRC_FILE_BLOCK)).
{ intros Heq. inversion HL3 as [|x l _ HL2]. inversion HL2 as [|y l2 Hy _]. apply Hy. rewrite Heq. left. reflexivity. }
assert (Hne_ub : (buf, p_bn cx) <> (b, p_nF cx)).
{ intros Heq. inversion HL3 as [|x l Hx _]. apply Hx. rewrite Heq. right. left. reflexivity. }
assert (Dfh : buf + p_bn cx <= h \/ h + 1304 <= buf).
{ pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hfbin Hhin Hne_uh) as D. unfold zdisjoint in D.
  cbn [fst snd] in D. rewrite ERS in D. change (req_size SRC_FILE_BLOCK) with 1304 in D. exact D. }
assert (Dfb : buf + p_bn cx <= b \/ b + req_size (p_nF cx) <= buf).
{ pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hfbin Hbin Hne_ub) as D. unfold zdisjoint in D.
  cbn [fst snd] in D. rewrite ERS in D. exact D. }
assert (Hfbout : ~ In (buf, p_bn cx) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (k3_notin_prefix _ _ _ _ (k3_ablocks_nodup _ _ _ _ _ HAR3) Hperm _); right; right; left; reflexivity).
assert (Hhout : ~ In (h, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (k3_notin_prefix _ _ _ _ (k3_ablocks_nodup _ _ _ _ _ HAR3) Hperm _); right; left; reflexivity).
assert (H24 : 24 <= p_nF cx).
{ pose proof Hgood as Hg. unfold p_good, PST.pcap_good in Hg. apply andb_true_iff in Hg as [Hg _].
  apply Z.leb_le in Hg. exact Hg. }
assert (EBN : AN.nx_bufn (p_cap cx) = p_bn cx) by reflexivity.
assert (Hsh4 : forall i, (4 <= i <= 6)%nat -> aview SEGS (w_H W3) (ms_mem ms) (pSH cx fp + Z.of_nat i) = Some 0).
{ intros i Hi. rewrite (F3 i ltac:(cbn; lia)).
  assert (Hc : (i = 4 \/ i = 5 \/ i = 6)%nat) by lia. destruct Hc as [-> | [-> | ->]]; reflexivity. }
clear HS SHOK HR0 HR1 HR2 HF HFr RUN.
eapply SRr_bind.
{ eapply (next_call SK B MT KS NSTK HNEXT LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms)
    (pPS cx fp) buf (p_cap cx) (pF cx fp + PO_TS) h b 24 (p_swz cx) lol lvt lvid PE_TS_NONE (c_M cx) PE_CID fp
    (p_C cx) bj pad (pch cx) HJ).
  - exact (k3_aro cx memS1 _ ly3 S3 W3 (ms_mem ms) _ k HB HJi1 Hag1).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small; [lia | change (2 ^ 64) with 18446744073709551616; lia].
  - rewrite Q3, Rgp. exact Hgp0.
  - rewrite Q4, Rtp. exact Htp0.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - rewrite Q13. reflexivity.
  - rewrite Usp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq].
    exists (2 * q). lia.
  - rewrite Usp. unfold LLVMF_STK. lia.
  - rewrite Usp. lia.
  - rewrite Usp. unfold s0Z at 1. rewrite Q8. unfold w64. rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
    destruct F1 as (S8 & Sj).
    pose proof (Sj 0 ltac:(lia)) as S16. replace (spZ (PcapEntryDefs.c_regs cx) - 16 - 8 * 0)
      with (spZ (PcapEntryDefs.c_regs cx) - 16) in S16 by lia.
    exact (k3_achain cx memS1 _ ly3 S3 W3 (ms_mem ms) _ k HB HJi1 Hag1 S8 S16).
  - rewrite Hfrs. vm_compute. reflexivity.
  - unfold AN.PS_F_OFF. rewrite Z.add_0_r. exact (proj1 F7).
  - change (2 ^ 64) with 18446744073709551616. lia.
  - exact Hps8.
  - unfold pPS, PO_PS. lia.
  - unfold AN.PS_LEN, pPS, PO_PS. change (2 ^ 47) with 140737488355328. lia.
  - unfold amem_range, AN.PS_LEN, pPS, PO_PS. destruct HFlo; [left | right]; lia.
  - left. reflexivity.
  - rewrite EFA. unfold pPS, PO_PS. lia.
  - rewrite EFA. change (fs_frame_bytes PE_CID) with 128. unfold AN.PS_LEN, pPS, PO_PS. lia.
  - apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. unfold AN.PS_LEN in Hi. change (24 / 8) with 3 in Hi.
    unfold pPS, PO_PS. rewrite shadow_of_addr_aligned_off by exact Hf8. change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]];
    [ replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia)
    | replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia)
    | replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia) ];
    apply Hsh4; lia.
  - intros _. unfold AN.nx_ps_at, AN.PS_F_OFF, AN.PS_SW_OFF, AN.PS_OL_OFF, AN.PS_VT_OFF, AN.PS_VID_OFF.
    rewrite Z.add_0_r. split; [exact (proj1 F7)|]. split; [exact (proj2 F7)|]. split; [exact Vlol|].
    split; [exact Vlvt|]. split; [exact Vlvid|]. split; [exact Hpad | exact Hpadl].
  - intros _. exact (p_swz_01 cx).
  - intros _. change (2 ^ 32) with 4294967296 in *. change (2 ^ 16) with 65536 in *. lia.
  - intros _ a Ha. unfold AN.PS_LEN, pPS, PO_PS in Ha. split.
    + right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes PE_CID) with 128. lia.
    + rewrite Usp. lia.
  - intros _. rewrite EBN. split; [exact Hfbin|]. split; [lia|].
    split; [change (2 ^ 63) with 9223372036854775808; lia|]. split; [exact Hbj|].
    split; [rewrite Hbjl, Z2Nat.id by lia; reflexivity|]. split; [unfold AN.NX_CAP_MAX; lia|].
    split; [|unfold AN.PS_LEN, pPS, PO_PS; lia].
    intros a Ha. split.
    + right; right; left. exists buf, (p_bn cx). split; [exact Hfbin|]. split; [exact Hfbout | rewrite ERS; lia].
    + rewrite Usp. lia.
  - intros _ _. unfold PO_TS. split; [unfold PE_TS_NONE; exact F9|].
    split; [exact Hts8|]. split; [lia|]. split; [change (2 ^ 47) with 140737488355328; lia|].
    split; [unfold amem_range; destruct HFlo; [left | right]; lia|].
    split; [exists PE_CID, fp; split; [left; reflexivity|]; rewrite EFA; change (fs_frame_bytes PE_CID) with 128; lia|].
    split.
    { intros a Ha. split.
      - right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes PE_CID) with 128. lia.
      - rewrite Usp. lia. }
    split.
    { apply zero_shadow_range; [exact Hts8 | reflexivity |].
      intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia.
      rewrite shadow_of_addr_aligned_off by exact Hf8. change (96 / 8) with 12.
      replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 12 + 0) with (pSH cx fp + Z.of_nat 12) by (unfold pSH; lia).
      rewrite (F3 12%nat ltac:(cbn; lia)). reflexivity. }
    split; [unfold AN.PS_LEN, pPS, PO_PS; lia | lia].
  - intros _. rewrite p_lens. split; [exact Hhin|]. split; [exact Hbin|]. split; [exact F8|].
    split; [lia|]. split; [lia|]. rewrite EBN. change SRC_FILE_BLOCK with 1304.
    split; [lia|]. split; [lia|]. split; [unfold AN.PS_LEN, pPS, PO_PS; lia|].
    split; [unfold AN.PS_LEN, pPS, PO_PS; lia|]. split; [intros _; unfold PO_TS; split; lia|].
    intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
    right. exists h, SRC_FILE_BLOCK. split; [exact Hhin|]. split; [exact Hhout|].
    change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. lia.
  - intros _. exact (k3_meta cx memS1 _ ly3 S3 W3 (ms_mem ms) _ k HB HJi1 Hag1). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl2 & Hfr2 & Hmle & Hfd2 & Hfs2 & Hfin2).
destruct Hfin2 as [(Hh00 & _) | (_ & Ha0 & HK & Hsrc2 & Hps2 & Hbj2 & Hts2)]; [lia|].
(* ---- PP_KD 0x80b04: the reader's first answer ---- *)
clear HJ HJi HJi1 Hout.
rewrite Q1.
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
  by exact HP2.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGD & _).
(* what the call kept: the body's footprint (k3_foot) is outside its window, its write set and its frame *)
assert (FK : forall a, 0 <= a < 2 ^ 64 -> k3_foot cx fp a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ destruct HK as (K1 & K2 & K3 & K4 & _ & _). rewrite Usp in K1.
  intros a Ha Hf. unfold k3_foot in Hf.
  assert (HnE : forall x, x < alloc_ceiling -> ~ (pF cx fp + 32 <= x < pF cx fp + 56) ->
    ~ (pF cx fp + 96 <= x < pF cx fp + 104) -> ~ (buf <= x < buf + p_bn cx) -> ~ (h <= x < h + 1304) ->
    ~ AN.nx_wrset (pPS cx fp) buf (p_cap cx) (pF cx fp + PO_TS) h x).
  { intros x Hx N1 N2 N3 N4 Hw. unfold AN.nx_wrset, AN.PS_LEN, pPS, PO_PS, PO_TS in Hw. rewrite EBN in Hw.
    destruct Hw as [Hw | [Hw | [[_ Hw] | [_ Hw]]]]; unfold SRC_FILE_BLOCK in Hw; lia. }
  assert (HnEhi : forall x, alloc_ceiling <= x -> ~ AN.nx_wrset (pPS cx fp) buf (p_cap cx) (pF cx fp + PO_TS) h x).
  { intros x Hx Hw. unfold AN.nx_wrset, AN.PS_LEN, pPS, PO_PS, PO_TS in Hw. rewrite EBN in Hw.
    destruct Hw as [Hw | [Hw | [[_ Hw] | [_ Hw]]]]; unfold SRC_FILE_BLOCK in Hw; lia. }
  destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]]].
  - apply K1; [lia | lia | apply HnEhi; lia].
  - apply K1; [lia | lia | apply HnEhi; lia].
  - apply (K4 PE_CID fp a Hfin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes PE_CID) with 128. lia.
    + apply HnE; lia.
  - apply (K4 PE_CID fp a Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes PE_CID / 8) with 16.
      unfold shadow_addr. unfold pSH, shadow_of_addr in Hf. lia.
    + apply HnE; [rewrite HSH in Hf; lia | | | |].
      * intros X. apply (Hsf (a - pSH cx fp)); lia.
      * intros X. apply (Hsf (a - pSH cx fp)); lia.
      * intros X. apply (Wapp buf (p_bn cx) a Huapp X). lia.
      * intros X. apply (Wapp h 1304 a Hhapp X). lia.
  - assert (Hcn : 0 < c_n cx) by lia.
    assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct (Z.eq_dec (c_n cx) 0) as [E0|_]; [lia|].
      pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin1]] & _); [lia|].
      apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin1. }
    assert (Hin1 : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))).
    { pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin1]] & _); [lia | exact Hin1]. }
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hpin) as (_ & Hp0 & Hp1 & Hpapp & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrqp].
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ PE_CID fp HAR3 Hpin Hfin) as Dpf.
    unfold zdisjoint in Dpf. cbn [fst snd] in Dpf. rewrite EFA in Dpf. change (fs_frame_bytes PE_CID) with 128 in Dpf.
    assert (Hnu : (c_p cx, c_n cx) <> (buf, p_bn cx)) by (intros Heq; apply Hfbout; rewrite <- Heq; exact Hin1).
    assert (Hnh : (c_p cx, c_n cx) <> (h, SRC_FILE_BLOCK)) by (intros Heq; apply Hhout; rewrite <- Heq; exact Hin1).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hpin Hfbin Hnu) as Dpu.
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hpin Hhin Hnh) as Dph.
    unfold zdisjoint in Dpu, Dph. cbn [fst snd] in Dpu, Dph. rewrite ERS in Dpu.
    change (req_size SRC_FILE_BLOCK) with 1304 in Dph.
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin); [lia|].
    replace (c_p cx + (a - c_p cx)) with a by lia. apply HnE; lia.
  - assert (HinG : inG pe_G a) by (unfold pe_G; apply inG_cons; right; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
    destruct (HG a HinG) as [Hi Hno]. pose proof (Himg a Hi).
    apply K3; [exact Hi | exact Hno | exact (proj1 (proj2 (proj2 (HGD a HinG))))].
  - assert (HinG : inG pe_G a) by (unfold pe_G; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
    destruct (HG a HinG) as [Hi Hno]. pose proof (Himg a Hi).
    apply K3; [exact Hi | exact Hno | exact (proj1 (proj2 (proj2 (HGD a HinG))))]. }
set (R := fun a => ~ k3_foot cx fp a).
assert (KEEP : mkw W3 W2 (ms_mem ms) mem2 R) by exact (k3_mkw_of_foot W3 W2 (ms_mem ms) mem2 (k3_foot cx fp) FK).
set (msx := mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_pcap_source_next)) (ms_mem ms) (seg_rom SEGS)).
assert (Hbodyx : pe_body cx fp AF_pcap_source_next W3 msx PSH_ts).
{ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [split; [exact Q2|]; split; [exact Q8|]; split; [exact Q9|]; split; [exact (eq_trans Q3 Rgp) | exact (eq_trans Q4 Rtp)]|].
  split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [reflexivity | exact F4]. }
set (ms4 := mkst regs2 (Z_to_bv 64 (BASE + 892)) mem2 (seg_rom SEGS)).
assert (Hlo : c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
{ pose proof HB as (_ & _ & _ & _ & [[H0 _] | [Hn1 Hin1]] & _); [left; exact H0|right].
  assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin1).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hpin) as (_ & Hp0 & Hp1 & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrqp]. lia. }
assert (Hbody4 : pe_body cx fp PP_KD W2 ms4 PSH_ts).
{ apply (pe_body_keepw cx fp AF_pcap_source_next PP_KD W3 W2 msx ms4 PSH_ts R Hbodyx); try reflexivity.
  - exact (P 2 ltac:(unfold acallee_saved; lia)).
  - exact (P 8 ltac:(unfold acallee_saved; lia)).
  - exact (P 9 ltac:(unfold acallee_saved; lia)).
  - exact (P 3 ltac:(unfold acallee_saved; lia)).
  - exact (P 4 ltac:(unfold acallee_saved; lia)).
  - exact KEEP.
  - intros a Ha Hn. apply Hn. unfold k3_foot. left. exact Ha.
  - intros a Ha Hn. apply Hn. unfold k3_foot. right; right; left; left. exact Ha.
  - intros a Ha Hn. apply Hn. unfold k3_foot. unfold PE_FLAGPTR in Ha. right; right; left; right. lia.
  - intros a Ha Hn. apply Hn. unfold k3_foot. right; right; right; left. exact Ha.
  - intros a Ha Hn. apply Hn. unfold k3_foot. right; right; right; right; left. exact Ha.
  - unfold LLVMF_STK. lia.
  - change (2 ^ 47) with 140737488355328. lia.
  - exact Hf4096.
  - unfold PE_FRAME. lia.
  - exact Hlo. }
assert (WF : forall l x (m : Model), m_fds (with_vm_backing l x m) = m_fds m /\ m_fs (with_vm_backing l x m) = m_fs m)
  by (intros l x [fd [mp lz mt] io fs pr li tm]; split; reflexivity).
assert (EQq : AN.nx_q (p_swz cx =? 1) (p_C cx) (p_cap cx) 24 = p_q cx 24)
  by (unfold AN.nx_q, p_q; rewrite k3_nxF; reflexivity).
assert (Hap : slots_apartw cx R) by (intros a Ha _ Hn; apply Hn; unfold k3_foot; right; left; lia).
apply (HKD cx fp (k + AN.EV_NEXT) (acc + 0) ly2 S2 W2 ms4 md2 HB HJ2).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle).
- unfold GI_KD. exists b, h, buf.
  split.
  { split; [exact Hbody4|]. split; [unfold AN.EV_NEXT; lia|]. split; [lia|].
    split; [rewrite Hbl2; exact Hperm|].
    split; [rewrite Hfd2, (proj1 (WF _ _ _)); exact Hfds | rewrite Hfs2, (proj2 (WF _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hgood|].
  split.
  { change (getr regs2 10 = w64 (p_first cx)). rewrite Ha0. unfold AN.nx_res. rewrite EQq, k3_nxF. reflexivity. }
  split; [exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18)|].
  split; [exact (eq_trans (P 19 ltac:(unfold acallee_saved; lia)) Q19)|].
  split; [exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) Q20)|].
  split; [exact (eq_trans (P 24 ltac:(unfold acallee_saved; lia)) Q24)|].
  split; [exact (pslots_keepw cx fp W3 W2 ms ms4 R (proj1 F5) KEEP Hap ltac:(lia)
                   ltac:(change (2 ^ 64) with 18446744073709551616; lia))|].
  split; [exact (pslot_keepw_apart cx W3 W2 ms ms4 R PS_BUF buf (proj2 F5) KEEP Hap ltac:(lia)
                   ltac:(change (2 ^ 64) with 18446744073709551616; lia) ltac:(tauto))|].
  split.
  { apply (p_glob_keepw cx W3 W2 ms ms4 R b F6 KEEP).
    - intros j Hj Hn. apply Hn. unfold k3_foot. right; right; right; right; right; left. lia.
    - intros j Hj Hn. apply Hn. unfold k3_foot. right; right; right; right; right; right. lia. }
  (* p_reader at 24: the contract's post, through the model's names *)
  unfold p_reader. cbv zeta.
  split.
  { unfold AN.nx_pos in Hsrc2. rewrite EQq, k3_nxF in Hsrc2. exact Hsrc2. }
  split.
  { destruct Hps2 as (V0 & V8 & _). unfold AN.PS_F_OFF, AN.PS_SW_OFF in V0, V8. rewrite Z.add_0_r in V0.
    split; [exact V0 | exact V8]. }
  intros Hfit.
  assert (Hkf : PSN.kind (p_swz cx =? 1) (p_F cx) (p_cap cx) (p_q cx 24) = PSN.KFit) by exact Hfit.
  assert (Hnf : AN.nx_fit (p_swz cx =? 1) (p_C cx) (p_cap cx) 24 = true)
    by (unfold AN.nx_fit, AN.nx_kind; rewrite EQq, k3_nxF, Hkf; reflexivity).
  assert (Hlh : AN.nx_lh (p_swz cx =? 1) (p_C cx) (p_cap cx) 24 = Some (p_q cx 24)).
  { unfold AN.nx_lh. rewrite k3_nxF. apply k3_lh_fit; [pose proof (p_sizes cx); lia | unfold p_nF in H24; lia | exact Hkf]. }
  destruct Hps2 as (_ & _ & V12 & V16 & V20 & _).
  unfold AN.PS_OL_OFF, AN.PS_VT_OFF, AN.PS_VID_OFF in V12, V16, V20.
  split; [unfold AN.nx_orig in V12; rewrite Hlh, k3_nxF in V12; exact V12|].
  split; [unfold AN.nx_vtag in V16; rewrite Hnf, EQq, k3_nxF in V16; exact V16|].
  split; [unfold AN.nx_vid in V20; rewrite Hnf, EQq, k3_nxF in V20; exact V20|].
  split.
  { pose proof (Hts2 ltac:(unfold PO_TS; lia)) as V. unfold AN.nx_tsv in V. rewrite Hnf, EQq, k3_nxF in V. exact V. }
  destruct Hbj2 as (bj' & G' & Lbj' & Pre). specialize (Pre Hnf).
  unfold AN.nx_rec in Pre. rewrite EQq, k3_nxF in Pre.
  rewrite <- (firstn_skipn (length (map (fun x : byte => bv_unsigned x)
    (PSN.rec_bytes (p_swz cx =? 1) (p_F cx) (p_q cx 24)))) bj') in G'.
  apply garr8_app in G'. destruct G' as [G1 _]. rewrite Pre in G1. exact G1.
Qed.






(* ---- A: PP_K1 0x809b8 -> PP_K2 0x80a10 ---- *)
(* The symbolic start at PP_K1 (and at PE_MEMSET_SITE 0x80a00). The stretch up to the jal of __asan_memcpy (0x809d8)
   reads and writes no memory (mv s2,a0; beqz s6; beqz s2; addi s4,s10,0x20; beqz s6; the three argument moves), and
   neither does the one from 0x80a00 to the jal of pcap_source_open (auipc a0; addi a1,a0,0x300; mv a0,s4), so the
   state has no region; atom 32 is the shadow base the token run names (k1_Bx), sp is the realigned stack pointer. *)
Definition k1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB_E SB_E 0)] [] [].
Definition ss_k1 (pc : Z) : sstate := mkSS pc sr_atoms [] None k1_facts.
Definition k1_extra : list word := map (Z_to_bv 64) [SB_E].
Definition k1_Bx : sv := SOff 32 0.
Definition k1_bspan : Z * Z := (SB_E, SB_E + 2 ^ 44 - 1).

Lemma k1_entry : forall pc cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pregs cx ms3 ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) k1_extra)) (ss_k1 pc)
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS))) /\
  sh_ok SEGS k1_Bx [] (Eimg (Ereg (ms_regs ms3) k1_extra)) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros pc cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs Hpregs.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
set (E := Eimg (Ereg (ms_regs ms3) k1_extra)).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) k1_extra) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (Usp : bv_unsigned (ew E 2) = c_sp1 cx) by (rewrite E2, Rsp; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ss_k1. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_nil.
+ exact I.
+ split; [|split; [exact I | exact I]].
  cbn [k1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32, !unsigned_lit_small by (unfold SB_E; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SB_E; lia |
    (rewrite <- Z.land_ones by lia; idtac)].
Qed.

(* The local cut at PE_MEMCPY_SITE 0x809dc (the copy is made: __asan_memcpy returned, or an empty file skipped it
   at 0x809c8): GI_K1 with the copy's bytes, s4 = &ps (0x809c4); a0, s5 and s6 are dead from here on. *)
Definition GI_KA1 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut B cx fp PE_MEMCPY_SITE PSH_entry k 1 acc (PA_K1 MT cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ 4096 <= b /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 19 = w64 (pa_val (A_OBJ 2)) /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\ getr (ms_regs ms3) 26 = w64 (pF cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\
  p_glob cx W3 ms3 (p_src cx) /\ p_copy cx W3 ms3 b /\ asource_none SEGS KS (rd W3 ms3).

(* ---- A's image facts (discharged at instantiation from the pin) ---- *)
(* g_file (object 2, written at 0x809dc) and g_file_len (object 4) are 32 bytes apart on the pin (PcapEntry.v
   G_HARNESS_U), and both lie in .bss of a writable PT_LOAD segment: the run's store needs region_ok's writable
   window, which wview grants from the segment for a byte the memory does not hold (no PAImg law states it). *)
Hypothesis HG42 : pa_val (A_OBJ 4) + 8 <= pa_val (A_OBJ 2) \/ pa_val (A_OBJ 2) + 8 <= pa_val (A_OBJ 4).
Hypothesis HGW : forall a, inG pe_G a -> wview SEGS (fun _ => None) (Z_to_bv 64 a) <> None.
(* The harness's globals are not the stream library's stdio statics (PSourceMeta.v asrc_env_addr: musl's
   __stdio_threaded, need_locks, the open-file-list lock, the mode literals and the canary), so the store of
   g_file (0x809dc) keeps `no stream is open`. An image fact of the pin, like pe_base's own per-byte conjunct. *)
Hypothesis HGSRC : forall a, inG pe_G a -> ~ asrc_env_addr KS a.

Lemma k1_gw : forall (W : world SEGS) (m : word -> option byte) a,
  gx_ok SEGS B pe_G -> inG pe_G a -> writable_at SEGS (mrestrict (w_H W) m) a.
Proof.
intros W m a HG Ha.
destruct (HG a Ha) as [Hi _].
pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
assert (Hh : w_H W (Z_to_bv 64 a) = false)
  by (apply hidden_not_img; rewrite unsigned_lit_small by lia; exact Hi).
pose proof (HGW a Ha) as Hw.
unfold writable_at, wview, mrestrict in *. rewrite Hh.
destruct (m (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* ---- A's callee contracts and the open's image facts (Section premises, discharged by the composer) ---- *)
(* __asan_memcpy / __asan_memset at their entries (the runtime rule aintrin_realizes, Reusable/YG0d.v:318; AsanAPI's
   aa_asan_memcpy / aa_asan_memset at pc_asan_memcpy / pc_asan_memset), and pcap_source_open's contract at the
   listing's image data (path literal object 3, g_file_len object 4, g_file object 2), with its own
   statement variables FM_RA / CTX / ROI; HROI, HPATH, HCTX, HFMU are lib/A's harness-tail premises
   (lib/A/Prog/PcapHarnessTail.v:162-170) at this call site PP_K2. *)
Hypothesis HMCPY : aintrin_realizes SEGS B OCpy (pa_sigma PS___asan_memcpy).
Hypothesis HMSET : aintrin_realizes SEGS B OSet (pa_sigma PS___asan_memset).
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.
Hypothesis HOPEN : tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4))
  (pa_val (A_OBJ 2)) ROI B KS MT FM_RA CTX (BASE + AF_pcap_source_open).
Hypothesis HROI : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (pa_val (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (pa_val (A_OBJ 3)) 13.
Hypothesis HCTX : In [BASE + PP_K2; RA_LLVMF] CTX /\ In [BASE + PP_K2] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).

(* ---- A's helpers (lib/A/Prog/PcapHarnessTail.v's, at this image's frame and slots) ---- *)
Lemma k1_lay_eqs : forall n ly ly', layout_le n ly ly' ->
  ly_F ly' = ly_F ly /\ ly_top ly' = ly_top ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _). auto. Qed.

Lemma k1_rdword_ext : forall (rA rB : reader) a,
  (forall i, 0 <= i < 8 -> rB (a + i) = rA (a + i)) -> rdword rB a = rdword rA a.
Proof.
  intros rA rB a H. unfold rdword.
  assert (H0 : rB a = rA a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* The body bytes every cut of A states and no callee of A changes: the saved registers, the spill slots
   s1+16 .. s1+152, the frame's header words, the frame's shadow and the input. *)
Definition k1_foot (cx : ecx) (fp a : Z) : Prop :=
  (spZ (PcapEntryDefs.c_regs cx) - 104 <= a < spZ (PcapEntryDefs.c_regs cx)) \/ (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) \/
  (c_p cx <= a < c_p cx + c_n cx).

Lemma k1_kept : forall (cx : ecx) fp (W : world SEGS) ms (W' : world SEGS) ms' sh,
  (forall a, k1_foot cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  psaved cx W ms -> pheader cx fp W ms -> pshadow cx fp W ms sh -> length sh = PE_NSH ->
  garr8 SEGS (rd W ms) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  psaved cx W' ms' /\ pheader cx fp W' ms' /\ pshadow cx fp W' ms' sh /\
  garr8 SEGS (rd W' ms') (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  (forall off v, 16 <= off -> off + 8 <= 152 -> pslot cx W ms off v -> pslot cx W' ms' off v).
Proof.
  intros cx fp W ms W' ms' sh HK (Hs8 & Hsj) (Hh0 & Hh8 & Hh16 & Hh120) Hsh Hlen Hin.
  assert (RW : forall a, (forall i, 0 <= i < 8 -> k1_foot cx fp (a + i)) ->
    rdword (aview SEGS (w_H W') (ms_mem ms')) a = rdword (aview SEGS (w_H W) (ms_mem ms)) a)
    by (intros a Ha; apply k1_rdword_ext; intros i Hi; apply HK, Ha, Hi).
  split; [|split; [|split; [|split]]].
  - split.
    + rewrite RW; [exact Hs8|]. intros i Hi. unfold k1_foot. left. lia.
    + intros j Hj. rewrite RW; [exact (Hsj j Hj)|]. intros i Hi. unfold k1_foot. left. lia.
  - unfold pheader, PE_FLAGPTR in *.
    split; [|split; [|split]]; (rewrite RW; [assumption|]); intros i Hi; unfold k1_foot; right; right; left;
    first [left; lia | right; lia].
  - intros i Hi. rewrite HK; [exact (Hsh i Hi)|]. unfold k1_foot. right; right; right; left.
    rewrite Hlen in Hi. unfold PE_NSH in Hi. lia.
  - apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS). apply HK.
    unfold k1_foot. right; right; right; right. rewrite length_map in Ha. unfold c_n. lia.
  - intros off v Ho1 Ho2 Hv. unfold pslot in *. rewrite RW; [exact Hv|]. intros i Hi. unfold k1_foot. right; left. lia.
Qed.

(* k1_foot without the frame's shadow, which the stretch rewrites (0x809e0 .. 0x809e8). *)
Definition k1_foot_ns (cx : ecx) (fp a : Z) : Prop :=
  (spZ (PcapEntryDefs.c_regs cx) - 104 <= a < spZ (PcapEntryDefs.c_regs cx)) \/ (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/
  (c_p cx <= a < c_p cx + c_n cx).

Lemma k1_kept_ns : forall (cx : ecx) fp (W : world SEGS) ms (W' : world SEGS) ms',
  (forall a, k1_foot_ns cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  psaved cx W ms -> pheader cx fp W ms ->
  garr8 SEGS (rd W ms) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  psaved cx W' ms' /\ pheader cx fp W' ms' /\
  garr8 SEGS (rd W' ms') (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  (forall off v, 16 <= off -> off + 8 <= 152 -> pslot cx W ms off v -> pslot cx W' ms' off v).
Proof.
  intros cx fp W ms W' ms' HK (Hs8 & Hsj) (Hh0 & Hh8 & Hh16 & Hh120) Hin.
  assert (RW : forall a, (forall i, 0 <= i < 8 -> k1_foot_ns cx fp (a + i)) ->
    rdword (aview SEGS (w_H W') (ms_mem ms')) a = rdword (aview SEGS (w_H W) (ms_mem ms)) a)
    by (intros a Ha; apply k1_rdword_ext; intros i Hi; apply HK, Ha, Hi).
  split; [|split; [|split]].
  - split.
    + rewrite RW; [exact Hs8|]. intros i Hi. unfold k1_foot_ns. left. lia.
    + intros j Hj. rewrite RW; [exact (Hsj j Hj)|]. intros i Hi. unfold k1_foot_ns. left. lia.
  - unfold pheader, PE_FLAGPTR in *.
    split; [|split; [|split]]; (rewrite RW; [assumption|]); intros i Hi; unfold k1_foot_ns; right; right; left;
    first [left; lia | right; lia].
  - apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS). apply HK.
    unfold k1_foot_ns. right; right; right. rewrite length_map in Ha. unfold c_n. lia.
  - intros off v Ho1 Ho2 Hv. unfold pslot in *. rewrite RW; [exact Hv|]. intros i Hi. unfold k1_foot_ns. right; left. lia.
Qed.

(* The clauses a callee's post keeps (topen_kept clauses 1, 2 and 4), for k1_foot, when its write set E misses it. *)
Lemma k1_foot_kept : forall (cx : ecx) fp lyc Sc (W : world SEGS) (memc : word -> option byte) (W2 : world SEGS)
  (mem2 : word -> option byte) slo shi (E : Z -> Prop),
  alloc_ceiling + 32368 <= c_sp1 cx -> c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 ->
  spZ (PcapEntryDefs.c_regs cx) <= 2 ^ 47 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  shi <= c_sp1 cx + 16 ->
  In (PE_CID, fp) (frames Sc) -> frame_addr lyc PE_CID fp = pF cx fp ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B lyc Sc)) ->
  (forall a, k1_foot cx fp a -> ~ E a) ->
  forall a, k1_foot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
  intros cx fp lyc Sc W memc W2 mem2 slo shi E Hs1lo Hs1hi H47 K1 K2 K4 Hshi Hfr Efa Hinb HE a Ha.
  pose proof asan_consts as (C1 & _).
  pose proof (HE a Ha) as HnE.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply K1; [lia | lia | exact HnE].
  - apply K1; [lia | lia | exact HnE].
  - apply (K4 PE_CID fp a Hfr); [|exact HnE]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes PE_CID) with 128. lia.
  - apply (K4 PE_CID fp a Hfr); [|exact HnE]. right. unfold in_zr. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes PE_CID / 8) with 16. unfold pSH, shadow_of_addr in Ha. unfold shadow_addr. lia.
  - destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn]; [|lia].
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx) (Hinb Hn)).
    + pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
    + replace (c_p cx + (a - c_p cx)) with a by lia. exact HnE.
Qed.

(* The input block, when there is one, is one of the caller's blocks and stays a block at every cut. *)
Lemma k1_input_block : forall cx ly3 S3 L,
  pe_base SK B MT KS cx -> Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3).
Proof.
  intros cx ly3 S3 L HB HP Hn. pose proof HB as (_ & _ & _ & _ & Hinp & _).
  destruct Hinp as [[H0 _] | [_ Hin]]; [lia|].
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.

(* A byte outside pe_G reads the same in the inner journal's start memory and in c_mem; above the allocator's ceiling
   every byte is outside pe_G. *)
Lemma k1_aview_memS : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> 0 <= a < 2 ^ 64 ->
  ~ inG pe_G a -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
  intros cx memS a Hag Ha HnG. apply (aview_gagree SEGS pe_G _ _ _ a Hag).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma k1_gagree_high : forall cx memS a,
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
  intros cx memS a Hag Ha. pose proof asan_consts as (C1 & _). apply (k1_aview_memS cx memS a Hag); [lia|].
  pose proof (pa_obj_img 4 ltac:(lia)) as O4. pose proof (pa_obj_img 2 ltac:(lia)) as O2.
  unfold pcap_img_end, YImgTop.IMG_TOP in O4, O2. intros HG.
  unfold pe_G in HG. apply inG_cons in HG as [HG|HG]; [|apply inG_cons in HG as [HG|HG]; [|exact (inG_nil a HG)]];
    unfold in_zr in HG; cbn [fst snd] in HG; lia.
Qed.

(* The read-only data and the source's meta invariant at a state of the walk (lib/A's aro_now / meta_now). *)
Lemma k1_aro_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
  intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _ & _ & _ & _ & _ & _ & _ & _ & HGX & HGD & _).
  eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ|].
  intros a Hro Ho He.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_img_range a Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
  rewrite (k1_aview_memS cx memS a Hag ltac:(lia)); [exact (Hrod a Hro Ho He)|].
  intros HaG. exact (proj1 (HGD a HaG) Hro).
Qed.

Lemma k1_meta_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly3 (mrestrict (w_H W3) mem3) (c_M cx).
Proof.
  intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & _ & _ & _ &
    _ & _ & HGX & HGD & _).
  pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  split; [rewrite Eextra; exact HX|]. split; [exact Himg|].
  split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
  - eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_kept_of_aview SEGS).
    destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
    pose proof (pa_img_range x Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
    rewrite <- (k1_aview_memS cx memS x Hag ltac:(lia)).
    + apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
    + intros HxG. destruct (HGD x HxG) as (_ & Hnm & _). apply Hnm. lia.
  - split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_kept_of_aview SEGS).
    rewrite <- (k1_aview_memS cx memS a Hag ltac:(lia)).
    + apply F5.
      * apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
      * intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi. pose proof (Himg a Hi). lia.
    + intros HaG. pose proof (proj1 (HGX a HaG)) as Hi. pose proof (Himg a Hi). lia.
Qed.

(* The chain the harness hands to a callee at sp = s1 (lib/A's pch_achain). *)
Lemma k1_pch_achain : forall cx own memS ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (PcapEntryDefs.c_regs cx) - 8) = Some (raZ (PcapEntryDefs.c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (PcapEntryDefs.c_regs cx) - 16) = Some (s0Z (PcapEntryDefs.c_regs cx)) ->
  achain ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (PcapEntryDefs.c_regs cx)) (pch cx).
Proof.
  intros cx own memS ly3 S3 W3 mem3 md3 k HB HJ Hag Hs1 R8 R16.
  pose proof HB as ((_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _) & _).
  pose proof Hstk as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in Hlo, Hbot.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  destruct (k1_lay_eqs _ _ _ Hly) as (_ & Etop & _ & _).
  apply (achain_ly_top (c_ly cx)); [exact Etop|].
  assert (H8 : spZ (PcapEntryDefs.c_regs cx) mod 8 = 0).
  { pose proof (Z.div_mod (spZ (PcapEntryDefs.c_regs cx)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
    apply Z.mod_divide; [lia|]. exists (2 * (spZ (PcapEntryDefs.c_regs cx) / 16)). lia. }
  assert (Hc0 : alloc_ceiling <= spZ (PcapEntryDefs.c_regs cx)) by lia.
  assert (Ht64 : ly_top (c_ly cx) <= 2 ^ 64) by lia.
  unfold pch. destruct (Z.ltb_spec (spZ (PcapEntryDefs.c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
  - assert (HK : forall a, spZ (PcapEntryDefs.c_regs cx) <= a < 2 ^ 64 ->
      aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
      by (intros a Ha; rewrite <- (k1_gagree_high cx memS a Hag) by lia; apply F1; lia).
    assert (Ht2 : spZ (PcapEntryDefs.c_regs cx) < ly_top (c_ly cx) - 16) by lia.
    assert (Hs2 : c_sp1 cx + 16 <= spZ (PcapEntryDefs.c_regs cx)) by lia.
    exact (achain_push _ _ _ _ _ _ _ _ Hch Ht64 HK R8 R16 Hra4 Hc0 H8 Ht2 Hs2).
  - left. split; [right; left; lia | reflexivity].
Qed.

(* The open contract's view of the file (bytes as Z) is the harness's p_F. *)
Lemma k1_pC_nth : forall cx j, nth j (p_C cx) 0 = bv_unsigned (nth j (p_F cx) (Z_to_bv 8 0)).
Proof.
  intros cx j. unfold p_C.
  rewrite <- (map_nth (fun x : byte => bv_unsigned x) (p_F cx) (Z_to_bv 8 0) j).
  reflexivity.
Qed.
Lemma k1_magicZ : forall cx, pcap_magicZ (p_C cx) = PST.pcap_magic (p_F cx).
Proof. intros cx. unfold pcap_magicZ, PST.pcap_magic, PST.pcap_byte. rewrite !k1_pC_nth. reflexivity. Qed.
Lemma k1_goodZ : forall cx, pcap_goodZ (p_C cx) = p_good cx.
Proof.
  intros cx. unfold pcap_goodZ, p_good, PST.pcap_good. rewrite k1_magicZ.
  unfold p_C, p_nF. rewrite length_map. reflexivity.
Qed.
Lemma k1_swZ : forall cx, pcap_swZ (p_C cx) = p_swz cx.
Proof. intros cx. unfold pcap_swZ, p_swz, PST.pcap_sw. rewrite k1_magicZ. reflexivity. Qed.

(* mbyte equality between two addresses, from their aviews (YCbq's mbyte_of_aview at one address). *)
Lemma k1_mbyte2 : forall (H : word -> bool) (m m' : word -> option byte) a a',
  aview SEGS H m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A one-byte val_mem is an aview (lib/A's aview_of_val_mem1). *)
Lemma k1_aview1 : forall (H : word -> bool) (m : word -> option byte) a v, 0 <= v < 256 ->
  val_mem SEGS (mrestrict H m) a 1 v -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hm. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
replace (YO0f.le_byte v 1 0) with v;
  [rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; change (2 ^ 8) with 256; apply Z.mod_small; lia
  | unfold YO0f.le_byte; change (2 ^ (8 * Z.of_nat 1)) with 256;
    rewrite ?Z.shiftr_0_r; rewrite (Z.mod_small v 256) by lia; symmetry; apply Z.mod_small; lia].
Qed.

(* PSH_ps is PSH_entry outside the three bytes of `ps` (0x809e0 .. 0x809e8). *)
Lemma k1_psh_eq : forall i, (i < 16)%nat -> i <> 4%nat -> i <> 5%nat -> i <> 6%nat ->
  nth i PSH_ps 0 = nth i PSH_entry 0.
Proof.
intros i Hi H4 H5 H6. do 16 (destruct i as [|i]; [first [reflexivity | exfalso; congruence] |]). exfalso; lia.
Qed.

(* Bytes of the call's own frame past its 24-byte header (ps) miss every byte of k1_foot (lib/A's frame_off_hfoot). *)
Lemma k1_frame_off_foot : forall cx fp ly3 S3 W3 mem3 md3 L q m,
  pe_base SK B MT KS cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  alloc_ceiling + 32368 <= c_sp1 cx -> c_sp1 cx <= spZ (PcapEntryDefs.c_regs cx) - 256 ->
  pF cx fp + 24 <= q -> q + m <= pF cx fp + 120 ->
  forall a, k1_foot cx fp a -> ~ (q <= a < q + m).
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 L q m HB HAR HP Hfin Efa Hs1lo Hs1hi Hq1 Hq2 x Hx Hex.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
  unfold k1_foot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia.
  assert (Hcn : 0 < c_n cx) by lia.
  pose proof (k1_input_block cx ly3 S3 _ HB HP Hcn) as Hpin.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hpin Hfin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Efa in D. change (fs_frame_bytes PE_CID) with 128 in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.

(* The symbolic start at PE_MEMCPY_SITE 0x809dc: g_file (s3's atom 19, written 0x809dc) and the frame's shadow (s9's
   atom 25; bytes 4 .. 6 written 0x809e0 .. 0x809e8). The run writes shadow bytes, so its token band is the null
   page (k1_span), not the shadow. *)
Definition a1_regions : smem :=
  [YP09.mkRegion (Some 19%nat) 0 8 0 8 []; YP09.mkRegion (Some 25%nat) 0 16 4 7 []].
Definition a1_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 65536 6254584 0);
           (25%nat, mkAF SB_E (SB_E + 2 ^ 44) 0); (32%nat, mkAF SB_E SB_E 0)] [] [].
Definition ss_a1 : sstate := mkSS PE_MEMCPY_SITE sr_atoms a1_regions None a1_facts.
Definition k1_span : Z * Z := (0, 4095).

Lemma a1_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pregs cx ms3 ->
  getr (ms_regs ms3) 19 = w64 (pa_val (A_OBJ 2)) -> getr (ms_regs ms3) 25 = w64 (pSH cx fp) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) k1_extra)) ss_a1
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PE_MEMCPY_SITE)) (ms_mem ms3) (seg_rom SEGS))) /\
  sh_ok SEGS k1_Bx [] (Eimg (Ereg (ms_regs ms3) k1_extra)) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs Hpregs R19 R25.
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & EFA & Hf4096 & Hfceil & Hfapp).
pose proof (pb_HG cx HB) as HGX.
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof (pa_obj_img 2 ltac:(lia)) as Ho2. unfold pcap_img_end, YImgTop.IMG_TOP in Ho2.
assert (HSHv : SB_E <= pSH cx fp /\ pSH cx fp + 16 < SB_E + 2 ^ 44).
{ unfold pSH, shadow_of_addr, SHADOW_OFF, SB_E. unfold PE_FRAME in Hfceil.
  assert (Hq : 0 <= pF cx fp / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  lia. }
assert (HSHp : forall a, pSH cx fp <= a < pSH cx fp + 16 -> apresent (w_H W3) (ms_mem ms3) a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
  right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold pSH, shadow_of_addr in Ha. rewrite EFA.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold SHADOW_OFF in *. lia. }
set (E := Eimg (Ereg (ms_regs ms3) k1_extra)).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) k1_extra) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr (ms_regs ms3) 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (E19 : ew E 19 = getr (ms_regs ms3) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 19 19%bv eq_refl)).
assert (E25 : ew E 25 = getr (ms_regs ms3) 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (Usp : bv_unsigned (ew E 2) = c_sp1 cx) by (rewrite E2, Rsp; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = pa_val (A_OBJ 2)) by (rewrite E19, R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp) by (rewrite E25, R25; apply unsigned_lit_small; unfold SB_E in HSHv; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold ss_a1. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold a1_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
  * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (k1_gw W3 (ms_mem ms3) _ HGX).
    unfold pe_G, inG. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  * rewrite U25. unfold SB_E in HSHv. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HSHp. lia.
+ apply pairwise_disjoint_of_extents.
  unfold a1_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  fold E. rewrite U19, U25. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SB_E in HSHv. repeat split; lia.
+ split; [|split; [exact I | exact I]].
  cbn [a1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, U19, U25, E32, !unsigned_lit_small by (unfold SB_E; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  unfold SB_E in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia |
    (rewrite <- Z.land_ones by lia; idtac)].
Qed.

(* The local cut at PE_MEMSET_SITE 0x80a00 (__asan_memset returned): g_file = b (0x809dc), ps in scope (PSH_ps,
   0x809e0 .. 0x809e8), s6 = 24 (0x809f4); GI_K2's registers, slots and memory before the open. *)
Definition GI_KA2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut B cx fp PE_MEMSET_SITE PSH_ps k 1 acc (PA_K1 MT cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ 4096 <= b /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 22 = w64 24 /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\ getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  getr (ms_regs ms3) 26 = w64 (pF cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\
  p_glob cx W3 ms3 b /\ p_copy cx W3 ms3 b /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K1 -> PE_MEMCPY_SITE: the two tests of an empty file (0x809bc, 0x809c8), fuzz_dup's NULL test (0x809c0, refuted
   by 4096 <= b) and the copy (jal __asan_memcpy 0x809d8). *)
Lemma k1_A0 : forall POST, pe_from SK B MT KS POST GI_KA1 -> pe_from SK B MT KS POST (GI_K1 B MT KS).
Proof.
intros POST HA1 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct HI as (b & Hcut & Hn26 & Hb4096 & R10 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & SD & SSHB & SF0 & Hglob & Hsn).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
destruct (k1_entry PP_K1 cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr Hregs) as [HS SHOK].
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LLVMF_STK in Hspc, Hpres.
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096' & Hbceil & Hbapp & _).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
assert (EFA : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (_ & _ & Hfapp).
rewrite EFA in Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfapp.
pose proof (req_size_pos (p_nF cx) ltac:(pose proof (p_sizes cx); lia)) as [_ Hrq1].
rewrite (ms_eta ms3 Hrv Hsv Hfreg Hfcsr), Hpc, Hrom.
remember (Eimg (Ereg (ms_regs ms3) k1_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) k1_extra) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) k1_extra) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HEdef.
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
assert (E22 : ew E 22 = Z_to_bv 64 (p_nF cx)) by (rewrite (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), R22; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10; reflexivity).
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (bpaj_run_to_x B LAWS pe_G HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK k1_bspan; [apply awr_ok_x_nil|].
psrr_branch_tok RUN BR HS SHOK k1_bspan.
- (* |F| = 0 (0x809bc taken): 0x809c4, 0x809c8 taken, PE_MEMCPY_SITE *)
  rewrite branch_eq_U, (U_atom E 22 (p_nF cx) E22), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK k1_bspan PE_MEMCPY_SITE; [apply awr_ok_x_nil|].
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp1 cx <= a < c_sp1 cx) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin; destruct Hin)) as UN1'.
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => c_sp1 cx <= a < c_sp1 cx) HFr0
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin; destruct Hin)) as UN2'.
  assert (UN : mk W3 (ms_mem ms3) (ms_mem ms0) (c_sp1 cx) (c_sp1 cx))
    by (intros a Ha Hn; rewrite (UN2' a Ha Hn); exact (UN1' a Ha Hn)).
  clear UN1' UN2' HF HFr HG HF0 HFr0 HG0.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26.
  apply (HA1 cx fp k acc ly3 S3 W3 _ _ HB HJ Hfr Hmo).
  pmkst HS.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10 in Q18.
  rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19 in Q19.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in Q20.
  rewrite unsigned_lit_small in Q20 by (unfold PE_FRAME in Hf1; lia).
  rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23 in Q23.
  rewrite (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl), R24 in Q24.
  rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25 in Q25.
  rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26 in Q26.
  assert (HlyF : p_F cx = []) by (apply length_zero_iff_nil; unfold p_nF in Hc; lia).
  exists b.
  split.
  { split.
    { eapply (pe_body_keep cx fp PP_K1 PE_MEMCPY_SITE W3 ms3 _ PSH_entry (c_sp1 cx) (c_sp1 cx) Hbody);
      try reflexivity; try (cbn [ms_regs mkst]; first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9]);
      [ cbn [ms_mem mkst]; exact UN | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    split; [repeat rewrite (proj1 (AC.wvb_fds_fs _ _ _)); exact Hfds
           | repeat rewrite (proj2 (AC.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hb4096|].
  cbn [ms_regs ms_mem mkst].
  split; [exact Q18|]. split; [exact Q19|].
  split; [rewrite Q20; reflexivity|].
  split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25|]. split; [exact Q26|].
  split; [apply (pslot_keep cx W3 ms3 _ _ _ _ _ SD UN); unfold PS_D; lia|].
  split; [apply (pslot_keep cx W3 ms3 _ _ _ _ _ SSHB UN); unfold PS_SHB; lia|].
  split; [apply (pslot_keep cx W3 ms3 _ _ _ _ _ SF0 UN); unfold PS_F0; lia|].
  split; [exact (p_glob_keep cx W3 ms3 _ _ _ _ Hglob UN ltac:(lia))|].
  split; [unfold p_copy, p_C; rewrite HlyF; apply garr8_nil|].
  exact (asource_none_keep _ _ ASIL W3 _ _ _ _ Hsn UN ltac:(lia)).
- (* |F| <> 0 (0x809bc not taken): fuzz_dup's NULL test 0x809c0 *)
  rewrite branch_eq_U, (U_atom E 22 (p_nF cx) E22), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK k1_bspan; [apply awr_ok_x_nil|].
  psrr_branch_tok RUN BR HS SHOK k1_bspan.
  + (* b = 0: PP_abort, refuted by 4096 <= b *)
    rewrite branch_eq_U, (U_atom E 10 b E10), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0. lia.
  + rewrite branch_eq_U, (U_atom E 10 b E10), U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK k1_bspan; [apply awr_ok_x_nil|].
    (* at the jal of __asan_memcpy 0x809d8: no byte written yet *)
    assert (HFm : ms_mem ms1 = ms_mem ms3).
    { transitivity (ms_mem ms0); [|transitivity (ms_mem ms)].
      - exact (no_write_run_mem _ _ _ _ HF1 ltac:(intros r Hr; vm_compute in Hr; destruct Hr)).
      - exact (no_write_run_mem _ _ _ _ HF0 ltac:(intros r Hr; vm_compute in Hr; destruct Hr)).
      - exact (no_write_run_mem _ _ _ _ HF ltac:(intros r Hr; vm_compute in Hr; destruct Hr)). }
    pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & Hstk & _) & _).
    pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
    pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
    unfold PE_FRAME in Hf1.
    assert (Hcn : c_n cx = p_nF cx + 1 /\ p_src cx = c_p cx + 1).
    { unfold c_n, p_nF, p_F, p_src. destruct (c_pl cx) as [|d0 l0] eqn:Epl.
      - exfalso. apply Hc. unfold p_nF, p_F. rewrite Epl. reflexivity.
      - cbn [tl length]. split; [lia | reflexivity]. }
    destruct Hcn as [Hcn Hsrc1].
    assert (HnF0 : 0 < p_nF cx) by (pose proof (p_sizes cx) as (Hq & _); lia).
    assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply (k1_input_block cx ly3 S3 _ HB Hperm); lia).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hpin)
      as (_ & Hp4096 & Hpceil & Hpapp & _).
    destruct (al_shadow _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hpin) as (Hpsh & Hphull).
    destruct (al_shadow _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (Hbsh & Hbhull).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrqp].
    pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as HBimg.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HBimg.
    pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as HFimg.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg. rewrite EFA in HFimg.
    change (fs_frame_bytes PE_CID) with 128 in HFimg.
    assert (Hbnew : ~ In (b, p_nF cx) (ablocks B (c_ly cx) (c_S cx)))
      by (exact (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ b (p_nF cx) HAR Hperm)).
    assert (Hne : (c_p cx, c_n cx) <> (b, p_nF cx)) by (intros Heq; injection Heq as _ Hq; lia).
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) b (p_nF cx) HAR Hpin Hb3 Hne) as Dpb.
    unfold zdisjoint in Dpb. cbn [fst snd] in Dpb.
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) PE_CID fp HAR Hb3 Hfin) as Dbf.
    unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite EFA in Dbf.
    change (fs_frame_bytes PE_CID) with 128 in Dbf.
    assert (Ho16 : (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)) mod 16 = 0).
    { pose proof (Z.div_mod (spZ (PcapEntryDefs.c_regs cx)) 16 ltac:(lia)) as D1.
      pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as D2.
      rewrite Hal16, Z.add_0_r in D1. rewrite Hal32, Z.add_0_r in D2.
      apply Z.mod_divide; [lia|]. exists (2 * (c_sp1 cx / 32) - spZ (PcapEntryDefs.c_regs cx) / 16). lia. }
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    assert (Hsp : spZ (ms_regs ms1) = c_sp1 cx).
    { unfold spZ at 1. rewrite Q2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp. unfold w64.
      apply unsigned_lit_small; lia. }
    assert (E21 : ew E 21 = w64 (p_src cx)) by (rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R21).
    eapply SRr_bind.
    { eapply (memcpy_call SK B LAWS (SIGMA PS___asan_memcpy) HMCPY W3 (ms_regs ms1) (ms_mem ms1)
        LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
        [(PE_CID, fp)] ly3 S3 _ k b (p_src cx) (p_nF cx) (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)) _ HJ).
      - rewrite Q10, (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10. reflexivity.
      - rewrite Q11, E21. reflexivity.
      - rewrite Q12, (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl), R22. reflexivity.
      - lia.
      - lia.
      - lia.
      - rewrite Hsp. lia.
      - exact Ho16.
      - lia.
      - unfold ESTACK, LLVMF_STK. lia.
      - rewrite Q3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp. exact Hgp0.
      - rewrite Q4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp. exact Htp0.
      - reflexivity.
      - rewrite Q1. apply ret_ok_codeptr_v; [unfold PE_MEMCPY_SITE; lia | reflexivity].
      - intros a Ha. split.
        + right; right; left. exists b, (p_nF cx). split; [exact Hb3|]. split; [exact Hbnew|]. lia.
        + unfold ESTACK. lia.
      - exact (amem_range_sub_app b (req_size (p_nF cx)) b (p_nF cx) Hbapp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      - rewrite HFm. apply (block_shadow_range _ _ b (req_size (p_nF cx)) b (p_nF cx) Hbsh); lia.
      - intros _ sx Hsx. rewrite HFm. apply Hbhull. split; [lia|].
        assert (Hle : shadow_addr (b + p_nF cx - 1) / 8 * 8 <= shadow_addr (b + req_size (p_nF cx) - 1) / 8 * 8).
        { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
          unfold shadow_addr, SHADOW_OFF. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
        lia.
      - split; [lia|]. split; [lia|]. split.
        + intros a Ha. split.
          * assert (Hj : (Z.to_nat (a - c_p cx) < length (map (fun b0 : byte => bv_unsigned b0) (c_pl cx)))%nat)
              by (rewrite length_map; unfold c_n in *; lia).
            pose proof (garr8_mbyte SEGS _ _ _ _ Hinb Hj) as Hm.
            rewrite Z2Nat.id in Hm by lia.
            replace (c_p cx + (a - c_p cx)) with a in Hm by lia.
            unfold aview. rewrite HFm. rewrite Hm. discriminate.
          * rewrite Hsp. unfold ESTACK. lia.
        + split; [lia|]. split.
          * exact (amem_range_sub_app (c_p cx) (req_size (c_n cx)) (p_src cx) (p_nF cx) Hpapp
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
          * split.
            -- rewrite HFm. apply (block_shadow_range _ _ (c_p cx) (req_size (c_n cx)) (p_src cx) (p_nF cx) Hpsh); lia.
            -- intros _ sx Hsx. rewrite HFm. apply Hphull. split.
               ++ assert (Hle : shadow_addr (c_p cx) / 8 * 8 <= shadow_addr (p_src cx) / 8 * 8).
                  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
                    unfold shadow_addr, SHADOW_OFF. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
                  lia.
               ++ assert (Hle : shadow_addr (p_src cx + p_nF cx - 1) / 8 * 8 <= shadow_addr (c_p cx + req_size (c_n cx) - 1) / 8 * 8).
                  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
                    unfold shadow_addr, SHADOW_OFF. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
                  lia. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hcpy & Hout & Hpres2 & Hsame).
    rewrite Q1.
    (* the bytes of the copy *)
    assert (Hsrcarr : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms1)) (p_src cx) (p_C cx)).
    { rewrite HFm.
      pose proof (garr8_sub SEGS _ (c_p cx) (map (fun b0 : byte => bv_unsigned b0) (c_pl cx)) 1%nat
        (length (p_C cx)) Hinb) as Hs.
      replace (firstn (length (p_C cx)) (skipn 1 (map (fun b0 : byte => bv_unsigned b0) (c_pl cx))))
        with (p_C cx) in Hs
        by (unfold p_C, p_F; destruct (c_pl cx) as [|d0 l0];
            [cbn [tl map skipn firstn length]; reflexivity
            | cbn [tl map skipn]; symmetry; rewrite skipn_O; apply firstn_all]).
      replace (c_p cx + Z.of_nat 1) with (p_src cx) in Hs by (change (Z.of_nat 1) with 1; lia). exact Hs. }
    assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
    assert (Hcopy2 : garr8 SEGS (mrestrict (w_H W3) mem2) b (p_C cx)).
    { apply (garr8_copy SEGS _ _ (p_src cx) b (p_C cx) Hsrcarr). intros i Hi. rewrite ELC in Hi.
      apply (k1_mbyte2 (w_H W3) (ms_mem ms1) mem2 (p_src cx + i) (b + i)). exact (Hcpy i ltac:(lia)). }
    (* the body bytes outside the copy *)
    assert (HSHv : 2147450880 <= pSH cx fp /\ pSH cx fp + 16 < 2147450880 + 2 ^ 44).
    { unfold pSH, shadow_of_addr, SHADOW_OFF.
      assert (Hq : 0 <= pF cx fp / 8 <= 17592184995840)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
    assert (Hfoot2 : forall a, k1_foot cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. rewrite <- HFm. apply Hout.
      - destruct Ha as [Hq|[Hq|[[Hq|Hq]|Hq]]]; lia.
      - destruct Ha as [Hq|[Hq|[[Hq|Hq]|Hq]]]; try lia.
        intros Hbad. exact (fshadow_not_app (pF cx fp) 16 b (req_size (p_nF cx)) a ltac:(lia) ltac:(lia)
          Hbapp ltac:(unfold pSH, shadow_of_addr, SHADOW_OFF in Hq; lia) ltac:(lia)).
      - unfold ESTACK. destruct Ha as [Hq|[Hq|[[Hq|Hq]|Hq]]]; lia. }
    destruct (k1_kept cx fp W3 ms3 W3 (mkst regs2 (Z_to_bv 64 (BASE + PE_MEMCPY_SITE)) mem2 (seg_rom SEGS)) PSH_entry
      ltac:(cbn [ms_mem mkst]; exact Hfoot2) Hsav Hhd Hsh Hshlen Hinb) as (T1 & T2 & T3 & T4 & T5).
    assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms1) (Z_to_bv 5 r)) by exact HP2.
    apply (HA1 cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + PE_MEMCPY_SITE)) mem2 (seg_rom SEGS)) md2
      HB HJ2 Hfr Hmo).
    exists b. split.
    { split.
      { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs ms_mem].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hshlen | exact T4]]]]].
        unfold pregs. cbn [ms_regs mkst].
        split; [transitivity (getr (ms_regs ms1) 2); [exact (P 2 ltac:(unfold acallee_saved; lia))
               | rewrite Q2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rsp]|].
        split; [transitivity (getr (ms_regs ms1) 8); [exact (P 8 ltac:(unfold acallee_saved; lia))
               | rewrite Q8, (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rs0]|].
        split; [transitivity (getr (ms_regs ms1) 9); [exact (P 9 ltac:(unfold acallee_saved; lia))
               | rewrite Q9, (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rs1]|].
        split; [transitivity (getr (ms_regs ms1) 3); [exact (P 3 ltac:(unfold acallee_saved; lia))
               | rewrite Q3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rgp]|].
        transitivity (getr (ms_regs ms1) 4); [exact (P 4 ltac:(unfold acallee_saved; lia))
               | rewrite Q4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rtp]. }
      split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
      unfold same_but_materialized in Hsame.
      split; [rewrite Hsame; repeat rewrite (proj1 (AC.wvb_fds_fs _ _ _)); exact Hfds
             | rewrite Hsame; repeat rewrite (proj2 (AC.wvb_fds_fs _ _ _)); exact Hfs]. }
    split; [exact Hn26|]. split; [exact Hb4096|].
    cbn [ms_regs ms_mem mkst].
    split; [transitivity (getr (ms_regs ms1) 18); [exact (P 18 ltac:(unfold acallee_saved; lia))
           | rewrite Q18, (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R10]|].
    split; [transitivity (getr (ms_regs ms1) 19); [exact (P 19 ltac:(unfold acallee_saved; lia))
           | rewrite Q19, (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R19]|].
    split; [transitivity (getr (ms_regs ms1) 20); [exact (P 20 ltac:(unfold acallee_saved; lia))
           | rewrite Q20, (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl), R26,
             unsigned_lit_small by lia; reflexivity]|].
    split; [transitivity (getr (ms_regs ms1) 23); [exact (P 23 ltac:(unfold acallee_saved; lia))
           | rewrite Q23, (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R23]|].
    split; [transitivity (getr (ms_regs ms1) 24); [exact (P 24 ltac:(unfold acallee_saved; lia))
           | rewrite Q24, (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R24]|].
    split; [transitivity (getr (ms_regs ms1) 25); [exact (P 25 ltac:(unfold acallee_saved; lia))
           | rewrite Q25, (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R25]|].
    split; [transitivity (getr (ms_regs ms1) 26); [exact (P 26 ltac:(unfold acallee_saved; lia))
           | rewrite Q26, (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R26]|].
    split; [exact (T5 PS_D _ ltac:(unfold PS_D; lia) ltac:(unfold PS_D; lia) SD)|].
    split; [exact (T5 PS_SHB _ ltac:(unfold PS_SHB; lia) ltac:(unfold PS_SHB; lia) SSHB)|].
    split; [exact (T5 PS_F0 _ ltac:(unfold PS_F0; lia) ltac:(unfold PS_F0; lia) SF0)|].
    assert (HGout : forall a, inG pe_G a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. rewrite <- HFm. apply Hout.
      - destruct (HGX a Ha) as [Hi _]. pose proof (pa_img_range a Hi) as Hr.
        unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
      - destruct (HGX a Ha) as [Hi _]. pose proof (pa_img_range a Hi) as Hr.
        unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
      - unfold ESTACK. destruct (HGX a Ha) as [Hi _]. pose proof (pa_img_range a Hi) as Hr.
        unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia. }
    split.
    { unfold p_glob, pval in *. cbn [ms_mem mkst]. split.
      - eapply val_mem_frame; [|exact (proj1 Hglob)]. intros x Hx. apply (mbyte_kept_of_aview SEGS). apply HGout.
        unfold pe_G, inG. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd].
        change (Z.of_nat 8) with 8 in Hx. lia.
      - eapply val_mem_frame; [|exact (proj2 Hglob)]. intros x Hx. apply (mbyte_kept_of_aview SEGS). apply HGout.
        unfold pe_G, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
        change (Z.of_nat 8) with 8 in Hx. lia. }
    split; [cbn [ms_mem mkst]; exact Hcopy2|].
    cbn [ms_mem mkst].
    apply (BCLO.asource_none_frame KS (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) mem2)); [|exact Hsn].
    intros a Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm. apply Hout.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
      unfold ESTACK. lia.
Qed.

(* PE_MEMCPY_SITE -> PE_MEMSET_SITE: g_file := b (sd s2,0(s3) 0x809dc), ps in scope (sb zero,4/5/6(s9) 0x809e0 ..
   0x809e8), the arguments (0x809ec .. 0x809f8; s6 := 24) and __asan_memset(&ps, 0xa5, 24) (jal 0x809fc). *)
Lemma k1_A1 : forall POST, pe_from SK B MT KS POST GI_KA2 -> pe_from SK B MT KS POST GI_KA1.
Proof.
intros POST HA2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct HI as (b & Hcut & Hn26 & Hb4096 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & SD & SSHB & SF0 & Hglob & Hcopy & Hsn).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
destruct (a1_entry cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr Hregs R19 R25) as [HS SHOK].
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
  as (_ & _ & _ & EFA & _ & _ & Hfapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LLVMF_STK in Hspc, Hpres. unfold PE_FRAME in Hf1.
rewrite (ms_eta ms3 Hrv Hsv Hfreg Hfcsr), Hpc, Hrom.
remember (Eimg (Ereg (ms_regs ms3) k1_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) k1_extra) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) k1_extra) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HEdef.
pose proof (pa_obj_img 2 ltac:(lia)) as Ho2. unfold pcap_img_end, YImgTop.IMG_TOP in Ho2.
assert (U19 : bv_unsigned (ew E 19) = pa_val (A_OBJ 2))
  by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp).
{ rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25; apply unsigned_lit_small.
  unfold pSH, shadow_of_addr, SHADOW_OFF. unfold PE_FRAME in Hf1.
  assert (Hq : 0 <= pF cx fp / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK k1_span.
- unfold ss_a1, a1_regions. cbn [ss_mem].
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
    unfold pe_G, inG. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
  left. split; [|lia].
  right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold pSH, shadow_of_addr in Ha. rewrite EFA.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold SHADOW_OFF in *. lia.
- (* at the jal of __asan_memset 0x809fc: the run wrote g_file = b and the three shadow bytes of `ps` *)
  pose proof (pa_obj_img 4 ltac:(lia)) as Ho4. unfold pcap_img_end, YImgTop.IMG_TOP in Ho4.
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as HFimg.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg. rewrite EFA in HFimg.
  change (fs_frame_bytes PE_CID) with 128 in HFimg.
  assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3)
    as (_ & Hb4096' & Hbceil & Hbapp & _).
  pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as HBimg.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HBimg.
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
  assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
  assert (HSHv : SB_E <= pSH cx fp /\ pSH cx fp + 16 < SB_E + 2 ^ 44).
  { unfold pSH, shadow_of_addr, SHADOW_OFF, SB_E. unfold PE_FRAME in Hf1.
    assert (Hq : 0 <= pF cx fp / 8 <= 17592184995840)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
  unfold SB_E in HSHv.
  assert (HSH8 : pSH cx fp mod 8 = 0).
  { unfold pSH, shadow_of_addr, SHADOW_OFF.
    replace (pF cx fp / 8) with (8 * (pF cx fp / 64)) by (Z.div_mod_to_equations; lia).
    apply Z.mod_divide; [lia|]. exists (268431360 + pF cx fp / 64). lia. }
  (* the regions of the run's state *)
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
    cbn [ms_mem restrict mkst] in HR0, HR1 end.
  pose proof (field_of_region E _ 19%nat (pa_val (A_OBJ 2)) _ _ _ _ _ 0 8%N (SOff 18 0) b HR0 U19
    ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18; unfold w64;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vg.
  rewrite Z.add_0_r in Vg. change (N.to_nat 8) with 8%nat in Vg.
  assert (Vsh : forall j, (4 <= j < 7)%nat -> aview SEGS (w_H W3) (ms_mem ms) (pSH cx fp + Z.of_nat j) = Some 0).
  { intros j Hj.
    assert (Hj3 : j = 4%nat \/ j = 5%nat \/ j = 6%nat) by lia.
    destruct Hj3 as [-> | [-> | ->]];
    [ pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 25%nat (pSH cx fp)
        _ 0 16 4 7 4 1%N (SLit 0) HR1 U25 ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vs
    | pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 25%nat (pSH cx fp)
        _ 0 16 4 7 5 1%N (SLit 0) HR1 U25 ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vs
    | pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 25%nat (pSH cx fp)
        _ 0 16 4 7 6 1%N (SLit 0) HR1 U25 ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vs ];
    (cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vs;
     match type of Vs with val_mem _ _ _ _ ?v => replace v with 0 in Vs by (vm_compute; reflexivity) end;
     cbn [Z.of_nat]; apply (k1_aview1 (w_H W3) (ms_mem ms) _ 0 ltac:(lia)); exact Vs). }
  (* every other byte is kept *)
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
    (fun a => (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) \/ (pSH cx fp + 4 <= a < pSH cx fp + 7)) HFr
    ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin; cbn [In] in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U19, ?U25 in Hrr;
                   first [left; lia | right; lia] |]); destruct Hin)) as UN0.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8) ->
    ~ (pSH cx fp + 4 <= a < pSH cx fp + 7) ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha H1 H2; apply UN0; [exact Ha | intros [X|X]; [exact (H1 X) | exact (H2 X)]]).
  clear UN0 HF HFr HG.
  (* the body bytes outside the frame's shadow are kept *)
  assert (Hpin : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (k1_input_block cx ly3 S3 _ HB Hperm Hn)).
  assert (Hpoff : 0 < c_n cx -> c_p cx + req_size (c_n cx) <= 65536 \/ (symaddr ImgPages.AsanUbsan.top) <= c_p cx).
  { intros Hn. pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR (Hpin Hn)) as Hq.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hq. exact Hq. }
  assert (Hpapp : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
  { intros Hn. destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR (Hpin Hn))
      as (_ & _ & _ & Hq & _). exact Hq. }
  assert (Hin64 : forall a, c_p cx <= a < c_p cx + c_n cx -> 0 <= a < alloc_ceiling)
    by (intros a Ha; destruct Hinp as [Hn0|(Hp0 & Hp1)]; [unfold c_n in *; lia | lia]).
  assert (Hf64a : forall a, k1_foot_ns cx fp a -> 0 <= a < 2 ^ 64).
  { intros a Ha. destruct Ha as [Hq|[Hq|[[Hq|Hq]|Hq]]]; first [lia | (pose proof (Hin64 a Hq); lia)]. }
  assert (HnotG : forall a, k1_foot_ns cx fp a -> ~ (pa_val (A_OBJ 2) <= a < pa_val (A_OBJ 2) + 8)).
  { intros a Ha. destruct Ha as [Hq|[Hq|[[Hq|Hq]|Hq]]]; try lia.
    assert (Hn : 0 < c_n cx) by lia. pose proof (Hpoff Hn). pose proof (req_size_pos (c_n cx) ltac:(lia)). lia. }
  assert (HnotS : forall a, k1_foot_ns cx fp a -> ~ (pSH cx fp + 4 <= a < pSH cx fp + 7)).
  { intros a Ha Hbad. unfold pSH, shadow_of_addr, SHADOW_OFF in Hbad.
    destruct Ha as [Hq|[Hq|[[Hq|Hq]|Hq]]].
    - unfold pSH, shadow_of_addr, SHADOW_OFF in HSHv. lia.
    - unfold pSH, shadow_of_addr, SHADOW_OFF in HSHv. lia.
    - exact (fshadow_not_app (pF cx fp) 16 (pF cx fp) 128 a ltac:(lia) ltac:(lia) Hfapp ltac:(lia) ltac:(lia)).
    - exact (fshadow_not_app (pF cx fp) 16 (pF cx fp) 128 a ltac:(lia) ltac:(lia) Hfapp ltac:(lia) ltac:(lia)).
    - assert (Hn : 0 < c_n cx) by lia. pose proof (req_size_pos (c_n cx) ltac:(lia)).
      exact (fshadow_not_app (pF cx fp) 16 (c_p cx) (req_size (c_n cx)) a ltac:(lia) ltac:(lia)
               (Hpapp Hn) ltac:(lia) ltac:(lia)). }
  assert (HKns : forall a, k1_foot_ns cx fp a -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; exact (UN a (Hf64a a Ha) (HnotG a Ha) (HnotS a Ha))).
  destruct (k1_kept_ns cx fp W3 ms3 W3 ms HKns Hsav Hhd Hinb) as (T1 & T2 & T3 & T4).
  assert (Hshps : pshadow cx fp W3 ms PSH_ps).
  { intros i Hi. vm_compute (length PSH_ps) in Hi.
    destruct (Nat.eq_dec i 4%nat) as [->|N4]; [rewrite (Vsh 4%nat ltac:(lia)); reflexivity|].
    destruct (Nat.eq_dec i 5%nat) as [->|N5]; [rewrite (Vsh 5%nat ltac:(lia)); reflexivity|].
    destruct (Nat.eq_dec i 6%nat) as [->|N6]; [rewrite (Vsh 6%nat ltac:(lia)); reflexivity|].
    rewrite (k1_psh_eq i Hi N4 N5 N6). rewrite UN; [exact (Hsh i ltac:(rewrite Hshlen; unfold PE_NSH; lia)) | | |].
    - unfold pSH, shadow_of_addr, SHADOW_OFF in *; lia.
    - unfold pSH, shadow_of_addr, SHADOW_OFF in *; lia.
    - lia. }
  (* the memset call *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & Hstk & _) & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
  assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
  assert (Ho16 : (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)) mod 16 = 0).
  { pose proof (Z.div_mod (spZ (PcapEntryDefs.c_regs cx)) 16 ltac:(lia)) as D1.
    pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as D2.
    rewrite Hal16, Z.add_0_r in D1. rewrite Hal32, Z.add_0_r in D2.
    apply Z.mod_divide; [lia|]. exists (2 * (c_sp1 cx / 32) - spZ (PcapEntryDefs.c_regs cx) / 16). lia. }
  assert (Hsp : spZ (ms_regs ms) = c_sp1 cx).
  { unfold spZ at 1. rewrite Q2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp. unfold w64.
    apply unsigned_lit_small; lia. }
  eapply SRr_bind.
  { eapply (memset_call SK B LAWS (SIGMA PS___asan_memset) HMSET W3 (ms_regs ms) (ms_mem ms)
      LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 _ k (pPS cx fp) 165 24 (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)) _ HJ).
    - rewrite Q10, (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20. reflexivity.
    - rewrite Q11. reflexivity.
    - rewrite Q12. reflexivity.
    - lia.
    - unfold pPS, PO_PS. lia.
    - unfold pPS, PO_PS in *. lia.
    - rewrite Hsp. lia.
    - exact Ho16.
    - lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - rewrite Q3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp. exact Hgp0.
    - rewrite Q4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp. exact Htp0.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [unfold PE_MEMSET_SITE; lia | reflexivity].
    - intros a Ha. split.
      + right; right; right. exists PE_CID, fp. split; [left; reflexivity|].
        left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes PE_CID) with 128.
        unfold pPS, PO_PS in Ha. lia.
      + unfold ESTACK. unfold pPS, PO_PS, PE_FRAME in *. lia.
    - exact (amem_range_sub_app (pF cx fp) 128 (pPS cx fp) 24 Hfapp ltac:(unfold PE_FRAME in Hf1; lia)
        ltac:(unfold pPS, PO_PS; lia) ltac:(unfold pPS, PO_PS; lia) ltac:(lia)).
    - apply zero_shadow_range; [rewrite Hps; apply Z.mod_divide; [lia|];
        pose proof Hf64 as H64; apply Z.mod_divide in H64; [|lia]; destruct H64 as [q Hq]; exists (8 * q + 4); lia
      | reflexivity |].
      intros i Hi. change (24 / 8) with 3 in Hi.
      rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|];
        pose proof Hf64 as H64; apply Z.mod_divide in H64; [|lia]; destruct H64 as [q Hq]; exists (8 * q); lia).
      change (32 / 8) with 4.
      assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
      destruct Hi3 as [-> | [-> | ->]].
      + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
        exact (Vsh 4%nat ltac:(lia)).
      + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
        exact (Vsh 5%nat ltac:(lia)).
      + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
        exact (Vsh 6%nat ltac:(lia)).
    - intros _ sx Hsx. unfold pPS, PO_PS, shadow_addr, SHADOW_OFF in Hsx.
      assert (HpSH : pSH cx fp = 2147450880 + pF cx fp / 8) by reflexivity.
      assert (Hd8 : pF cx fp / 8 = 8 * (pF cx fp / 64)) by (Z.div_mod_to_equations; lia).
      assert (E1 : (pF cx fp + 32) / 8 = 8 * (pF cx fp / 64) + 4) by (Z.div_mod_to_equations; lia).
      assert (E2 : (pF cx fp + 32 + 24 - 1) / 8 = 8 * (pF cx fp / 64) + 6) by (Z.div_mod_to_equations; lia).
      rewrite E1, E2 in Hsx.
      assert (E3 : (2147450880 + (8 * (pF cx fp / 64) + 4)) / 8 * 8 = 2147450880 + 8 * (pF cx fp / 64))
        by (Z.div_mod_to_equations; lia).
      assert (E4 : (2147450880 + (8 * (pF cx fp / 64) + 6)) / 8 * 8 = 2147450880 + 8 * (pF cx fp / 64))
        by (Z.div_mod_to_equations; lia).
      rewrite E3, E4 in Hsx. rewrite <- Hd8, <- HpSH in Hsx.
      assert (Hjx : exists j, (j < 16)%nat /\ sx = pSH cx fp + Z.of_nat j).
      { exists (Z.to_nat (sx - pSH cx fp)). split; [lia|]. rewrite Z2Nat.id by lia. lia. }
      destruct Hjx as (j & Hj & ->).
      destruct (Nat.eq_dec j 4%nat) as [->|N4]; [rewrite (Vsh 4%nat ltac:(lia)); discriminate|].
      destruct (Nat.eq_dec j 5%nat) as [->|N5]; [rewrite (Vsh 5%nat ltac:(lia)); discriminate|].
      destruct (Nat.eq_dec j 6%nat) as [->|N6]; [rewrite (Vsh 6%nat ltac:(lia)); discriminate|].
      rewrite UN; [ rewrite (Hsh j ltac:(rewrite Hshlen; unfold PE_NSH; lia)); discriminate
                  | unfold pSH, shadow_of_addr, SHADOW_OFF in *; lia
                  | unfold pSH, shadow_of_addr, SHADOW_OFF in *; lia | lia ].
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hset & Hout & Hpres2 & Hsame).
  rewrite Q1.
  assert (Hfoot2 : forall a, k1_foot_ns cx fp a \/ (pSH cx fp <= a < pSH cx fp + 16) ->
    aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64)
      by (destruct Ha as [Hq|Hq]; [exact (Hf64a a Hq) | lia]).
    assert (HnPS : ~ (pPS cx fp <= a < pPS cx fp + 24)).
    { unfold pPS, PO_PS. destruct Ha as [Hq|Hq].
      - destruct Hq as [Hq|[Hq|[[Hq|Hq]|Hq]]]; try lia.
        assert (Hn : 0 < c_n cx) by lia.
        pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ (c_p cx) (c_n cx) PE_CID fp HAR (Hpin Hn) Hfin) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA in D.
        change (fs_frame_bytes PE_CID) with 128 in D.
        pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
      - intros Hbad. exact (fshadow_not_app (pF cx fp) 16 (pF cx fp) 128 a ltac:(lia) ltac:(lia) Hfapp
          ltac:(unfold pSH, shadow_of_addr, SHADOW_OFF in Hq; lia) ltac:(lia)). }
    assert (HnW : ~ (spZ (PcapEntryDefs.c_regs cx) + (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)) - ESTACK <= a
                     < spZ (PcapEntryDefs.c_regs cx) + (c_sp1 cx - spZ (PcapEntryDefs.c_regs cx)))).
    { unfold ESTACK. destruct Ha as [Hq|Hq].
      - destruct Hq as [Hq|[Hq|[[Hq|Hq]|Hq]]]; first [lia | (pose proof (Hin64 a Hq); lia)].
      - lia. }
    exact (Hout a Ha64 HnPS HnW). }
  destruct (k1_kept_ns cx fp W3 ms W3 (mkst regs2 (Z_to_bv 64 (BASE + PE_MEMSET_SITE)) mem2 (seg_rom SEGS))
    ltac:(cbn [ms_mem mkst]; intros a Ha; apply Hfoot2; left; exact Ha) T1 T2 T3) as (U1 & U2 & U3 & U4).
  assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
  apply (HA2 cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + PE_MEMSET_SITE)) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfr Hmo).
  exists b. split.
  { split.
    { unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs ms_mem].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [|split; [exact U1 | split; [exact U2 | split; [|split; [exact Hshlen | exact U3]]]]].
      - unfold pregs. cbn [ms_regs mkst].
        split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia))
               | rewrite Q2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rsp]|].
        split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia))
               | rewrite Q8, (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rs0]|].
        split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia))
               | rewrite Q9, (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rs1]|].
        split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia))
               | rewrite Q3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rgp]|].
        transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia))
               | rewrite Q4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rtp].
      - intros i Hi. cbn [ms_mem mkst]. rewrite Hfoot2 by (right; vm_compute (length PSH_ps) in Hi; lia).
        exact (Hshps i Hi). }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hperm|].
    unfold same_but_materialized in Hsame.
    split; [rewrite Hsame; repeat rewrite (proj1 (AC.wvb_fds_fs _ _ _)); exact Hfds
           | rewrite Hsame; repeat rewrite (proj2 (AC.wvb_fds_fs _ _ _)); exact Hfs]. }
  split; [exact Hn26|]. split; [exact Hb4096|].
  cbn [ms_regs ms_mem mkst].
  split; [transitivity (getr (ms_regs ms) 18); [exact (P 18 ltac:(unfold acallee_saved; lia))
         | rewrite Q18, (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R18]|].
  split; [transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia))
         | rewrite Q20, (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R20]|].
  split; [transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia))
         | rewrite Q22; reflexivity]|].
  split; [transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia))
         | rewrite Q23, (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R23]|].
  split; [transitivity (getr (ms_regs ms) 24); [exact (P 24 ltac:(unfold acallee_saved; lia))
         | rewrite Q24, (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R24]|].
  split; [transitivity (getr (ms_regs ms) 25); [exact (P 25 ltac:(unfold acallee_saved; lia))
         | rewrite Q25, (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R25]|].
  split; [transitivity (getr (ms_regs ms) 26); [exact (P 26 ltac:(unfold acallee_saved; lia))
         | rewrite Q26, (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R26]|].
  split; [exact (U4 PS_D _ ltac:(unfold PS_D; lia) ltac:(unfold PS_D; lia)
                   (T4 PS_D _ ltac:(unfold PS_D; lia) ltac:(unfold PS_D; lia) SD))|].
  split; [exact (U4 PS_SHB _ ltac:(unfold PS_SHB; lia) ltac:(unfold PS_SHB; lia)
                   (T4 PS_SHB _ ltac:(unfold PS_SHB; lia) ltac:(unfold PS_SHB; lia) SSHB))|].
  split; [exact (U4 PS_F0 _ ltac:(unfold PS_F0; lia) ltac:(unfold PS_F0; lia)
                   (T4 PS_F0 _ ltac:(unfold PS_F0; lia) ltac:(unfold PS_F0; lia) SF0))|].
  assert (HGout : forall a, inG pe_G a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha. apply Hout.
    - destruct (HGX a Ha) as [Hi _]. pose proof (pa_img_range a Hi) as Hr.
      unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
    - unfold pPS, PO_PS. unfold pe_G, inG in Ha.
      apply inG_cons in Ha as [Ha|Ha]; [|apply inG_cons in Ha as [Ha|Ha]; [|exfalso; exact (inG_nil a Ha)]];
      unfold in_zr in Ha; cbn [fst snd] in Ha; lia.
    - unfold ESTACK. destruct (HGX a Ha) as [Hi _]. pose proof (pa_img_range a Hi) as Hr.
      unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia. }
  split.
  { unfold p_glob, pval. cbn [ms_mem mkst]. split.
    - eapply val_mem_frame; [|exact Vg]. intros x Hx. apply (mbyte_kept_of_aview SEGS). apply HGout.
      unfold pe_G, inG. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd].
      change (Z.of_nat 8) with 8 in Hx. lia.
    - eapply val_mem_frame; [|exact (proj2 Hglob)]. intros x Hx. apply (mbyte_kept_of_aview SEGS).
      change (Z.of_nat 8) with 8 in Hx.
      transitivity (aview SEGS (w_H W3) (ms_mem ms) x).
      + apply HGout. unfold pe_G, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      + apply UN; [lia | destruct HG42 as [HG|HG]; lia | lia]. }
  split.
  { unfold p_copy in *. cbn [ms_mem mkst]. apply (garr8_frame SEGS _ _ _ _ Hcopy). intros a Ha.
    rewrite ELC in Ha. apply (mbyte_of_aview SEGS).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b (p_nF cx) PE_CID fp HAR Hb3 Hfin) as Dbf.
    unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite EFA in Dbf.
    change (fs_frame_bytes PE_CID) with 128 in Dbf.
    transitivity (aview SEGS (w_H W3) (ms_mem ms) a).
    - apply Hout; [lia | unfold pPS, PO_PS; lia | unfold ESTACK; lia].
    - apply UN; [lia | lia |
        intros Hbad; exact (fshadow_not_app (pF cx fp) 16 b (req_size (p_nF cx)) a ltac:(lia) ltac:(lia) Hbapp
          ltac:(unfold pSH, shadow_of_addr, SHADOW_OFF in Hbad; lia) ltac:(lia))]. }
  cbn [ms_mem mkst].
  apply (BCLO.asource_none_frame KS (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) mem2)); [|].
  + intros a Ha. apply (mbyte_of_aview SEGS). apply Hout.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
      unfold pPS, PO_PS. lia.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
      unfold ESTACK. lia.
  + apply (BCLO.asource_none_frame KS (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms))); [|exact Hsn].
    intros a Ha. apply (mbyte_of_aview SEGS). apply UN.
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
    * intros Hbad. exact (HGSRC a ltac:(unfold pe_G, inG; apply Exists_cons_tl, Exists_cons_hd;
        unfold in_zr; cbn [fst snd]; lia) Ha).
    * pose proof (env_low _ _ ASIL a Ha) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
Qed.

(* PE_MEMSET_SITE -> PP_K2: a1 := the path literal (auipc a0,0xfffa0 0x80a00; addi a1,a0,0x300 0x80a04), a0 := &ps
   (0x80a08), and pcap_source_open (jal 0x80a0c). *)
Lemma k1_A2 : forall POST, pe_from SK B MT KS POST (GI_K2 B MT KS) -> pe_from SK B MT KS POST GI_KA2.
Proof.
intros POST HK2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct HI as (b & Hcut & Hn26 & Hb4096 & R18 & R20 & R22 & R23 & R24 & R25 & R26 & SD & SSHB & SF0 & Hglob & Hcopy & Hsn).
destruct Hcut as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
destruct (k1_entry PE_MEMSET_SITE cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr Hregs) as [HS SHOK].
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
destruct (pe_sp1_bounds cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
  as (Hs1ce & _ & _ & EFA & _ & _ & Hfapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & Hstk & _) & HraL & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ &
  _ & _ & _ & _ & Hmok & Hneed & _ & HGD & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
unfold LLVMF_STK in Hspc, Hpres.
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096' & Hbceil & _).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hrq1].
assert (ELC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
assert (EBB : blocks_bytes S3 = blocks_bytes (c_S cx) + p_nF cx).
{ rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  rewrite (bsum_perm _ _ Hperm), bsum_app. cbn [bsum fold_right snd]. lia. }
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0).
{ rewrite Hps. apply Z.mod_divide; [lia|]. pose proof Hf64 as H64. apply Z.mod_divide in H64; [|lia].
  destruct H64 as [q Hq]. exists (8 * q + 4). lia. }
rewrite (ms_eta ms3 Hrv Hsv Hfreg Hfcsr), Hpc, Hrom.
remember (Eimg (Ereg (ms_regs ms3) k1_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) k1_extra) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) k1_extra) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EO3 : ew E (A_OBJ 3) = Z_to_bv 64 (pa_val (A_OBJ 3)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HEdef.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK k1_bspan; [apply awr_ok_x_nil|].
assert (HFm : ms_mem ms = ms_mem ms3).
{ apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros x. apply HF. intros (r & Hr & _). cbn in Hr. destruct Hr. }
clear HF HFr HG.
destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & HSTK).
pose proof HJi as (HARi & Hly & _ & _ & _ & _ & Hnev & Hk0 & _).
destruct (k1_lay_eqs _ _ _ Hly) as (EF & Etop & Eslo & Eshi).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
change (ew E 244) with (ew E (A_OBJ 3)) in Q11.
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx).
{ unfold spZ at 1. rewrite Q2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp. unfold w64.
  apply unsigned_lit_small; lia. }
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (PcapEntryDefs.c_regs cx) - 8) = Some (raZ (PcapEntryDefs.c_regs cx)))
  by (rewrite HFm; exact (proj1 Hsav)).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (PcapEntryDefs.c_regs cx) - 16) = Some (s0Z (PcapEntryDefs.c_regs cx))).
{ rewrite HFm. pose proof (proj2 Hsav 0 ltac:(lia)) as H0.
  replace (spZ (PcapEntryDefs.c_regs cx) - 16 - 8 * 0) with (spZ (PcapEntryDefs.c_regs cx) - 16) in H0 by lia. exact H0. }
assert (Hsp0r : 0 <= spZ (PcapEntryDefs.c_regs cx) < 2 ^ 64) by lia.
rewrite pa_sigma_pcap_source_open.
eapply SRr_bind.
{ eapply (open_call SK B MT KS (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4)) (pa_val (A_OBJ 2)) ROI FM_RA CTX HOPEN
    LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pch cx) (pPS cx fp) (p_nF cx) b (c_M cx) (p_C cx)
    PE_CID fp HJ).
  - exact (k1_aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp. exact Hgp0.
  - rewrite Q4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp. exact Htp0.
  - rewrite Q10, (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20. reflexivity.
  - rewrite Q11, EO3. reflexivity.
  - rewrite Hsp. unfold s0Z at 1. rewrite Q8, (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0. unfold w64.
    rewrite unsigned_lit_small by lia.
    exact (k1_pch_achain cx _ memS ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag ltac:(lia) Hs8 Hs16).
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    unfold pch, spine. destruct (Z.ltb_spec (spZ (PcapEntryDefs.c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
    + cbn [map]. rewrite HraL. exact (proj1 HCTX).
    + cbn [map]. exact (proj2 HCTX).
  - rewrite Hsp. apply Z.mod_divide; [lia|]. pose proof Hal32 as H32. apply Z.mod_divide in H32; [|lia].
    destruct H32 as [q Hq]. exists (2 * q). lia.
  - rewrite Hsp, TPCAP_SOURCE_OPEN_STK_val. unfold LLVMF_STK. lia.
  - rewrite Hsp. lia.
  - rewrite Hsp, Etop. lia.
  - rewrite Hfr. cbn [length Z.of_nat]. lia.
  - left. reflexivity.
  - rewrite EFA, Hps. lia.
  - rewrite EFA, Hps. change (fs_frame_bytes PE_CID) with 128. lia.
  - rewrite Hps. lia.
  - exact Hps8.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. change (24 / 8) with 3 in Hi.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; pose proof Hf64 as H64;
      apply Z.mod_divide in H64; [|lia]; destruct H64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]].
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
      exact (Hsh 4%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
      exact (Hsh 5%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
      exact (Hsh 6%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
  - exists sink_token. split; [left; reflexivity|]. unfold sink_token. cbn [fst snd]. lia.
  - apply HROI. exact (k1_aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - rewrite HFm. exact (proj1 (HPATH ly3 S3 W3 (ms_mem ms3) md3 HAR)).
  - rewrite HFm. exact (proj2 (HPATH ly3 S3 W3 (ms_mem ms3) md3 HAR)).
  - rewrite HFm. exact (proj2 Hglob).
  - rewrite HFm. exact (proj1 Hglob).
  - lia.
  - rewrite HFm. exact Hsn.
  - symmetry. exact ELC.
  - lia.
  - intros _. split; [exact Hb3|]. unfold p_copy in Hcopy. split; [rewrite HFm; exact Hcopy|].
    exact (garr8_bytes_ok SEGS _ _ _ Hcopy).
  - exact (k1_meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - unfold EV_OPEN, AF.EV_FUZZ_FOPEN, EV_LIB in *. lia.
  - rewrite EBB. unfold SRC_FILE_BLOCK, LIVE_LIB in *. lia.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT SRC_FILE_BLOCK) MTL Hmok Hmo
      (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia))).
    pose proof (PA_K12_need MT MTL cx) as Hn. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (p_bn cx) ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)).
    unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1 in *. lia.
  - exact (proj1 HFMU).
  - exact (proj2 HFMU). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2 & Hfr2 & Hfd2 & Hfs2 & HK & Hmle & Hz12 & Hz16 &
  Hz20 & Harm).
rewrite Q1.
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HEps : forall a, k1_foot cx fp a -> ~ (pPS cx fp <= a < pPS cx fp + 22))
  by (exact (k1_frame_off_foot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 22 HB HAR Hperm Hfin EFA Hs1ce
       (proj2 Hs1lo) ltac:(rewrite Hps; lia) ltac:(rewrite Hps; lia))).
assert (Hfoot : forall a, k1_foot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm.
  exact (k1_foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _ (fun a => pPS cx fp <= a < pPS cx fp + 22)
    Hs1ce (proj2 Hs1lo) Hsp47 (fun a Ha1 Ha2 _ => K1 a Ha1 Ha2) K2 K4 ltac:(rewrite Hsp; lia)
    Hfin EFA (k1_input_block cx ly3 S3 _ HB Hperm) HEps a Ha). }
destruct (k1_kept cx fp W3 ms3 W2 (mkst regs2 (Z_to_bv 64 (BASE + 648)) mem2 (seg_rom SEGS)) PSH_ps Hfoot
  Hsav Hhd Hsh Hshlen Hinb) as (T1 & T2 & T3 & T4 & T5).
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
assert (HGk : forall a, inG pe_G a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- HFm. destruct (HGX a Ha) as [Hi Hno]. destruct (HGD a Ha) as (_ & _ & He & Ho).
  exact (K3 a Hi Hno He Ho). }
assert (Hbody2 : pe_body cx fp PP_K2 W2 (mkst regs2 (Z_to_bv 64 (BASE + 648)) mem2 (seg_rom SEGS)) PSH_ps).
{ unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hshlen | exact T4]]]]].
  unfold pregs. cbn [ms_regs mkst].
  split; [transitivity (getr (ms_regs ms) 2); [exact (P 2 ltac:(unfold acallee_saved; lia))
         | rewrite Q2, (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rsp]|].
  split; [transitivity (getr (ms_regs ms) 8); [exact (P 8 ltac:(unfold acallee_saved; lia))
         | rewrite Q8, (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rs0]|].
  split; [transitivity (getr (ms_regs ms) 9); [exact (P 9 ltac:(unfold acallee_saved; lia))
         | rewrite Q9, (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rs1]|].
  split; [transitivity (getr (ms_regs ms) 3); [exact (P 3 ltac:(unfold acallee_saved; lia))
         | rewrite Q3, (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rgp]|].
  transitivity (getr (ms_regs ms) 4); [exact (P 4 ltac:(unfold acallee_saved; lia))
         | rewrite Q4, (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl); exact Rtp]. }
assert (Hglob2 : p_glob cx W2 (mkst regs2 (Z_to_bv 64 (BASE + 648)) mem2 (seg_rom SEGS)) b).
{ destruct Hglob as [G1 G2]. unfold p_glob, pval in *. cbn [ms_mem mkst].
  pose proof (pa_obj_img 2 ltac:(lia)) as Ho2. pose proof (pa_obj_img 4 ltac:(lia)) as Ho4.
  split.
  - eapply val_mem_frame; [|exact G1]. intros x Hx. apply (mbyte_kept_of_aview SEGS). apply HGk.
    unfold pe_G, inG. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia.
  - eapply val_mem_frame; [|exact G2]. intros x Hx. apply (mbyte_kept_of_aview SEGS). apply HGk.
    unfold pe_G, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia. }
assert (Hcopy2 : p_copy cx W2 (mkst regs2 (Z_to_bv 64 (BASE + 648)) mem2 (seg_rom SEGS)) b).
{ unfold p_copy in *. cbn [ms_mem mkst]. apply (garr8_frame SEGS _ _ _ _ Hcopy). intros a Ha. rewrite ELC in Ha.
  apply (mbyte_of_aview SEGS). rewrite <- HFm. replace a with (b + (a - b)) by lia.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b (p_nF cx) PE_CID fp HAR Hb3 Hfin) as Dbf.
  unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite EFA in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
  apply (K2 b (p_nF cx) (a - b) Hb3); [lia|]. cbv beta. rewrite Hps. lia. }
assert (Hregs2 : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r) ->
  getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)) by auto.
clear Hregs2.
destruct Harm as [(HJ2 & Ha0 & Hgd & hh & Hh4096 & Hh16 & Hbl2 & Hpf2 & Hpsw2 & Hsrc2 & Hmle2) |
                  (HJ2 & Ha0 & Hgd & Hnull2 & H812 & Hperm2 & Hsn2)].
- (* accepted *)
  apply (HK2 cx fp (k + AF.EV_FUZZ_FOPEN) (acc + mo_malloc MT SRC_FILE_BLOCK) ly2 S2 W2
    (mkst regs2 (Z_to_bv 64 (BASE + 648)) mem2 (seg_rom SEGS)) md2 HB HJ2).
  + rewrite Hfr2. exact Hfr.
  + exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle2).
  + exists b. split; [exact Hbody2|]. split; [exact Hn26|].
    split; [rewrite Hfd2, (proj1 (AC.wvb_fds_fs _ _ _)); exact Hfds|].
    split; [rewrite Hfs2, (proj2 (AC.wvb_fds_fs _ _ _)); exact Hfs|].
    cbn [ms_regs ms_mem mkst].
    split; [transitivity (getr (ms_regs ms) 18); [exact (P 18 ltac:(unfold acallee_saved; lia))
           | rewrite Q18, (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R18]|].
    split; [transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia))
           | rewrite Q20, (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R20]|].
    split; [transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia))
           | rewrite Q22, (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R22]|].
    split; [transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia))
           | rewrite Q23, (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R23]|].
    split; [transitivity (getr (ms_regs ms) 24); [exact (P 24 ltac:(unfold acallee_saved; lia))
           | rewrite Q24, (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R24]|].
    split; [transitivity (getr (ms_regs ms) 25); [exact (P 25 ltac:(unfold acallee_saved; lia))
           | rewrite Q25, (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R25]|].
    split; [transitivity (getr (ms_regs ms) 26); [exact (P 26 ltac:(unfold acallee_saved; lia))
           | rewrite Q26, (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R26]|].
    split; [exact (T5 PS_D _ ltac:(unfold PS_D; lia) ltac:(unfold PS_D; lia) SD)|].
    split; [exact (T5 PS_SHB _ ltac:(unfold PS_SHB; lia) ltac:(unfold PS_SHB; lia) SSHB)|].
    split; [exact (T5 PS_F0 _ ltac:(unfold PS_F0; lia) ltac:(unfold PS_F0; lia) SF0)|].
    split; [exact Hglob2|]. split; [exact Hcopy2|].
    left. split; [rewrite <- k1_goodZ; exact Hgd|]. split; [exact Ha0|].
    split; [unfold AF.EV_FUZZ_FOPEN; lia|].
    split; [unfold PA_K2g; lia|].
    exists hh. split.
    * rewrite Hbl2. eapply Permutation_trans; [apply (Permutation_app_tail [(hh, SRC_FILE_BLOCK)] Hperm)|].
      rewrite <- app_assoc. cbn [app]. apply Permutation_refl.
    * split; [unfold p_psopen, pval; cbn [ms_mem mkst]; split; [exact Hpf2 | rewrite <- k1_swZ; exact Hpsw2]|].
      cbn [ms_mem mkst]. exact Hsrc2.
- (* refused *)
  apply (HK2 cx fp (k + EV_OPEN) (acc + OPEN_METER MT) ly2 S2 W2
    (mkst regs2 (Z_to_bv 64 (BASE + 648)) mem2 (seg_rom SEGS)) md2 HB HJ2).
  + rewrite Hfr2. exact Hfr.
  + exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle).
  + exists b. split; [exact Hbody2|]. split; [exact Hn26|].
    split; [rewrite Hfd2, (proj1 (AC.wvb_fds_fs _ _ _)); exact Hfds|].
    split; [rewrite Hfs2, (proj2 (AC.wvb_fds_fs _ _ _)); exact Hfs|].
    cbn [ms_regs ms_mem mkst].
    split; [transitivity (getr (ms_regs ms) 18); [exact (P 18 ltac:(unfold acallee_saved; lia))
           | rewrite Q18, (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R18]|].
    split; [transitivity (getr (ms_regs ms) 20); [exact (P 20 ltac:(unfold acallee_saved; lia))
           | rewrite Q20, (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R20]|].
    split; [transitivity (getr (ms_regs ms) 22); [exact (P 22 ltac:(unfold acallee_saved; lia))
           | rewrite Q22, (EW 22%nat 22%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R22]|].
    split; [transitivity (getr (ms_regs ms) 23); [exact (P 23 ltac:(unfold acallee_saved; lia))
           | rewrite Q23, (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R23]|].
    split; [transitivity (getr (ms_regs ms) 24); [exact (P 24 ltac:(unfold acallee_saved; lia))
           | rewrite Q24, (EW 24%nat 24%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R24]|].
    split; [transitivity (getr (ms_regs ms) 25); [exact (P 25 ltac:(unfold acallee_saved; lia))
           | rewrite Q25, (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R25]|].
    split; [transitivity (getr (ms_regs ms) 26); [exact (P 26 ltac:(unfold acallee_saved; lia))
           | rewrite Q26, (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R26]|].
    split; [exact (T5 PS_D _ ltac:(unfold PS_D; lia) ltac:(unfold PS_D; lia) SD)|].
    split; [exact (T5 PS_SHB _ ltac:(unfold PS_SHB; lia) ltac:(unfold PS_SHB; lia) SSHB)|].
    split; [exact (T5 PS_F0 _ ltac:(unfold PS_F0; lia) ltac:(unfold PS_F0; lia) SF0)|].
    split; [exact Hglob2|]. split; [exact Hcopy2|].
    right. split; [rewrite <- k1_goodZ; exact Hgd|]. split; [exact Ha0|].
    split; [unfold EV_OPEN, AF.EV_FUZZ_FOPEN; lia|].
    split; [unfold PA_K2r, OPEN_METER; lia|].
    split; [eapply Permutation_trans; [exact Hperm2 | exact Hperm]|].
    split; [unfold p_psnull, pval; cbn [ms_mem mkst]; exact Hnull2|].
    cbn [ms_mem mkst]. exact Hsn2.
Qed.

(* A: PP_K1 -> PP_K2, from the three sub-cuts (the copy, the globals and `ps`, the open). *)
Lemma pe_from_K1 : pe_from_K1_stmt.
Proof.
unfold pe_from_K1_stmt. intros POST HK2. apply k1_A0, k1_A1, k1_A2. exact HK2.
Qed.


(* The lane's whole stretch, PP_K1 to the exits PP_KD and PP_K12r: the five cuts, all proved. *)
Lemma pe_from_open : forall POST, pe_from SK B MT KS POST (GI_KD B MT KS) -> pe_from SK B MT KS POST (GI_K12r B MT KS) ->
  pe_from SK B MT KS POST (GI_K1 B MT KS).
Proof. exact (pe_from_open_compose pe_from_K1 pe_from_K2 pe_from_KM pe_from_REF pe_from_K3). Qed.

End c.
End b.
End a.
(* The sink head is EXPLICIT on every exported name that depends on it (a Theorem Labs lane, 21:57Z; see PcapEntry.v). *)
Arguments pe_from_K1_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_K2_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_KM_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_REF_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_K3_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_open_compose {fx rc} SK {PI} B MT KS.
Arguments pe_from_open {fx rc} SK {PI} B MT KS.
Arguments km_entry {fx rc} SK {PI} B MT KS LAWS.
Arguments pe_from_KMC_stmt {fx rc} SK {PI} B MT KS.
Arguments pe_from_KM_of_KMC {fx rc} SK {PI} B MT KS LAWS ASIL _.
