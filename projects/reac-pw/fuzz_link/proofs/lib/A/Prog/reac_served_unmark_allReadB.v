(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v; 249 of its 295 lines of code are new or changed and 545 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all) on image A, THE READ
   PIECE, stage 2: from reac_link_alias_read's return (+0x270, reac_served_unmark_allReadA.v um_gi_rd) to MID or JOIN.
     +0x270  bnez a0                            -> JOIN (+0x294): the read failed, name c is skipped
     +0x274..+0x280  a2 := 15, a0 := s5 (F + 32), a1 := s7 ("reac-pw:served"), jal wrapper_bcmp (0x4305c)
     the call        LinkWalkBcmp.v aj_gx_bcmp_at over abcmp_realizes (Section hypothesis HBC)
     +0x284  bnez a0                            -> JOIN: the alias is not "reac-pw:served", name c is skipped
     +0x288  MID: the alias is ours, the write branch remains (um_mid_obl)
   and closes the piece: `um_read : forall c, um_mid_obl SK B c -> um_join_obl SK B c -> um_head_obl SK B c`.

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c reac_link_alias_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkSide LinkWalkPi LinkWalkCall LinkWalkShadow LinkWalkZsh LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_unmark_allDefs reac_served_unmark_allReadK reac_served_unmark_allReadA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_um_read_b : YI16.sink_head := _.

(* +0x284: wrapper_bcmp's return; the register-only symbolic states at +0x270 and +0x284 *)
Definition UM_RET_BC : Z := AF_reac_served_unmark_all + 0x284.
Local Set Default Proof Using "All".
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* AR's laws; the start-up symbols; the segments; the relro window; the listing's values; reac_link_alias_read's
   contract (lib/A/Prog/reac_link_alias_read.v reac_link_alias_read_aproof): as
   reac_served_unmark_allReadA.v. wrapper_bcmp at its listing address: YG0d.v abcmp_realizes, discharged by the
   link instance's interceptor table (lib/A/Rt, the bcmp trampoline's own lemma). *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis LV : LinkVals.
Hypothesis HRD : reac_link_alias_read_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis HBC : abcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_bcmp).

Section c.
Variable cx : umcx.
Variable fpos : Z.
Hypothesis HPRE : um_pre SK B cx.
Hypothesis HNIN : ~ In (UM_CID, fpos) (frames (um_Sc cx)).
Hypothesis HS1W : exists S1 W1 mem1 md1, AR SEGS B (um_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (UM_CID, fpos) :: frames (um_Sc cx) /\ ablocks B (um_lyc cx) S1 = ablocks B (um_lyc cx) (um_Sc cx).
#[local] Notation F := (um_F cx fpos).
#[local] Notation SH := (um_SH cx fpos).

(* the bytes wrapper_bcmp compares: [F + 32, F + 47) and "reac-pw:served" with its NUL; its answer *)
Lemma urb_cmp : forall ly S W m md al, rk_inv SK B cx fpos ly S W m md ->
  acstr_at SEGS (rdW W m) (F + 32) al ->
  ((forall i, 0 <= i < 15 -> aview SEGS (w_H W) m (F + 32 + i) = aview SEGS (w_H W) m (LA_S_SERVED + i))
     <-> bl_eqb al S_SERVED = true).
Proof.
  intros ly S W m md al HI AL.
  destruct (rk_served_at SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W ly S W m md HI) as (SV & _).
  rewrite bl_eqb_iff. apply (rk_served_cmp (aview SEGS (w_H W) m) (F + 32) LA_S_SERVED al).
  - exact (rk_acstr_rd SEGS (w_H W) m (F + 32) al AL).
  - intros i Hi. apply (rk_acstr_rd SEGS (w_H W) m LA_S_SERVED S_SERVED SV). rewrite rk_S_SERVED_len. lia.
  - exact (proj2 AL).
Qed.
End c.

(* ==========================================================================
   THE STAGE: +0x270 -> JOIN / wrapper_bcmp -> JOIN / MID
   ========================================================================== *)
Theorem um_read_b : forall c, um_mid_obl SK B c -> um_join_obl SK B c -> um_from SK B (fun cx => um_gi_rd SK B cx c).
Proof.
intros c HMID HJOIN cx fpos ly3 S3 W3 ms3 md3 HPRE HGI.
destruct HGI as (Hpc & HLOOP & HBASE & HZ & kbs & al & AL & K1 & K2 & K3).
pose proof HBASE as HBASE0. pose proof HLOOP as HLOOP0.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm & HS1W & Hfa3
  & R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & _ & _ & _ & HFpres & HSpres & _ & Hfds3 & Hfs3 & _).
destruct HLOOP as (Hm & Hc & R21 & R22 & R23 & R24 & R26 & R27 & _ & _ & _).
pose proof (urb_R_of SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 ms3 md3 HLOOP0 HBASE0) as RR3.
pose proof (rk_inv_of_base SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 ms3 md3 HBASE0 HLOOP0)
  as HINV3.
destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W)
  as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W) as (F1 & F2 & F3 & F4 & F5 & F6).
unfold in_app, ASAN_CEIL in F4.
destruct (rk_SH SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W) as (SH1 & SH2 & SH3 & SH4).
pose proof HPRE as ((HJ & HGX & _ & _ & _ & Hgp & Htp & _) & _).
pose proof alloc_ceiling_value as (ACV & _).
(* ---- the register-only state at +0x270 ---- *)
pose (E := Eimg (Ereg (ms_regs ms3) [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (urb_ss UM_RET_RD) (restrict (w_H W3) ms3)).
{ rewrite (urd_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom. unfold w64. apply urb_entry. }
assert (HE : E = Eimg (Ereg (ms_regs ms3) [])) by reflexivity.
clearbody E.
pose proof (paj_run_call_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUNC.
pose proof (paj_run_to_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUNTO.
apply (paj_branch W3 E (urb_ss UM_RET_RD) ms3 md3 _ BC_NE (SOff 10 0) (SLit 0) HS).
- (* ==== +0x270 taken: the read failed; JOIN ==== *)
  intros Hbt HSt. rewrite HE in Hbt. pose proof (urb_bt_true (ms_regs ms3) Hbt) as Ha0.
  urb_run_to RUNTO HSt HJ3 UM_CUT_JOIN.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  intros msJ matJ HSJ HJJ HFJ HFJ' HGJ.
  set (mdJ := with_vm_backing (m_vm_lazy md3) matJ md3) in *.
  destruct (urd_wvb_fds_fs (m_vm_lazy md3) matJ md3) as (EfdsJ & EfsJ).
  assert (UNJ : forall a, aview SEGS (w_H W3) (ms_mem msJ) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a. apply (YCbq.aview_eq_of SEGS). apply HFJ'. intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
  assert (HXJ : forall a, False ->
    (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (um_SH cx fpos <= a < um_SH cx fpos + 64))
    by (intros a []).
  assert (HINVJ : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem msJ) mdJ).
  { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem msJ) mdJ
      (fun _ => False) HINV3 HJJ (fun a _ _ => UNJ a) HXJ).
    - intros a Hp. exact (urd_apresent_grows (w_H W3) (ms_mem ms3) (ms_mem msJ) a HGJ Hp).
    - exact EfdsJ.
    - exact EfsJ. }
  pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem msJ)
    (fun _ => False) kbs (S c) HINV3 (fun a _ _ => UNJ a) HXJ (K1 Ha0)) as HKJ.
  assert (PJ : aregs_preserved (ms_regs ms3) (ms_regs msJ)).
  { rewrite HE in HSJ. apply (urb_cs_pi (w_H W3) (ms_regs ms3) _ msJ HSJ). urb_cs_tac. }
  pose proof (urb_R_keep SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c _ _ RR3 PJ) as RRJ.
  pmkst HSJ.
  apply (HJOIN cx fpos ly3 S3 W3 _ mdJ HPRE).
  destruct (urb_close SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 (ms_regs msJ) (Z_to_bv 64 (BASE + UM_CUT_JOIN)) (ms_mem msJ) mdJ Hc RRJ HINVJ) as (HLJ & HBJ).
  unfold um_gi_join. cbn [ms_pc_val ms_regs ms_mem mkst].
  split; [unfold w64, UM_CUT_JOIN, AF_reac_served_unmark_all; reflexivity|].
  split; [exact HLJ|]. split; [exists kbs; exact HKJ | exact HBJ].
- (* ==== +0x270 not taken: the read answered 0; wrapper_bcmp ==== *)
  intros Hbf HSf. rewrite HE in Hbf. pose proof (urb_bt_false (ms_regs ms3) Hbf) as Ha0.
  urd_run_call RUNC HSf HJ3.
  { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  intros ms1 mat1 HS1 HJ1 HFr1 HFr1' HG1.
  set (md1 := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
  destruct (urd_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (Efds1 & Efs1).
  assert (UN1 : forall a, aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a. apply (YCbq.aview_eq_of SEGS). apply HFr1'. intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
  assert (HX1 : forall a, False ->
    (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (um_SH cx fpos <= a < um_SH cx fpos + 64))
    by (intros a []).
  assert (HINV1 : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem ms1) md1).
  { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms1) md1
      (fun _ => False) HINV3 HJ1 (fun a _ _ => UN1 a) HX1).
    - intros a Hp. exact (urd_apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms1) a HG1 Hp).
    - exact Efds1.
    - exact Efs1. }
  assert (P1 : aregs_preserved (ms_regs ms3) (ms_regs ms1)).
  { rewrite HE in HS1. apply (urb_cs_abs (w_H W3) (ms_regs ms3) _ ms1 HS1). urb_cs_tac. }
  pose proof (urb_R_keep SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c _ _ RR3 P1)
    as (Q2 & Q9 & Q8 & Q18 & Q19 & Q25 & Q20 & Q3 & Q4 & Q21 & Q22 & Q23 & Q24 & Q26 & Q27).
  assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hr; rewrite HE; exact (urb_ew (ms_regs ms3) n r Hr)).
  prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (12%bv : bv 5) Q12.
  prreg HS1 (1%bv : bv 5) Q1.
  rewrite (EREG 21%nat 21%bv eq_refl) in Q10. rewrite (EREG 23%nat 23%bv eq_refl) in Q11.
  (* the memory at the call, the alias and the literal there *)
  pose proof (urb_acstr_eq (w_H W3) (ms_mem ms3) (ms_mem ms1) _ _ UN1 AL) as AL1.
  unfold UM_ALIAS in AL1.
  destruct (rk_served_at SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1 HINV1)
    as (SV1 & RAy & HVy & AMy).
  assert (Hsp1 : spZ (ms_regs ms1) = um_sp1 cx) by (unfold spZ; apply urd_bvu; [exact Q2 | lia]).
  assert (HFp1 : forall a, um_F cx fpos <= a < um_F cx fpos + UM_FB -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (urd_apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms1) a HG1 (HFpres a Ha))).
  assert (HSp1 : forall a, um_SH cx fpos <= a < um_SH cx fpos + UM_SHN -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (urd_apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms1) a HG1 (HSpres a Ha))).
  pmkst HS1.
  (* ---- wrapper_bcmp ---- *)
  eapply SRr_bind.
  { apply (aj_gx_bcmp_at SK SEGS B LAWS pa_segs_low (pa_sigma LS___interceptor_trampoline_bcmp) HBC
      (um_G cx) (um_XO cx) (um_OUT cx) W3 (ms_regs ms1) (ms_mem ms1) (um_STK cx) (um_sp0 cx) (um_FP cx)
      (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly3 S3 md1 (um_k cx)
      (um_F cx fpos + 32) LA_S_SERVED 15 (Z_to_bv 64 (BASE + UM_RET_BC)) HGX HJ1).
    - rewrite Hsp1. exact S1al16.
    - rewrite Hsp1. unfold ESTACK. lia.
    - rewrite Hsp1. lia.
    - exact (eq_trans Q3 Hgp).
    - exact (eq_trans Q4 Htp).
    - exact Q1.
    - unfold UM_RET_BC. apply ret_ok_codeptr_v; [unfold AF_reac_served_unmark_all; lia | reflexivity].
    - exact (eq_trans Q10 R21).
    - exact (eq_trans Q11 R23).
    - exact Q12.
    - lia.
    - lia.
    - lia.
    - unfold LA_S_SERVED. lia.
    - unfold LA_S_SERVED. lia.
    - intros a Ha. split.
      + apply (rk_aview_present SEGS). apply HFp1. unfold UM_FB. lia.
      + rewrite Hsp1. unfold ESTACK. lia.
    - intros a Ha. split.
      + apply (urb_cstr_vis (w_H W3) (ms_mem ms1) LA_S_SERVED S_SERVED SV1). rewrite rk_S_SERVED_len. lia.
      + rewrite Hsp1. unfold ESTACK. unfold LA_S_SERVED in Ha. intros [Hl _]. clear - Ha Hl S1lo Wlo Wc ACV. lia.
    - intros a Ha. rewrite Hsp1. unfold ESTACK. lia.
    - intros a Ha. rewrite Hsp1. unfold ESTACK. unfold LA_S_SERVED in Ha. intros [Hl _]. clear - Ha Hl S1lo Wlo Wc ACV. lia.
    - unfold amem_range. rk_consts. lia.
    - exact AMy.
    - intros x Hx. unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
      pose proof (HZ (x / 8 - um_F cx fpos / 8 - 4) ltac:(lia)) as Hz. rewrite <- UN1 in Hz.
      replace (um_SH cx fpos + 4 + (x / 8 - um_F cx fpos / 8 - 4)) with (SHADOW_OFF + x / 8) in Hz by (rewrite SH1; ring).
      exact Hz.
    - intros _ s Hs. apply (rk_aview_present SEGS). apply HSp1. unfold UM_SHN. rewrite SH1.
      unfold shadow_addr, SHADOW_OFF in *. lia.
    - exact RAy.
    - intros _. exact HVy. }
  cbv beta. intros W2 c2 HWle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HRES & HKP2 & HPR2 & HSM2).
  assert (Efds2 : m_fds md2 = m_fds md1) by (rewrite HSM2; exact (proj1 (urd_wvb_fds_fs _ _ _))).
  assert (Efs2 : m_fs md2 = m_fs md1) by (rewrite HSM2; exact (proj2 (urd_wvb_fds_fs _ _ _))).
  rewrite Hsp1 in HKP2. unfold ESTACK in HKP2.
  assert (HX2 : forall a, um_sp1 cx - 2 * 4096 <= a < um_sp1 cx ->
    (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (um_SH cx fpos <= a < um_SH cx fpos + 64)).
  { intros a Ha. left. unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
      AUN_ALIAS_READ_STK. lia. }
  assert (HINV2 : rk_inv SK B cx fpos ly3 S3 W3 mem2 md2).
  { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1 mem2 md2
      (fun a => um_sp1 cx - 2 * 4096 <= a < um_sp1 cx) HINV1 HJ2 HKP2 HX2 HPR2 Efds2 Efs2). }
  pose proof (urb_R_keep SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c _ _
    (urb_R_keep SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c _ _ RR3 P1) HP2) as RR2.
  (* the answer of the compare *)
  pose proof (urb_cmp cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1 al HINV1 AL1) as CMP.
  (* ---- the register-only state at +0x284 ---- *)
  pose proof (urb_entry (w_H W3) regs2 UM_RET_BC mem2) as HS4.
  pose proof (Eimg_env (Ereg regs2 [])) as HEI4.
  apply (paj_branch W3 _ (urb_ss UM_RET_BC) _ md2 _ BC_NE (SOff 10 0) (SLit 0) HS4).
  + (* ==== +0x284 taken: the alias is not "reac-pw:served"; JOIN ==== *)
    intros Hbt4 HSt4. pose proof (urb_bt_true regs2 Hbt4) as Hb0.
    assert (Hneq : bl_eqb al S_SERVED = false).
    { destruct (bl_eqb al S_SERVED) eqn:Eb; [|reflexivity]. exfalso. apply Hb0. apply HRES. apply CMP. first [exact Eb | reflexivity]. }
    urb_run_to RUNTO HSt4 HJ2 UM_CUT_JOIN.
    { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
    intros msJ matJ HSJ HJJ HFJ HFJ' HGJ.
    set (mdJ := with_vm_backing (m_vm_lazy md2) matJ md2) in *.
    destruct (urd_wvb_fds_fs (m_vm_lazy md2) matJ md2) as (EfdsJ & EfsJ).
    cbn [ms_mem mkst] in HFJ', HGJ.
    assert (UNJ : forall a, aview SEGS (w_H W3) (ms_mem msJ) a = aview SEGS (w_H W3) mem2 a).
    { intros a. apply (YCbq.aview_eq_of SEGS). apply HFJ'. intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
    assert (HINVJ : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem msJ) mdJ).
    { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 mem2 md2 (ms_mem msJ) mdJ
        (fun _ => False) HINV2 HJJ (fun a _ _ => UNJ a) HX1).
      - intros a Hp. exact (urd_apresent_grows (w_H W3) mem2 (ms_mem msJ) a HGJ Hp).
      - exact EfdsJ.
      - exact EfsJ. }
    pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3
      (ms_mem ms1) (fun _ => False) kbs (S c) HINV3 (fun a _ _ => UN1 a) HX1 (K2 Ha0 Hneq)) as HK1.
    pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1
      mem2 (fun a => um_sp1 cx - 2 * 4096 <= a < um_sp1 cx) kbs (S c) HINV1 HKP2 HX2 HK1) as HK2.
    pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 mem2 md2
      (ms_mem msJ) (fun _ => False) kbs (S c) HINV2 (fun a _ _ => UNJ a) HX1 HK2) as HKJ.
    assert (PJ : aregs_preserved regs2 (ms_regs msJ)).
    { apply (urb_cs_pi (w_H W3) regs2 _ msJ HSJ). urb_cs_tac. }
    pose proof (urb_R_keep SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c _ _ RR2 PJ) as RRJ.
    pmkst HSJ.
    apply (HJOIN cx fpos ly3 S3 W3 _ mdJ HPRE).
    destruct (urb_close SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 (ms_regs msJ) (Z_to_bv 64 (BASE + UM_CUT_JOIN)) (ms_mem msJ) mdJ Hc RRJ HINVJ) as (HLJ & HBJ).
    unfold um_gi_join. cbn [ms_pc_val ms_regs ms_mem mkst].
    split; [unfold w64, UM_CUT_JOIN, AF_reac_served_unmark_all; reflexivity|].
    split; [exact HLJ|]. split; [exists kbs; exact HKJ | exact HBJ].
  + (* ==== +0x284 not taken: the alias is ours; MID ==== *)
    intros Hbf4 HSf4. pose proof (urb_bt_false regs2 Hbf4) as Hb0.
    assert (Heq : bl_eqb al S_SERVED = true) by (apply CMP; apply HRES; exact Hb0).
    urb_run_to RUNTO HSf4 HJ2 UM_CUT_MID.
    { intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
    intros msM matM HSM HJM HFM HFM' HGM.
    set (mdM := with_vm_backing (m_vm_lazy md2) matM md2) in *.
    destruct (urd_wvb_fds_fs (m_vm_lazy md2) matM md2) as (EfdsM & EfsM).
    cbn [ms_mem mkst] in HFM', HGM.
    assert (UNM : forall a, aview SEGS (w_H W3) (ms_mem msM) a = aview SEGS (w_H W3) mem2 a).
    { intros a. apply (YCbq.aview_eq_of SEGS). apply HFM'. intros (r & Hr & _). vm_compute in Hr. destruct Hr. }
    assert (HINVM : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem msM) mdM).
    { apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 mem2 md2 (ms_mem msM) mdM
        (fun _ => False) HINV2 HJM (fun a _ _ => UNM a) HX1).
      - intros a Hp. exact (urd_apresent_grows (w_H W3) mem2 (ms_mem msM) a HGM Hp).
      - exact EfdsM.
      - exact EfsM. }
    pose proof (rk_kinv_mid_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3
      (ms_mem ms1) (fun _ => False) kbs c HINV3 (fun a _ _ => UN1 a) HX1 (K3 Ha0 Heq)) as HK1.
    pose proof (rk_kinv_mid_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1
      mem2 (fun a => um_sp1 cx - 2 * 4096 <= a < um_sp1 cx) kbs c HINV1 HKP2 HX2 HK1) as HK2.
    pose proof (rk_kinv_mid_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 mem2 md2
      (ms_mem msM) (fun _ => False) kbs c HINV2 (fun a _ _ => UNM a) HX1 HK2) as HKM.
    assert (PM : aregs_preserved regs2 (ms_regs msM)).
    { apply (urb_cs_pi (w_H W3) regs2 _ msM HSM). urb_cs_tac. }
    pose proof (urb_R_keep SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c _ _ RR2 PM) as RRM.
    pmkst HSM.
    apply (HMID cx fpos ly3 S3 W3 _ mdM HPRE).
    destruct (urb_close SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 (ms_regs msM) (Z_to_bv 64 (BASE + UM_CUT_MID)) (ms_mem msM) mdM Hc RRM HINVM) as (HLM & HBM).
    unfold um_gi_mid. cbn [ms_pc_val ms_regs ms_mem mkst].
    split; [unfold w64, UM_CUT_MID, AF_reac_served_unmark_all; reflexivity|].
    split; [exact HLM|]. split; [exists kbs; exact HKM | exact HBM].
Qed.

(* ==========================================================================
   THE PIECE: HEAD c -> MID c / JOIN c
   ========================================================================== *)
Theorem um_read : forall c, um_mid_obl SK B c -> um_join_obl SK B c -> um_head_obl SK B c.
Proof.
  intros c HMID HJOIN.
  exact (um_read_a SK B LAWS TB HSEGS RELRO_IMG LV HRD c (um_read_b c HMID HJOIN)).
Qed.
End b.
End a.
