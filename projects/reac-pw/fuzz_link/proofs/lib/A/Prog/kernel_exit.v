(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's EXIT phase, kin_exit (+0x2140) -> `ret` (+0x21b0) -> the contract's Post (link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4; the cuts are kernel_defs.v, the statement-level facts kernel_exit_post.v).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3)):
     +0x2140  lui   a0, 0x45e03 ; addiw a0, a0, 0x60e    a0 := 0x45e0360e (the retired-frame magic)
     +0x2148  ld    a1, 0x30(s1)                          a1 := F (spill slot KS_F)
     +0x214c  sd    a0, 0(a1)                             [F] := 0x45e0360e
     +0x2150  ld    a0, 0x20(s1)                          a0 := F (spill slot KS_FRES)
     +0x2154  beqz  a0, +0x2168                           NOT taken: F >= 4096 (frames_bounds), so the
                                                          real-stack arm (+0x2168 meta_fill_00(s6, 0x448)) is dead
     +0x2158  lui   a1, 2 ; addiw a1, a1, 0x240           a1 := 0x2240
     +0x2160  jal   frame_release_8                       (0x3e10c), returning to +0x2164
     +0x2164  j     +0x2174
     +0x2174  addi  sp, s0, -0x160 ; ld ra, 0x158(sp) .. ld s11, 0xf8(sp) ; addi sp, sp, 0x160
     +0x21b0  ret                                         the only returning path of kernel
   No instrumented check and no error path in this phase.

   THE PROOF, in two runs of the PLAIN engine (the token engine's static check refuses a writable window at F,
   which is low or high application memory; no shadow token is needed here and none is taken):
   - A, from +0x2140: the symbolic state is rebuilt from the cut with `pa_entry_st_ok_full` -- the two spill
     slots at s1 + 0x20 and s1 + 0x30 holding F (atom 32), and F's first 8 bytes writable, with the atom fact
     4096 <= F <= 2 ^ 47 that decides the `beqz`.  The run ends at the call of frame_release_8 with a0 = F,
     a1 = 0x2240 and ra = +0x2164.  Its only write is [F, F + 8), a byte of the frame the journal's owner holds
     (LinkWalkSide aj_gx_awr_frame).
   - the call: LinkWalkSide.v `aj_gx_stack_free_at` (ASF8), whose premise is F's flag word, which `kframe`
     carries and the run does not touch.
   - B, from +0x2164: the symbolic state is rebuilt over the thirteen saved words at s0 - 8 .. s0 - 104
     (`ksaved`, atoms 32 .. 44), the epilogue restores sp, gp, tp and s0 .. s11, and the run stops at the `ret`
     (LinkPaLib paj_ret_at).  It writes nothing, so the memory at the return is the memory frame_release_8 left.
   - the Post: LinkWalkSide.v `apost_side_gen` at the witness state `kjbk` carries, with the kept clause
     extended across the two runs and the call by `akept_step`, and kernel_apost from the cut's kgnl
     (kernel_exit_post.v kx_gnl_post), kcursor, kla_at and kkept.  Every value of the Post moves from the cut
     to the return by one transport (`TR` / `TRC`): a read-set byte is outside kernel's window (kx_akb_out)
     and outside the released frame (kx_not_side), so the two runs and the release leave it alone.  Writability
     of g_nl and of long_alias comes from KernImg's ki_gnl_wseg / ki_la_wseg, and of the cursor from
     kx_writable_of_view, since frame_release_8's contract keeps presence only above the allocator's ceiling.

   Section hypotheses: LAWS (the lib/A frame), LV (LinkVals, for the callee's literal pc), TB (PcapSyms B,
   AD2l.PcapB_syms, for LinkWalkShadow), KI (KernImg, kernel_img_tfib) and ASF8 (frame_release_8:
   lib/A/Rt/StackSideInst.v link_stack_free_8).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK1d StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi LinkWalkNlw LinkWalkSide LinkWalkShadow BoxBase PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
kernel_c kernel_img kernel_defs kernel_exit_post.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- a run with no writable region keeps the memory ---- *)
Lemma kx_no_wrange : forall E rs a,
  in_wrange E rs a -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> False.
Proof.
  intros E rs a (r & Hin & Hr) Hrs. rewrite forallb_forall in Hrs. specialize (Hrs r Hin).
  apply Z.leb_le in Hrs. lia.
Qed.

Lemma kx_mem_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
  intros E rs m m' Hfr Hrs. apply functional_extensionality. intros x. apply Hfr.
  intros Hx. exact (kx_no_wrange E rs _ Hx Hrs).
Qed.

(* a call's model keeps the descriptor table and the file system *)
Lemma kx_sbm_fds_fs : forall md md', same_but_materialized md md' ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. unfold same_but_materialized in H. rewrite H. exact (wvb_fds_fs _ _ _). Qed.

(* ---- the symbolic state at +0x2140: the two slots that hold F, and F's header word, writable ---- *)
Definition kx_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) KS_FRES (KS_F + 8) 0 0
    [YP09.mkChunk KS_FRES (CVal 8 (SOff 32 0)); YP09.mkChunk KS_F (CVal 8 (SOff 32 0))].
Definition kx_hd : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition kx_ssA : sstate :=
  mkSS (kpc KP_EXIT) sr_atoms [kx_sl; kx_hd] None (mkFacts [(32%nat, mkAF 4096 (2 ^ 47) 0)] [] []).

(* ---- the symbolic state at +0x2164 (= kpc 0x2164 = 15560): the thirteen saved words below s0 ---- *)
Definition kx_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
Definition kx_ssB : sstate := mkSS 15560 sr_atoms [kx_sv] None (mkFacts [] [] []).

Lemma kx_ssB_pc : ss_pc kx_ssB = kpc 0x2164. Proof. reflexivity. Qed.

(* ---- the run tactics (kernel_entry.v kn_run_call_plain, over LinkWalkSide's plain instances) ---- *)
Ltac kx_frame_tac :=
  let b := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "xx" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hrr end; lia|]);
  destruct Hin.

Ltac kx_call_plain RUNC HS HJ HS2 HJ2 HF2 HFr2 HG2 :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi link_tpi FUEL ss) in
    lazymatch r with
    | (?ss2, PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi link_tpi FUEL ss = (ss2, PRS_call s)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNC W FUEL E ss ss2 s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
      [ clear Hrun
      | clear Hrun;
        let msx := fresh "msx" in let matx := fresh "matx" in
        intros msx matx HS2 HJ2 HF2 HFr2 HG2; cbn [ms_mem mkst] in HF2, HFr2, HG2, HJ2 ]
    | ?x => idtac "kx_call_plain: the run ends" x; fail
    end
  end.

Ltac kx_run_plain RUN HS HJ HS2 HJ2 HF2 HFr2 HG2 :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi link_tpi FUEL ss) in
    lazymatch r with
    | (?ss2, ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi link_tpi FUEL ss = (ss2, st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUN W FUEL E ss ss2 st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      [ clear Hrun
      | clear Hrun;
        let msx := fresh "msx" in let matx := fresh "matx" in
        intros msx matx HS2 HJ2 HF2 HFr2 HG2; cbn [ms_mem mkst] in HF2, HFr2, HG2, HJ2 ]
    end
  end.

(* one saved word of the epilogue's region *)
Ltac kx_ch n v EBeq Hsv :=
  apply (chunk_ok_val pa_segs _ _ _ _ 8%N (SOff n 0) v);
  [ apply sv_off0; rewrite EBeq; symmetry; apply Z_to_bv_bv_unsigned
  | apply getr_rng
  | cbn; lia
  | apply val_mem_of_rdword; exact Hsv ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.                                        (* AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                                 (* kernel_img_tfib *)
Hypothesis ASF8 : astack_free_realizes pa_segs B 0x3e10c 8.        (* StackSideInst.v link_stack_free_8 *)

(* A machine state at a cut is the one `mkst` builds. *)
Lemma kx_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 pc) (ms_mem ms) (seg_rom SEGS).
Proof using All.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

Theorem kn_exit : kfrom SK B (kpost SK B) (kin_exit B).
Proof.
intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
destruct HI as (j & adv & Hj & HK).
pose proof HK as (HMS & HR0 & HRL & HSV & HFRM & HSH & HSL & HJB & HKPT & HCU & HGN & HLA).
pose proof HMS as (Hpc & Hrv & Hsvc & Hrom & Hfreg & Hfcsr).
pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
destruct HFRM as (HFhdr & HFo13 & HFo14 & HFflag & HFpres & HFshp).
destruct HKPT as (HKEPT & HROD3).
unfold kregs_eq in HRL. rewrite !Forall_cons_iff in HRL. destruct HRL as (R24 & _). cbn [fst snd] in R24.
unfold kslots_eq in HSL. rewrite !Forall_cons_iff in HSL.
destruct HSL as (SLFSH & SLFRES & SLF & _). cbn [fst snd] in SLFSH, SLFRES, SLF.
pose proof HJB as (Hk2 & HS3fs & HPerm & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & HfrS1 & Habl1) & Hfds3 & Hfs3).
pose proof HB as HB0.
destruct HB as (HPRE & HRD & HKPRE & HNK & HWF & HWP & HWN & HWPr & HWNr & HD & HDL & HLAa & HLAL).
destruct HPRE as (HJ0 & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hroom & Hajw & HWRO).
destruct HKPRE as (kbsP & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16
  & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26).
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).

(* ---- the numbers ---- *)
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
assert (HAK : KERNEL_AK = 4640) by reflexivity.
assert (HESv : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes KN_CID = 16384) by reflexivity.
assert (Esf : sf_span KN_CID KN_FSZ = 1096) by reflexivity.
assert (Efb8 : fs_frame_bytes KN_CID / 8 = 2048) by reflexivity.
assert (Esp : spZ (k_regs cx) = ksp cx) by reflexivity.
assert (Ea0 : aarg (k_regs cx) 0 = ka0 cx) by reflexivity.
rewrite HAK in Hwlo.
assert (Hceil : alloc_ceiling <= k_sp0 cx - k_STK cx)
  by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
assert (Hspw : 0 <= ksp cx < 2 ^ 64) by (unfold ksp, spZ; apply getr_rng).
assert (Hal16' : ksp cx mod 16 = 0) by exact Hal16.
assert (Hsp352 : 0 <= ksp cx - 352) by lia.
assert (Hmod16 : (ksp cx - 352) mod 16 = 0) by (rewrite Zminus_mod, Hal16'; reflexivity).
pose proof (sp1_facts (ksp cx - 352) Hsp352 Hmod16) as (Hs1a & Hs1b & Hs1c).
assert (Esp1 : ksp1 cx = 32 * ((ksp cx - 352) / 32)) by reflexivity.
assert (Hsp1lo : ksp cx - 368 <= ksp1 cx) by (rewrite Esp1; lia).
assert (Hsp1hi : ksp1 cx <= ksp cx - 352) by (rewrite Esp1; lia).
assert (Hsp1m : ksp1 cx mod 16 = 0) by (rewrite Esp1; exact Hs1c).
assert (Hsp1w : 0 <= ksp1 cx < 2 ^ 64) by lia.

(* ---- F: its address at the current layout, its bounds and its class ---- *)
destruct (aj_gx_frame_addr SK SEGS B LAWS Hsegs (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
  (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2
  KN_CID fpos HJ) as (EFA3 & EFL3).
destruct (aj_gx_frame_addr SK SEGS B LAWS Hsegs (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
  (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx)
  (k_mdc cx) (k_k cx) KN_CID fpos HJ0) as (EFAc & EFLc).
assert (EFA : frame_addr ly3 KN_CID fpos = frame_addr (k_lyc cx) KN_CID fpos)
  by (rewrite EFA3, EFAc; reflexivity).
assert (EFL : flag_addr ly3 KN_CID fpos = flag_addr (k_lyc cx) KN_CID fpos)
  by (rewrite EFL3, EFLc; reflexivity).
assert (EkF : kF cx fpos = frame_addr (k_lyc cx) KN_CID fpos) by reflexivity.
assert (EkFL : kFL cx fpos = flag_addr (k_lyc cx) KN_CID fpos) by reflexivity.
assert (HinS1 : In (KN_CID, fpos) (frames S1)) by (rewrite HfrS1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 HinS1) as (HF4' & HFC' & _).
destruct (frame_facts B (k_lyc cx) S1 (aview SEGS (w_H W1) mem1) KN_CID fpos (proj1 HAR1) HinS1)
  as (Hcid & Hpos & _).
assert (HF4 : 4096 <= kF cx fpos) by (rewrite EkF; exact HF4').
assert (HF16 : kF cx fpos + 16384 <= alloc_ceiling) by (rewrite EkF; rewrite HFB in HFC'; exact HFC').
assert (HFw : 0 <= kF cx fpos < 2 ^ 64) by lia.

(* ---- the symbolic state at +0x2140 ---- *)
remember (Eimg (Ereg (ms_regs ms3) [w64 (kF cx fpos)])) as EA eqn:HEA.
assert (HEIA : img_env pa_val A_LIM EA) by (subst EA; apply Eimg_env).
assert (EA2 : ew EA 2%nat = w64 (ksp1 cx)) by (subst EA; rewrite <- A2; apply ew_Eimg_Ereg_nat; reflexivity).
assert (EA9 : ew EA 9%nat = w64 (ksp1 cx)) by (subst EA; rewrite <- A9; apply ew_Eimg_Ereg_nat; reflexivity).
assert (EA3 : ew EA 3%nat = getr (k_regs cx) 3)
  by (subst EA; rewrite <- A3; apply ew_Eimg_Ereg_nat; reflexivity).
assert (EA4 : ew EA 4%nat = getr (k_regs cx) 4)
  by (subst EA; rewrite <- A4; apply ew_Eimg_Ereg_nat; reflexivity).
assert (EA8 : ew EA 8%nat = w64 (ksp cx)) by (subst EA; rewrite <- A8; apply ew_Eimg_Ereg_nat; reflexivity).
assert (EA32 : ew EA 32%nat = w64 (kF cx fpos))
  by (subst EA; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra (ms_regs ms3) [w64 (kF cx fpos)] 0)).
assert (UA32 : bv_unsigned (ew EA 32%nat) = kF cx fpos)
  by (rewrite EA32; unfold w64; apply unsigned_lit_small; lia).
assert (UA9 : bv_unsigned (ew EA 9%nat) = ksp1 cx)
  by (rewrite EA9; unfold w64; apply unsigned_lit_small; lia).

assert (HSA : st_ok_pi SEGS pa_val EA kx_ssA (restrict (w_H W3) ms3)).
{ rewrite (kx_ms_shape ms3 (BASE + kpc KP_EXIT) Hpc Hrv Hsvc Hrom Hfreg Hfcsr).
  rewrite restrict_mkst_fx. unfold kx_ssA. apply pa_entry_st_ok_full.
  - subst EA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold kx_sl, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UA9.
      split; [unfold KS_FRES; lia|]. split; [unfold KS_F; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val pa_segs EA _ (ksp1 cx) KS_FRES 8%N (SOff 32 0) (kF cx fpos)).
        -- apply sv_off0. exact EA32.
        -- cbn; lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ SLFRES).
      * apply (chunk_ok_val pa_segs EA _ (ksp1 cx) KS_F 8%N (SOff 32 0) (kF cx fpos)).
        -- apply sv_off0. exact EA32.
        -- cbn; lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ SLF).
    + unfold kx_hd, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UA32.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply kn_apresent_writable. apply HFpres. rewrite HFB. lia.
  - apply pairwise_disjoint_of_extents.
    unfold kx_sl, kx_hd, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite UA9, UA32. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold KS_FRES, KS_F. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UA32, Z.pow_0_r, Z.mod_1_r. repeat split; lia. }

(* ---- the run to the call of frame_release_8 ---- *)
pose (RUNC := paj_run_call_plain_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
kx_call_plain RUNC HSA HJ HSA1 HJA1 HFA HFrA HGA.
{ unfold kx_ssA. cbn [ss_mem].
  apply awr_ok_x_cons; [| apply awr_ok_x_cons; [| apply awr_ok_x_nil]].
  - intros x Hx. unfold kx_sl in Hx.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia.
  - intros x Hx. unfold kx_hd in Hx.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite UA32 in Hx.
    left. apply (aj_gx_awr_frame SK SEGS B LAWS Hsegs (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx)
      (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3
      (ms_mem ms3) md3 k2 KN_CID fpos x HJ ltac:(left; reflexivity)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (frame_addr (k_lyc cx) KN_CID fpos) with (kF cx fpos). rewrite HFB. lia. }
pose proof (kept_of_frame (segs := SEGS) EA (ss_mem kx_ssA) (w_H W3) (ms_mem ms3) _
  (fun x => kF cx fpos <= x < kF cx fpos + 8) HFrA ltac:(kx_frame_tac)) as UNA.
pose proof (fun x Hp => apresent_grows _ _ _ x HGA Hp) as PA.

(* ---- the call ---- *)
pmkst HSA1.
prreg HSA1 (1%bv : bv 5) RA1. prreg HSA1 (2%bv : bv 5) RA2. prreg HSA1 (3%bv : bv 5) RA3.
prreg HSA1 (4%bv : bv 5) RA4. prreg HSA1 (8%bv : bv 5) RA8.
prreg HSA1 (10%bv : bv 5) RA10. prreg HSA1 (11%bv : bv 5) RA11.
rewrite (lv_sigma LV). change (link_sigma LS___asan_stack_free_8) with 0x3e10c.
repeat rewrite wvb_collapse in HJA1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (Qsp : spZ rg = ksp1 cx)
    by (unfold spZ; rewrite RA2, EA2; unfold w64; apply unsigned_lit_small; lia);
  eapply SRr_bind;
  [ eapply (aj_gx_stack_free_at SK SEGS B LAWS Hsegs 0x3e10c KN_CID ASF8 ltac:(unfold KN_CID; lia)
      (k_G cx) (k_XO cx) (k_OUT cx) W3 rg mm (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
      (k_mem0 cx) (k_md0 cx) (k_own cx) ly3 S3 mdx k2 fpos KN_FSZ _ HJA1)
  | ]
end.
- rewrite RA10, EA32, EFA, EkF. reflexivity.
- rewrite RA11. reflexivity.
- rewrite HFB. unfold KN_FSZ. lia.
- reflexivity.
- rewrite EFA, EFL. change (frame_addr (k_lyc cx) KN_CID fpos) with (kF cx fpos). change (flag_addr (k_lyc cx) KN_CID fpos) with (kFL cx fpos).
  rewrite <- HFflag. apply rdword_ext. intros kk Hk. apply UNA; rewrite HFB; lia.
- rewrite Qsp. exact Hsp1m.
- rewrite Qsp, HESv. lia.
- rewrite Qsp. lia.
- rewrite RA3, EA3. exact Hgp.
- rewrite RA4, EA4. exact Htp.
- exact RA1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- cbv beta. intros W4 c4 _ (-> & regs2 & mem2 & md2 & -> & HJF & HPRES & HF5 & HKEEPF & HPWIN & HPCEIL & HSMF).
  (* run A's symbolic state is a megabyte-sized term and is finished with: every later tactic would walk it *)
  clear HSA HSA1 HFA HFrA HJ HJA1.
  rewrite Qsp in HKEEPF, HPWIN.
  (* ---- the memory from the cut to the state frame_release_8 left ---- *)
  assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (ksp1 cx - ESTACK <= a < ksp1 cx) ->
      ~ aside_rng (k_lyc cx) KN_CID fpos a ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hw Hs.
    assert (Hsh : ~ (shadow_addr (frame_addr ly3 KN_CID fpos) <= a
                     < shadow_addr (frame_addr ly3 KN_CID fpos) + sf_span KN_CID KN_FSZ)).
    { rewrite EFA, Esf. intros Hc. apply Hs. right. left. unfold in_zr. cbn [fst snd].
      rewrite Efb8. lia. }
    assert (Hfl : a <> flag_addr ly3 KN_CID fpos).
    { rewrite EFL. intros Hc. apply Hs. right. right. exact Hc. }
    rewrite (HKEEPF a Ha Hsh Hfl Hw).
    apply UNA; [exact Ha|].
    intros Hc. apply Hs. left. unfold in_zr, frame_rng. cbn [fst snd]. change (frame_addr (k_lyc cx) KN_CID fpos) with (kF cx fpos). rewrite HFB. lia. }
  assert (PG2 : forall a, alloc_ceiling <= a < 2 ^ 64 ->
      apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem2 a)
    by (intros a Ha Hp; exact (HPCEIL a Ha (PA a Hp))).

  (* ---- the saved words at the state frame_release_8 left ---- *)
  assert (RDSV : forall a, ksp cx - 104 <= a -> a + 8 <= ksp cx ->
      rdword (aview SEGS (w_H W3) mem2) a = rdword (aview SEGS (w_H W3) (ms_mem ms3)) a).
  { intros a H1 H2. apply rdword_ext. intros kk Hk. apply UN2; [lia | lia |].
    intros Hsd. destruct (aside_rng_low SK SEGS B LAWS Hsegs (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos (a + kk)
      HAR1 HinS1 Hsd) as (Hlo & _). lia. }
  assert (SV0 : rdword (aview SEGS (w_H W3) mem2) (ksp cx + (-8))
                = Some (bv_unsigned (getr (k_regs cx) 1))).
  { replace (ksp cx + (-8)) with (ksp cx - 8) by lia.
    rewrite (RDSV (ksp cx - 8) ltac:(lia) ltac:(lia)). exact (proj1 HSV). }
  assert (SVG : forall jj off (r : bv 5), 0 <= jj < 12 -> off = -16 - 8 * jj ->
      Z_to_bv 5 (if jj <? 2 then 8 + jj else 16 + jj) = r ->
      rdword (aview SEGS (w_H W3) mem2) (ksp cx + off) = Some (bv_unsigned (getr (k_regs cx) r))).
  { intros jj off r Hjj -> <-.
    replace (ksp cx + (-16 - 8 * jj)) with (ksp cx - 16 - 8 * jj) by lia.
    rewrite (RDSV (ksp cx - 16 - 8 * jj) ltac:(lia) ltac:(lia)). exact (proj2 HSV jj Hjj). }

  (* ---- the symbolic state at +0x2164 ---- *)
  assert (QB : forall (z : Z) (r : bv 5), acallee_saved z -> Z_to_bv 5 z = r ->
      getr regs2 r = getr (ms_regs msx) r)
    by (intros z r Hc Hr; exact (kx_pres_at SK B LAWS _ _ z r HPRES Hc Hr)).
  remember (Eimg (Ereg regs2 [getr (k_regs cx) 1; getr (k_regs cx) 8; getr (k_regs cx) 9;
      getr (k_regs cx) 18; getr (k_regs cx) 19; getr (k_regs cx) 20; getr (k_regs cx) 21;
      getr (k_regs cx) 22; getr (k_regs cx) 23; getr (k_regs cx) 24; getr (k_regs cx) 25;
      getr (k_regs cx) 26; getr (k_regs cx) 27])) as EB eqn:HEB.
  assert (HEIB : img_env pa_val A_LIM EB) by (rewrite HEB; apply Eimg_env).
  assert (EB3 : ew EB 3%nat = getr (k_regs cx) 3).
  { transitivity (getr regs2 3%bv).
    - rewrite HEB. apply ew_Eimg_Ereg_nat. reflexivity.
    - rewrite (QB 3 3%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)), RA3. exact EA3. }
  assert (EB4 : ew EB 4%nat = getr (k_regs cx) 4).
  { transitivity (getr regs2 4%bv).
    - rewrite HEB. apply ew_Eimg_Ereg_nat. reflexivity.
    - rewrite (QB 4 4%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)), RA4. exact EA4. }
  assert (EB8 : ew EB 8%nat = w64 (ksp cx)).
  { transitivity (getr regs2 8%bv).
    - rewrite HEB. apply ew_Eimg_Ereg_nat. reflexivity.
    - rewrite (QB 8 8%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; vm_compute; reflexivity)), RA8. exact EA8. }
  assert (UB8 : bv_unsigned (ew EB 8%nat) = ksp cx)
    by (rewrite EB8; unfold w64; apply unsigned_lit_small; lia).
  (* the saved words are the extra atoms 32 .. 44: Eimg_low, then ew_Ereg_extra at the index written 32 + j *)
  assert (EB32 : ew EB 32%nat = getr (k_regs cx) 1).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 32%nat with (32 + 0)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB33 : ew EB 33%nat = getr (k_regs cx) 8).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB34 : ew EB 34%nat = getr (k_regs cx) 9).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 34%nat with (32 + 2)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB35 : ew EB 35%nat = getr (k_regs cx) 18).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 35%nat with (32 + 3)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB36 : ew EB 36%nat = getr (k_regs cx) 19).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 36%nat with (32 + 4)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB37 : ew EB 37%nat = getr (k_regs cx) 20).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 37%nat with (32 + 5)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB38 : ew EB 38%nat = getr (k_regs cx) 21).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 38%nat with (32 + 6)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB39 : ew EB 39%nat = getr (k_regs cx) 22).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 39%nat with (32 + 7)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB40 : ew EB 40%nat = getr (k_regs cx) 23).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 40%nat with (32 + 8)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB41 : ew EB 41%nat = getr (k_regs cx) 24).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 41%nat with (32 + 9)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB42 : ew EB 42%nat = getr (k_regs cx) 25).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 42%nat with (32 + 10)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB43 : ew EB 43%nat = getr (k_regs cx) 26).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 43%nat with (32 + 11)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }
  assert (EB44 : ew EB 44%nat = getr (k_regs cx) 27).
  { rewrite HEB, Eimg_low by (unfold A_TEXT; lia). change 44%nat with (32 + 12)%nat.
    rewrite ew_Ereg_extra. cbn [nth]. reflexivity. }

  assert (HSB : st_ok_pi SEGS pa_val EB kx_ssB
                  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 15560)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold kx_ssB. apply pa_entry_st_ok_full.
    - rewrite HEB. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold kx_sv, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UB8.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      + kx_ch 32%nat (bv_unsigned (getr (k_regs cx) 1)) EB32 SV0.
      + kx_ch 33%nat (bv_unsigned (getr (k_regs cx) 8)) EB33
          (SVG 0 (-16) 8%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 34%nat (bv_unsigned (getr (k_regs cx) 9)) EB34
          (SVG 1 (-24) 9%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 35%nat (bv_unsigned (getr (k_regs cx) 18)) EB35
          (SVG 2 (-32) 18%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 36%nat (bv_unsigned (getr (k_regs cx) 19)) EB36
          (SVG 3 (-40) 19%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 37%nat (bv_unsigned (getr (k_regs cx) 20)) EB37
          (SVG 4 (-48) 20%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 38%nat (bv_unsigned (getr (k_regs cx) 21)) EB38
          (SVG 5 (-56) 21%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 39%nat (bv_unsigned (getr (k_regs cx) 22)) EB39
          (SVG 6 (-64) 22%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 40%nat (bv_unsigned (getr (k_regs cx) 23)) EB40
          (SVG 7 (-72) 23%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 41%nat (bv_unsigned (getr (k_regs cx) 24)) EB41
          (SVG 8 (-80) 24%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 42%nat (bv_unsigned (getr (k_regs cx) 25)) EB42
          (SVG 9 (-88) 25%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 43%nat (bv_unsigned (getr (k_regs cx) 26)) EB43
          (SVG 10 (-96) 26%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
      + kx_ch 44%nat (bv_unsigned (getr (k_regs cx) 27)) EB44
          (SVG 11 (-104) 27%bv ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity)).
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - split; [cbn; exact I | split; [exact I | exact I]]. }

  (* ---- the epilogue ---- *)
  pose (RUN := paj_run_plain_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  kx_run_plain RUN HSB HJF HSB1 HJB1 HFB1 HFrB1 HGB1.
  { unfold kx_ssB. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold kx_sv in Hx.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. lia. }
  assert (HMB : ms_mem msx0 = mem2) by (eapply kx_mem_eq; [exact HFB1 | vm_compute; reflexivity]).
  prreg HSB1 (1%bv : bv 5) RB1. prreg HSB1 (2%bv : bv 5) RB2. prreg HSB1 (3%bv : bv 5) RB3.
  prreg HSB1 (4%bv : bv 5) RB4. prreg HSB1 (8%bv : bv 5) RB8. prreg HSB1 (9%bv : bv 5) RB9.
  prreg HSB1 (18%bv : bv 5) RB18. prreg HSB1 (19%bv : bv 5) RB19. prreg HSB1 (20%bv : bv 5) RB20.
  prreg HSB1 (21%bv : bv 5) RB21. prreg HSB1 (22%bv : bv 5) RB22. prreg HSB1 (23%bv : bv 5) RB23.
  prreg HSB1 (24%bv : bv 5) RB24. prreg HSB1 (25%bv : bv 5) RB25. prreg HSB1 (26%bv : bv 5) RB26.
  prreg HSB1 (27%bv : bv 5) RB27.
  pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
  eapply (RET W3 _ _ _ _ _ HSB1 eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  (* the two symbolic states are megabyte-sized terms: every later `lia` would walk them *)
  clear HSB HSB1 HGA HFB1 HFrB1 HGB1 HKEEPF HPWIN HF5 UNA PA.
  rewrite wvb_collapse, HMB.
  assert (EPCr : v_jalr (getr (ms_regs msx0) 1) 0 = getr (k_regs cx) 1)
    by (rewrite RB1, EB32; exact Hraw).
  rewrite EPCr.

  (* ---- the Post ---- *)
  unfold kpost.
  eapply (apost_side_gen SK SEGS B LAWS Hsegs).
  + exact HJ0.
  + rewrite HMB in HJB1.
    rewrite <- (wvb_collapse (m_vm_lazy md2) matF matx0 md2).
    apply (ajournal_gx_materialize SEGS B LAWS Hsegs). exact HJB1.
  + rewrite Hk2. lia.
  + destruct (kx_sbm_fds_fs _ _ HSMF) as (Hf1 & _).
    rewrite (proj1 (wvb_fds_fs _ _ _)), Hf1, (proj1 (wvb_fds_fs _ _ _)). exact Hfds3.
  + destruct (kx_sbm_fds_fs _ _ HSMF) as (_ & Hf2).
    rewrite (proj2 (wvb_fds_fs _ _ _)), Hf2, (proj2 (wvb_fds_fs _ _ _)). exact Hfs3.
  + apply kx_aregs.
    * rewrite RB2, EB8. unfold w64, ksp, spZ. apply Z_to_bv_bv_unsigned.
    * rewrite RB3. exact EB3.
    * rewrite RB4. exact EB4.
    * rewrite RB8. exact EB33.
    * rewrite RB9. exact EB34.
    * rewrite RB18. exact EB35.
    * rewrite RB19. exact EB36.
    * rewrite RB20. exact EB37.
    * rewrite RB21. exact EB38.
    * rewrite RB22. exact EB39.
    * rewrite RB23. exact EB40.
    * rewrite RB24. exact EB41.
    * rewrite RB25. exact EB42.
    * rewrite RB26. exact EB43.
    * rewrite RB27. exact EB44.
  + exact HAR1.
  + exact HfrS1.
  + exact Habl1.
  + (* the kept clause across the two runs and the call *)
    apply (akept_step SK SEGS B LAWS Hsegs (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
             W3 (ms_mem ms3) W3 mem2 (ksp cx - KERNEL_AK) (ksp cx)
             (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)
             (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)
             (fun a => aside_rng (k_lyc cx) KN_CID fpos a \/ (ksp1 cx - ESTACK <= a < ksp1 cx))
             HAR0).
    * rewrite HAK. lia.
    * lia.
    * exact HKEPT.
    * intros a Ha HX. apply UN2; [exact Ha | tauto | tauto].
    * intros a Ha Hp. exact (PG2 a Ha Hp).
    * intros a H. exact H.
    * intros a [H | H]; [left; right; exact H | right; rewrite HAK; rewrite HESv in H; lia].
  + (* Q *)
    split; [| split].
    * exact (set_fs_trans S3 (stack_free_state KN_CID fpos S3) (k_Sc cx) HS3fs
               (stack_free_state_set_fs KN_CID fpos S3)).
    * replace (ablocks B ly3 (stack_free_state KN_CID fpos S3)) with (ablocks B ly3 S3)
        by (unfold stack_free_state; rewrite ablocks_set_fs; reflexivity).
      exact HPerm.
    * (* kernel_apost: the transports from the cut (and from the call) to the return *)
      assert (TRN : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a ->
          ~ aside_rng (k_lyc cx) KN_CID fpos a).
      { intros a Ha.
        exact (kx_not_side SK B LAWS TB (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
                 (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx)
                 (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx) (ksp cx - KERNEL_AK) (ksp cx) KN_CID fpos a
                 HJ0 ltac:(unfold KN_CID; lia) Hpos Hnin (HRD a Ha)). }
      assert (TRB : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a ->
          0 <= a < 2 ^ 64 /\ ~ (ksp cx - KERNEL_AK <= a < ksp cx)).
      { intros a Ha.
        exact (kx_akb_out SK B LAWS (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
                 (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx)
                 (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx) (ksp cx - KERNEL_AK) (ksp cx) a
                 HJ0 ltac:(rewrite HAK; lia) (HRD a Ha)). }
      assert (TR : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
      { intros a Ha. destruct (TRB a Ha) as (Hr & Ho).
        apply UN2; [exact Hr | rewrite HAK in Ho; lia | exact (TRN a Ha)]. }
      assert (TRC : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a -> ~ kE cx a ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H (k_W cx)) (k_memc cx) a).
      { intros a Ha HnE. rewrite (TR a Ha).
        apply (akept_akb_gx SK SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
                 (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx)
                 (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx) W3 (ms_mem ms3) (ksp cx - KERNEL_AK) (ksp cx)
                 _ a HJ0 HKEPT (HRD a Ha));
          intros [H | H]; [exact (HnE H) | exact (TRN a Ha H)]. }
      (* a byte of g_nl above NK_OPEN, and a byte apart from every write, are outside the write set *)
      assert (HnEgnl : forall a, LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_SIZE -> ~ kE cx a).
      { intros a Ha (r & Hin & Hr). unfold kernel_awr in Hin. cbn [In] in Hin.
        unfold apart_gnl in P9. rewrite Ea0 in P9.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
          [ unfold NK_CHUNK, NK_OPEN, NK_SIZE in Ha, Hr; lia
          | unfold LA_G_NL, LA_LONG_ALIAS, LONG_ALIAS_SIZE, NK_OPEN, NK_SIZE in Ha, Hr; lia
          | rewrite Ea0 in Hr; unfold NK_OPEN, NK_SIZE in Ha, Hr, P9; lia ]. }
      assert (HnEap : forall p n a, kernel_apart (k_regs cx) p n -> p <= a < p + n -> ~ kE cx a).
      { intros p n a (Q1 & Q2 & Q3 & Q4) Hr (r & Hin & Hrr). unfold kernel_awr in Hin. cbn [In] in Hin.
        unfold apart_gnl, apart in Q2, Q3, Q4. rewrite Ea0 in Q4.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr;
          [ unfold NK_CHUNK, NK_OPEN, NK_SIZE in Hrr, Q2; lia
          | unfold LONG_ALIAS_SIZE in Hrr, Q3; lia
          | rewrite Ea0 in Hrr; lia ]. }
      intros kbs Hkbs.
      assert (Ekbs : kbs = k_kbs cx) by (exact (kx_anlk_unique SK B LAWS _ _ _ _ Hkbs HNK)).
      assert (EkbsP : kbsP = k_kbs cx) by (exact (kx_anlk_unique SK B LAWS _ _ _ _ P1 HNK)).
      subst kbs. subst kbsP.
      destruct HGN as (kbs3 & HNK3 & HGK).
      destruct (kx_gnl_post (k_kbs cx) kbs3 j HGK HWF Hj)
        as (GWF & GNX & GCH & GEE & GSO & GSE & GOP & GOD & GCL & GMI & GNS & GSNT & GNI).
      destruct HNK3 as ((HB3 & HW3a) & HL3).
      exists kbs3.
      assert (GBY : forall i, (i < length kbs3)%nat ->
          aview SEGS (w_H W3) mem2 (LA_G_NL + Z.of_nat i)
          = aview SEGS (w_H W3) (ms_mem ms3) (LA_G_NL + Z.of_nat i)).
      { intros i Hi. apply TR. unfold kernel_ard. right; right; left. lia. }
      assert (HNKE : anlk_at SEGS (mrestrict (w_H W3) mem2) LA_G_NL kbs3).
      { split; [split|].
        - exact (kx_abytes_moved SK B LAWS (w_H W3) (w_H W3) (ms_mem ms3) mem2 LA_G_NL kbs3 GBY HB3).
        - rewrite HL3. intros i Hi.
          exact (kx_writable_of_wseg SK B LAWS (mrestrict (w_H W3) mem2) LA_G_NL NK_SIZE (LA_G_NL + i)
                   ltac:(unfold LA_G_NL; lia) ltac:(unfold LA_G_NL, NK_SIZE; lia)
                   (ki_gnl_wseg SEGS B KI) ltac:(lia)).
        - exact HL3. }
      split; [exact HNKE|]. split; [exact GWF|]. split; [exact GNX|]. split; [exact GCH|].
      split; [exact GEE|]. split; [exact GSO|]. split; [exact GSE|].
      split; [exact GOP|]. split; [exact GOD|]. split; [exact GCL|]. split; [exact GMI|].
      split; [exact GNS|]. split; [exact GSNT|]. split; [exact GNI|].
      split.
      { (* the interface table *)
        intros tab (TN & TL & TE). split; [rewrite GNI; exact TN|]. split; [exact TL|].
        intros i nm ix Hi. destruct (TE i nm ix Hi) as (IXR & p & HU & HP0 & HCS & HU32).
        pose proof (proj1 (nth_error_Some tab i) ltac:(rewrite Hi; discriminate)) as Hlt.
        split; [exact IXR|]. exists p.
        assert (HNAME : kernel_apart (k_regs cx) p (Z.of_nat (length nm) + 1))
          by (exact (P26 tab i nm ix p (conj TN (conj TL TE)) Hi HU)).
        split.
        { apply (val_mem_moved SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) mem2
                   (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) 8 p);
            [| exact HU].
          intros kk Hk. apply TRC.
          - unfold kernel_ard. right; right; left. unfold NK_IF_NAME, NK_SIZE. lia.
          - apply HnEgnl. unfold NK_IF_NAME, NK_OPEN, NK_SIZE. lia. }
        split; [exact HP0|].
        split.
        { destruct HCS as (HCB & HCN). split; [|exact HCN].
          apply (kx_abytes_moved SK B LAWS (w_H (k_W cx)) (w_H W3) (k_memc cx) mem2 p (nm ++ [zb 0]));
            [| exact HCB].
          intros kk Hk. rewrite length_app in Hk. cbn [length] in Hk.
          apply TRC.
          - unfold kernel_ard. do 10 right. exists (k_kbs cx), tab, i, nm, ix, p.
            split; [exact HNK|]. split; [exact (conj TN (conj TL TE))|]. split; [exact Hi|].
            split; [exact HU|]. split; [exact (conj HCB HCN) | lia].
          - exact (HnEap p (Z.of_nat (length nm) + 1) (p + Z.of_nat kk) HNAME ltac:(lia)). }
        { apply (val_mem_moved SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) mem2
                   (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) 4 ix);
            [| exact HU32].
          intros kk Hk. apply TRC.
          - unfold kernel_ard. right; right; left. unfold NK_IF_INDEX, NK_SIZE. lia.
          - apply HnEgnl. unfold NK_IF_INDEX, NK_OPEN, NK_SIZE. lia. } }
      split.
      { (* the cursor *)
        intros wp wn HWPa HWNa Hwpr Hwnr.
        assert (Ewp : wp = k_wp cx)
          by (exact (kx_val64_unique SK B LAWS (w_H (k_W cx)) (k_memc cx) (ka0 cx) wp (k_wp cx)
                       HWPa HWP Hwpr HWPr)).
        assert (Ewn : wn = k_wn cx)
          by (exact (kx_val64_unique SK B LAWS (w_H (k_W cx)) (k_memc cx) (ka0 cx + 8) wn (k_wn cx)
                       HWNa HWN Hwnr HWNr)).
        subst wp wn.
        destruct HCU as (HAdv & HCp & HCn & HCw).
        exists adv. split; [lia|]. split.
        - apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 (ka0 cx) (ka0 cx) 8
                   (k_wp cx + adv)); [| exact HCp].
          intros kk Hk. apply TR. unfold kernel_ard. left. lia.
        - apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 (ka0 cx + 8) (ka0 cx + 8) 8
                   (k_wn cx - adv)); [| exact HCn].
          intros kk Hk. apply TR. unfold kernel_ard. left. lia. }
      split.
      { (* the cursor is writable *)
        destruct HCU as (HAdv & HCp & HCn & HCw).
        assert (HCpE : val_mem SEGS (mrestrict (w_H W3) mem2) (ka0 cx) 8 (k_wp cx + adv)).
        { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 (ka0 cx) (ka0 cx) 8
                   (k_wp cx + adv)); [| exact HCp].
          intros kk Hk. apply TR. unfold kernel_ard. left. lia. }
        assert (HCnE : val_mem SEGS (mrestrict (w_H W3) mem2) (ka0 cx + 8) 8 (k_wn cx - adv)).
        { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 (ka0 cx + 8) (ka0 cx + 8) 8
                   (k_wn cx - adv)); [| exact HCn].
          intros kk Hk. apply TR. unfold kernel_ard. left. lia. }
        rewrite Ea0. intros i Hi.
        destruct (TRB (ka0 cx + i) ltac:(unfold kernel_ard; left; lia)) as (Hrng & _).
        apply (kx_writable_of_view SK B LAWS (w_H W3) mem2 (ka0 cx + i) Hrng).
        - destruct (Z_lt_le_dec i 8) as [Hlt | Hge].
          + replace (ka0 cx + i) with (ka0 cx + Z.of_nat (Z.to_nat i)) by lia.
            exact (kx_view_of_val SK B LAWS (w_H W3) mem2 (ka0 cx) 8 (k_wp cx + adv) (Z.to_nat i)
                     HCpE ltac:(lia)).
          + replace (ka0 cx + i) with (ka0 cx + 8 + Z.of_nat (Z.to_nat (i - 8))) by lia.
            exact (kx_view_of_val SK B LAWS (w_H W3) mem2 (ka0 cx + 8) 8 (k_wn cx - adv)
                     (Z.to_nat (i - 8)) HCnE ltac:(lia)).
        - apply HWRO. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
          split; [unfold kernel_awr; cbn [In]; tauto | cbn [fst snd]; rewrite Ea0; lia]. }
      { (* long_alias *)
        destruct HLA as (la3 & (HLB & HLW) & HLL).
        exists la3. split; [split|].
        - apply (kx_abytes_moved SK B LAWS (w_H W3) (w_H W3) (ms_mem ms3) mem2 LA_LONG_ALIAS
                   (la3 ++ [zb 0])); [| exact HLB].
          intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
          apply TR. unfold kernel_ard. do 9 right; left. unfold LONG_ALIAS_SIZE. lia.
        - rewrite length_app. cbn [length]. intros i Hi.
          exact (kx_writable_of_wseg SK B LAWS (mrestrict (w_H W3) mem2) LA_LONG_ALIAS LONG_ALIAS_SIZE
                   (LA_LONG_ALIAS + i) ltac:(unfold LA_LONG_ALIAS; lia)
                   ltac:(unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE; lia)
                   (ki_la_wseg SEGS B KI) ltac:(unfold LONG_ALIAS_SIZE; lia)).
        - exact HLL. }
Qed.

End b.
End a.

Print Assumptions kn_exit.
