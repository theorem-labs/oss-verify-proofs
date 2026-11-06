(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1h.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC1h.v, ea5560a967b, carries it): the listing's names are bsym; frm_off_imgP states fuzz_boxreg.asan's image range as Reusable/YImgTop.v's [IMG_LO, IMG_TOP) in place of cgif's off_img (as BoxPaLib's blk_off_imgP does); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC1h.v, with its module paths and module names changed; 74 of its 98 lines of code are new or changed and 170 lines of the source are left out. *)
(* The program walk of reac_declared_vlan_add on reac-pw/fuzz_segconf image B (fuzz_segconf.asan-ubsan, entry
   BASE + AF_reac_declared_vlan_add = 0x8a514, 177 instructions, 112-byte frame, no side-stack frame) against
   reac_declared_vlan_add_contract (lib/B/Prog/reac_declared_vlan_add_c.v, image B's copy of the FINAL contract text
   at 6f783602b5e3): the image-B port of lib/A/Prog/reac_declared_vlan_add.v (commit
   fcd2fa03dd27, whose segment 0 it ports; the A walk was not closed at the port), ADAPTED to image B's code (the
   spilled shadow index, the loop's registers, UBSan's 13 branches to the trap `unimp` 0x8a760). Written for
   the image-B G4 + G5 walks. Step plan: the unit record's Bwalks-G45-plans/plan-reac_declared_vlan_add.md.
   The runtime entries the call reaches are Section hypotheses: the strcmp wrapper (RtString.astrcmp_realizes, row
   17), the checked memset (aintrin_realizes OSet, lib/B/YG0d.v) and the strncpy wrapper (RtSeg.astrncpy_realizes,
   row 12), each at its listing target; with them the listing's record PALib.
   This file composes the segments: segment 1 the entry (0x8a514 .. 0x8a5b8 / 0x8a614), segment 2 the search loop
   (0x8a5b8 .. 0x8a5f0, the duplicate exit, and the latch 0x8a5f0 .. 0x8a5b8 / 0x8a614), segment 3 the full exit and
   the checked memset (0x8a614 .. 0x8a654), segment 4 the strncpy call (0x8a654 .. 0x8a698), segment 5 the stores and
   the append exit (0x8a698 .. 0x8a75c); the loop by induction on the entries left. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtString RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase reac_declared_vlan_add_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_add_lem reac_declared_vlan_add_s0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_add_s1 reac_declared_vlan_add_s2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_add_s3 reac_declared_vlan_add_s4.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_add_s5.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
(* the runtime entries the call reaches, at their listing targets *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASTRNCPY : forall fx0 : YK11.FPState, @astrncpy_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncpy).

Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (rlo rhi tab max n par vid : Z) (t : list (list Z * Z)) (p : list Z).
Hypothesis HPRE : afn_pre SEGS B VAD_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS rlo rhi B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 tab.
Hypothesis H11 : getr regs 11 = w64 max.
Hypothesis H12 : getr regs 12 = w64 n.
Hypothesis H13 : getr regs 13 = w64 par.
Hypothesis H14 : getr regs 14 = w64 vid.
Hypothesis HADD : add_pre SEGS B ly S W mem regs tab max n par vid t p.

#[local] Notation Q := (@vad_Q fx rc SK PI B ly S W regs mem md tab max n vid t p).
#[local] Notation LHc := (@vad_LHc rc SK PI B ly S W regs mem md tab max n par vid t p).
#[local] Notation AFTc := (@vad_AFTc rc SK PI B ly S W regs mem md tab max n par vid t p).

(* after the search: the full exit, or memset, strncpy and the stores *)
Lemma vad_after : forall r m d, AFTc r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_AFT)) m (seg_rom SEGS)) d) Q.
Proof using HPRE HROD H10 H11 H12 H13 H14 HADD TL AMEMSET ASTRNCPY.
intros r m d HA.
eapply vad_aft; try eassumption.
intros r1 m1 d1 HMS. eapply vad_ms; try eassumption.
intros r2 m2 d2 HSN. eapply vad_sn; eassumption.
Qed.
(* the search loop from entry i, by induction on the entries left *)
Lemma vad_loop_all : forall dd i, (i + dd = length t)%nat -> (i < length t)%nat -> forall r m d, LHc i r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LH)) m (seg_rom SEGS)) d) Q.
Proof using HPRE HROD H10 H11 H12 H13 H14 HADD TL ASTRCMP AMEMSET ASTRNCPY.
induction dd as [|dd IH]; intros i Hd Hi r m d HLH; [lia|].
eapply vad_loop_step; try eassumption.
intros r1 m1 d1 HLT. eapply vad_latch; try eassumption.
- intros Hsi r2 m2 d2 HLH2. apply (IH (Datatypes.S i)); [lia | exact Hsi | exact HLH2].
- intros r2 m2 d2 HA. exact (vad_after r2 m2 d2 HA).
Qed.
Lemma vad_all : SRr SEGS W (cfg_at SEGS (BASE + AF_reac_declared_vlan_add) regs mem md) Q.
Proof using HPRE HROD H10 H11 H12 H13 H14 HADD TL ASTRCMP AMEMSET ASTRNCPY.
eapply vad_entry; try eassumption.
- intros r m d HLH. pose proof HLH as (_ & _ & _ & Hi & _).
  exact (vad_loop_all (length t) 0 ltac:(lia) Hi r m d HLH).
- intros r m d HA. exact (vad_after r m d HA).
Qed.
End w.

(* ---------- the contract, at image B's numbers: the entry BASE + AF_reac_declared_vlan_add (a listing term, 0x8a514)
   and image B's instance file's SegInstB.STK_reac_declared_vlan_add = 112 + 2 * ESTACK; any read-only
   window ---------- *)
Theorem reac_declared_vlan_add_walk : forall rlo rhi,
  reac_declared_vlan_add_contract SEGS B (BASE + AF_reac_declared_vlan_add) SegInstB.STK_reac_declared_vlan_add rlo rhi.
Proof using TL ASTRCMP AMEMSET ASTRNCPY.
intros rlo rhi. unfold reac_declared_vlan_add_contract.
intros ly S W regs mem md ch tab max n par vid t p HPRE HROD H10 Rtab H11 Rmax H12 Rn H13 Rpar H14 Rvid HADD HEV.
exact (vad_all ly S W regs mem md ch rlo rhi tab max n par vid t p HPRE HROD H10 H11 H12 H13 H14 HADD).
Qed.
End e.
End d.
End b.
