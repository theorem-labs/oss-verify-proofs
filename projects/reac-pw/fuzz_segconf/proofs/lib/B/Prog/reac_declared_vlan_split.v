(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4) on the ASan build of plugin-hostd/fuzz_command
   proves its statement tchain_words_spec (chain_words_c.v:94-134) directly: from the six segments and the transport
   (chain_words_a.v's cw_run), at statement passes 4 and 5 (the FP-existential post apost_baseF, the rounding-mode
   premise, no astack_pres). The returned block's size is exact in the statement
   (chain_words_c.v:127), as the walk's post cw_Q (chain_words_d.v) carries it from the two recorder callees. The
   callee contracts and runtime rules are the statement's, in its forall-fx0 form (chain_words_c.v:84-93); the
   per-binary facts the walk names are CmdRecFacts lemmas: relro_img and cmd_ro_ok_of_aro (CmdRecRo.v),
   cmd_prog_unowned (CmdRecImg.v), all over IMG : cmd_img_facts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_exact.v, with its module paths and module names changed; 20 of its 39 lines of code are new or changed and 65 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/trim.v, with its module paths and module names changed; 63 of its 85 lines of code are new or changed and 17 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca;
   entry 0x8a218 = BASE + AF_reac_declared_vlan_split, 496 bytes, 124 instructions): the walk, the image-B port of
   lib/A/Prog/reac_declared_vlan_split.v's design (commit ceb7e39832b2: its point interface
   _d.v, its kit _k.v, its helpers _h.v and _lem.v, KR in _r.v and K6 in _s6.v), with image B's UBSan arms.
   `reac_declared_vlan_split_walk` proves reac_declared_vlan_split_contract (lib/B/Prog/reac_declared_vlan_split_c.v,
   image B's copy of the FINAL contract 6f783602b5e3) at image B's numbers.

   The chain of points (_d.v), each segment proving its point's statement from the next ones':
     entry -> K1        _s0 (vs_K0: seed, the four beqz, the shadow base, the strrchr wrapper)
     K1 -> KL 0         _s1 (vs_K1: the dot arms, trap 0x8a28c, check C1, the first-byte arm)
     KL j -> KL (j + 1) _sl (vs_KL: the digit loop, trap 0x8a2c4, check C2; exit to K2)
     K2 -> K3           _s2 (vs_K2: the strtol wrapper)
     K3 -> K4           _s3 (vs_K3: the range test, the two plen tests, the strlen wrapper)
     K4 -> K5           _s4 (vs_K4: the len test, the checked memcpy)
     K5 -> K6           _s5 (vs_K5: trap 0x8a38c, check C3, the NUL store, name_ok)
     K6 -> KR           _s6 (vs_K6: trap 0x8a3b8, check C4, the vid store)
     KR                 _r  (vs_KR: the epilogue and apost_base)
   The UBSan trap `unimp` 0x8a3d8 is reached only by the four branches above (0x8a3d4 before it is `j 0x8a324`),
   each refuted at its branch from split_pre (the segment's, parent's and vid's sa_addr bounds below 2^63; vid
   mod 2 = 0).

   Image B's numbers this theorem is stated at, image B's instance file's (lib/B/Prog/SegInstB.v): STK =
   SegInstB.STK_reac_declared_vlan_split = 64 + 3 * ESTACK (named VS_STK in _k.v: the 64-byte frame above the strtol
   wrapper's window, the widest it calls); RLO / RHI = SegInstB.RLO_A / RHI_A (image B's SegGlob.SEG_RLO / SEG_RHI:
   0xa1c60, 0xa3f08); gotw = SegInstB.gotwA = 0xa3e98 (the GOT word musl's __strtol_internal loads at 0x9aa14,
   lib/B/Rt/RtSeg.v row 3), guard = SegInstB.guardA = 0x5ff838 (__stack_chk_guard, the word that GOT word holds:
   lib/B/Prog/SegRo.v RO_ptr_a3e98 = 38 f8 5f 00 00 00 00 00); name_ok's contract at SegInstB.STK_name_ok and
   RLO_A / RHI_A, the numbers name_ok's walk is stated at. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import name_ok_c reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_s6
  reac_declared_vlan_split_s5 reac_declared_vlan_split_s4 reac_declared_vlan_split_s3 reac_declared_vlan_split_s2
  reac_declared_vlan_split_sl reac_declared_vlan_split_s1 reac_declared_vlan_split_s0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's stack-protector cells (head comment), SegInstB's, under the names the proof below uses *)
#[local] Notation VS_GOTW_B := SegInstB.gotwA (only parsing).
#[local] Notation VS_GUARD_B := SegInstB.guardA (only parsing).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.
Hypothesis STRRCHR : forall fx0 : YK11.FPState, @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis STRTOL : forall fx0 : YK11.FPState,
  @RtSeg.astrtol0_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strtol) SegInstB.gotwA SegInstB.guardA.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis MEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis NAMEOK : name_ok_contract SEGS B (BASE + AF_name_ok) SegInstB.STK_name_ok SegInstB.RLO_A SegInstB.RHI_A.
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog.
Hypothesis ERR : errno_rom SEGS B.

Theorem reac_declared_vlan_split_walk :
  reac_declared_vlan_split_contract SEGS B (BASE + AF_reac_declared_vlan_split) SegInstB.STK_reac_declared_vlan_split
    SegInstB.RLO_A SegInstB.RHI_A SegInstB.gotwA SegInstB.guardA.
Proof using B ERR MEMCPY NAMEOK SIGP STRLEN STRRCHR STRTOL TL.
unfold reac_declared_vlan_split_contract.
intros ly S W regs mem md ch segment parent cap vid s HPRE HROD H10 R10 H11 R11 H12 R12 H13 R13 HSP HEV.
assert (Hcap : cap = 16) by (destruct HSP as (_ & _ & _ & _ & _ & _ & _ & Hc & _); exact Hc). subst cap.
set (e := mkVsE ly S W regs mem md ch segment parent vid s).
assert (HE : vs_entry B VS_GOTW_B VS_GUARD_B e).
{ unfold EV_reac_declared_vlan_split in HEV.
  exact (conj HPRE (conj HROD (conj H10 (conj R10 (conj H11 (conj R11 (conj H12 (conj H13 (conj R13
    (conj HSP (ltac:(lia) : st_nev S <= EV_MAX))))))))))). }
pose proof (vs_KR B VS_GOTW_B VS_GUARD_B) as HKR.
pose proof (vs_K6 B VS_GOTW_B VS_GUARD_B HKR) as HK6.
pose proof (vs_K5 B VS_GOTW_B VS_GUARD_B NAMEOK SIGP HK6) as HK5.
pose proof (vs_K4 B VS_GOTW_B VS_GUARD_B MEMCPY HKR HK5) as HK4.
pose proof (vs_K3 B VS_GOTW_B VS_GUARD_B STRLEN TL HKR HK4) as HK3.
pose proof (vs_K2 B VS_GOTW_B VS_GUARD_B STRTOL TL ERR
  ltac:(unfold VS_GOTW_B, VS_GUARD_B, kLowMemEnd; lia) HK3) as HK2.
pose proof (vs_KL B VS_GOTW_B VS_GUARD_B HKR HK2) as HKL.
pose proof (vs_K1 B VS_GOTW_B VS_GUARD_B HKR (HKL 0%nat)) as HK1.
exact (vs_K0 B VS_GOTW_B VS_GUARD_B STRRCHR TL HK1 e HE).
Qed.
End e.
End f.
End d.

Print Assumptions reac_declared_vlan_split_walk.
About reac_declared_vlan_split_walk.
