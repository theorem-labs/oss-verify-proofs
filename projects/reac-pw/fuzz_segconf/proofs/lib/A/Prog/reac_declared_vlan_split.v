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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/trim.v, with its module paths and module names changed; 45 of its 66 lines of code are new or changed and 18 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image A (0x89b8c = BASE + AF_reac_declared_vlan_split): the walk against
   reac_declared_vlan_split_contract (lib/A/Prog/reac_declared_vlan_split_c.v), at SegInstA's image-A numbers.
   proves function reac_declared_vlan_split (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates,
   origin/release/pau-projects-recipes and the working-branch lemma and live-head indexes /
   the stream's proof index reac_declared_vlan_split): none released; written new in the form
   of plugin-hostd/fuzz_command's lib/A/Prog walks (origin/ossv/recipes 501c0d516c69).

   The walk is a chain of program points (reac_declared_vlan_split_d.v), each stated over the concrete state there:
     entry  -> K1 (after the strrchr wrapper)            reac_declared_vlan_split_a.v  vs_entry_walk
     K1     -> KL 0 / KR (the dot tests)                 reac_declared_vlan_split_l.v  vs_K1
     KL j   -> KL (j + 1) / K2 / KR (the digit loop)     reac_declared_vlan_split_l.v  vs_KL_all
     K2     -> K3 (the strtol wrapper)                    reac_declared_vlan_split_a.v  vs_K2
     K3     -> K4 / KR (the range and plen tests, strlen) reac_declared_vlan_split_b.v  vs_K3
     K4     -> K5 (the length test, the checked memcpy)   reac_declared_vlan_split_b.v  vs_K4
     K5     -> K6 (the NUL store, name_ok)                reac_declared_vlan_split_s5.v vs_K5
     K6     -> KR (the vid store)                         reac_declared_vlan_split_s6.v vs_K6
     KR     -> the return (the epilogue)                  reac_declared_vlan_split_r.v  vs_KR
   The Section hypotheses are the callee contract (name_ok's), the wrapper contracts (strrchr, strtol with a NULL end
   pointer, strlen), the checked memcpy, the record (PALib B, errno_rom), and the listing's two facts seg_sig_prog and
   seg_val_relro, which the close discharges at image A's instance. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0q YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c name_ok_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_a reac_declared_vlan_split_b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_s5 reac_declared_vlan_split_s6.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.
(* the record *)
Hypothesis TL : PALib B.
Hypothesis ERRNO : errno_rom SEGS B.
(* the listing's facts at the instance: every program function's call target is its entry; the relro range *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : seg_val_relro.
(* the wrappers (the interceptor layer's interface rows 11, 3 and 16) and the checked memcpy *)
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis ASTRTOL0 : forall fx0 : YK11.FPState,
  @RtSeg.astrtol0_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strtol) gotwA guardA.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
(* the callee *)
Hypothesis NAMEOK : name_ok_contract SEGS B (BASE + AF_name_ok) STK_name_ok RLO_A RHI_A.

Theorem reac_declared_vlan_split_walk :
  reac_declared_vlan_split_contract SEGS B (BASE + AF_reac_declared_vlan_split) STK_reac_declared_vlan_split
    RLO_A RHI_A gotwA guardA.
Proof using TL ERRNO SIGP RELRO ASTRRCHR ASTRTOL0 ASTRLEN AMEMCPY NAMEOK.
unfold reac_declared_vlan_split_contract.
intros ly S W regs mem md ch segment parent cap vid s HPRE HROD H10 B10 H11 B11 H12 B12 H13 B13 HSP HEV.
pose proof HSP as (_ & _ & _ & _ & _ & _ & _ & Hcap & _). subst cap.
assert (HE : vs_entry B gotwA guardA (mkVsE ly S W regs mem md ch segment parent vid s)).
{ unfold vs_entry. cbn [e_ly e_S e_W e_regs e_mem e_md e_ch e_seg e_parent e_vid e_s].
  unfold EV_reac_declared_vlan_split in HEV.
  split; [exact HPRE|]. split; [exact HROD|]. split; [exact H10|]. split; [exact B10|]. split; [exact H11|].
  split; [exact B11|]. split; [exact H12|]. split; [exact H13|]. split; [exact B13|]. split; [exact HSP | lia]. }
assert (GW : 0 <= gotwA /\ gotwA + 8 <= alloc_ceiling /\ 0 <= guardA /\ guardA + 8 <= alloc_ceiling)
  by (pose proof asan_consts as (C1 & _); unfold gotwA, guardA, alloc_ceiling in *; lia).
pose proof (vs_KR B gotwA guardA) as KR.
pose proof (vs_K6 B gotwA guardA KR) as K6.
pose proof (vs_K5 B gotwA guardA SIGP RELRO NAMEOK K6) as K5.
pose proof (vs_K4 B gotwA guardA AMEMCPY K5) as K4.
pose proof (vs_K3 B gotwA guardA TL ASTRLEN KR K4) as K3.
pose proof (vs_K2 B gotwA guardA TL ERRNO ASTRTOL0 GW K3) as K2.
pose proof (vs_K1 B gotwA guardA KR K2) as K1.
exact (vs_entry_walk B gotwA guardA TL ASTRRCHR K1 (mkVsE ly S W regs mem md ch segment parent vid s) HE).
Qed.
End e.
End f.
End d.
