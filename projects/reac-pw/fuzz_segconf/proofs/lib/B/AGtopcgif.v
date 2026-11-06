(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGin.v (commit 95e6f1d72b6, file sha256 1d6276651a2a; written for cgif_file_fuzzer.asan-ubsan 1c29845fe605) onto libreac/fuzz_decode's asan image (pin 5973b76807d8, unstripped twin 4cb0a852e826); module paths changed, names TfibSyms -> GrantSyms; its 22 image addresses moved by code-verified function pairs (20 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 2 hand maps (agreloc-resolve.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/AGin.v, with its module paths and module names changed; 60 of its 92 lines of code are new or changed and 802 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGtopcgif.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 6ff42c6f54dc) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 3 image addresses moved by code-verified function pairs (3 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: Section d's trace premise UC is fs's instance U `fun tr S => tr_admit (as_universe B) S tr` (the U of AGif1.iface_cgif / AGif1k.iface_cgif_k at fs, FS-INSTANCE.md 1.4, and of AllocGcgif.aalloc_prim_realizes_cgif). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGtopcgif.v (donor image sha256 64b53ff86172), with its module paths changed, names TfibSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AGtopcgif.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The dispatch of the primary-size Allocate over the c5 interface, and its cgif_file corollary.
   [aalloc_prim_realizes_if] (Section c, moved here from AGtop.v so that AGtop.v imports no cgif instance) applies
   AGtop.aalloc_prim_realizes_of_arms with the uninited-cache fact from AGif0n.if_uninit and the hit arms AGik.ARM_HITG /
   AGil.ARM_HITK; [aalloc_prim_realizes_cgif_g] is AllocGcgif.aalloc_prim_realizes_cgif at can_fill in {0, 1}, at cgif's
   instance (AGif1.iface_cgif, AGif1k.iface_cgif_k).  The two miss arms are premises until AGim / AGin land (they are
   proved over AIfaceM, which cgif instantiates by AGif1m.iface_cgif_m). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0l YF0m YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YGAlloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import AllocGcgif AGtop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require AGif0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require AGik AGil AGif1 AGif1k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Over the c5 interface, can_fill in {0, 1}. *)
Section c.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis IFK : AGif0n.AIfaceK B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : SegBSyms B.
Variable cf : Z.
Hypothesis HCF : cf = 0 \/ cf = 1.
Let GOALi (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (n : Z) (tr : list Z) : Prop :=
  amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x331a4 regs mem md)
    (alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Let PREi (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z) : Prop :=
  alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr.
Hypothesis ARM_MISSGi : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PREi inst so bp ly S W regs mem md n tr -> 49 <= n <= 64512 ->
  pc_chunks (cache S (chunk_class n)) = [] -> GOALi inst ly S W regs mem md n tr.
Hypothesis ARM_MISSKi : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PREi inst so bp ly S W regs mem md n tr -> 0 <= n <= 48 ->
  pc_chunks (cache S (chunk_class n)) = [] -> GOALi inst ly S W regs mem md n tr.
Theorem aalloc_prim_realizes_if :
  aalloc_prim_realizes tfibsegs B U mt ARX AOX rpre nmax lmax lpost 0x331a4 TFIB_OOM 8 1 cf.
Proof.
apply (aalloc_prim_realizes_of_arms B U mt ARX AOX rpre nmax lmax lpost TFIB_OOM cf HCF);
  [| | | exact ARM_MISSGi | exact ARM_MISSKi].
- intros inst ly S W mem md c HA Hc CI. eapply AGif0n.if_uninit; [exact IF | exact HA | exact Hc | exact CI].
- intros inst so bp ly S W regs mem md n tr l off _ HPRE Hn CI El.
  eapply AGik.ARM_HITG; eassumption.
- intros inst so bp ly S W regs mem md n tr l off _ HPRE Hn CI El.
  eapply AGil.ARM_HITK; eassumption.
Qed.
End c.
Section d.
Variable B : asyms.
Hypothesis TS : SegBSyms B.
Hypothesis HD1 : tfib_depot_spec B.
Variable cf : Z.
Hypothesis HCF : cf = 0 \/ cf = 1.
Let UC : list Z -> astate -> Prop := fun tr S => tr_admit (as_universe B) S tr.
Let GOALc (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (n : Z) (tr : list Z) : Prop :=
  amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x331a4 regs mem md)
    (alloc_leaf tfibsegs B malloc (ARX_cgif B) (aowned B) qtight TFIB_OOM inst ly S W regs mem md n tr).
Let PREc (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z) : Prop :=
  alloc_pre tfibsegs B UC (ARX_cgif B) rpre_cgif MALLOC_MAX LIVE_MAX 8 1 cf inst so bp ly S W regs mem md n tr.
Hypothesis ARM_MISSGc : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PREc inst so bp ly S W regs mem md n tr -> 49 <= n <= 64512 ->
  pc_chunks (cache S (chunk_class n)) = [] -> GOALc inst ly S W regs mem md n tr.
Hypothesis ARM_MISSKc : forall inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
  PREc inst so bp ly S W regs mem md n tr -> 0 <= n <= 48 ->
  pc_chunks (cache S (chunk_class n)) = [] -> GOALc inst ly S W regs mem md n tr.
Theorem aalloc_prim_realizes_cgif_g : aalloc_prim_realizes_cgif B cf.
Proof.
exact (aalloc_prim_realizes_if B UC malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX qtight (AGif1.dpost_cgif B)
  202260 449860 (AGif1.iface_cgif B TS HD1) (AGif1k.iface_cgif_k B TS HD1) TS cf HCF ARM_MISSGc ARM_MISSKc).
Qed.
End d.
End a.
