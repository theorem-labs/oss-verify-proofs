(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormDleaf.v (a working branch 29b7505aa27, file sha256 b9c6a5ed87b3) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (0 lines name this file); 0 numerals changed. *)
(* Theorem Labs, 2026-10 (task MEMNORM): the Deallocate arm leaf with memnorm kept, image-free (as DGleafE.v).
   rule 24: no function proved (kind: leaf definition and bridges).
   - [dealloc_leaf_raw_eem]: DGleafE.dealloc_leaf_raw_ee (DeallocG.dealloc_leaf_raw plus errno on the raw memory and on
     the view) plus `memnorm mem -> memnorm mem'` (MemnormT.memnorm_keep), inside the same existential: the leaf of
     the NULL and common arm twins (MemnormDnull.v, MemnormDcommon.v);
   - the bridges: to DGleafE.dealloc_leaf_raw_ee (drop the keep), to MemnormT.dealloc_leaf_raw_em (the raw top
     twin's leaf) and to MemnormT.dealloc_leaf_em (the view top twin's leaf), and the keep by projection. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG DGleafE MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.

Section b.
Variable B : asyms.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable lpost : astate -> Prop.

(* DGleafE.dealloc_leaf_raw_ee with the keep *)
Definition dealloc_leaf_raw_eem (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
dealloc_post_raw im_segs B ARX AOX inst ly S W regs mem md
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
ErrnoG.errno_kept B mem mem' /\
ErrnoG.errno_kept_v im_segs B W W' mem mem' /\
MemnormT.memnorm_keep im_segs mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Lemma leaf_raw_eem_ee : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_eem inst ly S W regs mem md p n tr r W' c' ->
  DGleafE.dealloc_leaf_raw_ee B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & HEv & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HEv|].
split; [exact HL | exact HT].
Qed.

Lemma leaf_raw_eem_raw_em : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_eem inst ly S W regs mem md p n tr r W' c' ->
  MemnormT.dealloc_leaf_raw_em im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & _ & HK & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HK|].
split; [exact HL | exact HT].
Qed.

Lemma leaf_raw_eem_em : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_eem inst ly S W regs mem md p n tr r W' c' ->
  MemnormT.dealloc_leaf_em im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HEv & HK & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|].
split; [exact (MemnormT.dealloc_post_raw_post im_segs B ARX AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP)|].
split; [exact HEv|]. split; [exact HK|]. split; [exact HL | exact HT].
Qed.

Lemma leaf_raw_eem_keep : forall inst ly S W regs mem md p n tr r W' c',
  dealloc_leaf_raw_eem inst ly S W regs mem md p n tr r W' c' ->
  exists regs' mem' md', c' = cfg_at im_segs (raZ regs) regs' mem' md' /\ MemnormT.memnorm_keep im_segs mem mem'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & _ & _ & _ & HK & _).
exists regs', mem', md'. exact (conj Hc HK).
Qed.
End b.
End a.
