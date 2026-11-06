(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the user-poisoned-heads form of the asan state (unpoison, ARU, ecall_preU and their U = []
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/UPoison.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
   lemmas), taken by path from proofs/omx-clap-core/fuzz_state/lib/A/FSupoison.v:13-55, Section u only (a working branch
   7c46ddd1720; itself from a Theorem Labs lane's FMupoison.v, a working branch 7ba11794c88, design/POISON.md), into the shared core,
   module prefix only. The frame lemmas of FSupoison's Section l are not taken: the strcmp U form (AStrcmpDefU.v) needs only
   these definitions and the three _nil lemmas. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* User-poisoned granules inside live chunks (fuzz/alloc.c poisons a 16-byte head in each block it gets from
   malloc). The donor's AR fixes every chunk granule's shadow byte to the allocator's value; ARU is AR of the memory
   read with the user-poisoned shadow bytes as 0, plus where those ranges are and that their shadow bytes read 0xf7.
   ARU with no range is AR (ARU_nil). Design: design/POISON.md of a Theorem Labs lane. *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
(* s is a shadow byte of one of the ranges U, each (p, len) a run of whole granules. *)
Definition in_ush (U : list (Z * Z)) (s : Z) : bool :=
existsb (fun r => (shadow_addr (fst r) <=? s) && (s <? shadow_addr (fst r) + snd r / 8)) U.
(* The memory as the allocator made it: the user-poisoned shadow bytes read 0. *)
Definition unpoison (U : list (Z * Z)) (mem : word -> option byte) : word -> option byte :=
fun w => if in_ush U (bv_unsigned w) then Some (Z_to_bv 8 0) else mem w.
(* Each range is granule-aligned, in the whole user granules of a live block, and the ranges are disjoint. *)
Definition upoison_ok (ly : alayout) (S : astate) (U : list (Z * Z)) : Prop :=
Forall (fun r => fst r mod 8 = 0 /\ 8 <= snd r /\ snd r mod 8 = 0 /\
exists p n, In (p, n) (ablocks B ly S) /\ p <= fst r /\ fst r + snd r <= p + 8 * (req_size n / 8)) U /\
pairwise zdisjoint U.
(* Their shadow bytes hold kAsanUserPoisonedMemoryMagic. *)
Definition upoisoned (W : world segs) (mem : word -> option byte) (U : list (Z * Z)) : Prop :=
forall s, in_ush U s = true -> aview segs (w_H W) mem s = Some 247.
Definition ARU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
(md : Model) : Prop :=
AR segs B ly S W (unpoison U mem) md /\ upoison_ok ly S U /\ upoisoned W mem U.
Lemma unpoison_nil : forall mem, unpoison [] mem = mem.
Proof. intros mem. reflexivity. Qed.
Lemma ARU_nil : forall ly S W mem md, ARU ly S [] W mem md <-> AR segs B ly S W mem md.
Proof.
intros ly S W mem md. unfold ARU. rewrite unpoison_nil. split.
- intros (H & _ & _). exact H.
- intros H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs.
Qed.
(* ecall_pre (YG0d.v) with ARU's memory. *)
Definition ecall_preU (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ecall_pre segs B ly S W regs (unpoison U mem) md /\ upoison_ok ly S U /\ upoisoned W mem U.
Lemma ecall_preU_nil : forall ly S W regs mem md, ecall_preU ly S [] W regs mem md <-> ecall_pre segs B ly S W regs mem md.
Proof.
intros ly S W regs mem md. unfold ecall_preU. rewrite unpoison_nil. split.
- intros (H & _ & _). exact H.
- intros H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs.
Qed.
End u.
(* Donor (provenance of this file, origin first): omx-clap-core/fuzz_manifest lib/A/FMupoison.v (file sha256 a007f182c793; donor not released). *)
(* Through omx-clap-core/fuzz_state lib/A/FSupoison.v Section u (file sha256 a4cc17690f96; released). *)
(* Then copied from libreac/fuzz_grant lib/Reusable/UPoison.v (file sha256 fcd79de5e144; donor not released), module paths changed. *)
