(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/ErrnoGcf.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset (a Theorem Labs lane): the AllocG / DeallocG-dependent part of cgif's ErrnoG.v
   (this unit's whole copy is lib/Reusable/ErrnoG.v; cgif's at e8a7dd66acf2, file sha256 27b3f11ecf13, as history; first taken from blob
   0ece417fd908 at 271c6736b71, then given cgif's MP edits by line 3), taken by path: ErrnoG.v:59-231 (cgif :58-230), its Section a, one block under the
   copy line below, byte for byte (no module prefix occurs in it):
   - errno_kept and errno_kept_v (the raw and the view form);
   - Allocate: alloc_leaf_e, aalloc_prim_realizes_e, aalloc_realizes_e and their bridges (alloc_leaf_e_alloc_leaf,
     aalloc_prim_realizes_e_aalloc_prim_realizes, aalloc_realizes_e_aalloc_realizes);
   - Deallocate: the view forms dealloc_leaf_e / adealloc_realizes_e and the raw forms dealloc_leaf_raw_e /
     adealloc_realizes_raw_e, with their bridges (dealloc_leaf_e_dealloc_leaf, adealloc_realizes_e_adealloc_realizes,
     dealloc_leaf_raw_e_raw, adealloc_realizes_raw_e_raw).
   The view forms (here :46-47, 141-159, 181-194) were added on 2026-10-29 for MemnormT.v (by path from
   29b7505aa27), whose dealloc_leaf_em / adealloc_realizes_em / dealloc_leaf_em_e name ErrnoG.errno_kept_v and
   ErrnoG.dealloc_leaf_e; every definition of the earlier blocks is unchanged.  Not copied: the cgif-interface part
   (DIfaceE / DIfaceRE / AIfaceE / AIfaceME and their add-ons, ErrnoG.v:233-543).
   This unit's AllocG.v / DeallocG.v are cgif's by path (AllocG.v blob 8afdeb6e04ae at 271c6736b71 and e8a7dd66acf2,
   DeallocG.v blob 82ecb426078e at e8a7dd66acf2, as history), equal except the module prefix and the copy line, so the copied text takes
   AllocG's / DeallocG's arguments unchanged.  The Require lines are this unit's (AllocG's, plus AllocG DeallocG).
   No function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.


(* copy of lib/Reusable/ErrnoG.v:59-231 byte for byte (cgif's ErrnoG.v at e8a7dd66acf2, lines 58-230, as history) *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* errno's 4 bytes (at [as_errno B], the address ascratch excludes) are the same in [mem'] as in [mem]: on the raw
   memory (the form of alloc_post's and dealloc_post_raw's raw frames) and on the view (the form of dealloc_post's
   frame). *)
Definition errno_kept (B : asyms) (mem mem' : word -> option byte) : Prop :=
forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i)).
Definition errno_kept_v (segs : list Segment) (B : asyms) (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
forall a, as_errno B <= a < as_errno B + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Allocate: AllocG's section variables, in AllocG's order, so that the twins take AllocG's arguments.              *)
Section al.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable pcA : Z.
Variable oomb : Z.
Variable al : Z.
Variable atp : Z.
Variable cf : Z.

(* AllocG.alloc_leaf, with errno kept on the grant branch (next to alloc_post's memory facts). *)
Definition alloc_leaf_e (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
alloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
(fst r <> PNull -> errno_kept B mem mem') /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) /\
(fst r = PNull -> val_mem segs (mrestrict (w_H W') mem') oomb 1 1).

(* AllocG.aalloc_prim_realizes over alloc_leaf_e. *)
Definition aalloc_prim_realizes_e : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr -> n <= 64512 ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf_e inst ly S W regs mem md n tr).

(* AllocG.aalloc_realizes over alloc_leaf_e. *)
Definition aalloc_realizes_e : Prop :=
forall inst so bp ly S W regs mem md n tr,
alloc_pre segs B U ARX rpre nmax lmax al atp cf inst so bp ly S W regs mem md n tr ->
amreal segs (mt n tr S) W (cfg_at segs pcA regs mem md)
(alloc_leaf_e inst ly S W regs mem md n tr).

Lemma alloc_leaf_e_alloc_leaf : forall inst ly S W regs mem md n tr r W' c',
alloc_leaf_e inst ly S W regs mem md n tr r W' c' ->
alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HR & HL & HT & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HL|].
split; [exact HT | exact HO].
Qed.

Lemma aalloc_prim_realizes_e_aalloc_prim_realizes : aalloc_prim_realizes_e ->
aalloc_prim_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros H inst so bp ly S W regs mem md n tr P N.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P N)]; exact (alloc_leaf_e_alloc_leaf inst ly S W regs mem md n tr).
Qed.

Lemma aalloc_realizes_e_aalloc_realizes : aalloc_realizes_e ->
aalloc_realizes segs B U mt ARX AOX rpre nmax lmax lpost pcA oomb al atp cf.
Proof.
intros H inst so bp ly S W regs mem md n tr P.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md n tr P)]; exact (alloc_leaf_e_alloc_leaf inst ly S W regs mem md n tr).
Qed.
End al.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Deallocate: DeallocG's section variables, in DeallocG's order.                                                   *)
Section dl.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable pcD : Z.
Variable atp : Z.
Variable MP : (word -> option byte) -> Prop.

(* DeallocG.dealloc_leaf (the view form), with errno kept on the view (every branch: NULL and live block). *)
Definition dealloc_leaf_e (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
errno_kept_v segs B W W' mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* DeallocG.adealloc_realizes over dealloc_leaf_e. *)
Definition adealloc_realizes_e : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md)
(dealloc_leaf_e inst ly S W regs mem md p n tr).

(* DeallocG.dealloc_leaf_raw, with errno kept on the raw memory (every branch: NULL and live block). *)
Definition dealloc_leaf_raw_e (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
dealloc_post_raw segs B ARX AOX inst ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
ly' (snd r) W' regs' mem' md' /\
errno_kept B mem mem' /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

(* DeallocG.adealloc_realizes_raw over dealloc_leaf_raw_e. *)
Definition adealloc_realizes_raw_e : Prop :=
forall inst so bp ly S W regs mem md p n tr,
dealloc_pre segs B U ARX rpre fpre atp inst so bp ly S W regs mem md p n tr -> MP mem ->
amreal segs (ft p tr S) W (cfg_at segs pcD regs mem md)
(dealloc_leaf_raw_e inst ly S W regs mem md p n tr).

Lemma dealloc_leaf_e_dealloc_leaf : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_e inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HL | exact HT].
Qed.

Lemma adealloc_realizes_e_adealloc_realizes : adealloc_realizes_e ->
adealloc_realizes segs B U ft ARX AOX rpre lpost fpre pcD atp MP.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)]; exact (dealloc_leaf_e_dealloc_leaf inst ly S W regs mem md p n tr).
Qed.

Lemma dealloc_leaf_raw_e_raw : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_raw_e inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_raw segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HL | exact HT].
Qed.

Lemma adealloc_realizes_raw_e_raw : adealloc_realizes_raw_e ->
adealloc_realizes_raw segs B U ft ARX AOX rpre lpost fpre pcD atp MP.
Proof.
intros H inst so bp ly S W regs mem md p n tr P HMP.
eapply amreal_mono; [| exact (H inst so bp ly S W regs mem md p n tr P HMP)]; exact (dealloc_leaf_raw_e_raw inst ly S W regs mem md p n tr).
Qed.
End dl.
End a.
