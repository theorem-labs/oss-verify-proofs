(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AF0x.v, with its module paths changed; 18 of its 75 lines of code are new or changed and 516 lines of the source are left out. *)
(* copy of proofs/cgif/cgif_file_fuzzer/lib/ImgBase.v@aa322d8bb0b; do not edit. Only this line is added, and the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable. *)
(* The image-free base of the R2 interfaces (AGif0n / AGif2 / AGif4 / DGif0 / DMiface / DMspec).

   - [AImg]: ONE class that holds every fact about the binary's image the interfaces name.  An interface takes it as
     [Context {IM : AImg}], so a consumer's explicit arguments do not move; the image file of a binary declares the
     instance (cgif_file: AGif2cgif.AImg_cgif).  A field is added here when an interface first needs it.
   - image-free copies of the cell / byte helpers the interfaces borrow from YF0x, over a segment list [segs] in place
     of cgif's.  aexp_eqb / cell_lookup / cell_lookup_In / le_byte_eq are verbatim copies: each copy and its YF0x
     original are convertible, so the walk files and their proofs are untouched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image.                                                                                                       *)
Class AImg : Type := MkAImg {
  (* the loaded segments of the binary *)
  im_segs : list Segment;
  (* the data cells: the thread pointer, the TSD slot, the out-of-memory byte, errno *)
  im_tp : Z; im_tsd : Z; im_oom : Z; im_errno : Z;
  (* the layout's image window covers the binary's image *)
  im_img_cover : alayout -> Prop;
  (* the symbol facts of the binary, and its constant cells *)
  im_syms : asyms -> Prop;
  im_const : alayout -> list acell;
  im_const_eq : forall B ly, im_syms B -> as_const B ly = im_const ly
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cell / byte helpers, over any segment list.  [copy of] = byte-identical (imgcopy-check.py checks it);       *)
(* [generalised from] = the original's text with its segment list tfibsegs replaced by the section variable segs.  *)
(* copy of YF0x.v:87, remove when YF0x.v is ported *)
Lemma le_byte_eq : forall z w k, YG0f.le_byte z w k = YO0f.le_byte z w k.
Proof. reflexivity. Qed.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* generalised from YF0x.v:89 (tfibsegs -> segs; Local), remove when YF0x.v is ported *)
Local Lemma aview_some : forall H mem a v,
aview segs H mem a = Some v <-> exists b, mbyte segs (mrestrict H mem) a = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v. unfold aview. destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn.
- split; [intros E; injection E as <-; exists b; auto | intros (b' & E & <-); congruence].
- split; [discriminate | intros (b & E & _); discriminate].
Qed.
(* generalised from YF0x.v:96 (tfibsegs -> segs; Local), remove when YF0x.v is ported *)
Local Lemma aview_byte : forall H mem a v,
aview segs H mem a = Some v -> mbyte segs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. apply aview_some in Hv as (b & E & <-). rewrite Z_to_bv_bv_unsigned. exact E.
Qed.
(* generalised from YF0x.v:105 (tfibsegs -> segs), remove when YF0x.v is ported *)
Lemma cell_holds_val_mem : forall B ly H mem e (w : nat) e',
cell_holds B ly (aview segs H mem) (ACell e w (AV e')) ->
val_mem segs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros B ly H mem e w e' Hc k Hk. cbn [cell_holds c_at c_val c_w] in Hc.
rewrite <- le_byte_eq. apply aview_byte. exact (Hc k Hk).
Qed.
(* generalised from YF0x.v:138 (tfibsegs -> segs), remove when YF0x.v is ported *)
Lemma apresent_mbyte : forall (H : word -> bool) mem a,
apresent H mem a -> exists b, mbyte segs (mrestrict H mem) a = Some b.
Proof.
intros H mem a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.
End g.
(* copy of YF0x.v:183, remove when YF0x.v is ported *)
Fixpoint aexp_eqb (a b : aexp) : bool :=
match a, b with
| ANum x, ANum y => x =? y
| ASp x, ASp y => x =? y | AQ x, AQ y => x =? y | AT x, AT y => x =? y | AC x, AC y => x =? y
| AF x, AF y => x =? y | ANB x, ANB y => x =? y | ASB x, ASB y => x =? y
| ASec r x, ASec s y => Nat.eqb r s && (x =? y)
| ATop x, ATop y => x =? y | ATsd x, ATsd y => x =? y | AStk x, AStk y => x =? y
| AInst x, AInst y => x =? y | ADepot x, ADepot y => x =? y | AStore x, AStore y => x =? y
| ATp x, ATp y => x =? y | AIal x, AIal y => x =? y | AD x, AD y => x =? y
| ASh a', ASh b' => aexp_eqb a' b'
| _, _ => false
end.
(* copy of YF0x.v:195, remove when YF0x.v is ported *)
Fixpoint cell_lookup (l : list acell) (e : aexp) : option acell :=
match l with
| [] => None
| c :: t => if aexp_eqb (c_at c) e then Some c else cell_lookup t e
end.
(* copy of YF0x.v:200, remove when YF0x.v is ported *)
Lemma cell_lookup_In : forall l e c, cell_lookup l e = Some c -> In c l.
Proof.
induction l as [|x t IH]; intros e c H; cbn in H; [discriminate|].
destruct (aexp_eqb (c_at x) e); [injection H as ->; left; reflexivity | right; exact (IH e c H)].
Qed.
