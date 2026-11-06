(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): SEGMENT L7 of the walk of
   LLVMFuzzerTestOneInput (B' 0x816cc), THE COMPOSITION. Proves entry_B_of_segs_stmt of the B' cut file
   lib/AU/Ent102CutsB.v: the thirteen segment statements, chained, are the walk from cut_start to cut_ret. PORTED by
   port/a2b.py (sha256 f5113cbc90e503da) from lib/A/Prog/Ent102L7A.v (L7Lane's Qed proof on A'); the chain is the same
   graph, since the two bodies differ only in pc-relative fields.
   - LISTING: lib/B/Listing_prog.v 8bcc2c9e7809. This file reads no slot of it: the composition is generic over the
     listing class ({L} {PA : PAImg L}), so it holds at L := B_prog_listing with the PAListing of lib/B/Ent102PLB.v
     by instantiation of its implicit arguments.
   - The kit TEXTS (reached only through the cut file's statements; no text is opened here): PRH_Base.v 016934fdc1af,
     PRH_FnCheck.v 1b4213c5f76f, PRH_FnAlloc.v 006c7e1ef8e6, PRH_FnPj.v 50f4781cadb9.
   - Template: lib/B/EntryCutsB.v entry_B_of_segs (a working branch fbe3888c3879), its eb_bind; this
     cut graph has no loop, so SRr_bind (YA0n.v:41) and the case split of the branching posts are all it uses.
   THE GRAPH: start -> frame (L0a, exists fk) -> s1 | exit (L0b) -> cno (L1) -> pno | exit (L2) -> caw | free (L3)
   -> free | crs0 | acc (L4, exists t D); crs0 -> exit (L4j); acc -> rm (L5a) -> crt (L5b) -> free | crs1 (L5c);
   crs1 -> free (L5d); free -> exit (L6f); exit -> ret (L6x). Every cut after L0a is at the same fk.
   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes + the internal lemma index / proof-index LLVMFuzzerTestOneInput exit=0, checker
   CONFIRM; NEW walk on the #102 pins), segment L7 (the composition). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

Section L7.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : @PAImg rc L}.
Local Notation segs := (@pa_segs rc L PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable EC_RA : Z.
Variable EC_EMPTY : Z.
Variables EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
(* the per-cut count and live-bytes budgets (the cut file's two MARKED functions; ec_hyps carries their laws) *)
Variable ec_ccut : ecx -> nat -> Z.
Variable ec_lcut : ecx -> nat -> Z.
(* the lanes from L1 on are at wle' over the fixed zone (Ent102CutsB.v ec_laneR WLE') *)
Local Notation WLE' := (wle' segs (@YGcfRehidePost.RZ_cf rc)).

(* two lanes in a row are one lane (YA0nH.SRrG_bind at the transitive wle', YA0nH.v:155) *)
Lemma ec_bind {P Q R : world segs -> config -> Prop} :
  ec_laneR WLE' P Q -> ec_laneR WLE' Q R -> ec_laneR WLE' P R.
Proof.
unfold ec_laneR. intros H1 H2 W c HP.
eapply (SRrG_bind segs WLE' (wle'_trans segs _)); [exact (H1 W c HP)|].
intros W' c' _ HQ. exact (H2 W' c' HQ).
Qed.

(* a branching post: each arm's lane to the same end is a lane from the disjunction *)
Lemma ec_or {Rel : world segs -> world segs -> Prop} {P1 P2 R : world segs -> config -> Prop} :
  ec_laneR Rel P1 R -> ec_laneR Rel P2 R -> ec_laneR Rel (fun W c => P1 W c \/ P2 W c) R.
Proof.
unfold ec_laneR. intros H1 H2 W c [HP | HP]; [exact (H1 W c HP) | exact (H2 W c HP)].
Qed.

(* an existential post (L0a's fk, L4's t and D): a lane at every witness is a lane from the existential *)
Lemma ec_ex {A : Type} {Rel : world segs -> world segs -> Prop} {P : A -> world segs -> config -> Prop}
  {R : world segs -> config -> Prop} :
  (forall a, ec_laneR Rel (P a) R) -> ec_laneR Rel (fun W c => exists a, P a W c) R.
Proof.
unfold ec_laneR. intros H W c [a HP]. exact (H a W c HP).
Qed.

(* a lane from a stronger cut: the pre read through an implication (cut_exit at wle -> cut_exitR at wle') *)
Lemma ec_pre_lift {Rel : world segs -> world segs -> Prop} {P P' R : world segs -> config -> Prop} :
  ec_laneR Rel P' R -> (forall W c, P W c -> P' W c) -> ec_laneR Rel P R.
Proof.
unfold ec_laneR. intros H HPP W c HP. exact (H W c (HPP W c HP)).
Qed.

(* THE COMPOSITION, from the exit cut backwards. L0a / L0b are plain lanes (before any free), lifted by
   ec_lane_wle'; L0b's size-guard arm reaches cut_exit at wle, read at wle' by cut_exit_wle' before L6x. *)
Theorem entry_B_of_segs :
  @entry_B_of_segs_stmt fx rc ci cp PI RL L PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
intros L0a L0b L1 L2 L3 L4 L4j L5a L5b L5c L5d L6f L6x E HH.
assert (Texit := fun fk => L6x E fk HH).
(* L0b's size-guard arm: cut_exit at wle, read at wle' (cut_exit_wle') before L6x *)
assert (Texit0 := fun fk => ec_pre_lift (Texit fk) ltac:(intros ?W ?c ?Hc; apply cut_exit_wle'; exact Hc)).
assert (Tfree := fun fk => ec_bind (L6f E fk HH) (Texit fk)).
assert (Tcrs1 := fun fk t D => ec_bind (L5d E fk t D HH) (Tfree fk)).
assert (Tcrt := fun fk t D => ec_bind (L5c E fk t D HH) (ec_or (Tfree fk) (Tcrs1 fk t D))).
assert (Trm := fun fk t D => ec_bind (L5b E fk t D HH) (Tcrt fk t D)).
assert (Tacc := fun fk t D => ec_bind (L5a E fk t D HH) (Trm fk t D)).
assert (Tcrs0 := fun fk => ec_bind (L4j E fk HH) (Texit fk)).
assert (Tcaw := fun fk => ec_bind (L4 E fk HH)
  (ec_or (Tfree fk) (ec_or (Tcrs0 fk) (ec_ex (fun t => ec_ex (fun D => Tacc fk t D)))))).
assert (Tpno := fun fk => ec_bind (L3 E fk HH) (ec_or (Tcaw fk) (Tfree fk))).
assert (Tcno := fun fk => ec_bind (L2 E fk HH) (ec_or (Tpno fk) (Texit fk))).
assert (Ts1 := fun fk => ec_bind (L1 E fk HH) (Tcno fk)).
assert (Tframe := fun fk => ec_bind (ec_lane_wle' _ _ (L0b E fk HH)) (ec_or (Ts1 fk) (Texit0 fk))).
exact (ec_bind (ec_lane_wle' _ _ (L0a E HH)) (ec_ex Tframe)).
Qed.

End L7.

About entry_B_of_segs.
Print Assumptions entry_B_of_segs.
