(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma vw_sub : forall (C : (word -> option byte) -> Prop) (W W' : list (Z * Z)) (m0 m1 : word -> option byte),
  (forall m, munch W m0 m -> C m) -> munch W m0 m1 -> sub_fp W' W -> (forall m, munch W' m1 m -> C m).
Proof.
  intros C W W' m0 m1 H MU SF m MU'. apply H.
  apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU').
Qed.

(* [comment removed for export] *)
Definition sm_hi (cx : cctx) (e : est) (CO FV : Z) (w1360 : word) (totc gs : Z) : list cell :=
  let E := c_E cx in
  [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 999999999); C8 w1360; C8 (Z_to_bv 64 (flag6 (smA_ng e))); C8 (Z_to_bv 64 CO); C8 (Z_to_bv 64 FV);
   C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * smA_ng e)); C8 (Z_to_bv 64 (sm_alpha e));
   C8 (Z_to_bv 64 totc); C8 (Z_to_bv 64 gs)].

(* [comment removed for export] *)
Definition sm_loA (cx : cctx) (e : est) (FB SHF SHE : Z) (w16 w24 : word) : list cell :=
  let E := c_E cx in
  [C8 w16; C8 w24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 2147548970); C8 (Z_to_bv 64 784720);
   C8 (Z_to_bv 64 38998); C8 (Z_to_bv 64 38740); C8 (Z_to_bv 64 37708); C8 (Z_to_bv 64 51640); C8 (Z_to_bv 64 (flag6 (smA_ng e)));
   C8 (Z_to_bv 64 (4 * sm_alpha e)); C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 (Z_to_bv 64 E)].
Definition sm_loB (cx : cctx) (e : est) (SHE : Z) : list cell :=
  let E := c_E cx in
  [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (E + 51640)); C8 (Z_to_bv 64 (E + 668)); C8 (Z_to_bv 64 (SHE + 83)); C8 (Z_to_bv 64 (sm_alpha e));
   C8 (Z_to_bv 64 (smA_ng e)); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 (e_nInUse e))].

(* [comment removed for export] *)
Definition c100_bytes : list byte := Eval vm_compute in (match image_bytes a0segs 0x10368 8 with Some bs => bs | None => [] end).
Lemma c100_ro : forall m, mem_inv a0segs m -> bytes_at a0segs m 0x10368 c100_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image a0segs m 0x10368 c100_bytes MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ B].
  cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma c100_read : forall m, mem_inv a0segs m -> ov_read_bytes a0segs m (wa (0x10368 + 0)) 8 = Some c100_bytes.
Proof.
  intros m MI. rewrite (bytes_at_read a0segs m 0x10368 c100_bytes 0 8 (c100_ro m MI)) by (cbn; lia). reflexivity.
Qed.
Definition smF (F : bvmap 5 word) : bvmap 5 word := bvmap_set 8 (bv_extract 0 64 (le_bytes_to_word c100_bytes)) F.

(* [comment removed for export] *)
Definition sf1b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))).
Definition sf2b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-14))).
Definition sf3b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))).
Definition sf8b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8))).
(* [comment removed for export] *)
Definition sm_shadow : list cell :=
  [C1 sf1b; C1 sf1b; C1 sf1b; C1 sf1b; C1 z8; C1 (Z_to_bv 8 4); C1 sf2b; C1 sf2b; C1 z8; C1 z8; C1 z8; C1 sf2b; C1 sf2b; C1 sf2b; C1 sf2b; C1 sf2b;
   C1 sf8b; C1 sf3b; C1 sf3b; C1 sf3b].

End ACeilS1.
