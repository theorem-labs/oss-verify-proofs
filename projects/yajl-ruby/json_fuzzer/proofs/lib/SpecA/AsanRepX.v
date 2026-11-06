(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RX.
Variable segs : list Segment.
Variable E : aenv.
Variable DepotR : astate -> (word -> option byte) -> Prop.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Definition arep_shadow_but (blo bhi : Z) (s : astate) (m : mem) : Prop :=
  forall g v, Sh E s (8 * g) = Some v -> (8 * g + 8 <= blo \/ bhi <= 8 * g) -> rw_cells segs m (kShadowBase + g) [C1 (zb v)].

Definition ARepX (s : astate) (m : mem) (blo bhi : Z) : Prop :=
  arep_instance segs E s m /\ arep_regioninfo segs E s m /\ arep_region_mem segs E s m /\ arep_thread segs E s m
  /\ arep_secondary segs E s m /\ arep_chunks segs s m /\ arep_batches segs s m /\ arep_depot DepotR s m
  /\ arep_globals segs E s m /\ arep_shadow_but blo bhi s m.

Lemma ARep_ARepX : forall s m blo bhi, ARep segs E DepotR s m -> ARepX s m blo bhi.
Proof.
  intros s m blo bhi (A & B & C & D & F & G & H & I & J & K). repeat (split; [assumption|]). intros g v Hg _. exact (K g v Hg).
Qed.

Lemma ARepX_ARep : forall s m blo bhi, ARepX s m blo bhi ->
  (forall g v, Sh E s (8 * g) = Some v -> blo < 8 * g + 8 -> 8 * g < bhi -> rw_cells segs m (kShadowBase + g) [C1 (zb v)]) ->
  ARep segs E DepotR s m.
Proof.
  intros s m blo bhi (A & B & C & D & F & G & H & I & J & K) SH. repeat (split; [assumption|]).
  intros g v Hg. destruct (Z_le_gt_dec (8 * g + 8) blo); [apply K; [exact Hg| left; lia]|].
  destruct (Z_le_gt_dec bhi (8 * g)); [apply K; [exact Hg| right; lia]|]. apply SH; [exact Hg| lia| lia].
Qed.
End RX.
End RC__1.
