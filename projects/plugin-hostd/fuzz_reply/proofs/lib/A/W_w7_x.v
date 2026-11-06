(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_cx_x.v, with its module paths and module names changed; 17 of its 50 lines of code are new or changed and 568 lines of the source are left out. *)
(* Generic (ARx) twins of donor lemmas the W7 walks use and the kit does not carry yet, shared by the drain and
   send_line conversions so that no walk file inlines its own copy.  Each is the cgif donor's proof over the
   generic laws. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface YGcallx.
Import ListNotations.
Open Scope Z_scope.

Section w7x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.

(* cgif YCbq.v:2587 sep_blocks_perm, over sep_blocks_pos_x (YGcallx.v:422) *)
Lemma sep_blocks_perm_x : forall ly S Hp W mem md x y l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- assert (Hd : zdisjoint (block_rng y) (block_rng x)).
  { eapply (sep_blocks_pos_x segs B ARx LAWS ly S Hp W mem md y x b1 b2 a2 HAR).
    rewrite E1, E2, <- app_assoc. reflexivity. }
  unfold zdisjoint in *. lia.
- eapply (sep_blocks_pos_x segs B ARx LAWS ly S Hp W mem md x y a1 b1 b2 HAR).
  rewrite E1, E2. reflexivity.
Qed.

(* a live block's request size is at least 1.  cgif's blocks law ends with `0 <= n < MALLOC_MAX` (YG0d.v:441), which
   the generic ARx_blocks_law (YCbqG.v:53) drops; the shadow law over an empty range gives it, as YCbqG.v:373-376
   (blk_off_band_x) argues. *)
Lemma blk_req_pos_x : forall ly S Hp W mem md p n,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 1 <= req_size n.
Proof.
intros ly S Hp W mem md p n HAR Hin.
destruct (Z_lt_le_dec 0 (req_size n)) as [Q|Q]; [lia|]. exfalso.
destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md p n HAR Hin ltac:(intros h _ Hh; lia)) as [(_ & Q0 & _) _].
revert Q Q0. unfold req_size. destruct (Z.eqb_spec n 0); cbv beta iota; intros; lia.
Qed.
End w7x.
