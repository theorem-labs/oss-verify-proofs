(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YG0t.v, with its module paths changed; 1 of its 841 lines of code is new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-10: EV_MAX raised to 11776, as in omx-clap-core/fuzz_manifest's copy of this file; the proof unfolds kFreeArrayOffset in the primary-chunk bound of cfacts, which replaced 2 ^ 31. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YG0t.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG05_w YG0s_w YG0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section u.
Variable segs : list Segment.
Variable B : asyms.
Lemma ashadow_app : forall ly S rd g v, ARm B ly S rd -> ashadow B ly S g = Some v -> 4096 <= g /\ g + 7 <= kHighMemEnd.
Proof.
intros ly S rd g v M H. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_high _ LO) as [P1 P2].
unfold ashadow in H. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg]. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & _).
assert (ck_extent k mod 8 = 0 /\ ck_base B ly k mod 8 = 0) as [E1 E2].
{ pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & G3 & _ & _ & _ & G7 & _ & GG). split; [|apply Z.mod_divide in G3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult].
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & -> & _). pose proof (class_ok (prim_class o) ltac:(lia)) as (_ & K2 & _).
apply Z.mod_divide in K2 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult.
- destruct GG as (_ & Gp & _ & -> & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (_ & _ & _ & _ & SM & _).
apply Z.mod_divide in SM as [q Hq]; [|unfold kPage; lia]. rewrite Hq. unfold kPage. replace (q * 4096 - 4096) with ((q * 512 - 512) * 8) by lia. apply Z_mod_mult. }
apply Z.mod_divide in E1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in E2 as [q2 Hq2]; [|lia]. destruct G1 as [G0 _].
ceil; unfold ASAN_CEIL, kHighMemEnd in *. split; [lia|]. clear - Hg Hq1 Hq2 G2 CR0. nia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (wr_mapped_al _ _ _ _ _ _ CL) as A4.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c (am_wf _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
apply Z.mod_divide in R3 as [q3 Hq3]; [|lia]. apply Z.mod_divide in A4 as [q4 Hq4]; [|lia].
ceil; unfold ASAN_CEIL, kHighMemEnd, kHighMemBeg, kPrimResvSize in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | nia]).
+ pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Hin) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
ceil; unfold YG0f.page_aligned, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg in *.
apply Z.mod_divide in PA as [q Hq]; [|lia]. split; [lia | clear - Hg Hq I2 I3 CR0; nia].
Qed.
Lemma ashadow_low : forall ly S rd g v, ARm B ly S rd -> ashadow B ly S g = Some v -> SHADOW_OFF <= shadow_addr g < kHighMemBeg.
Proof.
intros ly S rd g v M H. destruct (ashadow_app ly S rd g v M H) as [Ga Gb].
destruct (shadow_addr_bounds g ltac:(lia)) as [X Y]. split; [exact X | exact (Y Gb)].
Qed.
Lemma in_combine_seq_iff : forall {A} (l : list A) s i x, In (i, x) (combine (seq s (length l)) l) <-> (s <= i)%nat /\ nth_error l (i - s) = Some x.
Proof.
intros A l. induction l as [|y t IH]; intros s i x; cbn [length seq combine].
- split; [intros [] | intros [_ E]; destruct (i - s)%nat; discriminate E].
- split.
+ intros [E|H]; [injection E as <- <-; split; [lia | rewrite Nat.sub_diag; reflexivity]|].
apply IH in H as [H1 H2]. split; [lia|]. replace (i - s)%nat with (S (i - S s))%nat by lia. exact H2.
+ intros [H1 H2]. destruct (Nat.eq_dec i s) as [->|Hne].
* left. rewrite Nat.sub_diag in H2. injection H2 as ->. reflexivity.
* right. apply IH. split; [lia|]. replace (i - S s)%nat with (Nat.pred (i - s)) by lia. destruct (i - s)%nat eqn:E; [lia|]. cbn. exact H2.
Qed.
End u.
End j.
