(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE22.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (2 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: the GOT canary cell z8 0x9e658 0x5f94b0 is found in the generated A/AF0m.v Tfib_const_abs by search, not at the donor's fixed position 193. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE22.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP0m YP09 YI04 YK04 YA0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import AF0x_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE20.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import AE2y_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_GOT_CANARY : Z := 0x9e658.
Definition V_GOT_CANARY : Z := 0x5f94b0.
Definition is_canary_region (r : YP09.region) : bool :=
match YP09.r_base r with
| None => ((YP09.r_lo r =? A_GOT_CANARY) && (YP09.r_hi r =? A_GOT_CANARY + 8) && (YP09.r_whi r <=? YP09.r_wlo r))%bool
| Some _ => false
end.
Lemma is_canary_region_sound : forall r, is_canary_region r = true ->
YP09.r_base r = None /\ YP09.r_lo r = A_GOT_CANARY /\ YP09.r_hi r = A_GOT_CANARY + 8 /\ YP09.r_whi r <= YP09.r_wlo r.
Proof.
intros r H. unfold is_canary_region in H. destruct (YP09.r_base r); [discriminate H|].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. repeat split; assumption.
Qed.
Section a.
Section S.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Lemma canary_cell_in : forall ly, In (z8 (ANum A_GOT_CANARY) V_GOT_CANARY) (as_const B ly).
Proof.
intros ly. rewrite (ts_const B HB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. left.
unfold Tfib_const_abs; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.
(* canary_got_kept from the two states' const cells alone (the walks' icpt_laws_x gives them, AE2y.v). *)
Lemma canary_got_kept_x : forall ly (H : word -> bool) mem ly' (H' : word -> bool) mem' i,
Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
Forall (cell_holds B ly' (aview tfibsegs H' mem')) (as_const B ly') -> 0 <= i < 8 ->
mbyte tfibsegs (mrestrict H' mem') (A_GOT_CANARY + i) = mbyte tfibsegs (mrestrict H mem) (A_GOT_CANARY + i).
Proof.
intros ly H mem ly' H' mem' i M M' Hi.
pose proof (proj1 (Forall_forall _ _) M _ (canary_cell_in ly)) as C.
pose proof (proj1 (Forall_forall _ _) M' _ (canary_cell_in ly')) as C'.
unfold cell_holds in C, C'. cbn [c_at c_val c_w z8 c8 aeval] in C, C'.
apply mbyte_of_aview. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (C (Z.to_nat i) ltac:(lia)), (C' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.
End S.
End a.
