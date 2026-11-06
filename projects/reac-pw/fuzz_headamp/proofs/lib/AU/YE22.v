(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE22.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: by a Theorem Labs lane, the .got canary cell (A_GOT_CANARY, V_GOT_CANARY) is row 209 of scene's generated Tfib_const_abs (AF0m / YF0m of a working branch d756770719b), not cgif's row 193. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE22.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AE22.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AE22.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AE22.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.reac_pw.fuzz_headamp.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YP0m YP09 YI04 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_GOT_CANARY : Z := 0x9d478.
Definition V_GOT_CANARY : Z := 0x5f8210.
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
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Lemma canary_cell_in : forall ly, In (z8 (ANum A_GOT_CANARY) V_GOT_CANARY) (as_const B ly).
Proof.
intros ly. rewrite (ts_const B HB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. left.
apply (nth_error_In Tfib_const_abs 193). reflexivity.
Qed.
Lemma canary_got_kept : forall ly S W mem md ly' S' W' mem' md' i,
AR tfibsegs B ly S W mem md -> AR tfibsegs B ly' S' W' mem' md' -> 0 <= i < 8 ->
mbyte tfibsegs (mrestrict (w_H W') mem') (A_GOT_CANARY + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + i).
Proof.
intros ly S W mem md ly' S' W' mem' md' i (M & _) (M' & _) Hi.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (canary_cell_in ly)) as C.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M') _ (canary_cell_in ly')) as C'.
unfold cell_holds in C, C'. cbn [c_at c_val c_w z8 c8 aeval] in C, C'.
apply mbyte_of_aview. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (C (Z.to_nat i) ltac:(lia)), (C' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.
Lemma got_canary_of_AR : forall ly S W mem md,
AR tfibsegs B ly S W mem md -> val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_CANARY 8 V_GOT_CANARY.
Proof.
intros ly S W mem md (M & _). pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (canary_cell_in ly)) as C.
unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
intros k Hk. pose proof (C k Hk) as Ck. unfold aview in Ck.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + Z.of_nat k)) as [b|]; [|discriminate Ck].
cbn [option_map] in Ck. injection Ck as Ck. f_equal. apply bv_eq. rewrite Ck, Z_to_bv_unsigned.
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma canary_region_kept : forall E ly S W mem md ly' S' W' mem' md' r,
AR tfibsegs B ly S W mem md -> AR tfibsegs B ly' S' W' mem' md' -> is_canary_region r = true -> region_wf r = true ->
region_ok tfibsegs E (mrestrict (w_H W) mem) r -> region_ok tfibsegs E (mrestrict (w_H W') mem') r.
Proof.
intros E ly S W mem md ly' S' W' mem' md' r HAR HAR' Hc Hwf (B1 & B2 & Wr & Cs).
destruct (is_canary_region_sound r Hc) as (Hb & Hlo & Hhi & Hw). pose proof (region_wf_facts r Hwf) as (_ & _ & Hci).
split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hin i Hi. pose proof (proj1 (Forall_forall _ _) Cs c Hin i Hi) as (b & Hb1 & Hb2).
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hin)) as (Ci1 & Ci2 & _).
exists b. split; [exact Hb1|]. rewrite <- Hb2. rewrite Hb. cbn [base_val]. rewrite !Z.add_0_l.
replace (YP09.c_off c + i) with (A_GOT_CANARY + (YP09.c_off c + i - A_GOT_CANARY)) by lia.
apply (canary_got_kept _ _ _ _ _ _ _ _ _ _ _ HAR HAR'). lia.
Qed.
End S.
End a.
