(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0b YI00 YK05 YA0i YA0l YG00 YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_GOT_CANARY {imgk : img} : Z := (0xa2e10 + D_10f0).
Definition V_GOT_CANARY {imgk : img} : Z := (0x5fd190 + D_10c0).
Definition is_canary_region {imgk : img} (r : YQ0b.region) : bool :=
match YQ0b.r_base r with
| None => ((YQ0b.r_lo r =? A_GOT_CANARY) && (YQ0b.r_hi r =? A_GOT_CANARY + 8) && (YQ0b.r_whi r <=? YQ0b.r_wlo r))%bool
| Some _ => false
end.
Lemma is_canary_region_sound {imgk : img} : forall r, is_canary_region r = true ->
YQ0b.r_base r = None /\ YQ0b.r_lo r = A_GOT_CANARY /\ YQ0b.r_hi r = A_GOT_CANARY + 8 /\ YQ0b.r_whi r <= YQ0b.r_wlo r.
Proof.
intros r H. unfold is_canary_region in H. destruct (YQ0b.r_base r); [img_try (discriminate H)|].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. repeat split; assumption.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis HB : TfxSyms B.
Lemma canary_cell_in : forall ly, In (z8 (ANum A_GOT_CANARY) V_GOT_CANARY) (as_const B ly).
Proof.
intros ly. rewrite (ts_const B HB ly). unfold Tfx_const. img_apply in_or_app. right. img_apply in_or_app. left.
img_apply (nth_error_In Tfx_const_abs 185). img_refl.
Qed.
Lemma canary_got_kept : forall ly S W mem md ly' S' W' mem' md' i,
AR tfxsegs B ly S W mem md -> AR tfxsegs B ly' S' W' mem' md' -> 0 <= i < 8 ->
mbyte tfxsegs (mrestrict (w_H W') mem') (A_GOT_CANARY + i) = mbyte tfxsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + i).
Proof.
intros ly S W mem md ly' S' W' mem' md' i (M & _) (M' & _) Hi.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (canary_cell_in ly)) as C.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M') _ (canary_cell_in ly')) as C'.
unfold cell_holds in C, C'. cbn [c_at c_val c_w z8 c8 aeval] in C, C'.
img_apply mbyte_of_aview. replace i with (Z.of_nat (Z.to_nat i)) by img_lia.
rewrite (C (Z.to_nat i) ltac:(img_lia)), (C' (Z.to_nat i) ltac:(img_lia)). img_refl.
Qed.
Lemma got_canary_of_AR : forall ly S W mem md,
AR tfxsegs B ly S W mem md -> val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_CANARY 8 V_GOT_CANARY.
Proof.
intros ly S W mem md (M & _). pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (canary_cell_in ly)) as C.
unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
intros k Hk. pose proof (C k Hk) as Ck. unfold aview in Ck.
destruct (mbyte tfxsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + Z.of_nat k)) as [b|]; [|img_try (discriminate Ck)].
cbn [option_map] in Ck. injection Ck as Ck. f_equal. img_apply bv_eq. rewrite Ck, Z_to_bv_unsigned.
do 8 (destruct k as [|k]; [img_try ((img_case; vm_compute); img_refl)|]). img_lia.
Qed.

End S.
End a.
