(* edited in place from cgif_file lib/A/AE22.v by rules r1,r2,r3,r6, generator 107cfa3ff571119170a251af71894ef99c74eb0651a9612aa72eb6730ba3621a *)
(* rC copy: the in-place output above under the set's module names Xcfh (the renaming is the last step), generator 107cfa3ff5711191 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE22.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YI04 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0xcfh AE20 AE2ycfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YGcfNames.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_GOT_CANARY : Z := 0xa2c98.
Definition V_GOT_CANARY : Z := 0x5fdf30.
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
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Section S.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Lemma canary_cell_in : forall ly, In (z8 (ANum A_GOT_CANARY) V_GOT_CANARY) (as_const B ly).
Proof.
intros ly. rewrite (ts_const B HB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. left.
apply (nth_error_In Tfib_const_abs 169). reflexivity.   (* the canary GOT cell 0xa2c98: index 193 in cgif's A/AF0m.v, 169 in preset's generated one (this reflexivity checks it): the donor's 24 descriptor cells (its indices 156-179) leave their places, as do its 5 own-global guard cells (205-209); preset's Tfib_const_abs has 1041 cells, 472 of them descriptor cells (8 per global, 59 globals; AF0m.v:4) at indices 405-876, and 164 cells follow them *)
Qed.
Lemma canary_got_kept : forall ly S Hp W mem md ly' S' W' mem' md' i,
ARcf tfibsegs B ly S Hp W mem md -> ARcf tfibsegs B ly' S' Hp W' mem' md' -> 0 <= i < 8 ->
mbyte tfibsegs (mrestrict (w_H W') mem') (A_GOT_CANARY + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + i).
Proof.
intros ly S Hp W mem md ly' S' W' mem' md' i (M & _) (M' & _) Hi.
pose proof (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) _ (canary_cell_in ly)) as C.
pose proof (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M') _ (canary_cell_in ly')) as C'.
unfold cell_holds in C, C'. cbn [c_at c_val c_w z8 c8 aeval] in C, C'.
apply mbyte_of_aview. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (C (Z.to_nat i) ltac:(lia)), (C' (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.
Lemma got_canary_of_AR : forall ly S Hp W mem md,
ARcf tfibsegs B ly S Hp W mem md -> val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_CANARY 8 V_GOT_CANARY.
Proof.
intros ly S Hp W mem md (M & _). pose proof (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) _ (canary_cell_in ly)) as C.
unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
intros k Hk. pose proof (C k Hk) as Ck. unfold aview in Ck.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (A_GOT_CANARY + Z.of_nat k)) as [b|]; [|discriminate Ck].
cbn [option_map] in Ck. injection Ck as Ck. f_equal. apply bv_eq. rewrite Ck, Z_to_bv_unsigned.
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma canary_region_kept : forall E ly S Hp W mem md ly' S' W' mem' md' r,
ARcf tfibsegs B ly S Hp W mem md -> ARcf tfibsegs B ly' S' Hp W' mem' md' -> is_canary_region r = true -> region_wf r = true ->
region_ok tfibsegs E (mrestrict (w_H W) mem) r -> region_ok tfibsegs E (mrestrict (w_H W') mem') r.
Proof.
intros E ly S Hp W mem md ly' S' W' mem' md' r HAR HAR' Hc Hwf (B1 & B2 & Wr & Cs).
destruct (is_canary_region_sound r Hc) as (Hb & Hlo & Hhi & Hw). pose proof (region_wf_facts r Hwf) as (_ & _ & Hci).
split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hin i Hi. pose proof (proj1 (Forall_forall _ _) Cs c Hin i Hi) as (b & Hb1 & Hb2).
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hin)) as (Ci1 & Ci2 & _).
exists b. split; [exact Hb1|]. rewrite <- Hb2. rewrite Hb. cbn [base_val]. rewrite !Z.add_0_l.
replace (YP09.c_off c + i) with (A_GOT_CANARY + (YP09.c_off c + i - A_GOT_CANARY)) by lia.
apply (canary_got_kept _ _ _ _ _ _ _ _ _ _ _ _ HAR HAR'). lia.
Qed.
End S.
End a.
