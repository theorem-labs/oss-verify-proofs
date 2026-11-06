(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4c YC4h YC4a YC27 YC2r YC4u YC52 YCaq YCct YCce YCcd YCc6 YCcb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 250.
Open Scope bv_scope.
Open Scope Z_scope.



Lemma unsigned_range_64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
Lemma land4_mod256 : forall x, 0 <= x -> Z.land (x mod 256) 4 = Z.land x 4.
Proof.
intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
destruct (Z.eq_dec n 2) as [-> | Hne].
- change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4 n) with false; [rewrite !andb_false_r; reflexivity|].
symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma attr_test : forall E e, Z.land (U E (SExt false 8 e)) 4 = Z.land (bv_unsigned (sv_denot E e)) 4.
Proof. intros E e. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. apply land4_mod256. apply (proj1 (unsigned_range_64 _)). Qed.
Ltac attr_test_in H :=
first [ rewrite attr_test in H
| lazymatch type of H with context [Z.land (U ?E0 ?e0) 4] => change (U E0 e0) with (bv_unsigned (sv_denot E0 e0)) in H end ].
Ltac payload_block Hc :=
let L := rnLAWS in
lazymatch goal with Hpn : (?n = 0 /\ ?p = A_EMPTY) \/ (0 < ?n < 2 ^ 26 /\ In (?p, ?n) (ablocks ?B ?ly ?S)), Eab3 : ablocks _ ?ly3 ?S3 = ablocks _ ?ly ?S,
HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly3 ?S3 _ _ _ _, Hfin3 : In (2, ?fpos) (frames ?S3), EFA3 : forall c q, frame_addr ?ly3 c q = _ |- _ =>
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hc; lia|];
assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin);
destruct (al_blocks _ _ L _ _ _ _ _ p n (proj1 HJ3) Hp3) as (Hp16 & Hp4096 & Hpceil & Hph_ia & HppresX & _); pose proof (proj1 Hph_ia) as Hph;
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0) as [He|Hne]; [exfalso; clear - Hnpos He; lia | reflexivity]);
rewrite Hrq in Hpceil, HppresX; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hpceil;
lazymatch goal with C3 : kHighMemBeg = _ |- _ => idtac; rewrite ?C3 in Hph end;
pose proof (sep_block_frame trasegs B L ly3 S3 _ _ _ p n 2 fpos (proj1 HJ3) Hp3 Hfin3) as HdPF;
unfold zdisjoint in HdPF; cbn [fst snd] in HdPF; rewrite Hrq in HdPF; change (fs_frame_bytes 2) with 256 in HdPF; rewrite EFA3 in HdPF;
repeat match goal with F := frame_addr _ _ _ |- _ => fold F in HdPF end;
pose proof (blk_off_img _ _ _ _ _ _ _ _ (proj1 HJ3) Hp3) as Hph_img; rewrite Hrq in Hph_img
end.
Ltac payload_fact HS :=
lazymatch goal with E10n : ew _ 10 = Z_to_bv 64 ?p, Hph : 4096 <= ?p, Hpceil : ?p + ?n <= alloc_ceiling, Hp16 : ?p mod 16 = 0, Hnpos : 0 < ?n < _ |- _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact trasegs Ev ssx msx 10%nat (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by nat_side;
rewrite E10n; rewrite unsigned_lit_small by (clear - Hph Hpceil Hnpos; ceil; lia);
change (2 ^ 4) with 16; clear - Hph Hpceil Hp16 Hnpos; ceil; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end.
Ltac payload_bytes2 HS c Hcb clr :=
lazymatch goal with E10n : ew _ 10 = Z_to_bv 64 ?p, HppresX : forall a, ?p <= a < ?p + ?n -> _, Hph : 4096 <= ?p, Hpceil : ?p + ?n <= alloc_ceiling, Hnpos : 0 < ?n < _,
AG : forall m, (m < 33)%nat -> _ |- _ =>
let b0 := fresh "b" in let b1 := fresh "b" in let Rb0 := fresh "Rb" in let Rb1 := fresh "Rb" in let Vb0 := fresh "Vb" in let Vb1 := fresh "Vb" in
let EK0 := fresh "Eb" in let EK1 := fresh "Eb" in
destruct (rt_val_mem_byte1 _ _ (p + c) (proj1 (HppresX (p + c) ltac:(clear - Hcb Hnpos; lia)))) as (b0 & Rb0 & Vb0);
destruct (rt_val_mem_byte1 _ _ (p + (c + 1)) (proj1 (HppresX (p + (c + 1)) ltac:(clear - Hcb Hnpos; lia)))) as (b1 & Rb1 & Vb1);
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in let K1 := eval vm_compute in (Datatypes.S K) in
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trasegs K Ev ssx msx [Z_to_bv 64 b0; Z_to_bv 64 b1] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (EK0 : ew (havoc Ev K [Z_to_bv 64 b0; Z_to_bv 64 b1]) K = Z_to_bv 64 b0) by (exact (ew_havoc_new _ K [Z_to_bv 64 b0; Z_to_bv 64 b1] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (EK1 : ew (havoc Ev K [Z_to_bv 64 b0; Z_to_bv 64 b1]) K1 = Z_to_bv 64 b1) by (exact (ew_havoc_new _ K [Z_to_bv 64 b0; Z_to_bv 64 b1] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK0, unsigned_lit_small by (clear - Rb0; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rb0; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K1 (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK1, unsigned_lit_small by (clear - Rb1; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rb1; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trasegs Ev2 _ _ (YQ0b.mkRegion (Some 10%nat) c (c + 2) 0 0 [YQ0b.mkChunk c (CVal 1 (SOff K 0)); YQ0b.mkChunk (c + 1) (CVal 1 (SOff K1 0))]) HS
ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by nat_side; rewrite E10n, unsigned_lit_small by (clear - Hph Hpceil Hnpos; ceil; lia);
split; [clear - Hph; lia|]; split; [clear - Hpceil Hcb; ceil; lia|];
split; [intros o Ho; exfalso; clear - Ho; lia |];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ p c 1 _ b0); [cbn [sv_denot]; rewrite EK0, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb0]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ p (c + 1) 1 _ b1); [cbn [sv_denot]; rewrite EK1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb1]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by nat_side;
rewrite E10n; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clr; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end end.
Ltac payload_bytes4 HS c Hcb clr :=
lazymatch goal with E10n : ew _ 10 = Z_to_bv 64 ?p, HppresX : forall a, ?p <= a < ?p + ?n -> _, Hph : 4096 <= ?p, Hpceil : ?p + ?n <= alloc_ceiling, Hnpos : 0 < ?n < _,
AG : forall m, (m < 33)%nat -> _ |- _ =>
let b0 := fresh "b" in let b1 := fresh "b" in let b2 := fresh "b" in let b3 := fresh "b" in
let Rb0 := fresh "Rb" in let Rb1 := fresh "Rb" in let Rb2 := fresh "Rb" in let Rb3 := fresh "Rb" in
let Vb0 := fresh "Vb" in let Vb1 := fresh "Vb" in let Vb2 := fresh "Vb" in let Vb3 := fresh "Vb" in
let EK0 := fresh "Eb" in let EK1 := fresh "Eb" in let EK2 := fresh "Eb" in let EK3 := fresh "Eb" in
destruct (rt_val_mem_byte1 _ _ (p + c) (proj1 (HppresX (p + c) ltac:(clear - Hcb Hnpos; lia)))) as (b0 & Rb0 & Vb0);
destruct (rt_val_mem_byte1 _ _ (p + (c + 1)) (proj1 (HppresX (p + (c + 1)) ltac:(clear - Hcb Hnpos; lia)))) as (b1 & Rb1 & Vb1);
destruct (rt_val_mem_byte1 _ _ (p + (c + 2)) (proj1 (HppresX (p + (c + 2)) ltac:(clear - Hcb Hnpos; lia)))) as (b2 & Rb2 & Vb2);
destruct (rt_val_mem_byte1 _ _ (p + (c + 3)) (proj1 (HppresX (p + (c + 3)) ltac:(clear - Hcb Hnpos; lia)))) as (b3 & Rb3 & Vb3);
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in let K1 := eval vm_compute in (Datatypes.S K) in
let K2 := eval vm_compute in (Datatypes.S K1) in let K3 := eval vm_compute in (Datatypes.S K2) in
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trasegs K Ev ssx msx [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (EK0 : ew (havoc Ev K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3]) K = Z_to_bv 64 b0) by (exact (ew_havoc_new _ K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (EK1 : ew (havoc Ev K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3]) K1 = Z_to_bv 64 b1) by (exact (ew_havoc_new _ K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (EK2 : ew (havoc Ev K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3]) K2 = Z_to_bv 64 b2) by (exact (ew_havoc_new _ K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3] 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (EK3 : ew (havoc Ev K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3]) K3 = Z_to_bv 64 b3) by (exact (ew_havoc_new _ K [Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3] 3 (Z_to_bv 64 0) ltac:(cbn; lia)));
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK0, unsigned_lit_small by (clear - Rb0; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rb0; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K1 (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK1, unsigned_lit_small by (clear - Rb1; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rb1; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K2 (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK2, unsigned_lit_small by (clear - Rb2; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rb2; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K3 (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK3, unsigned_lit_small by (clear - Rb3; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rb3; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trasegs Ev2 _ _ (YQ0b.mkRegion (Some 10%nat) c (c + 4) 0 0 [YQ0b.mkChunk c (CVal 1 (SOff K 0)); YQ0b.mkChunk (c + 1) (CVal 1 (SOff K1 0)); YQ0b.mkChunk (c + 2) (CVal 1 (SOff K2 0)); YQ0b.mkChunk (c + 3) (CVal 1 (SOff K3 0))]) HS
ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by nat_side; rewrite E10n, unsigned_lit_small by (clear - Hph Hpceil Hnpos; ceil; lia);
split; [clear - Hph; lia|]; split; [clear - Hpceil Hcb; ceil; lia|];
split; [intros o Ho; exfalso; clear - Ho; lia |];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ p c 1 _ b0); [cbn [sv_denot]; rewrite EK0, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb0]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ p (c + 1) 1 _ b1); [cbn [sv_denot]; rewrite EK1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb1]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ p (c + 2) 1 _ b2); [cbn [sv_denot]; rewrite EK2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb2]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ p (c + 3) 1 _ b3); [cbn [sv_denot]; rewrite EK3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vb3]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by nat_side;
rewrite E10n; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clr; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end end.
Ltac add_fact HS n lo hi Hv tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact trasegs Ev ssx msx n (mkAF lo hi 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv, unsigned_lit_small by tac; rewrite Z.pow_0_r, Z.mod_1_r; split; [tac | split; [reflexivity | clear; lia]])) as HS3;
clear HS; rename HS3 into HS end.
Ltac fieldC HS off n v pf ftac :=
let En := fresh "Ef" in
lazymatch type of HS with st_ok _ ?Ev _ _ =>
add_atom_win HS n (Z_to_bv 64 v) En; ftac HS En;
rechunk_at HS 75%nat off (SOff n 0)
ltac:(first [ rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite En; symmetry;
etransitivity; [apply (sv_denot_agree n Ev); [repeat (apply env_agree_havoc_ge; [clear; lia|]); apply env_agree_refl | vm_compute; reflexivity] | pf]
| match goal with |- ?g => idtac "FIELDC-FAIL" n g end; fail ]) end.
Ltac nofact HS En := idtac.
Ltac fact16 n rtac HS En := add_fact HS n 0 65535 En rtac.
Ltac fieldCraw HS off n :=
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base_off rs 75%nat off in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let cs := eval vm_compute in (YQ0b.r_chunks r) in
let j := idx_of_chunk cs off in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth j cs (YQ0b.mkChunk 0 (CVal 1 (SLit 0))))) with YQ0b.mkChunk _ (CVal _ ?e) =>
fieldC HS off n (bv_unsigned (sv_denot Ev e)) ltac:(symmetry; apply Z_to_bv_bv_unsigned) nofact end end.
Ltac fieldC0 off n HS := fieldC HS off n 0 ltac:(reflexivity) nofact.
Ltac fieldCR off n HS := fieldCraw HS off n.
