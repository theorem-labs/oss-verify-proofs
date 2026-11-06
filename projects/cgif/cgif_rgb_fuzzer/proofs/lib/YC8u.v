(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YCbe YP14 YP16 YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8w.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma m_bsum_node_blocks : forall tns, bsum (m_node_blocks tns) = NODE_SIZE * elen tns.
Proof.
intros tns. unfold m_node_blocks, elen. induction tns as [|t l IH]; [reflexivity|].
cbn [map length]. rewrite bsum_cons, IH. cbn [snd]. rewrite Nat2Z.inj_succ. unfold NODE_SIZE. lia.
Qed.
Lemma m_U_zext8_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma m_U_sext16_pred : forall E n v, ew E n = Z_to_bv 64 v -> 1 <= v < 2 ^ 15 -> U E (SAlu ALU_ADD (SExt true 16 (SOff n 0)) (SLit (-1))) = v - 1.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, (U_atom E n v Hn), U_SLit by lia. change (2 ^ Z.of_N 16) with 65536.
rewrite Z.mod_small by lia. rewrite (bv_swrap_small 16 v) by (change (bv_half_modulus 16) with (2 ^ 15); lia). rewrite (zcanon_id v) by (unfold M64; lia).
change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon, M64. replace (v + (2 ^ 64 - 1)) with (v - 1 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
End b.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma m_sep_nodes_lt : forall ly Sa W m md (tns : list tnode) others i j,
AR trasegs B ly Sa W m md -> Permutation (ablocks B ly Sa) (m_node_blocks tns ++ others) ->
0 <= i -> i < j -> j < elen tns ->
tn_addr (tnth tns i) + 56 <= tn_addr (tnth tns j) \/ tn_addr (tnth tns j) + 56 <= tn_addr (tnth tns i).
Proof.
intros ly Sa W m md tns others i j HAR HP Hi Hij Hj. unfold elen in Hj.
set (f := fun t : tnode => (tn_addr t, NODE_SIZE)).
set (i' := Z.to_nat i). set (j' := Z.to_nat j).
assert (Hi' : (i' < length tns)%nat) by (subst i'; lia).
pose proof (firstn_skipn i' tns) as Hsplit.
assert (Hsk : skipn i' tns = nth i' tns dtn :: skipn (Datatypes.S i') tns).
{ assert (SK : forall (l : list tnode) k, (k < length l)%nat -> skipn k l = nth k l dtn :: skipn (Datatypes.S k) l).
{ induction l as [|t l IH]; intros [|k] Hk; cbn [length] in Hk; try lia; [reflexivity|]. cbn [skipn nth]. apply IH. lia. }
exact (SK tns i' Hi'). }
assert (Hin : In (nth j' tns dtn) (skipn (Datatypes.S i') tns)).
{ replace j' with (S i' + (j' - S i'))%nat by (subst i' j'; lia). rewrite <- nth_skipn. apply nth_In. rewrite length_skipn. subst i' j'. lia. }
assert (HP2 : Permutation (ablocks B ly Sa) (f (nth i' tns dtn) :: (map f (firstn i' tns) ++ map f (skipn (Datatypes.S i') tns) ++ others))).
{ eapply Permutation_trans; [exact HP|]. unfold m_node_blocks. fold f. rewrite <- Hsplit at 1. rewrite Hsk, map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
apply Permutation_sym. apply Permutation_middle. }
pose proof (rg_sep_head_in B LAWS ly Sa W m md _ _ (f (nth j' tns dtn)) HAR HP2 ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map; exact Hin)) as Hd.
unfold zdisjoint, block_rng, f in Hd. cbn [fst snd] in Hd. change (req_size NODE_SIZE) with 56 in Hd. unfold tnth, znth. fold i' j'. exact Hd.
Qed.
Lemma m_sep_nodes : forall ly Sa W m md (tns : list tnode) others i j,
AR trasegs B ly Sa W m md -> Permutation (ablocks B ly Sa) (m_node_blocks tns ++ others) ->
0 <= i < elen tns -> 0 <= j < elen tns -> i <> j ->
tn_addr (tnth tns i) + 56 <= tn_addr (tnth tns j) \/ tn_addr (tnth tns j) + 56 <= tn_addr (tnth tns i).
Proof.
intros ly Sa W m md tns others i j HAR HP Hi Hj Hne. destruct (Z_lt_le_dec i j) as [Hlt | Hge].
- apply (m_sep_nodes_lt ly Sa W m md tns others i j HAR HP); lia.
- destruct (m_sep_nodes_lt ly Sa W m md tns others j i HAR HP ltac:(lia) ltac:(lia) ltac:(lia)) as [H | H]; [right | left]; exact H.
Qed.
Lemma m_node_upd3 : forall (m m' : word -> option byte) a c0 c1 tn lf c0' c1' lf',
obj_at trasegs m a LAY_Node (node_vals c0 c1 tn lf) -> length (tn_mean tn) = 3%nat ->
(forall i, 16 <= i < 50 -> mbyte trasegs m' (a + i) = mbyte trasegs m (a + i)) ->
val_mem trasegs m' a 8 c0' -> 0 <= c0' < 2 ^ 64 -> val_mem trasegs m' (a + 8) 8 c1' -> 0 <= c1' < 2 ^ 64 ->
val_mem trasegs m' (a + 50) 1 lf' -> 0 <= lf' < 256 ->
obj_at trasegs m' a LAY_Node (node_vals c0' c1' tn lf').
Proof.
intros m m' a c0 c1 tn lf c0' c1' lf' Ho Hl Hfr V0 R0 V1 R1 V9 R9.
unfold node_vals in *. destruct (tn_mean tn) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hl.
cbn [app obj_at LAY_Node] in Ho |- *.
destruct Ho as (_ & _ & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _ & _).
assert (K : forall (f : Z * N) v, 16 <= fst f -> fst f + Z.of_N (snd f) <= 50 -> field_ok trasegs m a f v -> field_ok trasegs m' a f v).
{ intros f v Hlo Hhi [Hv Hr]. split; [|exact Hr]. intros k Hk. rewrite <- (Hv k Hk). rewrite <- Z.add_assoc. apply Hfr. lia. }
split; [split; [rewrite Z.add_0_r; exact V0 | exact R0]|].
split; [split; [exact V1 | exact R1]|].
split; [apply K; [cbn; lia | cbn; lia | exact F2]|]. split; [apply K; [cbn; lia | cbn; lia | exact F3]|]. split; [apply K; [cbn; lia | cbn; lia | exact F4]|].
split; [apply K; [cbn; lia | cbn; lia | exact F5]|]. split; [apply K; [cbn; lia | cbn; lia | exact F6]|]. split; [apply K; [cbn; lia | cbn; lia | exact F7]|].
split; [apply K; [cbn; lia | cbn; lia | exact F8]|].
split; [split; [exact V9 | exact R9] | exact I].
Qed.
End d.
End c.
