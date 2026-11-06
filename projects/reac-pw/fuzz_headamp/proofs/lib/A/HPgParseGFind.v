(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v; 492 of its 562 lines of code are new or changed and 844 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v, with its module paths and module names changed; 111 of its 169 lines of code are new or changed and 504 lines of the source are left out. *)
(* reac-pw/fuzz_headamp: the model steps of the find loop of reac_headamp_prop_parse_result (Pod/Spa.v find_prop,
   spa_pod_object_find_prop, and is_struct_at, spa_pod_is_struct) at the cut FIND of lib/A/HPgParseBase.v
   (hp_m_find), shared by both images' find segments (image A lib/A/HPgParseCut.v, image B lib/AU/HPgParseCut.v).
   No image is Required here: no address, no table, no segment list is fixed. Proves no function (kind: helper
   lemmas for both images' find segments).

   Both images test the property at the offset r of the Props object at P, its size SZ = u32 at 0, as
     bltu (P + r) (P + 8)          r < 8: never (r >= 16);
     bltu (SZ - 16) (r - 8)        the property header does not fit in the object;
     bltu (P + SZ - 8 - (P + r)) VS   (VS = u32 at r + 8) the value does not fit;
   which is prop_is_inside bs 8 SZ r for an 8-aligned r >= 16 (hpf_pin). Then the key (u32 at r) against
   0x80001 (SPA_PROP_params), and on a match VS >> 20 and the value's type (u32 at r + 12) against 14
   (spa_pod_is_struct). The next property is r + ((VS + 15) | 7) + 1 = r + round_up8 (16 + VS) (hpf_ru8). The pod's
   words at a cut (role's pod_u32 / u32_at_range) are lib/A/HPgParseGWalk.v's hgw_pod_u32 / hgw_u32_range. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

(* ======================================= the words ======================================= *)
(* SPA_ROUND_UP_N (16 + v, 8) as the code computes it, and its bounds *)
Lemma hpf_ru8 : forall v, 0 <= v ->
Spa.round_up8 (16 + v) = Z.lor (v + 15) 7 + 1 /\ 16 + v <= Spa.round_up8 (16 + v) <= 23 + v /\
Spa.round_up8 (16 + v) mod 8 = 0.
Proof.
intros v Hv. split; [unfold Spa.round_up8; replace (16 + v - 1) with (v + 15) by lia; reflexivity|].
rewrite Spa.round_up8_eq by lia. pose proof (Model.pad8_bound (16 + v)) as B. pose proof (Model.pad8_eq (16 + v)) as E.
split; [lia|]. rewrite E, Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* spa_pod_prop_is_inside at an 8-aligned r >= 16: the code's two bounds tests *)
Lemma hpf_pin : forall bs size r, r mod 8 = 0 -> 16 <= r -> 16 <= size ->
Spa.prop_is_inside bs 8 size r = (r - 8 <=? size - 16) && (Spa.u32_at bs (r + 8) <=? size - 8 - r).
Proof.
intros bs size r H8 Hr Hs. unfold Spa.prop_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining.
replace (r mod 4 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
replace (8 <=? r) with true by (symmetry; apply Z.leb_le; lia).
replace (16 <=? size) with true by (symmetry; apply Z.leb_le; lia).
replace (8 + size - (r + 16)) with (size - 8 - r) by lia.
reflexivity.
Qed.

Lemma hpf_is_struct : forall bs r,
Spa.is_struct_at bs (r + 8) = (Spa.u32_at bs (r + 8) <? Spa.SPA_POD_MAX_SIZE) && (Spa.u32_at bs (r + 12) =? Model.POD_STRUCT).
Proof. intros bs r. unfold Spa.is_struct_at. replace (r + 8 + 4) with (r + 12) by lia. reflexivity. Qed.

(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v at afaa3cb55c1 (U_sub_l,
   U_sx32_eqb, U_add, U_or, U_srl, U_sext32), names prefixed hpf_. *)
(* ================== the engine's arithmetic on the find loop's values (both images) ================== *)
(* `sub rd,b,a` as the engine writes it *)
Lemma hpf_U_sub_l : forall E a b, U E (SAlu ALU_ADD (SMd M_MUL a (SLit (-1))) b) = (U E b - U E a) mod 2 ^ 64.
Proof.
intros E a b. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_l by lia.
replace (U E a * 18446744073709551615 + U E b) with ((U E b - U E a) + U E a * 2 ^ 64) by lia.
apply Z_mod_plus_full.
Qed.

(* `lw` of a u32 compared with a constant below 2^31: the test on the u32 itself *)
Lemma hpf_U_sx32_eqb : forall E a s c, U E a = s -> 0 <= s < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SExt true 32 a) =? c) = (s =? c).
Proof.
intros E a s c Ha Hs Hc. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec s (2 ^ 31)) as [Hlt|Hge].
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- assert (M1 : (s + 2 ^ 31) mod 2 ^ 32 = s - 2 ^ 31) by (symmetry; apply Z.mod_unique with 1; [left; lia | lia]).
  rewrite M1. assert (M2 : (s - 2 ^ 31 - 2 ^ 31) mod 2 ^ 64 = s - 2 ^ 32 + 2 ^ 64)
  by (symmetry; apply Z.mod_unique with (-1); [left; lia | lia]).
  rewrite M2. destruct (Z.eqb_spec (s - 2 ^ 32 + 2 ^ 64) c); destruct (Z.eqb_spec s c); first [reflexivity | lia].
Qed.

Lemma hpf_U_add : forall E a b, 0 <= U E a + U E b < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = U E a + U E b.
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia. Qed.

Lemma hpf_U_or : forall E a b, 0 <= Z.lor (U E a) (U E b) < 2 ^ 64 -> U E (SAlu ALU_OR a b) = Z.lor (U E a) (U E b).
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia. Qed.

Lemma hpf_U_srl : forall E a b, 0 <= U E b < 64 -> U E (SAlu ALU_SRL a b) = U E a / 2 ^ (U E b).
Proof.
intros E a b H. rewrite U_SAlu. cbn [zalu_raw].
replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 6) with 64. rewrite (Z.mod_small (U E b)) by lia.
rewrite Z.shiftr_div_pow2 by lia. pose proof (U_range E a) as Ha.
assert (0 < 2 ^ U E b) by (apply Z.pow_pos_nonneg; lia).
assert (U E a / 2 ^ U E b <= U E a) by (apply Z.div_le_upper_bound; [lia|]; nia).
assert (0 <= U E a / 2 ^ U E b) by (apply Z.div_pos; lia).
unfold zcanon, M64. apply Z.mod_small. unfold M64 in Ha. lia.
Qed.

Lemma hpf_U_sext32 : forall E a s, U E a = s -> 0 <= s < 2 ^ 31 -> U E (SExt true 32 a) = s.
Proof.
intros E a s Ha Hs. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* the next property's offset, as the code computes it: P + r + ((VS + 15) | 7) + 1 *)
Lemma hpf_U_next : forall E a b p v, U E a = p -> U E b = v + 15 -> 0 <= v -> 0 <= p -> p + v + 24 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD a (SAlu ALU_OR b (SLit 7))) (SLit 1)) = p + Spa.round_up8 (16 + v).
Proof.
intros E a b p v Ha Hb Hv Hp Hlt.
destruct (hpf_ru8 v Hv) as (R0 & R1 & _).
assert (U7 : U E (SLit 7) = 7) by (apply U_lit; lia).
assert (U1 : U E (SLit 1) = 1) by (apply U_lit; lia).
assert (HL : Z.lor (v + 15) 7 = Spa.round_up8 (16 + v) - 1) by lia.
assert (Hor : U E (SAlu ALU_OR b (SLit 7)) = Spa.round_up8 (16 + v) - 1).
{ rewrite hpf_U_or by (rewrite Hb, U7, HL; lia). rewrite Hb, U7, HL. reflexivity. }
rewrite hpf_U_add by (rewrite hpf_U_add by (rewrite Ha, Hor; lia); rewrite Ha, Hor, U1; lia).
rewrite hpf_U_add by (rewrite Ha, Hor; lia). rewrite Ha, Hor, U1. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.

(* the answer of a non-NULL call is the model's *)
Lemma hpf_ans : forall x : @hp_ctx segs, hx_null x = 0 -> hx_ans x = hx_res x.
Proof. intros x H. unfold hx_ans, hx_res, hd_props. rewrite H. reflexivity. Qed.

(* ======================================= one pass of the find loop ======================================= *)
(* (1) the property does not lie in the object: find_prop gives None, the answer is (0, [], (0, 0, 0)) *)
Lemma hpf_find_out : forall (x : @hp_ctx segs) r n, hp_m_find x r (S n) ->
(hx_SZ x - 16 < r - 8 \/ hx_SZ x - 8 - r < hp_vs x r) -> hx_ans x = (0, [], (0, 0, Headamp.REFUSE_NONE)).
Proof.
intros x r n (Hnull & Hobj & HSZ & Hr & Hr8 & Hfuel & Hres) Hout.
rewrite (hpf_ans x Hnull), Hres. cbn [Spa.find_prop].
rewrite (hpf_pin _ _ _ Hr8 ltac:(lia) HSZ). unfold hp_vs in Hout.
destruct Hout as [H|H].
- rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
- rewrite (proj2 (Z.leb_gt _ _) H), andb_false_r. reflexivity.
Qed.

(* (2) it lies in the object and its key is not SPA_PROP_params: the find loop at the next property *)
Lemma hpf_find_next : forall (x : @hp_ctx segs) r n, hp_m_find x r (S n) -> hx_SZ x = hx_len x - 8 ->
r - 8 <= hx_SZ x - 16 -> hp_vs x r <= hx_SZ x - 8 - r ->
Spa.u32_at (hx_bs x) r <> Model.POD_PROP_PARAMS -> hp_m_find x (r + Spa.round_up8 (16 + hp_vs x r)) n.
Proof.
intros x r n (Hnull & Hobj & HSZ & Hr & Hr8 & Hfuel & Hres) HL H1 H2 Hk.
assert (V : 0 <= hp_vs x r) by (unfold hp_vs, Spa.u32_at; apply Cursor.rd32_nonneg).
destruct (hpf_ru8 (hp_vs x r) V) as (_ & R1 & R2).
split; [exact Hnull|]. split; [exact Hobj|]. split; [exact HSZ|].
split; [lia|]. split; [rewrite Z.add_mod, Hr8, R2 by lia; reflexivity|]. split; [lia|].
rewrite Hres. cbn [Spa.find_prop].
rewrite (hpf_pin _ _ _ Hr8 ltac:(lia) HSZ). unfold hp_vs in *.
rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2), (proj2 (Z.eqb_neq _ _) Hk). reflexivity.
Qed.

(* (3) the key is SPA_PROP_params and its value is not a Struct: the answer is (0, [], (0, 0, 0)) *)
Lemma hpf_find_nostruct : forall (x : @hp_ctx segs) r n, hp_m_find x r (S n) ->
r - 8 <= hx_SZ x - 16 -> hp_vs x r <= hx_SZ x - 8 - r ->
Spa.u32_at (hx_bs x) r = Model.POD_PROP_PARAMS ->
(Spa.SPA_POD_MAX_SIZE <= hp_vs x r \/ Spa.u32_at (hx_bs x) (r + 12) <> Model.POD_STRUCT) ->
hx_ans x = (0, [], (0, 0, Headamp.REFUSE_NONE)).
Proof.
intros x r n (Hnull & Hobj & HSZ & Hr & Hr8 & Hfuel & Hres) H1 H2 Hk Hns.
rewrite (hpf_ans x Hnull), Hres. cbn [Spa.find_prop].
rewrite (hpf_pin _ _ _ Hr8 ltac:(lia) HSZ). unfold hp_vs in *.
rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2), (proj2 (Z.eqb_eq _ _) Hk). cbn [andb].
rewrite hpf_is_struct.
destruct Hns as [H|H].
- rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.

(* (4) the key is SPA_PROP_params and its value is a Struct: the pair loop at the Struct's first child, the key
   slot empty, nothing folded, fuel length bs *)
Lemma hpf_find_walk : forall (x : @hp_ctx segs) r n, hp_m_find x r (S n) -> hx_SZ x = hx_len x - 8 ->
r - 8 <= hx_SZ x - 16 -> hp_vs x r <= hx_SZ x - 8 - r ->
Spa.u32_at (hx_bs x) r = Model.POD_PROP_PARAMS ->
hp_vs x r < Spa.SPA_POD_MAX_SIZE -> Spa.u32_at (hx_bs x) (r + 12) = Model.POD_STRUCT -> 0 <= hx_cap x ->
hp_m_walk x r (r + 16) (length (hx_bs x)) None [] 0 0.
Proof.
intros x r n (Hnull & Hobj & HSZ & Hr & Hr8 & Hfuel & Hres) HL H1 H2 Hk Hvs Hty Hcap.
assert (V : 0 <= hp_vs x r) by (unfold hp_vs, Spa.u32_at; apply Cursor.rd32_nonneg).
unfold hx_len in HL.
split; [exact Hnull|].
split; [unfold hp_st_ok, hx_len; repeat split; lia|].
split; [lia|]. split; [rewrite Z.add_mod, Hr8 by lia; reflexivity|].
split; [unfold hx_len in *; lia|].
split; [intros ck Hck; discriminate Hck|].
split; [unfold hp_st; cbn [length Z.of_nat]; lia|].
rewrite Hres. cbn [Spa.find_prop].
rewrite (hpf_pin _ _ _ Hr8 ltac:(lia) HSZ). unfold hp_vs in *.
rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2), (proj2 (Z.eqb_eq _ _) Hk). cbn [andb].
rewrite hpf_is_struct, (proj2 (Z.ltb_lt _ _) Hvs), Hty, Z.eqb_refl. cbn [andb hp_l2key].
reflexivity.
Qed.

End b.

Print Assumptions hpf_find_out.
Print Assumptions hpf_find_next.
Print Assumptions hpf_find_nostruct.
Print Assumptions hpf_find_walk.
Print Assumptions hpf_ru8.
