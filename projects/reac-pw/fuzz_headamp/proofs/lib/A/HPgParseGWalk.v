(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/ParseWalk.v at 3e9fc5c8969
   (pw_nul_u, pw_ne_nul, pw_cmp_walk, pw_no_nul, pw_prefix_nonul, pw_prefix_len, pw_strncmp_prefix, pw_nth_firstn,
   pw_nth_skipn, pw_nul_idx_le, pw_nul_idx_bound, pw_cstr_nul, pw_cstr_nonul, pw_gs, pw_lor7, pw_inside,
   pw_inside_small) with module paths changed, the prefix hgw_ and strncmp's model taken from lib/Spec/StrFun.v
   (the model the strncmp wrapper's contract of lib/A/HPgHole.v reads); proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v
   at afaa3cb55c1 (U_off_of, U_subba, U_sext32, U_sext32_eqb, U_next, U_and3, U_s8: the arithmetic of the engine's
   forms of the pair loop's instructions, which both headamp images share) renamed hgw_U_*; the model steps between
   the cut states of lib/A/HPgParseBase.v and the key's string facts are new. *)
(* reac-pw/fuzz_headamp: the IMAGE-INDEPENDENT facts the walks of reac_headamp_prop_parse_result's pair loop use
   in both ASan images (image A lib/A/HPgParseWalk.v, image B lib/AU/HPgParseW.v): the tests of the pair loop's head
   (spa_pod_is_inside, iter.h:31-37; spa_pod_get_string, body.h:224-237; strncmp(key, "reac.headamp.", 13)) in the
   form the code computes them, the model step of HPgParseBase.v's cut states for each way out of the loop's head
   and of the advance, and the bytes of a pending key inside the pod. Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e.
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================= the key test ======================================= *)
Lemma hgw_nul_u : bv_unsigned Cursor.NUL = 0.
Proof. reflexivity. Qed.

Lemma hgw_ne_nul : forall b : byte, b <> Cursor.NUL -> bv_unsigned b <> 0.
Proof. intros b H E. apply H. apply bv_eq. rewrite E. reflexivity. Qed.

(* strncmp_walk on two NUL-terminated strings without inner NUL, r of k + 1 bytes: some byte difference, 0 exactly
   when the first k + 1 bytes of l are r. *)
Lemma hgw_cmp_walk : forall l r k, ~ In Cursor.NUL l -> ~ In Cursor.NUL r -> length r = S k ->
  exists v, StrFun.strncmp_walk (l ++ [Cursor.NUL]) (r ++ [Cursor.NUL]) k = Some v /\ -256 < v < 256 /\
            (v = 0 <-> Cursor.bytes_eqb (firstn (S k) l) r = true).
Proof.
  induction l as [|a l IH]; intros r k Hl Hr Lr; (destruct r as [|b r]; [discriminate Lr|]).
  - assert (Hb : bv_unsigned b <> 0) by (apply hgw_ne_nul; intros E; apply Hr; left; exact E).
    pose proof (Cursor.byte_range b) as Rb.
    exists (0 - bv_unsigned b). cbn [app StrFun.strncmp_walk]. rewrite hgw_nul_u. cbn [Z.eqb orb].
    split; [reflexivity|]. split; [lia|]. cbn [firstn Cursor.bytes_eqb]. split; [lia | intros E; discriminate E].
  - assert (Ha : bv_unsigned a <> 0) by (apply hgw_ne_nul; intros E; apply Hl; left; exact E).
    assert (Hb : bv_unsigned b <> 0) by (apply hgw_ne_nul; intros E; apply Hr; left; exact E).
    assert (Hl' : ~ In Cursor.NUL l) by (intros H; apply Hl; right; exact H).
    assert (Hr' : ~ In Cursor.NUL r) by (intros H; apply Hr; right; exact H).
    pose proof (Cursor.byte_range a) as Ra. pose proof (Cursor.byte_range b) as Rb.
    cbn [app StrFun.strncmp_walk].
    rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hb). cbn [orb].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct k as [|k].
      * cbn [Nat.eqb orb negb]. exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
        destruct r as [|b' r]; [|cbn [length] in Lr; discriminate Lr].
        cbn [firstn Cursor.bytes_eqb]. rewrite E, Z.eqb_refl. cbn [andb]. split; intros _; [reflexivity | lia].
      * cbn [Nat.eqb orb negb].
        destruct (IH r k Hl' Hr' ltac:(cbn [length] in Lr; lia)) as (v & Ev & Rv & Iv).
        exists v. split; [exact Ev|]. split; [exact Rv|].
        cbn [firstn Cursor.bytes_eqb]. rewrite E, Z.eqb_refl. cbn [andb]. exact Iv.
    + cbn [negb]. rewrite Bool.orb_true_r.
      exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      cbn [firstn Cursor.bytes_eqb]. rewrite (proj2 (Z.eqb_neq _ _) E). cbn [andb].
      split; [lia | intros F; discriminate F].
Qed.

Lemma hgw_no_nul : forall l, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In Cursor.NUL l.
Proof.
  induction l as [|x l IH]; cbn [forallb In]; [tauto|]. intros H [E|E].
  - subst x. rewrite hgw_nul_u in H. cbn [Z.eqb negb andb] in H. discriminate H.
  - apply andb_prop in H as [_ H]. exact (IH H E).
Qed.

Lemma hgw_prefix_nonul : ~ In Cursor.NUL Headamp.HA_PREFIX.
Proof. apply hgw_no_nul. vm_compute. reflexivity. Qed.

Lemma hgw_prefix_len : length Headamp.HA_PREFIX = 13%nat.
Proof. vm_compute. reflexivity. Qed.

(* The value of strncmp(key, "reac.headamp.", 13) on the C string k, as the strncmp wrapper's contract states its
   model: a byte difference, 0 exactly when k has the prefix. *)
Lemma hgw_strncmp_prefix : forall k, ~ In (Z_to_bv 8 0) k ->
  exists d, StrFun.strncmp_model (k ++ [Z_to_bv 8 0]) (Headamp.HA_PREFIX ++ [Z_to_bv 8 0]) 13 = Some d /\
            -256 < d < 256 /\ (d = 0 <-> Headamp.ha_prefix k = true).
Proof.
  intros k Hk. unfold Headamp.ha_prefix. rewrite hgw_prefix_len.
  change (StrFun.strncmp_model (k ++ [Z_to_bv 8 0]) (Headamp.HA_PREFIX ++ [Z_to_bv 8 0]) 13) with
    (StrFun.strncmp_walk (k ++ [Cursor.NUL]) (Headamp.HA_PREFIX ++ [Cursor.NUL]) 12).
  exact (hgw_cmp_walk k Headamp.HA_PREFIX 12 Hk hgw_prefix_nonul hgw_prefix_len).
Qed.

(* ======================================= C strings in a list of bytes ======================================= *)
Lemma hgw_nth_firstn : forall (l : list byte) n i, (i < n)%nat -> nth i (firstn n l) Cursor.NUL = nth i l Cursor.NUL.
Proof.
  induction l as [|x l IH]; intros n i H.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma hgw_nth_skipn : forall (l : list byte) a i, nth i (skipn a l) Cursor.NUL = nth (a + i) l Cursor.NUL.
Proof.
  induction l as [|x l IH]; intros a i.
  - rewrite skipn_nil. destruct i as [|i]; destruct (a + _)%nat; reflexivity.
  - destruct a as [|a]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma hgw_nul_idx_le : forall (l : list byte) i, (i < length l)%nat -> bv_unsigned (nth i l Cursor.NUL) = 0 ->
  (Cursor.nul_idx l <= i)%nat.
Proof.
  induction l as [|x l IH]; intros i Hi H; cbn [length] in Hi; [lia|]. cbn [Cursor.nul_idx].
  destruct (bv_unsigned x =? 0) eqn:E; [lia|].
  destruct i as [|i]; [cbn [nth] in H; apply Z.eqb_neq in E; contradiction|].
  cbn [nth] in H. specialize (IH i ltac:(lia) H). lia.
Qed.

Lemma hgw_nul_idx_bound : forall l : list byte, (Cursor.nul_idx l <= length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [Cursor.nul_idx length]; [lia|]. destruct (bv_unsigned x =? 0); lia.
Qed.

Lemma hgw_cstr_nul : forall l, (Cursor.nul_idx l < length l)%nat ->
  firstn (S (Cursor.nul_idx l)) l = Cursor.cstr l ++ [Cursor.NUL].
Proof.
  induction l as [|x l IH]; intros H; [cbn in H; lia|]. unfold Cursor.cstr in *. cbn [Cursor.nul_idx length] in *.
  destruct (bv_unsigned x =? 0) eqn:E.
  - cbn [firstn app]. f_equal. apply bv_eq. apply Z.eqb_eq in E. rewrite E. reflexivity.
  - cbn [firstn app]. f_equal. apply IH. lia.
Qed.

Lemma hgw_cstr_nonul : forall l, ~ In Cursor.NUL (Cursor.cstr l).
Proof.
  induction l as [|x l IH]; unfold Cursor.cstr in *; cbn [Cursor.nul_idx]; [cbn; tauto|].
  destruct (bv_unsigned x =? 0) eqn:E; cbn [firstn In]; [tauto|]. intros [Hx|Hx].
  - subst x. rewrite hgw_nul_u in E. cbn [Z.eqb] in E. discriminate E.
  - exact (IH Hx).
Qed.

Lemma hgw_nul_idx_nth : forall l : list byte, (Cursor.nul_idx l < length l)%nat ->
  bv_unsigned (nth (Cursor.nul_idx l) l Cursor.NUL) = 0.
Proof.
  induction l as [|b l IH]; [intros H; cbn in H; lia|].
  cbn [Cursor.nul_idx length].
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; intros H; cbn [nth]; [exact E|].
  apply IH. lia.
Qed.

Lemma hgw_nth_zbytes : forall (l : list byte) j, nth j (hd_zbytes l) 0 = bv_unsigned (nth j l Cursor.NUL).
Proof. unfold hd_zbytes. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

(* ======================================= the pair loop's tests ======================================= *)
(* spa_pod_get_string (body.h:224-237) of the child at cc, as the walk tests it: the size below 2^20, the type
   String (8), the size at least 1, the last body byte NUL. *)
Lemma hgw_gs : forall bs cc, 0 <= cc ->
  Spa.spa_get_string (Spa.child_at bs cc) =
  if (Spa.u32_at bs cc <? 2^20) && (Spa.u32_at bs (cc + 4) =? 8) && (1 <=? Spa.u32_at bs cc) &&
     (bv_unsigned (nth (Z.to_nat (cc + 8 + Spa.u32_at bs cc - 1)) bs Cursor.NUL) =? 0)
  then Some (Cursor.cstr (firstn (Z.to_nat (Spa.u32_at bs cc)) (skipn (Z.to_nat (cc + 8)) bs))) else None.
Proof.
  intros bs cc H0. unfold Spa.spa_get_string, Spa.child_at, Accessors.last_body_byte, Spa.SPA_POD_MAX_SIZE,
    Model.POD_STRING.
  cbn [Model.e_size Model.e_type Model.e_body].
  destruct (Spa.u32_at bs cc <? 2^20), (Spa.u32_at bs (cc + 4) =? 8); cbn [andb]; try reflexivity.
  destruct (1 <=? Spa.u32_at bs cc) eqn:E1; cbn [andb]; [|reflexivity].
  apply Z.leb_le in E1.
  rewrite hgw_nth_firstn by lia. rewrite hgw_nth_skipn.
  replace (Z.to_nat (cc + 8) + Z.to_nat (Spa.u32_at bs cc - 1))%nat
    with (Z.to_nat (cc + 8 + Spa.u32_at bs cc - 1)) by lia.
  reflexivity.
Qed.

(* the advance's arithmetic: ((CS + 7) | 7) + 1 = SPA_ROUND_UP_N (8 + CS, 8), a multiple of 8 *)
Lemma hgw_lor7 : forall z, 0 <= z -> z + 7 <= Z.lor (z + 7) 7 <= z + 14 /\
  Z.lor (z + 7) 7 + 1 = Spa.round_up8 (8 + z) /\ (Z.lor (z + 7) 7 + 1) mod 8 = 0.
Proof.
  intros z H. unfold Spa.round_up8. replace (8 + z - 1) with (z + 7) by lia. rewrite Spa.lor7 by lia.
  split; [Z.div_mod_to_equations; lia|]. split; [reflexivity|].
  replace (8 * ((z + 7) / 8) + 7 + 1) with (((z + 7) / 8 + 1) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma hgw_round_up8 : forall z, 0 <= z -> 8 + z <= Spa.round_up8 (8 + z) <= 8 + z + 7 /\
  Spa.round_up8 (8 + z) mod 8 = 0.
Proof.
  intros z H. destruct (hgw_lor7 z H) as (L1 & L2 & L3). rewrite <- L2. split; [lia | exact L3].
Qed.

(* spa_pod_is_inside (iter.h:31-37) on a child offset cc that is 0 mod 8 inside a Struct of at least 8 bytes *)
Lemma hgw_inside : forall bs r vs cc, r + 16 <= cc -> cc mod 8 = 0 -> 8 <= vs ->
  Spa.pod_is_inside bs (r + 16) vs cc = (cc - (r + 16) <=? vs - 8) && (Spa.u32_at bs cc <=? r + 8 + vs - cc).
Proof.
  intros bs r vs cc H1 H2 H3. unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining.
  replace (cc mod 4) with 0 by (Z.div_mod_to_equations; lia).
  rewrite (proj2 (Z.leb_le (r + 16) cc) H1), (proj2 (Z.leb_le 8 vs) H3). cbn [Z.eqb andb].
  replace (r + 16 + vs - (cc + 8)) with (r + 8 + vs - cc) by lia. reflexivity.
Qed.

(* A Struct of fewer than 8 bytes has no child. *)
Lemma hgw_inside_small : forall bs body vs cc, vs < 8 -> Spa.pod_is_inside bs body vs cc = false.
Proof.
  intros bs body vs cc H. unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside.
  rewrite (proj2 (Z.leb_gt 8 vs) H). destruct (cc mod 4 =? 0), (body <=? cc); reflexivity.
Qed.

(* What spa_pod_is_inside gives: the child's header and body lie in the Struct body. *)
Lemma hgw_inside_bounds : forall bs body vs cc, Spa.pod_is_inside bs body vs cc = true ->
  body <= cc /\ 8 <= vs /\ cc + 8 + Spa.u32_at bs cc <= body + vs.
Proof.
  intros bs body vs cc H. unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining in H.
  repeat match goal with Hb : (_ && _) = true |- _ => apply andb_prop in Hb as [? ?] end.
  repeat match goal with Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end.
  lia.
Qed.

Lemma hgw_u32_range : forall bs o, 0 <= Spa.u32_at bs o < 2 ^ 32.
Proof. intros bs o. apply Cursor.rd32_range. Qed.

(* ======================================= the engine's forms ======================================= *)
(* the symbolic values the engine forms for the pair loop's instructions (same in both images); U E v is v's value
   in the env E as an unsigned 64-bit number *)
Lemma hgw_U_off : forall E n v d, U E (SOff n 0) = v -> 0 <= v + d < 2 ^ 64 -> U E (SOff n d) = v + d.
Proof.
intros E n v d Hv Hd. pose proof (u64_range (ew E n)) as R. rewrite U_SOff in *. unfold zcanon, M64 in *.
rewrite Z.add_0_r, Z.mod_small in Hv by lia. rewrite Hv. apply Z.mod_small. lia.
Qed.

(* sub a1,s7,a4: s7 - a4 *)
Lemma hgw_U_subba : forall E n m a b, U E (SOff n 0) = a -> U E (SOff m 0) = b -> 0 <= a <= b ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit (-1))) (SOff m 0)) = b - a.
Proof.
intros E n m a b Ha Hb Hab. pose proof (U_range E (SOff m 0)) as Rb. rewrite Hb in Rb. unfold M64 in Rb.
rewrite U_SAlu, U_SMd, Ha, Hb, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_l by lia. replace (a * 18446744073709551615 + b) with ((b - a) + a * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* sub a2,s6,s7; add a0,a2,vs: s6 - s7 + vs *)
Lemma hgw_U_rest : forall E p q v a b c, U E (SOff p 0) = a -> U E (SOff q 0) = b -> U E (SOff v 0) = c ->
0 <= a -> 0 <= b -> 0 <= c -> 0 <= a - b + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff p 0) (SMd M_MUL (SOff q 0) (SLit 18446744073709551615))) (SOff v 0)) =
a - b + c.
Proof.
intros E p q v a b c Ha Hb Hc Ha0 Hb0 Hc0 Hr.
rewrite !U_SAlu, U_SMd, Ha, Hb, Hc, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_r, Z.add_mod_idemp_l by lia.
replace (a + b * 18446744073709551615 + c) with ((a - b + c) + b * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* lw of a u32 v: its sign extension *)
Lemma hgw_U_sext32 : forall E n v, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n v Hv Hr. rewrite U_SExt, Hv. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v) by lia. unfold bv_swrap, bv_wrap, zcanon, M64.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. apply Z.mod_small. lia.
- replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 31)) by lia.
  replace (v - 2 ^ 31 - 2 ^ 31) with ((v + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* the type test (bne of the sign-extended type word against 8) *)
Lemma hgw_U_sext32_eqb : forall E n v w, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? w) = (v =? w).
Proof.
intros E n v w Hv Hr Hw. rewrite (hgw_U_sext32 E n v Hv Hr).
destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
destruct (Z.eqb_spec (v + (2 ^ 64 - 2 ^ 32)) w); destruct (Z.eqb_spec v w); lia.
Qed.

(* s7 + ((CS + 7) | 7) + 1, the next child *)
Lemma hgw_U_next : forall E n m v cs, U E (SOff n 0) = v -> U E (SOff m 0) = cs -> 0 <= cs < 2 ^ 32 -> 0 <= v ->
v + Spa.round_up8 (8 + cs) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff n 0) (SAlu ALU_OR (SOff m 7) (SLit 7))) (SLit 1)) = v + Spa.round_up8 (8 + cs).
Proof.
intros E n m v cs Hv Hc Hcs Hv0 Hlt.
pose proof (hgw_lor7 cs ltac:(lia)) as (L1 & L2 & _).
rewrite !U_SAlu, Hv, (hgw_U_off E m cs 7 Hc ltac:(lia)), !U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
change (7 mod 2 ^ 64) with 7. change (1 mod 2 ^ 64) with 1.
rewrite (Z.mod_small (Z.lor (cs + 7) 7)) by lia. rewrite (Z.mod_small (v + Z.lor (cs + 7) 7)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.

(* andi a0,s7,3 of an aligned value *)
Lemma hgw_U_and3 : forall E e v, U E e = v -> v mod 4 = 0 -> U E (SAlu ALU_AND e (SLit 3)) = 0.
Proof.
intros E e v He Hv. rewrite U_SAlu, He, U_SLit. cbn [zalu_raw]. change (zcanon 3) with 3.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Hv. reflexivity.
Qed.

(* srli t,x,3; add t,t,s11: the shadow address of x, with s11 (atom 27) = SHADOW_OFF *)
Lemma hgw_U_shadow : forall E n v, U E (SOff n 0) = v -> U E (SOff 27 0) = SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 27 0)) = shadow_addr v.
Proof.
intros E n v Hn H27 Hv. rewrite !U_SAlu, Hn, H27, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= v / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold shadow_addr, zcanon, M64, SHADOW_OFF in *. rewrite (Z.mod_small (v / 8)) by lia. rewrite Z.mod_small by lia.
lia.
Qed.

(* ======================================= the model step of each way out ======================================= *)
Section g. Context {segs : list Segment}.
Local Notation pctx := (@hp_ctx segs).
Implicit Types x : pctx.

(* the key slot of the advance after a child with the key slot empty: the child itself when it is a String *)
Definition hgw_ko (x : pctx) (cc : Z) : option Z :=
match Spa.spa_get_string (Spa.child_at (hx_bs x) cc) with Some _ => Some cc | None => None end.

Lemma hgw_l2key_ko : forall x cc, hp_l2key x (hgw_ko x cc) = Spa.spa_get_string (Spa.child_at (hx_bs x) cc).
Proof.
  intros x cc. unfold hgw_ko. destruct (Spa.spa_get_string (Spa.child_at (hx_bs x) cc)) eqn:E; [|reflexivity].
  cbn [hp_l2key]. exact E.
Qed.

Lemma hgw_keyv_ko : forall x cc,
  hp_keyv x (hgw_ko x cc) = match Spa.spa_get_string (Spa.child_at (hx_bs x) cc) with
                            | Some _ => hx_P x + cc + 8 | None => 0 end.
Proof.
  intros x cc. unfold hgw_ko. destruct (Spa.spa_get_string (Spa.child_at (hx_bs x) cc)); reflexivity.
Qed.

(* a pending key's text *)
Lemma hgw_kstr : forall x ck, hp_key_ok x ck -> hp_l2key x (Some ck) = Some (hp_kstr x ck).
Proof.
  intros x ck (_ & _ & Hgs). cbn [hp_l2key]. unfold hp_kstr.
  destruct (Spa.spa_get_string (Spa.child_at (hx_bs x) ck)); [reflexivity | contradiction].
Qed.

(* the walk's end: the child at cc is not inside the Struct body *)
Lemma hgw_walk_exit : forall x r cc n ko cl keys rf, hp_m_walk x r cc (S n) ko cl keys rf ->
  Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false -> hp_m_exit x cl keys rf.
Proof.
  intros x r cc n ko cl keys rf (Hnull & _ & _ & _ & _ & _ & Hst & HW) Hin.
  unfold hp_vs in Hin. rewrite hp_walk_pairs_step, Hin in HW.
  split; [exact Hnull|]. split; [exact Hst|]. rewrite HW. reflexivity.
Qed.

(* the child at cc with the key slot empty: the advance with the key slot spa_pod_get_string gives *)
Lemma hgw_walk_adv0 : forall x r cc n cl keys rf, hp_m_walk x r cc (S n) None cl keys rf -> hp_child_in x r cc ->
  hp_m_adv x r cc n (hgw_ko x cc) cl keys rf.
Proof.
  intros x r cc n cl keys rf (Hnull & Hst & Hc1 & Hc8 & Hn & _ & Hs & HW) Hin.
  pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
  pose proof (hgw_inside_bounds _ _ _ _ Hin) as (B1 & B2 & B3).
  split; [exact Hnull|]. split; [exact Hst|]. split; [lia|]. split; [exact Hc8|]. split; [exact Hin|].
  split; [exact Hn|]. split.
  { intros ck Hck. unfold hgw_ko in Hck.
    destruct (Spa.spa_get_string (Spa.child_at (hx_bs x) cc)) eqn:E; [|discriminate Hck].
    injection Hck as <-. split; [lia|]. split; [lia|]. rewrite E. discriminate. }
  split; [exact Hs|].
  rewrite HW, hgw_l2key_ko. change (hp_l2key x None) with (@None (list byte)).
  rewrite hp_walk_pairs_step. unfold hp_child_in, hp_vs in Hin. rewrite Hin. reflexivity.
Qed.

(* the child at cc with the pending key ck whose text has no prefix: the pair is skipped *)
Lemma hgw_walk_skip : forall x r cc n ck cl keys rf, hp_m_walk x r cc (S n) (Some ck) cl keys rf ->
  hp_child_in x r cc -> Headamp.ha_prefix (hp_kstr x ck) = false -> hp_m_adv x r cc n None cl keys rf.
Proof.
  intros x r cc n ck cl keys rf (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW) Hin HP.
  split; [exact Hnull|]. split; [exact Hst|]. split; [lia|]. split; [exact Hc8|]. split; [exact Hin|].
  split; [exact Hn|]. split; [intros ck' Hck'; discriminate Hck'|]. split; [exact Hs|].
  rewrite HW, (hgw_kstr x ck (HK ck eq_refl)), hp_walk_pairs_step. unfold hp_child_in, hp_vs in Hin. rewrite Hin.
  cbv iota beta. rewrite hp_ha_fold_cons, HP. reflexivity.
Qed.

(* the child at cc with the pending key ck whose text has the prefix: the key cut *)
Lemma hgw_walk_key : forall x r cc n ck cl keys rf, hp_m_walk x r cc (S n) (Some ck) cl keys rf ->
  hp_child_in x r cc -> Headamp.ha_prefix (hp_kstr x ck) = true -> hp_m_key x r cc n ck cl keys rf.
Proof.
  intros x r cc n ck cl keys rf (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW) Hin HP.
  split; [exact Hnull|]. split; [exact Hst|]. split; [lia|]. split; [exact Hc8|]. split; [exact Hin|].
  split; [exact Hn|]. split; [exact (HK ck eq_refl)|]. split; [exact Hs|]. split; [exact HP|].
  rewrite HW, (hgw_kstr x ck (HK ck eq_refl)), hp_walk_pairs_step. unfold hp_child_in, hp_vs in Hin. rewrite Hin.
  cbv iota beta. rewrite hp_ha_fold_cons, HP. reflexivity.
Qed.

(* the next child *)
Lemma hgw_next_bounds : forall x r cc, hp_st_ok x r -> r + 16 <= cc -> cc mod 8 = 0 -> hp_child_in x r cc ->
  cc + 8 <= hp_next x cc <= r + 16 + hp_vs x r + 7 /\ hp_next x cc mod 8 = 0 /\
  hp_next x cc = cc + Z.lor (Spa.u32_at (hx_bs x) cc + 7) 7 + 1.
Proof.
  intros x r cc Hst Hc1 Hc8 Hin.
  pose proof (hgw_inside_bounds _ _ _ _ Hin) as (B1 & B2 & B3).
  pose proof (hgw_u32_range (hx_bs x) cc) as R.
  destruct (hgw_lor7 (Spa.u32_at (hx_bs x) cc) ltac:(lia)) as (L1 & L2 & L3).
  unfold hp_next. rewrite <- L2. split; [lia|]. split; [|lia].
  rewrite Z.add_mod, Hc8, L3 by lia. reflexivity.
Qed.

(* the advance to the next child: the loop's head there, with one pass of fuel less *)
Lemma hgw_adv_walk : forall x r cc n ko cl keys rf, hp_m_adv x r cc n ko cl keys rf ->
  hp_m_walk x r (hp_next x cc) n ko cl keys rf.
Proof.
  intros x r cc n ko cl keys rf (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HK & Hs & HW).
  pose proof (hgw_inside_bounds _ _ _ _ Hin) as (B1 & B2 & B3).
  destruct (hgw_next_bounds x r cc Hst Hc1 Hc8 Hin) as (N1 & N2 & _).
  split; [exact Hnull|]. split; [exact Hst|]. split; [lia|].
  split; [exact N2|]. split; [lia|].
  split; [exact HK|]. split; [exact Hs | exact HW].
Qed.

(* ======================================= the pending key's bytes ======================================= *)
(* The key text of the String child at ck: no NUL inside, its bytes and its NUL in the child's body. *)
Lemma hgw_key_bytes : forall x ck, hp_key_ok x ck ->
  ~ In (Z_to_bv 8 0) (hp_kstr x ck) /\
  ck + 8 + Z.of_nat (length (hp_kstr x ck)) + 1 <= ck + 8 + Spa.u32_at (hx_bs x) ck /\
  ck + 8 + Spa.u32_at (hx_bs x) ck <= hx_len x /\
  (forall i, (i < length (hp_kstr x ck))%nat ->
     nth (Z.to_nat (ck + 8) + i) (hx_bs x) Cursor.NUL = nth i (hp_kstr x ck) Cursor.NUL) /\
  bv_unsigned (nth (Z.to_nat (ck + 8) + length (hp_kstr x ck)) (hx_bs x) Cursor.NUL) = 0.
Proof.
  intros x ck (Hck & Hin & Hgs). unfold hp_kstr.
  rewrite (hgw_gs (hx_bs x) ck Hck) in Hgs |- *.
  match goal with |- context [if ?t then _ else _] => destruct t eqn:ET end;
  [|exfalso; apply Hgs; rewrite ?ET; reflexivity].
  apply andb_prop in ET as [ET1 E4]. apply andb_prop in ET1 as [_ E3].
  apply Z.leb_le in E3. apply Z.eqb_eq in E4.
  unfold hx_len in Hin |- *.
  set (CS := Spa.u32_at (hx_bs x) ck) in *.
  remember (firstn (Z.to_nat CS) (skipn (Z.to_nat (ck + 8)) (hx_bs x))) as body eqn:EB.
  assert (LB : length body = Z.to_nat CS) by (subst body; rewrite length_firstn, length_skipn; lia).
  assert (EBn : forall k, (k < Z.to_nat CS)%nat ->
    nth k body Cursor.NUL = nth (Z.to_nat (ck + 8) + k) (hx_bs x) Cursor.NUL).
  { intros k Hk. rewrite EB. rewrite hgw_nth_firstn by exact Hk. apply hgw_nth_skipn. }
  assert (NB : bv_unsigned (nth (Z.to_nat CS - 1) body Cursor.NUL) = 0).
  { rewrite EBn by lia.
    replace (Z.to_nat (ck + 8) + (Z.to_nat CS - 1))%nat with (Z.to_nat (ck + 8 + CS - 1)) by lia. exact E4. }
  pose proof (hgw_nul_idx_le body (Z.to_nat CS - 1) ltac:(lia) NB) as NI.
  assert (LC : length (Cursor.cstr body) = Cursor.nul_idx body).
  { unfold Cursor.cstr. rewrite length_firstn. pose proof (hgw_nul_idx_bound body). lia. }
  rewrite LC.
  split; [exact (hgw_cstr_nonul body)|]. split; [lia|]. split; [lia|]. split.
  - intros i Hi. unfold Cursor.cstr. rewrite hgw_nth_firstn by lia. rewrite EBn by lia. reflexivity.
  - rewrite <- EBn by lia. apply hgw_nul_idx_nth. lia.
Qed.

(* the pod's u32 at offset o and its byte at offset o, in any memory that holds the pod (role's pod_u32 / pod_u8) *)
Lemma hgw_nth_error_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma hgw_nth_error_firstn_lt : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros A l. induction l as [|a l IH]; intros n i Hi.
  - destruct n; destruct i; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma hgw_nth_error_skipn_add : forall {A} (l : list A) m i, nth_error (skipn m l) i = nth_error l (m + i).
Proof.
  intros A l m. revert l. induction m as [|m IH]; intros l i; [reflexivity|].
  destruct l as [|a l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma hgw_pod_u32 : forall (m : word -> option byte) (P : Z) (bs : list byte) o,
  garr8 segs m P (hd_zbytes bs) -> 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  val_mem segs m (P + o) 4 (Spa.u32_at bs o).
Proof.
  intros m P bs o HG Ho Ho4 kk Hkk.
  assert (Hj : (Z.to_nat o + kk < length (hd_zbytes bs))%nat) by (unfold hd_zbytes; rewrite length_map; lia).
  pose proof (garr8_mbyte segs m P (hd_zbytes bs) _ HG Hj) as Hm.
  replace (P + Z.of_nat (Z.to_nat o + kk)) with (P + o + Z.of_nat kk) in Hm by lia.
  rewrite Hm. f_equal.
  set (l := firstn 4 (skipn (Z.to_nat o) bs)).
  assert (Hl : length l = 4%nat) by (subst l; rewrite length_firstn, length_skipn; lia).
  pose proof (Cursor.rd32_range (skipn (Z.to_nat o) bs)) as Hr.
  change (Spa.u32_at bs o) with (bytes_le_to_Z l).
  change (Cursor.rd32 (skipn (Z.to_nat o) bs)) with (bytes_le_to_Z l) in Hr.
  rewrite le_byte_small by (cbn; lia).
  assert (E1 : nth_error l kk = Some (Z_to_bv 8 (Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat kk)))).
  { rewrite <- (YA0d.Z_to_le_bytes_to_Z l) at 1. rewrite Hl. apply hgw_nth_error_le_bytes. exact Hkk. }
  assert (E2 : nth_error l kk = nth_error bs (Z.to_nat o + kk)).
  { subst l. rewrite hgw_nth_error_firstn_lt by exact Hkk. apply hgw_nth_error_skipn_add. }
  rewrite E2 in E1.
  rewrite hgw_nth_zbytes, (nth_error_nth _ _ Cursor.NUL E1). apply Z_to_bv_bv_unsigned.
Qed.

Lemma hgw_pod_u8 : forall (m : word -> option byte) (P : Z) (bs : list byte) o,
  garr8 segs m P (hd_zbytes bs) -> 0 <= o -> o < Z.of_nat (length bs) ->
  val_mem segs m (P + o) 1 (bv_unsigned (nth (Z.to_nat o) bs Cursor.NUL)) /\
  0 <= bv_unsigned (nth (Z.to_nat o) bs Cursor.NUL) < 256.
Proof.
  intros m P bs o HG Ho Hlt. rewrite <- hgw_nth_zbytes.
  apply garr8_nthZ; [exact HG | exact Ho |]. unfold hd_zbytes. rewrite length_map. lia.
Qed.

(* A sub-list of the pod's bytes, in any memory that holds the pod. *)
Lemma hgw_garr8_sub : forall (m : word -> option byte) (P : Z) (bs l : list byte) (o : Z),
  garr8 segs m P (hd_zbytes bs) -> 0 <= o -> o + Z.of_nat (length l) <= Z.of_nat (length bs) ->
  (forall i, (i < length l)%nat -> nth (Z.to_nat o + i) bs Cursor.NUL = nth i l Cursor.NUL) ->
  garr8 segs m (P + o) (hd_zbytes l).
Proof.
  intros m P bs l o HG Ho Hl Hn j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
  assert (Hj' : (Z.to_nat o + j < length (hd_zbytes bs))%nat) by (unfold hd_zbytes; rewrite length_map; lia).
  destruct (HG _ Hj') as [Hv Hr].
  replace (P + Z.of_nat (Z.to_nat o + j)) with (P + o + Z.of_nat j) in Hv by lia.
  rewrite hgw_nth_zbytes in Hv, Hr |- *. rewrite (Hn j Hj) in Hv, Hr. split; [exact Hv | exact Hr].
Qed.

(* The pending key at P + ck + 8, its bytes and NUL, in any memory that holds the pod. *)
Lemma hgw_key_garr8 : forall (m : word -> option byte) x ck,
  garr8 segs m (hx_P x) (hd_zbytes (hx_bs x)) -> hp_key_ok x ck ->
  garr8 segs m (hx_P x + ck + 8) (hd_zbytes (hp_kstr x ck) ++ [0]).
Proof.
  intros m x ck HG HK.
  pose proof HK as (Hck & _ & _).
  destruct (hgw_key_bytes x ck HK) as (_ & L1 & L2 & Hb & Hz).
  unfold hx_len in L2.
  apply (proj2 (garr8_app segs m (hx_P x + ck + 8) (hd_zbytes (hp_kstr x ck)) [0])). split.
  - replace (hx_P x + ck + 8) with (hx_P x + (ck + 8)) by lia.
    apply (hgw_garr8_sub m (hx_P x) (hx_bs x) (hp_kstr x ck) (ck + 8) HG); [lia | lia | exact Hb].
  - replace [0] with (hd_zbytes [Cursor.NUL]) by reflexivity.
    assert (LZ : length (hd_zbytes (hp_kstr x ck)) = length (hp_kstr x ck)) by (unfold hd_zbytes; apply length_map).
    rewrite LZ.
    replace (hx_P x + ck + 8 + Z.of_nat (length (hp_kstr x ck)))
      with (hx_P x + (ck + 8 + Z.of_nat (length (hp_kstr x ck)))) by lia.
    apply (hgw_garr8_sub m (hx_P x) (hx_bs x) [Cursor.NUL]); [exact HG | lia | cbn [length]; lia |].
    intros i Hi. cbn [length] in Hi. assert (i = 0%nat) as -> by lia.
    replace (Z.to_nat (ck + 8 + Z.of_nat (length (hp_kstr x ck))) + 0)%nat
      with (Z.to_nat (ck + 8) + length (hp_kstr x ck))%nat by lia.
    cbn [nth]. apply bv_eq. rewrite Hz. reflexivity.
Qed.

(* Every byte after e up to the end of e's 8-byte word is readable when e lies in a range of 8-byte words that the
   memory holds: the tail of a key's NUL inside the pod. *)
Lemma hgw_str_tail : forall (H : word -> bool) (mem : word -> option byte) (P : Z) (l : list Z) (e : Z),
  garr8 segs (mrestrict H mem) P l -> P mod 8 = 0 -> Z.of_nat (length l) mod 8 = 0 ->
  P <= e < P + Z.of_nat (length l) -> hd_str_tail (aview segs H mem) e.
Proof.
  intros H mem P l e HG HP8 HL8 He a Ha.
  assert (Hb : a < P + Z.of_nat (length l)).
  { pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
    assert ((P + Z.of_nat (length l)) mod 8 = 0) by (rewrite Z.add_mod, HP8, HL8 by lia; reflexivity).
    Z.div_mod_to_equations. lia. }
  pose proof (garr8_mbyte segs (mrestrict H mem) P l (Z.to_nat (a - P)) HG ltac:(lia)) as M.
  rewrite Z2Nat.id in M by lia. replace (P + (a - P)) with a in M by lia.
  unfold aview. rewrite M. discriminate.
Qed.

End g.

Print Assumptions hgw_strncmp_prefix.
Print Assumptions hgw_walk_adv0.
Print Assumptions hgw_walk_key.
Print Assumptions hgw_adv_walk.
Print Assumptions hgw_key_garr8.
