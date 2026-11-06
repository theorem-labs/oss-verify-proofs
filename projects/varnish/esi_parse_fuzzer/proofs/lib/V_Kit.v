(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land7_of_mod8 : forall x, 0 <= x -> x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x Hx Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact Hm. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod8_of_mod16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. assert (E : x = 8 * (2 * (x / 16))) by lia. rewrite E at 1. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac klia K := first [rewrite Z.mod_small in K by lia | idtac]; lia.

(* [comment removed for export] *)
Lemma lxor_2_63 : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor. { reflexivity. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec i 63) as [Hlt|Hge].
  - rewrite (Z.pow2_bits_false 63 i) by lia. apply Bool.andb_false_r.
  - destruct (Z.eqb_spec i 63) as [->|Hne].
    + replace (Z.testbit x 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    + rewrite (Z.pow2_bits_false 63 i) by lia. apply Bool.andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite Z.mod_small; lia.
Qed.
Lemma signed_lit_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply signed_lit. lia. Qed.

(* [comment removed for export] *)
Ltac unsign K :=
  repeat match type of K with
  | context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_2_63 x) in K by lia
  | context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit x) in K by lia
  end.

(* [comment removed for export] *)
Ltac shl1_to_mul :=
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => replace (Z.shiftl x 1) with (2 * x) by (rewrite Z.shiftl_mul_pow2 by lia; lia)
  end.

(* [comment removed for export] *)
Lemma align16_add : forall s d, s mod 16 = 0 -> d mod 16 = 0 -> (s + d) mod 16 = 0.
Proof. intros s d Hs Hd. rewrite Z.add_mod, Hs, Hd by lia. reflexivity. Qed.
Lemma align_mod8_of16 : forall s d, s mod 16 = 0 -> d mod 8 = 0 -> (s + d) mod 8 = 0.
Proof. intros s d Hs Hd. rewrite Z.add_mod, (mod8_of_mod16 s Hs), Hd by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_cells_read_sub : forall segs m A cs (k : Z) n,
  rw_cells segs m A cs -> (0 <= k)%Z -> (Z.to_nat k + n <= cells_size cs)%nat ->
  ov_read_bytes segs m (wa (A + k)) n = Some (firstn n (skipn (Z.to_nat k) (cells_bytes cs))).
Proof.
  intros segs m A cs k n [[Hwf HB] _] Hk Hn.
  apply bytes_at_read; [exact HB | exact Hk | rewrite cells_bytes_length by exact Hwf; exact Hn].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac dead K :=
  exfalso;
  first [ klia K
        | unsign K; klia K
        | (* [comment removed for export] *)
          let t := type of K in
          lazymatch t with
          | context [le_bytes_to_word _] => fail
          | context [seg_rom _] => fail
          | _ => let t' := eval vm_compute in t in change t' in K; first [congruence | discriminate | lia]
          end ].

(* [comment removed for export] *)
Lemma le1_single : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - ((first [ intro dR_2; dand3 dR_2 as Ha Hl H | intros (Ha & Hl & H) ])). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hl1 & W1) & (Ha2 & Hl2 & W2)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
    intros i Hi. destruct (Z_lt_le_dec i n1).
    + apply W1. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply W2. lia.
Qed.

Lemma u8arr_app : forall segs m a bs1 bs2,
  u8arr segs m a (bs1 ++ bs2) <-> u8arr segs m a bs1 /\ u8arr segs m (a + Z.of_nat (length bs1)) bs2.
Proof.
  intros segs m a bs1 bs2. unfold u8arr. rewrite bytes_at_app, app_length, Nat2Z.inj_add.
  rewrite (wr_at_app segs m a (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) by lia. tauto.
Qed.

(* [comment removed for export] *)
Lemma u8arr_window : forall segs m a bs k n,
  u8arr segs m a bs -> (k + n <= length bs)%nat ->
  u8arr segs m a (firstn k bs) /\
  u8arr segs m (a + Z.of_nat k) (firstn n (skipn k bs)) /\
  u8arr segs m (a + Z.of_nat k + Z.of_nat n) (skipn (k + n) bs).
Proof.
  intros segs m a bs k n U Hkn.
  rewrite <- (firstn_skipn k bs) in U. apply u8arr_app in U. destruct U as [U1 U23].
  rewrite firstn_length_le in U23 by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in U23. apply u8arr_app in U23. destruct U23 as [U2 U3].
  rewrite firstn_length_le in U3 by (rewrite skipn_length; lia).
  rewrite skipn_skipn, Nat.add_comm in U3.
  split; [exact U1| split; [exact U2| exact U3]].
Qed.

Lemma u8arr_unwindow : forall segs m a pre mid post,
  u8arr segs m a pre -> u8arr segs m (a + Z.of_nat (length pre)) mid ->
  u8arr segs m (a + Z.of_nat (length pre) + Z.of_nat (length mid)) post ->
  u8arr segs m a (pre ++ mid ++ post).
Proof.
  intros segs m a pre mid post U1 U2 U3.
  apply u8arr_app. split; [exact U1|]. apply u8arr_app. split; [exact U2| exact U3].
Qed.

(* [comment removed for export] *)
Lemma lxor_ones : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = 18446744073709551615 - w.
Proof.
  intros w Hw. rewrite lnot_mod64 by lia. unfold Z.lnot. change (2^64) with 18446744073709551616.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
Qed.
(* [comment removed for export] *)
Ltac wrap_reg a b :=
  replace (Z_to_bv 64 a) with (Z_to_bv 64 b)
    by (apply Z_to_bv_eqm; first [ reflexivity | lia
       | rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia
       | rewrite <- (Z.mod_add _ (-1)) by lia; f_equal; lia ]).

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".

Ltac2 vk_is_eq (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h _ => match Constr.Unsafe.kind h with Constr.Unsafe.Ind _ _ => Constr.equal h '@eq | _ => false end
  | _ => false
  end.
Ltac2 rec vk_arith_logic (t : constr) : bool :=
  if zt_plain_arith t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@or then (if vk_arith_logic (Array.get args 0) then vk_arith_logic (Array.get args 1) else false)
          else if Constr.equal h '@and then (if vk_arith_logic (Array.get args 0) then vk_arith_logic (Array.get args 1) else false)
          else false
      | Constr.Unsafe.Constant _ _ =>
          (* [comment removed for export] *)
          if Constr.equal h '@not then (let a := Array.get args 0 in if vk_is_eq a then false else vk_arith_logic a) else false
      | _ => false
      end
  | Constr.Unsafe.Prod _ b =>
      (* [comment removed for export] *)
      if Constr.equal b 'False then
        (match Constr.Unsafe.kind t with
         | Constr.Unsafe.Prod bd _ => if vk_is_eq (Constr.Binder.type bd) then false else true
         | _ => true end)
      else false
  | _ => false
  end.

Ltac2 vk_prune () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if vk_arith_logic ty then None
                          else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac vk_lia_prune := ltac2:(Control.enter vk_prune).

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | vk_lia_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Lemma rw_cells_recast : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf HB] HW] Hwf' E. split; [split; [exact Hwf'|]|].
  - rewrite E. exact HB.
  - rewrite <- (cells_bytes_length cs') by exact Hwf'. rewrite E. rewrite cells_bytes_length by exact Hwf. exact HW.
Qed.

(* [comment removed for export] *)
Lemma all_zero_CB : forall segs m A n junk,
  rw_cells segs m A [CB n junk] -> (forall i, (0 <= i < Z.of_nat n)%Z -> m (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0)) ->
  junk = repeat (Z_to_bv 8 0) n.
Proof.
  intros segs m A n junk [[Hwf HB] _] Z0. cbn in Hwf. destruct Hwf as [Hn _]. subst n.
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. (first [ dand3 HB as _ _ HB | destruct HB as (_ & _ & HB) ]).
  apply nth_error_ext. intros i.
  destruct (Nat.ltb_spec i (length junk)) as [Hi|Hi].
  - rewrite <- (HB i Hi). unfold mrd, wa. rewrite (Z0 (Z.of_nat i)) by lia.
    rewrite nth_error_repeat by exact Hi. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.
