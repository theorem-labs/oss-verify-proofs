(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str_bytes : forall fs,
  map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string fs) ++ [Z_to_bv 8 0] = zb (str fs ++ [0]).
Proof.
  intros fs. unfold zb, str. rewrite map_app, map_map. cbn [map]. f_equal.
  apply map_ext. intros a. f_equal. unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma str_range : forall fs, Forall (fun c => 0 <= c < 256) (str fs ++ [0]).
Proof.
  intros fs. apply Forall_app. split; [| constructor; [lia | constructor]].
  unfold str. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (a & <- & _).
  pose proof (N_ascii_bounded a). lia.
Qed.

Lemma length_list_ascii_of_string : forall s, length (list_ascii_of_string s) = String.length s.
Proof. induction s as [|c s IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma str_length : forall fs, zlength (str fs) = Z.of_nat (String.length fs).
Proof. intros fs. unfold zlength, str. rewrite length_map, length_list_ascii_of_string. reflexivity. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma udigits_aux_length : forall f b n acc, (length (udigits_aux f b n acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros b n acc; cbn; [lia|].
  destruct (n <=? 0); [cbn; lia|]. eapply Nat.le_trans; [apply IH|]. cbn. lia.
Qed.
Lemma udigits_zlength : forall b n, zlength (udigits b n) <= 64.
Proof.
  intros. unfold zlength, udigits. pose proof (udigits_aux_length 64 b n []) as L.
  remember (udigits_aux 64 b n []) as d eqn:E. clear E. cbn [length Nat.add] in L. lia.
Qed.

Lemma int_pieces_bound : forall neg d, zlength d <= 64 -> zlength (List.concat (Fmt.int_pieces neg d)) <= 65.
Proof. intros neg d Hd. rewrite int_pieces_len. destruct neg; lia. Qed.

Definition farg_len (a : farg) : Z := match a with AStr s => zlength s | AInt _ => 0 end.

Lemma conv_len_bound : forall c a, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.conv_ok c a = true -> conv_len c a <= 80 + farg_len a.
Proof.
  intros c a OK. unfold conv_len, farg_len. destruct c; destruct a as [v|sv]; try discriminate OK; cbn [Fmt.conv_pieces].
  - pose proof (int_pieces_bound (s32 v <? 0) (dec_udigits (Z.abs (s32 v))) (udigits_zlength _ _)). lia.
  - pose proof (int_pieces_bound false (dec_udigits (u32 v)) (udigits_zlength _ _)). lia.
  - pose proof (udigits_zlength 16 (u32 v)) as L. unfold hex_udigits.
    remember (udigits 16 (u32 v)) as d eqn:Ed. clear Ed. pose proof (zlength_nonneg d) as L0.
    cbn [List.concat]. rewrite concat_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. change (zlength (@nil Z)) with 0.
    assert (A1 : zlength (List.concat (if zlength d + (if u32 v =? 0 then 1 else 0) <? 8
                                        then [zeros (8 - (zlength d + (if u32 v =? 0 then 1 else 0)))] else [])) <= 8).
    { destruct (Z.ltb_spec (zlength d + (if u32 v =? 0 then 1 else 0)) 8); cbn [List.concat].
      - rewrite app_nil_r. unfold zeros. rewrite zlength_zrepeat; [| destruct (u32 v =? 0); lia]. destruct (u32 v =? 0); lia.
      - change (zlength (@nil Z)) with 0. lia. }
    assert (A2 : zlength (List.concat match d with [] => [[48]; []] | _ :: _ => [d] end) <= 64).
    { destruct d; cbn [List.concat]; rewrite ?app_nil_r; [change (zlength [48]) with 1; lia | exact L]. }
    lia.
  - cbn [List.concat]. rewrite app_nil_r. cbn [app]. lia.
  - pose proof (int_pieces_bound false (dec_udigits (u64 v)) (udigits_zlength _ _)). lia.
Qed.

Fixpoint fargs_len (args : list farg) : Z :=
  match args with [] => 0 | a :: args' => 80 + farg_len a + fargs_len args' end.
Lemma fargs_len_nonneg : forall args, 0 <= fargs_len args.
Proof. induction args as [|a args IH]; cbn; [lia|]. destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; lia. Qed.

(* [comment removed for export] *)
Lemma fmt_output_bound_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  zlength (fmt_output (parse_fmt_aux fuel s) args) <= zlength s + fargs_len args.
Proof.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn in OK. destruct args; [| discriminate]. cbn. lia.
  - destruct s as [|c s0].
    { cbn in OK. destruct args; [| discriminate]. cbn. lia. }
    cbn in Hlen. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      unfold fmt_output. cbn [fmt_pieces hd tl]. rewrite zlength_concat_cons, zlength_concat_app. change (zlength (@nil Z)) with 0.
      fold (fmt_output (parse_fmt_aux f r') args'). fold (conv_len cv a).
      pose proof (conv_len_bound cv a OKc) as CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr.
      cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      unfold fmt_output. cbn [fmt_pieces]. rewrite zlength_concat_cons. fold (fmt_output (parse_fmt_aux f r) args).
      pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

Lemma fmt_output_bound : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (fmt_output (fmt fs) args) <= zlength (str fs) + fargs_len args.
Proof. intros fs args OK. unfold fmt, parse_fmt in *. apply fmt_output_bound_aux; [lia | exact OK]. Qed.

(* [comment removed for export] *)




(* [comment removed for export] *)
Lemma mod32_of_mod64 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. intros z. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.
Lemma s32_facts : forall z, -2^31 <= s32 z < 2^31 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = s32 z mod 2^32.
Proof.
  intros z. unfold s32. rewrite unsigned_lit_wrap, mod32_of_mod64.
  split; [Z.div_mod_to_equations; lia|].
  replace ((z + 2^31) mod 2^32 - 2^31) with (z - ((z + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r. rewrite Z_mod_mult. rewrite Z.sub_0_r. reflexivity.
Qed.
Lemma u32_facts : forall z, 0 <= u32 z < 2^32 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = u32 z.
Proof. intros z. unfold u32. rewrite unsigned_lit_wrap, mod32_of_mod64. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.
Lemma u64_facts : forall z, 0 <= u64 z < 2^64 /\ bv_unsigned (Z_to_bv 64 z : word) = u64 z.
Proof. intros z. unfold u64. rewrite unsigned_lit_wrap. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.

(* [comment removed for export] *)
Definition pad8 (x : Z) : Z := (- x) mod 8.
Lemma pad8_range : forall x, 0 <= pad8 x < 8.
Proof. intros. unfold pad8. Z.div_mod_to_equations. lia. Qed.
Lemma pad8_align : forall x b, 0 <= x -> x <= b -> b mod 8 = 0 -> x + pad8 x <= b.
Proof.
  intros x b Hx Hb Hal. unfold pad8.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E2.
  set (q1 := - x / 8) in *. set (r1 := (- x) mod 8) in *. set (q2 := b / 8) in *. clearbody q1 r1 q2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str_bytes : forall fs,
  map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string fs) ++ [Z_to_bv 8 0] = zb (str fs ++ [0]).
Proof.
  intros fs. unfold zb, str. rewrite map_app, map_map. cbn [map]. f_equal.
  apply map_ext. intros a. f_equal. unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma str_range : forall fs, Forall (fun c => 0 <= c < 256) (str fs ++ [0]).
Proof.
  intros fs. apply Forall_app. split; [| constructor; [lia | constructor]].
  unfold str. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (a & <- & _).
  pose proof (N_ascii_bounded a). lia.
Qed.

Lemma length_list_ascii_of_string : forall s, length (list_ascii_of_string s) = String.length s.
Proof. induction s as [|c s IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma str_length : forall fs, zlength (str fs) = Z.of_nat (String.length fs).
Proof. intros fs. unfold zlength, str. rewrite length_map, length_list_ascii_of_string. reflexivity. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma udigits_aux_length : forall f b n acc, (length (udigits_aux f b n acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros b n acc; cbn; [lia|].
  destruct (n <=? 0); [cbn; lia|]. eapply Nat.le_trans; [apply IH|]. cbn. lia.
Qed.
Lemma udigits_zlength : forall b n, zlength (udigits b n) <= 64.
Proof.
  intros. unfold zlength, udigits. pose proof (udigits_aux_length 64 b n []) as L.
  remember (udigits_aux 64 b n []) as d eqn:E. clear E. cbn [length Nat.add] in L. lia.
Qed.

Lemma int_pieces_bound : forall neg d, zlength d <= 64 -> zlength (List.concat (Fmt.int_pieces neg d)) <= 65.
Proof. intros neg d Hd. rewrite int_pieces_len. destruct neg; lia. Qed.

Definition farg_len (a : farg) : Z := match a with AStr s => zlength s | AInt _ => 0 end.

Lemma conv_len_bound : forall c a, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.conv_ok c a = true -> conv_len c a <= 80 + farg_len a.
Proof.
  intros c a OK. unfold conv_len, farg_len. destruct c; destruct a as [v|sv]; try discriminate OK; cbn [Fmt.conv_pieces].
  - pose proof (int_pieces_bound (s32 v <? 0) (dec_udigits (Z.abs (s32 v))) (udigits_zlength _ _)). lia.
  - pose proof (int_pieces_bound false (dec_udigits (u32 v)) (udigits_zlength _ _)). lia.
  - pose proof (udigits_zlength 16 (u32 v)) as L. unfold hex_udigits.
    remember (udigits 16 (u32 v)) as d eqn:Ed. clear Ed. pose proof (zlength_nonneg d) as L0.
    cbn [List.concat]. rewrite concat_app, !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. change (zlength (@nil Z)) with 0.
    assert (A1 : zlength (List.concat (if zlength d + (if u32 v =? 0 then 1 else 0) <? 8
                                        then [zeros (8 - (zlength d + (if u32 v =? 0 then 1 else 0)))] else [])) <= 8).
    { destruct (Z.ltb_spec (zlength d + (if u32 v =? 0 then 1 else 0)) 8); cbn [List.concat].
      - rewrite app_nil_r. unfold zeros. rewrite zlength_zrepeat; [| destruct (u32 v =? 0); lia]. destruct (u32 v =? 0); lia.
      - change (zlength (@nil Z)) with 0. lia. }
    assert (A2 : zlength (List.concat match d with [] => [[48]; []] | _ :: _ => [d] end) <= 64).
    { destruct d; cbn [List.concat]; rewrite ?app_nil_r; [change (zlength [48]) with 1; lia | exact L]. }
    lia.
  - cbn [List.concat]. rewrite app_nil_r. cbn [app]. lia.
  - pose proof (int_pieces_bound false (dec_udigits (u64 v)) (udigits_zlength _ _)). lia.
Qed.

Fixpoint fargs_len (args : list farg) : Z :=
  match args with [] => 0 | a :: args' => 80 + farg_len a + fargs_len args' end.
Lemma fargs_len_nonneg : forall args, 0 <= fargs_len args.
Proof. induction args as [|a args IH]; cbn; [lia|]. destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; lia. Qed.

(* [comment removed for export] *)
Lemma fmt_output_bound_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  zlength (fmt_output (parse_fmt_aux fuel s) args) <= zlength s + fargs_len args.
Proof.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn in OK. destruct args; [| discriminate]. cbn. lia.
  - destruct s as [|c s0].
    { cbn in OK. destruct args; [| discriminate]. cbn. lia. }
    cbn in Hlen. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      unfold fmt_output. cbn [fmt_pieces hd tl]. rewrite zlength_concat_cons, zlength_concat_app. change (zlength (@nil Z)) with 0.
      fold (fmt_output (parse_fmt_aux f r') args'). fold (conv_len cv a).
      pose proof (conv_len_bound cv a OKc) as CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr.
      cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      unfold fmt_output. cbn [fmt_pieces]. rewrite zlength_concat_cons. fold (fmt_output (parse_fmt_aux f r) args).
      pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

Lemma fmt_output_bound : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (fmt_output (fmt fs) args) <= zlength (str fs) + fargs_len args.
Proof. intros fs args OK. unfold fmt, parse_fmt in *. apply fmt_output_bound_aux; [lia | exact OK]. Qed.

(* [comment removed for export] *)




(* [comment removed for export] *)
Lemma mod32_of_mod64 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. intros z. apply Z.mod_mod_divide. exists (2^32). reflexivity. Qed.
Lemma s32_facts : forall z, -2^31 <= s32 z < 2^31 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = s32 z mod 2^32.
Proof.
  intros z. unfold s32. rewrite unsigned_lit_wrap, mod32_of_mod64.
  split; [Z.div_mod_to_equations; lia|].
  replace ((z + 2^31) mod 2^32 - 2^31) with (z - ((z + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r. rewrite Z_mod_mult. rewrite Z.sub_0_r. reflexivity.
Qed.
Lemma u32_facts : forall z, 0 <= u32 z < 2^32 /\ bv_unsigned (Z_to_bv 64 z : word) mod 2^32 = u32 z.
Proof. intros z. unfold u32. rewrite unsigned_lit_wrap, mod32_of_mod64. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.
Lemma u64_facts : forall z, 0 <= u64 z < 2^64 /\ bv_unsigned (Z_to_bv 64 z : word) = u64 z.
Proof. intros z. unfold u64. rewrite unsigned_lit_wrap. split; [Z.div_mod_to_equations; lia| reflexivity]. Qed.

(* [comment removed for export] *)
Definition pad8 (x : Z) : Z := (- x) mod 8.
Lemma pad8_range : forall x, 0 <= pad8 x < 8.
Proof. intros. unfold pad8. Z.div_mod_to_equations. lia. Qed.
Lemma pad8_align : forall x b, 0 <= x -> x <= b -> b mod 8 = 0 -> x + pad8 x <= b.
Proof.
  intros x b Hx Hb Hal. unfold pad8.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E2.
  set (q1 := - x / 8) in *. set (r1 := (- x) mod 8) in *. set (q2 := b / 8) in *. clearbody q1 r1 q2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End TwB.
