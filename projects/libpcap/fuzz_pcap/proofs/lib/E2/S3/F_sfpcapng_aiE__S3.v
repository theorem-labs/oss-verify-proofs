(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcapng_aiE.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiC.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *) From Ltac2 Require Ltac2.
#[local] Ltac2 Set StepFast.sf_fold_goal := Ltac2.Init.false.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition pio_body (fuel : nat) (sw : bool) (st : idbopts) (code olen voff : Z) (c1 : cursor) (buf0 : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  (if code =? OPT_ENDOFOPT then
     if negb (olen =? 0) then (buf0, inl (Msg.endofopt_len olen)) else (buf0, inr (st, c1))
   else if code =? IF_TSRESOL then
     if negb (olen =? 1) then (buf0, inl (Msg.tsresol_len olen)) else
     if io_saw_tsresol st then (buf0, inl Msg.tsresol_dup) else
     let tsresol_opt := get_u8 buf0 voff in
     if negb (Z.land tsresol_opt 128 =? 0) then
       let tsresol_shift := Z.land tsresol_opt 127 in
       if 63 <? tsresol_shift then (buf0, inl (Msg.tsresol_bin_high tsresol_shift))
       else process_idb_options_loop fuel sw (mkIdbOpts (2 ^ tsresol_shift) (io_tsoffset st) true true (io_saw_tsoffset st)) c1 buf0
     else
       if 19 <? tsresol_opt then (buf0, inl (Msg.tsresol_dec_high tsresol_opt))
       else process_idb_options_loop fuel sw (mkIdbOpts (10 ^ tsresol_opt) (io_tsoffset st) false true (io_saw_tsoffset st)) c1 buf0
   else if code =? IF_TSOFFSET then
     if negb (olen =? 8) then (buf0, inl (Msg.tsoffset_len olen)) else
     if io_saw_tsoffset st then (buf0, inl Msg.tsoffset_dup) else
     let raw := get_le64 buf0 voff in
     let tsoffset := if sw then s64 (bswap64 raw) else s64 raw in
     process_idb_options_loop fuel sw (mkIdbOpts (io_tsresol st) tsoffset (io_is_binary st) (io_saw_tsresol st) true) c1 buf0
   else process_idb_options_loop fuel sw st c1 buf0)%Z.
Definition pio_value (fuel : nat) (sw : bool) (st : idbopts) (code olen : Z) (c0 : cursor) (buf0 : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  match get_optvalue_from_block_data c0 olen with
  | inl m => (buf0, inl m)
  | inr (voff, c1) => pio_body fuel sw st code olen voff c1 buf0
  end.
Definition pio_iter (fuel : nat) (sw : bool) (st : idbopts) (c : cursor) (buf : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  (if cur_remaining c =? 0 then (buf, inr (st, c)) else
    match get_opthdr_from_block_data sw c buf with
    | inl m => (buf, inl m)
    | inr (code, olen, c0, buf0) => pio_value fuel sw st code olen c0 buf0
    end)%Z.
Lemma pio_unfold : forall fuel sw st c buf, process_idb_options_loop (S fuel) sw st c buf = pio_iter fuel sw st c buf.
Proof using Type. pin_using tt. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zslice_at {A} (pre l post : list A) : zslice (Z.of_nat (length pre)) (Z.of_nat (length l)) (pre ++ l ++ post) = l.
Proof using Type. pin_using tt.
  unfold zslice, zfirstn, zskipn. rewrite !Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. unfold skipn. cbn.
  rewrite firstn_app, firstn_all, Nat.sub_diag by lia. cbn. apply app_nil_r.
Qed.
Lemma get_le16_at pre u0 u1 rest : get_le16 (pre ++ u0 :: u1 :: rest) (Z.of_nat (length pre)) = u0 + 256 * u1.
Proof using Type. pin_using tt.
  unfold get_le16. change (pre ++ u0 :: u1 :: rest) with (pre ++ [u0; u1] ++ rest). change 2 with (Z.of_nat (length [u0; u1])).
  rewrite zslice_at. cbn. lia.
Qed.
Lemma get_le16_at2 pre u0 u1 u2 u3 rest : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: rest) (Z.of_nat (length pre) + 2) = u2 + 256 * u3.
Proof using Type. pin_using tt.
  replace (pre ++ u0 :: u1 :: u2 :: u3 :: rest) with ((pre ++ [u0; u1]) ++ u2 :: u3 :: rest) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 2) with (Z.of_nat (length (pre ++ [u0; u1]))) by (rewrite length_app; cbn; lia). apply get_le16_at.
Qed.
Lemma get_u8_at pre v rest : get_u8 (pre ++ v :: rest) (Z.of_nat (length pre)) = v.
Proof using Type. pin_using tt. unfold get_u8, znth. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Nat2Z.id. apply nth_middle. Qed.
Lemma get_le64_at pre v0 v1 v2 v3 v4 v5 v6 v7 rest :
  get_le64 (pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest) (Z.of_nat (length pre)) = le8val v0 v1 v2 v3 v4 v5 v6 v7.
Proof using Type. pin_using tt.
  unfold get_le64. change (pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest) with (pre ++ [v0; v1; v2; v3; v4; v5; v6; v7] ++ rest).
  change 8 with (Z.of_nat (length [v0; v1; v2; v3; v4; v5; v6; v7])). rewrite zslice_at. cbn -[Z.add Z.mul]. unfold le8val. lia.
Qed.
Lemma swap2_at pre u0 u1 rest : swap_field 2 (Z.of_nat (length pre)) (pre ++ u0 :: u1 :: rest) = pre ++ u1 :: u0 :: rest.
Proof using Type. pin_using tt.
  unfold swap_field.
  replace (zslice (Z.of_nat (length pre)) 2 (pre ++ u0 :: u1 :: rest)) with [u0; u1] by (symmetry; exact (zslice_at pre [u0; u1] rest)).
  unfold buf_write_at, zfirstn, zskipn, zlength. cbn [rev app length].
  rewrite Nat2Z.id, firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  replace (Z.to_nat (Z.of_nat (length pre) + Z.of_nat 2)) with (length pre + 2)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. replace (length pre + 2 - length pre)%nat with 2%nat by lia. reflexivity.
Qed.
Lemma swap2_at2 pre u0 u1 u2 u3 rest : swap_field 2 (Z.of_nat (length pre) + 2) (pre ++ u0 :: u1 :: u2 :: u3 :: rest) = pre ++ u0 :: u1 :: u3 :: u2 :: rest.
Proof using Type. pin_using tt.
  replace (pre ++ u0 :: u1 :: u2 :: u3 :: rest) with ((pre ++ [u0; u1]) ++ u2 :: u3 :: rest) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 2) with (Z.of_nat (length (pre ++ [u0; u1]))) by (rewrite length_app; cbn; lia).
  rewrite swap2_at, <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pfx_decomp (pre mid post : list Z) (bs : list byte) :
  firstn (length (pre ++ mid ++ post)) bs = map b8 (pre ++ mid ++ post) ->
  exists bsr, bs = map b8 pre ++ map b8 mid ++ bsr /\ firstn (length post) bsr = map b8 post.
Proof using Type. pin_using tt.
  intros H. set (k := (length pre + length mid)%nat). exists (skipn k bs).
  assert (Hk : firstn k bs = map b8 pre ++ map b8 mid).
  { transitivity (firstn k (firstn (length (pre ++ mid ++ post)) bs)).
    - rewrite firstn_firstn. f_equal. rewrite !length_app. lia.
    - rewrite H, !map_app, app_assoc, firstn_app, firstn_all2 by (rewrite !length_app, !length_map; lia).
      rewrite length_app, !length_map. replace (k - (length pre + length mid))%nat with 0%nat by lia. cbn. apply app_nil_r. }
  split.
  - rewrite <- (firstn_skipn k bs) at 1. rewrite Hk, <- app_assoc. reflexivity.
  - rewrite firstn_skipn_comm. replace (k + length post)%nat with (length (pre ++ mid ++ post)) by (rewrite !length_app; lia).
    rewrite H, !map_app, app_assoc, skipn_app, skipn_all2 by (rewrite length_app, !length_map; lia).
    rewrite length_app, !length_map. replace (k - (length pre + length mid))%nat with 0%nat by lia. reflexivity.
Qed.
Lemma pfx_comp (pre mid post : list Z) (bsr : list byte) :
  firstn (length post) bsr = map b8 post ->
  firstn (length (pre ++ mid ++ post)) (map b8 pre ++ map b8 mid ++ bsr) = map b8 (pre ++ mid ++ post).
Proof using Type. pin_using tt.
  intros H. rewrite !length_app, !map_app.
  rewrite firstn_app, length_map, firstn_all2 by (rewrite length_map; lia). f_equal.
  rewrite firstn_app, length_map, firstn_all2 by (rewrite length_map; lia). f_equal.
  replace (length pre + (length mid + length post) - length pre - length mid)%nat with (length post) by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma split_at4 (buf : list Z) (off : nat) : (off + 4 <= length buf)%nat ->
  exists pre u0 u1 u2 u3 post, buf = pre ++ u0 :: u1 :: u2 :: u3 :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|u0 [|u1 [|u2 [|u3 post]]]] eqn:E;
    try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists u0, u1, u2, u3, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.
Lemma split_at8 (buf : list Z) (off : nat) : (off + 8 <= length buf)%nat ->
  exists pre v0 v1 v2 v3 v4 v5 v6 v7 post, buf = pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post]]]]]]]] eqn:E;
    try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists v0, v1, v2, v3, v4, v5, v6, v7, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.
Lemma split_at1 (buf : list Z) (off : nat) : (off + 1 <= length buf)%nat ->
  exists pre v post, buf = pre ++ v :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|v post] eqn:E; try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists v, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.


(* [comment removed for export] *)
Lemma swap16_val a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor ((a + 256 * b) * 2 ^ 8) ((a + 256 * b) / 2 ^ 8) = b + 256 * a + 65536 * b.
Proof using Type. pin_using tt.
  intros Ha Hb. replace ((a + 256 * b) / 2 ^ 8) with b by (Z.div_mod_to_equations; lia).
  rewrite lor_high_low by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma land_m4 x : 0 <= x -> Z.land x (-4) = x / 4 * 4.
Proof using Type. pin_using tt.
  intros Hx. change (-4) with (Z.lnot (Z.ones 2)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma Z_to_bv64_mod x y : x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof using Type. pin_using tt. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul]. cbn in E. exact E. Qed.
(* [comment removed for export] *)
Lemma Z_to_bv64_s64 x : Z_to_bv 64 (s64 x) = Z_to_bv 64 x.
Proof using Type. pin_using tt. apply Z_to_bv64_mod. unfold s64. Z.div_mod_to_equations. lia. Qed.

Lemma land_128 v : 0 <= v < 256 -> Z.land v 128 = 128 * (v / 128).
Proof using Type. pin_using tt.
  intros Hv. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. change 128 with (2 ^ 7) at 1. rewrite Z.pow2_bits_eqb by lia.
  assert (Q : v / 2 ^ 7 = 0 \/ v / 2 ^ 7 = 1) by (Z.div_mod_to_equations; lia).
  destruct (Z.eqb_spec 7 n) as [<-|NE].
  - rewrite andb_true_r. change 128 with (2 ^ 7). destruct Q as [Q|Q]; rewrite Q.
    + rewrite Z.mul_0_r, Z.bits_0. apply Z.testbit_false; [lia|]. rewrite Q. reflexivity.
    + rewrite Z.mul_1_r, Z.pow2_bits_true by lia. apply Z.testbit_true; [lia|]. rewrite Q. reflexivity.
  - rewrite andb_false_r. change 128 with (2 ^ 7). destruct Q as [Q|Q]; rewrite Q.
    + rewrite Z.mul_0_r, Z.bits_0. reflexivity.
    + rewrite Z.mul_1_r, Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. exact NE.
Qed.
Lemma land_127_hi v : 128 <= v < 256 -> Z.land v 127 = v - 128.
Proof using Type. pin_using tt. intros. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. Z.div_mod_to_equations; lia. Qed.
Lemma land_255_mod v : Z.land v 255 = v mod 256.
Proof using Type. pin_using tt. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma signed_lit_any x : -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof using Type. pin_using tt.
  intros Hx. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.div Z.mul Z.opp].
  Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac if_tf' b := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux;
                     rewrite ?unsigned_lit, ?signed_lit_any by lia; zc_rec] end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma Z_to_bv64_drop x k : Z_to_bv 64 (x + k * 2^64) = Z_to_bv 64 x.
Proof using Type. pin_using tt. apply Z_to_bv64_mod. rewrite Z_mod_plus_full. reflexivity. Qed.
(* [comment removed for export] *)
Lemma swap16_shl48 a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (a + 256 * b + 65536 * a))) 48) = Z_to_bv 64 ((a + 256 * b) * 2 ^ 48).
Proof using Type. pin_using tt.
  intros Ha Hb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((a + 256 * b + 65536 * a) * 2 ^ 48) with ((a + 256 * b) * 2 ^ 48 + a * 2 ^ 64) by lia. apply Z_to_bv64_drop.
Qed.
Lemma shr48_of_shl48 x : 0 <= x < 65536 -> Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (x * 2 ^ 48))) 48) = Z_to_bv 64 x.
Proof using Type. pin_using tt. intros Hx. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. Qed.

Lemma land_m4w x : 0 <= x < 2^64 -> Z.land x 18446744073709551612 = x / 4 * 4.
Proof using Type. pin_using tt.
  intros Hx. change 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))).
  rewrite Z.land_assoc, Z.land_ones, Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Section AIE.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m.
  Hypothesis ST : stk ssegs m lo (bv_unsigned sp).
  Hypothesis LO : usp0 R - 8388608 <= lo.
  Hypothesis BU : lo + (65536 + 112) <= bv_unsigned sp.
  Hypothesis SPM : bv_unsigned sp <= rc_spmain R.
  Hypothesis MI : mem_inv ssegs m.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : bv_unsigned sp mod 16 = 0.
  Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPW : 0x7fff80000000 <= usp0 R.
  Hypothesis SP47 : usp0 R <= 2^47.
  Hypothesis HS : pc_priv p = PrivNg s i.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis B14 : 0 < B /\ B + pc_bufalloc p <= CEILZ.
  Hypothesis APB : P + 680 <= B \/ B + pc_bufalloc p <= P.
  (* [comment removed for export] *)
  Hypothesis P5 : out_of_image P 680.
  Hypothesis HPV : rw_cells ssegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].
  Hypothesis HNG : rw_cells ssegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad).
  Hypothesis HIF : ifaces_ok p I m.
  Hypothesis UTS : 0 < ng_user_tsresol s < 2^64.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis WMB : 0 <= ng_max_blocksize s < 2^32.
  Hypothesis HBUF : rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs].
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis LENB : Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32.
  Hypothesis GRD : Forall (fun z => 0 <= z < 256) (pc_bufdata p).
  Hypothesis HCUR : rw_cells ssegs m CUR (cursor_cells B c cpad).
  Hypothesis CUR1 : bv_unsigned sp <= CUR.
  Hypothesis CUR2 : CUR + 24 <= rc_spmain R.
  Hypothesis CUR8 : CUR mod 8 = 0.
  Hypothesis IDB0 : 0 <= idb_off.
  Hypothesis COFF : cur_off c = idb_off + 8.
  Hypothesis CREM : 0 <= cur_remaining c.
  Hypothesis CEND : cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)).
  Hypothesis CBT : 0 <= cur_block_type c < 2^32.
  Hypothesis HEB : rw_cells ssegs m EB [CB 256 ej].
  Hypothesis EBX : (bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ EB = P + 216.
  Hypothesis EB64 : 0 < EB /\ EB + 256 < 2^64.
  (* [comment removed for export] *)
  Hypothesis CLB : forall a, in_block (C1 ++ C2) a -> a < CEILZ.
  Hypothesis INPc : forall a, P <= a < P + 680 -> in_block (C1 ++ C2) a.
  Hypothesis INBc : forall a, B <= a < B + pc_bufalloc p -> in_block (C1 ++ C2) a.
  Hypothesis CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256.
  Hypothesis EBiv : client_iv R (C1 ++ C2) (EB, EB + 256).

  #[local] Notation POSTQ := (add_interface_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Notation AGP := (ai_AGP sp C1 C2 P B CUR EB p m).
  #[local] Notation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  #[local] Notation AIREST := (ai_REST K R C1 C2 FB P B CUR EB p s c ej (ps_outfile st)).
  #[local] Notation AIREST_F := (ai_REST_F K R C1 C2 FB P B CUR p s (ps_outfile st)).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Variables (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte) (hd : list cell).
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap idb_off p < 2^32)%Z.
  Hypothesis Hhd : cells_size hd = 8%nat.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Definition sgF : pcap_ng_sf := mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot0 idb_off p :: ng_ifaces sg).
  Definition pF (buf' : list Z) : pcapT := set_bufdata buf' (set_ng sgF (Some q1) (set_ng sg (Some q1) p)).
  Lemma ai_result_inl : forall buf' msg, ai_result idb_off p s c sg (Some q1) (buf', inl msg) = (false, c, pF buf', msg).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition AIM (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte) : Prop :=
    (0 < io_tsresol io < 2^64)%Z /\
    mem_inv ssegs m3 /\ stk ssegs m3 lo (bv_unsigned sp + -112) /\ AGP m3 /\
    rw_cells ssegs m3 (bv_unsigned sp + -112) hd /\ FRAME m3 /\
    rw_cells ssegs m3 (P + 648) (ng_cells sg I' pad1) /\
    rw_cells ssegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) /\
    rw_cells ssegs m3 SA [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sj] /\
    rw_cells ssegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] /\
    GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m3 /\
    rw_cells ssegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] /\ firstn (length buf') bs3 = map b8 buf' /\ length buf' = length (pc_bufdata p) /\
    Forall (fun z => 0 <= z < 256)%Z buf' /\
    rw_cells ssegs m3 CUR (cursor_cells B c' cpad3) /\
    (0 <= cur_remaining c')%Z /\ (cur_off c <= cur_off c')%Z /\ (cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c)%Z /\
    cur_block_type c' = cur_block_type c /\
    rw_cells ssegs m3 EB [CB 256 ej].

  (* [comment removed for export] *)
  Definition LREGS (ra' a3' s8' s9' s10' s11' t3' : word) (io : idbopts) (c' : cursor) :=
    mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 20) (Z_to_bv 64 10) (Z_to_bv 64 EB) (Z_to_bv 64 P)
        (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) (Z_to_bv 64 CUR) a3'
        (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io))) (Z_to_bv 64 3) (Z_to_bv 64 9)
        (Z_to_bv 64 (P + 648)) (Z_to_bv 64 65280) (Z_to_bv 64 16711680) (Z_to_bv 64 (cur_remaining c'))
        (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) s8' s9' s10' s11' t3'
        (Z_to_bv 64 14) (Z_to_bv 64 8) (Z_to_bv 64 (io_tsoffset io)).

  Definition LOOPK (fuel : nat) : Prop :=
    forall (ra' a3' xa4 xa5 xs5 xs6 xs7 s8' s9' s10' s11' t3' xt6 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      xa4 = Z_to_bv 64 (io_tsresol io) -> xa5 = Z_to_bv 64 (Z.b2z (io_is_binary io)) -> xs5 = Z_to_bv 64 (cur_remaining c') ->
      xs6 = Z_to_bv 64 (Z.b2z (io_saw_tsoffset io)) -> xs7 = Z_to_bv 64 (Z.b2z (io_saw_tsresol io)) -> xt6 = Z_to_bv 64 (io_tsoffset io) ->
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat fuel)%Z ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options_loop fuel (pc_swapped p) io c' buf')) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 20) (Z_to_bv 64 10) (Z_to_bv 64 EB) (Z_to_bv 64 P)
                 (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) (Z_to_bv 64 CUR) a3' xa4 xa5 (Z_to_bv 64 3) (Z_to_bv 64 9)
                 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 65280) (Z_to_bv 64 16711680) xs5 xs6 xs7 s8' s9' s10' s11' t3'
                 (Z_to_bv 64 14) (Z_to_bv 64 8) xt6) F (Z_to_bv 64 0x17078) fc None m3 (seg_rom ssegs)).
  Definition ITERK (fuel : nat) : Prop :=
    forall (ra' a3' s8' s9' s10' s11' t3' : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (0 < cur_remaining c')%Z ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options_loop (S fuel) (pc_swapped p) io c' buf')) stG)
        (MS (LREGS ra' a3' s8' s9' s10' s11' t3' io c') F (Z_to_bv 64 0x1707c) fc None m3 (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition ai_loop_step__stmt : Prop := forall fuel, ITERK fuel -> LOOPK (S fuel).
  Section Sz3.
  Variables fuel ra' a3' xa4 xa5 xs5 xs6 xs7 s8' s9' s10' s11' t3' xt6 io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_loop_step__stmt "vhvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_loop_step__body : ltac2:(SecDiet.SzSec.bodyP 'ai_loop_step__stmt "vhvvvvvvvvvvvvvvvvvvv").
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS. pin_using (fun (APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS : unit) => tt).
    intros IT.
 intros -> -> -> -> -> -> IV FUEL.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3).
    clear HPV HNG HBUF HCUR HEB HIF.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide CC3. hide HEB3.
    step.
    destruct (Z.eq_dec (cur_remaining c') 0) as [R0|R0].
    - rewrite (eqb_lits_eq _ _ R0). cbv iota. rewrite pio_unfold. unfold pio_iter. rewrite (proj2 (Z.eqb_eq _ _) R0).
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      eapply (ai_tail K HFL SFL); eassumption || (try exact IC1; try exact HSA; try lia).
    - rewrite (eqb_lits_false (cur_remaining c') 0) by lia. cbv iota.
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      apply (IT ra' a3' s8' s9' s10' s11' t3' io c' buf' m3 bs3 cpad3 IV FUEL ltac:(lia)).
  Qed.
  End Sz3.
  Lemma ai_loop_step : ltac:(let t := eval cbv delta [ai_loop_step__stmt] in ai_loop_step__stmt in exact t).
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS. intros fuel IT ra' a3' xa4 xa5 xs5 xs6 xs7 s8' s9' s10' s11' t3' xt6 io c' buf' m3 bs3 cpad3. ltac2:(SecDiet.SzSec.closeP 'ai_loop_step__body "vhvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma ai_loop0 : LOOPK O.
  Proof using Type. pin_using tt. red. intros until cpad3. intros _ _ _ _ _ _ IV FUEL. destruct IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR1 & _). exfalso. clear - FUEL CR1. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Definition loop_restf__stmt : Prop := forall (m3 : mem) (buf' : list Z) (bs3 : list byte) (ccs : list cell),
    GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m3 ->
    rw_cells ssegs m3 (P + 648) (ng_cells sg I' pad1) ->
    rw_cells ssegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) ->
    rw_cells ssegs m3 SA [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sj] ->
    rw_cells ssegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] ->
    rw_cells ssegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] -> firstn (length buf') bs3 = map b8 buf' -> length buf' = length (pc_bufdata p) ->
    Forall (fun z => 0 <= z < 256)%Z buf' ->
    rw_cells ssegs m3 CUR ccs -> cells_size ccs = 24%nat ->
    AIREST_F m3 stG c (pF buf').
  Section Sz5.
  Variables m3 buf' bs3 ccs : ltac2:(SecDiet.SzSec.tyM 'loop_restf__stmt "vvvv" @m3).
  Lemma loop_restf__body : ltac2:(SecDiet.SzSec.bodyP 'loop_restf__stmt "vvvv").
  Proof using BU CUR1 HSA Hhd IC1 IC2 LJS LO OFG RSP SPW SZ U1 U2. pin_using (fun (BU CUR1 HSA Hhd IC1 IC2 LJS LO OFG RSP SPW SZ U1 U2 : unit) => tt).
    intros G3 NG3 AR1 SL3 AR2 BUF3 PFX3 LB3 GR3 CC3 Hccs.
    exists sgF, (Some q1), I', pad1, bs3.
    split; [exact OFG|]. split; [reflexivity|]. split; [exact G3|]. split; [exact NG3|]. split; [cbn; exact U1|]. split; [cbn; exact U2|]. split; [cbn; lia|]. split; [cbn; lia|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LB3|]. split; [exact GR3|]. split.
    - cbn [ng_ifaces_closable sgF ng_ifaces_size]. split; [| lia].
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      pose proof (rw_cells_uncut _ _ _ _ _ AR1 SL3 ltac:(rewrite ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 AR2 ltac:(rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize]; lia)) as J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [junk HJ]. exists junk.
      rewrite !cells_size_app, ifs_cells_size in HJ by (rewrite length_rev; lia). rewrite length_rev in HJ. cbn [cells_size csize Nat.add] in HJ.
      lazymatch type of HJ with rw_cells _ _ _ [CB ?n _] => replace (Z.to_nat (40 * ng_ifaces_size sg)) with n by lia end. exact HJ.
    - exists ccs. split; [exact CC3| exact Hccs].
  Qed.
  End Sz5.
  Lemma loop_restf : ltac:(let t := eval cbv delta [loop_restf__stmt] in loop_restf__stmt in exact t).
  Proof using BU CUR1 HSA Hhd IC1 IC2 LJS LO OFG RSP SPW SZ U1 U2. intros m3 buf' bs3 ccs. ltac2:(SecDiet.SzSec.closeP 'loop_restf__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition loop_facts__stmt : Prop := forall (io : idbopts) (c' : cursor) (pre post : list Z) (u0 u1 u2 u3 : Z) (bsr cpad3 : list byte) (m3 m5 : mem)
      (c0 c1 l0 l1 : Z) (D : Z) (ccs : list cell),
      AIM io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 ->
      (4 <= cur_remaining c')%Z -> Z.of_nat (length pre) = cur_off c' -> D = (B + cur_off c')%Z ->
      firstn (length post) bsr = map b8 post ->
      (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z ->
      mem_inv ssegs m5 -> munch [(CUR, CUR + 16); (D, D + 4)]%Z m3 m5 -> wmono ssegs m3 m5 ->
      rw_cells ssegs m5 D [Cells.C2 (Z_to_bv 64 (c0 + 256 * c1)); Cells.C2 (Z_to_bv 64 (l0 + 256 * l1))] ->
      rw_cells ssegs m5 CUR ccs -> cells_size ccs = 24%nat ->
      let buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post in let bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr in
      stk ssegs m5 lo (bv_unsigned sp + -112) /\ AGP m5 /\
      rw_cells ssegs m5 (bv_unsigned sp + -112) hd /\ FRAME m5 /\
      rw_cells ssegs m5 (P + 648) (ng_cells sg I' pad1) /\
      rw_cells ssegs m5 I' (ifs_cells (rev (ng_ifaces s)) js) /\
      rw_cells ssegs m5 SA [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sj] /\
      rw_cells ssegs m5 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] /\
      GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m5 /\
      rw_cells ssegs m5 B [CB (Z.to_nat (pc_bufalloc p)) bs5] /\ firstn (length buf5) bs5 = map b8 buf5 /\ length buf5 = length (pc_bufdata p) /\
      Forall (fun z => 0 <= z < 256)%Z buf5 /\ Forall (fun z => 0 <= z < 256)%Z post /\
      rw_cells ssegs m5 EB [CB 256 ej] /\
      rw_cells ssegs m5 (D + 4) [CB (length bsr) bsr] /\
      AIREST_F m5 stG c (pF buf5).
  Section Sz6.
  Variables io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs : ltac2:(SecDiet.SzSec.tyM 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv" @io).
  Lemma loop_facts__body : ltac2:(SecDiet.SzSec.bodyP 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 LENB LJS LO OFG P14 RSP SFL SPW SZ U1 U2. pin_using (fun (APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 LENB LJS LO OFG P14 RSP SFL SPW SZ U1 U2 : unit) => tt).
    intros IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI5 MU WM HOPT5 CC5 Hccs buf5 bs5.
    destruct IV as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (LBS : (length pre + (4 + length bsr))%nat = Z.to_nat (pc_bufalloc p)).
    { destruct BUF3 as [[WF _] _]. cbn [cells_wf cell_wf] in WF. rewrite !length_app, !length_map in WF. cbn [length] in WF. lia. }
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length (pre ++ u0 :: u1 :: u2 :: u3 :: post)))%Z) by lia.
    rewrite length_app in LEN4. cbn [length] in LEN4.
    apply Forall_app in GR3 as [GRpre GB].
    pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as GRpost.
    cbv beta in B0, B1, B2, B3. clear GB.
    pose proof (head_apart K _ _ _ _ _ _ _ G3 HinB) as APIB. pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIB, APIP. unfold PCAP_NG_SF_TOTAL in APIP.
    pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
    assert (AGS35 : agrees_on (fun a => outside [(CUR, CUR + 16); (D, D + 4)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unfold ai_FRAME in FR3.
    transport HD3 m5 AGS35 ltac:(prs). transport FR3 m5 AGS35 ltac:(prs). transport NG3 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' js pad1 hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU P14 APB CUR1 G3 Lpre HDd LBS; prs)).
    transport AR1 m5 AGS35 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; (keep_hyps CEILV hptr sp R CUR lo idb_off p s c I' js hd c' pre post u0 u1 u2 u3 bsr ccs LJS; lia)); rewrite length_rev in Ha; cbn [outside]; (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' js hd c' pre post u0 u1 u2 u3 bsr m3 D ccs a LO BU CUR1 IC1 IC2 G3 Lpre HDd LBS Q4 APIB Ha; lia)).
    transport SL3 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' SA js sj hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU CUR1 IC1 IC2 HSA G3 Lpre HDd LBS Q4 APIB; prs)). transport AR2 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' SA js tail3 hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU CUR1 IC1 HSA G3 Lpre HDd LBS Q4 APIB; prs)). transport HEB3 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s c ej stG sg q1 I' js hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU P14 B14 APB CUR1 EBX G3 Lpre HDd LBS; prs)).
    assert (G5 : GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m5).
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo in *; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. unfold iv_in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    assert (ST5 : stk ssegs m5 lo (bv_unsigned sp + -112)) by (eapply stk_transport_disjoint; [exact ST3 | exact MU | exact WM | cbn [disjoint_from]; unfold rc_lo in *; lia]).
    assert (AG5 : AGP m5).
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS35|]. intros a (_ & _ & Hc & _ & Hb); cbn [outside]. split; [(keep_hyps CEILV hptr R B CUR p s I' js hd c' pre post u0 u1 u2 u3 bsr ccs a Hc; lia)|]. split; [(keep_hyps CEILV hptr sp R B CUR lo idb_off p s c I' js hd c' pre post u0 u1 u2 u3 bsr D ccs a Lpre HDd LBS Hb; lia)| exact Logic.I]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_recell _ _ _ [CB (length pre) (map b8 pre); CB 4 [b8 u0; b8 u1; b8 u2; b8 u3]; CB (length bsr) bsr] BUF3
                  ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity)) as BX.
    destruct (rw_cells_cut _ _ _ 1 BX) as [HB1 BX2]. destruct (rw_cells_cut _ _ _ 1 BX2) as [_ HB2]. clear BX BX2. cbn [firstn skipn cells_size csize Nat.add] in HB1, HB2.
    lazymatch type of HB2 with rw_cells _ _ ?A _ => replace A with (D + 4)%Z in HB2 by lia end.
    transport HB1 m5 AGS35 ltac:(prs). transport HB2 m5 AGS35 ltac:(prs).
    pose proof (rw_cells_uncut _ _ _ _ _ HB1 HOPT5 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 HB2 ltac:(cbn [cells_size csize Nat.add app]; lia)) as J2. clear J1.
    assert (BUF5 : rw_cells ssegs m5 B [CB (Z.to_nat (pc_bufalloc p)) bs5]).
    { eapply rw_cells_recell; [exact J2 | cbn; subst bs5; rewrite !length_app, !length_map; cbn [length]; lia |].
      subst bs5. cbn [cells_bytes cbytes app]. rewrite !le2_lit by lia. rewrite !app_nil_r. cbn [app]. reflexivity. }
    clear J2.
    assert (PFX5 : firstn (length buf5) bs5 = map b8 buf5) by (subst buf5 bs5; exact (pfx_comp pre [c0; c1; l0; l1] post bsr PFXr)).
    assert (LB5 : length buf5 = length (pc_bufdata p)) by (rewrite <- LB3; subst buf5; rewrite !length_app; reflexivity).
    assert (GR5 : Forall (fun z => 0 <= z < 256)%Z buf5) by (subst buf5; apply Forall_app; split; [exact GRpre|]; repeat (constructor; [lia|]); exact GRpost).
    split; [exact ST5|]. split; [exact AG5|]. split; [exact HD3|]. split; [exact FR3|]. split; [exact NG3|]. split; [exact AR1|]. split; [exact SL3|]. split; [exact AR2|].
    split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|]. split; [exact LB5|]. split; [exact GR5|]. split; [exact GRpost|]. split; [exact HEB3|]. split; [exact HB2|].
    eapply loop_restf; [exact G5 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | exact Hccs].
  Qed.
  End Sz6.
  Lemma loop_facts : ltac:(let t := eval cbv delta [loop_facts__stmt] in loop_facts__stmt in exact t).
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 LENB LJS LO OFG P14 RSP SFL SPW SZ U1 U2. intros io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs. ltac2:(SecDiet.SzSec.closeP 'loop_facts__body "vvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_disp__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (io : idbopts) (c' : cursor) (sw : bool) (pre post : list Z) (c0 c1 l0 l1 : Z) (bsr cpad3 : list byte) (m5 : mem) (D : Z),
      let code := (c0 + 256 * c1)%Z in let olen := (l0 + 256 * l1)%Z in let padded := ((olen + 3) / 4 * 4)%Z in
      let buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post in let bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr in
      let c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c') in
      (forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3) ->
      (0 < io_tsresol io < 2^64)%Z -> pc_swapped p = sw ->
      (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (4 <= cur_remaining c')%Z -> (padded <= cur_remaining c' - 4)%Z ->
      (8 <= cur_off c')%Z -> (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z ->
      D = (B + cur_off c')%Z -> Z.of_nat (length pre) = cur_off c' ->
      firstn (length post) bsr = map b8 post ->
      (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z ->
      Forall (fun z => 0 <= z < 256)%Z post ->
      rw_cells ssegs m5 (D + 4) [CB (length bsr) bsr] ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1) (pio_body fuel sw io code olen (cur_off c' + 4) c2 buf5)) stG)
        (MS (mkR (Z_to_bv 64 padded) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 20) (Z_to_bv 64 10) (Z_to_bv 64 EB) (Z_to_bv 64 P)
                 (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) (Z_to_bv 64 CUR) (Z_to_bv 64 olen)
                 (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io))) (Z_to_bv 64 3) (Z_to_bv 64 9)
                 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 65280) (Z_to_bv 64 16711680) (Z_to_bv 64 (cur_remaining c' - 4 - padded))
                 (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (D + 4 + padded)) (Z_to_bv 64 (Z.b2z sw))
                 (Z_to_bv 64 code) (Z_to_bv 64 (olen * 2 ^ 48)) (Z_to_bv 64 (D + 4))
                 (Z_to_bv 64 14) (Z_to_bv 64 8) (Z_to_bv 64 (io_tsoffset io)))
            F (Z_to_bv 64 0x1710c) fc None m5 (seg_rom ssegs)).
  Section Sz7.
  Variables fuel io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D : ltac2:(SecDiet.SzSec.tyM 'ai_disp__stmt "vhvvvvvvvvvvvvv" @fuel).
  Lemma ai_disp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_disp__stmt "vhvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt).
    intros LK code olen padded buf5 bs5 c2 AIM5 TSR SW FUEL GE4 FIT OFF0 LEN4 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2.
    assert (R2 : cur_remaining c2 = (cur_remaining c' - 4 - padded)%Z) by reflexivity.
    assert (FUEL2 : (cur_remaining c2 / 4 < Z.of_nat fuel)%Z) by (rewrite R2; clear - FUEL FIT HL0 HL1; subst padded olen; Z.div_mod_to_equations; lia).
    pose proof (AIM5 io TSR) as IV5.
    destruct IV5 as (_ & MI5 & ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5 & GR5 & CC5 & CR1 & CR2 & CR3 & CR4 & HEB5).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel pre c0 c1 l0 l1 q q3 r q0 r0 H0 H1 H5 H6; lia)).
    assert (Lpost : (cur_remaining c' - 4 <= Z.of_nat (length post))%Z) by (subst buf5; rewrite length_app in LEN4; cbn [length] in LEN4; lia).
    assert (RESTF5 : AIREST_F m5 stG c (pF buf5)).
    { eapply loop_restf; [exact G5 | exact NG5 | exact AR15 | exact SL5 | exact AR25 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | reflexivity]. }
    (* [comment removed for export] *)
    pose proof (ai_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU SPM TP ALN RSP SPW HinP P14 B14 APB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND EBX CLB CRE EBiv) as SNP.
    pose proof (ai_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej
                  G LO BU SPM RSP SPW HinP P14 B14 APB P5 UTS WMB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND CBT EBX EB64 CRE EBiv) as MCP.
    pose proof (ai_tail K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU RSP SPW HinP HinB P14 APB UTS IFW LENB CUR1 CUR8 IDB0 COFF CREM CEND EBX CLB) as TAIL.
    unfold pio_body.
    (* [comment removed for export] *)
    step.
    destruct (Z.eq_dec code 9) as [E9|NE9].
    { (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ E9). cbv iota.
      replace (code =? OPT_ENDOFOPT) with false by (rewrite E9; reflexivity). replace (code =? IF_TSRESOL) with true by (rewrite E9; reflexivity). cbv iota.
      step.
      destruct (Z.eq_dec olen 1) as [L1|L1].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 1) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 1) L1). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_FMT_TSRESOL_LEN "Interface Description Block has if_tsresol option with length %u != 1"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_TSRESOL_LEN; lia| unfold AI_FMT_TSRESOL_LEN; cbn; lia]).
        eapply SNP with (m3:=m5) (args:=[AInt olen]) (hd:=hd);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
      rewrite (eqb_lits_eq _ _ L1). cbv iota. rewrite (proj2 (Z.eqb_eq olen 1) L1). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      step.
      destruct (io_saw_tsresol io) eqn:SAWR.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 step.
        assert (MSG : fmt_at m5 AI_STR_TSRESOL_DUP "Interface Description Block has more than one if_tsresol option"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_STR_TSRESOL_DUP; lia| unfold AI_STR_TSRESOL_DUP; cbn; lia]).
        eapply MCP with (m3:=m5) (hd:=hd) (str:="Interface Description Block has more than one if_tsresol option"%string);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | cbn; (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | vm_compute; reflexivity | msg_ok | exact RESTF5 ]. }
      cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v post']; [exfalso; cbn [length] in Lpost; lia|].
      destruct bsr as [|bv0 bsr']; [cbn in PFXr; discriminate|]. cbn [firstn length map] in PFXr. injection PFXr as Ebv0 PFXr'. subst bv0.
      pose proof (Forall_inv GRpost) as Bv. cbv beta in Bv.
      assert (GU : get_u8 buf5 (cur_off c' + 4) = v).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply get_u8_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 1 [b8 v]; CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV1 _]. clear HV. cbn [firstn] in HV1.
      step. change (b8 v) with (Z_to_bv 8 v). rewrite (sxb_lit v) by lia.
      rewrite (land_128 v) by lia.
      destruct (Z.lt_ge_cases v 128) as [VLO|VHI].
      + (* [comment removed for export] *)
        rewrite (Z.div_small v 128) by lia. replace (128 * 0 =? 0)%Z with true by reflexivity. cbv beta iota delta [negb]. replace (v - 256 * 0)%Z with v by lia.
        step. rewrite (unsigned_lit v), land_255_mod, (Z.mod_small v 256) by lia.
        step. if_tf' false.
        step.
        destruct (Z.lt_ge_cases v 20) as [V20|V20].
        2:{ (* [comment removed for export] *)
          if_tf' true. rewrite (proj2 (Z.ltb_lt 19 v)) by lia. cbv iota. rewrite ai_result_inl.
          do 4 step.
          assert (MSG : fmt_at m5 AI_FMT_DEC_HIGH "Interface Description Block if_tsresol option resolution 10^-%u is too high"%string)
            by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_DEC_HIGH; lia| unfold AI_FMT_DEC_HIGH; cbn; lia]).
          eapply SNP with (m3:=m5) (args:=[AInt v]) (hd:=hd);
            [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_dec_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
        if_tf' false. rewrite (proj2 (Z.ltb_ge 19 v)) by lia. cbv iota.
        assert (P19 : (0 < 10 ^ v <= 10 ^ 19)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (10 ^ 19)%Z with 10000000000000000000%Z in P19.
        step.
        destruct (Z.eq_dec v 0) as [V0|V0].
        * (* [comment removed for export] *)
          if_tf' true. rewrite V0. change (10 ^ 0)%Z with 1%Z.
          do 4 step.
          rewrite <- SW; eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
        * if_tf' false. step. step.
          eapply evt_cut; [eapply (pow10_block (Z.to_nat v - 1) v 1); (keep_hyps CEILV hptr sp R CUR lo p s js hd fuel c' pre c0 c1 l0 l1 v post' Bv V0 V20 P19; lia) |].
          cbv beta. intros ms' ->. rewrite Z.mul_1_l.
          rewrite <- SW; eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + (* [comment removed for export] *)
        replace (v / 128)%Z with 1%Z by (Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel pre c0 c1 l0 l1 v post' q2 q r Bv VHI H0 H1; lia)). replace (128 * 1 =? 0)%Z with false by reflexivity. cbv beta iota delta [negb].
        rewrite (land_127_hi v) by lia. replace (v - 256 * 1)%Z with (v - 256)%Z by lia.
        step. rewrite (unsigned_lit_wrap (v - 256)), land_255_mod. replace (((v - 256) mod 2 ^ 64) mod 256)%Z with v by (Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel pre c0 c1 l0 l1 v post' q2 q r r2 q3 Bv H0 H1 H15; lia)).
        step. if_tf' true.
        step. rewrite (unsigned_lit v), (land_127_hi v) by lia.
        step. step.
        destruct (Z.lt_ge_cases 63 (v - 128)) as [V63|V63].
        { (* [comment removed for export] *)
          if_tf' true. rewrite (proj2 (Z.ltb_lt 63 (v - 128))) by lia. cbv iota. rewrite ai_result_inl.
          do 3 step.
          assert (MSG : fmt_at m5 AI_FMT_BIN_HIGH "Interface Description Block if_tsresol option resolution 2^-%u is too high"%string)
            by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_BIN_HIGH; lia| unfold AI_FMT_BIN_HIGH; cbn; lia]).
          eapply SNP with (m3:=m5) (args:=[AInt (v - 128)]) (hd:=hd);
            [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_bin_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
        if_tf' false. rewrite (proj2 (Z.ltb_ge 63 (v - 128))) by lia. cbv iota.
        assert (P63 : (0 < 2 ^ (v - 128) <= 2 ^ 63)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (2 ^ 63)%Z with 9223372036854775808%Z in P63.
        step. step. rewrite (unsigned_lit (v - 128)), (Z.mod_small (v - 128) 64), Z.shiftl_1_l by lia.
        step. step.
        rewrite <- SW; eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 9) by lia. cbv iota.
    replace (code =? IF_TSRESOL) with false by (symmetry; apply Z.eqb_neq; exact NE9).
    step.
    destruct (Z.eq_dec code 14) as [E14|NE14].
    { (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ E14). cbv beta iota delta [negb].
      replace (code =? OPT_ENDOFOPT) with false by (rewrite E14; reflexivity). replace (code =? IF_TSOFFSET) with true by (rewrite E14; reflexivity). cbv iota.
      step.
      destruct (Z.eq_dec olen 8) as [L8|L8].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 8) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 8) L8). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_FMT_TSOFF_LEN "Interface Description Block has if_tsoffset option with length %u != 8"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_TSOFF_LEN; lia| unfold AI_FMT_TSOFF_LEN; cbn; lia]).
        eapply SNP with (m3:=m5) (args:=[AInt olen]) (hd:=hd);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsoffset_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
      rewrite (eqb_lits_eq _ _ L8). cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_eq olen 8) L8). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      step.
      destruct (io_saw_tsoffset io) eqn:SAWO.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_STR_TSOFF_DUP "Interface Description Block has more than one if_tsoffset option"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_STR_TSOFF_DUP; lia| unfold AI_STR_TSOFF_DUP; cbn; lia]).
        eapply MCP with (m3:=m5) (hd:=hd) (str:="Interface Description Block has more than one if_tsoffset option"%string);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | cbn; (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | vm_compute; reflexivity | msg_ok | exact RESTF5 ]. }
      cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post']]]]]]]]; try (exfalso; cbn [length] in Lpost; (keep_hyps CEILV hptr sp R CUR lo p s js hd fuel c' pre c0 c1 l0 l1 R2 CR1 Lpost L8; lia)).
      destruct bsr as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bsr']]]]]]]]; try (cbn in PFXr; discriminate).
      cbn [firstn length map] in PFXr. injection PFXr as E0 E1 E2 E3 E4 E5 E6 E7 PFXr'. subst b0 b1 b2 b3 b4 b5 b6 b7.
      assert (Bv : forall x, In x [v0; v1; v2; v3; v4; v5; v6; v7] -> (0 <= x < 256)%Z).
      { intros x Hx. apply (proj1 (Forall_forall _ _) GRpost). cbn in Hx |- *. clear - Hx. tauto. }
      pose proof (Bv v0 ltac:(cbn; clear; tauto)) as Bv0. pose proof (Bv v1 ltac:(cbn; clear; tauto)) as Bv1. pose proof (Bv v2 ltac:(cbn; clear; tauto)) as Bv2. pose proof (Bv v3 ltac:(cbn; clear; tauto)) as Bv3.
      pose proof (Bv v4 ltac:(cbn; clear; tauto)) as Bv4. pose proof (Bv v5 ltac:(cbn; clear; tauto)) as Bv5. pose proof (Bv v6 ltac:(cbn; clear; tauto)) as Bv6. pose proof (Bv v7 ltac:(cbn; clear; tauto)) as Bv7. clear Bv.
      assert (GU : get_le64 buf5 (cur_off c' + 4) = le8val v0 v1 v2 v3 v4 v5 v6 v7).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply get_le64_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 8 (map b8 [v0; v1; v2; v3; v4; v5; v6; v7]); CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV8 _]. clear HV. cbn [firstn] in HV8.
      eapply evt_cut.
      { eapply ldu64_block with (A := (D + 4)%Z); [exact MI5 | lia | lia | exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7 | reflexivity | exact HV8]. }
      cbv beta. intros ms' (a3x & s8x' & s10x & t3x & ->).
      (* [comment removed for export] *)
      step.
      destruct sw.
      + cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb].
        eapply evt_cut.
        { eapply bswap64_block; [exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7]. }
        cbv beta. intros ms' (a3y & t3y & s8y & s9y & ->).
        rewrite (bswap64_bytes v0 v1 v2 v3 v4 v5 v6 v7) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre c0 c1 l0 l1 v0 v1 v2 v3 v4 v5 v6 v7 post' Bv0 Bv1 Bv2 Bv3 Bv4 Bv5 Bv6 Bv7; lia). rewrite <- (Z_to_bv64_s64 (le8val v7 v6 v5 v4 v3 v2 v1 v0)).
        replace (process_idb_options_loop fuel true) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
        rewrite <- (Z_to_bv64_s64 (le8val v0 v1 v2 v3 v4 v5 v6 v7)).
        replace (process_idb_options_loop fuel false) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 14) by lia. cbv beta iota delta [negb].
    replace (code =? IF_TSOFFSET) with false by (symmetry; apply Z.eqb_neq; exact NE14).
    step.
    destruct (Z.eq_dec code 0) as [E0|NE0].
    + rewrite (eqb_lits_eq _ _ E0). cbv iota. replace (code =? OPT_ENDOFOPT) with true by (rewrite E0; reflexivity). cbv iota.
      (* [comment removed for export] *)
      step.
      destruct (Z.eq_dec olen 0) as [L0|L0].
      * rewrite (eqb_lits_eq (olen * 2 ^ 48) 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_eq olen 0) L0). cbv beta iota delta [negb].
        eapply TAIL with (m3:=m5) (hd:=hd) (c':=c2) (opts:=io);
          [ exact U1 | exact U2 | exact U5 | exact IC1 | exact IC2 | exact SZ | exact LJS | exact HSA | exact SNR | exact TSR
          | exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact NG5 | exact AR15 | exact SL5 | exact AR25 | exact G5
          | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | exact CR1 | exact CR2 | exact CR3 | exact CR4 | exact HEB5 | exact OFG ].
      * rewrite (eqb_lits_false (olen * 2 ^ 48) 0) by (keep_hyps CEILV hptr sp R CUR lo p s js hd fuel c' pre post c0 c1 l0 l1 HOLEN L0; lia). cbv iota. rewrite (proj2 (Z.eqb_neq olen 0) L0). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_FMT_ENDOFOPT "Interface Description Block has opt_endofopt option with length %u != 0"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_ENDOFOPT; lia| unfold AI_FMT_ENDOFOPT; cbn; lia]).
        eapply SNP with (m3:=m5) (args:=[AInt olen]) (hd:=hd);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.endofopt_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ].
    + (* [comment removed for export] *)
      rewrite (eqb_lits_false code 0) by lia. cbv iota. replace (code =? OPT_ENDOFOPT) with false by (symmetry; apply Z.eqb_neq; exact NE0). cbv iota.
      replace (process_idb_options_loop fuel sw) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
      eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; exact TSR | exact FUEL2].
  Qed.
  End Sz7.
  Lemma ai_disp : ltac:(let t := eval cbv delta [ai_disp__stmt] in ai_disp__stmt in exact t).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. intros fuel LK io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D. ltac2:(SecDiet.SzSec.closeP 'ai_disp__body "vhvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_body__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte)
           (sw : bool) (pre post : list Z) (u0 u1 u2 u3 : Z) (bsr : list byte) (m4 : mem) (s8x : word),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (4 <= cur_remaining c')%Z ->
      pc_swapped p = sw ->
      buf' = pre ++ u0 :: u1 :: u2 :: u3 :: post -> Z.of_nat (length pre) = cur_off c' ->
      bs3 = map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr -> firstn (length post) bsr = map b8 post ->
      let c0 := (if sw then u1 else u0) in let c1 := (if sw then u0 else u1) in
      let l0 := (if sw then u3 else u2) in let l1 := (if sw then u2 else u3) in
      let code := (c0 + 256 * c1)%Z in let olen := (l0 + 256 * l1)%Z in let padded := ((olen + 3) / 4 * 4)%Z in
      (padded <= cur_remaining c' - 4)%Z ->
      mem_inv ssegs m4 ->
      munch [(CUR, CUR + 16); (B + cur_off c', B + cur_off c' + 4)]%Z m3 m4 -> wmono ssegs m3 m4 ->
      rw_cells ssegs m4 CUR [C8 (Z_to_bv 64 (B + cur_off c' + 4)); C8 (Z_to_bv 64 (cur_remaining c' - 4)); C4 (Z_to_bv 64 (cur_block_type c')); CB 4 cpad3] ->
      rw_cells ssegs m4 (B + cur_off c') [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1)
                   (pio_value fuel sw io code olen (mkCursor (cur_off c' + 4) (cur_remaining c' - 4) (cur_block_type c')) (pre ++ c0 :: c1 :: l0 :: l1 :: post))) stG)
        (MS (mkR (Z_to_bv 64 padded) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 20) (Z_to_bv 64 10) (Z_to_bv 64 EB) (Z_to_bv 64 P)
                 (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) (Z_to_bv 64 CUR) (Z_to_bv 64 olen)
                 (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 (Z.b2z (io_is_binary io))) (Z_to_bv 64 3) (Z_to_bv 64 9)
                 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 65280) (Z_to_bv 64 16711680) (Z_to_bv 64 (cur_remaining c' - 4))
                 (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) s8x (Z_to_bv 64 (Z.b2z sw))
                 (Z_to_bv 64 (B + cur_off c')) (Z_to_bv 64 (olen * 2 ^ 48)) (Z_to_bv 64 (B + cur_off c' + 4))
                 (Z_to_bv 64 14) (Z_to_bv 64 8) (Z_to_bv 64 (io_tsoffset io)))
            F (Z_to_bv 64 0x170f8) fc None m4 (seg_rom ssegs)).
  Section Sz8.
  Variables fuel io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 s8x : ltac2:(SecDiet.SzSec.tyM 'ai_body__stmt "vhvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_body__body : ltac2:(SecDiet.SzSec.bodyP 'ai_body__stmt "vhvvvvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt).
    intros LK IV FUEL GE4 SW Ebuf Lpre Ebs PFXr c0 c1 l0 l1 code olen padded FIT MI4 MU WM CC4 HOPT4.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
    assert (OFF0 : (8 <= cur_off c')%Z) by lia.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
    assert (Lpost : (Z.of_nat (length post) = Z.of_nat (length buf') - cur_off c' - 4)%Z) by (subst buf'; rewrite length_app in *; cbn [length] in *; lia).
    (* [comment removed for export] *)
    assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z /\ Forall (fun z => 0 <= z < 256)%Z pre /\ Forall (fun z => 0 <= z < 256)%Z post).
    { subst buf'. apply Forall_app in GR3 as [GA GB]. inversion GB as [|x0 l0' B0 GB1]; subst. inversion GB1 as [|x1 l1' B1 GB2]; subst.
      inversion GB2 as [|x2 l2' B2 GB3]; subst. inversion GB3 as [|x3 l3' B3 GB4]; subst. repeat split; try assumption; (keep_hyps CEILV hptr sp R CUR p s I' js hd fuel c' pre post u0 u1 u2 u3 bsr B0 B1 B2 B3; lia). }
    destruct GRh as ((B0 & B1 & B2 & B3) & GRpre & GRpost).
    assert (HC : (0 <= c0 < 256 /\ 0 <= c1 < 256 /\ 0 <= l0 < 256 /\ 0 <= l1 < 256)%Z) by (subst c0 c1 l0 l1; destruct sw; lia).
    destruct HC as (HC0 & HC1 & HL0 & HL1).
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel c' buf' bs3 sw pre post u0 u1 u2 u3 q2 q r q0 r0 H0 H1 H5 H6; lia)).
    set (buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post) in *.
    assert (LB5 : length buf5 = length buf') by (subst buf5 buf'; rewrite !length_app; reflexivity).
    assert (GR5 : Forall (fun z => 0 <= z < 256)%Z buf5) by (subst buf5; apply Forall_app; split; [exact GRpre|]; repeat (constructor; [lia|]); exact GRpost).
    (* [comment removed for export] *)
    remember (B + cur_off c')%Z as D eqn:HDd.
    step. rewrite (zx16_lit code) by lia.
    step. step. rewrite (unsigned_lit (cur_remaining c' - 4)), (unsigned_lit padded) by lia.
    pose proof (munch_refl [(CUR, CUR + 16)]%Z m4) as MU45. pose proof (wmono_refl ssegs m4) as WM45.
    hide HOPT4.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end. rename CC4 into CC5. rename MI4 into MI5.
    unhide HOPT4.
    (* [comment removed for export] *)
    assert (AGS45 : agrees_on (fun a => outside [(CUR, CUR + 16)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU45 | exact WM45 | intros a _ Ho; exact Ho]).
    transport HOPT4 m5 AGS45 ltac:(prs). rename HOPT4 into HOPT5.
    subst bs3. subst buf'.
    destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D _ IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI5 MU WM ltac:(subst code olen; exact HOPT5) CC5 eq_refl)
      as (ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5' & GR5' & _ & HEB5 & HB2 & RESTF5).
    set (bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr) in *.
    set (c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c')).
    assert (AIM5 : forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3).
    { intros io' TS'. split; [exact TS'|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact AG5|]. split; [exact HD5|]. split; [exact FR5|].
      split; [exact NG5|]. split; [exact AR15|]. split; [exact SL5|]. split; [exact AR25|]. split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|].
      split; [exact LB5'|]. split; [exact GR5'|]. split; [unfold cursor_cells; subst c2 D; cbn [cur_off cur_remaining cur_block_type]; replace (B + cur_off c' + 4 + padded)%Z with (B + (cur_off c' + 4 + padded))%Z in CC5 by lia; exact CC5|].
      subst c2; cbn [cur_off cur_remaining cur_block_type]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CR4| exact HEB5]. }
    (* [comment removed for export] *)
    unfold pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    fold padded. rewrite (proj2 (Z.ltb_ge (cur_remaining c' - 4) padded)) by lia. cbv beta iota. fold c2.
    assert (LEN5 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z) by (rewrite LB5; exact LEN4).
    apply (ai_disp fuel LK io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D AIM5 TSR SW FUEL GE4 FIT OFF0 LEN5 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2).
  Qed.
  End Sz8.
  Lemma ai_body : ltac:(let t := eval cbv delta [ai_body__stmt] in ai_body__stmt in exact t).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. intros fuel LK io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 s8x. ltac2:(SecDiet.SzSec.closeP 'ai_body__body "vhvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_iter__stmt : Prop := forall fuel, LOOPK fuel -> ITERK fuel.
  Section Sz9.
  Variables fuel ra' a3' s8' s9' s10' s11' t3' io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_iter__stmt "vhvvvvvvvvvvvvv" @fuel).
  Lemma ai_iter__body : ltac2:(SecDiet.SzSec.bodyP 'ai_iter__stmt "vhvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt).
    intros LK IV FUEL RPOS.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3).
    pose proof (ai_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU SPM TP ALN RSP SPW HinP P14 B14 APB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND EBX CLB CRE EBiv) as SNP.
    pose proof HPV as HPV3. transport HPV3 m3 AG3 ltac:(unfold ai_AGP, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s stG sg q1 I' js hd fuel c' buf' m3 LO BU P14 APB CUR1 EBX INPc G3; prs)).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    unfold cursor_cells in CC3.
    assert (REM64 : (cur_remaining c' < 2^32)%Z) by lia.
    rewrite pio_unfold. unfold pio_iter. rewrite (proj2 (Z.eqb_neq (cur_remaining c') 0)) by lia.
    unfold get_opthdr_from_block_data, get_from_block_data.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide HEB3. hide HPV3.
    unfold LREGS. step.
    destruct (Z.lt_ge_cases (cur_remaining c') 4) as [LT4|GE4].
    { (* [comment removed for export] *)
      replace (bv_ltu (Z_to_bv 64 3) (Z_to_bv 64 (cur_remaining c'))) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [negb].
      rewrite (proj2 (Z.ltb_lt (cur_remaining c') 4) LT4). rewrite ai_result_inl.
      step. rewrite (sx32_s32 (cur_block_type c')) by lia. do 4 step.
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide HEB3.
      assert (MSG : fmt_at m3 AI_FMT_TOOSHORT "block of type %u in pcapng dump file is too short"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold AI_FMT_TOOSHORT; lia| unfold AI_FMT_TOOSHORT; cbn; lia]).
      eapply SNP with (m3:=m3) (args:=[AInt (s32 (cur_block_type c'))]) (hd:=hd);
        [ exact MI3 | exact ST3 | exact AG3 | exact HD3 | exact Hhd | exact FR3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
        | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
        | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
          replace (convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
          apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
        | vm_compute; reflexivity | apply args_ok_ints1
        | eapply loop_restf; [exact G3 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF3 | exact PFX3 | exact LB3 | exact GR3 | exact CC3 | reflexivity] ]. }
    (* [comment removed for export] *)
    replace (bv_ltu (Z_to_bv 64 3) (Z_to_bv 64 (cur_remaining c'))) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_ge (cur_remaining c') 4) GE4). cbv beta iota.
    assert (OFF0 : (8 <= cur_off c')%Z) by lia.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
    destruct (split_at4 buf' (Z.to_nat (cur_off c')) ltac:(lia)) as (pre & u0 & u1 & u2 & u3 & post & Ebuf & Lpre).
    assert (LpreZ : Z.of_nat (length pre) = cur_off c') by lia. clear Lpre.
    subst buf'.
    destruct (pfx_decomp pre [u0; u1; u2; u3] post bs3 PFX3) as (bsr & Ebs & PFXr). cbn [map] in Ebs. subst bs3.
    assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z).
    { apply Forall_app in GR3 as [GA GB].
      pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. cbv beta in B0, B1, B2, B3. lia. }
    destruct GRh as (B0 & B1 & B2 & B3).
    (* [comment removed for export] *)
    unhide BUF3.
    pose proof (rw_cells_recell _ _ _ [CB (length pre) (map b8 pre); Cells.C2 (Z_to_bv 64 (u0 + 256 * u1)); Cells.C2 (Z_to_bv 64 (u2 + 256 * u3)); CB (length bsr) bsr] BUF3
                  ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX.
    destruct (rw_cells_cut _ _ _ 1 BX) as [_ BX2]. destruct (rw_cells_cut _ _ _ 2 BX2) as [HOPT _]. clear BX BX2. cbn [firstn skipn cells_size csize Nat.add app] in HOPT.
    remember (B + cur_off c')%Z as D eqn:HDd.
    lazymatch type of HOPT with rw_cells _ _ ?A _ => replace A with D in HOPT by lia end.
    hide BUF3.
    (* [comment removed for export] *)
    pose proof (munch_refl [(CUR, CUR + 16); (D, D + 4)]%Z m3) as MU. pose proof (wmono_refl ssegs m3) as WM.
    pose proof (munch_refl [(CUR, CUR + 16)]%Z m3) as MUc.
    hide HOPT.
    step. step. replace (cur_remaining c' + -4)%Z with (cur_remaining c' - 4)%Z by lia.
    step. step. step.
    step. rewrite (eqb_lits_false D 0) by lia. cbv iota.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4a end.
    assert (AGSc : agrees_on (fun a => outside [(CUR, CUR + 16)]%Z a) m3 m4a) by (eapply agrees_on_of_munch; [exact MUc | exact WM | intros a _ Ho; exact Ho]).
    unhide HPV3. transport HPV3 m4a AGSc ltac:(prs).
    step. rewrite (sx32_s32 (Z.b2z (pc_swapped p))) by (destruct (pc_swapped p); cbn; lia). rewrite (s32_small (Z.b2z (pc_swapped p))) by (destruct (pc_swapped p); cbn; lia).
    clear HPV3.
    unhide HOPT. transport HOPT m4a AGSc ltac:(prs).
    step.
    destruct (pc_swapped p) eqn:SW.
    - (* [comment removed for export] *)
      cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb].
      step. step. rewrite !zx16_lit by lia.
      step. step. step.
      match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
        replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (u1 + 256 * u0 + 65536 * u1)) by (f_equal; clear - B0 B1 B2 B3; norm_word; zlia) end.
      step. step. step.
      match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
        replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (u3 + 256 * u2 + 65536 * u3)) by (f_equal; clear - B0 B1 B2 B3; norm_word; zlia) end.
      (* [comment removed for export] *)
      pose proof (munch_refl [(D, D + 4)]%Z m4a) as MUd. pose proof (wmono_refl ssegs m4a) as WMd.
      hide CC3. clear MUc AGSc.
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
      step. step. rewrite (swap16_shl48 u3 u2) by lia. rewrite (shr48_of_shl48 (u3 + 256 * u2)) by lia.
      step. step. rewrite (unsigned_lit (u3 + 256 * u2 + 3)), land_m4w by lia.
      (* [comment removed for export] *)
      step.
      unhide CC3.
      assert (AGSd : agrees_on (fun a => outside [(D, D + 4)]%Z a) m4a m4) by (eapply agrees_on_of_munch; [exact MUd | exact WMd | intros a _ Ho; exact Ho]).
      transport CC3 m4 AGSd ltac:(prs). clear AGSd MUd WMd.
      pose proof (rw_cells_recell _ _ _ [Cells.C2 (Z_to_bv 64 (u1 + 256 * u0)); Cells.C2 (Z_to_bv 64 (u3 + 256 * u2))] HOPT ltac:(cbn; auto)
                    ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr B1 B0 B3 B2; lia);
                          rewrite (le2_of_val _ u1 u0 u1) by (try (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr B1 B0; lia); rewrite unsigned_lit by (keep_hyps CEILV hptr sp R CUR lo idb_off p s c js hd fuel c' pre u0 u1 u2 u3 post bsr B0 B1; lia); (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr; lia)); rewrite (le2_of_val _ u3 u2 u3) by (try (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr B3 B2; lia); rewrite unsigned_lit by (keep_hyps CEILV hptr sp R CUR lo idb_off p s c js hd fuel c' pre u0 u1 u2 u3 post bsr B2 B3; lia); (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr; lia)); reflexivity)) as HOPT4.
      clear HOPT.
      destruct (Z.le_gt_cases ((u3 + 256 * u2 + 3) / 4 * 4) (cur_remaining c' - 4)) as [FIT|NOFIT].
      + if_tf' true.
        assert (SWB : swap_field 2 (cur_off c' + 2) (swap_field 2 (cur_off c') (pre ++ u0 :: u1 :: u2 :: u3 :: post)) = pre ++ u1 :: u0 :: u3 :: u2 :: post) by (rewrite <- LpreZ, swap2_at, swap2_at2; reflexivity).
        assert (GL1 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c') = (u1 + 256 * u0)%Z) by (rewrite <- LpreZ; apply get_le16_at).
        assert (GL2 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c' + 2) = (u3 + 256 * u2)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite SWB, GL1, GL2. subst D.
        eapply (ai_body fuel LK io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 true pre post u0 u1 u2 u3 bsr m4);
          [exact IV | exact FUEL | exact GE4 | exact SW | reflexivity | exact LpreZ | reflexivity | exact PFXr | exact FIT | exact MI3 | exact MU | exact WM | exact CC3 | exact HOPT4].
      + (* [comment removed for export] *)
        if_tf' false. step.
        assert (SWB : swap_field 2 (cur_off c' + 2) (swap_field 2 (cur_off c') (pre ++ u0 :: u1 :: u2 :: u3 :: post)) = pre ++ u1 :: u0 :: u3 :: u2 :: post) by (rewrite <- LpreZ, swap2_at, swap2_at2; reflexivity).
        assert (GL2 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c' + 2) = (u3 + 256 * u2)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite SWB, GL2.
        unfold pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
        rewrite (proj2 (Z.ltb_lt (cur_remaining c' - 4) ((u3 + 256 * u2 + 3) / 4 * 4))) by lia. cbv beta iota.
        rewrite ai_result_inl.
        destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m4 u1 u0 u3 u2 D _ IV GE4 LpreZ HDd PFXr B1 B0 B3 B2 MI3 MU WM HOPT4 CC3 eq_refl)
          as (ST4 & AG4 & HD4 & FR4 & NG4 & AR14 & SL4 & AR24 & G4 & BUF4 & PFX4 & LB4 & GR4 & _ & HEB4 & _ & RESTF4).
        hide HD4. hide FR4. hide HEB4.
        step. rewrite (sx32_s32 (cur_block_type c')) by lia. do 4 step.
        unhide HD4. unhide FR4. unhide HEB4.
        assert (MSG : fmt_at m4 AI_FMT_TOOSHORT "block of type %u in pcapng dump file is too short"%string)
          by (apply (fmt_at_intro m4 _ _ MI3); [vm_compute; reflexivity| unfold AI_FMT_TOOSHORT; lia| unfold AI_FMT_TOOSHORT; cbn; lia]).
        eapply SNP with (m3:=m4) (args:=[AInt (s32 (cur_block_type c'))]) (hd:=hd);
          [ exact MI3 | exact ST4 | exact AG4 | exact HD4 | exact Hhd | exact FR4 | exact HEB4 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
          | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints1
          | exact RESTF4 ].
    - (* [comment removed for export] *)
      cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      clear MUc AGSc.
      step. rewrite !zx16_lit by lia.
      step. rewrite (unsigned_lit (u2 + 256 * u3)), Z.shiftl_mul_pow2 by lia.
      step. rewrite (shr48_of_shl48 (u2 + 256 * u3)) by lia.
      step. step. rewrite (unsigned_lit (u2 + 256 * u3 + 3)), land_m4w by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
      step.
      destruct (Z.le_gt_cases ((u2 + 256 * u3 + 3) / 4 * 4) (cur_remaining c' - 4)) as [FIT|NOFIT].
      + if_tf' false.
        assert (GL1 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c') = (u0 + 256 * u1)%Z) by (rewrite <- LpreZ; apply get_le16_at).
        assert (GL2 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c' + 2) = (u2 + 256 * u3)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite GL1, GL2. subst D.
        eapply (ai_body fuel LK io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 false pre post u0 u1 u2 u3 bsr m4);
          [exact IV | exact FUEL | exact GE4 | exact SW | reflexivity | exact LpreZ | reflexivity | exact PFXr | exact FIT | exact MI3 | exact MU | exact WM | exact CC3 | exact HOPT].
      + (* [comment removed for export] *)
        if_tf' true.
        assert (GL2 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c' + 2) = (u2 + 256 * u3)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite GL2.
        unfold pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
        rewrite (proj2 (Z.ltb_lt (cur_remaining c' - 4) ((u2 + 256 * u3 + 3) / 4 * 4))) by lia. cbv beta iota.
        rewrite ai_result_inl.
        destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m4 u0 u1 u2 u3 D _ IV GE4 LpreZ HDd PFXr B0 B1 B2 B3 MI3 MU WM HOPT CC3 eq_refl)
          as (ST4 & AG4 & HD4 & FR4 & NG4 & AR14 & SL4 & AR24 & G4 & BUF4 & PFX4 & LB4 & GR4 & _ & HEB4 & _ & RESTF4).
        hide HD4. hide FR4. hide HEB4.
        step. rewrite (sx32_s32 (cur_block_type c')) by lia. do 4 step.
        unhide HD4. unhide FR4. unhide HEB4.
        assert (MSG : fmt_at m4 AI_FMT_TOOSHORT "block of type %u in pcapng dump file is too short"%string)
          by (apply (fmt_at_intro m4 _ _ MI3); [vm_compute; reflexivity| unfold AI_FMT_TOOSHORT; lia| unfold AI_FMT_TOOSHORT; cbn; lia]).
        eapply SNP with (m3:=m4) (args:=[AInt (s32 (cur_block_type c'))]) (hd:=hd);
          [ exact MI3 | exact ST4 | exact AG4 | exact HD4 | exact Hhd | exact FR4 | exact HEB4 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
          | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints1
          | exact RESTF4 ].
  Qed.
  End Sz9.
  Lemma ai_iter : ltac:(let t := eval cbv delta [ai_iter__stmt] in ai_iter__stmt in exact t).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. intros fuel LK ra' a3' s8' s9' s10' s11' t3' io c' buf' m3 bs3 cpad3. ltac2:(SecDiet.SzSec.closeP 'ai_iter__body "vhvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Theorem ai_loop : forall fuel, LOOPK fuel.
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt). induction fuel as [|fuel IH]; [apply ai_loop0 | apply ai_loop_step, ai_iter, IH]. Qed.

  (* [comment removed for export] *)
  Theorem ai_enter : forall (ra' a3' xa4 xa5 xs5 xs6 xs7 s8' s9' s10' s11' t3' xt6 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte) (fuel : nat),
      xa4 = Z_to_bv 64 (io_tsresol io) -> xa5 = Z_to_bv 64 (Z.b2z (io_is_binary io)) -> xs5 = Z_to_bv 64 (cur_remaining c') ->
      xs6 = Z_to_bv 64 (Z.b2z (io_saw_tsoffset io)) -> xs7 = Z_to_bv 64 (Z.b2z (io_saw_tsresol io)) -> xt6 = Z_to_bv 64 (io_tsoffset io) ->
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (0 < cur_remaining c')%Z ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options_loop (S fuel) (pc_swapped p) io c' buf')) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 20) (Z_to_bv 64 10) (Z_to_bv 64 EB) (Z_to_bv 64 P)
                 (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) (Z_to_bv 64 CUR) a3' xa4 xa5 (Z_to_bv 64 3) (Z_to_bv 64 9)
                 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 65280) (Z_to_bv 64 16711680) xs5 xs6 xs7 s8' s9' s10' s11' t3'
                 (Z_to_bv 64 14) (Z_to_bv 64 8) xt6) F (Z_to_bv 64 0x1707c) fc None m3 (seg_rom ssegs)).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt). intros until fuel. intros -> -> -> -> -> -> IV FUEL RPOS. pose proof (ai_iter fuel (ai_loop fuel)) as IT. red in IT. eapply IT; eassumption. Qed.

  (* [comment removed for export] *)
  Theorem ai_done : forall (ra' t0' t1' t2' a2' a3' xa4 xa5 a6' a7' t3' t4' t5' xt6 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      xa4 = Z_to_bv 64 (io_tsresol io) -> xa5 = Z_to_bv 64 (Z.b2z (io_is_binary io)) -> xt6 = Z_to_bv 64 (io_tsoffset io) ->
      AIM io c' buf' m3 bs3 cpad3 ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1) (buf', inr (io, c'))) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 P)
                 (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) a2' a3' xa4 xa5 a6' a7'
                 (Z_to_bv 64 (P + 648)) y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' xt6)
            F (Z_to_bv 64 0x17240) fc None m3 (seg_rom ssegs)).
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS. pin_using (fun (APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS : unit) => tt).
    intros until cpad3. intros -> -> -> IV.
    destruct IV as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3).
    eapply (ai_tail K HFL SFL); eassumption || (try exact IC1; try exact HSA; try lia).
  Qed.
End AIE.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiC.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition pio_body (fuel : nat) (sw : bool) (st : idbopts) (code olen voff : Z) (c1 : cursor) (buf0 : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  (if code =? OPT_ENDOFOPT then
     if negb (olen =? 0) then (buf0, inl (Msg.endofopt_len olen)) else (buf0, inr (st, c1))
   else if code =? IF_TSRESOL then
     if negb (olen =? 1) then (buf0, inl (Msg.tsresol_len olen)) else
     if io_saw_tsresol st then (buf0, inl Msg.tsresol_dup) else
     let tsresol_opt := get_u8 buf0 voff in
     if negb (Z.land tsresol_opt 128 =? 0) then
       let tsresol_shift := Z.land tsresol_opt 127 in
       if 63 <? tsresol_shift then (buf0, inl (Msg.tsresol_bin_high tsresol_shift))
       else process_idb_options_loop fuel sw (mkIdbOpts (2 ^ tsresol_shift) (io_tsoffset st) true true (io_saw_tsoffset st)) c1 buf0
     else
       if 19 <? tsresol_opt then (buf0, inl (Msg.tsresol_dec_high tsresol_opt))
       else process_idb_options_loop fuel sw (mkIdbOpts (10 ^ tsresol_opt) (io_tsoffset st) false true (io_saw_tsoffset st)) c1 buf0
   else if code =? IF_TSOFFSET then
     if negb (olen =? 8) then (buf0, inl (Msg.tsoffset_len olen)) else
     if io_saw_tsoffset st then (buf0, inl Msg.tsoffset_dup) else
     let raw := get_le64 buf0 voff in
     let tsoffset := if sw then s64 (bswap64 raw) else s64 raw in
     process_idb_options_loop fuel sw (mkIdbOpts (io_tsresol st) tsoffset (io_is_binary st) (io_saw_tsresol st) true) c1 buf0
   else process_idb_options_loop fuel sw st c1 buf0)%Z.
Definition pio_value (fuel : nat) (sw : bool) (st : idbopts) (code olen : Z) (c0 : cursor) (buf0 : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  match get_optvalue_from_block_data c0 olen with
  | inl m => (buf0, inl m)
  | inr (voff, c1) => pio_body fuel sw st code olen voff c1 buf0
  end.
Definition pio_iter (fuel : nat) (sw : bool) (st : idbopts) (c : cursor) (buf : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  (if cur_remaining c =? 0 then (buf, inr (st, c)) else
    match get_opthdr_from_block_data sw c buf with
    | inl m => (buf, inl m)
    | inr (code, olen, c0, buf0) => pio_value fuel sw st code olen c0 buf0
    end)%Z.
Lemma pio_unfold : forall fuel sw st c buf, process_idb_options_loop (S fuel) sw st c buf = pio_iter fuel sw st c buf.
Proof using Type. pin_using tt. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zslice_at {A} (pre l post : list A) : zslice (Z.of_nat (length pre)) (Z.of_nat (length l)) (pre ++ l ++ post) = l.
Proof using Type. pin_using tt.
  unfold zslice, zfirstn, zskipn. rewrite !Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. unfold skipn. cbn.
  rewrite firstn_app, firstn_all, Nat.sub_diag by lia. cbn. apply app_nil_r.
Qed.
Lemma get_le16_at pre u0 u1 rest : get_le16 (pre ++ u0 :: u1 :: rest) (Z.of_nat (length pre)) = u0 + 256 * u1.
Proof using Type. pin_using tt.
  unfold get_le16. change (pre ++ u0 :: u1 :: rest) with (pre ++ [u0; u1] ++ rest). change 2 with (Z.of_nat (length [u0; u1])).
  rewrite zslice_at. cbn. lia.
Qed.
Lemma get_le16_at2 pre u0 u1 u2 u3 rest : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: rest) (Z.of_nat (length pre) + 2) = u2 + 256 * u3.
Proof using Type. pin_using tt.
  replace (pre ++ u0 :: u1 :: u2 :: u3 :: rest) with ((pre ++ [u0; u1]) ++ u2 :: u3 :: rest) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 2) with (Z.of_nat (length (pre ++ [u0; u1]))) by (rewrite length_app; cbn; lia). apply get_le16_at.
Qed.
Lemma get_u8_at pre v rest : get_u8 (pre ++ v :: rest) (Z.of_nat (length pre)) = v.
Proof using Type. pin_using tt. unfold get_u8, znth. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Nat2Z.id. apply nth_middle. Qed.
Lemma get_le64_at pre v0 v1 v2 v3 v4 v5 v6 v7 rest :
  get_le64 (pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest) (Z.of_nat (length pre)) = le8val v0 v1 v2 v3 v4 v5 v6 v7.
Proof using Type. pin_using tt.
  unfold get_le64. change (pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest) with (pre ++ [v0; v1; v2; v3; v4; v5; v6; v7] ++ rest).
  change 8 with (Z.of_nat (length [v0; v1; v2; v3; v4; v5; v6; v7])). rewrite zslice_at. cbn -[Z.add Z.mul]. unfold le8val. lia.
Qed.
Lemma swap2_at pre u0 u1 rest : swap_field 2 (Z.of_nat (length pre)) (pre ++ u0 :: u1 :: rest) = pre ++ u1 :: u0 :: rest.
Proof using Type. pin_using tt.
  unfold swap_field.
  replace (zslice (Z.of_nat (length pre)) 2 (pre ++ u0 :: u1 :: rest)) with [u0; u1] by (symmetry; exact (zslice_at pre [u0; u1] rest)).
  unfold buf_write_at, zfirstn, zskipn, zlength. cbn [rev app length].
  rewrite Nat2Z.id, firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  replace (Z.to_nat (Z.of_nat (length pre) + Z.of_nat 2)) with (length pre + 2)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. replace (length pre + 2 - length pre)%nat with 2%nat by lia. reflexivity.
Qed.
Lemma swap2_at2 pre u0 u1 u2 u3 rest : swap_field 2 (Z.of_nat (length pre) + 2) (pre ++ u0 :: u1 :: u2 :: u3 :: rest) = pre ++ u0 :: u1 :: u3 :: u2 :: rest.
Proof using Type. pin_using tt.
  replace (pre ++ u0 :: u1 :: u2 :: u3 :: rest) with ((pre ++ [u0; u1]) ++ u2 :: u3 :: rest) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 2) with (Z.of_nat (length (pre ++ [u0; u1]))) by (rewrite length_app; cbn; lia).
  rewrite swap2_at, <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pfx_decomp (pre mid post : list Z) (bs : list byte) :
  firstn (length (pre ++ mid ++ post)) bs = map b8 (pre ++ mid ++ post) ->
  exists bsr, bs = map b8 pre ++ map b8 mid ++ bsr /\ firstn (length post) bsr = map b8 post.
Proof using Type. pin_using tt.
  intros H. set (k := (length pre + length mid)%nat). exists (skipn k bs).
  assert (Hk : firstn k bs = map b8 pre ++ map b8 mid).
  { transitivity (firstn k (firstn (length (pre ++ mid ++ post)) bs)).
    - rewrite firstn_firstn. f_equal. rewrite !length_app. lia.
    - rewrite H, !map_app, app_assoc, firstn_app, firstn_all2 by (rewrite !length_app, !length_map; lia).
      rewrite length_app, !length_map. replace (k - (length pre + length mid))%nat with 0%nat by lia. cbn. apply app_nil_r. }
  split.
  - rewrite <- (firstn_skipn k bs) at 1. rewrite Hk, <- app_assoc. reflexivity.
  - rewrite firstn_skipn_comm. replace (k + length post)%nat with (length (pre ++ mid ++ post)) by (rewrite !length_app; lia).
    rewrite H, !map_app, app_assoc, skipn_app, skipn_all2 by (rewrite length_app, !length_map; lia).
    rewrite length_app, !length_map. replace (k - (length pre + length mid))%nat with 0%nat by lia. reflexivity.
Qed.
Lemma pfx_comp (pre mid post : list Z) (bsr : list byte) :
  firstn (length post) bsr = map b8 post ->
  firstn (length (pre ++ mid ++ post)) (map b8 pre ++ map b8 mid ++ bsr) = map b8 (pre ++ mid ++ post).
Proof using Type. pin_using tt.
  intros H. rewrite !length_app, !map_app.
  rewrite firstn_app, length_map, firstn_all2 by (rewrite length_map; lia). f_equal.
  rewrite firstn_app, length_map, firstn_all2 by (rewrite length_map; lia). f_equal.
  replace (length pre + (length mid + length post) - length pre - length mid)%nat with (length post) by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma split_at4 (buf : list Z) (off : nat) : (off + 4 <= length buf)%nat ->
  exists pre u0 u1 u2 u3 post, buf = pre ++ u0 :: u1 :: u2 :: u3 :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|u0 [|u1 [|u2 [|u3 post]]]] eqn:E;
    try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists u0, u1, u2, u3, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.
Lemma split_at8 (buf : list Z) (off : nat) : (off + 8 <= length buf)%nat ->
  exists pre v0 v1 v2 v3 v4 v5 v6 v7 post, buf = pre ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post]]]]]]]] eqn:E;
    try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists v0, v1, v2, v3, v4, v5, v6, v7, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.
Lemma split_at1 (buf : list Z) (off : nat) : (off + 1 <= length buf)%nat ->
  exists pre v post, buf = pre ++ v :: post /\ length pre = off.
Proof using Type. pin_using tt.
  intros Hl. exists (firstn off buf).
  destruct (skipn off buf) as [|v post] eqn:E; try (apply (f_equal (@length Z)) in E; rewrite length_skipn in E; cbn in E; lia).
  exists v, post. split; [| apply firstn_length_le; lia]. rewrite <- E. symmetry. apply firstn_skipn.
Qed.


(* [comment removed for export] *)
Lemma swap16_val a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor ((a + 256 * b) * 2 ^ 8) ((a + 256 * b) / 2 ^ 8) = b + 256 * a + 65536 * b.
Proof using Type. pin_using tt.
  intros Ha Hb. replace ((a + 256 * b) / 2 ^ 8) with b by (Z.div_mod_to_equations; lia).
  rewrite lor_high_low by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma land_m4 x : 0 <= x -> Z.land x (-4) = x / 4 * 4.
Proof using Type. pin_using tt.
  intros Hx. change (-4) with (Z.lnot (Z.ones 2)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma Z_to_bv64_mod x y : x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof using Type. pin_using tt. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul]. cbn in E. exact E. Qed.
(* [comment removed for export] *)
Lemma Z_to_bv64_s64 x : Z_to_bv 64 (s64 x) = Z_to_bv 64 x.
Proof using Type. pin_using tt. apply Z_to_bv64_mod. unfold s64. Z.div_mod_to_equations. lia. Qed.

Lemma land_128 v : 0 <= v < 256 -> Z.land v 128 = 128 * (v / 128).
Proof using Type. pin_using tt.
  intros Hv. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. change 128 with (2 ^ 7) at 1. rewrite Z.pow2_bits_eqb by lia.
  assert (Q : v / 2 ^ 7 = 0 \/ v / 2 ^ 7 = 1) by (Z.div_mod_to_equations; lia).
  destruct (Z.eqb_spec 7 n) as [<-|NE].
  - rewrite andb_true_r. change 128 with (2 ^ 7). destruct Q as [Q|Q]; rewrite Q.
    + rewrite Z.mul_0_r, Z.bits_0. apply Z.testbit_false; [lia|]. rewrite Q. reflexivity.
    + rewrite Z.mul_1_r, Z.pow2_bits_true by lia. apply Z.testbit_true; [lia|]. rewrite Q. reflexivity.
  - rewrite andb_false_r. change 128 with (2 ^ 7). destruct Q as [Q|Q]; rewrite Q.
    + rewrite Z.mul_0_r, Z.bits_0. reflexivity.
    + rewrite Z.mul_1_r, Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. exact NE.
Qed.
Lemma land_127_hi v : 128 <= v < 256 -> Z.land v 127 = v - 128.
Proof using Type. pin_using tt. intros. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. Z.div_mod_to_equations; lia. Qed.
Lemma land_255_mod v : Z.land v 255 = v mod 256.
Proof using Type. pin_using tt. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma signed_lit_any x : -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof using Type. pin_using tt.
  intros Hx. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.div Z.mul Z.opp].
  Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac if_tf' b := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux;
                     rewrite ?unsigned_lit, ?signed_lit_any by lia; zc_rec] end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma Z_to_bv64_drop x k : Z_to_bv 64 (x + k * 2^64) = Z_to_bv 64 x.
Proof using Type. pin_using tt. apply Z_to_bv64_mod. rewrite Z_mod_plus_full. reflexivity. Qed.
(* [comment removed for export] *)
Lemma swap16_shl48 a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (a + 256 * b + 65536 * a))) 48) = Z_to_bv 64 ((a + 256 * b) * 2 ^ 48).
Proof using Type. pin_using tt.
  intros Ha Hb. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((a + 256 * b + 65536 * a) * 2 ^ 48) with ((a + 256 * b) * 2 ^ 48 + a * 2 ^ 64) by lia. apply Z_to_bv64_drop.
Qed.
Lemma shr48_of_shl48 x : 0 <= x < 65536 -> Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (x * 2 ^ 48))) 48) = Z_to_bv 64 x.
Proof using Type. pin_using tt. intros Hx. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. Qed.

Lemma land_m4w x : 0 <= x < 2^64 -> Z.land x 18446744073709551612 = x / 4 * 4.
Proof using Type. pin_using tt.
  intros Hx. change 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))).
  rewrite Z.land_assoc, Z.land_ones, Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma and1_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 2 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 1 = 0%Z.
Proof using Type. pin_using tt.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1)%Z with 2%Z. exact Ha.
Qed.
Lemma mod2_of_16_4 : forall b o, (b mod 16 = 0)%Z -> (o mod 4 = 0)%Z -> ((b + o) mod 2 = 0)%Z.
Proof using Type. pin_using tt. intros b o Hb Ho. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_advance : forall o p, (o mod 4 = 0)%Z -> (p mod 4 = 0)%Z -> ((o + 4 + p) mod 4 = 0)%Z.
Proof using Type. pin_using tt. intros o p Ho Hp. Z.div_mod_to_equations. lia. Qed.

Section AIE.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m.
  Hypothesis ST : stk usegs m lo (bv_unsigned sp).
  Hypothesis LO : usp0 R - 8388608 <= lo.
  Hypothesis BU : lo + (65536 + 112) <= bv_unsigned sp.
  Hypothesis SPM : bv_unsigned sp <= rc_spmain R.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : bv_unsigned sp mod 16 = 0.
  Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPW : 0x7fff80000000 <= usp0 R.
  Hypothesis SP47 : usp0 R <= 2^47.
  Hypothesis HS : pc_priv p = PrivNg s i.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis B14 : 0 < B /\ B + pc_bufalloc p <= CEILZ.
  Hypothesis APB : P + 680 <= B \/ B + pc_bufalloc p <= P.
  (* [comment removed for export] *)
  Hypothesis P5 : out_of_image P 680.
  Hypothesis HPV : rw_cells usegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].
  Hypothesis HNG : rw_cells usegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad).
  Hypothesis HIF : ifaces_ok p I m.
  Hypothesis UTS : 0 < ng_user_tsresol s < 2^64.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis WMB : 0 <= ng_max_blocksize s < 2^32.
  Hypothesis HBUF : rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs].
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis LENB : Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32.
  Hypothesis GRD : Forall (fun z => 0 <= z < 256) (pc_bufdata p).
  Hypothesis HCUR : rw_cells usegs m CUR (cursor_cells B c cpad).
  Hypothesis CUR1 : bv_unsigned sp <= CUR.
  Hypothesis CUR2 : CUR + 24 <= rc_spmain R.
  Hypothesis CUR8 : CUR mod 8 = 0.
  Hypothesis IDB0 : 0 <= idb_off.
  Hypothesis COFF : cur_off c = idb_off + 8.
  Hypothesis CREM : 0 <= cur_remaining c.
  Hypothesis CEND : cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)).
  Hypothesis CBT : 0 <= cur_block_type c < 2^32.
  Hypothesis HEB : rw_cells usegs m EB [CB 256 ej].
  Hypothesis EBX : (bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ EB = P + 216.
  Hypothesis EB64 : 0 < EB /\ EB + 256 < 2^64.
  (* [comment removed for export] *)
  Hypothesis CLB : forall a, in_block (C1 ++ C2) a -> a < CEILZ.
  Hypothesis INPc : forall a, P <= a < P + 680 -> in_block (C1 ++ C2) a.
  Hypothesis INBc : forall a, B <= a < B + pc_bufalloc p -> in_block (C1 ++ C2) a.
  Hypothesis CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256.
  Hypothesis EBiv : client_iv R (C1 ++ C2) (EB, EB + 256).

  #[local] Notation POSTQ := (add_interface_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Notation AGP := (ai_AGP sp C1 C2 P B CUR EB p m).
  #[local] Notation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  #[local] Notation AIREST := (ai_REST K R C1 C2 FB P B CUR EB p s c ej (ps_outfile st)).
  #[local] Notation AIREST_F := (ai_REST_F K R C1 C2 FB P B CUR p s (ps_outfile st)).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Variables (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte) (hd : list cell).
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap idb_off p < 2^32)%Z.
  Hypothesis Hhd : cells_size hd = 8%nat.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Definition sgF : pcap_ng_sf := mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot0 idb_off p :: ng_ifaces sg).
  Definition pF (buf' : list Z) : pcapT := set_bufdata buf' (set_ng sgF (Some q1) (set_ng sg (Some q1) p)).
  Lemma ai_result_inl : forall buf' msg, ai_result idb_off p s c sg (Some q1) (buf', inl msg) = (false, c, pF buf', msg).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition AIM (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte) : Prop :=
    (0 < io_tsresol io < 2^64)%Z /\
    mem_inv usegs m3 /\ stk usegs m3 lo (bv_unsigned sp + -112) /\ AGP m3 /\
    rw_cells usegs m3 (bv_unsigned sp + -112) hd /\ FRAME m3 /\
    rw_cells usegs m3 (P + 648) (ng_cells sg I' pad1) /\
    rw_cells usegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) /\
    rw_cells usegs m3 SA [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sj] /\
    rw_cells usegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] /\
    GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m3 /\
    rw_cells usegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] /\ firstn (length buf') bs3 = map b8 buf' /\ length buf' = length (pc_bufdata p) /\
    Forall (fun z => 0 <= z < 256)%Z buf' /\
    rw_cells usegs m3 CUR (cursor_cells B c' cpad3) /\
    (0 <= cur_remaining c')%Z /\ (cur_off c <= cur_off c')%Z /\ (cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c)%Z /\
    cur_block_type c' = cur_block_type c /\
    rw_cells usegs m3 EB [CB 256 ej] /\
    (cur_off c' mod 4 = 0)%Z.

  (* [comment removed for export] *)
  Definition LREGS (ra' a3' s8' s9' s10' s11' : word) (io : idbopts) (c' : cursor) :=
    mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.b2z (io_is_binary io))) (Z_to_bv 64 19) (Z_to_bv 64 EB) (Z_to_bv 64 (P + 648))
        (Z_to_bv 64 P) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 CUR) a3'
        (Z_to_bv 64 SA) (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 9)
        (Z_to_bv 64 65280) (Z_to_bv 64 16711680) (Z_to_bv 64 (io_tsoffset io)) (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (cur_remaining c'))
        s8' s9' s10' s11' (Z_to_bv 64 10) (Z_to_bv 64 63) (Z_to_bv 64 14) (Z_to_bv 64 8).

  Definition LOOPK (fuel : nat) : Prop :=
    forall (ra' a3' xa1 xt1 xs7 xs5 xs6 s8' s9' s10' s11' xs4 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      xa1 = Z_to_bv 64 (io_tsresol io) -> xt1 = Z_to_bv 64 (Z.b2z (io_is_binary io)) -> xs7 = Z_to_bv 64 (cur_remaining c') ->
      xs5 = Z_to_bv 64 (Z.b2z (io_saw_tsoffset io)) -> xs6 = Z_to_bv 64 (Z.b2z (io_saw_tsresol io)) -> xs4 = Z_to_bv 64 (io_tsoffset io) ->
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat fuel)%Z ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options_loop fuel (pc_swapped p) io c' buf')) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) xt1 (Z_to_bv 64 19) (Z_to_bv 64 EB) (Z_to_bv 64 (P + 648))
                 (Z_to_bv 64 P) xa1 (Z_to_bv 64 CUR) a3' (Z_to_bv 64 SA) (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 9)
                 (Z_to_bv 64 65280) (Z_to_bv 64 16711680) xs4 xs5 xs6 xs7 s8' s9' s10' s11'
                 (Z_to_bv 64 10) (Z_to_bv 64 63) (Z_to_bv 64 14) (Z_to_bv 64 8)) F (Z_to_bv 64 0x176a8) fc None m3 (seg_rom usegs)).
  Definition ITERK (fuel : nat) : Prop :=
    forall (ra' a3' s8' s9' s10' s11' : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (0 < cur_remaining c')%Z ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options_loop (S fuel) (pc_swapped p) io c' buf')) stG)
        (MS (LREGS ra' a3' s8' s9' s10' s11' io c') F (Z_to_bv 64 0x176ac) fc None m3 (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition ai_loop_step__stmt : Prop := forall fuel, ITERK fuel -> LOOPK (S fuel).
  Section Sz6.
  Variables fuel ra' a3' xa1 xt1 xs7 xs5 xs6 s8' s9' s10' s11' xs4 io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_loop_step__stmt "vhvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_loop_step__body : ltac2:(SecDiet.SzSec.bodyP 'ai_loop_step__stmt "vhvvvvvvvvvvvvvvvvvv").
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS. pin_using (fun (APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS : unit) => tt).
    intros IT.
 intros -> -> -> -> -> -> IV FUEL.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & AL4).
    clear HPV HNG HBUF HCUR HEB HIF.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide CC3. hide HEB3.
    step.
    destruct (Z.eq_dec (cur_remaining c') 0) as [R0|R0].
    - rewrite (eqb_lits_eq _ _ R0). cbv iota. rewrite pio_unfold. unfold pio_iter. rewrite (proj2 (Z.eqb_eq _ _) R0).
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      eapply (ai_tail K HFL SFL); eassumption || (try exact IC1; try exact HSA; try lia).
    - rewrite (eqb_lits_false (cur_remaining c') 0) by lia. cbv iota.
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      apply (IT ra' a3' s8' s9' s10' s11' io c' buf' m3 bs3 cpad3 IV FUEL ltac:(lia)).
  Qed.
  End Sz6.
  Lemma ai_loop_step : ltac:(let t := eval cbv delta [ai_loop_step__stmt] in ai_loop_step__stmt in exact t).
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS. intros fuel IT ra' a3' xa1 xt1 xs7 xs5 xs6 s8' s9' s10' s11' xs4 io c' buf' m3 bs3 cpad3. ltac2:(SecDiet.SzSec.closeP 'ai_loop_step__body "vhvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma ai_loop0 : LOOPK O.
  Proof using Type. pin_using tt. red. intros until cpad3. intros _ _ _ _ _ _ IV FUEL. destruct IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR1 & _). exfalso. clear - FUEL CR1. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Definition loop_restf__stmt : Prop := forall (m3 : mem) (buf' : list Z) (bs3 : list byte) (ccs : list cell),
    GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m3 ->
    rw_cells usegs m3 (P + 648) (ng_cells sg I' pad1) ->
    rw_cells usegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) ->
    rw_cells usegs m3 SA [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sj] ->
    rw_cells usegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] ->
    rw_cells usegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] -> firstn (length buf') bs3 = map b8 buf' -> length buf' = length (pc_bufdata p) ->
    Forall (fun z => 0 <= z < 256)%Z buf' ->
    rw_cells usegs m3 CUR ccs -> cells_size ccs = 24%nat ->
    AIREST_F m3 stG c (pF buf').
  Section Sz8.
  Variables m3 buf' bs3 ccs : ltac2:(SecDiet.SzSec.tyM 'loop_restf__stmt "vvvv" @m3).
  Lemma loop_restf__body : ltac2:(SecDiet.SzSec.bodyP 'loop_restf__stmt "vvvv").
  Proof using BU CUR1 HSA Hhd IC1 IC2 LJS LO OFG RSP SPW SZ U1 U2. pin_using (fun (BU CUR1 HSA Hhd IC1 IC2 LJS LO OFG RSP SPW SZ U1 U2 : unit) => tt).
    intros G3 NG3 AR1 SL3 AR2 BUF3 PFX3 LB3 GR3 CC3 Hccs.
    exists sgF, (Some q1), I', pad1, bs3.
    split; [exact OFG|]. split; [reflexivity|]. split; [exact G3|]. split; [exact NG3|]. split; [cbn; exact U1|]. split; [cbn; exact U2|]. split; [cbn; lia|]. split; [cbn; lia|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LB3|]. split; [exact GR3|]. split.
    - cbn [ng_ifaces_closable sgF ng_ifaces_size]. split; [| lia].
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      pose proof (rw_cells_uncut _ _ _ _ _ AR1 SL3 ltac:(rewrite ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 AR2 ltac:(rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize]; lia)) as J2.
      destruct (rw_cells_forget _ _ _ _ J2) as [junk HJ]. exists junk.
      rewrite !cells_size_app, ifs_cells_size in HJ by (rewrite length_rev; lia). rewrite length_rev in HJ. cbn [cells_size csize Nat.add] in HJ.
      lazymatch type of HJ with rw_cells _ _ _ [CB ?n _] => replace (Z.to_nat (40 * ng_ifaces_size sg)) with n by lia end. exact HJ.
    - exists ccs. split; [exact CC3| exact Hccs].
  Qed.
  End Sz8.
  Lemma loop_restf : ltac:(let t := eval cbv delta [loop_restf__stmt] in loop_restf__stmt in exact t).
  Proof using BU CUR1 HSA Hhd IC1 IC2 LJS LO OFG RSP SPW SZ U1 U2. intros m3 buf' bs3 ccs. ltac2:(SecDiet.SzSec.closeP 'loop_restf__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition loop_facts__stmt : Prop := forall (io : idbopts) (c' : cursor) (pre post : list Z) (u0 u1 u2 u3 : Z) (bsr cpad3 : list byte) (m3 m5 : mem)
      (c0 c1 l0 l1 : Z) (D : Z) (ccs : list cell),
      AIM io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 ->
      (4 <= cur_remaining c')%Z -> Z.of_nat (length pre) = cur_off c' -> D = (B + cur_off c')%Z ->
      firstn (length post) bsr = map b8 post ->
      (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z ->
      mem_inv usegs m5 -> munch [(CUR, CUR + 16); (D, D + 4)]%Z m3 m5 -> wmono usegs m3 m5 ->
      rw_cells usegs m5 D [Cells.C2 (Z_to_bv 64 (c0 + 256 * c1)); Cells.C2 (Z_to_bv 64 (l0 + 256 * l1))] ->
      rw_cells usegs m5 CUR ccs -> cells_size ccs = 24%nat ->
      let buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post in let bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr in
      stk usegs m5 lo (bv_unsigned sp + -112) /\ AGP m5 /\
      rw_cells usegs m5 (bv_unsigned sp + -112) hd /\ FRAME m5 /\
      rw_cells usegs m5 (P + 648) (ng_cells sg I' pad1) /\
      rw_cells usegs m5 I' (ifs_cells (rev (ng_ifaces s)) js) /\
      rw_cells usegs m5 SA [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sj] /\
      rw_cells usegs m5 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] /\
      GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m5 /\
      rw_cells usegs m5 B [CB (Z.to_nat (pc_bufalloc p)) bs5] /\ firstn (length buf5) bs5 = map b8 buf5 /\ length buf5 = length (pc_bufdata p) /\
      Forall (fun z => 0 <= z < 256)%Z buf5 /\ Forall (fun z => 0 <= z < 256)%Z post /\
      rw_cells usegs m5 EB [CB 256 ej] /\
      rw_cells usegs m5 (D + 4) [CB (length bsr) bsr] /\
      AIREST_F m5 stG c (pF buf5).
  Section Sz9.
  Variables io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs : ltac2:(SecDiet.SzSec.tyM 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv" @io).
  Lemma loop_facts__body : ltac2:(SecDiet.SzSec.bodyP 'loop_facts__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 LENB LJS LO OFG P14 RSP SFL SPW SZ U1 U2. pin_using (fun (APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 LENB LJS LO OFG P14 RSP SFL SPW SZ U1 U2 : unit) => tt).
 intros IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI5 MU WM HOPT5 CC5 Hccs buf5 bs5.
    destruct IV as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & AL4).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (LBS : (length pre + (4 + length bsr))%nat = Z.to_nat (pc_bufalloc p)).
    { destruct BUF3 as [[WF _] _]. cbn [cells_wf cell_wf] in WF. rewrite !length_app, !length_map in WF. cbn [length] in WF. lia. }
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length (pre ++ u0 :: u1 :: u2 :: u3 :: post)))%Z) by lia.
    rewrite length_app in LEN4. cbn [length] in LEN4.
    apply Forall_app in GR3 as [GRpre GB].
    pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as GRpost.
    cbv beta in B0, B1, B2, B3. clear GB.
    pose proof (head_apart K _ _ _ _ _ _ _ G3 HinB) as APIB. pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIB, APIP. unfold PCAP_NG_SF_TOTAL in APIP.
    pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
    assert (AGS35 : agrees_on (fun a => outside [(CUR, CUR + 16); (D, D + 4)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unfold ai_FRAME in FR3.
    transport HD3 m5 AGS35 ltac:(prs). transport FR3 m5 AGS35 ltac:(prs). transport NG3 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' js pad1 hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU P14 APB CUR1 G3 Lpre HDd LBS; prs)).
    transport AR1 m5 AGS35 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; (keep_hyps CEILV hptr sp R CUR lo idb_off p s c I' js hd c' pre post u0 u1 u2 u3 bsr ccs LJS; lia)); rewrite length_rev in Ha; cbn [outside]; (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' js hd c' pre post u0 u1 u2 u3 bsr m3 D ccs a LO BU CUR1 IC1 IC2 G3 Lpre HDd LBS Q4 APIB Ha; lia)).
    transport SL3 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' SA js sj hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU CUR1 IC1 IC2 HSA G3 Lpre HDd LBS Q4 APIB; prs)). transport AR2 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR lo idb_off p s c stG sg q1 I' SA js tail3 hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU CUR1 IC1 HSA G3 Lpre HDd LBS Q4 APIB; prs)). transport HEB3 m5 AGS35 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s c ej stG sg q1 I' js hd c' pre post u0 u1 u2 u3 bsr m3 D ccs LO BU P14 B14 APB CUR1 EBX G3 Lpre HDd LBS; prs)).
    assert (G5 : GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m5).
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo in *; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. unfold iv_in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    assert (ST5 : stk usegs m5 lo (bv_unsigned sp + -112)) by (eapply stk_transport_disjoint; [exact ST3 | exact MU | exact WM | cbn [disjoint_from]; unfold rc_lo in *; lia]).
    assert (AG5 : AGP m5).
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS35|]. intros a (_ & _ & Hc & _ & Hb); cbn [outside]. split; [(keep_hyps CEILV hptr R B CUR p s I' js hd c' pre post u0 u1 u2 u3 bsr ccs a Hc; lia)|]. split; [(keep_hyps CEILV hptr sp R B CUR lo idb_off p s c I' js hd c' pre post u0 u1 u2 u3 bsr D ccs a Lpre HDd LBS Hb; lia)| exact Logic.I]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_recell _ _ _ [CB (length pre) (map b8 pre); CB 4 [b8 u0; b8 u1; b8 u2; b8 u3]; CB (length bsr) bsr] BUF3
                  ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity)) as BX.
    destruct (rw_cells_cut _ _ _ 1 BX) as [HB1 BX2]. destruct (rw_cells_cut _ _ _ 1 BX2) as [_ HB2]. clear BX BX2. cbn [firstn skipn cells_size csize Nat.add] in HB1, HB2.
    lazymatch type of HB2 with rw_cells _ _ ?A _ => replace A with (D + 4)%Z in HB2 by lia end.
    transport HB1 m5 AGS35 ltac:(prs). transport HB2 m5 AGS35 ltac:(prs).
    pose proof (rw_cells_uncut _ _ _ _ _ HB1 HOPT5 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 HB2 ltac:(cbn [cells_size csize Nat.add app]; lia)) as J2. clear J1.
    assert (BUF5 : rw_cells usegs m5 B [CB (Z.to_nat (pc_bufalloc p)) bs5]).
    { eapply rw_cells_recell; [exact J2 | cbn; subst bs5; rewrite !length_app, !length_map; cbn [length]; lia |].
      subst bs5. cbn [cells_bytes cbytes app]. rewrite !le2_lit by lia. rewrite !app_nil_r. cbn [app]. reflexivity. }
    clear J2.
    assert (PFX5 : firstn (length buf5) bs5 = map b8 buf5) by (subst buf5 bs5; exact (pfx_comp pre [c0; c1; l0; l1] post bsr PFXr)).
    assert (LB5 : length buf5 = length (pc_bufdata p)) by (rewrite <- LB3; subst buf5; rewrite !length_app; reflexivity).
    assert (GR5 : Forall (fun z => 0 <= z < 256)%Z buf5) by (subst buf5; apply Forall_app; split; [exact GRpre|]; repeat (constructor; [lia|]); exact GRpost).
    split; [exact ST5|]. split; [exact AG5|]. split; [exact HD3|]. split; [exact FR3|]. split; [exact NG3|]. split; [exact AR1|]. split; [exact SL3|]. split; [exact AR2|].
    split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|]. split; [exact LB5|]. split; [exact GR5|]. split; [exact GRpost|]. split; [exact HEB3|]. split; [exact HB2|].
    eapply loop_restf; [exact G5 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | exact Hccs].
  Qed.
  End Sz9.
  Lemma loop_facts : ltac:(let t := eval cbv delta [loop_facts__stmt] in loop_facts__stmt in exact t).
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 LENB LJS LO OFG P14 RSP SFL SPW SZ U1 U2. intros io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D ccs. ltac2:(SecDiet.SzSec.closeP 'loop_facts__body "vvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_disp__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (io : idbopts) (c' : cursor) (sw : bool) (pre post : list Z) (c0 c1 l0 l1 : Z) (bsr cpad3 : list byte) (m5 : mem) (D : Z),
      let code := (c0 + 256 * c1)%Z in let olen := (l0 + 256 * l1)%Z in let padded := ((olen + 3) / 4 * 4)%Z in
      let buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post in let bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr in
      let c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c') in
      (forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3) ->
      (0 < io_tsresol io < 2^64)%Z -> pc_swapped p = sw ->
      (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (4 <= cur_remaining c')%Z -> (padded <= cur_remaining c' - 4)%Z ->
      (8 <= cur_off c')%Z -> (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z ->
      D = (B + cur_off c')%Z -> Z.of_nat (length pre) = cur_off c' ->
      firstn (length post) bsr = map b8 post ->
      (0 <= c0 < 256)%Z -> (0 <= c1 < 256)%Z -> (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z ->
      Forall (fun z => 0 <= z < 256)%Z post ->
      rw_cells usegs m5 (D + 4) [CB (length bsr) bsr] ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1) (pio_body fuel sw io code olen (cur_off c' + 4) c2 buf5)) stG)
        (MS (mkR (Z_to_bv 64 (D + 4 + padded)) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.b2z (io_is_binary io))) (Z_to_bv 64 19) (Z_to_bv 64 EB) (Z_to_bv 64 (P + 648))
                 (Z_to_bv 64 P) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 CUR) (Z_to_bv 64 olen)
                 (Z_to_bv 64 SA) (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 9)
                 (Z_to_bv 64 65280) (Z_to_bv 64 16711680) (Z_to_bv 64 (io_tsoffset io))
                 (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (cur_remaining c' - 4 - padded))
                 (Z_to_bv 64 (D + 4)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 code) (Z_to_bv 64 padded)
                 (Z_to_bv 64 10) (Z_to_bv 64 63) (Z_to_bv 64 14) (Z_to_bv 64 8))
            F (Z_to_bv 64 0x1773c) fc None m5 (seg_rom usegs)).
  Section Sz10.
  Variables fuel io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D : ltac2:(SecDiet.SzSec.tyM 'ai_disp__stmt "vhvvvvvvvvvvvvv" @fuel).
  Lemma ai_disp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_disp__stmt "vhvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt).
    intros LK.
 intros code olen padded buf5 bs5 c2 AIM5 TSR SW FUEL GE4 FIT OFF0 LEN4 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2.
    assert (R2 : cur_remaining c2 = (cur_remaining c' - 4 - padded)%Z) by reflexivity.
    assert (FUEL2 : (cur_remaining c2 / 4 < Z.of_nat fuel)%Z) by (rewrite R2; clear - FUEL FIT HL0 HL1; subst padded olen; Z.div_mod_to_equations; lia).
    pose proof (AIM5 io TSR) as IV5.
    destruct IV5 as (_ & MI5 & ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5 & GR5 & CC5 & CR1 & CR2 & CR3 & CR4 & HEB5 & AL5).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel pre c0 c1 l0 l1 q q3 r q0 r0 H0 H1 H5 H6; lia)).
    assert (Lpost : (cur_remaining c' - 4 <= Z.of_nat (length post))%Z) by (subst buf5; rewrite length_app in LEN4; cbn [length] in LEN4; lia).
    assert (RESTF5 : AIREST_F m5 stG c (pF buf5)).
    { eapply loop_restf; [exact G5 | exact NG5 | exact AR15 | exact SL5 | exact AR25 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | reflexivity]. }
    (* [comment removed for export] *)
    pose proof (ai_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU SPM TP ALN RSP SPW HinP P14 B14 APB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND EBX CLB CRE EBiv) as SNP.
    pose proof (ai_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej
                  G LO BU SPM RSP SPW HinP P14 B14 APB P5 UTS WMB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND CBT EBX EB64 CRE EBiv) as MCP.
    pose proof (ai_tail K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU RSP SPW HinP HinB P14 APB UTS IFW LENB CUR1 CUR8 IDB0 COFF CREM CEND EBX CLB) as TAIL.
    unfold pio_body.
    (* [comment removed for export] *)
    step.
    destruct (Z.eq_dec code 9) as [E9|NE9].
    { (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ E9). cbv iota.
      replace (code =? OPT_ENDOFOPT) with false by (rewrite E9; reflexivity). replace (code =? IF_TSRESOL) with true by (rewrite E9; reflexivity). cbv iota.
      step.
      destruct (Z.eq_dec olen 1) as [L1|L1].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 1) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1 HOLEN L1; lia). cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 1) L1). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_FMT_TSRESOL_LEN "Interface Description Block has if_tsresol option with length %u != 1"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_TSRESOL_LEN; lia| unfold AI_FMT_TSRESOL_LEN; cbn; lia]).
        eapply SNP with (m3:=m5) (args:=[AInt olen]) (hd:=hd);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
      rewrite (eqb_lits_eq _ _ L1). cbv iota. rewrite (proj2 (Z.eqb_eq olen 1) L1). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      step.
      destruct (io_saw_tsresol io) eqn:SAWR.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 step.
        assert (MSG : fmt_at m5 AI_STR_TSRESOL_DUP "Interface Description Block has more than one if_tsresol option"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_STR_TSRESOL_DUP; lia| unfold AI_STR_TSRESOL_DUP; cbn; lia]).
        eapply MCP with (m3:=m5) (hd:=hd) (str:="Interface Description Block has more than one if_tsresol option"%string);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | cbn; (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | vm_compute; reflexivity | msg_ok | exact RESTF5 ]. }
      cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v post']; [exfalso; cbn [length] in Lpost; lia|].
      destruct bsr as [|bv0 bsr']; [cbn in PFXr; discriminate|]. cbn [firstn length map] in PFXr. injection PFXr as Ebv0 PFXr'. subst bv0.
      pose proof (Forall_inv GRpost) as Bv. cbv beta in Bv.
      assert (GU : get_u8 buf5 (cur_off c' + 4) = v).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply get_u8_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 1 [b8 v]; CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV1 _]. clear HV. cbn [firstn] in HV1.
      step. change (b8 v) with (Z_to_bv 8 v). rewrite (sxb_lit v) by lia.
      rewrite (land_128 v) by lia.
      destruct (Z.lt_ge_cases v 128) as [VLO|VHI].
      + (* [comment removed for export] *)
        rewrite (Z.div_small v 128) by lia. replace (128 * 0 =? 0)%Z with true by reflexivity. cbv beta iota delta [negb]. replace (v - 256 * 0)%Z with v by lia.
        step. rewrite (unsigned_lit v), land_255_mod, (Z.mod_small v 256) by lia.
        step. if_tf' false.
        step.
        destruct (Z.lt_ge_cases v 20) as [V20|V20].
        2:{ (* [comment removed for export] *)
          if_tf' true. rewrite (proj2 (Z.ltb_lt 19 v)) by lia. cbv iota. rewrite ai_result_inl.
          do 4 step.
          assert (MSG : fmt_at m5 AI_FMT_DEC_HIGH "Interface Description Block if_tsresol option resolution 10^-%u is too high"%string)
            by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_DEC_HIGH; lia| unfold AI_FMT_DEC_HIGH; cbn; lia]).
          eapply SNP with (m3:=m5) (args:=[AInt v]) (hd:=hd);
            [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_dec_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
        if_tf' false. rewrite (proj2 (Z.ltb_ge 19 v)) by lia. cbv iota.
        assert (P19 : (0 < 10 ^ v <= 10 ^ 19)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (10 ^ 19)%Z with 10000000000000000000%Z in P19.
        step.
        destruct (Z.eq_dec v 0) as [V0|V0].
        * (* [comment removed for export] *)
          if_tf' true. rewrite V0. change (10 ^ 0)%Z with 1%Z.
          do 4 step.
          rewrite <- SW; eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
        * if_tf' false. step. step.
          eapply evt_cut; [eapply (pow10_block (Z.to_nat v - 1) v 1); (keep_hyps CEILV hptr sp R CUR lo idb_off p s c js hd fuel c' pre c0 c1 l0 l1 v post' Bv V0 V20 P19; lia) |].
          cbv beta. intros ms' ->. rewrite Z.mul_1_l.
          rewrite <- SW; eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + (* [comment removed for export] *)
        replace (v / 128)%Z with 1%Z by (Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel pre c0 c1 l0 l1 v post' q2 q r Bv VHI H0 H1; lia)). replace (128 * 1 =? 0)%Z with false by reflexivity. cbv beta iota delta [negb].
        rewrite (land_127_hi v) by lia. replace (v - 256 * 1)%Z with (v - 256)%Z by lia.
        step. rewrite (unsigned_lit_wrap (v - 256)), land_255_mod. replace (((v - 256) mod 2 ^ 64) mod 256)%Z with v by (Z.div_mod_to_equations; (keep_hyps CEILV hptr R p s js hd fuel pre c0 c1 l0 l1 v post' q2 q r r2 q3 Bv H0 H1 H15; lia)).
        step. if_tf' true.
        step. rewrite (unsigned_lit v), (land_127_hi v) by lia.
        step.
        destruct (Z.lt_ge_cases 63 (v - 128)) as [V63|V63].
        { (* [comment removed for export] *)
          if_tf' true. rewrite (proj2 (Z.ltb_lt 63 (v - 128))) by lia. cbv iota. rewrite ai_result_inl.
          do 3 step.
          assert (MSG : fmt_at m5 AI_FMT_BIN_HIGH "Interface Description Block if_tsresol option resolution 2^-%u is too high"%string)
            by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_BIN_HIGH; lia| unfold AI_FMT_BIN_HIGH; cbn; lia]).
          eapply SNP with (m3:=m5) (args:=[AInt (v - 128)]) (hd:=hd);
            [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_bin_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
        if_tf' false. rewrite (proj2 (Z.ltb_ge 63 (v - 128))) by lia. cbv iota.
        assert (P63 : (0 < 2 ^ (v - 128) <= 2 ^ 63)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (2 ^ 63)%Z with 9223372036854775808%Z in P63.
        step. step. rewrite (unsigned_lit (v - 128)), (Z.mod_small (v - 128) 64), Z.shiftl_1_l by lia.
        step. step.
        rewrite <- SW; eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 9) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1 HCODE NE9; lia). cbv iota.
    replace (code =? IF_TSRESOL) with false by (symmetry; apply Z.eqb_neq; exact NE9).
    step.
    destruct (Z.eq_dec code 14) as [E14|NE14].
    { (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ E14). cbv beta iota delta [negb].
      replace (code =? OPT_ENDOFOPT) with false by (rewrite E14; reflexivity). replace (code =? IF_TSOFFSET) with true by (rewrite E14; reflexivity). cbv iota.
      step.
      destruct (Z.eq_dec olen 8) as [L8|L8].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 8) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1 HOLEN L8; lia). cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 8) L8). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_FMT_TSOFF_LEN "Interface Description Block has if_tsoffset option with length %u != 8"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_TSOFF_LEN; lia| unfold AI_FMT_TSOFF_LEN; cbn; lia]).
        eapply SNP with (m3:=m5) (args:=[AInt olen]) (hd:=hd);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsoffset_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ]. }
      rewrite (eqb_lits_eq _ _ L8). cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_eq olen 8) L8). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      step.
      destruct (io_saw_tsoffset io) eqn:SAWO.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_STR_TSOFF_DUP "Interface Description Block has more than one if_tsoffset option"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_STR_TSOFF_DUP; lia| unfold AI_STR_TSOFF_DUP; cbn; lia]).
        eapply MCP with (m3:=m5) (hd:=hd) (str:="Interface Description Block has more than one if_tsoffset option"%string);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | cbn; (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1; lia) | vm_compute; reflexivity | msg_ok | exact RESTF5 ]. }
      cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post']]]]]]]]; try (exfalso; cbn [length] in Lpost; (keep_hyps CEILV hptr sp R CUR lo idb_off p s c js hd fuel c' pre c0 c1 l0 l1 R2 CR1 Lpost L8; lia)).
      destruct bsr as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bsr']]]]]]]]; try (cbn in PFXr; discriminate).
      cbn [firstn length map] in PFXr. injection PFXr as E0 E1 E2 E3 E4 E5 E6 E7 PFXr'. subst b0 b1 b2 b3 b4 b5 b6 b7.
      assert (Bv : forall x, In x [v0; v1; v2; v3; v4; v5; v6; v7] -> (0 <= x < 256)%Z).
      { intros x Hx. apply (proj1 (Forall_forall _ _) GRpost). cbn in Hx |- *. clear - Hx. tauto. }
      pose proof (Bv v0 ltac:(cbn; clear; tauto)) as Bv0. pose proof (Bv v1 ltac:(cbn; clear; tauto)) as Bv1. pose proof (Bv v2 ltac:(cbn; clear; tauto)) as Bv2. pose proof (Bv v3 ltac:(cbn; clear; tauto)) as Bv3.
      pose proof (Bv v4 ltac:(cbn; clear; tauto)) as Bv4. pose proof (Bv v5 ltac:(cbn; clear; tauto)) as Bv5. pose proof (Bv v6 ltac:(cbn; clear; tauto)) as Bv6. pose proof (Bv v7 ltac:(cbn; clear; tauto)) as Bv7. clear Bv.
      assert (GU : get_le64 buf5 (cur_off c' + 4) = le8val v0 v1 v2 v3 v4 v5 v6 v7).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply get_le64_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 8 (map b8 [v0; v1; v2; v3; v4; v5; v6; v7]); CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV8 _]. clear HV. cbn [firstn] in HV8.
      eapply evt_cut.
      { eapply ldu64_block with (A := (D + 4)%Z); [exact MI5 | lia | lia | exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7 | reflexivity | exact HV8]. }
      cbv beta. intros ms' (a3x & s8x' & s10x & s11x & ->).
      (* [comment removed for export] *)
      step.
      destruct sw.
      + cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb].
        eapply evt_cut.
        { eapply bswap64_block; [exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7]. }
        cbv beta. intros ms' (a3y & s8y & s9y & s10y & ->).
        rewrite (bswap64_bytes v0 v1 v2 v3 v4 v5 v6 v7) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre c0 c1 l0 l1 v0 v1 v2 v3 v4 v5 v6 v7 post' Bv0 Bv1 Bv2 Bv3 Bv4 Bv5 Bv6 Bv7; lia). rewrite <- (Z_to_bv64_s64 (le8val v7 v6 v5 v4 v3 v2 v1 v0)).
        replace (process_idb_options_loop fuel true) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
        rewrite <- (Z_to_bv64_s64 (le8val v0 v1 v2 v3 v4 v5 v6 v7)).
        replace (process_idb_options_loop fuel false) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 14) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1 HCODE NE14; lia). cbv beta iota delta [negb].
    replace (code =? IF_TSOFFSET) with false by (symmetry; apply Z.eqb_neq; exact NE14).
    step.
    destruct (Z.eq_dec code 0) as [E0|NE0].
    + rewrite (eqb_lits_eq _ _ E0). cbv iota. replace (code =? OPT_ENDOFOPT) with true by (rewrite E0; reflexivity). cbv iota.
      (* [comment removed for export] *)
      step.
      destruct (Z.eq_dec olen 0) as [L0|L0].
      * rewrite (eqb_lits_eq olen 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_eq olen 0) L0). cbv beta iota delta [negb].
        eapply TAIL with (m3:=m5) (hd:=hd) (c':=c2) (opts:=io);
          [ exact U1 | exact U2 | exact U5 | exact IC1 | exact IC2 | exact SZ | exact LJS | exact HSA | exact SNR | exact TSR
          | exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact NG5 | exact AR15 | exact SL5 | exact AR25 | exact G5
          | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | exact CR1 | exact CR2 | exact CR3 | exact CR4 | exact HEB5 | exact OFG ].
      * rewrite (eqb_lits_false olen 0) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1 HOLEN L0; lia). cbv iota. rewrite (proj2 (Z.eqb_neq olen 0) L0). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 step.
        assert (MSG : fmt_at m5 AI_FMT_ENDOFOPT "Interface Description Block has opt_endofopt option with length %u != 0"%string)
          by (apply (fmt_at_intro m5 _ _ MI5); [vm_compute; reflexivity| unfold AI_FMT_ENDOFOPT; lia| unfold AI_FMT_ENDOFOPT; cbn; lia]).
        eapply SNP with (m3:=m5) (args:=[AInt olen]) (hd:=hd);
          [ exact MI5 | exact ST5 | exact AG5 | exact HD5 | exact Hhd | exact FR5 | exact HEB5 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.endofopt_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | exact RESTF5 ].
    + (* [comment removed for export] *)
      rewrite (eqb_lits_false code 0) by (keep_hyps CEILV hptr sp R CUR p s js hd fuel c' pre post c0 c1 l0 l1 HCODE NE0; lia). cbv iota. replace (code =? OPT_ENDOFOPT) with false by (symmetry; apply Z.eqb_neq; exact NE0). cbv iota.
      replace (process_idb_options_loop fuel sw) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
      eapply LK; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply AIM5; exact TSR | exact FUEL2].
  Qed.
  End Sz10.
  Lemma ai_disp : ltac:(let t := eval cbv delta [ai_disp__stmt] in ai_disp__stmt in exact t).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. intros fuel LK io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D. ltac2:(SecDiet.SzSec.closeP 'ai_disp__body "vhvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_body__stmt : Prop := forall fuel, LOOPK fuel ->
    forall (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte)
           (sw : bool) (pre post : list Z) (u0 u1 u2 u3 : Z) (bsr : list byte) (m4 : mem) (rax : word),
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (4 <= cur_remaining c')%Z ->
      pc_swapped p = sw ->
      buf' = pre ++ u0 :: u1 :: u2 :: u3 :: post -> Z.of_nat (length pre) = cur_off c' ->
      bs3 = map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr -> firstn (length post) bsr = map b8 post ->
      let c0 := (if sw then u1 else u0) in let c1 := (if sw then u0 else u1) in
      let l0 := (if sw then u3 else u2) in let l1 := (if sw then u2 else u3) in
      let code := (c0 + 256 * c1)%Z in let olen := (l0 + 256 * l1)%Z in let padded := ((olen + 3) / 4 * 4)%Z in
      (padded <= cur_remaining c' - 4)%Z ->
      mem_inv usegs m4 ->
      munch [(CUR, CUR + 16); (B + cur_off c', B + cur_off c' + 4)]%Z m3 m4 -> wmono usegs m3 m4 ->
      rw_cells usegs m4 CUR [C8 (Z_to_bv 64 (B + cur_off c' + 4)); C8 (Z_to_bv 64 (cur_remaining c' - 4)); C4 (Z_to_bv 64 (cur_block_type c')); CB 4 cpad3] ->
      rw_cells usegs m4 (B + cur_off c') [Cells.C2 (Z_to_bv 64 code); Cells.C2 (Z_to_bv 64 olen)] ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1)
                   (pio_value fuel sw io code olen (mkCursor (cur_off c' + 4) (cur_remaining c' - 4) (cur_block_type c')) (pre ++ c0 :: c1 :: l0 :: l1 :: post))) stG)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.b2z (io_is_binary io))) (Z_to_bv 64 19) (Z_to_bv 64 EB) (Z_to_bv 64 (P + 648))
                 (Z_to_bv 64 P) (Z_to_bv 64 (io_tsresol io)) (Z_to_bv 64 CUR) (Z_to_bv 64 olen)
                 (Z_to_bv 64 SA) (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 9)
                 (Z_to_bv 64 65280) (Z_to_bv 64 16711680) (Z_to_bv 64 (io_tsoffset io))
                 (Z_to_bv 64 (Z.b2z (io_saw_tsoffset io))) (Z_to_bv 64 (Z.b2z (io_saw_tsresol io))) (Z_to_bv 64 (cur_remaining c' - 4))
                 (Z_to_bv 64 (B + cur_off c' + 4)) (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 (B + cur_off c')) (Z_to_bv 64 padded)
                 (Z_to_bv 64 10) (Z_to_bv 64 63) (Z_to_bv 64 14) (Z_to_bv 64 8))
            F (Z_to_bv 64 0x17728) fc None m4 (seg_rom usegs)).
  Section Sz11.
  Variables fuel io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 rax : ltac2:(SecDiet.SzSec.tyM 'ai_body__stmt "vhvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_body__body : ltac2:(SecDiet.SzSec.bodyP 'ai_body__stmt "vhvvvvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt).
    intros LK.
 intros IV FUEL GE4 SW Ebuf Lpre Ebs PFXr c0 c1 l0 l1 code olen padded FIT MI4 MU WM CC4 HOPT4.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & AL4).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
    assert (OFF0 : (8 <= cur_off c')%Z) by lia.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
    assert (Lpost : (Z.of_nat (length post) = Z.of_nat (length buf') - cur_off c' - 4)%Z) by (subst buf'; rewrite length_app in *; cbn [length] in *; lia).
    (* [comment removed for export] *)
    assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z /\ Forall (fun z => 0 <= z < 256)%Z pre /\ Forall (fun z => 0 <= z < 256)%Z post).
    { subst buf'. apply Forall_app in GR3 as [GA GB]. inversion GB as [|x0 l0' B0 GB1]; subst. inversion GB1 as [|x1 l1' B1 GB2]; subst.
      inversion GB2 as [|x2 l2' B2 GB3]; subst. inversion GB3 as [|x3 l3' B3 GB4]; subst. repeat split; try assumption; (keep_hyps CEILV hptr sp R CUR p s I' js hd fuel c' pre post u0 u1 u2 u3 bsr B0 B1 B2 B3; lia). }
    destruct GRh as ((B0 & B1 & B2 & B3) & GRpre & GRpost).
    assert (HC : (0 <= c0 < 256 /\ 0 <= c1 < 256 /\ 0 <= l0 < 256 /\ 0 <= l1 < 256)%Z) by (subst c0 c1 l0 l1; destruct sw; lia).
    destruct HC as (HC0 & HC1 & HL0 & HL1).
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; (keep_hyps CEILV hptr R idb_off p s c js hd fuel c' buf' bs3 sw pre post u0 u1 u2 u3 q2 q r q0 r0 H0 H1 H5 H6; lia)).
    set (buf5 := pre ++ c0 :: c1 :: l0 :: l1 :: post) in *.
    assert (LB5 : length buf5 = length buf') by (subst buf5 buf'; rewrite !length_app; reflexivity).
    assert (GR5 : Forall (fun z => 0 <= z < 256)%Z buf5) by (subst buf5; apply Forall_app; split; [exact GRpre|]; repeat (constructor; [lia|]); exact GRpost).
    (* [comment removed for export] *)
    remember (B + cur_off c')%Z as D eqn:HDd.
    step. rewrite (zx16_lit code) by lia.
    step. step. rewrite (unsigned_lit (cur_remaining c' - 4)), (unsigned_lit padded) by lia.
    pose proof (munch_refl [(CUR, CUR + 16)]%Z m4) as MU45. pose proof (wmono_refl usegs m4) as WM45.
    hide HOPT4.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end. rename CC4 into CC5. rename MI4 into MI5.
    unhide HOPT4.
    (* [comment removed for export] *)
    assert (AGS45 : agrees_on (fun a => outside [(CUR, CUR + 16)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU45 | exact WM45 | intros a _ Ho; exact Ho]).
    transport HOPT4 m5 AGS45 ltac:(prs). rename HOPT4 into HOPT5.
    subst bs3. subst buf'.
    destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m5 c0 c1 l0 l1 D _ IV GE4 Lpre HDd PFXr HC0 HC1 HL0 HL1 MI5 MU WM ltac:(subst code olen; exact HOPT5) CC5 eq_refl)
      as (ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5' & GR5' & _ & HEB5 & HB2 & RESTF5).
    set (bs5 := map b8 pre ++ [b8 c0; b8 c1; b8 l0; b8 l1] ++ bsr) in *.
    set (c2 := mkCursor (cur_off c' + 4 + padded) (cur_remaining c' - 4 - padded) (cur_block_type c')).
    assert (AIM5 : forall io', (0 < io_tsresol io' < 2^64)%Z -> AIM io' c2 buf5 m5 bs5 cpad3).
    { intros io' TS'. split; [exact TS'|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact AG5|]. split; [exact HD5|]. split; [exact FR5|].
      split; [exact NG5|]. split; [exact AR15|]. split; [exact SL5|]. split; [exact AR25|]. split; [exact G5|]. split; [exact BUF5|]. split; [exact PFX5|].
      split; [exact LB5'|]. split; [exact GR5'|]. split; [unfold cursor_cells; subst c2 D; cbn [cur_off cur_remaining cur_block_type]; replace (B + cur_off c' + 4 + padded)%Z with (B + (cur_off c' + 4 + padded))%Z in CC5 by lia; exact CC5|].
      subst c2; cbn [cur_off cur_remaining cur_block_type]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CR4|]. split; [exact HEB5|].
      apply mod4_advance; [exact AL4| clear - HPAD; lia]. }
    (* [comment removed for export] *)
    unfold pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    fold padded. rewrite (proj2 (Z.ltb_ge (cur_remaining c' - 4) padded)) by lia. cbv beta iota. fold c2.
    assert (LEN5 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf5))%Z) by (rewrite LB5; exact LEN4).
    apply (ai_disp fuel LK io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D AIM5 TSR SW FUEL GE4 FIT OFF0 LEN5 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2).
  Qed.
  End Sz11.
  Lemma ai_body : ltac:(let t := eval cbv delta [ai_body__stmt] in ai_body__stmt in exact t).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. intros fuel LK io c' buf' m3 bs3 cpad3 sw pre post u0 u1 u2 u3 bsr m4 rax. ltac2:(SecDiet.SzSec.closeP 'ai_body__body "vhvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_iter__stmt : Prop := forall fuel, LOOPK fuel -> ITERK fuel.
  Section Sz12.
  Variables fuel ra' a3' s8' s9' s10' s11' io c' buf' m3 bs3 cpad3 : ltac2:(SecDiet.SzSec.tyM 'ai_iter__stmt "vhvvvvvvvvvvvv" @fuel).
  Lemma ai_iter__body : ltac2:(SecDiet.SzSec.bodyP 'ai_iter__stmt "vhvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt).
    intros LK.
 intros IV FUEL RPOS.
    pose proof IV as IV'. destruct IV' as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & AL4).
    pose proof (ai_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU SPM TP ALN RSP SPW HinP P14 B14 APB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND EBX CLB CRE EBiv) as SNP.
    pose proof HPV as HPV3. transport HPV3 m3 AG3 ltac:(unfold ai_AGP, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s stG sg q1 I' js hd fuel c' buf' m3 LO BU P14 APB CUR1 EBX INPc G3; prs)).
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (LBS : length bs3 = Z.to_nat (pc_bufalloc p)) by (destruct BUF3 as [[WF _] _]; cbn in WF; lia).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(right; apply in_or_app; left; exact HinB)) as (_ & B16 & _).
    cbn [cb_addr cb_size fst snd] in B16.
    unfold cursor_cells in CC3.
    assert (REM64 : (cur_remaining c' < 2^32)%Z) by lia.
    rewrite pio_unfold. unfold pio_iter. rewrite (proj2 (Z.eqb_neq (cur_remaining c') 0)) by lia.
    unfold get_opthdr_from_block_data, get_from_block_data.
    hide HD3. hide FR3. hide NG3. hide AR1. hide SL3. hide AR2. hide BUF3. hide HEB3. hide HPV3.
    unfold LREGS. step.
    destruct (Z.lt_ge_cases (cur_remaining c') 4) as [LT4|GE4].
    { (* [comment removed for export] *)
      replace (bv_ltu (Z_to_bv 64 (cur_remaining c')) (Z_to_bv 64 4)) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].
      rewrite (proj2 (Z.ltb_lt (cur_remaining c') 4) LT4). rewrite ai_result_inl.
      step. rewrite (sx32_s32 (cur_block_type c')) by lia. do 4 step.
      unhide HD3. unhide FR3. unhide NG3. unhide AR1. unhide SL3. unhide AR2. unhide BUF3. unhide HEB3.
      assert (MSG : fmt_at m3 AI_FMT_TOOSHORT "block of type %u in pcapng dump file is too short"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold AI_FMT_TOOSHORT; lia| unfold AI_FMT_TOOSHORT; cbn; lia]).
      eapply SNP with (m3:=m3) (args:=[AInt (s32 (cur_block_type c'))]) (hd:=hd);
        [ exact MI3 | exact ST3 | exact AG3 | exact HD3 | exact Hhd | exact FR3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
        | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
        | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
          replace (convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
          apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
        | vm_compute; reflexivity | apply args_ok_ints1
        | eapply loop_restf; [exact G3 | exact NG3 | exact AR1 | exact SL3 | exact AR2 | exact BUF3 | exact PFX3 | exact LB3 | exact GR3 | exact CC3 | reflexivity] ]. }
    (* [comment removed for export] *)
    replace (bv_ltu (Z_to_bv 64 (cur_remaining c')) (Z_to_bv 64 4)) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_ge (cur_remaining c') 4) GE4). cbv beta iota.
    assert (OFF0 : (8 <= cur_off c')%Z) by lia.
    assert (LEN4 : (cur_off c' + cur_remaining c' <= Z.of_nat (length buf'))%Z) by lia.
    destruct (split_at4 buf' (Z.to_nat (cur_off c')) ltac:(lia)) as (pre & u0 & u1 & u2 & u3 & post & Ebuf & Lpre).
    assert (LpreZ : Z.of_nat (length pre) = cur_off c') by lia. clear Lpre.
    subst buf'.
    destruct (pfx_decomp pre [u0; u1; u2; u3] post bs3 PFX3) as (bsr & Ebs & PFXr). cbn [map] in Ebs. subst bs3.
    assert (GRh : (0 <= u0 < 256 /\ 0 <= u1 < 256 /\ 0 <= u2 < 256 /\ 0 <= u3 < 256)%Z).
    { apply Forall_app in GR3 as [GA GB].
      pose proof (Forall_inv GB) as B0. pose proof (Forall_inv (Forall_inv_tail GB)) as B1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as B2.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as B3. cbv beta in B0, B1, B2, B3. lia. }
    destruct GRh as (B0 & B1 & B2 & B3).
    (* [comment removed for export] *)
    unhide BUF3.
    pose proof (rw_cells_recell _ _ _ [CB (length pre) (map b8 pre); Cells.C2 (Z_to_bv 64 (u0 + 256 * u1)); Cells.C2 (Z_to_bv 64 (u2 + 256 * u3)); CB (length bsr) bsr] BUF3
                  ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX.
    destruct (rw_cells_cut _ _ _ 1 BX) as [_ BX2]. destruct (rw_cells_cut _ _ _ 2 BX2) as [HOPT _]. clear BX BX2. cbn [firstn skipn cells_size csize Nat.add app] in HOPT.
    remember (B + cur_off c')%Z as D eqn:HDd.
    lazymatch type of HOPT with rw_cells _ _ ?A _ => replace A with D in HOPT by lia end.
    assert (D2 : (D mod 2 = 0)%Z) by (rewrite HDd; apply mod2_of_16_4; [exact B16| exact AL4]).
    assert (DR : (8 < D /\ D + cur_remaining c' <= CEILZ)%Z) by (rewrite HDd; clear - B14 OFF0 LEN4 LB3 LENB; lia).
    hide BUF3.
    (* [comment removed for export] *)
    pose proof (munch_refl [(CUR, CUR + 16); (D, D + 4)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof (munch_refl [(CUR, CUR + 16)]%Z m3) as MUc.
    hide HOPT.
    step. step.
    step. if_false_by (ltu_lits_false (D + 4) 5 ltac:(clear - DR; lia) ltac:(clear - DR CR1; lia)).
    unhide HPV3. step. rewrite (sx32_s32 (Z.b2z (pc_swapped p))) by (destruct (pc_swapped p); cbn; lia). rewrite (s32_small (Z.b2z (pc_swapped p))) by (destruct (pc_swapped p); cbn; lia).
    clear HPV3.
    step. replace (cur_remaining c' + -4)%Z with (cur_remaining c' - 4)%Z by lia.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4a end.
    assert (AGSc : agrees_on (fun a => outside [(CUR, CUR + 16)]%Z a) m3 m4a) by (eapply agrees_on_of_munch; [exact MUc | exact WM | intros a _ Ho; exact Ho]).
    unhide HOPT. transport HOPT m4a AGSc ltac:(prs).
    step.
    destruct (pc_swapped p) eqn:SW.
    - (* [comment removed for export] *)
      cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb].
      step. rewrite (and1_aligned D) by (clear - DR D2 CR1; lia). step. if_false.
      step. step. rewrite !zx16_lit by lia.
      step. step. step.
      match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
        replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (u1 + 256 * u0 + 65536 * u1)) by (f_equal; clear - B0 B1 B2 B3; norm_word; (keep_hyps u0 u1 B0; zlia)) end.
      step. step. step.
      match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
        replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (u3 + 256 * u2 + 65536 * u3)) by (f_equal; clear - B0 B1 B2 B3; norm_word; (keep_hyps u2 u3 B2; zlia)) end.
      (* [comment removed for export] *)
      pose proof (munch_refl [(D, D + 4)]%Z m4a) as MUd. pose proof (wmono_refl usegs m4a) as WMd.
      hide CC3. clear MUc AGSc.
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
      unhide CC3.
      assert (AGSd : agrees_on (fun a => outside [(D, D + 4)]%Z a) m4a m4) by (eapply agrees_on_of_munch; [exact MUd | exact WMd | intros a _ Ho; exact Ho]).
      transport CC3 m4 AGSd ltac:(prs). clear AGSd MUd WMd.
      pose proof (rw_cells_recell _ _ _ [Cells.C2 (Z_to_bv 64 (u1 + 256 * u0)); Cells.C2 (Z_to_bv 64 (u3 + 256 * u2))] HOPT ltac:(cbn; auto)
                    ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by (keep_hyps CEILV hptr sp R B CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr D B1 B0 B3 B2; lia);
                          rewrite (le2_of_val _ u1 u0 u1) by (try (keep_hyps CEILV hptr sp R B CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr D B1 B0; lia); rewrite unsigned_lit by (keep_hyps CEILV hptr sp R B CUR lo p s js hd fuel c' pre u0 u1 u2 u3 post bsr D B0 B1; lia); (keep_hyps CEILV hptr sp R B CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr D; lia)); rewrite (le2_of_val _ u3 u2 u3) by (try (keep_hyps CEILV hptr sp R B CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr D B3 B2; lia); rewrite unsigned_lit by (keep_hyps CEILV hptr sp R B CUR lo p s js hd fuel c' pre u0 u1 u2 u3 post bsr D B2 B3; lia); (keep_hyps CEILV hptr sp R B CUR p s js hd fuel c' pre u0 u1 u2 u3 post bsr D; lia)); reflexivity)) as HOPT4.
      clear HOPT.
      hide CC3.
      (* [comment removed for export] *)
      step. step. rewrite !zx16_lit by lia.
      step. step. rewrite (unsigned_lit (u3 + 256 * u2 + 3)), land_m4w by lia.
      step.
      unhide CC3.
      destruct (Z.le_gt_cases ((u3 + 256 * u2 + 3) / 4 * 4) (cur_remaining c' - 4)) as [FIT|NOFIT].
      + if_tf' false.
        (* [comment removed for export] *)
        step. rewrite (unsigned_lit (D + 4)) by (clear - DR CR1; lia). rewrite (lxor_ones64 (D + 4)) by (clear - DR CR1; lia).
        step. if_false_by (ltu_lits_false (18446744073709551615 - (D + 4)) ((u3 + 256 * u2 + 3) / 4 * 4) ltac:(clear - DR CR1 FIT B2 B3; lia) ltac:(clear - DR CR1; lia)).
        assert (SWB : swap_field 2 (cur_off c' + 2) (swap_field 2 (cur_off c') (pre ++ u0 :: u1 :: u2 :: u3 :: post)) = pre ++ u1 :: u0 :: u3 :: u2 :: post) by (rewrite <- LpreZ, swap2_at, swap2_at2; reflexivity).
        assert (GL1 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c') = (u1 + 256 * u0)%Z) by (rewrite <- LpreZ; apply get_le16_at).
        assert (GL2 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c' + 2) = (u3 + 256 * u2)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite SWB, GL1, GL2. subst D.
        eapply (ai_body fuel LK io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 true pre post u0 u1 u2 u3 bsr m4);
          [exact IV | exact FUEL | exact GE4 | exact SW | reflexivity | exact LpreZ | reflexivity | exact PFXr | exact FIT | exact MI3 | exact MU | exact WM | exact CC3 | exact HOPT4].
      + (* [comment removed for export] *)
        if_tf' true.
        assert (SWB : swap_field 2 (cur_off c' + 2) (swap_field 2 (cur_off c') (pre ++ u0 :: u1 :: u2 :: u3 :: post)) = pre ++ u1 :: u0 :: u3 :: u2 :: post) by (rewrite <- LpreZ, swap2_at, swap2_at2; reflexivity).
        assert (GL2 : get_le16 (pre ++ u1 :: u0 :: u3 :: u2 :: post) (cur_off c' + 2) = (u3 + 256 * u2)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite SWB, GL2.
        unfold pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
        rewrite (proj2 (Z.ltb_lt (cur_remaining c' - 4) ((u3 + 256 * u2 + 3) / 4 * 4))) by lia. cbv beta iota.
        rewrite ai_result_inl.
        destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m4 u1 u0 u3 u2 D _ IV GE4 LpreZ HDd PFXr B1 B0 B3 B2 MI3 MU WM HOPT4 CC3 eq_refl)
          as (ST4 & AG4 & HD4 & FR4 & NG4 & AR14 & SL4 & AR24 & G4 & BUF4 & PFX4 & LB4 & GR4 & _ & HEB4 & _ & RESTF4).
        hide HD4. hide FR4. hide HEB4.
        step. rewrite (sx32_s32 (cur_block_type c')) by lia. do 4 step.
        unhide HD4. unhide FR4. unhide HEB4.
        assert (MSG : fmt_at m4 AI_FMT_TOOSHORT "block of type %u in pcapng dump file is too short"%string)
          by (apply (fmt_at_intro m4 _ _ MI3); [vm_compute; reflexivity| unfold AI_FMT_TOOSHORT; lia| unfold AI_FMT_TOOSHORT; cbn; lia]).
        eapply SNP with (m3:=m4) (args:=[AInt (s32 (cur_block_type c'))]) (hd:=hd);
          [ exact MI3 | exact ST4 | exact AG4 | exact HD4 | exact Hhd | exact FR4 | exact HEB4 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
          | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints1
          | exact RESTF4 ].
    - (* [comment removed for export] *)
      cbn [Z.b2z]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      clear MUc AGSc.
      step. rewrite (eqb_lits_false D 0) by (clear - DR CR1; lia). cbv iota.
      step. rewrite (and1_aligned D) by (clear - DR D2 CR1; lia). step. if_false.
      step. rewrite !zx16_lit by lia.
      step. step. rewrite (unsigned_lit (u2 + 256 * u3 + 3)), land_m4w by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
      step.
      destruct (Z.le_gt_cases ((u2 + 256 * u3 + 3) / 4 * 4) (cur_remaining c' - 4)) as [FIT|NOFIT].
      + if_tf' false.
        step. rewrite (unsigned_lit (D + 4)) by (clear - DR CR1; lia). rewrite (lxor_ones64 (D + 4)) by (clear - DR CR1; lia).
        step. if_false_by (ltu_lits_false (18446744073709551615 - (D + 4)) ((u2 + 256 * u3 + 3) / 4 * 4) ltac:(clear - DR CR1 FIT B2 B3; lia) ltac:(clear - DR CR1; lia)).
        assert (GL1 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c') = (u0 + 256 * u1)%Z) by (rewrite <- LpreZ; apply get_le16_at).
        assert (GL2 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c' + 2) = (u2 + 256 * u3)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite GL1, GL2. subst D.
        eapply (ai_body fuel LK io c' (pre ++ u0 :: u1 :: u2 :: u3 :: post) m3 (map b8 pre ++ [b8 u0; b8 u1; b8 u2; b8 u3] ++ bsr) cpad3 false pre post u0 u1 u2 u3 bsr m4);
          [exact IV | exact FUEL | exact GE4 | exact SW | reflexivity | exact LpreZ | reflexivity | exact PFXr | exact FIT | exact MI3 | exact MU | exact WM | exact CC3 | exact HOPT].
      + (* [comment removed for export] *)
        if_tf' true.
        assert (GL2 : get_le16 (pre ++ u0 :: u1 :: u2 :: u3 :: post) (cur_off c' + 2) = (u2 + 256 * u3)%Z) by (rewrite <- LpreZ; apply get_le16_at2).
        rewrite GL2.
        unfold pio_value, get_optvalue_from_block_data, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
        rewrite (proj2 (Z.ltb_lt (cur_remaining c' - 4) ((u2 + 256 * u3 + 3) / 4 * 4))) by lia. cbv beta iota.
        rewrite ai_result_inl.
        destruct (loop_facts io c' pre post u0 u1 u2 u3 bsr cpad3 m3 m4 u0 u1 u2 u3 D _ IV GE4 LpreZ HDd PFXr B0 B1 B2 B3 MI3 MU WM HOPT CC3 eq_refl)
          as (ST4 & AG4 & HD4 & FR4 & NG4 & AR14 & SL4 & AR24 & G4 & BUF4 & PFX4 & LB4 & GR4 & _ & HEB4 & _ & RESTF4).
        hide HD4. hide FR4. hide HEB4.
        step. rewrite (sx32_s32 (cur_block_type c')) by lia. do 4 step.
        unhide HD4. unhide FR4. unhide HEB4.
        assert (MSG : fmt_at m4 AI_FMT_TOOSHORT "block of type %u in pcapng dump file is too short"%string)
          by (apply (fmt_at_intro m4 _ _ MI3); [vm_compute; reflexivity| unfold AI_FMT_TOOSHORT; lia| unfold AI_FMT_TOOSHORT; cbn; lia]).
        eapply SNP with (m3:=m4) (args:=[AInt (s32 (cur_block_type c'))]) (hd:=hd);
          [ exact MI3 | exact ST4 | exact AG4 | exact HD4 | exact Hhd | exact FR4 | exact HEB4 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil]
          | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block of type %u in pcapng dump file is too short")) with [Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints1
          | exact RESTF4 ].
  Qed.
  End Sz12.
  Lemma ai_iter : ltac:(let t := eval cbv delta [ai_iter__stmt] in ai_iter__stmt in exact t).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. intros fuel LK ra' a3' s8' s9' s10' s11' io c' buf' m3 bs3 cpad3. ltac2:(SecDiet.SzSec.closeP 'ai_iter__body "vhvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Theorem ai_loop : forall fuel, LOOPK fuel.
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt). induction fuel as [|fuel IH]; [apply ai_loop0 | apply ai_loop_step, ai_iter, IH]. Qed.

  (* [comment removed for export] *)
  Theorem ai_enter : forall (ra' a3' xa1 xt1 xs7 xs5 xs6 s8' s9' s10' s11' xs4 : word) (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte) (fuel : nat),
      xa1 = Z_to_bv 64 (io_tsresol io) -> xt1 = Z_to_bv 64 (Z.b2z (io_is_binary io)) -> xs7 = Z_to_bv 64 (cur_remaining c') ->
      xs5 = Z_to_bv 64 (Z.b2z (io_saw_tsoffset io)) -> xs6 = Z_to_bv 64 (Z.b2z (io_saw_tsresol io)) -> xs4 = Z_to_bv 64 (io_tsoffset io) ->
      AIM io c' buf' m3 bs3 cpad3 -> (cur_remaining c' / 4 < Z.of_nat (S fuel))%Z -> (0 < cur_remaining c')%Z ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options_loop (S fuel) (pc_swapped p) io c' buf')) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 1) xt1 (Z_to_bv 64 19) (Z_to_bv 64 EB) (Z_to_bv 64 (P + 648))
                 (Z_to_bv 64 P) xa1 (Z_to_bv 64 CUR) a3' (Z_to_bv 64 SA) (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 9)
                 (Z_to_bv 64 65280) (Z_to_bv 64 16711680) xs4 xs5 xs6 xs7 s8' s9' s10' s11'
                 (Z_to_bv 64 10) (Z_to_bv 64 63) (Z_to_bv 64 14) (Z_to_bv 64 8)) F (Z_to_bv 64 0x176ac) fc None m3 (seg_rom usegs)).
  Proof using ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB. pin_using (fun (ALN APB B14 BU CBT CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HPV HSA Hhd HinB HinP IC1 IC2 IDB0 IFW INPc LENB LJS LO OFG P14 P5 RSP SFL SNPRINTF SNR SPM SPW SZ TP U1 U2 U5 UTS WMB : unit) => tt). intros until fuel. intros -> -> -> -> -> -> IV FUEL RPOS. pose proof (ai_iter fuel (ai_loop fuel)) as IT. red in IT. eapply IT; eassumption. Qed.

  (* [comment removed for export] *)
  Theorem ai_done : forall (ra' t0' xt1 t2' a0' xa1 a2' a3' a5' a6' a7' t3' t4' t5' t6' y0 y2 y3 xs4 y5 y6 y7 y8 y9 y10 y11 : word)
      (io : idbopts) (c' : cursor) (buf' : list Z) (m3 : mem) (bs3 cpad3 : list byte),
      xa1 = Z_to_bv 64 (io_tsresol io) -> xt1 = Z_to_bv 64 (Z.b2z (io_is_binary io)) -> xs4 = Z_to_bv 64 (io_tsoffset io) ->
      AIM io c' buf' m3 bs3 cpad3 ->
      evt usegs (POSTQ (ai_result idb_off p s c sg (Some q1) (buf', inr (io, c'))) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' xt1 t2' y0 (Z_to_bv 64 (P + 648))
                 a0' xa1 a2' a3' (Z_to_bv 64 SA) a5' a6' a7'
                 y2 y3 xs4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x17874) fc None m3 (seg_rom usegs)).
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS. pin_using (fun (APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HSA Hhd HinB HinP IC1 IC2 IDB0 IFW LENB LJS LO OFG P14 RSP SFL SNR SPW SZ U1 U2 U5 UTS : unit) => tt).
    intros until cpad3. intros -> -> -> IV.
    destruct IV as (TSR & MI3 & ST3 & AG3 & HD3 & FR3 & NG3 & AR1 & SL3 & AR2 & G3 & BUF3 & PFX3 & LB3 & GR3 & CC3 & CR1 & CR2 & CR3 & CR4 & HEB3 & AL4).
    eapply (ai_tail K HFL SFL); eassumption || (try exact IC1; try exact HSA; try lia).
  Qed.
End AIE.

End WithCeil.
End TwB.
End F_sfpcapng_aiE.

(* [comment removed for export] *)
Module F_sfpcapng_ai.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Lemma get_le32_at pre v0 v1 v2 v3 rest :
  get_le32 (pre ++ v0 :: v1 :: v2 :: v3 :: rest) (Z.of_nat (length pre)) = le4val v0 v1 v2 v3.
Proof using Type. pin_using tt.
  unfold get_le32. change (pre ++ v0 :: v1 :: v2 :: v3 :: rest) with (pre ++ [v0; v1; v2; v3] ++ rest).
  change 4%Z with (Z.of_nat (length [v0; v1; v2; v3])). rewrite zslice_at. cbn -[Z.add Z.mul]. unfold le4val. lia.
Qed.

Lemma le4_s32_lit x0 x1 x2 x3 : 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  le4 (Z_to_bv 64 (s32 (le4val x0 x1 x2 x3))) = [Z_to_bv 8 x0; Z_to_bv 8 x1; Z_to_bv 8 x2; Z_to_bv 8 x3].
Proof using Type. pin_using tt.
  intros. unfold s32, le4val.
  destruct (Z.lt_ge_cases (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3) (2^31)) as [LT|GE].
  - apply (le4_of_val _ x0 x1 x2 x3 0); try lia. rewrite unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
  - apply (le4_of_val _ x0 x1 x2 x3 (2^32 - 1)); try lia. rewrite unsigned_lit_wrap. Z.div_mod_to_equations; lia.
Qed.

Section AI.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.

  Open Scope bv_scope.

  Definition add_interface_proof__stmt : Prop := add_interface_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej pad cpad : ltac2:(SecDiet.SzSec.tyM 'add_interface_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma add_interface_proof__body : ltac2:(SecDiet.SzSec.bodyP 'add_interface_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL HPL MALLOCS REALLOC SFL SNPRINTF. pin_using (fun (HFL HPL MALLOCS REALLOC SFL SNPRINTF : unit) => tt).
    intros PRE HS HinP HinB APB -> -> -> -> HPV HNG HIF UTS WMB HBUF PFX LENB GRD HCUR CUR1 CUR2 CUR8 IDB0 COFF CREM CEND CBT HEB EBR.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPWC. pose proof (proj1 SPWC) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold ADD_INTERFACE_STACK, MALLOC_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    (* [comment removed for export] *)
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinB as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    assert (HinP'' : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ IBLK i I s ++ C2)).
    { apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinP') as (P1 & P2 & P3 & P4 & P5 & _). cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4, P5. unfold PCAP_NG_SF_TOTAL in P4, P5.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinB') as (B1 & B2 & B3 & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4.
    assert (P14 : (0 < P /\ P + 680 <= CEILZ)%Z) by (split; [exact P1| exact P4]).
    assert (B14 : (0 < B /\ B + pc_bufalloc p <= CEILZ)%Z) by (split; [exact B1| exact B4]).
    unfold PCAP_NG_SF_TOTAL in APB.
    assert (P5' : out_of_image P 680) by (unfold out_of_image; exact P5).
    assert (CLB : forall a, in_block (C1 ++ C2) a -> (a < CEILZ)%Z).
    { intros a Ha. apply in_block_app in Ha. destruct (GIo_CLc_facts K R st (C1 ++ IBLK i I s ++ C2) [] FB m a ltac:(rewrite app_nil_r; exact G)) as [Hc _]; [| lia].
      apply in_block_app. destruct Ha as [Ha|Ha]; [left; exact Ha| right; apply in_block_app; right; exact Ha]. }
    assert (INPc : forall a, (P <= a < P + 680)%Z -> in_block (C1 ++ C2) a).
    { intros a Ha. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INBc : forall a, (B <= a < B + pc_bufalloc p)%Z -> in_block (C1 ++ C2) a).
    { intros a Ha. apply in_block_In. exists (pc_buffer p, B, pc_bufalloc p). split; [exact HinB|]. cbn [cb_addr cb_size fst snd]. lia. }
    (* [comment removed for export] *)
    assert (EBX : ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (EB = P + 216))%Z) by (destruct EBR as [X|X]; [left| right]; lia).
    clear EBR.
    assert (EB64 : (0 < EB /\ EB + 256 < 2^64)%Z) by (unfold rc_spmain in EBX; destruct EBX as [X| ->]; lia).
    assert (CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256).
    { destruct EBX as [X| ->]; [right; lia| left]. intros a Ha. apply INPc. lia. }
    assert (EBiv : client_iv R (C1 ++ C2) (EB, (EB + 256)%Z)).
    { destruct EBX as [X| ->]; [left; cbn [fst snd]; unfold rc_lo; lia| right]. unfold iv_in_block. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    (* [comment removed for export] *)
    unfold ifaces_ok in HIF. rewrite HS in HIF.
    assert (IFC : (0 <= ng_ifcount s /\ ng_ifcount s <= ng_ifaces_size s /\ ng_ifaces_size s < 2^26 /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)))%Z).
    { destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0); lia| destruct HIF as (-> & E0 & E1 & E2); rewrite E0, E1, E2; cbn; lia]. }
    (* [comment removed for export] *)
    unfold add_interface. unfold ng_of, ng_ifaces_ptr_of. rewrite HS.
    cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_realloc prims pc_bufdata pc_swapped set_ng set_priv].
    replace (u32 (ng_ifcount s + 1)) with (ng_ifcount s + 1)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
    replace (u32 (ng_ifaces_size s * 2) <? ng_ifaces_size s) with false by (unfold u32; rewrite Z.mod_small by lia; symmetry; apply Z.ltb_ge; lia).
    unfold ADD_INTERFACE_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB. hide HBUF. hide HCUR. hide HNG. hide HPV.
    ienter. carve_frame 112%nat ST. do 16 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R st (C1 ++ IBLK i I s ++ C2) FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 112, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0
    end.
    clear MU WM.
    assert (T0 : forall A cs, rw_cells ssegs m A cs -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= A)%Z -> rw_cells ssegs m0 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG0 | exact HC | intros a Ha; cbn [outside]; lia]. }
    unhide HEB. unhide HBUF. unhide HCUR. unhide HNG. unhide HPV. pose proof HPV as HPVm.
    apply T0 in HEB; [|cbn [cells_size csize Nat.add]; destruct EBX as [X| ->]; lia].
    apply T0 in HBUF; [|cbn [cells_size csize Nat.add]; lia].
    apply T0 in HCUR; [|unfold cursor_cells; cbn [cells_size csize Nat.add]; lia].
    apply T0 in HNG; [|unfold ng_cells, PCAP_PRIV_OFF; cbn [cells_size csize Nat.add]; lia].
    apply T0 in HPV; [|cbn [cells_size csize Nat.add]; lia].
    assert (AGa : ai_AGP sp C1 C2 P B CUR EB p m m0).
    { eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]. }
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR) as [HD FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in HD, FRS.
    replace (bv_unsigned sp + -112 + Z.of_nat 8)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
    (* [comment removed for export] *)
    unfold PCAP_PRIV_OFF in HPV, HNG. unfold ng_cells in HNG. unfold cursor_cells in HCUR.
    hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS.
    step. step. rewrite (sx32_small (ng_ifcount s)) by lia. step. rewrite (sx32_small (ng_ifaces_size s)) by lia.
    step. rewrite (unsigned_lit (ng_ifcount s)), (bv_swrap32_small (ng_ifcount s + 1)) by lia.
    pose proof (munch_refl [(P + 660, P + 664)]%Z m0) as MU1. pose proof (wmono_refl ssegs m0) as WM1.
    hide HPV. step. unhide HPV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (AGS1 : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m0 m1) by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
    assert (G1 : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m1).
    { eapply (GIo_client_frame K HFL SFL); [exact G0 | exact MU1 | exact WM1 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_exists.
      exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP'' |]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    clear MU1 WM1.
    (* [comment removed for export] *)
    assert (KED0 : forall (ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' y3 y4 y5 : word) (m2 : mem) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' : Z)
                          (js : list if_junk) (pad1 junk1 : list byte) (hd : list cell),
      ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
      (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z -> (ng_ifcount sg <= ng_ifaces_size sg)%Z -> (1 <= ng_ifaces_size sg < 2^26)%Z ->
      length js = length (ng_ifaces s) -> Forall if_wf (ng_ifaces s) ->
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -112) -> ai_AGP sp C1 C2 P B CUR EB p m m2 ->
      rw_cells ssegs m2 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat ->
      rw_cells ssegs m2 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m2 (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells ssegs m2 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells ssegs m2 CUR [C8 (Z_to_bv 64 (B + cur_off c)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad] ->
      rw_cells ssegs m2 EB [CB 256 ej] ->
      rw_cells ssegs m2 (P + 648) (ng_cells sg I' pad1) ->
      rw_cells ssegs m2 I' (ifs_cells (rev (ng_ifaces s)) js) ->
      rw_cells ssegs m2 (I' + 40 * (ng_ifcount sg - 1)) [CB (Z.to_nat (40 * (ng_ifaces_size sg - (ng_ifcount sg - 1)))) junk1] ->
      GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m2 -> ps_outfile stG = ps_outfile st ->
      evt ssegs (POSTQ (ai_result idb_off p s c sg (Some q1) (process_idb_options (pc_swapped p) c (pc_bufdata p))) stG)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 P)
                 (Z_to_bv 64 I') (Z_to_bv 64 (B + idb_off)) (Z_to_bv 64 CUR) (Z_to_bv 64 (ng_ifcount sg - 1)) a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 648)) y3 y4 y5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x1700c) fc None m2 (seg_rom ssegs))).
    { intros until hd. intros U1 U2 U5 IC1 IC2 SZ LJS IFW MI2 ST2 AG2 HD2 Hhd FR2 HPV2 BUF2 CC2 HEB2 NG2 AR1 JK G2 OFG.
      clear HNG HPV G0 AGa G1 AGS1 HIF.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      pose proof (head_apart K _ _ _ _ _ _ _ G2 HinB) as APIB. pose proof (head_apart K _ _ _ _ _ _ _ G2 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIB, APIP. unfold PCAP_NG_SF_TOTAL in APIP.
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      remember (I' + 40 * (ng_ifcount sg - 1))%Z as SA eqn:HSA.
      (* [comment removed for export] *)
      destruct (split_at4 (pc_bufdata p) (Z.to_nat (idb_off + 4)) ltac:(lia)) as (pre0 & x0 & x1 & x2 & x3 & post0 & Ebuf & Lpre0).
      assert (GX : (0 <= x0 < 256 /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ 0 <= x3 < 256)%Z).
      { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
        pose proof (Forall_inv GB) as X0. pose proof (Forall_inv (Forall_inv_tail GB)) as X1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as X2.
        pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as X3. cbv beta in X0, X1, X2, X3. lia. }
      destruct GX as (X0 & X1 & X2 & X3).
      assert (SNAP : ai_snap idb_off p = le4val x0 x1 x2 x3).
      { unfold ai_snap. rewrite Ebuf. replace (idb_off + 4)%Z with (Z.of_nat (length pre0)) by lia. apply get_le32_at. }
      assert (SNR : (0 <= ai_snap idb_off p < 2^32)%Z) by (rewrite SNAP; unfold le4val; lia).
      pose proof PFX as PFX0. rewrite Ebuf in PFX0.
      destruct (pfx_decomp pre0 [x0; x1; x2; x3] post0 bs PFX0) as (bsr0 & Ebs & _). cbn [map] in Ebs.
      pose proof BUF2 as BX. rewrite Ebs in BX.
      pose proof (rw_cells_recell _ _ _ [CB (length pre0) (map b8 pre0); C4 (Z_to_bv 64 (le4val x0 x1 x2 x3)); CB (length bsr0) bsr0] BX
                    ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
      destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 1 BX2) as [HSN _]. clear BX BX' BX2. cbn [firstn skipn cells_size csize Nat.add app] in HSN.
      lazymatch type of HSN with rw_cells _ _ ?A _ => replace A with (B + idb_off + 4)%Z in HSN by lia end.
      (* [comment removed for export] *)
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [4%nat; 36%nat; Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))] JK ltac:(cbn; lia)) as JK'. clear JK.
      cbn [mk_CB_cells app] in JK'.
      hide HD2. hide FR2. hide HPV2. hide BUF2. hide HEB2. hide NG2. hide AR1.
      step. rewrite (sx32_s32 (le4val x0 x1 x2 x3)) by (unfold le4val; lia).
      step. rewrite (unsigned_lit (ng_ifcount sg - 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
      step. step. step.
      step. rewrite (unsigned_lit ((ng_ifcount sg - 1) * 4294967296)) by (keep_hyps hptr sp R P B CUR EB lo idb_off p s c sg I' js hd pre0 IC1 IC2 SZ; nia). rewrite mulhu40 by lia.
      step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
      pose proof (munch_refl [(SA, SA + 4)]%Z m2) as MU2. pose proof (wmono_refl ssegs m2) as WM2.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
      assert (AGS23 : agrees_on (fun a => outside [(SA, SA + 4)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ Ho; exact Ho]).
      unhide HD2. unhide FR2. unhide BUF2. unhide HEB2. unhide NG2. unhide AR1. clear HPV2.
      transport HD2 m3 AGS23 ltac:(prs). transport FR2 m3 AGS23 ltac:(prs). transport BUF2 m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c bs sg I' js hd SA pre0 IC1 IC2 HSA APIB; prs)). transport HEB2 m3 AGS23 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo idb_off p s c ej m2 stG sg q1 I' js hd SA pre0 LO BU EBX IC1 IC2 HSA G2 Q4 APIP; prs)).
      transport NG2 m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c sg I' js pad1 hd SA pre0 IC1 IC2 HSA APIP; prs)).
      transport AR1 m3 AGS23 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside]; lia).
      assert (G3 : GIo K R stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB m3).
      { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU2 | exact WM2 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      rename ST2 into ST3.
      assert (AG3 : ai_AGP sp C1 C2 P B CUR EB p m m3).
      { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|].
        pose proof (CLB a Ha). destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr). pose proof (head_apart K _ _ _ _ _ _ _ G2 Hin) as AP. cbn [cb_addr cb_size fst snd] in AP. lia. }
      clear MU2 WM2 AGS23 AG2 G2. rename MI2 into MI3.
      (* [comment removed for export] *)
      destruct (rw_cells_cut _ _ _ 2 JK') as [SL AR2]. clear JK'. cbn [firstn skipn cells_size csize Nat.add app] in SL, AR2.
      lazymatch type of AR2 with rw_cells _ _ ?A _ => replace A with (SA + 40)%Z in AR2 by lia end.
      lazymatch type of SL with rw_cells _ _ _ [_; CB 36 ?sjx] =>
        pose proof (rw_cells_recell _ _ _ [C4 (Z_to_bv 64 (ai_snap idb_off p)); CB 36 sjx] SL ltac:(pose proof (proj1 (proj1 SL)) as WF; cbn in WF |- *; clear - WF; tauto)
                      ltac:(cbn [cells_bytes cbytes app]; rewrite SNAP, le4_lit, le4_s32_lit by lia; reflexivity)) as SL3 end.
      clear SL.
      (* [comment removed for export] *)
      step. step. step. step.
      lazymatch type of SL3 with rw_cells _ _ _ [_; CB 36 ?sjx] => lazymatch type of AR2 with rw_cells _ _ _ [CB _ ?tlx] =>
        assert (AIM0 : AIM K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m R C1 C2 FB P B CUR EB lo idb_off p s c ej stG sg q1 I' SA js pad1 sjx tlx hd
                         (mkIdbOpts 1000000 0 false false false) c (pc_bufdata p) m3 bs cpad)
      end end.
      { split; [cbn; lia|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact AG3|]. split; [exact HD2|]. split; [exact FR2|].
        split; [exact NG2|]. split; [exact AR1|]. split; [exact SL3|]. split; [exact AR2|]. split; [exact G3|]. split; [exact BUF2|]. split; [exact PFX|].
        split; [reflexivity|]. split; [exact GRD|]. split; [exact CC2|]. split; [exact CREM|]. split; [lia|]. split; [lia|]. split; [reflexivity| exact HEB2]. }
      unfold process_idb_options.
      destruct (Z.eq_dec (cur_remaining c) 0) as [R0|R0].
      - (* [comment removed for export] *)
        rewrite (eqb_lits_eq _ _ R0). cbv iota. step.
        rewrite R0. change (Z.to_nat (0 / 4 + 1)) with 1%nat. rewrite pio_unfold. unfold pio_iter. rewrite R0. cbn [Z.eqb]. cbv iota.
        eapply (ai_done K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU RSP SPW HinP HinB P14 APB UTS IFW LENB CUR1 CUR8 IDB0 COFF CREM CEND EBX CLB stG sg q1 I' SA js pad1 _ _ hd U1 U2 U5 IC1 IC2 SZ LJS HSA SNR Hhd OFG);
          [reflexivity | reflexivity | reflexivity | exact AIM0].
      - (* [comment removed for export] *)
        rewrite (eqb_lits_false (cur_remaining c) 0) by lia. cbv iota.
        do 14 step.
        replace (Z.to_nat (cur_remaining c / 4 + 1)) with (S (Z.to_nat (cur_remaining c / 4))) by lia.
        eapply (ai_enter K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej
                  G LO BU SPM TP ALN RSP SPW HinP HinB P14 B14 APB P5' HPVm UTS IFW WMB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND CBT EBX EB64 CLB INPc CRE EBiv
                  stG sg q1 I' SA js pad1 _ _ hd U1 U2 U5 IC1 IC2 SZ LJS HSA SNR Hhd OFG);
          [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact AIM0 | lia | lia]. }
    (* [comment removed for export] *)
    assert (IBF : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size s <= CEILZ /\ (P + 680 <= I \/ I + 40 * ng_ifaces_size s <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size s <= B))%Z).
    { intros q ->. assert (HinI : In (q, I, (40 * ng_ifaces_size s)%Z) ((C1 ++ IBLK (Some q) I s ++ C2) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G HinI) as (I1 & I2 & I3 & I4 & _). cbn [cb_addr cb_size fst snd] in I1, I2, I3, I4.
      pose proof (mid_apart K _ _ _ _ _ _ _ _ G HinP) as AP1. pose proof (mid_apart K _ _ _ _ _ _ _ _ G HinB) as AP2. cbn [cb_addr cb_size fst snd] in AP1, AP2. unfold PCAP_NG_SF_TOTAL in AP1. lia. }
    (* [comment removed for export] *)
    step.
    destruct (Z.lt_ge_cases (ng_ifaces_size s) (ng_ifcount s + 1)) as [GROW|NOGROW].
    2:{ (* [comment removed for export] *)
      if_tf' true. rewrite (proj2 (Z.ltb_ge (ng_ifaces_size s) (ng_ifcount s + 1)) NOGROW).
      destruct i as [q|]; [| exfalso; lia].
      destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
      step. step.
      apply evt_done. apply (implM_retb ssegs). cbv beta iota.
      set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)).
      lazymatch goal with |- implM _ ?mdl _ _ _ =>
        replace mdl with (mret (St:=PS) (ai_result idb_off p s c SG (Some q) (process_idb_options (pc_swapped p) c (pc_bufdata p))))
          by (unfold ai_result, ai_slot, ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
              destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
      apply (implM_ret ssegs).
      (* [comment removed for export] *)
      unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
      transport HEB m1 AGS1 ltac:(prs). transport HBUF m1 AGS1 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p s bs js APB; prs)). transport HCUR m1 AGS1 ltac:(prs). transport HD m1 AGS1 ltac:(prs). transport FRS m1 AGS1 ltac:(prs). transport HPV m1 AGS1 ltac:(prs).
      apply T0 in AR; [| rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize Nat.add]; lia].
      transport AR m1 AGS1 ltac:(intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; lia).
      destruct (proj1 (rw_cells_app ssegs m1 I _ _) AR) as [AR1 JK]. clear AR. rewrite ifs_cells_size in JK by (rewrite length_rev; lia). rewrite length_rev in JK.
      assert (AGa1 : ai_AGP sp C1 C2 P B CUR EB p m m1).
      { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AGS1|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
      assert (G1p : GIo K R st ((q, I, 40 * ng_ifaces_size s)%Z :: C1 ++ C2) FB m1).
      { eapply (GIo_perm K HPL); [exact G1|]. cbn [IBLK app]. apply Permutation_sym. apply Permutation_middle. }
      replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
      eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 st SG q I js pad tail);
        [reflexivity | reflexivity | reflexivity | cbn; lia | cbn; lia | cbn; lia | exact LJS | exact IFW0 | exact MI | exact ST | exact AGa1 | exact HD | reflexivity | exact FRS | exact HPV | exact HBUF | exact HCUR | exact HEB
        | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
        | exact AR1
        | cbn [SG ng_ifcount ng_ifaces_size]; replace (ng_ifcount s + 1 - 1)%Z with (ng_ifcount s) by lia;
          lazymatch type of JK with rw_cells _ _ ?A _ => replace (I + 40 * ng_ifcount s)%Z with A by lia end; exact JK
        | exact G1p | reflexivity ]. }
    (* [comment removed for export] *)
    if_tf' false. rewrite (proj2 (Z.ltb_lt (ng_ifaces_size s) (ng_ifcount s + 1)) GROW).
    unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
    transport HEB m1 AGS1 ltac:(prs). transport HBUF m1 AGS1 ltac:(prs). transport HCUR m1 AGS1 ltac:(prs). transport HD m1 AGS1 ltac:(prs). transport FRS m1 AGS1 ltac:(prs). transport HPV m1 AGS1 ltac:(prs).
    assert (AGa1 : ai_AGP sp C1 C2 P B CUR EB p m m1).
    { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AGS1|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
    pose proof (ai_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R st C1 C2 FB P B CUR EB lo idb_off p s c bs ej
                  LO BU SPM TP ALN RSP SPW HinP P14 B14 APB LENB CUR1 CUR2 CUR8 IDB0 COFF CREM CEND EBX CLB CRE EBiv) as SNP.
    hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS.
    step.
    destruct (Z.eq_dec (ng_ifaces_size s) 0) as [SZ0|SZ0].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ SZ0). cbv iota. rewrite (proj2 (Z.eqb_eq _ _) SZ0).
      destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0); exfalso; lia|]. destruct HIF as (I0 & IFN & IC0 & _).
      do 4 step.
      apply evt_done. apply (implM_bind_assoc ssegs).
      name_sp sp (-112)%Z.
      eapply (implM_bind ssegs).
      { eapply MALLOCS; [| reflexivity | unfold PCAP_NG_IF_SIZE; lia].
        split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros qo st1 ms1 PO. cbv beta in PO.
      destruct PO as (av & m2 & E & OF1 & MI2 & ST2 & AG12 & RM).
      unfold hpost_regs in E. destruct_exs E. subst ms1. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 94188)) with (Z_to_bv 64 94188) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [IBLK app] in AG12.
      unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
      transport HD m2 AG12 ltac:(prs). transport FRS m2 AG12 ltac:(prs). transport HPV m2 AG12 ltac:(prs). transport HNG m2 AG12 ltac:(prs).
      transport HBUF m2 AG12 ltac:(prs). transport HCUR m2 AG12 ltac:(prs). transport HEB m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p s ej INPc EBX; prs)).
      assert (AGa2 : ai_AGP sp C1 C2 P B CUR EB p m m2).
      { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a ([Ha|Ha] & _); [left; lia| right; exact Ha]. }
      clear AG12 MI ST.
      hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV.
      destruct qo as [q'|].
      + (* [comment removed for export] *)
        destruct RM as (A & junkA & -> & G2 & HBK). cbn [IBLK app] in G2.
        pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4. unfold PCAP_NG_IF_SIZE in Q4, HBK.
        pose proof (head_apart K _ _ _ _ _ _ _ G2 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL, PCAP_NG_IF_SIZE in APIP.
        (* [comment removed for export] *)
        cbv iota. apply (implM_retb ssegs). cbv beta iota.
        set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) 1 (ng_ifaces s)).
        lazymatch goal with |- implM _ ?mdl _ _ _ =>
          replace mdl with (mret (St:=PS) (ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
            by (unfold ai_result, ai_slot, ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
                destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
        apply (implM_ret ssegs).
        step. step. rewrite (eqb_lits_false A 0) by lia. cbv iota.
        step. step. step. change (sx32 (Z_to_bv 64 (ng_ifcount s + 1))) with (sx32 (Z_to_bv 64 (ng_ifcount s + 1))). rewrite (sx32_small (ng_ifcount s + 1)) by lia.
        pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl ssegs m2) as WM3.
        hide HBK.
        step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
        assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
        assert (G3 : GIo K R st1 ((q', A, 40)%Z :: C1 ++ C2) FB m3).
        { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU3 | exact WM3 |].
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
            exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV. unhide HBK.
        transport HD m3 AGS23 ltac:(prs). transport FRS m3 AGS23 ltac:(prs). transport HPV m3 AGS23 ltac:(prs).
        transport HBUF m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c bs A APB; prs)). transport HCUR m3 AGS23 ltac:(prs). transport HEB m3 AGS23 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ej q' st1 A m3 LO BU P14 EBX G3; prs)). transport HBK m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p s A junkA APIP; prs)).
        assert (AGa3 : ai_AGP sp C1 C2 P B CUR EB p m m3).
        { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
        clear MU3 WM3 AGS23 G2 AGa2.
        destruct (rw_cells_cut _ _ _ 0 HBK) as [AR1 _]. cbn [firstn] in AR1.
        replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
        eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 st1 SG q' A [] pad junkA);
          [reflexivity | reflexivity | reflexivity | cbn; rewrite IFN; cbn; lia | cbn; lia | cbn; lia | rewrite IFN; reflexivity | rewrite IFN; constructor | exact MI2 | exact ST2 | exact AGa3 | exact HD | reflexivity | exact FRS | exact HPV | exact HBUF | exact HCUR | exact HEB
          | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
          | rewrite IFN; cbn [rev ifs_cells]; exact AR1
          | cbn [SG ng_ifcount ng_ifaces_size]; replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with A by lia; replace (Z.to_nat (40 * (1 - (ng_ifcount s + 1 - 1)))) with (Z.to_nat 40) by lia; exact HBK
          | exact G3 | exact OF1 ].
      + (* [comment removed for export] *)
        destruct RM as (-> & G2 & _). cbn [IBLK app] in G2.
        cbv iota. apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
        step. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
        step. change (sx32 (Z_to_bv 64 (ng_ifcount s + 1))) with (sx32 (Z_to_bv 64 (ng_ifcount s + 1))). rewrite (sx32_small (ng_ifcount s + 1)) by lia.
        do 4 step.
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV.
        assert (MSG : fmt_at m2 AI_FMT_OOM_IF "out of memory for per-interface information (%u interfaces)"%string)
          by (apply (fmt_at_intro m2 _ _ MI2); [vm_compute; reflexivity| unfold AI_FMT_OOM_IF; lia| unfold AI_FMT_OOM_IF; cbn; lia]).
        eapply SNP with (m3:=m2) (args:=[AInt (ng_ifcount s + 1)]);
          [ exact MI2 | exact ST2 | exact AGa2 | exact HD | reflexivity | exact FRS | exact HEB | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.oom_interfaces, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | ].
        exists (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)), None, I, pad, bs.
        split; [exact OF1|]. split; [reflexivity|]. split; [cbn [IBLK app]; exact G2|]. split; [unfold ng_cells; cbn; exact HNG|]. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
        split; [exact HBUF|]. split; [exact PFX|]. split; [reflexivity|]. split; [exact GRD|]. split; [exact I0|].
        eexists. split; [exact HCUR| reflexivity].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_false (ng_ifaces_size s) 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_neq _ _) SZ0). cbv iota.
      (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (ng_ifcount s) (2 ^ 22)) as [IFC25|IFC25].
      2:{ replace (ng_ifcount s <? 2 ^ 22) with false by (symmetry; apply Z.ltb_ge; exact IFC25). cbv beta iota delta [negb].
          apply evt_done. apply (implM_unr ssegs st). }
      replace (ng_ifcount s <? 2 ^ 22) with true by (symmetry; apply Z.ltb_lt; exact IFC25). cbv beta iota delta [negb].
      destruct i as [q|]; [| destruct HIF as (_ & _ & _ & E0); exfalso; lia].
      destruct HIF as (js & tail & LJS & AR & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
      assert (SZE : ng_ifaces_size s = ng_ifcount s) by lia.
      step. if_tf' false.
      step. rewrite (unsigned_lit (ng_ifaces_size s)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
      step. step. rewrite (unsigned_lit (ng_ifaces_size s * 2)), Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
      step. step. rewrite (unsigned_lit (ng_ifaces_size s * 2 * 4294967296)), Z.shiftr_div_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z. rewrite Z.div_mul by lia.
      step. rewrite (unsigned_lit (ng_ifaces_size s * 2 * 4294967296)) by lia. rewrite mulhu40 by lia.
      step. if_tf' true.
      (* [comment removed for export] *)
      apply T0 in AR; [| rewrite cells_size_app, ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; cbn [cells_size csize Nat.add]; lia].
      transport AR m1 AGS1 ltac:(intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; (keep_hyps CEILV hptr sp R P B I CUR EB lo p s js tail a LJS; lia)); rewrite length_rev in Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; (keep_hyps CEILV hptr sp R P B I CUR EB lo p s js a IFC API Ha; lia)).
      pose proof (proj1 (proj1 AR)) as WFA. apply cells_wf_app in WFA as [WFI WFT]. cbn in WFT. destruct WFT as [LT _].
      assert (TL0 : tail = []) by (destruct tail; [reflexivity| cbn in LT; lia]). subst tail.
      assert (ARm : rw_cells ssegs m1 I ([] ++ (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) []]) ++ [])) by (cbn [app]; rewrite app_nil_r; exact AR).
      apply rw_cells_merge in ARm. cbn [app] in ARm. rewrite cells_size_app, cells_bytes_app, ifs_cells_size in ARm by (rewrite length_rev; lia). rewrite length_rev in ARm.
      cbn [cells_size cells_bytes cbytes csize Nat.add app] in ARm. rewrite app_nil_r in ARm.
      replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in ARm by lia.
      (* [comment removed for export] *)
      do 5 step.
      apply evt_done. apply (implM_bind_assoc ssegs).
      name_sp sp (-112)%Z.
      cbn [IBLK app] in G1.
      eapply (implM_bind ssegs).
      { eapply REALLOC; [| reflexivity | unfold PCAP_NG_IF_SIZE; reflexivity | unfold PCAP_NG_IF_SIZE; lia | exact ARm].
        split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros qo st1 ms1 PO. cbv beta in PO.
      destruct PO as (av & m2 & E & OF1 & MI2 & ST2 & AG12 & RM).
      unfold hpost_regs in E. destruct_exs E. subst ms1. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 94892)) with (Z_to_bv 64 94892) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS.
      transport HD m2 AG12 ltac:(prs). transport FRS m2 AG12 ltac:(prs). transport HPV m2 AG12 ltac:(prs). transport HNG m2 AG12 ltac:(prs).
      transport HBUF m2 AG12 ltac:(prs). transport HCUR m2 AG12 ltac:(prs). transport HEB m2 AG12 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p s ej js INPc EBX; prs)).
      assert (AGa2 : ai_AGP sp C1 C2 P B CUR EB p m m2).
      { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a ([Ha|Ha] & _); [left; lia| right; exact Ha]. }
      clear AG12 MI ST AR ARm.
      hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV.
      unfold PCAP_NG_IF_SIZE in RM.
      destruct qo as [q'|].
      + (* [comment removed for export] *)
        destruct RM as (A & junkA & -> & G2 & HBK).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
        pose proof (head_apart K _ _ _ _ _ _ _ G2 HinP) as APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL in APIP.
        rewrite !Z.min_l in HBK by lia.
        (* [comment removed for export] *)
        cbv iota. apply (implM_retb ssegs). cbv beta iota.
        set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s * 2) (ng_ifaces s)).
        lazymatch goal with |- implM _ ?mdl _ _ _ =>
          replace mdl with (mret (St:=PS) (ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
            by (unfold ai_result, ai_slot, ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
                destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
        apply (implM_ret ssegs).
        step. rewrite (eqb_lits_false A 0) by lia. cbv beta iota delta [negb].
        step. step. step. change (sx32 (Z_to_bv 64 (ng_ifcount s + 1))) with (sx32 (Z_to_bv 64 (ng_ifcount s + 1))). rewrite (sx32_small (ng_ifcount s + 1)) by lia.
        pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl ssegs m2) as WM3.
        hide HBK.
        step. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
        assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
        assert (G3 : GIo K R st1 ((q', A, ng_ifaces_size s * 2 * 40)%Z :: C1 ++ C2) FB m3).
        { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU3 | exact WM3 |].
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
            exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV. unhide HBK.
        transport HD m3 AGS23 ltac:(prs). transport FRS m3 AGS23 ltac:(prs). transport HPV m3 AGS23 ltac:(prs).
        transport HBUF m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo idb_off p s c bs js A APB; prs)). transport HCUR m3 AGS23 ltac:(prs). transport HEB m3 AGS23 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ej js q' st1 A m3 LO BU P14 EBX G3; prs)). transport HBK m3 AGS23 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p s js A junkA APIP; prs)).
        assert (AGa3 : ai_AGP sp C1 C2 P B CUR EB p m m3).
        { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. (keep_hyps CEILV hptr sp R P B CUR EB p s js A a Hn; lia). }
        clear MU3 WM3 AGS23 G2 AGa2.
        (* [comment removed for export] *)
        destruct (rw_cells_cut _ _ _ 1 HBK) as [AR1 JK]. cbn [firstn skipn cells_size csize Nat.add] in AR1, JK.
        pose proof (rw_cells_recell _ _ _ (ifs_cells (rev (ng_ifaces s)) js) AR1 WFI
                      ltac:(cbn [cells_bytes cbytes app]; rewrite app_nil_r; symmetry; apply firstn_all2; rewrite (cells_bytes_length _ WFI), ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as AR1'.
        replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
        eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 st1 SG q' A js pad junkA);
          [reflexivity | reflexivity | reflexivity | cbn; (keep_hyps CEILV hptr sp R P B CUR EB lo p s js A E1; lia) | cbn; (keep_hyps CEILV hptr sp R P B CUR EB lo p s js A E3 SZE; lia) | cbn; (keep_hyps CEILV hptr sp R P B CUR EB lo p s js A E3 IFC25 SZE; lia) | exact LJS | exact IFW0 | exact MI2 | exact ST2 | exact AGa3 | exact HD | reflexivity | exact FRS | exact HPV | exact HBUF | exact HCUR | exact HEB
          | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
          | exact AR1'
          | cbn [SG ng_ifcount ng_ifaces_size]; lazymatch type of JK with rw_cells _ _ ?AA [CB ?n _] => replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with AA by (keep_hyps CEILV hptr sp R P B CUR EB lo p s js A E3 SZE; lia); replace (Z.to_nat (40 * (ng_ifaces_size s * 2 - (ng_ifcount s + 1 - 1)))) with n by (keep_hyps CEILV hptr sp R P B CUR EB lo p s js A SZE; lia) end; exact JK
          | replace (40 * ng_ifaces_size SG)%Z with (ng_ifaces_size s * 2 * 40)%Z by (cbn [SG ng_ifaces_size]; (keep_hyps CEILV hptr sp R P B CUR EB p s js A; lia)); exact G3 | exact OF1 ].
      + (* [comment removed for export] *)
        destruct RM as (-> & G2 & HBK & _).
        cbv iota. apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
        step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
        step. change (sx32 (Z_to_bv 64 (ng_ifcount s + 1))) with (sx32 (Z_to_bv 64 (ng_ifcount s + 1))). rewrite (sx32_small (ng_ifcount s + 1)) by lia.
        do 4 step.
        unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HPV.
        assert (MSG : fmt_at m2 AI_FMT_OOM_IF "out of memory for per-interface information (%u interfaces)"%string)
          by (apply (fmt_at_intro m2 _ _ MI2); [vm_compute; reflexivity| unfold AI_FMT_OOM_IF; lia| unfold AI_FMT_OOM_IF; cbn; lia]).
        eapply SNP with (m3:=m2) (args:=[AInt (ng_ifcount s + 1)]);
          [ exact MI2 | exact ST2 | exact AGa2 | exact HD | reflexivity | exact FRS | exact HEB | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.oom_interfaces, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 | ].
        exists (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)), (Some q), I, pad, bs.
        split; [exact OF1|]. split; [reflexivity|]. split; [cbn [IBLK app ng_ifaces_size]; eapply (GIo_perm K HPL); [exact G2| apply Permutation_sym; apply Permutation_middle]|].
        split; [unfold ng_cells; cbn; exact HNG|]. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
        split; [exact HBUF|]. split; [exact PFX|]. split; [reflexivity|]. split; [exact GRD|].
        split. { unfold ng_ifaces_closable. cbn [ng_ifaces_size]. split; [eexists; exact HBK| lia]. }
        eexists. split; [exact HCUR| reflexivity].
  Qed.
  End Sz1.
  Theorem add_interface_proof : ltac:(let t := eval cbv delta [add_interface_proof__stmt] in add_interface_proof__stmt in exact t).
  Proof using HFL HPL MALLOCS REALLOC SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB P B I CUR EB lo idb_off p s i c bs ej pad cpad. ltac2:(SecDiet.SzSec.closeP 'add_interface_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AI.

End WithCeil.
End F_sfpcapng_ai.

(* [comment removed for export] *)
Module F_sfpcapng_chkB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Lemma max_snaplen_le3 : forall d, (1 <= max_snaplen_for_dlt d <= 134217728)%Z.
Proof using Type. pin_using tt. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

(* [comment removed for export] *)
Lemma shl_shr_32_small : forall x, (0 <= x < 2^32)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32 = x.
Proof using Type. pin_using tt.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
Qed.

Section ChkNgB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).
  (* [comment removed for export] *)
  Variables (qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z) (ew : word).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis P16 : P mod 16 = 0.
  Hypothesis P5 : out_of_image P 680.
  Hypothesis BS0R : 1 <= BS0 <= 2^21.
  Hypothesis MINR : 0 <= MINOR < 2^16.

  #[local] Notation pL := (ngc_p f qs sw BS0 MINOR).
  #[local] Notation hcells := (ngc_hcells P sw BS0 MINOR).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ngc_ok_tail__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x0 x4 x5 x7 x8 x9 : word) (m5 : mem) (ps5 : PS)
           (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z) (pad bs e : list byte) (hc : list cell),
      mem_inv ssegs m5 -> stk ssegs m5 lo (bv_unsigned sp + -128) -> AGQ m5 ->
      GIo K R ps5 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m5 -> ps_outfile ps5 = ps_outfile s ->
      rw_cells ssegs m5 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m5 ->
      rw_cells ssegs m5 ERR [C4 ew] -> rw_cells ssegs m5 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m5 EB [CB 256 e] ->
      rw_cells ssegs m5 P (hcells B) -> rw_cells ssegs m5 (P + 648) (ng_cells sg I pad) ->
      ng_user_tsresol sg = 1000000%Z -> ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE -> (0 <= ng_ifcount sg < 2^32)%Z -> (0 <= ng_ifaces_size sg < 2^32)%Z ->
      ifaces_ok (pL qb bufalloc bufdata sg i) I m5 ->
      rw_cells ssegs m5 B [CB (Z.to_nat bufalloc) bs] -> firstn (length bufdata) bs = map b8 bufdata ->
      (16 <= Z.of_nat (length bufdata) <= bufalloc)%Z -> (0 <= bufalloc < 2^32)%Z -> (BS0 <= bufalloc)%Z -> Forall (fun z => 0 <= z < 256)%Z bufdata ->
      implM ssegs (ngc_done PR 0 8 (pL qb bufalloc bufdata sg i)) ps5 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' x0 (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 P) (Z_to_bv 64 (B + 8)) x4 x5 (Z_to_bv 64 (P + 648)) x7 x8 x9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16ad4) fc None m5 (seg_rom ssegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x0 x4 x5 x7 x8 x9 m5 ps5 qb B bufalloc bufdata sg i I pad bs e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngc_ok_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0R CTX HFL HPL MINR P14 P16 SFL. pin_using (fun (BS0R CTX HFL HPL MINR P14 P16 SFL : unit) => tt).
    intros MI5 ST5 AG5 G5 OF5 HC5 Hhc FRS5 ERR5 MG5 HEB5 CELLS NG5 UTS MB IC IS HIF BUF5 PFX LENB BAR BSB GRD.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    (* [comment removed for export] *)
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G5 ltac:(lia)) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    (* [comment removed for export] *)
    destruct (split_at8 bufdata 8 ltac:(lia)) as (pre8 & l0 & l1 & r0 & r1 & n0 & n1 & n2 & n3 & post & Ebuf & Lpre8).
    assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
    { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
      pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
      cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
    destruct GX as (L0 & L1 & R0' & R1' & N0 & N1 & N2 & N3).
    assert (GLT : get_le16 bufdata 8 = (l0 + 256 * l1)%Z) by (rewrite Ebuf; replace 8%Z with (Z.of_nat (length pre8)) by lia; apply get_le16_at).
    assert (GSN : get_le32 bufdata 12 = le4val n0 n1 n2 n3).
    { rewrite Ebuf. change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post).
      rewrite app_assoc. replace 12%Z with (Z.of_nat (length (pre8 ++ [l0; l1; r0; r1]))) by (rewrite length_app; cbn; lia). apply get_le32_at. }
    pose proof PFX as PFX0. rewrite Ebuf in PFX0.
    change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
    destruct (pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) as (bsr & Ebs & PFXr). cbn [map] in Ebs.
    pose proof BUF5 as BX. rewrite Ebs in BX.
    assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat bufalloc)%nat).
    { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
    pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                  ltac:(cbn; rewrite length_map; repeat split; fastfirst (first [reflexivity | lia]))
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
    destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HIDB _]. clear BX BX' BX2.
    cbn [firstn skipn cells_size csize Nat.add app] in HIDB. rewrite Lpre8 in HIDB.
    lazymatch type of HIDB with rw_cells _ _ ?A _ => replace A with (B + 8)%Z in HIDB by lia end.
    (* [comment removed for export] *)
    unfold ngc_done. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [pc_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_version_major pc_version_minor ng_of ngc_p pc_priv ng_ifaces_ptr_of].
    rewrite GLT. replace (8 + 4)%Z with 12%Z by reflexivity. rewrite GSN, MB, UTS.
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (msl := max_snaplen_for_dlt lt). pose proof (max_snaplen_le3 lt) as MSR. fold msl in MSR.
    unfold MAX_BLOCKSIZE_FOR_SNAPLEN, INITIAL_MAX_BLOCKSIZE.
    apply (implM_ret ssegs).
    unfold ngc_hcells, ngcells in CELLS. unfold ng_cells in NG5. rewrite MB, UTS in NG5. unfold INITIAL_MAX_BLOCKSIZE in NG5.
    hide HC5. hide FRS5. hide ERR5. hide MG5. hide HEB5. hide BUF5. hide NG5. hide CELLS.
    step. rewrite (zx16_lit (l0 + 256 * l1)) by lia. step.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply linktype_to_dlt_proof; [exact MI5 | reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x16adc)) with (Z_to_bv 64 0x16adc) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold lt.
    step. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    unhide CELLS. unhide NG5.
    pose proof (munch_refl [(P, P + 680)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    clear HIDB. step. step.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply adjust_snapshot_proof; [reflexivity | lia | reflexivity | unfold le4val; lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x16ae8)) with (Z_to_bv 64 0x16ae8) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold snap.
    step. rewrite (sx32_small lt) by lia.
    step. pstep. step. step.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x16afc)) with (Z_to_bv 64 0x16afc) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold msl.
    step. step. rewrite (zx32_lit 16777216) by lia. step. rewrite (shl_shr_32_small msl) by lia.
    step. step. step.
    (* [comment removed for export] *)
    assert (FIN : forall (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : mem) (mb : Z),
      (0 <= mb <= 2^30)%Z ->
      (if 16777216 <? msl + 131104 then mb = msl + 131104 else mb = 16777216)%Z ->
      mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -128) -> munch [(P, P + 680)]%Z m5 m6 -> wmono ssegs m5 m6 ->
      rw_cells ssegs m6 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
                             (C4 (Z_to_bv 64 snap)) (C4 (Z_to_bv 64 lt)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells ssegs m6 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 mb); C4 (Z_to_bv 64 (ng_ifcount sg)); C4 (Z_to_bv 64 (ng_ifaces_size sg)); CB 4 pad; C8 (Z_to_bv 64 I)] ->
      evt ssegs (POSTQ (CH_Ok (mkPcap qs f BS0 bufalloc qb bufdata sw 1 MINOR snap lt 0 0 0 [] hdr0
                                (PrivNg (if 16777216 <? msl + 131104 then mkNg 1000000 (msl + 131104) (ng_ifcount sg) (ng_ifaces_size sg) (ng_ifaces sg) else sg) i))) ps5)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0x t1x t2x (Z_to_bv 64 131104) (Z_to_bv 64 EB) a0x a1x a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 P) (Z_to_bv 64 (B + 8)) x4 x5 (Z_to_bv 64 (P + 648)) x7 x8 x9 s10 s11 t3x t4x t5x t6x)
            F (Z_to_bv 64 0x16b28) fc None m6 (seg_rom ssegs))).
    { intros until mb. intros MBR MBE MI6 ST6 MU6 WM6 CELLS6 NG6.
      clear MU WM CELLS NG5 ST5. unfold ngcells in CELLS6.
      step. step. step. pstep. step. step. pstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      assert (AGS : agrees_on (fun a => outside [(P, P + 680)]%Z a) m5 m7) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      rename ST6 into ST7.
      unhide FRS5. unfold ngc_FRS in FRS5. transport FRS5 m7 AGS ltac:(prs).
      unhide HC5. destruct (rw_cells_forget _ _ _ _ HC5) as [hj HC']. clear HC5. rewrite Hhc in HC'. transport HC' m7 AGS ltac:(prs).
      hide CELLS6. hide NG6.
      do 13 step.
      release_frame HC' ST7 (bv_unsigned sp + -88)%Z. release_frame FRS5 ST7 (bv_unsigned sp).
      unhide CELLS6. unhide NG6. unhide ERR5. unhide MG5. unhide HEB5. unhide BUF5.
      transport ERR5 m7 AGS ltac:(prs). transport HEB5 m7 AGS ltac:(prs). transport BUF5 m7 AGS ltac:(prs).
      transport MG5 m7 AGS ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia).
      assert (G7 : GIo K R ps5 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m7).
      { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. right. apply ngl_iv_P; lia. }
      assert (HIF7 : ifaces_ok (pL qb bufalloc bufdata sg i) I m7).
      { eapply ifaces_ok_agree; [exact AGS | | exact HIF]. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. destruct (API sg' q E) as (I1 & I4 & IP & IB). cbn [outside]. lia. }
      destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL. cbn [map] in MG5.
      apply evt_done. unfold check_header_post.
      exists (Z_to_bv 64 P), m7, ew.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact OF5|]. split; [assumption|]. split; [exact ST7|].
      split. { unfold ngc_AGQ in AG5. eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|].
               intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in *; lia| pose proof (NPB a Ha); lia]. }
      split; [eapply rw_cells_recell; [exact MG5 | cbn; repeat split; exact Logic.I | reflexivity]|].
      split; [exact ERR5|].
      exists P, ((qs, P, 680%Z) :: (qb, B, bufalloc) :: IBLK i I sg).
      split; [reflexivity|].
      split; [eapply (GIo_perm K HPL); [exact G7| apply ngl_perm]|].
      split; [| split; [reflexivity| exists e; exact HEB5]].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, I, blank_junk, pad, bs.
      destruct (16777216 <? msl + 131104) eqn:HLT; subst mb.
      all: split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ng_ifaces_size]; destruct i; reflexivity|].
      all: split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk;
                  cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_ng pk_cleanup_ng
                       pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                       pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0];
                  exact CELLS6 |].
      all: split; [unfold priv_cells, PCAP_PRIV_OFF; cbn [pc_priv]; unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size ng_ifaces]; rewrite ?UTS, ?MB; exact NG6|].
      all: split; [exact BUF5|]. all: split; [exact PFX|].
      all: split; [unfold ifaces_ok in HIF7 |- *; cbn [pc_priv ngc_p ng_ifaces ng_ifcount ng_ifaces_size] in HIF7 |- *; exact HIF7|].
      all: unfold pcap_wf; cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size].
      all: rewrite ?UTS, ?MB; unfold INT_MAX, INITIAL_MAX_BLOCKSIZE; repeat split; lia. }
    step.
    unfold bv_ltu. rewrite (unsigned_lit (msl + 131104)), (unsigned_lit 16777216) by lia.
    destruct (Z.lt_ge_cases 16777216 (msl + 131104)) as [LT|GE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) LT) in FIN |- *. cbn [negb]. cbv iota.
      step. rewrite (sx32_small lt) by lia. step.
      eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
      cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & -> & ->).
      replace (ret_pc (Z_to_bv 64 0x16b20)) with (Z_to_bv 64 0x16b20) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold msl.
      step. rewrite ?(unsigned_lit msl) by lia. step.
      eapply FIN with (mb := (msl + 131104)%Z); [lia | reflexivity | assumption | assumption | exact MU | exact WM | exact CELLS | exact NG5].
    - rewrite (proj2 (Z.ltb_ge _ _) GE) in FIN |- *. cbn [negb]. cbv iota.
      eapply FIN with (mb := 16777216%Z); [lia | reflexivity | assumption | assumption | exact MU | exact WM | exact CELLS | exact NG5].
  Qed.
  End Sz3.
  Lemma ngc_ok_tail : ltac:(let t := eval cbv delta [ngc_ok_tail__stmt] in ngc_ok_tail__stmt in exact t).
  Proof using BS0R CTX HFL HPL MINR P14 P16 SFL. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x0 x4 x5 x7 x8 x9 m5 ps5 qb B bufalloc bufdata sg i I pad bs e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_ok_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgB.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcapng_chkK. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Lemma max_snaplen_le3 : forall d, (1 <= max_snaplen_for_dlt d <= 134217728)%Z.
Proof using Type. pin_using tt. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

(* [comment removed for export] *)
Lemma shl_shr_32_small : forall x, (0 <= x < 2^32)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32 = x.
Proof using Type. pin_using tt.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
Qed.

Section ChkNgB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).
  (* [comment removed for export] *)
  Variables (qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z) (ew : word).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis P16 : P mod 16 = 0.
  Hypothesis P5 : out_of_image P 680.
  Hypothesis BS0R : 1 <= BS0 <= 2^21.
  Hypothesis MINR : 0 <= MINOR < 2^16.

  #[local] Notation pL := (ngc_p f qs sw BS0 MINOR).
  #[local] Notation hcells := (ngc_hcells P sw BS0 MINOR).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ngc_ok_tail__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x0 x4 x5 x7 x8 x9 : word) (m5 : mem) (ps5 : PS)
           (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z) (pad bs e : list byte) (hc : list cell),
      mem_inv usegs m5 -> stk usegs m5 lo (bv_unsigned sp + -128) -> AGQ m5 ->
      GIo K R ps5 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m5 -> ps_outfile ps5 = ps_outfile s ->
      rw_cells usegs m5 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m5 ->
      rw_cells usegs m5 ERR [C4 ew] -> rw_cells usegs m5 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m5 EB [CB 256 e] ->
      rw_cells usegs m5 P (hcells B) -> rw_cells usegs m5 (P + 648) (ng_cells sg I pad) ->
      ng_user_tsresol sg = 1000000%Z -> ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE -> (0 <= ng_ifcount sg < 2^32)%Z -> (0 <= ng_ifaces_size sg < 2^32)%Z ->
      ifaces_ok (pL qb bufalloc bufdata sg i) I m5 ->
      rw_cells usegs m5 B [CB (Z.to_nat bufalloc) bs] -> firstn (length bufdata) bs = map b8 bufdata ->
      (16 <= Z.of_nat (length bufdata) <= bufalloc)%Z -> (0 <= bufalloc < 2^32)%Z -> (BS0 <= bufalloc)%Z -> Forall (fun z => 0 <= z < 256)%Z bufdata ->
      implM usegs (ngc_done PR 0 8 (pL qb bufalloc bufdata sg i)) ps5 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' x0 (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (B + 8)) (Z_to_bv 64 P) x4 x5 (Z_to_bv 64 (P + 648)) x7 x8 x9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16f20) fc None m5 (seg_rom usegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x0 x4 x5 x7 x8 x9 m5 ps5 qb B bufalloc bufdata sg i I pad bs e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngc_ok_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS0R CTX HFL HPL MINR P14 P16 SFL. pin_using (fun (BS0R CTX HFL HPL MINR P14 P16 SFL : unit) => tt).
 intros MI5 ST5 AG5 G5 OF5 HC5 Hhc FRS5 ERR5 MG5 HEB5 CELLS NG5 UTS MB IC IS HIF BUF5 PFX LENB BAR BSB GRD.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    (* [comment removed for export] *)
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G5 ltac:(lia)) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    (* [comment removed for export] *)
    destruct (split_at8 bufdata 8 ltac:(lia)) as (pre8 & l0 & l1 & r0 & r1 & n0 & n1 & n2 & n3 & post & Ebuf & Lpre8).
    assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
    { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
      pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
      pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
      cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
    destruct GX as (L0 & L1 & R0' & R1' & N0 & N1 & N2 & N3).
    assert (GLT : get_le16 bufdata 8 = (l0 + 256 * l1)%Z) by (rewrite Ebuf; replace 8%Z with (Z.of_nat (length pre8)) by lia; apply get_le16_at).
    assert (GSN : get_le32 bufdata 12 = le4val n0 n1 n2 n3).
    { rewrite Ebuf. change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post).
      rewrite app_assoc. replace 12%Z with (Z.of_nat (length (pre8 ++ [l0; l1; r0; r1]))) by (rewrite length_app; cbn; lia). apply get_le32_at. }
    pose proof PFX as PFX0. rewrite Ebuf in PFX0.
    change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
    destruct (pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) as (bsr & Ebs & PFXr). cbn [map] in Ebs.
    pose proof BUF5 as BX. rewrite Ebs in BX.
    assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat bufalloc)%nat).
    { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
    pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                  ltac:(cbn; rewrite length_map; repeat split; fastfirst (first [reflexivity | lia]))
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
    destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HIDB _]. clear BX BX' BX2.
    cbn [firstn skipn cells_size csize Nat.add app] in HIDB. rewrite Lpre8 in HIDB.
    lazymatch type of HIDB with rw_cells _ _ ?A _ => replace A with (B + 8)%Z in HIDB by lia end.
    (* [comment removed for export] *)
    unfold ngc_done. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [pc_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_version_major pc_version_minor ng_of ngc_p pc_priv ng_ifaces_ptr_of].
    rewrite GLT. replace (8 + 4)%Z with 12%Z by reflexivity. rewrite GSN, MB, UTS.
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (msl := max_snaplen_for_dlt lt). pose proof (max_snaplen_le3 lt) as MSR. fold msl in MSR.
    unfold MAX_BLOCKSIZE_FOR_SNAPLEN, INITIAL_MAX_BLOCKSIZE.
    apply (implM_ret usegs).
    unfold ngc_hcells, ngcells in CELLS. unfold ng_cells in NG5. rewrite MB, UTS in NG5. unfold INITIAL_MAX_BLOCKSIZE in NG5.
    hide HC5. hide FRS5. hide ERR5. hide MG5. hide HEB5. hide BUF5. hide NG5. hide CELLS.
    step. rewrite (zx16_lit (l0 + 256 * l1)) by lia. step.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply linktype_to_dlt_proof; [exact MI5 | reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x16f28)) with (Z_to_bv 64 0x16f28) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold lt.
    step. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    unhide CELLS. unhide NG5.
    pose proof (munch_refl [(P, P + 680)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    clear HIDB. step. step.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply adjust_snapshot_proof; [reflexivity | lia | reflexivity | unfold le4val; lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x16f34)) with (Z_to_bv 64 0x16f34) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold snap.
    step. rewrite (sx32_small lt) by lia.
    step. pstep. step. step.
    (* [comment removed for export] *)
    eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x16f48)) with (Z_to_bv 64 0x16f48) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold msl.
    step. step. rewrite (zx32_lit 16777216) by lia. step. rewrite (shl_shr_32_small msl) by lia.
    step. step. step.
    (* [comment removed for export] *)
    assert (FIN : forall (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : mem) (mb : Z),
      (0 <= mb <= 2^30)%Z ->
      (if 16777216 <? msl + 131104 then mb = msl + 131104 else mb = 16777216)%Z ->
      mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -128) -> munch [(P, P + 680)]%Z m5 m6 -> wmono usegs m5 m6 ->
      rw_cells usegs m6 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
                             (C4 (Z_to_bv 64 snap)) (C4 (Z_to_bv 64 lt)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells usegs m6 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 mb); C4 (Z_to_bv 64 (ng_ifcount sg)); C4 (Z_to_bv 64 (ng_ifaces_size sg)); CB 4 pad; C8 (Z_to_bv 64 I)] ->
      evt usegs (POSTQ (CH_Ok (mkPcap qs f BS0 bufalloc qb bufdata sw 1 MINOR snap lt 0 0 0 [] hdr0
                                (PrivNg (if 16777216 <? msl + 131104 then mkNg 1000000 (msl + 131104) (ng_ifcount sg) (ng_ifaces_size sg) (ng_ifaces sg) else sg) i))) ps5)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0x t1x t2x (Z_to_bv 64 131104) (Z_to_bv 64 EB) a0x a1x a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 (B + 8)) (Z_to_bv 64 P) x4 x5 (Z_to_bv 64 (P + 648)) x7 x8 x9 s10 s11 t3x t4x t5x t6x)
            F (Z_to_bv 64 0x16f74) fc None m6 (seg_rom usegs))).
    { intros until mb. intros MBR MBE MI6 ST6 MU6 WM6 CELLS6 NG6.
      clear MU WM CELLS NG5 ST5. unfold ngcells in CELLS6.
      step. step. step. pstep. step. step. pstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      assert (AGS : agrees_on (fun a => outside [(P, P + 680)]%Z a) m5 m7) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      rename ST6 into ST7.
      unhide FRS5. unfold ngc_FRS in FRS5. transport FRS5 m7 AGS ltac:(prs).
      unhide HC5. destruct (rw_cells_forget _ _ _ _ HC5) as [hj HC']. clear HC5. rewrite Hhc in HC'. transport HC' m7 AGS ltac:(prs).
      hide CELLS6. hide NG6.
      do 13 step.
      release_frame HC' ST7 (bv_unsigned sp + -88)%Z. release_frame FRS5 ST7 (bv_unsigned sp).
      unhide CELLS6. unhide NG6. unhide ERR5. unhide MG5. unhide HEB5. unhide BUF5.
      transport ERR5 m7 AGS ltac:(prs). transport HEB5 m7 AGS ltac:(prs). transport BUF5 m7 AGS ltac:(prs).
      transport MG5 m7 AGS ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia).
      assert (G7 : GIo K R ps5 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m7).
      { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. right. apply ngl_iv_P; lia. }
      assert (HIF7 : ifaces_ok (pL qb bufalloc bufdata sg i) I m7).
      { eapply ifaces_ok_agree; [exact AGS | | exact HIF]. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. destruct (API sg' q E) as (I1 & I4 & IP & IB). cbn [outside]. lia. }
      destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL. cbn [map] in MG5.
      apply evt_done. unfold check_header_post.
      exists (Z_to_bv 64 P), m7, ew.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact OF5|]. split; [assumption|]. split; [exact ST7|].
      split. { unfold ngc_AGQ in AG5. eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|].
               intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in *; lia| pose proof (NPB a Ha); lia]. }
      split; [eapply rw_cells_recell; [exact MG5 | cbn; repeat split; exact Logic.I | reflexivity]|].
      split; [exact ERR5|].
      exists P, ((qs, P, 680%Z) :: (qb, B, bufalloc) :: IBLK i I sg).
      split; [reflexivity|].
      split; [eapply (GIo_perm K HPL); [exact G7| apply ngl_perm]|].
      split; [| split; [reflexivity| exists e; exact HEB5]].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, I, blank_junk, pad, bs.
      destruct (16777216 <? msl + 131104) eqn:HLT; subst mb.
      all: split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc ng_ifaces_size]; destruct i; reflexivity|].
      all: split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk;
                  cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_ng pk_cleanup_ng
                       pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                       pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0];
                  exact CELLS6 |].
      all: split; [unfold priv_cells, PCAP_PRIV_OFF; cbn [pc_priv]; unfold ng_cells; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size ng_ifaces]; rewrite ?UTS, ?MB; exact NG6|].
      all: split; [exact BUF5|]. all: split; [exact PFX|].
      all: split; [unfold ifaces_ok in HIF7 |- *; cbn [pc_priv ngc_p ng_ifaces ng_ifcount ng_ifaces_size] in HIF7 |- *; exact HIF7|].
      all: unfold pcap_wf; cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size].
      all: rewrite ?UTS, ?MB; unfold INT_MAX, INITIAL_MAX_BLOCKSIZE; repeat split; lia. }
    step.
    unfold bv_ltu. rewrite (unsigned_lit (msl + 131104)), (unsigned_lit 16777216) by lia.
    destruct (Z.lt_ge_cases 16777216 (msl + 131104)) as [LT|GE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) LT) in FIN |- *. cbn [negb]. cbv iota.
      step. rewrite (sx32_small lt) by lia. step.
      eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
      cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & -> & ->).
      replace (ret_pc (Z_to_bv 64 0x16f6c)) with (Z_to_bv 64 0x16f6c) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold msl.
      step. rewrite ?(unsigned_lit msl) by lia. step.
      eapply FIN with (mb := (msl + 131104)%Z); [lia | reflexivity | assumption | assumption | exact MU | exact WM | exact CELLS | exact NG5].
    - rewrite (proj2 (Z.ltb_ge _ _) GE) in FIN |- *. cbn [negb]. cbv iota.
      eapply FIN with (mb := 16777216%Z); [lia | reflexivity | assumption | assumption | exact MU | exact WM | exact CELLS | exact NG5].
  Qed.
  End Sz3.
  Lemma ngc_ok_tail : ltac:(let t := eval cbv delta [ngc_ok_tail__stmt] in ngc_ok_tail__stmt in exact t).
  Proof using BS0R CTX HFL HPL MINR P14 P16 SFL. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x0 x4 x5 x7 x8 x9 m5 ps5 qb B bufalloc bufdata sg i I pad bs e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_ok_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgB.

End WithCeil.
End TwB.
End F_sfpcapng_chkB.

(* [comment removed for export] *)
Module F_sfpcapng_chkC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL}.
Lemma swap4_at pre (u0 u1 u2 u3 : Z) rest :
  swap_field 4 (Z.of_nat (length pre)) (pre ++ u0 :: u1 :: u2 :: u3 :: rest) = pre ++ u3 :: u2 :: u1 :: u0 :: rest.
Proof using Type. pin_using tt.
  unfold swap_field.
  replace (zslice (Z.of_nat (length pre)) 4 (pre ++ u0 :: u1 :: u2 :: u3 :: rest)) with [u0; u1; u2; u3] by (symmetry; exact (zslice_at pre [u0; u1; u2; u3] rest)).
  unfold buf_write_at, zfirstn, zskipn, zlength. cbn [rev app length].
  rewrite Nat2Z.id, firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  replace (Z.to_nat (Z.of_nat (length pre) + Z.of_nat 4)) with (length pre + 4)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. replace (length pre + 4 - length pre)%nat with 4%nat by lia. reflexivity.
Qed.
End WithCeil.


Open Scope bv_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition idb_swap_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (A : Z) (l0 l1 r0 r1 n0 n1 n2 n3 : Z),
    mem_inv ssegs m -> (0 < A)%Z -> (A + 8 < 2^64)%Z ->
    (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= r0 < 256)%Z -> (0 <= r1 < 256)%Z ->
    (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
    s3 = Z_to_bv 64 A ->
    rw_cells ssegs m A [C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ->
    evt ssegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16ac0) fc None m' (seg_rom ssegs)
        /\ munch [(A, A + 8)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' A [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16a78) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A l0 l1 r0 r1 n0 n1 n2 n3 : ltac2:(SecDiet.SzSec.tyM 'idb_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma idb_swap_block__body : ltac2:(SecDiet.SzSec.bodyP 'idb_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI HA1 HA2 L0 L1 R0 R1 N0 N1 N2 N3 -> HC.
  pose proof (munch_refl [(A, A + 8)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 18 step.
  apply evt_done. do 6 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HC | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le2_lit l1 l0), (le2_lit r0 r1), (le4_lit n3 n2 n1 n0) by lia.
  rewrite (le2_of_val _ l1 l0 l1); [| lia | lia | lia | apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.swap16_val; [lia | lia | apply unsigned_zx16; lia] ].
  rewrite (le4_of_val _ n3 n2 n1 n0 (n1 + 256 * n2 + 65536 * n3 + 16777216 * ((((n3 / 128) * 4294967295) mod 256))));
    [reflexivity | lia | lia | lia | lia | Z.div_mod_to_equations; lia
    | apply (swap32_val _ n0 n1 n2 n3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
Qed.
End Sz1.
Lemma idb_swap_block : ltac:(let t := eval cbv delta [idb_swap_block__stmt] in idb_swap_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A l0 l1 r0 r1 n0 n1 n2 n3. ltac2:(SecDiet.SzSec.closeP 'idb_swap_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WithCeil.


Close Scope bv_scope.

(* [comment removed for export] *)
Ltac prsMG GL := intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; repeat match goal with |- _ /\ _ => split end; fastfirst (first [lia | left; lia | exact Logic.I]).

Section WithCeil.
Context {CEILV : CEIL}.
Section ChkNgC.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).
  (* [comment removed for export] *)
  Variables (qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z) (ew : word).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis P16 : P mod 16 = 0.
  Hypothesis P5 : out_of_image P 680.
  Hypothesis BS0R : 1 <= BS0 <= 2^21.
  Hypothesis MINR : 0 <= MINOR < 2^16.

  #[local] Notation pL := (ngc_p f qs sw BS0 MINOR).
  #[local] Notation hcells := (ngc_hcells P sw BS0 MINOR).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ngc_snp_fail__stmt : Prop := forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' a3v a4v x3 x4 x5 x8 x9 : word) (RA : Z) (m3 : mem) (ps3 : PS)
           (fs : string) (args : list farg) (FMTA : Z) (msg bufdata : list Z)
           (qb : hptr) (i : option hptr) (sg : pcap_ng_sf) (B I nb : Z) (e : list byte) (hc : list cell),
      (RA = 0x169a4 \/ RA = 0x16a08)%Z ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -128) -> AGQ m3 ->
      GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m3 -> ps_outfile ps3 = ps_outfile s ->
      match i with Some _ => True | None => I = 0%Z end ->
      rw_cells ssegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m3 ->
      rw_cells ssegs m3 ERR [C4 ew] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m3 EB [CB 256 e] ->
      rw_cells ssegs m3 (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells ssegs m3 (P + 672) [C8 (Z_to_bv 64 I)] ->
      (0 <= I < 2^64)%Z -> (1 <= nb)%Z ->
      fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      (forall (CLx : list cblk) D dn, Forall2 (farg_word R CLx (bv_unsigned sp + -128) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
      items_okb (fmt fs) = true -> Forall arg_ok args -> Fmt.snprintf 256 fs args = msg ->
      implM ssegs (ngc_fail MOps PR msg (ngc_p f qs sw BS0 MINOR qb nb bufdata sg i)) ps3 POSTQ
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
                 (Z_to_bv 64 P) x3 x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) x8 x9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m3 (seg_rom ssegs)).
  Section Sz2.
  Variables t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' a3v a4v x3 x4 x5 x8 x9 RA m3 ps3 fs args FMTA msg bufdata qb i sg B I nb e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @t0').
  Lemma ngc_snp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_snp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CTX FREE HFL HPL P14 SFL SNPRINTF. pin_using (fun (CTX FREE HFL HPL P14 SFL SNPRINTF : unit) => tt).
    intros HRA MI3 ST3 AG3 G3 OF3 HI HC3 Hhc FRS3 ERR3 MG3 HEB3 HPB HPI IR NB FAT FOK ALEN FW FIT AOK EMSG.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 NB) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
    unfold implM. iprefix.
    name_sp sp (-128)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB lo EB 256%Z FMTA fs args e);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3
        | right; rewrite Hsp; lia ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -128 - STDIO_STACK, bv_unsigned sp + -128); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    unfold STDIO_STACK in AGS, MU4.
    assert (G4 : GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4).
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    transport HC3 m4 AGS ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia).
    unfold ngc_FRS in FRS3. transport FRS3 m4 AGS ltac:(prs). transport ERR3 m4 AGS ltac:(prs).
    transport MG3 m4 AGS ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia).
    transport HPB m4 AGS ltac:(prs). transport HPI m4 AGS ltac:(prs).
    assert (AG4 : AGQ m4).
    { unfold ngc_AGQ in AG3 |- *. eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|].
      intros a [[Ha|Ha] [Hn _]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
    pose proof (snprintf_length 256 fs args) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. rewrite EMSG in LS, HEB4.
    change (Z.to_nat 256) with 256%nat in HEB4.
    replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia.
    hide HC3. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide HPB. hide HPI.
    destruct HRA as [-> | ->];
      [ replace (ret_pc (Z_to_bv 64 0x169a4)) with (Z_to_bv 64 0x169a4) by (symmetry; apply ret_pc_even; [lia|reflexivity])
      | replace (ret_pc (Z_to_bv 64 0x16a08)) with (Z_to_bv 64 0x16a08) by (symmetry; apply ret_pc_even; [lia|reflexivity]) ].
    all: step.
    all: unhide HC3; unhide FRS3; unhide ERR3; unhide MG3; unhide HEB4; unhide HPB; unhide HPI.
    all: apply evt_done; eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
      [ exact CTX | exact MI4 | exact ST4 | exact AG4 | destruct i; exact G4 | exact HI | exact HC3 | exact Hhc | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
      | lia | rewrite <- EMSG; apply snprintf_ok; [exact FIT| exact AOK] | exact OF3 | exact HPB | exact HPI | exact IR | lia | lia ].
  Qed.
  End Sz2.
  Lemma ngc_snp_fail : ltac:(let t := eval cbv delta [ngc_snp_fail__stmt] in ngc_snp_fail__stmt in exact t).
  Proof using CTX FREE HFL HPL P14 SFL SNPRINTF. intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' a3v a4v x3 x4 x5 x8 x9 RA m3 ps3 fs args FMTA msg bufdata qb i sg B I nb e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_snp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_mcp_fail__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' x3 x4 x5 x8 x9 : word) (m3 : mem) (ps3 : PS)
           (SRC n : Z) (str : string) (msg bufdata : list Z)
           (qb : hptr) (i : option hptr) (sg : pcap_ng_sf) (B I nb : Z) (e : list byte) (hc : list cell),
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -128) -> AGQ m3 ->
      GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m3 -> ps_outfile ps3 = ps_outfile s ->
      match i with Some _ => True | None => I = 0%Z end ->
      rw_cells ssegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m3 ->
      rw_cells ssegs m3 ERR [C4 ew] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m3 EB [CB 256 e] ->
      rw_cells ssegs m3 (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells ssegs m3 (P + 672) [C8 (Z_to_bv 64 I)] ->
      (0 <= I < 2^64)%Z -> (1 <= nb)%Z ->
      fmt_at m3 SRC str -> (Z.of_nat (String.length str) + 1 = n)%Z -> (n <= 256)%Z ->
      map b8 msg = map (fun ch => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii ch))) (String.list_ascii_of_string str) ->
      Forall (fun z => 0 < z < 256)%Z msg ->
      implM ssegs (ngc_fail MOps PR msg (ngc_p f qs sw BS0 MINOR qb nb bufdata sg i)) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 a0' (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                 (Z_to_bv 64 P) x3 x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) x8 x9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16a28) fc None m3 (seg_rom ssegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' x3 x4 x5 x8 x9 m3 ps3 SRC n str msg bufdata qb i sg B I nb e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngc_mcp_fail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_mcp_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CTX FREE HFL HPL P14 SFL. pin_using (fun (CTX FREE HFL HPL P14 SFL : unit) => tt).
    intros MI3 ST3 AG3 G3 OF3 HI HC3 Hhc FRS3 ERR3 MG3 HEB3 HPB HPI IR NB [SRCB SRCR] LN NB2 EMSG MOK.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 NB) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (LM : length msg = String.length str).
    { apply (f_equal (@length _)) in EMSG. rewrite !length_map, length_list_ascii in EMSG. exact EMSG. }
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB3 ltac:(cbn; lia)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
    unfold implM. iprefix.
    hide HC3. hide FRS3. hide ERR3. hide MG3. hide HE2. hide HPB. hide HPI.
    step. step.
    eapply evt_cut.
    { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB SRC n);
        [reflexivity | reflexivity | reflexivity | exact SRCB | rewrite length_app, length_map, length_list_ascii; cbn [length]; lia | lia | exact HE1
        | lia | lia | lia | exact MI3]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MU4 & WM4 & MI4 & HE1' & _). clear HE1.
    replace (ret_pc (Z_to_bv 64 0x16a30)) with (Z_to_bv 64 0x16a30) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(EB, EB + n)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (ST4 : stk ssegs m4 lo (bv_unsigned sp + -128)).
    { eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
    assert (G4 : GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4).
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    unhide HC3. unhide FRS3. unhide ERR3. unhide MG3. unhide HE2. unhide HPB. unhide HPI.
    transport HC3 m4 AGS ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia).
    unfold ngc_FRS in FRS3. transport FRS3 m4 AGS ltac:(prs). transport ERR3 m4 AGS ltac:(prs).
    transport MG3 m4 AGS ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia).
    transport HE2 m4 AGS ltac:(prs). transport HPB m4 AGS ltac:(prs). transport HPI m4 AGS ltac:(prs).
    assert (AG4 : AGQ m4).
    { unfold ngc_AGQ in AG3 |- *. eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|].
      intros a [_ [Hn _]]; cbn [outside]. lia. }
    lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] =>
      assert (HEB4 : rw_cells ssegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) j]) end.
    { join_cells HE1' HE2.
      eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_list_ascii in *; cbn [length] in *; repeat split; try lia; tauto |].
      cbn [cells_bytes cbytes app]. rewrite EMSG, <- app_assoc. reflexivity. }
    apply evt_done. eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
      [ exact CTX | exact MI4 | exact ST4 | exact AG4 | destruct i; exact G4 | exact HI | exact HC3 | exact Hhc | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
      | rewrite LM; lia | exact MOK | exact OF3 | exact HPB | exact HPI | exact IR | lia | lia ].
  Qed.
  End Sz3.
  Lemma ngc_mcp_fail : ltac:(let t := eval cbv delta [ngc_mcp_fail__stmt] in ngc_mcp_fail__stmt in exact t).
  Proof using CTX FREE HFL HPL P14 SFL. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' x3 x4 x5 x8 x9 m3 ps3 SRC n str msg bufdata qb i sg B I nb e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_mcp_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma hcells_cut : forall mX B,
    rw_cells ssegs mX P (hcells B) ->
    rw_cells ssegs mX (P + 24) [C8 (Z_to_bv 64 B)]
    /\ rw_cells ssegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z sw))].
  Proof using Type. pin_using tt.
    intros mX B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 4 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 X2]. destruct (rw_cells_cut _ _ _ 2 X2) as [_ X3]. destruct (rw_cells_cut _ _ _ 2 X3) as [X4 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1, X4. unfold PCAP_PRIV_OFF.
    split; [replace (P + 24)%Z with (P + Z.of_nat 24)%Z by lia; exact X1|].
    replace (P + 48)%Z with (P + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16)%Z by lia. exact X4.
  Qed.
  Lemma ngcells_cut672 : forall mX sg I pad,
    rw_cells ssegs mX (P + 648) (ng_cells sg I pad) -> rw_cells ssegs mX (P + 672) [C8 (Z_to_bv 64 I)].
  Proof using Type. pin_using tt.
    intros mX sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 5 HN) as [_ X]. cbn [firstn skipn cells_size csize Nat.add app] in X.
    replace (P + 672)%Z with (P + 648 + Z.of_nat 24)%Z by lia. exact X.
  Qed.

  (* [comment removed for export] *)
  Hypothesis AI : add_interface_stmt HO K sites.

  Definition ngc_idb__stmt : Prop := forall (fuel : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x8 : word) (m4 : mem) (ps4 : PS)
           (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z) (pad bs e cpad j0 j1 : list byte) (c : cursor),
      mem_inv ssegs m4 -> stk ssegs m4 lo (bv_unsigned sp + -128) -> AGQ m4 ->
      GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m4 -> ps_outfile ps4 = ps_outfile s ->
      rw_cells ssegs m4 (bv_unsigned sp + -128) [CB 8 j0] -> rw_cells ssegs m4 (bv_unsigned sp + -120) (cursor_cells B c cpad) ->
      rw_cells ssegs m4 (bv_unsigned sp + -96) [CB 8 j1] -> FRS m4 ->
      rw_cells ssegs m4 ERR [C4 ew] -> rw_cells ssegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m4 EB [CB 256 e] ->
      rw_cells ssegs m4 P (hcells B) -> rw_cells ssegs m4 (P + 648) (ng_cells sg I pad) ->
      ng_user_tsresol sg = 1000000%Z -> ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE -> (0 <= ng_ifcount sg < 2^32)%Z -> (0 <= ng_ifaces_size sg < 2^32)%Z ->
      ifaces_ok (pL qb bufalloc bufdata sg i) I m4 ->
      rw_cells ssegs m4 B [CB (Z.to_nat bufalloc) bs] -> firstn (length bufdata) bs = map b8 bufdata ->
      Z.of_nat (length bufdata) = (cur_remaining c + 12)%Z ->
      cur_off c = 8%Z -> (0 <= cur_remaining c)%Z -> (cur_remaining c + 12 <= bufalloc)%Z -> (cur_remaining c + 12 <= 2^30)%Z -> cur_block_type c = 1%Z ->
      (0 <= bufalloc < 2^32)%Z -> (BS0 <= bufalloc)%Z -> Forall (fun z => 0 <= z < 256)%Z bufdata ->
      implM ssegs (mbind (ngc_K MOps PR fuel (RB_Ok c (pL qb bufalloc bufdata sg i))) (ngc_loop_tail MOps PR 0)) ps4 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 P) (Z_to_bv 64 FA) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) x8 (Z_to_bv 64 6) s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16980) fc None m4 (seg_rom ssegs)).
  Section Sz6.
  Variables fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x8 m4 ps4 qb B bufalloc bufdata sg i I pad bs e cpad j0 j1 c : ltac2:(SecDiet.SzSec.tyM 'ngc_idb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_idb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI BS0R CTX FREE HFL HPL MINR P14 P16 SFL SNPRINTF. pin_using (fun (AI BS0R CTX FREE HFL HPL MINR P14 P16 SFL SNPRINTF : unit) => tt).
    intros MI4 ST4 AG4 G4 OF4 HD4 HCUR4 HTL4 FRS4 ERR4 MG4 HEB4 CELLS NG4 UTS MB IC IS HIF BUF4 PFX LENB COFF CREM CR1 CR2 CBT BAR BSB GRD.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G4 ltac:(lia)) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    (* [comment removed for export] *)
    unfold ngc_K. rewrite CBT. unfold BT_IDB. cbn [Z.eqb Pos.eqb]. cbv iota.
    unfold get_from_block_data. rewrite COFF, CBT.
    unfold cursor_cells in HCUR4. rewrite COFF, CBT in HCUR4.
    assert (IR : (0 <= I < 2^64)%Z) by (destruct i as [q|]; [destruct (API sg q eq_refl) as (I1 & I4 & _); lia| cbn in HI; lia]).
    (* [comment removed for export] *)
    assert (HC40 : forall mX ccs, rw_cells ssegs mX (bv_unsigned sp + -128) [CB 8 j0] -> rw_cells ssegs mX (bv_unsigned sp + -120) ccs -> cells_size ccs = 24%nat ->
                   rw_cells ssegs mX (bv_unsigned sp + -96) [CB 8 j1] ->
                   rw_cells ssegs mX (bv_unsigned sp + -128) ([CB 8 j0] ++ ccs ++ [CB 8 j1]) /\ cells_size ([CB 8 j0] ++ ccs ++ [CB 8 j1]) = 40%nat).
    { intros mX ccs X1 X2 X3 X4. split; [| rewrite !cells_size_app, X3; reflexivity].
      pose proof (rw_cells_uncut _ _ _ _ _ X1 X2 ltac:(cbn; lia)) as J1.
      exact (rw_cells_uncut _ _ _ _ _ J1 X4 ltac:(rewrite cells_size_app, X3; cbn; lia)). }
    hide HD4. hide HTL4. hide FRS4. hide ERR4. hide MG4. hide HEB4. hide CELLS. hide NG4. hide BUF4.
    unfold implM. iprefix.
    step. step. step.
    unfold bv_ltu. rewrite (unsigned_lit 7), (unsigned_lit (cur_remaining c)) by lia.
    destruct (Z.lt_ge_cases (cur_remaining c) 8) as [RLT|RGE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_ge 7 (cur_remaining c))) by lia. cbv iota.
      rewrite (proj2 (Z.ltb_lt (cur_remaining c) 8) RLT). cbv iota.
      apply evt_done. apply (implM_retb ssegs). unfold ngc_loop_tail. unfold implM. iprefix.
      do 6 step.
      assert (MSG : fmt_at m4 0x10cd0 "block of type %u in pcapng dump file is too short"%string)
        by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| lia| cbn; lia]).
      unhide HD4. unhide HTL4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4. unhide CELLS. unhide NG4.
      destruct (HC40 m4 _ HD4 HCUR4 ltac:(reflexivity) HTL4) as [HC Hhc].
      apply evt_done.
      eapply (ngc_snp_fail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x169a4 m4 ps4 "block of type %u in pcapng dump file is too short"%string [AInt 1] 0x10cd0
                (Msg.block_too_short 1) bufdata qb i sg B I bufalloc e);
        [ left; reflexivity | exact MI4 | exact ST4 | exact AG4 | exact G4 | exact OF4 | exact HI | exact HC | exact Hhc | exact FRS4 | exact ERR4 | exact MG4 | exact HEB4
        | exact (proj1 (hcells_cut _ _ CELLS)) | exact (ngcells_cut672 _ _ _ _ NG4) | exact IR | lia
        | exact MSG | reflexivity | cbn; lia | intros; cbn [length firstn]; constructor; [reflexivity| constructor]
        | vm_compute; reflexivity | apply args_ok_ints1 | unfold Msg.block_too_short, PCAP_ERRBUF_SIZE; reflexivity ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt 7 (cur_remaining c))) by lia. cbv iota.
      rewrite (proj2 (Z.ltb_ge (cur_remaining c) 8) RGE). cbv iota.
      cbn [pc_swapped ngc_p pc_bufdata].
      (* [comment removed for export] *)
      assert (CALL : forall (rax a1x a2x a3x a4x a5x : word) (m5 : mem) (bd : list Z) (bs5 : list byte),
        bd = (if sw then swap_field 4 12 (swap_field 2 8 bufdata) else bufdata) ->
        mem_inv ssegs m5 -> stk ssegs m5 lo (bv_unsigned sp + -128) -> AGQ m5 ->
        GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m5 ->
        rw_cells ssegs m5 (bv_unsigned sp + -128) [CB 8 j0] ->
        rw_cells ssegs m5 (bv_unsigned sp + -120) (cursor_cells B (mkCursor 16 (cur_remaining c - 8) 1) cpad) ->
        rw_cells ssegs m5 (bv_unsigned sp + -96) [CB 8 j1] -> FRS m5 ->
        rw_cells ssegs m5 ERR [C4 ew] -> rw_cells ssegs m5 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m5 EB [CB 256 e] ->
        rw_cells ssegs m5 P (hcells B) -> rw_cells ssegs m5 (P + 648) (ng_cells sg I pad) ->
        ifaces_ok (pL qb bufalloc bd sg i) I m5 ->
        rw_cells ssegs m5 B [CB (Z.to_nat bufalloc) bs5] -> firstn (length bd) bs5 = map b8 bd -> length bd = length bufdata ->
        Forall (fun z => 0 <= z < 256)%Z bd ->
        evt ssegs (fun ms1 => impl ssegs (at_node ssegs) (npeek ssegs)
             ((Monad.mbind (mo_bind MOps (add_interface MOps PR (pL qb bufalloc bd sg i) 8 (mkCursor 16 (cur_remaining c - 8) 1))
                             (fun x : bool * cursor * pcapT * list Z => let '(ok, _, p, m) := x in
                                if ok then mo_ret MOps (@inr (list Z) Z 8%Z, p) else mo_ret MOps (@inl (list Z) Z m, p)))
                          (ngc_loop_tail MOps PR 0)) ps4)
             (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
          (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 P) a1x a2x a3x a4x a5x a6' a7'
                   (Z_to_bv 64 P) (Z_to_bv 64 (B + 8)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) x8 (Z_to_bv 64 6) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x16ac0) fc None m5 (seg_rom ssegs))).
      { intros until bs5. intros Ebd MI5 ST5 AG5 G5 HD5 HCUR5 HTL5 FRS5 ERR5 MG5 HEB5 CELLS5 NG5 HIF5 BUF5 PFX5 LEN5 GRD5.
        clear ST4 MI4 AG4 G4 HCUR4 HIF PFX GRD.
        assert (LBD : Z.of_nat (length bd) = (cur_remaining c + 12)%Z) by (rewrite LEN5; exact LENB).
        hide HD5. hide HTL5. hide FRS5. hide ERR5. hide MG5. hide HEB5. hide CELLS5. hide NG5. hide BUF5. hide HCUR5.
        do 4 step.
        unhide HEB5. unhide CELLS5. unhide NG5. unhide BUF5. unhide HCUR5.
        apply evt_done. apply (implM_bind_assoc ssegs). name_sp sp (-128)%Z. eapply (implM_bind ssegs).
        { eapply (AI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps4 [] ((qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB P B I (bv_unsigned sp + -120)%Z EB lo 8%Z
                     (pL qb bufalloc bd sg i) sg i (mkCursor 16 (cur_remaining c - 8) 1) bs5 e pad cpad);
            [ split; [cbn [app]; exact G5|]; split; [rewrite Hsp; exact ST5|]; split; [unfold rc_lo; lia|]; split; [unfold ADD_INTERFACE_STACK, MALLOC_STACK; rewrite Hsp; lia|];
              split; [rewrite Hsp; lia|]; split; [exact MI5|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
            | reflexivity | left; reflexivity | right; left; reflexivity | unfold PCAP_NG_SF_TOTAL; cbn [pc_bufalloc ngc_p]; lia
            | reflexivity | reflexivity | reflexivity | reflexivity
            | exact (proj2 (hcells_cut _ _ CELLS5)) | exact NG5 | exact HIF5 | rewrite UTS; lia | rewrite MB; unfold INITIAL_MAX_BLOCKSIZE; lia
            | exact BUF5 | exact PFX5 | cbn [pc_bufdata pc_bufalloc ngc_p]; lia | exact GRD5
            | exact HCUR5 | rewrite ?Hsp; lia | lia | rewrite ?Hsp; apply aligned16_8; [exact ALN| reflexivity]
            | lia | reflexivity | cbn [cur_remaining]; lia | cbn [cur_off cur_remaining pc_bufdata ngc_p]; lia | cbn [cur_block_type]; lia
            | exact HEB5 | left; rewrite Hsp; lia ]. }
        intros [[[ok c5] p5] msg5] ps5 ms5 PO.
        destruct PO as (a0v & m6 & s' & i' & I' & pad' & bs' & E & OF5 & MI6 & ST6 & AG6 & EP & G6 & NG6 & U1 & U2 & U3 & U4 & BUF6 & PFX6 & LEN6 & GR6 & -> & RM).
        unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 0x16ad0)) with (Z_to_bv 64 0x16ad0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        cbn [app] in G6. set (bd' := pc_bufdata p5) in *. rewrite EP. cbn [pc_bufdata pc_bufalloc ngc_p] in LEN6.
        assert (OF6 : ps_outfile ps5 = ps_outfile s) by (rewrite OF5; exact OF4).
        destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia)) as (_ & _ & API' & _).
        unhide HD5. unhide HTL5. unhide FRS5. unhide ERR5. unhide MG5.
        cbn [pc_bufalloc ngc_p] in AG6. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in AG6.
        transport HD5 m6 AG6 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs). transport HTL5 m6 AG6 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs).
        unfold ngc_FRS in FRS5. transport FRS5 m6 AG6 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs). transport ERR5 m6 AG6 ltac:(unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs).
        transport MG5 m6 AG6 ltac:(prsMG GL).
        assert (INP5 : forall a, (P <= a < P + 680)%Z -> in_block ([] ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) a).
        { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        transport CELLS5 m6 AG6 ltac:(unfold ngc_hcells, ngcells, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; prs).
        assert (AG06 : AGQ m6).
        { unfold ngc_AGQ in AG5 |- *. eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|].
          intros a [[Ha|Ha] [Hn _]]; unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL; cbn [app]; [split; [left; lia| lia]|].
          pose proof (CLB a Ha). pose proof (NPB a Ha). split; [right; unfold in_block in Ha |- *; do 2 apply Exists_cons_tl; exact Ha| lia]. }
        unfold implM. iprefix.
        destruct ok; cbn [Z.b2z].
        - (* [comment removed for export] *)
          destruct RM as (HIF6 & (cpad' & HCUR6) & CR1' & CR2' & CR3' & CBT' & HEB6 & ->). rewrite EP in HIF6.
          hide HD5. hide HTL5. hide FRS5. hide ERR5. hide MG5. hide CELLS5. hide NG6. hide BUF6. hide HCUR6. hide HEB6.
          step. rewrite (eqb_lits_false 1 0) by lia. cbv iota.
          unhide HD5. unhide HTL5. unhide FRS5. unhide ERR5. unhide MG5. unhide CELLS5. unhide NG6. unhide BUF6. unhide HCUR6. unhide HEB6.
          destruct (HC40 m6 _ HD5 HCUR6 ltac:(reflexivity) HTL5) as [HC Hhc].
          apply evt_done. apply (implM_retb ssegs). unfold ngc_loop_tail.
          eapply (ngc_ok_tail HO K sites HFL SFL HPL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX
                    qs P sw BS0 MINOR ew (conj P1 P4) P16 BS0R MINR);
            [ exact MI6 | exact ST6 | exact AG06 | exact G6 | exact OF6 | exact HC | exact Hhc | exact FRS5 | exact ERR5 | exact MG5 | exact HEB6
            | exact CELLS5 | exact NG6 | rewrite U1; exact UTS | rewrite U2; exact MB | exact U3 | exact U4 | exact HIF6 | exact BUF6 | exact PFX6
            | cbn [pc_bufdata pc_bufalloc ngc_p set_ng set_priv set_bufdata]; lia | cbn [pc_bufalloc ngc_p set_ng set_priv set_bufdata]; lia | cbn [pc_bufalloc ngc_p set_ng set_priv set_bufdata]; lia | exact GR6 ].
        - (* [comment removed for export] *)
          destruct RM as (CLOS & (ccs' & HCUR6 & Hccs') & (junk6 & HEB6) & LENM & MOK).
          hide HD5. hide HTL5. hide FRS5. hide ERR5. hide MG5. hide CELLS5. hide NG6. hide BUF6. hide HCUR6. hide HEB6.
          step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
          unhide HD5. unhide HTL5. unhide FRS5. unhide ERR5. unhide MG5. unhide CELLS5. unhide NG6. unhide BUF6. unhide HCUR6. unhide HEB6.
          destruct (HC40 m6 _ HD5 HCUR6 Hccs' HTL5) as [HC Hhc].
          apply evt_done. apply (implM_retb ssegs). unfold ngc_loop_tail. unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
          assert (HI' : match i' with Some _ => True | None => I' = 0%Z end) by (unfold ng_ifaces_closable in CLOS; destruct i'; [exact Logic.I| exact CLOS]).
          assert (IR' : (0 <= I' < 2^64)%Z) by (destruct i' as [q|]; [destruct (API' s' q eq_refl) as (I1 & I4 & _); lia| cbn in HI'; lia]).
          eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i') (ni := (40 * ng_ifaces_size s')%Z);
            [ exact CTX | exact MI6 | exact ST6 | exact AG06 | destruct i'; exact G6 | exact HI' | exact HC | exact Hhc | exact FRS5 | exact ERR5 | exact MG5 | exact HEB6
            | exact LENM | exact MOK | exact OF6 | exact (proj1 (hcells_cut _ _ CELLS5)) | exact (ngcells_cut672 _ _ _ _ NG6) | exact IR' | lia | lia ]. }
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp + -120, bv_unsigned sp + -96)]%Z m4) as MUc. pose proof (wmono_refl ssegs m4) as WMc.
      step. step. rewrite ?(unsigned_lit (cur_remaining c)) by lia. step.
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      assert (AGS45 : agrees_on (fun a => outside [(bv_unsigned sp + -120, bv_unsigned sp + -96)]%Z a) m4 m5)
        by (eapply agrees_on_of_munch; [exact MUc | exact WMc | intros a _ Ho; exact Ho]).
      assert (G5 : GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MUc | exact WMc |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG5 : AGQ m5).
      { unfold ngc_AGQ in AG4 |- *. eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AGS45|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      assert (HIF5 : ifaces_ok (pL qb bufalloc bufdata sg i) I m5).
      { eapply ifaces_ok_agree; [exact AGS45 | | exact HIF]. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. destruct (API sg' q E) as (I1 & I4 & _). cbn [outside]. lia. }
      unhide HD4. unhide HTL4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4. unhide CELLS. unhide NG4. unhide BUF4.
      transport HD4 m5 AGS45 ltac:(prs). transport HTL4 m5 AGS45 ltac:(prs). unfold ngc_FRS in FRS4. transport FRS4 m5 AGS45 ltac:(prs).
      transport ERR4 m5 AGS45 ltac:(prs). transport MG4 m5 AGS45 ltac:(prsMG GL). transport HEB4 m5 AGS45 ltac:(prs).
      transport CELLS m5 AGS45 ltac:(unfold ngc_hcells, ngcells; prs). transport NG4 m5 AGS45 ltac:(unfold ng_cells; prs). transport BUF4 m5 AGS45 ltac:(prs).
      clear MUc WMc AG4 G4 HIF.
      replace (B + 8 + 8)%Z with (B + 16)%Z in HCUR4 by lia.
      (* [comment removed for export] *)
      step. rewrite (eqb_lits_false (B + 8) 0) by lia. cbv iota.
      step. unfold ngc_hcells, ngcells in CELLS. step. rewrite (sx32_small (Z.b2z sw)) by (destruct sw; cbn; lia). step.
      replace (cur_remaining c + -8)%Z with (cur_remaining c - 8)%Z in HCUR4 by lia.
      destruct sw; cbn [Z.b2z].
      + (* [comment removed for export] *)
        rewrite (eqb_lits_false 1 0) by lia. cbv iota.
        destruct (split_at8 bufdata 8 ltac:(lia)) as (pre8 & l0 & l1 & r0 & r1 & n0 & n1 & n2 & n3 & post & Ebuf & Lpre8).
        assert (GX : (0 <= l0 < 256 /\ 0 <= l1 < 256 /\ 0 <= r0 < 256 /\ 0 <= r1 < 256 /\ 0 <= n0 < 256 /\ 0 <= n1 < 256 /\ 0 <= n2 < 256 /\ 0 <= n3 < 256)%Z).
        { rewrite Ebuf in GRD. apply Forall_app in GRD as [_ GB].
          pose proof (Forall_inv GB) as X0. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X1. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X2. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X3. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X4. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X5. apply Forall_inv_tail in GB.
          pose proof (Forall_inv GB) as X6. apply Forall_inv_tail in GB. pose proof (Forall_inv GB) as X7.
          cbv beta in X0, X1, X2, X3, X4, X5, X6, X7. lia. }
        destruct GX as (L0 & L1 & R0' & R1' & N0 & N1 & N2 & N3).
        pose proof PFX as PFX0. rewrite Ebuf in PFX0.
        change (pre8 ++ l0 :: l1 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l0; l1; r0; r1; n0; n1; n2; n3] ++ post) in PFX0.
        destruct (pfx_decomp pre8 [l0; l1; r0; r1; n0; n1; n2; n3] post bs PFX0) as (bsr & Ebs & PFXr). cbn [map] in Ebs.
        pose proof BUF4 as BX. rewrite Ebs in BX.
        assert (Lbsr : (length pre8 + 8 + length bsr = Z.to_nat bufalloc)%nat).
        { pose proof (proj1 (proj1 BX)) as WF. cbn in WF. rewrite !length_app, length_map in WF. cbn in WF. lia. }
        pose proof (rw_cells_recell _ _ _ [CB (length pre8) (map b8 pre8); C2 (Z_to_bv 64 (l0 + 256 * l1)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (length bsr) bsr] BX
                      ltac:(cbn; rewrite length_map; repeat split; fastfirst (first [reflexivity | lia]))
                      ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit, le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
        destruct (rw_cells_cut _ _ _ 1 BX') as [HB0 BX2]. destruct (rw_cells_cut _ _ _ 3 BX2) as [HX HBR]. clear BX BX' BX2 BUF4.
        cbn [firstn skipn cells_size csize Nat.add app] in HB0, HX, HBR. rewrite Lpre8 in HX, HBR.
        replace (B + Z.of_nat 8)%Z with (B + 8)%Z in HX by lia. replace (B + Z.of_nat 8 + Z.of_nat 8)%Z with (B + 16)%Z in HBR by lia.
        hide HD4. hide HCUR4. hide HTL4. hide FRS4. hide ERR4. hide MG4. hide HEB4. hide CELLS. hide NG4. hide HB0. hide HBR.
        eapply evt_cut.
        { eapply (idb_swap_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (B + 8)%Z l0 l1 r0 r1 n0 n1 n2 n3);
            [assumption | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | reflexivity | exact HX]. }
        cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & z4 & z5 & m6 & -> & MU6 & WM6 & MI6 & HX6). clear HX.
        assert (AGS56 : agrees_on (fun a => outside [(B + 8, B + 8 + 8)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        assert (ST6 : stk ssegs m6 lo (bv_unsigned sp + -128)).
        { eapply stk_transport_disjoint; [eassumption | exact MU6 | exact WM6 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
        assert (G6 : GIo K R ps4 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m6).
        { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. right. apply ngl_iv_B; lia. }
        assert (AG6 : AGQ m6).
        { unfold ngc_AGQ in AG5 |- *. eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS56|].
          intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB a Ha). lia. }
        assert (HIF6 : ifaces_ok (pL qb bufalloc (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i) I m6).
        { assert (HIF' : ifaces_ok (pL qb bufalloc (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i) I m5) by exact HIF5.
          eapply ifaces_ok_agree; [exact AGS56 | | exact HIF']. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E. destruct (API sg' q E) as (I1 & I4 & IP & IB). cbn [outside]. lia. }
        unhide HD4. unhide HCUR4. unhide HTL4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4. unhide CELLS. unhide NG4. unhide HB0. unhide HBR.
        transport HD4 m6 AGS56 ltac:(prs). transport HCUR4 m6 AGS56 ltac:(unfold cursor_cells; prs). transport HTL4 m6 AGS56 ltac:(prs). transport FRS4 m6 AGS56 ltac:(prs).
        transport ERR4 m6 AGS56 ltac:(prs). transport MG4 m6 AGS56 ltac:(prsMG GL). transport HEB4 m6 AGS56 ltac:(prs).
        transport CELLS m6 AGS56 ltac:(prs). transport NG4 m6 AGS56 ltac:(unfold ng_cells; prs).
        transport HB0 m6 AGS56 ltac:(prs). transport HBR m6 AGS56 ltac:(prs).
        assert (BUF6 : rw_cells ssegs m6 B [CB (Z.to_nat bufalloc) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr)]).
        { replace (B + 8)%Z with (B + Z.of_nat (cells_size [CB (length pre8) (map b8 pre8)]))%Z in HX6 by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ HB0 HX6 ltac:(cbn; lia)) as J1.
          replace (B + 16)%Z with (B + Z.of_nat (cells_size ([CB (length pre8) (map b8 pre8)] ++ [C2 (Z_to_bv 64 (l1 + 256 * l0)); C2 (Z_to_bv 64 (r0 + 256 * r1)); C4 (Z_to_bv 64 (le4val n3 n2 n1 n0))])))%Z in HBR by (cbn; lia).
          pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR ltac:(cbn; lia)) as J2. cbn [app] in J2.
          eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; repeat split; try exact Logic.I; lia |].
          cbn [cells_bytes cbytes app]. rewrite !le2_lit, le4_lit by lia. rewrite !app_nil_r, <- ?app_assoc. cbn [app]. lazymatch goal with |- ?GG => first [reflexivity | fail 0 GG] end. }
        assert (EQSW : swap_field 4 12 (swap_field 2 8 bufdata) = pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post).
        { rewrite Ebuf. replace 8%Z with (Z.of_nat (length pre8)) by lia. rewrite swap2_at.
          change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n0 :: n1 :: n2 :: n3 :: post) with (pre8 ++ [l1; l0; r0; r1] ++ n0 :: n1 :: n2 :: n3 :: post). rewrite app_assoc.
          replace 12%Z with (Z.of_nat (length (pre8 ++ [l1; l0; r0; r1]))) by (rewrite length_app; cbn; lia). rewrite swap4_at, <- app_assoc. reflexivity. }
        rewrite EQSW.
        change (set_bufdata (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (ngc_p f qs true BS0 MINOR qb bufalloc bufdata sg i))
          with (ngc_p f qs true BS0 MINOR qb bufalloc (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) sg i).
        eapply (CALL _ _ _ _ _ _ m6 (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr));
          [ symmetry; exact EQSW
          | exact MI6 | exact ST6 | exact AG6 | exact G6 | exact HD4 | exact HCUR4 | exact HTL4 | exact FRS4 | exact ERR4 | exact MG4 | exact HEB4 | exact CELLS | exact NG4
          | exact HIF6 | exact BUF6
          | change (pre8 ++ l1 :: l0 :: r0 :: r1 :: n3 :: n2 :: n1 :: n0 :: post) with (pre8 ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ post);
            replace (map b8 pre8 ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ bsr) with (map b8 pre8 ++ map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ bsr) by reflexivity;
            apply pfx_comp; exact PFXr
          | rewrite Ebuf, !length_app; cbn [length]; lia
          | rewrite Ebuf in GRD; apply Forall_app in GRD as [GA GB]; apply Forall_app; split; [exact GA|]; do 8 (apply Forall_inv_tail in GB); repeat (constructor; [cbv beta; lia|]); exact GB ].
      + (* [comment removed for export] *)
        rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
        eapply (CALL _ _ _ _ _ _ m5 bufdata bs);
          [ reflexivity | assumption | assumption | exact AG5 | exact G5 | exact HD4 | exact HCUR4 | exact HTL4 | exact FRS4 | exact ERR4 | exact MG4 | exact HEB4 | exact CELLS | exact NG4
          | exact HIF5 | exact BUF4 | exact PFX | reflexivity | exact GRD ].
  Qed.
  End Sz6.
  Lemma ngc_idb : ltac:(let t := eval cbv delta [ngc_idb__stmt] in ngc_idb__stmt in exact t).
  Proof using AI BS0R CTX FREE HFL HPL MINR P14 P16 SFL SNPRINTF. intros fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x8 m4 ps4 qb B bufalloc bufdata sg i I pad bs e cpad j0 j1 c. ltac2:(SecDiet.SzSec.closeP 'ngc_idb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgC.

End WithCeil.
End F_sfpcapng_chkC.
