(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: drain's three literal facts HLIT5 / HLIT6 / HLIT7 (W_drain_cx_x.v Section c, lines 171-173
   at 645f80c7a8c; dlit_at_x is the Definition at lines 166-170) at the instance of A's top_x: PI := PB_fr,
   ARx := top_x's ARX (W_LLVMFuzzerTestOneInput_top_x.v:189, written out here as the same relation, as
   W_shadow_pin_x.v's ashp_str2_1_fr_cf does, so this file does not Require top_x), B := TfibB (B is not an argument of
   dlit_at_x: its three conjuncts read SEGS, VAL and ARx only).
     topx_HLIT5_x : dlit_at_x ARX 21 (K_GESTURE ++ [0])   .str.5 "param_gesture\0" at 0x20f20, 14 bytes
     topx_HLIT6_x : dlit_at_x ARX 23 (W_BEGIN ++ [0])     .str.6 "begin\0"         at 0x20f40,  6 bytes
     topx_HLIT7_x : dlit_at_x ARX 24 (W_END ++ [0])       .str.7 "end\0"           at 0x20f60,  4 bytes
   Each lemma's type is the hypothesis text at that instance, so pb_drain_x's HLIT5 / 6 / 7 close by
   `exact topx_HLIT5_x` (ARX unfolds to the relation written here).
   The conjuncts:
   - bytes and in_rom: dlit_romb decides, over the image's own segment table frsegs (= Asan.M.loaded_segments, the
     segments of fuzz_reply.asan, sha256 42c58610e125e0b4...), that each byte of the literal reads as the list's byte
     and lies in a read-only segment; dlit_romb_ok turns the decision into the two conjuncts.  Decided by vm_compute
     on closed terms outside the Section (no Section variable reaches vm_compute).
   - ashp: W_shadow_pin_x.v's ashp_gesture_14_fr_x / ashp_begin_6_fr_x / ashp_end_4_fr_x over ARX, whose laws are
     top_x's ARX_laws (restated as topx_dlit_ARX_laws, the proof of top_x.v:163).
   Numerals (each against fuzz_reply.asan itself; numerals_a.py (sha256 7a4f1e9eedd3; internal record) of the lane):
     A_OBJ 21 / 23 / 24 = 0x20f20 / 0x20f40 / 0x20f60 (W_place.v fr_obj 21 / 23 / 24; ASan global descriptors at
       0xa23e0 / 0xa2420 / 0xa2460 of section asan_globals name .str.5 / .str.6 / .str.7 with sizes 14 / 6 / 4 and
       size_with_redzone 32; section .rodata in the unstripped twin);
     bytes: 0x20f20.. = 112 97 114 97 109 95 103 101 115 116 117 114 101 0, 0x20f40.. = 98 101 103 105 110 0,
       0x20f60.. = 101 110 100 0 (RelayModel.v K_GESTURE / W_BEGIN / W_END, each ++ [0]);
     ROM segment: PT_LOAD 0 of the ELF, vaddr 0x10000 memsz 0x1f994 flags R (not writable); frsegs' first segment is
       base 0x10000 size 0x20000 not writable; [0x20f20, 0x20f64) lies in both;
     shadow (AF0m.Tfib_const_shadow / Tfib_zero_shadow, = ASan's poisoning of the descriptors above): 0x7fffc1e4 = 0
       (zero-shadow range (0x20f20, 8)), 0x7fffc1e5 = 6, 0x7fffc1e8 = 6, 0x7fffc1ec = 4; the hulls' other bytes
       0x7fffc1e0 = 5 (.str.4), 0x7fffc1e1-e3 / e6-e7 / e9-eb / ed-ef = 0xf9 (redzones).
   SATISFIABILITY (VERIFY rule 10): the only premise is ARX inside ashp_x.  ARX holds at the start-up hand-off state:
   AD1pcf.v:148 proves ARcf TSEGS B ly init_state [] W' FULL model by Reusable/YGcfNilInit.v:96 ARcf_nil_init from the
   start-up AR, with Hp = [] (B := TfibB by ReplyTFIBcf.v; ReplyDriverCf.v runs the driver at cp := CfParams_reply);
   so ashp_x's premise is met there and the first two conjuncts hold outright.
   proves no function (kind: image facts of the instance). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_place W_kit W_img W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_shadow_pin_x W_drain_cx_x.
(* the zify flag as this file's proofs expect it, whatever a Required file leaves (YCbqG / W_contract_x Require
   FCiface; cut_x.v:55's form) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the bytes and the read-only placement of a literal, decided over frsegs ---- *)
Definition dlit_romb (base : Z) (l : list Z) : bool :=
  forallb (fun j =>
    existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? base + Z.of_nat j) &&
      (base + Z.of_nat j <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) frsegs &&
    match seg_rom frsegs (Z_to_bv 64 (base + Z.of_nat j)), nth_error l j with
    | Some b, Some z => bv_unsigned b =? bv_unsigned (Z_to_bv 8 z)
    | _, _ => false
    end)
  (seq 0 (length l)).

Lemma dlit_romb_ok : forall base l, dlit_romb base l = true ->
  (forall k, (k < length l)%nat ->
     seg_rom frsegs (Z_to_bv 64 (base + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
  (forall x, base <= x < base + Z.of_nat (length l) -> YG0d.in_rom frsegs x).
Proof.
  intros base l H. unfold dlit_romb in H. rewrite forallb_forall in H. split.
  - intros k Hk. specialize (H k ltac:(apply in_seq; lia)). apply andb_prop in H as [_ H].
    destruct (seg_rom frsegs (Z_to_bv 64 (base + Z.of_nat k))) as [b|]; [|discriminate H].
    destruct (nth_error l k) as [z|]; [|discriminate H].
    apply Z.eqb_eq in H. cbn [option_map]. f_equal. apply bv_eq. exact H.
  - intros x Hx. specialize (H (Z.to_nat (x - base)) ltac:(apply in_seq; lia)).
    apply andb_prop in H as [H _]. rewrite Z2Nat.id in H by lia.
    replace (base + (x - base)) with x in H by lia.
    apply existsb_exists in H as (sg & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
    apply Bool.negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    unfold YG0d.in_rom. exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.

(* the placement (W_place.v fr_obj) and the three decisions, on closed terms *)
Lemma dlit_vals : fr_val (A_OBJ 21) = 0x20f20 /\ fr_val (A_OBJ 23) = 0x20f40 /\ fr_val (A_OBJ 24) = 0x20f60.
Proof. vm_compute. repeat split. Qed.
Lemma dlit_rom21 : dlit_romb 0x20f20 (K_GESTURE ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_rom23 : dlit_romb 0x20f40 (W_BEGIN ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_rom24 : dlit_romb 0x20f60 (W_END ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.

Section topx_dlit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* top_x.v:161 Definition ARX, the same relation *)
#[local] Abbreviation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []).

(* top_x.v:163 ARX_laws, restated (same proof) *)
Lemma topx_dlit_ARX_laws : AR_laws_x segs TfibB ARX (@cf_head CfParams_reply).
Proof.
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* HLIT5 (W_drain_cx_x.v:199) *)
Lemma topx_HLIT5_x : W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX 21 (K_GESTURE ++ [0]).
Proof.
  unfold W_drain_cx_x.dlit_at_x. split; [|split].
  - change (VAL (A_OBJ 21)) with (fr_val (A_OBJ 21)). rewrite (proj1 dlit_vals).
    exact (proj1 (dlit_romb_ok _ _ dlit_rom21)).
  - change (VAL (A_OBJ 21)) with (fr_val (A_OBJ 21)). rewrite (proj1 dlit_vals).
    exact (proj2 (dlit_romb_ok _ _ dlit_rom21)).
  - change (Z.of_nat (length (K_GESTURE ++ [0]))) with 14.
    exact (W_shadow_pin_x.ashp_gesture_14_fr_x TfibB TfibB_syms ARX topx_dlit_ARX_laws).
Qed.

(* HLIT6 (W_drain_cx_x.v:200) *)
Lemma topx_HLIT6_x : W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX 23 (W_BEGIN ++ [0]).
Proof.
  unfold W_drain_cx_x.dlit_at_x. split; [|split].
  - change (VAL (A_OBJ 23)) with (fr_val (A_OBJ 23)). rewrite (proj1 (proj2 dlit_vals)).
    exact (proj1 (dlit_romb_ok _ _ dlit_rom23)).
  - change (VAL (A_OBJ 23)) with (fr_val (A_OBJ 23)). rewrite (proj1 (proj2 dlit_vals)).
    exact (proj2 (dlit_romb_ok _ _ dlit_rom23)).
  - change (Z.of_nat (length (W_BEGIN ++ [0]))) with 6.
    exact (W_shadow_pin_x.ashp_begin_6_fr_x TfibB TfibB_syms ARX topx_dlit_ARX_laws).
Qed.

(* HLIT7 (W_drain_cx_x.v:201) *)
Lemma topx_HLIT7_x : W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX 24 (W_END ++ [0]).
Proof.
  unfold W_drain_cx_x.dlit_at_x. split; [|split].
  - change (VAL (A_OBJ 24)) with (fr_val (A_OBJ 24)). rewrite (proj2 (proj2 dlit_vals)).
    exact (proj1 (dlit_romb_ok _ _ dlit_rom24)).
  - change (VAL (A_OBJ 24)) with (fr_val (A_OBJ 24)). rewrite (proj2 (proj2 dlit_vals)).
    exact (proj2 (dlit_romb_ok _ _ dlit_rom24)).
  - change (Z.of_nat (length (W_END ++ [0]))) with 4.
    exact (W_shadow_pin_x.ashp_end_4_fr_x TfibB TfibB_syms ARX topx_dlit_ARX_laws).
Qed.
End topx_dlit.
