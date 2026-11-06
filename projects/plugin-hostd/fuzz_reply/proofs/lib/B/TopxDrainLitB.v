(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: drain's three literal facts HLIT5 / HLIT6 / HLIT7 (lib/B/W_drain_cx_x.v Section c, lines
   193-195 at c24ce76b828; dlit_at_x is the Definition at lines 187-191, A's W_drain_cx_x.v:172-176 word for word) at
   the instance of image B's top_x (fuzz_reply.asan-ubsan): PI := PB_fr (lib/B/W_img.v), ARx := B top_x's ARX
   (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:162-163, written out here as the same relation, so this file does not
   Require top_x), B := TfibB (B is not an argument of dlit_at_x: its three conjuncts read SEGS, VAL and ARx only).
   B's literal objects are A_OBJ 18 / 20 / 21 (A's are 21 / 23 / 24):
     topx_HLIT5_x : dlit_at_x ARX 18 (K_GESTURE ++ [0])   .str.6 "param_gesture\0" at 0x20f20, 14 bytes
     topx_HLIT6_x : dlit_at_x ARX 20 (W_BEGIN ++ [0])     .str.7 "begin\0"         at 0x20f40,  6 bytes
     topx_HLIT7_x : dlit_at_x ARX 21 (W_END ++ [0])       .str.8 "end\0"           at 0x20f60,  4 bytes
   Each lemma's type is the hypothesis text at that instance, so Section c's HLIT5 / 6 / 7 close by
   `exact topx_HLIT5_x` (ARX unfolds to the relation written here).
   The conjuncts:
   - bytes and in_rom: dlit_romb decides, over image B's own segment table frsegs (lib/B/W_tbl.v,
     AsanUbsan.M.loaded_segments), that each byte of the literal reads as the list's byte and lies in a read-only
     segment; dlit_romb_ok turns the decision into the two conjuncts.  vm_compute runs on closed terms only.
   - ashp: lib/B/TopxImageB.v's tfib_shp_x (the shadow check over image B's start-up tables YF0m.Tfib_const_shadow /
     Tfib_zero_shadow), its two law premises read from ARcf's first conjunct ARmcf (YG0ncf.v amc_const /
     amc_zshadow), as TopxImageB.v's ashp_str3_1_fr_cf does.  No AR_laws_x record and no off-image fact of the YCbq
     carry (its image top is image A's) is used.
   Numerals (each against fuzz_reply.asan-ubsan itself, sha256 10ffb5f9202ae2bd...; numerals_b.py (sha256 a5b7ea16a634; internal record) of the lane):
     A_OBJ 18 / 20 / 21 = 0x20f20 / 0x20f40 / 0x20f60 (lib/B/W_place.v fr_obj 18 / 20 / 21; ASan global descriptors at
       0xa2960 / 0xa29a0 / 0xa29e0 of section asan_globals, names .str.6 / .str.7 / .str.8, sizes 14 / 6 / 4,
       size_with_redzone 32; section .rodata in the unstripped twin);
     bytes: 0x20f20.. = 112 97 114 97 109 95 103 101 115 116 117 114 101 0, 0x20f40.. = 98 101 103 105 110 0,
       0x20f60.. = 101 110 100 0 (lib/Prog/RelayModel.v K_GESTURE / W_BEGIN / W_END, each ++ [0]);
     ROM segment: the ELF's first PT_LOAD, vaddr 0x10000 memsz 0x1f9ec flags R (not writable); frsegs' first segment
       starts at 0x10000 and is not writable (dlit_rom_seg_b); [0x20f20, 0x20f64) lies in both;
     shadow (lib/B/YF0m.v Tfib_const_shadow / Tfib_zero_shadow, = ASan's poisoning of the descriptors above):
       0x7fffc1e4 = 0 (zero-shadow range (0x20f20, 8)), 0x7fffc1e5 = 6, 0x7fffc1e8 = 6, 0x7fffc1ec = 4; the hulls'
       other bytes 0x7fffc1e0 = 5 (.str.5 at 0x20f00, size 5), 0x7fffc1e1-e3 / e6-e7 / e9-eb / ed-ef = 0xf9.
   SATISFIABILITY (VERIFY rule 10): the only premise is ARX inside ashp_x.  B's ARX holds at the start-up hand-off
   state: lib/B/YD1pcf.v:133 proves ARcf TSEGS B ly init_state [] W' FULL model by Reusable/YGcfNilInit.v:96
   ARcf_nil_init from the start-up AR, with Hp = [] (B := TfibB by lib/B/ReplyTFIBBcf.v), so ashp_x's premise is met
   there and the first two conjuncts hold outright.
   proves no function (kind: image facts of the instance). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_tbl W_place W_kit W_img W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m.
(* B's ashp_x, and the ARX instance (B top_x Requires lib/A's CfParamsReply, Reusable YG0ncf) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
(* the zify flag as this file's proofs expect it, whatever a Required file leaves (W_contract_x Requires FCiface) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the bytes and the read-only placement of a literal, decided over image B's frsegs ---- *)
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

(* image B's placement (lib/B/W_place.v fr_obj 18 / 20 / 21), its read-only segment, and the decisions, on closed
   terms (a wrong object index or image fails here) *)
Lemma dlit_vals_b : fr_val (A_OBJ 18) = 0x20f20 /\ fr_val (A_OBJ 20) = 0x20f40 /\ fr_val (A_OBJ 21) = 0x20f60.
Proof. vm_compute. repeat split. Qed.
Lemma dlit_rom_seg_b : hd_error (map (fun s => (seg_writable s, Z.of_N (seg_base s))) frsegs) = Some (false, 0x10000).
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_rom18 : dlit_romb 0x20f20 (K_GESTURE ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_rom20 : dlit_romb 0x20f40 (W_BEGIN ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_rom21 : dlit_romb 0x20f60 (W_END ++ [0]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_shp18 : shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow 0x20f20 14 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_shp20 : shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow 0x20f40 6 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dlit_shp21 : shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow 0x20f60 4 = true.
Proof. vm_compute. reflexivity. Qed.

Section topx_dlit_b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* B lib/B/W_LLVMFuzzerTestOneInput_top_x.v:177-179 Definition ARX, the same relation (W1: its third conjunct, image B's arodata_ok_cf) *)
#[local] Abbreviation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem).

(* ashp at ARX from a decided shadow check: TopxImageB.v's tfib_shp_x, the laws from ARmcf (ashp_str3_1_fr_cf's) *)
Lemma topx_dlit_ashp_b : forall a n,
  shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow a n = true -> ashp_x (PI := PB_fr) ARX a n.
Proof.
  intros a n H. apply (TopxImageB.tfib_shp_x TfibB TfibB_syms _); [| | exact H].
  - intros ly S Hp W mem md ((M & _) & _). exact (amc_const _ _ _ _ _ M).
  - intros ly S Hp W mem md r ((M & _) & _) Hr. exact (proj1 (Forall_forall _ _) (amc_zshadow _ _ _ _ _ M) r Hr).
Qed.

(* HLIT5 (lib/B/W_drain_cx_x.v:199) *)
Lemma topx_HLIT5_x : W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX 18 (K_GESTURE ++ [0]).
Proof.
  unfold W_drain_cx_x.dlit_at_x.
  change (VAL (A_OBJ 18)) with (fr_val (A_OBJ 18)). rewrite (proj1 dlit_vals_b).
  split; [|split].
  - exact (proj1 (dlit_romb_ok _ _ dlit_rom18)).
  - exact (proj2 (dlit_romb_ok _ _ dlit_rom18)).
  - change (Z.of_nat (length (K_GESTURE ++ [0]))) with 14. exact (topx_dlit_ashp_b _ _ dlit_shp18).
Qed.

(* HLIT6 (lib/B/W_drain_cx_x.v:200) *)
Lemma topx_HLIT6_x : W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX 20 (W_BEGIN ++ [0]).
Proof.
  unfold W_drain_cx_x.dlit_at_x.
  change (VAL (A_OBJ 20)) with (fr_val (A_OBJ 20)). rewrite (proj1 (proj2 dlit_vals_b)).
  split; [|split].
  - exact (proj1 (dlit_romb_ok _ _ dlit_rom20)).
  - exact (proj2 (dlit_romb_ok _ _ dlit_rom20)).
  - change (Z.of_nat (length (W_BEGIN ++ [0]))) with 6. exact (topx_dlit_ashp_b _ _ dlit_shp20).
Qed.

(* HLIT7 (lib/B/W_drain_cx_x.v:201) *)
Lemma topx_HLIT7_x : W_drain_cx_x.dlit_at_x (PI := PB_fr) ARX 21 (W_END ++ [0]).
Proof.
  unfold W_drain_cx_x.dlit_at_x.
  change (VAL (A_OBJ 21)) with (fr_val (A_OBJ 21)). rewrite (proj2 (proj2 dlit_vals_b)).
  split; [|split].
  - exact (proj1 (dlit_romb_ok _ _ dlit_rom21)).
  - exact (proj2 (dlit_romb_ok _ _ dlit_rom21)).
  - change (Z.of_nat (length (W_END ++ [0]))) with 4. exact (topx_dlit_ashp_b _ _ dlit_shp21).
Qed.
End topx_dlit_b.
