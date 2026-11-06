(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the generic half of the bridge from a Bz body walk (lib/A/Bz, relocated onto
   fuzz_reply.asan) to the W_sites.v runtime site contracts, for every runtime lane of fuzz_reply. *)
(* Modified by Theorem Labs, 2026-10: the comments of fr_rt_rest and FrRtCells corrected: the generated AF0m.v (sha256 007c9a7eb8b9; internal record) holds all 14 cells of fr_rt_rest, and RT_kit_cells_x.FrRtCells_of_syms / FrRtCells_x_of_syms discharge FrRtCells / FrRtCells_x (comments only). *)
(* Ported from: a working branch 3210d71ee38 proofs/omx-clap-core/fuzz_state/lib/A/FSstrlen.v:90-750
   (a Theorem Labs lane's bridge, itself from a Theorem Labs lane's FMbz_bridge / FMbz_str and a Theorem Labs lane's MemNorm / RegisterBridge).
   Changes (R1Str, 2026-10-29):
   - fuzz_state.asan -> fuzz_reply.asan: Img0.rsegs is lib/A/Img0.v (the ASan segments, NOT lib/Img0.v, which is the
     plain image); FR_IMG_TOP 0x600000 is above fuzz_reply.asan's image end 0x5fb000 (rsegs_below decides it);
   - U-free: the W_sites forms carry no user-poisoned ranges, so ecall_preU_k / ARU / unpoison are gone;
   - the post (aentry_post_of_walk) and the transport lemmas (bz_transport, chk_norm, stk_norm_high, the cell
     agreement and ro->rw lemmas, the register lemmas) are R3Mem's lib/A/RT_post.v, taken from the same FSstrlen.v by
     agreement so that there is one copy; this file keeps the byte-list lemmas the string walks need and the cells;
   - the runtime cells are fuzz_reply.asan's, named premises FrShadowSyms (the shadow cell and its GOT slot) and
     FrRtCells (the rest), both facts about B's constant cells; FrRtCells holds the memmove cells R3 needs too.
   The fuzz_state -> fuzz_reply address table of the relocated Bz tree (fs.asan sha 64b53ff86172 -> fuzz_reply.asan),
   every code numeral paired by code (relocation fields masked, unique match over .text), every data numeral by the
   instruction that loads it, values from fuzz_reply.asan's .got and the generated AF0m (a working branch):
   trampolines strcmp 0x4265c->0x42198, memchr 0x4266c->0x421b0; ___interceptor_strlen 0x426e4->0x42230,
   _strnlen 0x42978->0x424c4, _strcmp 0x42c10->0x42a6c, _memchr 0x43e30->0x44548 (inner pcs shifted with them);
   MemToShadow copies 0x52dc8->0x53b40, 0x54758->0x554d0, 0x5d644->0x5e454; __asan_region_is_poisoned
   0x54be4->0x5595c; AsanInited 0x59168->0x59ee0; TryAsanInitFromRtl 0x5a078->0x5adf0; mem_is_zero 0x64924->0x65734;
   musl bcmp 0x98920->0x963cc, memchr 0x98924->0x963d0, memcmp 0x989f0->0x9649c, strlen 0x99070->0x96b4c,
   strnlen 0x992ac->0x96e48; GOT common_flags 0x9f6e0->0x9d9c0, shadow cell 0x9f6f0->0x9d9d0, kMidMemBeg/End,
   kHighMemEnd 0x9f6f8/0x9f700/0x9f708->0x9d9d8/0x9d9e0/0x9d9e8; shadow cell 0xa7f38->0xa60b8; asan_inited
   0xa8c18->0xa6d98; kHighMemEnd/kMidMemBeg/kMidMemEnd 0xa8c20/28/30->0xa6da0/a8/b0; REAL(strlen/memchr/strnlen)
   0xa1408/0xa1430/0xa1518->0x9f6e8/0x9f728/0x9f818; common_flags 0x139a68->0x137be8 (+0xf5/+0xfa/+0xfb);
   image end 0x5fd000->0x5fb000. Unchanged (same code, same constant): 0x7fff8000, 0x7fff7fff, 0x10007fff8000,
   0x10007fff7fff, 0x7fffffffffff. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strcmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strlen.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v W_syms W_listing W_kit W_tbl W_place W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FRbz_str RT_post.
(* the ARx-generic twins (fuzz_reply.runtime_twins) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import RTx.
(* RTx Requires FCiface -> YF0v, which sets Zify's euclidean-division flag to false globally; restore the value the
   header above ended with (true, W_sites' chain), which this file's importers' lia expect. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module I0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Module BM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Module BD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.D_kit.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module BN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Module BS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strcmpw.
Module BL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strlen.
Module BMC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memchrw.
Module YCbq := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.
Module FSS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRbz_str.
Module RP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_post.

(* the image's W^X fact, which FRbz_bridge.srr_of_evt takes as a premise *)
Lemma Hwx_fr : wx_segs_nowrap frsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* the string's bytes, its NUL and the rest of the NUL's 8-byte word *)
Definition byte_at (m : word -> option byte) (a : Z) : byte :=
  match BM.mrd BI.asegs m (BM.wa a) with Some b => b | None => Z_to_bv 8 0 end.
Definition mk_slack (m : word -> option byte) (e : Z) (k : nat) : list byte :=
  map (fun j => byte_at m (e + Z.of_nat j)) (seq 0 k).
Definition slack_len (e : Z) : nat := Z.to_nat ((- e) mod 8).

Lemma length_mk_slack : forall m e k, length (mk_slack m e k) = k.
Proof. intros. unfold mk_slack. rewrite length_map, length_seq. reflexivity. Qed.

Lemma le_byte_1 : forall v, 0 <= v < 256 -> Z_to_bv 8 (le_byte v 1 0) = Z_to_bv 8 v.
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

Lemma nth_mk_slack : forall m e k i, (i < k)%nat -> nth_error (mk_slack m e k) i = Some (byte_at m (e + Z.of_nat i)).
Proof.
  intros m e k i Hi. unfold mk_slack. rewrite nth_error_map, nth_error_seq.
  replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
Qed.

Lemma map_seq_shift : forall (f : Z -> byte) a b,
  map (fun j => f (Z.of_nat j)) (seq a b) = map (fun j => f (Z.of_nat a + Z.of_nat j)) (seq 0 b).
Proof.
  intros f a b. revert a. induction b as [|b IH]; intros a; [reflexivity|].
  cbn [seq map]. rewrite (IH (S a)). rewrite <- seq_shift, map_map.
  f_equal; [f_equal; lia|]. apply map_ext. intros j. f_equal. lia.
Qed.

Lemma mk_slack_app : forall m e a b, mk_slack m e (a + b) = mk_slack m e a ++ mk_slack m (e + Z.of_nat a) b.
Proof.
  intros m e a b. unfold mk_slack. rewrite seq_app, map_app. f_equal.
  etransitivity; [apply (map_seq_shift (fun z => byte_at m (e + z)))|].
  apply map_ext. intros j. f_equal. lia.
Qed.

(* the bytes [x, x + k) the walk reads, each visible to the donor's reader, as a Bz byte list *)
Lemma bytes_at_mk : forall (H : word -> bool) mem x k,
  0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
  (forall a, x <= a < x + Z.of_nat k -> aview frsegs H mem a <> None) ->
  BM.bytes_at BI.asegs (mrestrict H mem) x (mk_slack (mrestrict H mem) x k).
Proof.
  intros H mem x k Hx Hk Hv. split; [exact Hx|]. split; [rewrite length_mk_slack; exact Hk|].
  intros i Hi. rewrite length_mk_slack in Hi. rewrite nth_mk_slack by exact Hi. unfold byte_at.
  assert (V : aview frsegs H mem (x + Z.of_nat i) <> None) by (apply Hv; lia).
  unfold aview in V. rewrite FSS.mbyte_mrd in V.
  destruct (BM.mrd BI.asegs (mrestrict H mem) (BM.wa (x + Z.of_nat i))) as [b|]; [reflexivity | exfalso; apply V; reflexivity].
Qed.

(* a byte the donor's reader sees with value v is the byte the walk reads *)
Lemma byte_at_view : forall (H : word -> bool) mem a v, aview frsegs H mem a = Some v ->
  byte_at (mrestrict H mem) a = Z_to_bv 8 v /\ 0 <= v < 256.
Proof.
  intros H mem a v Hv. unfold aview in Hv. rewrite FSS.mbyte_mrd in Hv. unfold byte_at.
  destruct (BM.mrd BI.asegs (mrestrict H mem) (BM.wa a)) as [b|]; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-. split; [symmetry; apply Z_to_bv_bv_unsigned|].
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* bytes of value v <> 0 are not the NUL byte *)
Lemma bv8_ne0 : forall v, 0 <= v < 256 -> v <> 0 -> Z_to_bv 8 v <> Z_to_bv 8 0.
Proof.
  intros v Hv H0 E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite (Z.mod_small v 256), Z.mod_0_l in E by lia. lia.
Qed.


(* the shadow cell and its GOT slot (FrShadowSyms, from AR_const_law): .got 0x9d9d0 holds 0xa60b8,
   __asan_shadow_memory_dynamic_address, which holds the shadow offset *)
Definition fr_tl_cells (m : word -> option byte) : Prop :=
  BSt.ro_cells BI.asegs m 0x9d9d0 [BC.C8 (Z_to_bv 64 0xa60b8)] /\
  BSt.ro_cells BI.asegs m 0xa60b8 [BC.C8 (Z_to_bv 64 0x7fff8000)].

(* the rest (the named premise FrRtCells), fuzz_reply.asan's cells: .got 0x9d9c0 = common_flags 0x137be8, .got
   0x9d9d8.. = kMidMemBeg 0xa6da8 / kMidMemEnd 0xa6db0 / kHighMemEnd 0xa6da0, REAL(strlen) 0x9f6e8 = 0x96b4c,
   REAL(memchr) 0x9f728 = 0x963d0, REAL(strnlen) 0x9f818 = 0x96e48, asan_inited 0xa6d98 = 1, kHighMemEnd /
   kMidMemBeg / kMidMemEnd at 0xa6da0.., the common_flags bytes +0xf5 = 0x137cdd (strict_string_checks) = 0,
   +0xfa = 0x137ce2 (intercept_strcmp) = 1, +0xfb = 0x137ce3 (intercept_strlen) = 1, for __asan_memmove (R3)
   .got 0x9e538 = 0xa6d99 (replace_intrin_cached) and 0xa6d99 = 1, and for strrchr (R2) common_flags + 0xfd =
   0x137ce5 (intercept_strchr) = 1 and REAL(strrchr) 0x9f710 = 0x96e8c.  The values are start-up state; the
   generated AF0m's Tfib_const (AF0m.v sha256 007c9a7eb8b9; internal record) holds all 14 cells: 13 are rows (REAL(strlen) 0x9f6e8 at
   AF0m.v:444; REAL(strrchr) 0x9f710 at AF0m.v:447, row index 405 of Tfib_const_abs), and 0x137ce5 is byte 5 of the
   row 0x137ce0 = 0x0101010101010101.  So FrRtCells is dischargeable: RT_kit_cells_x.FrRtCells_of_syms gives it from
   AR_laws and TfibSyms (RT_kit_cells_x.FrRtCells_x_of_syms gives FrRtCells_x from rt_laws and TfibSyms); the twins
   in RT_*_x.v carry no cell premise. *)
Definition fr_rt_rest (m : word -> option byte) : Prop :=
  BSt.ro_cells BI.asegs m 0x9d9c0 [BC.C8 (Z_to_bv 64 0x137be8)] /\
  BSt.ro_cells BI.asegs m 0x9d9d8 [BC.C8 (Z_to_bv 64 0xa6da8); BC.C8 (Z_to_bv 64 0xa6db0); BC.C8 (Z_to_bv 64 0xa6da0)] /\
  BSt.ro_cells BI.asegs m 0x9f6e8 [BC.C8 (Z_to_bv 64 0x96b4c)] /\
  BSt.ro_cells BI.asegs m 0x9f728 [BC.C8 (Z_to_bv 64 0x963d0)] /\
  BSt.ro_cells BI.asegs m 0x9f818 [BC.C8 (Z_to_bv 64 0x96e48)] /\
  BSt.ro_cells BI.asegs m 0xa6d98 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0xa6da0 [BC.C8 (Z_to_bv 64 BR.kHighMemEnd); BC.C8 (Z_to_bv 64 0); BC.C8 (Z_to_bv 64 0)] /\
  BSt.ro_cells BI.asegs m 0x137cdd [BC.C1 (Z_to_bv 8 0)] /\
  BSt.ro_cells BI.asegs m 0x137ce2 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x137ce3 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x9e538 [BC.C8 (Z_to_bv 64 0xa6d99)] /\
  BSt.ro_cells BI.asegs m 0xa6d99 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x137ce5 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x9f710 [BC.C8 (Z_to_bv 64 0x96e8c)].

(* what the string interceptor walks ask *)
Definition fr_walk_cells (m : word -> option byte) : Prop :=
  BR.m2s_cells m /\ BN.icells_sn m /\ BN.icells_sns m /\ BL.icells_sl m /\ BS.icells_sc m /\
  BSt.ro_cells BI.asegs m 0x137ce2 [BC.C1 (Z_to_bv 8 1)] /\ BMC.icells_mc m.

Ltac cell_ro C :=
  eapply BD.ro_cells_agree; [exact C|]; apply RP.agree_cells; vm_compute; reflexivity.

Lemma fr_tl_norm : forall (H : word -> bool) mem,
  fr_tl_cells (mrestrict H mem) -> fr_tl_cells (NM.normalize_cj I0.rsegs (mrestrict H mem)).
Proof. intros H mem (C1 & C2). split; [cell_ro C1 | cell_ro C2]. Qed.

Lemma fr_rest_norm : forall (H : word -> bool) mem,
  fr_rt_rest (mrestrict H mem) -> fr_rt_rest (NM.normalize_cj I0.rsegs (mrestrict H mem)).
Proof.
  intros H mem (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  split; [cell_ro C1|]. split; [cell_ro C2|]. split; [cell_ro C3|]. split; [cell_ro C4|].
  split; [cell_ro C5|]. split; [cell_ro C6|]. split; [cell_ro C7|]. split; [cell_ro C8|].
  split; [cell_ro C9|]. split; [cell_ro C10|]. split; [cell_ro C11|]. split; [cell_ro C12|].
  split; [cell_ro C13 | cell_ro C14].
Qed.

Ltac cell_rw C := apply RP.rw_of_ro; [exact C | vm_compute; reflexivity | reflexivity].

Lemma fr_walk_cells_of : forall m, fr_tl_cells m -> fr_rt_rest m -> fr_walk_cells m.
Proof.
  intros m (T1 & T2) (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & _ & _ & _ & _).
  assert (G : BSt.ro_cells BI.asegs m 0x9d9d0
    [BC.C8 (Z_to_bv 64 0xa60b8); BC.C8 (Z_to_bv 64 0xa6da8); BC.C8 (Z_to_bv 64 0xa6db0); BC.C8 (Z_to_bv 64 0xa6da0)])
    by (apply RP.ro_cons8; [exact T1 | exact R2]).
  split; [split; [cell_rw G | split; [cell_rw T2 | cell_rw R7]]|].
  split; [split; [exact R1 | split; [exact T1 | split; [exact T2 | split; [cell_rw R6 | exact R10]]]]|].
  split; [exact R5|].
  split; [exact R3|].
  split; [split; [exact R1 | split; [exact T1 | split; [exact T2 | split; [cell_rw R6 | exact R8]]]]|].
  split; [exact R9|].
  split; [exact T1 | split; [exact R4 | split; [exact T2 | cell_rw R6]]].
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* NAMED PREMISE: at every ASan state the restricted memory holds fr_rt_rest, fuzz_reply.asan's runtime cells the
   string walks read beyond FrShadowSyms'.  A fact about B's constant cells (as_const); the relocated core's
   TfibSyms with the generated AF0m discharges it (AF0x.tfib_const_lookup per cell; AF0m.v (sha256 007c9a7eb8b9; internal record) holds
   every cell named in fr_rt_rest's comment): RT_kit_cells_x.FrRtCells_of_syms. *)
Definition FrRtCells (B : asyms) : Prop :=
  forall ly S (W : world frsegs) mem md, AR frsegs B ly S W mem md -> fr_rt_rest (mrestrict (w_H W) mem).

(* NAMED PREMISE: the two symbols of the shadow-offset cell at fuzz_reply.asan's addresses (the walk kit's PALib
   gives both at PB_fr: fr_shadow_of_palib). *)
Definition FrShadowSyms (B : asyms) : Prop := as_got_shadow B = 0x9d9d0 /\ as_shadow_cell B = 0xa60b8.

Lemma fr_shadow_of_palib : forall B, PALib (PI := PB_fr) B -> FrShadowSyms B.
Proof. intros B [Hg Hc _ _ _ _ _]. split; [rewrite Hg | rewrite Hc]; vm_compute; reflexivity. Qed.

(* ---- the cells over a generic allocator relation ARx (its third argument the head set Hp), from the four runtime
   laws rt_laws (lib/Rt/RTx.v). FrRtCells_x is FrRtCells over ARx, a NAMED PREMISE exactly as FrRtCells is: at
   ARx := FCiface.AR_nohp it IS FrRtCells (FrRtCells_x_AR). cgif's AR forms follow as corollaries. ---- *)
Definition FrRtCells_x (B : asyms) (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop)
  : Prop :=
  forall ly S Hp (W : world frsegs) mem md, ARx ly S Hp W mem md -> fr_rt_rest (mrestrict (w_H W) mem).

Lemma FrRtCells_x_AR : forall B, FrRtCells B -> FrRtCells_x B (FCiface.AR_nohp frsegs B).
Proof. intros B H ly S Hp W mem md HAR. exact (H ly S W mem md HAR). Qed.

Lemma tl_cells_x : forall B ARx, FrShadowSyms B -> rt_laws frsegs B ARx -> forall ly S Hp (W : world frsegs) mem md,
  ARx ly S Hp W mem md -> fr_tl_cells (mrestrict (w_H W) mem).
Proof.
  intros B ARx (Egot & Ecell) LAWS ly S Hp W mem md HAR.
  destruct (rtl_const _ _ _ LAWS ly S Hp W mem md HAR) as (C1 & _ & C3 & _).
  rewrite Ecell in C1, C3. rewrite Egot in C3.
  split; apply RP.ro_c8_of_val_mem; try lia.
  - exact (YCbq.val_mem_of_rdword frsegs _ _ _ _ C3).
  - exact (YCbq.val_mem_of_rdword frsegs _ _ _ _ C1).
Qed.

Lemma walk_cells_x : forall B ARx, rt_laws frsegs B ARx -> FrShadowSyms B -> FrRtCells_x B ARx ->
  forall ly S Hp (W : world frsegs) mem md, ARx ly S Hp W mem md ->
  fr_walk_cells (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).
Proof.
  intros B ARx LAWS TL CELLS ly S Hp W mem md HAR. apply fr_walk_cells_of.
  - exact (fr_tl_norm (w_H W) mem (tl_cells_x B ARx TL LAWS ly S Hp W mem md HAR)).
  - exact (fr_rest_norm (w_H W) mem (CELLS ly S Hp W mem md HAR)).
Qed.

Lemma walk_rest_x : forall B ARx, FrRtCells_x B ARx -> forall ly S Hp (W : world frsegs) mem md,
  ARx ly S Hp W mem md -> fr_rt_rest (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).
Proof. intros B ARx CELLS ly S Hp W mem md HAR. exact (fr_rest_norm (w_H W) mem (CELLS ly S Hp W mem md HAR)). Qed.

(* ---- cgif's AR: each lemma above at ARx := FCiface.AR_nohp (Hp := []), whose laws rt_laws_AR gives. ---- *)
(* the shadow-offset cell and its GOT slot, by AR_const_law *)
Lemma tl_cells : forall B, FrShadowSyms B -> AR_laws frsegs B -> forall ly S (W : world frsegs) mem md,
  AR frsegs B ly S W mem md -> fr_tl_cells (mrestrict (w_H W) mem).
Proof.
  intros B TL LAWS ly S W mem md HAR.
  exact (tl_cells_x B (FCiface.AR_nohp frsegs B) TL (rt_laws_AR frsegs B LAWS) ly S [] W mem md HAR).
Qed.

(* all the cells, on the walk's (normalized) memory *)
Lemma walk_cells : forall B, AR_laws frsegs B -> FrShadowSyms B -> FrRtCells B ->
  forall ly S (W : world frsegs) mem md, AR frsegs B ly S W mem md ->
  fr_walk_cells (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).
Proof.
  intros B LAWS TL CELLS ly S W mem md HAR.
  exact (walk_cells_x B (FCiface.AR_nohp frsegs B) (rt_laws_AR frsegs B LAWS) TL (FrRtCells_x_AR B CELLS)
    ly S [] W mem md HAR).
Qed.

(* the cells themselves on the walk's memory, for walks that read cells fr_walk_cells does not bundle *)
Lemma walk_rest : forall B, FrRtCells B -> forall ly S (W : world frsegs) mem md, AR frsegs B ly S W mem md ->
  fr_rt_rest (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)).
Proof.
  intros B CELLS ly S W mem md HAR.
  exact (walk_rest_x B (FCiface.AR_nohp frsegs B) (FrRtCells_x_AR B CELLS) ly S [] W mem md HAR).
Qed.

(* the frame the string interceptors keep: the bytes [x, x + n) outside [sp - STK, sp) and the stack window below
   them, from the W_sites premise that no byte of the range is in the scratch window *)
Lemma off_window : forall sp STK x n, 0 < n -> 0 < STK ->
  (forall a, x <= a < x + n -> ~ (sp - STK <= a < sp)) -> x + n - 1 < sp - STK \/ sp <= x.
Proof.
  intros sp STK x n Hn HS H. destruct (Z_lt_le_dec x sp) as [L|L]; [left|right; exact L].
  destruct (Z_lt_le_dec (x + n - 1) (sp - STK)) as [L2|L2]; [exact L2|].
  exfalso. destruct (Z_lt_le_dec x (sp - STK)) as [L3|L3].
  - apply (H (sp - STK)); lia.
  - apply (H x); lia.
Qed.

End core.
