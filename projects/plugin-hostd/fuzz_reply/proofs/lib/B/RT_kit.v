(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the generic half of the bridge from a Bz body walk (lib/B/Bz, on
   fuzz_reply.asan-ubsan) to the W_sites.v runtime site contracts, for every runtime lane of fuzz_reply. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_kit.v at commit debcdf3fa6a, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (95 numerals; per-numeral report). *)
(* Ported from: a working branch 3210d71ee38 proofs/omx-clap-core/fuzz_state/lib/A/FSstrlen.v:90-750
   (a Theorem Labs lane's bridge, itself from a Theorem Labs lane's FMbz_bridge / FMbz_str and a Theorem Labs lane's MemNorm / RegisterBridge).
   Changes (R1Str, 2026-10-29):
   - fuzz_state.asan -> fuzz_reply.asan-ubsan: Img0.rsegs is lib/B/Img0.v (the ASan-UBSan segments, NOT lib/Img0.v,
     which is the plain image); FR_IMG_TOP 0x600000 is above fuzz_reply.asan-ubsan's image end 0x5fc000 (rsegs_below);
   - U-free: the W_sites forms carry no user-poisoned ranges, so ecall_preU_k / ARU / unpoison are gone;
   - the post (aentry_post_of_walk) and the transport lemmas (bz_transport, chk_norm, stk_norm_high, the cell
     agreement and ro->rw lemmas, the register lemmas) are R3Mem's RT_post.v (lib/B/RT_post.v here), from FSstrlen.v by
     agreement so that there is one copy; this file keeps the byte-list lemmas the string walks need and the cells;
   - the runtime cells are fuzz_reply.asan-ubsan's, named premises FrShadowSyms (the shadow cell and its GOT slot) and
     FrRtCells (the rest), both facts about B's constant cells; FrRtCells holds the memmove cells R3 needs too.
   The fuzz_state -> fuzz_reply address table of the relocated Bz tree (fs.asan sha 64b53ff86172 -> fuzz_reply.asan-ubsan),
   every code numeral paired by code (relocation fields masked, unique match over .text), every data numeral by the
   instruction that loads it, values from fuzz_reply.asan-ubsan's .got and the generated YF0m (lib/B/YF0m.v):
   trampolines strcmp 0x4265c->0x421f0, memchr 0x4266c->0x42208; ___interceptor_strlen 0x426e4->0x42288,
   _strnlen 0x42978->0x4251c, _strcmp 0x42c10->0x42ac4, _memchr 0x43e30->0x445a0 (inner pcs shifted with them);
   MemToShadow copies 0x52dc8->0x53b98, 0x54758->0x55528, 0x5d644->0x5e4ac; __asan_region_is_poisoned
   0x54be4->0x559b4; AsanInited 0x59168->0x59f38; TryAsanInitFromRtl 0x5a078->0x5ae48; mem_is_zero 0x64924->0x6578c;
   musl bcmp 0x98920->0x9694c, memchr 0x98924->0x96950, memcmp 0x989f0->0x96a1c, strlen 0x99070->0x970cc,
   strnlen 0x992ac->0x973c8; GOT common_flags 0x9f6e0->0x9df40, shadow cell 0x9f6f0->0x9df50, kMidMemBeg/End,
   kHighMemEnd 0x9f6f8/0x9f700/0x9f708->0x9df58/0x9df60/0x9df68; shadow cell 0xa7f38->0xa6638; asan_inited
   0xa8c18->0xa7318; kHighMemEnd/kMidMemBeg/kMidMemEnd 0xa8c20/28/30->0xa7320/28/30; REAL(strlen/memchr/strnlen)
   0xa1408/0xa1430/0xa1518->0x9fc68/0x9fca8/0x9fd98; common_flags 0x139a68->0x138168 (+0xf5/+0xfa/+0xfb);
   image end 0x5fd000->0x5fc000. Unchanged (same code, same constant): 0x7fff8000, 0x7fff7fff, 0x10007fff8000,
   0x10007fff7fff, 0x7fffffffffff. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strcmpw.
(* B's Bz tree keeps icells_sc (and its _agree lemma) in Bz/A/I_strncmpw.v, not in Bz/A/I_strcmpw.v as A's does: BS names it *)
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strncmpw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memchrw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v W_syms W_listing W_kit W_tbl W_place W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FRbz_str RT_post.
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
Module I0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Module BM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Module BI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Module BD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Module BS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strncmpw.
Module BL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Module BMC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_memchrw.
Module YCbq := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.
Module FSS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRbz_str.
Module RP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_post.

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


(* the shadow cell and its GOT slot (FrShadowSyms, from AR_const_law): .got 0x9df50 holds 0xa6638,
   __asan_shadow_memory_dynamic_address, which holds the shadow offset *)
Definition fr_tl_cells (m : word -> option byte) : Prop :=
  BSt.ro_cells BI.asegs m 0x9df50 [BC.C8 (Z_to_bv 64 0xa6638)] /\
  BSt.ro_cells BI.asegs m 0xa6638 [BC.C8 (Z_to_bv 64 0x7fff8000)].

(* the rest (the named premise FrRtCells), fuzz_reply.asan-ubsan's cells: .got 0x9df40 = common_flags 0x138168, .got
   0x9df58.. = kMidMemBeg 0xa7328 / kMidMemEnd 0xa7330 / kHighMemEnd 0xa7320, REAL(strlen) 0x9fc68 = 0x970cc,
   REAL(memchr) 0x9fca8 = 0x96950, REAL(strnlen) 0x9fd98 = 0x973c8, asan_inited 0xa7318 = 1, kHighMemEnd /
   kMidMemBeg / kMidMemEnd at 0xa7320.., the common_flags bytes +0xf5 = 0x13825d (strict_string_checks) = 0,
   +0xfa = 0x138262 (intercept_strcmp) = 1, +0xfb = 0x138263 (intercept_strlen) = 1, for __asan_memmove (R3)
   .got 0x9eab8 = 0xa7319 (replace_intrin_cached) and 0xa7319 = 1, and for strrchr (R2) common_flags + 0xfd =
   0x138265 (intercept_strchr) = 1 and REAL(strrchr) 0x9fc90 = 0x9740c.  The values are start-up state.  On A the
   generated AF0m's Tfib_const (AF0m.v sha256 007c9a7eb8b9; internal record) holds all 14 cells, and RT_kit_cells_x.FrRtCells_of_syms
   gives FrRtCells from AR_laws and TfibSyms (FrRtCells_x_of_syms: FrRtCells_x from rt_laws and TfibSyms).  On B the
   generated YF0m's Tfib_const (lib/B/YF0m.v (sha256 9dfefcb3f00e; internal record) at the B top e43cf0c7bef, sha256 e71d30bf6539 (internal record) at integ
   debcdf3fa6a) has 12 of the cells as rows (REAL(strlen) 0x9fc68 at YF0m.v:443) and 0x138265 as byte 5 of the row
   0x138260 = 0x0101010101010101 (YF0m.v:72), but NO row for REAL(strrchr) 0x9fc90: A's row for it (AF0m.v:447,
   0x9f710) came with ZeroGlobals' regeneration of AF0m, which YF0m has not had.  The image file holds the value
   (fuzz_reply.asan-ubsan's bytes at 0x9fc90 are 0x9740c), so the B discharge needs that row in YF0m first. *)
Definition fr_rt_rest (m : word -> option byte) : Prop :=
  BSt.ro_cells BI.asegs m 0x9df40 [BC.C8 (Z_to_bv 64 0x138168)] /\
  BSt.ro_cells BI.asegs m 0x9df58 [BC.C8 (Z_to_bv 64 0xa7328); BC.C8 (Z_to_bv 64 0xa7330); BC.C8 (Z_to_bv 64 0xa7320)] /\
  BSt.ro_cells BI.asegs m 0x9fc68 [BC.C8 (Z_to_bv 64 0x970cc)] /\
  BSt.ro_cells BI.asegs m 0x9fca8 [BC.C8 (Z_to_bv 64 0x96950)] /\
  BSt.ro_cells BI.asegs m 0x9fd98 [BC.C8 (Z_to_bv 64 0x973c8)] /\
  BSt.ro_cells BI.asegs m 0xa7318 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0xa7320 [BC.C8 (Z_to_bv 64 BR.kHighMemEnd); BC.C8 (Z_to_bv 64 0); BC.C8 (Z_to_bv 64 0)] /\
  BSt.ro_cells BI.asegs m 0x13825d [BC.C1 (Z_to_bv 8 0)] /\
  BSt.ro_cells BI.asegs m 0x138262 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x138263 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x9eab8 [BC.C8 (Z_to_bv 64 0xa7319)] /\
  BSt.ro_cells BI.asegs m 0xa7319 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x138265 [BC.C1 (Z_to_bv 8 1)] /\
  BSt.ro_cells BI.asegs m 0x9fc90 [BC.C8 (Z_to_bv 64 0x9740c)].

(* what the string interceptor walks ask *)
Definition fr_walk_cells (m : word -> option byte) : Prop :=
  BR.m2s_cells m /\ BN.icells_sn m /\ BN.icells_sns m /\ BL.icells_sl m /\ BS.icells_sc m /\
  BSt.ro_cells BI.asegs m 0x138262 [BC.C1 (Z_to_bv 8 1)] /\ BMC.icells_mc m.

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
  assert (G : BSt.ro_cells BI.asegs m 0x9df50
    [BC.C8 (Z_to_bv 64 0xa6638); BC.C8 (Z_to_bv 64 0xa7328); BC.C8 (Z_to_bv 64 0xa7330); BC.C8 (Z_to_bv 64 0xa7320)])
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

(* NAMED PREMISE: at every ASan state the restricted memory holds fr_rt_rest, fuzz_reply.asan-ubsan's runtime cells
   the string walks read beyond FrShadowSyms'.  A fact about B's constant cells (as_const); the relocated core's
   TfibSyms with the generated YF0m discharges it once YF0m holds every cell named in fr_rt_rest's comment (above:
   REAL(strrchr) is missing there; on A, AF0x.tfib_const_lookup per cell with AF0m.v (sha256 007c9a7eb8b9; internal record)). *)
Definition FrRtCells (B : asyms) : Prop :=
  forall ly S (W : world frsegs) mem md, AR frsegs B ly S W mem md -> fr_rt_rest (mrestrict (w_H W) mem).

(* NAMED PREMISE: the two symbols of the shadow-offset cell at fuzz_reply.asan-ubsan's addresses (the walk kit's PALib
   gives both at PB_fr: fr_shadow_of_palib). *)
Definition FrShadowSyms (B : asyms) : Prop := as_got_shadow B = 0x9df50 /\ as_shadow_cell B = 0xa6638.

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
