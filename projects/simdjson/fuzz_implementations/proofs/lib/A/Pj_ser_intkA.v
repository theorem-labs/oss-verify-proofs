(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition shpU1Z : list Z :=
  [241; 241; 241; 241; 0; 0; 4; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242; 0; 0; 0; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 0; 242; 242; 242; 0; 242; 242; 242; 0; 0; 243; 243; 243; 243].

Definition shpU2Z : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242; 0; 0; 0; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 0; 242; 242; 242; 0; 242; 242; 242; 0; 0; 243; 243; 243; 243].

Definition shpI1Z : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 242; 242; 242; 242; 242; 0; 0; 4; 242; 242; 242; 242; 242; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 0; 0; 0; 242; 242; 242; 242; 242; 0; 242; 242; 242; 0; 242; 242; 242; 0; 0; 243; 243; 243; 243].
Definition shpI2Z : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 0; 0; 0; 242; 242; 242; 242; 242; 0; 242; 242; 242; 0; 242; 242; 242; 0; 0; 243; 243; 243; 243].
Definition shpU1 : list byte := map (Z_to_bv 8) shpU1Z.
Definition shpU2 : list byte := map (Z_to_bv 8) shpU2Z.
Definition shpI1 : list byte := map (Z_to_bv 8) shpI1Z.
Definition shpI2 : list byte := map (Z_to_bv 8) shpI2Z.

Lemma shpU1_eq : upd (upd (upd (upd (upd (upd ser_shpatA 4 z8) 5 z8) 6 (Z_to_bv 8 4)) 30 z8) 31 z8) 32 z8 = shpU1.
Proof. reflexivity. Qed.
Lemma shpU2_eq : upd (upd (upd shpU1 4 (Z_to_bv 8 248)) 5 (Z_to_bv 8 248)) 6 (Z_to_bv 8 248) = shpU2.
Proof. reflexivity. Qed.
Lemma shpU0_eq : upd (upd (upd shpU2 30 (Z_to_bv 8 248)) 31 (Z_to_bv 8 248)) 32 (Z_to_bv 8 248) = ser_shpatA.
Proof. reflexivity. Qed.
Lemma shpI1_eq : upd (upd (upd (upd (upd (upd ser_shpatA 12 z8) 13 z8) 14 (Z_to_bv 8 4)) 38 z8) 39 z8) 40 z8 = shpI1.
Proof. reflexivity. Qed.
Lemma shpI2_eq : upd (upd (upd shpI1 12 (Z_to_bv 8 248)) 13 (Z_to_bv 8 248)) 14 (Z_to_bv 8 248) = shpI2.
Proof. reflexivity. Qed.
Lemma shpI0_eq : upd (upd (upd shpI2 38 (Z_to_bv 8 248)) 39 (Z_to_bv 8 248)) 40 (Z_to_bv 8 248) = ser_shpatA.
Proof. reflexivity. Qed.

Lemma u8arr_write_le1 : forall (m : mem) A bs (i : Z) (v : word) a,
  u8arr asegs m A bs -> (0 <= i < Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  u8arr asegs (write_to_mem m a (le1 v)) A (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned v))).
Proof.
  intros m A bs i v a U Hi ->.
  assert (E1 : le1 v = [Z_to_bv 8 (bv_unsigned v)]) by reflexivity.
  rewrite E1. apply u8arr_write; [exact U| exact Hi].
Qed.

Lemma zb8_m8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8))) = Z_to_bv 8 248.
Proof. apply bv_eq. reflexivity. Qed.

Lemma f3_acc3 : forall (m : mem) (f : Z) (shp : list byte) (g : nat),
  u8arr asegs m (f / 8 + 2147450880) shp -> nth_error shp g = Some z8 -> nth_error shp (S g) = Some z8 -> nth_error shp (S (S g)) = Some z8 ->
  8 * (f / 8) = f -> 0 <= f -> acc asegs m (f + 8 * Z.of_nat g) 24.
Proof.
  intros m f shp g [HB _] N0 N1 N2 Ef F0 i Hi. exists z8. split; [| left; reflexivity].
  assert (C : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2) by (Z.div_mod_to_equations; lia).
  assert (SH : shad (f + 8 * Z.of_nat g + i) = f / 8 + 2147450880 + (Z.of_nat g + i / 8)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite SH. destruct C as [C|[C|C]]; rewrite C.
  - replace (Z.of_nat g + 0) with (Z.of_nat g) by lia. exact (bytes_at_nth1 asegs m _ shp g z8 HB N0).
  - replace (Z.of_nat g + 1) with (Z.of_nat (S g)) by lia. exact (bytes_at_nth1 asegs m _ shp (S g) z8 HB N1).
  - replace (Z.of_nat g + 2) with (Z.of_nat (S (S g))) by lia. exact (bytes_at_nth1 asegs m _ shp (S (S g)) z8 HB N2).
Qed.
Lemma f3_acc20 : forall (m : mem) (f : Z) (shp : list byte) (g : nat),
  u8arr asegs m (f / 8 + 2147450880) shp -> nth_error shp g = Some z8 -> nth_error shp (S g) = Some z8 -> nth_error shp (S (S g)) = Some (Z_to_bv 8 4) ->
  8 * (f / 8) = f -> 0 <= f -> acc asegs m (f + 8 * Z.of_nat g) 20.
Proof.
  intros m f shp g [HB _] N0 N1 N2 Ef F0 i Hi.
  assert (C : i / 8 = 0 \/ i / 8 = 1 \/ (i / 8 = 2 /\ i mod 8 < 4)) by (Z.div_mod_to_equations; lia).
  assert (SH : shad (f + 8 * Z.of_nat g + i) = f / 8 + 2147450880 + (Z.of_nat g + i / 8)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite SH. destruct C as [C|[C|[C M]]]; rewrite C.
  - exists z8. split; [| left; reflexivity]. replace (Z.of_nat g + 0) with (Z.of_nat g) by lia. exact (bytes_at_nth1 asegs m _ shp g z8 HB N0).
  - exists z8. split; [| left; reflexivity]. replace (Z.of_nat g + 1) with (Z.of_nat (S g)) by lia. exact (bytes_at_nth1 asegs m _ shp (S g) z8 HB N1).
  - exists (Z_to_bv 8 4). split.
    + replace (Z.of_nat g + 2) with (Z.of_nat (S (S g))) by lia. exact (bytes_at_nth1 asegs m _ shp (S (S g)) _ HB N2).
    + right. change (bv_unsigned (Z_to_bv 8 4)) with 4. split; [lia|].
      replace ((f + 8 * Z.of_nat g + i) mod 8) with (i mod 8) by (Z.div_mod_to_equations; lia). exact M.
Qed.

Lemma f3_shadow_read : forall (m : mem) (f : Z) (shp : list byte) (g : nat) (j : Z) (b : byte),
  u8arr asegs m (f / 8 + 2147450880) shp -> nth_error shp (Z.to_nat (Z.of_nat g + j / 8)) = Some b -> 8 * (f / 8) = f -> 0 <= f -> 0 <= j ->
  ov_read_bytes asegs m (wa (shad (f + 8 * Z.of_nat g + j))) 1 = Some [b].
Proof.
  intros m f shp g j b U N Ef F0 J0.
  apply (u8arr_read asegs m (f / 8 + 2147450880) shp (Z.of_nat g + j / 8) b); [exact U| exact N| Z.div_mod_to_equations; lia|].
  unfold shad, SHB, wa. f_equal. Z.div_mod_to_equations. lia.
Qed.

Lemma shpU1_gran : forall idx, 0 <= idx <= 19 ->
  exists b, nth_error shpU1 (Z.to_nat (Z.of_nat 4 + idx / 8)) = Some b /\ (idx <= 15 -> b = z8) /\ (16 <= idx -> b = Z_to_bv 8 4).
Proof.
  intros idx H. assert (C : idx / 8 = 0 \/ idx / 8 = 1 \/ (idx / 8 = 2 /\ 16 <= idx)) by (Z.div_mod_to_equations; lia).
  destruct C as [C|[C|[C G]]]; rewrite C.
  - exists z8. split; [reflexivity|]. split; [reflexivity| intros; exfalso; Z.div_mod_to_equations; lia].
  - exists z8. split; [reflexivity|]. split; [reflexivity| intros; exfalso; Z.div_mod_to_equations; lia].
  - exists (Z_to_bv 8 4). split; [reflexivity|]. split; [intros; exfalso; lia| reflexivity].
Qed.
Lemma shpI1_gran : forall idx, 0 <= idx <= 19 ->
  exists b, nth_error shpI1 (Z.to_nat (Z.of_nat 12 + idx / 8)) = Some b /\ (idx <= 15 -> b = z8) /\ (16 <= idx -> b = Z_to_bv 8 4).
Proof.
  intros idx H. assert (C : idx / 8 = 0 \/ idx / 8 = 1 \/ (idx / 8 = 2 /\ 16 <= idx)) by (Z.div_mod_to_equations; lia).
  destruct C as [C|[C|[C G]]]; rewrite C.
  - exists z8. split; [reflexivity|]. split; [reflexivity| intros; exfalso; Z.div_mod_to_equations; lia].
  - exists z8. split; [reflexivity|]. split; [reflexivity| intros; exfalso; Z.div_mod_to_equations; lia].
  - exists (Z_to_bv 8 4). split; [reflexivity|]. split; [intros; exfalso; lia| reflexivity].
Qed.

Lemma itoa_shadow_read : forall (m : mem) (f : Z) (shp : list byte) (g : nat) (base idx : Z) (b : byte),
  u8arr asegs m (f / 8 + 2147450880) shp -> nth_error shp (Z.to_nat (Z.of_nat g + idx / 8)) = Some b -> 8 * (f / 8) = f -> 0 <= f -> 0 <= idx ->
  base = 8 * Z.of_nat g -> ov_read_bytes asegs m (wa (shad (f + base + idx))) 1 = Some [b].
Proof.
  intros m f shp g base idx b U N Ef F0 I0 ->. replace (f + 8 * Z.of_nat g + idx) with (f + 8 * Z.of_nat g + idx) by lia.
  exact (f3_shadow_read m f shp g idx b U N Ef F0 I0).
Qed.

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition f3copy_stmtA : Prop :=
  forall E D I w168 w224 w232 w240 xs shp isobj Σ st m (K : config -> Prop) (Dst Src n rpc : Z) (bs : list byte) (F : bvmap 5 word) (fc : bv 32)
         (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> sctxA E D I -> SERMA RT E I w168 w224 w232 w240 xs shp isobj Σ st m ->
  bytes_at asegs m Src bs -> Z.of_nat (length bs) = n -> 1 <= n ->
  si_f I + 24 <= Src -> Src + n <= si_f I + 432 -> si_f I + 24 <= Dst -> Dst + n <= si_f I + 432 ->
  acc asegs m Src n -> acc asegs m Dst n -> (Dst + n <= Src \/ Src + n <= Dst) -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     SERMA RT E I w168 w224 w232 w240 xs shp isobj Σ st m' -> bytes_at asegs m' Dst bs ->
     aevt Σ K (SSTA I rpc (wz rpc) yt0 yt1 yt2 (wz Dst) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc m')) ->
  aevt Σ K (SSTA I e_asan_memcpy (wz rpc) xt0 xt1 xt2 (wz Dst) (wz Src) (wz n) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).

Definition u64_stmtA' : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A X : Z)
         (xs5 xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σ st m -> frm0 fc ->
    1 <= i -> i + 1 < pa_n E -> ty (pa_T E) i = t_u64 -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + 20 <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 0 <= X ->
    av_KA RT PMc E I K isobj (i + 1) dp X (A + 20) ->
    aevt Σ K (LSTA E I PJ_U64_A i dp (wz (SHDOCA E)) xs5 (wz PJ_NE_TAB_A) (wz (8 * i)) (wz (pa_SB E)) (wz (T5A E))
                 xra xt0 xt1 xt2 (wz 117) (wz (pa_TAPE E)) (wz PJ_ITOA_BASE_A) (wz 117) xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Definition i64_stmtA' : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A X : Z)
         (xs5 xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σ st m -> frm0 fc ->
    1 <= i -> i + 1 < pa_n E -> ty (pa_T E) i = t_i64 -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + 20 <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 0 <= X ->
    av_KA RT PMc E I K isobj (i + 1) dp X (A + 20) ->
    aevt Σ K (LSTA E I PJ_I64_A i dp (wz (SHDOCA E)) xs5 (wz PJ_NE_TAB_A) (wz (8 * i)) (wz (pa_SB E)) (wz (T5A E))
                 xra xt0 xt1 xt2 (wz 108) (wz (pa_TAPE E)) (wz PJ_ITOA_BASE_A) (wz 108) xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
End Stmts.
