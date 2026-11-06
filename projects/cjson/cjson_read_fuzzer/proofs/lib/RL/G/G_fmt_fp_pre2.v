(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_fmt_fp_pre.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {RS_102ac : RelSym (sym 0x102ac)}.
  Let rp_102ac : (0 <= sym 0x102ac /\ sym 0x102ac < 2^30)%Z := @rel_sym_pf _ RS_102ac.
  Context {RO_prefix : RoB img_segs (sym 0x102ac) (zb PREFIX_STR)}.
  Collection ImgHyps := IMG RS_102ac rp_102ac RO_prefix.



(* [comment removed for export] *)
Lemma prefix_u8ro : forall m, mem_inv img_segs m -> u8ro img_segs m (sym 0x102ac) (zb PREFIX_STR).
Proof.
  intros m MI. unfold u8ro. apply ro_bytes_at. { exact MI. } { arel_side. } { cbn. arel_side. }
  apply ro_bytes_b_sound. exact ro_b_pf.
Qed.

Lemma zb_nth : forall l i, (0 <= i)%Z -> (Z.to_nat i < length l)%nat ->
  nth_error (zb l) (Z.to_nat i) = Some (Z_to_bv 8 (znth l i)).
Proof.
  intros l i Hi Hl. unfold zb, znth. rewrite (proj2 (Z.ltb_ge i 0)) by lia.
  rewrite nth_error_map. rewrite (nth_error_nth' l 0%Z Hl). reflexivity.
Qed.

Lemma PREFIX_STR_range : forall i, (0 <= znth PREFIX_STR i <= 120)%Z.
Proof.
  intros i. unfold znth. destruct (i <? 0); [cbn; lia|].
  assert (HF : Forall (fun z => 0 <= z <= 120)%Z PREFIX_STR).
  { unfold PREFIX_STR. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  destruct (nth_in_or_default (Z.to_nat i) PREFIX_STR 0%Z) as [H|H]; [|rewrite H; cbn; lia].
  exact (proj1 (Forall_forall _ _) HF _ H).
Qed.

Lemma sext32_m1 : sext32 (-1) = 18446744073709551615%Z.
Proof. reflexivity. Qed.

Lemma unsigned_lit8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma srliw1_small : forall i, (0 <= i < 2^31)%Z -> bv_swrap 32 (Z.shiftr (bv_wrap 32 i) 1) = (i / 2)%Z.
Proof.
  intros i Hi. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite swrap32_eq. mlia.
Qed.

(* [comment removed for export] *)
Lemma u32s_low_byte : forall ws k, (k < length ws)%nat ->
  nth_error (u32s ws) (4 * k) = Some (Z_to_bv 8 (bv_unsigned (nth k ws (Z_to_bv 64 0)))).
Proof.
  induction ws as [|w0 ws IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k].
  - cbn. reflexivity.
  - cbn [u32s nth]. replace (4 * S k)%nat with (4 + 4 * k)%nat by lia.
    rewrite nth_error_app2 by (rewrite length_le4; lia). rewrite length_le4. replace (4 + 4 * k - 4)%nat with (4 * k)%nat by lia.
    apply IH. cbn in Hk. lia.
Qed.

Lemma wnth_low_byte : forall ws k, (0 <= k)%Z -> (Z.to_nat k < length ws)%nat ->
  nth_error (u32s ws) (Z.to_nat (4 * k)) = Some (Z_to_bv 8 (wval ws k)).
Proof.
  intros ws k Hk Hl. replace (Z.to_nat (4 * k)) with (4 * Z.to_nat k)%nat by lia.
  rewrite (u32s_low_byte ws (Z.to_nat k) Hl). unfold wval, wnth. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
  rewrite <- (Z.mod_mod_divide _ 4294967296 256) by (exists 16777216%Z; reflexivity). reflexivity.
Qed.

Lemma land1_mod256 : forall v, (0 <= v)%Z -> Z.land (v mod 256) 1 = Z.land v 1.
Proof.
  intros v Hv. rewrite !land_bit0. change 256%Z with (2 * 128)%Z. rewrite Z.rem_mul_r, Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

End Img.
