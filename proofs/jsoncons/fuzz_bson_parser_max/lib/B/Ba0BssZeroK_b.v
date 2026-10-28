(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require FxHexScan.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.

Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Definition DEP_LO : Z := 0x221b18.
Definition DEP_HI : Z := 0x621b18.
Lemma as0_dep_zscan : zscanN AsanUbsan_seg_bytes_003 64 0xe8b18 0x400000 = true.
Proof. apply (FxHexScan.FXH.zscan_ok zscanN byte_zero (fun _ _ _ _ => eq_refl) (fun _ _ H => H)); [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.

Open Scope Z_scope.
Lemma as0_dep_rom_zero : forall a, DEP_LO <= a < DEP_HI -> seg_rom ASEGS0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. unfold DEP_LO, DEP_HI in Ha. unfold seg_rom, memory_read. rewrite u64_lit by lia.
  rewrite asan0_segs_eq. cbn [find_segment].
  cbn [seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002 AsanUbsan_segment_003].
  replace (Z.leb (Z.of_N 65536) a && Z.leb (a + Z.of_N 1) (Z.of_N 65536 + Z.of_N 266240))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace (Z.leb (Z.of_N 331776) a && Z.leb (a + Z.of_N 1) (Z.of_N 331776 + Z.of_N 917504))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace (Z.leb (Z.of_N 1249280) a && Z.leb (a + Z.of_N 1) (Z.of_N 1249280 + Z.of_N 32768))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace (Z.leb (Z.of_N 1282048) a && Z.leb (a + Z.of_N 1) (Z.of_N 1282048 + Z.of_N 5623808))%bool with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  assert (Hr : seg_readable AsanUbsan_segment_003 = true) by (vm_compute; reflexivity).
  rewrite Hr. cbn [seg_bytes seg_base AsanUbsan_segment_003].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
  rewrite asan0_len3.
  replace (Z.to_N (a - Z.of_N 1282048) <? 5623808)%N with true by (symmetry; apply N.ltb_lt; lia).
  pose proof (zscanN_sound _ _ _ _ as0_dep_zscan (Z.to_N (a - 0x221b18)) ltac:(lia)) as Hz.
  replace (0xe8b18 + Z.to_N (a - 0x221b18))%N with (Z.to_N (a - Z.of_N 1282048)) in Hz by lia.
  rewrite Hz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma as0_dep_rdn_zero : forall (M : word -> option byte) n a, DEP_LO <= a -> a + Z.of_nat n <= DEP_HI ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M x = None) ->
  rdn ASEGS0 M (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros M n. induction n as [|n IH]; intros a Ha Hb HM; [reflexivity|].
  assert (Hr : DEP_LO <= a < DEP_HI) by lia. unfold DEP_LO, DEP_HI in Ha, Hb.
  cbn [rdn repeat]. rewrite (HM (Z_to_bv 64 a)) by (rewrite u64_lit by lia; lia). rewrite (as0_dep_rom_zero a Hr).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  - rewrite IH; [reflexivity | unfold DEP_LO; lia | unfold DEP_HI; lia | intros x Hx; apply HM; lia].
  - apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    change (bv_unsigned (1 : word)) with 1. rewrite Z.mod_small by lia. reflexivity.
Qed.
