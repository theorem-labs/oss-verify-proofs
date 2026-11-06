(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA
  PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HK2.
Definition mem := (word -> option byte).
Abbreviation RSEGS := Pm5PlanKit.RSEGS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efootA_ns (V S2 : Z) (g : PMES.eghost) (a : Z) : Prop :=
  (V <= a < V + PMES.ENC_SIZE) \/ (S2 <= a < S2 + 24) \/ in_block (PMES.g_lbv g) a \/ (exists b, In b (PMES.g_lbv g) /\ in_shadow_of (fst b) (snd b) a).
Definition enc_agree_nsP (enc_invA : mem -> Z -> Z -> PMES.eghost -> Prop) : Prop :=
  forall (M M' : mem) V S2 g, enc_invA M V S2 g -> (forall a, efootA_ns V S2 g a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> enc_invA M' V S2 g.
Lemma efootA_ns_efootA : forall V S2 g a, efootA_ns V S2 g a -> PMXA.efootA V S2 g a.
Proof. intros V S2 g a H. unfold PMXA.efootA. unfold efootA_ns in H. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma opts_idle_ag : forall L (M M' : mem) (P : Z -> Prop), (forall a, P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  forall V, PTA.out P (V + 96) 128 -> PMESA.opts_idle L M V -> PMESA.opts_idle L M' V.
Proof.
  intros L M M' P AG V Ho (A & B & C & D & E & F). unfold PMESA.opts_idle, PMSA.u64 in *.
  repeat split; (eapply (PTA.u64_ag (hl_segs L) M M' P AG); [eapply PTA.out_sub; [exact Ho | lia | lia] | assumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_img : forall (M : mem) (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof. intros M a n Ha Hn H. symmetry. apply (L5C.rdn_agree RSEGS M (fun _ => None) n a Ha Hn). intros i Hi. rewrite H; [reflexivity | exact Hi]. Qed.
Lemma lits_pristine_okA : forall L C, L5A.as0_layout L C -> forall M, PMLA.lits_pristine PMLA.C_xboth M -> PMLA.lits_ok (hl_segs L) PMLA.C_xboth M.
Proof.
  intros L C LAY M H. rewrite (L5A.aly_segs L C LAY). unfold PMLA.lits_pristine, PMLA.LIT_LO, PMLA.LIT_HI in H. cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xboth] in H.
  unfold PMLA.lits_ok, PMLA.lit_ok, PMLA.u8, PMLA.u64, L5.u8_at, L5.u64_at. cbn [PMLA.LIT_NULL_S PMLA.LIT_NULL_G PMLA.LIT_TRUE_S PMLA.LIT_TRUE_G PMLA.LIT_FALSE_S PMLA.LIT_FALSE_G PMLA.C_xboth].
  repeat split; left; rewrite !(rdn_img M) by (first [cbn; lia | intros i Hi; apply H; cbn in Hi; lia]); repeat split; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_S1 : forall segs (M : mem) x (n : nat),
  rdn segs M x (Datatypes.S n) = match (match M x with Some b => Some b | None => seg_rom segs x end) with
                       | Some b => match rdn segs M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end.
Proof. reflexivity. Qed.
Lemma u8_of_u64 : forall segs (M : mem) a v, L5.u64_at segs M a v -> L5.u8_at segs M a (v mod 256).
Proof.
  intros segs M a v H. unfold L5.u64_at in H. unfold L5.u8_at.
  change (rdn segs M (Z_to_bv 64 a) 8) with (rdn segs M (Z_to_bv 64 a) (Datatypes.S 7)) in H. rewrite rdn_S1 in H. rewrite (rdn_S1 segs M (Z_to_bv 64 a) 0%nat).
  change (rdn segs M (Z_to_bv 64 a + 1)%bv 0%nat) with (Some (@nil byte)).
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b|]; [|discriminate H].
  destruct (rdn segs M (Z_to_bv 64 a + 1)%bv 7) as [rest|]; [|discriminate H].
  unfold word_to_le_bytes in H |- *. cbn [Z_to_le_bytes] in H |- *. injection H as Hb Hrest. rewrite Hb. f_equal. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity.
Qed.
Lemma testbit_mod256 : forall v, Z.testbit (v mod 256) 0 = Z.testbit v 0.
Proof. intros v. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. reflexivity. Qed.
Lemma odd_land1 : forall v, 0 <= v -> Z.testbit v 0 = true -> Z.land v 1 = 1.
Proof.
  intros v Hv Hb. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. destruct (Z.eq_dec n 0) as [->|Hne].
  - rewrite Hb. reflexivity.
  - change 1 with (2 ^ 0). rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.
Lemma even_land1 : forall k, 0 <= k -> Z.land (2 * k) 1 = 0.
Proof.
  intros k Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec n 0) as [->|Hne].
  - rewrite Z.bit0_odd, Z.odd_mul. cbn. reflexivity.
  - change 1 with (2 ^ 0). rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.
(* [comment removed for export] *)
Lemma sink_short_byte0 : forall L (M : mem) o s, PMESA.sink_atA L M o (PML.SShort s) -> L5.u8_at (hl_segs L) M o (2 * Z.of_nat (length s)) /\ (length s <= 22)%nat.
Proof. intros L M o s ((Hl & Hb & _ & _) & _ & _ & _). split; [exact Hb | exact Hl]. Qed.
(* [comment removed for export] *)
Lemma sink_long_facts : forall L (M : mem) o cap p s, PMESA.sink_atA L M o (PML.SLong cap p s) ->
  exists w0, L5.u64_at (hl_segs L) M o w0 /\ Z.testbit w0 0 = true /\ L5.u64_at (hl_segs L) M (o + 16) p /\ 48 <= cap /\ cap mod 8 = 0 /\
             PML.srep_blocks (PML.SLong cap p s) = [(p, cap)] /\ shadow_blk M p cap.
Proof.
  intros L M o cap p s (((Hbit & Hw0 & _ & Hp & _) & Hc8 & _) & _ & Hok & Hsh). exists (cap + 1).
  split; [exact Hw0|]. split; [exact Hbit|]. split; [exact Hp|]. split; [exact Hok|]. split; [exact Hc8|]. split; [reflexivity | exact Hsh].
Qed.
(* [comment removed for export] *)
Lemma sink_empty : forall L (M : mem) o, (forall j, 0 <= j < 24 -> byte_at M (o + j) 0) -> L5.defined M o 24 -> PMESA.sink_atA L M o (PML.SShort []).
Proof.
  intros L M o HZ HD. split; [|split; [exact HD | split; [exact I | exact I]]].
  unfold PMSA.str_at, PMLA.str_at, L5.lstr_short. change (2 * Z.of_nat (@length Z [])) with 0. change (Z.of_nat (@length Z [])) with 0.
  split; [cbn; lia|]. split; [apply CL5A.byte_at_u8; replace o with (o + 0) by lia; apply HZ; lia|].
  split; [intros i Hi; cbn in Hi; lia|]. apply CL5A.byte_at_u8. replace (o + 1 + 0) with (o + 1) by lia. apply HZ. lia.
Qed.
(* [comment removed for export] *)
Definition eg_after_dtor (g : PMES.eghost) : PMES.eghost := PMES.EG (PMES.g_es g) (PMES.g_len g) (PMES.g_rep g) 0 0.
Lemma g_lbv_after_dtor : forall g, PMES.g_lbv (eg_after_dtor g) = PML.srep_blocks (PMES.g_rep g).
Proof. intros g. unfold PMES.g_lbv, eg_after_dtor, PMES.stack_blocks. cbn [PMES.g_rep PMES.g_sb PMES.g_scap Z.eqb]. apply app_nil_r. Qed.
Lemma g_lbv_g0 : PMES.g_lbv PMES.g0 = [].
Proof. reflexivity. Qed.
End HK2.
