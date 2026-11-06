(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     BigModel BigFactsRun BigFactsDigits L5Defs L5Core L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5ArithSpecsB0 L5ParseSpecsBB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5ASCS.
Import L5A. Import L5CA. Import L5CSA. Import L5CB. Import L5PSA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRCTOR : Z := 0x8e9ac.
Definition STRCTOR_THROW : Z := 0x8eaa0.        (* [comment removed for export] *)
Definition STRCTOR_N_SCRB : Z := 32 + Z.max L5PSB.TOBIG_SCRB 2560.      (* [comment removed for export] *)

Definition strctor_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fbo : Z) (s : list Z) (SCR : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let neg := fst (split_sign s) in let ds := snd (split_sign s) in
  regs_preserved R R' /\ parses s /\ parse_post L ar LB FF LKq cr M M' o sp (Z.land fbo 252) neg ds SCR LB' cr'.

(* [comment removed for export] *)
Definition strctor_throw_state (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fbo : Z) (s : list Z) (SCR : Z) (cr' : credit) : Prop :=
  no_parse s /\
  getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 9) = Z_to_bv 64 22 /\
  getr R' (reg 18) = Z_to_bv 64 SB /\                       (* [comment removed for export] *)
  (forall i, In i [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr R (reg i)) /\
  L5.u64_at RSEGS M' (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8))) /\
  L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 32) (bv_unsigned (getr R (reg 18))) /\
  L5.big_at RSEGS M' o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0)) /\ shadow_zero M' o 4 /\
  credit_le (parse_debit L cr (length (snd (split_sign s)))) cr' /\
  astk ar M' sp SCR /\
  ahpres L ar LB FF sp SCR [(o, 32)] M M'.

Definition strctor_norm_specB (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (HI : asan_iface) (SCR : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o so sp r fbo : Z) (s : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 so ->
    (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
    parse_credit L cr (length (snd (split_sign s))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCR -> L5ASB.stksh ar M (sp - SCR) ->
    ffr FF LK 5 -> ffrk 2 FF LK 2 -> ffrs FF sp ->
    (* [comment removed for export] *)
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> aobj FF o 32 -> shadow_zero M o 4 ->
    (* [comment removed for export] *)
    aobj FF so 24 -> shadow_zero M so 3 -> (o + 32 <= so \/ so + 24 <= o) ->
    ( L5.lstr_short RSEGS M so s
      \/ (exists w0 pd, L5.lstr_long RSEGS M so s w0 pd /\ In (pd, w0 - 1) LB /\ Z.of_nat (length s) + 1 <= w0 - 1 /\ 0 <= w0 < 2 ^ 64) ) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        strctor_post L ar LB FF LK' cr M M' R R' o sp fbo s SCR LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        strctor_throw_state L ar LB FF cr M M' R R' o sp fbo s SCR cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' STRCTOR_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRCTOR M model) K.

(* [comment removed for export] *)
Lemma rdn_head M a (k : nat) b rest : rdn RSEGS M a (Datatypes.S k) = Some (b :: rest) -> rdn RSEGS M a 1 = Some [b].
Proof.
  cbn [rdn]. destruct (match M a with Some b0 => Some b0 | None => seg_rom RSEGS a end) as [b0|]; [|discriminate].
  destruct (rdn RSEGS M (a + 1)%bv k) as [r0|]; [|discriminate]. intros E. injection E as -> _. reflexivity.
Qed.
Lemma u8_of_u64_lo M a v : L5.u64_at RSEGS M a v -> L5.u8_at RSEGS M a (v mod 256).
Proof.
  unfold L5.u64_at, L5.u8_at. intros HU. unfold word_to_le_bytes in HU. change 8%nat with (Datatypes.S 7) in HU. cbn [Z_to_le_bytes] in HU.
  rewrite (rdn_head M (Z_to_bv 64 a) 7 _ _ HU). f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. change (2 ^ 64) with (256 * 72057594037927936).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End SCFG_1.
End L5ASCS.
