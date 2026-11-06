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
     BigModel BigFactsRun BigFactsDigits L5Defs L5Core L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5ParseSpecsAB0 L5ArithSpecsB0.

Module L5PSB.
Import L5A. Import L5CA. Import L5CSA. Import L5CB. Import L5PSA. Import L5ASB.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition DETAIL_SCRB : Z := 208 + ADDD_SCRB.    (* [comment removed for export] *)

Definition detail_postB (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fb : Z) (neg : bool) (ds : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  ( ((1 <= length ds)%nat /\ digits_ok ds /\ getr R' 11%bv = Z_to_bv 64 0 /\ parse_post L ar LB FF LKq cr M M' o sp fb neg ds DETAIL_SCRB LB' cr')
  \/ ((length ds = 0%nat \/ ~ digits_ok ds) /\ getr R' 11%bv = Z_to_bv 64 22 /\ noparse_post L ar LB FF cr M M' o sp fb (length ds) DETAIL_SCRB LB' cr') ).

Definition parser_spec_atB (pc SCR cls : Z) (oreg : bv 5) (with_neg : bool)
           (POST : asan_layout -> asan_run -> list (Z * Z) -> list fframe -> list fframe -> credit -> (word -> option byte) -> (word -> option byte) ->
                   bvmap 5 word -> bvmap 5 word -> Z -> Z -> Z -> bool -> list Z -> list (Z * Z) -> credit -> Prop)
           (CRED : list Z -> nat)
           (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (p o sp r fb : Z) (neg : bool) (s : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (Z.of_nat (length s)) ->
    (with_neg = true -> getr R 12%bv = Z_to_bv 64 (if neg then 1 else 0)) -> getr R oreg = Z_to_bv 64 o ->
    (length s <= 4999)%nat -> parse_credit L cr (CRED s) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = cls -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCR -> stksh ar M (sp - SCR) ->
    ffr FF LK 5 -> ffrk 2 FF LK 2 -> ffrs FF sp ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> Z.land fb 3 = 0 -> aobj FF o 32 -> shadow_zero M o 4 ->
    (* [comment removed for export] *)
    L5.bytes_at RSEGS M p s -> Forall (fun c => 0 <= c < 256) s -> asrc IL LB FF M p (Z.of_nat (length s)) ->
    (p + Z.of_nat (length s) <= o \/ o + 32 <= p) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        POST L ar LB FF LK' cr M M' R R' o sp fb neg s LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.

Definition detail_specB := parser_spec_atB DETAIL DETAIL_SCRB 16 13%bv true detail_postB (fun s => length s).

Definition TOBIG_SCRB : Z := 16 + DETAIL_SCRB.

Definition tobig_postB (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fb : Z) (_ : bool) (s : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let neg := fst (split_sign s) in let ds := snd (split_sign s) in
  regs_preserved R R' /\
  ( (parses s /\ getr R' 11%bv = Z_to_bv 64 0 /\ parse_post L ar LB FF LKq cr M M' o sp fb neg ds TOBIG_SCRB LB' cr')
  \/ (no_parse s /\ getr R' 11%bv = Z_to_bv 64 22 /\ noparse_post L ar LB FF cr M M' o sp fb (length ds) TOBIG_SCRB LB' cr') ).

Definition tobig_spec_atB (pc : Z) := parser_spec_atB pc TOBIG_SCRB 0 12%bv false tobig_postB (fun s => length (snd (split_sign s))).
Definition tobig3_specB := tobig_spec_atB TOBIG3.
Definition tobig4_specB := tobig_spec_atB TOBIG4.

Definition CSTR_SCRB : Z := 32 + Z.max TOBIG_SCRB 2560.

Definition cstr_postB (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fbo : Z) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  L5.big_at RSEGS M' o (L5.BO (Z.land fbo 252) 2 (L5.BInl A0 A1)) /\
  credit_le (parse_debit L cr 38) cr' /\
  ahpres L ar LB FF sp CSTR_SCRB [(o, 32)] M M'.

Definition cstr_specB (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r fbo : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ALIT -> parse_credit L cr 38 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp CSTR_SCRB -> stksh ar M (sp - CSTR_SCRB) ->
    ffr FF LK 5 -> ffrk 2 FF LK 2 -> ffrs FF sp ->
    L5.img_clear M 0x10000 0x3c000 ->                               (* [comment removed for export] *)
    (* [comment removed for export] *)
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> aobj FF o 32 -> shadow_zero M o 4 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        cstr_postB L ar LB FF cr M M' R R' o sp fbo cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R CSTR M model) K.

End SCFG_1.
End L5PSB.
