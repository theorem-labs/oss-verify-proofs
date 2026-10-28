(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmStatics PmStaticsA PnStatics PnStaticsA HeapIfaceABx
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARBS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition SCR : Z := 14336.                       (* [comment removed for export] *)
Definition bparser_at := (PNM.bparser_at RSEGS PMA.AD PMSPA.accA PNRA.annA (pa_vp_parser PMA.AD)).

(* [comment removed for export] *)
Definition st1 (s : PNM.bpst) : PNM.bpst :=
  PNM.BPST 1 0 (PNM.b_src s) (PGV8.v8_clear (PNM.b_bb s)) (PNM.b_nb s) (PNM.b_tb s)
           (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s).
Definition st2 (s : PNM.bpst) : PNM.bpst :=
  PNM.BPST 1 0 (PNM.b_src s) (PGV8.v8_clear (PNM.b_bb s)) (PNRA.vs_clear (PNM.b_nb s)) (PNRA.vs_clear (PNM.b_tb s))
           (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) [].

Section Call.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PNM.bpst).

Definition op : Z := fb + 464.
(* [comment removed for export] *)
Definition W : list L5.range := [(op + 8, 8); (op + 320, 24); (op + 344, 24); (op + 368, 24); (op + 392, 24)].

(* [comment removed for export] *)
Definition pre : Prop :=
  ri_inv HI (PNM.bparser_own s ++ LBX) FF LK0 cr Aw0 M0 (vml_of model0) /\ L5CA.amodel_ok Aw0 model0 /\ K [] /\ PMSPA.entryA PMA.AD L ar R0 M0 sp r 1
  /\ PGSA.ffroomB PNRA.FCB 1 FF LK0 /\ PMSPA.ffrsA FF sp /\ PNRA.frame_okB FF fb
  /\ getr R0 (reg 10) = Z_to_bv 64 op /\ bparser_at M0 op (fb + 96) s /\ PMSPA.accA M0 op 416 /\ PMSTA.base_okA RSEGS PMA.AD M0.

(* [comment removed for export] *)
Definition kont : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
    regs_preserved R0 R' -> bparser_at M' op (fb + 96) (PNRA.bpst_reset s) ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 1) W M0 M' ->
    model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx') R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (sp - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20))).

(* [comment removed for export] *)
Definition smid (w18 : word) (sk : PNM.bpst) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 op /\ getr R (reg 18) = w18 /\ getr R (reg 19) = Z_to_bv 64 2147450880
  /\ (forall k, In k [3; 4; 9; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k))
  /\ saves M /\ bparser_at M op (fb + 96) sk /\ PMSPA.accA M op 416 /\ PMSTA.base_okA RSEGS PMA.AD M
  /\ L5CA.astk ar M sp SCR /\ shadow_zero M (sp - SCR) (SCR / 8)
  /\ ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw
  /\ L5SAR.ek L ar LBX FF sp SCR W M0 M /\ L5SAR.dk L ar LBX FF sp SCR M0 M.

Definition smid1 := smid (getr R0 (reg 18)) (st1 s).              (* [comment removed for export] *)
Definition smid2 := smid (Z_to_bv 64 (op + 392)) (st2 s).      (* [comment removed for export] *)
End Call.

(* [comment removed for export] *)
Lemma own_st1 s : PNM.bparser_own (st1 s) = PNM.bparser_own s.
Proof. destruct s as [mo dn src bb nb tb ng tg bg sb sk stk]. unfold st1, PNM.bparser_own, PNM.brest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. destruct bb; reflexivity. Qed.
Lemma own_st2 s : PNM.bparser_own (st2 s) = PNM.bparser_own s.
Proof. destruct s as [mo dn src bb nb tb ng tg bg sb sk stk]. unfold st2, PNM.bparser_own, PNM.brest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. destruct bb, nb, tb; reflexivity. Qed.

Section Spec.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
(* [comment removed for export] *)
Definition reset_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PNM.bpst),
    ri_inv HI (PNM.bparser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA PMA.AD L ar R M sp r 1 ->
    PGSA.ffroomB PNRA.FCB 1 FF LK -> PMSPA.ffrsA FF sp -> PNRA.frame_okB FF fb ->
    getr R 10%bv = Z_to_bv 64 (fb + 464) -> bparser_at M (fb + 464) (fb + 96) s ->
    PMSPA.accA M (fb + 464) 416 -> PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> bparser_at M' (fb + 464) (fb + 96) (PNRA.bpst_reset s) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 1) [(fb + 464 + 8, 8); (fb + 464 + 320, 24); (fb + 464 + 344, 24); (fb + 464 + 368, 24); (fb + 464 + 392, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNM.bparser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx') R' r M' model') K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xadb68 M model) K.

(* [comment removed for export] *)
Lemma spec_of : (forall (fx : FPState) R M model K LBX FF LK Aw cr sp r fb s,
   pre L ar HI R M model K LBX FF LK Aw cr sp r fb s -> kont L ar HI R M model K LBX FF LK Aw cr sp r fb s ->
   srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xadb68 M model) K) -> reset_spec.
Proof.
  intros HK. unfold reset_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb s HH AM K0 ENT FRM FRS FOK A10 PA ACC BASE KONT.
  apply (HK fx R M model K LBX FF LK Aw cr sp r fb s).
  - exact (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj A10 (conj PA (conj ACC BASE)))))))))).
  - exact KONT.
Qed.
(* [comment removed for export] *)
Lemma weak_of : reset_spec -> (forall M fb s, bparser_at M (fb + 464) (fb + 96) s -> PMSPA.accA M (fb + 464) 416 /\ PMSTA.base_okA RSEGS PMA.AD M) ->
  PNRAa.reset_spec L ar HI.
Proof.
  intros RS ACCP. unfold PNRAa.reset_spec, PNRA.reset_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb s HH AM K0 ENT FRM FRS FOK A10 PA KONT.
  unfold PNRA.o_p, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PmSpecs.PMSP.o_p, PmSpecs.PMSP.o_is in *.
  cbn [PNL.pn_reset pa_off_p pa_off_is PNRAa.AD PNRAa.AN PMA.AD PMA.AN ADDR_A NADDR_A] in *.
  change PNM.OFF_BB with 320 in *. change PNM.OFF_NB with 344 in *. change PNM.OFF_TB with 368 in *. change PNM.OFF_STK with 392 in *.
  destruct (ACCP M fb s PA) as (ACC & BASE).
  exact (RS fx R M model K LBX FF LK Aw cr sp r fb s HH AM K0 ENT FRM FRS FOK A10 PA ACC BASE KONT).
Qed.
End Spec.
End PNARBS.
