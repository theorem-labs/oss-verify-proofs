(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceABx PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnStatics PnStaticsA PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnSpecsAa_b PnRunAa_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNHAK3.

(* [comment removed for export] *)
Lemma lb_remove_mid p c (pre post : list (Z * Z)) :
  NoDup (map fst (pre ++ (p, c) :: post)) -> lb_remove p (pre ++ (p, c) :: post) = pre ++ post.
Proof.
  induction pre as [|a pre IH]; cbn [app map lb_remove fst]; intros ND.
  - rewrite Z.eqb_refl. reflexivity.
  - inversion ND as [|x0 l0 NI0 ND0]. subst.
    destruct (Z.eqb (fst a) p) eqn:EQ.
    + apply Z.eqb_eq in EQ. exfalso. apply NI0. rewrite EQ, map_app. apply elem_of_app. right. cbn [map fst]. constructor.
    + f_equal. apply IH. exact ND0.
Qed.
Lemma lb_remove_at p c (l pre post : list (Z * Z)) :
  l = pre ++ (p, c) :: post -> NoDup (map fst l) -> lb_remove p l = pre ++ post.
Proof. intros -> ND. exact (lb_remove_mid p c pre post ND). Qed.
(* [comment removed for export] *)
Lemma nodup_mid_notin p c (pre post : list (Z * Z)) m :
  NoDup (map fst (pre ++ (p, c) :: post)) -> ~ In (p, m) pre /\ ~ In (p, m) post.
Proof.
  induction pre as [|a pre IH]; cbn [app map fst]; intros ND.
  - inversion ND as [|x0 l0 NI0 ND0]. subst. split; [intros []|]. intros Hin. apply NI0. apply list_elem_of_In. rewrite in_map_iff. exists (p, m). split; [reflexivity| exact Hin].
  - inversion ND as [|x0 l0 NI0 ND0]. subst. destruct (IH ND0) as [IH1 IH2]. split; [| exact IH2].
    intros [E|Hin]; [| exact (IH1 Hin)]. apply NI0. subst a. cbn [fst]. rewrite map_app. apply elem_of_app. right. cbn [map fst]. constructor.
Qed.

(* [comment removed for export] *)
Lemma own_resetA ps : PNM.bparser_own (PNRA.bpst_reset ps) = PNM.bparser_own ps.
Proof.
  destruct ps as [mo dn src bb nb tb ng tg bg sb sk stk]. unfold PNM.bparser_own, PNM.brest_own, PNRA.bpst_reset. cbn.
  destruct bb; destruct nb; destruct tb; reflexivity.
Qed.
Lemma reset_initA qc b : PNRA.bpst_reset (PNRA.bparser_init qc b) = PNRA.bparser_init qc b.
Proof. reflexivity. Qed.
Lemma own_initA qc b : PNM.bparser_own (PNRA.bparser_init qc b) = [(qc, PM.CHUNK); (b, 40)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma berr_W_hull r : In r (PNST.berr_W PMA.AD PMA.AN) -> (0x6722c0 <= fst r /\ fst r + snd r <= 0x672308) \/ (fst r = 0x693d50 /\ snd r = 544).
Proof.
  unfold PNST.berr_W, PNST.cat_W, PNST.dec_W. cbn. intros Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma scA_cr0 L : PMSPA.scA L PMSP.cr0 = PMSPA.cr0.
Proof. unfold PMSPA.scA, PMSP.cr0, PMSPA.cr0. cbn [fst snd]. rewrite Z.mul_0_r. reflexivity. Qed.

(* [comment removed for export] *)
Section DtorSpecs.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Abbreviation RSEGS := PMA.RSEGS.
Definition vec_dtor_specA (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PNM.bstate),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA PMA.AD L ar R M sp r 1 -> PGSA.ffroomB PNRA.FCB 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> PMSPA.accA M t 8 -> L5.u64_at RSEGS M t v ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> PMSPA.accA M v 24 ->
    PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> In (b, PNM.BSZ * 2 ^ k) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (lb_remove b LB) FF sp (PMSPA.pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (lb_remove b LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Definition vu8_dtor_specA (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (t v sp r : Z) (x : PGV8.v8),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA PMA.AD L ar R M sp r 1 -> PGSA.ffroomB PNRA.FCB 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> PMSPA.accA M t 8 -> L5.u64_at RSEGS M t v ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> PMSPA.accA M v 24 ->
    PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M v x -> incl (PGV8.v8_own x) LB ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        L5CA.ahpres L ar (PNRA.lb_remove_v8 x LB) FF sp (PMSPA.pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNRA.lb_remove_v8 x LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
(* [comment removed for export] *)
Lemma vec_dtor_specA_iff AN : vec_dtor_specA (PNL.pn_vec_dtor AN) <-> @PNRA.vec_dtor_spec SCFG_P RSEGS PMA.AD AN L ar HI.
Proof. split; intros H; exact H. Qed.
Lemma vu8_dtor_specA_iff AN : vu8_dtor_specA (PNL.pn_vu8_dtor AN) <-> @PNRA.vu8_dtor_spec SCFG_P RSEGS PMA.AD AN L ar HI.
Proof. split; intros H; exact H. Qed.
End DtorSpecs.

End PNHAK3.
