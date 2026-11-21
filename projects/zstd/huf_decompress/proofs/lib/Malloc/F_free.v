(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (oracle_ok_refl, oracle_ok_hdr_st, munmap_ok_range_val and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_enframe F_mm_syscalls MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_ntf F_free_A F_free_B F_free_C.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_free_K.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_free () := "C35stdpp4base6lookupC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_filterC35stdpp4base6FilterC45stdpp;list_basics4list9app_inj_1C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc5F_ntf9oracle_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8F_free_K6hdr_stC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6NArith6BinNat1N3eqbC47Corelib4Init9Datatypes3orbK47Corelib7Numbers7BinNums8positive01C47Corelib4Init9Datatypes4andbK59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8F_free_K@hdr_st_cell_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib6Malloc:MallocTree9range_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introK47Corelib4Init5Logic2or02C46Stdlib4Bool4Bool>orb_true_introC59OSSVerify5KrLib6Malloc8ProgDeps9neg_errnoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib6Malloc6F_free?round_up_pg_modC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6in_mapC47Corelib4Init5Logic7f_equalI46Stdlib5Lists4List5NoDup00I47Corelib4Init5Logic2or00C45stdpp;list_basics4list;filter_consC35stdpp4base6filterC35stdpp4base8DecisionC47Corelib4Init5Logic3iffC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_ind".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
                /\ r_base r <= a < r_base r + round_up_pg (r_len r).

(* [comment removed for export] *)
Definition lbrm (LB : list block) (blk : block) : list block :=
  filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oracle_ok_refl m st : oracle_ok m m st.
Proof. intros rid r q h _ _ _ _ _. reflexivity. Qed.

Lemma oracle_ok_hdr_st o m st pf : ticks_ok st -> oracle_ok o m st -> oracle_ok o m (hdr_st st pf).
Proof.
  intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
  rewrite hdr_st_cell_read in Hc by exact TK.
  destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
  - apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - reflexivity.
Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof.
  pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
  set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac cover_intervals tac :=
  let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros lo0 hi0 HW y Hy; cbn [In] in HW;
  repeat (destruct HW as [HW|HW]); try contradiction;
  injection HW; intros; subst lo0 hi0; tac y Hy.

Section CANSEC2. Context {rc : runConstT}.
Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : ATOP <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
End FREE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
  List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
  (forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
  induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
  rewrite IH by (intros x Hx; apply HE; right; exact Hx).
  destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
    pose proof (HE a (or_introl eq_refl)); tauto.
Qed.


End CANSEC2.
