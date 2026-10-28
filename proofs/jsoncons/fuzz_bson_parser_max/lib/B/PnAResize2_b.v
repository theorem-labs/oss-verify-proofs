(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnARzKit_b PnAResizeP_b PnAReset1_b PnAResize1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.

Module PMARZ2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation vstr_at := (PM.vstr_at RSEGS PMSPA.accA).

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (o n S r tg : Z) (s : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hn1 : 0 <= n <= PM.vs_size s + PM.CHUNK.
Hypothesis Hn2 : n < 2 ^ 26 + PM.CHUNK.
Hypothesis OPN : PMA.opnew_spec L ar HI.
Hypothesis OPD : PMA.opdel_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (s' : PM.vstr) (tg' : Z) (cr' : credit),
  regs_preserved R0 R' -> vstr_at M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
  (n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
  L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 1) [(o, 24)] M0 M' ->
  PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV s' tg')) ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.


(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 14336 [(o, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M o 24.
Let sub_in := PMARZ1.sub_in.
Let vfacts := PMARZ1.vfacts L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let bfacts := PMARZ1.bfacts L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let finish_long := PMARZ1.finish_long L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let saves_keep := PMARZ1.saves_keep L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let mem_ok_fill := PMARZ1.mem_ok_fill L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof. intros AC H1 H2 x Hx. apply AC. clear - H1 H2 Hx. lia. Qed.

(* [comment removed for export] *)
Lemma mem_ok_obj (M M1 : word -> option byte) :
  mem_ok M -> mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  0x696000 <= o -> o + 24 <= 2 ^ 47 -> (0x7fff7000 + 17592186048512 <= o \/ o + 24 <= 0x7fff7000) -> mem_ok M1.
Proof using All.
  intros (EK & DK & STK & ACO) MG FR H0 H1 H5. split; [|split; [|split]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
    apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 (fun a => o <= a < o + 24) FR). intros a Ha CA OW Wa.
    apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M1 MG).
  - exact (L5SAR.astk_grows ar M M1 S 14336 STK MG).
  - apply (PMFA.accA_agree M M1 o 24); [| exact ACO].
    apply (PMARZK.agsh_frame M M1 (fun a => o <= a < o + 24) o 24 FR); [intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma mem_ok_mem (M M1 : word -> option byte) (LBo : list (Z * Z)) LK cr Aw model (dst len : Z) :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (LBo ++ LB) FF (S - 80) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, S - 80 - 2560 <= a < S - 80 -> M1 (Z_to_bv 64 a) <> None) -> L5.defined M1 dst len ->
  (exists q A, In (q, A) LBo /\ q <= dst /\ dst + len <= q + A) ->
  mem_ok M1.
Proof using All.
  intros HH (EK & DK & STK & ACO) PRES SD DD (q & A & Hin & X1 & X2). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & ODEF & _).
  destruct (bfacts _ _ _ _ _ _ q A HH (in_or_app _ _ _ (or_introl Hin))) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
  assert (PRESl : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (S - 80) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc Hd. apply PRES; [exact Ha| apply (L5SAR.aclient_appb L ar LB LBo FF (S - 80) 2560 a Hc)| exact Hd]. }
  assert (NC : forall a, aclient L ar LB FF S 14336 a -> ~ (dst <= a < dst + len)).
  { intros a CA Da. exact (PMARS1.own_not_aclient L ar C HI HIok LBo LB FF LK cr Aw M _ q A a S 14336 HH Hin ltac:(lia) CA). }
  split; [|split; [|split]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
    apply (L5SAR.ek_mem L ar LB FF S 14336 (S - 80) 2560 (fun a => dst <= a < dst + len) _ M M1 PRESl); [lia| lia|].
    intros a CA _. exact (NC a CA).
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK).
    apply (L5SAR.dk_mem L ar LB FF S 14336 (S - 80) 2560 (fun a => dst <= a < dst + len) M M1 PRESl SD); [| intros a; clear; lia| lia| lia].
    intros a Da. replace a with (dst + (a - dst)) by lia. apply DD. lia.
  - apply (L5SAR.astk_after_eq L ar C HI HIok _ FF LK cr Aw M M M1 _ S 14336 (S - 80) 2560 HH STK (fun x X => X)); [| exact SD| lia| lia| lia].
    intros a Ha Hs Hns. apply PRES; [exact Ha| apply L5SAR.stack_client; lia| lia].
  - apply (PMFA.accA_agree M M1 o 24); [| exact ACO]. intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply PRES; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| | unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia].
    destruct AO as (f & Hf & F1 & F2). unfold aclient, aclient_g. do 5 right. left. exists f. split; [exact Hf|].
    unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.

(* [comment removed for export] *)
Lemma accA_mem (M M1 : word -> option byte) (LB' : list (Z * Z)) (dst len q A : Z) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF (S - 80) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  In (q, A) LB' -> 0 <= q -> q + A <= 2 ^ 47 -> (dst + len <= 0x7fff7000 \/ 0x10007fff8000 <= dst) -> PMSPA.accA M q A -> PMSPA.accA M1 q A.
Proof using All.
  intros PRES Hin H0 H1 HD AC. apply (PMFA.accA_agree M M1 q A); [| exact AC]. intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
  apply PRES; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| | unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia].
  unfold aclient, aclient_g. do 6 right. exists (q, A). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.

(* [comment removed for export] *)
Lemma saves_mem (M M1 : word -> option byte) (LB' : list (Z * Z)) (dst len : Z) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF (S - 80) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  dst + len <= ahl_ceil ar -> ahl_ceil ar + 4096 + 14336 <= S -> S <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar -> 0 <= len -> saves M -> saves M1.
Proof using All.
  intros PRES H1 H2 H3 H5 H4 SV. apply (saves_keep M M1 (fun a => (a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 80 - 2560 <= a < S - 80)) \/ (dst <= a < dst + len))); [| | lia| exact SV].
  - intros a Ha N. apply PRES; [exact Ha| apply L5SAR.stack_client; lia| intros X; apply N; right; exact X].
  - intros a Ha [X|X]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grow_store (fx : FPState) R M model LK Aw (n0 m B A pc : Z) :
  stok model LK Aw -> n = n0 + m -> 1 <= m -> 0 <= n0 -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  (pc = 0xd5e68 \/ (pc = 0xd5e54 /\ getr R (reg 23) = Z_to_bv 64 22 /\ n0 <= 22 /\ getr R (reg 10) = Z_to_bv 64 B)) ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 20) = Z_to_bv 64 B -> getr R (reg 21) = Z_to_bv 64 A -> getr R (reg 22) = Z_to_bv 64 n ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A ->
  ri_inv HI ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV (PM.VLong A n B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros STO En Hm Hn0 HnA HA HA8 PC A2 A8 A9 A18 A20 A21 A22 KP SV MO ACB HH TBOK GROW CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as G10. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as G24.
  change (bv_modulus 64) with (2 ^ 64) in G10, G24.
  assert (A24 : getr R (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (A10' : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (STORED : exists fx1 R1 M1v, msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) MV (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x77c88) M1v (seg_rom RSEGS))
      /\ mem_grows MV M1v /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o + 0 <= a < o + 0 + 24) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
      /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
      /\ getr R1 (reg 1) = Z_to_bv 64 876172 /\ getr R1 (reg 10) = Z_to_bv 64 (n0 + B) /\ getr R1 (reg 12) = Z_to_bv 64 m
      /\ L5.u64_at RSEGS M1v (o + 16) B /\ L5.u64_at RSEGS M1v o (2 * (A / 2) + 1)).
  { destruct PC as [->|(-> & A23 & Hn022 & A10)].
    - LeanFeed.pfeed P (PMARZP.apF_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
                    | 43%nat => m | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
      exists fx1, R1, M1v. split; [exact MS1|]. split; [exact MG1|]. split; [exact FR1|].
      split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
      split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0].
    - LeanFeed.pfeed P (PMARZP.apDS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
                    | 43%nat => m | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
      exists fx1, R1, M1v. split; [exact MS1|]. split; [exact MG1|]. split; [exact FR1|].
      split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
      split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0]. }
  destruct STORED as (fx1 & R1 & M1v & MS1 & MG1 & FR1 & KS1 & F1 & F10 & F12 & C16 & C0).
  set (W1 := fun a => o + 0 <= a < o + 0 + 24).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R pc R1 0x77c88 M1v W1 K HH AM MS1 MG1 FR1).
  { intros a Ha Wa. unfold W1 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia| lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1.
  assert (OVIS1 : L5A.avis (ahid Aw model1) o 24) by (rewrite HID1; exact OVIS).
  assert (NSH1 : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold W1 in X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  assert (MO1 : mem_ok M1) by (apply (mem_ok_obj M M1 MO MGM1); [intros a Ha N; apply FR1'; [exact Ha| unfold W1; lia]| lia| lia| exact O5]).
  assert (ACB1 : PMSPA.accA M1 B A) by (apply (PMFA.accA_agree M M1 B A (PMARZK.agsh_frame M M1 W1 B A FR1' NSH1 ltac:(lia) ltac:(lia)) ACB)).
  assert (C16' : L5.u64_at RSEGS M1 (o + 16) B).
  { rewrite <- VIS1 in C16. exact (proj1 (L5A.u64_at_vis _ M1 (o + 16) B (L5A.avis_sub _ o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C16). }
  assert (C0' : L5.u64_at RSEGS M1 o (2 * (A / 2) + 1)).
  { rewrite <- VIS1 in C0. exact (proj1 (L5A.u64_at_vis _ M1 o _ (L5A.avis_sub _ o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C0). }
  assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
  assert (AM1' : L5CA.amodel_ok Aw model1) by exact AM1.
  (* [comment removed for export] *)
  apply (PMARZK.fill_stage L ar C HI LY HIok ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M1 model1 fx1 R1 (n0 + B) m (S - 80) 0xd5e8c K HH1 AM1'
           (aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH1) F1 ltac:(split; [lia| reflexivity]) F2 F10 F12 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(pose proof (L5SAR.astk_grows ar M M1 S 14336 STK MGM1) as (_ & _ & _ & _ & D1 & _); apply (L5.defined_sub M1 (S - 14336) 14336); [exact D1| lia| lia])).
  { left. exists B, A. split; [left; reflexivity| lia]. }
  { apply (L5.defined_sub M1 B A); [intros i Hi; apply MGM1; apply DB; exact Hi| lia| lia]. }
  { apply (aacc_sub M1 B A); [exact ACB1| lia| lia]. }
  intros R3 M3 model3 HH3 AM3 MRT3 HID3 MG3 FR3 D3 KS3 A3.
  assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
  set (P3 := fun a => (n0 + B <= a < n0 + B + m) \/ (S - 80 - 2560 <= a < S - 80)).
  assert (FRP : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N. apply FR3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  assert (NSH3 : forall x, P3 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  apply (finish_long fx1 R3 M3 model3 LK Aw B A (tg + 1) (adebit L cr0 A)).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model1 model3 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT3)|]. split; [exact ILK| exact IAW].
  - rewrite (KSR 2%nat) by inl. exact F2.
  - rewrite (KSR 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
  - rewrite (KSR 20%nat) by inl. rewrite (KS1 20%nat) by inl. exact A20.
  - rewrite (KSR 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact A22.
  - intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - apply (saves_keep M1 M3 P3 FRP); [intros a Ha [X|X]; lia| lia|].
    apply (saves_keep M M1 W1); [intros a Ha N; apply FR1'; [exact Ha| exact N]| intros a Ha X; unfold W1 in X; lia| lia| exact SV].
  - apply (mem_ok_fill M1 M3 (n0 + B) m [(B, A)] LK (adebit L cr0 A) Aw model1 HH1 MO1 MG3 FR3 ltac:(lia) ltac:(lia)). right. exists B, A. split; [left; reflexivity| lia].
  - apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia|].
    replace (A + 1) with (2 * (A / 2) + 1) by lia. exact C0'.
  - apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia| exact C16'].
  - lia.
  - lia.
  - lia.
  - exact (PMFA.accA_agree M1 M3 B A (PMARZK.agsh_frame M1 M3 P3 B A FRP NSH3 ltac:(lia) ltac:(lia)) ACB1).
  - exact HH3.
  - exact TBOK.
  - intros X. exfalso. lia.
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma aacc_of_block (M : word -> option byte) u m p k : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + k <= u + m -> aacc M p k.
Proof.
  intros [SZ SP] U8 U0 H1 H2 a Ha. clear - SZ SP U8 U0 H1 H2 Ha. unfold shadow_zero, byte_at in SZ, SP |- *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E : HeapIfaceA.S a = HeapIfaceA.S u + (a / 8 - u / 8)) by (unfold HeapIfaceA.S; Lia.lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
  - left. rewrite E. apply SZ. Lia.lia.
  - right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by Lia.lia. assert (G : a / 8 - u / 8 = m / 8) by Lia.lia.
    split. rewrite E, G. apply SP. exact NZ. Lia.lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma gan_short (fx : FPState) R M model LK Aw (n0 m B A : Z) :
  stok model LK Aw -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> 0 <= n0 <= 22 -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 19) = Z_to_bv 64 (o + 1) -> getr R (reg 21) = Z_to_bv 64 A -> getr R (reg 22) = Z_to_bv 64 n ->
  getr R (reg 23) = Z_to_bv 64 22 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A ->
  ri_inv HI ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV (PM.VLong A n B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5e3c M model) K.
Proof using All.
  intros STO Es En Hm Hn0 HnA HA HA8 A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO ACB HH TBOK GROW CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  LeanFeed.pfeed P (PMARZP.apN_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => o + 1 | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
  unfold PMSPA.cfg.
  destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
  - (* [comment removed for export] *)
    assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by inl; exact A10).
    assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
    assert (F4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; rewrite (KP 4%nat) by (cbn; auto); exact Rtp0).
    apply (PMARZK.move_stage_pre L ar C HI LY HIok IL ICok ILY ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5e3c R1 B (o + 1) n0 (S - 80) 0xd5e54 K
             HH AM K0 MS1 F1 ltac:(split; [lia| reflexivity]) F2 F4 F10 F11 F12 ltac:(lia)).
    { apply (L5SAR.astk_sub ar M M S 14336 80 2560 STK (fun x X => X)); [lia| lia| lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    { exists B, A. split; [left; reflexivity| lia]. }
    { apply (L5.defined_sub M B A); [exact DB| lia| lia]. }
    { apply (aacc_sub M B A); [exact ACB| lia| lia]. }
    { right. exists o, 24. split; [exact AOB| lia]. }
    { apply (L5.defined_sub M o 24); [exact ODEF| lia| lia]. }
    { apply (aacc_sub M o 24); [exact ACO| lia| lia]. }
    { lia. }
    intros R3 M3 model3 RP3 R3_10 PRES3 SDEF3 D3 MRT3 AM3 HH3.
    assert (C3 : forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R1 (reg x)) by (intros x Hx; exact (L5SAR.cs_of_preserved R1 R3 x RP3 Hx)).
    apply (grow_store fx1 R3 M3 model3 LK Aw n0 m B A 0xd5e54).
    + split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
    + exact En.
    + exact Hm.
    + lia.
    + exact HnA.
    + exact HA.
    + exact HA8.
    + right. split; [reflexivity|]. split; [rewrite (C3 23%nat) by inl; rewrite (KS1 23%nat) by inl; exact A23|]. split; [lia| exact R3_10].
    + rewrite (C3 2%nat) by inl. exact F2.
    + rewrite (C3 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
    + rewrite (C3 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact A9.
    + rewrite (C3 18%nat) by inl. rewrite (KS1 18%nat) by inl. exact A18.
    + rewrite (C3 20%nat) by inl. exact F20.
    + rewrite (C3 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact A21.
    + rewrite (C3 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact A22.
    + intros x Hx. rewrite (C3 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + exact (saves_mem M M3 _ B n0 PRES3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SV).
    + apply (mem_ok_mem M M3 [(B, A)] LK (adebit L cr0 A) Aw model B n0 HH MO PRES3 SDEF3 D3). exists B, A. split; [left; reflexivity| lia].
    + exact (accA_mem M M3 _ B n0 B A PRES3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) ACB).
    + exact HH3.
    + exact TBOK.
    + exact GROW.
    + exact CK.
  - (* [comment removed for export] *)
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5e3c R1 0xd5e54 _ K HH AM MS1 (fun x X => X) (fun a _ => eq_refl)).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
    assert (EM1 : M1 = M).
    { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
      change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
    subst M1.
    assert (En0 : n0 = 0) by lia.
    apply (grow_store fx1 R1 M model1 LK Aw n0 m B A 0xd5e54).
    + split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
    + exact En.
    + exact Hm.
    + lia.
    + exact HnA.
    + exact HA.
    + exact HA8.
    + right. split; [reflexivity|]. split; [rewrite (KS1 23%nat) by inl; exact A23|]. split; [lia| rewrite (KS1 10%nat) by inl; rewrite A10; f_equal; lia].
    + rewrite (KS1 2%nat) by inl. exact A2.
    + rewrite (KS1 8%nat) by inl. exact A8.
    + rewrite (KS1 9%nat) by inl. exact A9.
    + rewrite (KS1 18%nat) by inl. exact A18.
    + exact F20.
    + rewrite (KS1 21%nat) by inl. exact A21.
    + rewrite (KS1 22%nat) by inl. exact A22.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + exact SV.
    + exact MO.
    + exact ACB.
    + exact HH1.
    + exact TBOK.
    + exact GROW.
    + exact CK.
Qed.

(* [comment removed for export] *)
Lemma gan_long_del (fx : FPState) R M model LK Aw (c n0 p m B A : Z) :
  stok model LK Aw -> n = n0 + m -> 1 <= m -> 0 <= n0 -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 -> 26 <= c <= 2 ^ 27 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 19) = Z_to_bv 64 p -> getr R (reg 20) = Z_to_bv 64 B -> getr R (reg 21) = Z_to_bv 64 A ->
  getr R (reg 22) = Z_to_bv 64 n -> getr R (reg 23) = Z_to_bv 64 (c - 1) ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> B <> p ->
  ri_inv HI ((B, A) :: (p, c) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV (PM.VLong A n B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5e54 M model) K.
Proof using All.
  intros STO En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A18 A19 A20 A21 A22 A23 KP SV MO ACB NBp HH TBOK GROW CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (bfacts _ _ _ _ _ _ p c HH (or_intror (or_introl eq_refl))) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  LeanFeed.pfeed P (PMARZP.apDL_conc fx R MV (fun j => match j with 2%nat => S | 37%nat => c - 1 | 42%nat => p | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5e54 R1 0xd39ac _ K HH AM MS1 (fun x X => X) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (EM1 : M1 = M).
  { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
    change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
  subst M1.
  (* [comment removed for export] *)
  set (LBc := (B, A) :: (p, c) :: LB) in *.
  assert (Ip : In (p, c) LBc) by (right; left; reflexivity).
  assert (ELB : lb_remove p LBc = (B, A) :: LB).
  { unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B p) as [X|_]; [exfalso; exact (NBp X)|]. rewrite Z.eqb_refl. reflexivity. }
  assert (STKd : L5CA.astk ar M (S - 80) PMSPA.OPDEL_SCR).
  { apply (L5SAR.astk_sub ar M M S 14336 80 PMSPA.OPDEL_SCR STK (fun x X => X)); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD ADDR_A] in OPD.
  apply (OPD fx1 R1 M model1 K LBc FF LK Aw (adebit L cr0 A) p c (S - 80) 0xd5e68 HH1 AM1 K0 Ip).
  { rewrite L5K.rl10. exact F10. }
  { rewrite L5K.rl1. exact F1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS1 2%nat) by inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKd. }
  intros fx4 R4 M4 model4 Aw4 RP4 HP4 MRT4 IAW4 AM4 HH4. rewrite ELB in HP4, HH4.
  assert (C4 : forall x, In x [2; 8; 9; 18; 20; 21; 22]%nat -> getr R4 (reg x) = getr R (reg x)).
  { intros x Hx. rewrite (L5SAR.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  assert (EK14 : L5SAR.ek L ar LB FF S 14336 [(o, 24)] M M4).
  { apply (L5SAR.ek_callee L ar LB [(B, A)] FF [] S 14336 (S - 80) PMSPA.OPDEL_SCR [(o, 24)] [] M M4 HP4); [unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| lia|].
    intros a _ _ rr []. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
    intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (WAPP : PMKA.wapp [(o, 24)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  apply (grow_store fx4 R4 M4 model4 LK Aw4 n0 m B A 0xd5e68).
  - split; [exact AM4|]. split; [exact (L5LZ.model_rt_trans model0 model1 model4 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT4)|].
    split; [exact ILK| intros x Hx; exact (IAW4 x (IAW x Hx))].
  - exact En.
  - exact Hm.
  - exact Hn0.
  - exact HnA.
  - exact HA.
  - exact HA8.
  - left; reflexivity.
  - rewrite (C4 2%nat) by inl. exact A2.
  - rewrite (C4 8%nat) by inl. exact A8.
  - rewrite (C4 9%nat) by inl. exact A9.
  - rewrite (C4 18%nat) by inl. exact A18.
  - rewrite (C4 20%nat) by inl. exact A20.
  - rewrite (C4 21%nat) by inl. exact A21.
  - rewrite (C4 22%nat) by inl. exact A22.
  - intros x Hx. rewrite (L5SAR.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - destruct HP4 as (PR4 & _ & _).
    apply (saves_keep M M4 (fun a => a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 80 - PMSPA.OPDEL_SCR <= a < S - 80))); [| | lia| exact SV].
    + intros a Ha N. apply PR4. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
    + intros a Ha X. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in X. lia.
  - split; [|split; [|split]].
    + exact (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M4 EK EK14).
    + apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M4 DK).
      apply (L5SAR.dk_callee L ar LB [(B, A)] FF [] S 14336 (S - 80) PMSPA.OPDEL_SCR [] M M4 HP4); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia.
    + apply (L5SAR.astk_after_eq L ar C HI HIok LBc FF LK (adebit L cr0 A) Aw M M M4 _ S 14336 (S - 80) PMSPA.OPDEL_SCR HH1 STK (fun x X => X));
        [| | unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| lia| lia].
      * intros a Ha Hs Hns. destruct HP4 as (PR4 & _ & _). apply PR4. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
      * destruct HP4 as (_ & SD4 & _). intros a Ha. replace a with ((S - 80 - PMSPA.OPDEL_SCR) + (a - (S - 80 - PMSPA.OPDEL_SCR))) by lia. apply SD4. lia.
    + exact (PMKA.acc_keepA' L ar LB FF S 14336 [(o, 24)] M M4 EK14 WAPP FRB o 24 AO ACO).
  - exact (PMFA.accA_agree M M4 B A (PMARZK.agsh_ahpres L ar _ FF (S - 80) PMSPA.OPDEL_SCR [] M M4 B A HP4 (or_introl eq_refl) PMKA.wapp_nil ltac:(lia) ltac:(lia)) ACB).
  - exact HH4.
  - exact TBOK.
  - exact GROW.
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma gan_long (fx : FPState) R M model LK Aw (c n0 p m B A : Z) :
  stok model LK Aw -> n = n0 + m -> 1 <= m -> 0 <= n0 < c -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 -> 26 <= c <= 2 ^ 27 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 19) = Z_to_bv 64 p -> getr R (reg 21) = Z_to_bv 64 A ->
  getr R (reg 22) = Z_to_bv 64 n -> getr R (reg 23) = Z_to_bv 64 (c - 1) ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> PMSPA.accA M p c -> (B + A <= p \/ p + c <= B) ->
  ri_inv HI ((B, A) :: (p, c) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV (PM.VLong A n B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5e3c M model) K.
Proof using All.
  intros STO En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO ACB ACP ABp HH TBOK GROW CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (NBp : B <> p) by lia.
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (bfacts _ _ _ _ _ _ p c HH (or_intror (or_introl eq_refl))) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  LeanFeed.pfeed P (PMARZP.apN_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => p | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
  unfold PMSPA.cfg.
  destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
  - assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by inl; exact A10).
    assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
    assert (F4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; rewrite (KP 4%nat) by (cbn; auto); exact Rtp0).
    apply (PMARZK.move_stage_pre L ar C HI LY HIok IL ICok ILY ((B, A) :: (p, c) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5e3c R1 B p n0 (S - 80) 0xd5e54 K
             HH AM K0 MS1 F1 ltac:(split; [lia| reflexivity]) F2 F4 F10 F11 F12 ltac:(lia)).
    { apply (L5SAR.astk_sub ar M M S 14336 80 2560 STK (fun x X => X)); [lia| lia| lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    { exists B, A. split; [left; reflexivity| lia]. }
    { apply (L5.defined_sub M B A); [exact DB| lia| lia]. }
    { apply (aacc_sub M B A); [exact ACB| lia| lia]. }
    { left. exists p, c. split; [right; left; reflexivity| lia]. }
    { apply (L5.defined_sub M p c); [exact DP| lia| lia]. }
    { apply (aacc_sub M p c); [exact ACP| lia| lia]. }
    { lia. }
    intros R3 M3 model3 RP3 R3_10 PRES3 SDEF3 D3 MRT3 AM3 HH3.
    assert (C3 : forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R1 (reg x)) by (intros x Hx; exact (L5SAR.cs_of_preserved R1 R3 x RP3 Hx)).
    apply (gan_long_del fx1 R3 M3 model3 LK Aw c n0 p m B A).
    + split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
    + exact En.
    + exact Hm.
    + lia.
    + exact HnA.
    + exact HA.
    + exact HA8.
    + exact Hc.
    + rewrite (C3 2%nat) by inl. exact F2.
    + rewrite (C3 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
    + rewrite (C3 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact A9.
    + rewrite (C3 18%nat) by inl. rewrite (KS1 18%nat) by inl. exact A18.
    + rewrite (C3 19%nat) by inl. rewrite (KS1 19%nat) by inl. exact A19.
    + rewrite (C3 20%nat) by inl. exact F20.
    + rewrite (C3 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact A21.
    + rewrite (C3 22%nat) by inl. rewrite (KS1 22%nat) by inl. exact A22.
    + rewrite (C3 23%nat) by inl. rewrite (KS1 23%nat) by inl. exact A23.
    + intros x Hx. rewrite (C3 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + exact (saves_mem M M3 _ B n0 PRES3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SV).
    + apply (mem_ok_mem M M3 [(B, A); (p, c)] LK (adebit L cr0 A) Aw model B n0 HH MO PRES3 SDEF3 D3). exists B, A. split; [left; reflexivity| lia].
    + exact (accA_mem M M3 _ B n0 B A PRES3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) ACB).
    + exact NBp.
    + exact HH3.
    + exact TBOK.
    + exact GROW.
    + exact CK.
  - apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5e3c R1 0xd5e54 _ K HH AM MS1 (fun x X => X) (fun a _ => eq_refl)).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
    assert (EM1 : M1 = M).
    { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
      change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
    subst M1.
    apply (gan_long_del fx1 R1 M model1 LK Aw c n0 p m B A).
    + split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
    + exact En.
    + exact Hm.
    + lia.
    + exact HnA.
    + exact HA.
    + exact HA8.
    + exact Hc.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + rewrite (KS1 8%nat) by inl. exact A8.
    + rewrite (KS1 9%nat) by inl. exact A9.
    + rewrite (KS1 18%nat) by inl. exact A18.
    + rewrite (KS1 19%nat) by inl. exact A19.
    + exact F20.
    + rewrite (KS1 21%nat) by inl. exact A21.
    + rewrite (KS1 22%nat) by inl. exact A22.
    + rewrite (KS1 23%nat) by inl. exact A23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + exact SV.
    + exact MO.
    + exact ACB.
    + exact NBp.
    + exact HH1.
    + exact TBOK.
    + exact GROW.
    + exact CK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_credit (s' : PM.vstr) (A : Z) :
  PM.tb_ok s tg -> PM.vs_cap s <= 2 ^ 27 -> 2 * PM.vs_cap s <= PM.vs_cap s' -> PM.vs_cap s' = A - 1 -> A <= 2 ^ 27 ->
  PMSPA.credit_le (scA (PM.pot_text HV s tg)) cr0 ->
  acredit_ok L cr0 A /\ PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV s' (tg + 1))) /\ tg <= 22.
Proof using All.
  intros (T0 & T1 & _) Hc Hc' Ec HA (CR1 & CR2).
  pose proof (PMA.ly_cost L C LY) as (HK & HL & HB).
  assert (Htg : tg <= 22).
  { destruct (Z.eq_dec tg 23) as [E|Nq]; [|lia]. rewrite E in T1. change (2 ^ 23) with 8388608 in T1. lia. }
  pose proof (PMF.pot_text_step HV s s' tg Hc') as (P1 & P2).
  unfold PMSPA.scA, PM.credit_add, PM.cost1, PM.pot_text, PMSPA.HV, LibIfaceAB.heap_view in P1, P2, CR1, CR2 |- *.
  cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in P1, P2, CR1, CR2 |- *. rewrite HK, HL, HB in *. rewrite ?Ec in P1, P2 |- *.
  split; [unfold acredit_ok; rewrite HK, HL, HB; split; nia|]. split; [|exact Htg].
  unfold PMSPA.credit_keep, adebit. rewrite HK, HL, HB. cbn [fst snd]. split; nia.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_new (M M3 : word -> option byte) (BX : list (Z * Z)) LK cr Aw model :
  ri_inv HI (BX ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (BX ++ LB) FF (S - 80) PMSPA.OPNEW_SCR [] M M3 -> mem_ok M3.
Proof using All.
  intros HH (EK & DK & STK & ACO) HP. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
  assert (EK13 : L5SAR.ek L ar LB FF S 14336 [(o, 24)] M M3).
  { apply (L5SAR.ek_callee L ar LB BX FF [] S 14336 (S - 80) PMSPA.OPNEW_SCR [(o, 24)] [] M M3 HP); [unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia|].
    intros a _ _ rr []. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
    intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (WAPP : PMKA.wapp [(o, 24)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  split; [|split; [|split]].
  - exact (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M3 EK EK13).
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M3 DK).
    apply (L5SAR.dk_callee L ar LB BX FF [] S 14336 (S - 80) PMSPA.OPNEW_SCR [] M M3 HP); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia.
  - apply (L5SAR.astk_after_eq L ar C HI HIok _ FF LK cr Aw M M M3 _ S 14336 (S - 80) PMSPA.OPNEW_SCR HH STK (fun x X => X));
      [| | unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia| lia].
    + intros a Ha Hs Hns. destruct HP as (PR & _ & _). apply PR. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
    + destruct HP as (_ & SD & _). intros a Ha. replace a with ((S - 80 - PMSPA.OPNEW_SCR) + (a - (S - 80 - PMSPA.OPNEW_SCR))) by lia. apply SD. lia.
  - exact (PMKA.acc_keepA' L ar LB FF S 14336 [(o, 24)] M M3 EK13 WAPP FRB o 24 AO ACO).
Qed.
Lemma saves_new (M M3 : word -> option byte) (LB' : list (Z * Z)) :
  L5CA.ahpres L ar LB' FF (S - 80) PMSPA.OPNEW_SCR [] M M3 -> ahl_ceil ar + 4096 + 14336 <= S -> S <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar ->
  saves M -> saves M3.
Proof using All.
  intros (PR & _ & _) H1 H2 H3 SV.
  apply (saves_keep M M3 (fun a => a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 80 - PMSPA.OPNEW_SCR <= a < S - 80))); [| | lia| exact SV].
  - intros a Ha Nq. apply PR. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
  - intros a Ha X. unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in X. lia.
Qed.

Lemma grow_short (fx : FPState) R M model LK Aw (n0 m : Z) :
  stok model LK Aw -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> 22 < n -> 0 <= n0 <= 22 -> PM.tb_ok s tg ->
  PMSPA.credit_le (scA (PM.pot_text HV s tg)) cr0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 0 ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 23) = Z_to_bv 64 22 ->
  kept0 R -> saves M -> mem_ok M ->
  ri_inv HI LB FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d9c M model) K.
Proof using All.
  intros STO Es En Hm Hn Hn0 TBOK CR A2 A8 A9 A10 A18 A23 KP SV MO HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (Hn1' : n <= 22 + 16384) by (pose proof Hn1 as Hn1c; rewrite Es in Hn1c; cbn [PM.vs_size] in Hn1c; unfold PM.CHUNK in Hn1c; lia).
  set (A := Z.lor (Z.max 44 n) 7 + 1).
  destruct (PMF.tb_law_first n A ltac:(lia) Hn1' eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
  assert (EA : A = 8 * (Z.max 44 n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
  (* [comment removed for export] *)
  assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd5d9c) MV (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x130338) MV (seg_rom RSEGS))
     /\ getr R2 (reg 1) = Z_to_bv 64 876092 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 (o + 1) /\ getr R2 (reg 21) = Z_to_bv 64 A
     /\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
  { LeanFeed.pfeed P (PMARZP.agrowS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
    assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
    assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
    destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE in F.
    - idtac.
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
      LeanFeed.pfeed Q (PMARZP.arec_conc fx1 R1 MV (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
      destruct Q as (fx2 & R2 & M2v & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
      assert (EM : M2v = MV) by (apply functional_extensionality; exact FRw2). subst M2v.
      assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
      exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
      split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by inl; exact F19|].
      split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by inl; rewrite F22, En; reflexivity|].
      intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
    - exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 48) by (rewrite EA, Z.max_l by lia; reflexivity).
      split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
      split; [rewrite F22, En; reflexivity|].
      intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr0 Aw M model fx fx2 R 0xd5d9c R2 0x130338 _ K HH AM MS2 (fun x X => X) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (EM1 : M1 = M).
  { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
    change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
  subst M1.
  (* [comment removed for export] *)
  destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
  assert (STKn : L5CA.astk ar M (S - 80) PMSPA.OPNEW_SCR).
  { apply (L5SAR.astk_sub ar M M S 14336 80 PMSPA.OPNEW_SCR STK (fun x X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMA.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMA.AD ADDR_A] in OPN.
  apply (OPN fx2 R2 M model1 K LB FF LK Aw cr0 A (S - 80) 0xd5e3c HH1 AM1 K0).
  { rewrite L5K.rl10. exact B10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact B1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS2 2%nat) by inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS2 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 Aw3 B R3_10 RP3 FB HP3 MRT3 IAW3 AM3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4 & FB5) & FBa & FBf & FBd & FBs). cbn [fst snd] in *.
  assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
  { intros x Hx. apply (L5SAR.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
  apply (gan_short fx3 R3 M3 model3 LK Aw3 n0 m B A).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model1 model3 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT3)|].
    split; [exact ILK| intros x Hx; exact (IAW3 x (IAW x Hx))].
  - exact Es.
  - exact En.
  - exact Hm.
  - exact Hn0.
  - lia.
  - lia.
  - exact LA4.
  - rewrite (C3 2%nat) by inl. rewrite (KS2 2%nat) by inl. exact A2.
  - rewrite (C3 8%nat) by inl. rewrite (KS2 8%nat) by inl. exact A8.
  - rewrite (C3 9%nat) by inl. rewrite (KS2 9%nat) by inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by inl. rewrite (KS2 18%nat) by inl. exact A18.
  - rewrite (C3 19%nat) by inl. exact B19.
  - rewrite (C3 21%nat) by inl. exact B21.
  - rewrite (C3 22%nat) by inl. exact B22.
  - rewrite (C3 23%nat) by inl. rewrite (KS2 23%nat) by inl. exact A23.
  - intros x Hx. rewrite (L5SAR.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - exact (saves_new M M3 LB HP3 ltac:(lia) ltac:(lia) ltac:(lia) SV).
  - exact (mem_ok_new M M3 [] LK cr0 Aw model1 HH1 MO HP3).
  - apply (aacc_of_block M3 B A B A FBs); [apply PMFA.mod16_8; exact FB2| lia| lia| lia].
  - exact HH3.
  - assert (Etg : tg = 0) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X); exact X).
    rewrite Etg. split; [lia|]. split; [cbn; lia|]. split; [exact LAW| lia].
  - rewrite Es. cbn. lia.
  - rewrite Es in CK |- *. exact CK.
Qed.

Lemma grow_long (fx : FPState) R M model LK Aw (c n0 p m : Z) :
  stok model LK Aw -> s = PM.VLong c n0 p -> n = n0 + m -> 1 <= m -> c - 1 < n -> 0 <= n0 < c -> PM.tb_ok s tg ->
  26 <= c <= 2 ^ 27 -> c mod 2 = 0 -> L5.u64_at RSEGS M (o + 16) p -> PMSPA.accA M p c ->
  PMSPA.credit_le (scA (PM.pot_text HV s tg)) cr0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 1 ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 23) = Z_to_bv 64 (c - 1) ->
  kept0 R -> saves M -> mem_ok M ->
  ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d9c M model) K.
Proof using All.
  intros STO Es En Hm Hn Hn0 TBOK Hc Hce W16 ACP CR A2 A8 A9 A10 A18 A23 KP SV MO HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
  { apply (proj2 (L5A.u64_at_vis H M (o + 16) p (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (Hn1' : n <= c - 1 + 16384) by (pose proof Hn1 as Hn1c; rewrite Es in Hn1c; cbn [PM.vs_size] in Hn1c; unfold PM.CHUNK in Hn1c; lia).
  assert (TLAW : PM.tb_law c) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X & _); exact X).
  set (A := Z.lor (Z.max (2 * (c - 1)) n) 7 + 1).
  destruct (PMF.tb_law_step c n A TLAW ltac:(lia) ltac:(lia) Hn1' ltac:(lia) eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
  assert (EA : A = 8 * (Z.max (2 * (c - 1)) n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
  (* [comment removed for export] *)
  assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd5d9c) MV (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x130338) MV (seg_rom RSEGS))
     /\ getr R2 (reg 1) = Z_to_bv 64 876092 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 p /\ getr R2 (reg 21) = Z_to_bv 64 A
     /\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
  { LeanFeed.pfeed P (PMARZP.agrowL_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 37%nat => c - 1 | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
    assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
    assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
    assert (MODC : (2 * (c - 1)) mod 2 ^ 64 = 2 * (c - 1)) by (rewrite Z.mod_small; lia).
    destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE, MODC in F.
    - idtac.
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
      LeanFeed.pfeed Q (PMARZP.arec_conc fx1 R1 MV (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
      destruct Q as (fx2 & R2 & M2v & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
      assert (EM : M2v = MV) by (apply functional_extensionality; exact FRw2). subst M2v.
      assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
      exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
      split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by inl; exact F19|].
      split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by inl; rewrite F22, En; reflexivity|].
      intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
    - exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 8 * ((2 * (c - 1)) / 8) + 8) by (rewrite EA, Z.max_l by lia; reflexivity).
      split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
      split; [rewrite F22, En; reflexivity|].
      intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr0 Aw M model fx fx2 R 0xd5d9c R2 0x130338 _ K HH AM MS2 (fun x X => X) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (EM1 : M1 = M).
  { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
    change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
  subst M1.
  (* [comment removed for export] *)
  destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
  assert (STKn : L5CA.astk ar M (S - 80) PMSPA.OPNEW_SCR).
  { apply (L5SAR.astk_sub ar M M S 14336 80 PMSPA.OPNEW_SCR STK (fun x X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMA.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMA.AD ADDR_A] in OPN.
  apply (OPN fx2 R2 M model1 K ((p, c) :: LB) FF LK Aw cr0 A (S - 80) 0xd5e3c HH1 AM1 K0).
  { rewrite L5K.rl10. exact B10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact B1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS2 2%nat) by inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS2 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 Aw3 B R3_10 RP3 FB HP3 MRT3 IAW3 AM3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4 & FB5) & FBa & FBf & FBd & FBs). cbn [fst snd] in *.
  assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
  { intros x Hx. apply (L5SAR.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
  assert (ABp : B + A <= p \/ p + c <= B) by (exact (FBa (p, c) ltac:(left; reflexivity))).
  apply (gan_long fx3 R3 M3 model3 LK Aw3 c n0 p m B A).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model1 model3 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT3)|].
    split; [exact ILK| intros x Hx; exact (IAW3 x (IAW x Hx))].
  - exact En.
  - exact Hm.
  - exact Hn0.
  - lia.
  - lia.
  - exact LA4.
  - exact Hc.
  - rewrite (C3 2%nat) by inl. rewrite (KS2 2%nat) by inl. exact A2.
  - rewrite (C3 8%nat) by inl. rewrite (KS2 8%nat) by inl. exact A8.
  - rewrite (C3 9%nat) by inl. rewrite (KS2 9%nat) by inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by inl. rewrite (KS2 18%nat) by inl. exact A18.
  - rewrite (C3 19%nat) by inl. exact B19.
  - rewrite (C3 21%nat) by inl. exact B21.
  - rewrite (C3 22%nat) by inl. exact B22.
  - rewrite (C3 23%nat) by inl. rewrite (KS2 23%nat) by inl. exact A23.
  - intros x Hx. rewrite (L5SAR.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - exact (saves_new M M3 _ HP3 ltac:(lia) ltac:(lia) ltac:(lia) SV).
  - exact (mem_ok_new M M3 [(p, c)] LK cr0 Aw model1 HH1 MO HP3).
  - apply (aacc_of_block M3 B A B A FBs); [apply PMFA.mod16_8; exact FB2| lia| lia| lia].
  - exact (PMFA.accA_agree M M3 p c (PMARZK.agsh_ahpres L ar _ FF (S - 80) PMSPA.OPNEW_SCR [] M M3 p c HP3 (or_introl eq_refl) PMKA.wapp_nil ltac:(lia) ltac:(lia)) ACP).
  - exact ABp.
  - exact HH3.
  - pose proof TBOK as (Tg0 & Tg1 & _). rewrite Es in Tg1. cbn [PM.vs_cap] in Tg1.
    split; [lia|]. split; [cbn [PM.vs_cap]; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia|]. split; [exact LAW| lia].
  - rewrite Es. cbn. lia.
  - rewrite Es in CK |- *. exact CK.
Qed.

End Call.
End WithHeap.
End PMARZ2.
