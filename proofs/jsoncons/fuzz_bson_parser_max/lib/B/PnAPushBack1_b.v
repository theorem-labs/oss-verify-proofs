(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnARzKit_b PnAPushBackP_b PnAReset1_b Ba0_code_d36f8_d36fc_b.
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

Module PNAPB1.
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
Variables (o ch S r tg : Z) (x : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hch : 0 <= ch < 256.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 ch.
Hypothesis SZ : PM.vs_size x < 2 ^ 26.
Hypothesis OPN : PMA.opnew_spec L ar HI.
Hypothesis OPD : PMA.opdel_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (x' : PM.vstr) (tg' : Z) (cr' : credit),
  regs_preserved R0 R' -> vstr_at M' o x' -> PM.vs_size x' = PM.vs_size x + 1 -> PM.tb_ok x' tg' ->
  (PM.vs_size x < PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ tg' = tg) ->
  L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 1) [(o, 24)] M0 M' ->
  PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV x tg)) (scA (PM.pot_text HV x' tg')) ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.vs_own x' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall y, In y [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg y) = getr R0 (reg y).
(* [comment removed for export] *)
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 14336 [(o, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M o 24.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (y & Hy & E). apply Nat.eqb_eq in E. subst y. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma regs_back (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S -> getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) ->
  getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) -> getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) ->
  getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) -> getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) ->
  kept0 R1 -> regs_preserved R0 R1.
Proof using All.
  intros E2 E8 E9 E18 E19 E20 E21 E22 KP. apply L5SAR.preserved_by_index. intros y Hy. unfold L5SAR.cs_all in Hy.
  destruct Hy as [<-|Hy]; [rewrite E2, Rsp0; reflexivity|].
  destruct Hy as [<-|Hy]; [apply KP; cbn; auto|]. destruct Hy as [<-|Hy]; [apply KP; cbn; auto|].
  destruct Hy as [<-|Hy]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E22; apply Z_to_bv_bv_unsigned|].
  apply KP. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
Qed.

(* [comment removed for export] *)
Lemma vfacts LB' LK cr Aw M model :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.astk ar M S 14336 ->
  (forall a m, S - 14336 <= a -> a + m <= 2 ^ 47 -> L5A.avis (ahid Aw model) a m)
  /\ (0x696000 <= o /\ o + 24 <= ahl_ceil ar /\ (0x7fff7000 + 17592186048512 <= o \/ o + 24 <= 0x7fff7000))
  /\ L5.defined M o 24 /\ L5A.avis (ahid Aw model) o 24
  /\ (forall q m a k, In (q, m) LB' -> q <= a -> a + k <= q + m -> L5A.avis (ahid Aw model) a k).
Proof using All.
  intros HH STK. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB' FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB' FF LK cr Aw M model o 24 S 14336 HH (PMKA.aobj_of_aobjA FF o 24 AO Ho3) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & _).
  split; [intros a m X1 X2; apply VIS; lia|]. split; [lia|]. split; [exact ODEF|]. split; [exact OVIS|].
  intros q m a k Hin X1 X2. exact (VBLK q m a k Hin X1 X2).
Qed.

(* [comment removed for export] *)
Lemma bfacts LB' LK cr Aw M V q m :
  ri_inv HI LB' FF LK cr Aw M V -> In (q, m) LB' ->
  4096 <= q /\ (q + m <= 0x10000 \/ 0x696000 <= q) /\ q mod 16 = 0 /\ 0 < m /\ q + m <= ahl_ceil ar /\ (q + m <= 0x7fff7000 \/ 0x10007fff8000 <= q)
  /\ q + m <= 2 ^ 47 /\ L5.defined M q m /\ (q + m <= o \/ o + 24 <= q).
Proof using All.
  intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB (q, m) Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & DQ & _ & _ & _ & FA & _). cbn [fst snd] in *.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  destruct AO as (f & Hf & X1 & X2). specialize (FA f (in_or_app _ _ _ (or_introl Hf))).
  repeat split; try lia. exact DQ.
Qed.

(* [comment removed for export] *)
Lemma saves_vis LB' LK cr Aw M model :
  ri_inv HI LB' FF LK cr Aw M (vml_of model) -> L5CA.astk ar M S 14336 ->
  forall a v, S - 64 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof using All.
  intros HH STK a v X1 X2 X. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & _).
  apply (proj2 (L5A.u64_at_vis (ahid Aw model) M a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail (fx : FPState) R M model LK Aw (n p A B pc a0 s5 tg' : Z) (cr' : credit) :
  stok model LK Aw -> n = PM.vs_size x -> 0 <= n -> n + 2 <= A -> 26 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  (pc = 0xd5c98 /\ s5 = 23 \/ pc = 0xd5cac) ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 a0 ->
  getr R (reg 18) = Z_to_bv 64 p -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 s5 -> getr R (reg 22) = Z_to_bv 64 B ->
  0 <= a0 < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= s5 < 2 ^ 64 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A ->
  ri_inv HI ((B, A) :: LB) FF LK cr' Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A (n + 1) B) tg' -> PM.vs_cap x = n ->
  PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV x tg)) (scA (PM.pot_text HV (PM.VLong A (n + 1) B) tg')) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros STO En Hn0 HnA HA HA8 PC A2 A8 A9 A10 A18 A19 A20 A21 A22 Ha0 Hp Hs5 KP SV (EK & DK & STK & ACO) ACB HH TBOK FULL CK.
  destruct STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  pose proof (saves_vis _ _ _ _ _ _ HH STK) as VU64.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
  pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
  pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
  pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
  pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
  assert (WST : L5.writable RSEGS MV (S - 64) 64).
  { apply (proj2 (L5A.writable_vis H M (S - 64) 64 (VSTK (S - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (WBV : L5.writable RSEGS MV (B + n) 2).
  { apply (proj2 (L5A.writable_vis H M (B + n) 2 (VBLK B A (B + n) 2 (or_introl eq_refl) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B A (B + n) 2 DB); lia| lia| lia]. }
  assert (Dbo : B + n + 2 <= o \/ o + 24 <= B + n) by lia.
  assert (Dbf : B + n + 2 <= S - 64 \/ S - 64 + 64 <= B + n) by lia.
  assert (Dof : S - 64 + 64 <= o \/ o + 24 <= S - 64) by lia.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in *.
  (* [comment removed for export] *)
  assert (STORED : exists fx1 R1 M1v, msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) MV (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xd5cf4) M1v (seg_rom RSEGS))
      /\ mem_grows MV M1v /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> ~ (B + n <= a < B + n + 2) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
      /\ (forall y, In y [3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (reg y) = getr R (reg y))
      /\ getr R1 (reg 1) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 1))) /\ getr R1 (reg 2) = Z_to_bv 64 S
      /\ getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) /\ getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9)))
      /\ getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) /\ getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19)))
      /\ getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) /\ getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21)))
      /\ getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))
      /\ L5.u8_at RSEGS M1v (B + n + 1) 0 /\ L5.u8_at RSEGS M1v (B + n) ch
      /\ L5.u64_at RSEGS M1v (o + 8) (n + 1) /\ L5.u64_at RSEGS M1v (o + 16) B /\ L5.u64_at RSEGS M1v o (2 * (A / 2) + 1)).
  { destruct PC as [(-> & ->)| ->].
    - LeanFeed.pfeed PP (PNAPBP.apbTS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 41%nat => p
                    | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                    | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                    | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 54%nat => a0 | 56%nat => ch | _ => 0 end)) ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F2 & F8 & F9 & _ & _ & F18 & F19 & F20 & F21 & F22 & C1 & C2 & C3 & C4 & C5).
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X Y; apply FR1; [exact Ha| lia| lia]|].
      split; [intros y Hy; apply KS1; revert y Hy; apply sub_in; vm_compute; reflexivity|].
      repeat split; first [assumption | (rewrite Z.add_comm; assumption) | (replace (B + n + 1) with ((B + n) + 1) by lia; assumption)].
    - LeanFeed.pfeed PP (PNAPBP.apbT_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 40%nat => s5 | 41%nat => p
                    | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                    | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                    | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 55%nat => a0 | 56%nat => ch | _ => 0 end)) ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F2 & F8 & F9 & _ & _ & F18 & F19 & F20 & F21 & F22 & C1 & C2 & C3 & C4 & C5).
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X Y; apply FR1; [exact Ha| lia| lia]|].
      split; [intros y Hy; apply KS1; revert y Hy; apply sub_in; vm_compute; reflexivity|].
      repeat split; first [assumption | (rewrite Z.add_comm; assumption) | (replace (B + n + 1) with ((B + n) + 1) by lia; assumption)]. }
  destruct STORED as (fx1 & R1 & M1v & MS1 & MG1 & FZ1 & KS1 & F1 & F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & C1 & C2 & C3 & C4 & C5).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite F1, Z_to_bv_bv_unsigned; exact Rra0).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd5cf4 W_d36f8 r F_d36f8 eq_refl D_d36f8 R1ra ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => (o <= a < o + 24) \/ (B + n <= a < B + n + 2)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok ((B, A) :: LB) FF LK cr' Aw M model fx fx1 R pc R1 r M1v W1 K HH AM).
  { eapply msteps_trans; [exact MS1| exact MS2]. }
  { exact MG1. }
  { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa]; split.
    - apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
    - lia.
    - apply (L5SAR.block_client L ar ((B, A) :: LB) FF 0 0 B A a (or_introl eq_refl)); lia.
    - lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (NSH : forall y, W1 y -> y < BIGSHADOW_LO \/ BIGSHADOW_HI <= y) by (intros y [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  assert (OVIS1 : L5A.avis (ahid Aw model1) o 24) by (rewrite HID1; exact OVIS).
  assert (TOM : forall a v, o <= a -> a + 8 <= o + 24 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (L5A.avis_sub _ o 24 a 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
  apply (KONT fx1 R1 M1 model1 LK Aw (PM.VLong A (n + 1) B) tg' cr').
  - apply regs_back; try assumption.
    intros y Hy. rewrite (KS1 y Hy). apply KP. exact Hy.
  - split; [intros i Hi; apply MGM1; apply ODEF; exact Hi|].
    split; [apply (PMFA.accA_agree M M1 o 24 (PMARZK.agsh_frame M M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
    split; [replace (A + 1) with (2 * (A / 2) + 1) by lia; apply (TOM o _ ltac:(lia) ltac:(lia) C5)|].
    split; [apply (TOM (o + 8) _ ltac:(lia) ltac:(lia) C3)|].
    split; [apply (TOM (o + 16) _ ltac:(lia) ltac:(lia) C4)|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [intros i Hi; apply MGM1; apply DB; exact Hi|].
    apply (PMFA.accA_agree M M1 B A (PMARZK.agsh_frame M M1 W1 B A FR1 NSH ltac:(lia) ltac:(lia)) ACB).
  - cbn [PM.vs_size]. lia.
  - exact TBOK.
  - intros X. exfalso. rewrite FULL in X. lia.
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
    + apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
      apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 W1 FR1). intros a Ha CA OW Wa. destruct Wa as [X|X].
      * apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * exact (PMARS1.own_not_aclient L ar C HI HIok [(B, A)] LB FF LK cr' Aw M _ B A a S 14336 HH (or_introl eq_refl) ltac:(lia) CA).
    + pose proof (L5SAR.astk_grows ar M M1 S 14336 STK MGM1) as (_ & _ & _ & _ & D1 & _). exact D1.
    + apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M1 MGM1).
  - exact CK.
  - exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1).
  - exact ILK.
  - exact IAW.
  - exact AM1.
  - exact HH1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof. intros AC H1 H2 y Hy. apply AC. clear - H1 H2 Hy. lia. Qed.

Lemma saves_keep (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, S - 64 <= a < S -> ~ P a) ->
  140735332483136 <= S <= 2 ^ 47 -> saves M -> saves M'.
Proof using All.
  intros FRZ X HS (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
  assert (AG : forall a, S - 64 <= a -> a + 8 <= S -> L5C.agree_on M M' a 8).
  { intros a H1 H2 i Hi. apply FRZ; [lia| apply X; lia]. }
  unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [apply AG; lia|lia|lia|eassumption]).
Qed.

(* [comment removed for export] *)
Lemma mem_ok_mem (M M1 : word -> option byte) (LBo : list (Z * Z)) LK cr Aw model (dst len : Z) :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (LBo ++ LB) FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, S - 64 - 2560 <= a < S - 64 -> M1 (Z_to_bv 64 a) <> None) -> L5.defined M1 dst len ->
  (exists q A, In (q, A) LBo /\ q <= dst /\ dst + len <= q + A) ->
  mem_ok M1.
Proof using All.
  intros HH (EK & DK & STK & ACO) PRES SD DD (q & A & Hin & X1 & X2). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & ODEF & _).
  destruct (bfacts _ _ _ _ _ _ q A HH (in_or_app _ _ _ (or_introl Hin))) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
  assert (PRESl : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc Hd. apply PRES; [exact Ha| apply (L5SAR.aclient_appb L ar LB LBo FF (S - 64) 2560 a Hc)| exact Hd]. }
  assert (NC : forall a, aclient L ar LB FF S 14336 a -> ~ (dst <= a < dst + len)).
  { intros a CA Da. exact (PMARS1.own_not_aclient L ar C HI HIok LBo LB FF LK cr Aw M _ q A a S 14336 HH Hin ltac:(lia) CA). }
  split; [|split; [|split]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
    apply (L5SAR.ek_mem L ar LB FF S 14336 (S - 64) 2560 (fun a => dst <= a < dst + len) _ M M1 PRESl); [lia| lia|].
    intros a CA _. exact (NC a CA).
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK).
    apply (L5SAR.dk_mem L ar LB FF S 14336 (S - 64) 2560 (fun a => dst <= a < dst + len) M M1 PRESl SD); [| intros a; clear; lia| lia| lia].
    intros a Da. replace a with (dst + (a - dst)) by lia. apply DD. lia.
  - apply (L5SAR.astk_after_eq L ar C HI HIok _ FF LK cr Aw M M M1 _ S 14336 (S - 64) 2560 HH STK (fun y X => X)); [| exact SD| lia| lia| lia].
    intros a Ha Hs Hns. apply PRES; [exact Ha| apply L5SAR.stack_client; lia| lia].
  - apply (PMFA.accA_agree M M1 o 24); [| exact ACO]. intros y Hy. pose proof (PMKA.S_in_shadow y ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply PRES; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| | unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia].
    destruct AO as (f & Hf & F1 & F2). unfold aclient, aclient_g. do 5 right. left. exists f. split; [exact Hf|].
    unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.

(* [comment removed for export] *)
Lemma accA_mem (M M1 : word -> option byte) (LB' : list (Z * Z)) (dst len q A : Z) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  In (q, A) LB' -> 0 <= q -> q + A <= 2 ^ 47 -> (dst + len <= 0x7fff7000 \/ 0x10007fff8000 <= dst) -> PMSPA.accA M q A -> PMSPA.accA M1 q A.
Proof using All.
  intros PRES Hin H0 H1 HD AC. apply (PMFA.accA_agree M M1 q A); [| exact AC]. intros y Hy. pose proof (PMKA.S_in_shadow y ltac:(lia)) as SX.
  unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
  apply PRES; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| | unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia].
  unfold aclient, aclient_g. do 6 right. exists (q, A). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
Qed.

(* [comment removed for export] *)
Lemma saves_mem (M M1 : word -> option byte) (LB' : list (Z * Z)) (dst len : Z) :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB' FF (S - 64) 2560 a -> ~ (dst <= a < dst + len) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  dst + len <= ahl_ceil ar -> ahl_ceil ar + 4096 + 14336 <= S -> S <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar -> 0 <= len -> saves M -> saves M1.
Proof using All.
  intros PRES H1 H2 H3 H5 H4 SV. apply (saves_keep M M1 (fun a => (a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 64 - 2560 <= a < S - 64)) \/ (dst <= a < dst + len))); [| | lia| exact SV].
  - intros a Ha N. apply PRES; [exact Ha| apply L5SAR.stack_client; lia| intros X; apply N; right; exact X].
  - intros a Ha [X|X]; lia.
Qed.

Lemma aacc_of_block (M : word -> option byte) u m p k : shadow_blk M u m -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + k <= u + m -> aacc M p k.
Proof.
  intros [SZ0 SP] U8 U0 H1 H2 a Ha. clear - SZ0 SP U8 U0 H1 H2 Ha. unfold shadow_zero, byte_at in SZ0, SP |- *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (E : HeapIfaceA.S a = HeapIfaceA.S u + (a / 8 - u / 8)) by (unfold HeapIfaceA.S; Lia.lia).
  destruct (Z_lt_le_dec (a / 8 - u / 8) (m / 8)) as [LT|GE].
  - left. rewrite E. apply SZ0. Lia.lia.
  - right. exists (m mod 8). assert (NZ : m mod 8 <> 0) by Lia.lia. assert (G : a / 8 - u / 8 = m / 8) by Lia.lia.
    split. rewrite E, G. apply SP. exact NZ. Lia.lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_new_short (fx : FPState) R M model LK Aw (A B : Z) :
  stok model LK Aw -> PM.vs_size x = 22 -> PM.vs_cap x = 22 -> 26 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 (o + 1) -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 22 -> getr R (reg 21) = Z_to_bv 64 23 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A ->
  ri_inv HI ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A (22 + 1) B) (tg + 1) ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV x tg)) (scA (PM.pot_text HV (PM.VLong A (22 + 1) B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5c88 M model) K.
Proof using All.
  intros STO En FULL HA HA8 A2 A8 A9 A10 A18 A19 A20 A21 KP SV MO ACB HH TBOK CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  pose proof (saves_vis _ _ _ _ _ _ HH STK) as VU64.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
  pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
  pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
  pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
  pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
  assert (WST : L5.writable RSEGS MV (S - 64) 64).
  { apply (proj2 (L5A.writable_vis H M (S - 64) 64 (VSTK (S - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 64 + 64 <= o \/ o + 24 <= S - 64) by lia.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed PP (PNAPBP.apbN_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => 22 | 40%nat => 23 | 41%nat => o + 1
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 56%nat => ch | _ => 0 end)) ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F11 & F12 & F22).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by inl; exact A10).
  assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 64)) by (rewrite (KS1 2%nat) by inl; exact A2).
  assert (F4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; rewrite (KP 4%nat) by (cbn; auto); exact Rtp0).
  apply (PMARZK.move_stage_pre L ar C HI LY HIok IL ICok ILY ((B, A) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5c88 R1 B (o + 1) 22 (S - 64) 0xd5c98 K
           HH AM K0 MS1 F1 ltac:(split; [lia| reflexivity]) F2 F4 F10 F11 F12 ltac:(lia)).
  { apply (L5SAR.astk_sub ar M M S 14336 64 2560 STK (fun y X => X)); [lia| lia| lia|]. replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exists B, A. split; [left; reflexivity| lia]. }
  { apply (L5.defined_sub M B A); [exact DB| lia| lia]. }
  { apply (aacc_sub M B A); [exact ACB| lia| lia]. }
  { right. exists o, 24. split; [exact AOB| lia]. }
  { apply (L5.defined_sub M o 24); [exact ODEF| lia| lia]. }
  { apply (aacc_sub M o 24); [exact ACO| lia| lia]. }
  { lia. }
  intros R3 M3 model3 RP3 R3_10 PRES3 SDEF3 D3 MRT3 AM3 HH3.
  assert (C3 : forall y, In y L5SAR.cs_all -> getr R3 (reg y) = getr R1 (reg y)) by (intros y Hy; exact (L5SAR.cs_of_preserved R1 R3 y RP3 Hy)).
  apply (tail fx1 R3 M3 model3 LK Aw 22 (o + 1) A B 0xd5c98 B 23 (tg + 1) (adebit L cr0 A)).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
  - symmetry. exact En.
  - lia.
  - lia.
  - exact HA.
  - exact HA8.
  - left. split; reflexivity.
  - rewrite (C3 2%nat) by inl. exact F2.
  - rewrite (C3 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
  - rewrite (C3 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by inl. rewrite (KS1 18%nat) by inl. exact A18.
  - rewrite (C3 19%nat) by inl. rewrite (KS1 19%nat) by inl. exact A19.
  - rewrite (C3 20%nat) by inl. rewrite (KS1 20%nat) by inl. exact A20.
  - rewrite (C3 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact A21.
  - rewrite (C3 22%nat) by inl. exact F22.
  - lia.
  - lia.
  - lia.
  - intros y Hy. rewrite (C3 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - exact (saves_mem M M3 _ B 22 PRES3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SV).
  - apply (mem_ok_mem M M3 [(B, A)] LK (adebit L cr0 A) Aw model B 22 HH MO PRES3 SDEF3 D3). exists B, A. split; [left; reflexivity| lia].
  - exact (accA_mem M M3 _ B 22 B A PRES3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) ACB).
  - exact HH3.
  - exact TBOK.
  - exact FULL.
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma after_move_long (fx : FPState) R M model LK Aw (n q c A B a0 : Z) :
  stok model LK Aw -> n = PM.vs_size x -> PM.vs_cap x = n -> 1 <= n -> n + 2 <= A -> 26 <= A <= 2 ^ 27 -> A mod 8 = 0 -> 26 <= c <= 2 ^ 27 -> n < c ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 a0 ->
  getr R (reg 18) = Z_to_bv 64 q -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 c -> getr R (reg 22) = Z_to_bv 64 B ->
  0 <= a0 < 2 ^ 64 ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> B <> q ->
  ri_inv HI ((B, A) :: (q, c) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A (n + 1) B) (tg + 1) ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV x tg)) (scA (PM.pot_text HV (PM.VLong A (n + 1) B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5c98 M model) K.
Proof using All.
  intros STO En FULL Hn1 HnA HA HA8 Hc Hnc A2 A8 A9 A10 A18 A19 A20 A21 A22 Ha0 KP SV MO ACB NBq HH TBOK CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (bfacts _ _ _ _ _ _ q c HH (or_intror (or_introl eq_refl))) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  pose proof (saves_vis _ _ _ _ _ _ HH STK) as VU64.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
  pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
  pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
  pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
  pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
  assert (WST : L5.writable RSEGS MV (S - 64) 64).
  { apply (proj2 (L5A.writable_vis H M (S - 64) 64 (VSTK (S - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 64 + 64 <= o \/ o + 24 <= S - 64) by lia.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed PP (PNAPBP.apbD_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 40%nat => c | 41%nat => q
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 54%nat => a0 | 56%nat => ch | _ => 0 end)) ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5c98 R1 0xd39ac _ K HH AM MS1 (fun y X => X) (fun a _ => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (EM1 : M1 = M).
  { apply functional_extensionality. intros y. rewrite <- (Z_to_bv_bv_unsigned 64 y). apply FR1. pose proof (bv_unsigned_in_range 64 y) as X.
    change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
  subst M1.
  (* [comment removed for export] *)
  set (LBc := (B, A) :: (q, c) :: LB) in *.
  assert (Ip : In (q, c) LBc) by (right; left; reflexivity).
  assert (ELB : lb_remove q LBc = (B, A) :: LB).
  { unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B q) as [X|_]; [exfalso; exact (NBq X)|]. rewrite Z.eqb_refl. reflexivity. }
  assert (STKd : L5CA.astk ar M (S - 64) PMSPA.OPDEL_SCR).
  { apply (L5SAR.astk_sub ar M M S 14336 64 PMSPA.OPDEL_SCR STK (fun y X => X)); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof OPD as OD. unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OD. cbn [pa_opdel PMA.AD ADDR_A] in OD.
  apply (OD fx1 R1 M model1 K LBc FF LK Aw (adebit L cr0 A) q c (S - 64) 0xd5cac HH1 AM1 K0 Ip).
  { rewrite L5K.rl10. exact F10. }
  { rewrite L5K.rl1. exact F1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS1 2%nat) by inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKd. }
  intros fx4 R4 M4 model4 Aw4 RP4 HP4 MRT4 IAW4 AM4 HH4. rewrite ELB in HP4, HH4.
  assert (C4 : forall y, In y [2; 8; 9; 18; 19; 20; 21; 22]%nat -> getr R4 (reg y) = getr R (reg y)).
  { intros y Hy. rewrite (L5SAR.cs_of_preserved R1 R4 y RP4) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
    apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity. }
  assert (EK14 : L5SAR.ek L ar LB FF S 14336 [(o, 24)] M M4).
  { apply (L5SAR.ek_callee L ar LB [(B, A)] FF [] S 14336 (S - 64) PMSPA.OPDEL_SCR [(o, 24)] [] M M4 HP4); [unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| lia|].
    intros a _ _ rr []. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
    intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (WAPP : PMKA.wapp [(o, 24)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  pose proof (bv_unsigned_in_range 64 (getr R4 (reg 10))) as G10. change (bv_modulus 64) with (2 ^ 64) in G10.
  apply (tail fx4 R4 M4 model4 LK Aw4 n q A B 0xd5cac (bv_unsigned (getr R4 (reg 10))) c (tg + 1) (adebit L cr0 A)).
  - split; [exact AM4|]. split; [exact (L5LZ.model_rt_trans model0 model1 model4 (L5LZ.model_rt_trans model0 model model1 MRT MRT1) MRT4)|].
    split; [exact ILK| intros y Hy; exact (IAW4 y (IAW y Hy))].
  - exact En.
  - lia.
  - exact HnA.
  - exact HA.
  - exact HA8.
  - right. reflexivity.
  - rewrite (C4 2%nat) by inl. exact A2.
  - rewrite (C4 8%nat) by inl. exact A8.
  - rewrite (C4 9%nat) by inl. exact A9.
  - symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite (C4 18%nat) by inl. exact A18.
  - rewrite (C4 19%nat) by inl. exact A19.
  - rewrite (C4 20%nat) by inl. exact A20.
  - rewrite (C4 21%nat) by inl. exact A21.
  - rewrite (C4 22%nat) by inl. exact A22.
  - exact G10.
  - lia.
  - lia.
  - intros y Hy. rewrite (L5SAR.cs_of_preserved R1 R4 y RP4) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - destruct HP4 as (PR4 & _ & _).
    apply (saves_keep M M4 (fun a => a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 64 - PMSPA.OPDEL_SCR <= a < S - 64))); [| | lia| exact SV].
    + intros a Ha N. apply PR4. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
    + intros a Ha X. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in X. lia.
  - split; [|split; [|split]].
    + exact (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M4 EK EK14).
    + apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M4 DK).
      apply (L5SAR.dk_callee L ar LB [(B, A)] FF [] S 14336 (S - 64) PMSPA.OPDEL_SCR [] M M4 HP4); unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia.
    + apply (L5SAR.astk_after_eq L ar C HI HIok LBc FF LK (adebit L cr0 A) Aw M M M4 _ S 14336 (S - 64) PMSPA.OPDEL_SCR HH1 STK (fun y X => X));
        [| | unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR; lia| lia| lia].
      * intros a Ha Hs Hns. destruct HP4 as (PR4 & _ & _). apply PR4. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
      * destruct HP4 as (_ & SD4 & _). intros a Ha. replace a with ((S - 64 - PMSPA.OPDEL_SCR) + (a - (S - 64 - PMSPA.OPDEL_SCR))) by lia. apply SD4. lia.
    + exact (PMKA.acc_keepA' L ar LB FF S 14336 [(o, 24)] M M4 EK14 WAPP FRB o 24 AO ACO).
  - exact (PMFA.accA_agree M M4 B A (PMARZK.agsh_ahpres L ar _ FF (S - 64) PMSPA.OPDEL_SCR [] M M4 B A HP4 (or_introl eq_refl) PMKA.wapp_nil ltac:(lia) ltac:(lia)) ACB).
  - exact HH4.
  - exact TBOK.
  - exact FULL.
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma after_new_long (fx : FPState) R M model LK Aw (n q c A B : Z) :
  stok model LK Aw -> n = PM.vs_size x -> PM.vs_cap x = n -> 1 <= n -> n + 2 <= A -> 26 <= A <= 2 ^ 27 -> A mod 8 = 0 -> 26 <= c <= 2 ^ 27 -> n < c ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 q -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 c ->
  kept0 R -> saves M -> mem_ok M -> PMSPA.accA M B A -> PMSPA.accA M q c -> (B + A <= q \/ q + c <= B) ->
  ri_inv HI ((B, A) :: (q, c) :: LB) FF LK (adebit L cr0 A) Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A (n + 1) B) (tg + 1) ->
  PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV x tg)) (scA (PM.pot_text HV (PM.VLong A (n + 1) B) (tg + 1))) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5c88 M model) K.
Proof using All.
  intros STO En FULL Hn1 HnA HA HA8 Hc Hnc A2 A8 A9 A10 A18 A19 A20 A21 KP SV MO ACB ACQ ABq HH TBOK CK.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (NBq : B <> q) by lia.
  destruct (bfacts _ _ _ _ _ _ B A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DB & QO).
  destruct (bfacts _ _ _ _ _ _ q c HH (or_intror (or_introl eq_refl))) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  pose proof (saves_vis _ _ _ _ _ _ HH STK) as VU64.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
  pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
  pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
  pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
  pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
  assert (WST : L5.writable RSEGS MV (S - 64) 64).
  { apply (proj2 (L5A.writable_vis H M (S - 64) 64 (VSTK (S - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 64 + 64 <= o \/ o + 24 <= S - 64) by lia.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed PP (PNAPBP.apbN_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 40%nat => c | 41%nat => q
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 56%nat => ch | _ => 0 end)) ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F11 & F12 & F22).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by inl; exact A10).
  assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 64)) by (rewrite (KS1 2%nat) by inl; exact A2).
  assert (F4 : getr R1 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite (KS1 4%nat) by inl; rewrite (KP 4%nat) by (cbn; auto); exact Rtp0).
  apply (PMARZK.move_stage_pre L ar C HI LY HIok IL ICok ILY ((B, A) :: (q, c) :: LB) FF LK (adebit L cr0 A) Aw M model fx fx1 R 0xd5c88 R1 B q n (S - 64) 0xd5c98 K
           HH AM K0 MS1 F1 ltac:(split; [lia| reflexivity]) F2 F4 F10 F11 F12 ltac:(lia)).
  { apply (L5SAR.astk_sub ar M M S 14336 64 2560 STK (fun y X => X)); [lia| lia| lia|]. replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exists B, A. split; [left; reflexivity| lia]. }
  { apply (L5.defined_sub M B A); [exact DB| lia| lia]. }
  { apply (aacc_sub M B A); [exact ACB| lia| lia]. }
  { left. exists q, c. split; [right; left; reflexivity| lia]. }
  { apply (L5.defined_sub M q c); [exact DP| lia| lia]. }
  { apply (aacc_sub M q c); [exact ACQ| lia| lia]. }
  { lia. }
  intros R3 M3 model3 RP3 R3_10 PRES3 SDEF3 D3 MRT3 AM3 HH3.
  assert (C3 : forall y, In y L5SAR.cs_all -> getr R3 (reg y) = getr R1 (reg y)) by (intros y Hy; exact (L5SAR.cs_of_preserved R1 R3 y RP3 Hy)).
  apply (after_move_long fx1 R3 M3 model3 LK Aw n q c A B B).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
  - exact En.
  - exact FULL.
  - exact Hn1.
  - exact HnA.
  - exact HA.
  - exact HA8.
  - exact Hc.
  - exact Hnc.
  - rewrite (C3 2%nat) by inl. exact F2.
  - rewrite (C3 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
  - rewrite (C3 9%nat) by inl. rewrite (KS1 9%nat) by inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by inl. rewrite (KS1 18%nat) by inl. exact A18.
  - rewrite (C3 19%nat) by inl. rewrite (KS1 19%nat) by inl. exact A19.
  - rewrite (C3 20%nat) by inl. rewrite (KS1 20%nat) by inl. exact A20.
  - rewrite (C3 21%nat) by inl. rewrite (KS1 21%nat) by inl. exact A21.
  - rewrite (C3 22%nat) by inl. exact F22.
  - lia.
  - intros y Hy. rewrite (C3 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - exact (saves_mem M M3 _ B n PRES3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SV).
  - apply (mem_ok_mem M M3 [(B, A); (q, c)] LK (adebit L cr0 A) Aw model B n HH MO PRES3 SDEF3 D3). exists B, A. split; [left; reflexivity| lia].
  - exact (accA_mem M M3 _ B n B A PRES3 (or_introl eq_refl) ltac:(lia) ltac:(lia) ltac:(lia) ACB).
  - exact NBq.
  - exact HH3.
  - exact TBOK.
  - exact CK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_credit (x' : PM.vstr) (A : Z) :
  PM.tb_ok x tg -> PM.vs_cap x <= 2 ^ 27 -> 2 * PM.vs_cap x <= PM.vs_cap x' -> PM.vs_cap x' = A - 1 -> A <= 2 ^ 27 ->
  PMSPA.credit_le (scA (PM.pot_text HV x tg)) cr0 ->
  acredit_ok L cr0 A /\ PMSPA.credit_keep cr0 (adebit L cr0 A) (scA (PM.pot_text HV x tg)) (scA (PM.pot_text HV x' (tg + 1))) /\ tg <= 22.
Proof using All.
  intros (T0 & T1 & _) Hc Hc' Ec HA (CR1 & CR2).
  pose proof (PMA.ly_cost L C LY) as (HK & HL & HB).
  assert (Htg : tg <= 22).
  { destruct (Z.eq_dec tg 23) as [E|Nq]; [|lia]. rewrite E in T1. change (2 ^ 23) with 8388608 in T1. lia. }
  pose proof (PMF.pot_text_step HV x x' tg Hc') as (P1 & P2).
  unfold PMSPA.scA, PM.credit_add, PM.cost1, PM.pot_text, PMSPA.HV, LibIfaceAB.heap_view in P1, P2, CR1, CR2 |- *.
  cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in P1, P2, CR1, CR2 |- *. rewrite HK, HL, HB in *. rewrite ?Ec in P1, P2 |- *.
  split; [unfold acredit_ok; rewrite HK, HL, HB; split; nia|]. split; [|exact Htg].
  unfold PMSPA.credit_keep, adebit. rewrite HK, HL, HB. cbn [fst snd]. split; nia.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_new (M M3 : word -> option byte) (BX : list (Z * Z)) LK cr Aw model :
  ri_inv HI (BX ++ LB) FF LK cr Aw M (vml_of model) -> mem_ok M ->
  L5CA.ahpres L ar (BX ++ LB) FF (S - 64) PMSPA.OPNEW_SCR [] M M3 -> mem_ok M3.
Proof using All.
  intros HH (EK & DK & STK & ACO) HP. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
  assert (EK13 : L5SAR.ek L ar LB FF S 14336 [(o, 24)] M M3).
  { apply (L5SAR.ek_callee L ar LB BX FF [] S 14336 (S - 64) PMSPA.OPNEW_SCR [(o, 24)] [] M M3 HP); [unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia|].
    intros a _ _ rr []. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _).
    intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (WAPP : PMKA.wapp [(o, 24)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| apply PMKA.wapp_nil]. }
  split; [|split; [|split]].
  - exact (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M3 EK EK13).
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M3 DK).
    apply (L5SAR.dk_callee L ar LB BX FF [] S 14336 (S - 64) PMSPA.OPNEW_SCR [] M M3 HP); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia.
  - apply (L5SAR.astk_after_eq L ar C HI HIok _ FF LK cr Aw M M M3 _ S 14336 (S - 64) PMSPA.OPNEW_SCR HH STK (fun y X => X));
      [| | unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; lia| lia| lia].
    + intros a Ha Hs Hns. destruct HP as (PR & _ & _). apply PR. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
    + destruct HP as (_ & SD & _). intros a Ha. replace a with ((S - 64 - PMSPA.OPNEW_SCR) + (a - (S - 64 - PMSPA.OPNEW_SCR))) by lia. apply SD. lia.
  - exact (PMKA.acc_keepA' L ar LB FF S 14336 [(o, 24)] M M3 EK13 WAPP FRB o 24 AO ACO).
Qed.
Lemma saves_new (M M3 : word -> option byte) (LB' : list (Z * Z)) :
  L5CA.ahpres L ar LB' FF (S - 64) PMSPA.OPNEW_SCR [] M M3 -> ahl_ceil ar + 4096 + 14336 <= S -> S <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar ->
  saves M -> saves M3.
Proof using All.
  intros (PR & _ & _) H1 H2 H3 SV.
  apply (saves_keep M M3 (fun a => a < ahl_ceil ar \/ 2 ^ 47 <= a \/ (S - 64 - PMSPA.OPNEW_SCR <= a < S - 64))); [| | lia| exact SV].
  - intros a Ha Nq. apply PR. split; [exact Ha|]. split; [apply L5SAR.stack_client; lia| intros rr []].
  - intros a Ha X. unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in X. lia.
Qed.

(* [comment removed for export] *)
Lemma grow_short (fx : FPState) R M model LK Aw :
  stok model LK Aw -> x = PM.VShort 22 -> PM.tb_ok x tg -> PMSPA.credit_le (scA (PM.pot_text HV x tg)) cr0 ->
  getr R (reg 1) = Z_to_bv 64 0xd5c88 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 48 ->
  getr R (reg 18) = Z_to_bv 64 (o + 1) -> getr R (reg 19) = Z_to_bv 64 48 -> getr R (reg 20) = Z_to_bv 64 22 -> getr R (reg 21) = Z_to_bv 64 23 ->
  kept0 R -> saves M -> mem_ok M ->
  ri_inv HI LB FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x130338 M model) K.
Proof using All.
  intros STO Es TBOK CR A1 A2 A8 A9 A10 A18 A19 A20 A21 KP SV MO HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (PMF.tb_law_first 23 48 ltac:(lia) ltac:(lia) eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
  destruct (grow_credit (PM.VLong 48 (22 + 1) 0) 48 TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl ltac:(lia) CR) as (CROK & CK & Htg).
  assert (STKn : L5CA.astk ar M (S - 64) PMSPA.OPNEW_SCR).
  { apply (L5SAR.astk_sub ar M M S 14336 64 PMSPA.OPNEW_SCR STK (fun y X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof OPN as ON. unfold PMA.opnew_spec, PMSPA.opnew_spec in ON. cbn [pa_opnew PMA.AD ADDR_A] in ON. unfold PMSPA.cfg.
  apply (ON fx R M model K LB FF LK Aw cr0 48 (S - 64) 0xd5c88 HH AM K0).
  { rewrite L5K.rl10. exact A10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact A2. }
  { rewrite L5K.rl4. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 Aw3 B R3_10 RP3 FB HP3 MRT3 IAW3 AM3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4 & FB5) & FBa & FBf & FBd & FBs). cbn [fst snd] in *.
  assert (C3 : forall y, In y [2; 8; 9; 18; 19; 20; 21]%nat -> getr R3 (reg y) = getr R (reg y)).
  { intros y Hy. apply (L5SAR.cs_of_preserved R R3 y RP3). revert y Hy. apply sub_in. vm_compute. reflexivity. }
  apply (after_new_short fx3 R3 M3 model3 LK Aw3 48 B).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|].
    split; [exact ILK| intros y Hy; exact (IAW3 y (IAW y Hy))].
  - rewrite Es. reflexivity.
  - rewrite Es. reflexivity.
  - lia.
  - reflexivity.
  - rewrite (C3 2%nat) by inl. exact A2.
  - rewrite (C3 8%nat) by inl. exact A8.
  - rewrite (C3 9%nat) by inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by inl. exact A18.
  - rewrite (C3 19%nat) by inl. exact A19.
  - rewrite (C3 20%nat) by inl. exact A20.
  - rewrite (C3 21%nat) by inl. exact A21.
  - intros y Hy. rewrite (L5SAR.cs_of_preserved R R3 y RP3) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - exact (saves_new M M3 LB HP3 ltac:(lia) ltac:(lia) ltac:(lia) SV).
  - exact (mem_ok_new M M3 [] LK cr0 Aw model HH MO HP3).
  - apply (aacc_of_block M3 B 48 B 48 FBs); [apply PMFA.mod16_8; exact FB2| lia| lia| lia].
  - exact HH3.
  - assert (Etg : tg = 0) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X); exact X).
    rewrite Etg. split; [lia|]. split; [cbn; lia|]. split; [exact LAW| lia].
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma grow_long (fx : FPState) R M model LK Aw (c n0 p A : Z) :
  stok model LK Aw -> x = PM.VLong c n0 p -> n0 + 1 = c -> 1 <= n0 -> PM.tb_ok x tg -> PMSPA.credit_le (scA (PM.pot_text HV x tg)) cr0 ->
  26 <= c <= 2 ^ 27 -> PMSPA.accA M p c ->
  PM.tb_law A /\ 2 * n0 <= A - 1 /\ n0 + 2 <= A /\ A <= 2 ^ 27 /\ A mod 8 = 0 /\ 26 <= A ->
  getr R (reg 1) = Z_to_bv 64 0xd5c88 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 A ->
  getr R (reg 18) = Z_to_bv 64 p -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n0 -> getr R (reg 21) = Z_to_bv 64 c ->
  kept0 R -> saves M -> mem_ok M ->
  ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0x130338 M model) K.
Proof using All.
  intros STO Es FULL Hn1 TBOK CR Hc ACP (LAW & LA1 & LA2 & LA3 & LA4 & LA5) A1 A2 A8 A9 A10 A18 A19 A20 A21 KP SV MO HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & DP & PO).
  destruct (grow_credit (PM.VLong A (n0 + 1) 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn [PM.vs_cap]; lia) ltac:(cbn [PM.vs_cap]; lia) LA3 CR) as (CROK & CK & Htg).
  assert (STKn : L5CA.astk ar M (S - 64) PMSPA.OPNEW_SCR).
  { apply (L5SAR.astk_sub ar M M S 14336 64 PMSPA.OPNEW_SCR STK (fun y X => X)); unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR; [lia| lia| lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof OPN as ON. unfold PMA.opnew_spec, PMSPA.opnew_spec in ON. cbn [pa_opnew PMA.AD ADDR_A] in ON. unfold PMSPA.cfg.
  apply (ON fx R M model K ((p, c) :: LB) FF LK Aw cr0 A (S - 64) 0xd5c88 HH AM K0).
  { rewrite L5K.rl10. exact A10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact A2. }
  { rewrite L5K.rl4. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 Aw3 B R3_10 RP3 FB HP3 MRT3 IAW3 AM3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4 & FB5) & FBa & FBf & FBd & FBs). cbn [fst snd] in *.
  assert (C3 : forall y, In y [2; 8; 9; 18; 19; 20; 21]%nat -> getr R3 (reg y) = getr R (reg y)).
  { intros y Hy. apply (L5SAR.cs_of_preserved R R3 y RP3). revert y Hy. apply sub_in. vm_compute. reflexivity. }
  assert (ABp : B + A <= p \/ p + c <= B) by (exact (FBa (p, c) ltac:(left; reflexivity))).
  apply (after_new_long fx3 R3 M3 model3 LK Aw3 n0 p c A B).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|].
    split; [exact ILK| intros y Hy; exact (IAW3 y (IAW y Hy))].
  - rewrite Es. reflexivity.
  - rewrite Es. cbn [PM.vs_cap]. lia.
  - exact Hn1.
  - exact LA2.
  - lia.
  - exact LA4.
  - exact Hc.
  - lia.
  - rewrite (C3 2%nat) by inl. exact A2.
  - rewrite (C3 8%nat) by inl. exact A8.
  - rewrite (C3 9%nat) by inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by inl. exact A18.
  - rewrite (C3 19%nat) by inl. exact A19.
  - rewrite (C3 20%nat) by inl. exact A20.
  - rewrite (C3 21%nat) by inl. exact A21.
  - intros y Hy. rewrite (L5SAR.cs_of_preserved R R3 y RP3) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - exact (saves_new M M3 _ HP3 ltac:(lia) ltac:(lia) ltac:(lia) SV).
  - exact (mem_ok_new M M3 [(p, c)] LK cr0 Aw model HH MO HP3).
  - apply (aacc_of_block M3 B A B A FBs); [apply PMFA.mod16_8; exact FB2| lia| lia| lia].
  - exact (PMFA.accA_agree M M3 p c (PMARZK.agsh_ahpres L ar _ FF (S - 64) PMSPA.OPNEW_SCR [] M M3 p c HP3 (or_introl eq_refl) PMKA.wapp_nil ltac:(lia) ltac:(lia)) ACP).
  - exact ABp.
  - exact HH3.
  - pose proof TBOK as (Tg0 & Tg1 & _). rewrite Es in Tg1. cbn [PM.vs_cap] in Tg1.
    split; [lia|]. split; [cbn [PM.vs_cap]; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia|]. split; [exact LAW| lia].
  - exact CK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma half2 c : c mod 2 = 0 -> 2 * ((c + 1) / 2) = c.
Proof.
  intros Hc. assert (E : c = 2 * (c / 2)) by (apply Z_div_exact_2; Lia.lia). set (k := c / 2) in *. rewrite E.
  replace (2 * k + 1) with (k * 2 + 1) by Lia.lia. rewrite Z.div_add_l by Lia.lia. change (1 / 2) with 0. Lia.lia.
Qed.
Lemma capm1 c : 0 <= c < 2 ^ 63 -> ((c mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = c - 1 + (if Z.eqb c 0 then 2 ^ 64 else 0).
Proof.
  intros Hc. rewrite (Z.mod_small c) by Lia.lia. destruct (Z.eqb_spec c 0) as [->|N]; [reflexivity|].
  replace (c + 18446744073709551615) with ((c - 1) + 1 * 2 ^ 64) by Lia.lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by Lia.lia. Lia.lia.
Qed.
Lemma wrap_ne n0 c : 0 <= n0 -> n0 + 1 < c -> c < 2 ^ 62 -> c mod 2 = 0 ->
  1 <= ((n0 - ((((2 * ((c + 1) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64).
Proof.
  intros H0 H1 H2 Hc. rewrite half2 by exact Hc. rewrite capm1 by Lia.lia. destruct (Z.eqb_spec c 0) as [E|N]; [Lia.lia|].
  replace (n0 - (c - 1 + 0)) with ((n0 - c + 1 + 2 ^ 64) + (-1) * 2 ^ 64) by Lia.lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by Lia.lia. Lia.lia.
Qed.
Lemma wrap_eq n0 c : n0 + 1 = c -> 0 < c < 2 ^ 62 -> c mod 2 = 0 ->
  ((n0 - ((((2 * ((c + 1) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1.
Proof.
  intros H1 H2 Hc. rewrite half2 by exact Hc. rewrite capm1 by Lia.lia. destruct (Z.eqb_spec c 0) as [E|N]; [Lia.lia|].
  replace (n0 - (c - 1 + 0)) with 0 by Lia.lia. rewrite Z.mod_0_l by Lia.lia. Lia.lia.
Qed.
Lemma newcnt c : 8 <= c -> c mod 8 = 0 -> 8 * ((4 * ((c + 1) / 2) - 2) / 8) + 8 = 2 * c.
Proof.
  intros Hc H8. assert (E : c = 8 * (c / 8)) by (apply Z_div_exact_2; Lia.lia). set (k := c / 8) in *. rewrite E.
  replace (8 * k + 1) with ((4 * k) * 2 + 1) by Lia.lia. rewrite Z.div_add_l by Lia.lia. change (1 / 2) with 0.
  replace (4 * (4 * k + 0) - 2) with ((2 * k - 1) * 8 + 6) by Lia.lia. rewrite Z.div_add_l by Lia.lia. change (6 / 8) with 0. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame (M M' : word -> option byte) (LBo : list (Z * Z)) LK cr Aw model :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) ->
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S - 64 + 64) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M'.
Proof using All.
  intros HH (EK & DK & STK & ACO) MG FR. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
  split; [|split; [|split]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M' EK).
    apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M' (fun a => S - 64 <= a < S - 64 + 64) FR). intros a Ha CA OW Wa.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB LBo FF S 14336 a CA)) as [Z1|Z1]; lia.
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M' DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M' MG).
  - exact (L5SAR.astk_grows ar M M' S 14336 STK MG).
  - apply (PMFA.accA_agree M M' o 24); [| exact ACO].
    apply (PMARZK.agsh_frame M M' (fun a => S - 64 <= a < S - 64 + 64) o 24 FR); [intros y X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia].
Qed.

Lemma saves_of (M : word -> option byte) :
  L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) ->
  L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) ->
  L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) ->
  L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M.
Proof using All. intros. unfold saves. repeat split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pb_entry (fx : FPState) :
  L5CA.amodel_ok Aw0 model0 -> ri_inv HI (PM.vs_own x ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0) ->
  getr R0 (reg 10) = Z_to_bv 64 o -> vstr_at M0 o x -> PM.tb_ok x tg -> PMSPA.credit_le (scA (PM.pot_text HV x tg)) cr0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R0 0xd5bc4 M0 model0) K.
Proof using All.
  intros AM0 HH A10 VS TBOK CR.
  pose proof STK0 as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  pose proof VS as (DO & ACO & _).
  destruct (vfacts _ _ _ _ _ _ HH STK0) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw0 model0) in *. set (MV := mrestrict H M0) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  assert (WST : L5.writable RSEGS MV (S - 64) 64).
  { apply (proj2 (L5A.writable_vis H M0 (S - 64) 64 (VSTK (S - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M0 S 14336); [exact STK0| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M0 o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 64 + 64 <= o \/ o + 24 <= S - 64) by lia.
  assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HC : bv_unsigned (getr R0 (reg 11)) = ch) by (rewrite A11; apply L5.unsigned_lit; lia).
  assert (MR0 : model_rt model0 model0) by (unfold model_rt; destruct model0; reflexivity).
  assert (STO0 : stok model0 LK0 Aw0) by (split; [exact AM0|]; split; [exact MR0|]; split; apply incl_refl).
  assert (MO0 : mem_ok M0).
  { split; [intros a _; reflexivity|]. split; [intros a _ _ D; exact D|]. split; [exact STK0| exact ACO]. }
  assert (KP0 : kept0 R0) by (intros y _; reflexivity).
  assert (R2 : getr R0 (reg 2) = Z_to_bv 64 S) by exact Rsp0.
  assert (TOMV8 : forall M1 M1v a v, mrestrict H M1 = M1v -> o <= a -> a + 1 <= o + 24 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v).
  { intros M1 M1v a v VIS1 X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u8_at_vis _ M1 a v (L5A.avis_sub _ o 24 a 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
  assert (TOMV64 : forall M1 M1v a v, mrestrict H M1 = M1v -> o <= a -> a + 8 <= o + 24 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros M1 M1v a v VIS1 X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (L5A.avis_sub _ o 24 a 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
  assert (TOMF64 : forall M1 M1v a v, mrestrict H M1 = M1v -> S - 64 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros M1 M1v a v VIS1 X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
  unfold PMSPA.cfg.
  assert (CASE : (exists n0, x = PM.VShort n0) \/ (exists c n0 p, x = PM.VLong c n0 p)) by (destruct x as [a|a b d]; [left; exists a | right; exists a, b, d]; reflexivity).
  destruct CASE as [(n0 & Es)|(c & n0 & p & Es)]; pose proof SZ as SZx; rewrite Es in VS, HH, SZx.
  - (* [comment removed for export] *)
    destruct VS as (_ & _ & Hn0 & B0). cbn [PM.vs_size] in SZx. cbn [PM.vs_own app] in HH.
    assert (B0v : L5.u8_at RSEGS MV o (2 * n0)).
    { apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
    destruct (Z_lt_le_dec n0 22) as [LT|GE].
    + (* [comment removed for export] *)
      pose proof (PNAPBP.apbS_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia | apply PMF.even_byte]).
      destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & _ & _ & C2 & C1 & C0 & _).
      replace (2 * n0 / 2) with n0 in C2, C1 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra0).
      pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd5cf4 W_d36f8 r F_d36f8 eq_refl D_d36f8 RA1 ltac:(lia) Hr2) as MS2.
      set (W1 := fun a => (S - 64 <= a < S - 64 + 64) \/ (o + 0 <= a < o + 0 + 24)).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd5bc4 R1 r M1v W1 K HH AM0).
      { eapply msteps_trans; [exact MS1| exact MS2]. }
      { exact MG1. }
      { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { intros a Ha [Wa|Wa]; split.
        - apply (L5SAR.stack_client L ar LB FF 0 0 a); lia.
        - lia.
        - apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
        - lia. }
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
      assert (NSH : forall y, W1 y -> y < BIGSHADOW_LO \/ BIGSHADOW_HI <= y) by (intros y [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
      apply (KONT fx1 R1 M1 model1 LK0 Aw0 (PM.VShort (n0 + 1)) tg cr0).
      * apply L5SAR.preserved_by_index. intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MGM1; apply DO; exact Hi|].
        split; [exact (PMFA.accA_agree M0 M1 o 24 (PMARZK.agsh_frame M0 M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
        split; [lia|]. replace (2 * (n0 + 1)) with (2 * n0 + 2) by lia. exact (TOMV8 M1 M1v o _ VIS1 ltac:(lia) ltac:(lia) C0).
      * rewrite Es. reflexivity.
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
        -- apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M1 W1 FR1). intros a Ha CA OW Wa. destruct Wa as [X|X].
           ++ destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 14336 a HH SPT CA) as [Z1|Z1]; lia.
           ++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- pose proof (L5SAR.astk_grows ar M0 M1 S 14336 STK0 MGM1) as (_ & _ & _ & _ & D2 & _). exact D2.
        -- apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M1 MGM1).
      * rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
      * exact MRT1.
      * apply incl_refl.
      * apply incl_refl.
      * exact AM1.
      * exact HH1.
    + (* [comment removed for export] *)
      assert (En0 : n0 = 22) by lia. subst n0.
      pose proof (PNAPBP.apbGS_conc fx R0 MV (fun j => match j with 2%nat => S | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
      destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & _ & F18 & F19 & F20 & F21 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd5bc4 R1 0x130338 M1v (fun a => S - 64 <= a < S - 64 + 64) K HH AM0 MS1 MG1 FZ1).
      { intros a Ha Wa. split; [apply (L5SAR.stack_client L ar LB FF 0 0 a); lia| lia]. }
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
      apply (grow_short fx1 R1 M1 model1 LK0 Aw0).
      * split; [exact AM1|]. split; [exact MRT1|]. split; apply incl_refl.
      * exact Es.
      * exact TBOK.
      * exact CR.
      * exact F1.
      * exact F2.
      * rewrite F8. exact A11.
      * rewrite F9. exact A10.
      * exact F10.
      * rewrite F18. reflexivity.
      * exact F19.
      * exact F20.
      * exact F21.
      * intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * apply saves_of; (apply (TOMF64 M1 M1v _ _ VIS1); [lia| lia| assumption]).
      * exact (mem_ok_frame M0 M1 [] LK0 cr0 Aw0 model0 HH MO0 MGM1 FR1).
      * exact HH1.
  - (* [comment removed for export] *)
    pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & ACP). cbn [PM.vs_size] in SZx. cbn [PM.vs_own app] in HH.
    destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & _ & PO).
    pose proof (PMF.u8_of_u64 RSEGS M0 o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
    assert (TB1 : Z.testbit (c + 1) 0 = true) by (rewrite <- (Z.mod_pow2_bits_low (c + 1) 8 0) by lia; exact ODB).
    assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
    assert (B0v : L5.u8_at RSEGS MV o ((c + 1) mod 256)).
    { apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
    assert (W0v : L5.u64_at RSEGS MV o (c + 1)).
    { apply (proj2 (L5A.u64_at_vis H M0 o _ (L5A.avis_sub H o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W0. }
    assert (W8v : L5.u64_at RSEGS MV (o + 8) n0).
    { apply (proj2 (L5A.u64_at_vis H M0 (o + 8) _ (L5A.avis_sub H o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W8. }
    assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
    { apply (proj2 (L5A.u64_at_vis H M0 (o + 16) _ (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
    destruct (Z_lt_le_dec (n0 + 1) c) as [LT|GE].
    + (* [comment removed for export] *)
      pose proof (wrap_ne n0 c ltac:(lia) LT ltac:(lia) Hce) as WNE.
      assert (WRp : L5.writable RSEGS MV (p + n0) 2).
      { apply (proj2 (L5A.writable_vis H M0 (p + n0) 2 (VBLK p c (p + n0) 2 ltac:(rewrite Es; left; reflexivity) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
        apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M0 p c (p + n0) 2 DP); lia| lia| lia]. }
      assert (Dpo : p + n0 + 2 <= o \/ o + 24 <= p + n0) by lia.
      assert (Dpf : p + n0 + 2 <= S - 64 \/ S - 64 + 64 <= p + n0) by lia.
      pose proof (PNAPBP.apbLI_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 35%nat => p | 36%nat => c + 1 | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
      destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & _ & _ & _ & C2 & C1 & C8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CW0 & CW16).
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra0).
      pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd5cf4 W_d36f8 r F_d36f8 eq_refl D_d36f8 RA1 ltac:(lia) Hr2) as MS2.
      set (W1 := fun a => (S - 64 <= a < S - 64 + 64) \/ (o + 0 <= a < o + 0 + 24) \/ (p + n0 + 0 <= a < p + n0 + 0 + 2)).
      apply (L5SAR.apiece L ar C HI LYa HIok ((p, c) :: LB) FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd5bc4 R1 r M1v W1 K HH AM0).
      { eapply msteps_trans; [exact MS1| exact MS2]. }
      { exact MG1. }
      { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
      { intros a Ha [Wa|[Wa|Wa]]; split.
        - apply (L5SAR.stack_client L ar _ FF 0 0 a); lia.
        - lia.
        - apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
        - lia.
        - apply (L5SAR.block_client L ar ((p, c) :: LB) FF 0 0 p c a (or_introl eq_refl)); lia.
        - lia. }
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
      assert (NSH : forall y, W1 y -> y < BIGSHADOW_LO \/ BIGSHADOW_HI <= y) by (intros y [X|[X|X]]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
      apply (KONT fx1 R1 M1 model1 LK0 Aw0 (PM.VLong c (n0 + 1) p) tg cr0).
      * apply L5SAR.preserved_by_index. intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MGM1; apply DO; exact Hi|].
        split; [exact (PMFA.accA_agree M0 M1 o 24 (PMARZK.agsh_frame M0 M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
        split; [exact (TOMV64 M1 M1v o _ VIS1 ltac:(lia) ltac:(lia) CW0)|].
        split; [exact (TOMV64 M1 M1v (o + 8) _ VIS1 ltac:(lia) ltac:(lia) C8)|].
        split; [exact (TOMV64 M1 M1v (o + 16) _ VIS1 ltac:(lia) ltac:(lia) CW16)|].
        split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MGM1; apply DP; exact Hi|].
        exact (PMFA.accA_agree M0 M1 p c (PMARZK.agsh_frame M0 M1 W1 p c FR1 NSH ltac:(lia) ltac:(lia)) ACP).
      * rewrite Es. reflexivity.
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
        -- apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M1 W1 FR1). intros a Ha CA OW Wa. destruct Wa as [X|[X|X]].
           ++ destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB [(p, c)] FF S 14336 a CA)) as [Z1|Z1]; lia.
           ++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ exact (PMARS1.own_not_aclient L ar C HI HIok [(p, c)] LB FF LK0 cr0 Aw0 M0 _ p c a S 14336 HH (or_introl eq_refl) ltac:(lia) CA).
        -- pose proof (L5SAR.astk_grows ar M0 M1 S 14336 STK0 MGM1) as (_ & _ & _ & _ & D2 & _). exact D2.
        -- apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M1 MGM1).
      * rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
      * exact MRT1.
      * apply incl_refl.
      * apply incl_refl.
      * exact AM1.
      * exact HH1.
    + (* [comment removed for export] *)
      assert (En0 : n0 + 1 = c) by lia.
      pose proof (wrap_eq n0 c En0 ltac:(lia) Hce) as WEQ.
      pose proof (PNAPBP.apbLG_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 35%nat => p | 36%nat => c + 1 | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      L5SAR.feed PP ltac:(first [assumption | unfold PNAPBP.aligned; lia | lia]).
      destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & _ & _ & F18 & F19 & F20 & F21 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8).
      assert (TBL : PM.tb_law c /\ 1 <= tg) by (pose proof TBOK as TB; rewrite Es in TB; destruct TB as (_ & _ & TB3); exact TB3).
      destruct TBL as (TLAW & Htg1).
      assert (C8m : c mod 8 = 0).
      { destruct TLAW as (j & J0 & J1 & J2 & J3). apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 (2 ^ (3 + j)) c).
        - exists (2 ^ j). rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia.
        - apply Z.mod_divide; [lia| exact J3]. }
      assert (Ek : c = 8 * (c / 8)) by (apply Z_div_exact_2; lia).
      assert (EQA : Z.lor (Z.max (2 * (c - 1)) c) 7 + 1 = 2 * c).
      { rewrite Z.max_l by lia. rewrite PMF.lor7 by lia. set (k := c / 8) in *. rewrite Ek.
        replace (2 * (8 * k - 1)) with ((2 * k - 1) * 8 + 6) by lia. rewrite Z.div_add_l by lia. change (6 / 8) with 0. lia. }
      pose proof (newcnt c ltac:(lia) C8m) as NC. pose proof (half2 c Hce) as H2.
      destruct (PMF.tb_law_step c c (2 * c) TLAW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (eq_sym EQA)) as (LAW & LA1 & LA2 & LA3 & LA4).
      apply (L5SAR.apiece L ar C HI LYa HIok ((p, c) :: LB) FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd5bc4 R1 0x130338 M1v (fun a => S - 64 <= a < S - 64 + 64) K HH AM0 MS1 MG1 FZ1).
      { intros a Ha Wa. split; [apply (L5SAR.stack_client L ar _ FF 0 0 a); lia| lia]. }
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
      apply (grow_long fx1 R1 M1 model1 LK0 Aw0 c n0 p (2 * c)).
      * split; [exact AM1|]. split; [exact MRT1|]. split; apply incl_refl.
      * exact Es.
      * exact En0.
      * lia.
      * exact TBOK.
      * exact CR.
      * lia.
      * apply (PMFA.accA_agree M0 M1 p c); [| exact ACP].
        apply (PMARZK.agsh_frame M0 M1 (fun a => S - 64 <= a < S - 64 + 64) p c FR1); [intros y X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia].
      * split; [exact LAW|]. lia.
      * exact F1.
      * exact F2.
      * rewrite F8. exact A11.
      * rewrite F9. exact A10.
      * rewrite F10, NC. reflexivity.
      * exact F18.
      * rewrite F19, NC. reflexivity.
      * rewrite F20, H2. f_equal. lia.
      * rewrite F21, H2. reflexivity.
      * intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * apply saves_of; (apply (TOMF64 M1 M1v _ _ VIS1); [lia| lia| assumption]).
      * exact (mem_ok_frame M0 M1 [(p, c)] LK0 cr0 Aw0 model0 HH MO0 MGM1 FR1).
      * exact HH1.
Qed.

End Call.
End WithHeap.
End PNAPB1.
