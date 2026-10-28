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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnARzKit_b PnAResizeP_b PnAReset1_b Ba0_code_rd0c30_d0c34_b.
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

Module PMARZ1.
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
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LB FF S 14336 [(o, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M o 24.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma regs_back (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S -> getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) ->
  getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) -> getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) ->
  getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) -> getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) ->
  getr R1 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) -> getr R1 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) ->
  kept0 R1 -> regs_preserved R0 R1.
Proof using All.
  intros E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 KP. apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
  destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
  destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
  destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E24; apply Z_to_bv_bv_unsigned|].
  apply KP. destruct Hx as [<-|[<-|[<-|[]]]]; cbn; auto 10.
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
(* [comment removed for export] *)
Lemma finish_long (fx : FPState) R M model LK Aw (q A tg' : Z) (cr' : credit) :
  stok model LK Aw ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 20) = Z_to_bv 64 q -> getr R (reg 22) = Z_to_bv 64 n ->
  kept0 R -> saves M -> mem_ok M ->
  L5.u64_at RSEGS M o (A + 1) -> L5.u64_at RSEGS M (o + 16) q ->
  1 <= n < A -> 26 <= A <= 2 ^ 27 -> A mod 2 = 0 -> PMSPA.accA M q A ->
  ri_inv HI ((q, A) :: LB) FF LK cr' Aw M (vml_of model) ->
  PM.tb_ok (PM.VLong A n q) tg' -> (n <= PM.vs_cap s -> [(q, A)] = PM.vs_own s /\ tg' = tg) ->
  PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV (PM.VLong A n q) tg')) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5e8c M model) K.
Proof using All.
  intros STO A2 A8 A20 A22 KP SV (EK & DK & STK & ACO) W0 W16 Hn HA HAe ACQ HH TBOK OWN CK.
  destruct STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct (bfacts _ _ _ _ _ _ q A HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DQ & QO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  assert (VU64 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v X1 X2 X. apply (proj2 (L5A.u64_at_vis H M a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
  pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
  pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
  pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
  pose proof (VU64 (S - 72) _ ltac:(lia) ltac:(lia) S72) as V72. pose proof (VU64 (S - 80) _ ltac:(lia) ltac:(lia) S80) as V80.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (WQV : L5.writable RSEGS MV (q + n) 1).
  { apply (proj2 (L5A.writable_vis H M (q + n) 1 (VBLK q A (q + n) 1 (or_introl eq_refl) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M q A (q + n) 1 DQ); lia| lia| lia]. }
  pose proof (PMF.u8_of_u64 RSEGS M o (A + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte A HAe ltac:(lia)) as ODB.
  assert (B0v : L5.u8_at RSEGS MV o ((A + 1) mod 256)).
  { apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
  assert (H33 : 0 <= (A + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (A + 1) 256 ltac:(lia)); lia).
  assert (Dqo : q + n + 1 <= o \/ o + 24 <= q + n) by lia.
  assert (Dqf : q + n + 1 <= S - 80 \/ S - 80 + 80 <= q + n) by lia.
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed P (PMARZP.aapML_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => (A + 1) mod 256 | 35%nat => q | 38%nat => n
        | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
        | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
        | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
        | 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & C0 & C8).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd5ee0 W_d38e4 r F_d38e4 eq_refl D_d38e4 R1ra ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => (o + 8 <= a < o + 8 + 8) \/ (q + n + 0 <= a < q + n + 0 + 1)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok ((q, A) :: LB) FF LK cr' Aw M model fx fx1 R 0xd5e8c R1 r M1v W1 K HH AM).
  { eapply msteps_trans; [exact MS1| exact MS2]. }
  { exact MG1. }
  { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa]; split.
    - apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
    - lia.
    - apply (L5SAR.block_client L ar ((q, A) :: LB) FF 0 0 q A a (or_introl eq_refl)); lia.
    - lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (NSH : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ W1 i) -> L5C.agree_on M M1 a m).
  { intros a0 m0 Ha0 Hm0 X i Hi. apply FR1; [lia| apply X; exact Hi]. }
  assert (OVIS1 : L5A.avis (ahid Aw model1) o 24) by (rewrite HID1; exact OVIS).
  apply (KONT fx1 R1 M1 model1 LK Aw (PM.VLong A n q) tg' cr').
  - apply regs_back; try assumption.
    intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - split; [intros i Hi; apply MGM1; apply ODEF; exact Hi|].
    split; [apply (PMFA.accA_agree M M1 o 24 (PMARZK.agsh_frame M M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
    split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W0]|].
    split; [rewrite <- VIS1 in C8; exact (proj1 (L5A.u64_at_vis _ M1 (o + 8) n (L5A.avis_sub _ o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C8)|].
    split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W16]|].
    split; [lia|]. split; [lia|]. split; [exact HAe|]. split; [intros i Hi; apply MGM1; apply DQ; exact Hi|].
    apply (PMFA.accA_agree M M1 q A (PMARZK.agsh_frame M M1 W1 q A FR1 NSH ltac:(lia) ltac:(lia)) ACQ).
  - reflexivity.
  - exact TBOK.
  - intros X. destruct (OWN X) as (Ow1 & Ow2). split; [exact Ow1| exact Ow2].
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
    + apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
      apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 W1 FR1). intros a Ha CA OW Wa. destruct Wa as [X|X].
      * apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * exact (PMARS1.own_not_aclient L ar C HI HIok [(q, A)] LB FF LK cr' Aw M _ q A a S 14336 HH (or_introl eq_refl) ltac:(lia) CA).
    + pose proof (L5SAR.astk_grows ar M M1 S 14336 STK MGM1) as (_ & _ & _ & _ & D1 & _). exact D1.
    + apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M1 DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M1 MGM1).
  - exact CK.
  - exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1).
  - exact ILK.
  - exact IAW.
  - exact AM1.
  - exact HH1.
Qed.

Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof. intros AC H1 H2 x Hx. apply AC. clear - H1 H2 Hx. lia. Qed.

(* [comment removed for export] *)
Lemma finish_short (fx : FPState) R M model LK Aw (b0 : Z) (cr' : credit) :
  stok model LK Aw ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 20) = Z_to_bv 64 (o + 1) -> getr R (reg 22) = Z_to_bv 64 n ->
  kept0 R -> saves M -> mem_ok M ->
  L5.u8_at RSEGS M o b0 -> 0 <= b0 <= 255 -> Z.testbit b0 0 = false -> 1 <= n <= 22 ->
  ri_inv HI LB FF LK cr' Aw M (vml_of model) ->
  PM.tb_ok (PM.VShort n) tg -> (n <= PM.vs_cap s -> [] = PM.vs_own s) ->
  PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV (PM.VShort n) tg)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5e8c M model) K.
Proof using All.
  intros STO A2 A8 A20 A22 KP SV (EK & DK & STK & ACO) B0 HB0 EVB Hn HH TBOK OWN CK.
  destruct STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  assert (VU64 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v).
  { intros a v X1 X2 X. apply (proj2 (L5A.u64_at_vis H M a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  pose proof (VU64 (S - 8) _ ltac:(lia) ltac:(lia) S8) as V8. pose proof (VU64 (S - 16) _ ltac:(lia) ltac:(lia) S16) as V16.
  pose proof (VU64 (S - 24) _ ltac:(lia) ltac:(lia) S24) as V24. pose proof (VU64 (S - 32) _ ltac:(lia) ltac:(lia) S32) as V32.
  pose proof (VU64 (S - 40) _ ltac:(lia) ltac:(lia) S40) as V40. pose proof (VU64 (S - 48) _ ltac:(lia) ltac:(lia) S48) as V48.
  pose proof (VU64 (S - 56) _ ltac:(lia) ltac:(lia) S56) as V56. pose proof (VU64 (S - 64) _ ltac:(lia) ltac:(lia) S64) as V64.
  pose proof (VU64 (S - 72) _ ltac:(lia) ltac:(lia) S72) as V72. pose proof (VU64 (S - 80) _ ltac:(lia) ltac:(lia) S80) as V80.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (B0v : L5.u8_at RSEGS MV o b0).
  { apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in *.
  LeanFeed.pfeed P (PMARZP.aapMS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => b0 | 38%nat => n
        | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
        | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
        | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
        | 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & CN & CB).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd5ee0 W_d38e4 r F_d38e4 eq_refl D_d38e4 R1ra ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => o + 0 <= a < o + 0 + 24).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr' Aw M model fx fx1 R 0xd5e8c R1 r M1v W1 K HH AM).
  { eapply msteps_trans; [exact MS1| exact MS2]. }
  { exact MG1. }
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); unfold W1 in Wa; lia| unfold W1 in Wa; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (NSH : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold W1 in X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  apply (KONT fx1 R1 M1 model1 LK Aw (PM.VShort n) tg cr').
  - apply regs_back; try assumption.
    intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - split; [intros i Hi; apply MGM1; apply ODEF; exact Hi|].
    split; [apply (PMFA.accA_agree M M1 o 24 (PMARZK.agsh_frame M M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
    split; [lia|]. rewrite <- VIS1 in CB. exact (proj1 (L5A.u8_at_vis _ M1 o (2 * n) (L5A.avis_sub _ o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CB).
  - reflexivity.
  - exact TBOK.
  - intros X. split; [exact (OWN X)| reflexivity].
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
    + apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M1 EK).
      apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M1 W1 FR1). intros a Ha CA OW Wa. unfold W1 in Wa.
      apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
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
Lemma saves_keep (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, S - 80 <= a < S -> ~ P a) ->
  140735332483152 <= S <= 2 ^ 47 -> saves M -> saves M'.
Proof using All.
  intros FRZ X HS (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  assert (AG : forall a, S - 80 <= a -> a + 8 <= S -> L5C.agree_on M M' a 8).
  { intros a H1 H2 i Hi. apply FRZ; [lia| apply X; lia]. }
  unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [apply AG; lia|lia|lia|eassumption]).
Qed.

(* [comment removed for export] *)
Lemma mem_ok_fill (M M' : word -> option byte) (pd m : Z) (LBo : list (Z * Z)) LK cr Aw model :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) ->
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (pd <= a < pd + m) -> ~ (S - 80 - 2560 <= a < S - 80) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  0 <= pd -> pd + m <= 2 ^ 47 ->
  ((o <= pd /\ pd + m <= o + 24) \/ (exists q A, In (q, A) LBo /\ q <= pd /\ pd + m <= q + A)) ->
  mem_ok M'.
Proof using All.
  intros HH (EK & DK & STK & ACO) MG FR H0 H1 WH. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
  set (P := fun a => (pd <= a < pd + m) \/ (S - 80 - 2560 <= a < S - 80)).
  assert (FRP : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FR; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  assert (NSH : forall x, P x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x).
  { intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; [| lia].
    destruct WH as [W|(q & A & Hin & W1 & W2)]; [lia|].
    destruct (bfacts _ _ _ _ _ _ q A HH (in_or_app _ _ _ (or_introl Hin))) as (_ & _ & _ & _ & _ & Q5 & _). lia. }
  split; [|split; [|split]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M' EK).
    apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M' P FRP). intros a Ha CA OW [Pa|Pa].
    + destruct WH as [W|(q & A & Hin & W1 & W2)].
      * apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * exact (PMARS1.own_not_aclient L ar C HI HIok LBo LB FF LK cr Aw M _ q A a S 14336 HH Hin ltac:(lia) CA).
    + destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB LBo FF S 14336 a CA)) as [Z1|Z1]; lia.
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M' DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M' MG).
  - exact (L5SAR.astk_grows ar M M' S 14336 STK MG).
  - exact (PMFA.accA_agree M M' o 24 (PMARZK.agsh_frame M M' P o 24 FRP NSH ltac:(lia) ltac:(lia)) ACO).
Qed.

(* [comment removed for export] *)
Lemma fit_short (fx : FPState) R M model LK Aw (n0 m : Z) :
  stok model LK Aw -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> n <= 22 -> 0 <= n0 -> tg = 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 0 ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 23) = Z_to_bv 64 22 ->
  kept0 R -> saves M -> mem_ok M -> L5.u8_at RSEGS M o (2 * n0) ->
  ri_inv HI LB FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d74 M model) K.
Proof using All.
  intros STO Es En Hm Hn Hn0 Etg A2 A8 A9 A10 A18 A23 KP SV MO B0 HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  LeanFeed.pfeed P (PMARZP.afitS_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
  unfold PMSPA.cfg.
  apply (PMARZK.fill_stage_pre L ar C HI LY HIok LB FF LK cr0 Aw M model fx fx1 R 0xd5d74 R1 (o + n0 + 1) m (S - 80) 0xd5e8c K HH (proj1 STO) MS1
           (aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) F1 ltac:(split; [lia| reflexivity]) F2 F10 F12 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(apply (L5.defined_sub M (S - 14336) 14336); [exact SDEF| lia| lia])).
  { right. exists o, 24. split; [exact AOB|]. lia. }
  { apply (L5.defined_sub M o 24); [exact ODEF| lia| lia]. }
  { apply (aacc_sub M o 24); [exact ACO| lia| lia]. }
  intros R3 M3 model3 HH3 AM3 MRT3 HID3 MG3 FR3 D3 KS3 A3.
  assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
  apply (finish_short fx1 R3 M3 model3 LK Aw (2 * n0) cr0).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
  - rewrite (KSR 2%nat) by inl. exact F2.
  - rewrite (KSR 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
  - rewrite (KSR 20%nat) by inl. exact F20.
  - rewrite (KSR 22%nat) by inl. rewrite F22. f_equal. lia.
  - intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - apply (saves_keep M M3 (fun a => (o + n0 + 1 <= a < o + n0 + 1 + m) \/ (S - 80 - 2560 <= a < S - 80))).
    + intros a Ha N. apply FR3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X].
    + intros a Ha [X|X]; lia.
    + lia.
    + exact SV.
  - apply (mem_ok_fill M M3 (o + n0 + 1) m [] LK cr0 Aw model HH MO MG3 FR3 ltac:(lia) ltac:(lia)). left; lia.
  - apply (L5C.u8_at_agree RSEGS M M3); [intros i Hi; apply FR3; lia| lia| lia| exact B0].
  - lia.
  - apply PMF.even_byte.
  - lia.
  - exact HH3.
  - subst tg. unfold PM.tb_ok. cbn. lia.
  - intros _. rewrite Es. reflexivity.
  - rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma fit_long (fx : FPState) R M model LK Aw (c n0 p m : Z) :
  stok model LK Aw -> s = PM.VLong c n0 p -> n = n0 + m -> 1 <= m -> n <= c - 1 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 1 ->
  getr R (reg 18) = Z_to_bv 64 n0 ->
  kept0 R -> saves M -> mem_ok M ->
  L5.u64_at RSEGS M o (c + 1) -> L5.u64_at RSEGS M (o + 16) p -> 0 <= n0 -> 26 <= c <= 2 ^ 27 -> c mod 2 = 0 -> PMSPA.accA M p c -> PM.tb_ok s tg ->
  ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d74 M model) K.
Proof using All.
  intros STO Es En Hm Hn A2 A8 A9 A10 A18 KP SV MO W0 W16 Hn0 Hc Hce ACP TBOK HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & DP & QO).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
  { apply (proj2 (L5A.u64_at_vis H M (o + 16) p (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  LeanFeed.pfeed P (PMARZP.afitL_conc fx R MV (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 43%nat => m | _ => 0 end)) ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
  assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
  assert (F2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
  unfold PMSPA.cfg.
  apply (PMARZK.fill_stage_pre L ar C HI LY HIok ((p, c) :: LB) FF LK cr0 Aw M model fx fx1 R 0xd5d74 R1 (n0 + p) m (S - 80) 0xd5e8c K HH (proj1 STO) MS1
           (aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) F1 ltac:(split; [lia| reflexivity]) F2 F10 F12 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(apply (L5.defined_sub M (S - 14336) 14336); [exact SDEF| lia| lia])).
  { left. exists p, c. split; [left; reflexivity| lia]. }
  { apply (L5.defined_sub M p c); [exact DP| lia| lia]. }
  { apply (aacc_sub M p c); [exact ACP| lia| lia]. }
  intros R3 M3 model3 HH3 AM3 MRT3 HID3 MG3 FR3 D3 KS3 A3.
  assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
  set (P := fun a => (n0 + p <= a < n0 + p + m) \/ (S - 80 - 2560 <= a < S - 80)).
  assert (FRP : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FR3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  assert (NSH : forall x, P x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  apply (finish_long fx1 R3 M3 model3 LK Aw p c tg cr0).
  - split; [exact AM3|]. split; [exact (L5LZ.model_rt_trans model0 model model3 MRT MRT3)|]. split; [exact ILK| exact IAW].
  - rewrite (KSR 2%nat) by inl. exact F2.
  - rewrite (KSR 8%nat) by inl. rewrite (KS1 8%nat) by inl. exact A8.
  - rewrite (KSR 20%nat) by inl. exact F20.
  - rewrite (KSR 22%nat) by inl. rewrite F22. f_equal. lia.
  - intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - apply (saves_keep M M3 P FRP); [intros a Ha [X|X]; lia| lia| exact SV].
  - apply (mem_ok_fill M M3 (n0 + p) m [(p, c)] LK cr0 Aw model HH MO MG3 FR3 ltac:(lia) ltac:(lia)). right. exists p, c. split; [left; reflexivity| lia].
  - apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia| exact W0].
  - apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FRP; [lia| intros [X|X]; lia]| lia| lia| exact W16].
  - lia.
  - lia.
  - exact Hce.
  - exact (PMFA.accA_agree M M3 p c (PMARZK.agsh_frame M M3 P p c FRP NSH ltac:(lia) ltac:(lia)) ACP).
  - exact HH3.
  - rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
  - intros _. rewrite Es. split; reflexivity.
  - rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
Qed.

End Call.
End WithHeap.
End PMARZ1.
