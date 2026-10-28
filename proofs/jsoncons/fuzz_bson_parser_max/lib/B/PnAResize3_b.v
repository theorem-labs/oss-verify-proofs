(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnARzKit_b PnAResizeP_b PnAReset1_b PnAResize1_b PnAResize2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnTxtKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_rd1008_d100c_b Ba0_code_rd102c_d1030_b.
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

Module PMARZ3.
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
Let fit_short := PMARZ1.fit_short L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let fit_long := PMARZ1.fit_long L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let grow_short := PMARZ2.grow_short L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let grow_long := PMARZ2.grow_long L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let mem_ok_obj := PMARZ2.mem_ok_obj L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.

Lemma sub_wrap1 x k : 0 <= x -> x <= k -> k < 2 ^ 63 -> ((18446744073709551615 * x) mod 2 ^ 64 + k) mod 2 ^ 64 = k - x.
Proof.
  intros H0 H1 H2. replace (18446744073709551615 * x) with (- x + x * 2 ^ 64) by (clear - H0; lia). rewrite Z_mod_plus_full.
  rewrite Zplus_mod_idemp_l. replace (- x + k) with (k - x) by (clear; lia). apply Z.mod_small. clear - H0 H1 H2. lia.
Qed.
Lemma sub_wrap2 x y : 0 <= x -> x < y -> y < 2 ^ 63 ->
  ((((18446744073709551615 * x) mod 2 ^ 64) + (y mod 2 ^ 64)) mod 2 ^ 64 + 18446744073709551615) mod 2 ^ 64 = y - x - 1.
Proof.
  intros H0 H1 H2. rewrite (Z.mod_small y) by (clear - H0 H1 H2; lia). rewrite (sub_wrap1 x y) by (clear - H0 H1 H2; lia).
  replace (y - x + 18446744073709551615) with ((y - x - 1) + 1 * 2 ^ 64) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_small. clear - H0 H1 H2. lia.
Qed.

Definition rs_regs (R : bvmap 5 word) : Prop :=
  forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).

Lemma saves_of (M : word -> option byte) :
  L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))) -> L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) ->
  L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) ->
  L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) ->
  L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) ->
  L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M.
Proof using All. intros. unfold saves. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame (M M' : word -> option byte) (LBo : list (Z * Z)) LK cr Aw model :
  ri_inv HI (LBo ++ LB) FF LK cr Aw M (vml_of model) ->
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 80 <= a < S - 80 + 80) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M'.
Proof using All.
  intros HH (EK & DK & STK & ACO) MG FR. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
  split; [|split; [|split]].
  - apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M' EK).
    apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M' (fun a => S - 80 <= a < S - 80 + 80) FR). intros a Ha CA OW Wa.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB LBo FF S 14336 a CA)) as [Z1|Z1]; lia.
  - apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M' DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M' MG).
  - exact (L5SAR.astk_grows ar M M' S 14336 STK MG).
  - apply (PMFA.accA_agree M M' o 24); [| exact ACO].
    apply (PMARZK.agsh_frame M M' (fun a => S - 80 <= a < S - 80 + 80) o 24 FR); [intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia].
Qed.

Lemma append_short (fx : FPState) R M model LK Aw (n0 m : Z) :
  stok model LK Aw -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> 0 <= n0 <= 22 -> PM.tb_ok s tg -> PMSPA.credit_le (scA (PM.pot_text HV s tg)) cr0 ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 m -> rs_regs R ->
  mem_ok M -> L5.u8_at RSEGS M o (2 * n0) ->
  ri_inv HI LB FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d10 M model) K.
Proof using All.
  intros STO Es En Hm Hn0 TBOK CR A10 A11 RR MO B0 HH.
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
  assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  destruct (PMTK.u64_of_defined RSEGS M o ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M o 24 o 8 ODEF); lia)) as (w & Hw & W0).
  pose proof (PMTK.u64_low_byte RSEGS M o w (2 * n0) W0 B0 Hw ltac:(lia)) as WL.
  pose proof (PMTK.short_size w n0 Hw WL Hn0) as HSS.
  assert (TB0 : Z.testbit w 0 = false).
  { rewrite <- (Z.mod_pow2_bits_low w 8 0) by lia. change (2 ^ 8) with 256. rewrite WL. apply PMF.even_byte. }
  assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by inl; exact Rsp0).
  assert (B0v : L5.u8_at RSEGS MV o (2 * n0)).
  { apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
  assert (W0v : L5.u64_at RSEGS MV o w).
  { apply (proj2 (L5A.u64_at_vis H M o _ (L5A.avis_sub H o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W0. }
  pose proof (PMARZP.aapS0_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 36%nat => w | 43%nat => m | _ => 0 end)) as P.
  cbn beta iota in P. rewrite HO in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMARZP.aligned; lia | lia | apply PMF.even_byte]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & EX).
  rewrite HSS in EX. rewrite (sub_wrap1 n0 22) in EX by lia.
  unfold PMSPA.cfg.
  assert (CONT : forall (fx1' : FPState) (R1' : bvmap 5 word) (pc1 : Z), msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd5d10) MV (seg_rom RSEGS)) (@mkst fx1' R1' (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
             (forall M1 model1, ri_inv HI LB FF LK cr0 Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> mem_ok M1 ->
                mrestrict (ahid Aw model) M1 = M1v -> L5.u8_at RSEGS M1 o (2 * n0) -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1' R1' pc1 M1 model1) K) ->
             srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d10 M model) K).
  { intros fx1' R1' pc1 MS K1. unfold PMSPA.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr0 Aw M model fx fx1' R 0xd5d10 R1' pc1 M1v (fun a => S - 80 <= a < S - 80 + 80) K HH AM MS MG1 FR1).
    { intros a Ha Wa. split; [apply (L5SAR.stack_client L ar LB FF 0 0 a); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1. apply (K1 M1 model1 HH1 AM1 MRT1).
    - exact (mem_ok_frame M M1 [] LK cr0 Aw model HH MO MGM1 FR1').
    - exact VIS1.
    - apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia| lia| lia| exact B0]. }
  destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 |(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
  - apply (CONT fx1 R1 0xd5d74 MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 B01.
    assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    apply (fit_short fx1 R1 M1 model1 LK Aw n0 m).
    + split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
    + exact Es.
    + exact En.
    + exact Hm.
    + lia.
    + lia.
    + rewrite Es in TBOK. destruct TBOK as (_ & _ & X). exact X.
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
    + exact E23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
    + exact MO1.
    + exact B01.
    + exact HH1.
  - apply (CONT fx1 R1 0xd5d9c MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 B01.
    assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    apply (grow_short fx1 R1 M1 model1 LK Aw n0 m).
    + split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
    + exact Es.
    + exact En.
    + exact Hm.
    + lia.
    + exact Hn0.
    + exact TBOK.
    + exact CR.
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
    + exact E23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
    + exact MO1.
    + exact HH1.
Qed.

Lemma append_long (fx : FPState) R M model LK Aw (c n0 p m : Z) :
  stok model LK Aw -> s = PM.VLong c n0 p -> n = n0 + m -> 1 <= m -> PM.tb_ok s tg -> PMSPA.credit_le (scA (PM.pot_text HV s tg)) cr0 ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 m -> rs_regs R ->
  mem_ok M -> vstr_at M o s ->
  ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M (vml_of model) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d10 M model) K.
Proof using All.
  intros STO Es En Hm TBOK CR A10 A11 RR MO VS HH.
  pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  rewrite Es in VS. destruct VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & ACP).
  destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (WST : L5.writable RSEGS MV (S - 80) 80).
  { apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  pose proof (PMF.u8_of_u64 RSEGS M o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
  assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
  assert (TB1 : Z.testbit (c + 1) 0 = true) by (rewrite <- (Z.mod_pow2_bits_low (c + 1) 8 0) by lia; exact ODB).
  assert (EC : 2 * ((c + 1) / 2) = c) by (pose proof (Z.div_mod (c + 1) 2 ltac:(lia)) as X; rewrite Z.add_mod, Hce in X by lia; cbn in X; lia).
  assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by inl; exact Rsp0).
  assert (B0v : L5.u8_at RSEGS MV o ((c + 1) mod 256)).
  { apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
  assert (W0v : L5.u64_at RSEGS MV o (c + 1)).
  { apply (proj2 (L5A.u64_at_vis H M o _ (L5A.avis_sub H o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W0. }
  assert (W8v : L5.u64_at RSEGS MV (o + 8) n0).
  { apply (proj2 (L5A.u64_at_vis H M (o + 8) _ (L5A.avis_sub H o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W8. }
  pose proof (PMARZP.aapL0_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 36%nat => c + 1 | 43%nat => m | _ => 0 end)) as P.
  cbn beta iota in P. rewrite HO in P.
  L5SAR.feed P ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & EX).
  rewrite EC in EX. rewrite (sub_wrap2 n0 c) in EX by lia.
  unfold PMSPA.cfg.
  assert (CONT : forall (fx1' : FPState) (R1' : bvmap 5 word) (pc1 : Z), msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd5d10) MV (seg_rom RSEGS)) (@mkst fx1' R1' (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
             (forall M1 model1, ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> mem_ok M1 ->
                mrestrict (ahid Aw model) M1 = M1v -> L5.u64_at RSEGS M1 o (c + 1) -> L5.u64_at RSEGS M1 (o + 16) p -> PMSPA.accA M1 p c ->
                srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1' R1' pc1 M1 model1) K) ->
             srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd5d10 M model) K).
  { intros fx1' R1' pc1 MS K1. unfold PMSPA.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok ((p, c) :: LB) FF LK cr0 Aw M model fx fx1' R 0xd5d10 R1' pc1 M1v (fun a => S - 80 <= a < S - 80 + 80) K HH AM MS MG1 FR1).
    { intros a Ha Wa. split; [apply (L5SAR.stack_client L ar _ FF 0 0 a); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1. apply (K1 M1 model1 HH1 AM1 MRT1).
    - exact (mem_ok_frame M M1 [(p, c)] LK cr0 Aw model HH MO MGM1 FR1').
    - exact VIS1.
    - apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia| lia| lia| exact W0].
    - apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia| lia| lia| exact W16].
    - destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & _).
      apply (PMFA.accA_agree M M1 p c); [| exact ACP].
      apply (PMARZK.agsh_frame M M1 (fun a => S - 80 <= a < S - 80 + 80) p c FR1'); [intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia]. }
  destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 |(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
  - apply (CONT fx1 R1 0xd5d74 MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 W01 W161 ACP1.
    assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    apply (fit_long fx1 R1 M1 model1 LK Aw c n0 p m).
    + split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
    + exact Es.
    + exact En.
    + exact Hm.
    + lia.
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + exact E18.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
    + exact MO1.
    + exact W01.
    + exact W161.
    + lia.
    + exact Hc.
    + exact Hce.
    + exact ACP1.
    + exact TBOK.
    + exact HH1.
  - apply (CONT fx1 R1 0xd5d9c MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 W01 W161 ACP1.
    assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
    apply (grow_long fx1 R1 M1 model1 LK Aw c n0 p m).
    + split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
    + exact Es.
    + exact En.
    + exact Hm.
    + lia.
    + lia.
    + exact TBOK.
    + exact Hc.
    + exact Hce.
    + exact W161.
    + exact ACP1.
    + exact CR.
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + exact E18.
    + exact E23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
    + exact MO1.
    + exact HH1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resize_entry (fx : FPState) :
  L5CA.amodel_ok Aw0 model0 -> ri_inv HI (PM.vs_own s ++ LB) FF LK0 cr0 Aw0 M0 (vml_of model0) ->
  getr R0 (reg 10) = Z_to_bv 64 o -> getr R0 (reg 11) = Z_to_bv 64 n ->
  vstr_at M0 o s -> PM.tb_ok s tg -> PMSPA.credit_le (scA (PM.pot_text HV s tg)) cr0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R0 0xd628c M0 model0) K.
Proof using All.
  intros AM0 HH A10 A11 VS TBOK CR.
  pose proof STK0 as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  pose proof VS as (DO & ACO & _).
  destruct (vfacts _ _ _ _ _ _ HH STK0) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
  set (H := ahid Aw0 model0) in *. set (MV := mrestrict H M0) in *.
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M0 o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (MR0 : model_rt model0 model0) by (unfold model_rt; destruct model0; reflexivity).
  assert (STO0 : stok model0 LK0 Aw0) by (split; [exact AM0|]; split; [exact MR0|]; split; apply incl_refl).
  assert (MO0 : mem_ok M0).
  { split; [intros a _; reflexivity|]. split; [intros a _ _ D; exact D|]. split; [exact STK0| exact ACO]. }
  assert (RR0 : rs_regs R0) by (intros x _; reflexivity).
  assert (NSHo : forall x, o + 0 <= x < o + 0 + 24 -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  unfold PMSPA.cfg.
  assert (CASE : (exists n0, s = PM.VShort n0) \/ (exists c n0 p, s = PM.VLong c n0 p)) by (destruct s as [x|x y z]; [left; exists x | right; exists x, y, z]; reflexivity).
  destruct CASE as [(n0 & Es)|(c & n0 & p & Es)]; rewrite Es in VS, HH.
  - (* [comment removed for export] *)
    destruct VS as (_ & _ & Hn0 & B0).
    assert (Hn1' : n <= n0 + 16384) by (pose proof Hn1 as Hn1c; rewrite Es in Hn1c; cbn [PM.vs_size] in Hn1c; unfold PM.CHUNK in Hn1c; lia).
    assert (B0v : L5.u8_at RSEGS MV o (2 * n0)).
    { apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
    pose proof (PMARZP.arzS_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 37%nat => n | _ => 0 end)) as P.
    cbn beta iota in P. rewrite HO in P.
    L5SAR.feed P ltac:(first [assumption | unfold PMARZP.aligned; lia | lia | apply PMF.even_byte]).
    destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
    assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
    replace (2 * n0 / 2) with n0 in EX by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    destruct EX as [(MS1 & KS1 & F13 & _ & F)|(MS1 & KS1 & F11 & _ & _ & F)].
    + (* [comment removed for export] *)
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by inl; exact Rsp0).
      assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by inl; exact A11).
      assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by inl; exact HO).
      pose proof (PMARZP.arzTS_conc fx1 R1 MV (fun j => match j with 2%nat => S | 37%nat => n | _ => 0 end)) as Q.
      cbn beta iota in Q. rewrite HO1 in Q.
      L5SAR.feed Q ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
      destruct Q as (fx2 & R2 & M2v & MG2 & _ & FR2 & MS2 & KS2 & _ & _ & _ & CN & CB).
      assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by inl; rewrite (KS1 1%nat) by inl; exact Rra0).
      pose proof (PMK.ret_to RSEGS fx2 R2 M2v 0xd62b8 W_d3cbc r F_d3cbc eq_refl D_d3cbc RA2 ltac:(lia) Hr2) as MS3.
      set (W1 := fun a => o + 0 <= a < o + 0 + 24).
      apply (L5SAR.apiece L ar C HI LYa HIok (PM.vs_own (PM.VShort n0) ++ LB) FF LK0 cr0 Aw0 M0 model0 fx fx2 R0 0xd628c R2 r M2v W1 K HH AM0).
      { eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]. }
      { exact MG2. }
      { exact FR2. }
      { intros a Ha Wa. unfold W1 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia| lia]. }
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2' VV2.
      apply (KONT fx2 R2 M2 model2 LK0 Aw0 (PM.VShort n) tg cr0).
      * apply L5SAR.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
        apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MGM2; apply DO; exact Hi|].
        split; [exact (PMFA.accA_agree M0 M2 o 24 (PMARZK.agsh_frame M0 M2 W1 o 24 FR2' NSHo ltac:(lia) ltac:(lia)) ACO)|].
        split; [lia|]. rewrite <- VIS2 in CB. exact (proj1 (L5A.u8_at_vis _ M2 o (2 * n) (L5A.avis_sub _ o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CB).
      * reflexivity.
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M2).
        -- apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M2 W1 FR2'). intros a Ha CA OW Wa. unfold W1 in Wa.
           apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- pose proof (L5SAR.astk_grows ar M0 M2 S 14336 STK0 MGM2) as (_ & _ & _ & _ & D2 & _). exact D2.
        -- apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M2 MGM2).
      * rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
      * exact MRT2.
      * apply incl_refl.
      * apply incl_refl.
      * exact AM2.
      * exact HH2.
    + (* [comment removed for export] *)
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd628c R1 0xd5d10 _ K HH AM0 MS1 (fun x X => X) (fun a _ => eq_refl)).
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
      assert (EM1 : M1 = M0).
      { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
        change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
      subst M1.
      apply (append_short fx1 R1 M0 model1 LK0 Aw0 n0 (n - n0)).
      * split; [exact AM1|]. split; [exact MRT1|]. split; apply incl_refl.
      * exact Es.
      * lia.
      * lia.
      * exact Hn0.
      * exact TBOK.
      * exact CR.
      * rewrite (KS1 10%nat) by inl. exact A10.
      * exact F11.
      * intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * exact MO0.
      * exact B0.
      * exact HH1.
  - (* [comment removed for export] *)
    pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & ACP).
    destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & _ & PO).
    pose proof (PMF.u8_of_u64 RSEGS M0 o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
    assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
    assert (B0v : L5.u8_at RSEGS MV o ((c + 1) mod 256)).
    { apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
    assert (W8v : L5.u64_at RSEGS MV (o + 8) n0).
    { apply (proj2 (L5A.u64_at_vis H M0 (o + 8) _ (L5A.avis_sub H o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W8. }
    pose proof (PMARZP.arzL_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 37%nat => n | _ => 0 end)) as P.
    cbn beta iota in P. rewrite HO in P.
    L5SAR.feed P ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
    assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
    destruct EX as [(MS1 & KS1 & F11 & _ & _ & F)|(MS1 & KS1 & F13 & _ & F)].
    + (* [comment removed for export] *)
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd628c R1 0xd5d10 _ K HH AM0 MS1 (fun x X => X) (fun a _ => eq_refl)).
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
      assert (EM1 : M1 = M0).
      { apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
        change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
      subst M1.
      apply (append_long fx1 R1 M0 model1 LK0 Aw0 c n0 p (n - n0)).
      * split; [exact AM1|]. split; [exact MRT1|]. split; apply incl_refl.
      * exact Es.
      * lia.
      * lia.
      * exact TBOK.
      * exact CR.
      * rewrite (KS1 10%nat) by inl. exact A10.
      * rewrite F11. f_equal. lia.
      * intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * exact MO0.
      * rewrite Es. exact VS.
      * exact HH1.
    + (* [comment removed for export] *)
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by inl; exact Rsp0).
      assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by inl; exact A11).
      assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by inl; exact HO).
      assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
      { apply (proj2 (L5A.u64_at_vis H M0 (o + 16) p (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
      assert (WRp : L5.writable RSEGS MV (p + n) 1).
      { apply (proj2 (L5A.writable_vis H M0 (p + n) 1 (VBLK p c (p + n) 1 ltac:(rewrite Es; left; reflexivity) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
        apply (L5C.writable_of_defined RSEGS M0 (p + n) 1); [apply (L5.defined_sub M0 p c (p + n) 1 DP); lia|lia|lia]. }
      assert (Dpo : p + n + 1 <= o \/ o + 24 <= p + n) by lia.
      pose proof (PMARZP.arzTL_conc fx1 R1 MV (fun j => match j with 2%nat => S | 35%nat => p | 37%nat => n | _ => 0 end)) as Q.
      cbn beta iota in Q. rewrite HO1 in Q.
      L5SAR.feed Q ltac:(first [assumption | unfold PMARZP.aligned; lia | lia]).
      destruct Q as (fx2 & R2 & M2v & MG2 & _ & FR2 & MS2 & KS2 & _ & _ & CN & C8).
      assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by inl; rewrite (KS1 1%nat) by inl; exact Rra0).
      pose proof (PMK.ret_to RSEGS fx2 R2 M2v 0xd62dc W_d3ce0 r F_d3ce0 eq_refl D_d3ce0 RA2 ltac:(lia) Hr2) as MS3.
      set (W1 := fun a => (o + 8 <= a < o + 8 + 8) \/ (p + n + 0 <= a < p + n + 0 + 1)).
      assert (Ip : In (p, c) (PM.vs_own (PM.VLong c n0 p) ++ LB)) by (left; reflexivity).
      apply (L5SAR.apiece L ar C HI LYa HIok (PM.vs_own (PM.VLong c n0 p) ++ LB) FF LK0 cr0 Aw0 M0 model0 fx fx2 R0 0xd628c R2 r M2v W1 K HH AM0).
      { eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]. }
      { exact MG2. }
      { intros a Ha Nw. apply FR2; [exact Ha| intros X; apply Nw; left; exact X| intros X; apply Nw; right; exact X]. }
      { intros a Ha [Wa|Wa]; split.
        - apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
        - lia.
        - apply (L5SAR.block_client L ar _ FF 0 0 p c a Ip); lia.
        - lia. }
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2' VV2.
      assert (NSH2 : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
      assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ W1 i) -> L5C.agree_on M0 M2 a m).
      { intros a0 m0 Ha0 Hm0 X i Hi. apply FR2'; [lia| apply X; exact Hi]. }
      apply (KONT fx2 R2 M2 model2 LK0 Aw0 (PM.VLong c n p) tg cr0).
      * apply L5SAR.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
        apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MGM2; apply DO; exact Hi|].
        split; [exact (PMFA.accA_agree M0 M2 o 24 (PMARZK.agsh_frame M0 M2 W1 o 24 FR2' NSH2 ltac:(lia) ltac:(lia)) ACO)|].
        split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W0]|].
        split; [rewrite <- VIS2 in C8; exact (proj1 (L5A.u64_at_vis _ M2 (o + 8) n (L5A.avis_sub _ o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C8)|].
        split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W16]|].
        split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MGM2; apply DP; exact Hi|].
        exact (PMFA.accA_agree M0 M2 p c (PMARZK.agsh_frame M0 M2 W1 p c FR2' NSH2 ltac:(lia) ltac:(lia)) ACP).
      * reflexivity.
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M2).
        -- apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M2 W1 FR2'). intros a Ha CA OW Wa. destruct Wa as [X|X].
           ++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ exact (PMARS1.own_not_aclient L ar C HI HIok [(p, c)] LB FF LK0 cr0 Aw0 M0 _ p c a S 14336 HH (or_introl eq_refl) ltac:(lia) CA).
        -- pose proof (L5SAR.astk_grows ar M0 M2 S 14336 STK0 MGM2) as (_ & _ & _ & _ & D2 & _). exact D2.
        -- apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M2 MGM2).
      * rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
      * exact MRT2.
      * apply incl_refl.
      * apply incl_refl.
      * exact AM2.
      * exact HH2.
Qed.

End Call.
End WithHeap.
End PMARZ3.
