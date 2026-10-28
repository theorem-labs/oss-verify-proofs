(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128OP1_b PnADec128OP2_b PnADec128OP3_b PnADec128S_b PnADec128Out1_b PnASrcReadK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnMemW PnSDec128Rnd2 PnADec128Bv.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128P3_b PnADec128P6_b PnADec128Rnd_b PnADec128Rnd2_b PnADec128RndC_b PnADec128RndM_b.

Module PNADRN3.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Definition HD (R0 : bvmap 5 word) (S F V : Z) (R : bvmap 5 word) (Mv : mem) (k : Z) : Prop :=
  PNADRN.RRa R0 S F R k
  /\ L5.u64_at RSEGS Mv (S - 136) (PNSDRN2.p0 (PNSDRN2.Wk V k) + 2 ^ 32 * PNSDRN2.p1 (PNSDRN2.Wk V k))
  /\ L5.u64_at RSEGS Mv (S - 128) (PNSDRN2.p2 (PNSDRN2.Wk V k) + 2 ^ 32 * PNSDRN2.p3 (PNSDRN2.Wk V k))
  /\ L5.u64_at RSEGS Mv (S - 168) (F + 32)
  /\ PNADD.digs F V Mv (k + 1) /\ PNADD.zers F Mv (k + 1).
Definition Wrnd (S F a : Z) : Prop := S - 136 <= a < S - 104 \/ F + 32 <= a < F + 176.
Definition Wkeep (S F a : Z) : Prop := (S - 256 <= a < S \/ F <= a < F + 24 \/ F + 32 <= a < F + 512) /\ ~ Wrnd S F a.


Lemma rnd_rdn_def (M : word -> option byte) : forall (n : nat) a bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) <> None -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs E i Hi D; [lia|].
  cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
  - rewrite L5C.add1_lit in E. destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. destruct i as [|i].
    + cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact Ea.
    + cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
  - destruct i as [|i]; [cbn [Z.of_nat] in D; rewrite Z.add_0_r in D; exfalso; apply D; exact Ea|].
    destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [y|]; [|discriminate E]. rewrite L5C.add1_lit in E.
    destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
Qed.
Lemma rnd_u64_same (M M' : word -> option byte) a v i : L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v -> a <= i < a + 8 ->
  M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros U U' Hi D D'. unfold L5.u64_at in U, U'.
  assert (Hj : (Z.to_nat (i - a) < 8)%nat) by lia.
  assert (E : i = a + Z.of_nat (Z.to_nat (i - a))) by lia.
  rewrite E in D, D' |- *. rewrite (rnd_rdn_def M' _ a _ U' _ Hj D'), (rnd_rdn_def M _ a _ U _ Hj D). reflexivity.
Qed.

Lemma rnd_fin (R0 Rf : bvmap 5 word) (S F fl V k : Z) (M0 MF : mem) (pcA pcB pc' : Z) :
  S - 256 + 256 <= F \/ F + 512 <= S - 256 -> 0 <= S - 256 -> S <= 2 ^ 47 -> 0 <= F -> F + 512 <= 2 ^ 47 -> 0 <= k <= 3 ->
  (forall a, (S - 256 <= a < S \/ F <= a < F + 24 \/ F + 32 <= a < F + 504) -> ~ (S - 136 <= a < S - 104) ->
     ~ (F + 32 + 36 * k <= a < F + 32 + 36 * k + 36) -> MF (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  L5.u64_at RSEGS M0 (F + 504) fl -> L5.u64_at RSEGS MF (F + 504) fl -> L5.defined M0 (F + 504) 8 -> L5.defined MF (F + 504) 8 ->
  (forall m, 0 <= m <= 8 -> PNADD.cell F MF (9 * k + m) (PNDF.dg V (9 * k + m))) ->
  PNADD.digs F V M0 (k + 1) -> PNADD.zers F M0 (k + 1) -> L5.u64_at RSEGS M0 (S - 168) (F + 32) ->
  (1 <= k -> L5.u64_at RSEGS MF (S - 136) (PNSDRN2.p0 (PNSDRN2.Wk V (k - 1)) + 2 ^ 32 * PNSDRN2.p1 (PNSDRN2.Wk V (k - 1)))
           /\ L5.u64_at RSEGS MF (S - 128) (PNSDRN2.p2 (PNSDRN2.Wk V (k - 1)) + 2 ^ 32 * PNSDRN2.p3 (PNSDRN2.Wk V (k - 1)))) ->
  ((k = 0 /\ pc' = pcA /\ PNADRN.RRo R0 S F Rf) \/ (1 <= k /\ pc' = pcB /\ PNADRN.RRa R0 S F Rf (k - 1))) ->
  (forall a, Wkeep S F a -> MF (Z_to_bv 64 a) = M0 (Z_to_bv 64 a))
  /\ ((k = 0 /\ pc' = pcA /\ PNADRN.RRo R0 S F Rf /\ PNADD.digs F V MF 0)
      \/ (1 <= k /\ pc' = pcB /\ HD R0 S F V Rf MF (k - 1))).
Proof.
  intros FFS GS0 GS1 GF0 GF1 Hk AG U0 UF D0 DF RC DG ZR C168 CW EX.
  assert (CX : forall i v, 0 <= i < 36 -> (i < 9 * k \/ 9 * k + 9 <= i) -> PNADD.cell F M0 i v -> PNADD.cell F MF i v).
  { intros i v Hi Ho C0. unfold PNADD.cell in *.
    apply (PNMW.u32_at_agree RSEGS M0 MF); [| clear - Hi GF0 GF1; lia| clear - Hi GF0 GF1; lia| exact C0].
    intros x Hx. apply AG; clear - Hx Hi Ho FFS GF0; lia. }
  assert (DGk : PNADD.digs F V MF k).
  { intros i Hi. destruct (Z_lt_le_dec i (9 * k + 9)) as [LT|GE].
    - replace i with (9 * k + (i - 9 * k)) by (clear; lia). apply RC. clear - Hi LT; lia.
    - apply CX; [clear - Hi Hk; lia| right; exact GE| apply DG; clear - GE Hi; lia]. }
  assert (ZRk : PNADD.zers F MF k).
  { intros i Hi. apply CX; [clear - Hi Hk; lia| left; clear - Hi; lia| apply ZR; clear - Hi; lia]. }
  split.
  - intros a (Ha & Hn). unfold Wrnd in Hn. destruct (Z_lt_le_dec a (F + 504)) as [LT|GE].
    + apply AG; [clear - Ha LT; lia| clear - Hn; lia| clear - Hn Hk; lia].
    + destruct (Z_lt_le_dec a (F + 512)) as [LT2|GE2].
      * apply (rnd_u64_same M0 MF (F + 504) fl a U0 UF ltac:(clear - GE LT2; lia)).
        -- replace a with (F + 504 + (a - (F + 504))) by (clear; lia). apply D0. clear - GE LT2; lia.
        -- replace a with (F + 504 + (a - (F + 504))) by (clear; lia). apply DF. clear - GE LT2; lia.
      * apply AG; [clear - Ha GE2; lia| clear - Hn; lia| clear - Hn Hk; lia].
  - destruct EX as [(K0 & EP & RO)|(K1 & EP & RA)].
    + left. split; [exact K0|]. split; [exact EP|]. split; [exact RO|]. subst k. exact DGk.
    + right. split; [exact K1|]. split; [exact EP|]. destruct (CW K1) as (C1 & C2).
      unfold HD. split; [exact RA|]. split; [exact C1|]. split; [exact C2|]. split.
      * apply (L5C.u64_at_agree RSEGS M0 MF); [| clear - GS0 GS1; lia| clear - GS0 GS1; lia| exact C168].
        intros x Hx. apply AG; clear - Hx FFS GS0 GF0 Hk; lia.
      * replace (k - 1 + 1) with k by (clear; lia). split; [exact DGk| exact ZRk].
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Lemma rnd_zero (E : dve) (X : dkc L ar HI E) (V k : Z) (fx : FPState) (R : bvmap 5 word) (Mc : mem) (modelc : Model)
    (LKc : list fframe) (Ac : list (Z * Z)) (fxh : FPState) (Rh : bvmap 5 word) (Mh : mem) (modelh : Model) :
  0 <= V < 2 ^ 113 -> 0 <= k <= 3 ->
  dst L ar HI E Mc modelc LKc Ac ->
  HD (vR E) (vsp E) (vF E) V R (mrestrict (ahid Ac modelc) Mc) k ->
  dst L ar HI E Mh modelh LKc Ac ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (vsp E - 120 <= a < vsp E - 104) ->
     mrestrict (ahid Ac modelh) Mh (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  PNADRN.RRb (vR E) (vsp E) (vF E) Rh k -> getr Rh (reg 24) = Z_to_bv 64 k ->
  PNSDRN2.Wk V k = 0 -> getr Rh (reg 18) = Z_to_bv 64 (vF E + 32) -> getr Rh (reg 12) = Z_to_bv 64 0 ->
  L5.u64_at RSEGS (mrestrict (ahid Ac modelh) Mh) (vsp E - 120) 0 -> L5.u64_at RSEGS (mrestrict (ahid Ac modelh) Mh) (vsp E - 112) 0 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (Mc' : mem) (modelc' : Model) (pc' : Z),
     dst L ar HI E Mc' modelc' LKc Ac ->
     (forall a, Wkeep (vsp E) (vF E) a -> mrestrict (ahid Ac modelc') Mc' (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
     ((k = 0 /\ pc' = 0xb4268 /\ PNADRN.RRo (vR E) (vsp E) (vF E) R' /\ PNADD.digs (vF E) V (mrestrict (ahid Ac modelc') Mc') 0)
      \/ (1 <= k /\ pc' = 0xb4164 /\ HD (vR E) (vsp E) (vF E) V R' (mrestrict (ahid Ac modelc') Mc') (k - 1))) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' pc' Mc' modelc') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fxh Rh 0xb4248 Mh modelh) (vK E).
Proof.
  intros HV Hk ST HD0 STh AGh RBh X24 W0 X18 X12 Z120 Z112 KX.
  pose proof HD0 as (_ & _ & _ & C168 & DG & ZR).
  dgeom L ar HI E X.
  pose proof (geom_rng L ar HI E X) as (GR1 & GR2 & _ & _ & _ & _ & GR7 & GR8 & _).
  assert (FFS0 : vsp E - 256 + 256 <= vF E \/ vF E + 512 <= vsp E - 256) by assumption.
  pose proof (c_Rtp L ar HI E X) as RTP.
  pose proof (PNADRN2.tail0 (vR E) (vsp E) (vF E)) as T0. try L5SAR.feed T0 ltac:(first [assumption | lia]).
  pose proof (PNADRN2.tail0r (vR E) (vsp E) (vF E)) as T0R. try L5SAR.feed T0R ltac:(first [assumption | lia]).
  pose proof (PNSDRN2.Wk_step V) as WKS. try L5SAR.feed WKS ltac:(first [assumption | lia]).
  assert (SG0 : dsg L ar HI E (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac) by (apply dsg_of_dst; exact ST).
  pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ SG0) as (GM0 & _). unfold gmem in GM0.
  destruct GM0 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FL0 & _) & _ & _ & _ & FD0).
  assert (D0f : L5.defined (mrestrict (ahid Ac modelc) Mc) (vF E + 504) 8) by (apply (L5.defined_sub _ (vF E) 512); [exact FD0| clear; lia| clear; lia]).
  pose proof (dmem_of L ar C HI LY HIok E X Mh modelh LKc Ac STh) as DMh. unfold dmem, PNADD.MIA in DMh.
  destruct DMh as ((WSh & _) & _).
  destruct (T0 fxh Rh (mrestrict (ahid Ac modelh) Mh) k 0 RBh X18 X24 X12 Hk ltac:(clear; lia) WSh)
    as (fx2 & R2 & MS2 & RB2 & Y18 & Y24 & Y1 & Y10 & Y11 & Y12).
  assert (UZ : forall a, 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS (mrestrict (ahid Ac modelh) Mh) a 0 ->
             L5.u32_at RSEGS (mrestrict (ahid Ac modelh) Mh) a 0 /\ L5.u32_at RSEGS (mrestrict (ahid Ac modelh) Mh) (a + 4) 0).
  { intros a H1 H2 H. split.
    - exact (PNMW.u32_of_u64_lo RSEGS _ a 0 H1 H2 ltac:(clear; lia) H).
    - exact (PNMW.u32_of_u64_hi RSEGS _ a 0 H1 H2 ltac:(clear; lia) H). }
  destruct (UZ (vsp E - 120) ltac:(clear - GR1; lia) ltac:(clear - GR2; lia) Z120) as (Q0 & Q1).
  destruct (UZ (vsp E - 112) ltac:(clear - GR1; lia) ltac:(clear - GR2; lia) Z112) as (Q2 & Q3).
  replace (vsp E - 120 + 4) with (vsp E - 116) in Q1 by (clear; lia).
  replace (vsp E - 112 + 4) with (vsp E - 108) in Q3 by (clear; lia).
  apply (dk_piece L ar C HI LY HIok E X fxh fx2 Rh R2 _ _ Mh modelh LKc Ac _ (fun _ => False) STh MS2 (mem_grows_refl _)
           (fun a _ _ => eq_refl) (fun a Wa => False_ind _ Wa)).
  intros M3 model3 ST3 HID3 VIS3.
  assert (V3 : mrestrict (ahid Ac model3) M3 = mrestrict (ahid Ac modelh) Mh) by (rewrite HID3; exact VIS3).
  rewrite <- V3 in Q0, Q1, Q2, Q3.
  pose proof RB2 as (G2 & _ & G4 & _).
  assert (Y4 : getr R2 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite G4; exact RTP).
  refine (PNADRNM.rnd_memcpy L ar C HI LY HIok E X fx2 R2 M3 model3 LKc Ac _ _ _ _ _ ST3 Q0 Q1 Q2 Q3 Y10 Y11 Y12 Y4 Y1 ltac:(reflexivity) ltac:(clear; lia) G2 _).
  intros Rb Mb modelb RPb STb D0 D1 D2 D3 AGb.
  pose proof (dmem_of L ar C HI LY HIok E X Mb modelb LKc Ac STb) as DMb. unfold dmem, PNADD.MIA in DMb.
  destruct DMb as ((WSb & _) & _).
  pose proof (PNADRN.RRb_preserved _ _ _ _ _ _ RB2 RPb) as RBb.
  assert (Zb18 : getr Rb (reg 18) = getr R2 (reg 18)) by (apply (L5SAR.cs_of_preserved R2 Rb 18%nat RPb); apply L5K.In_of_mem; vm_compute; reflexivity).
  assert (Zb24 : getr Rb (reg 24) = getr R2 (reg 24)) by (apply (L5SAR.cs_of_preserved R2 Rb 24%nat RPb); apply L5K.In_of_mem; vm_compute; reflexivity).
  rewrite Y18 in Zb18. rewrite Y24 in Zb24.
  assert (AGz : forall a, (vsp E - 256 <= a < vsp E \/ vF E <= a < vF E + 24 \/ vF E + 32 <= a < vF E + 504) -> ~ (vsp E - 136 <= a < vsp E - 104) ->
            mrestrict (ahid Ac modelb) Mb (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite (AGb a Ha) by (clear - Hn; lia). rewrite V3. apply AGh; clear - Ha Hn GR1 GR2 GR7 GR8; lia. }
  assert (SGb : dsg L ar HI E (PNST.bax_add_dec (vax E)) Mb modelb LKc Ac) by (apply dsg_of_dst; exact STb).
  pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ SGb) as (GMb & _). unfold gmem in GMb.
  destruct GMb as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FLb & _) & _ & _ & _ & FDb).
  assert (Cb168 : L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 168) (vF E + 32)).
  { apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) _); [| clear - GR1; lia| clear - GR2; lia| exact C168].
    intros x Hx. apply AGz; clear - Hx; lia. }
  destruct (T0R fx2 Rb (mrestrict (ahid Ac modelb) Mb) k RBb Zb18 Zb24 Hk WSb Cb168) as (fx3 & R3 & pc3 & MS3 & EX3).
  apply (dk_piece L ar C HI LY HIok E X fx2 fx3 Rb R3 _ _ Mb modelb LKc Ac _ (fun _ => False) STb MS3 (mem_grows_refl _)
           (fun a _ _ => eq_refl) (fun a Wa => False_ind _ Wa)).
  intros M4 model4 ST4 HID4 VIS4.
  assert (V4 : mrestrict (ahid Ac model4) M4 = mrestrict (ahid Ac modelb) Mb) by (rewrite HID4; exact VIS4).
  refine ((fun FIN => KX fx3 R3 M4 model4 pc3 ST4 (proj1 FIN) (proj2 FIN))
            (rnd_fin _ _ _ _ _ _ _ _ _ _ _ _ FFS0 GR1 GR2 GR7 GR8 Hk _ FL0 _ D0f _ _ DG ZR C168 _ EX3)).
  - intros a Ha Hn _. rewrite V4. exact (AGz a Ha Hn).
  - rewrite V4. exact FLb.
  - rewrite V4. apply (L5.defined_sub _ (vF E) 512); [exact FDb| clear; lia| clear; lia].
  - intros m Hm. pose proof W0 as W0'. unfold PNSDRN2.Wk in W0'.
    rewrite (PNDF.dg_W_zero V k m ltac:(clear - HV; lia) Hk Hm W0'). rewrite V4. unfold PNADD.cell.
    apply (PNMW.u32_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) _); [| clear - Hm Hk GR7 GR8; lia| clear - Hm Hk GR7 GR8; lia| apply ZR; clear - Hm Hk; lia].
    intros x Hx. apply AGz; clear - Hx Hm Hk FFS0 GR7; lia.
  - intros K1. rewrite (WKS k ltac:(clear - Hk K1; lia)), W0, Z.div_0_l by (clear; lia). rewrite V4. split.
    + assert (U : L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 136) (0 + 4294967296 * 0)).
      { apply PNMW.u64_of_u32x2; [clear - GR1; lia| clear - GR2; lia| clear; lia| clear; lia| exact D0| replace (vsp E - 136 + 4) with (vsp E - 132) by (clear; lia); exact D1]. }
      exact U.
    + assert (U : L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 128) (0 + 4294967296 * 0)).
      { apply PNMW.u64_of_u32x2; [clear - GR1; lia| clear - GR2; lia| clear; lia| clear; lia| exact D2| replace (vsp E - 128 + 4) with (vsp E - 124) by (clear; lia); exact D3]. }
      exact U.
Qed.

Lemma rnd_limbs (E : dve) (X : dkc L ar HI E) (V k : Z) (fx : FPState) (R : bvmap 5 word) (Mc : mem) (modelc : Model)
    (LKc : list fframe) (Ac : list (Z * Z)) (fxh : FPState) (Rh : bvmap 5 word) (Mh : mem) (modelh : Model) :
  0 <= V < 2 ^ 113 -> 0 <= k <= 3 ->
  dst L ar HI E Mc modelc LKc Ac ->
  HD (vR E) (vsp E) (vF E) V R (mrestrict (ahid Ac modelc) Mc) k ->
  dst L ar HI E Mh modelh LKc Ac ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (vsp E - 120 <= a < vsp E - 104) ->
     mrestrict (ahid Ac modelh) Mh (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  PNADRN.RRb (vR E) (vsp E) (vF E) Rh k -> getr Rh (reg 24) = Z_to_bv 64 k ->
  getr Rh (reg 10) = Z_to_bv 64 (vsp E - 120) -> getr Rh (reg 18) = Z_to_bv 64 (vF E + 28 + 36 * k) -> getr Rh (reg 21) = Z_to_bv 64 0 ->
  L5.u32_at RSEGS (mrestrict (ahid Ac modelh) Mh) (vsp E - 120) (PNSDRN2.p0 (PNSDRN2.Wk V k)) ->
  L5.u32_at RSEGS (mrestrict (ahid Ac modelh) Mh) (vsp E - 116) (PNSDRN2.p1 (PNSDRN2.Wk V k)) ->
  L5.u32_at RSEGS (mrestrict (ahid Ac modelh) Mh) (vsp E - 112) (PNSDRN2.p2 (PNSDRN2.Wk V k)) ->
  L5.u32_at RSEGS (mrestrict (ahid Ac modelh) Mh) (vsp E - 108) (PNSDRN2.p3 (PNSDRN2.Wk V k)) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (Mc' : mem) (modelc' : Model) (pc' : Z),
     dst L ar HI E Mc' modelc' LKc Ac ->
     (forall a, Wkeep (vsp E) (vF E) a -> mrestrict (ahid Ac modelc') Mc' (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
     ((k = 0 /\ pc' = 0xb4268 /\ PNADRN.RRo (vR E) (vsp E) (vF E) R' /\ PNADD.digs (vF E) V (mrestrict (ahid Ac modelc') Mc') 0)
      \/ (1 <= k /\ pc' = 0xb4164 /\ HD (vR E) (vsp E) (vF E) V R' (mrestrict (ahid Ac modelc') Mc') (k - 1))) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' pc' Mc' modelc') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fxh Rh 0xb41c8 Mh modelh) (vK E).
Proof.
  intros HV Hk ST HD0 STh AGh RBh X24 X10 X18 X21 P0 P1 P2 P3 KX.
  pose proof HD0 as (_ & _ & _ & C168 & DG & ZR).
  dgeom L ar HI E X.
  pose proof (geom_rng L ar HI E X) as (GR1 & GR2 & _ & _ & _ & _ & GR7 & GR8 & _).
  assert (FFS0 : vsp E - 256 + 256 <= vF E \/ vF E + 512 <= vsp E - 256) by assumption.
  pose proof (c_Rtp L ar HI E X) as RTP.
  pose proof (PNADRN2.reload (vR E) (vsp E) (vF E)) as RL. try L5SAR.feed RL ltac:(first [assumption | lia]).
  pose proof (PNADRN2.digits (vR E) (vsp E) (vF E)) as DGT. try L5SAR.feed DGT ltac:(first [assumption | lia]).
  pose proof (PNADRN2.tail (vR E) (vsp E) (vF E)) as TL. try L5SAR.feed TL ltac:(first [assumption | lia]).
  pose proof (PNADRN.limbs_call (vR E) (vsp E) (vF E)) as LC. try L5SAR.feed LC ltac:(first [assumption | lia]).
  pose proof (PNSDRN2.Wk_range V) as WKR. try L5SAR.feed WKR ltac:(first [assumption | lia]).
  pose proof (WKR k Hk) as HWk.
  assert (HW : 0 <= PNSDRN2.Wk V k < 2 ^ 113) by (clear - HWk HV; lia).
  pose proof (PNSDRN2.Wk_step V) as WKS. try L5SAR.feed WKS ltac:(first [assumption | lia]).
  assert (SG0 : dsg L ar HI E (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac) by (apply dsg_of_dst; exact ST).
  pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ SG0) as (GM0 & _). unfold gmem in GM0.
  destruct GM0 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FL0 & _) & _ & _ & _ & FD0).
  pose proof (dmem_of L ar C HI LY HIok E X Mh modelh LKc Ac STh) as DMh. unfold dmem, PNADD.MIA in DMh.
  destruct DMh as ((WSh & _) & _).
  destruct (PNSDRN2.parts_val _ HW) as (EW & B0 & B1 & B2 & B3).
  destruct (LC fxh Rh (mrestrict (ahid Ac modelh) Mh) k (PNSDRN2.p0 (PNSDRN2.Wk V k)) (PNSDRN2.p1 (PNSDRN2.Wk V k))
              (PNSDRN2.p2 (PNSDRN2.Wk V k)) (PNSDRN2.p3 (PNSDRN2.Wk V k)) RBh X10 X18 X21 X24 Hk ltac:(clear - B0; lia) B1 B2 B3 WSh P0 P1 P2 P3)
    as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & RB2 & Y18 & Y21 & Y24 & Y1 & Y10 & Y11 & Y12 & Q0 & Q1 & Q2 & Q3).
  pose proof (PNDF.ldiv4 (PNSDRN2.p0 (PNSDRN2.Wk V k)) (PNSDRN2.p1 (PNSDRN2.Wk V k)) (PNSDRN2.p2 (PNSDRN2.Wk V k)) (PNSDRN2.p3 (PNSDRN2.Wk V k))
                ltac:(clear - B0; lia) B1 B2 B3) as LD. cbn zeta in LD.
  destruct LD as (EQ & Hr3 & Hq0 & Hq1 & Hq2 & Hq3 & _).
  match type of EQ with _ = ?b * ?Qt + ?rt =>
    pose proof (PNSDRN2.limb_uniq Qt _ _ _ _ eq_refl Hq0 Hq1 Hq2 Hq3) as (U0 & U1 & U2 & U3);
    assert (HQ : Qt = PNSDRN2.Wk V k / b) by (apply (Z.div_unique_pos (PNSDRN2.Wk V k) b Qt rt); [exact Hr3| clear - EW EQ; lia]);
    assert (HR : rt = PNSDRN2.Wk V k mod b) by (apply (Z.mod_unique_pos (PNSDRN2.Wk V k) b Qt rt); [exact Hr3| clear - EW EQ; lia])
  end.
  apply (dk_piece L ar C HI LY HIok E X fxh fx2 Rh R2 _ _ Mh modelh LKc Ac M2 (fun a => vsp E - 120 <= a < vsp E - 104) STh MS2 MG2 FZ2).
  { intros a Wa. unfold Wmid. clear - Wa. lia. }
  intros M3 model3 ST3 HID3 VIS3.
  assert (V3 : mrestrict (ahid Ac model3) M3 = M2) by (rewrite HID3; exact VIS3).
  rewrite <- V3 in Q0, Q1, Q2, Q3.
  pose proof RB2 as (G2 & _ & G4 & _).
  assert (Y4 : getr R2 (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite G4; exact RTP).
  refine (PNADRNM.rnd_memcpy L ar C HI LY HIok E X fx2 R2 M3 model3 LKc Ac _ _ _ _ _ ST3 Q0 Q1 Q2 Q3 Y10 Y11 Y12 Y4 Y1 ltac:(reflexivity) ltac:(clear; lia) G2 _).
  intros Rb Mb modelb RPb STb D0 D1 D2 D3 AGb.
  pose proof (dmem_of L ar C HI LY HIok E X Mb modelb LKc Ac STb) as DMb. unfold dmem, PNADD.MIA in DMb.
  destruct DMb as ((WSb & _ & WFb & _) & _).
  pose proof (PNADRN.RRb_preserved _ _ _ _ _ _ RB2 RPb) as RBb.
  assert (Zb18 : getr Rb (reg 18) = getr R2 (reg 18)) by (apply (L5SAR.cs_of_preserved R2 Rb 18%nat RPb); apply L5K.In_of_mem; vm_compute; reflexivity).
  assert (Zb21 : getr Rb (reg 21) = getr R2 (reg 21)) by (apply (L5SAR.cs_of_preserved R2 Rb 21%nat RPb); apply L5K.In_of_mem; vm_compute; reflexivity).
  assert (Zb24 : getr Rb (reg 24) = getr R2 (reg 24)) by (apply (L5SAR.cs_of_preserved R2 Rb 24%nat RPb); apply L5K.In_of_mem; vm_compute; reflexivity).
  rewrite Y18 in Zb18. rewrite Y21 in Zb21. rewrite Y24 in Zb24.
  assert (AGn : forall a, (vsp E - 256 <= a < vsp E \/ vF E <= a < vF E + 24 \/ vF E + 32 <= a < vF E + 504) -> ~ (vsp E - 136 <= a < vsp E - 104) ->
            mrestrict (ahid Ac modelb) Mb (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite (AGb a Ha) by (clear - Hn; lia). rewrite V3.
    rewrite (FZ2 a) by (clear - Ha Hn GR1 GR2 GR7 GR8; lia). apply AGh; clear - Ha Hn GR1 GR2 GR7 GR8; lia. }
  assert (SGb : dsg L ar HI E (PNST.bax_add_dec (vax E)) Mb modelb LKc Ac) by (apply dsg_of_dst; exact STb).
  pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ SGb) as (GMb & _). unfold gmem in GMb.
  destruct GMb as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FLb & _) & _ & _ & _ & FDb).
  assert (Cb168 : L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 168) (vF E + 32)).
  { apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) _); [| clear - GR1; lia| clear - GR2; lia| exact C168].
    intros x Hx. apply AGn; clear - Hx; lia. }
  assert (CWb : 1 <= k -> L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 136) (PNSDRN2.p0 (PNSDRN2.Wk V (k - 1)) + 2 ^ 32 * PNSDRN2.p1 (PNSDRN2.Wk V (k - 1)))
                       /\ L5.u64_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 128) (PNSDRN2.p2 (PNSDRN2.Wk V (k - 1)) + 2 ^ 32 * PNSDRN2.p3 (PNSDRN2.Wk V (k - 1)))).
  { intros K1. rewrite (WKS k ltac:(clear - Hk K1; lia)), <- HQ, U0, U1, U2, U3. split.
    - apply PNMW.u64_of_u32x2; [clear - GR1; lia| clear - GR2; lia| exact Hq0| exact Hq1| exact D0| replace (vsp E - 136 + 4) with (vsp E - 132) by (clear; lia); exact D1].
    - apply PNMW.u64_of_u32x2; [clear - GR1; lia| clear - GR2; lia| exact Hq2| exact Hq3| exact D2| replace (vsp E - 128 + 4) with (vsp E - 124) by (clear; lia); exact D3]. }
  assert (D0f : L5.defined (mrestrict (ahid Ac modelc) Mc) (vF E + 504) 8) by (apply (L5.defined_sub _ (vF E) 512); [exact FD0| clear; lia| clear; lia]).
  destruct (RL fx2 Rb (mrestrict (ahid Ac modelb) Mb) k _ RBb Zb18 Zb21 Zb24 Hk Hr3 WSb)
    as (fx4 & R4 & pc4 & MS4 & RB4 & Z18 & Z21 & Z24 & [(-> & R0z) | (-> & Rnz & Z10)]).
  - destruct (TL fx4 R4 (mrestrict (ahid Ac modelb) Mb) k _ RB4 Z18 Z21 Z24 Hk ltac:(clear - Hr3; lia) WSb Cb168) as (fx5 & R5 & pc5 & MS5 & EX5).
    apply (dk_piece L ar C HI LY HIok E X fx2 fx5 Rb R5 _ _ Mb modelb LKc Ac _ (fun _ => False) STb (msteps_trans _ _ _ _ MS4 MS5) (mem_grows_refl _)
             (fun a _ _ => eq_refl) (fun a Wa => False_ind _ Wa)).
    intros M6 model6 ST6 HID6 VIS6.
    assert (V6 : mrestrict (ahid Ac model6) M6 = mrestrict (ahid Ac modelb) Mb) by (rewrite HID6; exact VIS6).
    refine ((fun FIN => KX fx5 R5 M6 model6 pc5 ST6 (proj1 FIN) (proj2 FIN))
              (rnd_fin _ _ _ _ _ _ _ _ _ _ _ _ FFS0 GR1 GR2 GR7 GR8 Hk _ FL0 _ D0f _ _ DG ZR C168 _ EX5)).
    + intros a Ha Hn _. rewrite V6. exact (AGn a Ha Hn).
    + rewrite V6. exact FLb.
    + rewrite V6. apply (L5.defined_sub _ (vF E) 512); [exact FDb| clear; lia| clear; lia].
    + intros m Hm. pose proof HR as HR'. rewrite R0z in HR'. unfold PNSDRN2.Wk in HR'.
      rewrite (PNDF.dg_round_zero V k m ltac:(clear - HV; lia) Hk Hm ltac:(symmetry; exact HR')). rewrite V6. unfold PNADD.cell.
      apply (PNMW.u32_at_agree RSEGS (mrestrict (ahid Ac modelc) Mc) _); [| clear - Hm Hk GR7 GR8; lia| clear - Hm Hk GR7 GR8; lia| apply ZR; clear - Hm Hk; lia].
      intros x Hx. apply AGn; clear - Hx Hm Hk FFS0 GR7; lia.
    + intros K1. rewrite V6. exact (CWb K1).
  - pose proof (DGT k Hk) as DK. unfold PNADRN2.digits_stmt in DK.
    destruct (DK fx4 R4 (mrestrict (ahid Ac modelb) Mb) _ RB4 Z10 Z18 Z21 Z24 ltac:(clear - Rnz Hr3; lia) WSb WFb)
      as (fx5 & R5 & M5 & MS5 & MG5 & FZ5 & RB5 & W18 & W21 & W24 & CELLS).
    pose proof (L5.writable_grows RSEGS _ _ _ _ MG5 WSb) as WS5.
    assert (C5168 : L5.u64_at RSEGS M5 (vsp E - 168) (vF E + 32)).
    { apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelb) Mb) M5); [| clear - GR1; lia| clear - GR2; lia| exact Cb168].
      intros x Hx. apply FZ5; clear - Hx Hk FFS0 GR1 GR2; lia. }
    destruct (TL fx5 R5 M5 k _ RB5 W18 W21 W24 Hk ltac:(clear; lia) WS5 C5168) as (fx6 & R6 & pc6 & MS6 & EX6).
    apply (dk_piece L ar C HI LY HIok E X fx2 fx6 Rb R6 _ _ Mb modelb LKc Ac M5 (fun a => vF E + 32 + 36 * k <= a < vF E + 32 + 36 * k + 36) STb
             (msteps_trans _ _ _ _ MS4 (msteps_trans _ _ _ _ MS5 MS6)) MG5 FZ5).
    { intros a Wa. unfold Wmid. clear - Wa Hk. lia. }
    intros M7 model7 ST7 HID7 VIS7.
    assert (V7 : mrestrict (ahid Ac model7) M7 = M5) by (rewrite HID7; exact VIS7).
    assert (A5 : forall x, vF E + 504 <= x < vF E + 512 -> M5 (Z_to_bv 64 x) = mrestrict (ahid Ac modelb) Mb (Z_to_bv 64 x)).
    { intros x Hx. apply FZ5; clear - Hx Hk GR7 GR8; lia. }
    refine ((fun FIN => KX fx6 R6 M7 model7 pc6 ST7 (proj1 FIN) (proj2 FIN))
              (rnd_fin _ _ _ _ _ _ _ _ _ _ _ _ FFS0 GR1 GR2 GR7 GR8 Hk _ FL0 _ D0f _ _ DG ZR C168 _ EX6)).
    + intros a Ha Hn Hr. rewrite V7. rewrite (FZ5 a) by (clear - Ha Hr GR1 GR2 GR7 GR8; lia). exact (AGn a Ha Hn).
    + rewrite V7. apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelb) Mb) M5); [| clear - GR7 GR8; lia| clear - GR7 GR8; lia| exact FLb].
      intros x Hx. apply A5; clear - Hx; lia.
    + rewrite V7. intros i Hi. rewrite (A5 (vF E + 504 + i)) by (clear - Hi; lia). replace (vF E + 504 + i) with (vF E + (504 + i)) by (clear; lia). apply FDb. clear - Hi; lia.
    + intros m Hm.
      match type of HR with ?rt = _ =>
        assert (DR : PNSDRN2.rdig rt m = PNDF.dg V (9 * k + m))
          by (rewrite <- (PNDF.dg_round V k m ltac:(clear - HV; lia) Hk Hm), HR; unfold PNSDRN2.rdig, PNSDRN2.Wk; reflexivity)
      end.
      rewrite <- DR. rewrite V7. exact (CELLS m Hm).
    + intros K1. rewrite V7. destruct (CWb K1) as (E1 & E2). split.
      * apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelb) Mb) M5); [| clear - GR1; lia| clear - GR2; lia| exact E1].
        intros x Hx. apply FZ5; clear - Hx Hk FFS0 GR1 GR2; lia.
      * apply (L5C.u64_at_agree RSEGS (mrestrict (ahid Ac modelb) Mb) M5); [| clear - GR1; lia| clear - GR2; lia| exact E2].
        intros x Hx. apply FZ5; clear - Hx Hk FFS0 GR1 GR2; lia.
Qed.

Lemma round_step (E : dve) (X : dkc L ar HI E) (V k : Z) (fx : FPState) (R : bvmap 5 word) (Mc : mem) (modelc : Model)
    (LKc : list fframe) (Ac : list (Z * Z)) :
  0 <= V < 2 ^ 113 -> 0 <= k <= 3 ->
  dst L ar HI E Mc modelc LKc Ac ->
  HD (vR E) (vsp E) (vF E) V R (mrestrict (ahid Ac modelc) Mc) k ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (Mc' : mem) (modelc' : Model) (pc' : Z),
     dst L ar HI E Mc' modelc' LKc Ac ->
     (forall a, Wkeep (vsp E) (vF E) a -> mrestrict (ahid Ac modelc') Mc' (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
     ((k = 0 /\ pc' = 0xb4268 /\ PNADRN.RRo (vR E) (vsp E) (vF E) R' /\ PNADD.digs (vF E) V (mrestrict (ahid Ac modelc') Mc') 0)
      \/ (1 <= k /\ pc' = 0xb4164 /\ HD (vR E) (vsp E) (vF E) V R' (mrestrict (ahid Ac modelc') Mc') (k - 1))) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' pc' Mc' modelc') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb4164 Mc modelc) (vK E).
Proof.
  intros HV Hk ST HD0 KX. pose proof HD0 as (RRk & C136 & C128 & _).
  dgeom L ar HI E X.
  pose proof (dmem_of L ar C HI LY HIok E X Mc modelc LKc Ac ST) as DM0. unfold dmem, PNADD.MIA in DM0.
  destruct DM0 as ((WS0 & _) & _).
  pose proof (PNSDRN2.Wk_range V) as WKR. try L5SAR.feed WKR ltac:(first [assumption | lia]).
  pose proof (WKR k Hk) as HWk.
  assert (HW : 0 <= PNSDRN2.Wk V k < 2 ^ 113) by (clear - HWk HV; lia).
  pose proof (PNADRN2.headfork (vR E) (vsp E) (vF E)) as HF. try L5SAR.feed HF ltac:(first [assumption | lia]).
  destruct (HF fx R (mrestrict (ahid Ac modelc) Mc) k (PNSDRN2.Wk V k) RRk Hk HW WS0 C136 C128)
    as (fx1 & R1 & M1 & pc1 & MS1 & MG1 & FZ1 & RB1 & X24 & BR).
  apply (dk_piece L ar C HI LY HIok E X fx fx1 R R1 _ _ Mc modelc LKc Ac M1 (fun a => vsp E - 120 <= a < vsp E - 104) ST MS1 MG1 FZ1).
  { intros a Wa. unfold Wmid. clear - Wa. lia. }
  intros M3 model3 ST3 HID3 VIS3.
  assert (V3 : mrestrict (ahid Ac model3) M3 = M1) by (rewrite HID3; exact VIS3).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (vsp E - 120 <= a < vsp E - 104) ->
            mrestrict (ahid Ac model3) M3 (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)).
  { intros a Ha Hn. rewrite V3. exact (FZ1 a Ha Hn). }
  destruct BR as [(-> & W0 & X18 & X12 & Z120 & Z112) | (-> & X10 & X18 & X21 & P0 & P1 & P2 & P3)].
  - rewrite <- V3 in Z120, Z112.
    exact (rnd_zero E X V k fx R Mc modelc LKc Ac fx1 R1 M3 model3 HV Hk ST HD0 ST3 AG3 RB1 X24 W0 X18 X12 Z120 Z112 KX).
  - rewrite <- V3 in P0, P1, P2, P3.
    exact (rnd_limbs E X V k fx R Mc modelc LKc Ac fx1 R1 M3 model3 HV Hk ST HD0 ST3 AG3 RB1 X24 X10 X18 X21 P0 P1 P2 P3 KX).
Qed.

Lemma rounds_from (E : dve) (X : dkc L ar HI E) (V : Z) (Mc0 : mem) (modelc0 : Model) (LKc : list fframe) (Ac : list (Z * Z)) :
  0 <= V < 2 ^ 113 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (Mc' : mem) (modelc' : Model),
     dst L ar HI E Mc' modelc' LKc Ac ->
     (forall a, Wkeep (vsp E) (vF E) a -> mrestrict (ahid Ac modelc') Mc' (Z_to_bv 64 a) = mrestrict (ahid Ac modelc0) Mc0 (Z_to_bv 64 a)) ->
     PNADRN.RRo (vR E) (vsp E) (vF E) R' -> PNADD.digs (vF E) V (mrestrict (ahid Ac modelc') Mc') 0 ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb4268 Mc' modelc') (vK E)) ->
  forall (n : nat) (fx : FPState) (R : bvmap 5 word) (Mc : mem) (modelc : Model),
  0 <= Z.of_nat n <= 3 ->
  dst L ar HI E Mc modelc LKc Ac ->
  HD (vR E) (vsp E) (vF E) V R (mrestrict (ahid Ac modelc) Mc) (Z.of_nat n) ->
  (forall a, Wkeep (vsp E) (vF E) a -> mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a) = mrestrict (ahid Ac modelc0) Mc0 (Z_to_bv 64 a)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb4164 Mc modelc) (vK E).
Proof.
  intros HV KX n. induction n as [|m IH]; intros fx R Mc modelc Hn ST H AG;
    apply (round_step E X V _ fx R Mc modelc LKc Ac HV Hn ST H);
    intros fx' R' Mc' modelc' pc' ST' AG' [(_ & -> & RO & DG) | (Hk & -> & H')].
  - apply KX; [exact ST' | | exact RO | exact DG]. intros a Wa. rewrite (AG' a Wa). exact (AG a Wa).
  - lia.
  - apply KX; [exact ST' | | exact RO | exact DG]. intros a Wa. rewrite (AG' a Wa). exact (AG a Wa).
  - apply (IH fx' R' Mc' modelc'); [lia | exact ST' | | ].
    + replace (Z.of_nat m) with (Z.of_nat (Datatypes.S m) - 1) by lia. exact H'.
    + intros a Wa. rewrite (AG' a Wa). exact (AG a Wa).
Qed.

Lemma rounds (E : dve) (X : dkc L ar HI E) (V : Z) (fx : FPState) (R : bvmap 5 word) (Mc : mem) (modelc : Model)
    (LKc : list fframe) (Ac : list (Z * Z)) :
  0 <= V < 2 ^ 113 ->
  dst L ar HI E Mc modelc LKc Ac ->
  HD (vR E) (vsp E) (vF E) V R (mrestrict (ahid Ac modelc) Mc) 3 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (Mc' : mem) (modelc' : Model),
     dst L ar HI E Mc' modelc' LKc Ac ->
     (forall a, Wkeep (vsp E) (vF E) a -> mrestrict (ahid Ac modelc') Mc' (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
     PNADRN.RRo (vR E) (vsp E) (vF E) R' -> PNADD.digs (vF E) V (mrestrict (ahid Ac modelc') Mc') 0 ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb4268 Mc' modelc') (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb4164 Mc modelc) (vK E).
Proof using All.
  intros HV ST H KX.
  apply (rounds_from E X V Mc modelc LKc Ac HV KX 3%nat fx R Mc modelc); [cbn; lia | exact ST | exact H | intros a _; reflexivity].
Qed.
End WithHeap.
End SCFG_1.
End PNADRN3.
