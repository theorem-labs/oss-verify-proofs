(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PmRef.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmRef_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmLibSanity_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmTopSpecsXW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopKitX_u5 TopSpecs_u5 HarnessXStretch_u5 HarnessXTail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require EncKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import LibSpecU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HNXWU.
Import HNXT.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Ltac ow := unfold L5.outside; let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w Hw Hin; unfold PML.ll_foot_xsrc, PMES.W_enc, PMES.O_STACK, PMES.O_DEPTH, PML.LIT_LO, PML.LIT_HI, PMES.ENC_SIZE in Hw; cbn [In map fst snd app Z.add Z.sub] in Hw;
  repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia|]); destruct Hw.
Ltac cov_stack := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; split; [ow | left; lia].
Ltac ocov := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; ow.
Ltac inb0 Hb := repeat (first [rewrite in_app_iff in Hb | rewrite in_app_iff | progress cbn [In] in Hb | progress cbn [In]]); clear - Hb; tauto.
Ltac inb := let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; inb0 Hb.
Ltac foot_in2 := unfold in_footx, PML.ll_footx_xsrc, PML.ll_foot_xsrc; cbn [app];
  first [ eexists; split; [left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 2 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 3 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 4 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 5 right; left; reflexivity | cbn [fst snd]; lia]
        | eexists; split; [do 6 right; left; reflexivity | cbn [fst snd]; lia] ].
Ltac wok := let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw; unfold PML.ll_foot_xsrc, PMES.W_enc, PMES.O_STACK, PMES.O_DEPTH, PML.LIT_LO, PML.LIT_HI in Hw; cbn [In map fst snd app Z.add Z.sub] in Hw;
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; first [left; lia | right; split; [lia|]; split; [lia|]; let a := fresh "a" in let Hi := fresh "Hi" in intros a Hi; unfold L5.in_rng in Hi; cbn [fst snd] in Hi; foot_in2]|]); destruct Hw.
Ltac to_out AG lo len := apply (TK.samem_weaken _ _ _ _ AG); let a := fresh "a" in let Ho := fresh "Ho" in let Hin := fresh "Hin" in
  intros a Ho Hin; apply (Ho (lo, len) (or_introl eq_refl)); unfold L5.in_rng; cbn [fst snd]; lia.
Ltac mok BV Hh Hl Hmat := split; [rewrite (L5C.halted_but_vm _ _ BV); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV); exact Hmat]].

Lemma foot11_small : forall a, PML.in_foot11 a -> a < 2 ^ 39.
Proof.
  intros a (iv & Hiv & Hr). unfold PML.ll_foot_xsrc in Hiv. cbn [In] in Hiv.
  repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Variable WD_SCR : Z.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis STRINIT : PMS.strinit_spec L HI.
Hypothesis ISS : PMS.iss_ctor_spec L HI.
Hypothesis ENC_CTOR : PMES.enc_ctor_spec L HI.
Hypothesis RCTOR : PMS.reader_ctor_spec L HI.
Hypothesis SYSCAT : PMS.system_category_spec L.
Hypothesis READXW : PMXW.read_specxwU L HI STRTOD_SCR WD_SCR.
Hypothesis PDTOR : PMS.parser_dtor_spec L HI.
Hypothesis SDTOR : PMS.source_dtor_spec L HI.
Hypothesis ENC_DTOR : PMES.enc_dtor_spec L HI.
Hypothesis OPDELS : PMS.opdel_sized_spec L HI.
Hypothesis LOCDTOR : PMS.locale_dtor_spec L.
Hypothesis ISTRDTOR : TPS.istream_dtor_spec L.
Hypothesis IOSBDTOR : TPS.iosb_dtor_spec L.
Hypothesis ROOM0 : forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> PmRef.PMR.IND txt < 2 ^ 34 ->
  PmLibSpecsW_u5.PMW.wroomU PmEncSpecs_u5.PMES.g0 (PmRef_u5.PMR.K txt) (PmRef_u5.PMR.ALLOW txt).

Section Run.
Variable Lay : lib_layout.
Hypothesis LH : ll_heap Lay = L.
Hypothesis LF : ll_foot Lay = PML.ll_footx_xsrc.
Hypothesis LC : LCU.lay_creditU L Lay.
Let SS := ll_stack Lay.
Hypothesis HSS : 1376 + 9568 <= SS.
Hypothesis HSSR : 1376 + PMX.READX_SCR STRTOD_SCR WD_SCR <= SS.
Variables (LB : list (Z * Z)) (cr : credit) (sp ra : Z) (pyld : list byte) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Let n := Z.of_nat (length pyld).
Hypothesis Psp : getr R 2%bv = Z_to_bv 64 sp.
Hypothesis Ptp : getr R 4%bv = Z_to_bv 64 PML.TP.
Hypothesis Plen : 0 <= n < 2 ^ 26.
Hypothesis Prok : L5.ra_ok ra.
Hypothesis SPOK : HSX.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis BOK0 : TK2.blocks_ok L LB.
Hypothesis HK0 : K [].
Hypothesis PIND : PmRef.PMR.IND (map bv_unsigned pyld) < 2 ^ 34.
Hypothesis CONT : forall (fx' : FPState) (g' : PML.ls_state) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit),
  PML.fp_ok fx' -> lib_post Lay PMX.pm_staticsx g' LB cr sp pyld R M R' M' cr' -> hi_heap HI LB cr' M' (m_vmmaps model') -> model_but_vm model model' ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' ra M' model') K.

Lemma step_out_g : forall F reps M1 M2 LBx crk modelk,
  hi_heap HI LBx crk M1 (m_vmmaps modelk) -> TK.samem (L5.outside F) M1 M2 -> mem_grows M1 M2 ->
  (forall w, In w F -> (sp - SS <= fst w /\ fst w + snd w <= sp - 40 /\ 0 <= snd w)) -> (forall b, In b (PML.srep_blocks reps) -> In b LBx) ->
  HNXT.pers sp ra R reps M1 -> TK2.FR L LB sp SS in_footx M M1 ->
  HNXT.pers sp ra R reps M2 /\ TK2.FR L LB sp SS in_footx M M2 /\ hi_heap HI LBx crk M2 (m_vmmaps modelk) /\
  TK2.statics_cov (L5.outside F) /\ TK2.w_si L F /\ TKX.lits_cov (L5.outside F).
Proof.
  intros F reps M1 M2 LBx crk modelk HH AG GR HF HB PE FR1.
  pose proof SPOK as (Hspb & Hsp16).
  pose proof (eq_refl : SS = ll_stack Lay) as ESS.
  assert (OUTH : forall a, (a < sp - SS \/ sp - 40 <= a) -> L5.outside F a).
  { intros a Ha w Hw Hin. destruct (HF w Hw) as (A & B & C). unfold L5.in_rng in Hin. lia. }
  assert (WSI : TK2.w_si L F) by (intros w Hw; left; destruct (HF w Hw) as (A & B & C); lia).
  assert (BOKx : TK2.blocks_ok L LBx) by (eapply TK2.blocks_ok_heap; eassumption).
  split; [| split; [| split; [| split; [| split]]]].
  - apply (HNXT.pers_x Lay sp ra pyld R SPOK (L5.outside F) M1 M2 reps AG); [intros i Hi; apply OUTH; lia | | exact PE].
    apply (TK2.str_cov_out L LAY); [lia | intros i Hi; apply OUTH; lia | exact WSI | intros b Hb; exact (BOKx b (HB b Hb))].
  - eapply TK2.FR_grows; try eassumption; try lia.
    intros a Ha. left. destruct (HNXT.not_outside F a Ha) as (w & Hw & Hin). destruct (HF w Hw) as (A & B & C). unfold L5.in_rng in Hin. lia.
  - eapply TK2.heap_stack_write with (lo := sp - SS) (hi := sp); try eassumption; try lia.
    apply (TK.samem_weaken _ _ _ _ AG). intros a Ha. apply OUTH. lia.
  - first [apply (TK2.statics_cov_out L LAY) | apply (TK2.statics_cov_out L)]; [intros w Hw; destruct (HF w Hw) as (A & B & C); lia | lia].
  - exact WSI.
  - apply TKX.lits_cov_out. intros w Hw. destruct (HF w Hw) as (A & B & C). unfold PML.LIT_LO, PML.LIT_HI. left. lia.
Qed.

Lemma run_okU : forall (fx : FPState) (g : PML.ls_state) ptr,
  PML.fp_ok fx -> getr R 1%bv = Z_to_bv 64 ra -> getr R 10%bv = Z_to_bv 64 ptr -> getr R 11%bv = Z_to_bv 64 n ->
  ((length pyld = 0%nat) \/ (0 < n /\ In (ptr, n) LB)) -> rdn RSEGS M (Z_to_bv 64 ptr) (length pyld) = Some pyld ->
  credit_le (LCU.pm_creditxU L n) cr -> PML.ls_ok g M -> PML.lits_ok M -> hi_heap HI LB cr M (m_vmmaps model) -> PML.model_ok model ->
  (forall a, sp - SS <= a < sp -> M (Z_to_bv 64 a) <> None) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_LIB M model) K.
Proof.
  intros fx g ptr Hfp Pra Pptr Pn Ppl Prd Pcr Pls Plits Hh0 Hmod Hdef.
  pose proof (eq_refl : n = Z.of_nat (length pyld)) as En.
  pose proof (eq_refl : SS = ll_stack Lay) as ESS.
  pose proof Hmod as (Hhalt & Hlazy & Hmat).
  pose proof SPOK as (Hspb & Hsp16).
  pose proof (PmLayout.ly_kpm L LAY) as KPM0.
  pose proof (PmLayout.ly_bov L LAY) as BOV0.
  assert (OPN : PMS.OPNEW_SCR = 8240) by reflexivity.
  set (txt := map bv_unsigned pyld).
  assert (Htxt : Z.of_nat (length txt) = n) by (unfold txt; rewrite length_map; reflexivity).
  assert (FR0 : TK2.FR L LB sp SS in_footx M M) by (split; [intros; reflexivity | exact Hdef]).
  assert (Hpr : length pyld = 0%nat \/ (4096 <= ptr /\ ptr + n <= hl_ceil L /\ In (ptr, n) LB)).
  { destruct Ppl as [E|(Hn & Hin)]; [left; exact E | right].
    pose proof (BOK0 _ Hin) as Bk. unfold block_range in Bk; cbn [fst snd] in Bk. split; [lia|]. split; [lia|]. exact Hin. }
  apply (HSX.s_entry FPM fx R M model K sp ra Hhalt Hlazy Hfp Psp Pra).
  { unfold L5.ra_ok in Prok; lia. }
  { exact SPOK. }
  { intros i Hi. apply Hdef. lia. }
  intros fx1 R1 M1 Hfp1 R1sp R1ra R1a0 R1a1 R1a2 KS1 RA1 S01 AG1 GR1.
  assert (FR1 : TK2.FR L LB sp SS in_footx M M1).
  { eapply TK2.FR_grows with (K := fun a => ~ (sp - 1376 <= a < sp)); try eassumption; try lia;
    intros a Ha; left; apply NNPP in Ha; lia. }
  assert (HH1 : hi_heap HI LB cr M1 (m_vmmaps model)).
  { eapply TK2.heap_stack_write with (lo := sp - 1376) (hi := sp); try eassumption; lia. }
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 1376) (48 + PMS.OPNEW_SCR)).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M1); try eassumption; try lia. }
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS1 4%bv ltac:(kin)); exact Ptp).
  assert (BY1 : L5.bytes_at RSEGS M1 ptr txt).
  { destruct Hpr as [E|(Hp0 & Hp1 & Hin)].
    - intros i Hi. exfalso. unfold txt in Hi. rewrite length_map in Hi. lia.
    - apply (L5C.rdn_bytes_at RSEGS M1 pyld ptr); [lia | lia | ].
      rewrite (TK.rdn_samem (fun a => ~ (sp - 1376 <= a < sp)) M M1 ptr (length pyld) AG1); [exact Prd | lia | lia | ].
      intros i Hi Hc. lia. }
  pose proof HIok as HOK. destruct HOK as [_ _ _ _ _ HWF _].
  assert (DF1 : L5.defined M1 ptr n).
  { destruct Hpr as [E|(Hp0 & Hp1 & Hin)]; [intros i Hi; lia |].
    destruct (HWF LB cr M1 _ HH1) as (BW & _). destruct (BW _ Hin) as (_ & Dd & _). exact Dd. }
  assert (DO1 : L5.defined M1 (sp - 40) 24) by (intros i Hi; apply (proj2 FR1); lia).
  assert (CLU0 : 0 <= PMES.CLU) by (unfold PMES.CLU; lia).
  pose proof (LCU.kenc_g0 L) as KG0. pose proof (LCU.benc_g0 L) as BG0.
  pose proof Pcr as (Pk & Pb). unfold LCU.pm_creditxU in Pk, Pb; cbn [fst snd] in Pk, Pb.
  pose proof (HNXT.str_cap_bounds n (proj1 Plen)) as SCB.
  eapply (STRINIT LB cr (sp - 40) ptr (sp - 1376) _ txt fx1 R1 M1 model K HH1 Hmod HK0 Hfp1).
  { split; [apply HNXT.mk_entry; [exact R1ra | split; [lia | reflexivity] | exact R1sp | exact TP1 | exact STK1] |].
    split; [exact R1a0 |].
    split; [unfold PML.a1; rewrite R1a1; exact Pptr |].
    split; [unfold PML.a2; rewrite Htxt, R1a2; exact Pn |].
    split; [rewrite Htxt; lia |].
    split; [exact BY1 |].
    split; [rewrite Htxt; exact DF1 |].
    split; [HNXT.oos Hsp16 |].
    split; [exact DO1 |].
    split.
    - destruct Hpr as [E|(Hp0 & Hp1 & Hin)]; [left | right].
      + unfold txt. apply length_zero_iff_nil. rewrite length_map. exact E.
      + exists (ptr, n). cbn [fst snd]. rewrite Htxt. split; [exact Hin | lia].
    - intros _. rewrite Htxt. unfold credit_ok. lia. }
  intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 POST2 RP2 HP2 BV2 HH2.
  (* after strinit: one string representation for both cases *)
  destruct POST2 as (EW2 & ELBk2 & POST2). subst W2 LBk2.
  assert (S2 : exists reps, PML.str_at_w M2 (sp - 40) reps /\ PML.srep_chars reps = txt /\ LB2 = PML.srep_blocks reps ++ LB /\
                 fst cr - hl_k_per_malloc L <= fst cr2 /\ snd cr - (n + 10 + hl_b_overhead L) <= snd cr2 /\
                 (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10)).
  { destruct POST2 as [(Q0 & SA & ELB & ECR) | (Q0 & p & SA & FB & ELB & ECR)].
    - exists (PML.SShort txt). cbn [PML.srep_chars PML.srep_blocks app]. subst LB2 cr2.
      split; [exact SA|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros b [].
    - exists (PML.SLong (PML.str_cap (Z.of_nat (length txt))) p txt). cbn [PML.srep_chars PML.srep_blocks app]. subst LB2 cr2.
      rewrite Htxt in *. unfold debit; cbn [fst snd].
      split; [exact SA|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
      intros b [<-|[]]. cbn [snd]. lia. }
  destruct S2 as (reps & SA2 & LEN2 & ELB2 & CR2k & CR2b & CAPs). subst LB2.
  assert (BOK2 : TK2.blocks_ok L (PML.srep_blocks reps ++ LB)) by (eapply TK2.blocks_ok_heap; eassumption).
  assert (AG2 : TK.samem (TK2.keepH L LB [(sp - 40, 24)] (sp - 1376) (48 + PMS.OPNEW_SCR)) M1 M2)
    by (eapply TK2.hpres_samem; try eassumption; lia).
  assert (MOK2 : PML.model_ok model2) by (mok BV2 Hhalt Hlazy Hmat).
  pose proof MOK2 as (Hhalt2 & Hlazy2 & Hmat2).
  assert (FR2 : TK2.FR L LB sp SS in_footx M M2).
  { eapply TK2.FR_hpres; try eassumption; try apply incl_refl; try lia;
    intros w a Hw Hin; destruct Hw as [<-|[]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; left; lia. }
  assert (CV2 : forall a, sp - 1376 <= a < sp -> ~ (sp - 40 <= a < sp - 16) -> TK2.keepH L LB [(sp - 40, 24)] (sp - 1376) (48 + PMS.OPNEW_SCR) a).
  { intros a Ha Hn. split; [| left; lia]. intros w Hw Hin. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin; cbn [fst snd] in Hin. lia. }
  assert (PE2 : HNXT.pers sp ra R reps M2).
  { split; [| split; [| exact SA2]].
    - apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply CV2; lia | exact RA1].
    - apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply CV2; lia | exact S01]. }
  assert (Pls1 : PML.ls_ok g M1).
  { apply (TK2.ls_ok_x _ M M1 AG1); [apply TK2.statics_cov_lo; intros a Ha Hc; lia | exact Pls]. }
  assert (LIT1 : PML.lits_ok M1).
  { apply (TKX.lits_ok_x _ M M1 AG1); [intros a Ha Hc; unfold PML.LIT_LO, PML.LIT_HI in Ha; lia | exact Plits]. }
  assert (Pls2 : PML.ls_ok g M2) by (apply (TK2.ls_ok_x _ M1 M2 AG2); [st_cov | exact Pls1]).
  assert (LIT2 : PML.lits_ok M2) by (apply (TKX.lits_ok_x _ M1 M2 AG2); [lit_cov | exact LIT1]).
  assert (R2sp : getr R2 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP2 2%bv CS2); exact R1sp).
  assert (KS2 : TK.keepsR HSX.KS8 R R2) by (apply (TK.keepsR_trans _ R R1 R2 KS1); apply KSP; exact RP2).
  assert (ISSv : 80 + Z.max PMS.CTOR_SCR PMS.ISLAND_SCR = 9344) by (vm_compute; reflexivity).
  pose proof (HNXT.copy_cap_bounds n (proj1 Plen)) as CCB.
  apply (HSX.s_r_strinit FPM fx2 R2 M2 model2 K sp Hhalt2 Hlazy2 Hfp2 R2sp SPOK).
  intros fx3 R3 Hfp3 R3sp R3ra R3a0 R3a1 R3a2 KS3.
  assert (KS3' : TK.keepsR HSX.KS8 R R3) by (exact (TK.keepsR_trans _ R R2 R3 KS2 KS3)).
  assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS3' 4%bv ltac:(kin)); exact Ptp).
  assert (STK3 : L5C.stk (hl_sptop L) M2 (sp - 1376) (80 + Z.max PMS.CTOR_SCR PMS.ISLAND_SCR)).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M2); try eassumption; try lia. }
  eapply (ISS (PML.srep_blocks reps ++ LB) cr2 (sp - 312) (sp - 40) (sp - 1376) _ reps fx3 R3 M2 model2 K HH2 MOK2 HK0 Hfp3).
  { split; [apply HNXT.mk_entry; [exact R3ra | split; [lia | reflexivity] | exact R3sp | exact TP3 | exact STK3] |].
    split; [exact R3a0 |]. split; [exact R3a1 |]. split; [exact R3a2 |].
    split; [exact SA2 |].
    split; [intros b Hb; apply in_or_app; left; exact Hb |].
    split; [rewrite LEN2, Htxt; lia |].
    split; [HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |].
    split; [unfold PML.apart; lia |].
    split; [intros i Hi; apply (proj2 FR2); lia |].
    split; [intros i Hi; apply (proj2 FR2); lia |].
    split; [destruct g; [left; exact Pls2 | right; apply ls1_mid; exact Pls2 | right; apply ls2_mid; exact Pls2] |].
    rewrite LEN2, Htxt. unfold credit_ok. lia. }
  intros fx4 R4 M4 model4 LB4 cr4 LBk4 W4 Hfp4 POST4 RP4 HP4 BV4 HH4.
  (* after the iss ctor *)
  destruct POST4 as (rep & LENr & ISRC4 & MID4 & ELB4 & ELBk4 & FBr & CRr & EW4). subst LB4 LBk4 W4.
  assert (MOK4 : PML.model_ok model4) by (mok BV4 Hhalt2 Hlazy2 Hmat2).
  pose proof MOK4 as (Hhalt4 & Hlazy4 & Hmat4).
  assert (BOK4 : TK2.blocks_ok L (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by (eapply TK2.blocks_ok_heap; eassumption).
  assert (WOK4 : HNXT.w_ok sp ((sp - 312, 272) :: map (fun iv : Z * Z => (fst iv, snd iv - fst iv)) PML.ll_foot_xsrc))
    by (unfold HNXT.w_ok; wok).
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M2 M4 _ _ _ HP4 BOK2 (incl_refl _)
              ltac:(lia) ltac:(lia) WOK4 PE2 FR2) as (PE4 & FR4 & AG4 & WSI4).
  assert (CR4 : fst cr2 - hl_k_per_malloc L <= fst cr4 /\ snd cr2 - (n + 52 + hl_b_overhead L) <= snd cr4 /\
                (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52)).
  { rewrite LEN2, Htxt in FBr. destruct (PML.srep_blocks rep) as [|b0 bs] eqn:EB.
    - rewrite (CRr eq_refl). split; [lia|]. split; [lia|]. intros b [].
    - destruct (FBr b0 (or_introl eq_refl)) as (_ & Ecap & Ecr). subst cr4. unfold debit; cbn [fst snd]. rewrite Ecap.
      split; [lia|]. split; [lia|]. intros b Hb. destruct (FBr b Hb) as (_ & Eb & _). rewrite Eb. lia. }
  destruct CR4 as (CR4k & CR4b & CAPr).
  assert (LIT4 : PML.lits_ok M4) by (apply (TKX.lits_ok_x _ M2 M4 AG4); [lit_cov | exact LIT2]).
  assert (R4sp : getr R4 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP4 2%bv CS2); exact R3sp).
  assert (KS4 : TK.keepsR HSX.KS8 R R4) by (apply (TK.keepsR_trans _ R R3 R4 KS3'); apply KSP; exact RP4).
  apply (HSX.s_r_iss FPM fx4 R4 M4 model4 K sp Hhalt4 Hlazy4 Hfp4 R4sp SPOK);
    [intros i Hi; apply (proj2 FR4); lia | intros i Hi; apply (proj2 FR4); lia |].
  intros fx5 R5 M5 Hfp5 R5sp R5ra R5a0 R5a1 R5a2 KS5 Z5a Z5b Z5c SK5 AG5 GR5.
  assert (AG5o : TK.samem (L5.outside [(sp - 336, 24); (sp - 1344, 8)]) M4 M5).
  { apply (TK.samem_weaken _ _ _ _ AG5). intros a Ho. split; intros Hin.
    - apply (Ho (sp - 336, 24)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
    - apply (Ho (sp - 1344, 8)); [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (HF5 : forall w, In w [(sp - 336, 24); (sp - 1344, 8)] -> sp - SS <= fst w /\ fst w + snd w <= sp - 40 /\ 0 <= snd w)
    by (intros w [<-|[<-|[]]]; cbn [fst snd]; lia).
  assert (HB5 : forall b, In b (PML.srep_blocks reps) -> In b (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB))
    by (intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb).
  destruct (step_out_g [(sp - 336, 24); (sp - 1344, 8)] reps M4 M5 _ cr4 model4 HH4 AG5o GR5 HF5 HB5 PE4 FR4)
    as (PE5 & FR5 & HH5 & SC5 & WSI5 & LC5).
  assert (ISRC5 : PML.isrc_at M5 (sp - 312) rep (PML.srep_data (sp - 312 + 80) rep) 0).
  { apply (TK2.isrc_at_x _ M4 M5 AG5o); [lia | | | exact ISRC4].
    - intros i Hi w [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia.
    - apply (TK2.str_cov_out L LAY); [lia | | exact WSI5 |].
      + intros i Hi w [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia.
      + intros b Hb. apply BOK4. apply in_or_app. left. exact Hb. }
  assert (MID5 : PMS.statics_mid M5) by (apply (TK2.statics_mid_x _ M4 M5 AG5o SC5); exact MID4).
  assert (LIT5 : PML.lits_ok M5) by (apply (TKX.lits_ok_x _ M4 M5 AG5o LC5); exact LIT4).
  assert (KS5' : TK.keepsR HSX.KS8 R R5) by (exact (TK.keepsR_trans _ R R4 R5 KS4 KS5)).
  assert (TP5 : getr R5 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS5' 4%bv ltac:(kin)); exact Ptp).
  assert (SINK5 : PMES.sink_at M5 (sp - 336) (PML.SShort [])).
  { apply TKX.sink0; [lia | lia | exact Z5a | intros i Hi; apply (proj2 FR5); lia]. }
  assert (ECv : PMES.ENC_CTOR_SCR = 8864) by (vm_compute; reflexivity).
  assert (STK5 : L5C.stk (hl_sptop L) M5 (sp - 1376) PMES.ENC_CTOR_SCR).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M5); try eassumption; try lia. }
  eapply (ENC_CTOR (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr4 (sp - 1376) _ (sp - 744) (sp - 336) (sp - 1344)
            fx5 R5 M5 model4 K HH5 MOK4 HK0 Hfp5).
  { split; [apply HNXT.mk_entry; [exact R5ra | split; [lia | reflexivity] | exact R5sp | exact TP5 | exact STK5] |].
    split; [exact R5a0 |]. split; [exact R5a1 |]. split; [exact SK5 |].
    split; [intros i Hi; apply (proj2 FR5); lia |].
    split; [exact SINK5 |].
    split; [unfold PMES.ENC_SIZE; intros i Hi; apply (proj2 FR5); lia |].
    split; [unfold PMES.objs_enc, PMES.ENC_SIZE; split; [HNXT.oos Hsp16 | split; [HNXT.oos Hsp16 | unfold PML.apart; lia]] |].
    split; [HNXT.oos Hsp16 |].
    split; [unfold PML.apart, PMES.ENC_SIZE; lia |].
    split; [unfold PML.apart; lia |].
    destruct MID5 as (RO5 & LQ5 & _). split; [exact RO5 | exact LQ5]. }
  intros fx6 R6 M6 model6 LB6 cr6 LBk6 W6 Hfp6 POST6 RP6 HP6 BV6 HH6.
  (* after the encoder ctor *)
  destruct POST6 as (EI6 & OI6 & SK6 & ELB6 & ECR6 & ELBk6 & EW6). subst LB6 cr6 LBk6 W6.
  assert (MOK6 : PML.model_ok model6) by (mok BV6 Hhalt4 Hlazy4 Hmat4).
  pose proof MOK6 as (Hhalt6 & Hlazy6 & Hmat6).
  assert (WOK6 : HNXT.w_ok sp [(sp - 744, PMES.ENC_SIZE); (sp - 1344, 8)]) by (unfold HNXT.w_ok, PMES.ENC_SIZE; wok).
  assert (INC6 : incl (PML.srep_blocks reps ++ LB) (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB))
    by (intros b Hb; apply in_or_app; right; exact Hb).
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M5 M6 _ _ _ HP6 BOK4 INC6
              ltac:(lia) ltac:(lia) WOK6 PE5 FR5) as (PE6 & FR6 & AG6 & WSI6).
  assert (CVK6 : forall a, sp - 1376 <= a < sp -> ~ (sp - 744 <= a < sp - 336) -> ~ (sp - 1344 <= a < sp - 1336) ->
             TK2.keepH L (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) [(sp - 744, PMES.ENC_SIZE); (sp - 1344, 8)] (sp - 1376) PMES.ENC_CTOR_SCR a).
  { intros a Ha H1 H2. split; [| left; lia]. intros w [<-|[<-|[]]] Hin; unfold L5.in_rng, PMES.ENC_SIZE in Hin; cbn [fst snd] in Hin; lia. }
  assert (ISRC6 : PML.isrc_at M6 (sp - 312) rep (PML.srep_data (sp - 312 + 80) rep) 0).
  { apply (TK2.isrc_at_x _ M5 M6 AG6); [lia | intros i Hi; apply CVK6; lia | | exact ISRC5].
    first [apply (TK2.str_cov_keepH L LAY) | apply (TK2.str_cov_keepH L)]; [lia | intros i Hi; apply CVK6; lia | exact WSI6 |].
    intros b Hb. split; [apply in_or_app; left; exact Hb | apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (MID6 : PMS.statics_mid M6) by (apply (TK2.statics_mid_x _ M5 M6 AG6); [st_cov | exact MID5]).
  assert (LIT6 : PML.lits_ok M6) by (apply (TKX.lits_ok_x _ M5 M6 AG6); [lit_cov | exact LIT5]).
  assert (R6sp : getr R6 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP6 2%bv CS2); exact R5sp).
  assert (KS6 : TK.keepsR HSX.KS8 R R6) by (apply (TK.keepsR_trans _ R R5 R6 KS5'); apply KSP; exact RP6).
  apply (HSX.s_r_encctor FPM fx6 R6 M6 model6 K sp Hhalt6 Hlazy6 Hfp6 R6sp SPOK).
  intros fx7 R7 Hfp7 R7sp R7ra R7a0 R7a1 R7a2 R7a3 KS7.
  assert (KS7' : TK.keepsR HSX.KS8 R R7) by (exact (TK.keepsR_trans _ R R6 R7 KS6 KS7)).
  assert (TP7 : getr R7 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS7' 4%bv ltac:(kin)); exact Ptp).
  assert (RCv : 304 + PMS.CTOR_SCR = 9568) by (vm_compute; reflexivity).
  assert (STK7 : L5C.stk (hl_sptop L) M6 (sp - 1376) (304 + PMS.CTOR_SCR)).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M6); try eassumption; try lia. }
  eapply (RCTOR (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr4 (sp - 1344) (sp - 312) (sp - 744) (sp - 1376) _
            fx7 R7 M6 model6 K HH6 MOK6 HK0 Hfp7).
  { split; [apply HNXT.mk_entry; [exact R7ra | split; [lia | reflexivity] | exact R7sp | exact TP7 | exact STK7] |].
    split; [exact R7a0 |]. split; [exact R7a1 |]. split; [exact R7a2 |].
    split; [exists rep, (PML.srep_data (sp - 312 + 80) rep); exact ISRC6 |].
    split; [destruct EI6 as (EO6 & _); exact (proj1 EO6) |].
    destruct MID6 as (RO6 & LQ6 & GL6 & _).
    split; [exact RO6 |]. split; [exact GL6 |].
    split; [HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |].
    split; [unfold PML.apart; lia |]. split; [unfold PML.apart; lia |].
    split; [intros i Hi; apply (proj2 FR6); lia |].
    split; lia. }
  intros fx8 R8 M8 model8 LB8 cr8 LBk8 W8 Hfp8 POST8 RP8 HP8 BV8 HH8.
  (* after the reader ctor *)
  destruct POST8 as (ch & sb & bptr & RD8 & ELB8 & ELBk8 & EW8 & ECR8). subst LB8 LBk8 W8.
  assert (MOK8 : PML.model_ok model8) by (mok BV8 Hhalt6 Hlazy6 Hmat6).
  pose proof MOK8 as (Hhalt8 & Hlazy8 & Hmat8).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH8) as BOK8.
  assert (WOK8 : HNXT.w_ok sp [(sp - 1344, 592)]) by (unfold HNXT.w_ok; wok).
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M6 M8 _ _ _ HP8 BOK4 INC6
              ltac:(lia) ltac:(lia) WOK8 PE6 FR6) as (PE8 & FR8 & AG8 & WSI8).
  assert (ISRC8 : PML.isrc_at M8 (sp - 312) rep (PML.srep_data (sp - 312 + 80) rep) 0).
  { apply (TK2.isrc_at_x _ M6 M8 AG8); [lia | cov_stack | | exact ISRC6].
    first [apply (TK2.str_cov_keepH L LAY) | apply (TK2.str_cov_keepH L)]; [lia | cov_stack | exact WSI8 |].
    intros b Hb. split; [apply in_or_app; left; exact Hb | apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (EI8 : PMES.enc_inv M8 (sp - 744) (sp - 336) PMES.g0).
  { apply (TKX.enc_inv_x _ M6 M8 _ _ _ AG8); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | cov_stack | cov_stack | | exact EI6].
    intros b Hb. rewrite TKX.g_lbv_g0 in Hb. destruct Hb. }
  assert (MID8 : PMS.statics_mid M8) by (apply (TK2.statics_mid_x _ M6 M8 AG8); [st_cov | exact MID6]).
  assert (LIT8 : PML.lits_ok M8) by (apply (TKX.lits_ok_x _ M6 M8 AG8); [lit_cov | exact LIT6]).
  assert (OI8 : PMES.opts_idle M8 (sp - 744)) by (apply (TKX.opts_idle_x _ M6 M8 _ AG8); [lia | unfold PMES.ENC_SIZE; lia | cov_stack | exact OI6]).
  assert (R8sp : getr R8 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP8 2%bv CS2); exact R7sp).
  assert (KS8' : TK.keepsR HSX.KS8 R R8) by (apply (TK.keepsR_trans _ R R7 R8 KS7'); apply KSP; exact RP8).
  apply (HSX.s_r_rctor FPM fx8 R8 M8 model8 K sp Hhalt8 Hlazy8 Hfp8 R8sp SPOK); [intros i Hi; apply (proj2 FR8); lia |].
  intros fx9 R9 M9 Hfp9 R9sp R9ra KS9 U9 AG9 GR9.
  assert (AG9o : TK.samem (L5.outside [(sp - 1360, 4)]) M8 M9).
  { apply (TK.samem_weaken _ _ _ _ AG9). intros a Ho Hin. apply (Ho (sp - 1360, 4)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  destruct (step_out_g [(sp - 1360, 4)] reps M8 M9 _ _ model8 HH8 AG9o GR9 ltac:(intros w [<-|[]]; cbn [fst snd]; lia) ltac:(inb) PE8 FR8)
    as (PE9 & FR9 & HH9 & SC9 & WSI9 & LC9).
  assert (ISRC9 : PML.isrc_at M9 (sp - 312) rep (PML.srep_data (sp - 312 + 80) rep) 0).
  { apply (TK2.isrc_at_x _ M8 M9 AG9o); [lia | ocov | | exact ISRC8].
    apply (TK2.str_cov_out L LAY); [lia | ocov | exact WSI9 | intros b Hb; apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (EI9 : PMES.enc_inv M9 (sp - 744) (sp - 336) PMES.g0).
  { apply (TKX.enc_inv_x _ M8 M9 _ _ _ AG9o); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | ocov | ocov | | exact EI8].
    intros b Hb. rewrite TKX.g_lbv_g0 in Hb. destruct Hb. }
  assert (MID9 : PMS.statics_mid M9) by (apply (TK2.statics_mid_x _ M8 M9 AG9o SC9); exact MID8).
  assert (LIT9 : PML.lits_ok M9) by (apply (TKX.lits_ok_x _ M8 M9 AG9o LC9); exact LIT8).
  assert (OI9 : PMES.opts_idle M9 (sp - 744)) by (apply (TKX.opts_idle_x _ M8 M9 _ AG9o); [lia | unfold PMES.ENC_SIZE; lia | ocov | exact OI8]).
  assert (RD9 : PML.reader_at M9 (sp - 1344) (sp - 312) (sp - 744) ch true (PMS.ps_init sb bptr)).
  { apply (TK2.reader_at_x _ M8 M9 AG9o); [lia | ocov | | reflexivity | exact RD8].
    first [apply (TK2.ps_cov_out L LAY) | apply (TK2.ps_cov_out L)]; [lia | exact WSI9 | intros b Hb; apply BOK8; apply in_or_app; left; exact Hb]. }
  (* system_category *)
  assert (KS9' : TK.keepsR HSX.KS8 R R9) by (exact (TK.keepsR_trans _ R R8 R9 KS8' KS9)).
  assert (TP9 : getr R9 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS9' 4%bv ltac:(kin)); exact Ptp).
  assert (STK9 : L5C.stk (hl_sptop L) M9 (sp - 1376) 64).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M9); try eassumption; try lia. }
  eapply (SYSCAT (sp - 1376) _ fx9 R9 M9 model8 K Hhalt8 Hlazy8 HK0 Hfp9).
  { split; [apply HNXT.mk_entry; [exact R9ra | split; [lia | reflexivity] | exact R9sp | exact TP9 | exact STK9] |].
    destruct MID9 as (RO9 & LQ9 & GL9 & GD9 & _). split; [exact RO9 | exact GD9]. }
  intros fx10 R10 M10 Hfp10 (A10 & U10) RP10 FB10 GR10.
  pose proof (TK2.frame_but_samem _ M9 M10 FB10) as AG10.
  match type of AG10 with TK.samem (L5.outside ?F) _ _ => set (F10 := F) in AG10 end.
  assert (WSI10 : TK2.w_si L F10).
  { unfold F10. intros w Hw. repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; first [left; lia | right; lia] |]). destruct Hw. }
  assert (OUT10 : forall a, (a < sp - 1440 \/ sp - 1376 <= a) -> 2 ^ 39 <= a -> L5.outside F10 a).
  { intros a H1 H2. unfold F10. ow. }
  assert (PE10 : HNXT.pers sp ra R reps M10).
  { apply (HNXT.pers_x Lay sp ra pyld R SPOK _ M9 M10 reps AG10); [intros i Hi; apply OUT10; lia | | exact PE9].
    apply (TK2.str_cov_out L LAY); [lia | intros i Hi; apply OUT10; lia | exact WSI10 | intros b Hb; apply BOK2; apply in_or_app; left; exact Hb]. }
  assert (FR10 : TK2.FR L LB sp SS in_footx M M10).
  { eapply TK2.FR_grows; try eassumption; try lia.
    intros a Ha. destruct (HNXT.not_outside F10 a Ha) as (w & Hw & Hin). unfold F10 in Hw.
    destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [left; lia | right; foot_in2]. }
  match type of HH9 with hi_heap HI ?LBx ?c _ ?vm => assert (HH10 : hi_heap HI LBx c M10 vm) end.
  { eapply TK2.heap_pure_write; try eassumption; try lia.
    intros a Ha Hn. destruct (HNXT.not_outside F10 a Hn) as (w & Hw & Hin). unfold F10 in Hw.
    destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [left; lia | right; lia]. }
  assert (LIT10 : PML.lits_ok M10).
  { apply (TKX.lits_ok_x _ M9 M10 AG10); [intros a Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; unfold F10; ow | exact LIT9]. }
  assert (OI10 : PMES.opts_idle M10 (sp - 744)).
  { apply (TKX.opts_idle_x _ M9 M10 _ AG10); [lia | unfold PMES.ENC_SIZE; lia | intros i Hi; apply OUT10; lia | exact OI9]. }
  assert (LSX : exists g1, g1 <> PML.LS0 /\ PML.ls_ok g1 M10).
  { apply (TK2.mid_to_ls _ M9 M10 AG10); [ | | exact MID9 | exact U10].
    - intros a Hf Hn. pose proof (foot11_small a Hf) as Ha. unfold F10. ow.
    - intros a Ha. unfold PML.IMG_RO_HI in Ha. unfold F10. ow. }
  destruct LSX as (g1 & G1NE & LS10).
  assert (ISRC10 : PML.isrc_at M10 (sp - 312) rep (PML.srep_data (sp - 312 + 80) rep) 0).
  { apply (TK2.isrc_at_x _ M9 M10 AG10); [lia | intros i Hi; apply OUT10; lia | | exact ISRC9].
    apply (TK2.str_cov_out L LAY); [lia | intros i Hi; apply OUT10; lia | exact WSI10 | intros b Hb; apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (EI10 : PMES.enc_inv M10 (sp - 744) (sp - 336) PMES.g0).
  { apply (TKX.enc_inv_x _ M9 M10 _ _ _ AG10); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | | | | exact EI9].
    - unfold PMES.ENC_SIZE. intros i Hi; apply OUT10; lia.
    - intros i Hi; apply OUT10; lia.
    - intros b Hb. rewrite TKX.g_lbv_g0 in Hb. destruct Hb. }
  assert (RD10 : PML.reader_at M10 (sp - 1344) (sp - 312) (sp - 744) ch true (PMS.ps_init sb bptr)).
  { apply (TK2.reader_at_x _ M9 M10 AG10); [lia | intros i Hi; apply OUT10; lia | | reflexivity | exact RD9].
    first [apply (TK2.ps_cov_out L LAY) | apply (TK2.ps_cov_out L)]; [lia | exact WSI10 | intros b Hb; apply BOK8; apply in_or_app; left; exact Hb]. }
  assert (U9' : L5.u32_at RSEGS M10 (sp - 1360) 0).
  { apply (TK.u32_samem _ M9 M10 _ _ AG10); [lia | intros i Hi; apply OUT10; lia | exact U9]. }
  assert (R10sp : getr R10 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP10 2%bv CS2); exact R9sp).
  assert (KS10 : TK.keepsR HSX.KS8 R R10) by (apply (TK.keepsR_trans _ R R9 R10 KS9'); apply KSP; exact RP10).
  apply (HSX.s_r_syscat FPM fx10 R10 M10 model8 K sp PML.OBJ_SYSTEM_CATEGORY Hhalt8 Hlazy8 Hfp10 R10sp SPOK A10);
    [unfold PML.OBJ_SYSTEM_CATEGORY; lia | intros i Hi; apply (proj2 FR10); lia |].
  intros fx11 R11 M11 Hfp11 R11sp R11ra R11a0 R11a1 KS11 U11 AG11 GR11.
  assert (AG11o : TK.samem (L5.outside [(sp - 1352, 8)]) M10 M11).
  { apply (TK.samem_weaken _ _ _ _ AG11). intros a Ho Hin. apply (Ho (sp - 1352, 8)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  destruct (step_out_g [(sp - 1352, 8)] reps M10 M11 _ _ model8 HH10 AG11o GR11 ltac:(intros w [<-|[]]; cbn [fst snd]; lia) ltac:(inb) PE10 FR10)
    as (PE11 & FR11 & HH11 & SC11 & WSI11 & LC11).
  (* transfers to the read call state *)
  assert (ISRC11 : PML.isrc_at M11 (sp - 312) rep (PML.srep_data (sp - 312 + 80) rep) 0).
  { apply (TK2.isrc_at_x _ M10 M11 AG11o); [lia | ocov | | exact ISRC10].
    apply (TK2.str_cov_out L LAY); [lia | ocov | exact WSI11 | intros b Hb; apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (EI11 : PMES.enc_inv M11 (sp - 744) (sp - 336) PMES.g0).
  { apply (TKX.enc_inv_x _ M10 M11 _ _ _ AG11o); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | ocov | ocov | | exact EI10].
    intros b Hb. rewrite TKX.g_lbv_g0 in Hb. destruct Hb. }
  assert (RD11 : PML.reader_at M11 (sp - 1344) (sp - 312) (sp - 744) ch true (PMS.ps_init sb bptr)).
  { apply (TK2.reader_at_x _ M10 M11 AG11o); [lia | ocov | | reflexivity | exact RD10].
    first [apply (TK2.ps_cov_out L LAY) | apply (TK2.ps_cov_out L)]; [lia | exact WSI11 | intros b Hb; apply BOK8; apply in_or_app; left; exact Hb]. }
  assert (LS11 : PML.ls_ok g1 M11) by (apply (TK2.ls_ok_x _ M10 M11 AG11o SC11); exact LS10).
  assert (LIT11 : PML.lits_ok M11) by (apply (TKX.lits_ok_x _ M10 M11 AG11o LC11); exact LIT10).
  assert (OI11 : PMES.opts_idle M11 (sp - 744)) by (apply (TKX.opts_idle_x _ M10 M11 _ AG11o); [lia | unfold PMES.ENC_SIZE; lia | ocov | exact OI10]).
  assert (U11e : L5.u32_at RSEGS M11 (sp - 1360) 0).
  { apply (TK.u32_samem _ M10 M11 _ _ AG11o); [lia | ocov | exact U9']. }
  assert (KS11' : TK.keepsR HSX.KS8 R R11) by (exact (TK.keepsR_trans _ R R10 R11 KS10 KS11)).
  assert (TP11 : getr R11 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS11' 4%bv ltac:(kin)); exact Ptp).
  assert (RX0 : 0 <= PMX.READX_SCR STRTOD_SCR WD_SCR) by (unfold PMX.READX_SCR, PMX.READNEXTX_SCR, PMX.PSOMEX_SCR, PMX.PFX_SCR; lia).
  assert (STK11 : L5C.stk (hl_sptop L) M11 (sp - 1376) (PMX.READX_SCR STRTOD_SCR WD_SCR)).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M11); try eassumption; try lia. }
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH11) as (_ & ND11 & _).
  assert (KL0 : PML.kleft (PMS.ps_init sb bptr) = 22) by (vm_compute; reflexivity).
  assert (BL0 : PML.bleft (PMS.ps_init sb bptr) = 2 ^ 28 + 1452) by (vm_compute; reflexivity).
  match type of HH11 with hi_heap HI (PML.ps_blocks _ ++ ?LBo) ?c ?m ?vm =>
    assert (HH11' : hi_heap HI (PML.ps_blocks (PMS.ps_init sb bptr) ++ LBo ++ PMES.g_lbv PMES.g0) c m vm)
      by (rewrite TKX.g_lbv_g0, app_nil_r; exact HH11);
    set (LBo0 := LBo) in *
  end.
  eapply (READXW LBo0 cr8 (sp - 1376) _ (sp - 1344) (sp - 312) (sp - 744) (sp - 1360) (sp - 336) ch
            (PML.srep_data (sp - 312 + 80) rep) sb bptr
            (fst cr8 - PMES.kenc L PMES.g0 - 22 * hl_k_per_malloc L)
            (snd cr8 - PMES.benc L PMES.g0 - (2 ^ 28 + 1452) - 22 * hl_b_overhead L)
            rep g1 PMES.g0 fx11 R11 M11 model8 K HH11' MOK8 HK0 Hfp11).
  { split; [apply HNXT.mk_entry; [exact R11ra | split; [lia | reflexivity] | exact R11sp | exact TP11 | exact STK11] |].
    split; [exact R11a0 |]. split; [exact R11a1 |].
    split.
    { split; [exact RD11 |]. split; [apply wf_ps_init |]. split; [exact ISRC11 |].
      split; [destruct EI11 as (EO11 & _); exact (proj1 EO11) |].
      split; [split; [exact U11e | split; [intros i Hi; apply (proj2 FR11); lia | left; reflexivity]] |].
      split; [unfold LBo0; left; reflexivity |].
      split; [unfold LBo0; inb |].
      split; [HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |].
      unfold PML.apart; lia. }
    split; [reflexivity |].
    split; [intros b Hb; exact (HNXT.nodup_mid _ _ _ _ ND11 b Hb) |].
    split; [rewrite LENr, LEN2, Htxt; lia |].
    split; [rewrite LENr, LEN2; exact (PMXW.zs_of_bytes_range pyld) |].
    split; [exact LS11 |]. split; [exact G1NE |].
    split; [exact EI11 |]. split; [exact LIT11 |].
    split; [split; [reflexivity | unfold PMX.key_inv; intros _ H; exfalso; vm_compute in H;
                                  destruct H as [H|(x & Hx & H)]; [lia | destruct Hx as [<-|[]]; lia]] |].
    pose proof (f_equal fst ECR8) as CR8k. pose proof (f_equal snd ECR8) as CR8b. unfold debit in CR8k, CR8b. cbn [fst snd] in CR8k, CR8b.
    unfold PML.pcredit_x, PML.pcredit. rewrite KL0, BL0. cbn [PML.ps_bcap PMS.ps_init].
    split; [lia |]. split; [lia |].
    split; [repeat split; cbn [fst snd]; lia |].
    split; [unfold PMES.ENC_SIZE; HNXT.oos Hsp16 |]. split; [HNXT.oos Hsp16 |].
    split; [unfold PML.apart, PMES.ENC_SIZE; lia |]. split; [unfold PML.apart, PMES.ENC_SIZE; lia |].
    split; [unfold PML.apart; lia |]. split; [unfold PML.apart, PMES.ENC_SIZE; lia |].
    split; [unfold PML.apart; lia |]. split; [unfold PML.apart, PMES.ENC_SIZE; lia |].
    split; [unfold PML.apart; lia |].
    rewrite LENr, LEN2. apply ROOM0; [rewrite Htxt; lia | exact PIND]. }
  intros fx12 R12 M12 model12 LB12 cr12 LBk12 W12 Hfp12 POST12 RP12 HP12 BV12 HH12.
  (* after the read *)
  destruct POST12 as (ps1 & code & gp1 & rdst1 & g2 & eg1 & SRC12 & PAR12 & ISRC12 & EC12 & LS12 & G2c & EI12 & LIT12 & ELB12 & ELBk12 & PCR12 & WF12 & EW12 & RR12).
  subst LB12 LBk12 W12.
  assert (MOK12 : PML.model_ok model12) by (mok BV12 Hhalt8 Hlazy8 Hmat8).
  pose proof MOK12 as (Hhalt12 & Hlazy12 & Hmat12).
  assert (ELBk : lb_remove ch LBo0 = PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)
    by (unfold LBo0; cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
  rewrite ELBk in HP12.
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH12) as BOK12.
  match type of HP12 with L5C.hpres _ _ _ _ ?W _ _ => assert (WOK12 : HNXT.w_ok sp W) by (unfold HNXT.w_ok; wok) end.
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M11 M12 _ _ _ HP12 BOK4 INC6
              ltac:(lia) ltac:(lia) WOK12 PE11 FR11) as (PE12 & FR12 & AG12 & WSI12).
  assert (R12sp : getr R12 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP12 2%bv CS2); exact R11sp).
  assert (KS12 : TK.keepsR HSX.KS8 R R12) by (apply (TK.keepsR_trans _ R R11 R12 KS11'); apply KSP; exact RP12).
  apply (HSX.s_r_read FPM fx12 R12 M12 model12 K sp Hhalt12 Hlazy12 Hfp12 R12sp SPOK).
  intros fx13 R13 Hfp13 R13sp R13ra R13a0 KS13.
  assert (KS13' : TK.keepsR HSX.KS8 R R13) by (exact (TK.keepsR_trans _ R R12 R13 KS12 KS13)).
  assert (TP13 : getr R13 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS13' 4%bv ltac:(kin)); exact Ptp).
  assert (ODv : 64 + PMS.OPDEL_SCR = 8288) by (vm_compute; reflexivity).
  assert (STK13 : L5C.stk (hl_sptop L) M12 (sp - 1376) (64 + PMS.OPDEL_SCR)).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M12); try eassumption; try lia. }
  eapply (PDTOR (LBo0 ++ PMES.g_lbv eg1) cr12 (sp - 1376) _ (sp - 1024) ps1 fx13 R13 M12 model12 K HH12 MOK12 HK0 Hfp13).
  { split; [apply HNXT.mk_entry; [exact R13ra | split; [lia | reflexivity] | exact R13sp | exact TP13 | exact STK13] |].
    split; [exact R13a0 |].
    split; [replace (sp - 1024) with (sp - 1344 + 320) by lia; exact PAR12 |].
    split; [exact (proj1 LS12) |].
    split; [HNXT.oos Hsp16 |].
    destruct WF12 as (_ & _ & _ & SCAP & _). cbn [In] in SCAP. lia. }
  intros fx14 R14 M14 model14 LB14 cr14 LBk14 W14 Hfp14 POST14 RP14 HP14 BV14 HH14.
  (* after the parser dtor *)
  assert (OI12 : PMES.opts_idle M12 (sp - 744)) by (apply (TKX.opts_idle_x _ M11 M12 _ AG12); [lia | unfold PMES.ENC_SIZE; lia | cov_stack | exact OI11]).
  destruct POST14 as (ELB14 & ECR14 & ELBk14 & EW14). subst LB14 cr14 LBk14 W14.
  assert (MOK14 : PML.model_ok model14) by (mok BV14 Hhalt12 Hlazy12 Hmat12).
  pose proof MOK14 as (Hhalt14 & Hlazy14 & Hmat14).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH14) as BOK14.
  assert (INC14 : incl (PML.srep_blocks reps ++ LB) (LBo0 ++ PMES.g_lbv eg1)) by (unfold LBo0; inb).
  assert (WOK14 : HNXT.w_ok sp [(sp - 1024, 272)]) by (unfold HNXT.w_ok; wok).
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M12 M14 _ _ _ HP14 BOK14 INC14
              ltac:(lia) ltac:(lia) WOK14 PE12 FR12) as (PE14 & FR14 & AG14 & WSI14).
  assert (SRC14 : PML.source_at M14 (sp - 1344) ch) by (apply (TK2.source_at_x _ M12 M14 AG14); [lia | cov_stack | exact SRC12]).
  assert (ISRC14 : PML.isrc_at M14 (sp - 312) rep gp1 rdst1).
  { apply (TK2.isrc_at_x _ M12 M14 AG14); [lia | cov_stack | | exact ISRC12].
    first [apply (TK2.str_cov_keepH L LAY) | apply (TK2.str_cov_keepH L)]; [lia | cov_stack | exact WSI14 |].
    intros b Hb. split; [unfold LBo0; inb0 Hb | apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (LS14 : PML.ls_ok g2 M14) by (apply (TK2.ls_ok_x _ M12 M14 AG14); [st_cov | exact LS12]).
  assert (LIT14 : PML.lits_ok M14) by (apply (TKX.lits_ok_x _ M12 M14 AG14); [lit_cov | exact LIT12]).
  assert (OI14 : PMES.opts_idle M14 (sp - 744)) by (apply (TKX.opts_idle_x _ M12 M14 _ AG14); [lia | unfold PMES.ENC_SIZE; lia | cov_stack | exact OI12]).
  assert (EI14 : PMES.enc_inv M14 (sp - 744) (sp - 336) eg1).
  { apply (TKX.enc_inv_x _ M12 M14 _ _ _ AG14); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | cov_stack | cov_stack | | exact EI12].
    intros b Hb. assert (Hb' : In b (LBo0 ++ PMES.g_lbv eg1)) by (apply in_or_app; right; exact Hb).
    pose proof (BOK14 b Hb') as Bb. pose proof Bb as (B0 & B1 & B2 & B3 & B4).
    split; [lia |]. split; [lia |]. destruct b as (p & c). cbn [fst snd] in *.
    first [apply (TK2.cov_block L LAY) | apply (TK2.cov_block L)]; [exact WSI14 | exact Hb' | exact Bb]. }
  assert (R14sp : getr R14 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP14 2%bv CS2); exact R13sp).
  assert (KS14 : TK.keepsR HSX.KS8 R R14) by (apply (TK.keepsR_trans _ R R13 R14 KS13'); apply KSP; exact RP14).
  apply (HSX.s_r_pdtor FPM fx14 R14 M14 model14 K sp Hhalt14 Hlazy14 Hfp14 R14sp SPOK).
  intros fx15 R15 Hfp15 R15sp R15ra R15a0 KS15.
  assert (KS15' : TK.keepsR HSX.KS8 R R15) by (exact (TK.keepsR_trans _ R R14 R15 KS14 KS15)).
  assert (TP15 : getr R15 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS15' 4%bv ltac:(kin)); exact Ptp).
  assert (SDv : 96 + PMS.OPDEL_SCR = 8320) by (vm_compute; reflexivity).
  assert (STK15 : L5C.stk (hl_sptop L) M14 (sp - 1376) (96 + PMS.OPDEL_SCR)).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M14); try eassumption; try lia. }
  eapply (SDTOR (LBo0 ++ PMES.g_lbv eg1) cr12 (sp - 1344) ch (sp - 1376) _ fx15 R15 M14 model14 K HH14 MOK14 HK0 Hfp15).
  { split; [apply HNXT.mk_entry; [exact R15ra | split; [lia | reflexivity] | exact R15sp | exact TP15 | exact STK15] |].
    split; [exact R15a0 |]. split; [exact SRC14 |].
    split; [unfold LBo0; apply in_or_app; left; left; reflexivity |].
    split; [exact (proj1 LS14) |].
    HNXT.oos Hsp16. }
  intros fx16 R16 M16 model16 LB16 cr16 LBk16 W16 Hfp16 POST16 RP16 HP16 BV16 HH16.
  (* after the source dtor *)
  destruct POST16 as (ELB16 & ECR16 & ELBk16 & EW16). subst LB16 cr16 LBk16 W16.
  assert (ERM : lb_remove ch (LBo0 ++ PMES.g_lbv eg1) = (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ++ PMES.g_lbv eg1)
    by (unfold LBo0; cbn [lb_remove app fst]; rewrite Z.eqb_refl; reflexivity).
  rewrite ERM in HP16, HH16.
  assert (MOK16 : PML.model_ok model16) by (mok BV16 Hhalt14 Hlazy14 Hmat14).
  pose proof MOK16 as (Hhalt16 & Hlazy16 & Hmat16).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH16) as BOK16.
  assert (INC16 : incl (PML.srep_blocks reps ++ LB) ((PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ++ PMES.g_lbv eg1)) by inb.
  assert (WOK16 : HNXT.w_ok sp [(sp - 1344, 592)]) by (unfold HNXT.w_ok; wok).
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M14 M16 _ _ _ HP16 BOK16 INC16
              ltac:(lia) ltac:(lia) WOK16 PE14 FR14) as (PE16 & FR16 & AG16 & WSI16).
  assert (ISRC16 : PML.isrc_at M16 (sp - 312) rep gp1 rdst1).
  { apply (TK2.isrc_at_x _ M14 M16 AG16); [lia | cov_stack | | exact ISRC14].
    first [apply (TK2.str_cov_keepH L LAY) | apply (TK2.str_cov_keepH L)]; [lia | cov_stack | exact WSI16 |].
    intros b Hb. split; [inb0 Hb | apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (LS16 : PML.ls_ok g2 M16) by (apply (TK2.ls_ok_x _ M14 M16 AG16); [st_cov | exact LS14]).
  assert (LIT16 : PML.lits_ok M16) by (apply (TKX.lits_ok_x _ M14 M16 AG16); [lit_cov | exact LIT14]).
  assert (OI16 : PMES.opts_idle M16 (sp - 744)) by (apply (TKX.opts_idle_x _ M14 M16 _ AG16); [lia | unfold PMES.ENC_SIZE; lia | cov_stack | exact OI14]).
  assert (EI16 : PMES.enc_inv M16 (sp - 744) (sp - 336) eg1).
  { apply (TKX.enc_inv_x _ M14 M16 _ _ _ AG16); [lia | unfold PMES.ENC_SIZE; lia | lia | lia | cov_stack | cov_stack | | exact EI14].
    intros b Hb. assert (Hb' : In b ((PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ++ PMES.g_lbv eg1)) by (apply in_or_app; right; exact Hb).
    pose proof (BOK16 b Hb') as Bb. pose proof Bb as (B0 & B1 & B2 & B3 & B4).
    split; [lia |]. split; [lia |]. destruct b as (p & c). cbn [fst snd] in *.
    first [apply (TK2.cov_block L LAY) | apply (TK2.cov_block L)]; [exact WSI16 | exact Hb' | exact Bb]. }
  assert (R16sp : getr R16 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP16 2%bv CS2); exact R15sp).
  assert (KS16 : TK.keepsR HSX.KS8 R R16) by (apply (TK.keepsR_trans _ R R15 R16 KS15'); apply KSP; exact RP16).
  apply (HSX.s_r_sdtor FPM fx16 R16 M16 model16 K sp Hhalt16 Hlazy16 Hfp16 R16sp SPOK).
  intros fx17 R17 Hfp17 R17sp R17ra R17a0 KS17.
  assert (KS17' : TK.keepsR HSX.KS8 R R17) by (exact (TK.keepsR_trans _ R R16 R17 KS16 KS17)).
  assert (TP17 : getr R17 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS17' 4%bv ltac:(kin)); exact Ptp).
  assert (EDv : PMES.ENC_DTOR_SCR = 8288) by (vm_compute; reflexivity).
  assert (STK17 : L5C.stk (hl_sptop L) M16 (sp - 1376) PMES.ENC_DTOR_SCR).
  { eapply (HNXT.mk_stk L LB sp SS in_footx M M16); try eassumption; try lia. }
  eapply (ENC_DTOR (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) cr12 (sp - 1376) _ (sp - 744) (sp - 336) eg1
            fx17 R17 M16 model16 K HH16 MOK16 HK0 Hfp17).
  { split; [apply HNXT.mk_entry; [exact R17ra | split; [lia | reflexivity] | exact R17sp | exact TP17 | exact STK17] |].
    split; [exact R17a0 |]. split; [exact EI16 |]. split; [exact OI16 |].
    split; [unfold PMES.ENC_SIZE; intros i Hi; apply (proj2 FR16); lia |].
    split; [unfold PMES.objs_enc, PMES.ENC_SIZE; split; [HNXT.oos Hsp16 | split; [HNXT.oos Hsp16 | unfold PML.apart; lia]] |].
    exact (proj1 LS16). }
  intros fx18 R18 M18 model18 LB18 cr18 LBk18 W18 Hfp18 POST18 RP18 HP18 BV18 HH18.
  (* after the encoder dtor *)
  destruct POST18 as (SINK18 & ELB18 & ECR18 & ELBk18 & EW18). subst LB18 cr18 LBk18 W18.
  assert (MOK18 : PML.model_ok model18) by (mok BV18 Hhalt16 Hlazy16 Hmat16).
  pose proof MOK18 as (Hhalt18 & Hlazy18 & Hmat18).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH18) as BOK18.
  assert (INC18 : incl (PML.srep_blocks reps ++ LB) ((PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ++ PML.srep_blocks (PMES.g_rep eg1))) by inb.
  assert (WOK18 : HNXT.w_ok sp [(sp - 744, PMES.ENC_SIZE)]) by (unfold HNXT.w_ok, PMES.ENC_SIZE; wok).
  destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M16 M18 _ _ _ HP18 BOK18 INC18
              ltac:(lia) ltac:(lia) WOK18 PE16 FR16) as (PE18 & FR18 & AG18 & WSI18).
  assert (ISRC18 : PML.isrc_at M18 (sp - 312) rep gp1 rdst1).
  { apply (TK2.isrc_at_x _ M16 M18 AG18); [lia | cov_stack | | exact ISRC16].
    first [apply (TK2.str_cov_keepH L LAY) | apply (TK2.str_cov_keepH L)]; [lia | cov_stack | exact WSI18 |].
    intros b Hb. split; [inb0 Hb | apply BOK4; apply in_or_app; left; exact Hb]. }
  assert (LS18 : PML.ls_ok g2 M18) by (apply (TK2.ls_ok_x _ M16 M18 AG18); [st_cov | exact LS16]).
  assert (LIT18 : PML.lits_ok M18) by (apply (TKX.lits_ok_x _ M16 M18 AG18); [lit_cov | exact LIT16]).
  assert (G2NE : g2 <> PML.LS0) by (destruct G2c as [->|(-> & _)]; [exact G1NE | discriminate]).
  assert (BV18' : model_but_vm model model18).
  { exact (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _
             (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _ (L5C.model_but_vm_trans _ _ _ BV2 BV4) BV6) BV8) BV12) BV14) BV16) BV18). }
  assert (CRT : credit_le (credit_sub cr (ll_credit Lay n)) cr12).
  { rewrite (LC n). unfold LCU.pm_creditxU, credit_le, credit_sub; cbn [fst snd].
    pose proof (f_equal fst ECR8) as CR8k. pose proof (f_equal snd ECR8) as CR8b. unfold debit in CR8k, CR8b. cbn [fst snd] in CR8k, CR8b.
    destruct PCR12 as (K0 & B0 & PB & PK & PBB). cbn [fst snd] in PK, PBB.
    pose proof (Z.log2_nonneg (2 ^ 27 / PML.ps_bcap ps1)). pose proof (Z.log2_nonneg (1056 / PML.ps_scap ps1)).
    assert (KL1 : 0 <= PML.kleft ps1) by (unfold PML.kleft; lia).
    assert (BL1 : 0 <= PML.bleft ps1).
    { destruct WF12 as (_ & _ & _ & SCAP & _). cbn [In] in SCAP. unfold PML.bleft. lia. }
    assert (0 <= PML.kleft ps1 * hl_k_per_malloc L) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= PML.kleft ps1 * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= PMES.kenc L eg1) by (change (PMES.kenc L eg1) with (PMX.kenc L eg1); apply TKX.kenc_nonneg; lia).
    pose proof (EncKit_u5.EK.benc_nonneg L KPM0 BOV0 eg1).
    split; lia. }
  assert (R18sp : getr R18 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP18 2%bv CS2); exact R17sp).
  assert (KS18 : TK.keepsR HSX.KS8 R R18) by (apply (TK.keepsR_trans _ R R17 R18 KS17'); apply KSP; exact RP18).
  assert (OPDv : PMS.OPDEL_SCR = 8224) by (vm_compute; reflexivity).
  pose proof SINK18 as (STR18 & DEF18 & ROK18).
  destruct (PMES.g_rep eg1) as [s | cap p s] eqn:EREP.
  - (* short output string: no buffer to free *)
    cbn [PML.str_at] in STR18. pose proof STR18 as (SL18 & SB18 & _).
    cbn [PML.srep_blocks] in HH18. rewrite app_nil_r in HH18.
    apply (HSX.s_r_encdtor FPM fx18 R18 M18 model18 K sp (2 * Z.of_nat (length s)) Hhalt18 Hlazy18 Hfp18 R18sp SPOK SB18); [lia |].
    intros fx19 R19 Hfp19 R19sp B19 KS19.
    apply (HSX.s_b0_short FPM fx19 R19 M18 model18 K sp Hhalt18 Hlazy18 Hfp19 R19sp SPOK).
    { apply HNXT.reg_of_u. rewrite B19. apply HNXT.land1_even. }
    intros fx20 R20 Hfp20 R20sp KS20.
    assert (KS20' : TK.keepsR HSX.KS8 R R20) by (exact (TK.keepsR_trans _ R R19 R20 (TK.keepsR_trans _ R R18 R19 KS18 KS19) KS20)).
    eapply (HNXT.tail0 L HI HIok LAY FPM OPDELS LOCDTOR ISTRDTOR IOSBDTOR Lay LH LF HSS LB cr sp ra pyld R M model K Psp Ptp Plen Prok SPOK
              Hceil Hsptop Htop BOK0 HK0 CONT fx20 R20 M18 model18 cr12 g2 reps rep gp1 rdst1 Hfp20 R20sp);
      [intros r Hr; apply KS20'; apply HNXT.KS_in_KS8; exact Hr | exact PE18 | exact CAPs | exact CAPr | exact FR18 | exact BV18'
      | exact MOK18 | exact HH18 | exact LS18 | exact G2NE | exact LIT18 | exact CRT | exact ISRC18].
  - (* long output string: operator delete of its buffer, then the tail *)
    cbn [PML.str_at] in STR18. destruct STR18 as ((TB & W0 & WL & WP & BY & Z0) & CM8 & CLT).
    cbn [PML.srep_blocks] in HH18, BOK18.
    pose proof (BOK18 (p, cap) ltac:(apply in_or_app; right; left; reflexivity)) as BRp. cbn [fst snd] in BRp.
    pose proof BRp as (P0 & P1 & P2 & P3 & P4).
    apply (HSX.s_r_encdtor FPM fx18 R18 M18 model18 K sp ((cap + 1) mod 256) Hhalt18 Hlazy18 Hfp18 R18sp SPOK);
      [apply (TK2.u64_u8_low M18 (sp - 336) (cap + 1)); [lia | lia | exact W0] | pose proof (Z.mod_pos_bound (cap + 1) 256); lia |].
    intros fx19 R19 Hfp19 R19sp B19 KS19.
    apply (HSX.s_b0_long FPM fx19 R19 M18 model18 K sp (cap + 1) p Hhalt18 Hlazy18 Hfp19 R19sp SPOK);
      [apply HNXT.reg_of_u; rewrite B19; apply HNXT.land1_odd_low; exact TB | exact W0
      | replace (sp - 320) with (sp - 336 + 16) by lia; exact WP | lia | lia |].
    intros fx20 R20 Hfp20 R20sp R20ra R20a0 KS20.
    assert (KS20' : TK.keepsR HSX.KS8 R R20) by (exact (TK.keepsR_trans _ R R19 R20 (TK.keepsR_trans _ R R18 R19 KS18 KS19) KS20)).
    assert (TP20 : getr R20 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS20' 4%bv ltac:(kin)); exact Ptp).
    assert (STK20 : L5C.stk (hl_sptop L) M18 (sp - 1376) PMS.OPDEL_SCR).
    { eapply (HNXT.mk_stk L LB sp SS in_footx M M18); try eassumption; try lia. }
    eapply (OPDELS ((PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ++ [(p, cap)]) cr12 p cap (sp - 1376) _
              fx20 R20 M18 model18 K HH18 MOK18 HK0 Hfp20).
    { split; [apply HNXT.mk_entry; [exact R20ra | split; [lia | reflexivity] | exact R20sp | exact TP20 | exact STK20] |].
      split; [exact R20a0 | apply in_or_app; right; left; reflexivity]. }
    intros fx21 R21 M21 model21 LB21 cr21 LBk21 W21 Hfp21 (ELB21 & ECR21 & ELBk21 & EW21) RP21 HP21 BV21 HH21.
    pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH18) as (_ & ND18 & _).
    assert (ERM21 : lb_remove p ((PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) ++ [(p, cap)]) = PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB).
    { apply TKX.lb_remove_last. intros b Hb. exact (TKX.nodup_last _ _ ND18 b Hb). }
    subst LB21 cr21 LBk21 W21. rewrite ERM21 in HP21, HH21.
    assert (MOK21 : PML.model_ok model21) by (mok BV21 Hhalt18 Hlazy18 Hmat18).
    pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH21) as BOK21.
    assert (INC21 : incl (PML.srep_blocks reps ++ LB) (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB)) by inb.
    assert (WOK21 : HNXT.w_ok sp []) by (intros w []).
    destruct (HNXT.step_heap L LAY Lay HSS LB sp ra pyld R M SPOK Hceil Hsptop Htop BOK0 reps M18 M21 _ _ _ HP21 BOK21 INC21
                ltac:(lia) ltac:(lia) WOK21 PE18 FR18) as (PE21 & FR21 & AG21 & WSI21).
    assert (ISRC21 : PML.isrc_at M21 (sp - 312) rep gp1 rdst1).
    { apply (TK2.isrc_at_x _ M18 M21 AG21); [lia | cov_stack | | exact ISRC18].
      first [apply (TK2.str_cov_keepH L LAY) | apply (TK2.str_cov_keepH L)]; [lia | cov_stack | exact WSI21 |].
      intros b Hb. split; [inb0 Hb | apply BOK4; apply in_or_app; left; exact Hb]. }
    assert (LS21 : PML.ls_ok g2 M21) by (apply (TK2.ls_ok_x _ M18 M21 AG21); [st_cov | exact LS18]).
    assert (LIT21 : PML.lits_ok M21) by (apply (TKX.lits_ok_x _ M18 M21 AG21); [lit_cov | exact LIT18]).
    assert (R21sp : getr R21 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP21 2%bv CS2); exact R20sp).
    assert (KS21 : TK.keepsR HSX.KS8 R R21) by (apply (TK.keepsR_trans _ R R20 R21 KS20'); apply KSP; exact RP21).
    eapply (HNXT.tail0 L HI HIok LAY FPM OPDELS LOCDTOR ISTRDTOR IOSBDTOR Lay LH LF HSS LB cr sp ra pyld R M model K Psp Ptp Plen Prok SPOK
              Hceil Hsptop Htop BOK0 HK0 CONT fx21 R21 M21 model21 cr12 g2 reps rep gp1 rdst1 Hfp21 R21sp);
      [intros r Hr; apply KS21; apply HNXT.KS_in_KS8; exact Hr | exact PE21 | exact CAPs | exact CAPr | exact FR21
      | exact (L5C.model_but_vm_trans _ _ _ BV18' BV21) | exact MOK21 | exact HH21 | exact LS21 | exact G2NE | exact LIT21 | exact CRT | exact ISRC21].
Qed.
End Run.

Theorem walkU : LSU.harness_runU L HI STRTOD_SCR WD_SCR.
Proof.
  intros Lay LH LF LC HSS HSSR LB cr sp ra pyld R M model K Psp Ptp Plen Prok SPB Hceil Hsptop Htop BOK0 HK0 PIND CONT.
  apply run_okU; assumption.
Qed.
End H.

(* The harness run from the library specs of LSU.lib_fnspecsU and the encoder's output room for inputs with IND < 2^34. *)
Theorem walkU_fns {SCFG_P : ScfgP} (L : heap_layout) (HI : heap_iface) (SS WD : Z) :
  heap_iface_ok L SCFG HI -> PmLayout.pm0_layout L -> LSU.fp_inv -> LSU.lib_fnspecsU L HI SS WD ->
  (forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> PmRef.PMR.IND txt < 2 ^ 34 ->
     PmLibSpecsW_u5.PMW.wroomU PmEncSpecs_u5.PMES.g0 (PmRef_u5.PMR.K txt) (PmRef_u5.PMR.ALLOW txt)) ->
  LSU.harness_runU L HI SS WD.
Proof.
  intros HIok LAY FPM FNS ROOM0. destruct FNS.
  eapply walkU; eassumption.
Qed.
End HNXWU.
