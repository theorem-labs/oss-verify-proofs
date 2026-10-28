(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Znumtheory FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u
     PnSRvK_u PnSRvA_u PnSRvB_u PnSRvOH_u PnSRvOP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVO.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma tb0_long c : 0 <= c -> c mod 2 = 0 -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros Hc He. rewrite Z.testbit_true by lia. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite (Z.mod_mod_divide (c + 1) 256 2) by (exists 128; reflexivity). rewrite <- Zplus_mod_idemp_l, He. reflexivity.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 8).
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation rv_ctx := (PNSRVK.rv_ctx L).
Abbreviation rv_kont := (PNSRVK.rv_kont L HI).

Hypothesis MKE : PNRS.make_ec_spec L HI.
Hypothesis SRD : PNRS.src_read_spec L HI.
Hypothesis RSZ : PMS.str_resize_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned]).

(* [comment removed for export] *)
Lemma step3 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  PNM.b_bb s9 = PNM.b_bb s -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm -> PM.vs_size (PNM.b_tb s9) = 24 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37a7c M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 EC9 INV9 TP9 EBB LEU SZ9.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  pose proof PA9 as (_ & PD9 & _ & _ & _ & CM9 & _).
  pose proof BR9 as ((_ & _ & VIS9 & _ & BASE9 & _) & _). cbn [PNBK.be_M] in VIS9, BASE9.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS9. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS9.
  pose proof BASE9 as (IMG9 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG9.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (BRG9 & OWNB9 & _).
  pose proof (PNSRVK.tb_facts M9 fb s9 PA9) as TBF.
  (* [comment removed for export] *)
  destruct (PNM.b_tb s9) as [n9|c9 n9 p9] eqn:ETB; [destruct TBF as (Hn9 & _); cbn [PM.vs_size] in SZ9; lia|].
  cbn [PM.vs_size] in SZ9. subst n9.
  destruct TBF as (B0 & U8 & U16 & Hn9 & Hc9 & He9 & Dp & U0 & D24).
  assert (TBIN : In (p9, c9) (PNM.bparser_own s9)).
  { unfold PNM.bparser_own, PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
  destruct (OWNB9 p9 c9 TBIN) as (P0 & P4). unfold hl_ceil in P4.
  destruct (BRG9 p9 c9 ltac:(apply in_or_app; left; exact TBIN)) as (_ & PIMG & _). rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in PIMG.
  pose proof BR9 as (_ & _ & _ & _ & _ & _ & HH9 & _). cbn [PNBK.be_M PNBK.be_s PNBK.be_cr PNBK.be_model] in HH9.
  pose proof (proj1 (hio_wf L SCFG HI HIok _ _ _ _ HH9) (p9, c9) ltac:(apply in_or_app; left; exact TBIN)) as ((_ & _ & PA16 & _) & _). cbn [fst snd] in PA16.
  assert (PA2 : p9 mod 2 = 0).
  { pose proof (Z.div_mod p9 16 ltac:(lia)) as DM. rewrite PA16, Z.add_0_r in DM. rewrite DM.
    replace (16 * (p9 / 16)) with ((8 * (p9 / 16)) * 2) by ring. apply Z.mod_mul. lia. }
  pose proof (Z.mod_pos_bound (c9 + 1) 256 ltac:(lia)) as MB9.
  (let T := type of (PNSRVOP.vlO3_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVOP.vlO3_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc | apply tb0_long; lia])).
  destruct P as (fx10 & R10 & M10 & MG10 & EQ10w & EQ10 & MS10 & KS10 & Y1 & Y10 & Y11).
  assert (EM10 : M10 = M9) by (apply functional_extensionality; exact EQ10w). subst M10.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
           ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR10.
  (* [comment removed for export] *)
  assert (TC9 : PNSRVOH.tab_clear M9) by (intros x Hx; unfold PNSRVOH.TABLE in Hx; rewrite <- (Z_to_bv_bv_unsigned 64 x); apply IMG9; lia).
  assert (WP9 : L5.writable RSEGS M9 p9 24) by (apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M9 p9 c9); [exact Dp|lia|lia]|lia|lia]).
  assert (DEF9 : L5.defined M9 (sp - 96) 12) by (apply (L5.defined_sub M9 _ _ (sp - 96) 12 SDEF9); lia).
  assert (BY : exists b : nat -> Z, (forall i, (i < 12)%nat -> 0 <= b i < 256) /\ forall i, (i < 12)%nat -> L5.u8_at RSEGS M9 (sp - 96 + Z.of_nat i) (b i)).
  { assert (ONE : forall i, (i < 12)%nat -> exists v, 0 <= v < 256 /\ L5.u8_at RSEGS M9 (sp - 96 + Z.of_nat i) v).
    { intros i Hi. apply (PMCG.u8_of_defined RSEGS M9); [lia| lia|]. intros j Hj. replace (sp - 96 + Z.of_nat i + j) with (sp - 96 + (Z.of_nat i + j)) by lia. apply DEF9. lia. }
    assert (CH : forall n, (n <= 12)%nat -> exists b : nat -> Z, (forall i, (i < n)%nat -> 0 <= b i < 256) /\ forall i, (i < n)%nat -> L5.u8_at RSEGS M9 (sp - 96 + Z.of_nat i) (b i)).
    { induction n as [|n IH]; intros Hn.
      - exists (fun _ => 0). split; intros i Hi; lia.
      - destruct (IH ltac:(lia)) as (b0 & B1 & B2). destruct (ONE n ltac:(lia)) as (v & V1 & V2).
        exists (fun i => if Nat.eqb i n then v else b0 i). split; intros i Hi.
        + destruct (Nat.eqb_spec i n); [lia| apply B1; lia].
        + destruct (Nat.eqb_spec i n) as [->|NE]; [exact V2| apply B2; lia]. }
    exact (CH 12%nat ltac:(lia)). }
  destruct BY as (b & HB & BU).
  pose proof (HB 0%nat ltac:(lia)) as HB0. pose proof (HB 1%nat ltac:(lia)) as HB1. pose proof (HB 2%nat ltac:(lia)) as HB2. pose proof (HB 3%nat ltac:(lia)) as HB3.
  pose proof (HB 4%nat ltac:(lia)) as HB4. pose proof (HB 5%nat ltac:(lia)) as HB5. pose proof (HB 6%nat ltac:(lia)) as HB6. pose proof (HB 7%nat ltac:(lia)) as HB7.
  pose proof (HB 8%nat ltac:(lia)) as HB8. pose proof (HB 9%nat ltac:(lia)) as HB9. pose proof (HB 10%nat ltac:(lia)) as HB10. pose proof (HB 11%nat ltac:(lia)) as HB11.
  assert (TU : forall i, (i < 12)%nat -> PNSRVOP.u16_at M9 (2 * b i + 80496) (bytes_le_to_Z (PNSRVOH.tabb (b i))) /\ 0 <= bytes_le_to_Z (PNSRVOH.tabb (b i)) < 65536).
  { intros i Hi. destruct (PNSRVOH.tab_u16 M9 (b i) TC9 (HB i Hi)) as (U1 & U2). split; [| exact U2].
    unfold PNSRVOP.u16_at. replace (2 * b i + 80496) with (PNSRVOH.TABLE + 2 * b i) by (unfold PNSRVOH.TABLE; lia). exact U1. }
  pose proof (proj2 (TU 0%nat ltac:(lia))) as TR0. pose proof (proj2 (TU 1%nat ltac:(lia))) as TR1. pose proof (proj2 (TU 2%nat ltac:(lia))) as TR2.
  pose proof (proj2 (TU 3%nat ltac:(lia))) as TR3. pose proof (proj2 (TU 4%nat ltac:(lia))) as TR4. pose proof (proj2 (TU 5%nat ltac:(lia))) as TR5.
  pose proof (proj2 (TU 6%nat ltac:(lia))) as TR6. pose proof (proj2 (TU 7%nat ltac:(lia))) as TR7. pose proof (proj2 (TU 8%nat ltac:(lia))) as TR8.
  pose proof (proj2 (TU 9%nat ltac:(lia))) as TR9. pose proof (proj2 (TU 10%nat ltac:(lia))) as TR10. pose proof (proj2 (TU 11%nat ltac:(lia))) as TR11.
  assert (PT : p9 + 24 <= 80496 \/ 80496 + 512 <= p9) by lia.
  assert (PS : sp - 96 + 12 <= p9 \/ p9 + 24 <= sp - 96) by lia.
  assert (MID10 : PNSRVK.rv_mid R R10 M9 sp r fb).
  { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID10 as (V2 & V3 & V4 & V8 & V9 & V18 & _).
  (let T := type of (PNSRVOP.vlOH_conc fx10 R10 M9 (PNSRVK.tv sp r fb R (fun j => match j with 57%nat => p9
                   | 60%nat => b 0%nat | 61%nat => b 1%nat | 62%nat => b 2%nat | 63%nat => b 3%nat | 64%nat => b 4%nat | 65%nat => b 5%nat
                   | 66%nat => b 6%nat | 67%nat => b 7%nat | 68%nat => b 8%nat | 69%nat => b 9%nat | 70%nat => b 10%nat | 71%nat => b 11%nat
                   | 72%nat => bytes_le_to_Z (PNSRVOH.tabb (b 0%nat)) | 73%nat => bytes_le_to_Z (PNSRVOH.tabb (b 1%nat)) | 74%nat => bytes_le_to_Z (PNSRVOH.tabb (b 2%nat))
                   | 75%nat => bytes_le_to_Z (PNSRVOH.tabb (b 3%nat)) | 76%nat => bytes_le_to_Z (PNSRVOH.tabb (b 4%nat)) | 77%nat => bytes_le_to_Z (PNSRVOH.tabb (b 5%nat))
                   | 78%nat => bytes_le_to_Z (PNSRVOH.tabb (b 6%nat)) | 79%nat => bytes_le_to_Z (PNSRVOH.tabb (b 7%nat)) | 80%nat => bytes_le_to_Z (PNSRVOH.tabb (b 8%nat))
                   | 81%nat => bytes_le_to_Z (PNSRVOH.tabb (b 9%nat)) | 82%nat => bytes_le_to_Z (PNSRVOH.tabb (b 10%nat)) | 83%nat => bytes_le_to_Z (PNSRVOH.tabb (b 11%nat))
                   | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in
   LeanFeed.pfeed_at P (PNSRVOP.vlOH_conc fx10 R10 M9 (PNSRVK.tv sp r fb R (fun j => match j with 57%nat => p9
                   | 60%nat => b 0%nat | 61%nat => b 1%nat | 62%nat => b 2%nat | 63%nat => b 3%nat | 64%nat => b 4%nat | 65%nat => b 5%nat
                   | 66%nat => b 6%nat | 67%nat => b 7%nat | 68%nat => b 8%nat | 69%nat => b 9%nat | 70%nat => b 10%nat | 71%nat => b 11%nat
                   | 72%nat => bytes_le_to_Z (PNSRVOH.tabb (b 0%nat)) | 73%nat => bytes_le_to_Z (PNSRVOH.tabb (b 1%nat)) | 74%nat => bytes_le_to_Z (PNSRVOH.tabb (b 2%nat))
                   | 75%nat => bytes_le_to_Z (PNSRVOH.tabb (b 3%nat)) | 76%nat => bytes_le_to_Z (PNSRVOH.tabb (b 4%nat)) | 77%nat => bytes_le_to_Z (PNSRVOH.tabb (b 5%nat))
                   | 78%nat => bytes_le_to_Z (PNSRVOH.tabb (b 6%nat)) | 79%nat => bytes_le_to_Z (PNSRVOH.tabb (b 7%nat)) | 80%nat => bytes_le_to_Z (PNSRVOH.tabb (b 8%nat))
                   | 81%nat => bytes_le_to_Z (PNSRVOH.tabb (b 9%nat)) | 82%nat => bytes_le_to_Z (PNSRVOH.tabb (b 10%nat)) | 83%nat => bytes_le_to_Z (PNSRVOH.tabb (b 11%nat))
                   | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv])
     ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc
                 | lazymatch goal with |- L5.u8_at _ _ (sp - ?o) (b ?i) => replace (sp - o) with (sp - 96 + Z.of_nat i) by lia; apply BU; lia end
                 | lazymatch goal with |- PNSRVOP.u16_at _ (2 * b ?i + _) _ => exact (proj1 (TU i ltac:(lia))) end])).
  destruct P as (fx11 & R11 & M12 & MG12 & _ & FRZ12 & MS11 & KS11 & _).
  assert (AG912 : forall a n, (a + n <= p9 \/ p9 + 24 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M9 M12 a n).
  { intros a n H0 H1 H2 i Hi. apply FRZ12; lia. }
  apply (PNSRVK.brel_piece_tb L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx10 fx11 R10 R11 _ _ M12
           (fun a => p9 <= a < p9 + 24) (PM.VLong c9 24 p9) K BR10 FOK INCS MS11 MG12
           ltac:(intros a Ha N; cbn beta in N; apply FRZ12; [exact Ha| intros X; apply N; lia]) ltac:(intros a; apply PMK.rng_dec));
    [| | rewrite ETB; reflexivity| rewrite ETB; reflexivity|].
  { intros a Pa. cbn beta in Pa. right. right. rewrite ETB. exists (p9, c9). split; [cbn; auto| cbn [fst snd]; lia]. }
  { unfold PM.vstr_at. split; [apply (L5.defined_grows M9 _ _ _ MG12 D24)|]. split; [exact I|].
    split; [apply (L5C.u64_at_agree RSEGS M9); [apply AG912; lia|lia|lia| exact U0]|].
    split; [apply (L5C.u64_at_agree RSEGS M9); [apply AG912; lia|lia|lia| replace (fb + 408 + 8) with (fb + 40 + 376) by lia; exact U8]|].
    split; [apply (L5C.u64_at_agree RSEGS M9); [apply AG912; lia|lia|lia| replace (fb + 408 + 16) with (fb + 40 + 384) by lia; exact U16]|].
    split; [lia|]. split; [lia|]. split; [exact He9|]. split; [apply (L5.defined_grows M9 _ _ _ MG12 Dp)| exact I]. }
  intros BR12.
  assert (MID12 : PNSRVK.rv_mid R R11 M12 sp r fb).
  { apply (PNSRVK.rv_mid_xfer R R10 R11 M9 M12 sp r fb _ MID10 KS11); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n H1 H2; apply AG912; lia| lia| lia]. }
  pose proof MID12 as (W2 & W3 & W4 & W8 & W9 & W18 & SV12 & SX12).
  assert (EC12 : PMSP.ec_at RSEGS M12 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M9 M12); [apply AG912; lia|lia|lia| exact EC9]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR12) as (PA12 & _ & _ & _ & STK12 & _).
  change (PMSP.pm_scr 8) with 28672 in STK12. pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK12) as WR12.
  pose proof PA12 as (_ & PD12 & _ & _ & _ & CM12 & _).
  assert (VIS12 : L5.u64_at RSEGS M12 (fb + 464) 726280) by (apply (L5C.u64_at_agree RSEGS M9); [apply AG912; lia|lia|lia| exact VIS9]).
  assert (IMG12 : L5.img_clear M12 65536 754672) by (intros i Hi; rewrite FRZ12; [apply IMG9; exact Hi| lia| lia]).
  pose proof (PNSRVK.tb_facts M12 fb _ PA12) as TBF12. cbn [PNBO.set_tb PNM.b_tb] in TBF12. destruct TBF12 as (B0' & U8' & U16' & _).
  (let T := type of (PNSRVOP.vlO4_conc fx11 R11 M12 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 58%nat => 24 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVOP.vlO4_conc fx11 R11 M12 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 58%nat => 24 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc | apply tb0_long; lia])).
  destruct P as (fx13 & R13 & M13 & MG13 & _ & FRZ13 & MS13 & KS13 & _ & Y10' & _).
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M12 model9 cr9 _ sm9 ax9 fx11 fx13 R11 R13 _ _ M13 (fun a => sp - 64 <= a < sp - 64 + 16) K
           ltac:(lia) BR12 FOK INCS MS13 MG13 FRZ13 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
  intros BR13.
  apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx13 R13 M13 model9 cr9 _ sm9 ax9 1 CTX KONT BR13); [| exact Y10'|].
  - apply (PNSRVK.rv_mid_xfer R R11 R13 M12 M13 sp r fb _ MID12 KS13); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n H1 H2 i Hi; apply FRZ13; lia| lia| lia].
  - right. split; [reflexivity|]. split; [apply (PNSRVK.ec_agree M12 M13); [intros i Hi; apply FRZ13; lia|lia|lia| exact EC12]|].
    split; [destruct INV9 as (ID & SH); split; [exact ID| exact SH]|].
    split; [left; destruct TP9 as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; cbn [PNBO.set_tb PNM.b_stk]; split; [exact Ea|]; split; [exact Eb| exact Q]|].
    intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_tb PNM.b_bb PNM.b_src]. rewrite EBB. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [exact LEU| exact R0].
Qed.

(* [comment removed for export] *)
Lemma step1 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 (d : Z) :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  PNM.b_bb s9 = PNM.b_bb s -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm ->
  getr R9 (PMK.reg 10) = Z_to_bv 64 d -> 0 <= d <= 12 -> L5.defined M9 (sp - 80) d ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x379b4 M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 EC9 INV9 TP9 EBB LEU Q10 Hd DEF9.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9 INV9) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  set (et := PNM.b_sb s9 + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  (let T := type of (PNSRVOP.vlO1_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVOP.vlO1_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & [(MS10 & KS10 & _ & _ & _ & LT & CP10)|(MS10 & KS10 & _ & _ & _ & LT & CP10)]).
  - (* [comment removed for export] *)
    apply (PNSRVB.pos_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx9 fx10 R9 R10 M9 M10 model9 cr9 s9 sm9 ax9 _
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64)
             ltac:(left; split; reflexivity) CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [| unfold et in E1; exact E1| unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia| intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto].
    intros a Pa. cbn beta in Pa. unfold et in Pa. right; lia.
  - (* [comment removed for export] *)
    pose proof (PNSRVB.eq_of_mod d 12 Hd ltac:(lia) LT) as Hd12. subst d.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((12 + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; cbn beta in Pa; unfold et in Pa; right; lia
      | unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia |].
    intros BR10.
    set (s10 := PNBO.set_stk s9 (l ++ [PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((12 + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)])) in *.
    assert (AG910 : forall a m, (a + m <= et + 16 \/ et + 24 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M9 M10 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ10; lia).
    assert (MID10 : PNSRVK.rv_mid R R10 M10 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG910; unfold et; lia| lia| lia]. }
    pose proof MID10 as (W2 & W3 & W4 & W8 & W9 & W18 & SV10).
    assert (EC10 : PMSP.ec_at RSEGS M10 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M9 M10); [apply AG910; unfold et; lia|lia|lia| exact EC9]).
    assert (INV10 : PNR.binv s10) by (apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity]).
    assert (TP10 : PNR.btop_pos s s10) by (apply (PNBK2.btop_pos_trans s s9); [exact TP9|]; apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| exact OKc'| reflexivity| reflexivity| reflexivity| reflexivity]).
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR10) as (PA10 & _ & _ & _ & STK10 & _).
    change (PMSP.pm_scr 8) with 28672 in STK10. pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK10) as WR10.
    (* [comment removed for export] *)
    assert (DEF10 : L5.defined M10 (sp - 80) 12) by (apply (L5C.defined_agree M9 M10 (sp - 80) 12); [apply AG910; unfold et; lia| exact DEF9]).
    assert (BY : exists b : nat -> Z, (forall i, (i < 12)%nat -> 0 <= b i < 256) /\ forall i, (i < 12)%nat -> L5.u8_at RSEGS M10 (sp - 80 + Z.of_nat i) (b i)).
    { assert (ONE : forall i, (i < 12)%nat -> exists v, 0 <= v < 256 /\ L5.u8_at RSEGS M10 (sp - 80 + Z.of_nat i) v).
      { intros i Hi. apply (PMCG.u8_of_defined RSEGS M10); [lia| lia|]. intros j Hj. replace (sp - 80 + Z.of_nat i + j) with (sp - 80 + (Z.of_nat i + j)) by lia. apply DEF10. lia. }
      assert (CH : forall n, (n <= 12)%nat -> exists b : nat -> Z, (forall i, (i < n)%nat -> 0 <= b i < 256) /\ forall i, (i < n)%nat -> L5.u8_at RSEGS M10 (sp - 80 + Z.of_nat i) (b i)).
      { induction n as [|n IH]; intros Hn.
        - exists (fun _ => 0). split; intros i Hi; lia.
        - destruct (IH ltac:(lia)) as (b0 & B1 & B2). destruct (ONE n ltac:(lia)) as (v & V1 & V2).
          exists (fun i => if Nat.eqb i n then v else b0 i). split; intros i Hi.
          + destruct (Nat.eqb_spec i n); [lia| apply B1; lia].
          + destruct (Nat.eqb_spec i n) as [->|NE]; [exact V2| apply B2; lia]. }
      exact (CH 12%nat ltac:(lia)). }
    destruct BY as (b & HB & BU).
    pose proof (HB 0%nat ltac:(lia)) as HB0. pose proof (HB 1%nat ltac:(lia)) as HB1. pose proof (HB 2%nat ltac:(lia)) as HB2. pose proof (HB 3%nat ltac:(lia)) as HB3.
    pose proof (HB 4%nat ltac:(lia)) as HB4. pose proof (HB 5%nat ltac:(lia)) as HB5. pose proof (HB 6%nat ltac:(lia)) as HB6. pose proof (HB 7%nat ltac:(lia)) as HB7.
    pose proof (HB 8%nat ltac:(lia)) as HB8. pose proof (HB 9%nat ltac:(lia)) as HB9. pose proof (HB 10%nat ltac:(lia)) as HB10. pose proof (HB 11%nat ltac:(lia)) as HB11.
    (let T := type of (PNSRVOP.vlO2_conc fx10 R10 M10 (PNSRVK.tv sp r fb R (fun j => match j with 60%nat => b 0%nat | 61%nat => b 1%nat | 62%nat => b 2%nat | 63%nat => b 3%nat | 64%nat => b 4%nat | 65%nat => b 5%nat
                   | 66%nat => b 6%nat | 67%nat => b 7%nat | 68%nat => b 8%nat | 69%nat => b 9%nat | 70%nat => b 10%nat | 71%nat => b 11%nat | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVOP.vlO2_conc fx10 R10 M10 (PNSRVK.tv sp r fb R (fun j => match j with 60%nat => b 0%nat | 61%nat => b 1%nat | 62%nat => b 2%nat | 63%nat => b 3%nat | 64%nat => b 4%nat | 65%nat => b 5%nat
                   | 66%nat => b 6%nat | 67%nat => b 7%nat | 68%nat => b 8%nat | 69%nat => b 9%nat | 70%nat => b 10%nat | 71%nat => b 11%nat | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc
                           | lazymatch goal with |- L5.u8_at _ _ (sp - ?o) (b ?i) => replace (sp - o) with (sp - 80 + Z.of_nat i) by lia; apply BU; lia end])).
    destruct P as (fx11 & R11 & M11 & MG11 & _ & FRZ11 & MS11 & KS11 & Y1 & Y10 & Y11 & _).
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M10 model9 cr9 s10 sm9 ax9 fx10 fx11 R10 R11 _ _ M11 (fun a => sp - 96 <= a < sp - 96 + 12) K
             ltac:(lia) BR10 FOK INCS MS11 MG11 FRZ11 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
    intros BR11.
    assert (AG1011 : forall a m, (a + m <= sp - 96 \/ sp - 84 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M10 M11 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ11; lia).
    assert (MID11 : PNSRVK.rv_mid R R11 M11 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R10 R11 M10 M11 sp r fb _ MID10 KS11); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG1011; lia| lia| lia]. }
    pose proof MID11 as (V2 & V3 & V4 & V8 & V9 & V18 & SV11).
    (* [comment removed for export] *)
    change (@PMSP.cfg RSEGS fx11 R11 0x59000 M11 model9) with (@PMSP.cfg RSEGS fx11 R11 (pa_str_resize AD) M11 model9).
    apply (PNSRVK.brel_str_resize_tb L HI LY HIok LBX sp fb str _ M11 model9 cr9 s10 sm9 ax9 fx11 R11 (sp - 96) _ 24 K RSZ K0 BR11 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity]) V2 V3 V4 Y10 Y11);
      [pose proof (PNSRVK.tb_facts M10 fb s10 PA10) as T; destruct (PNM.b_tb s10); cbn [PM.vs_size]; [destruct T as (T1 & _)| destruct T as (_ & _ & _ & T1 & _)]; unfold PM.CHUNK; lia
      | unfold PM.CHUNK; lia| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)|].
    intros fx12 R12 M12 model12 x12 g12 cr12 RP1112 SZ12 _ BR12 AG1112.
    apply (step3 t K LBX sp r fb cat e str R M model cr s sm ax fx12 R12 M12 model12 cr12 (PNBO.set_tb s10 x12 g12) sm9 ax9 CTX KONT BR12).
    + apply (PNSRVK.rv_mid_pres R R11 R12 M11 M12 sp r fb MID11 RP1112); [intros a m H1 H2; apply AG1112; lia| lia| lia].
    + apply (PNSRVK.ec_agree M11 M12); [apply AG1112; lia|lia|lia|]. apply (PNSRVK.ec_agree M10 M11); [apply AG1011; lia|lia|lia| exact EC10].
    + destruct INV10 as (ID & SH). split; [exact ID| exact SH].
    + destruct TP10 as (la & ca & cb & Ea & Eb & Q). exists la, ca, cb. cbn [PNBO.set_tb PNM.b_stk]. split; [exact Ea|]. split; [exact Eb| exact Q].
    + cbn [PNBO.set_tb PNM.b_bb s10 PNBO.set_stk]. exact EBB.
    + cbn [PNBO.set_tb PNM.b_src s10 PNBO.set_stk]. exact LEU.
    + cbn [PNBO.set_tb PNM.b_tb]. exact SZ12.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma armOid : PNSRVA.arm_stmt L HI 0x379a4.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVOP.vlO0_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVOP.vlO0_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVOP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 80) 12 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  apply (step1 t K LBX sp r fb cat e str R M model cr s sm ax fx7 R7 M7 model5 cr5 (PNM.with_srcB s src7) sm7 ax5 d CTX KONT BR7);
    [| apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]| destruct INV0 as (ID & SH); split; [exact ID| exact SH]
     | destruct (PNBK2.btop_pos_refl s INV0) as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; split; [exact Ea|]; split; [exact Eb| exact Q]
     | reflexivity| cbn [PNM.with_srcB PNM.b_src]; lia| exact Z10| exact Hd| exact DEF7].
  apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
  apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia].
Qed.

End WithHeap.
End PNSRVO.
