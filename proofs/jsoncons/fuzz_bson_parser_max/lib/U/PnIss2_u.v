(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5KnA_u PnIssStmts_u PnIssSP_u
     Bs0_code_r342cc_342d0_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMIS2.
Import PMS.

Lemma csk_icCs1 : forall k, In k PMIS.CSK -> In k PMISP.KS_icCs1. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icCs2 : forall k, In k PMIS.CSK -> In k PMISP.KS_icCs2. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.

Ltac t14 AG C := lazymatch type of C with
  | L5.u64_at _ ?Ms _ _ => apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.u32_at _ ?Ms _ _ => apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.u8_at _ ?Ms _ _ => apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.defined ?Ms _ _ => apply (L5C.defined_agree Ms); [intros i Hi; apply AG; lia | first [exact C | PMK.gmem]]
  | L5KA.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
                               apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  | PM.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
                            apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  end.

(* [comment removed for export] *)
Ltac gx AG :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M2 ?a ?v => match goal with H : L5.u64_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  | |- L5.u32_at ?sg ?M2 ?a ?v => match goal with H : L5.u32_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  | |- L5.u8_at ?sg ?M2 ?a ?v => match goal with H : L5.u8_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (L5C.u8_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  end.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma tail_short :
  forall (fx1 : FPState) R0 M0 model0 K LB cr ois os sp r s b R1 M1 model1 n,
    PMIS.pre L HI R0 M0 model0 K LB cr ois os sp r s b ->
    PMIS.kont L HI R0 M0 model0 K LB cr ois sp r s b ->
    s = PM.VShort n ->
    PMIS.mid L HI R0 M0 model0 LB cr ois os sp s b R1 M1 model1 ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36204 M1 model1) K.
Proof.
  intros fx1 R0 M0 model0 K LB cr ois os sp r s b R1 M1 model1 n PRE KONT Es MID.
  destruct PRE as (_ & _ & _ & ENT & _ & _ & _ & Hspo & Hoos & Hostop & Ho8 & Hos8 & _ & _ & _ & SZ & _ & _ & _ & _).
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & _ & _ & STK0).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  destruct MID as (R2 & R8 & R9 & R19 & R20 & R21 & RCSK & SI & SB & HC & DEF1 & VS1 & STK1 & BASE1 & LOC1 & HH1 & MOK1 & MB1 & EK01 & DK01).
  pose proof MOK1 as (Mh & Ml & Mm).
  pose proof (L5C.stk_floor _ _ _ _ STK1) as FL. pose proof (L5C.stk_writable RSEGS _ M1 sp _ STK1) as WR1.
  pose proof STK1 as (S16 & SBd & SC & SD & SW). unfold PMIS.SCR in *.
  assert (WRO : L5.writable RSEGS M1 ois 272) by (apply (L5C.writable_of_defined RSEGS M1 ois 272 DEF1); lia).
  pose proof (PMCK.lb_hi L HI HIok LB cr M1 _ HH1) as LBhi.
  pose proof BASE1 as (RO1 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO1.
  subst s. destruct VS1 as (DEFS & _ & Hn & U0).
  destruct (PMCG.u64_of_defined RSEGS M1 os ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M1 os 24); [exact DEFS|lia|lia])) as (w0 & Hw0 & W0).
  destruct (PMCG.u64_of_defined RSEGS M1 (os + 8) ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M1 os 24); [exact DEFS|lia|lia])) as (w1 & Hw1 & W1).
  destruct (PMCG.u64_of_defined RSEGS M1 (os + 16) ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M1 os 24); [exact DEFS|lia|lia])) as (w2 & Hw2 & W2).
  assert (LOW : w0 mod 256 = 2 * n) by (apply (PMCG.u8_of_u64_eq RSEGS M1 os w0 (2 * n) Hw0 ltac:(lia) W0 U0)).
  LeanFeed.pfeed P (PMISP.icCs1_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => ois | 35%nat => w0 | 36%nat => w1 | 37%nat => w2 | 38%nat => 2 * n
                                                               | 39%nat => os - ois | _ => 0 end)) ltac:(first [ PMK.sc | exact RO1 | exact (PMF.even_byte n) ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx2 & R3 & M2 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG2 & FR2 & FRZ2 & MS2 & KS2 & B1 & B10 & B11 & B12 & B13 & B14 & B18 & C80 & C88 & C96 & C112 & C104 & C16 & Z32)); PMK.pvz_clrT.
  clear FR2 C88 C96 C104 B10 B11 B12 B13 B14 B18.
  unfold PMSP.cfg.
  set (P2 := fun a => ois + 16 <= a < ois + 24 \/ ois + 32 <= a < ois + 116).
  assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P2 in NP. apply FRZ2; [exact Ha| |]; intros X; apply NP; lia. }
  assert (CW2 : forall a, P2 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M1 sp 20480 a STK1). unfold P2 in Ha. lia. }
  assert (DEC2 : forall a, {P2 a} + {~ P2 a}) by (intros a; unfold P2; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model1 fx1 fx2 R1 0x36204 R3 0x36248 M2 P2 K HH1 Mh Ml ltac:(lia) MS2 MG2 AG2 CW2 DEC2).
  intros HH2.
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (L5C.stk_grows _ M1 M2 _ _ MG2 STK1)).
  assert (EK12n : PMK.ek L LB sp 20480 [(ois, 272)] M1 M2).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M1 M2 P2 AG2 STK1 LBhi). intros a X. unfold P2 in X. right; apply PMK.inW_here; lia. }
  assert (EK12 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M1 M2).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 (PMIS.WF ois b) M1 M2 P2 AG2 STK1 LBhi). intros a X. unfold P2 in X. right; unfold PMIS.WF; apply PMK.inW_here; lia. }
  assert (LOC2 : PMST.loc_ok RSEGS AD M2 true).
  { apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M1 M2 EK12n true); [|exact LOC1].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
  assert (U80 : L5.u8_at RSEGS M2 (ois + 80) (2 * n)).
  { rewrite <- LOW. apply (PMF.u8_of_u64 RSEGS M2 (ois + 80) w0 Hw0 C80). }
  (* [comment removed for export] *)
  destruct SI as (S8 & S16b & S24 & S32 & S40 & S48 & S56 & S64 & S72).
  destruct SB as (T88 & T96 & T104 & T112 & T120 & T128 & T136).
  assert (V1 : 0 <= bv_unsigned (getr R0 (PMK.reg 1)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V8 : 0 <= bv_unsigned (getr R0 (PMK.reg 8)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V9 : 0 <= bv_unsigned (getr R0 (PMK.reg 9)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V18 : 0 <= bv_unsigned (getr R0 (PMK.reg 18)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V19 : 0 <= bv_unsigned (getr R0 (PMK.reg 19)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V20 : 0 <= bv_unsigned (getr R0 (PMK.reg 20)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V21 : 0 <= bv_unsigned (getr R0 (PMK.reg 21)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V22 : 0 <= bv_unsigned (getr R0 (PMK.reg 22)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V23 : 0 <= bv_unsigned (getr R0 (PMK.reg 23)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (R3sp : getr R3 (PMK.reg 2) = Z_to_bv 64 (sp - 144)) by (rewrite (KS2 2%nat) by PMK.inl; exact R2).
  assert (R3s0 : getr R3 (PMK.reg 8) = Z_to_bv 64 (ois + 16)) by (rewrite (KS2 8%nat) by PMK.inl; exact R8).
  assert (WR2 : L5.writable RSEGS M2 (sp - 20480) 20480) by (apply (L5C.stk_writable RSEGS _ M2 sp _ STK2)).
  assert (WRO2 : L5.writable RSEGS M2 ois 272) by (apply (L5.writable_grows RSEGS M1 M2 _ _ MG2); exact WRO).
  assert (AG2s : forall a, sp - 208 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; apply AG2; [lia| unfold P2; lia]).
  LeanFeed.pfeed P (PMISP.icCs2_conc fx2 R3 M2 (fun j => match j with 2%nat => sp | 33%nat => ois | 38%nat => 2 * n | 39%nat => os - ois
      | 43%nat => bv_unsigned (getr R0 (PMK.reg 1)) | 44%nat => bv_unsigned (getr R0 (PMK.reg 8)) | 45%nat => bv_unsigned (getr R0 (PMK.reg 9))
      | 46%nat => bv_unsigned (getr R0 (PMK.reg 18)) | 47%nat => bv_unsigned (getr R0 (PMK.reg 19)) | 48%nat => bv_unsigned (getr R0 (PMK.reg 20))
      | 49%nat => bv_unsigned (getr R0 (PMK.reg 21)) | 50%nat => bv_unsigned (getr R0 (PMK.reg 22)) | 51%nat => bv_unsigned (getr R0 (PMK.reg 23)) | _ => 0 end)) ltac:(first [ PMK.sc | exact (PMF.even_byte n) | gx AG2s ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R4 & M3 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E18 & E19 & E20 & E21 & E22 & E23 & G104 & G48 & G40 & G32)); PMK.pvz_clrT.
  clear FR3 E10 E11 E12 E13 E14.
  set (P3 := fun a => sp - 192 <= a < sp - 144 \/ ois + 32 <= a < ois + 56 \/ ois + 104 <= a < ois + 112).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P3 in NP. apply FRZ3; [exact Ha| | |]; intros X; apply NP; lia. }
  assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M2 sp 20480 a STK2). unfold P3 in Ha. lia. }
  assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model1 fx2 fx3 R3 0x36248 R4 0x34ab8 M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 AG3 CW3 DEC3).
  intros HH3.
  assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (L5C.stk_grows _ M2 M3 _ _ MG3 STK2)).
  assert (EK23n : PMK.ek L LB sp 20480 [(ois, 272)] M2 M3).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M2 M3 P3 AG3 STK2 LBhi). intros a X. unfold P3 in X.
    destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
  assert (EK23 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M2 M3).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 (PMIS.WF ois b) M2 M3 P3 AG3 STK2 LBhi). intros a X. unfold P3 in X.
    destruct X as [X|X]; [left; lia| right; unfold PMIS.WF; apply PMK.inW_here; lia]. }
  (* [comment removed for export] *)
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx3 R4 M3 0x34ab8 W_34744 r F_34744 ltac:(reflexivity) D_34744)|].
  { rewrite E1, Z_to_bv_bv_unsigned. exact Rra. } { exact RA1. } { exact RA2. }
  assert (AG13 : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> ~ P3 a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N2 N3. rewrite (AG3 a Ha N3). apply AG2; assumption. }
  assert (AG13r : forall a, 0 <= a < 2 ^ 64 -> ~ (ois + 16 <= a < ois + 24) -> ~ (ois + 32 <= a < ois + 116) -> ~ (sp - 192 <= a < sp - 144) ->
            M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. apply AG13; [exact Ha| unfold P2; lia| unfold P3; lia]. }
  assert (AG23r : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 192 <= a < sp - 144) -> ~ (ois + 32 <= a < ois + 56) -> ~ (ois + 104 <= a < ois + 112) ->
            M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. apply AG3; [exact Ha| unfold P3; lia]. }
  assert (MG13 : mem_grows M1 M3) by (intros x Hx; apply MG3, MG2; exact Hx).
  destruct HC as (H0 & H24 & H120 & H152 & H156 & H160 & H168 & H176).
  cbn [pa_vp_iss pa_classic_imp pa_vp_iss_ios AD PnLayoutS_u.ADDR_S] in H0, H24, H120, H168.
  assert (E2n : 2 * n / 2 = n) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
  rewrite E2n in G104, G48.
  apply (KONT fx3 R4 M3 model1 (PM.VShort n) (PM.STRM (ois + 81) (ois + 81 + n) 0) cr).
  - apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
    assert (CH : forall j, In j PMIS.CSK -> getr R4 (PMK.reg j) = getr R0 (PMK.reg j)).
    { intros j Hj. rewrite (KS3 j (csk_icCs2 j Hj)), (KS2 j (csk_icCs1 j Hj)). apply RCSK. exact Hj. }
    destruct Hk as [<-|Hk]; [rewrite E2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
    destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
    destruct Hk as [<-|Hk]; [rewrite E8; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E18; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E20; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E22; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
    repeat (destruct Hk as [<-|Hk]; [apply CH; PMK.inl|]). destruct Hk.
  - unfold PMIS.iss_at, PM.iss_at. cbn [pa_vp_iss pa_vp_strbuf pa_classic_imp pa_vp_iss_ios PM.vs_data PM.vs_size PM.sm_g PM.sm_eg PM.sm_st AD PnLayoutS_u.ADDR_S].
    split; [t14 AG13r H0|].
    split; [apply (L5.defined_grows M1 M3 _ _ MG13); apply (L5.defined_sub M1 ois 272); [exact DEF1|lia|lia]|].
    split; [exact I|].
    split; [t14 AG23r C16|].
    split; [t14 AG13r H24|].
    split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem|].
    split; [apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; apply AG23r; lia|lia|lia|]; apply (PMCG.u64_of_zeros RSEGS M2); [|lia|lia];
            apply (PMCG.zeros_sub M2 (ois + 32) 48); [exact Z32|lia|lia]|].
    split.
    { split; [apply (L5.defined_grows M1 M3 _ _ MG13); apply (L5.defined_sub M1 ois 272); [exact DEF1|lia|lia]|]. split; [exact I|].
      split; [lia| t14 AG23r U80]. }
    split; [PMK.gmem|].
    split; [t14 AG23r C112|].
    split.
    { unfold PM.iosb_at. cbn [pa_classic_imp AD PnLayoutS_u.ADDR_S].
      split; [t14 AG13r H120|]. split; [t14 AG13r H152|]. split; [t14 AG13r H156|]. split; [t14 AG13r H160|].
      split; [t14 AG13r H168|]. split; [t14 AG13r H176|].
      split; [apply (L5.defined_grows M1 M3 _ _ MG13); apply (L5.defined_sub M1 ois 272); [exact DEF1|lia|lia]|].
      split; [exact I| left; reflexivity]. }
    split; lia.
  - reflexivity.
  - cbn. lia.
  - reflexivity.
  - apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M2 M3 EK23n true); [|exact LOC2].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW.
  - apply PMK.hpres_of.
    + apply (PMK.ek_trans L LB sp 20480 _ M0 M1 M3 EK01). apply (PMK.ek_trans L LB sp 20480 _ M1 M2 M3 EK12 EK23).
    + destruct STK3 as (_ & _ & _ & _ & X). exact X.
    + apply (PMK.dk_trans L LB sp 20480 M0 M1 M3 DK01). apply PMK.dk_grows. exact MG13.
  - unfold PMSP.credit_keep, PMIS.cost, PMSP.cr0, PM.cost1. cbn [fst snd]. pose proof (ly_kpm L LY). pose proof (ly_bov L LY). cbn [PM.vs_size]. lia.
  - exact MB1.
  - cbn [PM.vs_own app]. exact HH3.
Qed.

End Stage.
End PMIS2.
