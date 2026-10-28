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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface AxSymExec3 AxSymExec3Sound AsanPlanSoundSums
     L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnOwnerOkS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2 PnBrKit3 PnBrKit4. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSReadStrP_u
     Bs0_code_37698_3769c_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRST.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma ec_agree (M M' : mem) o v c : L5C.agree_on M M' o 16 -> 0 <= o -> o + 16 <= 2 ^ 64 -> PMSP.ec_at RSEGS M o v c -> PMSP.ec_at RSEGS M' o v c.
Proof.
  intros AG H1 H2 (E0 & E8 & ED). split; [|split].
  - apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
  - apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
  - apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma mod16_sub80 sp : sp mod 16 = 0 -> (sp - 80) mod 16 = 0.
Proof. intros H. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.
Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.
Lemma u32_of_defined (M : mem) a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4 -> exists w, 0 <= w < 2 ^ 32 /\ L5.u32_at RSEGS M a w.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 4%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [lia|]. unfold L5.u32_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.
(* [comment removed for export] *)
Lemma fork_eq n2 len : 1 <= len <= 2147483647 -> 0 <= n2 <= 2147483647 ->
  ((n2 - ((len + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1 -> n2 = len - 1.
Proof.
  intros Hl Hn H. replace (len + 18446744073709551615) with ((len - 1) + 1 * 2 ^ 64) in H by lia.
  rewrite Z.mod_add, (Z.mod_small (len - 1)) in H by lia.
  destruct (Z.eq_dec n2 (len - 1)) as [E|NE]; [exact E|]. exfalso.
  destruct (Z_lt_le_dec n2 (len - 1)) as [LT|GE].
  - replace (n2 - (len - 1)) with ((n2 - (len - 1) + 2 ^ 64) + (-1) * 2 ^ 64) in H by lia. rewrite Z.mod_add, Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma fork_ne n2 len : 1 <= len <= 2147483647 -> 0 <= n2 <= 2147483647 ->
  1 <= ((n2 - ((len + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) -> n2 <> len - 1.
Proof.
  intros Hl Hn H ->. replace (len + 18446744073709551615) with ((len - 1) + 1 * 2 ^ 64) in H by lia.
  rewrite Z.mod_add, (Z.mod_small (len - 1)), Z.sub_diag, Z.mod_0_l in H by lia. lia.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 7).
Abbreviation pot := (PNR.pot_bparser L).

Hypothesis SRD : PNRS.src_read_spec L HI.
Hypothesis RSP : PNRS.read_span_spec L HI.
Hypothesis MKE : PNRS.make_ec_spec L HI.

Lemma twok_S : PNBK3.twok RSEGS AD L HI.
Proof.
  intros fb s H1 H2 H3 H4. apply (PNOKS.txt_owner_ok_S L HI LY HIok). unfold PNOKS.owok_pre. split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
Qed.

(* [comment removed for export] *)
Definition rs_kont (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.brun_post RSEGS AD AN false (PNR.bprog_rs AD fb) R' M' fb s s' str sm sm' ax ax' cat e ->
      L5C.hpres L LBX sp (PMSP.pm_scr 7) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) (pot s') ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition rs_ctx (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb e : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit)
           (s : PNM.bpst) (sm : PM.strm) : Prop :=
  K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr /\ PNR.binv s /\ PM.unread (PNM.b_src s) sm < 2 ^ 26 /\ 0 <= e <= 64.
Definition rs_saved (R : bvmap 5 word) (M1 : mem) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) r /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\ L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))
  /\ L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 21))) /\ L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 22))).
Lemma rs_saved_agree R (M1 M2 : mem) sp r :
  (forall a n, sp - 64 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n) -> 0 <= sp - 80 -> sp <= 2 ^ 64 -> rs_saved R M1 sp r -> rs_saved R M2 sp r.
Proof.
  intros AG H1 H2 (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). unfold rs_saved.
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- L5.u64_at _ M2 ?a ?v => apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| assumption]
  end.
Qed.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc]).
Local Ltac ksl KS := rewrite (KS _) by PMK.inl.
Local Ltac ksk KS Hk := rewrite (KS _) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).

(* [comment removed for export] *)
Lemma rs_fin K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  rs_ctx K LBX sp r fb e str R cr s sm -> rs_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R5 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R5 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  getr R5 (PMK.reg 20) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 20))) -> getr R5 (PMK.reg 21) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 21))) ->
  getr R5 (PMK.reg 22) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 22))) ->
  (forall k, In k [23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  (   ((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M5 (fb + 16) v (pa_errcat_obj AD)) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true
       /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bprog_rs AD fb R5 M5 s s5 sm sm5)) ->
  PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x387f8 M5 model5) K.
Proof.
  intros (K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He) KONT BR Y1 Y2 Y3 Y4 Y8 Y9 Y18 Y19 Y20 Y21 Y22 YK POST BB.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx5 R5 M5 0x387f8 W_3773c r F_3773c eq_refl D_3773c); [exact Y1| lia| exact Hr2]. }
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite Y8; apply Z_to_bv_bv_unsigned | rewrite Y9; apply Z_to_bv_bv_unsigned | rewrite Y18; apply Z_to_bv_bv_unsigned
            | rewrite Y19; apply Z_to_bv_bv_unsigned | rewrite Y20; apply Z_to_bv_bv_unsigned | rewrite Y21; apply Z_to_bv_bv_unsigned
            | rewrite Y22; apply Z_to_bv_bv_unsigned | apply YK; cbn; tauto ].
  - unfold PNR.brun_post. split; [exact RP|]. split; [exact STEP|]. split; [exact AXL|].
    unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S].
    split; [| exact BB].
    destruct POST as [((v & Hv & E1) & MO & CAT & LEN & INV')|(E0 & INV & PROG)].
    + left. exists v. split; [exact Hv|]. split; [exact E1|]. split; [exact MO|]. split; [exact CAT|]. split; [exact LEN| exact INV'].
    + right. split; [exact E0|]. split; [exact INV| exact PROG].
  - exact HP.
  - exact CK.
  - exact MB.
  - exact HH.
Qed.

(* [comment removed for export] *)
Lemma rs_err K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx3 : FPState) R3 (M3 : mem) model3 cr3 s3 sm3 ax3 v :
  rs_ctx K LBX sp r fb e str R cr s sm -> rs_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M3 model3 cr3 s3 sm3 ax3) ->
  getr R3 (PMK.reg 1) = Z_to_bv 64 0x38810 -> getr R3 (PMK.reg 2) = Z_to_bv 64 (sp - 80) ->
  getr R3 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R3 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R3 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R3 (PMK.reg 10) = Z_to_bv 64 (fb + 16) -> getr R3 (PMK.reg 11) = Z_to_bv 64 v ->
  getr R3 (PMK.reg 19) = Z_to_bv 64 (fb + 16) -> getr R3 (PMK.reg 20) = Z_to_bv 64 (fb + 40 + 16) ->
  (forall k, In k [23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg k) = getr R (PMK.reg k)) ->
  1 <= v <= 64 -> rs_saved R M3 sp r -> L5.defined M3 (fb + 16) 16 ->
  PNR.binv s3 -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0x36ee4 M3 model3) K.
Proof.
  intros CTX KONT BR3 X1 X2 X3 X4 X8 X10 X11 X19 X20 XK Hv SV3 ED3 INV3 LEN3 EBB3.
  pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  unfold PNRS.make_ec_spec in MKE.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 BR3) as (PA3 & _ & _ & _ & STK3 & MOK3).
  change (PMSP.pm_scr 7) with 26624 in STK3. pose proof STK3 as (A16 & SLO & SHI & STOP & SDEF3).
  pose proof (L5C.stk_floor _ M3 sp 26624 STK3) as SFL.
  change 0x36ee4 with (pa_make_ec AD).
  apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 7 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 fx3 R3 (sp - 80) 0x38810 v K MKE ltac:(lia) K0 BR3 FOK INCS
           X1 ltac:(split; [lia| reflexivity]) X2 X3 X4 X10 X11 Hv ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub80 sp A16) ED3).
  intros fx4 R4 M4 RP34 EC4 BR4 AG34.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str _ M4 model3 cr3 s3 sm3 _ BR4) as (PA4 & _ & _ & _ & STK4 & MOK4).
  change (PMSP.pm_scr 7) with 26624 in STK4. pose proof (L5C.stk_writable RSEGS _ M4 sp 26624 STK4) as WR4.
  assert (WP4 : L5.writable RSEGS M4 (fb + 40) 416) by (destruct PA4 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
  assert (SV4 : rs_saved R M4 sp r) by (apply (rs_saved_agree R M3 M4 sp r); [intros a m H1 H2; apply AG34; lia|lia|lia| exact SV3]).
  pose proof SV4 as (T8 & T16 & T24 & T32 & T40 & T48 & T56 & T64).
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BUR_20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BUR_21.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BUR_22.
  LeanFeed.pfeed P (PNSRSP.bstE_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 36%nat => r
               | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
               | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => bv_unsigned (getr R (PMK.reg 20)) | 42%nat => bv_unsigned (getr R (PMK.reg 21))
               | 43%nat => bv_unsigned (getr R (PMK.reg 22)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc | rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl; first [exact X2 | exact X8 | exact X19 | exact X20] ]).
  pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y18 & Y19 & Y20 & Y21 & Y22 & MO5)); PMK.pvz_clrT.
  apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 7 LBX sp fb str _ M4 model3 cr3 s3 sm3 _ fx4 fx5 R4 R5 0x38810 0x387f8 M5
           (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR4 FOK INCS MS5 MG5 FRZ5 ltac:(intros a; apply PMK.rng_dec)
           ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO5) ltac:(left; reflexivity)).
  intros BR5.
  apply (rs_fin K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model3 cr3 _ sm3 _ CTX KONT BR5 Y1 Y2);
    [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| exact Y22| | | cbn [PNBO.set_more PNM.b_bb]; exact EBB3].
  { intros k Hk. ksk KS5 Hk. rewrite (PMK.cs_of_preserved R3 R4 k RP34) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk. }
  left. split; [| split; [reflexivity|]; split; [apply bax_cat_add|]].
  { exists v. split; [exact Hv|]. apply (ec_agree M4 M5); [intros i Hi; apply FRZ5; lia|lia|lia| exact EC4]. }
  split; [cbn [PNBO.set_more PNM.b_stk]; exact LEN3| destruct INV3 as (ID & SH); split; [exact ID| exact SH]].
Qed.

(* [comment removed for export] *)
Lemma rs_top LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) -> PNR.binv s1 ->
  exists l c, PNM.b_stk s1 = l ++ [c] /\ PNM.bstate_ok c
    /\ L5.u64_at RSEGS M1 (fb + 40 + 400) (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40)
    /\ L5.u64_at RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) (PNM.bs_pos c)
    /\ L5.writable RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) 8
    /\ 4096 <= PNM.b_sb s1 + 40 * Z.of_nat (length l) /\ PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40 <= sp - 26624
    /\ (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40) mod 8 = 0
    /\ L5.defined M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) 8.
Proof.
  intros BR INV.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 7 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  change (PMSP.pm_scr 7) with 26624 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof INV as (_ & (L1 & _ & _ & _ & OKs)).
  destruct (exists_last (l := PNM.b_stk s1) ltac:(intros X; rewrite X in L1; cbn in L1; lia)) as (l & c & ES).
  exists l, c. split; [exact ES|].
  pose proof (OKs (length l) ltac:(rewrite ES, length_app; cbn; lia)) as OKc. rewrite ES, nth_middle in OKc. split; [exact OKc|].
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _). unfold PNM.OFF_STK in SV1.
  pose proof SV1 as (V0 & V8 & _ & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  rewrite ES, length_app in Hlen, EL, V8. cbn [length] in Hlen, EL, V8.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length l)) in *.
  assert (Hn : 0 <= n /\ n + 1 <= 2 ^ k) by (unfold n; lia).
  assert (TOPIN : b + 40 * n + 40 <= b + 40 * 2 ^ k) by nia.
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in S4.
  split; [replace (b + 40 * n + 40) with (b + 40 * (Z.of_nat (length l + 1))) by (unfold n; lia); replace (fb + 40 + 400) with (fb + 40 + 392 + 8) by lia; exact V8|].
  pose proof (EL (length l) ltac:(lia)) as ET. rewrite nth_middle in ET. fold n in ET. destruct ET as (_ & _ & Tp & _ & _).
  split; [exact Tp|].
  split; [apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 b (40 * 2 ^ k)); [exact DB|lia|lia]|lia|lia]|].
  split; [lia|]. split; [lia|].
  split; [replace (b + 40 * n + 40) with (b + 8 * (5 * n + 5)) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact Hal|].
  apply (L5.defined_sub M1 b (40 * 2 ^ k)); [exact DB|lia|lia].
Qed.

Lemma own_set_stk s l : PNM.bparser_own (PNBO.set_stk s l) = PNM.bparser_own s.
Proof. destruct s; reflexivity. Qed.
Lemma sr_qc_of_brel LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) -> PM.sr_qc (PNM.b_src s1) = PM.sr_qc (PNM.b_src (PNBK.be_s E0)).
Proof. intros (_ & (E & _) & _). exact E. Qed.

(* [comment removed for export] *)
Lemma rs_body2 K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx2 : FPState) R2 (M2 : mem) model2 cr2 s2 sm2 ax2 len ptr n2 :
  rs_ctx K LBX sp r fb e str R cr s sm -> rs_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M2 model2 cr2 s2 sm2 ax2) ->
  getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 80) -> getr R2 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R2 (PMK.reg 9) = Z_to_bv 64 (len - 1) -> getr R2 (PMK.reg 10) = Z_to_bv 64 ptr ->
  getr R2 (PMK.reg 11) = Z_to_bv 64 n2 -> getr R2 (PMK.reg 19) = Z_to_bv 64 (fb + 16) -> getr R2 (PMK.reg 20) = Z_to_bv 64 (fb + 40 + 16) ->
  getr R2 (PMK.reg 21) = Z_to_bv 64 len ->
  (forall k, In k [23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg k) = getr R (PMK.reg k)) ->
  rs_saved R M2 sp r -> PMSP.ec_at RSEGS M2 (fb + 16) e cat ->
  1 <= len <= 2147483647 -> 0 <= n2 <= len - 1 -> n2 < 2 ^ 26 ->
  ((ptr = 0 /\ n2 = 0) \/ PGS.in_blk (PNM.bparser_own s2) ptr n2 \/ (fb + 40 + 368 + 1 <= ptr /\ ptr + n2 <= fb + 40 + 368 + 24)) ->
  L5.defined M2 ptr n2 ->
  PM.unread (PNM.b_src s2) sm2 + 4 <= PM.unread (PNM.b_src s) sm ->
  PNR.binv s2 -> PNR.btop_pos s s2 -> PNM.b_bb s2 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x38780 M2 model2) K.
Proof.
  intros CTX KONT BR2 X2 X3 X4 X8 X9 X10 X11 X19 X20 X21 XK SV2 EC2 Hlen Hn2 Hn26 LOC DEF2 UNR2 INV2 TP02 EBB2.
  pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  unfold PNRS.src_read_spec, PNR.src_read_spec in SRD.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 BR2) as (PA2 & IA2 & GR2 & UN2 & STK2 & MOK2).
  change (PMSP.pm_scr 7) with 26624 in STK2. pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF2). pose proof MOK2 as (Mh2 & Ml2 & Mm2).
  pose proof (L5C.stk_floor _ M2 sp 26624 STK2) as SFL. pose proof (L5C.stk_writable RSEGS _ M2 sp 26624 STK2) as WR2.
  assert (LEN02 : (length (PNM.b_stk s) <= length (PNM.b_stk s2))%nat).
  { destruct TP02 as (l1 & c1 & c1' & TE1 & TE2 & _). rewrite TE1, TE2. rewrite !length_app. cbn [length]. lia. }
  assert (ED2 : L5.defined M2 (fb + 16) 16) by (destruct EC2 as (_ & _ & ED); exact ED).
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 BR2) as (_ & OWNB2 & _).
  assert (Hptr : 0 <= ptr /\ ptr + n2 < 2 ^ 64).
  { destruct LOC as [(-> & ->)|[(B & m & Hin & HB1 & HB2)|X]]; [lia| destruct (OWNB2 B m Hin); unfold hl_ceil in *; lia| lia]. }
  destruct Hptr as (Hptr0 & Hptr1).
  LeanFeed.pfeed P (PNSRSP.bstS_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 46%nat => len | 47%nat => ptr | 48%nat => n2 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc]).
  destruct P as (fx3 & R3 & M3 & MG3 & EQ3w & EQ3 & [(MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y18 & Y22 & FK)|(MS3 & KS3 & Y1 & Y10 & Y11 & FK)]);
    assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w); subst M3.
  - (* [comment removed for export] *)
    pose proof (fork_eq n2 len Hlen ltac:(lia) FK) as En2. clear FK.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx2 fx3 R2 R3 0x38780 0x370d0 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 MG3 ltac:(intros a Ha _; apply EQ3; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3.
    change 0x370d0 with (pa_src_read AD).
    apply (PNBK4.brel_src_read_d RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx3 R3 (sp - 80) 0x3879c (sp - 69) 1 K SRD
             ltac:(lia) K0 BR3 FOK INCS Y1 ltac:(split; [lia| reflexivity]) ltac:(ksl KS3; exact X2) ltac:(ksl KS3; exact X3) ltac:(ksl KS3; exact X4)
             ltac:(rewrite Y10; replace (fb + 40 + 16) with (fb + 56) by lia; reflexivity) Y11 Y12
             ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub80 sp A16) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros fx4 R4 M4 src4 sm4 d RP34 Z10 Hd UNR4 DEFc BR4 AG34 DK34.
    assert (SV4 : rs_saved R M4 sp r) by (apply (rs_saved_agree R M2 M4 sp r); [intros a m H1 H2; apply AG34; lia| lia| lia| exact SV2]).
    assert (EC4 : PMSP.ec_at RSEGS M4 (fb + 16) e cat) by (apply (ec_agree M2 M4); [apply AG34; lia|lia|lia| exact EC2]).
    assert (INV4 : PNR.binv (PNM.with_srcB s2 src4)) by exact INV2.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str _ M4 model2 cr2 _ sm4 ax2 BR4) as (PA4 & IA4 & GR4 & UN4 & STK4 & MOK4).
    change (PMSP.pm_scr 7) with 26624 in STK4. pose proof (L5C.stk_writable RSEGS _ M4 sp 26624 STK4) as WR4.
    assert (Hd01 : d = 0 \/ d = 1) by lia. destruct Hd01 as [->| ->].
    + (* [comment removed for export] *)
      LeanFeed.pfeed P (PNSRSP.bstT0_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 46%nat => len | 47%nat => ptr | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc | rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl; first [exact Y18 | exact Y22 | ksl KS3; assumption] ]).
      pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG5 & EQ5w & EQ5 & MS5 & KS5 & W1 & W10 & W11)); PMK.pvz_clrT.
      assert (EM5 : M5 = M4) by (apply functional_extensionality; exact EQ5w). subst M5.
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str _ M4 model2 cr2 _ sm4 ax2 fx4 fx5 R4 R5 0x3879c 0x36ee4 M4 (fun _ => False) K
               ltac:(lia) BR4 FOK INCS MS5 MG5 ltac:(intros a Ha _; apply EQ5; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
      intros BR5.
      apply (rs_err K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M4 model2 cr2 _ sm4 ax2 1 CTX KONT BR5 W1); [| | | | exact W10| exact W11| | | | lia| exact SV4| | exact INV4| cbn [PNM.with_srcB PNM.b_stk]; exact LEN02| cbn [PNM.with_srcB PNM.b_bb]; exact EBB2].
      all: try (ksl KS5; rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl; first [exact Y18 | exact Y22 | ksl KS3; first [assumption | replace (fb + 40 + 16) with (fb + 56) by lia; assumption]]).
      { intros k Hk. ksk KS5 Hk. rewrite (PMK.cs_of_preserved R3 R4 k RP34) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). ksk KS3 Hk. apply XK. exact Hk. }
      { destruct EC4 as (_ & _ & ED). exact ED. }
    + (* [comment removed for export] *)
      destruct (rs_top LBX sp fb str _ M4 model2 cr2 _ sm4 ax2 BR4 INV4) as (l & c & ES & OKc & VE & VP & WP & E0 & E1 & EAL & DP).
      cbn [PNM.with_srcB PNM.b_sb PNM.b_stk PNM.b_src] in ES, VE, VP, WP, E0, E1, EAL, DP.
      set (et := PNM.b_sb s2 + 40 * Z.of_nat (length l)) in *.
      pose proof OKc as (OKm & OKl & POS & OKt & OKi).
      assert (WP4 : L5.writable RSEGS M4 (fb + 40) 416) by (destruct PA4 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
      pose proof SV4 as (T8 & T16 & T24 & T32 & T40 & T48 & T56 & T64).
      pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9.
      pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19.
      pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BUR_20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BUR_21.
      pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BUR_22.
      LeanFeed.pfeed P (PNSRSP.bstT1_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 36%nat => r
                   | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
                   | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => bv_unsigned (getr R (PMK.reg 20)) | 42%nat => bv_unsigned (getr R (PMK.reg 21))
                   | 43%nat => bv_unsigned (getr R (PMK.reg 22)) | 45%nat => et + 40 | 46%nat => len | 47%nat => ptr | 49%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc
                             | replace (et + 40 - 24) with (et + 16) by lia; first [exact VP | exact WP]
                             | rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl; first [exact Y18 | exact Y22 | ksl KS3; first [assumption | replace (fb + 40 + 16) with (fb + 56) by lia; assumption]] ]).
      pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP;
                    destruct pvzP as (MG5 & _ & FRZ5 & MS5 & KS5 & W1 & W2 & W8 & W9 & W10 & W11 & W18 & W19 & W20 & W21 & W22)); PMK.pvz_clrT.
      destruct (PMCG.u64_of_defined RSEGS M5 (et + 16) ltac:(lia) ltac:(lia)) as (v' & Hv' & CP5).
      { apply (L5.defined_grows M4 M5 _ _ MG5). exact DP. }
      apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 7 LBX sp fb str _ M4 model2 cr2 _ sm4 ax2 fx4 fx5 R4 R5 0x3879c 0x387f8 M5
               (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c v' K ltac:(lia) BR4 FOK INCS MS5 MG5 FRZ5 ltac:(intros a; apply PMK.rng_dec) ES);
        [cbn [PNM.with_srcB PNM.b_sb]; intros a Pa; right; lia| cbn [PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s2 + 40 * Z.of_nat (length l) + 16) with (et + 16) by lia; exact CP5| exact Hv'|].
      intros BR5.
      pose proof (sr_qc_of_brel LBX sp fb str _ M4 model2 cr2 _ sm4 ax2 BR4) as QC4. pose proof (sr_qc_of_brel LBX sp fb str _ M2 model2 cr2 _ sm2 ax2 BR2) as QC2.
      cbn [PNBK.be_s PNM.with_srcB PNM.b_src] in QC4, QC2.
      apply (rs_fin K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model2 cr2 _ sm4 ax2 CTX KONT BR5 W1 W2);
        [| | exact W8| exact W9| exact W18| exact W19| exact W20| exact W21| exact W22| | | cbn [PNBO.set_stk PNM.with_srcB PNM.b_bb]; exact EBB2].
      { ksl KS5. rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl. ksl KS3. exact X3. }
      { ksl KS5. rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl. ksl KS3. exact X4. }
      { intros k Hk. ksk KS5 Hk. rewrite (PMK.cs_of_preserved R3 R4 k RP34) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). ksk KS3 Hk. apply XK. exact Hk. }
      right. split; [apply (ec_agree M4 M5); [intros i Hi; apply FRZ5; lia|lia|lia| exact EC4]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV4| exact ES| unfold PNM.bstate_ok; cbn; lia| reflexivity]|].
      unfold PNR.bprog_rs. split; [| split].
      { apply (PNBK2.btop_pos_trans s (PNM.with_srcB s2 src4)); [exact TP02|].
        apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| unfold PNM.bstate_ok; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity]. }
      { cbn [PNBO.set_stk PNM.with_srcB PNM.b_src]. lia. }
      exists ptr, (len - 1). split; [exact W10|]. split; [exact W11|]. split; [lia|].
      unfold PNR.o_tb, PNR.o_p, PMSP.o_p, PNM.OFF_TB. cbn [pa_off_p AD PnLayoutS_u.ADDR_S]. rewrite own_set_stk, (PNBK.own_with_src s2 src4 ltac:(rewrite QC4, QC2; reflexivity)).
      subst n2. split; [| exact LOC].
      apply (L5.defined_grows M4 M5 _ _ MG5).
      destruct LOC as [(-> & En)|LOC'].
      { intros i Hi. lia. }
      apply (DK34 ptr (len - 1) ltac:(lia) ltac:(lia)); [| exact DEF2].
      destruct LOC' as [IB|X]; [left; exact IB| right; lia].
  - (* [comment removed for export] *)
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx2 fx3 R2 R3 0x38780 0x36ee4 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 MG3 ltac:(intros a Ha _; apply EQ3; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3.
    apply (rs_err K LBX sp r fb cat e str R M model cr s sm ax fx3 R3 M2 model2 cr2 s2 sm2 ax2 1 CTX KONT BR3 Y1); [| | | | exact Y10| exact Y11| | | | lia| exact SV2| exact ED2| exact INV2| exact LEN02| exact EBB2].
    all: try (ksl KS3; first [assumption | replace (fb + 40 + 16) with (fb + 56) by lia; assumption]).
    intros k Hk. ksk KS3 Hk. apply XK. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem read_string_ok : PNRS.read_string_spec L HI.
Proof.
  unfold PNRS.read_string_spec, PNR.read_string_spec, PNR.brun_spec_fb.
  intros fb fx R M model K LBX cr sp r cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 7) with 26624 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (A10 & A11). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  unfold PNR.o_p, PNR.o_ec, PMSP.o_p, PMSP.o_ec in A10, A11, EC0. cbn [pa_off_p pa_off_ec AD PnLayoutS_u.ADDR_S] in A10, A11, EC0.
  pose proof (L5C.stk_floor _ M sp 26624 STK) as SFL. pose proof (L5C.stk_writable RSEGS _ M sp 26624 STK) as WR.
  pose proof (PNBK.brel_init RSEGS AD AN L HI 7 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  change (PMSP.pm_scr 7) with 26624 in BR0.
  assert (CTX : rs_ctx K LBX sp r fb e str R cr s sm).
  { split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|].
    split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp|]. split; [exact CRED|]. split; [exact INV|]. split; [exact UNR| exact He]. }
  assert (KONT' : rs_kont K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  unfold PNRS.src_read_spec, PNR.src_read_spec in SRD. unfold PNRS.read_span_spec, PNR.read_span_spec in RSP.
  unfold PMSP.cfg. cbn [PNL.pn_read_string AN PnLayoutS_u.NADDR_S].
  LeanFeed.pfeed P (PNSRSP.bstA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X19 & X20 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
  change (mkCfg (@mkst fx R (Z_to_bv 64 0x3871c) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x3871c M model).
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x3871c 0x370d0 M1 (fun a => sp - 64 <= a < sp - 64 + 64) K
           ltac:(lia) BR0 FOK INCS MS1 MG1 FRZ1 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)).
  intros BR1.
  assert (SV1 : rs_saved R M1 sp r).
  { unfold rs_saved. rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia.
    split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32|]. split; [exact C40|]. split; [exact C48|]. split; [exact C56| exact C64]. }
  assert (EC1 : PMSP.ec_at RSEGS M1 (fb + 16) e cat) by (apply (ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]).
  (* [comment removed for export] *)
  change 0x370d0 with (pa_src_read AD).
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 7 LBX sp fb str _ M1 model cr s sm ax fx1 R1 (sp - 80) 0x38760 (sp - 68) 4 K SRD
           ltac:(lia) K0 BR1 FOK INCS X1 ltac:(split; [lia| reflexivity]) X2 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(rewrite X10; replace (fb + 40 + 16) with (fb + 56) by lia; reflexivity) X11 X12
           ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub80 sp A16) ltac:(lia) ltac:(lia) ltac:(lia)).
  intros fx2 R2 M2 src2 sm2 d RP12 Y10 Hd UNR2 DEFq BR2 AG12.
  assert (SV2 : rs_saved R M2 sp r) by (apply (rs_saved_agree R M1 M2 sp r); [intros a m H1 H2; apply AG12; lia| lia| lia| exact SV1]).
  assert (EC2 : PMSP.ec_at RSEGS M2 (fb + 16) e cat) by (apply (ec_agree M1 M2); [apply AG12; lia|lia|lia| exact EC1]).
  assert (ED2 : L5.defined M2 (fb + 16) 16) by (destruct EC2 as (_ & _ & ED); exact ED).
  assert (INV2 : PNR.binv (PNM.with_srcB s src2)) by exact INV.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model cr _ sm2 ax BR2) as (PA2 & IA2 & GR2 & UN2 & STK2 & MOK2).
  change (PMSP.pm_scr 7) with 26624 in STK2. pose proof (L5C.stk_writable RSEGS _ M2 sp 26624 STK2) as WR2.
  cbn [PNM.with_srcB PNM.b_src] in UN2.
  assert (ERR : forall (fx3 : FPState) R3 v,
            msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x38760) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x36ee4) M2 (seg_rom RSEGS)) ->
            (forall k, In k [2; 3; 4; 8; 19; 20; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg k) = getr R2 (PMK.reg k)) ->
            getr R3 (PMK.reg 1) = Z_to_bv 64 0x38810 -> getr R3 (PMK.reg 10) = Z_to_bv 64 (fb + 16) -> getr R3 (PMK.reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x38760 M2 model) K).
  { intros fx3 R3 v MS3 KS3 W1 W10 W11 Hv.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model cr _ sm2 ax fx2 fx3 R2 R3 0x38760 0x36ee4 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 (mem_grows_refl M2) ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3.
    apply (rs_err K LBX sp r fb cat e str R M model cr s sm ax fx3 R3 M2 model cr _ sm2 ax v CTX KONT' BR3 W1); [| | | | exact W10| exact W11| | | | exact Hv| exact SV2| exact ED2| exact INV2| cbn [PNM.with_srcB PNM.b_stk]; lia| reflexivity].
    all: try (ksl KS3; rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; first [assumption | PMK.rk | rewrite X20; replace (fb + 40 + 16) with (fb + 56) by lia; reflexivity]).
    intros k Hk. ksk KS3 Hk. rewrite (PMK.cs_of_preserved R1 R2 k RP12) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). ksk KS1 Hk. reflexivity. }
  assert (Hd4 : d <= 3 \/ d = 4) by lia. destruct Hd4 as [Hd3| ->].
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSRSP.bstRe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 44%nat => d | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc | rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; first [assumption | PMK.rk] ]).
    pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & EQ3w & EQ3 & MS3 & KS3 & W1 & W10 & W11)); PMK.pvz_clrT.
    assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w). subst M3.
    apply (ERR fx3 R3 1 MS3); [intros k Hk; apply KS3; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact W1| exact W10| exact W11| lia].
  - (* [comment removed for export] *)
    destruct (u32_of_defined M2 (sp - 68) ltac:(lia) ltac:(lia) DEFq) as (w & Hw & U32).
    assert (Hw3 : w = 0 \/ 2147483648 <= w \/ 1 <= w <= 2147483647) by lia. destruct Hw3 as [->|[HwN|HwP]].
    + (* [comment removed for export] *)
      LeanFeed.pfeed P (PNSRSP.bstRz_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc | rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; first [assumption | PMK.rk] ]).
      pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & EQ3w & EQ3 & MS3 & KS3 & W1 & W10 & W11 & W21)); PMK.pvz_clrT.
      assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w). subst M3.
      apply (ERR fx3 R3 5 MS3); [intros k Hk; apply KS3; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact W1| exact W10| exact W11| lia].
    + (* [comment removed for export] *)
      LeanFeed.pfeed P (PNSRSP.bstRn_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 46%nat => w | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc | rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; first [assumption | PMK.rk] ]).
      pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & EQ3w & EQ3 & MS3 & KS3 & W1 & W10 & W11)); PMK.pvz_clrT.
      assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w). subst M3.
      apply (ERR fx3 R3 5 MS3); [intros k Hk; apply KS3; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact W1| exact W10| exact W11| lia].
    + (* [comment removed for export] *)
      LeanFeed.pfeed P (PNSRSP.bstRp_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 46%nat => w | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRSP.aligned; PMK.sc | rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; first [assumption | PMK.rk] ]).
      pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & EQ3w & EQ3 & MS3 & KS3 & W1 & W9 & W10 & W11 & W12 & W21)); PMK.pvz_clrT.
      assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w). subst M3.
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model cr _ sm2 ax fx2 fx3 R2 R3 0x38760 0x39290 M2 (fun _ => False) K
               ltac:(lia) BR2 FOK INCS MS3 (mem_grows_refl M2) ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
      intros BR3.
      change 0x39290 with (pa_read_span AD).
      apply (PNBK3.brel_read_span RSEGS AD AN L HI KH 7 LBX sp fb str _ M2 model cr _ sm2 ax fx3 R3 (sp - 80) 0x38780 (w - 1) K twok_S RSP
               ltac:(lia) K0 BR3 FOK INCS ltac:(cbn [PNBK.be_s PNBK.be_cr]; exact CRED) W1 ltac:(split; [lia| reflexivity])
               ltac:(ksl KS3; rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; exact X2)
               ltac:(ksl KS3; rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; PMK.rk)
               ltac:(ksl KS3; rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; PMK.rk)
               ltac:(rewrite W10; replace (fb + 40 + 16) with (fb + 56) by lia; reflexivity) W11 W12
               ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub80 sp A16) ltac:(cbn [PNM.with_srcB PNM.b_src]; lia)).
      intros fx4 R4 M4 model4 src4 tb4 tg4 sm4 cr4 ptr n RP34 Z10 Z11 Hn Hn26 LOC DEF4 UNR4 BR4 AG34.
      cbn [PNM.with_srcB PNM.b_src] in UNR4.
      apply (rs_body2 K LBX sp r fb cat e str R M model cr s sm ax fx4 R4 M4 model4 cr4 _ sm4 ax w ptr n CTX KONT' BR4);
        [| | | | | exact Z10| exact Z11| | | | | | | exact HwP| exact Hn| exact Hn26| exact LOC| exact DEF4| cbn [PNM.with_src_tb PNM.with_srcB PNM.b_src]; lia| exact INV| | reflexivity].
      all: try (rewrite (PMK.cs_of_preserved R3 R4 _ RP34) by PMK.inl; first [exact W9 | exact W21 | ksl KS3; rewrite (PMK.cs_of_preserved R1 R2 _ RP12) by PMK.inl; first [assumption | PMK.rk | rewrite X20; replace (fb + 40 + 16) with (fb + 56) by lia; reflexivity]]).
      { intros k Hk. rewrite (PMK.cs_of_preserved R3 R4 k RP34) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). ksk KS3 Hk.
        rewrite (PMK.cs_of_preserved R1 R2 k RP12) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). ksk KS1 Hk. reflexivity. }
      { apply (rs_saved_agree R M2 M4 sp r); [intros a m H1 H2; apply AG34; lia| lia| lia| exact SV2]. }
      { apply (ec_agree M2 M4); [apply AG34; lia|lia|lia| exact EC2]. }
      { destruct (PNBK2.btop_pos_refl s INV) as (l & c & c' & E1 & E2 & Q). exists l, c, c'. cbn [PNM.with_src_tb PNM.with_srcB PNM.b_stk].
        split; [exact E1|]. split; [exact E2| exact Q]. }
Qed.

End WithHeap.
End PNSRST.
