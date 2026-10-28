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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSReadEnP_u
     Bs0_code_36690_36694_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSEN.
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
Lemma mod16_sub64 sp : sp mod 16 = 0 -> (sp - 64) mod 16 = 0.
Proof. intros H. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.
Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.
Lemma tb0_short n : Z.testbit (2 * n) 0 = false.
Proof. apply Z.testbit_even_0. Qed.
Lemma tb0_long c : 0 <= c -> c mod 2 = 0 -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros Hc He. rewrite Z.testbit_true by lia. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite (Z.mod_mod_divide (c + 1) 256 2) by (exists 128; reflexivity). rewrite <- Zplus_mod_idemp_l, He. reflexivity.
Qed.
Lemma lor_small a b : 0 <= a <= 64 -> 0 <= b <= 1 -> 0 <= Z.lor a b <= 65 /\ (Z.lor a b = 0 -> a = 0 /\ b = 0).
Proof.
  intros Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)). pose proof (proj2 (Z.land_nonneg a b) ltac:(lia)). pose proof (Z.add_lor_land a b).
  split; [lia|]. intros E. apply Z.lor_eq_0_iff. exact E.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 6).
Abbreviation pot := (PNR.pot_bparser L).

Hypothesis RCS : PNRS.read_cstring_spec L HI.
Hypothesis VAL : PMS.validate_spec L.
Hypothesis MKE : PNRS.make_ec_spec L HI.

(* [comment removed for export] *)
Definition en_kont (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.brun_post RSEGS AD AN false PNR.bprog_name R' M' fb s s' str sm sm' ax ax' cat e ->
      L5C.hpres L LBX sp (PMSP.pm_scr 6) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) (pot s') ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition en_ctx (t : Z) (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb e : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit)
           (s : PNM.bpst) (sm : PM.strm) : Prop :=
  (t = 0 \/ t = 1) /\ K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr /\ PNR.binv s /\ PM.unread (PNM.b_src s) sm < 2 ^ 26 /\ 0 <= e <= 64.
Definition en_saved (R : bvmap 5 word) (M1 : mem) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) r /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))).
Lemma en_saved_agree R (M1 M2 : mem) sp r :
  (forall a n, sp - 40 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n) -> 0 <= sp - 64 -> sp <= 2 ^ 64 -> en_saved R M1 sp r -> en_saved R M2 sp r.
Proof.
  intros AG H1 H2 (S8 & S16 & S24 & S32 & S40). unfold en_saved.
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- L5.u64_at _ M2 ?a ?v => apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| assumption]
  end.
Qed.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc]).

(* [comment removed for export] *)
Lemma en_fin t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  en_ctx t K LBX sp r fb e str R cr s sm -> en_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R5 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R5 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  (   ((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M5 (fb + 16) v (pa_errcat_obj AD)) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true
       /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bprog_name R5 M5 s s5 sm sm5)) ->
  PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x37440 M5 model5) K.
Proof.
  intros (Ht & K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He) KONT BR Y1 Y2 Y3 Y4 Y8 Y9 Y18 Y19 YK POST BB.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx5 R5 M5 0x37440 W_36734 r F_36734 eq_refl D_36734); [exact Y1| lia| exact Hr2]. }
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite Y8; apply Z_to_bv_bv_unsigned | rewrite Y9; apply Z_to_bv_bv_unsigned | rewrite Y18; apply Z_to_bv_bv_unsigned
            | rewrite Y19; apply Z_to_bv_bv_unsigned | apply YK; cbn; tauto ].
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
Lemma nb_facts (M1 : mem) fb s1 :
  bparser_at M1 (fb + 40) (fb + 472) s1 ->
  match PNM.b_nb s1 with
  | PM.VShort n => 0 <= n <= 22 /\ L5.u8_at RSEGS M1 (fb + 40 + 344) (2 * n) /\ L5.defined M1 (fb + 384) 24
  | PM.VLong c n p => L5.u8_at RSEGS M1 (fb + 40 + 344) ((c + 1) mod 256) /\ L5.u64_at RSEGS M1 (fb + 40 + 352) n /\ L5.u64_at RSEGS M1 (fb + 40 + 360) p
                      /\ 0 <= n < c /\ 26 <= c <= 2 ^ 27 /\ c mod 2 = 0 /\ L5.defined M1 p c /\ L5.u64_at RSEGS M1 (fb + 384) (c + 1) /\ L5.defined M1 (fb + 384) 24
  end.
Proof.
  intros PA. pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NB & _). unfold PNM.OFF_NB in NB.
  destruct (PNM.b_nb s1) as [n|c n p]; destruct NB as (D & _ & NB').
  - destruct NB' as (Hn & U8). split; [exact Hn|]. split; [exact U8| replace (fb + 384) with (fb + 40 + 344) by lia; exact D].
  - destruct NB' as (U0 & U8 & U16 & Hn & Hc & He & Dp & _).
    split; [apply (PMF.u8_of_u64 RSEGS M1 _ (c + 1) ltac:(lia) U0)|].
    split; [replace (fb + 40 + 352) with (fb + 40 + 344 + 8) by lia; exact U8|].
    split; [replace (fb + 40 + 360) with (fb + 40 + 344 + 16) by lia; exact U16|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. split; [exact Dp|].
    split; [replace (fb + 384) with (fb + 40 + 344) by lia; exact U0| replace (fb + 384) with (fb + 40 + 344) by lia; exact D].
Qed.

(* [comment removed for export] *)
Lemma en_body t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx2 : FPState) R2 (M2 : mem) model2 cr2 s1 s2 sm2 ax2 :
  en_ctx t K LBX sp r fb e str R cr s sm -> en_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M2 model2 cr2 s2 sm2 ax2) ->
  getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr R2 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R2 (PMK.reg 9) = Z_to_bv 64 (fb + 16) ->
  getr R2 (PMK.reg 18) = Z_to_bv 64 (fb + 464) -> getr R2 (PMK.reg 19) = Z_to_bv 64 t ->
  (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg k) = getr R (PMK.reg k)) ->
  en_saved R M2 sp r ->
  PNR.btop_pos s s1 -> PM.unread (PNM.b_src s1) sm <= PM.unread (PNM.b_src s) sm -> PM.vs_size (PNM.b_nb s1) = 0 ->
  PNM.b_bb s2 = PNM.b_bb s ->
  (   ((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M2 (fb + 16) v (pa_errcat_obj AD)) /\ PNM.b_more s2 = 0 /\ PNST.bax_cat ax2 = true
       /\ (length (PNM.b_stk s1) <= length (PNM.b_stk s2))%nat /\ PNR.binv s2)
   \/ (PMSP.ec_at RSEGS M2 (fb + 16) e cat /\ PNR.binv s2 /\ PNR.bprog_cs 0 R2 M2 s1 s2 sm sm2)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x37394 M2 model2) K.
Proof.
  intros CTX KONT BR2 X2 X3 X4 X8 X9 X18 X19 XK SV2 TP01 LE01 SZ01 EBB2 POST.
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  assert (AL16 : (fb + 16) mod 8 = 0) by (replace (fb + 16) with (fb + 8 * 2) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  assert (AL464 : (fb + 464) mod 8 = 0) by (replace (fb + 464) with (fb + 8 * 58) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  unfold PNRS.make_ec_spec in MKE. unfold PMS.validate_spec, PMSP.validate_spec, PMSP.scan_spec in VAL. cbn [pa_validate AD PnLayoutS_u.ADDR_S] in VAL.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 6 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 BR2) as (PA2 & IA2 & GR2 & UN2 & STK2 & MOK2).
  change (PMSP.pm_scr 6) with 24576 in STK2. pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF2). pose proof MOK2 as (Mh2 & Ml2 & Mm2).
  pose proof (L5C.stk_floor _ M2 sp 24576 STK2) as SFL. pose proof (L5C.stk_writable RSEGS _ M2 sp 24576 STK2) as WR2.
  pose proof SV2 as (S8 & S16 & S24 & S32 & S40).
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19.
  (* [comment removed for export] *)
  assert (ECV : exists ecv, 0 <= ecv <= 64 /\ L5.u32_at RSEGS M2 (fb + 16) ecv
            /\ (ecv = 0 -> PMSP.ec_at RSEGS M2 (fb + 16) e cat /\ PNR.binv s2 /\ PNR.bprog_cs 0 R2 M2 s1 s2 sm sm2)).
  { destruct POST as [((v & Hv & (E1 & _)) & _)|((E0 & E8 & ED0) & INV & PROG)].
    - exists v. split; [lia|]. split; [exact E1|]. intros ->. lia.
    - exists e. split; [exact He|]. split; [exact E0|]. intros _. split; [split; [exact E0|]; split; [exact E8| exact ED0]|]. split; [exact INV| exact PROG]. }
  destruct ECV as (ecv & Hecv & U32 & OKP).
  pose proof (lor_small ecv t Hecv ltac:(lia)) as (LOR1 & LOR2).
  LeanFeed.pfeed P (PNSENP.benR_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => t | 36%nat => fb + 16
               | 37%nat => r | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9)) | 40%nat => bv_unsigned (getr R (PMK.reg 18))
               | 41%nat => bv_unsigned (getr R (PMK.reg 19)) | 44%nat => ecv | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc]).
  destruct P as (fx3 & R3 & M3 & MG3 & EQ3w & EQ3 & [(MS3 & KS3 & _ & LT)|PX]); assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w); subst M3.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in LT by lia. destruct (LOR2 ltac:(lia)) as (-> & ->).
    destruct (OKP eq_refl) as (EC2 & INV2 & (TP12 & LT12 & SZ12)). clear OKP POST.
    unfold PNR.bcs_str in SZ12. cbn [Z.eqb] in SZ12.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 6 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx2 fx3 R2 R3 0x37394 0x373a0 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 MG3 ltac:(intros a Ha _; apply EQ3; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3.
    (* [comment removed for export] *)
    assert (VCALL : forall (fx4 : FPState) R4 p n,
              msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 0x373a0) M2 (seg_rom RSEGS)) (@mkst fx4 R4 (Z_to_bv 64 0x384bc) M2 (seg_rom RSEGS)) ->
              (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (PMK.reg k) = getr R3 (PMK.reg k)) ->
              getr R4 (PMK.reg 1) = Z_to_bv 64 0x373c4 -> getr R4 (PMK.reg 10) = Z_to_bv 64 p -> getr R4 (PMK.reg 11) = Z_to_bv 64 n ->
              p = PM.vs_data (fb + 384) (PNM.b_nb s2) -> n = PM.vs_size (PNM.b_nb s2) -> L5.defined M2 p n -> 0 <= n < 2 ^ 26 -> 4096 <= p ->
              (sp - 64 <= p \/ p + n <= sp - 64 - 12288) -> p + n <= 2 ^ 47 ->
              srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0x373a0 M2 model2) K).
    { intros fx4 R4 p n MS4 KS4 Q1 Q10 Q11 Hp Hn DEF Gn2 Gp2 PLOC Hpn.
      pose proof BR3 as ((_ & _ & _ & _ & BASE3 & _) & _ & _ & _ & _ & _ & HH3 & STK3 & _). cbn [PNBK.be_M PNBK.be_s PNBK.be_cr PNBK.be_model] in BASE3, HH3, STK3.
      change (PMSP.pm_scr 6) with 24576 in STK3.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh2| exact Ml2| exact MS4|].
      change (mkCfg (@mkst fx4 R4 (Z_to_bv 64 0x384bc) M2 (seg_rom RSEGS)) model2) with (@PMSP.cfg RSEGS fx4 R4 0x384bc M2 model2).
      apply (VAL fx4 R4 M2 model2 K p n (sp - 64) 0x373c4 Mh2 Ml2 K0).
      { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact Q1|]. split; [split; [lia| reflexivity]|].
        split; [rewrite (KS4 2%nat) by (cbn; tauto); PMK.rk|]. split; [rewrite (KS4 3%nat) by (cbn; tauto); PMK.rk|]. split; [rewrite (KS4 4%nat) by (cbn; tauto); PMK.rk|].
        apply (PMK.stk_call L M2 sp 24576 (sp - 64) (PMSP.pm_scr 0) STK3); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact (mod16_sub64 sp A16)]. }
      { rewrite L5K.rl10. exact Q10. } { rewrite L5K.rl11. exact Q11. } { lia. } { lia. } { lia. } { lia. } { exact DEF. }
      { unfold PMSP.pm_scr. lia. } { exact BASE3. }
      intros fx5 R5 M5 RP45 FB5 MG5.
      assert (FRZ5 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 - 12288 <= i < sp - 64) -> M5 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)).
      { intros i Hi N. apply FB5. rewrite L5.unsigned_lit by exact Hi. intros r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply N. unfold PMSP.pm_scr in Hr. lia. }
      pose proof (PNBK.brel_stack_only RSEGS AD AN L HI KH 6 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 M5 (fun a => sp - 64 - 12288 <= a < sp - 64)
                    ltac:(lia) BR3 FOK INCS MG5 FRZ5 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)) as BR5.
      destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 6 LBX sp fb str _ M5 model2 cr2 s2 sm2 ax2 BR5) as (PA5 & _ & _ & _ & STK5 & _).
      change (PMSP.pm_scr 6) with 24576 in STK5. pose proof (L5C.stk_writable RSEGS _ M5 sp 24576 STK5) as WR5.
      assert (AG25 : forall a m, sp - 64 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M2 M5 a m).
      { intros a m H1 H2 i Hi. apply FRZ5; lia. }
      idtac.
      pose proof (bv_unsigned_in_range _ (getr R5 (PMK.reg 11))) as BUR5_11.
      LeanFeed.pfeed P (PNSENP.benC_conc fx5 R5 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => 0 | 36%nat => fb + 16
                   | 46%nat => bv_unsigned (getr R5 (PMK.reg 11)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned
                             | rewrite (PMK.cs_of_preserved R4 R5 _ RP45) by PMK.inl; rewrite (KS4 _) by (cbn; tauto); PMK.rk ]).
      destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & [(MS6 & KS6)|(MS6 & KS6 & Z1 & Z10 & Z11)]); assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w); subst M6.
      + (* [comment removed for export] *)
        apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 6 LBX sp fb str _ M5 model2 cr2 s2 sm2 ax2 fx5 fx6 R5 R6 0x373c4 0x373cc M5 (fun _ => False) K
                 ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
        intros BR6.
        pose proof BR6 as ((PA6 & _ & VIS6 & _ & BASE6 & _) & _). cbn [PNBK.be_M PNBK.be_s] in PA6, VIS6, BASE6.
        unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA6, VIS6. cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in PA6, VIS6.
        pose proof BASE6 as (IMG6 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG6.
        pose proof PA6 as (_ & PD6 & _ & _ & _ & CM6 & _).
        assert (WP6 : L5.writable RSEGS M5 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD6|lia|lia]).
        assert (SV6 : en_saved R M5 sp r).
        { apply (en_saved_agree R M2 M5 sp r); [|lia|lia| exact SV2]. intros a m H1 H2. apply AG25; lia. }
        pose proof SV6 as (T8 & T16 & T24 & T32 & T40).
        pose proof (nb_facts M5 fb s2 PA6) as NBF.
        assert (KEY : forall (fx7 : FPState) R7 (M7 : mem),
                  msteps RSEGS (@mkst fx6 R6 (Z_to_bv 64 0x373cc) M5 (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0x37440) M7 (seg_rom RSEGS)) -> mem_grows M5 M7 ->
                  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 56 <= i < sp - 56 + 16) -> ~ (fb + 40 + 8 <= i < fb + 40 + 8 + 1) -> M7 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i)) ->
                  (forall k, In k [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (PMK.reg k) = getr R6 (PMK.reg k)) ->
                  getr R7 (PMK.reg 1) = Z_to_bv 64 r -> getr R7 (PMK.reg 2) = Z_to_bv 64 sp ->
                  getr R7 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R7 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
                  getr R7 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R7 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
                  L5.u8_at RSEGS M7 (fb + 40 + 8) 1 ->
                  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0x373cc M5 model2) K).
        { intros fx7 R7 M7 MS7 MG7 FRZ7 KS7 W1 W2 W8 W9 W18 W19 MO7.
          apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 6 LBX sp fb str _ M5 model2 cr2 s2 sm2 ax2 fx6 fx7 R6 R7 0x373cc 0x37440 M7
                   (fun a => (sp - 56 <= a < sp - 56 + 16) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1)) 1 K ltac:(lia) BR6 FOK INCS MS7 MG7
                   ltac:(intros a Ha N; apply FRZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
                   ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)
                   ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO7) ltac:(right; reflexivity)).
          intros BR7.
          apply (en_fin _ K LBX sp r fb cat e str R M model cr s sm ax fx7 R7 M7 model2 cr2 _ sm2 ax2 CTX KONT BR7 W1 W2); [| | exact W8| exact W9| exact W18| exact W19| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; exact EBB2].
          { rewrite (KS7 3%nat) by (cbn; tauto). PMK.rk. } { rewrite (KS7 4%nat) by (cbn; tauto). PMK.rk. }
          { intros k Hk. rewrite (KS7 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS6 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
            rewrite (PMK.cs_of_preserved R4 R5 k RP45) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
            rewrite (KS4 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS3 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk. }
          right. split.
          { apply (ec_agree M5 M7); [intros i Hi; apply FRZ7; lia|lia|lia|]. apply (ec_agree M2 M5); [apply AG25; lia|lia|lia| exact EC2]. }
          split; [destruct INV2 as (ID & SH); split; [exact ID| exact SH]|].
          unfold PNR.bprog_name. cbn [PNBO.set_more PNM.b_src PNM.b_stk].
          split; [apply (PNBK2.btop_pos_trans s s1); [exact TP01| destruct TP12 as (l & c & c' & E1 & E2 & Q); exists l, c, c'; cbn [PNBO.set_more PNM.b_stk]; split; [exact E1|]; split; [exact E2| exact Q]]| lia]. }
        destruct (PNM.b_nb s2) as [n2|c2 n2 p2] eqn:ENB2.
        * destruct NBF as (Hn2 & B0 & D24).
          LeanFeed.pfeed P (PNSENP.benKS_conc fx6 R6 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => 0 | 36%nat => fb + 16
                       | 37%nat => r | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9)) | 40%nat => bv_unsigned (getr R (PMK.reg 18))
                       | 41%nat => bv_unsigned (getr R (PMK.reg 19)) | 42%nat => 2 * n2 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | apply tb0_short | rewrite (KS6 _) by PMK.inl; rewrite (PMK.cs_of_preserved R4 R5 _ RP45) by PMK.inl; rewrite (KS4 _) by (cbn; tauto); PMK.rk ]).
          pvz_hg ltac:(idtac; destruct P as (fx7 & R7 & M7 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG7 & _ & FRZ7 & MS7 & KS7 & V1 & V2 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V18 & V19 & MO7 & _)); PMK.pvz_clrT.
          apply (KEY fx7 R7 M7 MS7 MG7 FRZ7); [intros k Hk; apply KS7; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact V1| exact V2| exact V8| exact V9| exact V18| exact V19| exact MO7].
        * destruct NBF as (B0 & U8 & U16 & Hn2 & Hc2 & He2 & Dp & U0 & D24).
          destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 6 LBX sp fb str _ M5 model2 cr2 s2 sm2 ax2 BR6) as (_ & OWNB6 & _).
          assert (Hp2 : 4096 <= p2 /\ p2 + c2 <= hl_sptop L - 2 ^ 23).
          { destruct (OWNB6 p2 c2) as (Q0 & Q4); [| unfold hl_ceil in Q4; lia].
            unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
            rewrite ENB2. cbn. auto. }
          idtac.
          pose proof (Z.mod_pos_bound (c2 + 1) 256 ltac:(lia)) as MB2.
          LeanFeed.pfeed P (PNSENP.benKL_conc fx6 R6 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => 0 | 36%nat => fb + 16
                       | 37%nat => r | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9)) | 40%nat => bv_unsigned (getr R (PMK.reg 18))
                       | 41%nat => bv_unsigned (getr R (PMK.reg 19)) | 42%nat => (c2 + 1) mod 256 | 43%nat => p2 | 45%nat => n2 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | apply tb0_long; lia | rewrite (KS6 _) by PMK.inl; rewrite (PMK.cs_of_preserved R4 R5 _ RP45) by PMK.inl; rewrite (KS4 _) by (cbn; tauto); PMK.rk ]).
          pvz_hg ltac:(idtac; destruct P as (fx7 & R7 & M7 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG7 & _ & FRZ7 & MS7 & KS7 & V1 & V2 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V18 & V19 & MO7 & _)); PMK.pvz_clrT.
          apply (KEY fx7 R7 M7 MS7 MG7 FRZ7); [intros k Hk; apply KS7; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact V1| exact V2| exact V8| exact V9| exact V18| exact V19| exact MO7].
      + (* [comment removed for export] *)
        apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 6 LBX sp fb str _ M5 model2 cr2 s2 sm2 ax2 fx5 fx6 R5 R6 0x373c4 0x36ee4 M5 (fun _ => False) K
                 ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
        intros BR6.
        pose proof AG25 as AG26.
        assert (ED6 : L5.defined M5 (fb + 16) 16) by (destruct EC2 as (_ & _ & ED); apply (L5C.defined_agree M2 M5 (fb + 16) 16); [apply AG26; lia| exact ED]).
        apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 6 LBX sp fb str _ M5 model2 cr2 _ sm2 ax2 fx6 R6 (sp - 64) 0x37450 3 K MKE ltac:(lia) K0 BR6 FOK INCS
                 Z1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Z10 Z11 ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub64 sp A16) ED6).
        intros fx7 R7 M7 RP67 EC7 BR7 AG67.
        destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 6 LBX sp fb str _ M7 model2 cr2 _ sm2 _ BR7) as (PA7 & _ & _ & _ & STK7 & _).
        change (PMSP.pm_scr 6) with 24576 in STK7. pose proof (L5C.stk_writable RSEGS _ M7 sp 24576 STK7) as WR7.
        assert (WP7 : L5.writable RSEGS M7 (fb + 40) 416) by (destruct PA7 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
        assert (SV7 : en_saved R M7 sp r).
        { apply (en_saved_agree R M5 M7 sp r); [intros a m H1 H2; apply AG67; lia|lia|lia|].
          apply (en_saved_agree R M2 M5 sp r); [intros a m H1 H2; apply AG26; lia|lia|lia| exact SV2]. }
        pose proof SV7 as (T8 & T16 & T24 & T32 & T40).
        LeanFeed.pfeed P (PNSENP.benE_conc fx7 R7 M7 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => 0 | 36%nat => fb + 16
                     | 37%nat => r | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9)) | 40%nat => bv_unsigned (getr R (PMK.reg 18))
                     | 41%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc
                               | rewrite (PMK.cs_of_preserved R6 R7 _ RP67) by PMK.inl; rewrite (KS6 _) by PMK.inl; rewrite (PMK.cs_of_preserved R4 R5 _ RP45) by PMK.inl; rewrite (KS4 _) by (cbn; tauto); PMK.rk ]).
        pvz_hg ltac:(idtac; destruct P as (fx8 & R8 & M8 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG8 & _ & FRZ8 & MS8 & KS8 & Y1 & Y2 & Y8 & Y9 & Y18 & Y19 & MO8)); PMK.pvz_clrT.
        apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 6 LBX sp fb str _ M7 model2 cr2 _ sm2 _ fx7 fx8 R7 R8 0x37450 0x37440 M8
                 (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec)
                 ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO8) ltac:(left; reflexivity)).
        intros BR8.
        apply (en_fin _ K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model2 cr2 _ sm2 _ CTX KONT BR8 Y1 Y2); [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; exact EBB2].
        { intros k Hk. rewrite (KS8 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (PMK.cs_of_preserved R6 R7 k RP67) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
          rewrite (KS6 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (PMK.cs_of_preserved R4 R5 k RP45) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
          rewrite (KS4 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS3 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk. }
        left. split; [| split; [reflexivity|]; split; [apply bax_cat_add|]].
        { exists 3. split; [lia|]. unfold PNR.o_ec, PMSP.o_ec in EC7. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in EC7.
          apply (ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]. }
        split; [| destruct INV2 as (ID & SH); split; [exact ID| exact SH]].
        destruct TP01 as (l1 & c1 & c1' & TE1 & TE2 & _). destruct TP12 as (l2 & c2 & c2' & TF1 & TF2 & _). cbn [PNBO.set_more PNM.b_stk]. rewrite TE1, TF2.
        rewrite TE2 in TF1. apply (f_equal (@length _)) in TF1. revert TF1. clear. intros TF1. rewrite !length_app in *. cbn [length] in *. lia. }
    (* [comment removed for export] *)
    pose proof BR3 as ((PA3 & _) & _). cbn [PNBK.be_M PNBK.be_s] in PA3.
    unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is in PA3. cbn [pa_off_p pa_off_is AD PnLayoutS_u.ADDR_S] in PA3.
    pose proof (nb_facts M2 fb s2 PA3) as NBF.
    destruct (PNM.b_nb s2) as [n2|c2 n2 p2] eqn:ENB2; cbn [PM.vs_size PM.vs_data] in SZ12 |- *.
    + destruct NBF as (Hn2 & B0 & D24).
      LeanFeed.pfeed P (PNSENP.benVS_conc fx3 R3 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => 0 | 36%nat => fb + 16 | 42%nat => 2 * n2 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | apply tb0_short]).
      pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & EQ4w & EQ4 & MS4 & KS4 & Y1 & Y10 & Y11)); PMK.pvz_clrT.
      assert (EM4 : M4 = M2) by (apply functional_extensionality; exact EQ4w). subst M4.
      rewrite (Z.mul_comm 2 n2), Z.div_mul in Y11 by lia.
      apply (VCALL fx4 R4 (fb + 40 + 345) n2 MS4); [intros k Hk; apply KS4; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11| cbn; lia| reflexivity| | lia| lia| lia| lia].
      apply (L5.defined_sub M2 (fb + 384) 24); [exact D24| lia| lia].
    + destruct NBF as (B0 & U8 & U16 & Hn2 & Hc2 & He2 & Dp & U0 & D24).
      destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 6 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 BR3) as (_ & OWNB3 & _).
      assert (Hp2 : 4096 <= p2 /\ p2 + c2 <= hl_sptop L - 2 ^ 23).
      { destruct (OWNB3 p2 c2) as (Q0 & Q4); [| unfold hl_ceil in Q4; lia].
        unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
        rewrite ENB2. cbn. auto. }
      idtac.
      pose proof (Z.mod_pos_bound (c2 + 1) 256 ltac:(lia)) as MB2.
      LeanFeed.pfeed P (PNSENP.benVL_conc fx3 R3 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => 0 | 36%nat => fb + 16
                   | 42%nat => (c2 + 1) mod 256 | 43%nat => p2 | 45%nat => n2 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | apply tb0_long; lia]).
      pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & EQ4w & EQ4 & MS4 & KS4 & Y1 & Y10 & Y11)); PMK.pvz_clrT.
      assert (EM4 : M4 = M2) by (apply functional_extensionality; exact EQ4w). subst M4.
      apply (VCALL fx4 R4 p2 n2 MS4); [intros k Hk; apply KS4; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11| reflexivity| reflexivity| | lia| lia| unfold PMSP.pm_scr in *; lia| lia].
      apply (L5.defined_sub M2 p2 c2); [exact Dp| lia| lia].
  - (* [comment removed for export] *)
    destruct PX as (MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & _ & Y18 & Y19 & GE).
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 6 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx2 fx3 R2 R3 0x37394 0x37440 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 MG3 ltac:(intros a Ha _; apply EQ3; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3.
    apply (en_fin _ K LBX sp r fb cat e str R M model cr s sm ax fx3 R3 M2 model2 cr2 _ sm2 _ CTX KONT BR3 Y1 Y2); [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; exact EBB2].
    { intros k Hk. rewrite (KS3 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk. }
    destruct POST as [((v & Hv & E1) & MO & CAT & LEN & INV')|(E0 & INV & (TP12 & LT12 & _))].
    + left. split; [exists v; split; [exact Hv| apply (ec_agree M2 M2); [intros i Hi; apply EQ3; lia|lia|lia| exact E1]]|]. split; [exact MO|]. split; [exact CAT|]. split; [| exact INV'].
      destruct TP01 as (l1 & c1 & c1' & E1' & E2' & _). rewrite E1'. rewrite E2' in LEN. revert LEN. clear. intros LEN. rewrite !length_app in *. cbn [length] in *. lia.
    + right. split; [apply (ec_agree M2 M2); [intros i Hi; apply EQ3; lia|lia|lia| exact E0]|]. split; [exact INV|].
      unfold PNR.bprog_name. split; [apply (PNBK2.btop_pos_trans s s1 s2 TP01 TP12)| lia].
Qed.

(* [comment removed for export] *)
Theorem read_e_name_ok : PNRS.read_e_name_spec L HI.
Proof.
  unfold PNRS.read_e_name_spec, PNR.read_e_name_spec, PNR.brun_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 6) with 24576 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (A10 & A11 & A13 & A12). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl13 in A13. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v in A10, A11, A13, EC0. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S] in A10, A11, A13, EC0.
  assert (Ht : exists t, (t = 0 \/ t = 1) /\ getr R (PMK.reg 12) = Z_to_bv 64 t) by (destruct A12 as [E|E]; [exists 0| exists 1]; (split; [lia| exact E])).
  clear A12. destruct Ht as (t & Ht & A12).
  pose proof (L5C.stk_floor _ M sp 24576 STK) as SFL. pose proof (L5C.stk_writable RSEGS _ M sp 24576 STK) as WR.
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof (PNBK.brel_init RSEGS AD AN L HI 6 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  change (PMSP.pm_scr 6) with 24576 in BR0.
  assert (CTX : en_ctx t K LBX sp r fb e str R cr s sm).
  { split; [exact Ht|]. split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|].
    split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp|]. split; [exact CRED|]. split; [exact INV|]. split; [exact UNR| exact He]. }
  assert (KONT' : en_kont K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 6 LBX sp fb str _ M model cr s sm ax BR0) as (_ & OWNB & _).
  pose proof RPRE as (PA0 & _). unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is in PA0. cbn [pa_off_p pa_off_is AD PnLayoutS_u.ADDR_S] in PA0.
  pose proof PA0 as (_ & PD0 & _).
  assert (WP : L5.writable RSEGS M (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD0|lia|lia]).
  pose proof (nb_facts M fb s PA0) as NBF.
  unfold PNRS.read_cstring_spec, PNR.read_cstring_spec in RCS.
  unfold PMSP.cfg. cbn [PNL.pn_read_e_name AN PnLayoutS_u.NADDR_S].
  (* [comment removed for export] *)
  assert (CALL : forall (fx1 : FPState) R1 (M1 : mem) x,
            brel LBX sp fb str (BENT M model cr s sm ax) (BENT M1 model cr (PNBO.set_nb s x (PNM.b_ng s)) sm ax) ->
            getr R1 (PMK.reg 1) = Z_to_bv 64 0x37394 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64) ->
            getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
            getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 16) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40) ->
            getr R1 (PMK.reg 11) = Z_to_bv 64 (fb + 40 + 344) -> getr R1 (PMK.reg 12) = Z_to_bv 64 (fb + 16) ->
            getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 464) -> getr R1 (PMK.reg 19) = Z_to_bv 64 t ->
            (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg k) = getr R (PMK.reg k)) ->
            en_saved R M1 sp r -> PMSP.ec_at RSEGS M1 (fb + 16) e cat -> PM.vs_size x = 0 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x383f8 M1 model) K).
  { intros fx1 R1 M1 x BR1 X1 X2 X3 X4 X8 X9 X10 X11 X12 X18 X19 XK SV1 EC1 SZx.
    change 0x383f8 with (PNL.pn_read_cstring AN).
    apply (PNBK2.brel_call RSEGS AD AN L HI KH false _ 5 (PNR.bargs_cs AD 0) (PNR.bprog_cs 0) 6 LBX sp fb str _ M1 model cr _ sm ax fx1 R1 (sp - 64) 0x37394 cat e K
             (RCS 0 (or_introl eq_refl)) ltac:(lia) ltac:(lia) K0 BR1 FOK INCS CRED X1 ltac:(split; [lia| reflexivity]) X2 X3 X4 ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub64 sp A16)).
    { unfold PNR.bargs_cs, PNR.o_p, PNR.o_ec, PMSP.o_p, PMSP.o_ec, PNR.bcs_off, PNR.bcs_str, PNM.OFF_NB. cbn [Z.eqb pa_off_p pa_off_ec AD PnLayoutS_u.ADDR_S PNBO.set_nb PNM.b_nb PNM.b_src].
      rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact X10|]. split; [exact X11|]. split; [exact X12| lia]. }
    { destruct INV as (ID & SH). split; [exact ID| exact SH]. }
    { exact EC1. }
    { exact He. }
    { cbn [PNBO.set_nb PNM.b_src]. exact UNR. }
    intros fx2 R2 M2 model2 s2 sm2 ax2 cr2 RP12 POST BR2 AG12.
    apply (en_body t K LBX sp r fb cat e str R M model cr s sm ax fx2 R2 M2 model2 cr2 (PNBO.set_nb s x (PNM.b_ng s)) s2 sm2 ax2 CTX KONT' BR2);
      [PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| intros k Hk; rewrite (PMK.cs_of_preserved R1 R2 k RP12) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto); apply XK; exact Hk
      | apply (en_saved_agree R M1 M2 sp r); [intros a m H1 H2; apply AG12; lia|lia|lia| exact SV1]
      | destruct (PNBK2.btop_pos_refl s INV) as (l & c & c' & E1 & E2 & Q); exists l, c, c'; cbn [PNBO.set_nb PNM.b_stk]; split; [exact E1|]; split; [exact E2| exact Q]
      | cbn [PNBO.set_nb PNM.b_src]; lia | cbn [PNBO.set_nb PNM.b_nb]; exact SZx
      | destruct POST as (_ & _ & _ & _ & BBP); exact BBP |].
    destruct POST as (_ & _ & _ & DISJ & _). unfold PNR.o_ec, PMSP.o_ec in DISJ. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in DISJ.
    destruct DISJ as [(v & Hv & E1 & MO & CAT & LEN & INV3)|(E0 & INV2 & PROG)]; [left| right].
    - split; [exists v; split; [exact Hv| exact E1]|]. split; [exact MO|]. split; [exact CAT|]. split; [exact LEN| exact INV3].
    - split; [exact E0|]. split; [exact INV2| exact PROG]. }
  destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:ENB.
  - (* [comment removed for export] *)
    destruct NBF as (Hn0 & B0 & D24).
    LeanFeed.pfeed P (PNSENP.benAS_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => t | 36%nat => fb + 16 | 42%nat => 2 * n0 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | apply tb0_short]).
    pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X11 & X12 & X18 & X19 & (NB0 & NB1) & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
    change (mkCfg (@mkst fx R (Z_to_bv 64 0x37338) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x37338 M model).
    apply (PNBK2.brel_piece_nb RSEGS AD AN L HI KH 6 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x37338 0x383f8 M1
             (fun a => (sp - 40 <= a < sp - 40 + 40) \/ (fb + 40 + 344 <= a < fb + 40 + 344 + 2)) (PM.VShort 0) K ltac:(lia) BR0 FOK INCS MS1 MG1
             ltac:(intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
             ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)); [| rewrite ENB; reflexivity| rewrite ENB; reflexivity|].
    { unfold PM.vstr_at. split; [apply (L5.defined_grows M M1 _ _ MG1 D24)|]. split; [exact I|]. split; [lia|]. replace (fb + 384) with (fb + 40 + 344) by lia. exact NB0. }
    intros BR1.
    apply (CALL fx1 R1 M1 (PM.VShort 0) BR1 X1 X2); [PMK.rk| PMK.rk| exact X8| exact X9| PMK.rk| exact X11| exact X12| exact X18| rewrite X19; exact A12 || (rewrite <- A12; PMK.rk)
      | intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | | reflexivity].
    { unfold en_saved. rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia. split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32| exact C40]. }
    { apply (ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]. }
  - (* [comment removed for export] *)
    destruct NBF as (B0 & U8 & U16 & Hn0 & Hc0 & He0 & Dp & U0 & D24).
    assert (Hp0 : 4096 <= p0 /\ p0 + c0 <= hl_sptop L - 2 ^ 23).
    { destruct (OWNB p0 c0) as (Q0 & Q4); [| unfold hl_ceil in Q4; lia].
      unfold PNM.bparser_own, PNM.brest_own. rewrite ENB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. cbn. auto. }
    assert (WPp : L5.writable RSEGS M p0 c0) by (apply (L5C.writable_of_defined RSEGS); [exact Dp|lia|lia]).
    assert (WP1 : L5.writable RSEGS M p0 1) by (apply (L5.writable_sub RSEGS M p0 c0 p0 1 WPp); lia). clear WPp.
    pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)) as MB0.
    LeanFeed.pfeed P (PNSENP.benAL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => t | 36%nat => fb + 16
                 | 42%nat => (c0 + 1) mod 256 | 43%nat => p0 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENP.aligned; PMK.sc | apply tb0_long; lia]).
    pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X11 & X12 & X18 & X19 & SZ0 & PB0 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
    change (mkCfg (@mkst fx R (Z_to_bv 64 0x37338) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x37338 M model).
    apply (PNBK2.brel_piece_nb RSEGS AD AN L HI KH 6 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x37338 0x383f8 M1
             (fun a => (sp - 40 <= a < sp - 40 + 40) \/ (fb + 40 + 352 <= a < fb + 40 + 352 + 8) \/ (p0 + 0 <= a < p0 + 0 + 1)) (PM.VLong c0 0 p0) K ltac:(lia) BR0 FOK INCS MS1 MG1
             ltac:(intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X])
             ltac:(intros a; apply PMK.or_dec; [| apply PMK.or_dec]; apply PMK.rng_dec)); [| | rewrite ENB; reflexivity| rewrite ENB; reflexivity|].
    { intros a Pa. cbn beta in Pa. destruct Pa as [X|[X|X]]; [left; unfold PMSP.pm_scr; lia| right; left; lia|].
      right. right. rewrite ENB. exists (p0, c0). split; [cbn; auto| cbn [fst snd]; lia]. }
    { unfold PM.vstr_at. split; [apply (L5.defined_grows M M1 _ _ MG1 D24)|]. split; [exact I|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact U0]|].
      split; [replace (fb + 384 + 8) with (fb + 40 + 352) by lia; exact SZ0|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ1; lia|lia|lia| replace (fb + 384 + 16) with (fb + 40 + 360) by lia; exact U16]|].
      split; [lia|]. split; [lia|]. split; [exact He0|]. split; [apply (L5.defined_grows M M1 _ _ MG1 Dp)| exact I]. }
    intros BR1.
    apply (CALL fx1 R1 M1 (PM.VLong c0 0 p0) BR1 X1 X2); [PMK.rk| PMK.rk| exact X8| exact X9| PMK.rk| exact X11| exact X12| exact X18| rewrite X19; exact A12 || (rewrite <- A12; PMK.rk)
      | intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | | reflexivity].
    { unfold en_saved. rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia. split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32| exact C40]. }
    { apply (ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]. }
Qed.

End WithHeap.
End PNSEN.
