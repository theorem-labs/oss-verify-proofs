(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrGrow. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnCpyKit_u PnSrcSMemmove_u
     PnSBarrP_u Bs0_code_37878_3787c_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSBAG.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma ec_agree (M M' : mem) o v c : L5C.agree_on M M' o 16 -> 0 <= o -> o + 16 <= 2 ^ 64 -> PMSP.ec_at RSEGS M o v c -> PMSP.ec_at RSEGS M' o v c.
Proof.
  intros AG H0 H1 (E1 & E2 & E3). split; [| split].
  - apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG; lia|lia|lia| exact E1].
  - apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia|lia|lia| exact E2].
  - apply (L5C.defined_agree M M'); [intros i Hi; apply AG; lia| exact E3].
Qed.
Lemma mod16_off sp z : sp mod 16 = 0 -> (sp + z * 16) mod 16 = 0.
Proof. intros H. rewrite Z.mod_add by lia. exact H. Qed.
Lemma bvu (w : bv 64) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Lemma grow_begin_fold (B m : Z) : 1 <= m <= 1024 ->
  alu64 Instr.ALU_ADD (Z_to_bv 64 B) (alu64 Instr.ALU_ADD (mul_div Instr.M_MUL (Z_to_bv 64 40) (Z_to_bv 64 m))
    (mul_div Instr.M_MUL (Z_to_bv 64 (-8)) (alu64 Instr.ALU_SRA (mul_div Instr.M_MUL (Z_to_bv 64 40) (Z_to_bv 64 m)) (Z_to_bv 64 3))))
  = Z_to_bv 64 B.
Proof.
  intros Hm. rewrite !BigLinkGlue_u.BG.md_mul_lit.
  assert (S : alu64 Instr.ALU_SRA (Z_to_bv 64 (40 * m)) (Z_to_bv 64 3) = Z_to_bv 64 (5 * m)).
  { apply bv_eq. rewrite AxSymExec3Sound.AX2S.u_sra64_nonneg by (rewrite BigLinkGlue_u.BG.unsigned_lit; lia).
    rewrite !BigLinkGlue_u.BG.unsigned_lit by lia. change (3 mod 64) with 3. change (2 ^ 3) with 8.
    replace (40 * m) with (5 * m * 8) by lia. apply Z.div_mul. lia. }
  rewrite S, BigLinkGlue_u.BG.md_mul_lit, !BigLinkGlue_u.BG.alu_add_lit.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. f_equal. lia.
Qed.
Lemma pow2_cases k m : 0 <= k <= 11 -> 2 ^ k = m -> m <= 1024 ->
  m = 1 \/ m = 2 \/ m = 4 \/ m = 8 \/ m = 16 \/ m = 32 \/ m = 64 \/ m = 128 \/ m = 256 \/ m = 512 \/ m = 1024.
Proof.
  intros Hk Hm Hle.
  destruct (ltac:(lia) : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11)
    as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; cbn in Hm; lia.
Qed.
(* [comment removed for export] *)
Lemma bstack_shape_push stk c : PNR.bstack_shape stk -> Z.of_nat (length stk) <= PNM.MAX_DEPTH -> PNM.bstate_ok c -> PNR.bmode_cont (PNM.bs_mode c) ->
  PNR.bstack_shape (stk ++ [c]).
Proof.
  intros (L1 & L2 & BOT & CONT & OKs) LEN OKc Mc. unfold PNR.bstack_shape. rewrite length_app. cbn [length].
  split; [lia|]. split; [lia|].
  split; [rewrite app_nth1 by lia; exact BOT|].
  split.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [LT|GE].
    + rewrite app_nth1 by exact LT. apply CONT. lia.
    + rewrite app_nth2 by exact GE. replace (i - length stk)%nat with 0%nat by lia. cbn [nth]. exact Mc.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [LT|GE].
    + rewrite app_nth1 by exact LT. apply OKs. exact LT.
    + rewrite app_nth2 by exact GE. replace (i - length stk)%nat with 0%nat by lia. cbn [nth]. exact OKc.
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
Abbreviation gw := (PNBG.gw RSEGS AD AN L HI 7).
Abbreviation pot := (PNR.pot_bparser L).

Hypothesis OPN : PMS.opnew_spec L HI.
Hypothesis OPD : PMS.opdel_spec L HI.

(* [comment removed for export] *)
Definition bd_kont (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.brun_post RSEGS AD AN false PNR.bprog_value R' M' fb s s' str sm sm' ax ax' cat e ->
      L5C.hpres L LBX sp (PMSP.pm_scr 7) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) (pot s') ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition bd_ctx (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit) (s : PNM.bpst) : Prop :=
  K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr.
Definition bd_saved (R : bvmap 5 word) (M1 : mem) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) r /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
  /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))).
Lemma bd_saved_agree R (M1 M2 : mem) sp r :
  (forall a n, sp - 40 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n) -> 40 <= sp -> sp <= 2 ^ 64 -> bd_saved R M1 sp r -> bd_saved R M2 sp r.
Proof.
  intros AG H1 H2 (S1 & S2 & S3 & S4 & S5). unfold bd_saved.
  repeat split; (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia|assumption]).
Qed.
Definition bd_gcells (M1 : mem) (sp fb lenv : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 192) (sp - 144) /\ L5.u64_at RSEGS M1 (sp - 184) 223340 /\ L5.u64_at RSEGS M1 (sp - 112) (fb + 40 + 392)
  /\ L5.u64_at RSEGS M1 (sp - 120) 0 /\ L5.u64_at RSEGS M1 (sp - 168) (sp - 56) /\ L5.u64_at RSEGS M1 (sp - 160) (fb + 40 + 392)
  /\ L5.u64_at RSEGS M1 (sp - 152) 229952 /\ L5.u64_at RSEGS M1 (sp - 104) lenv /\ L5.u64_at RSEGS M1 (sp - 96) (fb + 464)
  /\ L5.u64_at RSEGS M1 (sp - 88) (fb + 16) /\ L5.u64_at RSEGS M1 (sp - 80) (fb + 40) /\ L5.u64_at RSEGS M1 (sp - 72) 231724
  /\ L5.u32_at RSEGS M1 (sp - 64) 3 /\ L5.u32_at RSEGS M1 (sp - 60) lenv /\ L5.u64_at RSEGS M1 (sp - 56) 4.
Lemma bd_gcells_agree (M1 M2 : mem) sp fb lenv :
  (forall a n, sp - 192 <= a -> a + n <= sp - 48 -> L5C.agree_on M1 M2 a n) -> 192 <= sp -> sp <= 2 ^ 64 ->
  bd_gcells M1 sp fb lenv -> bd_gcells M2 sp fb lenv.
Proof.
  intros AG H1 H2 G. unfold bd_gcells in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia|assumption])
             | (lazymatch goal with |- L5.u32_at _ _ ?a _ =>
                  apply (PMF.u32_at_agree RSEGS M1 M2); [intros i Hi; apply (AG a 4); lia|lia|lia|assumption] end) ].
Qed.

(* [comment removed for export] *)
Lemma bd_fin (pcret : Z) K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  (forall fx Rx Mx, getr Rx (PMK.reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
      msteps RSEGS (@mkst fx Rx (Z_to_bv 64 pcret) Mx (seg_rom RSEGS)) (@mkst fx Rx (Z_to_bv 64 r) Mx (seg_rom RSEGS))) ->
  bd_ctx K LBX sp r fb str R cr s -> bd_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R5 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R5 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  (   ((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M5 (fb + 16) v (pa_errcat_obj AD)) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true
       /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bpush_rel s s5 sm sm5)) ->
  PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pcret M5 model5) K.
Proof.
  intros RET (K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED) KONT BR Y1 Y2 Y3 Y4 Y8 Y9 Y18 Y19 YK POST BB.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact (RET fx5 R5 M5 Y1 Hr1 Hr2)|].
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite Y8; apply Z_to_bv_bv_unsigned | rewrite Y9; apply Z_to_bv_bv_unsigned
            | rewrite Y18; apply Z_to_bv_bv_unsigned | rewrite Y19; apply Z_to_bv_bv_unsigned | apply YK; cbn; tauto ].
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

Lemma bd_ret r : forall fx Rx Mx, getr Rx (PMK.reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
  msteps RSEGS (@mkst fx Rx (Z_to_bv 64 0x38960) Mx (seg_rom RSEGS)) (@mkst fx Rx (Z_to_bv 64 r) Mx (seg_rom RSEGS)).
Proof. intros fx0 Rx Mx X1 H1 H2. apply (PMK.ret_to RSEGS fx0 Rx Mx 0x38960 W_3791c r F_3791c eq_refl D_3791c X1 H1 H2). Qed.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | apply bvu | unfold PNSBAP.aligned; PMK.sc]).
Local Ltac carry1 M M2 AG side :=
  match goal with
  | H : L5.u64_at RSEGS M ?a ?v |- _ => lazymatch goal with _ : L5.u64_at RSEGS M2 a v |- _ => fail | _ => idtac end;
      let N := fresh "CY" in assert (N : L5.u64_at RSEGS M2 a v) by (apply (L5C.u64_at_agree RSEGS M M2); [apply AG; side|side|side| exact H])
  | H : L5.u32_at RSEGS M ?a ?v |- _ => lazymatch goal with _ : L5.u32_at RSEGS M2 a v |- _ => fail | _ => idtac end;
      let N := fresh "CY" in assert (N : L5.u32_at RSEGS M2 a v) by (apply (PMF.u32_at_agree RSEGS M M2); [apply AG; side|side|side| exact H])
  | H : L5.u8_at RSEGS M ?a ?v |- _ => lazymatch goal with _ : L5.u8_at RSEGS M2 a v |- _ => fail | _ => idtac end;
      let N := fresh "CY" in assert (N : L5.u8_at RSEGS M2 a v) by (apply (L5C.u8_at_agree RSEGS M M2); [apply AG; side|side|side| exact H])
  end.
Local Ltac carry M M2 AG side := repeat carry1 M M2 AG side.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bd_gtail K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx2 : FPState) R2 (M2 : mem) model1 cr1 s1 sm1 ax1 (m lenv : Z) :
  bd_ctx K LBX sp r fb str R cr s -> bd_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  gw LBX sp fb str (BENT M model cr s sm ax) (PNM.bparser_own s1 ++ LBX) M2 model1 cr1 (PNM.b_src s1) sm1 ax1 ->
  bparser_at M2 (fb + 40) (fb + 472) s1 -> PNM.bgrow_ok s1 -> PMSP.credit_keep cr cr1 (pot s) (pot s1) ->
  PNR.binv s1 -> PNM.b_stk s1 = PNM.b_stk s -> PNM.b_bb s1 = PNM.b_bb s -> 2 ^ PNM.b_sk s1 = m -> Z.of_nat (length (PNM.b_stk s1)) = m -> m <= 1024 ->
  PMSP.ec_at RSEGS M2 (fb + 16) e cat -> PM.unread (PNM.b_src s1) sm1 + 4 <= PM.unread (PNM.b_src s) sm -> 0 <= lenv < 2 ^ 64 ->
  getr R2 (PMK.reg 1) = Z_to_bv 64 0x36a74 -> getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 192) ->
  getr R2 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (PMK.reg 8) = Z_to_bv 64 (2 * m) -> getr R2 (PMK.reg 9) = Z_to_bv 64 m -> getr R2 (PMK.reg 10) = Z_to_bv 64 (80 * m) ->
  getr R2 (PMK.reg 18) = Z_to_bv 64 (sp - 60) -> getr R2 (PMK.reg 19) = Z_to_bv 64 (sp - 64) ->
  (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg k) = getr R (PMK.reg k)) ->
  bd_gcells M2 sp fb lenv -> bd_saved R M2 sp r ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0xb03b8 M2 model1) K.
Proof.
  intros CTX KONT GW2 PA2 GR1 CK1 INV1 ESTK EBB Hm HL Hm10 EC2 UNR4 Hlenv Y1 Y2 Y3 Y4 Y8 Y9 Y10 Y18 Y19 YK2 GC2 SV2.
  pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof RAok as (Hr1 & Hr2).
  set (E0 := BENT M model cr s sm ax) in *.
  set (LB1 := PNM.bparser_own s1 ++ LBX) in *.
  pose proof GW2 as (IA2 & VIS2 & VREF2 & BASE2 & ERR2 & STEP2 & AXL2 & HP2 & MB2 & HH2 & STK2 & MOK2 & INC2).
  change (PMSP.pm_scr 7) with 26624 in STK2. pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF2).
  assert (BRG1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M2 _ HH2); apply incl_refl).
  assert (NDL1 : NoDup (map fst LB1)) by exact (PMPK.heap_nodup L HI HIok LB1 cr1 M2 _ HH2).
  pose proof (ly_kpm L LY) as KPM. pose proof (ly_bov L LY) as BOV.
  (* [comment removed for export] *)
  pose proof PA2 as (_ & PD2 & _ & H8_2 & _ & _ & _ & _ & _ & _ & _ & BB2 & NB2 & TB2 & SV2' & M01 & _).
  unfold PNM.OFF_STK, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB in BB2, NB2, TB2, SV2'.
  pose proof SV2' as (_ & _ & _ & Hk & Hlen & Hal & _). clear SV2'. unfold PNM.BSZ in Hlen.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (stk1 := PNM.b_stk s1) in *.
  pose proof INV1 as (ID1 & SH1). pose proof SH1 as (L1 & _).
  assert (Hm1 : 1 <= m) by lia.
  assert (Hk10 : k <= 10).
  { destruct (Z.eq_dec k 11) as [E|NE]; [| lia]. exfalso. rewrite E in Hm. change (2 ^ 11) with 2048 in Hm. lia. }
  assert (P2 : 2 ^ (k + 1) = 2 * m) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
  assert (Bs : In (b, 40 * m) (PNM.bparser_own s1)).
  { rewrite <- Hm. unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PNM.BSZ, b, k. apply in_or_app. right. left. reflexivity. }
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own; left; reflexivity).
  assert (OWNB : forall B n, In (B, n) (PNM.bparser_own s1) -> 4096 <= B /\ B + n <= hl_sptop L - 8388608).
  { intros B n Hin. destruct (BRG1 B n ltac:(unfold LB1; apply in_or_app; left; exact Hin)) as (Q0 & _ & Q4). unfold hl_ceil in Q4. lia. }
  destruct (OWNB _ _ Bs) as (Hb0 & Hb4). destruct (OWNB _ _ Bq) as (Hq0 & Hq4). unfold PM.CHUNK in Hq4.
  assert (NEqb : PM.sr_qc (PNM.b_src s1) <> b).
  { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1)) (PNM.brest_own s1 ++ LBX) _ PM.CHUNK _ (40 * m));
      [unfold LB1, PNM.bparser_own in NDL1; rewrite <- app_assoc in NDL1; exact NDL1| unfold PM.src_own; left; reflexivity|].
    apply in_or_app. left. rewrite <- Hm. unfold PNM.brest_own, PNM.bvec_own, PNM.BSZ, b, k. left. reflexivity. }
  (* [comment removed for export] *)
  assert (CROK : credit_ok L cr1 (80 * m)).
  { pose proof GR1 as (NG & TG & BG).
    pose proof (PNBK.pot_text_nonneg RSEGS AD AN L HI KH M2 _ _ _ NB2 NG) as (N1 & N2).
    pose proof (PNBK.pot_text_nonneg RSEGS AD AN L HI KH M2 _ _ _ TB2 TG) as (T1' & T2').
    pose proof (PNBK.pot_v8_nonneg RSEGS AD AN L HI KH M2 _ _ _ BB2 BG) as (B1' & B2').
    unfold credit_ok. unfold PMSP.credit_le, PMSP.credit_keep in CRED, CK1. unfold PNR.pot_bparser, PNR.pot_bstack, PM.credit_add in CRED, CK1.
    cbn [fst snd] in CRED, CK1. fold k in CK1. rewrite P2 in CK1. change (2 ^ 12) with 4096 in CK1.
    change (2 ^ 12) with 4096 in CRED. unfold PNM.BSZ in CRED, CK1.
    assert (X1 : hl_k_per_malloc L * 1 <= hl_k_per_malloc L * (11 - k)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (X2 : 1 * hl_b_overhead L <= (11 - k) * hl_b_overhead L) by (apply Z.mul_le_mono_nonneg_r; lia).
    split; [clear -CRED CK1 X1 N1 T1' B1' KPM; lia| clear -CRED CK1 X2 N2 T2' B2' BOV Hm10 Hm1; lia]. }
  unfold PMS.opnew_spec in OPN.
  apply (PNBG.gw_opnew RSEGS AD AN L HI KH 7 LBX sp fb str E0 LB1 M2 model1 cr1 (PNM.b_src s1) sm1 ax1 fx2 R2 (sp - 192) 0x36a74 (80 * m) K OPN
           ltac:(lia) K0 GW2 FOK INCS Y1 ltac:(split; [lia| reflexivity]) Y2 Y4 Y10 ltac:(lia) CROK ltac:(lia)
           ltac:(change (PMSP.pm_scr 7) with 26624; change PMSP.OPNEW_SCR with 8240; lia)
           ltac:(replace (sp - 192) with (sp + (-12) * 16) by lia; apply mod16_off; exact A16)).
  intros fx3 R3 M3 model3 Bn RP23 Z10 FRESH GW3 AGH23 AGB23.
  pose proof (L5C.fresh_block_bounds L LB1 M3 Bn _ FRESH) as (FB0 & FB1 & FB16 & FBn & FB4). unfold hl_ceil in FB4. rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in FB1.
  assert (SPR : 224 <= sp /\ sp <= 2 ^ 64) by lia. assert (SPBN : Bn + 80 * m <= sp - 224) by lia.
  assert (FBN : Bn + 80 * m <= fb + 432 \/ fb + 456 <= Bn) by lia. assert (FSP : sp - 144 <= fb + 432 /\ fb + 472 <= 2 ^ 64) by lia.
  destruct FRESH as (_ & FAP & FDEF).
  assert (APo : forall B n, In (B, n) (PNM.bparser_own s1) -> Bn + 80 * m <= B \/ B + n <= Bn).
  { intros B n Hin. exact (FAP (B, n) ltac:(unfold LB1; apply in_or_app; left; exact Hin)). }
  pose proof (APo _ _ Bs) as APb. pose proof (APo _ _ Bq) as APq.
  pose proof GW3 as (_ & _ & _ & BASE3 & _ & _ & _ & _ & _ & HH3 & STK3 & MOK3 & INC3).
  change (PMSP.pm_scr 7) with 26624 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 26624 STK3) as WR3. pose proof MOK3 as (Mh3 & Ml3 & _).
  pose proof BASE3 as (IMG3 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG3.
  assert (PA3 : bparser_at M3 (fb + 40) (fb + 472) s1).
  { apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M2 M3 (fb + 40) (fb + 472) s1); unfold PNM.PSIZE; [lia|lia| apply AGH23; lia| | exact PA2].
    intros B n Hin. destruct (OWNB B n Hin) as (Q0 & Q4). split; [lia|]. split; [lia|]. apply (AGB23 (B, n)). unfold LB1. apply in_or_app. left. exact Hin. }
  assert (EC3 : PMSP.ec_at RSEGS M3 (fb + 16) e cat) by (apply (ec_agree M2 M3); [apply AGH23; lia|lia|lia| exact EC2]).
  assert (GC3 : bd_gcells M3 sp fb lenv) by (apply (bd_gcells_agree M2 M3 sp fb lenv); [intros a n H1 H2; apply AGH23; lia|lia|lia| exact GC2]).
  pose proof GC3 as (F192 & F184 & F112 & F120 & F168 & F160 & F152 & F104 & F96 & F88 & F80 & F72 & F64 & F60 & F56).
  assert (SV3 : bd_saved R M3 sp r) by (apply (bd_saved_agree R M2 M3 sp r); [intros a n H1 H2; apply AGH23; lia|lia|lia| exact SV2]).
  pose proof SV3 as (S8 & S16 & S24 & S32 & S40).
  pose proof PA3 as (_ & PD3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV3' & _). unfold PNM.OFF_STK in SV3'.
  pose proof SV3' as (V0 & V8 & V16 & _ & _ & _ & DB3 & _ & _ & EL3). clear SV3'. unfold PNM.BSZ in V8, V16, DB3, EL3. fold b k stk1 in V0, V8, V16, DB3, EL3.
  rewrite HL in V8. rewrite Hm in V16, DB3.
  LeanFeed.pfeed P (PNSBAP.bbaH1_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r | 19%nat => lenv
               | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
               | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => b | 47%nat => Bn | 53%nat => m | _ => 0 end)) ltac:(first [PMK.sc | apply bvu | unfold PNSBAP.aligned; PMK.sc
                         | apply (L5C.writable_of_defined RSEGS); [exact FDEF|lia|lia] ]).
  pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z2 & Z8 & Z9 & Z10h & Z11 & Z12 & Z14 & Z15 & Z16 & Z17 & Z18
                                  & H176 & H168 & H160 & H152 & H128 & D0 & D1 & D2 & D3 & D4 & H120 & H136 & H144 & H192 & H184 & H112
                                  & H104 & H96 & H88 & H80 & H72 & D5 & D6 & D7 & D8 & D9 & H64 & H60 & H56)); PMK.pvz_clrT.
  apply (PNBG.gw_piece RSEGS AD AN L HI KH 7 LBX sp fb str E0 ((Bn, 80 * m) :: LB1) M3 model3 (debit L cr1 (80 * m)) (PNM.b_src s1) sm1 ax1 fx3 fx4 R3 R4 0x36a74 0xab480 M4
           (fun a => (sp - 224 <= a < sp - 224 + 224) \/ (Bn + 0 <= a < Bn + 0 + 80 * m)) K ltac:(lia) GW3 FOK INCS MS4 MG4
           ltac:(intros a Ha N; apply FRZ4; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
           ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)).
  { intros a [X|X]; [left; change (PMSP.pm_scr 7) with 26624; lia|]. right. right. exists (Bn, 80 * m). split; [left; reflexivity|]. cbn [fst snd].
    split; [| lia]. intros Hin. destruct (FAP (Bn, 80 * m) ltac:(unfold LB1; apply in_or_app; right; exact Hin)) as [Y|Y]; cbn [fst snd] in Y; lia. }
  intros GW4.
  assert (PA4 : bparser_at M4 (fb + 40) (fb + 472) s1).
  { apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M3 M4 (fb + 40) (fb + 472) s1); unfold PNM.PSIZE; [lia|lia| intros i Hi; apply FRZ4; lia| | exact PA3].
    intros B n Hin. destruct (OWNB B n Hin) as (Q0 & Q4). pose proof (APo B n Hin) as AP. split; [lia|]. split; [lia|]. intros i Hi. apply FRZ4; [lia|lia| clear -AP Hi; lia]. }
  assert (EC4 : PMSP.ec_at RSEGS M4 (fb + 16) e cat) by (apply (ec_agree M3 M4); [intros i Hi; apply FRZ4; lia|lia|lia| exact EC3]).
  assert (DBn4 : L5.defined M4 Bn (80 * m)) by exact (L5.defined_grows M3 M4 _ _ MG4 FDEF).
  assert (DB4 : L5.defined M4 b (40 * m)) by exact (L5.defined_grows M3 M4 _ _ MG4 DB3).
  pose proof PA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV4' & _). unfold PNM.OFF_STK in SV4'.
  pose proof SV4' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EL4). clear SV4'. unfold PNM.BSZ in EL4. fold b stk1 in EL4.
  pose proof GW4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK4 & MOK4 & _). change (PMSP.pm_scr 7) with 26624 in STK4. pose proof MOK4 as (Mh4 & Ml4 & _).
  (* [comment removed for export] *)
  destruct (PNCK.copy_run_eq RSEGS 0xab480 PMCPS.memcpy_copy1 fx4 R4 M4 Bn b (40 * m) 0x36988 ltac:(rewrite Z10h; apply grow_begin_fold; lia) Z11 Z12 Z1 ltac:(split; [lia| reflexivity])
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear -APb Hm1; lia)
              ltac:(apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M4 Bn (80 * m)); [exact DBn4|lia|lia]|lia|lia]) DB4)
    as (R5 & M5 & MS5 & MG5 & FRZ5 & DF5 & CP5 & KS5 & W10).
  apply (PNBG.gw_piece RSEGS AD AN L HI KH 7 LBX sp fb str E0 ((Bn, 80 * m) :: LB1) M4 model3 (debit L cr1 (80 * m)) (PNM.b_src s1) sm1 ax1 fx4 fx4 R4 R5 0xab480 0x36988 M5
           (fun a => Bn <= a < Bn + 40 * m) K ltac:(lia) GW4 FOK INCS MS5 MG5 FRZ5 ltac:(intros a; apply PMK.rng_dec)).
  { intros a X. right. right. exists (Bn, 80 * m). split; [left; reflexivity|]. cbn [fst snd].
    split; [| lia]. intros Hin. destruct (FAP (Bn, 80 * m) ltac:(unfold LB1; apply in_or_app; right; exact Hin)) as [Y|Y]; cbn [fst snd] in Y; lia. }
  intros GW5.
  assert (AG45 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= Bn \/ Bn + 40 * m <= a) -> L5C.agree_on M4 M5 a n).
  { intros a n H1 H2 H3 i Hi. apply FRZ5; [lia| clear -H3 Hi; lia]. }
  carry M4 M5 AG45 ltac:(clear - SPBN SPR FB0 Hm1 Hm10; lia).
  assert (X18_5 : getr R5 (PMK.reg 18) = Z_to_bv 64 Bn) by (rewrite <- (grow_begin_fold Bn m) by lia; PMK.rk).
  assert (PA5 : bparser_at M5 (fb + 40) (fb + 472) s1).
  { apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M4 M5 (fb + 40) (fb + 472) s1); unfold PNM.PSIZE; [lia|lia| apply AG45; lia| | exact PA4].
    intros B n Hin. destruct (OWNB B n Hin) as (Q0 & Q4). pose proof (APo B n Hin) as AP. split; [lia|]. split; [lia|]. apply AG45; [lia|lia| clear -AP Hm1; lia]. }
  assert (EC5 : PMSP.ec_at RSEGS M5 (fb + 16) e cat) by (apply (ec_agree M4 M5); [apply AG45; lia|lia|lia| exact EC4]).
  assert (SV5 : bd_saved R M5 sp r) by (apply (bd_saved_agree R M4 M5 sp r); [intros a n H1 H2; apply AG45; lia|lia|lia| split; [exact D5| split; [exact D6| split; [exact D7| split; [exact D8| exact D9]]]]]).
  pose proof SV5 as (T8 & T16 & T24 & T32 & T40).
  assert (DBn5 : L5.defined M5 Bn (80 * m)) by exact (L5.defined_grows M4 M5 _ _ MG5 DBn4).
  assert (DB5 : L5.defined M5 b (40 * m)) by exact (L5.defined_grows M4 M5 _ _ MG5 DB4).
  pose proof GW5 as (_ & _ & _ & BASE5 & _ & _ & _ & _ & _ & HH5 & STK5 & MOK5 & _). change (PMSP.pm_scr 7) with 26624 in STK5.
  pose proof (L5C.stk_writable RSEGS _ M5 sp 26624 STK5) as WR5. pose proof BASE5 as (IMG5 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG5.
  pose proof PA5 as (_ & PD5 & _ & H8_5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV5' & _). unfold PNM.OFF_STK in SV5'.
  pose proof SV5' as (V0_5 & V8_5 & V16_5 & _). clear SV5'. unfold PNM.BSZ in V8_5, V16_5. fold b k stk1 in V0_5, V8_5, V16_5. rewrite HL in V8_5. rewrite Hm in V16_5.
  assert (WP5 : L5.writable RSEGS M5 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD5|lia|lia]).
  assert (WBn5 : L5.writable RSEGS M5 Bn (80 * m)) by (apply (L5C.writable_of_defined RSEGS); [exact DBn5|lia|lia]).
  (* [comment removed for export] *)
  set (c := PNM.BS 3 (bv_unsigned (AxSymExec3.AX2.ext_val true 0 4 (Z_to_bv 64 lenv))) 4 0 0).
  assert (NEW5 : forall i, (i < length (stk1 ++ [c]))%nat -> PNM.bstate_at RSEGS M5 (Bn + 40 * Z.of_nat i) (nth i (stk1 ++ [c]) PNM.bs_root)).
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. destruct (Nat.lt_ge_cases i (length stk1)) as [LT|GE].
    - rewrite app_nth1 by exact LT.
      apply (PNCK.bstate_copy RSEGS M4 M5 (b + 40 * Z.of_nat i) (Bn + 40 * Z.of_nat i)); [lia|lia|lia|lia| apply (L5.defined_sub M4 b (40 * m)); [exact DB4|lia|lia]| | apply EL4; exact LT].
      intros j Hj. replace (Bn + 40 * Z.of_nat i + j) with (Bn + (40 * Z.of_nat i + j)) by lia. replace (b + 40 * Z.of_nat i + j) with (b + (40 * Z.of_nat i + j)) by lia.
      apply CP5. lia.
    - assert (Ei : i = length stk1) by lia. rewrite app_nth2 by lia. rewrite Ei, Nat.sub_diag. cbn [nth]. replace (Z.of_nat (length stk1)) with m by lia.
      unfold PNM.bstate_at. cbn [c PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [apply (PMF.u32_at_agree RSEGS M4 M5); [apply AG45; lia|lia|lia| exact D4]|].
      split; [apply (L5C.u64_at_agree RSEGS M4 M5); [apply AG45; lia|lia|lia| exact D3]|].
      split; [apply (L5C.u64_at_agree RSEGS M4 M5); [apply AG45; lia|lia|lia| exact D2]|].
      split; [apply (L5C.u8_at_agree RSEGS M4 M5); [apply AG45; lia|lia|lia| exact D1]|].
      apply (L5C.u64_at_agree RSEGS M4 M5); [apply AG45; lia|lia|lia| exact D0]. }
  (* [comment removed for export] *)
  LeanFeed.pfeed P (PNSBAP.bbaH2_conc fx4 R5 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r | 19%nat => lenv
               | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
               | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => b | 47%nat => Bn | 53%nat => m | _ => 0 end)) ltac:(first [PMK.sc | apply bvu | unfold PNSBAP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG6 & _ & FRZ6 & MS6 & KS6 & U1 & U2 & U8 & U9 & U10 & U11 & U12 & U13 & U18 & J120 & J144 & E0' & J128 & E1
                                  & J136 & E2 & J176 & J168 & J160 & J152 & J192 & J184 & J112 & J104 & J96 & J88 & J80 & J72 & E3 & E4 & E5 & E6 & E7
                                  & J64 & J60 & J56)); PMK.pvz_clrT.
  apply (PNBG.gw_piece RSEGS AD AN L HI KH 7 LBX sp fb str E0 ((Bn, 80 * m) :: LB1) M5 model3 (debit L cr1 (80 * m)) (PNM.b_src s1) sm1 ax1 fx4 fx6 R5 R6 0x36988 0x56720 M6
           (fun a => (sp - 224 <= a < sp - 224 + 224) \/ (fb + 40 + 392 <= a < fb + 40 + 392 + 24)) K ltac:(lia) GW5 FOK INCS MS6 MG6
           ltac:(intros a Ha N; apply FRZ6; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
           ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)).
  { intros a [X|X]; [left; change (PMSP.pm_scr 7) with 26624; lia|]. right. left. unfold PNBK.pwr. lia. }
  intros GW6.
  assert (AG56 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 224 \/ sp <= a) -> (a + n <= fb + 432 \/ fb + 456 <= a) -> L5C.agree_on M5 M6 a n).
  { intros a n H1 H2 H3 H4 i Hi. apply FRZ6; [lia| clear -H3 Hi; lia| clear -H4 Hi; lia]. }
  carry M5 M6 AG56 ltac:(clear - SPBN SPR FB0 Hm1 Hm10 FBN; lia).
  set (s' := PNM.BPST (PNM.b_more s1) (PNM.b_done s1) (PNM.b_src s1) (PNM.b_bb s1) (PNM.b_nb s1) (PNM.b_tb s1) (PNM.b_ng s1) (PNM.b_tg s1) (PNM.b_bg s1) Bn (k + 1) (stk1 ++ [c])).
  assert (PA6 : bparser_at M6 (fb + 40) (fb + 472) s').
  { apply (PNBO.bparser_revec RSEGS AD (pa_vp_parser AD) M5 M6 (fun a => (sp - 224 <= a < sp - 224 + 224) \/ (fb + 40 + 392 <= a < fb + 40 + 392 + 24))
             ltac:(intros a Ha N; apply FRZ6; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]) MG6
             (fb + 40) (fb + 472) s1 (PNM.b_more s1) Bn (k + 1) (stk1 ++ [c])); unfold PNM.PSIZE, PNM.OFF_STK; [lia|lia| exact PA5| | | | exact M01| |lia| unfold PM.CHUNK; lia].
    - intros a Ha [X|X]; [exfalso; lia| right; lia].
    - intros i Hi. unfold PM.CHUNK in Hi. intros [X|X]; lia.
    - apply (L5C.u8_at_agree RSEGS M5 M6); [apply AG56; lia|lia|lia| exact H8_5].
    - unfold PNM.bvec_at, PNM.BSZ. rewrite length_app. cbn [length]. rewrite P2.
      split; [exact E2|].
      split; [replace (Bn + 40 * Z.of_nat (length stk1 + 1)) with (Bn + 40 * m + 40) by lia; replace (fb + 40 + 392 + 8) with (fb + 40 + 400) by lia; exact E1|].
      split; [replace (Bn + 40 * (2 * m)) with (Bn + 80 * m) by lia; replace (fb + 40 + 392 + 16) with (fb + 40 + 408) by lia; exact E0'|].
      split; [lia|]. split; [lia|]. split; [exact FB16|].
      split; [replace (40 * (2 * m)) with (80 * m) by lia; exact (L5.defined_grows M5 M6 _ _ MG6 DBn5)|]. split; [exact I|]. split; [exact I|].
      intros i Hi. apply (PNMF.bstate_at_agree RSEGS M5 M6); [lia| lia| | apply NEW5; rewrite length_app; cbn [length]; exact Hi].
      apply AG56; lia. }
  (* [comment removed for export] *)
  assert (NLBX : forall x, In x LBX -> fst x <> b).
  { intros (B', n') Hin E. cbn [fst] in E. apply (PMPK.fst_neq_app (PNM.bparser_own s1) LBX b (40 * m) B' n' NDL1 Bs Hin). symmetry. exact E. }
  unfold PMS.opdel_spec, PMSP.opdel_spec in OPD. cbn [pa_opdel AD PnLayoutS_u.ADDR_S] in OPD.
  apply (PNBG.gw_opdel RSEGS AD AN L HI KH 0x56720 7 LBX sp fb str E0 ((Bn, 80 * m) :: LB1) M6 model3 (debit L cr1 (80 * m)) (PNM.b_src s1) sm1 ax1 fx6 R6 (sp - 144) 0x38298 b (40 * m) K OPD
           ltac:(lia) K0 GW6 FOK INCS ltac:(right; unfold LB1; apply in_or_app; left; exact Bs) NLBX U1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) U10
           ltac:(lia) ltac:(change (PMSP.pm_scr 7) with 26624; change PMSP.OPDEL_SCR with 8224; lia)
           ltac:(replace (sp - 144) with (sp + (-9) * 16) by lia; apply mod16_off; exact A16)).
  intros fx7 R7 M7 model7 RP67 GW7 AGH67 AGB67.
  assert (NEnb : Bn <> b) by (clear -APb Hm1; lia).
  assert (LBEQ : lb_remove b ((Bn, 80 * m) :: LB1) = (Bn, 80 * m) :: (PM.sr_qc (PNM.b_src s1), PM.CHUNK) :: ((PGV8.v8_own (PNM.b_bb s1) ++ PM.vs_own (PNM.b_nb s1) ++ PM.vs_own (PNM.b_tb s1)) ++ LBX)).
  { unfold LB1, PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PM.src_own, PNM.BSZ. fold b k. rewrite Hm. cbn [lb_remove app fst].
    rewrite (proj2 (Z.eqb_neq Bn b) NEnb), (proj2 (Z.eqb_neq (PM.sr_qc (PNM.b_src s1)) b) NEqb), Z.eqb_refl. reflexivity. }
  rewrite LBEQ in GW7, AGB67.
  assert (PA7 : bparser_at M7 (fb + 40) (fb + 472) s').
  { apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M6 M7 (fb + 40) (fb + 472) s'); unfold PNM.PSIZE; [lia|lia| apply AGH67; lia| | exact PA6].
    intros B n Hin. unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PM.src_own, PNM.BSZ in Hin.
    cbn [s' PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk app] in Hin. rewrite P2 in Hin.
    destruct Hin as [E|[E|Hin]].
    - injection E as <- <-. split; [lia|]. split; [unfold PM.CHUNK; lia|]. apply (AGB67 (PM.sr_qc (PNM.b_src s1), PM.CHUNK)). right. left. reflexivity.
    - injection E as <- <-. split; [lia|]. split; [lia|]. replace (40 * (2 * m)) with (80 * m) by lia. apply (AGB67 (Bn, 80 * m)). left. reflexivity.
    - assert (Hin1 : In (B, n) (PNM.bparser_own s1)).
      { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PM.src_own. cbn [app]. right. right. exact Hin. }
      destruct (OWNB B n Hin1) as (Q0 & Q4). split; [lia|]. split; [lia|]. apply (AGB67 (B, n)). right. right. apply in_or_app. left. exact Hin. }
  assert (BR7 : brel LBX sp fb str E0 (BENT M7 model7 (debit L cr1 (80 * m)) s' sm1 ax1)).
  { apply (PNBG.brel_of_gw RSEGS AD AN L HI KH 7 LBX sp fb str E0 _ M7 model7 _ (PNM.b_src s1) sm1 ax1 s' GW7); [| exact PA7| reflexivity| exact GR1|].
    - unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PM.src_own, PNM.BSZ. cbn [s' PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk app].
      rewrite P2. replace (40 * (2 * m)) with (80 * m) by lia. apply perm_swap.
    - unfold s', E0. cbn [PNBK.be_cr PNBK.be_s]. rewrite (PNBG.pot_grow L s1 Bn k (stk1 ++ [c]) eq_refl ltac:(lia)).
      unfold PMSP.credit_keep, debit in *. cbn [fst snd]. rewrite P2. unfold PNM.BSZ. clear -CK1. lia. }
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat).
  { apply (ec_agree M6 M7); [apply AGH67; lia|lia|lia|]. apply (ec_agree M5 M6); [apply AG56; lia|lia|lia| exact EC5]. }
  assert (VE7 : L5.u64_at RSEGS M7 (fb + 40 + 400) (Bn + 40 * m + 40)) by (apply (L5C.u64_at_agree RSEGS M6 M7); [apply AGH67; lia|lia|lia| exact E1]).
  assert (U8' : L5.u64_at RSEGS M7 (sp - 8) r) by (apply (L5C.u64_at_agree RSEGS M6 M7); [apply AGH67; lia|lia|lia| exact E3]).
  assert (U16' : L5.u64_at RSEGS M7 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M6 M7); [apply AGH67; lia|lia|lia| exact E4]).
  assert (U24' : L5.u64_at RSEGS M7 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M6 M7); [apply AGH67; lia|lia|lia| exact E5]).
  assert (U32' : L5.u64_at RSEGS M7 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M6 M7); [apply AGH67; lia|lia|lia| exact E6]).
  assert (U40' : L5.u64_at RSEGS M7 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M6 M7); [apply AGH67; lia|lia|lia| exact E7]).
  carry M6 M7 AGH67 ltac:(clear - SPR FSP; lia).
  assert (AGBn : forall a n, Bn <= a -> a + n <= Bn + 80 * m -> L5C.agree_on M6 M7 a n)
    by (intros a n H1 H2 i Hi; apply (AGB67 (Bn, 80 * m)); [left; reflexivity| cbn [fst snd]; lia]).
  carry M6 M7 AGBn ltac:(clear - SPBN SPR FB0 Hm1 Hm10; lia).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str E0 M7 model7 _ s' sm1 ax1 BR7) as (_ & _ & _ & _ & STK7 & MOK7).
  change (PMSP.pm_scr 7) with 26624 in STK7. pose proof (L5C.stk_writable RSEGS _ M7 sp 26624 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & _). assert (WP7 : L5.writable RSEGS M7 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD7|lia|lia]).
  pose proof GW7 as (_ & _ & _ & BASE7 & _). pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  assert (DBn7 : L5.defined M7 Bn (80 * m)) by (apply (L5C.defined_agree M6 M7); [apply AGBn; lia| exact (L5.defined_grows M5 M6 _ _ MG6 DBn5)]).
  assert (WBn7 : L5.writable RSEGS M7 Bn (80 * m)) by (apply (L5C.writable_of_defined RSEGS); [exact DBn7|lia|lia]).
  LeanFeed.pfeed P (PNSBAP.bbaT_conc fx7 R7 M7 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r | 19%nat => lenv
               | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
               | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => b | 47%nat => Bn | 53%nat => m | _ => 0 end)) ltac:(first [PMK.sc | apply bvu | unfold PNSBAP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx8 & R8 & M8 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG8 & _ & FRZ8 & MS8 & KS8 & T1 & T2 & T8' & T9' & T10' & T11' & T18' & T19' & TE)); PMK.pvz_clrT.
  apply (PNBK2.brel_piece_stk RSEGS AD AN L HI KH 7 LBX sp fb str E0 M7 model7 _ s' sm1 ax1 fx7 fx8 R7 R8 0x38298 0x38960 M8
           (fun a => fb + 40 + 400 <= a < fb + 40 + 400 + 8) (stk1 ++ [c]) [] [] K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec));
    cbn [s' PNM.b_stk PNM.b_sb PNM.b_sk].
  { rewrite app_nil_r. reflexivity. }
  { intros a Pa. right. left. lia. }
  { rewrite app_nil_r, length_app. cbn [length]. replace (Bn + 40 * Z.of_nat (length stk1 + 1)) with (Bn + 40 * m + 40) by lia. replace (fb + 440) with (fb + 40 + 400) by lia. exact TE. }
  { intros i Hi. cbn in Hi. lia. }
  { rewrite app_nil_r, length_app, P2. cbn [length]. lia. }
  intros BR8.
  apply (bd_fin 0x38960 K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model7 _ _ sm1 ax1 (bd_ret r) CTX KONT BR8 T1 T2); [PMK.rk| PMK.rk| exact T8'| exact T9'| exact T18'| exact T19'| | | cbn [s' PNBO.set_stk PNM.b_bb]; exact EBB].
  { intros j Hj. rewrite (KS8 j) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). rewrite (PMK.cs_of_preserved R6 R7 j RP67) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto).
    rewrite (KS6 j) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). rewrite (KS5 j) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto).
    rewrite (KS4 j) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). rewrite (PMK.cs_of_preserved R2 R3 j RP23) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto).
    apply YK2. exact Hj. }
  right. split; [apply (ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
  assert (OKc : PNM.bstate_ok c).
  { unfold PNM.bstate_ok. cbn [c PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    pose proof (bvu (AxSymExec3.AX2.ext_val true 0 4 (Z_to_bv 64 lenv))) as BL. lia. }
  split.
  { unfold PNR.binv. cbn [s' PNBO.set_stk PNM.b_done PNM.b_stk]. rewrite app_nil_r. split; [exact ID1|].
    apply (bstack_shape_push stk1 c SH1); [unfold PNM.MAX_DEPTH; lia| exact OKc| unfold PNR.bmode_cont; cbn; lia]. }
  unfold PNR.bpush_rel. right. exists c. cbn [s' PNBO.set_stk PNM.b_stk PNM.b_src]. rewrite app_nil_r.
  split; [rewrite ESTK; reflexivity|]. split; [exact OKc|]. split; [unfold PNR.bmode_cont; cbn; lia|]. split; [reflexivity| exact UNR4].
Qed.

End WithHeap.
End PNSBAG.
