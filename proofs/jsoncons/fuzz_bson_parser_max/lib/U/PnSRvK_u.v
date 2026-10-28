(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Znumtheory FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSRvTP_u
     Bs0_code_36f50_36f54_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVK.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

(* [comment removed for export] *)
Definition sregs : list nat := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma ec_agree (M M' : mem) o v c : L5C.agree_on M M' o 16 -> 0 <= o -> o + 16 <= 2 ^ 64 -> PMSP.ec_at RSEGS M o v c -> PMSP.ec_at RSEGS M' o v c.
Proof.
  intros AG H1 H2 (E0 & E8 & ED). split; [|split].
  - apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
  - apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
  - apply (L5C.defined_agree M M' o 16 AG ED).
Qed.
Lemma mod16_sub176 sp : sp mod 16 = 0 -> (sp - 96) mod 16 = 0.
Proof. intros H. replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.
Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PieceTb.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable vp : Z.
Variables M M' : mem.
Variable X : Z -> Prop.
Hypothesis FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis MG : mem_grows M M'.
Let Y : Z -> Prop := fun _ => True.
Let NT : Z -> Prop := fun a => ~ X a.
Let AGX := (PNBO.AGX M M' X FRZ).
Let DKY := (PNBO.DKY M M' MG).
Let src_keep_x := (PNBO.src_keep_x segs M M' NT AGX).
Let v8_keep_x := (PNBO.v8_keep_x segs M M' NT Y AGX DKY).
Let vstr_keep_x := (PNBO.vstr_keep_x segs M M' NT Y AGX DKY).
Let bvec_keep_x := (PNBO.bvec_keep_x segs M M' NT AGX).
Let bparser_at_xfer := (PNBO.bparser_at_xfer segs A vp M M' NT Y AGX DKY).
Local Ltac yt := first [ exact (fun _ _ => I) | exact (fun _ _ _ _ _ => I) ].
Lemma bparser_set_tb op ois s x' :
  0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> PNM.bparser_at segs A PMSP.T3 PMSP.T4 vp M op ois s ->
  (forall a, op <= a < op + PNM.PSIZE -> X a -> op + PNM.OFF_TB <= a < op + PNM.OFF_TB + 24) ->
  (forall i, PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK -> ~ X i) ->
  (forall i, PNM.b_sb s <= i < PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s -> ~ X i) ->
  0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 -> 0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  PM.vstr_at segs PMSP.T3 M' (op + PNM.OFF_TB) x' ->
  PNM.bparser_at segs A PMSP.T3 PMSP.T4 vp M' op ois (PNBO.set_tb s x' (PNM.b_tg s)).
Proof.
  intros Ho Ho' PA XW NXq NXs Hq0 Hq1 Hb0 Hb1 TB'. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.BSZ in *.
  assert (NX : forall i, op <= i < op + 416 -> ~ (op + 368 <= i < op + 368 + 24) -> ~ X i) by (intros i Hi N Xi; apply N; apply XW; [exact Hi| exact Xi]).
  apply (bparser_at_xfer op ois s (PNBO.set_tb s x' (PNM.b_tg s)) Ho Ho' PA (fun _ _ => I)); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNBO.set_tb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - intros i Hi. apply NX; lia.
  - apply (L5C.u8_at_agree segs M M'); [apply AGX; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply AGX; [lia|lia|intros i Hi; apply NX; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply src_keep_x; [lia|lia|lia|lia| intros i Hi; apply NX; lia| exact NXq| exact SRC].
  - apply v8_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| exact BB].
  - apply vstr_keep_x; [lia|lia| intros i Hi; apply NX; lia| yt| yt| exact NB].
  - exact TB'.
  - unfold PNM.BSZ. apply bvec_keep_x; [lia|lia|lia|unfold PNM.BSZ; lia| intros i Hi; apply NX; lia| unfold PNM.BSZ; exact NXs| exact STK].
Qed.
End PieceTb.

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

Hypothesis MKE : PNRS.make_ec_spec L HI.

(* [comment removed for export] *)
Definition rv_kont (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.brun_post RSEGS AD AN true PNR.bprog_value R' M' fb s s' str sm sm' ax ax' cat e ->
      L5C.hpres L LBX sp (PMSP.pm_scr 8) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) (pot s') ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition rv_ctx (t : Z) (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb e : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit)
           (s : PNM.bpst) (sm : PM.strm) : Prop :=
  0 <= t < 256 /\ K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr /\ PNR.binv s /\ PM.unread (PNM.b_src s) sm < 2 ^ 26 /\ 0 <= e <= 64 /\ PNR.bb_room s sm.
(* [comment removed for export] *)
Definition rv_saved (R : bvmap 5 word) (M1 : mem) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) r
  /\ (forall i, (i < 5)%nat -> L5.u64_at RSEGS M1 (sp - 16 - 8 * Z.of_nat i) (bv_unsigned (getr R (PMK.reg (nth i sregs 0%nat))))).
Lemma rv_saved_agree R (M1 M2 : mem) sp r :
  (forall a n, sp - 48 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n) -> 0 <= sp - 96 -> sp <= 2 ^ 64 -> rv_saved R M1 sp r -> rv_saved R M2 sp r.
Proof.
  intros AG H1 H2 (S8 & SR). split.
  - apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact S8].
  - intros i Hi. apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact (SR i Hi)].
Qed.
(* [comment removed for export] *)
Lemma rv_saved_cells R (M1 : mem) sp r :
  rv_saved R M1 sp r ->
  L5.u64_at RSEGS M1 (sp - 8) r
  /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
  /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
  /\ L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))).
Proof.
  intros (S8 & SR). split; [exact S8|].
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- L5.u64_at _ _ (sp - ?o) _ =>
      let T := fresh "T" in
      first [ pose proof (SR 0%nat ltac:(lia)) as T; cbn [nth sregs] in T; lazymatch type of T with L5.u64_at _ _ ?a _ => replace a with (sp - o) in T by lia end; exact T
            | pose proof (SR 1%nat ltac:(lia)) as T; cbn [nth sregs] in T; lazymatch type of T with L5.u64_at _ _ ?a _ => replace a with (sp - o) in T by lia end; exact T
            | pose proof (SR 2%nat ltac:(lia)) as T; cbn [nth sregs] in T; lazymatch type of T with L5.u64_at _ _ ?a _ => replace a with (sp - o) in T by lia end; exact T
            | pose proof (SR 3%nat ltac:(lia)) as T; cbn [nth sregs] in T; lazymatch type of T with L5.u64_at _ _ ?a _ => replace a with (sp - o) in T by lia end; exact T
            | pose proof (SR 4%nat ltac:(lia)) as T; cbn [nth sregs] in T; lazymatch type of T with L5.u64_at _ _ ?a _ => replace a with (sp - o) in T by lia end; exact T ]
  end.
Qed.
Lemma rv_saved_intro R (M1 : mem) sp r :
  L5.u64_at RSEGS M1 (sp - 8) r ->
  L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) -> L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) ->
  L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) -> L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) ->
  L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))) ->
  rv_saved R M1 sp r.
Proof.
  intros S8 T0 T1 T2 T3 T4. split; [exact S8|].
  intros i Hi.
  destruct i as [|[|[|[|[|i]]]]]; [| | | | | lia]; cbn [nth sregs];
    lazymatch goal with |- L5.u64_at _ _ (sp - 16 - ?o) _ => let n := eval vm_compute in (16 + o) in replace (sp - 16 - o) with (sp - n) by lia end;
    assumption.
Qed.
Lemma rv_sx_words (R R5 : bvmap 5 word) :
  (forall k, In k [21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  getr R5 (PMK.reg 21) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 21))) /\ getr R5 (PMK.reg 22) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 22)))
  /\ getr R5 (PMK.reg 23) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 23))) /\ getr R5 (PMK.reg 24) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 24)))
  /\ getr R5 (PMK.reg 25) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 25))) /\ getr R5 (PMK.reg 26) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 26)))
  /\ getr R5 (PMK.reg 27) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 27))).
Proof.
  intros SX.
  assert (W : forall k, In k [21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg k))))
    by (intros k Hk; rewrite (SX k Hk); symmetry; apply Z_to_bv_bv_unsigned).
  refine (conj (W 21%nat _) (conj (W 22%nat _) (conj (W 23%nat _) (conj (W 24%nat _) (conj (W 25%nat _) (conj (W 26%nat _) (W 27%nat _))))))); PMK.inl.
Qed.

(* [comment removed for export] *)
Definition rv_restored (R R5 : bvmap 5 word) (sp r : Z) : Prop :=
  getr R5 (PMK.reg 1) = Z_to_bv 64 r /\ getr R5 (PMK.reg 2) = Z_to_bv 64 sp
  /\ getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ (forall k, In k sregs -> getr R5 (PMK.reg k) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg k)))).
Lemma rv_restored_intro (R R5 : bvmap 5 word) sp r :
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R5 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R5 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  getr R5 (PMK.reg 20) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 20))) -> getr R5 (PMK.reg 21) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 21))) ->
  getr R5 (PMK.reg 22) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 22))) -> getr R5 (PMK.reg 23) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 23))) ->
  getr R5 (PMK.reg 24) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 24))) -> getr R5 (PMK.reg 25) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 25))) ->
  getr R5 (PMK.reg 26) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 26))) -> getr R5 (PMK.reg 27) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 27))) ->
  rv_restored R R5 sp r.
Proof.
  intros Y1 Y2 Y3 Y4 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 Y27.
  split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
  intros k Hk. cbn in Hk.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; assumption.
Qed.

(* [comment removed for export] *)
Definition rv_post (fb cat e : Z) (s : PNM.bpst) (sm : PM.strm) (R5 : bvmap 5 word) (M5 : mem) (s5 : PNM.bpst) (sm5 : PM.strm) (ax5 : PNST.bax) : Prop :=
  (   ((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M5 (fb + 16) v (pa_errcat_obj AD)) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true
       /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bpush_rel s s5 sm sm5))
  /\ (PNR.bb_room s sm -> PNM.b_more s5 = 1 -> PNR.bb_room s5 sm5).

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rv_ret t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  rv_restored R R5 sp r -> rv_post fb cat e s sm R5 M5 s5 sm5 ax5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x37d94 M5 model5) K.
Proof.
  intros (Ht & K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0) KONT BR (Y1 & Y2 & Y3 & Y4 & YK) (POST & BB).
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx5 R5 M5 0x37d94 W_36ff4 r F_36ff4 eq_refl D_36ff4); [exact Y1| lia| exact Hr2]. }
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite YK by (cbn; tauto); apply Z_to_bv_bv_unsigned ].
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
Definition tv (sp r fb : Z) (R : bvmap 5 word) (x : nat -> Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 36%nat => fb + 16 | 37%nat => r
  | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9))
  | 40%nat => bv_unsigned (getr R (PMK.reg 18)) | 41%nat => bv_unsigned (getr R (PMK.reg 19))
  | 42%nat => bv_unsigned (getr R (PMK.reg 20)) | 43%nat => bv_unsigned (getr R (PMK.reg 21))
  | 44%nat => bv_unsigned (getr R (PMK.reg 22)) | 45%nat => bv_unsigned (getr R (PMK.reg 23))
  | 46%nat => bv_unsigned (getr R (PMK.reg 24)) | 47%nat => bv_unsigned (getr R (PMK.reg 25))
  | 48%nat => bv_unsigned (getr R (PMK.reg 26)) | 49%nat => bv_unsigned (getr R (PMK.reg 27))
  | _ => x j
  end.

Lemma b_set_more s v :
  PNM.b_more (PNBO.set_more s v) = v /\ PNM.b_done (PNBO.set_more s v) = PNM.b_done s /\ PNM.b_src (PNBO.set_more s v) = PNM.b_src s
  /\ PNM.b_bb (PNBO.set_more s v) = PNM.b_bb s /\ PNM.b_stk (PNBO.set_more s v) = PNM.b_stk s.
Proof. destruct s; cbn; repeat split; reflexivity. Qed.
Lemma binv_set_more s v : PNR.binv s -> PNR.binv (PNBO.set_more s v).
Proof. intros (D & SH). unfold PNR.binv. destruct s; cbn in *. split; [exact D| exact SH]. Qed.
Lemma bpush_rel_set_more s s5 sm sm5 v : PNR.bpush_rel s s5 sm sm5 -> PNR.bpush_rel s (PNBO.set_more s5 v) sm sm5.
Proof.
  intros H. unfold PNR.bpush_rel, PNR.btop_pos in *. destruct s5; cbn [PNBO.set_more PNM.b_stk PNM.b_src] in *. exact H.
Qed.
Lemma bb_room_set_more s5 sm5 v : PNR.bb_room s5 sm5 -> PNR.bb_room (PNBO.set_more s5 v) sm5.
Proof. unfold PNR.bb_room. destruct s5; cbn. intros H; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rv_epi t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  getr R5 (PMK.reg 2) = Z_to_bv 64 (sp - 96) -> getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (fb + 16) -> getr R5 (PMK.reg 18) = Z_to_bv 64 (fb + 464) ->
  rv_saved R M5 sp r -> (forall k, In k [21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  rv_post fb cat e s sm R5 M5 s5 sm5 ax5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x37d78 M5 model5) K.
Proof.
  intros CTX KONT BR5 X2 X3 X4 X8 X9 X18 SV5 SX5 POST.
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof (rv_saved_cells R M5 sp r SV5) as (S8 & T8 & T9 & T18 & T19 & T20).
  pose proof (rv_sx_words R R5 SX5) as (X21 & X22 & X23 & X24 & X25 & X26 & X27).
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BUR_20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BUR_21.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BUR_22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BUR_23.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BUR_24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BUR_25.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 26))) as BUR_26. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 27))) as BUR_27.
  (let T := type of (PNSRVTP.vlT2_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlT2_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
  pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y2 & Y8 & Y9 & Y18 & Y19 & Y20)); PMK.pvz_clrT.
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx5 fx6 R5 R6 0x37d78 0x37d94 M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  apply (rv_ret t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M5 model5 cr5 s5 sm5 ax5 CTX KONT BR6); [| exact POST].
  apply (rv_restored_intro R R6 sp r Y1 Y2); [rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| rewrite (KS6 21%nat) by PMK.inl; exact X21| rewrite (KS6 22%nat) by PMK.inl; exact X22
    | rewrite (KS6 23%nat) by PMK.inl; exact X23| rewrite (KS6 24%nat) by PMK.inl; exact X24| rewrite (KS6 25%nat) by PMK.inl; exact X25
    | rewrite (KS6 26%nat) by PMK.inl; exact X26| rewrite (KS6 27%nat) by PMK.inl; exact X27].
Qed.

(* [comment removed for export] *)
Definition rv_mid (R R5 : bvmap 5 word) (M5 : mem) (sp r fb : Z) : Prop :=
  getr R5 (PMK.reg 2) = Z_to_bv 64 (sp - 96) /\ getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ getr R5 (PMK.reg 8) = Z_to_bv 64 (fb + 40) /\ getr R5 (PMK.reg 9) = Z_to_bv 64 (fb + 16) /\ getr R5 (PMK.reg 18) = Z_to_bv 64 (fb + 464)
  /\ rv_saved R M5 sp r /\ (forall k, In k [21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)).
Lemma rv_mid_intro (R R5 : bvmap 5 word) (M5 : mem) sp r fb :
  getr R5 (PMK.reg 2) = Z_to_bv 64 (sp - 96) -> getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (fb + 16) -> getr R5 (PMK.reg 18) = Z_to_bv 64 (fb + 464) ->
  rv_saved R M5 sp r -> (forall k, In k [21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) -> rv_mid R R5 M5 sp r fb.
Proof.
  intros X2 X3 X4 X8 X9 X18 SV SX. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X8|]. split; [exact X9|].
  split; [exact X18|]. split; [exact SV| exact SX].
Qed.
(* [comment removed for export] *)
Lemma rv_mid_xfer (R R5 R6 : bvmap 5 word) (M5 M6 : mem) sp r fb (ks : list nat) :
  rv_mid R R5 M5 sp r fb ->
  (forall k, In k ks -> getr R6 (PMK.reg k) = getr R5 (PMK.reg k)) ->
  (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> In k ks) ->
  (forall a n, sp - 48 <= a -> a + n <= sp -> L5C.agree_on M5 M6 a n) -> 0 <= sp - 96 -> sp <= 2 ^ 64 ->
  rv_mid R R6 M6 sp r fb.
Proof.
  intros (X2 & X3 & X4 & X8 & X9 & X18 & SV & SX) KS SUB AG H1 H2.
  split; [rewrite (KS 2%nat) by (apply SUB; cbn; tauto); exact X2|]. split; [rewrite (KS 3%nat) by (apply SUB; cbn; tauto); exact X3|].
  split; [rewrite (KS 4%nat) by (apply SUB; cbn; tauto); exact X4|]. split; [rewrite (KS 8%nat) by (apply SUB; cbn; tauto); exact X8|].
  split; [rewrite (KS 9%nat) by (apply SUB; cbn; tauto); exact X9|]. split; [rewrite (KS 18%nat) by (apply SUB; cbn; tauto); exact X18|].
  split; [apply (rv_saved_agree R M5 M6 sp r AG H1 H2 SV)|].
  intros k Hk. rewrite (KS k) by (apply SUB; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). exact (SX k Hk).
Qed.
Lemma rv_mid_pres (R R5 R6 : bvmap 5 word) (M5 M6 : mem) sp r fb :
  rv_mid R R5 M5 sp r fb -> regs_preserved R5 R6 ->
  (forall a n, sp - 48 <= a -> a + n <= sp -> L5C.agree_on M5 M6 a n) -> 0 <= sp - 96 -> sp <= 2 ^ 64 ->
  rv_mid R R6 M6 sp r fb.
Proof.
  intros MID RP AG H1 H2. apply (rv_mid_xfer R R5 R6 M5 M6 sp r fb PMK.cs_all MID); [| | exact AG| exact H1| exact H2].
  - intros k Hk. apply (PMK.cs_of_preserved R5 R6 k RP Hk).
  - intros k Hk. cbn in Hk. unfold PMK.cs_all. cbn. tauto.
Qed.

Local Ltac burs R :=
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8; pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9;
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18; pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19;
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BUR_20; pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BUR_21;
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BUR_22; pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BUR_23;
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BUR_24; pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BUR_25;
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 26))) as BUR_26; pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 27))) as BUR_27.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rv_sbmore t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 v :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  rv_mid R R5 M5 sp r fb -> getr R5 (PMK.reg 10) = Z_to_bv 64 v ->
  (   (v = 0 /\ (exists w, 1 <= w <= 64 /\ PMSP.ec_at RSEGS M5 (fb + 16) w (pa_errcat_obj AD)) /\ PNST.bax_cat ax5 = true
       /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (v = 1 /\ PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bpush_rel s s5 sm sm5 /\ (PNR.bb_room s sm -> PNR.bb_room s5 sm5))) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x37d74 M5 model5) K.
Proof.
  intros CTX KONT BR5 (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5) X10 POST.
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof PA5 as (_ & PD5 & _).
  assert (WP5 : L5.writable RSEGS M5 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD5|lia|lia]).
  pose proof (rv_saved_cells R M5 sp r SV5) as (S8 & T8 & T9 & T18 & T19 & T20).
  pose proof (rv_sx_words R R5 SX5) as (X21 & X22 & X23 & X24 & X25 & X26 & X27).
  burs R.
  assert (Hv : 0 <= v <= 1) by (destruct POST as [(-> & _)|(-> & _)]; lia).
  (let T := type of (PNSRVTP.vlT1_conc fx5 R5 M5 (tv sp r fb R (fun j => match j with 53%nat => v | _ => 0 end))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlT1_conc fx5 R5 M5 (tv sp r fb R (fun j => match j with 53%nat => v | _ => 0 end))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
  pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG6 & _ & FRZ6 & MS6 & KS6 & Y1 & Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & MO6)); PMK.pvz_clrT.
  apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx5 fx6 R5 R6 0x37d74 0x37d94 M6
           (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) v K ltac:(lia) BR5 FOK INCS MS6 MG6 FRZ6 ltac:(intros a; apply PMK.rng_dec)
           ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO6) ltac:(lia)).
  intros BR6.
  assert (AG56 : L5C.agree_on M5 M6 (fb + 16) 16) by (intros i Hi; apply FRZ6; lia).
  apply (rv_ret t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M6 model5 cr5 _ sm5 ax5 CTX KONT BR6).
  - apply (rv_restored_intro R R6 sp r Y1 Y2); [rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
      | exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| rewrite (KS6 21%nat) by PMK.inl; exact X21| rewrite (KS6 22%nat) by PMK.inl; exact X22
      | rewrite (KS6 23%nat) by PMK.inl; exact X23| rewrite (KS6 24%nat) by PMK.inl; exact X24| rewrite (KS6 25%nat) by PMK.inl; exact X25
      | rewrite (KS6 26%nat) by PMK.inl; exact X26| rewrite (KS6 27%nat) by PMK.inl; exact X27].
  - pose proof (b_set_more s5 v) as (BM & BD & BS & BB & BK). split.
    + destruct POST as [(-> & (w & Hw & EC5) & CAT & LEN & INV5)|(-> & EC5 & INV5 & PR & RM)].
      * left. split; [exists w; split; [exact Hw| apply (ec_agree M5 M6 _ _ _ AG56 ltac:(lia) ltac:(lia) EC5)]|].
        split; [exact BM|]. split; [exact CAT|]. split; [rewrite BK; exact LEN| apply binv_set_more; exact INV5].
      * right. split; [apply (ec_agree M5 M6 _ _ _ AG56 ltac:(lia) ltac:(lia) EC5)|]. split; [apply binv_set_more; exact INV5| apply bpush_rel_set_more; exact PR].
    + intros R0 M1. destruct POST as [(-> & _)|(-> & _ & _ & _ & RM)]; [rewrite BM in M1; lia|]. apply bb_room_set_more. apply RM. exact R0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rv_errtail t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 w :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  rv_mid R R5 M5 sp r fb ->
  1 <= w <= 64 -> PMSP.ec_at RSEGS M5 (fb + 16) w (pa_errcat_obj AD) -> PNST.bax_cat ax5 = true ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNR.binv s5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x37700 M5 model5) K.
Proof.
  intros CTX KONT BR5 (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5) Hw EC5 CAT LEN INV5.
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof PA5 as (_ & PD5 & _).
  assert (WP5 : L5.writable RSEGS M5 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD5|lia|lia]).
  pose proof (rv_saved_cells R M5 sp r SV5) as (S8 & T8 & T9 & T18 & T19 & T20).
  pose proof (rv_sx_words R R5 SX5) as (X21 & X22 & X23 & X24 & X25 & X26 & X27).
  burs R.
  assert (STEP : exists (fx6 : FPState) R6 (M6 : mem),
            mem_grows M5 M6 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (fb + 40 + 8 <= i < fb + 40 + 8 + 1) -> M6 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i))
            /\ msteps RSEGS (@mkst fx5 R5 (Z_to_bv 64 0x37700) M5 (seg_rom RSEGS)) (@mkst fx6 R6 (Z_to_bv 64 0x37d94) M6 (seg_rom RSEGS))
            /\ getr R6 (PMK.reg 3) = getr R5 (PMK.reg 3) /\ getr R6 (PMK.reg 4) = getr R5 (PMK.reg 4)
            /\ rv_restored R R6 sp r /\ L5.u8_at RSEGS M6 (fb + 40 + 8) 0).
  { (let T := type of (PNSRVTP.vlTA_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlTA_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
    pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG6 & _ & FRZ6 & MS6 & KS6 & Y1 & Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & MO6)); PMK.pvz_clrT.
    exists fx6, R6, M6. split; [exact MG6|]. split; [exact FRZ6|]. split; [exact MS6|].
    split; [apply KS6; PMK.inl|]. split; [apply KS6; PMK.inl|]. split; [| exact MO6].
    apply (rv_restored_intro R R6 sp r Y1 Y2); [rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
      | exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| rewrite (KS6 21%nat) by PMK.inl; exact X21| rewrite (KS6 22%nat) by PMK.inl; exact X22
      | rewrite (KS6 23%nat) by PMK.inl; exact X23| rewrite (KS6 24%nat) by PMK.inl; exact X24| rewrite (KS6 25%nat) by PMK.inl; exact X25
      | rewrite (KS6 26%nat) by PMK.inl; exact X26| rewrite (KS6 27%nat) by PMK.inl; exact X27]. }
  destruct STEP as (fx6 & R6 & M6 & MG6 & FRZ6 & MS6 & K3 & K4 & RST & MO6).
  apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx5 fx6 R5 R6 _ 0x37d94 M6
           (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR5 FOK INCS MS6 MG6 FRZ6 ltac:(intros a; apply PMK.rng_dec)
           ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO6) ltac:(lia)).
  intros BR6.
  assert (AG56 : L5C.agree_on M5 M6 (fb + 16) 16) by (intros i Hi; apply FRZ6; lia).
  pose proof (b_set_more s5 0) as (BM & BD & BS & BB & BK).
  apply (rv_ret t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M6 model5 cr5 _ sm5 ax5 CTX KONT BR6 RST).
  split.
  - left. split; [exists w; split; [exact Hw| apply (ec_agree M5 M6 _ _ _ AG56 ltac:(lia) ltac:(lia) EC5)]|].
    split; [exact BM|]. split; [exact CAT|]. split; [rewrite BK; exact LEN| apply binv_set_more; exact INV5].
  - intros _ M1. rewrite BM in M1. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_mkec v t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx6 : FPState) R6 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  rv_mid R R6 M5 sp r fb -> L5.defined M5 (fb + 16) 16 ->
  getr R6 (PMK.reg 1) = Z_to_bv 64 0x37700 ->
  getr R6 (PMK.reg 10) = Z_to_bv 64 (fb + 16) -> getr R6 (PMK.reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNR.binv s5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0x36ee4 M5 model5) K.
Proof.
  intros CTX KONT BR5 MID ED5 Y1 Y10 Y11 HV LEN INV5. pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5).
  change (@PMSP.cfg RSEGS fx6 R6 0x36ee4 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_make_ec AD) M5 model5).
  pose proof MKE as MKE'. unfold PNRS.make_ec_spec in MKE'.
  apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx6 R6 (sp - 96) 0x37700 v K MKE' ltac:(lia) K0 BR5 FOK INCS Y1);
    [split; [lia| reflexivity]| exact X2| exact X3| exact X4
    | exact Y10| exact Y11| exact HV| lia| unfold PMSP.pm_scr; lia| exact (mod16_sub176 sp A16)| exact ED5|].
  intros fx7 R7 M7 RP67 EC7 BR7 AG67.
  apply (rv_errtail t K LBX sp r fb cat e str R M model cr s sm ax fx7 R7 M7 model5 cr5 s5 sm5 _ v CTX KONT BR7); [| exact HV| exact EC7| apply bax_cat_add| exact LEN| exact INV5].
  apply (rv_mid_pres R R6 R7 M5 M7 sp r fb MID RP67); [intros a n H1 H2; apply AG67; lia| lia| lia].
Qed.

(* [comment removed for export] *)
Definition rv_errhead (pce v : Z) : Prop :=
  (pce = 0x37d98 /\ v = 1) \/ (pce = 0x37da0 /\ v = 3) \/ (pce = 0x37da8 /\ v = 6) \/ (pce = 0x376f4 /\ v = 14).
Lemma rv_err pce v t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  rv_errhead pce v ->
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  rv_mid R R5 M5 sp r fb -> L5.defined M5 (fb + 16) 16 ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNR.binv s5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pce M5 model5) K.
Proof.
  intros HD CTX KONT BR5 MID ED5 LEN INV5. pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  assert (HV : 1 <= v <= 64) by (unfold rv_errhead in HD; lia).
  (* [comment removed for export] *)
  assert (STEP : exists (fx6 : FPState) R6,
            msteps RSEGS (@mkst fx5 R5 (Z_to_bv 64 pce) M5 (seg_rom RSEGS)) (@mkst fx6 R6 (Z_to_bv 64 0x36ee4) M5 (seg_rom RSEGS))
            /\ (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (PMK.reg k) = getr R5 (PMK.reg k))
            /\ getr R6 (PMK.reg 1) = Z_to_bv 64 0x37700
            /\ getr R6 (PMK.reg 10) = Z_to_bv 64 (fb + 16) /\ getr R6 (PMK.reg 11) = Z_to_bv 64 v).
  { unfold rv_errhead in HD.
    destruct (Z.eq_dec pce 0x37d98) as [->|N1].
    { assert (Hv1 : v = 1) by lia. subst v.
      (let T := type of (PNSRVTP.vlR1_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlR1_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
      destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11).
      assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
      exists fx6, R6. split; [exact MS6|]. split; [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact Y1|]. split; [exact Y10| exact Y11]. }
    destruct (Z.eq_dec pce 0x37da0) as [->|N2].
    { assert (Hv1 : v = 3) by lia. subst v.
      (let T := type of (PNSRVTP.vlR3_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlR3_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
      destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11).
      assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
      exists fx6, R6. split; [exact MS6|]. split; [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact Y1|]. split; [exact Y10| exact Y11]. }
    destruct (Z.eq_dec pce 0x37da8) as [->|N4].
    { assert (Hv1 : v = 6) by lia. subst v.
      (let T := type of (PNSRVTP.vlR6_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlR6_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
      destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11).
      assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
      exists fx6, R6. split; [exact MS6|]. split; [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      split; [exact Y1|]. split; [exact Y10| exact Y11]. }
    assert (E5 : pce = 0x376f4 /\ v = 14) by lia. destruct E5 as (-> & ->).
    (let T := type of (PNSRVTP.vlR14_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [tv] in T in LeanFeed.pfeed_at P (PNSRVTP.vlR14_conc fx5 R5 M5 (tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [tv]) ltac:(first [PMK.sc | unfold PNSRVTP.aligned; PMK.sc])).
    destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11).
    assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
    exists fx6, R6. split; [exact MS6|]. split; [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
    split; [exact Y1|]. split; [exact Y10| exact Y11]. }
  destruct STEP as (fx6 & R6 & MS6 & KS6 & Y1 & Y10 & Y11).
  pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh5| exact Ml5| exact MS6|].
  change (mkCfg (@mkst fx6 R6 (Z_to_bv 64 0x36ee4) M5 (seg_rom RSEGS)) model5) with (@PMSP.cfg RSEGS fx6 R6 0x36ee4 M5 model5).
  apply (rv_mkec v t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M5 model5 cr5 s5 sm5 ax5 CTX KONT BR5); [| exact ED5| exact Y1| exact Y10| exact Y11| exact HV| exact LEN| exact INV5].
  apply (rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_call_fb bb pc hg args prog LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' cat e : Z) K :
  PNR.brun_spec_fb RSEGS AD AN L HI bb fb pc hg args prog ->
  0 <= hg -> K [] ->
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok AD L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (PNBK.be_s E0)) (PNBK.be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  sp' <= sp -> sp - PMSP.pm_scr 8 <= sp' - PMSP.pm_scr hg -> sp' mod 16 = 0 ->
  args R1 fb s1 sm1 -> PNR.binv s1 -> PMSP.ec_at RSEGS M1 (fb + 16) e cat -> 0 <= e <= 64 -> PM.unread (PNM.b_src s1) sm1 < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 s2 sm2 ax2 cr2,
      regs_preserved R1 R2 ->
      PNR.brun_post RSEGS AD AN bb prog R2 M2 fb s1 s2 str sm1 sm2 ax1 ax2 cat e ->
      brel LBX sp fb str E0 (BENT M2 model2 cr2 s2 sm2 ax2) ->
      (forall a n, sp' <= a -> a + n <= fb + 16 -> L5C.agree_on M1 M2 a n) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 r' M2 model2) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc M1 model1) K.
Proof.
  intros SPEC Hg K0 BR FOK INCS CRED0 X1 RA X2 X3 X4 S1 S2 S3 ARGS INV EC He UNR KONT.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in RP, STEP, AXL, HP, CK, MB, HH, STK, MOK.
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg 8 ltac:(lia)) as SC0. pose proof (PNBK.scr_nonneg hg Hg) as SCg. pose proof (PMK.kl_img RSEGS L KL) as (IMG0 & IMG1).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' (PMSP.pm_scr hg)) by (apply (PMK.stk_call L M1 sp (PMSP.pm_scr 8) sp' (PMSP.pm_scr hg) STK); [exact S1| exact S2| exact SCg| exact S3]).
  assert (CRED1 : PMSP.credit_le (pot s1) cr1) by (unfold PMSP.credit_le, PMSP.credit_keep in *; lia).
  unfold PNR.brun_spec_fb in SPEC.
  apply (SPEC fx1 R1 M1 model1 K LBX cr1 sp' r' cat e s1 str sm1 ax1 HH MOK K0).
  - unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact STKc].
  - unfold PMSP.frame_ok. cbn [pa_frame AD PnLayoutS_u.ADDR_S]. split; [lia|]. split; [exact F2| exact F3].
  - exact ARGS.
  - exact RP.
  - exact INCS.
  - exact INV.
  - unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S]. exact EC.
  - exact He.
  - exact UNR.
  - exact CRED1.
  - intros fx2 R2 M2 model2 s2 sm2 ax2 cr2 RP12 POST HP2 CK2 MB2 HH2.
    pose proof POST as (RP2 & STEP2 & AXL2 & _).
    pose proof (PMK.stk_after RSEGS L KL LBX M1 M2 sp (PMSP.pm_scr 8) sp' (PMSP.pm_scr hg) _ STK HP2 S1 S2 SCg) as STK2.
    apply (KONT fx2 R2 M2 model2 s2 sm2 ax2 cr2 RP12 POST).
    + unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax].
      split; [exact RP2|]. split; [exact (PMPK.src_step_trans _ _ _ _ _ _ STEP STEP2)|]. split; [exact (PNST.bax_le_trans _ _ _ AXL AXL2)|].
      split.
      { apply (PMK.hpres_of L LBX sp (PMSP.pm_scr 8) _ (PNBK.be_M E0) M2).
        - apply (PMK.ek_trans L LBX sp (PMSP.pm_scr 8) _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp (PMSP.pm_scr 8) _ _ M1 HP)).
          apply (PMK.ek_callee L LBX LBX sp (PMSP.pm_scr 8) sp' (PMSP.pm_scr hg) _ _ M1 M2 HP2); [apply incl_refl| exact S2| exact S1| intros a _ O; exact O].
        - destruct STK2 as (_ & _ & _ & _ & D). exact D.
        - apply (PMK.dk_trans L LBX sp (PMSP.pm_scr 8) (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp (PMSP.pm_scr 8) _ _ M1 HP)).
          apply (PMK.dk_callee L LBX LBX sp (PMSP.pm_scr 8) sp' (PMSP.pm_scr hg) _ M1 M2 HP2); [apply incl_refl| exact S2| exact S1]. }
      split; [exact (PNBK.credit_keep_trans _ _ _ _ _ _ CK CK2)|]. split; [exact (L5C.model_but_vm_trans _ _ _ MB MB2)|].
      split; [exact HH2|]. split; [exact STK2| exact (PMFR.model_ok_but_vm model1 model2 MOK MB2)].
    + intros a n H1 H2. apply (PMKP.ek_agree_stack RSEGS L KL LBX sp' (PMSP.pm_scr hg) _ M1 M2 a n (PMK.ek_of_hpres L LBX sp' (PMSP.pm_scr hg) _ _ _ HP2) STKc SCg H1 ltac:(lia)).
      intros i Hi. apply PMFR.outside_of_not_inW. intros I. destruct (PNBK2.wrun_floor RSEGS AD AN L HI KH fb i I); [lia|].
      pose proof (PMK.kl_img RSEGS L KL). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brun_post_tail R' (M' : mem) fb s s' str sm sm' ax ax5 ax' cat e :
  PNR.brun_post RSEGS AD AN false PNR.bprog_value R' M' fb s s' str sm sm' ax5 ax' cat e -> PNST.bax_le ax ax5 ->
  PNR.brun_post RSEGS AD AN true PNR.bprog_value R' M' fb s s' str sm sm' ax ax' cat e.
Proof.
  intros (RP & STEP & AXL & DISJ & BB) AXL0. unfold PNR.brun_post. split; [exact RP|]. split; [exact STEP|]. split; [exact (PNST.bax_le_trans _ _ _ AXL0 AXL)|]. split; [exact DISJ|].
  cbn [PNR.bb_post] in BB |- *. intros R0 _. unfold PNR.bb_room in *. rewrite BB.
  apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [| exact R0]. destruct STEP as (_ & _ & _ & _ & LE). exact LE.
Qed.
Lemma rv_tail pc t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx6 : FPState) R6 (M5 : mem) model5 cr5 ax5 :
  PNR.brun_spec RSEGS AD AN L HI false pc 7 (PNR.bargs3 AD) PNR.bprog_value ->
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s sm ax5) ->
  rv_restored R R6 sp r ->
  getr R6 (PMK.reg 10) = Z_to_bv 64 (fb + 40) -> getr R6 (PMK.reg 11) = Z_to_bv 64 (fb + 464) -> getr R6 (PMK.reg 12) = Z_to_bv 64 (fb + 16) ->
  PMSP.ec_at RSEGS M5 (fb + 16) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 pc M5 model5) K.
Proof.
  intros SPEC CTX KONT BR5 (Y1 & Y2 & Y3 & Y4 & YK) X10 X11 X12 EC5.
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  assert (RP06 : regs_preserved R R6).
  { apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite YK by (cbn; tauto); apply Z_to_bv_bv_unsigned ]. }
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (_ & _ & _ & _ & (A16 & _) & _).
  apply (PNBK2.brel_call RSEGS AD AN L HI KH false pc 7 (PNR.bargs3 AD) PNR.bprog_value 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 sp r cat e K
           SPEC ltac:(lia) ltac:(lia) K0 BR5 FOK INCS CRED Y1 RAok Y2 Y3 Y4 ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) A16).
  - unfold PNR.bargs3, PNR.o_p, PNR.o_v, PNR.o_ec, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD PnLayoutS_u.ADDR_S].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact X10|]. split; [exact X11| exact X12].
  - exact INV0.
  - exact EC5.
  - exact He.
  - exact UNR0.
  - intros fx7 R7 M7 model7 s7 sm7 ax7 cr7 RP67 POST BR7 AG67.
    pose proof BR7 as (_ & _ & _ & HP7 & CK7 & MB7 & HH7 & _). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in HP7, CK7, MB7, HH7.
    pose proof BR5 as (_ & _ & AXL5 & _). cbn [PNBK.be_ax] in AXL5.
    apply (KONT fx7 R7 M7 model7 s7 sm7 ax7 cr7 (PMK.regs_preserved_trans R R6 R7 RP06 RP67) (brun_post_tail _ _ _ _ _ _ _ _ _ _ _ _ _ POST AXL5) HP7 CK7 MB7 HH7).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rv_top LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) -> PNR.binv s1 ->
  exists l c, PNM.b_stk s1 = l ++ [c] /\ PNM.bstate_ok c
    /\ L5.u64_at RSEGS M1 (fb + 40 + 400) (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40)
    /\ L5.u64_at RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) (PNM.bs_pos c)
    /\ L5.writable RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) 8
    /\ 4096 <= PNM.b_sb s1 + 40 * Z.of_nat (length l) /\ PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40 <= sp - 28672
    /\ (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40 <= 65536 \/ 0xeb000 <= PNM.b_sb s1 + 40 * Z.of_nat (length l))
    /\ (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40) mod 8 = 0.
Proof.
  intros BR INV.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  change (PMSP.pm_scr 8) with 28672 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
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
  destruct (BRG b (40 * 2 ^ k) ltac:(apply in_or_app; left; exact Bs)) as (_ & IMGA & _).
  rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in IMGA.
  split; [replace (b + 40 * n + 40) with (b + 40 * (Z.of_nat (length l + 1))) by (unfold n; lia); replace (fb + 40 + 400) with (fb + 40 + 392 + 8) by lia; exact V8|].
  pose proof (EL (length l) ltac:(lia)) as ET. rewrite nth_middle in ET. fold n in ET. destruct ET as (_ & _ & Tp & _ & _).
  split; [exact Tp|].
  split; [apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 b (40 * 2 ^ k)); [exact DB|lia|lia]|lia|lia]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  replace (b + 40 * n + 40) with (b + 8 * (5 * n + 5)) by lia. apply PMPK.m8_add. apply PMPK.m16_8. exact Hal.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_piece_tb LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) x' K :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok AD L sp fb -> incl (PM.vs_own str) LBX ->
  msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom RSEGS)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> (sp - PMSP.pm_scr 8 <= a < sp) \/ (fb + 408 <= a < fb + 432) \/ in_block (PM.vs_own (PNM.b_tb s1)) a) ->
  PM.vstr_at RSEGS PMSP.T3 M2 (fb + 408) x' -> PM.vs_own x' = PM.vs_own (PNM.b_tb s1) -> PM.vs_cap x' = PM.vs_cap (PNM.b_tb s1) ->
  (brel LBX sp fb str E0 (BENT M2 model1 cr1 (PNBO.set_tb s1 x' (PNM.b_tg s1)) sm1 ax1) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M2 model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros BR FOK INCS MS MG FRZ DEC PF VS OWNx CAPx KONT.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg 8 ltac:(lia)) as SC0.
  pose proof BR as (_ & _ & _ & _ & _ & _ & HH & _). cbn [PNBK.be_M PNBK.be_cr PNBK.be_s PNBK.be_model] in HH.
  set (LB := PNM.bparser_own s1 ++ LBX) in *.
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr1 M1 _ HH).
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bq) as (Q0 & Q4). destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in Q4, S4. unfold PNM.BSZ in S4.
  assert (TBIN : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s1)) -> In (B, m) (PNM.bparser_own s1)).
  { intros B m Hin. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
  assert (APn : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s1)) ->
            (PM.sr_qc (PNM.b_src s1) + PM.CHUNK <= B \/ B + m <= PM.sr_qc (PNM.b_src s1))
            /\ (PNM.b_sb s1 + PNM.BSZ * 2 ^ PNM.b_sk s1 <= B \/ B + m <= PNM.b_sb s1)).
  { intros B m Hin.
    assert (HB : In (B, m) LB) by (unfold LB; apply in_or_app; left; apply TBIN; exact Hin).
    assert (Hq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) LB) by (unfold LB; apply in_or_app; left; exact Bq).
    assert (Hs : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) LB) by (unfold LB; apply in_or_app; left; exact Bs).
    assert (NE1 : PM.sr_qc (PNM.b_src s1) <> B).
    { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1)) (PNM.brest_own s1 ++ LBX) _ PM.CHUNK B m);
        [unfold LB, PNM.bparser_own in NDL; rewrite <- app_assoc in NDL; exact NDL| unfold PM.src_own; cbn; auto|].
      apply in_or_app. left. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (NE2 : PNM.b_sb s1 <> B).
    { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1) ++ PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1)) (PGV8.v8_own (PNM.b_bb s1) ++ PM.vs_own (PNM.b_nb s1) ++ PM.vs_own (PNM.b_tb s1) ++ LBX) _ (PNM.BSZ * 2 ^ PNM.b_sk s1) B m);
        [unfold LB, PNM.bparser_own, PNM.brest_own in NDL; rewrite <- !app_assoc in NDL; rewrite <- !app_assoc; exact NDL
        | apply in_or_app; right; unfold PNM.bvec_own; cbn; auto
        | apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hin]. }
    split; [exact (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ _ _ _ _ HH Hq HB NE1)| exact (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ _ _ _ _ HH Hs HB NE2)]. }
  apply (PNBK.brel_piece RSEGS AD AN L HI KH 8 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P (PNBO.set_tb s1 x' (PNM.b_tg s1)) K ltac:(lia) BR FOK INCS MS MG FRZ DEC);
    [| | | reflexivity| | | exact KONT].
  - intros a Pa. destruct (PF a Pa) as [X|[X|((B, m) & Hb & Hr)]]; [left; exact X| right; left; unfold PNBK.pwr; lia|].
    right. right. exists (B, m). split; [apply TBIN; exact Hb| exact Hr].
  - apply (bparser_set_tb RSEGS AD (pa_vp_parser AD) M1 M2 P FRZ MG (fb + 40) (fb + 472) s1 x'); unfold PNM.PSIZE, PNM.OFF_TB, PNM.BSZ; try lia.
    + exact PA1.
    + intros a Ha Pa. destruct (PF a Pa) as [X|[X|((B, m) & Hb & Hr)]]; [lia| lia|]. cbn [fst snd] in Hr. destruct (OWNB B m (TBIN B m Hb)). lia.
    + intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| lia|]. cbn [fst snd] in Hr. destruct (APn B m Hb) as (AP & _). lia.
    + intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| lia|]. cbn [fst snd] in Hr. destruct (APn B m Hb) as (_ & AP). unfold PNM.BSZ in AP. lia.
    + replace (fb + 40 + 368) with (fb + 408) by lia. exact VS.
  - unfold PNM.bparser_own, PNM.brest_own. cbn [PNBO.set_tb PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. rewrite OWNx. reflexivity.
  - unfold PNR.pot_bparser. cbn [PNBO.set_tb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. unfold PM.pot_text. rewrite CAPx. reflexivity.
  - unfold PNM.bgrow_ok in *. cbn [PNBO.set_tb PNM.b_nb PNM.b_ng PNM.b_tb PNM.b_tg PNM.b_bb PNM.b_bg]. destruct GR1 as (G1 & G2 & G3).
    split; [exact G1| split; [| exact G3]].
    unfold PM.tb_ok in *. rewrite CAPx. destruct G2 as (T1 & T2 & T3). split; [exact T1|]. split; [exact T2|].
    destruct x' as [n'|c' n' p']; destruct (PNM.b_tb s1) as [n0|c0 n0 p0]; cbn [PM.vs_own PM.vs_cap] in OWNx, CAPx, T3 |- *; try exact T3.
    + discriminate OWNx.
    + discriminate OWNx.
    + injection OWNx as E1 E2. subst. exact T3.
Qed.

(* [comment removed for export] *)
Lemma tb_facts (M1 : mem) fb s1 :
  bparser_at M1 (fb + 40) (fb + 472) s1 ->
  match PNM.b_tb s1 with
  | PM.VShort n => 0 <= n <= 22 /\ L5.u8_at RSEGS M1 (fb + 40 + 368) (2 * n) /\ L5.defined M1 (fb + 408) 24
  | PM.VLong c n p => L5.u8_at RSEGS M1 (fb + 40 + 368) ((c + 1) mod 256) /\ L5.u64_at RSEGS M1 (fb + 40 + 376) n /\ L5.u64_at RSEGS M1 (fb + 40 + 384) p
                      /\ 0 <= n < c /\ 26 <= c <= 2 ^ 27 /\ c mod 2 = 0 /\ L5.defined M1 p c /\ L5.u64_at RSEGS M1 (fb + 408) (c + 1) /\ L5.defined M1 (fb + 408) 24
  end.
Proof.
  intros PA. pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & _). unfold PNM.OFF_TB in TB.
  destruct (PNM.b_tb s1) as [n|c n p]; destruct TB as (D & _ & TB').
  - destruct TB' as (Hn & U8). split; [exact Hn|]. split; [exact U8| replace (fb + 408) with (fb + 40 + 368) by lia; exact D].
  - destruct TB' as (U0 & U8 & U16 & Hn & Hc & He & Dp & _).
    split; [apply (PMF.u8_of_u64 RSEGS M1 _ (c + 1) ltac:(lia) U0)|].
    split; [replace (fb + 40 + 376) with (fb + 40 + 368 + 8) by lia; exact U8|].
    split; [replace (fb + 40 + 384) with (fb + 40 + 368 + 16) by lia; exact U16|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. split; [exact Dp|].
    split; [replace (fb + 408) with (fb + 40 + 368) by lia; exact U0| replace (fb + 408) with (fb + 40 + 368) by lia; exact D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_str_resize_tb LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' nsz : Z) K :
  PMSP.str_resize_spec RSEGS AD L HI ->
  K [] ->
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok AD L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (PNBK.be_s E0)) (PNBK.be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 368) -> getr R1 (PMK.reg 11) = Z_to_bv 64 nsz -> 0 <= nsz <= PM.vs_size (PNM.b_tb s1) + PM.CHUNK -> nsz < 2 ^ 26 + PM.CHUNK ->
  sp' <= sp -> sp - PMSP.pm_scr 8 <= sp' - PMSP.pm_scr 1 -> sp' mod 16 = 0 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 x' g' cr2,
      regs_preserved R1 R2 -> PM.vs_size x' = nsz -> (nsz <= PM.vs_cap (PNM.b_tb s1) -> PM.vs_own x' = PM.vs_own (PNM.b_tb s1) /\ g' = PNM.b_tg s1) ->
      brel LBX sp fb str E0 (BENT M2 model2 cr2 (PNBO.set_tb s1 x' g') sm1 ax1) ->
      (forall a n, sp' <= a -> a + n <= fb + 40 -> L5C.agree_on M1 M2 a n) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 r' M2 model2) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_str_resize AD) M1 model1) K.
Proof.
  intros PB K0 BR FOK INCS CRED0 X1 RA1 X2 X3 X4 X10 X11 Hn1 Hn2 S1 S2 S3 KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof (PNBK.scr_nonneg 8 ltac:(lia)) as SC0. set (sc := PMSP.pm_scr 8) in *.
  change (PMSP.pm_scr 1) with 14336 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img RSEGS L KL) as (IMG0 & IMG1). pose proof (PMK.kl_errno RSEGS L KL) as (ERN0 & ERN1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  cbn [pa_off_p pa_off_is pa_off_v AD PnLayoutS_u.ADDR_S] in PA1, IA1, VIS1, VREF1.
  destruct s1 as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  set (s1 := PNM.BPST mo dn src bb nb tb ng tg bg sb sk stk) in *.
  set (OWNr := PM.src_own src ++ PNM.bvec_own sb sk ++ PGV8.v8_own bb ++ PM.vs_own nb).
  set (LBr := OWNr ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) (PM.vs_own tb ++ LBr)).
  { unfold LBr, OWNr, s1, PNM.bparser_own, PNM.brest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply PNBK.perm5. }
  assert (HHp : hi_heap HI (PM.vs_own tb ++ LBr) cr1 M1 (m_vmmaps model1)) by (apply (PNBK.hi_heap_perm RSEGS AD AN L HI KH _ _ _ _ _ HH PERM1)).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 14336) by (apply (PMK.stk_call L M1 sp sc sp' 14336 STK); [exact S1| exact S2| lia| exact S3]).
  assert (AL : (fb + 40 + 368) mod 8 = 0) by (replace (fb + 40 + 368) with (fb + 8 * 51) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof PA1 as (_ & PDEF & _ & H8 & H9 & _ & _ & _ & SRC1 & _ & _ & BB1 & NB1 & TB1 & SV1 & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  cbn [s1 PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in H8, H9, SRC1, BB1, NB1, TB1, SV1, M01, D01.
  destruct GR1 as (GNB & GTB & GBB). cbn [s1 PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in GNB, GTB, GBB.
  assert (CRL1 : PMSP.credit_le (pot s1) cr1) by (apply (PMPK.credit_le_keep _ _ _ _ CRED0 CK)).
  assert (CRX : PMSP.credit_le (PM.pot_text L tb tg) cr1).
  { pose proof (PNBK.pot_bstack_nonneg RSEGS AD AN L HI KH sk ltac:(destruct SV1 as (_ & _ & _ & Hk & _); exact Hk)) as (Q1 & Q2).
    pose proof (PNBK.pot_text_nonneg RSEGS AD AN L HI KH _ _ _ _ NB1 GNB) as (Q3 & Q4). pose proof (PNBK.pot_v8_nonneg RSEGS AD AN L HI KH _ _ _ _ BB1 GBB) as (Q5 & Q6).
    pose proof (PNBK.pot_text_nonneg RSEGS AD AN L HI KH _ _ _ _ TB1 GTB) as (Q7 & Q8).
    revert CRL1. unfold PMSP.credit_le, PNR.pot_bparser, PM.credit_add, s1. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear - Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8. lia. }
  unfold PMSP.str_resize_spec in PB.
  apply (PB fx1 R1 M1 model1 K LBr cr1 (fb + 40 + 368) nsz sp' r' tg tb HHp MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { lia. } { lia. } { exact AL. }
  { exact TB1. } { exact GTB. } { exact Hn1. } { exact Hn2. } { exact CRX. }
  intros fx2 R2 M2 model2 x' g' cr2 RP2 VS2 SZ2 TBK2 KEEP2 HP2 CK2 MB2 HH2.
  set (s2 := PNBO.set_tb s1 x' g').
  assert (PERM2 : Permutation (PM.vs_own x' ++ LBr) (PNM.bparser_own s2 ++ LBX)).
  { unfold LBr, OWNr, s2, s1, PNM.bparser_own, PNM.brest_own. cbn [PNBO.set_tb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply Permutation_sym. apply PNBK.perm5. }
  assert (HH2' : hi_heap HI (PNM.bparser_own s2 ++ LBX) cr2 M2 (m_vmmaps model2)) by (apply (PNBK.hi_heap_perm RSEGS AD AN L HI KH _ _ _ _ _ HH2 PERM2)).
  pose proof (PMFR.model_ok_but_vm model1 model2 MOK MB2) as MOK2.
  set (WE := [(fb + 40 + 368, 24)] : list L5.range) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> fb + 40 + 368 <= a < fb + 40 + 368 + 24) by (intros a I; apply PMFR.inW_inv1 in I; exact I).
  assert (EKc : PMK.ek L LBr sp' 14336 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (BRr : PMFR.brange L LBr).
  { apply (PMFR.brange_of_heap L HI HIok _ LBr cr1 M1 _ HHp). apply incl_appr. apply incl_refl. }
  assert (WHI : forall a, PMK.inW WE a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WCE in I; left; lia).
  assert (AGH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 40 + 368 \/ fb + 40 + 368 + 24 <= a) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 H3. apply (PMFR.ag_hi RSEGS L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) a n H1 H2). intros i Hi I. apply WCE in I. lia. }
  assert (AGB : forall B m, In (B, m) LBr -> L5C.agree_on M1 M2 B m) by (intros B m Hin; apply (PMFR.ag_block RSEGS L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) BRr WHI B m Hin)).
  assert (DKH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M1 M2 a n) by (intros a n H1 H2; apply (PMPK.dkr_hpres_hi RSEGS L KL LBr sp' 14336 WE M1 M2 a n HP2 STKc ltac:(lia) H1 H2)).
  assert (DKB : forall B m, In (B, m) LBr -> PMPK.dkr M1 M2 B m) by (intros B m Hin; apply (PMPK.dkr_hpres_blk RSEGS L KL LBr sp' 14336 WE M1 M2 B m HP2 Hin BRr); lia).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) LBr) by (unfold LBr, OWNr, PM.src_own; cbn; left; reflexivity).
  assert (SIN : In (sb, PNM.BSZ * 2 ^ sk) LBr) by (unfold LBr, OWNr, PNM.bvec_own; cbn; right; left; reflexivity).
  assert (PA2 : bparser_at M2 (fb + 40) (fb + 472) s2).
  { unfold PNM.bparser_at, PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    cbn [s2 s1 PNBO.set_tb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
    destruct PA1 as (H0 & _ & _ & _ & _ & H10 & H12 & NI & _ & H312 & _).
    split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H0]|].
    split; [apply (PMPK.defined_dkr M1 M2 (fb + 40) 416); [apply DKH; lia| exact PDEF]|]. split; [exact I|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H8]|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H9]|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H10]|].
    split; [apply (PMF.u32_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H12]|].
    split; [apply (PMF.nullis_at_agree RSEGS AD M1 M2); [lia|lia| apply AGH; lia| exact NI]|].
    split.
    { destruct (BRr _ _ QIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PMF.src_fields_at_agree RSEGS M1 M2); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AGH; lia| apply AGB; exact QIN| exact SRC1]. }
    split; [apply (PMF.u32_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H312]|]. split; [exact I|].
    split.
    { apply (PNMF.v8_at_keep RSEGS M1 M2); [lia|lia| apply AGH; lia| | exact BB1].
      intros b n c0 E. apply DKB. unfold LBr, OWNr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      rewrite E. cbn. auto. }
    split.
    { apply (PNMF.vstr_at_keep RSEGS M1 M2 (fb + 40 + 344) nb); [lia|lia| destruct nb; cbn [PNMF.vs_cells fst snd]; apply AGH; lia| apply DKH; lia| | exact NB1].
      intros c0 n p E. apply DKB. unfold LBr, OWNr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      rewrite E. cbn. auto. }
    split; [exact VS2|].
    split.
    { destruct (BRr _ _ SIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PNMF.bvec_at_agree RSEGS M1 M2); [lia|lia|lia|lia| apply AGH; lia| apply AGB; exact SIN| exact SV1]. }
    split; [exact M01| exact D01]. }
  assert (INCSr : incl (PM.vs_own str) LBr) by (unfold LBr; apply incl_appr; exact INCS).
  assert (IA2 : PM.iss_at RSEGS AD PMSP.T3 M2 (fb + 472) str sm1).
  { apply (PMFR.iss_keep RSEGS AD L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) BRr WHI (fb + 472) str sm1); [lia|lia| intros i Hi I; apply WCE in I; lia| exact INCSr| exact IA1]. }
  destruct (PNBK.statics_keep RSEGS AD AN L HI KH LBr sp' 14336 WE M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCE in I. lia. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after RSEGS L KL LBr M1 M2 sp sc sp' 14336 WE STK HP2); lia).
  assert (OWN1 : PNBK.own_ok L (PNM.bparser_own s1) LBX) by (apply (PNBK.own_ok_heap RSEGS AD AN L HI KH _ LBX cr1 M1 (m_vmmaps model1)); exact HH).
  assert (OWNR : PNBK.own_ok L OWNr LBX).
  { intros B m Hin. apply OWN1. revert Hin. apply (PNBK.incl_own_r (PM.src_own src) (PNM.bvec_own sb sk) (PGV8.v8_own bb) (PM.vs_own nb) (PM.vs_own tb) false). }
  apply (KONT fx2 R2 M2 model2 x' g' cr2 RP2 SZ2 KEEP2).
  - unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax]. fold s2.
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. cbn [pa_off_p pa_off_is pa_off_v AD PnLayoutS_u.ADDR_S].
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|].
      unfold PNM.bgrow_ok. cbn [s2 s1 PNBO.set_tb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg]. split; [exact GNB|]. split; [exact TBK2| exact GBB]. }
    split; [exact STEP|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PNBK.ek_lbx_callee RSEGS AD AN L HI KH OWNr LBX sp sc sp' 14336 _ WE M1 M1 M2 HP2 S2 S1 OWNR); [|exact STK|].
        + apply (PMFR.brange_hi L LBX). apply (PMFR.brange_incl L LBX LBr BRr). unfold LBr. apply incl_appr. apply incl_refl.
        + intros a I. right. left. apply WCE in I. apply (PNBK.wrun_of_range RSEGS AD AN L HI KH). lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LBr sp sc sp' 14336 WE M1 M2 HP2); [unfold LBr; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split.
    { revert CK CK2. unfold PMSP.credit_keep, PNR.pot_bparser, PM.credit_add, s2, s1.
      cbn [PNBO.set_tb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear. lia. }
    split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2'|]. split; [exact STK2| exact MOK2].
  - intros a n H1 H2. apply AGH; [exact H1| lia| lia].
Qed.

End WithHeap.
End PNSRVK.
