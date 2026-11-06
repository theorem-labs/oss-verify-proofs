(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim RefMemcpyLib LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablVia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma vgrow_mono : forall c c', 0 <= c <= c' -> vgrow c <= vgrow c'.
Proof. intros c c' H. unfold vgrow. lia. Qed.

Lemma vgrow_ge : forall c, c + 1 <= vgrow c /\ 2 * c <= vgrow c.
Proof. intros c. unfold vgrow. lia. Qed.

Lemma nodup_fst_fun : forall (l : list (Z * Z)) q k k',
  List.NoDup (map fst l) -> In (q, k) l -> In (q, k') l -> k = k'.
Proof.
  induction l as [|[q0 k0] l IH]; intros q k k' ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|x l' Hnin ND']; subst.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - injection E1 as -> ->. exfalso. apply Hnin. change q with (fst (q, k')). apply in_map. exact H2.
  - injection E2 as -> ->. exfalso. apply Hnin. change q with (fst (q, k)). apply in_map. exact H1.
  - exact (IH q k k' ND' H1 H2).
Qed.

Lemma nodup_of_fst : forall (l : list (Z * Z)), List.NoDup (map fst l) -> List.NoDup l.
Proof.
  induction l as [|[q k] l IH]; intros ND; [constructor|]. cbn in ND. inversion ND as [|x l' Hnin ND']; subst.
  constructor; [|apply IH; exact ND']. intros Hin. apply Hnin. change q with (fst (q, k)). apply in_map. exact Hin.
Qed.

Section Weight.
Context {AC : AllocCeiling}.
  Variable w : Z * Z -> Z.
  Hypothesis w_nonneg : forall x, 0 <= w x.
  Fixpoint wsum (l : list (Z * Z)) : Z := match l with [] => 0 | x :: r => w x + wsum r end.
  Lemma wsum_nonneg : forall l, 0 <= wsum l.
  Proof using w w_nonneg. induction l as [|x l IH]; cbn; [lia|]. pose proof (w_nonneg x). lia. Qed.
  Lemma wsum_app : forall l1 l2, wsum (l1 ++ l2) = wsum l1 + wsum l2.
  Proof using w. induction l1 as [|x l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.
  Lemma wsum_incl : forall l1 l2, List.NoDup l1 -> (forall x, In x l1 -> In x l2) -> wsum l1 <= wsum l2.
  Proof using w w_nonneg.
    induction l1 as [|x l1 IH]; intros l2 ND Hincl; cbn; [apply wsum_nonneg|].
    inversion ND as [|x' l' Hnin ND']; subst.
    destruct (in_split x l2 (Hincl x (or_introl eq_refl))) as (la & lb & ->).
    rewrite wsum_app. cbn. pose proof (IH (la ++ lb) ND') as IH'. rewrite wsum_app in IH'.
    assert (Hi : forall y, In y l1 -> In y (la ++ lb)).
    { intros y Hy. pose proof (Hincl y (or_intror Hy)) as H2. apply in_app_iff in H2. apply in_app_iff.
      destruct H2 as [H2|[<-|H2]]; [left; exact H2 | exfalso; exact (Hnin Hy) | right; exact H2]. }
    specialize (IH' Hi). lia.
  Qed.
End Weight.

Lemma count_class_f_wsum : forall cls big l c,
  count_class_f cls big l c = wsum (fun x => if (snd x <? big) && (cls (snd x) =? c) then 1 else 0) l.
Proof. intros cls big l c. induction l as [|[q k] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma big_bytes_f_wsum : forall rb big l,
  big_bytes_f rb big l = wsum (fun x => if big <=? snd x then rb (snd x) else 0) l.
Proof. intros rb big l. induction l as [|[q k] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section Push.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

Record lay_ok : Prop := LAY_OK {
  lo_img   : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling;
  lo_rw    : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a;
  lo_relro : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a;
  lo_err   : forall a, errno_win L a -> in_ranges (ly_img L) a;
  lo_rw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a;
  lo_err_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a;
  lo_noseg : forall x, alloc_ceiling <= x -> find_segment SEGS x 1 = None
}.

#[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

Variables (A0 : AS MI) (s : SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
Variables (sp ret STK FRM : Z) (pat b0 cap0 : Z) (xs0 : list Z) (lenR : Z) (kR : nat).
Record pctx : Prop := PCTX {
  pc_ly   : lay_ok;
  pc_ms   : 0 <= MALLOC_STACK MI;
  pc_cb   : callB MI ST A0 s R0 M0 model0 sp ret STK;
  pc_vec0 : vec32 MI A0 M0 pat b0 xs0 cap0;
  pc_obj0 : obj_ok MI A0 sp STK pat 24;
  pc_frm  : 0 < FRM <= STK /\ FRM mod 16 = 0;
  pc_rp   : room_pushes SEGS L MI A0 (live MI A0) lenR cap0 kR;
  pc_nmx  : caps_bound lenR cap0 (Z.of_nat kR) <= NMAX MI;
  pc_len  : 0 <= lenR <= Zlen xs0
}.
Variable PC : pctx.
#[local] Notation HLimg_lo := (lo_img (pc_ly PC)).
#[local] Notation HLrw_img := (lo_rw (pc_ly PC)).
#[local] Notation HLrelro_img := (lo_relro (pc_ly PC)).
#[local] Notation HLerr_img := (lo_err (pc_ly PC)).
#[local] Notation HLrw_relro := (lo_rw_relro (pc_ly PC)).
#[local] Notation HLerr_rw := (lo_err_rw (pc_ly PC)).
#[local] Notation HLnoseg := (lo_noseg (pc_ly PC)).
#[local] Notation MSpos := (pc_ms PC).
#[local] Notation CB := (pc_cb PC).
#[local] Notation VEC0 := (pc_vec0 PC).
#[local] Notation OBJ0 := (pc_obj0 PC).
#[local] Notation HFRM := (pc_frm PC).
#[local] Notation RP := (pc_rp PC).
#[local] Notation NMX := (pc_nmx PC).
#[local] Notation HlenR := (pc_len PC).

Lemma live_nodup : forall A M model, ainv MI A M model -> List.NoDup (map fst (live MI A)).
Proof using AC SEGS L MI. intros A M model AI. apply (proj1 (NoDup_ListNoDup _)). exact (ai_live_nodup MI A M model AI). Qed.

#[local] Notation hi_unowned := (hi_unowned SEGS L MI HLimg_lo HLrw_img).
#[local] Notation stack_sep := (stack_sep SEGS L MI HLimg_lo HLrw_img).
#[local] Notation placed_sep := (placed_sep SEGS L MI HLimg_lo HLrw_img).
#[local] Notation offimg_sep := (offimg_sep SEGS L ST HLrw_img HLrelro_img HLerr_img).

Definition W : Z * Z := (sp - STK, sp).
Definition FP (b cap : Z) : Z -> Prop := pushes_fp SEGS L MI A0 pat b0 cap0 b cap.
Definition CAPB : Z := Z.max cap0 (2 * (lenR + Z.of_nat kR)).

Record PINV (A : AS MI) (M : mem) (model : Model) (b cap : Z) (xs : list Z) : Prop := MKPINV {
  pi_ainv : ainv MI A M model;
  pi_mstd : mstd model;
  pi_fs   : m_fs model = m_fs model0 /\ m_fds model = m_fds model0;
  pi_sx   : sx_inv ST s M;
  pi_roc  : img_ro_clear L M;
  pi_vec  : vec32 MI A M pat b xs cap;
  pi_post : pushes_post SEGS L MI A0 A lenR (Z.of_nat kR) b0 cap0 b cap;
  pi_eff  : eff MI A0 A M0 M W (FP b cap);
  pi_win  : mdef M (sp - STK) STK
}.

#[local] Ltac dCB := destruct CB as [AI0 MS0 ROC0 SX0 SXH0 CR0 Hceil0 HROOM0 Hwin0 Hown_sx0 Herr_sx0].

Lemma sp_facts : alloc_ceiling + STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC. dCB. destruct CR0. pose proof ac_bounds_lit as [? ?]. repeat split; assumption. Qed.

Lemma pat_win : pat + 24 <= sp - STK \/ sp <= pat.
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  destruct OBJ0 as [_ Wn]. pose proof HFRM.
  destruct (Z.lt_ge_cases pat sp); [left|right; lia].
  destruct (Z.lt_ge_cases (pat + 24) (sp - STK + 1)); [lia|]. exfalso.
  destruct (Z.lt_ge_cases pat (sp - STK)).
  - apply (Wn (sp - STK)); unfold zwin; lia.
  - apply (Wn pat); unfold zwin; lia.
Qed.

Lemma b0_facts : b0 = 0 /\ cap0 = 0 \/
  0 < b0 /\ 0 < cap0 /\ In (b0, 4 * cap0) (live MI A0) /\ b0 + 4 * cap0 <= alloc_ceiling /\
  (pat + 24 <= b0 \/ b0 + 4 * cap0 <= pat) /\
  (forall a, b0 <= a < b0 + 4 * cap0 -> ~ owned MI A0 a /\ ~ in_ranges (ly_img L) a /\ M0 (Z_to_bv 64 a) <> None) /\
  (forall k, In (b0, k) (live MI A0) -> k = 4 * cap0).
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  dCB. destruct VEC0 as (_ & _ & _ & _ & Hb & _).
  destruct Hb as [[-> ->]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [left; split; reflexivity | right].
  destruct (ai_live_block MI A0 M0 model0 b0 (4 * cap0) AI0 HIn) as (_ & _ & _ & Hce & Hblk).
  repeat (split; [first [assumption | lia] |]).
  intros k Hk. exact (nodup_fst_fun _ _ _ _ (live_nodup A0 M0 model0 AI0) Hk HIn).
Qed.

Section Facts.
  Variables (A : AS MI) (M : mem) (model : Model) (b cap : Z) (xs : list Z).
  Hypothesis PI : PINV A M model b cap xs.

  Lemma cur_facts : b = 0 /\ cap = 0 \/
    0 < b /\ 0 < cap /\ In (b, 4 * cap) (live MI A) /\ b + 4 * cap <= alloc_ceiling /\
    (pat + 24 <= b \/ b + 4 * cap <= pat) /\
    (forall a, b <= a < b + 4 * cap -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) <> None).
  Proof using AC SEGS L MI ST A0 s M0 model0 sp STK pat b0 cap0 lenR kR A M model b cap xs PI.
    destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. destruct VEC as (_ & _ & _ & _ & Hb & _).
    destruct Hb as [[-> ->]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [left; split; reflexivity | right].
    destruct (ai_live_block MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hce & Hblk).
    repeat (split; [first [assumption | lia] |]). exact Hblk.
  Qed.

  Lemma live_keep : forall q k, In (q, k) (live MI A0) -> q <> b0 -> In (q, k) (live MI A).
  Proof using AC SEGS L MI ST A0 s M0 model0 sp STK pat b0 cap0 lenR kR A M model b cap xs PI.
    intros q k Hin Hne. destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. destruct PP as ([Hle Hcb] & Hsame & Hgrow).
    destruct (Z.eq_dec cap cap0) as [E|NE].
    - destruct (Hsame E) as [_ ->]. exact Hin.
    - destruct (Hgrow NE) as [Hm _]. apply Hm. left. split; assumption.
  Qed.

  Lemma pinv_placed : placed MI A pat 24.
  Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC A M model b cap xs PI.
    pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. dCB.
    destruct OBJ0 as [[Hhi|(q & k & Hin & H1 & H2)] _]; [left; exact Hhi | right].
    exists q, k. split; [|split; assumption]. apply live_keep; [exact Hin|]. intros ->.
    destruct b0_facts as [[Hb0 _]|(Hbp & Hcp & HIn & Hce & Hdj & _ & Hk)].
    - destruct (ai_live_block MI A0 M0 model0 b0 k AI0 Hin) as (_ & _ & Hp & _). lia.
    - pose proof (Hk k Hin). lia.
  Qed.

  Lemma fp_sep : forall a, FP b cap a -> ~ in_ranges (ly_img L) a /\ (a < sp - STK \/ sp <= a) /\ a < alloc_ceiling \/
                              FP b cap a /\ zwin pat (pat + 24) a /\ ~ in_ranges (ly_img L) a /\ (a < sp - STK \/ sp <= a).
  Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC A M model b cap xs PI.
    intros a Ha. pose proof sp_facts as (Hc & _ & _ & Hcv). pose proof pat_win as PW. pose proof PI as PI'.
    destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. dCB.
    destruct Ha as [Hp|[[Hbnz Hb]|[Hb'|Hj]]].
    - right. split; [left; exact Hp|]. split; [exact Hp|]. unfold zwin in Hp.
      split; [exact (proj2 (placed_sep A0 M0 model0 pat 24 a AI0 (proj1 OBJ0) Hp)) | lia].
    - left. unfold zwin in Hb. destruct b0_facts as [[? _]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk & _)]; [lia|].
      destruct (Hblk a Hb) as (_ & Hni & _). split; [exact Hni|]. lia.
    - left. unfold zwin in Hb'. destruct cur_facts as [[-> ->]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk)]; [lia|].
      destruct (Hblk a Hb') as (_ & Hni & _). split; [exact Hni|]. lia.
    - left. destruct Hj as (Hr & Hni & _). split; [exact Hni|]. lia.
  Qed.

  Lemma fp_offimg : forall a, FP b cap a -> ~ in_ranges (ly_img L) a.
  Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC A M model b cap xs PI. intros a Ha. destruct (fp_sep a Ha) as [(H & _)|(_ & _ & H & _)]; exact H. Qed.

  Lemma cur_junk : forall a, b <> 0 -> b <= a < b + 4 * cap ->
    (b0 <> 0 /\ zwin b0 (b0 + 4 * cap0) a) \/ junk SEGS L MI A0 a.
  Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC A M model b cap xs PI.
    intros a Hbnz Ha. pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. dCB.
    destruct (classic (b0 <> 0 /\ zwin b0 (b0 + 4 * cap0) a)) as [Hy|Hn]; [left; exact Hy | right].
    destruct cur_facts as [[-> ->]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk)]; [lia|].
    destruct PP as ([Hle Hcb] & Hsame & Hgrow).
    destruct (Z.eq_dec cap cap0) as [E|NE].
    { exfalso. destruct (Hsame E) as [-> _]. apply Hn. split; [exact Hbnz|]. unfold zwin. lia. }
    destruct (Hgrow NE) as [Hm Hfresh].
    destruct (Hblk a Ha) as (_ & Hni & _).
    split; [lia|]. split; [exact Hni|]. intros q k Hq Hqa.
    destruct (Z.eq_dec q b0) as [->|Hqb].
    - destruct b0_facts as [[Hb0 _]|(Hbp0 & Hcp0 & HIn0 & Hce0 & Hdj0 & _ & Hk)].
      + destruct (ai_live_block MI A0 M0 model0 b0 k AI0 Hq) as (_ & _ & Hp & _). lia.
      + pose proof (Hk k Hq) as ->. apply Hn. split; [lia|]. unfold zwin. lia.
    - pose proof (live_keep q k Hq Hqb) as HqA. pose proof (Hfresh q k Hq Hqb) as Hqb'.
      destruct (ai_live_disjoint MI A M model b (4 * cap) q k AI HIn HqA ltac:(congruence)); lia.
  Qed.

  Lemma pinv_agree_hi : forall (P : Z -> Prop),
    (forall a, P a -> alloc_ceiling <= a < 2 ^ 64 /\ M0 (Z_to_bv 64 a) <> None /\ ~ zwin pat (pat + 24) a /\ ~ (sp - STK <= a < sp)) ->
    agree_on P M0 M.
  Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC A M model b cap xs PI.
    intros P HP. pose proof sp_facts as (Hc & _ & _ & Hcv). pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. dCB.
    eapply (agree_via_eff SEGS L MI); [exact EF|]. intros a Ha. destruct (HP a Ha) as (Hr & Hd & Hnp & Hnw).
    split; [lia|]. split; [apply (hi_unowned A0 M0 model0); [exact AI0|lia]|]. split; [apply (hi_unowned A M model); [exact AI|lia]|].
    split; [exact Hd|]. split.
    - intros HF. destruct (fp_sep a HF) as [(_ & _ & Hlt)|(_ & Hp & _)]; [lia | exact (Hnp Hp)].
    - split; [unfold W_of, W; cbn; lia|]. apply (hi_not_errno L HLimg_lo HLerr_img). lia.
  Qed.

  Lemma pinv_stores : forall M', stores_in (zwin (sp - FRM) sp) M M' -> PINV A M' model b cap xs.
  Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC A M model b cap xs PI.
    intros M' STI. pose proof sp_facts as (Hc & Hs47 & _ & Hcv). pose proof HFRM as [HF1 HF2]. pose proof pat_win as PW.
    pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN].
    assert (SEPw : forall a, zwin (sp - FRM) sp a -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a).
    { intros a Ha. apply (stack_sep A M model a AI). unfold zwin in Ha. lia. }
    constructor.
    - eapply stores_in_ainv; [exact AI | exact STI | intros a Ha; exact (proj1 (SEPw a Ha))].
    - exact MS. - exact FS.
    - eapply stores_in_sx; [exact SX | exact STI |]. intros a Ha.
      destruct (offimg_sep a (proj2 (SEPw a Ha))) as (H1 & H2 & _). split; assumption.
    - eapply roc_stores; [exact ROC | exact STI |]. intros a Ha. exact (proj2 (SEPw a Ha)).
    - eapply (vec32_frame MI); [exact VEC|]. eapply stores_in_agree; [exact STI|].
      pose proof VEC as (Hv0 & Hv1 & _ & Hlen & _). intros a Ha.
      destruct cur_facts as [[-> ->]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk)];
        (destruct Ha as [Ha|[Hnz Ha]]; unfold zwin in *; [split; [lia|lia] | split; [lia|lia]]).
    - exact PP.
    - eapply eff_weaken; [eapply (eff_trans MI); [exact EF | eapply (eff_of_stores SEGS L MI A M M' W (fun _ => False)); [exact STI|] |]|].
      + intros a Ha. right. unfold W_of, W, zwin in *; cbn. lia.
      + intros a Ha. apply (hi_unowned A M' model). 2: unfold W_of, W in Ha; cbn in Ha; lia.
        eapply stores_in_ainv; [exact AI | exact STI | intros x Hx; exact (proj1 (SEPw x Hx))].
      + intros a [H|[]]. exact H.
    - eapply stores_in_mdef; [exact STI | exact WIN].
  Qed.
End Facts.

Lemma pinv_init : PINV A0 M0 model0 b0 cap0 xs0.
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  pose proof sp_facts as (Hc & Hs47 & _ & Hcv). pose proof HFRM as [HF1 HF2]. dCB.
  constructor.
  - exact AI0. - exact MS0. - split; reflexivity. - exact SX0. - exact ROC0. - exact VEC0.
  - split; [lia|]. split; [intros _; split; reflexivity | intros H; exfalso; exact (H eq_refl)].
  - apply eff_refl.
  - eapply store_ok_mdef_offimg; [exact HROOM0 | lia | lia | lia |]. intros x Hx. apply HLnoseg. lia.
Qed.

Lemma pinv_room : forall A M model b cap xs,
  PINV A M model b cap xs -> lenR <= Zlen xs -> Zlen xs < lenR + Z.of_nat kR -> Zlen xs = cap ->
  roomL MI A (live MI A) (4 * vgrow cap).
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  intros A M model b cap xs PI H1 H2 Hfull. pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN].
  destruct PP as ([Hle Hcb] & Hsame & Hgrow).
  pose proof (RP cap Hle ltac:(lia) ltac:(lia)) as [RS RBG].
  pose proof EF as [HC HB _ _ _ _].
  assert (SUB : forall (w : Z * Z -> Z), (forall x, 0 <= w x) -> (forall q k k', w (q, k) = w (k', k)) ->
                wsum w (live MI A) <= wsum w ((0, 4 * cap) :: live MI A0)).
  { intros w Hw Hwq. destruct (Z.eq_dec cap cap0) as [E|NE].
    - destruct (Hsame E) as [_ ->]. cbn. pose proof (Hw (0, 4 * cap)). lia.
    - destruct (Hgrow NE) as [Hm _].
      transitivity (wsum w ((b, 4 * cap) :: live MI A0)); [|cbn; rewrite (Hwq b (4 * cap) 0); lia].
      apply wsum_incl; [exact Hw | apply nodup_of_fst; exact (live_nodup A M model AI) |].
      intros [q k] Hin. destruct (proj1 (Hm q k) Hin) as [[H _]|[-> ->]]; [right; exact H | left; reflexivity]. }
  unfold roomL in *. rewrite HC, HB. split.
  - intros Hsmall. destruct (RS Hsmall) as [R1 R2].
    rewrite count_class_f_wsum in R1. rewrite count_class_f_wsum in R2.
    rewrite (count_class_f_wsum _ _ _ (size_class MI (4 * vgrow cap))), (count_class_f_wsum _ _ _ (size_class MI (4 * vgrow cap) + 1)).
    pose proof (SUB (fun x => if (snd x <? BIG MI) && (size_class MI (snd x) =? size_class MI (4 * vgrow cap)) then 1 else 0)
                  ltac:(intros x; cbn; destruct (_ && _); lia) ltac:(intros; reflexivity)).
    pose proof (SUB (fun x => if (snd x <? BIG MI) && (size_class MI (snd x) =? size_class MI (4 * vgrow cap) + 1) then 1 else 0)
                  ltac:(intros x; cbn; destruct (_ && _); lia) ltac:(intros; reflexivity)).
    cbn beta in *. lia.
  - intros Hbig. specialize (RBG Hbig). rewrite big_bytes_f_wsum in RBG. rewrite big_bytes_f_wsum.
    pose proof (SUB (fun x => if BIG MI <=? snd x then round_big MI (snd x) else 0)
                  ltac:(intros [q k]; cbn; destruct (Z.leb_spec (BIG MI) k); [apply (ai_round_big_nonneg MI); pose proof (ai_big_pos MI); lia | lia]) ltac:(intros; reflexivity)).
    cbn beta in *. lia.
Qed.

Lemma pinv_push : forall {fx : FPState} cpb A M model b cap xs (R1 : bvmap 5 word) (ra src x : Z) (K : TSet),
  vec32_push_back_stmt SEGS L MI ST cpb ->
  0 <= vc_stack cpb -> vc_stack cpb + NEW_STACK SEGS L MI + FRM <= STK ->
  PINV A M model b cap xs ->
  lenR <= Zlen xs -> Zlen xs < lenR + Z.of_nat kR ->
  getr R1 10%bv = Z_to_bv 64 pat -> getr R1 11%bv = Z_to_bv 64 src -> getr R1 2%bv = Z_to_bv 64 (sp - FRM) ->
  getr R1 1%bv = Z_to_bv 64 ra -> ret_ok (Z_to_bv 64 ra) -> 0 <= ra < 2 ^ 64 ->
  getr R1 3%bv = getr R0 3%bv -> getr R1 4%bv = getr R0 4%bv ->
  sp - FRM <= src -> src + 4 <= sp -> fld SEGS M src 4 x -> 0 <= x < 2 ^ 32 ->
  (forall A' R' M' model' (b' cap' : Z),
      PINV A' M' model' b' cap' (xs ++ [x]) -> kept R1 R' -> agree_on (zwin (sp - FRM) sp) M M' ->
      srealizes SEGS (cfg fx R' ra M' model') K) ->
  srealizes SEGS (cfg fx R1 (vc_entry cpb) M model) K.
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  intros fx cpb A M model b cap xs R1 ra src x K PB Hvs Hfit PI HL1 HL2 G10 G11 G2 G1 Hret Hra G3 G4 Hs1 Hs2 Fx Hx CONT.
  pose proof sp_facts as (Hc & Hs47 & Hs16 & Hcv). pose proof pat_win as PW.
  pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. pose proof CB as CB0. dCB. destruct CR0.
  pose proof (ai_nmax_bound MI) as HNM. pose proof MSpos as HMS. pose proof HlenR as HLR0. pose proof HFRM as [HF1 HF2].
  unfold NEW_STACK in Hfit.
  eapply (PB fx A s R1 M model (sp - FRM) ra pat b cap src x xs K); unfold NEW_STACK in *.
  -
    constructor.
    + exact AI. + exact MS. + exact ROC. + exact SX. + exact SXH0.
    + constructor; try assumption.
      * replace (sp - FRM) with (sp + (- (FRM / 16)) * 16) by (pose proof (Z_div_mod_eq_full FRM 16); lia).
        rewrite Z.mod_add by lia. exact Hs16.
      * lia.
      * rewrite G3. assumption. * rewrite G4. assumption.
    + lia.
    + unfold stack_room. replace (sp - FRM - (vc_stack cpb + (16 + MALLOC_STACK MI))) with (sp - STK + (STK - FRM - (vc_stack cpb + (16 + MALLOC_STACK MI)))) by lia.
      apply (mdef_store_ok_off SEGS M (sp - STK) STK); try lia. exact WIN.
    + intros a Ha. unfold zwin in Ha. split.
      * apply (hi_unowned A M model); [exact AI | lia].
      * apply (proj2 (Hwin0 a ltac:(unfold zwin; lia))).
    + intros a Ho. pose proof EF as [_ _ HOWN _ _ _]. destruct (HOWN a Ho) as [HoA|[Hnm|HF]].
      * exact (Hown_sx0 a HoA).
      * destruct Hnm as (Hni & _). exact (proj1 (offimg_sep a Hni)).
      * exact (proj1 (offimg_sep a (fp_offimg A M model b cap xs PI' a HF))).
    + exact Herr_sx0.
  - exact G10. - exact G11. - exact VEC.
  - split; [exact (pinv_placed A M model b cap xs PI')|]. intros a Ha Hw. apply (proj2 OBJ0 a Ha). unfold zwin in *. lia.
  - exact Fx. - exact Hx.
  - split; [left; lia|]. intros a Ha Hw. unfold zwin in *. lia.
  - lia. - lia.
  - intros a Ha Hp. apply (proj2 OBJ0 a Hp). unfold zwin in *. lia.
  - transitivity (caps_bound lenR cap0 (Z.of_nat kR)); [|exact NMX]. unfold caps_bound.
    destruct PP as ([Hle Hcb] & _). pose proof (vgrow_mono cap (Z.max cap0 (2 * (lenR + Z.of_nat kR)))). destruct VEC as (_ & _ & _ & Hlen & _). lia.
  - intros Hfull. exact (pinv_room A M model b cap xs PI' HL1 HL2 Hfull).
  -
    intros A' R' M' model' b' cap' RB VEC' ALT EFc.
    destruct RB as [AI' MS' Hfs' Hfds' SX' KEPT].
    assert (Fc_sep : forall a, zwin pat (pat + 24) a \/ b <> 0 /\ zwin b (b + 4 * cap) a \/ zwin b' (b' + 4 * cap') a ->
                     ~ in_ranges (ly_img L) a /\ ~ (sp - STK <= a < sp)).
    { intros a [Hp|[[Hbnz Hb]|Hb']].
      - split; [exact (proj2 (placed_sep A0 M0 model0 pat 24 a AI0 (proj1 OBJ0) ltac:(unfold zwin in Hp; exact Hp))) | unfold zwin in Hp; lia].
      - destruct (cur_facts A M model b cap xs PI') as [[-> ->]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk)]; [lia|].
        unfold zwin in Hb. destruct (Hblk a Hb) as (_ & Hni & _). split; [exact Hni | lia].
      - destruct VEC' as (_ & _ & _ & Hlen' & Hbb & _). unfold zwin in Hb'.
        destruct Hbb as [[-> ->]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|].
        destruct (ai_live_block MI A' M' model' b' (4 * cap') AI' HIn) as (_ & _ & _ & Hce & Hblk).
        destruct (Hblk a Hb') as (_ & Hni & _). split; [exact Hni | lia]. }
    apply (CONT A' R' M' model' b' cap'); [| exact KEPT |].
    2:{ eapply (agree_hi_via_eff SEGS L MI HLimg_lo HLrw_img HLerr_img A A' M M' model model'); [exact EFc | exact AI | exact AI' | lia | lia | | | cbn; lia].
        - replace (sp - (sp - FRM)) with FRM by lia. intros i Hi. replace (sp - FRM + i) with (sp - STK + (STK - FRM + i)) by lia. apply WIN. lia.
        - intros a Ha HF. exact (proj2 (Fc_sep a HF) ltac:(lia)). }
    constructor.
    + exact AI'. + exact MS'. + rewrite Hfs', Hfds'. exact FS. + exact SX'.
    + apply (img_ro_clear_of' SEGS L ST s); [|exact SX'].
      eapply (ro_clear_via_eff SEGS L MI HLimg_lo HLerr_rw A A' M M' model); [| exact AI | exact EFc | intros a Ha; exact (proj1 (Fc_sep a Ha)) | cbn; lia].
      intros w Hw. apply ROC; [exact (proj1 Hw) | exact (proj1 (proj2 Hw))].
    + exact VEC'.
    +
      destruct PP as ([Hle Hcb] & Hsame & Hgrow).
      destruct ALT as [(Hlt & -> & -> & HL) | (Hfull & Hcap' & LAP)].
      * split; [split; [exact Hle | exact Hcb]|]. split; [intros E; rewrite HL; exact (Hsame E)|]. intros NE. rewrite HL. exact (Hgrow NE).
      * cbn [lapply] in LAP. destruct LAP as (lv1 & [-> Hnin] & LAP).
        pose proof (vgrow_ge cap) as [Hg1 Hg2].
        assert (Hbb' : b' <> b /\ (b = 0 -> 0 < b')).
        { destruct VEC' as (_ & _ & _ & Hlen' & Hbb & _).
          destruct Hbb as [[-> Hc0]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|]. split; [|lia].
          intros ->. destruct (cur_facts A M model b cap xs PI') as [[Hb0 _]|(_ & _ & HInA & _)]; [lia|].
          apply Hnin. change b with (fst (b, 4 * cap)). apply in_map. exact HInA. }
        destruct Hbb' as [Hne Hpos].
        assert (MEM : forall q k, In (q, k) (live MI A') <-> (In (q, k) (live MI A) /\ q <> b) \/ (q = b' /\ k = 4 * cap')).
        { intros q k. unfold del_if in LAP. destruct (Z.eqb_spec b 0) as [Hb0|Hb0].
          - cbn [lapply] in LAP. rewrite LAP. cbn [In]. split.
            + intros [E|H]; [right; injection E as <- <-; split; [reflexivity|lia] | left; split; [exact H|]].
              intros ->. destruct (cur_facts A M model b cap xs PI') as [[_ Hc0]|(Hbp & _)]; [|lia].
              destruct (ai_live_block MI A M model b k AI H) as (_ & _ & Hp & _). lia.
            + intros [[H _]|[-> ->]]; [right; exact H | left; f_equal; lia].
          - cbn [lapply] in LAP. destruct LAP as (lv2 & HD & <-). rewrite (HD q k). cbn [In]. split.
            + intros [[E|H] Hq]; [right; injection E as <- <-; split; [reflexivity|lia] | left; split; assumption].
            + intros [[H Hq]|[-> ->]]; [split; [right; exact H | exact Hq] | split; [left; f_equal; lia | exact Hne]]. }
        split; [unfold vgrow in *; lia|]. split; [intros E; exfalso; lia|]. intros _.
        destruct (Z.eq_dec cap cap0) as [E|NE].
        -- destruct (Hsame E) as [-> HL]. rewrite HL in MEM, Hnin. split; [exact MEM|].
           intros q k Hq Hqb ->. apply Hnin. change b' with (fst (b', k)). apply in_map. exact Hq.
        -- destruct (Hgrow NE) as [Hm Hfresh]. split.
           ++ intros q k. rewrite MEM, (Hm q k). split.
              ** intros [[[[H1 H2]|[-> ->]] H3]|[-> ->]]; [left; split; assumption | exfalso; exact (H3 eq_refl) | right; split; reflexivity].
              ** intros [[H1 H2]|[-> ->]]; [left | right; split; reflexivity]. split; [left; split; assumption|]. exact (Hfresh q k H1 H2).
           ++ intros q k Hq Hqb ->. apply Hnin. change b' with (fst (b', k)). apply in_map. apply Hm. left. split; [exact Hq | exact Hqb].
    +
      eapply eff_weaken.
      * eapply (eff_trans MI); [exact EF | | intros a Ha; apply (hi_unowned A' M' model'); [exact AI' | unfold W_of, W in Ha; cbn in Ha; lia]].
        eapply (eff_widen SEGS L MI); [exact EFc | cbn; lia | cbn; lia].
      * intros a [HF|HFc].
        -- destruct HF as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
           destruct (Z.eq_dec b 0) as [->|Hbnz]; [unfold zwin in H|].
           ++ destruct (cur_facts A M model 0 cap xs PI') as [[_ ->]|(? & _)]; lia.
           ++ destruct (cur_junk A M model b cap xs PI' a Hbnz ltac:(unfold zwin in H; exact H)) as [Hy|Hj]; [right; left; exact Hy | right; right; right; exact Hj].
        -- destruct HFc as [H|[[Hbnz H]|H]]; [left; exact H | | right; right; left; exact H].
           destruct (cur_junk A M model b cap xs PI' a Hbnz ltac:(unfold zwin in H; exact H)) as [Hy|Hj]; [right; left; exact Hy | right; right; right; exact Hj].
    + eapply (mdef_via_eff SEGS L MI HLimg_lo HLrw_img HLerr_rw A A'); [exact EFc | left; lia | lia | lia | | | exact WIN].
      * intros i Hi. apply (hi_unowned A M model); [exact AI | lia].
      * intros i Hi HF. exact (proj2 (Fc_sep _ HF) ltac:(lia)).
Qed.

Lemma Zlen_removelast : forall (xs : list Z), xs <> [] -> Zlen (removelast xs) = Zlen xs - 1.
Proof using.
  intros xs Hne. unfold Zlen. rewrite removelast_firstn_len. rewrite length_firstn.
  destruct xs; [congruence|]. cbn [length]. lia.
Qed.

Lemma Znth_removelast : forall (xs : list Z) i, 0 <= i < Zlen xs - 1 -> Znth i (removelast xs) = Znth i xs.
Proof using.
  intros xs i Hi. unfold Znth, Zlen in *. rewrite removelast_firstn_len, nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat i) (Init.Nat.pred (length xs))); [reflexivity | lia].
Qed.

Lemma pinv_pop : forall A M model b cap xs M',
  PINV A M model b cap xs -> xs <> [] ->
  M' = wbytes M (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * (Zlen xs - 1)))) ->
  PINV A M' model b cap (removelast xs).
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  intros A M model b cap xs M' PI Hne ->. pose proof sp_facts as (Hc & Hs47 & _ & Hcv). pose proof pat_win as PW.
  pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN].
  pose proof (pinv_placed A M model b cap xs PI') as PL.
  pose proof VEC as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FE).
  assert (STI : stores_in (zwin (pat + 8) (pat + 16)) M (wbytes M (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * (Zlen xs - 1)))))).
  { apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; [lia | cbn; lia |]. intros a Ha. unfold zwin. cbn in Ha. lia. }
  assert (SEPh : forall a, zwin (pat + 8) (pat + 16) a -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a).
  { intros a Ha. apply (placed_sep A M model pat 24 a AI PL). unfold zwin in Ha. lia. }
  pose proof (Zlen_removelast xs Hne) as HLR.
  assert (HL1 : 1 <= Zlen xs) by (destruct xs; [congruence | unfold Zlen; cbn [length]; lia]).
  constructor.
  - eapply stores_in_ainv; [exact AI | exact STI | intros a Ha; exact (proj1 (SEPh a Ha))].
  - exact MS. - exact FS.
  - eapply stores_in_sx; [exact SX | exact STI |]. intros a Ha.
    destruct (offimg_sep a (proj2 (SEPh a Ha))) as (H1 & H2 & _). split; assumption.
  - eapply roc_stores; [exact ROC | exact STI |]. intros a Ha. exact (proj2 (SEPh a Ha)).
  - unfold vec32. rewrite HLR.
    split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact STI | exact HD]|].
    split; [lia|]. split; [exact Hbb|].
    split; [eapply fld_agree; [lia | cbn; lia | exact F0 |]; eapply stores_in_agree; [exact STI|]; intros a Ha; unfold zwin in *; cbn in Ha; lia|].
    split; [apply (fld_wbytes8 SEGS); lia|].
    split; [eapply fld_agree; [lia | cbn; lia | exact F2 |]; eapply stores_in_agree; [exact STI|]; intros a Ha; unfold zwin in *; cbn in Ha; lia|].
    intros i Hi. rewrite Znth_removelast by lia. destruct (FE i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
    eapply fld_agree; [| | exact HF |]. 1,2: destruct Hbb as [[-> ->]|(Hbp & _ & Hcp & Hbc & _)]; cbn; lia.
    eapply stores_in_agree; [exact STI|]. intros a Ha. unfold zwin in *; cbn in Ha.
    destruct Hbb as [[-> ->]|(Hbp & _ & Hcp & Hbc & _ & Hdj)]; lia.
  - exact PP.
  - eapply eff_weaken; [eapply (eff_trans MI); [exact EF | eapply (eff_of_stores SEGS L MI A M _ W (FP b cap)); [exact STI|] |]|].
    + intros a Ha. left. left. unfold zwin in *. lia.
    + intros a Ha. eapply (hi_unowned A _ model). 2: unfold W_of, W in Ha; cbn in Ha; lia.
      eapply stores_in_ainv; [exact AI | exact STI | intros x Hx; exact (proj1 (SEPh x Hx))].
    + intros a [H|H]; exact H.
  - eapply stores_in_mdef; [exact STI | exact WIN].
Qed.

Lemma Zlen_firstn : forall (xs : list Z) k, 0 <= k <= Zlen xs -> Zlen (firstn (Z.to_nat k) xs) = k.
Proof using. intros xs k Hk. unfold Zlen in *. rewrite length_firstn. lia. Qed.

Lemma Znth_firstn : forall (xs : list Z) k i, 0 <= i < k -> Znth i (firstn (Z.to_nat k) xs) = Znth i xs.
Proof using.
  intros xs k i Hi. unfold Znth. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat k)); [reflexivity | lia].
Qed.

Lemma pinv_set_len : forall A M model b cap xs M' k,
  PINV A M model b cap xs -> 0 <= k <= Zlen xs ->
  M' = wbytes M (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * k))) ->
  PINV A M' model b cap (firstn (Z.to_nat k) xs).
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  intros A M model b cap xs M' k PI Hk ->. pose proof sp_facts as (Hc & Hs47 & _ & Hcv). pose proof pat_win as PW.
  pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN].
  pose proof (pinv_placed A M model b cap xs PI') as PL.
  pose proof VEC as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FE).
  assert (STI : stores_in (zwin (pat + 8) (pat + 16)) M (wbytes M (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * k))))).
  { apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; [lia | cbn; lia |]. intros a Ha. unfold zwin. cbn in Ha. lia. }
  assert (SEPh : forall a, zwin (pat + 8) (pat + 16) a -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a).
  { intros a Ha. apply (placed_sep A M model pat 24 a AI PL). unfold zwin in Ha. lia. }
  pose proof (Zlen_firstn xs k Hk) as HLR.
  constructor.
  - eapply stores_in_ainv; [exact AI | exact STI | intros a Ha; exact (proj1 (SEPh a Ha))].
  - exact MS. - exact FS.
  - eapply stores_in_sx; [exact SX | exact STI |]. intros a Ha.
    destruct (offimg_sep a (proj2 (SEPh a Ha))) as (H1 & H2 & _). split; assumption.
  - eapply roc_stores; [exact ROC | exact STI |]. intros a Ha. exact (proj2 (SEPh a Ha)).
  - unfold vec32. rewrite HLR.
    split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact STI | exact HD]|].
    split; [lia|]. split; [exact Hbb|].
    split; [eapply fld_agree; [lia | cbn; lia | exact F0 |]; eapply stores_in_agree; [exact STI|]; intros a Ha; unfold zwin in *; cbn in Ha; lia|].
    split; [apply (fld_wbytes8 SEGS); lia|].
    split; [eapply fld_agree; [lia | cbn; lia | exact F2 |]; eapply stores_in_agree; [exact STI|]; intros a Ha; unfold zwin in *; cbn in Ha; lia|].
    intros i Hi. rewrite Znth_firstn by lia. destruct (FE i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
    eapply fld_agree; [| | exact HF |]. 1,2: destruct Hbb as [[-> ->]|(Hbp & _ & Hcp & Hbc & _)]; cbn; lia.
    eapply stores_in_agree; [exact STI|]. intros a Ha. unfold zwin in *; cbn in Ha.
    destruct Hbb as [[-> ->]|(Hbp & _ & Hcp & Hbc & _ & Hdj)]; lia.
  - exact PP.
  - eapply eff_weaken; [eapply (eff_trans MI); [exact EF | eapply (eff_of_stores SEGS L MI A M _ W (FP b cap)); [exact STI|] |]|].
    + intros a Ha. left. left. unfold zwin in *. lia.
    + intros a Ha. eapply (hi_unowned A _ model). 2: unfold W_of, W in Ha; cbn in Ha; lia.
      eapply stores_in_ainv; [exact AI | exact STI | intros x Hx; exact (proj1 (SEPh x Hx))].
    + intros a [H|H]; exact H.
  - eapply stores_in_mdef; [exact STI | exact WIN].
Qed.

Lemma pinv_push_fast : forall A M model b cap xs M' x,
  PINV A M model b cap xs -> Zlen xs < cap -> 0 <= x < 2 ^ 32 ->
  M' = wbytes (wbytes M (Z_to_bv 64 (b + 4 * Zlen xs)) (word_to_le_bytes 4 (Z_to_bv 64 x)))
              (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs + 4))) ->
  PINV A M' model b cap (xs ++ [x]).
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  intros A M model b cap xs M' x PI Hlt Hx ->. pose proof sp_facts as (Hc & Hs47 & _ & Hcv). pose proof pat_win as PW.
  pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN].
  pose proof (pinv_placed A M model b cap xs PI') as PL.
  pose proof VEC as (Hv0 & Hv1 & HD & Hlen & Hbb & F0 & F1 & F2 & FE).
  destruct (cur_facts A M model b cap xs PI') as [[-> ->]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk)]; [lia|].
  set (G := fun a => zwin (pat + 8) (pat + 16) a \/ zwin (b + 4 * Zlen xs) (b + 4 * Zlen xs + 4) a).
  assert (STI : stores_in G M (wbytes (wbytes M (Z_to_bv 64 (b + 4 * Zlen xs)) (word_to_le_bytes 4 (Z_to_bv 64 x)))
              (Z_to_bv 64 (pat + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs + 4))))).
  { apply stores_in_wbytes_more; rewrite ?length_N_to_le_bytes; [| lia | cbn; lia | intros a Ha; subst G; left; unfold zwin; cbn in Ha; lia].
    apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; [lia | cbn; lia | intros a Ha; subst G; right; unfold zwin; cbn in Ha; lia]. }
  assert (SEPh : forall a, G a -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a).
  { intros a [Ha|Ha]; unfold zwin in Ha.
    - apply (placed_sep A M model pat 24 a AI PL). lia.
    - destruct (Hblk a ltac:(lia)) as (H1 & H2 & _). split; assumption. }
  pose proof (Zlen_app1 xs x) as HLA.
  constructor.
  - eapply stores_in_ainv; [exact AI | exact STI | intros a Ha; exact (proj1 (SEPh a Ha))].
  - exact MS. - exact FS.
  - eapply stores_in_sx; [exact SX | exact STI |]. intros a Ha.
    destruct (offimg_sep a (proj2 (SEPh a Ha))) as (H1 & H2 & _). split; assumption.
  - eapply roc_stores; [exact ROC | exact STI |]. intros a Ha. exact (proj2 (SEPh a Ha)).
  - unfold vec32. rewrite HLA.
    split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact STI | exact HD]|].
    split; [lia|]. split; [exact Hbb|].
    split; [eapply fld_agree; [lia | cbn; lia | exact F0 |]; eapply stores_in_agree; [exact STI|]; intros a Ha; subst G; unfold zwin in *; cbn in Ha; lia|].
    split; [replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia; apply (fld_wbytes8 SEGS); lia|].
    split; [eapply fld_agree; [lia | cbn; lia | exact F2 |]; eapply stores_in_agree; [exact STI|]; intros a Ha; subst G; unfold zwin in *; cbn in Ha; lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Zlen xs)) as [Hlo|Hhi].
    + rewrite Znth_app_l by lia. destruct (FE i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
      eapply fld_agree; [lia | cbn; lia | exact HF |]. eapply stores_in_agree; [exact STI|]. intros a Ha. subst G; unfold zwin in *; cbn in Ha. lia.
    + replace i with (Zlen xs) by lia. rewrite Znth_app_r1.
      split; [lia|]. unfold fld. rewrite CatExec.rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn; lia | cbn; lia | cbn; lia].
      apply (fld_wbytes4 SEGS); lia.
  - exact PP.
  - eapply eff_weaken; [eapply (eff_trans MI); [exact EF | eapply (eff_of_stores SEGS L MI A M _ W (FP b cap)); [exact STI|] |]|].
    + intros a [Ha|Ha]; left; [left; unfold zwin in *; lia | right; right; left; unfold zwin in *; lia].
    + intros a Ha. eapply (hi_unowned A _ model). 2: unfold W_of, W in Ha; cbn in Ha; lia.
      eapply stores_in_ainv; [exact AI | exact STI | intros y Hy; exact (proj1 (SEPh y Hy))].
    + intros a [H|H]; exact H.
  - eapply stores_in_mdef; [exact STI | exact WIN].
Qed.

Lemma pinv_pbslow : forall (xb : Z), forall {fx : FPState} cpb A M model b cap xs (R1 : bvmap 5 word) (ra src x : Z) (K : TSet),
  vec32_pbslow_stmt SEGS L MI ST xb cpb -> xb <= 2 ^ 32 -> pat mod 8 = 0 ->
  0 <= vc_stack cpb -> vc_stack cpb + NEW_STACK SEGS L MI + FRM <= STK ->
  PINV A M model b cap xs ->
  lenR <= Zlen xs -> Zlen xs < lenR + Z.of_nat kR -> Zlen xs = cap ->
  getr R1 10%bv = Z_to_bv 64 pat -> getr R1 11%bv = Z_to_bv 64 src -> getr R1 2%bv = Z_to_bv 64 (sp - FRM) ->
  getr R1 1%bv = Z_to_bv 64 ra -> ret_ok (Z_to_bv 64 ra) -> 0 <= ra < 2 ^ 64 ->
  getr R1 3%bv = getr R0 3%bv -> getr R1 4%bv = getr R0 4%bv ->
  sp - FRM <= src -> src + 4 <= sp -> src mod 4 = 0 -> fld SEGS M src 4 x -> 0 <= x < xb ->
  (forall A' R' M' model' (b' cap' : Z),
      PINV A' M' model' b' cap' (xs ++ [x]) -> kept R1 R' -> agree_on (zwin (sp - FRM) sp) M M' ->
      getr R' 10%bv = Z_to_bv 64 (b' + 4 * (Zlen xs + 1)) ->
      srealizes SEGS (cfg fx R' ra M' model') K) ->
  srealizes SEGS (cfg fx R1 (vc_entry cpb) M model) K.
Proof using AC SEGS L MI ST A0 s R0 M0 model0 sp ret STK FRM pat b0 cap0 xs0 lenR kR PC.
  intros xb fx cpb A M model b cap xs R1 ra src x K PB Hxb PAT8 Hvs Hfit PI HL1 HL2 Hfull0 G10 G11 G2 G1 Hret Hra G3 G4 Hs1 Hs2 Hs4 Fx Hx CONT.
  pose proof sp_facts as (Hc & Hs47 & Hs16 & Hcv). pose proof pat_win as PW.
  pose proof PI as PI'. destruct PI as [AI MS FS SX ROC VEC PP EF WIN]. pose proof CB as CB0. dCB. destruct CR0.
  pose proof (ai_nmax_bound MI) as HNM. pose proof MSpos as HMS. pose proof HlenR as HLR0. pose proof HFRM as [HF1 HF2].
  unfold NEW_STACK in Hfit.
  eapply (PB fx A s R1 M model (sp - FRM) ra pat b cap src x xs K); unfold NEW_STACK in *.
  -
    constructor.
    + exact AI. + exact MS. + exact ROC. + exact SX. + exact SXH0.
    + constructor; try assumption.
      * replace (sp - FRM) with (sp + (- (FRM / 16)) * 16) by (pose proof (Z_div_mod_eq_full FRM 16); lia).
        rewrite Z.mod_add by lia. exact Hs16.
      * lia.
      * rewrite G3. assumption. * rewrite G4. assumption.
    + lia.
    + unfold stack_room. replace (sp - FRM - (vc_stack cpb + (16 + MALLOC_STACK MI))) with (sp - STK + (STK - FRM - (vc_stack cpb + (16 + MALLOC_STACK MI)))) by lia.
      apply (mdef_store_ok_off SEGS M (sp - STK) STK); try lia. exact WIN.
    + intros a Ha. unfold zwin in Ha. split.
      * apply (hi_unowned A M model); [exact AI | lia].
      * apply (proj2 (Hwin0 a ltac:(unfold zwin; lia))).
    + intros a Ho. pose proof EF as [_ _ HOWN _ _ _]. destruct (HOWN a Ho) as [HoA|[Hnm|HF]].
      * exact (Hown_sx0 a HoA).
      * destruct Hnm as (Hni & _). exact (proj1 (offimg_sep a Hni)).
      * exact (proj1 (offimg_sep a (fp_offimg A M model b cap xs PI' a HF))).
    + exact Herr_sx0.
  - exact G10. - exact G11. - exact VEC.
  - exact Hfull0.
  - split; [exact (pinv_placed A M model b cap xs PI')|]. intros a Ha Hw. apply (proj2 OBJ0 a Ha). unfold zwin in *. lia.
  - exact PAT8.
  - exact Fx. - exact Hx.
  - split; [left; lia|]. intros a Ha Hw. unfold zwin in *. lia.
  - lia. - lia.
  - exact Hs4.
  - intros a Ha Hp. apply (proj2 OBJ0 a Hp). unfold zwin in *. lia.
  - transitivity (caps_bound lenR cap0 (Z.of_nat kR)); [|exact NMX]. unfold caps_bound.
    destruct PP as ([Hle Hcb] & _). pose proof (vgrow_mono cap (Z.max cap0 (2 * (lenR + Z.of_nat kR)))). destruct VEC as (_ & _ & _ & Hlen & _). lia.
  - exact (pinv_room A M model b cap xs PI' HL1 HL2 Hfull0).
  -
    intros A' R' M' model' b' RB VEC' A10' LAP0 EFc. remember (vgrow cap) as cap' eqn:Hc'.
    assert (ALT : (Zlen xs < cap /\ b' = b /\ cap' = cap /\ live MI A' = live MI A)
                  \/ (Zlen xs = cap /\ cap' = vgrow cap /\ lapply (live MI A) (LAdd b' (4 * cap') :: del_if b) (live MI A')))
      by (right; split; [exact Hfull0 | split; [exact Hc' | exact LAP0]]).
    destruct RB as [AI' MS' Hfs' Hfds' SX' KEPT].
    assert (Fc_sep : forall a, zwin pat (pat + 24) a \/ b <> 0 /\ zwin b (b + 4 * cap) a \/ zwin b' (b' + 4 * cap') a ->
                     ~ in_ranges (ly_img L) a /\ ~ (sp - STK <= a < sp)).
    { intros a [Hp|[[Hbnz Hb]|Hb']].
      - split; [exact (proj2 (placed_sep A0 M0 model0 pat 24 a AI0 (proj1 OBJ0) ltac:(unfold zwin in Hp; exact Hp))) | unfold zwin in Hp; lia].
      - destruct (cur_facts A M model b cap xs PI') as [[-> ->]|(Hbp & Hcp & HIn & Hce & Hdj & Hblk)]; [lia|].
        unfold zwin in Hb. destruct (Hblk a Hb) as (_ & Hni & _). split; [exact Hni | lia].
      - destruct VEC' as (_ & _ & _ & Hlen' & Hbb & _). unfold zwin in Hb'.
        destruct Hbb as [[-> ->]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|].
        destruct (ai_live_block MI A' M' model' b' (4 * cap') AI' HIn) as (_ & _ & _ & Hce & Hblk).
        destruct (Hblk a Hb') as (_ & Hni & _). split; [exact Hni | lia]. }
    apply (CONT A' R' M' model' b' cap'); [| exact KEPT | | exact A10'].
    2:{ eapply (agree_hi_via_eff SEGS L MI HLimg_lo HLrw_img HLerr_img A A' M M' model model'); [exact EFc | exact AI | exact AI' | lia | lia | | | cbn; lia].
        - replace (sp - (sp - FRM)) with FRM by lia. intros i Hi. replace (sp - FRM + i) with (sp - STK + (STK - FRM + i)) by lia. apply WIN. lia.
        - intros a Ha HF. exact (proj2 (Fc_sep a HF) ltac:(lia)). }
    constructor.
    + exact AI'. + exact MS'. + rewrite Hfs', Hfds'. exact FS. + exact SX'.
    + apply (img_ro_clear_of' SEGS L ST s); [|exact SX'].
      eapply (ro_clear_via_eff SEGS L MI HLimg_lo HLerr_rw A A' M M' model); [| exact AI | exact EFc | intros a Ha; exact (proj1 (Fc_sep a Ha)) | cbn; lia].
      intros w Hw. apply ROC; [exact (proj1 Hw) | exact (proj1 (proj2 Hw))].
    + exact VEC'.
    +
      destruct PP as ([Hle Hcb] & Hsame & Hgrow).
      destruct ALT as [(Hlt & -> & -> & HL) | (Hfull & Hcap' & LAP)].
      * split; [split; [exact Hle | exact Hcb]|]. split; [intros E; rewrite HL; exact (Hsame E)|]. intros NE. rewrite HL. exact (Hgrow NE).
      * cbn [lapply] in LAP. destruct LAP as (lv1 & [-> Hnin] & LAP).
        pose proof (vgrow_ge cap) as [Hg1 Hg2].
        assert (Hbb' : b' <> b /\ (b = 0 -> 0 < b')).
        { destruct VEC' as (_ & _ & _ & Hlen' & Hbb & _).
          destruct Hbb as [[-> Hc0]|(Hbp & _ & Hcp & _ & HIn & Hdj)]; [lia|]. split; [|lia].
          intros ->. destruct (cur_facts A M model b cap xs PI') as [[Hb0 _]|(_ & _ & HInA & _)]; [lia|].
          apply Hnin. change b with (fst (b, 4 * cap)). apply in_map. exact HInA. }
        destruct Hbb' as [Hne Hpos].
        assert (MEM : forall q k, In (q, k) (live MI A') <-> (In (q, k) (live MI A) /\ q <> b) \/ (q = b' /\ k = 4 * cap')).
        { intros q k. unfold del_if in LAP. destruct (Z.eqb_spec b 0) as [Hb0|Hb0].
          - cbn [lapply] in LAP. rewrite LAP. cbn [In]. split.
            + intros [E|H]; [right; injection E as <- <-; split; [reflexivity|lia] | left; split; [exact H|]].
              intros ->. destruct (cur_facts A M model b cap xs PI') as [[_ Hc0]|(Hbp & _)]; [|lia].
              destruct (ai_live_block MI A M model b k AI H) as (_ & _ & Hp & _). lia.
            + intros [[H _]|[-> ->]]; [right; exact H | left; f_equal; lia].
          - cbn [lapply] in LAP. destruct LAP as (lv2 & HD & <-). rewrite (HD q k). cbn [In]. split.
            + intros [[E|H] Hq]; [right; injection E as <- <-; split; [reflexivity|lia] | left; split; assumption].
            + intros [[H Hq]|[-> ->]]; [split; [right; exact H | exact Hq] | split; [left; f_equal; lia | exact Hne]]. }
        split; [unfold vgrow in *; lia|]. split; [intros E; exfalso; lia|]. intros _.
        destruct (Z.eq_dec cap cap0) as [E|NE].
        -- destruct (Hsame E) as [-> HL]. rewrite HL in MEM, Hnin. split; [exact MEM|].
           intros q k Hq Hqb ->. apply Hnin. change b' with (fst (b', k)). apply in_map. exact Hq.
        -- destruct (Hgrow NE) as [Hm Hfresh]. split.
           ++ intros q k. rewrite MEM, (Hm q k). split.
              ** intros [[[[H1 H2]|[-> ->]] H3]|[-> ->]]; [left; split; assumption | exfalso; exact (H3 eq_refl) | right; split; reflexivity].
              ** intros [[H1 H2]|[-> ->]]; [left | right; split; reflexivity]. split; [left; split; assumption|]. exact (Hfresh q k H1 H2).
           ++ intros q k Hq Hqb ->. apply Hnin. change b' with (fst (b', k)). apply in_map. apply Hm. left. split; [exact Hq | exact Hqb].
    +
      eapply eff_weaken.
      * eapply (eff_trans MI); [exact EF | | intros a Ha; apply (hi_unowned A' M' model'); [exact AI' | unfold W_of, W in Ha; cbn in Ha; lia]].
        eapply (eff_widen SEGS L MI); [exact EFc | cbn; lia | cbn; lia].
      * intros a [HF|HFc].
        -- destruct HF as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
           destruct (Z.eq_dec b 0) as [->|Hbnz]; [unfold zwin in H|].
           ++ destruct (cur_facts A M model 0 cap xs PI') as [[_ ->]|(? & _)]; lia.
           ++ destruct (cur_junk A M model b cap xs PI' a Hbnz ltac:(unfold zwin in H; exact H)) as [Hy|Hj]; [right; left; exact Hy | right; right; right; exact Hj].
        -- destruct HFc as [H|[[Hbnz H]|H]]; [left; exact H | | right; right; left; exact H].
           destruct (cur_junk A M model b cap xs PI' a Hbnz ltac:(unfold zwin in H; exact H)) as [Hy|Hj]; [right; left; exact Hy | right; right; right; exact Hj].
    + eapply (mdef_via_eff SEGS L MI HLimg_lo HLrw_img HLerr_rw A A'); [exact EFc | left; lia | lia | lia | | | exact WIN].
      * intros i Hi. apply (hi_unowned A M model); [exact AI | lia].
      * intros i Hi HF. exact (proj2 (Fc_sep _ HF) ltac:(lia)).
Qed.

End Push.
