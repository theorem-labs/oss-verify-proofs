(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InftreesCoverage InflateArms Inflate InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 Callee6i.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Fixpoint fields_upd_ok (F : franges) (mem' : word -> option byte) (Sb : Z) (L : list (Z * nat)) (vs vs' : list Z) : Prop :=
  match L, vs, vs' with
  | [], [], [] => True
  | (o, w) :: L', v :: t, v' :: t' =>
      ((v' = v /\ disj_franges F (Sb + o) (Z.of_nat w)) \/ cell s6_segs mem' (Sb + o) w v') /\ fields_upd_ok F mem' Sb L' t t'
  | _, _, _ => False
  end.

Lemma fields_agree_upd : forall F mem mem' Sb L vs vs' size,
  fields s6_segs mem Sb L vs -> layout_within L size = true ->
  agree_out F mem mem' -> fields_upd_ok F mem' Sb L vs vs' ->
  0 <= Sb -> Sb + size <= 2 ^ 64 ->
  fields s6_segs mem' Sb L vs'.
Proof.
  intros F mem mem' Sb L. induction L as [|[o w] L' IH]; intros vs vs' size Hf HL Hag HU HS HSz.
  - destruct vs; destruct vs'; cbn in HU; try contradiction. exact I.
  - destruct vs as [|v t]; [destruct Hf|]. destruct vs' as [|v' t']; [destruct HU|].
    destruct Hf as [Hc Hf']. destruct HU as [HU1 HU'].
    cbn [layout_within] in HL. apply andb_prop in HL as [HL HL']. apply andb_prop in HL as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    split; [| exact (IH t t' size Hf' HL' Hag HU' HS HSz)].
    destruct HU1 as [[-> Hd] | Hc']; [| exact Hc'].
    apply (cell_agree_out s6_segs F mem mem' _ w _ Hag Hd); [lia | lia | exact Hc].
Qed.


Section Itable.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition ITF (pbo : Z) : franges :=
    [(cv_sp v - INF_FRAME - INF_SCRATCH, INF_SCRATCH); (cv_S v + 808, 6352); (cv_S v + 160, 8); (cv_S v + pbo, 4)].

  Lemma ITF_agree : forall pbo M M',
    (forall x : word,
       ~ (cv_sp v - 224 - ITFR6 <= bv_unsigned x < cv_sp v - 224) -> ~ (cv_S v + 808 <= bv_unsigned x < cv_S v + 7160) ->
       ~ (cv_S v + 160 <= bv_unsigned x < cv_S v + 168) -> ~ (cv_S v + pbo <= bv_unsigned x < cv_S v + pbo + 4) ->
       M' x = M x) ->
    agree_out (ITF pbo) M M'.
  Proof.
    intros pbo M M' H x Hx. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH, ITFR6 in *. apply H; intros K; apply Hx; cbn; lia.
  Qed.

  Ltac upd_fields CfS CS Csp :=
    repeat (split; [first [ right; assumption
                          | left; split; [reflexivity | intros x Hx Hin; unfold ITF, in_franges, INF_FRAME, INF_SCRATCH in Hin; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add] in Hx; clear - Hx Hin CfS CS Csp; lia] ] |]);
    exact I.

  Lemma LMEM_itable : forall s c r M M' (pbo nx' bits' : Z) (tbl' work' : arr),
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v -> (pbo = 136 \/ pbo = 140) ->
    agree_out (ITF pbo) M M' -> (forall x, M x <> None -> M' x <> None) ->
    cells s6_segs M' (cv_S v + 1384) 4 4 1444 (arr_get tbl') -> cells s6_segs M' (cv_S v + 808) 2 2 288 (arr_get work') ->
    cell s6_segs M' (cv_S v + 160) 8 (cv_S v + 1384 + 4 * nx') -> cell s6_segs M' (cv_S v + pbo) 4 bits' ->
    LMEM v (mkW (iset_work (iset_codes (iset_next (if pbo =? 136 then iset_lenbits s bits' else iset_distbits s bits') nx') tbl') work') c r) M'.
  Proof.
    intros s c r M M' pbo nx' bits' tbl' work' HM Hput Hpb Hag Hg Hcodes Hwork Hnext Hbits.
    open_ictx C. open_lmem HM. unfold mapped in *.
    assert (DJo : forall a n, (cv_sp v - 224 <= a \/ a + n <= cv_sp v - 224 - 192) -> (a + n <= cv_S v \/ cv_S v + 7176 <= a) -> disj_franges (ITF pbo) a n).
    { intros a n Ha Hb x Hx Hin. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH in Hin. clear - Ha Hb Hx Hin Hpb. lia. }
    set (s1 := if pbo =? 136 then iset_lenbits s bits' else iset_distbits s bits').
    assert (EL : is_lens (iset_work (iset_codes (iset_next s1 nx') tbl') work') = is_lens s) by (subst s1; destruct (pbo =? 136); destruct s; reflexivity).
    assert (EW : is_window (iset_work (iset_codes (iset_next s1 nx') tbl') work') = is_window s) by (subst s1; destruct (pbo =? 136); destruct s; reflexivity).
    constructor; cbn [w_s w_c w_r]; rewrite ?EL, ?EW.
    - intros x Hx. rewrite (Hag x); [exact (Mrod x Hx)|]. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH. unfold ROD6_LO, ROD6_HI in Hx.
      unfold offimg, IMG6_TOP in CoS. clear - Hx Csp CoS CS Hpb. lia.
    - unfold is6_scalars, isl_scalars in *.
      apply (fields_agree_upd (ITF pbo) M M' (cv_S v) is6_layout _ _ is6_SIZE Msc is6_layout_within Hag); [| clear - CS; lia | unfold is6_SIZE; clear - CS; lia].
      unfold sep in CfS. subst s1. destruct Hpb as [-> | ->]; cbn [Z.eqb]; destruct s; cbn; upd_fields CfS CS Csp.
    - eapply (cells_agree_out _ _ M M'); [exact Hag | | cbn; lia | lia | lia | exact Mlens].
      intros x Hx Hin. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH in Hin. unfold sep in CfS. clear - Hx Hin CfS CS Hpb. lia.
    - exact Hwork.
    - cbn. exact Hcodes.
    - intros Hwn. eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJo; [unfold sep in CfW; clear - CfW CWB Hwn; lia | unfold sep in CSW; clear - CSW CWB Hwn; lia] | cbn; lia | lia | lia | exact (Mwin Hwn)].
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJo; [specialize (CfI ltac:(lia)); unfold sep in CfI; clear - CfI CI0; lia | specialize (CSI ltac:(lia)); unfold sep in CSI; clear - CSI CI0; lia] | cbn; lia | lia | lia | exact Minp].
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      eapply (cells_agree_out _ _ M M'); [exact Hag | apply DJo; [specialize (CfP ltac:(lia)); unfold sep in CfP; clear - CfP CP0 Hput; lia | specialize (CSP ltac:(lia)); unfold sep in CSP; clear - CSP CP0 Hput; lia] | cbn; lia | lia | lia | exact Mout].
    - eapply (izs6_agree v C); [exact Mzs | exact Hag | apply DJo; [unfold sep in CfZ; clear - CfZ CZP; lia | unfold sep in CZS; clear - CZS CZP; lia]].
    - unfold iframe6 in *. unfold INF_FRAME in *.
      destruct Mfr as (Fsv & F104 & F96 & F88 & F72 & F56 & F48 & F40 & F32 & F24 & F16 & F8 & Fd0).
      split.
      { intros rg o Hro. pose proof (Fsv rg o Hro) as X. cbn in Hro.
        assert (Ho : 120 <= o /\ o + 8 <= 224)
          by (clear -Hro; destruct Hro as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-; lia). clear Hro.
        eapply (cell_agree_out _ _ M M'); [exact Hag | apply DJo; [lia | unfold sep in CfS; clear - CfS CS Ho; lia] | lia | cbn; lia | exact X]. }
      repeat match goal with |- _ /\ _ => split end;
        (eapply (cell_agree_out _ _ M M'); [exact Hag | apply DJo; [lia | unfold sep in CfS; clear - CfS CS; lia] | lia | cbn; lia | assumption]).
    - unfold INF_FRAME in *. eapply (cell_agree_out _ _ M M'); [exact Hag | apply DJo; [lia | unfold sep in CfS; clear - CfS CS; lia] | lia | cbn; lia | exact Moutc].
    - intros x Hx. apply Hg. apply Mmap_f. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_Z. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_S. exact Hx.
    - intros x Hx. apply Hg. apply Mmap_P. exact Hx.
    - intros Hwn x Hx. apply Hg. apply (Mmap_W Hwn). exact Hx.
  Qed.

  Lemma RETC_itable : forall w pbo M M', RETC v w M -> (pbo = 136 \/ pbo = 140) -> agree_out (ITF pbo) M M' -> RETC v w M'.
  Proof.
    intros w pbo M M' H Hpb Hag. pose proof (ic_sp _ C) as Csp. pose proof (ic_d_fS _ C) as CfS. pose proof (ic_S _ C) as CS.
    unfold RETC, INF_FRAME, INF_SCRATCH, IMG6_TOP, sep in *.
    eapply (cell_agree_out _ _ M M'); [exact Hag | | lia | cbn; lia | exact H].
    intros x Hx Hin. unfold ITF, in_franges, INF_FRAME, INF_SCRATCH in Hin. clear - Hx Hin Csp CfS CS Hpb. lia.
  Qed.
End Itable.

Definition LVARK (v : icv) (w : iw) (R : bvmap 5 word) : Prop :=
  let r := w_r w in
  getr R 18 = zw (ir_have r) /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 9 = zw (ir_left r)
  /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r)
  /\ getr R 27 = zw (cv_I0 v + ir_next r).
End FXG.
