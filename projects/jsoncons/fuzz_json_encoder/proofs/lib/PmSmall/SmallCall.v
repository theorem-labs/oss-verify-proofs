(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutL5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPC.
Abbreviation mem := (word -> option byte).

Section PureCall.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable FPI : FPState -> Prop.
Variables (CPS : list CC.cutpoint) (NF : nat) (E0 : env) (M0 : mem) (model0 : Model) (F0 : list SGP.region) (K : ShapeAlg.TSet).
Variables (sp0 SCR sptop tp : Z).
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis U2 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 tp.
Hypothesis STK : L5C.stk sptop M0 sp0 SCR.
Hypothesis SCRP : 0 <= SCR.
(* [comment removed for export] *)
Variable CRS : list SGP.region.
Hypothesis CRS_ok : forall r, In r CRS -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> a < sp0 - SCR \/ sp0 <= a.

Abbreviation Amb := (CL.pure_amb NF E0 M0 model0 F0).

(* [comment removed for export] *)
Lemma leaf_regs_ok : forall c ps E' R' M M', CH2.all_regs_chk ps = true -> CC.leaf_facts segs c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R'.
Proof.
  intros c ps E' R' M M' H HLF r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
    cbn [edenot]. replace (0%bv : bv 5) with (Z_to_bv 5 0) by (apply bv_eq; reflexivity). exact (CC.lf_x0 _ _ _ _ _ _ _ HLF).
  - assert (Hr : (1 <= ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
      unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
    unfold CA.ps_reglist. destruct (ridx r) as [|m] eqn:Em; [lia|]. cbn [nth].
    rewrite (nth_indep _ (ELit 0) (CA.ps_reg ps 0%nat)) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (CA.ps_reg ps) (seq 1 31) 0%nat m). rewrite seq_nth by lia.
    unfold CH2.all_regs_chk in H. rewrite forallb_forall in H. specialize (H (1 + m)%nat ltac:(apply in_seq; lia)).
    unfold CA.ps_reg. destruct (find (fun ie : nat * expr => Nat.eqb (fst ie) (1 + m)) (SR.ps_regs ps)) as [[i e]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hi]. cbn [fst snd] in *. apply Nat.eqb_eq in Hi. subst i.
      destruct (CC.lf_regs _ _ _ _ _ _ _ HLF _ _ Hin) as [_ Hg]. rewrite <- Hg. f_equal. rewrite <- (CC.reg_of_ridx r). rewrite Em. reflexivity.
    + exfalso. apply existsb_exists in H as (ie & Hin & Hb). rewrite (find_none _ _ Hf ie Hin) in Hb. discriminate.
Qed.

Lemma within_sem : forall E M kn REGS b k n, know_ok segs E M kn -> CH.within kn REGS b k n = true ->
  exists r, In r REGS /\ forall a, estart E (SA b k) <= a < estart E (SA b k) + elenZ E n -> CH2.in_reg E r a.
Proof.
  intros E M kn REGS b k n HK H. unfold CH.within in H. destruct (SGP.withinE kn REGS b k n) eqn:H1.
  - unfold SGP.withinE in H1. apply existsb_exists in H1 as ([[rb rlo] rlen] & Hin & Hx).
    destruct (xinside_sound segs E M kn b k n rb rlo rlen HK Hx) as [X1 X2].
    exists (rb, rlo, rlen). split; [exact Hin|]. intros a Ha. unfold CH2.in_reg. lia.
  - apply existsb_exists in H as ([[rb rlo] rlen] & Hin & Hx).
    destruct (CX.xinside2_sound segs E M kn b k n rb rlo rlen HK Hx) as [X1 X2].
    exists (rb, rlo, rlen). split; [exact Hin|]. intros a Ha. unfold CH2.in_reg. lia.
Qed.

Lemma ev2 : forall E, env_agree NF E0 E -> bv_unsigned (ev E 2) = sp0.
Proof. intros E [H _]. rewrite <- (H 2%nat) by lia. exact U2. Qed.

Lemma entry_support : forall E M X b k n, kentry_ok segs E M X -> CH.entry_reg X = Some (b, k, n) ->
  forall x, CH.ksupport E X x -> 0 <= x < 2 ^ 64 /\ estart E (SA b k) <= x < estart E (SA b k) + elenZ E n.
Proof.
  intros E M X b k n HK He x Hx.
  destruct X as [[kb kk] w v|[kb kk] m|[kb kk] m id|lo hi|e m|e lo hi|[kb kk] m|a1 n1 a2 n2|[kb kk] m c|[kb kk] m]; cbn [CH.entry_reg] in He; try discriminate;
    injection He as <- <- <-; cbn [CH.ksupport kentry_ok] in *.
  - destruct HK as (Hw & (F1 & F2 & F3 & F4) & _). unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
Qed.

(* [comment removed for export] *)
Definition keep_regs (scr csp : Z) : list SGP.region := (EVar 2, csp, ELit (- csp)) :: (EVar 2, - SCR, ELit (SCR + csp - scr)) :: CRS.
Definition keep_chk (kn : list kentry) (scr csp : Z) (wregs : list SGP.region) (X : kentry) : bool :=
  match X with
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true
  | KUnk _ _ | KWr _ _ => true
  | KImg lo hi => (Z.leb 0 lo && Z.leb hi (2 ^ 40) && Z.ltb (hi - lo) (2 ^ 64)
                   && forallb (fun w : SGP.region => let '(wb, wk, wn) := w in APC.fact_ok kn (KDisj (SA (ELit 0) lo) (ELit (hi - lo)) (SA wb wk) wn)) wregs)%bool
  | _ => match CH.entry_reg X with
         | Some (b, k, n) => (CH.within kn (keep_regs scr csp) b k n
                              && forallb (fun w : SGP.region => let '(wb, wk, wn) := w in APC.fact_ok kn (KDisj (SA b k) n (SA wb wk) wn)) wregs)%bool
         | None => false
         end
  end.
Definition kept_chk (cells : list kentry) (scr csp : Z) (nx : nat) (wregs : list SGP.region) (X : kentry) : bool :=
  (CC.has_cell cells X && keep_chk cells scr csp wregs X && APC.kentry_vars_lt nx X)%bool.

Definition call_chk (scr : Z) (ng : nat) (wregs : list SGP.region) (news : list kentry) (a0x : option expr)
           (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS - ng)%nat in
  let cells := SR.ps_cells ps in
  match nth 1 regs (ELit 0), split_lit (nth 2 regs (ELit 0)) with
  | ELit ra, (EVar 2, csp) =>
      let regs1 := APC.sr_fresh regs APC.caller_saved (nx + ng) in
      if (CH2.all_regs_chk ps && Nat.leb (APC.NCS + ng) (CC.cp_nx cj) && Nat.leb (CC.cp_nx c) nx && Nat.leb NF (CC.cp_nx c)
          && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx cells
          && Z.eqb ra (CC.cp_pc cj) && Z.eqb (ra mod 2) 0 && Z.leb 0 ra && Z.ltb ra (2 ^ 47)
          && expr_eqb (nth 4 regs (ELit 0)) (EVar 4)
          && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1)) && CC.has_cell cells (KRange (CC.cp_meas c) 1 CC.MB)
          && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
          && Z.eqb (csp mod 16) 0 && Z.leb csp 0 && Z.leb 0 scr && Z.leb (- SCR) (csp - scr)
          && CA.regs_eqb (CC.cp_regs cj) (match a0x with Some e => sr_upd regs1 10 e | None => regs1 end)
          && forallb (fun X => (kept_chk cells scr csp nx wregs X || CC.has_cell news X)%bool) (CC.cp_know cj))%bool
      then Some (CH2.CI regs nx csp ra) else None
  | _, _ => None
  end.

Lemma keep_sound : forall E' (M' M2 : mem) cells scr csp wregs (Wc : list L5.range) X,
  know_ok segs E' M' cells -> kentry_ok segs E' M' X -> keep_chk cells scr csp wregs X = true -> env_agree NF E0 E' ->
  csp <= 0 -> 0 <= scr -> - SCR <= csp - scr ->
  L5.frame_but ((sp0 + csp - scr, scr) :: Wc) M' M2 -> mem_grows M' M2 ->
  (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CH2.in_reg E' r a) ->
  (forall x, CH.ksupport E' X x -> M2 (Z_to_bv 64 x) = M' (Z_to_bv 64 x))
  \/ (CH.def_only X = true /\ forall x, CH.ksupport E' X x -> M' (Z_to_bv 64 x) <> None -> M2 (Z_to_bv 64 x) <> None).
Proof.
  intros E' M' M2 cells scr csp wregs Wc X HK HY0 K2 HagE' Hc1 Hs0 Hc2 HFB HG2 HWc.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. destruct STK as (S1 & S2 & S3 & S4 & S5).
  assert (KEEPX : forall x, 0 <= x < 2 ^ 64 ->
            (sp0 + csp <= x \/ x < sp0 + csp - scr) -> (forall w, In w Wc -> ~ L5.in_rng w x) -> M2 (Z_to_bv 64 x) = M' (Z_to_bv 64 x)).
  { intros x Hx Hs Hw. apply HFB. rewrite u64_of_Z by lia. intros w [<-|Hin]; [unfold L5.in_rng; cbn [fst snd]; lia | exact (Hw w Hin)]. }
  assert (REG : forall b k n, CH.entry_reg X = Some (b, k, n) ->
            (CH.within cells (keep_regs scr csp) b k n
             && forallb (fun w : SGP.region => let '(wb, wk, wn) := w in APC.fact_ok cells (KDisj (SA b k) n (SA wb wk) wn)) wregs)%bool = true ->
            forall x, CH.ksupport E' X x -> M2 (Z_to_bv 64 x) = M' (Z_to_bv 64 x)).
  { intros b k n He Hw x Hx. apply andb_prop in Hw as [Kw Kd]. destruct (entry_support E' M' X b k n HY0 He x Hx) as [Hfl Hin].
    destruct (within_sem E' M' _ _ b k n HK Kw) as (r & Hr & Hs). specialize (Hs x Hin).
    apply KEEPX; [exact Hfl | |].
    - destruct Hr as [<-|[<-|Hr]].
      + unfold CH2.in_reg, estart, elenZ in Hs. cbn [a_base a_off edenot] in Hs. rewrite (ev2 E' HagE') in Hs. rewrite u64_of_Z in Hs by lia. lia.
      + unfold CH2.in_reg, estart, elenZ in Hs. cbn [a_base a_off edenot] in Hs. rewrite (ev2 E' HagE') in Hs. rewrite u64_of_Z in Hs by lia. lia.
      + destruct (CRS_ok r Hr) as [Hv Hc]. specialize (Hc x (CH2.in_reg_agree NF E0 E' r x HagE' Hv Hs)). lia.
    - intros w0 Hw0 Hin0. destruct (HWc w0 x Hw0 Hin0) as ([[wb wk] wn] & Hwr & Hwin). rewrite forallb_forall in Kd. specialize (Kd _ Hwr). cbn beta iota in Kd.
      pose proof (APS.fact_ok_sound segs E' M' _ _ HK Kd) as Gd. cbn [kentry_ok] in Gd. unfold CH2.in_reg in Hwin. lia. }
  destruct X as [[kb kk] w v|[kb kk] m|[kb kk] m id|lo hi|e m|e lo hi|[kb kk] m|a1 n1 a2 n2|[kb kk] m c0|[kb kk] m]; cbn [keep_chk] in K2.
  - left. eapply REG; [reflexivity | exact K2].
  - left. eapply REG; [reflexivity | exact K2].
  - left. eapply REG; [reflexivity | exact K2].
  - (* [comment removed for export] *) left. intros x Hx. cbn [CH.ksupport] in Hx. apply andb_prop in K2 as [K2 Kd]. apply andb_prop in K2 as [K2 Klt]. apply andb_prop in K2 as [Klo Khi].
    apply Z.leb_le in Klo, Khi. apply Z.ltb_lt in Klt.
    apply KEEPX; [lia | lia |].
    intros w0 Hw0 Hin0. destruct (HWc w0 x Hw0 Hin0) as ([[wb wk] wn] & Hwr & Hwin). rewrite forallb_forall in Kd. specialize (Kd _ Hwr). cbn beta iota in Kd.
    pose proof (APS.fact_ok_sound segs E' M' _ _ HK Kd) as Gd. cbn [kentry_ok] in Gd. unfold CH2.in_reg in Hwin.
    assert (E1 : estart E' (SA (ELit 0) lo) = lo) by (unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
    assert (E2' : elenZ E' (ELit (hi - lo)) = hi - lo) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
    rewrite E1, E2' in Gd. lia.
  - left. intros x Hx. exfalso. exact Hx.
  - left. intros x Hx. exfalso. exact Hx.
  - right. split; [reflexivity|]. intros x _ Hd. exact (HG2 _ Hd).
  - left. intros x Hx. exfalso. exact Hx.
  - left. eapply REG; [reflexivity | exact K2].
  - right. split; [reflexivity|]. intros x _ Hd. exact (HG2 _ Hd).
Qed.

(* [comment removed for export] *)
Lemma pure_call_ret : forall scr ng wregs news a0x i c ps j cj ci,
  nth_error CPS j = Some cj -> call_chk scr ng wregs news a0x c ps cj = Some ci -> CL.sub_F NF E0 F0 c ->
  forall E R M model E' R' M',
    CC.At segs c E R M -> Amb i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
    CC.IH segs CPS Amb K FPI (CC.meas c E) ->
    (model = model0 /\ env_agree NF E0 E' /\ regs_ok E' (CA.ps_reglist ps) R' /\ know_ok segs E' M' (SR.ps_cells ps) /\
     getr R' 1%bv = Z_to_bv 64 (CC.cp_pc cj) /\ L5.ra_ok (CC.cp_pc cj) /\ getr R' 2%bv = Z_to_bv 64 (sp0 + CH2.ci_csp ci) /\ getr R' 4%bv = Z_to_bv 64 tp /\
     L5C.stk sptop M' (sp0 + CH2.ci_csp ci) scr /\ (forall a : word, SGP.outside E0 F0 a -> M' a = M0 a) /\ mem_grows M0 M' /\
     SR.ps_pc ps = SR.ps_pc ps /\ CH2.ci_csp ci <= 0 /\ 0 <= scr /\ - SCR <= CH2.ci_csp ci - scr) /\
    forall (fx2 : FPState) R2 M2 ghosts (Wc : list L5.range),
      length ghosts = ng -> FPI fx2 ->
      (forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r) ->
      match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) e | None => True end ->
      L5.frame_but ((sp0 + CH2.ci_csp ci - scr, scr) :: Wc) M' M2 -> mem_grows M' M2 ->
      (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CH2.in_reg E' r a) ->
      (forall x : word, SGP.outside E0 F0 x -> L5.outside ((sp0 + CH2.ci_csp ci - scr, scr) :: Wc) (bv_unsigned x)) ->
      (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok segs (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2 X) ->
      srealizes segs SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 (CC.cp_pc cj)) M2 (seg_rom segs)) model0) K.
Proof.
  intros scr ng wregs news a0x i c ps j cj ci Hcj H HsubF E R M model E' R' M' HAt HA Hag HLF HIH. unfold call_chk in H.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |] eqn:Hra; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp] eqn:Hsp.
  destruct spb as [|v| | | | | |]; try discriminate. destruct v as [|[|[|v]]]; cbv beta iota zeta in H; try discriminate.
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as <-. cbn [CH2.ci_csp CH2.ci_nx].
  apply andb_prop in Hb as [Hb Z4]. apply andb_prop in Hb as [Hb Z1].
  apply andb_prop in Hb as [Hb Y18]. apply andb_prop in Hb as [Hb Y17]. apply andb_prop in Hb as [Hb Y16]. apply andb_prop in Hb as [Hb Y15].
  apply andb_prop in Hb as [Hb Y14]. apply andb_prop in Hb as [Hb Y13]. apply andb_prop in Hb as [Hb Y12]. apply andb_prop in Hb as [Hb Y11].
  apply andb_prop in Hb as [Hb Y10]. apply andb_prop in Hb as [Hb Y9]. apply andb_prop in Hb as [Hb Y8]. apply andb_prop in Hb as [Hb Y7].
  apply andb_prop in Hb as [Hb Y6]. apply andb_prop in Hb as [Hb Y5]. apply andb_prop in Hb as [Hb Y4b]. apply andb_prop in Hb as [Hb Y4]. apply andb_prop in Hb as [Y2 Y3].
  apply Nat.leb_le in Y3, Y4, Y4b. apply Z.eqb_eq in Y7, Y8, Y15. apply Z.leb_le in Y9, Y16, Y17, Y18. apply Z.ltb_lt in Y10.
  apply expr_eqb_eq in Y11, Y12. apply CC.has_cell_In in Y13. apply CH2.regs_eqb_eq in Z1.
  set (nx := (CC.cp_nx cj - APC.NCS - ng)%nat) in *.
  pose proof (leaf_regs_ok c ps E' R' M M' Y2 HLF) as HR.
  pose proof (CL.pure_amb_step segs NF E0 M0 model0 F0 i i c ps E E' E' R' M M' model HsubF Y4b HA Hag HLF (CC.env_agree_refl _ _)) as (Hmod & HagE' & Hfr & Hgr).
  assert (HK : know_ok segs E' M' (SR.ps_cells ps)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. destruct STK as (S1 & S2 & S3 & S4 & S5).
  assert (G1 : getr R' 1%bv = Z_to_bv 64 ra).
  { rewrite (HR 1%bv). unfold sr_get. change (bv_eqb (1%bv : bv 5) 0) with false. cbv iota. change (ridx 1%bv) with 1%nat. rewrite Hra. reflexivity. }
  assert (G2 : getr R' 2%bv = Z_to_bv 64 (sp0 + csp)).
  { rewrite (HR 2%bv). unfold sr_get. change (bv_eqb (2%bv : bv 5) 0) with false. cbv iota. change (ridx 2%bv) with 2%nat.
    rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal.
    rewrite (APS.split_lit_denot E' _ _ _ Hsp). cbn [edenot]. rewrite (ev2 E' HagE'). apply u64_of_Z. lia. }
  assert (G4 : getr R' 4%bv = Z_to_bv 64 tp).
  { rewrite (HR 4%bv). unfold sr_get. change (bv_eqb (4%bv : bv 5) 0) with false. cbv iota. change (ridx 4%bv) with 4%nat. rewrite Y11. cbn [edenot].
    destruct HagE' as [Y _]. rewrite <- (Y 4%nat) by lia. exact TP0. }
  assert (HSTK : L5C.stk sptop M' (sp0 + csp) scr).
  { split; [rewrite Z.add_mod by lia; rewrite S1, Y15; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. apply Hgr. replace (sp0 + csp - scr + k) with (sp0 - SCR + (SCR + csp - scr + k)) by lia. apply S5. lia. }
  split.
  { split; [exact Hmod|]. split; [exact HagE'|]. split; [exact HR|]. split; [exact HK|]. split; [rewrite G1, Y7; reflexivity|].
    split; [rewrite <- Y7; unfold L5.ra_ok; split; [lia | exact Y8]|]. split; [exact G2|]. split; [exact G4|]. split; [exact HSTK|]. split; [exact Hfr|]. split; [exact Hgr|]. split; [reflexivity|]. split; [exact Y16|]. split; [exact Y17 | exact Y18]. }
  intros fx2 R2 M2 ghosts Wc Hlen HFP2 Hkeep Ha0 HFB HG2 HWc HWF Hnews.
  set (E2 := CH2.retEx E' nx ghosts R2) in *.
  pose proof (CH2.retEx_agree E' nx ghosts R2 : env_agree nx E' E2) as Hag2.
  assert (V5 : CC.cp_nx cj = (nx + ng + APC.NCS)%nat) by (unfold nx; lia).
  apply (HIH j cj fx2 E2 R2 M2 model0 Hcj).
  - split.
    + (* [comment removed for export] *)
      assert (HR1 : regs_ok E2 (APC.sr_fresh (CA.ps_reglist ps) APC.caller_saved (nx + ng)) R2).
      { unfold E2, CH2.retEx. rewrite Hlen. apply (CH2.ret_regs (APS.ext_list E' nx ghosts) _ (nx + ng) R' R2).
        - intros r. rewrite (HR r). apply (SR.edenot_agree_AP nx); [apply APS.ext_list_agree|].
          unfold sr_get. destruct (bv_eqb r 0); [reflexivity | apply CH.nth_vars_lt; exact Y5].
        - eapply APS.sr_vars_lt_mono; [exact Y5 | lia].
        - exact Hkeep. }
      rewrite Z1. destruct a0x as [e|]; [apply CH2.regs_ok_upd_same; [exact HR1 | exact Ha0] | exact HR1].
    + (* [comment removed for export] *)
      unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in Z4. specialize (Z4 Y HY).
      apply orb_prop in Z4 as [Hk|Hn]; [|apply CC.has_cell_In in Hn; exact (Hnews Y Hn HY)].
      unfold kept_chk in Hk. apply andb_prop in Hk as [Hk K3]. apply andb_prop in Hk as [K1 K2]. apply CC.has_cell_In in K1.
      pose proof (proj1 (Forall_forall _ _) HK _ K1) as HY0.
      assert (G : know_ok segs E' M2 [Y]).
      { apply (CH.know_transport segs E' M' M2 [Y]); [|constructor; [exact HY0 | constructor]].
        intros X0 [<-|[]]. exact (keep_sound E' M' M2 _ scr csp wregs Wc Y HK HY0 K2 HagE' Y16 Y17 Y18 HFB HG2 HWc). }
      assert (G2' : know_ok segs E2 M2 [Y]).
      { apply (APS.know_ok_agree' segs nx E' E2 M2 [Y] Hag2); [cbn [APC.kn_vars_lt]; rewrite K3; reflexivity | exact G]. }
      inversion G2'; assumption.
  - (* [comment removed for export] *)
    split; [reflexivity|]. split; [eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]|]. split.
    + intros a Ha. rewrite (HFB a (HWF a Ha)). exact (Hfr a Ha).
    + eapply mem_grows_trans; [exact Hgr | exact HG2].
  - exact HFP2.
  - (* [comment removed for export] *)
    unfold CC.meas. rewrite Y12. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Y4) Y14). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag Y14). }
    rewrite Em. pose proof (proj1 (Forall_forall _ _) HK _ Y13) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag Y14) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma hwf_intro : forall csp scr (Wc : list L5.range), csp <= 0 -> 0 <= scr -> - SCR <= csp - scr -> In (EVar 2, - SCR, ELit SCR) F0 -> SCR < 2 ^ 64 ->
  (forall w, In w Wc -> exists rb rlo rlen, In (rb, rlo, rlen) F0 /\ estart E0 (SA rb rlo) <= fst w /\ fst w + snd w <= estart E0 (SA rb rlo) + elenZ E0 rlen) ->
  forall x : word, SGP.outside E0 F0 x -> L5.outside ((sp0 + csp - scr, scr) :: Wc) (bv_unsigned x).
Proof.
  intros csp scr Wc Hc Hs Hc2 Hst HS HW x Hout w [<-|Hin]; unfold L5.in_rng; cbn [fst snd].
  - unfold SGP.outside in Hout. rewrite Forall_forall in Hout. specialize (Hout _ Hst). cbv beta iota zeta in Hout.
    unfold estart, elenZ in Hout. cbn [a_base a_off edenot] in Hout. rewrite U2 in Hout. rewrite u64_of_Z in Hout by lia. lia.
  - destruct (HW w Hin) as (rb & rlo & rlen & Hr & H1 & H2). unfold SGP.outside in Hout. rewrite Forall_forall in Hout. specialize (Hout _ Hr). cbv beta iota zeta in Hout. lia.
Qed.
End PureCall.
End SPC.
