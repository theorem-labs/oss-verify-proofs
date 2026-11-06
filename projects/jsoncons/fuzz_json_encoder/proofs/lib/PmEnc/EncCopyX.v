(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Module ECX.
Abbreviation mem := (word -> option byte).

Section CopyX.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000.
Hypothesis LY_errno : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Hypothesis LY_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a.
Hypothesis LY_stack : 0 <= hl_stack L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis HSTK_eq : hl_stack L = CH.hd_hstk d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.

Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).

Definition copyx_entry_ok (kn1 : list kentry) (db : expr) (dk : Z) (n : expr) (nx : nat) (X : kentry) : bool :=
  if (CC.has_cell kn1 X && APC.kentry_vars_lt nx X)%bool then true else APC.kentry_eqb X (KUnk (SA db dk) n).

(* [comment removed for export] *)
Definition copyx_chk (PC : Z) (SE NE : expr) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match CH2.common_chk NF d c ps cj BLi with
  | Some ci =>
      let cells := SR.ps_cells ps in let regs := CH2.ci_regs ci in let nx := CH2.ci_nx ci in
      let dst := nth 10 regs (ELit 0) in let src := nth 11 regs (ELit 0) in let n := nth 12 regs (ELit 0) in
      let '(db, dk) := split_lit dst in
      let kn1 := APC.kn_havoc cells db dk n in
      (Z.eqb (SR.ps_pc ps) PC
       && CA.regs_eqb (CC.cp_regs cj) (sr_upd (APC.sr_fresh regs APC.caller_saved nx) 10 dst)
       && CH2.blocks_eqb BLj BLi && CH2.blocks_vars_lt nx BLi
       && CH.within cells (CH.foot_regs d BLi) db dk n
       && existsb (fun X => match X with KWr (SA b k) m => xinside cells db dk n b k m | _ => false end) cells
       && expr_eqb src SE && expr_eqb n NE && APC.expr_vars_lt NF SE && APC.expr_vars_lt NF NE
       && APC.fact_ok cells (KRange dst 0 4611686018427387904)
       && forallb (copyx_entry_ok kn1 db dk n nx) (CC.cp_know cj))%bool
  | None => false
  end.

Lemma copyx_leaf_ok : forall i c ps j cj PC SE NE (S n : Z),
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> FPI fx -> FPI fx') ->
  CH2.copy1_spec L PC -> nth_error CPS j = Some cj ->
  copyx_chk PC SE NE c ps cj (nth i BLS []) (nth j BLS []) = true ->
  bv_unsigned (edenot E0 SE) = S -> bv_unsigned (edenot E0 NE) = n -> 1 <= n -> S + n <= 2 ^ 62 ->
  (forall a, S <= a < S + n -> L5C.kept L LBrest sp0 (CH.hd_scr d) W a) ->
  (exists bs, rdn (hl_segs L) M0 (Z_to_bv 64 S) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n) ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
       forall E2, env_agree (CC.cp_nx cj - APC.NCS) E' E2 -> Cred j E2 cr) ->
  CC.leaf_ok (hl_segs L) CPS HAMB K FPI i c ps.
Proof.
  intros i c ps j cj PC SE NE S n FPM0 HSPEC Hcj Hchk HS0 HN0 Hn1 HSn HKEPT (bs & Hrd0 & Hlen) HCred fx' E R M model E' R' M' HAt HA HFP Hag HLF HIH.
  unfold copyx_chk in Hchk. destruct (CH2.common_chk NF d c ps cj (nth i BLS [])) as [ci|] eqn:Hc; [|discriminate].
  destruct (CH2.common_sound L HI HIok LY_img LY_errno LY_ro LY_stack NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos HSTK_eq NF32 SP0 TP0 W_ok WRS_ok
              i c ps cj ci E R M model E' R' M' Hc HAt HA Hag HLF)
    as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := CH2.ci_nx ci) in *. set (dste := nth 10 (CH2.ci_regs ci) (ELit 0)) in *. set (srce := nth 11 (CH2.ci_regs ci) (ELit 0)) in *.
  set (ne := nth 12 (CH2.ci_regs ci) (ELit 0)) in *.
  destruct (split_lit dste) as [db dk] eqn:Hsd.
  repeat (apply andb_prop in Hchk as [Hchk ?X]). apply Z.eqb_eq in Hchk. apply CH2.regs_eqb_eq in X9. apply CH2.blocks_eqb_eq in X8.
  apply expr_eqb_eq in X4, X3.
  pose proof (APS.fact_ok_sound (hl_segs L) E' M' _ _ HK X0) as Fd. cbn [kentry_ok] in Fd.
  assert (ESE : bv_unsigned (edenot E' srce) = S) by (rewrite X4, <- HS0; f_equal; symmetry; exact (SR.edenot_agree_AP NF E0 E' SE HagE' X2)).
  assert (ENE : bv_unsigned (edenot E' ne) = n) by (rewrite X3, <- HN0; f_equal; symmetry; exact (SR.edenot_agree_AP NF E0 E' NE HagE' X1)).
  set (D := bv_unsigned (edenot E' dste)) in *.
  assert (Hva : APC.expr_vars_lt nx dste = true /\ APC.expr_vars_lt nx ne = true) by (split; apply CH.nth_vars_lt; exact V1).
  assert (G10 : getr R' 10%bv = edenot E' dste).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. reflexivity. }
  assert (G11 : getr R' 11%bv = Z_to_bv 64 S).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. fold srce. rewrite <- ESE. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (G12 : getr R' 12%bv = Z_to_bv 64 n).
  { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. fold ne. rewrite <- ENE. symmetry. apply Z_to_bv_bv_unsigned. }
  (* [comment removed for export] *)
  apply existsb_exists in X5 as (YW & HYW & HxW). destruct YW as [| | | | | |[wb wk] wm| | |]; try discriminate.
  pose proof (proj1 (Forall_forall _ _) HK _ HYW) as HW. cbn [kentry_ok] in HW. destruct HW as [(W1 & W2 & W3 & W4) HW].
  destruct (xinside_sound (hl_segs L) E' M' _ _ _ _ _ _ _ HK HxW) as [IW1 IW2]. change (elenZ E' ne) with (bv_unsigned (edenot E' ne)) in IW2. rewrite ENE in IW2.
  assert (ED : estart E' (SA db dk) = D) by (symmetry; apply (CH2.split_start E' dste db dk Hsd); lia).
  rewrite ED in *.
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  (* [comment removed for export] *)
  assert (HFOOT : forall a, D <= a < D + n -> CH2.foot_sem sp0 d W (CH2.den E' (nth i BLS [])) a).
  { intros a Ha. destruct (CH2.within_sem L NF sp0 d STK SCR_pos NF32 E' M' _ _ db dk ne HK X6) as (r & Hr & Hs).
    apply (CH2.foot_regs_sem L NF E0 sp0 d W STK SCR_pos NF32 SP0 WRS_ok E' _ r _ HagE' Hr). apply Hs. rewrite ED. change (elenZ E' ne) with (bv_unsigned (edenot E' ne)). rewrite ENE. exact Ha. }
  assert (HHc : hi_heap HI (CH2.den E' (nth i BLS []) ++ LBrest) cr M' (m_vmmaps model)).
  { unfold CH2.cur in HH. rewrite Hden. exact HH. }
  assert (Hdisj : D + n <= S \/ S + n <= D).
  { destruct (Z_le_dec (D + n) S) as [G|G]; [left; exact G|]. destruct (Z_le_dec (S + n) D) as [G'|G']; [right; exact G'|]. exfalso.
    destruct (Z_le_dec D S) as [G2|G2].
    - apply (CH2.foot_not_kept L HI HIok LY_img LY_errno NF LBrest sp0 d W STK SCR_pos NF32 _ cr M' _ S HHc (HFOOT S ltac:(lia)) (HKEPT S ltac:(lia))).
    - apply (CH2.foot_not_kept L HI HIok LY_img LY_errno NF LBrest sp0 d W STK SCR_pos NF32 _ cr M' _ D HHc (HFOOT D ltac:(lia)) (HKEPT D ltac:(lia))). }
  assert (Hrd : rdn (hl_segs L) M' (Z_to_bv 64 S) (Z.to_nat n) = Some bs).
  { rewrite <- Hrd0. apply (L5C.rdn_agree (hl_segs L) M0 M' (Z.to_nat n) S).
    - destruct (HKEPT S ltac:(lia)) as (Hs0 & _). lia.
    - rewrite Z2Nat.id by lia. lia.
    - intros a Ha. rewrite Z2Nat.id in Ha by lia. apply Hfr. apply HKEPT. exact Ha. }
  assert (S0 : 0 <= S) by (destruct (HKEPT S ltac:(lia)) as (Hs0 & _); lia).
  pose proof (HCred E E' R' M M' cr HagE Hag HLF HC) as HC2.
  assert (Dw : Z_to_bv 64 D = getr R' 10%bv) by (rewrite G10; unfold D; apply Z_to_bv_bv_unsigned).
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply u64_of_Z; destruct (HKEPT S ltac:(lia)) as (Hs0 & _); lia).
  destruct (HSPEC fx' M' (getr R' 10%bv) (getr R' 11%bv) n bs R' (getr R' 1%bv)) as (fx2 & R2 & Hms & Hkept & Ha0); try reflexivity.
  { lia. } { rewrite G10. fold D. lia. } { rewrite G11, US. lia. } { exact Hlen. } { rewrite Hlen, G11. exact Hrd. }
  { rewrite Hlen, <- Dw. replace D with (estart E' (SA wb wk) + (D - estart E' (SA wb wk))) by lia. apply HW; lia. }
  { rewrite G10, G11, US. fold D. lia. } { rewrite G11, US. lia. } { rewrite G10. fold D. lia. } { exact Hret. } { exact G12. }
  rewrite Hchk. eapply L5.cps_of_msteps; [exact (proj1 Hmo) | exact (proj1 (proj2 Hmo)) | exact Hms |]. rewrite Hra.
  set (M2 := wbytes M' (getr R' 10%bv) bs) in *.
  assert (UD : bv_unsigned (getr R' 10%bv) = D) by (rewrite G10; reflexivity).
  assert (Hlz : Z.of_nat (length bs) = n) by (rewrite Hlen; lia).
  assert (Hout : forall x : word, bv_unsigned x < D \/ D + n <= bv_unsigned x -> M2 x = M' x).
  { intros x [Hx|Hx]; unfold M2; [apply wbytes_below; rewrite ?UD, ?Hlz; lia | apply wbytes_above; rewrite UD, Hlz; lia]. }
  assert (Hin2 : forall k, 0 <= k < n -> M2 (Z_to_bv 64 (D + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0))).
  { intros k Hk. unfold M2. replace (D + k) with (bv_unsigned (getr R' 10%bv) + Z.of_nat (Z.to_nat k)) by (rewrite UD; lia).
    apply wbytes_nth; [rewrite UD, Hlz; lia | lia]. }
  set (E2 := CH2.retE E' nx R2). pose proof (CH2.retE_agree E' nx R2 : env_agree nx E' E2) as Hag2.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  assert (Hkn1 : know_ok (hl_segs L) E' M2 (APC.kn_havoc (SR.ps_cells ps) db dk ne)).
  { apply (APS.know_ok_havoc (hl_segs L) E' M' M2 _ _ _ _ HK); [| unfold M2; apply wbytes_grows]. intros x Hx. apply Hout. rewrite ED in Hx.
    change (elenZ E' ne) with (bv_unsigned (edenot E' ne)) in Hx. rewrite ENE in Hx. exact Hx. }
  assert (UNK2 : kentry_ok (hl_segs L) E' M2 (KUnk (SA db dk) ne)).
  { cbn [kentry_ok]. rewrite ED. change (elenZ E' ne) with (bv_unsigned (edenot E' ne)). rewrite ENE. split; [unfold flat; rewrite ED; lia|]. intros k Hk. rewrite (Hin2 k Hk). discriminate. }
  assert (TR : forall Y, APC.kentry_vars_lt nx Y = true -> kentry_ok (hl_segs L) E' M2 Y -> kentry_ok (hl_segs L) E2 M2 Y).
  { intros Y Hv HY. assert (G : know_ok (hl_segs L) E2 M2 [Y]).
    { apply (APS.know_ok_agree' (hl_segs L) nx E' E2 M2 [Y] Hag2); [cbn [APC.kn_vars_lt]; rewrite Hv; reflexivity | constructor; [exact HY | constructor]]. }
    inversion G; assumption. }
  assert (Vd : APC.expr_vars_lt nx db = true) by exact (CH2.split_lit_vars nx dste db dk Hsd (proj1 Hva)).
  apply (HIH j cj fx2 E2 R2 M2 model Hcj).
  - split.
    + rewrite X9. apply CH2.regs_ok_upd_same; [apply (CH2.ret_regs E' _ nx R' R2 HR V1); intros r Hr Hn; exact (Hkept r Hr Hn)|].
      rewrite Ha0, G10. exact (SR.edenot_agree_AP nx E' E2 dste Hag2 (proj1 Hva)).
    + unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in X. specialize (X Y HY). unfold copyx_entry_ok in X.
      lazymatch type of X with (if ?b then _ else _) = _ => destruct b eqn:C1 end.
      { apply andb_prop in C1 as [C1 C2]. apply CC.has_cell_In in C1. exact (TR Y C2 (proj1 (Forall_forall _ _) Hkn1 _ C1)). }
      apply APS.kentry_eqb_eq in X. subst Y. apply TR; [|exact UNK2]. unfold APC.kentry_vars_lt, APC.saddr_vars_lt. cbn [a_base]. rewrite Vd, (proj2 Hva). reflexivity.
  - apply (CH2.amb_pure_step L HI HIok LY_img LY_errno LY_ro NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 W_ok i j E E2 M' M2 model
             (conj Hmo (conj Hbv (conj HagE (conj (ex_intro _ cr (conj HH HC)) (conj Hfr Hdf)))))).
    + intros a Hn. apply Hout. destruct (Z_lt_dec (bv_unsigned a) D) as [G1|G1]; [left; exact G1|].
      destruct (Z_le_dec (D + n) (bv_unsigned a)) as [G2|G2]; [right; exact G2|]. exfalso. apply Hn.
      rewrite <- Hden. apply HFOOT. lia.
    + unfold M2. apply wbytes_grows.
    + eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4] | eapply CC.env_agree_le; [exact Hag2 | lia]].
    + rewrite X8. rewrite (CH2.den_agree nx E' E2 _ Hag2 X7). exact Hden.
    + intros cr' HC'. apply (HCred E E' R' M M' cr' HagE Hag HLF HC'). replace (CC.cp_nx cj - APC.NCS)%nat with nx by lia. exact Hag2.
  - rewrite Hra in Hms. exact (FPM0 _ _ _ _ _ _ _ _ Hms HFP).
  - apply Hmeas. exact Hag2.
Qed.
End CopyX.
End ECX.
