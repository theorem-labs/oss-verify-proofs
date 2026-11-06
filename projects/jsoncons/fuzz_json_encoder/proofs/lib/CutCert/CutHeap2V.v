(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CH2V.
Definition mem := (word -> option byte).

Section V.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000.
Hypothesis LY_errno : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Hypothesis LY_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a.

Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.                     (* [comment removed for export] *)
Variable model0 : Model.
Variable LBo : list (Z * Z).            (* [comment removed for export] *)
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable BLS : list CA.blocks.
(* [comment removed for export] *)
Variable G : Type.
Variable gB : G -> list (Z * Z).
Variable CredV : G -> nat -> env -> credit -> Prop.
Variable XIv : G -> nat -> env -> mem -> Prop.

Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + SCR <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBo sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M00 (sp0 - SCR) SCR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LBr (g : G) : list (Z * Z) := LBo ++ gB g.

Definition okV (M0c : mem) : Prop :=
  (forall a, L5C.kept L LBo sp0 SCR W a -> M0c (Z_to_bv 64 a) = M00 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> CH2.client0 L LBo sp0 a -> M00 (Z_to_bv 64 a) <> None -> M0c (Z_to_bv 64 a) <> None) /\
  L5.defined M0c (sp0 - SCR) SCR.

Definition heap_ambV (g : G) (M0c : mem) : nat -> env -> mem -> Model -> Prop :=
  CH2.heap_amb L HI NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g).
Definition amb3XV (g : G) (M0c : mem) : nat -> env -> mem -> Model -> Prop :=
  CH2.amb3 L HI NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g) (XIv g).
Definition amb3V (i : nat) (E : env) (M : mem) (model : Model) : Prop :=
  exists (g : G) (M0c : mem), okV M0c /\ amb3XV g M0c i E M model.

Lemma amb3V_intro : forall g M0c i E M model, okV M0c -> amb3XV g M0c i E M model -> amb3V i E M model.
Proof. intros g M0c i E M model H1 H2. exists g, M0c. split; assumption. Qed.

Lemma okV_refl : okV M00.
Proof. split; [intros; reflexivity|]. split; [intros a _ _ H; exact H | exact DEF0]. Qed.
Lemma okV_def0 : forall M0c, okV M0c -> L5.defined M0c (sp0 - SCR) SCR.
Proof. intros M0c (_ & _ & H). exact H. Qed.

Lemma incl_LBo : forall g, incl LBo (LBr g).
Proof. intros g. unfold LBr. apply incl_appl, incl_refl. Qed.
Lemma client_LBr : forall g sp scr a, client_addr L LBo sp scr a -> client_addr L (LBr g) sp scr a.
Proof.
  intros g sp scr a [(b & Hb & Hr)|[X|X]]; [left; exists b; split; [exact (incl_LBo g b Hb) | exact Hr] | right; left; exact X | right; right; exact X].
Qed.
Lemma kept_LBr : forall g sp scr Wx a, L5C.kept L LBo sp scr Wx a -> L5C.kept L (LBr g) sp scr Wx a.
Proof. intros g sp scr Wx a (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact (client_LBr g sp scr a H2)|]. split; assumption. Qed.

Lemma CRS_okV : forall g r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L (LBr g) sp0 a.
Proof.
  intros g r Hr. destruct (CRS_ok r Hr) as [H1 H2]. split; [exact H1|]. intros a Ha. destruct (H2 a Ha) as (X1 & [X|[X|(b & Hb & Hrb)]]).
  - split; [exact X1 | left; exact X].
  - split; [exact X1 | right; left; exact X].
  - split; [exact X1 | right; right; exists b; split; [exact (incl_LBo g b Hb) | exact Hrb]].
Qed.

Lemma amb3V_model : forall i E M model, amb3V i E M model -> m_halted model = None /\ m_vm_lazy model = [].
Proof.
  intros i E M model (g & M0c & _ & H).
  exact (CH2.amb3_model L HI NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g) (XIv g) i E M model H).
Qed.

Lemma ih_of : forall g M0c mu, okV M0c -> CC.IH (hl_segs L) CPS amb3V K FPI mu -> CC.IH (hl_segs L) CPS (amb3XV g M0c) K FPI mu.
Proof.
  intros g M0c mu OKV H j cj fx2 E2 R2 M2 model2 Hcj HAt HAmb HFP Hlt.
  exact (H j cj fx2 E2 R2 M2 model2 Hcj HAt (amb3V_intro g M0c j E2 M2 model2 OKV HAmb) HFP Hlt).
Qed.

Lemma frame00 : forall g M0c i E M model, okV M0c -> heap_ambV g M0c i E M model ->
  (forall a, L5C.kept L LBo sp0 SCR W a -> M (Z_to_bv 64 a) = M00 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> CH2.client0 L LBo sp0 a -> M00 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None).
Proof.
  intros g M0c i E M model (O1 & O2 & _) (_ & _ & _ & _ & Hfr & Hdf). split.
  - intros a Ha. rewrite (Hfr a (kept_LBr g _ _ _ a Ha)). exact (O1 a Ha).
  - intros a Ha Hc Hd. apply (Hdf a Ha); [|exact (O2 a Ha Hc Hd)]. destruct Hc as [Hc He]. split; [exact (client_LBr g _ _ a Hc) | exact He].
Qed.

Lemma hpres_rebase : forall g M0c M1, okV M0c ->
  L5C.hpres L (LBr g) sp0 SCR W M0c M1 -> L5C.hpres L LBo sp0 SCR W M00 M1.
Proof.
  intros g M0c M1 (O1 & O2 & _) (H1 & H2 & H3). split; [|split].
  - intros a Ha. rewrite (H1 a (kept_LBr g _ _ _ a Ha)). exact (O1 a Ha).
  - exact H2.
  - intros a Ha Hc He Hd. apply (H3 a Ha (client_LBr g _ _ a Hc) He). apply (O2 a Ha); [|exact Hd]. split; [|exact He].
    destruct Hc as [X|[(X1 & X2)|X]]; [left; exact X | right; left; split; [exact X1 | lia] | right; right; exact X].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amb_calleeV : forall g g' M0c (i j : nat) E E2 M1 M2 model model2 c scr LBk Wc cr',
  okV M0c -> heap_ambV g M0c i E M1 model ->
  L5C.hpres L LBk (sp0 + c) scr Wc M1 M2 -> incl LBo LBk -> c <= 0 -> 0 <= scr -> - SCR <= c - scr ->
  (forall w a, In w Wc -> L5.in_rng w a -> ~ L5C.kept L LBo sp0 SCR W a) ->
  model_but_vm model model2 ->
  hi_heap HI (CH2.cur (LBr g') BLS j E2) cr' M2 (m_vmmaps model2) ->
  env_agree NF E E2 -> CredV g' j E2 cr' ->
  okV M2 /\ heap_ambV g' M2 j E2 M2 model2.
Proof.
  intros g g' M0c i j E E2 M1 M2 model model2 c scr LBk Wc cr' OKV HA HP Hincl Hc Hs0 Hc2 HWc Hbv' HH' Hag2 HC.
  destruct (frame00 g M0c i E M1 model OKV HA) as (F1 & F2).
  destruct HA as (Hmo & Hbv & Hag & _ & _ & _).
  pose proof (CH2.sp0_range L NF sp0 d STK SCR_pos NF32) as SR0. pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  assert (CLI : forall a sp' scr', client_addr L LBo sp0 0 a -> ~ (sp' - scr' <= a < sp') -> client_addr L LBk sp' scr' a).
  { intros a sp' scr' [B|[[C1 C2]|C0]] Hn; [left; destruct B as (b & Hb & Hr); exists b; split; [exact (Hincl b Hb) | exact Hr] | right; left; split; [exact C1 | exact Hn] | right; right; exact C0]. }
  assert (DEF2 : forall a, 0 <= a < 2 ^ 64 -> CH2.client0 L LBo sp0 a -> M00 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
  { intros a Ha [HC0 HE] Hd. pose proof (F2 a Ha (conj HC0 HE) Hd) as HdM.
    destruct (Z_le_dec (sp0 + c - scr) a) as [G1|G1]; [destruct (Z_lt_dec a (sp0 + c)) as [G2|G2]|].
    - pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP (a - (sp0 + c - scr)) ltac:(lia)) as Y. replace (sp0 + c - scr + (a - (sp0 + c - scr))) with a in Y by lia. exact Y.
    - apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [|exact HE | exact HdM]. apply CLI; [exact HC0 | lia].
    - apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [|exact HE | exact HdM]. apply CLI; [exact HC0 | lia]. }
  split.
  - split; [|split; [exact DEF2|]].
    + intros a HK. rewrite <- (F1 a HK). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). destruct HK as (K1 & K2 & K3 & K4).
      split; [exact K1|]. split; [|split; [exact K3 | intros w Hw Hin; exact (HWc w a Hw Hin (conj K1 (conj K2 (conj K3 K4))))]].
      destruct K2 as [B|[[C1 C2]|C0]]; [left; destruct B as (b & Hb & Hr); exists b; split; [exact (Hincl b Hb) | exact Hr] | right; left; split; [exact C1 | lia] | right; right; exact C0].
    + intros k Hk. apply (DEF2 (sp0 - SCR + k)); [lia | | apply DEF0; exact Hk].
      split; [right; left; split; lia|]. unfold in_errno. destruct LY_img as (I0 & I1). destruct LY_errno as (E1 & E2'). lia.
  - split; [exact (CH2.model_ok_but_vm _ _ Hbv' Hmo)|]. split; [exact (L5C.model_but_vm_trans _ _ _ Hbv Hbv')|].
    split; [eapply CC.env_agree_trans; eassumption|]. split; [exists cr'; split; assumption|].
    split; [intros a _; reflexivity | intros a _ _ H; exact H].
Qed.

Lemma amb_callee_xV : forall g g' M0c scr ng c ps cj ci i j E E' R' M' model E2 M2 model2 LBk Wc cr',
  okV M0c ->
  CH2.common_facts_x L HI NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g) scr ng c ps cj ci i E E' R' M' model ->
  L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> incl LBo LBk ->
  (forall w a, In w Wc -> L5.in_rng w a -> ~ L5C.kept L LBo sp0 SCR W a) ->
  model_but_vm model model2 -> hi_heap HI (CH2.cur (LBr g') BLS j E2) cr' M2 (m_vmmaps model2) ->
  env_agree (CH2.ci_nx ci) E' E2 -> CredV g' j E2 cr' ->
  okV M2 /\ heap_ambV g' M2 j E2 M2 model2.
Proof.
  intros g g' M0c scr ng c ps cj ci i j E E' R' M' model E2 M2 model2 LBk Wc cr' OKV CF HP Hincl HWc Hbv2 HH2 Hag2 HC.
  destruct CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  pose proof HA' as (_ & _ & HagE & _).
  apply (amb_calleeV g g' M0c i j E E2 M' M2 model model2 (CH2.ci_csp ci) scr LBk Wc cr' OKV HA' HP Hincl Hc1 Hs0 Hc2 HWc Hbv2 HH2); [|exact HC].
  apply (CC.env_agree_trans NF E E0 E2); [apply CC.env_agree_sym; exact HagE|].
  apply (CC.env_agree_trans NF E0 E' E2); [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2 | lia].
Qed.

(* [comment removed for export] *)
Lemma custom_retV : forall g M0c scr ng BLk wregs news a0x i c ps j cj ci,
  okV M0c ->
  nth_error CPS j = Some cj -> CH2.custom_chk NF d scr ng BLk wregs news a0x c ps cj (nth i BLS []) = Some ci ->
  forall E R M model E' R' M',
    CC.At (hl_segs L) c E R M -> heap_ambV g M0c i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
    CC.IH (hl_segs L) CPS amb3V K FPI (CC.meas c E) ->
    CH2.common_facts_x L HI NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g) scr ng c ps cj ci i E E' R' M' model /\
    forall (fx2 : FPState) R2 M2 model2 ghosts LBk Wc,
      length ghosts = ng -> FPI fx2 ->
      (forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r) ->
      match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) e | None => True end ->
      L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> incl (CH2.den E' BLk ++ LBo) LBk ->
      (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CH2.in_reg E' r a) ->
      (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2 X) ->
      amb3V j (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2 model2 ->
      srealizes (hl_segs L) SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 (CC.cp_pc cj)) M2 (seg_rom (hl_segs L))) model2) K.
Proof.
  intros g M0c scr ng BLk wregs news a0x i c ps j cj ci OKV Hcj Hchk E R M model E' R' M' HAt HA Hag HLF HIH.
  unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d scr ng c ps cj (nth i BLS [])) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
  pose proof (CH2.common_sound_x L HI HIok LY_img LY_errno LY_ro NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g) STK SCR_pos NF32 SP0 TP0 W_ok WRS_ok (okV_def0 M0c OKV)
                scr ng i c ps cj ci0 E R M model E' R' M' Hc HAt HA Hag HLF) as CF.
  split; [exact CF|].
  destruct CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  apply andb_prop in Hb as [Hb Z4]. apply andb_prop in Hb as [Hb Z3]. apply andb_prop in Hb as [Z1 Z2]. apply CH2.regs_eqb_eq in Z1.
  intros fx2 R2 M2 model2 ghosts LBk Wc Hlen HFP2 Hkeep Ha0 HP Hincl HWc Hnews HA2.
  set (nx := CH2.ci_nx ci0) in *. set (E2 := CH2.retEx E' nx ghosts R2) in *.
  pose proof (CH2.retEx_agree E' nx ghosts R2 : env_agree nx E' E2) as Hag2.
  apply (HIH j cj fx2 E2 R2 M2 model2 Hcj); [| exact HA2 | exact HFP2 | apply Hmeas; exact Hag2].
  split.
  - assert (HR1 : regs_ok E2 (APC.sr_fresh (CH2.ci_regs ci0) APC.caller_saved (nx + ng)) R2).
    { unfold E2, CH2.retEx. rewrite Hlen. apply (CH2.ret_regs (APS.ext_list E' nx ghosts) _ (nx + ng) R' R2).
      - intros r. rewrite (HR r). apply (SR.edenot_agree_AP nx); [apply APS.ext_list_agree|].
        unfold sr_get. destruct (bv_eqb r 0); [reflexivity | apply CH.nth_vars_lt; exact V1].
      - eapply APS.sr_vars_lt_mono; [exact V1 | lia].
      - exact Hkeep. }
    rewrite Z1. destruct a0x as [e|]; [apply CH2.regs_ok_upd_same; [exact HR1 | exact Ha0] | exact HR1].
  - unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in Z4. specialize (Z4 Y HY).
    destruct (CC.has_cell news Y) eqn:Hn; [apply CC.has_cell_In in Hn; exact (Hnews Y Hn HY)|]. rename Z4 into Hk.
    unfold CH2.kept_chk in Hk. apply andb_prop in Hk as [Hk K3]. apply andb_prop in Hk as [K1 K2]. apply CC.has_cell_In in K1.
    pose proof (proj1 (Forall_forall _ _) HK _ K1) as HY0.
    destruct HA' as (_ & _ & _ & (cr & HH & _) & _ & _). unfold CH2.cur in HH. rewrite <- Hden in HH.
    assert (Hbr : CH2.blocks_in_range L (CH2.den E' BLk ++ LBo)).
    { intros b Hb0. apply (CH2.blocks_in_range_of L HI HIok _ _ _ _ _ HH). apply in_app_or in Hb0 as [Hb0|Hb0]; apply in_or_app;
        [left; exact (CH2.blk_in_den E' _ _ Z3 b Hb0) | right; exact (incl_LBo g b Hb0)]. }
    assert (GG : know_ok (hl_segs L) E' M2 [Y]).
    { apply (CH2.hpres_know L LY_img LY_errno NF E0 LBo sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok IMG_ok E' M' M2 BLk LBk (SR.ps_cells ps) scr (CH2.ci_csp ci0) Wc wregs [Y]
               HagE' Hbr Hincl Hc1 Hs0 Hc2 HWc HK);
        [constructor; [exact HY0 | constructor] | cbn [forallb]; rewrite K2; reflexivity | exact HP]. }
    assert (G2 : know_ok (hl_segs L) E2 M2 [Y]).
    { apply (APS.know_ok_agree' (hl_segs L) nx E' E2 M2 [Y] Hag2); [cbn [APC.kn_vars_lt]; rewrite K3; reflexivity | exact GG]. }
    inversion G2; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hi_heap_perm : forall LB LB' cr M VM, hi_heap HI LB cr M VM -> Permutation LB LB' -> hi_heap HI LB' cr M VM.
Proof.
  intros LB LB' cr M VM HH HP. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & Hnd & _).
  apply (hio_perm L SCFG HI HIok LB LB' cr M VM HH).
  - intros b. split; [apply (Permutation_in b HP) | apply (Permutation_in b (Permutation_sym HP))].
  - apply base.NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst HP)). apply base.NoDup_ListNoDup. exact Hnd.
Qed.
(* [comment removed for export] *)
Lemma perm_ghost_out : forall (own lo g1 g2 : list (Z * Z)) b, Permutation (own ++ lo ++ g1 ++ b :: g2) (b :: own ++ lo ++ g1 ++ g2).
Proof. intros own lo g1 g2 b. rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. Qed.
Lemma perm_ghost_in : forall (own lo g1 g2 : list (Z * Z)) b, Permutation (b :: own ++ lo ++ g1 ++ g2) (own ++ lo ++ g1 ++ b :: g2).
Proof. intros own lo g1 g2 b. apply Permutation_sym. apply perm_ghost_out. Qed.
Lemma hi_heap_ghost_out : forall own g1 g2 b cr M VM, hi_heap HI (own ++ LBo ++ g1 ++ b :: g2) cr M VM -> hi_heap HI (b :: own ++ LBo ++ g1 ++ g2) cr M VM.
Proof. intros own g1 g2 b cr M VM HH. exact (hi_heap_perm _ _ cr M VM HH (perm_ghost_out own LBo g1 g2 b)). Qed.
Lemma hi_heap_ghost_in : forall own g1 g2 b cr M VM, hi_heap HI (b :: own ++ LBo ++ g1 ++ g2) cr M VM -> hi_heap HI (own ++ LBo ++ g1 ++ b :: g2) cr M VM.
Proof. intros own g1 g2 b cr M VM HH. exact (hi_heap_perm _ _ cr M VM HH (perm_ghost_in own LBo g1 g2 b)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable TAGS : list (list CC.tag).

Definition leaf_okV (g : G) (M0c : mem) (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : Prop :=
  forall (fx' : FPState) E R M model E' R' M',
    CC.At (hl_segs L) c E R M -> amb3XV g M0c i E M model -> FPI fx' ->
    env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
    CC.IH (hl_segs L) CPS amb3V K FPI (CC.meas c E) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom (hl_segs L))) model) K.

Lemma leaf_okV_of : forall g M0c i c ps, okV M0c ->
  CC.leaf_ok (hl_segs L) CPS (amb3XV g M0c) K FPI i c ps -> leaf_okV g M0c i c ps.
Proof.
  intros g M0c i c ps OKV H fx' E R M model E' R' M' HAt HA HFP Hag HLF HIH.
  exact (H fx' E R M model E' R' M' HAt HA HFP Hag HLF (ih_of g M0c _ OKV HIH)).
Qed.

Theorem cert_sound3V :
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound (hl_segs L) c) ->
  CC.tags_chk CPS TAGS NF = true ->
  CH2.heap_chk3 NF d BLS CPS TAGS = true ->
  (forall g i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E E' R' M M' cr, env_agree NF E0 E ->
       env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> CredV g i E cr -> CredV g j (CC.env_over NF s E') cr) ->
  (forall g M0c, okV M0c -> forall i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E R E' R' M M' model,
       CC.At (hl_segs L) c E R M -> heap_ambV g M0c i E M model ->
       env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> XIv g i E M -> XIv g j (CC.env_over NF s E') M') ->
  (forall i c k ps pc, CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> forall g M0c, okV M0c -> leaf_okV g M0c i c ps) ->
  forall i c (fx : FPState) E R M model,
    nth_error CPS i = Some c -> CC.At (hl_segs L) c E R M -> amb3V i E M model -> FPI fx ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros FPM PLANS TCHK HCHK CG XG LEAVES.
  apply (CC.cutcert_sound_tagged (hl_segs L) CPS TAGS NF amb3V K FPI FPM PLANS TCHK amb3V_model).
  - intros i c tags k ps j s Hc Htg Hps Ht.
    assert (IL : CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s)) by (exists tags; repeat split; assumption).
    pose proof (CH2.leaves_all_sound CPS TAGS (CH2.leaf_chk3 NF d BLS) HCHK i c k ps _ IL) as X. cbn [CH2.leaf_chk3] in X.
    intros E R M model E' R' M' HAt (g & M0c & OKV & HA & HXI) Hag HLF.
    exists g, M0c. split; [exact OKV|]. split.
    + exact (CH2.goto_amb L HI HIok LY_img LY_errno LY_ro NF E0 M0c model0 (LBr g) sp0 d W BLS (CredV g) STK SCR_pos NF32 SP0 W_ok WRS_ok
               i c ps j s X (CG g i c k ps j s IL) E R M model E' R' M' HAt HA Hag HLF).
    + exact (XG g M0c OKV i c k ps j s IL E R E' R' M M' model HAt HA Hag HLF HXI).
  - intros i c tags k ps pc Hc Htg Hps Ht fx' E R M model E' R' M' HAt (g & M0c & OKV & HAX) HFP Hag HLF HIH.
    assert (IL : CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc)) by (exists tags; repeat split; assumption).
    exact (LEAVES i c k ps pc IL g M0c OKV fx' E R M model E' R' M' HAt HAX HFP Hag HLF HIH).
Qed.

End V.
End CH2V.
