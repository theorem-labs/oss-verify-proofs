(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff FxLazy FxCellFrame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrKset.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import CXI.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv BrMem BrPart BrRev BrRevLedger BrClass BrRevS BrDress BrGrow BrRa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mat_lazy (m : Model) : Prop :=
  forall p, In p (m_vm_materialized m) -> page_in_ranges p (m_vm_lazy m) = true.

Lemma materialize_mat_lazy m l m' :
  materialize_model_accesses m l = Some m' -> mat_lazy m -> mat_lazy m'.
Proof.
  unfold materialize_model_accesses, materialize_accesses. intros Hm Hl.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) l) in *.
  assert (Hnew : forall p, In p new -> page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply List.filter_In in Hp as [_ Hb].
    apply andb_prop in Hb as [Hb _]. exact Hb. }
  destruct new as [|q qs] eqn:En.
  - injection Hm as <-. intros p Hp. exact (Hl p Hp).
  - destruct (vm_backing_used m + Z.of_nat (length (q :: qs)) * page_size <=? vm_limit (m_vmmaps m)); [|discriminate].
    injection Hm as <-. intros p Hp.
    change (In p ((q :: qs) ++ m_vm_materialized m)) in Hp.
    change (page_in_ranges p (m_vm_lazy m) = true).
    apply in_app_or in Hp as [Hp|Hp]; [exact (Hnew p Hp) | exact (Hl p Hp)].
Qed.

Section Run.
Variable segs : list Segment.

Lemma account_step_mat_lazy ms m ms' m' :
  mi_account_step segs ms m = MachineOk (ms', m') -> mat_lazy m -> mat_lazy m'.
Proof.
  unfold mi_account_step. intros Hs Hl.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; try discriminate.
  destruct (materialize_model_accesses m (accessed_ranges _ report)) as [m1|] eqn:Hm; [|discriminate].
  injection Hs as _ <-. exact (materialize_mat_lazy m _ m1 Hm Hl).
Qed.

Lemma asteps_mat_lazy : forall k ms m ms' m',
  asteps segs k (ms, m) = MachineOk (ms', m') -> mat_lazy m -> mat_lazy m'.
Proof.
  induction k as [|k IH]; intros ms m ms' m' Ha Hl; cbn [asteps fst snd] in Ha.
  - injection Ha as _ <-. exact Hl.
  - destruct (ms_svc_pending ms); [injection Ha as _ <-; exact Hl|].
    destruct (mi_account_step segs ms m) as [[ms1 m1]| |] eqn:Hs; try discriminate.
    exact (IH ms1 m1 ms' m' Ha (account_step_mat_lazy ms m ms1 m1 Hs Hl)).
Qed.

(* [comment removed for export] *)
Lemma A_bytes_wf A : AsanAcct.A_wf A -> LazyCfg.A_bytes A = AsanAcct.A_bytes A.
Proof.
  induction A as [|iv A IH]; intros Hwf; [reflexivity|].
  pose proof (Forall_inv Hwf) as (Hle & _). pose proof (Forall_inv_tail Hwf) as Hr.
  unfold LazyCfg.A_bytes in *. cbn [fold_right AsanAcct.A_bytes]. rewrite (IH Hr). lia.
Qed.

Lemma page_inv_of_MInv A m : AsanAcct.A_wf A -> AsanAcct.MInv A m -> LazyCfg.page_inv A m.
Proof.
  intros Hwf [Hnd Hal Hall _ Hb]. constructor.
  - exact Hnd.
  - apply Forall_forall. intros p Hp. exact (Hal p Hp).
  - apply Forall_forall. intros p Hp. exact (Hall p Hp).
  - rewrite (A_bytes_wf A Hwf). exact Hb.
Qed.

Lemma MInv_of_page_inv A m : AsanAcct.A_wf A -> LazyCfg.page_inv A m -> mat_lazy m -> AsanAcct.MInv A m.
Proof.
  intros Hwf [Hnd Hal Hall Hb] Hl. rewrite Forall_forall in Hal, Hall. constructor.
  - exact Hnd.
  - intros p Hp. exact (Hal p Hp).
  - intros p Hp. exact (Hall p Hp).
  - exact Hl.
  - rewrite <- (A_bytes_wf A Hwf). exact Hb.
Qed.

(* [comment removed for export] *)
Theorem rzc_rsteps_minv cfg A k ms ms' m T :
  AsanAcct.A_wf A ->
  m_halted m = None ->
  rsteps segs k ms = MachineOk ms' ->
  AsanAcct.MInv A m ->
  (forall j msj, (j < k)%nat -> rsteps segs j ms = MachineOk msj -> touch_ok segs (m_vm_lazy m) A msj) ->
  (forall m', lazy_frame m m' -> AsanAcct.MInv A m' -> realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros Hwf Hh Hr Hinv Htouch HT.
  destruct (asteps_pages segs A k ms ms' m Hr (page_inv_of_MInv A m Hwf Hinv) Htouch) as (m' & Ha & Hf & Hi).
  apply (rzc_asteps cfg segs k ms m ms' m' T Hh Ha). apply (HT m' Hf).
  apply (MInv_of_page_inv A m' Hwf Hi). apply (asteps_mat_lazy k ms m ms' m' Ha).
  intros p Hp. exact (AsanAcct.minv_lazy A m Hinv p Hp).
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Transform.
Variable segs : list Segment.
Variable A : APC.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Lemma hid_with_ss E CS ss m m' :
  lazy_frame m m' -> APS.hid A argH E (APC.with_ss CS ss) m' = APS.hid A argH E CS m.
Proof. intros [mat' ->]. reflexivity. Qed.

Theorem cs_ok_transform E CS R FULL m pc' regs' kn' nxt' R' FULL' m' :
  CXI.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  let CS' := APC.with_ss CS (APC.mk_ss pc' regs' kn' nxt') in
  AX2S.regs_ok E regs' R' ->
  AX2S.know_ok segs E (mrestrict (APS.hid A argH E CS m) FULL') kn' ->
  lazy_frame m m' ->
  AsanAcct.MInv (APS.allowA A E CS) m' ->
  (forall a, APS.hid A argH E CS m a = true -> FULL' a = FULL a) ->
  CXI.cs_ok segs A Lim SINV argH ISP FS0 E CS' R' FULL' m'.
Proof.
  intros HC CS' Hregs Hkn Hf Hminv Hhid.
  pose proof (hid_with_ss E CS (APC.mk_ss pc' regs' kn' nxt') m m' Hf) as Ehid.
  destruct Hf as [mat' ->]. subst CS'.
  destruct HC as [HC Hvisp]. split; [|exact Hvisp].
  destruct HC. constructor; try assumption; try reflexivity.
  - (* [comment removed for export] *) intros a Ha H1 H2 H3 H4. rewrite (Hhid a Ha).
    exact (co_zero a Ha H1 H2 H3 H4).
  - (* [comment removed for export] *) apply (SINV_frame E FULL FULL'); [|exact co_sinv].
    intros a Ha. apply Hhid. unfold APS.hid. rewrite Ha. reflexivity.
Qed.

End Transform.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KExt.
Variable segs : list Segment.
Variable E : AX2.env.
Variables base base' : word -> option byte.

Lemma rdn_ext : forall n a,
  (forall j, (j < n)%nat -> base' (aoff a j) = base (aoff a j)) ->
  PropExec.rdn segs base' a n = PropExec.rdn segs base a n.
Proof.
  induction n as [|n IH]; intros a Hb; [reflexivity|]. cbn [PropExec.rdn].
  rewrite (IH (a + 1)%bv) by (intros j Hj; rewrite !aoff_S; apply Hb; lia).
  pose proof (Hb 0%nat ltac:(lia)) as H0. rewrite aoff_0 in H0. rewrite H0. reflexivity.
Qed.

Lemma store_ok_ext : forall n a,
  (forall j, (j < n)%nat -> base' (aoff a j) = base (aoff a j)) ->
  RiscvSemantics.store_ok segs base' a n = RiscvSemantics.store_ok segs base a n.
Proof.
  induction n as [|n IH]; intros a Hb; [reflexivity|]. cbn [RiscvSemantics.store_ok].
  rewrite (IH (a + 1)%bv) by (intros j Hj; rewrite !aoff_S; apply Hb; lia).
  pose proof (Hb 0%nat ltac:(lia)) as H0. rewrite aoff_0 in H0.
  unfold wview. rewrite H0. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kentry_bytes (K : AX2.kentry) (x : Z) : Prop :=
  match K with
  | AX2.KWord a w _ => AX2S.estart E a <= x < AX2S.estart E a + Z.of_nat w
  | AX2.KZero a n | AX2.KBlob a n _ | AX2.KFill a n _ | AX2.KUnk a n | AX2.KWr a n =>
      AX2S.estart E a <= x < AX2S.estart E a + AX2S.elenZ E n
  | AX2.KImg lo hi => lo <= x < hi
  | _ => False
  end.

Lemma aoff_lit z j : 0 <= z -> z + Z.of_nat j < 2 ^ 64 -> aoff (Z_to_bv 64 z) j = Z_to_bv 64 (z + Z.of_nat j).
Proof.
  intros Hz Hj. unfold aoff. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small z) by lia.
  rewrite (Z.mod_small (Z.of_nat j)) by lia. reflexivity.
Qed.

Theorem kentry_ok_ext K :
  (forall x, kentry_bytes K x -> base' (Z_to_bv 64 x) = base (Z_to_bv 64 x)) ->
  AX2S.kentry_ok segs E base K -> AX2S.kentry_ok segs E base' K.
Proof.
  intros Hb HK.
  destruct K as [a w v | a n | a n j | lo hi | e m0 | e lo hi | a n | a1 n1 a2 n2 | a n c | a n];
    cbn [AX2S.kentry_ok kentry_bytes] in *; try exact HK.
  - (* [comment removed for export] *) destruct HK as (Hw & Hflat & Hr). split; [exact Hw|]. split; [exact Hflat|].
    rewrite <- Hr. apply rdn_ext. intros j Hj.
    assert (Ea : AX2.adenot E a = Z_to_bv 64 (AX2S.estart E a)).
    { apply bv_eq. rewrite (AX2S.flat_u _ _ _ Hflat). destruct Hflat as (F1 & F2 & _).
      rewrite Z_to_bv_small by (unfold bv_modulus; lia). reflexivity. }
    destruct Hflat as (F1 & F2 & F3 & F4).
    rewrite Ea, aoff_lit by lia. apply Hb. lia.
  - (* [comment removed for export] *) destruct HK as (Hflat & Hz). split; [exact Hflat|]. intros i Hi. rewrite Hb by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as (Hflat & Hl & Hz). split; [exact Hflat|]. split; [exact Hl|].
    intros i Hi. rewrite Hb by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as (H0 & H1 & Hz). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite Hb by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as (Hflat & Hs). split; [exact Hflat|]. intros d m Hd Hm.
    rewrite <- (Hs d m Hd Hm). apply store_ok_ext. intros j Hj.
    destruct Hflat as (F1 & F2 & F3 & F4).
    rewrite aoff_lit by lia. apply Hb. lia.
  - (* [comment removed for export] *) destruct HK as (Hflat & Hz). split; [exact Hflat|]. intros i Hi. rewrite Hb by lia. exact (Hz i Hi).
  - (* [comment removed for export] *) destruct HK as (Hflat & Hz). split; [exact Hflat|]. intros i Hi. rewrite Hb by lia. exact (Hz i Hi).
Qed.

End KExt.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint forallbL {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => true | a :: r => if f a then forallbL f r else false end.
Lemma forallbL_eq {T : Type} (f : T -> bool) (l : list T) : forallbL f l = forallb f l.
Proof. induction l as [|a r IH]; cbn [forallbL forallb]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FrameSafe.
Variable segs : list Segment.
Variable IM : fimage.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn : list AX2.kentry.
Variable base : word -> option byte.
Variable d : sdesc.
Variable mem0 : word -> option byte.
Hypothesis HTT : tt_wf TT = true.
Hypothesis Hkn : AX2S.know_ok segs E base kn.
(* [comment removed for export] *)
Variable ra : ra_t.
Hypothesis Era : ra = AX2.ranges_apart kn.

Local Notation rho := (rho_of TT E).
(* [comment removed for export] *)
Variable XTv : list (int * AX2.lin).
Hypothesis EXT : XTv = xt_of TT.
Variable M0 : itrie region.
Hypothesis EM0 : M0 = f_mem (state_of d).
Local Notation XT := XTv.
Hypothesis Hmem : mem_ok segs IM rho M0 mem0.

Lemma HXTv_fs : xt_ok rho (AX2.ev E) (AX2.eb E) [] XTv.
Proof. rewrite EXT. exact (xt_of_ok TT E HTT). Qed.

Fixpoint pages_nowr (rg : region) (t pn : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match page_at IM rg t pn with Some p => negb (pg_wr p) | None => true end
            && pages_nowr rg t (pn + 1)%uint63 k'
  end.

Lemma pages_nowr_spec rg t : forall k pn,
  to_Z pn + Z.of_nat k <= 2 ^ 50 ->
  pages_nowr rg t pn k = true ->
  forall q p, to_Z pn <= q < to_Z pn + Z.of_nat k -> page_at IM rg t (of_Z q) = Some p -> pg_wr p = false.
Proof.
  induction k as [|k IH]; intros pn Hb Hw q p Hq Hp; [lia|].
  cbn [pages_nowr] in Hw. apply andb_prop in Hw as [Hp0 Hrest].
  pose proof (i63_range pn) as Hpn.
  destruct (Z.eq_dec q (to_Z pn)) as [->|Hne].
  - rewrite of_to_Z in Hp. rewrite Hp in Hp0. apply negb_true_iff in Hp0. exact Hp0.
  - assert (E1 : to_Z (pn + 1)%uint63 = to_Z pn + 1).
    { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
    apply (IH (pn + 1)%uint63 ltac:(lia) Hrest q p); [lia | exact Hp].
Qed.

(* [comment removed for export] *)
Definition sparse_rg (rg : region) (t : int) : bool :=
  negb (t =? 0)%uint63 && match rg_dflt rg with None => true | Some _ => false end.
Definition nowr_sparse (rg : region) (p0 p1 : Z) : bool :=
  forallb (fun pp => negb ((p0 <=? to_Z (fst pp)) && (to_Z (fst pp) <=? p1)) || negb (pg_wr (snd pp)))
          (ielements (rg_pages rg)).
Definition nowr_chk (rg : region) (t : int) (p0 p1 : Z) : bool :=
  if sparse_rg rg t then nowr_sparse rg p0 p1
  else if (p1 - p0 + 1 <=? 4194304) then pages_nowr rg t (of_Z p0) (Z.to_nat (p1 - p0 + 1)) else false.

(* [comment removed for export] *)
Definition view_dec (a : AX2.saddr) (n : Z) : option bool :=
  match aview [] M0 [] XT a with
  | Some (t, o) =>
      match iget t M0 with
      | Some rg => if (0 <=? o) && (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg)) && (o + n <? 2 ^ 62)
                   then Some (nowr_chk rg t (o / 4096) ((o + n - 1) / 4096)) else None
      | None => None
      end
  | None => None
  end.
Definition view_chk (a : AX2.saddr) (n : Z) : bool := match view_dec a n with Some b => b | None => false end.

(* [comment removed for export] *)
Definition has_claims (r : rdesc) : bool :=
  (rd_tag r =? 0)%uint63 || match rd_dflt r with Some _ => true | None => false end
  || match rd_pages r with [] => false | _ => true end.

Definition apart_chk (a : AX2.saddr) (n : Z) : bool :=
  forallbL (fun r => if has_claims r
                    then ra (AX2.a_base a) (AX2.a_off a) n
                           (tte TT (rd_tag r)) (to_Z (rd_lo r)) (to_Z (rd_len r) - to_Z (rd_lo r))
                    else true) (sd_mem d).

(* [comment removed for export] *)
Definition frame_chk (a : AX2.saddr) (n : Z) : bool :=
  (0 <? n) && match view_dec a n with Some b => b | None => apart_chk a n end.

Lemma HM0 : forall t rg, iget t M0 = Some rg -> region_ok rho t rg.
Proof. intros t rg Hg. exact (proj1 (proj1 Hmem t rg Hg)). Qed.

Lemma lit_adr t z : Z_to_bv 64 (bv_unsigned (rho t) + z) = adr rho t z.
Proof.
  unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Theorem frame_chk_sound a n n' :
  frame_chk a n = true -> AX2S.flat E a n' -> n' <= n ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + n' -> ~ claimed_wr IM rho M0 (Z_to_bv 64 x).
Proof.
  unfold frame_chk. intros Hc Hflat Hn x Hx (t' & rg' & pn & p & j & Hg' & Hpn & Hp & Hwr & Hj & Hhi' & Ex).
  apply andb_prop in Hc as [Hn0 Hc]. apply Z.ltb_lt in Hn0.
  destruct Hflat as (F1 & F2 & F3 & F4).
  destruct (proj1 Hmem t' rg' Hg') as [Hrok' Hpages']. destruct (Hpages' pn p Hpn Hp) as (_ & Hlo' & _ & _).
  destruct Hrok' as (_ & _ & Hb63' & _).
  pose proof (br_u64 (rho t')) as Hu'. pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rg_lo rg')) as Hl0'.
  assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply br_lit_small; lia).
  assert (Ux' : bv_unsigned (adr rho t' (to_Z pn * 4096 + j)) = bv_unsigned (rho t') + (to_Z pn * 4096 + j))
    by (apply adr_unsigned; lia).
  assert (Exz : x = bv_unsigned (rho t') + (to_Z pn * 4096 + j)) by (rewrite <- Ux, Ex; exact Ux').
  destruct (view_dec a n) as [bdec|] eqn:Hv.
  - subst bdec. unfold view_dec in Hv. destruct (aview [] M0 [] XT a) as [[t o]|] eqn:Hav; [|discriminate].
    destruct (iget t M0) as [rg|] eqn:Hg; [|discriminate].
    destruct ((0 <=? o) && (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg)) && (o + n <? 2 ^ 62)) eqn:Hbd; [|discriminate].
    injection Hv as Hnw. apply andb_prop in Hbd as [Hbd H62]. apply andb_prop in Hbd as [Hbd Hlen].
    apply andb_prop in Hbd as [Ho0 Hlo]. apply Z.leb_le in Ho0, Hlo, Hlen. apply Z.ltb_lt in H62.
    pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M0 [] XT HM0 (rho_of_0 TT E) eq_refl HXTv_fs a t o Hav) as Hs.
    rewrite env_eta in Hs.
    destruct (HM0 t rg Hg) as (_ & _ & Hb63 & _). pose proof (br_u64 (rho t)) as Hu.
    destruct (t' =? t)%uint63 eqn:Et.
    + apply Uint63.eqb_spec in Et. subst t'. rewrite Hg in Hg'. injection Hg' as <-.
      assert (Eo : x - bv_unsigned (rho t) = to_Z pn * 4096 + j) by lia.
      assert (Hq : to_Z pn = (x - bv_unsigned (rho t)) / 4096) by (rewrite Eo; Z.div_mod_to_equations; lia).
      set (p0 := o / 4096) in *. set (p1 := (o + n - 1) / 4096) in *.
      assert (Hp01 : 0 <= p0 <= p1) by (unfold p0, p1; Z.div_mod_to_equations; lia).
      assert (Hp1 : p1 < 2 ^ 50) by (unfold p1; apply Z.div_lt_upper_bound; lia).
      assert (Hof : to_Z (of_Z p0) = p0) by (apply of_Z_small; lia).
      assert (Hkb : to_Z (of_Z p0) + Z.of_nat (Z.to_nat (p1 - p0 + 1)) <= 2 ^ 50) by (rewrite Hof; lia).
      assert (Hin : to_Z (of_Z p0) <= to_Z pn < to_Z (of_Z p0) + Z.of_nat (Z.to_nat (p1 - p0 + 1))).
      { rewrite Hof, Z2Nat.id by lia. rewrite Hq. unfold p0, p1. rewrite Hs in Hx.
        split; [apply Z.div_le_mono; lia|]. assert ((x - bv_unsigned (rho t)) / 4096 <= (o + n - 1) / 4096) by (apply Z.div_le_mono; lia). lia. }
      unfold nowr_chk in Hnw. fold p0 p1 in Hnw. destruct (sparse_rg rg t) eqn:Esp.
      * (* [comment removed for export] *)
        unfold sparse_rg in Esp. apply andb_prop in Esp as [Et0 Edf]. apply negb_true_iff in Et0.
        destruct (rg_dflt rg) eqn:Edflt; [discriminate|].
        unfold page_at in Hp. destruct (iget pn (rg_pages rg)) as [pe|] eqn:Hex.
        -- injection Hp as <-. unfold nowr_sparse in Hnw. rewrite forallb_forall in Hnw.
           pose proof (Hnw (pn, pe) (proj2 (ielements_spec (rg_pages rg) pn pe) Hex)) as Hsp. cbn [fst snd] in Hsp.
           rewrite Hwr in Hsp. rewrite Hof in Hin. rewrite Z2Nat.id in Hin by lia.
           replace (p0 <=? to_Z pn) with true in Hsp by (symmetry; apply Z.leb_le; lia).
           replace (to_Z pn <=? p1) with true in Hsp by (symmetry; apply Z.leb_le; lia). discriminate Hsp.
        -- rewrite Et0, Edflt in Hp. discriminate.
      * destruct (p1 - p0 + 1 <=? 4194304); [|discriminate].
        pose proof (pages_nowr_spec rg t _ (of_Z p0) Hkb Hnw (to_Z pn) p Hin) as Hno.
        rewrite of_to_Z in Hno. rewrite (Hno Hp) in Hwr. discriminate.
    + assert (Hne : t <> t') by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
      destruct (proj2 Hmem t t' rg rg' Hne Hg Hg') as [Hsep|Hsep]; rewrite Hs in Hx; lia.
  - unfold apart_chk in Hc. rewrite forallbL_eq, forallb_forall in Hc.
    rewrite EM0 in Hg'. cbn [state_of f_mem] in Hg'.
    destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hg') as (r & Hr & Ht & ->). subst t'.
    pose proof (Hc r Hr) as Hcr. cbv beta in Hcr.
    destruct (has_claims r) eqn:Ehc.
    2:{ (* [comment removed for export] *)
      exfalso. unfold has_claims in Ehc. apply orb_false_iff in Ehc as [Ehc E3]. apply orb_false_iff in Ehc as [E1 E2].
      unfold page_at in Hp. cbn [region_of rg_pages rg_dflt] in Hp.
      destruct (rd_pages r); [|discriminate]. cbn [map] in Hp. change (iof_list []) with (@iempty page) in Hp.
      rewrite iget_iempty, E1 in Hp. destruct (rd_dflt r); discriminate. }
    rewrite Era in Hcr. pose proof (AX2S.ranges_apart_sound segs E base kn _ _ _ _ _ _ Hkn Hcr) as Hd.
    unfold AX2S.estart in Hd, Hx. cbn [AX2.a_base AX2.a_off] in Hd. rewrite <- (rho_tte E TT) in Hd.
    cbn [region_of rg_lo rg_len] in Hlo', Hhi'. lia.
Qed.

End FrameSafe.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RootVis.
Variable segs : list Segment.
Variable IM : fimage.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn0 : list AX2.kentry.
Variable H : word -> bool.
Variable FULL : word -> option byte.
Variable M0 : itrie region.
Hypothesis HTT : tt_wf TT = true.
Hypothesis Hnoseg : forall x, H x = true -> find_segment segs (bv_unsigned x) 1 = None.
Hypothesis Hkn0 : AX2S.know_ok segs E (mrestrict H FULL) kn0.

Local Notation rho := (rho_of TT E).
Variable XTv : list (int * AX2.lin).
Hypothesis EXT : XTv = xt_of TT.
Local Notation XT := XTv.
Hypothesis HM0 : forall t rg, iget t M0 = Some rg -> region_ok rho t rg.

Lemma HXTv_rv : xt_ok rho (AX2.ev E) (AX2.eb E) [] XTv.
Proof. rewrite EXT. exact (xt_of_ok TT E HTT). Qed.

Definition cov_chk (t : int) (o n : Z) (a : AX2.saddr) (l : Z) : bool :=
  match aview [] M0 [] XT a with
  | Some (t', o') => (t' =? t)%uint63 && (o' <=? o) && (o + n <=? o' + l)
  | None => false
  end.

Definition covers (t : int) (o n : Z) (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w _ => cov_chk t o n a (Z.of_nat w)
  | AX2.KZero a (AX2.ELit l) | AX2.KWr a (AX2.ELit l) | AX2.KUnk a (AX2.ELit l)
  | AX2.KBlob a (AX2.ELit l) _ | AX2.KFill a (AX2.ELit l) _ =>
      (0 <=? l) && (l <? 2 ^ 64) && cov_chk t o n a l
  | _ => false
  end.

Definition vis_root (t : int) (o n : Z) : bool := existsb (covers t o n) kn0.

Lemma seg_rom_hidden x : H x = true -> PropExec.seg_rom segs x = None.
Proof.
  intros Hx. unfold PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite (Hnoseg x Hx). reflexivity.
Qed.

Lemma cov_view t o n a l : cov_chk t o n a l = true ->
  exists o', AX2S.estart E a = bv_unsigned (rho t) + o' /\ o' <= o /\ o + n <= o' + l.
Proof.
  unfold cov_chk. destruct (aview [] M0 [] XT a) as [[t' o']|] eqn:Hav; [|discriminate].
  intros Hc. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Ht H1].
  apply Uint63.eqb_spec in Ht. subst t'. apply Z.leb_le in H1, H2. exists o'.
  pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M0 [] XT HM0 (rho_of_0 TT E) eq_refl HXTv_rv a t o' Hav) as Hs.
  rewrite env_eta in Hs. tauto.
Qed.

Lemma lit_adr' t z : Z_to_bv 64 (bv_unsigned (rho t) + z) = adr rho t z.
Proof.
  unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Theorem vis_root_sound t o n :
  vis_root t o n = true -> forall j, 0 <= j < n -> H (adr rho t (o + j)) = false.
Proof.
  unfold vis_root. intros Hv j Hj. apply existsb_exists in Hv as (K & HK & Hc).
  pose proof (proj1 (Forall_forall _ _) Hkn0 K HK) as Hok.
  destruct (H (adr rho t (o + j))) eqn:Hx; [exfalso|reflexivity].
  assert (Hpt : forall a l, cov_chk t o n a l = true ->
            exists i, 0 <= i < l /\ Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + j)).
  { intros a l Hcc. destruct (cov_view t o n a l Hcc) as (o' & Es & H1 & H2).
    exists (o - o' + j). split; [lia|]. rewrite Es. rewrite <- lit_adr'. f_equal. lia. }
  destruct K as [a w v | a l | a l k | | | | a l | | a l c | a l]; cbn [covers] in Hc; try discriminate.
  - (* [comment removed for export] *)
    destruct (Hpt a _ Hc) as (i & Hi & Ei). destruct Hok as (Hw & Hflat & Hr).
    pose proof (rdn_bytes segs w _ _ _ Hr (Z.to_nat i) ltac:(lia)) as Hb.
    pose proof (PropExec.rdn_length _ _ _ _ _ Hr) as Hlen.
    assert (Ea : aoff (AX2.adenot E a) (Z.to_nat i) = adr rho t (o + j)).
    { rewrite <- Ei. destruct Hflat as (F1 & F2 & F3 & F4).
      assert (Ead : AX2.adenot E a = Z_to_bv 64 (AX2S.estart E a)).
      { apply bv_eq. rewrite (AX2S.flat_u _ _ _ (conj F1 (conj F2 (conj F3 F4)))).
        rewrite Z_to_bv_small by (unfold bv_modulus; lia). reflexivity. }
      rewrite Ead, aoff_lit by lia. f_equal. lia. }
    rewrite Ea in Hb. unfold rview, mrestrict in Hb. rewrite Hx in Hb.
    fold (PropExec.seg_rom segs (adr rho t (o + j))) in Hb. rewrite (seg_rom_hidden _ Hx) in Hb.
    symmetry in Hb. apply nth_error_None in Hb. lia.
  - (* [comment removed for export] *)
    destruct l as [l| | | | | | |]; try discriminate. apply andb_prop in Hc as [Hl Hc]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct (Hpt a _ Hc) as (i & Hi & Ei). destruct Hok as (_ & Hz).
    unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    specialize (Hz i Hi). rewrite Ei in Hz. unfold mrestrict in Hz. rewrite Hx in Hz. discriminate.
  - (* [comment removed for export] *)
    destruct l as [l| | | | | | |]; try discriminate. apply andb_prop in Hc as [Hl Hc]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct (Hpt a _ Hc) as (i & Hi & Ei). destruct Hok as (_ & _ & Hz).
    unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    specialize (Hz i Hi). rewrite Ei in Hz. unfold mrestrict in Hz. rewrite Hx in Hz. discriminate.
  - (* [comment removed for export] *)
    destruct l as [l| | | | | | |]; try discriminate. apply andb_prop in Hc as [Hl Hc]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct (Hpt a _ Hc) as (i & Hi & Ei). destruct Hok as (_ & Hs).
    unfold AX2S.elenZ in Hs. cbn [AX2.edenot] in Hs. rewrite br_lit_small in Hs by lia.
    specialize (Hs i 1%nat ltac:(lia) ltac:(lia)). rewrite Ei in Hs. cbn [store_ok] in Hs.
    unfold wview, mrestrict in Hs. rewrite Hx, (Hnoseg _ Hx) in Hs. discriminate.
  - (* [comment removed for export] *)
    destruct l as [l| | | | | | |]; try discriminate. apply andb_prop in Hc as [Hl Hc]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct (Hpt a _ Hc) as (i & Hi & Ei). destruct Hok as (_ & Hz).
    unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    specialize (Hz i Hi). rewrite Ei in Hz. unfold mrestrict in Hz. rewrite Hx in Hz. discriminate.
  - (* [comment removed for export] *)
    destruct l as [l| | | | | | |]; try discriminate. apply andb_prop in Hc as [Hl Hc]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct (Hpt a _ Hc) as (i & Hi & Ei). destruct Hok as (_ & Hz).
    unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    specialize (Hz i Hi). rewrite Ei in Hz. unfold mrestrict in Hz. rewrite Hx in Hz. congruence.
Qed.


(* [comment removed for export] *)
Definition ovcovers (t : int) (o n : Z) (K : AX2.kentry) : bool :=
  match K with
  | AX2.KZero a (AX2.ELit l) | AX2.KUnk a (AX2.ELit l) | AX2.KBlob a (AX2.ELit l) _ | AX2.KFill a (AX2.ELit l) _ =>
      (0 <=? l) && (l <? 2 ^ 64) && cov_chk t o n a l
  | _ => false
  end.

Definition ovdef_root (t : int) (o n : Z) : bool := existsb (ovcovers t o n) kn0.

Theorem ovdef_root_sound t o n :
  ovdef_root t o n = true -> forall j, 0 <= j < n -> FULL (adr rho t (o + j)) <> None.
Proof.
  unfold ovdef_root. intros Hv j Hj. apply existsb_exists in Hv as (K & HK & Hc).
  pose proof (proj1 (Forall_forall _ _) Hkn0 K HK) as Hok.
  assert (Hpt : forall a l, cov_chk t o n a l = true ->
            exists i, 0 <= i < l /\ Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + j)).
  { intros a l Hcc. destruct (cov_view t o n a l Hcc) as (o' & Es & H1 & H2).
    exists (o - o' + j). split; [lia|]. rewrite Es. rewrite <- lit_adr'. f_equal. lia. }
  assert (Hmr : forall y, mrestrict H FULL y <> None -> FULL y <> None).
  { intros y. unfold mrestrict. destruct (H y); [intros Hq; contradiction | tauto]. }
  destruct K as [a w v | a l | a l k | | | | a l | | a l c | a l]; cbn [ovcovers] in Hc; try discriminate;
    destruct l as [l| | | | | | |]; try discriminate;
    apply andb_prop in Hc as [Hl Hc]; apply andb_prop in Hl as [Hl0 Hl1];
    apply Z.leb_le in Hl0; apply Z.ltb_lt in Hl1;
    destruct (Hpt a _ Hc) as (i & Hi & Ei); apply Hmr; rewrite <- Ei.
  - destruct Hok as (_ & Hz). unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    rewrite (Hz i Hi). discriminate.
  - destruct Hok as (_ & _ & Hz). unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    rewrite (Hz i Hi). discriminate.
  - destruct Hok as (_ & Hz). unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    rewrite (Hz i Hi). discriminate.
  - destruct Hok as (_ & Hz). unfold AX2S.elenZ in Hz. cbn [AX2.edenot] in Hz. rewrite br_lit_small in Hz by lia.
    exact (Hz i Hi).
Qed.


(* [comment removed for export] *)
Definition view_l (a : AX2.saddr) (l : Z) : option (int * Z * Z) :=
  match aview [] M0 [] XT a with Some (t', o') => Some (t', o', l) | None => None end.

Definition cover_of (K : AX2.kentry) : option (int * Z * Z) :=
  match K with
  | AX2.KWord a w _ => view_l a (Z.of_nat w)
  | AX2.KZero a (AX2.ELit l) | AX2.KWr a (AX2.ELit l) | AX2.KUnk a (AX2.ELit l)
  | AX2.KBlob a (AX2.ELit l) _ | AX2.KFill a (AX2.ELit l) _ =>
      if (0 <=? l) && (l <? 2 ^ 64) then view_l a l else None
  | _ => None
  end.

Definition ovcover_of (K : AX2.kentry) : option (int * Z * Z) :=
  match K with
  | AX2.KZero a (AX2.ELit l) | AX2.KUnk a (AX2.ELit l) | AX2.KBlob a (AX2.ELit l) _ | AX2.KFill a (AX2.ELit l) _ =>
      if (0 <=? l) && (l <? 2 ^ 64) then view_l a l else None
  | _ => None
  end.

Definition olist {T : Type} (o : option T) : list T := match o with Some x => [x] | None => [] end.
Definition root_cov : list (int * Z * Z) := flat_map (fun K => olist (cover_of K)) kn0.
Definition root_ovcov : list (int * Z * Z) := flat_map (fun K => olist (ovcover_of K)) kn0.

Definition in_cov (t : int) (o n : Z) (c : int * Z * Z) : bool :=
  let '(t', o', l) := c in (t' =? t)%uint63 && (o' <=? o) && (o + n <=? o' + l).
Definition vis_pre (cov : list (int * Z * Z)) (t : int) (o n : Z) : bool := existsb (in_cov t o n) cov.

Lemma view_l_cov t o n a l c : view_l a l = Some c -> in_cov t o n c = true -> cov_chk t o n a l = true.
Proof.
  unfold view_l, cov_chk. destruct (aview [] M0 [] XT a) as [[t' o']|]; [|discriminate].
  intros Hq. injection Hq as <-. cbn [in_cov]. tauto.
Qed.

Lemma vis_pre_root t o n : vis_pre root_cov t o n = true -> vis_root t o n = true.
Proof.
  unfold vis_pre, vis_root, root_cov. intros Hv. apply existsb_exists in Hv as (c & Hc & Hin).
  apply in_flat_map in Hc as (K & HK & Hc). apply existsb_exists. exists K. split; [exact HK|].
  destruct K as [a w v | a l | a l k | | | | a l | | a l c0 | a l]; cbn [cover_of olist] in Hc; try contradiction;
    cbn [covers];
    try (destruct l as [l| | | | | | |]; cbn [olist] in Hc; try contradiction;
         destruct ((0 <=? l) && (l <? 2 ^ 64)) eqn:El; cbn [olist] in Hc; try contradiction; cbn [andb]);
    (destruct (view_l a _) as [c1|] eqn:Ev; cbn [olist] in Hc; [|contradiction]; destruct Hc as [->|[]];
     exact (view_l_cov t o n a _ c Ev Hin)).
Qed.

Lemma ovdef_pre_root t o n : vis_pre root_ovcov t o n = true -> ovdef_root t o n = true.
Proof.
  unfold vis_pre, ovdef_root, root_ovcov. intros Hv. apply existsb_exists in Hv as (c & Hc & Hin).
  apply in_flat_map in Hc as (K & HK & Hc). apply existsb_exists. exists K. split; [exact HK|].
  destruct K as [a w v | a l | a l k | | | | a l | | a l c0 | a l]; cbn [ovcover_of olist] in Hc; try contradiction;
    cbn [ovcovers];
    (destruct l as [l| | | | | | |]; cbn [olist] in Hc; try contradiction;
     destruct ((0 <=? l) && (l <? 2 ^ 64)) eqn:El; cbn [olist] in Hc; try contradiction; cbn [andb];
     destruct (view_l a _) as [c1|] eqn:Ev; cbn [olist] in Hc; [|contradiction]; destruct Hc as [->|[]];
     exact (view_l_cov t o n a _ c Ev Hin)).
Qed.

End RootVis.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Leaf.
Variable segs : list Segment.
Variable IM : fimage.
Variable A : APC.atable.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn0 : list AX2.kentry.
Variable H : word -> bool.
Variables FULL FULL' : word -> option byte.
Variable d : sdesc.
Variable M1 : itrie region.
Variable VT : vtab.
Variable nx : nat.
Hypothesis HTT : tt_wf TT = true.
Hypothesis Hnoseg : forall x, H x = true -> find_segment segs (bv_unsigned x) 1 = None.
Hypothesis Hkn0 : AX2S.know_ok segs E (mrestrict H FULL) kn0.
Variable ra : ra_t.                                   (* [comment removed for export] *)
Hypothesis Era : ra = AX2.ranges_apart kn0.
Variable km : AX2.kentry -> bool.                     (* [comment removed for export] *)
Hypothesis Ekm : forall K, km K = existsb (APC.kentry_eqb K) kn0.

Local Notation rho := (rho_of TT E).
(* [comment removed for export] *)
Variable XTv : list (int * AX2.lin).
Hypothesis EXT : XTv = xt_of TT.
Variable M0 : itrie region.
Hypothesis EM0 : M0 = f_mem (state_of d).
Variables cov ovcov : list (int * Z * Z).
Hypothesis Ecov : cov = root_cov kn0 M0 XTv.
Hypothesis Eovcov : ovcov = root_ovcov kn0 M0 XTv.
Local Notation XT := XTv.
Local Notation E' := (env_of rho (AX2.ev E) (AX2.eb E) VT).
Hypothesis Hmem0 : mem_ok segs IM rho M0 FULL.
Hypothesis Hmem1 : mem_ok segs IM rho M1 FULL'.
Hypothesis Hfr : forall x, ~ claimed_wr IM rho M0 x -> FULL' x = FULL x.
(* [comment removed for export] *)
Hypothesis Hcf : forall x, ~ cell_expl rho M1 x -> FULL' x = FULL x.
(* [comment removed for export] *)
Hypothesis Hgrow : forall x, FULL x <> None -> FULL' x <> None.
Hypothesis HVT : forallb (fun p => Nat.leb nx (fst p)) VT = true.
Hypothesis Hkv : APC.kn_vars_lt nx kn0 = true.
Hypothesis HTv : forallb (fun p => APC.expr_vars_lt nx (snd p)) TT = true.

(* [comment removed for export] *)
Lemma vt_get_new : forall x, (x < nx)%nat -> vt_get VT x = None.
Proof.
  intros x Hx. revert HVT. induction VT as [|[y dd] r IH]; intros Hv; [reflexivity|].
  cbn [forallb fst] in Hv. apply andb_prop in Hv as [Hy Hr]. apply Nat.leb_le in Hy.
  cbn [vt_get]. destruct (Nat.eqb x y) eqn:Eyx; [apply Nat.eqb_eq in Eyx; lia | exact (IH Hr)].
Qed.

Lemma tr_agree : AxSymRun3.env_agree nx E E'.
Proof.
  split; [|reflexivity]. intros x Hx. rewrite ev_env_of, (vt_get_new x Hx). reflexivity.
Qed.

Lemma tr_xt : xt_ok rho (AX2.ev E) (AX2.eb E) VT XT.
Proof.
  rewrite EXT. unfold xt_ok, xt_of. apply Forall_forall. intros p Hp.
  apply in_map_iff in Hp as ([t e] & <- & Hin). cbn [fst snd].
  destruct (tt_get_In TT t e HTT Hin) as [Hg Hne].
  rewrite forallb_forall in HTv. pose proof (HTv (t, e) Hin) as Hve. cbn [snd] in Hve.
  assert (Er : rho t = AX2.edenot E' e).
  { unfold rho_of. destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; contradiction|].
    rewrite Hg. exact (APS.edenot_agree' nx E E' e tr_agree Hve). }
  rewrite Er. apply AX2S.lin_of_sound.
Qed.

(* [comment removed for export] *)
Definition noseg_chk (t : int) (o n : Z) : bool :=
  (0 <=? o) && (0 <=? n)
  && match AX2.base_range kn0 (tte TT t) with Some (_, bhi) => (bhi + o + n <=? 2 ^ 64) | None => false end
  && ra (AX2.ELit 0) (APC.img_lo A) (APC.img_hi A - APC.img_lo A) (tte TT t) o n.

Lemma noseg_chk_sound t o n :
  noseg_chk t o n = true -> forall j, 0 <= j < n -> find_segment segs (bv_unsigned (adr rho t (o + j))) 1 = None.
Proof.
  unfold noseg_chk. intros Hc j Hj. apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hb].
  apply andb_prop in Hc as [Ho Hn]. apply Z.leb_le in Ho, Hn.
  destruct (AX2.base_range kn0 (tte TT t)) as [[blo bhi]|] eqn:Hr; [|discriminate]. apply Z.leb_le in Hb.
  destruct (AX2S.base_range_sound segs E _ kn0 _ blo bhi Hkn0 Hr) as [_ Hhi]. rewrite <- (rho_tte E TT) in Hhi.
  rewrite Era in Hap. pose proof (AX2S.ranges_apart_sound segs E _ kn0 _ _ _ _ _ _ Hkn0 Hap) as Hd.
  unfold AX2S.estart in Hd. cbn [AX2.a_base AX2.a_off AX2.edenot] in Hd. rewrite <- (rho_tte E TT) in Hd.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hd.
  pose proof (br_u64 (rho t)) as Hu.
  assert (Ux : bv_unsigned (adr rho t (o + j)) = bv_unsigned (rho t) + (o + j)) by (apply adr_unsigned; lia).
  apply SEGS_in_hull. unfold APS.in_hull. rewrite Ux. apply andb_false_iff.
  destruct Hd as [Hd|Hd]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
Qed.

(* [comment removed for export] *)
Definition is_pure (K : AX2.kentry) : bool :=
  match K with AX2.KAlign _ _ | AX2.KRange _ _ _ | AX2.KDisj _ _ _ _ => true | _ => false end.

Definition len_hi (n : AX2.expr) : option Z :=
  match n with
  | AX2.ELit z => if (0 <=? z) && (z <? 2 ^ 64) then Some z else None
  | _ => match AX2.erange kn0 n with Some (_, hi) => Some hi | None => None end
  end.

Lemma len_hi_sound n h : len_hi n = Some h -> AX2S.elenZ E n <= h.
Proof.
  unfold len_hi, AX2S.elenZ. intros Hl.
  assert (Hgen : match AX2.erange kn0 n with Some (_, hi) => Some hi | None => None end = Some h ->
                 bv_unsigned (AX2.edenot E n) <= h).
  { destruct (AX2.erange kn0 n) as [[lo hi]|] eqn:Hr; [|discriminate]. intros Hq. injection Hq as <-.
    exact (proj2 (AX2S.erange_sound segs E _ kn0 n lo hi Hkn0 Hr)). }
  destruct n as [z| | | | | | |]; try exact (Hgen Hl).
  destruct ((0 <=? z) && (z <? 2 ^ 64)) eqn:Hz; [|discriminate]. injection Hl as <-.
  apply andb_prop in Hz as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  cbn [AX2.edenot]. rewrite br_lit_small by lia. lia.
Qed.

Definition fchk (a : AX2.saddr) (n : Z) : bool := (n <=? 0) || frame_chk IM TT d ra XTv M0 a n.

Definition carried_chk (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w _ => fchk a (Z.of_nat w)
  | AX2.KZero a n | AX2.KBlob a n _ | AX2.KFill a n _ | AX2.KUnk a n | AX2.KWr a n =>
      match len_hi n with Some h => fchk a h | None => false end
  | AX2.KImg lo hi => (0 <=? lo) && fchk (AX2.SA (AX2.ELit 0) lo) (hi - lo)
  | _ => false
  end.

Lemma fchk_sound a n n' :
  fchk a n = true -> AX2S.flat E a n' -> n' <= n ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + n' -> ~ claimed_wr IM rho M0 (Z_to_bv 64 x).
Proof.
  unfold fchk. intros Hc Hflat Hn x Hx. apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
  exact (frame_chk_sound segs IM E TT kn0 _ d FULL HTT Hkn0 ra Era XTv EXT M0 EM0 Hmem0 a n n' Hc Hflat Hn x Hx).
Qed.

Lemma carried_sound K :
  carried_chk K = true -> AX2S.kentry_ok segs E (mrestrict H FULL) K ->
  forall x, kentry_bytes E K x -> ~ claimed_wr IM rho M0 (Z_to_bv 64 x).
Proof.
  intros Hc HK x Hx.
  destruct K as [a w v | a n | a n j | lo hi | e m0 | e lo hi | a n | a1 n1 a2 n2 | a n c | a n];
    cbn [carried_chk kentry_bytes AX2S.kentry_ok] in *; try discriminate; try contradiction.
  - destruct HK as (_ & Hflat & _). exact (fchk_sound a _ _ Hc Hflat ltac:(lia) x Hx).
  - destruct (len_hi n) as [h|] eqn:Hl; [|discriminate]. destruct HK as (Hflat & _).
    exact (fchk_sound a h _ Hc Hflat (len_hi_sound n h Hl) x Hx).
  - destruct (len_hi n) as [h|] eqn:Hl; [|discriminate]. destruct HK as (Hflat & _).
    exact (fchk_sound a h _ Hc Hflat (len_hi_sound n h Hl) x Hx).
  - apply andb_prop in Hc as [Hlo Hc]. apply Z.leb_le in Hlo. destruct HK as (_ & Hhi & _).
    assert (Hflat : AX2S.flat E (AX2.SA (AX2.ELit 0) lo) (hi - lo)).
    { unfold AX2S.flat, AX2S.estart. cbn [AX2.a_base AX2.a_off AX2.edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0. lia. }
    apply (fchk_sound _ _ _ Hc Hflat ltac:(lia) x).
    unfold AX2S.estart. cbn [AX2.a_base AX2.a_off AX2.edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  - destruct (len_hi n) as [h|] eqn:Hl; [|discriminate]. destruct HK as (Hflat & _).
    exact (fchk_sound a h _ Hc Hflat (len_hi_sound n h Hl) x Hx).
  - destruct (len_hi n) as [h|] eqn:Hl; [|discriminate]. destruct HK as (Hflat & _).
    exact (fchk_sound a h _ Hc Hflat (len_hi_sound n h Hl) x Hx).
  - destruct (len_hi n) as [h|] eqn:Hl; [|discriminate]. destruct HK as (Hflat & _).
    exact (fchk_sound a h _ Hc Hflat (len_hi_sound n h Hl) x Hx).
Qed.

(* [comment removed for export] *)
Definition cells_small (M : itrie region) : bool :=
  forallb (fun tr => forallb (fun pp => (to_Z (fst pp) <? 2 ^ 50)
                                        && (to_Z (rg_lo (snd tr)) <=? to_Z (fst pp) * 4096)
                                        && forallb (fun cc => (to_Z (fst cc) <? 512)
                                                              && (to_Z (fst pp) * 4096 + to_Z (fst cc) * 8 + 8 <=? to_Z (rg_len (snd tr))))
                                                   (ielements (pg_cells (snd pp))))
                             (ielements (rg_pages (snd tr)))) (ielements M).

Definition cells_off (p : page) (pn : int) (lo hi : Z) : bool :=
  forallb (fun cc => let c := to_Z pn * 4096 + to_Z (fst cc) * 8 in (c + 8 <=? lo) || (hi <=? c)) (ielements (pg_cells p)).

Definition kimg_chk (lo hi : Z) : bool :=
  match iget 0%uint63 M1 with
  | Some rg0 =>
      (0 <=? lo) && (to_Z (rg_lo rg0) <=? lo) && (hi <=? to_Z (rg_len rg0))
      && forallb (fun pp => cells_off (snd pp) (fst pp) lo hi) (ielements (rg_pages rg0))
  | None => false
  end.

Definition kimg_cell_chk (K : AX2.kentry) : bool :=
  match K with AX2.KImg lo hi => kimg_chk lo hi | _ => false end.

Hypothesis Hsmall : cells_small M1 = true.

Lemma cells_small_spec t rg pn p ci :
  iget t M1 = Some rg -> iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) <> None ->
  to_Z pn < 2 ^ 50 /\ to_Z ci < 512
  /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 + to_Z ci * 8 + 8 <= to_Z (rg_len rg).
Proof.
  intros Hg Hp Hc. unfold cells_small in Hsmall. rewrite forallb_forall in Hsmall.
  pose proof (Hsmall (t, rg) (proj2 (ielements_spec M1 t rg) Hg)) as H1. cbn [snd] in H1.
  rewrite forallb_forall in H1.
  pose proof (H1 (pn, p) (proj2 (ielements_spec (rg_pages rg) pn p) Hp)) as H2. cbn [fst snd] in H2.
  apply andb_prop in H2 as [H2 H3]. apply andb_prop in H2 as [H2 H2l]. apply Z.ltb_lt in H2. apply Z.leb_le in H2l.
  destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|contradiction].
  rewrite forallb_forall in H3.
  pose proof (H3 (ci, c) (proj2 (ielements_spec (pg_cells p) ci c) Ec)) as H4. cbn [fst] in H4.
  apply andb_prop in H4 as [H4 H5]. apply Z.ltb_lt in H4. apply Z.leb_le in H5. tauto.
Qed.

(* [comment removed for export] *)
Definition pages_off (pages : itrie page) (lo hi : Z) : bool :=
  forallb (fun pp : int * page =>
     if (to_Z (fst pp) * 4096 + 4096 <=? lo) || (hi <=? to_Z (fst pp) * 4096) then true
     else cells_off (snd pp) (fst pp) lo hi) (ielements pages).

Lemma pages_off_all t rg lo hi : iget t M1 = Some rg -> pages_off (rg_pages rg) lo hi = true ->
  forallb (fun pp => cells_off (snd pp) (fst pp) lo hi) (ielements (rg_pages rg)) = true.
Proof.
  intros Hg Hc. unfold pages_off in Hc. rewrite forallb_forall in Hc. apply forallb_forall. intros [pn p] Hin.
  pose proof (Hc _ Hin) as H1. cbn [fst snd] in *.
  destruct ((to_Z pn * 4096 + 4096 <=? lo) || (hi <=? to_Z pn * 4096)) eqn:Eo; [|exact H1].
  unfold cells_off. apply forallb_forall. intros [ci c] Hcin. cbn [fst]. cbv zeta.
  pose proof (proj1 (ielements_spec (rg_pages rg) pn p) Hin) as Hp.
  pose proof (proj1 (ielements_spec (pg_cells p) ci c) Hcin) as Hcc.
  destruct (cells_small_spec t rg pn p ci Hg Hp ltac:(rewrite Hcc; discriminate)) as (_ & Hci & _).
  pose proof (i63_range ci) as Hci0.
  apply orb_prop in Eo as [Eo|Eo]; apply Z.leb_le in Eo; apply orb_true_iff; [left | right]; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Fixpoint pages_off_n (pages : itrie page) (lo hi : Z) (pn : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match iget pn pages with Some p => cells_off p pn lo hi | None => true end
            && pages_off_n pages lo hi (pn + 1)%uint63 k'
  end.

Lemma pages_off_n_spec pages lo hi : forall k pn, to_Z pn + Z.of_nat k < 2 ^ 62 ->
  pages_off_n pages lo hi pn k = true ->
  forall q p, to_Z pn <= to_Z q < to_Z pn + Z.of_nat k -> iget q pages = Some p -> cells_off p q lo hi = true.
Proof.
  induction k as [|k IH]; intros pn Hb Hc q p Hq Hg; [lia|].
  cbn [pages_off_n] in Hc. apply andb_prop in Hc as [H0 Hr]. pose proof (i63_range pn) as Hpn.
  destruct (Z.eq_dec (to_Z q) (to_Z pn)) as [Eq|Hne].
  - assert (q = pn) by (apply to_Z_inj; exact Eq). subst q. rewrite Hg in H0. exact H0.
  - assert (E1 : to_Z (pn + 1)%uint63 = to_Z pn + 1).
    { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
    apply (IH (pn + 1)%uint63 ltac:(lia) Hr q p); [lia | exact Hg].
Qed.

Definition pages_off2 (pages : itrie page) (lo hi : Z) : bool :=
  if (0 <=? lo) && (lo <? hi) && (hi - lo <=? 1048576) && (hi <? 2 ^ 62)
  then pages_off_n pages lo hi (of_Z (lo / 4096)) (Z.to_nat ((hi - 1) / 4096 - lo / 4096 + 1))
  else pages_off pages lo hi.

Lemma pages_off2_all t rg lo hi : iget t M1 = Some rg -> pages_off2 (rg_pages rg) lo hi = true ->
  forallb (fun pp => cells_off (snd pp) (fst pp) lo hi) (ielements (rg_pages rg)) = true.
Proof.
  intros Hg. unfold pages_off2.
  destruct ((0 <=? lo) && (lo <? hi) && (hi - lo <=? 1048576) && (hi <? 2 ^ 62)) eqn:Efast; [|exact (pages_off_all t rg lo hi Hg)].
  apply andb_prop in Efast as [Ef H62]. apply andb_prop in Ef as [Ef Hsz]. apply andb_prop in Ef as [Hlo0 Hlt].
  apply Z.leb_le in Hlo0, Hsz. apply Z.ltb_lt in Hlt, H62.
  intros Hc. apply forallb_forall. intros [pn p] Hin. cbn [fst snd].
  pose proof (proj1 (ielements_spec (rg_pages rg) pn p) Hin) as Hp. pose proof (i63_range pn) as Hpn.
  assert (Ep0 : to_Z (of_Z (lo / 4096)) = lo / 4096).
  { apply of_Z_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hdiv : 0 <= lo / 4096 <= (hi - 1) / 4096 /\ (hi - 1) / 4096 < 2 ^ 50).
  { split; [split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia] | apply Z.div_lt_upper_bound; lia]. }
  destruct (Z_le_dec (lo / 4096) (to_Z pn)) as [H1|H1]; [destruct (Z_le_dec (to_Z pn) ((hi - 1) / 4096)) as [H2|H2]|].
  - apply (pages_off_n_spec (rg_pages rg) lo hi (Z.to_nat ((hi - 1) / 4096 - lo / 4096 + 1)) (of_Z (lo / 4096)));
      [rewrite Ep0, Z2Nat.id by lia; lia | exact Hc | rewrite Ep0, Z2Nat.id by lia; lia | exact Hp].
  - (* [comment removed for export] *)
    unfold cells_off. apply forallb_forall. intros [ci c] Hcin. cbn [fst]. cbv zeta. apply orb_true_iff. right. apply Z.leb_le.
    pose proof (i63_range ci) as Hci0. assert (hi <= to_Z pn * 4096) by (clear - H2 Hlt; Z.div_mod_to_equations; lia). lia.
  - (* [comment removed for export] *)
    unfold cells_off. apply forallb_forall. intros [ci c] Hcin. cbn [fst]. cbv zeta. apply orb_true_iff. left. apply Z.leb_le.
    pose proof (proj1 (ielements_spec (pg_cells p) ci c) Hcin) as Hcc.
    destruct (cells_small_spec t rg pn p ci Hg Hp ltac:(rewrite Hcc; discriminate)) as (_ & Hci & _).
    pose proof (i63_range ci) as Hci0. assert (to_Z pn * 4096 + 4096 <= lo) by (clear - H1 Hlo0; Z.div_mod_to_equations; lia). lia.
Qed.

Definition kimg_fast (lo hi : Z) : bool :=
  match iget 0%uint63 M1 with
  | Some rg0 => (0 <=? lo) && (to_Z (rg_lo rg0) <=? lo) && (hi <=? to_Z (rg_len rg0)) && pages_off2 (rg_pages rg0) lo hi
  | None => false
  end.

Lemma kimg_fast_ok lo hi : kimg_fast lo hi = true -> kimg_chk lo hi = true.
Proof.
  unfold kimg_fast, kimg_chk. destruct (iget 0%uint63 M1) as [rg0|] eqn:Hg0; [|discriminate]. intros Hc.
  apply andb_prop in Hc as [Hc Hp]. rewrite Hc. cbn [andb]. exact (pages_off2_all _ rg0 lo hi Hg0 Hp).
Qed.


Definition kimg_cell_fast (K : AX2.kentry) : bool :=
  match K with AX2.KImg lo hi => kimg_fast lo hi | _ => false end.
Lemma kimg_cell_fast_ok K : kimg_cell_fast K = true -> kimg_cell_chk K = true.
Proof. destruct K; cbn [kimg_cell_fast kimg_cell_chk]; try discriminate. apply kimg_fast_ok. Qed.


Lemma kimg_chk_sound lo hi :
  kimg_chk lo hi = true -> forall i, lo <= i < hi -> ~ cell_expl rho M1 (Z_to_bv 64 i).
Proof.
  unfold kimg_chk. intros Hc i Hi (t & rg & pn & p & ci & Hg & Hp & Hce & j & Hj & Ex).
  destruct (iget 0%uint63 M1) as [rg0|] eqn:Hg0; [|discriminate].
  apply andb_prop in Hc as [Hc Hpages]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo0 Hlo].
  apply Z.leb_le in Hlo0, Hlo, Hhi.
  destruct (cells_small_spec t rg pn p ci Hg Hp Hce) as (Hpn & Hci & Hplo & Hphi).
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range ci) as Hci0.
  destruct (proj1 Hmem1 t rg Hg) as [Hreg _].
  destruct Hreg as (_ & Hlen62 & Hnw & _).
  destruct (proj1 Hmem1 0%uint63 rg0 Hg0) as [(_ & Hlen0 & _) _].
  pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range (rg_lo rg)) as Hrl.
  assert (Ux : bv_unsigned (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + j))
               = bv_unsigned (rho t) + (to_Z pn * 4096 + to_Z ci * 8 + j)) by (apply adr_unsigned; lia).
  assert (Ei : i = bv_unsigned (rho t) + (to_Z pn * 4096 + to_Z ci * 8 + j)).
  { rewrite <- Ux, <- Ex. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    symmetry. apply Z.mod_small. lia. }
  destruct (t =? 0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. rewrite Hg0 in Hg. injection Hg as <-.
    rewrite (rho_of_0 TT E) in Ei. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Ei.
    rewrite forallb_forall in Hpages.
    pose proof (Hpages (pn, p) (proj2 (ielements_spec (rg_pages rg0) pn p) Hp)) as Hoff. cbn [fst snd] in Hoff.
    unfold cells_off in Hoff. rewrite forallb_forall in Hoff.
    destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|contradiction].
    pose proof (Hoff (ci, c) (proj2 (ielements_spec (pg_cells p) ci c) Ec)) as Hd. cbn [fst] in Hd. cbv zeta in Hd.
    apply orb_prop in Hd as [Hd|Hd]; [apply Z.leb_le in Hd | apply Z.leb_le in Hd]; lia.
  - assert (Hne : 0%uint63 <> t) by (intros <-; rewrite Uint63.eqb_refl in Et; discriminate).
    pose proof (proj2 Hmem1 0%uint63 t rg0 rg Hne Hg0 Hg) as Hsep.
    rewrite (rho_of_0 TT E) in Hsep. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hsep. lia.
Qed.

Definition xs0 : int -> Z -> option slots := fun _ _ => None.
Definition xw0 : int -> Z -> Z -> bool := fun _ _ _ => false.
Local Notation visb := (vis_pre cov).

(* [comment removed for export] *)
Definition ov_chk (t : int) (o n : Z) : bool := noseg_chk t o n || vis_pre ovcov t o n.

Lemma ov_chk_sound t o n : ov_chk t o n = true -> forall j, 0 <= j < n ->
  FULL' (adr rho t (o + j)) <> None \/ find_segment segs (bv_unsigned (adr rho t (o + j))) 1 = None.
Proof.
  unfold ov_chk. intros Hc j Hj. apply orb_prop in Hc as [Hc|Hc].
  - right. exact (noseg_chk_sound t o n Hc j Hj).
  - left. apply Hgrow. rewrite Eovcov in Hc.
    exact (ovdef_root_sound segs E TT kn0 H FULL M0 HTT Hkn0 XTv EXT (fun t0 rg Hg => proj1 (proj1 Hmem0 t0 rg Hg)) t o n
             (ovdef_pre_root kn0 M0 XTv t o n Hc) j Hj).
Qed.

Definition new_chk (K : AX2.kentry) : bool :=
  match K with
  (* [comment removed for export] *)
  | AX2.KWord a w v => kword_ok IM VT M1 [] XT [] visb a w v || kword_slots_ok IM VT M1 [] XT [] visb (slotsP IM M1) a w v
  | AX2.KWr a n => kwr_ok IM VT M1 [] XT visb (wr_rangeP IM M1) a n
  | AX2.KUnk a n => kunk_ok IM VT M1 [] XT visb ov_chk (wr_rangeP IM M1) a n
  | AX2.KZero a n => kzero_ok IM VT M1 [] XT visb ov_chk (slotsP IM M1) a n
  | _ => false
  end.

(* [comment removed for export] *)
Definition kimg_sub_chk (K : AX2.kentry) : bool :=
  match K with
  | AX2.KImg lo hi =>
      existsb (fun K0 => match K0 with AX2.KImg lo0 hi0 => (lo0 <=? lo) && (hi <=? hi0) | _ => false end) kn0
      && kimg_chk lo hi
  | _ => false
  end.


(* [comment removed for export] *)
Definition cellfreeC_chk (t : int) (lo hi : Z) : bool :=
  match iget t M1 with
  | Some rg0 =>
      (0 <=? lo) && (to_Z (rg_lo rg0) <=? lo) && (hi <=? to_Z (rg_len rg0))
      && pages_off2 (rg_pages rg0) lo hi
  | None => false
  end.

Lemma cellfreeC_sound t0 lo hi :
  cellfreeC_chk t0 lo hi = true -> forall i, lo <= i < hi -> ~ cell_expl rho M1 (adr rho t0 i).
Proof.
  unfold cellfreeC_chk. intros Hc i Hi (t & rg & pn & p & ci & Hg & Hp & Hce & j & Hj & Ex).
  destruct (iget t0 M1) as [rg0|] eqn:Hg0; [|discriminate].
  apply andb_prop in Hc as [Hc Hpages]. apply (pages_off2_all _ rg0 _ _ Hg0) in Hpages.
  apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo0 Hlo].
  apply Z.leb_le in Hlo0, Hlo, Hhi.
  destruct (cells_small_spec t rg pn p ci Hg Hp Hce) as (Hpn & Hci & Hplo & Hphi).
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range ci) as Hci0.
  destruct (proj1 Hmem1 t rg Hg) as [Hreg _].
  destruct Hreg as (_ & Hlen62 & Hnw & _).
  destruct (proj1 Hmem1 t0 rg0 Hg0) as [(_ & Hlen0 & Hnw0 & _) _].
  pose proof (br_u64 (rho t)) as Hu. pose proof (br_u64 (rho t0)) as Hu0.
  pose proof (i63_range (rg_lo rg)) as Hrl. pose proof (i63_range (rg_lo rg0)) as Hrl0.
  assert (Ux : bv_unsigned (adr rho t (to_Z pn * 4096 + to_Z ci * 8 + j))
               = bv_unsigned (rho t) + (to_Z pn * 4096 + to_Z ci * 8 + j)) by (apply adr_unsigned; lia).
  assert (Ui : bv_unsigned (adr rho t0 i) = bv_unsigned (rho t0) + i) by (apply adr_unsigned; lia).
  assert (Ei : bv_unsigned (rho t0) + i = bv_unsigned (rho t) + (to_Z pn * 4096 + to_Z ci * 8 + j)) by (rewrite <- Ux, <- Ui, Ex; reflexivity).
  destruct (t =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. rewrite Hg0 in Hg. injection Hg as <-.
    rewrite forallb_forall in Hpages.
    pose proof (Hpages (pn, p) (proj2 (ielements_spec (rg_pages rg0) pn p) Hp)) as Hoff. cbn [fst snd] in Hoff.
    unfold cells_off in Hoff. rewrite forallb_forall in Hoff.
    destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|contradiction].
    pose proof (Hoff (ci, c) (proj2 (ielements_spec (pg_cells p) ci c) Ec)) as Hd. cbn [fst] in Hd. cbv zeta in Hd.
    apply orb_prop in Hd as [Hd|Hd]; [apply Z.leb_le in Hd | apply Z.leb_le in Hd]; lia.
  - assert (Hne : t0 <> t) by (intros <-; rewrite Uint63.eqb_refl in Et; discriminate).
    pose proof (proj2 Hmem1 t0 t rg0 rg Hne Hg0 Hg) as Hsep. lia.
Qed.

Definition vfchkC (a : AX2.saddr) (nn : Z) : bool :=
  if (nn <=? 0) then true else
  match aview [] M0 [] XTv a with
  | Some (t, o) => (0 <=? o) && (o + nn <? 2 ^ 62) && cellfreeC_chk t o (o + nn)
  | None => false
  end.

Definition carried_cfC (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w _ => vfchkC a (Z.of_nat w)
  | AX2.KZero a nn | AX2.KBlob a nn _ | AX2.KFill a nn _ | AX2.KUnk a nn | AX2.KWr a nn =>
      match len_hi nn with Some h => vfchkC a h | None => false end
  | _ => false
  end.

Lemma vfchkC_sound a nn nn' :
  vfchkC a nn = true -> nn' <= nn ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + nn' -> ~ cell_expl rho M1 (Z_to_bv 64 x).
Proof.
  unfold vfchkC. intros Hc Hn x Hx. destruct (nn <=? 0) eqn:E0; [apply Z.leb_le in E0; lia|].
  destruct (aview [] M0 [] XTv a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hc as [Hc Hcf0]. apply andb_prop in Hc as [Ho H62].
  apply Z.ltb_lt in H62. apply Z.leb_le in Ho.
  assert (HXTv0 : xt_ok rho (AX2.ev E) (AX2.eb E) [] XTv) by (rewrite EXT; exact (xt_of_ok TT E HTT)).
  assert (HM0r : forall t rg, iget t M0 = Some rg -> region_ok rho t rg) by (intros t1 rg1 Hg1; exact (proj1 (proj1 Hmem0 t1 rg1 Hg1))).
  pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M0 [] XTv HM0r (rho_of_0 TT E) eq_refl HXTv0 a t o Hav) as Hs.
  rewrite env_eta in Hs.
  replace (Z_to_bv 64 x) with (adr rho t (o + (x - AX2S.estart E a))).
  - apply (cellfreeC_sound t o (o + nn) Hcf0). lia.
  - unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma carried_cfC_sound K :
  carried_cfC K = true -> AX2S.kentry_ok segs E (mrestrict H FULL) K ->
  forall x, kentry_bytes E K x -> ~ cell_expl rho M1 (Z_to_bv 64 x).
Proof.
  intros Hc HK x Hx.
  destruct K as [a w v | a nn | a nn j | lo hi | e m0 | e lo hi | a nn | a1 n1 a2 n2 | a nn c | a nn];
    cbn [carried_cfC kentry_bytes] in *; try discriminate; try contradiction;
    try (destruct (len_hi nn) as [h|] eqn:Hl; [|discriminate]; exact (vfchkC_sound a h _ Hc (len_hi_sound nn h Hl) x Hx)).
  exact (vfchkC_sound a (Z.of_nat w) (Z.of_nat w) Hc (Z.le_refl _) x Hx).
Qed.

(* [comment removed for export] *)
Definition kimg_sub_fast (K : AX2.kentry) : bool :=
  match K with
  | AX2.KImg lo hi =>
      if existsb (fun K0 => match K0 with AX2.KImg lo0 hi0 => (lo0 <=? lo) && (hi <=? hi0) | _ => false end) kn0
      then kimg_fast lo hi else false
  | _ => false
  end.
Lemma kimg_sub_fast_ok K : kimg_sub_fast K = true -> kimg_sub_chk K = true.
Proof.
  destruct K as [ | | | lo hi | | | | | | ]; cbn [kimg_sub_fast kimg_sub_chk]; try discriminate.
  destruct (existsb _ kn0); [|discriminate]. intros Hc. rewrite (kimg_fast_ok _ _ Hc). reflexivity.
Qed.

Definition tr_entry_chk (K : AX2.kentry) : bool :=
  (* [comment removed for export] *)
  if (if (if km K
          then (if (if (if is_pure K then true else carried_chk K) then true else kimg_cell_fast K) then true else carried_cfC K) else false)
      then true else kimg_sub_fast K)
  then true else new_chk K.

Lemma HM0' : forall t rg, iget t M0 = Some rg -> region_ok rho t rg.
Proof. intros t rg Hg. exact (proj1 (proj1 Hmem0 t rg Hg)). Qed.

Lemma tr_visb_sound : forall t o n, visb t o n = true -> forall j, 0 <= j < n -> H (adr rho t (o + j)) = false.
Proof.
  intros t o n Hv. rewrite Ecov in Hv.
  exact (vis_root_sound segs E TT kn0 H FULL M0 HTT Hnoseg Hkn0 XTv EXT HM0' t o n (vis_pre_root kn0 M0 XTv t o n Hv)).
Qed.

Lemma kvars_in_gen : forall l K, APC.kn_vars_lt nx l = true -> In K l -> APC.kn_vars_lt nx [K] = true.
Proof.
  induction l as [|K0 r IH]; intros K Hv Hin; [destruct Hin|].
  cbn [APC.kn_vars_lt] in Hv. apply andb_prop in Hv as [H0 Hr]. destruct Hin as [->|Hin].
  - cbn [APC.kn_vars_lt]. rewrite H0. reflexivity.
  - exact (IH K Hr Hin).
Qed.

Lemma kvars_in K : In K kn0 -> APC.kn_vars_lt nx [K] = true.
Proof. exact (kvars_in_gen kn0 K Hkv). Qed.

Theorem tr_entry_sound K : tr_entry_chk K = true -> AX2S.kentry_ok segs E' (mrestrict H FULL') K.
Proof.
  unfold tr_entry_chk. rewrite (Ekm K). intros Hc. apply orb_prop in Hc as [Hc|Hc]; [apply orb_prop in Hc as [Hc|Hc]|].
  2:{ (* [comment removed for export] *)
    apply kimg_sub_fast_ok in Hc.
    destruct K as [ | | | lo hi | | | | | | ]; cbn [kimg_sub_chk] in Hc; try discriminate.
    apply andb_prop in Hc as [Hsub Hci]. apply existsb_exists in Hsub as (K0 & HK0 & Hs).
    destruct K0 as [ | | | lo0 hi0 | | | | | | ]; try discriminate.
    apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1, Hs2.
    pose proof (proj1 (Forall_forall _ _) Hkn0 _ HK0) as Hok. cbn [AX2S.kentry_ok] in *.
    destruct Hok as (Hk1 & Hk2 & Hk3). split; [lia|]. split; [lia|].
    intros i Hi. specialize (Hk3 i ltac:(lia)). unfold mrestrict in *.
    destruct (H (Z_to_bv 64 i)); [reflexivity|].
    rewrite (Hcf _ (kimg_chk_sound _ _ Hci i Hi)). exact Hk3. }
  - apply andb_prop in Hc as [Hin Hc]. apply existsb_exists in Hin as (K0 & HK0 & Heq).
    apply APS.kentry_eqb_eq in Heq. subst K0.
    pose proof (proj1 (Forall_forall _ _) Hkn0 K HK0) as Hok.
    assert (Hok' : AX2S.kentry_ok segs E (mrestrict H FULL') K).
    { apply orb_prop in Hc as [Hc|Hcfc].
      2:{ (* [comment removed for export] *)
        apply (kentry_ok_ext segs E (mrestrict H FULL) (mrestrict H FULL') K); [|exact Hok].
        intros x Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)); [reflexivity|].
        apply Hcf. exact (carried_cfC_sound K Hcfc Hok x Hx). }
      apply orb_prop in Hc as [Hc|Hci]; [apply orb_prop in Hc as [Hp|Hcar]|].
      - destruct K; try discriminate; exact Hok.
      - apply (kentry_ok_ext segs E (mrestrict H FULL) (mrestrict H FULL') K); [|exact Hok].
        intros x Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)); [reflexivity|].
        apply Hfr. exact (carried_sound K Hcar Hok x Hx).
      - (* [comment removed for export] *)
        apply kimg_cell_fast_ok in Hci.
        destruct K; cbn [kimg_cell_chk] in Hci; try discriminate.
        cbn [AX2S.kentry_ok] in *. destruct Hok as (Hk1 & Hk2 & Hk3). split; [exact Hk1|]. split; [exact Hk2|].
        intros i Hi. specialize (Hk3 i Hi). unfold mrestrict in *.
        destruct (H (Z_to_bv 64 i)); [reflexivity|].
        rewrite (Hcf _ (kimg_chk_sound _ _ Hci i Hi)). exact Hk3. }
    assert (Hl : AX2S.know_ok segs E (mrestrict H FULL') [K]) by (constructor; [exact Hok' | constructor]).
    pose proof (APS.know_ok_agree' segs nx E E' (mrestrict H FULL') [K] tr_agree (kvars_in K HK0) Hl) as Hk.
    exact (Forall_inv Hk).
  - destruct K as [a w v | a n | | | | | a n | | | a n]; cbn [new_chk] in Hc; try discriminate.
    + apply orb_prop in Hc as [Hc|Hc].
      * exact (kword_sound segs IM rho (AX2.ev E) (AX2.eb E) VT M1 [] XT [] FULL' (rho_of_0 TT E) Hmem1 eq_refl tr_xt
                 (Forall_nil _) H visb tr_visb_sound a w v Hc).
      * apply (kword_slots_sound segs IM rho (AX2.ev E) (AX2.eb E) VT M1 [] XT [] FULL' (rho_of_0 TT E) Hmem1 eq_refl tr_xt
                 (Forall_nil _) H visb tr_visb_sound (slotsP IM M1));
          [exact (slotsP_sound segs IM rho M1 FULL' (rho_of_0 TT E) Hmem1) | exact Hc].
    + apply (kzero_sound segs IM rho (AX2.ev E) (AX2.eb E) VT M1 [] XT FULL' (rho_of_0 TT E) Hmem1 eq_refl tr_xt
               H visb tr_visb_sound ov_chk ov_chk_sound (slotsP IM M1));
        [exact (slotsP_sound segs IM rho M1 FULL' (rho_of_0 TT E) Hmem1) | exact Hc].
    + apply (kwr_sound segs IM rho (AX2.ev E) (AX2.eb E) VT M1 [] XT FULL' (rho_of_0 TT E) Hmem1 eq_refl tr_xt
               H visb tr_visb_sound (wr_rangeP IM M1)); [exact (wr_rangeP_sound segs IM rho M1 FULL' Hmem1) | exact Hc].
    + apply (kunk_sound segs IM rho (AX2.ev E) (AX2.eb E) VT M1 [] XT FULL' (rho_of_0 TT E) Hmem1 eq_refl tr_xt
               H visb tr_visb_sound ov_chk ov_chk_sound (wr_rangeP IM M1)); [exact (wr_rangeP_sound segs IM rho M1 FULL' Hmem1) | exact Hc].
Qed.

End Leaf.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DressChk.
Variable segs : list Segment.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn : list AX2.kentry.
Variable base : word -> option byte.
Hypothesis Hkn : AX2S.know_ok segs E base kn.
Variable n : int.

(* [comment removed for export] *)
Definition shadow_e (e : AX2.expr) : AX2.expr :=
  AX2.EAlu ALU_ADD (AX2.EAlu ALU_SRL e (AX2.ELit 3)) (AX2.ELit (to_Z shadow_K)).

Lemma shadow_e_den e : bv_unsigned (AX2.edenot E (shadow_e e)) = bv_unsigned (AX2.edenot E e) / 8 + to_Z shadow_K.
Proof.
  unfold shadow_e. cbn [AX2.edenot]. rewrite AX2S.u_add64, AX2S.u_srl64.
  rewrite !br_lit_small by (cbv; split; congruence). change (3 mod 64) with 3. change (2 ^ 3) with 8.
  pose proof (br_u64 (AX2.edenot E e)) as Hu. apply Z.mod_small.
  change (to_Z shadow_K) with 2147450880. split; [|].
  - pose proof (Z.div_pos (bv_unsigned (AX2.edenot E e)) 8 ltac:(lia) ltac:(lia)). lia.
  - assert (bv_unsigned (AX2.edenot E e) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Definition dress_chk (x : ditem) : bool :=
  let '(t, clo, chi, k) := x in
  (to_Z t <? to_Z n)
  && match AX2.base_range kn (tte TT t) with
     | Some (blo, bhi) => (to_Z clo <=? blo) && (bhi <=? to_Z chi)
     | None => false
     end
  && match k with
     | RK_plain => true
     | RK_shadow p => (to_Z p <? to_Z t) && AX2.expr_eqb (tte TT t) (shadow_e (tte TT p))
     end.

Lemma dress_chk_sound x : dress_chk x = true -> ditem_lt n x /\ ditem_ok (rho_of TT E) x.
Proof.
  destruct x as [[[t clo] chi] k]. unfold dress_chk. intros Hc.
  apply andb_prop in Hc as [Hc Hk]. apply andb_prop in Hc as [Ht Hb]. apply Z.ltb_lt in Ht.
  destruct (AX2.base_range kn (tte TT t)) as [[blo bhi]|] eqn:Hr; [|discriminate].
  apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2.
  destruct (AX2S.base_range_sound segs E base kn _ blo bhi Hkn Hr) as [Hlo Hhi].
  rewrite <- (rho_tte E TT t) in Hlo, Hhi.
  destruct k as [|p].
  - split; cbn [ditem_lt ditem_ok rkind_ok]; repeat split; try exact I; lia.
  - apply andb_prop in Hk as [Hp He]. apply Z.ltb_lt in Hp. apply AX2S.expr_eqb_eq in He.
    split; cbn [ditem_lt ditem_ok rkind_ok]; repeat split; try lia.
    rewrite (rho_tte E TT t), He, shadow_e_den, <- (rho_tte E TT p). reflexivity.
Qed.

Lemma dress_chk_all bs : forallb dress_chk bs = true ->
  Forall (ditem_lt n) bs /\ Forall (ditem_ok (rho_of TT E)) bs.
Proof.
  intros H. rewrite forallb_forall in H. split; apply Forall_forall; intros x Hx;
    destruct (dress_chk_sound x (H x Hx)) as [H1 H2]; assumption.
Qed.
End DressChk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FxTransform.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : APC.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> APC.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : APC.expr_vars_lt nx0 APC.e_sp0_early = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

(* [comment removed for export] *)
Variable TT : ttab_e.
Variable n : int.
Variable shapes : list rshape.
Variable cuts : list (int * list Z).
Variable classes : list (int * rclass).     (* [comment removed for export] *)
Variable CS : APC.acs.
Variable d : sdesc.
Variable bs : list ditem.        (* [comment removed for export] *)
Variable bp : int.
Variable k : nat.
Variable F' : fstate.
Variable r : stop.
Variable cnt : int.
Variable VT : vtab.
Variable pc' : Z.
Variable regs' : list AX2.expr.
Variable kn' : list AX2.kentry.
Variable nxt' : nat.

Definition tr_state : APC.acs := APC.with_ss CS (APC.mk_ss pc' regs' kn' nxt').

Definition tr_check : bool :=
  (* [comment removed for export] *)
  let XTv := xt_of TT in
  let M0v := f_mem (state_of d) in
  let cov := root_cov (APC.kn CS) M0v XTv in
  let ovc := root_ovcov (APC.kn CS) M0v XTv in
  rb_check IM A TT n shapes cuts classes CS d
  && forallb (dress_chk TT (APC.kn CS) n) bs
  && APC.fresh_ok nx0 CS
  && forallb (fun p => Nat.leb (APC.nxt CS) (fst p)) VT
  && forallb (fun p => APC.expr_vars_lt (APC.nxt CS) (snd p)) TT
  && (pc' =? to_Z (f_pc F'))
  && match f_resv F' with None => true | Some _ => false end
  && forallb (fun i => val_match VT [] XTv [] (nth i regs' (AX2.ELit 0)) (FxState.rget F' (of_Z (Z.of_nat i)))) (seq 1 31)
  && cells_small (f_mem F')
  && (let ra := ra_fast (APC.kn CS) in      (* [comment removed for export] *)
      forallb (tr_entry_chk IM A TT (APC.kn CS) d (f_mem F') VT ra (BrKset.kset_mem (BrKset.kset_of (APC.kn CS))) XTv M0v cov ovc) kn').

Variable E : AX2.env.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXI.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hchk : tr_check = true.
Hypothesis Hk : (k <= 61)%nat.
Hypothesis Hrun : fx_run IM code bp k (dress (state_of d) bs) = (F', r, cnt).

Local Notation rho := (rho_of TT E).
Local Notation H := (APS.hid A argH E CS m).
Local Notation M0 := (f_mem (state_of d)).
Local Notation AA := (APS.allowA A E CS).
Hypothesis HLZ : LZ IM rho (m_vm_lazy m) AA M0.
Hypothesis Hcw : forall x, claimed_wr IM rho M0 x -> H x = false.

Local Notation ms0 := (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (APC.a_ss CS))) FULL (PropExec.seg_rom segs)).
Local Notation E' := (env_of rho (AX2.ev E) (AX2.eb E) VT).

Lemma ms_eta (ms : machine_state) regs pcv mem rom :
  ms_regs ms = regs -> ms_fregs ms = bvmap_empty -> ms_pc_val ms = pcv -> ms_svc_pending ms = None ->
  ms_resv ms = None -> ms_fcsr ms = Z_to_bv 32 0 -> ms_mem ms = mem -> ms_rom ms = rom ->
  ms = PropExec.mkst regs pcv mem rom.
Proof. destruct ms. cbn. intros -> -> -> -> -> -> -> ->. reflexivity. Qed.

Theorem fx_transform T :
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (APC.nxt CS) E E1 ->
     CXI.cs_ok segs A Lim SINV argH ISP FS0 E1 tr_state R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (APS.cfg_of segs R1 pc' FULL1 m1) T) ->
  realizes_cfg cfg segs (APS.cfg_of segs R (AX2.s_pc (APC.a_ss CS)) FULL m) T.
Proof.
  intros HK.
  unfold tr_check in Hchk. cbv zeta in Hchk.
  apply andb_prop in Hchk as [Hc Hkn']. apply andb_prop in Hc as [Hc Hsmall]. apply andb_prop in Hc as [Hc Hregs']. apply andb_prop in Hc as [Hc Hresv].
  apply andb_prop in Hc as [Hc Hpc]. apply andb_prop in Hc as [Hc HTv]. apply andb_prop in Hc as [Hc HVT].
  apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hrb Hdress]. apply Z.eqb_eq in Hpc.
  pose proof (rb_parts IM A TT n shapes cuts classes CS d Hrb) as (HTT & _).
  (* [comment removed for export] *)
  pose proof (rb_Rn segs IM HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high TT n shapes cuts classes CS d E R FULL m HCS Hrb) as HRn0.
  pose proof (rho_of_0 TT E) as Hrho0.
  assert (HR0 : FxRel.R segs IM rho (state_of d) ms0) by (apply HRn0; split; [exact Hrho0 | intros; reflexivity]).
  (* [comment removed for export] *)
  destruct (dress_chk_all segs E TT (APC.kn CS) _ (CXI.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) n bs Hdress) as [Hdlt Hdok].
  pose proof (Rn_dress segs IM n rho (state_of d) ms0 bs HRn0 Hdlt Hdok) as HRn0d.
  assert (HR0d : FxRel.R segs IM rho (dress (state_of d) bs) ms0) by (apply HRn0d; split; [exact Hrho0 | intros; reflexivity]).
  pose proof (dress_same bs M0) as Hsame. change (fold_left dress_mem bs M0) with (f_mem (dress (state_of d) bs)) in Hsame.
  (* [comment removed for export] *)
  destruct (fx_run_Rn segs IM code Hcode n rho bp k (dress (state_of d) bs) F' r cnt ms0 Hk Hrun Hrho0 HRn0d)
    as (ms' & Hsteps & HRn1 & _ & Hframe_d & _ & Hrom).
  assert (Hframe : forall x, ~ claimed_wr IM rho M0 x -> ms_mem ms' x = ms_mem ms0 x).
  { intros x Hx. apply Hframe_d. intros Hc. apply Hx. exact (claimed_wr_same IM rho _ _ x Hsame Hc). }
  destruct (fx_run_Rn_shape segs IM code Hcode n rho bp k (dress (state_of d) bs) F' r cnt ms0 ms' Hk Hrun Hrho0 HRn0d Hsteps) as [Hfregs Hfcsr].
  assert (HR1 : FxRel.R segs IM rho F' ms') by (apply HRn1; split; [exact Hrho0 | intros; reflexivity]).
  pose proof (fx_run_cellframe segs IM rho Hrho0 code Hcode bp k (dress (state_of d) bs) F' r cnt Hk Hrun ms0 ms' HR0d Hsteps) as Hcellfr.
  destruct (fx_run_touch segs IM rho Hrho0 code Hcode (m_vm_lazy m) AA bp k (dress (state_of d) bs) F' r cnt Hk Hrun) as [_ Htouch].
  pose proof (APS.A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E CS) as HAwf.
  unfold APS.cfg_of.
  apply (rzc_rsteps_minv segs cfg AA _ ms0 ms' m T HAwf (CXI.co_halt _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hsteps
           (CXI.co_minv _ _ _ _ _ _ _ _ _ _ _ _ HCS) (Htouch ms0 HR0d (LZ_same IM rho _ _ _ _ Hsame HLZ))).
  intros m' Hlf Hminv'.
  (* [comment removed for export] *)
  destruct HR1 as [R1pc R1regs R1svc R1resv R1mem].
  assert (Ems : ms' = PropExec.mkst (ms_regs ms') (Z_to_bv 64 pc') (ms_mem ms') (PropExec.seg_rom segs)).
  { apply ms_eta; try reflexivity.
    - rewrite Hfregs. reflexivity.
    - rewrite R1pc, Hpc. reflexivity.
    - exact R1svc.
    - rewrite R1resv. destruct (f_resv F'); [discriminate | reflexivity].
    - rewrite Hfcsr. reflexivity.
    - rewrite Hrom. reflexivity. }
  rewrite Ems.
  (* [comment removed for export] *)
  pose proof (tr_agree E TT VT (APC.nxt CS) HVT) as Hag.
  unfold APC.fresh_ok in Hfresh. cbv zeta in Hfresh.
  pose proof Hfresh as Hfresh0.
  apply andb_prop in Hfresh as [Hf Hle]. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _].   (* [comment removed for export] *)
  apply andb_prop in Hf as [Hf Fgh]. apply andb_prop in Hf as [Hf Fvis]. apply andb_prop in Hf as [Hf _].
  apply andb_prop in Hf as [_ Fkn]. apply Nat.leb_le in Hle.
  assert (Fallow : APC.pairs_vars_lt (APC.nxt CS) (APC.a_vis CS ++ APC.a_ghost CS) = true).
  { unfold APC.pairs_vars_lt in *. rewrite forallb_app, Fvis, Fgh. reflexivity. }
  pose proof (CXI.cs_ok_agree segs A nx0 Lim NX0_spw SINV argH ISP argH_agree SINV_agree FS0 E E' CS R FULL m Hag Hfresh0 HCS) as HCS'.
  pose proof (APS.hid_agree A nx0 argH argH_agree (APC.nxt CS) E E' CS m Hag Hle Fallow) as Ehid.
  pose proof (APS.allowA_agree A (APC.nxt CS) E E' CS Hag Fallow) as EA.
  (* [comment removed for export] *)
  assert (Hhid : forall a, H a = true -> ms_mem ms' a = FULL a).
  { intros a Ha. apply (Hframe a). intros Hcl. rewrite (Hcw a Hcl) in Ha. discriminate. }
  apply (HK E' (ms_regs ms') (ms_mem ms') m' Hag).
  - apply (cs_ok_transform segs A Lim SINV argH ISP FS0 SINV_frame E' CS R FULL m pc' regs' kn' nxt'
             (ms_regs ms') (ms_mem ms') m' HCS').
    + (* [comment removed for export] *)
      unfold AX2S.regs_ok. intros rr. unfold getr, AX2.sr_get.
      destruct (bv_eqb rr 0) eqn:Er; [reflexivity|].
      pose proof (R1regs rr) as Hreg. unfold Sem.rget in Hreg. change (is_x0 rr) with (bv_eqb rr 0) in Hreg.
      rewrite Er in Hreg. change (c_regs (core_of ms')) with (ms_regs ms') in Hreg. rewrite Hreg.
      rewrite forallb_forall in Hregs'.
      pose proof (bv_unsigned_in_range _ rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
      assert (Hr0 : bv_unsigned rr <> 0) by (intros E0; unfold bv_eqb in Er; rewrite E0 in Er; discriminate).
      specialize (Hregs' (AX2.ridx rr)). unfold AX2.ridx in *. rewrite Z2Nat.id in Hregs' by lia.
      symmetry.
      apply (val_match_sound rho (AX2.ev E) (AX2.eb E) VT (f_mem F') [] (xt_of TT) []
               (fun t rg Hg => proj1 (proj1 R1mem t rg Hg)) Hrho0 eq_refl
               (tr_xt E TT VT (APC.nxt CS) HTT (xt_of TT) eq_refl HVT HTv) (Forall_nil _)).
      apply Hregs'. apply in_seq. lia.
    + (* [comment removed for export] *)
      rewrite Ehid. apply Forall_forall. intros K HKin. rewrite forallb_forall in Hkn'.
      apply (tr_entry_sound segs IM A SEGS_in_hull E TT (APC.kn CS) H FULL (ms_mem ms') d (f_mem F') VT (APC.nxt CS) HTT
               (APS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH (CXI.argH_high1 argH ISP argH_high) E CS m)
               (CXI.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) (ra_fast (APC.kn CS)) (ra_fast_eq _) _ (BrKset.kset_mem_of' (APC.kn CS)) _ eq_refl _ eq_refl _ _ eq_refl eq_refl
               (R_mem _ _ _ _ _ HR0) R1mem Hframe Hcellfr
               (rsteps_mem_grows segs _ ms0 ms' Hsteps) HVT Fkn HTv Hsmall K (Hkn' K HKin)).
    + exact Hlf.
    + rewrite EA. exact Hminv'.
    + intros a Ha. rewrite Ehid in Ha. exact (Hhid a Ha).
  - destruct Hlf as [mat' ->]. reflexivity.
Qed.

End FxTransform.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Side.
Variable segs : list Segment.
Variable IM : fimage.
Variable A : APC.atable.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn0 : list AX2.kentry.
Variable H : word -> bool.
Variable FULL : word -> option byte.
Variable d : sdesc.
Variable lazy : list (word * word).
Variable AA : list (Z * Z).
Hypothesis HTT : tt_wf TT = true.
Hypothesis Hnoseg : forall x, H x = true -> find_segment segs (bv_unsigned x) 1 = None.
Hypothesis Hkn0 : AX2S.know_ok segs E (mrestrict H FULL) kn0.
Hypothesis Hhull : forall a, APC.img_lo A <= a < APC.img_hi A -> H (Z_to_bv 64 a) = false.
Hypothesis Hcover : AsanAcct.lazy_cover H lazy AA.

Local Notation rho := (rho_of TT E).
Local Notation M0 := (f_mem (state_of d)).
Hypothesis Hmem0 : mem_ok segs IM rho M0 FULL.
Local Notation visb := (vis_root kn0 M0 (xt_of TT)).

(* [comment removed for export] *)
Definition page_ext (r : rdesc) (p : pdesc) : Z := Z.min 4096 (to_Z (rd_len r) - to_Z (pd_pn p) * 4096).

Definition page_side_chk (r : rdesc) (p : pdesc) : bool :=
  if pd_wr p then visb (rd_tag r) (to_Z (pd_pn p) * 4096) (page_ext r p)
  else (12 <=? to_Z (rd_align r))
       && existsb (fun c => (to_Z (fst c) <? 512) && visb (rd_tag r) (to_Z (pd_pn p) * 4096 + to_Z (fst c) * 8) 1) (pd_cells p).

Definition region_side_chk (r : rdesc) : bool :=
  if (rd_tag r =? 0)%uint63 then (APC.img_lo A <=? to_Z (rd_lo r)) && (to_Z (rd_len r) <=? APC.img_hi A)
  else match rd_dflt r with
       | Some _ => visb (rd_tag r) (to_Z (rd_lo r)) (to_Z (rd_len r) - to_Z (rd_lo r))
       | None => forallb (page_side_chk r) (rd_pages r)
       end.

Definition side_chk : bool := forallb region_side_chk (sd_mem d).

(* [comment removed for export] *)
Definition page_side_chkP (cov : list (int * Z * Z)) (r : rdesc) (p : pdesc) : bool :=
  if pd_wr p then vis_pre cov (rd_tag r) (to_Z (pd_pn p) * 4096) (page_ext r p)
  else (12 <=? to_Z (rd_align r))
       && existsb (fun c => (to_Z (fst c) <? 512) && vis_pre cov (rd_tag r) (to_Z (pd_pn p) * 4096 + to_Z (fst c) * 8) 1) (pd_cells p).
Definition region_side_chkP (cov : list (int * Z * Z)) (r : rdesc) : bool :=
  if (rd_tag r =? 0)%uint63 then (APC.img_lo A <=? to_Z (rd_lo r)) && (to_Z (rd_len r) <=? APC.img_hi A)
  else match rd_dflt r with
       | Some _ => vis_pre cov (rd_tag r) (to_Z (rd_lo r)) (to_Z (rd_len r) - to_Z (rd_lo r))
       | None => forallb (page_side_chkP cov r) (rd_pages r)
       end.
Definition side_chkP : bool :=
  let cov := root_cov kn0 M0 (xt_of TT) in forallb (region_side_chkP cov) (sd_mem d).

Lemma region_side_chkP_ok r : region_side_chkP (root_cov kn0 M0 (xt_of TT)) r = true -> region_side_chk r = true.
Proof.
  unfold region_side_chkP, region_side_chk. intros H2.
  destruct (rd_tag r =? 0)%uint63; [exact H2|]. destruct (rd_dflt r) as [k|].
  - exact (vis_pre_root kn0 M0 (xt_of TT) _ _ _ H2).
  - apply forallb_forall. intros p Hp. rewrite forallb_forall in H2. pose proof (H2 p Hp) as H3.
    unfold page_side_chkP in H3. unfold page_side_chk. destruct (pd_wr p).
    + exact (vis_pre_root kn0 M0 (xt_of TT) _ _ _ H3).
    + apply andb_prop in H3 as [H4 H5]. rewrite H4. cbn [andb]. apply existsb_exists in H5 as (c & Hc1 & Hc2).
      apply existsb_exists. exists c. split; [exact Hc1|]. apply andb_prop in Hc2 as [H6 H7]. rewrite H6. cbn [andb].
      exact (vis_pre_root kn0 M0 (xt_of TT) _ _ _ H7).
Qed.
Lemma side_chkP_ok : side_chkP = true -> side_chk = true.
Proof.
  unfold side_chkP, side_chk. cbv zeta. intros Hc. apply forallb_forall. intros r Hr. rewrite forallb_forall in Hc.
  exact (region_side_chkP_ok r (Hc r Hr)).
Qed.

Hypothesis Hside : side_chk = true.

Lemma HM0s : forall t rg, iget t M0 = Some rg -> region_ok rho t rg.
Proof. intros t rg Hg. exact (proj1 (proj1 Hmem0 t rg Hg)). Qed.

Lemma visb_nh : forall t o n, visb t o n = true -> forall j, 0 <= j < n -> H (adr rho t (o + j)) = false.
Proof. exact (vis_root_sound segs E TT kn0 H FULL M0 HTT Hnoseg Hkn0 (xt_of TT) eq_refl HM0s). Qed.

(* [comment removed for export] *)
Lemma page_class t rg pn p :
  iget t M0 = Some rg -> to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p ->
  (forall x, 0 <= x < 4096 -> to_Z pn * 4096 + x < to_Z (rg_len rg) -> H (adr rho t (to_Z pn * 4096 + x)) = false)
  \/ (pg_wr p = false /\ bv_unsigned (rho t) mod 4096 = 0
      /\ exists x, 0 <= x < 4096 /\ H (adr rho t (to_Z pn * 4096 + x)) = false).
Proof.
  intros Hg Hpn Hp.
  destruct (proj1 Hmem0 t rg Hg) as [Hrok Hpages]. destruct (Hpages pn p Hpn Hp) as (_ & Hlo & Hlt & _).
  cbn [state_of f_mem] in Hg.
  destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hg) as (r & Hr & Ht & ->). subst t.
  unfold side_chk in Hside. rewrite forallb_forall in Hside. pose proof (Hside r Hr) as Hrc.
  unfold region_side_chk in Hrc. cbn [region_of rg_lo rg_len] in Hlo, Hlt. cbn [region_of rg_len].
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rd_lo r)) as Hl0.
  destruct (rd_tag r =? 0)%uint63 eqn:Et.
  - (* [comment removed for export] *)
    left. intros x Hx Hxl. apply Uint63.eqb_spec in Et. rewrite Et.
    apply andb_prop in Hrc as [H1 H2]. apply Z.leb_le in H1, H2.
    unfold adr. rewrite (rho_of_0 TT E).
    replace (bv_add (Z_to_bv 64 0) (Z_to_bv 64 (to_Z pn * 4096 + x))) with (Z_to_bv 64 (to_Z pn * 4096 + x)).
    + apply Hhull. lia.
    + apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      rewrite Z.add_0_l, bv_wrap_small by apply bv_unsigned_in_range. reflexivity.
  - destruct (rd_dflt r) as [kd|] eqn:Ed.
    + (* [comment removed for export] *)
      left. intros x Hx Hxl.
      replace (to_Z pn * 4096 + x) with (to_Z (rd_lo r) + (to_Z pn * 4096 + x - to_Z (rd_lo r))) by lia.
      apply (visb_nh _ _ _ Hrc). lia.
    + (* [comment removed for export] *)
      unfold page_at in Hp. cbn [region_of rg_pages rg_dflt] in Hp.
      destruct (iget pn (iof_list (map (fun p0 => (pd_pn p0, page_of p0)) (rd_pages r)))) as [p1|] eqn:Hex.
      * injection Hp as <-.
        destruct (iget_iof_list_map_In pd_pn page_of _ _ _ Hex) as (pd & Hpd & Epn & ->). subst pn.
        rewrite forallb_forall in Hrc. pose proof (Hrc pd Hpd) as Hpc. unfold page_side_chk in Hpc.
        cbn [page_of pg_wr]. destruct (pd_wr pd) eqn:Ew.
        -- left. intros x Hx Hxl. apply (visb_nh _ _ _ Hpc). unfold page_ext. lia.
        -- right. split; [reflexivity|]. apply andb_prop in Hpc as [Hal Hwit]. apply Z.leb_le in Hal.
           destruct Hrok as (_ & _ & _ & _ & Hmod & _). cbn [region_of rg_align] in Hmod.
           split.
           { pose proof (i63_range (rd_align r)) as Ha0.
             assert (Hdiv : (4096 | 2 ^ to_Z (rd_align r))).
             { exists (2 ^ (to_Z (rd_align r) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
             apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ _ _ Hdiv).
             apply Z.mod_divide; [apply Z.pow_nonzero; lia | exact Hmod]. }
           apply existsb_exists in Hwit as (c & _ & Hc). apply andb_prop in Hc as [Hc512 Hv]. apply Z.ltb_lt in Hc512.
           pose proof (i63_range (fst c)) as Hc0.
           exists (to_Z (fst c) * 8). split; [lia|].
           replace (to_Z (pd_pn pd) * 4096 + to_Z (fst c) * 8) with (to_Z (pd_pn pd) * 4096 + to_Z (fst c) * 8 + 0) by lia.
           apply (visb_nh _ _ _ Hv). lia.
      * rewrite Et, Ed in Hp. discriminate.
Qed.

Theorem side_cw : forall x, claimed_wr IM rho M0 x -> H x = false.
Proof.
  intros x (t & rg & pn & p & j & Hg & Hpn & Hp & Hwr & Hj & Hjl & ->).
  destruct (page_class t rg pn p Hg Hpn Hp) as [Hnh | (Hro & _)]; [exact (Hnh j Hj Hjl) | congruence].
Qed.

Theorem side_LZ : LZ IM rho lazy AA M0.
Proof.
  intros t rg pn p x Hg Hpn Hp Hx Hxl Hlz.
  destruct (proj1 Hmem0 t rg Hg) as [Hrok Hpages]. destruct (Hpages pn p Hpn Hp) as (_ & Hlo & Hlt & _).
  destruct Hrok as (_ & _ & Hb63 & _).
  pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rg_lo rg)) as Hl0.
  assert (Hadr : forall y, 0 <= y < 4096 ->
            bv_unsigned (adr rho t (to_Z pn * 4096 + y)) = bv_unsigned (rho t) + to_Z pn * 4096 + y).
  { intros y Hy. rewrite adr_unsigned by lia. lia. }
  destruct (page_class t rg pn p Hg Hpn Hp) as [Hnh | (_ & Hmod & y & Hy & Hnhy)].
  - pose proof (Hcover (adr rho t (to_Z pn * 4096 + x))) as Hc. unfold page_base in Hc.
    rewrite (Hadr x Hx) in Hc. exact (Hc Hlz (Hnh x Hx Hxl)).
  - pose proof (Hcover (adr rho t (to_Z pn * 4096 + y))) as Hc. unfold page_base in Hc.
    rewrite (Hadr y Hy) in Hc.
    assert (Epg : page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + y)
                  = page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + x)).
    { unfold page_base_of, page_size. f_equal. clear - Hmod Hx Hy. Z.div_mod_to_equations. lia. }
    rewrite Epg in Hc. exact (Hc Hlz Hnhy).
Qed.

End Side.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FxTransformChk.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : APC.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> APC.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : APC.expr_vars_lt nx0 APC.e_sp0_early = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Theorem fx_transform_chk TT n shapes cuts classes CS d bs bp k F' r cnt VT pc' regs' kn' nxt' E R FULL m T :
  CXI.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  tr_check IM A nx0 TT n shapes cuts classes CS d bs F' VT pc' regs' kn' = true ->
  side_chk A TT (APC.kn CS) d = true ->
  (k <= 61)%nat ->
  fx_run IM code bp k (dress (state_of d) bs) = (F', r, cnt) ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (APC.nxt CS) E E1 ->
     CXI.cs_ok segs A Lim SINV argH ISP FS0 E1 (tr_state CS pc' regs' kn' nxt') R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (APS.cfg_of segs R1 pc' FULL1 m1) T) ->
  realizes_cfg cfg segs (APS.cfg_of segs R (AX2.s_pc (APC.a_ss CS)) FULL m) T.
Proof.
  intros HCS Hchk Hside Hk Hrun HK.
  assert (Hrb : rb_check IM A TT n shapes cuts classes CS d = true).
  { pose proof Hchk as Hc0. unfold tr_check in Hc0. cbv zeta in Hc0. do 9 (apply andb_prop in Hc0 as [Hc0 _]). exact Hc0. }
  pose proof (rb_parts IM A TT n shapes cuts classes CS d Hrb) as (HTT & _).
  pose proof (rb_Rn segs IM HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high TT n shapes cuts classes CS d E R FULL m HCS Hrb) as HRn0.
  assert (HR0 : FxRel.R segs IM (rho_of TT E) (state_of d)
                  (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (APC.a_ss CS))) FULL (PropExec.seg_rom segs)))
    by (apply HRn0; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR0) as Hmem0. cbn [ms_mem PropExec.mkst] in Hmem0.
  pose proof (APS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH (CXI.argH_high1 argH ISP argH_high) E CS m) as Hnoseg.
  pose proof (CXI.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn0.
  pose proof (fun a => rb_hull A argH ISP HULL_ok argH_high CS E m a) as Hhull.
  pose proof (APS.lazy_cover_cs segs A Lim (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
                HULL_ok SINV argH FS0 0%nat E CS R FULL m (CXI.cs_ok_aps _ _ _ _ _ _ _ _ _ _ _ _ HCS)) as Hcover.
  apply (fx_transform cfg segs IM code Hcode HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high nx0 NX0_spw
           argH_agree SINV_agree SINV_frame TT n shapes cuts classes CS d bs bp k F' r cnt VT pc' regs' kn' nxt' E R FULL m
           HCS Hchk Hk Hrun); [ | | exact HK].
  - exact (side_LZ segs IM A E TT (APC.kn CS) _ FULL d _ _ HTT Hnoseg Hkn0 Hhull Hcover Hmem0 Hside).
  - exact (side_cw segs IM A E TT (APC.kn CS) _ FULL d HTT Hnoseg Hkn0 Hhull Hmem0 Hside).
Qed.

End FxTransformChk.
