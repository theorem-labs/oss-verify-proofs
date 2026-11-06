(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS Tac. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface RT_client_kit D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface BgLayerF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Definition nbuf (PL : placement) (r : bnref) : Prop := forall a d, pl_of PL r <> Some (PFrameBuf a d).

Lemma wref_nbuf : forall PL r, wref PL r -> nbuf PL r.
Proof. intros PL r [_ H]. exact H. Qed.
Lemma hpl_nbuf : forall PL r, hpl PL r -> nbuf PL r.
Proof. intros PL r H. exact (proj2 (hpl_wref PL r H)). Qed.
Lemma nbuf_pool : forall PL i, nbuf PL (RPool i).
Proof. intros PL i. exact (proj2 (wref_pool PL i)). Qed.
Lemma nbuf_one : forall PL, nbuf PL ROne.
Proof. intros PL a d. rewrite pl_of_one. discriminate. Qed.
Lemma nbuf_nofr : forall PL r, pl_wf PL -> pl_frames PL = [] -> nbuf PL r.
Proof.
  intros PL r WF NOFR a d E. destruct (pl_of_cases PL r _ E) as [[_ E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
  exact (pl_frames_no_framebuf PL r a d WF NOFR Eb).
Qed.

Ltac w_lib_ref HA NRO :=
  right; right; lazymatch type of HA with ref_at _ _ _ ?r ?a => exists r, a; split; [first [exact HA | eassumption | eapply ref_at_stable; eassumption] | split; [exact NRO | cbn [fst snd]; split; lia]] end.

Ltac lb_in_heap :=
  let b := fresh "b" in let Hb := fresh "Hb" in
  intros b Hb; first [ exact Hb | apply in_or_app; right; exact Hb | right; apply in_or_app; right; exact Hb ].

Ltac solve_nbuf :=
  first [ assumption
        | match goal with H : wref ?PL ?r |- nbuf ?PL ?r => exact (wref_nbuf PL r H) end
        | match goal with H : hpl ?PL ?r |- nbuf ?PL ?r => exact (hpl_nbuf PL r H) end
        | apply nbuf_pool
        | match goal with H : ?r = RPool ?i |- nbuf ?PL ?r => rewrite H; apply nbuf_pool end
        | match goal with H : pl_frames ?PL = [] , W : pl_wf ?PL |- nbuf ?PL ?r => exact (nbuf_nofr PL r W H) end ].

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition frames_lb (PL : placement) (LB : list block) : Prop := pl_frames_lb PL LB /\ frames_al PL.

Lemma frames_lb_nofr : forall PL LB, pl_frames PL = [] -> frames_lb PL LB.
Proof. intros PL LB E. split; [apply pl_frames_lb_nofr; exact E|]. intros iv H. rewrite E in H. destruct H. Qed.
Lemma frames_lb_incl : forall PL LB LB', frames_lb PL LB -> (forall b, In b LB -> In b LB') -> frames_lb PL LB'.
Proof. intros PL LB LB' [H1 H2] HI. split; [eapply pl_frames_lb_incl; eauto | exact H2]. Qed.
Lemma frames_lb_ok : forall PL LB SPX BX, frames_lb PL LB -> ACEIL <= SPX -> BX < 2^63 -> frames_ok LB PL SPX BX.
Proof. intros PL LB SPX BX [H1 _] H2 H3. split; [exact H1 | lia]. Qed.

Definition bn_preA (Σ : rts RT) (st : ST) (m : mem) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (sp : word) (lo : Z) (stack cost : Z) : Prop :=
  AHEAP Σ OW LB m /\ lib_state st m OW PL EA /\ frames_ok LB PL (bv_unsigned sp) USTACK_TOP
  /\ stk bgbsegs m lo (bv_unsigned sp) /\ ACEIL <= lo /\ lo <= bv_unsigned sp - stack
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
  /\ mem_inv bgbsegs m
  /\ cnt_ok st OW LB /\ cost <= rt_credit RT Σ
  /\ frames_al PL /\ frames_lb PL LB.

Lemma bn_preA_F : forall Σ st m OW LB PL EA sp lo stack cost,
  BgIface.bn_preA Σ st m OW LB PL EA sp lo stack cost -> bn_preA Σ st m OW LB PL EA sp lo stack cost.
Proof.
  intros Σ st m OW LB PL EA sp lo stack cost (HEAP & LS & FROK & ST & CEIL & LOSP & TOP & AL16 & MI & CNT & CRED & FAL & NOFR).
  split; [exact HEAP|]. split; [exact LS|]. split; [exact (frames_ok_nofr LB PL _ _ FROK NOFR)|].
  do 8 (split; [assumption|]). split; [exact FAL | exact (frames_lb_nofr PL LB NOFR)].
Qed.

Lemma frames_ok_call : forall LB PL sp sp' B lo, frames_ok LB PL sp B -> ACEIL <= lo -> lo <= sp' -> sp' <= sp -> frames_ok LB PL sp' B.
Proof. intros LB PL sp sp' B lo H H1 H2 H3. eapply frames_ok_mono; [exact H| lia]. Qed.

Lemma w_lib_struct_cases : forall Σ LB m st OW PL EA SPX BX r a, AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  (exists b, In b OW /\ blk_addr b <= a /\ a + 24 <= blk_addr b + blk_size b)
  \/ (In (a, a + BN_STRUCT_SZ) (pl_frames PL) /\ exists b, In b LB /\ blk_addr b <= a /\ a + 24 <= blk_addr b + blk_size b).
Proof.
  intros Σ LB m st OW PL EA SPX BX r a HEAP PARTS FROK HA NE.
  destruct (ref_skF OW st PL EA PARTS r a HA) as [q A n HA0 NR Hin R1 R2|p S Eb Hiv HF|Er Ea]; [| | exfalso; exact (NE Er)].
  - left. exists (q, A, n). split; [exact Hin|]. cbn. lia.
  - right. split; [exact HF|]. destruct (frame_iv_blk LB PL SPX BX FROK _ HF) as (b & Hb & R1 & R2). cbn [fst snd] in R1, R2. unfold BN_STRUCT_SZ in R2.
    exists b. split; [exact Hb | lia].
Qed.

Lemma seg_heap : forall Σ st OW LB PL EA SPX m m' W lo sp,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX USTACK_TOP ->
  munch W m m' -> wmono bgbsegs m m' -> Forall (w_lib st OW PL lo sp) W -> ACEIL <= lo -> sp <= USTACK_TOP ->
  AHEAP Σ OW LB m'.
Proof.
  intros Σ st OW LB PL EA SPX m m' W lo sp HEAP PARTS FROK MU WM HW CEIL SPT. eapply AH_frame; [exact HEAP| exact MU| exact WM|].
  eapply Forall_impl; [|exact HW]. intros [x y] [[H1 H2]|[(b & Hb & H1 & H2)|(r & a & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - left. cbn. lia.
  - right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. auto.
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & b & Hb & B1 & B2)].
    + right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn. lia.
    + right; right. exists b. split; [apply in_or_app; right; exact Hb|]. cbn. lia.
Qed.

Lemma seg_ax_pres : forall Σ st OW LB PL EA SPX m m' W lo sp X,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX USTACK_TOP ->
  munch W m m' -> Forall (w_lib st OW PL lo sp) W -> ACEIL <= lo -> lo <= sp ->
  (forall b x, In b OW -> blk_addr b <= x < blk_addr b + blk_size b -> client_static x -> rin_ivs X x) ->
  (forall x, rin_ivs (pl_frames PL) x -> rin_ivs X x) ->
  ax_pres LB sp X m m'.
Proof.
  intros Σ st OW LB PL EA SPX m m' W lo sp X HEAP PARTS FROK MU HW CEIL LOSP HCS HFR. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a [HX Hc]. pose proof (AH_nodup _ _ _ _ HEAP) as ND. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
  assert (BLK : forall b, In b OW -> blk_addr b <= x -> y <= blk_addr b + blk_size b -> ~ (x <= a < y)).
  { intros b Hb H1 H2 Hx. pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & BC & BI).
    destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _); lia| |].
    + apply HX. apply (HCS b a Hb); [lia | exact Hc].
    + assert (NE : blk_id b <> blk_id b').
      { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hb']. }
      pose proof (AH_disjoint_gen _ _ _ _ b b' HEAP ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NE). lia. }
  intros Hx. destruct Hiv as [[H1 H2]|[(b & Hb & H1 & H2)|(r & a' & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
  - destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| |].
    +
      destruct Hc as [(l & h & Hin & Hr) _]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
      unfold CLIENT_STATIC, SEGTOP_A in *. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
    + pose proof (AH_range_gen _ _ _ _ b' HEAP ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & _ & BC & _). lia.
  - exact (BLK b Hb H1 H2 Hx).
  - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & _)].
    + apply (BLK b Hb); [lia| lia| exact Hx].
    +
      apply HX. apply HFR. apply rin_ivs_In. exists (a', a' + BN_STRUCT_SZ). split; [exact HF|]. cbn. unfold BN_STRUCT_SZ. lia.
Qed.

Lemma seg_ax_pres' : forall Σ st OW LB PL EA SPX m m' W lo sp,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX USTACK_TOP ->
  munch W m m' -> Forall (w_lib st OW PL lo sp) W -> ACEIL <= lo -> lo <= sp -> ax_pres LB sp (XW PL) m m'.
Proof.
  intros Σ st OW LB PL EA SPX m m' W lo sp HEAP PARTS FROK MU HW CEIL LOSP. eapply seg_ax_pres; eauto.
  - intros b x Hb Hx Hc. exfalso. eapply blk_not_static; eauto.
  - intros x Hx. unfold XW. apply rin_ivs_app. right. exact Hx.
Qed.

Lemma ref_at_inbA : forall Σ st OW LB PL EA m r a,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_lb PL LB -> ref_at st OW PL r a -> r <> ROne ->
  exists q A n, In (q, A, n) (OW ++ LB) /\ A <= a /\ a + 24 <= A + n.
Proof.
  intros Σ st OW LB PL EA m r a HEAP PARTS NOFR HA NE. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  eapply (ref_at_blk st OW PL EA ACEIL 0 Σ LB m r a HEAP PARTS); [| exact HA | exact NE].
  apply frames_lb_ok; [exact NOFR | lia | lia].
Qed.

Lemma ref_at_al8A : forall Σ st OW LB PL EA m r a,
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_lb PL LB -> ref_at st OW PL r a -> r <> ROne -> a mod 8 = 0.
Proof.
  intros Σ st OW LB PL EA m r a HEAP PARTS NOFR HA NE. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  assert (FROK : frames_ok LB PL ACEIL 0) by (apply frames_lb_ok; [exact NOFR | lia | lia]).
  destruct (ref_skF OW st PL EA PARTS r a HA) as [q0 A0 n0 HA0 NR Hin _ _|p S Eb Hiv HF|Er Ea]; [| exact (proj2 NOFR _ HF) | exfalso; exact (NE Er)].
  exact (BgIface.ref_at_al8A Σ st OW LB (pl_strip PL) EA m r a HEAP (lib_parts_strip st OW PL EA PARTS) (pl_frames_strip PL) HA0 NE).
Qed.

Lemma bn_arr_nofr : forall LB PL r m OW D b, pl_wf PL -> frames_lb PL LB -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D b -> nbuf PL r -> BnRepDefs.bn_arr m OW D b.
Proof.
  intros LB PL r m OW D b WF NOFR NE ARR NB. unfold bn_arr in ARR. unfold BnRepDefs.bn_arr. destruct (bn_d b) as [p|]; [exact ARR|].
  destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try exact ARR.
  - exfalso. exact (NB x d Ep).
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.

Lemma bn_arr_of_nofr : forall LB PL r m OW D b, pl_wf PL -> frames_lb PL LB -> r <> ROne ->
  BnRepDefs.bn_arr m OW D b -> nbuf PL r -> bn_arr m OW (pl_of PL r) D b.
Proof.
  intros LB PL r m OW D b WF NOFR NE ARR NB. unfold BnRepDefs.bn_arr in ARR. unfold bn_arr. destruct (bn_d b) as [p|]; [exact ARR|].
  destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try exact ARR.
  - exfalso. exact (NB x d Ep).
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.

Lemma bn_arr_sh : forall Σ OW LB m st PL EA SPX BX r D, AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX BX -> frames_al PL ->
vref r st -> r <> ROne -> bn_arr m OW (pl_of PL r) D (getbn r st) ->
  acc bgbsegs m D (8 * Z.of_nat (bn_dmax (getbn r st))) /\ D mod 8 = 0 /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= SHLO \/ SHHI <= D).
Proof.
intros Σ OW LB m st PL EA SPX BX r D HEAP PARTS FROK FAL HV HNO HArr. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB). unfold bn_arr in HArr. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
  - destruct HArr as [Hin _]. assert (INX : In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) (OW ++ LB)) by (apply in_or_app; left; exact Hin).
    split; [exact (AH_acc_in _ _ _ _ (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) D (8 * Z.of_nat (bn_dmax (getbn r st))) HEAP INX ltac:(cbn [blk_addr blk_size fst snd]; lia) ltac:(cbn [blk_addr blk_size fst snd]; lia))|].
    pose proof (AH_okA _ _ _ _ _ _ _ HEAP Hin) as [H16 _].
    split; [clear - H16; Z.div_mod_to_equations; lia|].
    pose proof (AH_offsh _ _ _ _ (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) HEAP INX) as OX. cbn [blk_addr blk_size fst snd] in OX. lia.
  - assert (EMP : D = 0 /\ bn_buf (getbn r st) = [] ->
      acc bgbsegs m D (8 * Z.of_nat (bn_dmax (getbn r st))) /\ D mod 8 = 0 /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= SHLO \/ SHHI <= D)).
    { intros [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length Z.of_nat]. split; [intros i Hi; lia|]. split; [reflexivity|]. left. unfold SHLO. lia. }
    destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try (apply EMP; exact HArr).
    + destruct HArr as (-> & HU & HL).
      destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      destruct (frame_iv_blk LB PL SPX BX FROK _ HFd) as (b & Hb & R1 & R2). cbn [fst snd] in R1, R2.
      assert (INX : In b (OW ++ LB)) by (apply in_or_app; right; exact Hb).
      unfold bn_dmax. rewrite HL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unfold TMOD_BUF_SZ in *.
      split; [exact (AH_acc_in _ _ _ _ b d 16 HEAP INX R1 ltac:(lia))|]. split; [exact (FAL _ HFd)|].
      pose proof (AH_offsh _ _ _ _ b HEAP INX) as OX. lia.
    + exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
      pose proof (proj1 PWF r _ Eb) as (_ & _ & _ & F). exact F.
Qed.

Lemma bn_arr_blk : forall Σ OW LB m PL SPX BX r D (b : BN), AHEAP Σ OW LB m -> pl_wf PL -> frames_ok LB PL SPX BX -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D b -> (0 < bn_dmax b)%nat ->
  exists bk, In bk (OW ++ LB) /\ blk_addr bk <= D /\ D + 8 * Z.of_nat (bn_dmax b) <= blk_addr bk + blk_size bk /\ 0 < D /\ D + 8 * Z.of_nat (bn_dmax b) <= ACEIL.
Proof.
  intros Σ OW LB m PL SPX BX r D b HEAP PWF FROK NE ARR HD. unfold bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. exists (p, D, 8 * Z.of_nat (bn_dmax b)). cbn [blk_addr blk_size fst snd].
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & _).
    split; [apply in_or_app; left; exact Hin|]. split; [lia|]. split; [lia|]. split; [exact B0 | exact BC].
  - assert (EMP : D = 0 /\ bn_buf b = [] -> False) by (intros [_ Eb]; unfold bn_dmax in HD; rewrite Eb in HD; cbn in HD; lia).
    destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try (exfalso; apply EMP; exact ARR).
    + destruct ARR as (-> & _ & HL).
      destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      destruct (frame_iv_blk LB PL SPX BX FROK _ HFd) as (bk & Hb & R1 & R2). cbn [fst snd] in R1, R2.
      destruct (frame_iv_range Σ OW LB m HEAP PL SPX BX FROK _ HFd) as (P0 & C0 & _). cbn [fst snd] in P0, C0.
      exists bk. unfold bn_dmax. rewrite HL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unfold TMOD_BUF_SZ in *.
      split; [apply in_or_app; right; exact Hb|]. split; [lia|]. split; [lia|]. split; [lia | lia].
    + exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
      exact (proj2 (proj2 (proj2 (proj1 PWF r _ Eb)))).
Qed.

Lemma xw_stack_out : forall Σ OW LB m PL SPX BX a, AHEAP Σ OW LB m -> frames_ok LB PL SPX BX -> ACEIL <= a -> ~ rin_ivs (XW PL) a.
Proof.
  intros Σ OW LB m PL SPX BX a HEAP FROK Ha. unfold XW. rewrite rin_ivs_app. intros [H|H].
  - pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. revert H.
    unfold LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold BnHeapA.ACEIL in *. lia.
  - apply rin_ivs_In in H. destruct H as (iv & Hiv & Hx).
    destruct (frame_iv_range Σ OW LB m HEAP PL SPX BX FROK iv Hiv) as (_ & C & _). lia.
Qed.

Lemma xw_clientF : forall Σ OW m PL LB SP SPX BX x, AHEAP Σ OW LB m -> frames_ok LB PL SPX BX -> ACEIL <= SP -> SP <= x < USTACK_TOP -> ax_client LB SP (XW PL) x.
Proof.
  intros Σ OW m PL LB SP SPX BX x HEAP FROK H1 H2. split; [| left; exact H2]. apply (xw_stack_out Σ OW LB m PL SPX BX x HEAP FROK). lia.
Qed.

Definition w_own (LB : list block) (PL : placement) (iv : Z * Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b /\ forall x, fst iv <= x < snd iv -> ~ rin_ivs (pl_frames PL) x.

Theorem lib_state_frame_lb : forall s LB SPX BX cxo hs st m m' OW PL EA W,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> munch W m m' -> wmono bgbsegs m m' -> frames_ok LB PL SPX BX ->
  Forall (fun iv => w_okc OW LB st PL EA SPX cxo hs iv \/ w_own LB PL iv) W -> lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA W HEAP HS MU WM FROK HW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
  intros a Ha. clear MU WM. induction HW as [|[lo hi] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [| exact IH].
  destruct Hiv as [Hiv|(b & Hb & B1 & B2 & NF)].
  - assert (FW : Forall (w_okc OW LB st PL EA SPX cxo hs) [(lo, hi)]) by (constructor; [exact Hiv | constructor]).
    pose proof (own_fp_outside s OW LB m HEAP st PL EA SPX BX PARTS FROK cxo hs [(lo, hi)] a FW Ha) as O. cbn [outside] in O. tauto.
  - cbn [fst snd] in *. intros Hx.
    destruct (BgLayer.own_fp_block OW st PL EA PARTS cxo hs a Ha) as [HL|[(q & A & n & Hq & Hxq & _)|(iv & Hiv & Hxi)]].
    + pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & BI).
      revert HL. unfold libw, LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia.
    + pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
      assert (NE : blk_id (q, A, n) <> blk_id b).
      { intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [rewrite <- E; apply in_map; exact Hq | apply in_map; exact Hb]. }
      pose proof (AH_disjoint_gen _ _ _ _ (q, A, n) b HEAP ltac:(apply in_or_app; left; exact Hq) ltac:(apply in_or_app; right; exact Hb) NE) as DJ.
      cbn [blk_addr blk_size fst snd] in DJ. lia.
    + apply (NF a Hx). apply rin_ivs_In. exists iv. split; [exact Hiv | exact Hxi].
Qed.

End WithRT.

Ltac xw_client_stack FROK :=
  lazymatch goal with
  | H : BnHeapA.AHEAP ?S ?OW ?LB ?m |- ax_client ?LB ?SP _ ?x =>
      apply (xw_clientF S OW m _ LB SP _ _ x H FROK); [unfold BnHeapA.ACEIL in *; lia | unfold USTACK_TOP in *; lia]
  end.
Notation bn_preAF := bn_preA.
Arguments bn_arr_nofr {LB} PL r m OW D b.
Arguments bn_arr_of_nofr {LB} PL r m OW D b.
