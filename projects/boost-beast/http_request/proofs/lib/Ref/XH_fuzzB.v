(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt CXXRep CXXLib CXXLib2 HeapSR_iface CXXHeap
     XRep XE_kit XA_leaves F_memset XA_alloc XS_sp XA_registry XA_sched_ctor2 XA_sched_ctor5 XS_ctor XS_ctor2 XFuzz_stmt XFuzz_stmt2 XH_fuzzA.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim STree Malloc Prog.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 Set StepFast.sf_check := true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac hp_frame HPRES P :=
  repeat match goal with
  | Hc : rw_cells rsegs ?mm (P + _) _ |- _ =>
      lazymatch type of HPRES with rheap_pres _ _ mm _ => apply (rheap_pres_rw_cells _ _ _ _ _ _ HPRES) in Hc; [| left; cbn; lia] end
  | Hc : rw_cells rsegs ?mm P _ |- _ =>
      lazymatch type of HPRES with rheap_pres _ _ mm _ => apply (rheap_pres_rw_cells _ _ _ _ _ _ HPRES) in Hc; [| left; cbn; lia] end
  end.
(* [comment removed for export] *)
Ltac szs := unfold NEWSZ_REG, NEWSZ_CFG, NEWSZ_SCH, SZ_ALLOCIMPL, NEWSZ_SSVC, SZ_SPCI_IMPL, SZ_SPCI_STATE, SZ_BS, SZ_IOC, SZ_FB in *.
Ltac xclient_frame := split; [left; cbn; lia| repeat (apply Forall_cons; [cbn; szs; lia|]); apply Forall_nil].
Ltac xp_frame XP P :=
  repeat match goal with
  | Hc : rw_cells rsegs ?mm (P + _) _ |- _ =>
      lazymatch type of XP with xpres _ _ _ mm _ => eapply (xpres_rw_cells _ _ _ _ _) in Hc; [| exact XP| xclient_frame] end
  | Hc : rw_cells rsegs ?mm P _ |- _ =>
      lazymatch type of XP with xpres _ _ _ mm _ => eapply (xpres_rw_cells _ _ _ _ _) in Hc; [| exact XP| xclient_frame] end
  end.
(* [comment removed for export] *)
Ltac mu_frame MU WM P :=
  repeat match goal with
  | Hc : rw_cells rsegs ?mm (P + _) _ |- _ =>
      lazymatch type of MU with munch _ mm ?m' => eapply (rw_cells_transport rsegs _ mm m') in Hc; [| exact MU| exact WM| cbn; lia] end
  | Hc : rw_cells rsegs ?mm P _ |- _ =>
      lazymatch type of MU with munch _ mm ?m' => eapply (rw_cells_transport rsegs _ mm m') in Hc; [| exact MU| exact WM| cbn; lia] end
  end.


Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fzX (P : Z) (NEW : list block) (a : Z) : Prop :=
  (hceil <= a < P + 512) \/ (exists b, In b NEW /\ blk_addr b <= a < blk_addr b + blk_size b).

Lemma rin_ivs_XH : forall a, rin_ivs XH_X a <-> XH_LO <= a < XH_HI.
Proof. intros a. unfold XH_X. cbn. tauto. Qed.

Section W.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma fzX_not_client : forall s NEW LB m1 P a,
    hs_RHEAP H s (NEW ++ LB) m1 -> hceil <= P + 512 ->
    rclient_addr LB (P + 512) a -> fzX P NEW a -> False.
  Proof.
    intros s NEW LB m1 P a HP CE HC [K|(b & Hb & K)].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [lia| hcb; lia|].
      assert (INb : In b (NEW ++ LB)) by (apply in_or_app; right; exact Hb).
      pose proof (hh_blocks H HH _ _ _ _ HP INb) as (_ & _ & _ & R4 & _). lia.
    - pose proof (fresh_outside_gen H HH _ _ _ _ _ _ _ HP Hb CE HC). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xp_lift : forall s NEW LB m1 m0 m m' P SP X,
    xpres LB (P + 512) XH_X m0 m ->
    xpres (NEW ++ LB) SP X m m' -> SP <= P + 512 -> hceil <= P + 512 ->
    hs_RHEAP H s (NEW ++ LB) m1 ->
    (forall a, rin_ivs X a -> fzX P NEW a \/ (XH_LO <= a < XH_HI)) ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s NEW LB m1 m0 m m' P SP X X0 XP LE CE HP HX.
    eapply xpres_trans; [exact X0|]. intros a Ha [HC NX]. apply XP; [exact Ha|]. split.
    - destruct HC as [K|[K|(b & Hb & K)]]; [left; lia| right; left; exact K| right; right].
      exists b. split; [apply in_or_app; right; exact Hb| exact K].
    - intros R. destruct (HX a R) as [K|K].
      + exact (fzX_not_client _ _ _ _ _ _ HP CE HC K).
      + apply NX. apply rin_ivs_XH. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma xp_lift_heap : forall s NEW LB m1 m0 m m' P SP,
    xpres LB (P + 512) XH_X m0 m ->
    rheap_pres (NEW ++ LB) SP m m' -> SP <= P + 512 -> hceil <= P + 512 ->
    hs_RHEAP H s (NEW ++ LB) m1 ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s NEW LB m1 m0 m m' P SP X0 RP LE CE HP.
    eapply (xp_lift s NEW LB m1 m0 m m' P SP []); [exact X0| apply xpres_of_heap_pres; exact RP| exact LE| exact CE| exact HP|].
    intros a [].
  Qed.

  (* [comment removed for export] *)
  Lemma xp_lift_munch : forall s NEW LB m1 m0 m m' P W,
    xpres LB (P + 512) XH_X m0 m ->
    munch W m m' -> wmono rsegs m m' -> hceil <= P + 512 ->
    hs_RHEAP H s (NEW ++ LB) m1 ->
    Forall (fun iv : Z * Z => forall a, fst iv <= a < snd iv -> fzX P NEW a \/ (XH_LO <= a < XH_HI)) W ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s NEW LB m1 m0 m m' P W X0 MU WM CE HP FW.
    eapply xpres_trans; [exact X0|]. eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC NX]. clear MU WM X0. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as F1. cbn in F1. split; [| apply IH; exact (Forall_inv_tail FW)].
    intros R. destruct (F1 a R) as [K|K].
    - exact (fzX_not_client _ _ _ _ _ _ HP CE HC K).
    - apply NX. apply rin_ivs_XH. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma xp_lift_free : forall s NEW LB m1 m0 m m' P SP p A n,
    xpres LB (P + 512) XH_X m0 m ->
    hs_RHEAP H s (NEW ++ LB) m1 -> In (p, A, n) NEW ->
    rheap_pres (hs_lb_remove H p (NEW ++ LB)) SP m m' -> SP <= P + 512 -> hceil <= P + 512 ->
    xpres LB (P + 512) XH_X m0 m'.
  Proof.
    intros s NEW LB m1 m0 m m' P SP p A n X0 HP IN RP LE CE.
    eapply (xp_lift s NEW LB m1 m0 m m' P SP [(A, A + n)]); [exact X0| | exact LE| exact CE| exact HP|].
    - eapply (xpres_free H HH); [exact HP| apply in_or_app; left; exact IN| exact RP|]. intros a Ha. cbn. left. exact Ha.
    - intros a [R|[]]. left. right. exists (p, A, n). split; [exact IN| cbn; cbn in R; lia].
  Qed.
End W.

(* [comment removed for export] *)
Lemma XImg_xpres0 : forall LB P m0 m, XImg m0 -> xpres LB (P + 512) XH_X m0 m -> XImg m.
Proof.
  intros LB P m0 m XI XP. eapply XImg_agree; [exact XI|]. intros a Ha.
  destruct (XP a) as [E _]; [unfold XRELRO_LO, XRELRO_HI, XDATA_LO, XDATA_HI in Ha; lia| | exact E].
  split; [right; left| rewrite rin_ivs_XH; unfold XH_LO, XH_HI, XRELRO_LO, XRELRO_HI, XDATA_LO, XDATA_HI in *; lia].
  unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK, XRELRO_LO, XRELRO_HI, XDATA_LO, XDATA_HI in *. lia.
Qed.

Lemma XStatics_xpres0 : forall LB P m0 m, XImg m0 -> xpres LB (P + 512) XH_X m0 m -> XStatics m.
Proof. intros LB P m0 m XI XP. apply XStatics_of_XImg. eapply XImg_xpres0; eassumption. Qed.


(* [comment removed for export] *)
Lemma HStat_xpres_keep : forall FT LB SP X m m',
  ft_local FT -> HStat FT m -> xpres LB SP X m m' -> (forall a, XH_LO <= a < XH_HI -> ~ rin_ivs X a) -> HStat FT m'.
Proof.
  intros FT LB SP X m m' FL HS XP NX. eapply HStat_agree; [exact FL| exact HS|].
  intros a Ha. destruct (XP a) as [E _]; [unfold XH_LO, XH_HI in Ha; lia| | exact E].
  split; [| exact (NX a Ha)]. right; left.
  unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK, XH_LO, XH_HI in *. lia.
Qed.

Lemma HStat_munch_keep : forall FT W m m',
  ft_local FT -> HStat FT m -> munch W m m' -> Forall (fun iv : Z * Z => snd iv <= XH_LO \/ XH_HI <= fst iv) W -> HStat FT m'.
Proof.
  intros FT W m m' FL HS MU FW. eapply HStat_agree; [exact FL| exact HS|].
  intros a Ha. unfold wa. apply MU. rewrite unsigned_lit by (unfold XH_LO, XH_HI in Ha; lia).
  clear MU HS. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as F1. cbn in F1.
  split; [lia| apply IH; exact (Forall_inv_tail FW)].
Qed.

(* [comment removed for export] *)
Section W2.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma payload_xpres0 : forall s NEW LB m1 m0 m P D N ds,
    bytes_at rsegs m0 D ds -> Z.of_nat (length ds) = N ->
    (1 <= N -> exists pD, In (pD, D, N) LB) ->
    hs_RHEAP H s (NEW ++ LB) m1 ->
    xpres LB (P + 512) XH_X m0 m -> bytes_at rsegs m D ds.
  Proof.
    intros s NEW LB m1 m0 m P D N ds SRC LEN INB HP XP.
    destruct (Z_lt_le_dec N 1) as [N0|N1].
    - destruct ds; [| cbn in LEN; lia]. eapply bytes_at_nil_any. exact SRC.
    - destruct (INB N1) as [pD IND].
      assert (IN2 : In (pD, D, N) (NEW ++ LB)) by (apply in_or_app; right; exact IND).
      pose proof (hh_blocks H HH _ _ _ _ HP IN2) as (R1 & R2 & R3 & R4 & R5). cbn in R1, R4, R5.
      eapply xpres_bytes_at; [exact XP| exact SRC|]. rewrite LEN. split.
      + right; right. exists (pD, D, N). split; [exact IND| cbn; lia].
      + unfold XH_X, XH_LO, XH_HI. constructor; [cbn; lia| constructor].
  Qed.
End W2.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fz_LB1 (p1 : bptr) (allocb : Z) (p2 : bptr) (regb : Z) (p3 : bptr) (cfgb : Z) (p4 : bptr) (schedb : Z) (LB : list block) : list block :=
  (p4, schedb, NEWSZ_SCH) :: (p3, cfgb, NEWSZ_CFG) :: (p2, regb, NEWSZ_REG) :: (p1, allocb, SZ_ALLOCIMPL) :: LB.

(* [comment removed for export] *)
Lemma ro_cell0 : forall m A c cs, rw_cells rsegs m A (c :: cs) -> ro_cells rsegs m A [c].
Proof.
  intros m A c cs RC. pose proof (rw_cells_ro_cell _ _ _ _ 0 c RC eq_refl) as R. cbn [Z.of_nat] in R.
  rewrite Z.add_0_r in R. exact R.
Qed.

Section W.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis RHEAP_canary : forall s LB m, hs_RHEAP H s LB m -> CanaryReads m.
  Variable FT : mem -> Prop.
  Hypothesis FT_local : ft_local FT.

  (* [comment removed for export] *)
  Definition fz_pure (P D N lo B : Z) (ra : word) (LB : list block) : Prop :=
    P mod 16 = 0 /\ hceil <= lo /\ lo + FUZZ_STACK <= P + 512 /\ P + 512 <= B /\ B < 2^64 /\ P + 512 <= 0x7fffffffffff
    /\ bv_unsigned ra mod 2 = 0 /\ 0 <= N < 2^26 /\ D mod 16 = 0 /\ 0 <= D /\ D + N <= 2^64
    /\ (1 <= N -> exists pD, In (pD, D, N) LB) /\ (N = 0 -> D = P_FUZZ_EMPTY)
    /\ lb_bytes LB + FUZZ_LIVE2 <= hs_LIVE_MAX H /\ Z.of_nat (length LB) + FUZZ_CNT <= hs_LIVE_CNT_MAX H.

  Definition fzK1 (gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P D N lo B : Z) (ra s0 s1 s2 : word) (LB : list block) (m0 : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m (s' : PState) (errv : word)
                    (p1 : bptr) (allocb : Z) (p2 : bptr) (regb : Z) (p3 : bptr) (cfgb : Z) (p4 : bptr) (schedb : Z) (j351 j32 : list byte),
      cfg_ms c = MS (mkR (Z_to_bv 64 P_FZ_RET_SCT) (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 D)
                         (Z_to_bv 64 (P + 352)) (Z_to_bv 64 (P + 384)) (Z_to_bv 64 D) (Z_to_bv 64 N) a4 a5 a6 a7
                         (Z_to_bv 64 u64max) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_STREAM_CTOR) fc None m (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m /\ stk rsegs m lo P
      /\ rw_cells rsegs m (errno_addr tp) [C4 errv] /\ hs_rauxv_ok H m B
      /\ hs_RHEAP H s' (fz_LB1 p1 allocb p2 regb p3 cfgb p4 schedb LB) m
      /\ IoWorld2 (fz_LB1 p1 allocb p2 regb p3 cfgb p4 schedb LB) m (P + 384) allocb regb cfgb schedb
      /\ rw_cells rsegs m P [CB 1 [b8 0]; CB 351 j351] /\ rw_cells rsegs m (P + 352) [CB 32 j32]
      /\ rw_cells rsegs m (P + 408) (FlatBufCells FB_empty) /\ rw_cells rsegs m (P + 456) (ErrCodeCells EC_clear)
      /\ rw_cells rsegs m (P + 480) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ HStat FT m
      /\ xpres LB (P + 512) XH_X m0 m.

  Lemma fz_AB : forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (P D N lo B : Z) (ds : list byte) (errv : word),
    fz_pure P D N lo B ra LB ->
    bytes_at rsegs m D ds -> Z.of_nat (length ds) = N ->
    hs_RHEAP H s LB m -> hs_KREL H s mo -> hs_rauxv_ok H m B ->
    stk rsegs m lo (P + 512) ->
    rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
    XImg m -> HStat FT m ->
    F = bvmap_empty -> fc = Z_to_bv 32 0 ->
    hs_SR H (fzK1 gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P D N lo B ra s0 s1 s2 LB m mo)
      (mkCfg (MS (mkR ra (Z_to_bv 64 (P + 512)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 N) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 P_FUZZ) fc None m (seg_rom rsegs)) mo).
  Proof.
    intros until errv. intros PU SRC LEN HP KREL AUX ST ERR MI TP XI HS FZ1 FZ2.
    pose proof PU as (AL & CEIL & LO & PB & BHI & P47 & RAE & NR & DAL & D0 & DNH & INB & DEMP & BUD & BUDC).
    unfold FUZZ_STACK in LO. unfold FUZZ_LIVE2 in BUD. unfold FUZZ_CNT in BUDC. hcb.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = RERRNO) by (unfold RATP, RERRNO; rewrite unsigned_lit; lia).
    subst tp. rewrite EA in ERR.
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= hceil).
    { intros b Hb. destruct (hh_blocks H HH _ _ _ b HP Hb) as (_ & _ & _ & H4 & _). exact H4. }
    pose proof (xpres_refl LB (P + 512) XH_X m) as XP0.
    (* [comment removed for export] *)
    eapply (hh_evt_then H HH); [exact KREL| |].
    { eapply fzA; [exact ST| lia| exact CEIL| lia| exact MI]. }
    intros ms1 PO. unfold fzA_post in PO.
    destruct PO as (x0 & x1 & x2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m1 & jA & -> & MU & WM & MI1 & ST1 & FRP & FB1 & EC1 & SAV1).
    (* [comment removed for export] *)
    eapply (rw_cells_transport rsegs _ m m1) in ERR; [| exact MU| exact WM| unfold RERRNO in *; cbn; lia].
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (hh_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL in *. constructor; [cbn; lia| constructor]. }
    assert (XP1 : xpres LB (P + 512) XH_X m m1).
    { eapply (xp_lift_munch H HH s [] LB m1); [exact XP0| exact MU| exact WM| lia| exact HP1|].
      constructor; [| constructor]. cbn. intros a Ha. left. left. lia. }
    assert (HS1 : HStat FT m1).
    { eapply HStat_munch_keep; [exact FT_local| exact HS| exact MU|]. constructor; [cbn; unfold XH_LO, XH_HI; lia| constructor]. }
    clear MU WM MI ST AUX HS.
    (* [comment removed for export] *)
    pose proof (hh_opnew H HH) as OP. unfold opnew_sr_stmt, malloc_sr_stmt_at in OP.
    eapply (hh_seq H HH).
    { eapply OP with (lo := lo) (B := B) (LB := LB) (s := s) (n := 16); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ unfold ROPNEW_STACK, RMALLOC_STACK; lia | lia | exact MI1 | exact ST1 | exact KREL | rewrite EA; exact ERR | exact HP1 | exact AUX1 ].
      eapply (hh_alloc H HH); [exact HP1| lia| lia| lia]. }
    intros [ms2 mo2] PO. unfold malloc_sr_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m2 & errv2 & allocb & jal & p1 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BRA & HEAP2 & BLKA).
    rewrite (unsigned_lit P) in ST2, HPRES by lia. rewrite EA in ERR2.
    hp_frame HPRES P.
    pose proof BRA as (A1 & A2 & _ & A4 & A5).
    assert (XP2 : xpres LB (P + 512) XH_X m m2).
    { eapply (xp_lift_heap H HH s [] LB m1); [exact XP1| exact HPRES| lia| lia| exact HP1]. }
    assert (HS2 : HStat FT m2).
    { eapply (HStat_xpres_keep FT LB P []); [exact FT_local| exact HS1| exact HPRES || apply xpres_of_heap_pres; exact HPRES| intros a _ []]. }
    clear HP1 AUX1 MI1 ST1 XP1 HS1 ERR OP.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_NEW)) with (Z_to_bv 64 P_FZ_RET_NEW)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_NEW; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL2| |].
    { eapply fzB1; [exact FRP| lia| lia| exact BLKA| lia| lia| exact MI2]. }
    intros ms3 PO. unfold fzB1_post in PO.
    destruct PO as (m3 & j344 & j32 & j16 & j8 & -> & MU & WM & MI3 & FRP3 & FRS3 & FRI3 & BA3). clear FRP.
    (* [comment removed for export] *)
    eapply (rw_cells_transport rsegs _ m2 m3) in ERR2; [| exact MU| exact WM| unfold RERRNO in *; cbn; lia].
    mu_frame MU WM P.
    eapply (stk_transport_disjoint rsegs _ m2 m3) in ST2; [| exact MU| exact WM| cbn; lia].
    assert (HP3 : hs_RHEAP H s2' ((p1, allocb, 16) :: LB) m3).
    { eapply (hh_RHEAP_frame H HH); [exact HEAP2| exact MU| exact WM|].
      constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor].
      right; right. exists (p1, allocb, 16). split; [left; reflexivity| cbn; lia]. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX2| exact MU| exact WM|]. unfold RAUXV_CELL in *.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    assert (XP3 : xpres LB (P + 512) XH_X m m3).
    { eapply (xp_lift_munch H HH s2' [(p1, allocb, 16)] LB m3); [exact XP2| exact MU| exact WM| lia| exact HP3|].
      constructor; [cbn; intros a Ha; left; left; lia|]. constructor; [cbn; intros a Ha; left; left; lia|]. constructor; [| constructor].
      cbn. intros a Ha. left. right. exists (p1, allocb, 16). split; [left; reflexivity| cbn; lia]. }
    assert (HS3 : HStat FT m3).
    { eapply HStat_munch_keep; [exact FT_local| exact HS2| exact MU|]. unfold XH_LO, XH_HI.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    assert (AI3 : AllocImpl ((p1, allocb, 16) :: LB) m3 allocb).
    { exists p1, j8. split; [left; reflexivity| exact BA3]. }
    clear MU WM MI2 AUX2 XP2 HS2 HEAP2 HPRES.
    (* [comment removed for export] *)
    pose proof (alloc_obj_registry_spec H HH RHEAP_canary) as AR. unfold alloc_obj_registry_stmt in AR.
    eapply (hh_seq H HH).
    { eapply AR with (AT := P) (ioc := P + 384) (allocb := allocb) (lo := lo) (B := B) (LB := (p1, allocb, 16) :: LB) (s := s2');
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI3 | exact ST2 | exact KREL2 | rewrite EA; exact ERR2 | exact HP3 | exact AUX3 | exact AI3
                     | unfold P_FZ_RET_REG; cbn; lia ].
      - exact (ro_cell0 _ _ _ _ FRP3).
      - eapply XStatics_xpres0; [exact XI| exact XP3].
      - rewrite lb_bytes_cons. cbn [blk_size snd]. unfold NEWSZ_REG. lia.
      - unfold ALLOC_OBJ_REGISTRY_STACK, ALLOCATE_STACK, ROPNEW_STACK, RMALLOC_STACK. lia. }
    intros [ms4 mo4] PO. unfold alloc_obj_registry_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0' & u1' & u2' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & u3' & u4' & u5' & u6' & m4 & errv4 & s4' & p2 & regb &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & BRR & HEAP4 & REG4 & AI4 & XS4 & XPC).
    rewrite (unsigned_lit P) in ST4, XPC by lia. rewrite EA in ERR4.
    apply (hh_mpres_trans H HH _ _ _ MP2) in MP4. clear MP2.
    xp_frame XPC P.
    pose proof BRR as (R1 & R2 & _ & R4 & R5). unfold NEWSZ_REG in R4, R5.
    assert (XP4 : xpres LB (P + 512) XH_X m m4).
    { eapply (xp_lift H HH s2' [(p1, allocb, 16)] LB m3); [exact XP3| exact XPC| lia| lia| exact HP3| intros a []]. }
    assert (HS4 : HStat FT m4).
    { eapply (HStat_xpres_keep FT _ P []); [exact FT_local| exact HS3| exact XPC| intros a _ []]. }
    clear MI3 ST2 ERR2 AUX3 HP3 XP3 HS3 AI3 AR XPC BA3.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_REG)) with (Z_to_bv 64 P_FZ_RET_REG)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_REG; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL4| |].
    { eapply fzB2; [exact FRP3| reflexivity| exact FRI3| lia| lia| exact MI4]. }
    intros ms5 PO. unfold fzB2_post in PO.
    destruct PO as (m5 & j348 & j8' & -> & MU & WM & MI5 & FRP5 & FRI5). clear FRP3 FRI3.
    (* [comment removed for export] *)
    eapply (rw_cells_transport rsegs _ m4 m5) in ERR4; [| exact MU| exact WM| unfold RERRNO in *; cbn; lia].
    mu_frame MU WM P.
    eapply (stk_transport_disjoint rsegs _ m4 m5) in ST4; [| exact MU| exact WM| cbn; lia].
    assert (HP5 : hs_RHEAP H s4' ((p2, regb, NEWSZ_REG) :: (p1, allocb, 16) :: LB) m5).
    { eapply (hh_RHEAP_frame H HH); [exact HEAP4| exact MU| exact WM|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX5 : hs_rauxv_ok H m5 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX4| exact MU| exact WM|]. unfold RAUXV_CELL in *. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    assert (XP5 : xpres LB (P + 512) XH_X m m5).
    { eapply (xp_lift_munch H HH s4' [(p2, regb, NEWSZ_REG); (p1, allocb, 16)] LB m5); [exact XP4| exact MU| exact WM| lia| exact HP5|].
      constructor; [cbn; intros a Ha; left; left; lia|]. constructor; [cbn; intros a Ha; left; left; lia| constructor]. }
    assert (HS5 : HStat FT m5).
    { eapply HStat_munch_keep; [exact FT_local| exact HS4| exact MU|]. unfold XH_LO, XH_HI. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    eapply (Registry_transport _ _ m4 m5) in REG4; [| exact MU| exact WM| unfold NEWSZ_REG; cbn; lia].
    eapply (AllocImpl_transport _ _ m4 m5) in AI4; [| exact MU| exact WM| unfold SZ_ALLOCIMPL; cbn; lia].
    clear MU WM MI4 AUX4 XP4 HS4 HEAP4 XS4.
    (* [comment removed for export] *)
    pose proof (make_svc_config_spec H HH) as MC. unfold make_svc_config_stmt in MC.
    eapply (hh_seq H HH).
    { eapply MC with (r := regb) (hintp := P) (ioc := P + 384) (allocb := allocb) (lo := lo) (B := B)
                     (LB := (p2, regb, NEWSZ_REG) :: (p1, allocb, 16) :: LB) (s := s4');
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI5 | exact ST4 | exact KREL4 | rewrite EA; exact ERR4 | exact HP5 | exact AUX5 | exact AI4 | exact REG4
                     | unfold P_FZ_RET_CFG; cbn; lia ].
      - exact (ro_cell0 _ _ _ _ FRI5).
      - exact (ro_cell0 _ _ _ _ FRP5).
      - eapply XStatics_xpres0; [exact XI| exact XP5].
      - rewrite !lb_bytes_cons. cbn [blk_size snd]. unfold NEWSZ_REG, NEWSZ_CFG. lia.
      - unfold MAKE_SVC_CONFIG_STACK, ALLOCATE_STACK, ROPNEW_STACK, RMALLOC_STACK. lia. }
    intros [ms6 mo6] PO. unfold make_svc_config_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m6 & errv6 & s6' & p3 & cfgb &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & BRC & HEAP6 & CFG6 & REG6 & AI6 & XS6 & XPC).
    rewrite (unsigned_lit P) in ST6, XPC by lia. rewrite EA in ERR6.
    apply (hh_mpres_trans H HH _ _ _ MP4) in MP6. clear MP4.
    xp_frame XPC P.
    pose proof BRC as (Y1 & Y2 & _ & Y4 & Y5). unfold NEWSZ_CFG in Y4, Y5.
    assert (XP6 : xpres LB (P + 512) XH_X m m6).
    { eapply (xp_lift H HH s4' [(p2, regb, NEWSZ_REG); (p1, allocb, 16)] LB m5); [exact XP5| exact XPC| lia| lia| exact HP5|].
      intros a [R|[]]. left. right. exists (p2, regb, NEWSZ_REG). split; [left; reflexivity| cbn in R |- *; lia]. }
    assert (HS6 : HStat FT m6).
    { eapply (HStat_xpres_keep FT _ P _); [exact FT_local| exact HS5| exact XPC|]. intros a Ha [R|[]]. cbn in R. unfold NEWSZ_REG in R. unfold XH_LO, XH_HI in Ha. lia. }
    clear MI5 ST4 ERR4 AUX5 HP5 XP5 HS5 AI4 REG4 MC XPC.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_CFG)) with (Z_to_bv 64 P_FZ_RET_CFG)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_CFG; lia| reflexivity]).
    eapply (hh_evt_then H HH); [exact KREL6| |].
    { eapply fzB3; [exact FRP5| reflexivity| exact FRI5| lia| lia| lia| exact MI6]. }
    intros ms7 PO. unfold fzB3_post in PO.
    destruct PO as (m7 & j351 & -> & MU & WM & MI7 & FRP7). clear FRP5.
    (* [comment removed for export] *)
    eapply (rw_cells_transport rsegs _ m6 m7) in ERR6; [| exact MU| exact WM| unfold RERRNO in *; cbn; lia].
    mu_frame MU WM P.
    eapply (stk_transport_disjoint rsegs _ m6 m7) in ST6; [| exact MU| exact WM| cbn; lia].
    assert (HP7 : hs_RHEAP H s6' ((p3, cfgb, NEWSZ_CFG) :: (p2, regb, NEWSZ_REG) :: (p1, allocb, 16) :: LB) m7).
    { eapply (hh_RHEAP_frame H HH); [exact HEAP6| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX7 : hs_rauxv_ok H m7 B).
    { eapply (hh_rauxv_frame H HH); [exact AUX6| exact MU| exact WM|]. unfold RAUXV_CELL in *. constructor; [cbn; lia| constructor]. }
    assert (XP7 : xpres LB (P + 512) XH_X m m7).
    { eapply (xp_lift_munch H HH s6' [(p3, cfgb, NEWSZ_CFG); (p2, regb, NEWSZ_REG); (p1, allocb, 16)] LB m7); [exact XP6| exact MU| exact WM| lia| exact HP7|].
      constructor; [cbn; intros a Ha; left; left; lia| constructor]. }
    assert (HS7 : HStat FT m7).
    { eapply HStat_munch_keep; [exact FT_local| exact HS6| exact MU|]. unfold XH_LO, XH_HI. constructor; [cbn; lia| constructor]. }
    eapply (Registry_transport _ _ m6 m7) in REG6; [| exact MU| exact WM| unfold NEWSZ_REG; cbn; lia].
    eapply (AllocImpl_transport _ _ m6 m7) in AI6; [| exact MU| exact WM| unfold SZ_ALLOCIMPL; cbn; lia].
    eapply (ConfigSvc_transport _ _ m6 m7) in CFG6; [| exact MU| exact WM| unfold NEWSZ_CFG; cbn; lia].
    clear MU WM MI6 AUX6 XP6 HS6 HEAP6 XS6.
    (* [comment removed for export] *)
    pose proof (make_svc_sched_spec H HH RHEAP_canary) as MSC. unfold make_svc_sched_stmt in MSC.
    eapply (hh_seq H HH).
    { eapply MSC with (regb := regb) (ownp := P) (ioc := P + 384) (cfgb := cfgb) (allocb := allocb) (lo := lo) (B := B)
                      (LB := (p3, cfgb, NEWSZ_CFG) :: (p2, regb, NEWSZ_REG) :: (p1, allocb, 16) :: LB) (s := s6') (errv := errv6);
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try solve [ lia | exact MI7 | exact ST6 | exact KREL6 | exact HP7 | exact AUX7 | exact AI6 | exact FZ1 | exact FZ2
                     | unfold P_FZ_RET_SCH; cbn; lia ].
      - exact (ro_cell0 _ _ _ _ FRP7).
      - exact (ro_cell0 _ _ _ _ FRI5).
      - (* [comment removed for export] *) split; [| split; [exact REG6| split; [exact CFG6| split; [| split]]]].
        + unfold O_IOC_REGISTRY. exact (rw_cells_ro_cell _ _ _ _ 8 _ FRI5 eq_refl).
        + eapply XStatics_xpres0; [exact XI| exact XP7].
        + eapply RHEAP_canary. exact HP7.
        + replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO by (unfold RATP, RERRNO; rewrite unsigned_lit; lia). exact ERR6.
      - rewrite !lb_bytes_cons. cbn [blk_size snd]. unfold NEWSZ_REG, NEWSZ_CFG, NEWSZ_SCH. lia.
      - unfold MAKE_SVC_SCHED_STACK, ALLOC_OBJ_SCHED_STACK, ALLOCATE_STACK, ROPNEW_STACK, RMALLOC_STACK. lia. }
    intros [ms8 mo8] PO. unfold make_svc_sched_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m8 & s8' & p4 & schedb &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & BRS & HEAP8 & SCH8 & REG8 & CFG8 & AI8 & XS8 & CAN8 & XPC).
    rewrite (unsigned_lit P) in ST8, XPC by lia.
    replace (bv_unsigned (Z_to_bv 64 RATP) + -164) with RERRNO in ERR8 by (unfold RATP, RERRNO; rewrite unsigned_lit; lia).
    apply (hh_mpres_trans H HH _ _ _ MP6) in MP8. clear MP6.
    xp_frame XPC P.
    pose proof BRS as (S1 & S2 & _ & S4 & S5). unfold NEWSZ_SCH in S4, S5.
    assert (XP8 : xpres LB (P + 512) XH_X m m8).
    { eapply (xp_lift H HH s6' [(p3, cfgb, NEWSZ_CFG); (p2, regb, NEWSZ_REG); (p1, allocb, 16)] LB m7); [exact XP7| exact XPC| lia| lia| exact HP7|].
      intros a [R|[]]. left. right. exists (p2, regb, NEWSZ_REG). split; [right; left; reflexivity| cbn in R |- *; lia]. }
    assert (HS8 : HStat FT m8).
    { eapply (HStat_xpres_keep FT _ P _); [exact FT_local| exact HS7| exact XPC|]. intros a Ha [R|[]]. cbn in R. unfold NEWSZ_REG in R. unfold XH_LO, XH_HI in Ha. lia. }
    clear MI7 ST6 ERR6 AUX7 HP7 XP7 HS7 AI6 REG6 CFG6 MSC XPC.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 P_FZ_RET_SCH)) with (Z_to_bv 64 P_FZ_RET_SCH)
      by (symmetry; apply ret_pc_even; [unfold P_FZ_RET_SCH; lia| reflexivity]).
    eapply (hh_evt H HH); [exact KREL8| |].
    { eapply fzB4; [exact FRI5| lia| lia| exact MI8]. }
    intros ms9 PO. unfold fzB4_post in PO. unfold fzK1. cbn [cfg_ms cfg_model].
    destruct PO as (m9 & -> & MU & WM & MI9 & IOC9). clear FRI5.
    eapply (rw_cells_transport rsegs _ m8 m9) in ERR8; [| exact MU| exact WM| unfold RERRNO in *; cbn; lia].
    mu_frame MU WM P.
    eapply (stk_transport_disjoint rsegs _ m8 m9) in ST8; [| exact MU| exact WM| cbn; lia].
    do 11 eexists. exists m9, s8', (wz 0), p1, allocb, p2, regb, p3, cfgb, p4, schedb, j351, j32.
    split; [reflexivity|]. split; [exact KREL8|]. split; [exact MP8|]. split; [exact MI9|]. split; [exact ST8|].
    split; [rewrite EA; exact ERR8|].
    split. { eapply (hh_rauxv_frame H HH); [exact AUX8| exact MU| exact WM|]. unfold RAUXV_CELL in *. constructor; [cbn; lia| constructor]. }
    assert (HP9 : hs_RHEAP H s8' (fz_LB1 p1 allocb p2 regb p3 cfgb p4 schedb LB) m9).
    { unfold fz_LB1. eapply (hh_RHEAP_frame H HH); [exact HEAP8| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
    split; [exact HP9|].
    split. { unfold fz_LB1, SZ_ALLOCIMPL. split; [exact IOC9|]. split; [| split; [| split]].
      - eapply (AllocImpl_transport _ _ m8 m9); [exact AI8| exact MU| exact WM| unfold SZ_ALLOCIMPL; cbn; lia].
      - eapply (Registry_transport _ _ m8 m9); [exact REG8| exact MU| exact WM| unfold NEWSZ_REG; cbn; lia].
      - eapply (ConfigSvc_transport _ _ m8 m9); [exact CFG8| exact MU| exact WM| unfold NEWSZ_CFG; cbn; lia].
      - eapply (Scheduler_transport _ _ m8 m9); [exact SCH8| exact MU| exact WM| unfold NEWSZ_SCH; cbn; lia]. }
    split; [exact FRP7|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split. { eapply HStat_munch_keep; [exact FT_local| exact HS8| exact MU|]. unfold XH_LO, XH_HI. constructor; [cbn; lia| constructor]. }
    eapply (xp_lift_munch H HH s8' [(p4, schedb, NEWSZ_SCH); (p3, cfgb, NEWSZ_CFG); (p2, regb, NEWSZ_REG); (p1, allocb, 16)] LB m9);
      [exact XP8| exact MU| exact WM| lia| exact HP9|].
    constructor; [cbn; intros a Ha; left; left; lia| constructor].
  Qed.
End W.
End HCW.
