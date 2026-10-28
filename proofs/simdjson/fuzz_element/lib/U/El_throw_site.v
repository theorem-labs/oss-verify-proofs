(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl Prog Monad Target SjModel AtpModel ElModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks MallocKit_B F_malloc_free F_malloc_fast Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Sj_iface Sj_kit El_xs_soundG El_xs_core El_xs_kitP El_xs_adapt El_xs_frame El_throw El_xcxa.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xr_cast0 El_xr_cast4 El_xr_cast7 El_xr_cast1 El_xr_cast5 El_xr_cast2 El_xr_cast3 El_xr_cast6 El_xr_begin El_xr_end.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac st1 := step; fix_lit_store; try nrm.
Ltac probe := match goal with |- ?g => idtac "PROBE"; idtac g end; fail "PROBE".
Import AX2. Import AX2SG.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma pj_relro_rheap : forall LB SP m m', rheap_pres LB SP m m' -> pj_relro m -> pj_relro m'.
Proof.
  intros LB SP m m' RP H a Ha. destruct (RP a ltac:(lia)) as [E _].
  { right. left. unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia. }
  rewrite E. apply H. exact Ha.
Qed.

Definition site_post (gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (LB : list block) (usp lo B : Z) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 t3 t4 t5 t6 F' m' (errv' : word),
    ms' = MS (mkR ra (wz (usp + 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (wz 0x3c520) fc None m' (seg_rom usegs)
    /\ (forall r : reg, reg_get F' r = reg_get F r)
    /\ mem_inv usegs m' /\ stk usegs m' lo (usp + 16)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ RHEAP s' LB m' /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rw_cells usegs m' 0xedb98 [C8 (wz 0); C4 (wz 0)]
    /\ rw_cells usegs m' 0xef4b0 (uw_cells true)
    /\ (forall a, 0 <= a < 2^64 -> rclient_addr LB (usp + 16) a ->
          ~ (0xedb98 <= a < 0xedb98 + 12) -> ~ (0xef4b0 <= a < 0xef4b0 + 8) ->
          m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)).

Definition xp_none (m : mem) (usp : Z) : Prop := True.
Definition xp_err (m : mem) (usp : Z) : Prop := exists e, 0 <= e < 64 /\ rw_cells usegs m (usp - 8) [C4 (wz e)].
Definition xp_end (m : mem) (usp : Z) : Prop :=
  xp_err m usp /\ exists w1 w2 : word, rw_cells usegs m (usp - 56) [C8 w2; C8 w1; C8 (wz 0x3da0c)].
Definition xr_none (usp : Z) (s1 : word) : Prop := True.
Definition xr_end (usp : Z) (s1 : word) : Prop := s1 = wz (usp - 24).
Definition cast_D (sel : Z) : Z := if sel =? 5 then 0 else 32.
Definition cast_XP (sel : Z) : mem -> Z -> Prop := if sel =? 4 then xp_err else xp_none.

Definition throw_site_stmt (pcs D raval : Z) (XP : mem -> Z -> Prop) (XR : Z -> word -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (canary errv w0 : word) (uw : bool),
  let usp := bv_unsigned sp + D in
  RHEAP s LB m -> usp mod 16 = 0 ->
  stk usegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 16384 -> usp + 16 <= B -> B < 2^62 ->
  rauxv_ok m B -> mem_inv usegs m -> pj_relro m -> ssp_cells m canary ->
  rw_cells usegs m EL_XDATA [C8 (wz EL_XDATA_V0); C8 (wz EL_XDATA_V1)] ->
  rw_cells usegs m EL_HDLR [C8 (wz EL_HDLR_V0); C8 (wz EL_HDLR_V1)] ->
  rw_cells usegs m EL_MREPL [C4 (wz 0); C4 (wz 0)] ->
  rw_cells usegs m EL_EHG [C8 (wz 0); C4 (wz 0)] ->
  rw_cells usegs m EL_UNW (uw_cells uw) ->
  rw_cells usegs m usp [C8 w0] -> rw_cells usegs m (usp + 8) [C8 (wz raval)] ->
  XP m usp -> XR usp s1 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  implM usegs (bind lops (AtpModel.newnt lops EL_EXC) (fun e => AtpModel.del lops e)) s (site_post gp tp s9 s10 s11 F fc s LB usp lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcs) fc None m (seg_rom usegs)).

Section Site.
  Variables (pcs pc0 pc1 D raval : Z) (XP : mem -> Z -> Prop) (XR : Z -> word -> Prop) (xk : list kentry) (IT : itab).
  Hypothesis ITS : itab_sound usegs IT.
  Hypothesis RUN : forall uw : bool, exit_ok (xautoP IT xs_W xs_RW 0x7c1b8 XS_FUEL XS_KD (xs_ssD D xk pc1 raval uw)) = true.
  Hypothesis PC0 : pc0 = pcs + 8.
  Hypothesis PCS : 0 <= pcs /\ pcs + 8 < 2^32 /\ (pcs + 8) mod 2 = 0.
  Hypothesis RAV : 0 <= raval < 2^64.
  Hypothesis DR : 0 <= D <= 64.

  Hypothesis CODE : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv usegs m ->
    evt usegs (fun ms1 => ms1 = MS (mkR (wz (pcs + 8)) sp gp tp t0 t1 t2 s0 s1 (wz 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x7b904) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcs) fc None m (seg_rom usegs)).
  Hypothesis CODE2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv usegs m -> 16384 <= bv_unsigned sp + D < 2^62 -> XP m (bv_unsigned sp + D) -> XR (bv_unsigned sp + D) s1 ->
    evt usegs (fun ms1 => exists a1' a2' : word,
                 ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc1) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc0) fc None m (seg_rom usegs)).
  Hypothesis XPT : forall (m m' : mem) usp, XP m usp ->
    (forall A cs, rw_cells usegs m A cs -> usp - D <= A -> rw_cells usegs m' A cs) -> XP m' usp.
  Hypothesis XKV : forall (m : mem) usp, 16384 <= usp < 2^62 -> XP m usp ->
    exists w1 w2 : word, forall E : env, ev E 2 = wz usp -> ev E 50 = w1 -> ev E 51 = w2 -> know_ok usegs E m xk.

  Theorem throw_site_core : throw_site_stmt pcs D raval XP XR.
  Proof.
    intros until uw. intros usp HP AL ST LO LOW SPB B62 AUX MI RELRO SSP XD HD MREPL EHG UNW W0S RAS XPm XRs ERR TP.
    assert (USP : bv_unsigned sp + D = usp) by reflexivity. clearbody usp.
    pose proof alloc_ceiling_range as CR. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof DR as DR'. pose proof RAV as RAV'.
    cbn [bind lops Target.ops].
    destruct (stk_split usegs m lo (bv_unsigned sp) usp ST ltac:(lia)) as [STs STf].

    eapply implM_evt; [apply CODE; exact MI|]. intros ms1 ->.

    eapply implM_bind.
    { eapply (cxa_alloc_spec (wz (pcs + 8)) sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv HP AUX);
        [lia| exact STs| exact LO| unfold RMALLOC_STACK; lia| exact ERR| exact MI| exact TP| exact MREPL]. }
    intros p s1' ms2 POST. unfold cxa_post in POST.
    destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & blk & errv1 & -> & MI1 & ST1 & ERR1 & AUX1 & RP1 & FA1 & SO1 & RB & HP1 & HB).
    rewrite ret_pc_even by (clear - PCS; lia).

    assert (AG : forall A cs, rw_cells usegs m A cs -> rclient_range LB (bv_unsigned sp) A (Z.of_nat (cells_size cs)) -> rw_cells usegs m1 A cs).
    { intros A cs H HR. eapply rheap_pres_rw_cells; [exact RP1| exact H| exact HR]. }
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HP1) as ND.
    assert (XP1 : XP m1 usp) by (apply (XPT m m1 usp XPm); intros A cs H HA; apply AG; [exact H| left; lia]).
    destruct (XKV m1 usp ltac:(lia) XP1) as (w1 & w2 & XK1).
    assert (STF1 : stk usegs m1 (bv_unsigned sp) usp) by (eapply rheap_pres_stk; [exact RP1| exact STf| lia]).
    assert (XP1' : XP m1 (bv_unsigned sp + D)) by (rewrite USP; exact XP1).
    assert (XR1' : XR (bv_unsigned sp + D) s1) by (rewrite USP; exact XRs).

    cbn [del lib_free lops Target.ops lib_free_opt].
    rewrite <- PC0.
    eapply implM_evt; [apply (CODE2 (wz pc0) sp gp tp u0 u1 u2 s0 s1 (wz (blk + 128)) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 MI1 ltac:(lia) XP1' XR1')|].
    intros ms3 (a1' & a2' & ->).
    eapply implM_post_evt.
    { eapply (xs_throw_A IT pc1 raval D xk ITS RUN (wz pc0) sp gp tp u0 u1 u2 s0 s1 a1' a2' v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                F fc m1 s1' ((p, blk, 144) :: LB) p blk lo B usp canary errv1 w0 w1 w2 uw USP HP1 ltac:(left; reflexivity) HB RB).
      - pose proof (stk_of_rw_cells usegs m1 _ _ (AG _ _ W0S ltac:(left; lia))) as S1. pose proof (stk_of_rw_cells usegs m1 _ _ (AG _ _ RAS ltac:(left; lia))) as S2.
        cbn [cells_size csize Nat.add] in S1, S2. replace (usp + 8 + 8) with (usp + 16) in S2 by lia.
        eapply stk_merge; [exact ST1| eapply stk_merge; [exact STF1| eapply stk_merge; [exact S1| exact S2| lia]| lia]| lia].
      - exact LO.
      - lia.
      - lia.
      - lia.
      - exact AL.
      - exact AUX1.
      - exact MI1.
      - eapply pj_relro_rheap; [exact RP1| exact RELRO].
      - rewrite (ssp_canary_0 _ _ _ _ HP SSP). exact (RHEAP_ssp _ _ _ HP1).
      - apply AG; [exact XD| right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      - apply AG; [exact HD| right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      - apply AG; [exact EHG| right; left; cbn; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia].
      - apply AG; [exact UNW| right; left]. replace (Z.of_nat (cells_size (uw_cells uw))) with 8 by (destruct uw; reflexivity).
        unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
      - apply AG; [exact W0S| left; lia].
      - apply AG; [exact RAS| left; lia].
      - exact RAV.
      - exact ERR1.
      - exact TP.
      - exact XK1. }

    intros [] s' ms' X. apply evt_done. unfold xs_post in X. unfold site_post.
    rewrite (lb_remove_hd p blk 144 LB ND) in X.
    destruct X as (zra & z0 & z1 & z2 & y0 & y1 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & z3 & z4 & z5 & z6 & F' & m' &
                   -> & HF & MI' & ST' & ERR' & AUX' & HP' & FA' & SO' & EHG' & UNW' & FR').
    do 27 eexists. exists errv1. split; [reflexivity|]. split; [exact HF|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split; [exact HP'|]. split; [rewrite FA'; exact FA1|]. split; [rewrite SO'; exact SO1|]. split; [exact EHG'|]. split; [exact UNW'|].
    intros a Ha HC N1 N2. destruct (FR' a Ha HC N1 N2) as [E1 W1].
    destruct (RP1 a Ha) as [E0 W0]. { destruct HC as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H]. }
    rewrite E1, E0. split; [reflexivity|]. intros W. apply W1. apply W0. exact W.
  Qed.
End Site.

Lemma code2_refl : forall (pc D : Z) (XP : mem -> Z -> Prop) (XR : Z -> word -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> 16384 <= bv_unsigned sp + D < 2^62 -> XP m (bv_unsigned sp + D) -> XR (bv_unsigned sp + D) s1 ->
  evt usegs (fun ms1 => exists a1' a2' : word,
               ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. apply evt_done. exists a1, a2. reflexivity. Qed.

Lemma xpt_none : forall (D : Z) (m m' : mem) usp, xp_none m usp ->
  (forall A cs, rw_cells usegs m A cs -> usp - D <= A -> rw_cells usegs m' A cs) -> xp_none m' usp.
Proof. intros. exact I. Qed.
Lemma xpt_err : forall (D : Z), 8 <= D -> forall (m m' : mem) usp, xp_err m usp ->
  (forall A cs, rw_cells usegs m A cs -> usp - D <= A -> rw_cells usegs m' A cs) -> xp_err m' usp.
Proof. intros D HD m m' usp (e & He & C) T. exists e. split; [exact He|]. apply T; [exact C| lia]. Qed.
Lemma xpt_end : forall (m m' : mem) usp, xp_end m usp ->
  (forall A cs, rw_cells usegs m A cs -> usp - 64 <= A -> rw_cells usegs m' A cs) -> xp_end m' usp.
Proof.
  intros m m' usp [X (w1 & w2 & C)] T. split; [exact (xpt_err 64 ltac:(lia) m m' usp X T)|].
  exists w1, w2. apply T; [exact C| lia].
Qed.

Lemma xkv_nil : forall (XP : mem -> Z -> Prop) (m : mem) usp, 16384 <= usp < 2^62 -> XP m usp ->
  exists w1 w2 : word, forall E : env, ev E 2 = wz usp -> ev E 50 = w1 -> ev E 51 = w2 -> know_ok usegs E m [].
Proof. intros. exists (wz 0), (wz 0). intros. constructor. Qed.
Lemma xkv_end : forall (m : mem) usp, 16384 <= usp < 2^62 -> xp_end m usp ->
  exists w1 w2 : word, forall E : env, ev E 2 = wz usp -> ev E 50 = w1 -> ev E 51 = w2 -> know_ok usegs E m xk_end.
Proof.
  intros m usp UB [_ (w1 & w2 & C)]. exists w1, w2. intros E E2 E50 E51.
  destruct C as [[_ BC] _]. cbn [cells_bytes cbytes] in BC. rewrite app_nil_r in BC.
  apply Mem.bytes_at_app in BC as [B2 BC]. rewrite Mem.length_le8 in BC.
  apply Mem.bytes_at_app in BC as [B1 B0]. rewrite Mem.length_le8 in B0.
  replace (usp - 56 + Z.of_nat 8) with (usp + -48) in B1 by lia.
  replace (usp - 56 + Z.of_nat 8 + Z.of_nat 8) with (usp + -40) in B0 by lia.
  replace (usp - 56) with (usp + -56) in B2 by lia.
  assert (UX : bv_unsigned (edenot E XSP) = usp) by (cbn [edenot XSP]; rewrite E2; apply unsigned_lit; lia).
  unfold xk_end. constructor; [| constructor; [| constructor; [| constructor]]]; apply kword_at; rewrite ?UX; try lia; cbn [edenot].
  - exact B0.
  - rewrite E50. exact B1.
  - rewrite E51. exact B2.
Qed.

Lemma sx32_lt64 : forall e, 0 <= e < 64 -> bv_unsigned (Mem.sx32 (wz e)) = e.
Proof.
  intros e He. unfold Mem.sx32. rewrite (unsigned_lit e) by lia.
  replace (bv_swrap 32 e) with e.
  2:{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
      rewrite Z.mod_small by lia. lia. }
  apply unsigned_lit. lia.
Qed.

Lemma code2_err : forall (pc D : Z) (XR : Z -> word -> Prop),
  pc = 0x3d6b0 -> D = 32 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> 16384 <= bv_unsigned sp + D < 2^62 -> xp_err m (bv_unsigned sp + D) -> XR (bv_unsigned sp + D) s1 ->
  evt usegs (fun ms1 => exists a1' a2' : word,
               ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (pc + 12)) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom usegs)).
Proof.
  intros pc D XR Hpc HD. subst pc D. intros until m. intros MI UB (e & He & C) _.
  set (u := bv_unsigned sp) in *. assert (SPE : sp = wz u) by (subst u; symmetry; apply Z_to_bv_bv_unsigned). clearbody u. subst sp.
  replace (u + 32 - 8) with (u + 24) in C by lia.
  unfold wz. zstep. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; rewrite sx32_lt64 in K by lia; lia|].
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma code2_end : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> 16384 <= bv_unsigned sp + 64 < 2^62 -> xp_end m (bv_unsigned sp + 64) -> xr_end (bv_unsigned sp + 64) s1 ->
  evt usegs (fun ms1 => exists a1' a2' : word,
               ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3f024) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3f018) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros MI UB [(e & He & C) _] XR. unfold xr_end in XR. subst s1.
  set (u := bv_unsigned sp) in *. assert (SPE : sp = wz u) by (subst u; symmetry; apply Z_to_bv_bv_unsigned). clearbody u. subst sp.
  replace (u + 64 - 8) with (u + 56) in C by lia. replace (u + 64 - 24) with (u + 40) by lia.
  unfold wz. zstep. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; rewrite sx32_lt64 in K by lia; lia|].
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Local Ltac site_code := intros until m; intros MI; unfold wz; st1; st1; apply evt_done; reflexivity.
Theorem throw_site_begin : throw_site_stmt 0x3d968 0 0x3c344 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d968 0x3d970 0x3d970 0 0x3c344 xp_none xr_none [] el_IT_begin (itab_of_ranges_soundP el_ranges_begin) xr_begin_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d970 0 xp_none xr_none)| exact (xpt_none 0)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast0 : throw_site_stmt 0x3d644 32 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d644 0x3d64c 0x3d64c 32 0x3c378 xp_none xr_none [] el_IT_cast0 (itab_of_ranges_soundP el_ranges_cast0) xr_cast0_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d64c 32 xp_none xr_none)| exact (xpt_none 32)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast1 : throw_site_stmt 0x3d840 32 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d840 0x3d848 0x3d848 32 0x3c378 xp_none xr_none [] el_IT_cast1 (itab_of_ranges_soundP el_ranges_cast1) xr_cast1_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d848 32 xp_none xr_none)| exact (xpt_none 32)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast2 : throw_site_stmt 0x3d714 32 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d714 0x3d71c 0x3d71c 32 0x3c378 xp_none xr_none [] el_IT_cast2 (itab_of_ranges_soundP el_ranges_cast2) xr_cast2_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d71c 32 xp_none xr_none)| exact (xpt_none 32)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast3 : throw_site_stmt 0x3d774 32 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d774 0x3d77c 0x3d77c 32 0x3c378 xp_none xr_none [] el_IT_cast3 (itab_of_ranges_soundP el_ranges_cast3) xr_cast3_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d77c 32 xp_none xr_none)| exact (xpt_none 32)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast4 : throw_site_stmt 0x3d6a8 32 0x3c378 xp_err xr_none.
Proof.
  apply (throw_site_core 0x3d6a8 0x3d6b0 0x3d6bc 32 0x3c378 xp_err xr_none [] el_IT_cast4 (itab_of_ranges_soundP el_ranges_cast4) xr_cast4_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_err 0x3d6b0 32 xr_none eq_refl eq_refl)| exact (xpt_err 32 ltac:(lia))| exact (xkv_nil xp_err)].
Qed.
Theorem throw_site_cast5 : throw_site_stmt 0x3ef04 0 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3ef04 0x3ef0c 0x3ef0c 0 0x3c378 xp_none xr_none [] el_IT_cast5 (itab_of_ranges_soundP el_ranges_cast5) xr_cast5_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3ef0c 0 xp_none xr_none)| exact (xpt_none 0)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast6 : throw_site_stmt 0x3d8d8 32 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d8d8 0x3d8e0 0x3d8e0 32 0x3c378 xp_none xr_none [] el_IT_cast6 (itab_of_ranges_soundP el_ranges_cast6) xr_cast6_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d8e0 32 xp_none xr_none)| exact (xpt_none 32)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_cast7 : throw_site_stmt 0x3d7dc 32 0x3c378 xp_none xr_none.
Proof.
  apply (throw_site_core 0x3d7dc 0x3d7e4 0x3d7e4 32 0x3c378 xp_none xr_none [] el_IT_cast7 (itab_of_ranges_soundP el_ranges_cast7) xr_cast7_ok);
    [reflexivity| lia| lia| lia| site_code| exact (code2_refl 0x3d7e4 32 xp_none xr_none)| exact (xpt_none 32)| exact (xkv_nil xp_none)].
Qed.
Theorem throw_site_end : throw_site_stmt 0x3f010 64 0x3c3ec xp_end xr_end.
Proof.
  apply (throw_site_core 0x3f010 0x3f018 0x3f024 64 0x3c3ec xp_end xr_end xk_end el_IT_end (itab_of_ranges_soundP el_ranges_end) xr_end_ok);
    [reflexivity| lia| lia| lia| site_code| exact code2_end| exact xpt_end| exact xkv_end].
Qed.
End WithCeiling0.
