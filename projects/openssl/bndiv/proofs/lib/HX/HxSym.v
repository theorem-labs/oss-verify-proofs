(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie AxFetchFast AxFetchFast2 AxDecInt.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxLearn.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Export HxSymDef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma valw_agree (n : int) (rho rho' : valuation) (a : sarg) : agree_below n rho rho' -> arg_below n a -> valw rho' a = valw rho a.
Proof. intros Ha Hb. destruct a as [w|t]; [reflexivity|]. cbn [valw arg_below] in *. rewrite (Ha t Hb). reflexivity. Qed.

Lemma log_ok_agree (n : int) (rho rho' : valuation) (log : list snode) :
  agree_below n rho rho' -> log_below n log -> log_ok rho log -> log_ok rho' log.
Proof.
  intros Ha Hb Hok. unfold log_ok, log_below in *. rewrite Forall_forall in *. intros nd Hin.
  destruct (Hb nd Hin) as (B1 & B2 & B3). unfold node_ok. rewrite (Ha _ B1), (valw_agree n rho rho' _ Ha B2), (valw_agree n rho rho' _ Ha B3).
  exact (Hok nd Hin).
Qed.

Lemma log_below_mono (n n' : int) (log : list snode) : to_Z n <= to_Z n' -> log_below n log -> log_below n' log.
Proof.
  intros Hn H. unfold log_below in *. rewrite Forall_forall in *. intros nd Hin. destruct (H nd Hin) as (B1 & B2 & B3).
  unfold node_below. split; [lia|]. split; [destruct (sn_a nd); cbn in *; [exact I | lia] | destruct (sn_b nd); cbn in *; [exact I | lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sarg_of_den (rho : valuation) (v : hval) (a : sarg) (x : bv 64) : sarg_of v = Some a -> den rho v x -> x = valw rho a.
Proof.
  destruct v as [w|t o| |]; cbn [sarg_of]; try discriminate.
  - intros E H. injection E as <-. exact H.
  - destruct (is_zero o) eqn:Ez; [|discriminate]. intros E H. injection E as <-. apply is_zero_spec in Ez. subst o.
    cbn [den valw] in *. rewrite H. unfold pword. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity.
Qed.

Section Sym.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition sx_post (rho : valuation) (log : list snode) (S : sstate) (ms : machine_state) (log' : list snode) (S' : sstate) : Prop :=
  exists rho' ms', agree_below (s_next S) rho rho' /\ mstep segs ms ms' /\ Rn segs rho' S' ms'
    /\ log_ok rho' log' /\ log_below (s_next S') log' /\ to_Z (s_next S) <= to_Z (s_next S')
    /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
    /\ same_dirs (s_mem S) (s_mem S') /\ mem_step rho' (s_mem S) (ms_mem ms) (ms_mem ms') /\ regs_step (ms_regs ms) (ms_regs ms')
    /\ s_abs S' = s_abs S.

(* [comment removed for export] *)
Definition rho_ext (rho : valuation) (t : int) (z : Z) : valuation := fun x => if (x =? t)%uint63 then z else rho x.

Lemma rho_ext_agree (rho : valuation) (t : int) (z : Z) : agree_below t rho (rho_ext rho t z).
Proof.
  intros x Hx. unfold rho_ext. destruct (eqbP x t) as [E|E]; [lia | reflexivity].
Qed.

Lemma rho_ext_same (rho : valuation) (t : int) (z : Z) : rho_ext rho t z t = z.
Proof. unfold rho_ext. rewrite Uint63.eqb_refl. reflexivity. Qed.

Lemma rho_ext_agree_ge (rho : valuation) (n t : int) (z : Z) : to_Z n <= to_Z t -> agree_below n rho (rho_ext rho t z).
Proof. intros Hn x Hx. unfold rho_ext. destruct (eqbP x t) as [E|E]; [lia | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sarg_tag_below (rho : valuation) (n tx : int) (v : hval) (x : bv 64) :
  sarg_of v = Some (AN tx) -> (forall rho1, agree_below n rho rho1 -> den rho1 v x) -> to_Z tx < to_Z n.
Proof.
  intros Ea Hd. destruct (Z_lt_le_dec (to_Z tx) (to_Z n)) as [L|L]; [exact L|]. exfalso.
  pose proof (sarg_of_den (rho_ext rho tx 0) v (AN tx) x Ea (Hd (rho_ext rho tx 0) (rho_ext_agree_ge rho n tx 0 L))) as X0.
  pose proof (sarg_of_den (rho_ext rho tx 1) v (AN tx) x Ea (Hd (rho_ext rho tx 1) (rho_ext_agree_ge rho n tx 1 L))) as X1.
  cbn [valw] in X0, X1. rewrite rho_ext_same in X0, X1. rewrite X0 in X1. apply (f_equal bv_unsigned) in X1.
  rewrite !Z_to_bv_unsigned in X1. discriminate X1.
Qed.

(* [comment removed for export] *)
Lemma sym_result_sound (rho : valuation) (log log' : list snode) (S S' : sstate) (ms : machine_state)
    (rd : reg) (op : sop) (a b normal : hval) (x y : bv 64) :
  Rn segs rho S ms -> log_ok rho log -> log_below (s_next S) log ->
  (forall rho1, agree_below (s_next S) rho rho1 -> den rho1 a x /\ den rho1 b y /\ den rho1 normal (sop_eval op x y)) ->
  mstep segs ms (MS_of_core (Sem.rset rd (sop_eval op x y) (Sem.with_pc (wbv (w_add (s_pc S) w_four)) (core_of ms))) (ms_mem ms) (ms_rom ms)) ->
  (forall t0, to_Z t0 < to_Z (s_next S) -> True) ->
  sym_result log S (rix_of_reg rd) op a b normal = Some (log', S') ->
  sx_post rho log S ms log' S'.
Proof.
  intros HRn Hlog Hbel Hden Hstep _ H.
  set (v := sop_eval op x y) in *. set (npc := w_add (s_pc S) w_four) in *.
  set (ms' := MS_of_core (Sem.rset rd v (Sem.with_pc (wbv npc) (core_of ms))) (ms_mem ms) (ms_rom ms)) in *.
  (* [comment removed for export] *)
  assert (Normal : forall hv, (forall rho1, agree_below (s_next S) rho rho1 -> den rho1 hv v) ->
            sx_post rho log S ms log (with_reg_pc S (rix_of_reg rd) hv npc)).
  { intros hv Hhv. exists rho, ms'. split; [apply agree_below_refl|]. split; [exact Hstep|]. split.
    { intros rho1 Ha. cbn [with_reg_pc s_next] in Ha. pose proof (HRn rho1 Ha) as (Hsvc & Hpc & Hr & Hv & Hm).
      unfold with_reg_pc, ms'. apply R_done.
      - rewrite rset_pc. reflexivity.
      - apply Rregs_set; [exact Hr | exact (Hhv rho1 Ha)].
      - rewrite rset_resv. exact Hv.
      - exact Hm. }
    split; [exact Hlog|]. split; [exact Hbel|]. split; [cbn [with_reg_pc s_next]; lia|].
    unfold ms', MS_of_core, MS. cbn [ms_fregs ms_fcsr ms_rom ms_mem ms_regs]. rewrite rset_fregs, rset_fcsr.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply same_dirs_refl|].
    split; [left; reflexivity|]. split; [exact (regs_step_rset rd v (Sem.with_pc (wbv npc) (core_of ms))) | reflexivity]. }
  unfold sym_result in H. fold npc in H.
  destruct normal as [w|tn on| |tn on];
    try (injection H as <- <-; apply Normal; intros rho1 Ha; exact (proj2 (proj2 (Hden rho1 Ha)))).
  destruct (sarg_of a) as [xa|] eqn:Ea; [|injection H as <- <-; apply Normal; intros rho1 Ha; exact I].
  destruct (sarg_of b) as [yb|] eqn:Eb; [|injection H as <- <-; apply Normal; intros rho1 Ha; exact I].
  destruct (s_next S <? TAGMAX)%uint63 eqn:Et; [|discriminate]. apply ltb_spec in Et. change (to_Z TAGMAX) with 1048576 in Et.
  injection H as <- <-. set (t := s_next S) in *.
  assert (Et1 : to_Z (t + 1)%uint63 = to_Z t + 1).
  { rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. pose proof (to_Z_bounded t). rewrite wB_eq. unfold two63. lia. }
  set (rho' := rho_ext rho t (bv_unsigned v)).
  assert (Hag : agree_below t rho rho') by apply rho_ext_agree.
  exists rho', ms'. split; [exact Hag|]. split; [exact Hstep|]. split.
  { intros rho2 Ha2. cbn [s_next] in Ha2.
    assert (Ha : agree_below t rho rho2).
    { intros z Hz. rewrite (Ha2 z) by lia. apply Hag. exact Hz. }
    pose proof (HRn rho2 Ha) as (Hsvc & Hpc & Hr & Hv & Hm). unfold ms'. apply R_done.
    - rewrite rset_pc. reflexivity.
    - apply Rregs_set; [exact Hr|]. cbn [den]. unfold pword. change (wZ w_zero) with 0. rewrite Z.add_0_r.
      rewrite (Ha2 t) by lia. unfold rho'. rewrite rho_ext_same. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite rset_resv. exact Hv.
    - exact Hm. }
  assert (Hx : x = valw rho xa) by exact (sarg_of_den rho a xa x Ea (proj1 (Hden rho (agree_below_refl _ _)))).
  assert (Hy : y = valw rho yb) by exact (sarg_of_den rho b yb y Eb (proj1 (proj2 (Hden rho (agree_below_refl _ _))))).
  (* [comment removed for export] *)
  assert (Bx : arg_below t xa).
  { destruct xa as [w|tx]; [exact I|]. cbn [arg_below]. apply (sarg_tag_below rho t tx a x Ea). intros rho1 Ha. exact (proj1 (Hden rho1 Ha)). }
  assert (By : arg_below t yb).
  { destruct yb as [w|ty]; [exact I|]. cbn [arg_below]. apply (sarg_tag_below rho t ty b y Eb). intros rho1 Ha. exact (proj1 (proj2 (Hden rho1 Ha))). }
  split.
  { constructor.
    - unfold node_ok. cbn [sn_t sn_op sn_a sn_b]. unfold rho' at 1. rewrite rho_ext_same.
      rewrite (valw_agree t rho rho' xa Hag Bx), (valw_agree t rho rho' yb Hag By), <- Hx, <- Hy. reflexivity.
    - exact (log_ok_agree t rho rho' log Hag Hbel Hlog). }
  split.
  { cbn [s_next]. constructor.
    - unfold node_below. cbn [sn_t sn_a sn_b]. rewrite Et1. split; [lia|].
      split; [destruct xa; cbn [arg_below] in *; [exact I | lia] | destruct yb; cbn [arg_below] in *; [exact I | lia]].
    - apply (log_below_mono t); [lia | exact Hbel]. }
  split; [cbn [s_next]; fold t; lia|].
  unfold ms', MS_of_core, MS. cbn [ms_fregs ms_fcsr ms_rom ms_mem ms_regs s_mem s_abs]. rewrite rset_fregs, rset_fcsr.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply same_dirs_refl|].
  split; [left; reflexivity|]. split; [exact (regs_step_rset rd v (Sem.with_pc (wbv npc) (core_of ms))) | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma reg_step (S : sstate) (ms : machine_state) (rho : valuation) (w : bv 32) (i : instr) (rd : reg) (v : bv 64) :
  R segs rho S ms -> fetch_word segs (wbv (s_pc S)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  interp_eff segs (exec (Z_to_bv 64 4) i (core_of ms)) (ms_mem ms)
    = MachineOk (Sem.rset rd v (Sem.with_pc (bv_add (ms_pc_val ms) (Z_to_bv 64 4)) (core_of ms)), ms_mem ms) ->
  mstep segs ms (MS_of_core (Sem.rset rd v (Sem.with_pc (wbv (w_add (s_pc S) w_four)) (core_of ms))) (ms_mem ms) (ms_rom ms)).
Proof.
  intros HR Hfw Hec Hdec Hex. pose proof HR as (Hsvc & Hpc & _). split; [exact Hsvc|].
  assert (Enpc : bv_add (ms_pc_val ms) (Z_to_bv 64 4) = wbv (w_add (s_pc S) w_four)) by (rewrite wbv_add, wbv_four, Hpc; reflexivity).
  rewrite Enpc in Hex. rewrite (MS_eta ms Hsvc) at 1. rewrite <- Hpc in Hfw.
  rewrite (step_gen segs _ _ _ _ _ _ _ w i 4 Hfw Hec Hdec). unfold core_of in Hex |- *. rewrite Hex. reflexivity.
Qed.

Theorem sx_step_sound (rho : valuation) (log log' : list snode) (S S' : sstate) (ms : machine_state) :
  Rn segs rho S ms -> log_ok rho log -> log_below (s_next S) log -> sx_step segs log S = Some (log', S') ->
  sx_post rho log S ms log' S'.
Proof.
  intros HRn Hlog Hbel H. unfold sx_step in H.
  destruct (hx_fetch segs IEmpty (s_pc S)) as [[d ic1]|] eqn:Ef; [|discriminate].
  pose proof (Rn_R segs rho S ms HRn) as HR.
  destruct (hx_fetch_sound segs IEmpty ic1 (s_pc S) d (ic_ok_empty segs) Ef) as (_ & w & i & Hfw & Hec & Hdec & Ed).
  assert (Hden : forall rho1 r, agree_below (s_next S) rho rho1 -> den rho1 (rget S (rix_of_reg r)) (Sem.rget (core_of ms) r)).
  { intros rho1 r Ha. pose proof (HRn rho1 Ha) as (_ & _ & Hr & _). exact (Hr r). }
  assert (Hctx : forall rho1, agree_below (s_next S) rho rho1 -> ctx_ok rho1 (ctx_of (s_mem S))).
  { intros rho1 Ha. pose proof (HRn rho1 Ha) as (_ & _ & _ & _ & Hm). exact (ctx_of_ok segs rho1 (s_mem S) (ms_mem ms) Hm). }
  (* [comment removed for export] *)
  assert (Ord : forall lg X, match hx_step segs IEmpty S with (_, SNext S1) => Some (log, S1) | (_, SStuck _ _) => None end = Some (lg, X) ->
                  sx_post rho log S ms lg X).
  { intros lg X H1. destruct (hx_step segs IEmpty S) as [ic2 [S1|c S1]] eqn:Es; [|discriminate]. injection H1 as <- <-.
    destruct (hx_step_Rn segs rho IEmpty ic2 S S1 ms (ic_ok_empty segs) HRn Es) as (_ & ms' & Hst & HRn' & Hf & Hc & Ho & Hm & Hrs).
    destruct (hx_step_next segs IEmpty ic2 S S1 Es) as [Hnx Habs].
    exists rho, ms'. split; [apply agree_below_refl|]. split; [exact Hst|]. split; [exact HRn'|]. split; [exact Hlog|].
    split; [rewrite Hnx; exact Hbel|]. split; [rewrite Hnx; lia|]. repeat (split; [assumption|]).
    split; [exact (mem_step_dirs segs S S1 IEmpty ic2 Es)|]. split; [exact Hm|]. split; [exact Hrs | exact Habs]. }
  destruct d; try exact (Ord log' S' H); destruct i; cbn [predec] in Ed; try discriminate.
  - (* [comment removed for export] *)
    injection Ed as -> -> -> ->.
    eapply (sym_result_sound rho log log' S S' ms rd0 (SAlu op0) _ _ _ (Sem.rget (core_of ms) rs0) (sext 64 imm0) HRn Hlog Hbel); [| |auto|exact H].
    + intros rho1 Ha. split; [exact (Hden rho1 rs0 Ha)|]. split; [apply den_imm|].
      exact (v_alu64_ok rho1 _ op0 _ _ _ _ (Hctx rho1 Ha) (Hden rho1 rs0 Ha) (den_imm rho1 (sext 64 imm0))).
    + apply (reg_step S ms rho w _ rd0 _ HR Hfw Hec Hdec). reflexivity.
  - (* [comment removed for export] *)
    injection Ed as -> -> -> ->.
    eapply (sym_result_sound rho log log' S S' ms rd0 (SAlu op0) _ _ _ (Sem.rget (core_of ms) rs0) (zext 64 shamt) HRn Hlog Hbel); [| |auto|exact H].
    + intros rho1 Ha. split; [exact (Hden rho1 rs0 Ha)|]. split; [apply den_imm|].
      exact (v_alu64_ok rho1 _ op0 _ _ _ _ (Hctx rho1 Ha) (Hden rho1 rs0 Ha) (den_imm rho1 (zext 64 shamt))).
    + apply (reg_step S ms rho w _ rd0 _ HR Hfw Hec Hdec). reflexivity.
  - (* [comment removed for export] *)
    injection Ed as -> -> -> ->.
    eapply (sym_result_sound rho log log' S S' ms rd0 (SAlu op0) _ _ _ (Sem.rget (core_of ms) rs0) (Sem.rget (core_of ms) rs3) HRn Hlog Hbel); [| |auto|exact H].
    + intros rho1 Ha. split; [exact (Hden rho1 rs0 Ha)|]. split; [exact (Hden rho1 rs3 Ha)|].
      exact (v_alu64_ok rho1 _ op0 _ _ _ _ (Hctx rho1 Ha) (Hden rho1 rs0 Ha) (Hden rho1 rs3 Ha)).
    + apply (reg_step S ms rho w _ rd0 _ HR Hfw Hec Hdec). reflexivity.
  - (* [comment removed for export] *)
    injection Ed as -> -> -> ->.
    eapply (sym_result_sound rho log log' S S' ms rd0 (SMul op0) _ _ _ (Sem.rget (core_of ms) rs0) (Sem.rget (core_of ms) rs3) HRn Hlog Hbel); [| |auto|exact H].
    + intros rho1 Ha. split; [exact (Hden rho1 rs0 Ha)|]. split; [exact (Hden rho1 rs3 Ha)|].
      exact (v_muldiv_ok rho1 op0 _ _ _ _ (Hden rho1 rs0 Ha) (Hden rho1 rs3 Ha)).
    + apply (reg_step S ms rho w _ rd0 _ HR Hfw Hec Hdec). reflexivity.
Qed.

End Sym.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SymRun.
Variable segs : list Segment.
Variable stop : w64 -> bool.

(* [comment removed for export] *)
Definition sx_pres (rho : valuation) (P : sstate -> machine_state -> Prop) : Prop :=
  forall S S' ms ms', P S ms -> Rn segs rho S ms -> Rn segs rho S' ms' -> mstep segs ms ms' ->
    ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
    same_dirs (s_mem S) (s_mem S') -> mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') -> regs_step (ms_regs ms) (ms_regs ms') ->
    P S' ms'.

Theorem sx_run_sound (P : sstate -> machine_state -> Prop) (n0 : int) (rho0 : valuation) :
  (forall rho, agree_below n0 rho0 rho -> sx_pres rho P) ->
  forall (n : nat) (rho : valuation) (log log' : list snode) (S S' : sstate) (ms : machine_state),
    agree_below n0 rho0 rho -> to_Z n0 <= to_Z (s_next S) ->
    Rn segs rho S ms -> P S ms -> log_ok rho log -> log_below (s_next S) log -> sx_run segs stop n log S = Some (log', S') ->
    exists rho' ms', agree_below (s_next S) rho rho' /\ msteps segs ms ms' /\ Rn segs rho' S' ms' /\ P S' ms'
                     /\ log_ok rho' log' /\ log_below (s_next S') log'.
Proof.
  intros HP. induction n as [|n IH]; intros rho log log' S S' ms Hag0 Hn0 HRn HPS Hlog Hbel H; cbn [sx_run] in H.
  - injection H as <- <-. exists rho, ms. split; [apply agree_below_refl|]. split; [apply msteps_refl|]. auto.
  - destruct (stop (s_pc S)).
    + injection H as <- <-. exists rho, ms. split; [apply agree_below_refl|]. split; [apply msteps_refl|]. auto.
    + destruct (sx_step segs log S) as [[log1 S1]|] eqn:Es; [|discriminate].
      destruct (sx_step_sound segs rho log log1 S S1 ms HRn Hlog Hbel Es)
        as (rho1 & ms1 & Hag1 & Hst & HRn1 & Hlog1 & Hbel1 & Hnx & Hf & Hc & Ho & Hd & Hm & Hrs & _).
      assert (Hag01 : agree_below n0 rho0 rho1).
      { intros t Ht. rewrite (Hag1 t) by lia. apply Hag0. exact Ht. }
      assert (HP1 : P S1 ms1).
      { apply (HP rho1 Hag01 S S1 ms ms1 HPS); try assumption. exact (Rn_agree segs rho rho1 S ms Hag1 HRn). }
      destruct (IH rho1 log1 log' S1 S' ms1 Hag01 ltac:(lia) HRn1 HP1 Hlog1 Hbel1 H) as (rho2 & ms2 & Hag2 & Hms & HRn2 & HP2 & Hlog2 & Hbel2).
      exists rho2, ms2. split.
      { intros t Ht. rewrite (Hag2 t) by lia. apply Hag1. exact Ht. }
      split; [exact (msteps_cons segs _ _ _ Hst Hms)|]. auto.
Qed.

End SymRun.

(* [comment removed for export] *)
Lemma CInv_sx (segs : list Segment) (rho : valuation) (M0 : mem) (W : list ivl) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) :
  (forall t rg, mget M0 t = Some rg -> rg_wr rg = true -> inside W (rbase rho t rg) (to_Z (rg_size rg))) ->
  sx_pres segs rho (CInv segs M0 W m0 F0 fc0).
Proof.
  intros W_ok S S' ms ms' HC HRn HRn' Hst Ef Ec Eo Hd Hm Hrs.
  exact (CInv_pres segs rho M0 W m0 F0 fc0 W_ok S S' ms ms' HC (Rn_R segs rho S ms HRn) Ef Ec Eo Hd Hm Hrs).
Qed.
