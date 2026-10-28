(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound HxsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs HxaHkMalloc HxaHkFrame HxaHkRelease HxaHkRealloc HxaHkPmalign HxaHkMemset HxaHkStrlen HxaHkMemcpy HxaImgSh HxaRun HxaIface HxaHandoffImg HxaHandoff.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rho_i (B : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary : word) : valuation := fun t =>
  if (t =? T_STK)%uint63 then B else if (t =? 3)%uint63 then shad B
  else if (t =? T_RA)%uint63 then bv_unsigned ra else if (t =? T_GP)%uint63 then bv_unsigned gp
  else if (t =? T_S0)%uint63 then bv_unsigned s0 else if (t =? T_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? T_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? T_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? T_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? T_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? T_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? T_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? T_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? T_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? T_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? T_S0 + 11)%uint63 then bv_unsigned s11
  else if (t =? T_CANARY)%uint63 then bv_unsigned canary else 0.

Lemma Rregs_init (rho : valuation) (ri : int)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  ri = 0%uint63 \/ ri = 16%uint63 ->
  (forall t, to_Z t < to_Z NEXT0 -> rho t = rho_i (bv_unsigned sp - to_Z ri - 262144) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary t) ->
  tp = wbv TPV ->
  Rregs rho (regs0 ri) (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros H_ri Hrho -> r.
  assert (Esp : pword rho T_STK (W false (STK + ri)%uint63) = sp).
  { unfold pword. rewrite (Hrho T_STK) by (vm_compute; reflexivity).
    change (rho_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T_STK) with (bv_unsigned sp - to_Z ri - 262144).
    assert (Ew : wZ (W false (STK + ri)%uint63) = 262144 + to_Z ri) by (destruct H_ri as [-> | ->]; reflexivity). rewrite Ew.
    replace (bv_unsigned sp - to_Z ri - 262144 + (262144 + to_Z ri)) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma final_regs_den (rho : valuation) (ri : int) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_ok ri S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho T_RA w_zero /\ x2 = pword rho T_STK (W false (STK + ri)%uint63) /\ x3 = pword rho T_GP w_zero /\ x4 = wbv TPV
  /\ x8 = pword rho T_S0 w_zero /\ x9 = pword rho (T_S0 + 1)%uint63 w_zero /\ x18 = pword rho (T_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (T_S0 + 3)%uint63 w_zero /\ x20 = pword rho (T_S0 + 4)%uint63 w_zero /\ x21 = pword rho (T_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (T_S0 + 6)%uint63 w_zero /\ x23 = pword rho (T_S0 + 7)%uint63 w_zero /\ x24 = pword rho (T_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (T_S0 + 9)%uint63 w_zero /\ x26 = pword rho (T_S0 + 10)%uint63 w_zero /\ x27 = pword rho (T_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_ok, final_regs in Hok. cbn [forallb fst snd] in Hok.
  repeat (apply andb_prop in Hok as [?E Hok]). clear Hok.
  repeat match goal with E : hval_eqb (rget S ?X) ?v = true |- _ => apply hval_eqb_eq in E end.
  pose proof (HR (Z_to_bv 5 1)) as D1. pose proof (HR (Z_to_bv 5 2)) as D2. pose proof (HR (Z_to_bv 5 3)) as D3. pose proof (HR (Z_to_bv 5 4)) as D4.
  pose proof (HR (Z_to_bv 5 8)) as D8. pose proof (HR (Z_to_bv 5 9)) as D9. pose proof (HR (Z_to_bv 5 18)) as D18. pose proof (HR (Z_to_bv 5 19)) as D19.
  pose proof (HR (Z_to_bv 5 20)) as D20. pose proof (HR (Z_to_bv 5 21)) as D21. pose proof (HR (Z_to_bv 5 22)) as D22. pose proof (HR (Z_to_bv 5 23)) as D23.
  pose proof (HR (Z_to_bv 5 24)) as D24. pose proof (HR (Z_to_bv 5 25)) as D25. pose proof (HR (Z_to_bv 5 26)) as D26. pose proof (HR (Z_to_bv 5 27)) as D27.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 1))) with (rget S X1) in D1. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 2))) with (rget S X2) in D2.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 3))) with (rget S X3) in D3. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 4))) with (rget S X4) in D4.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 8))) with (rget S X8) in D8. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 9))) with (rget S X9) in D9.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 18))) with (rget S X18) in D18. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 19))) with (rget S X19) in D19.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 20))) with (rget S X20) in D20. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 21))) with (rget S X21) in D21.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 22))) with (rget S X22) in D22. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 23))) with (rget S X23) in D23.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 24))) with (rget S X24) in D24. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 25))) with (rget S X25) in D25.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 26))) with (rget S X26) in D26. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 27))) with (rget S X27) in D27.
  repeat match goal with E : rget S ?X = _, D : den rho (rget S ?X) _ |- _ => rewrite E in D; clear E end.
  cbn [den] in *. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition start_b (ri : int) (k : Z) (rg : region) : bool :=
  (k <? 32) &&
  match rg_abs rg with
  | Some a => existsb (fun s => (fst (fst s) =? to_Z a) && (snd (fst s) =? to_Z a + to_Z (rg_size rg)) && Bool.eqb (snd s) (rg_wr rg)) STATICS
              && (negb (to_Z a =? IMGSH_LO) || (k =? 16))
  | None => ((k =? 2) && (to_Z (rg_size rg) =? 262144 + to_Z ri) && rg_wr rg)
            || ((k =? 3) && (to_Z (rg_size rg) =? (262144 + to_Z ri) / 8) && negb (rg_wr rg))
  end.

Lemma M0_checked_0 : mem_check (start_b 0) (M0 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma M0_checked_16 : mem_check (start_b 16) (M0 16) = true. Proof. vm_compute. reflexivity. Qed.
Lemma M0_imgsh_0 : mget (M0 0) 16%uint63 = Some RG_IMGSH. Proof. vm_compute. reflexivity. Qed.
Lemma M0_imgsh_16 : mget (M0 16) 16%uint63 = Some RG_IMGSH. Proof. vm_compute. reflexivity. Qed.

Lemma M0_checked (ri : int) : ri = 0%uint63 \/ ri = 16%uint63 -> mem_check (start_b ri) (M0 ri) = true /\ mget (M0 ri) 16%uint63 = Some RG_IMGSH.
Proof. intros [-> | ->]; [exact (conj M0_checked_0 M0_imgsh_0) | exact (conj M0_checked_16 M0_imgsh_16)]. Qed.

Lemma start_class (ri : int) (H_ri : ri = 0%uint63 \/ ri = 16%uint63) (t : int) (rg : region) : mget (M0 ri) t = Some rg ->
  to_Z t < 32 /\
  match rg_abs rg with
  | Some a => static_ok (to_Z a) (to_Z a + to_Z (rg_size rg)) (rg_wr rg) /\ (to_Z a = IMGSH_LO -> rg = RG_IMGSH)
  | None => (t = T_STK /\ to_Z (rg_size rg) = 262144 + to_Z ri /\ rg_wr rg = true)
            \/ (t = sh_tag T_STK /\ to_Z (rg_size rg) = (262144 + to_Z ri) / 8 /\ rg_wr rg = false)
  end.
Proof.
  intros G. destruct (M0_checked ri H_ri) as [Hck Himg]. pose proof (mem_check_ok _ _ Hck t rg G) as H. unfold start_b in H.
  apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. split; [exact H1|].
  destruct (rg_abs rg) as [a|].
  - apply andb_prop in H2 as [H2 H3]. split.
    + apply existsb_exists in H2 as ([[l h] w] & Hin & E). cbn [fst snd] in E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
      apply Z.eqb_eq in E1, E2. apply Bool.eqb_prop in E3. subst l h w. exact Hin.
    + intros Ea. rewrite Ea, Z.eqb_refl in H3. cbn [negb orb] in H3. apply Z.eqb_eq in H3.
      assert (t = 16%uint63) by (apply to_Z_inj; exact H3). subst t. rewrite Himg in G. injection G as <-. reflexivity.
  - apply orb_prop in H2 as [H2|H2]; apply andb_prop in H2 as [H2 H5]; apply andb_prop in H2 as [H3 H4]; apply Z.eqb_eq in H3, H4.
    + left. split; [apply to_Z_inj; exact H3 | split; [exact H4 | exact H5]].
    + right. split; [apply to_Z_inj; exact H3 | split; [exact H4 | apply negb_true_iff; exact H5]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma TPV_wbv : wbv TPV = Z_to_bv 64 0xba93f0. Proof. reflexivity. Qed.
Lemma e_init_pc : Z_to_bv 64 e_init = wbv (W false 2048236). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition XP_INIT : xpar := XP [] [] HxaInit.LIBW_HXA 1700 RG_IMGSH 262144.
Lemma XP_INIT_ro : rg_wr (xp_rgsh XP_INIT) = false. Proof. reflexivity. Qed.
Lemma XP_INIT_stk : stk_okx (xp_stk XP_INIT). Proof. unfold stk_okx. cbn [xp_stk XP_INIT]. split; [reflexivity | lia]. Qed.
Lemma XP_INIT_nb : NB_MAX <= xp_nbmax XP_INIT. Proof. apply Z.le_refl. Qed.

Section Main.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis LIVE_POS : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 < n.
(* [comment removed for export] *)
Hypothesis PMA : posix_memalign_init_contract RT.
Variable LIBA : rts RT -> list (Z * Z) -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Hypothesis LIBA_final : forall (ri : int) (ic : icache) (cd : xcd) (S : sstate) (CL : list (Z * Z)) (lo sp0 : Z) (m0 : word -> option byte) (cr0 anc : Z)
    (rho : valuation) (Σ' : rts RT) (ms' : machine_state),
  ri = 0%uint63 \/ ri = 16%uint63 -> run_result ri = (ic, XDone cd S) ->
  lib_pristineA m0 ->      (* [comment removed for export] *)
  XInv ctasegs SHBW (ghost RT) (FInv RT CL lo sp0 (to_Z ri) m0 cr0 anc XP_INIT) (GH RT Σ') rho cd S ms' ->
  LIBA Σ' (blk_list rho (s_mem S) (x_blocks cd)) (ms_mem ms').

Lemma init_residue (ri : int) (H_ri : ri = 0%uint63 \/ ri = 16%uint63) (Hcert : run_ok ri (run_result ri) = true) :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : word -> option byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba93f0 ->
  rt_frames RT Σ = [] -> lroom3 (rt_live RT Σ) INIT_LIVE INIT_PB INIT_NB -> INIT_COST <= rt_credit RT Σ ->      (* [comment removed for export] *)
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lib_pristineA m -> ART RT Σ m -> mem_inv ctasegs m ->
  stk ctasegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + INIT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = to_Z ri ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_init m)))
    (fun c => exists (Σ' : rts RT) (LW : list (Z * Z)) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) [] (bv_unsigned sp) HxaIface.LIBW_HXA m m' /\ LIBA Σ' LW m') c
       /\ rt_live RT Σ' = LW ++ rt_live RT Σ /\ (Z.of_nat (length LW) <= INIT_LIVE /\ psum LW <= INIT_PB /\ nbig LW <= INIT_NB) /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - INIT_COST <= rt_credit RT Σ').
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         Hfdfs Hmat Etp Hfr0 Hlive Hcred Hs0 [V_lib C_key] HART Hmi Hstk Hlo1 Hlo2 Hsp47 Hsp32.
  intros T c Hc Hk.
  assert (Hr01 : to_Z ri = 0 \/ to_Z ri = 16) by (destruct H_ri as [-> | ->]; [left | right]; reflexivity).
  unfold INIT_PB, INIT_NB, INIT_COST, INIT_STACK in *.      (* [comment removed for export] *)
  set (sp0 := bv_unsigned sp) in *. set (B := sp0 - to_Z ri - 262144).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (af_sp0_win RT AF _ _ HART) as Hsp0w.
  (* [comment removed for export] *)
  destruct (af_client_consts RT AF _ _ HART) as (_ & C_shb & _ & C_uar & Hrelro).
  unfold g_shadow_memory_dynamic_address in C_shb. unfold g_detect_stack_use_after_return in C_uar.
  assert (V_relro : forall a, 5451776 <= a < 5947392 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a)).
  { intros a Ha. apply Hrelro. rewrite wa_unsigned by lia. unfold RELRO_LO, RELRO_HI. lia. }
  pose proof (proj1 (af_tsd RT AF _ _ HART)) as C_tsd0. pose proof (af_tsd RT AF _ _ HART) as C_tsd.
  destruct (seg_rw_c8' m 12358704 seg_rw_guard) as (canary & C_can0). pose proof (proj1 C_can0) as C_can.
  assert (Z_stk : forall i, 0 <= i < (262144 + to_Z ri) / 8 -> mrd ctasegs m (wa (shad B + i)) = Some z8).
  { intros i Hi. rewrite <- (shad_add8 B i).
    assert (HB32 : B mod 8 = 0).
    { unfold B. pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32 in D.
      replace (sp0 - to_Z ri - 262144) with (0 + (4 * (sp0 / 32) - 32768) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    apply acc_granule_zero; [rewrite Z.add_mod, HB32, Z.mul_comm, Z.mod_mul by lia; reflexivity|].
    apply (af_acc_stack RT AF Σ m _ _ HART); unfold B, USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia. }
  set (rho0 := rho_i B ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary).
  set (ms0 := entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_init m).
  (* [comment removed for export] *)
  assert (HXI : XInv ctasegs SHBW (ghost RT) (FInv RT (rt_live RT Σ) lo sp0 (to_Z ri) m (rt_credit RT Σ) (rt_sp0 RT Σ) XP_INIT) (GH RT Σ) rho0 (XCD [] [] 0 0) (S0 ri) ms0).
  { (* [comment removed for export] *)
    unfold XInv, RSn, Rn, R, FInv. cbn [S0 s_pc s_regs s_resv s_mem s_next].
    split; [split|split; [|split; [reflexivity | unfold ms0, entry_st; cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
    - (* [comment removed for export] *)
      intros rho2 Hag.
      assert (Hrho : forall t, to_Z t < to_Z NEXT0 -> rho2 t = rho0 t) by exact Hag.
      unfold ms0, entry_st. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS].
      split; [reflexivity|]. split; [exact e_init_pc|]. split.
      { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS].
        apply (Rregs_init rho2 ri ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary F _ fc None H_ri Hrho).
        rewrite Etp. symmetry. exact TPV_wbv. }
      split; [reflexivity|].
      apply (rmem0 rho2 m ri H_ri Hmi V_relro V_lib C_key C_shb C_uar C_tsd canary C_can (Hrho T_CANARY ltac:(vm_compute; reflexivity))
               (IMGSH_OK RT AF Σ m rho2 T_IMGSH HART) lo sp0 Hstk (Hrho T_STK ltac:(vm_compute; reflexivity)) (Hrho 3%uint63 ltac:(vm_compute; reflexivity)));
        unfold STACK_WIN, USTACK_TOP in *; try lia; try assumption.
    - (* [comment removed for export] *)
      intros rho2 Hag s rg G Ea Hodd.
      destruct (start_class ri H_ri s rg G) as [_ C]. rewrite Ea in C. rewrite SHBW_Z.
      destruct C as [(-> & _)|(-> & _)]; [discriminate Hodd|].
      rewrite (Hag (sh_tag T_STK)) by (vm_compute; reflexivity). change ((sh_tag T_STK - 1)%uint63) with T_STK. rewrite (Hag T_STK) by (vm_compute; reflexivity). reflexivity.
    - (* [comment removed for export] *)
      unfold FMem. cbv zeta. cbn [x_blocks x_frames x_calls x_nb g_S ms_mem ms0 entry_st MS blk_list frm_list map app length].
      split; [reflexivity|]. split; [exact Hfr0|]. split; [constructor|]. split; [intros t []|].
      split; [intros t rg G; exact (proj1 (start_class ri H_ri t rg G))|]. split; [lia|]. split; [vm_compute; reflexivity|].
      split.
      { intros t rg G. destruct (start_class ri H_ri t rg G) as [_ C]. destruct (rg_abs rg) as [a|].
        - destruct C as [C Cimg]. right. split; [exists (rg_wr rg); split; [exact C | auto]|]. split; [exact Cimg|].
          intros Hw. rewrite Hw in C. destruct (static_facts _ _ _ C) as (_ & _ & _ & _ & S5 & _). exact (proj2 (S5 eq_refl)).
        - change (xp_stk XP_INIT) with 262144. destruct C as [C|C]; [left; exact C | right; left; exact C]. }
      split; [split; intros t []|].
      split.
      { split; [reflexivity|]. split; [reflexivity|]. split; [intros t []|].
        change (rho0 T_S0) with (bv_unsigned s0). split; [pose proof (bv_unsigned_in_range 64 s0) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X | exact Hs0]. }
      split; [exact HART|]. split; [exact Hmi|]. split; [exact Hstk|].
      split; [unfold B0; change (xp_stk XP_INIT) with 262144; repeat split; lia|].
      split; [split; [cbn [xp_nbmax XP_INIT]; unfold INIT_LIVE in Hlive; exact Hlive | repeat split; lia]|]. split; [intros; reflexivity|]. split; [reflexivity | intros t n w []]. }
  (* [comment removed for export] *)
  assert (Hks : forall h, In h hooksA -> xhook_ok ctasegs SHBW (ghost RT) (J RT PMc T) (FInv RT (rt_live RT Σ) lo sp0 (to_Z ri) m (rt_credit RT Σ) (rt_sp0 RT Σ) XP_INIT) h).
  { intros h Hin. unfold hooksA in Hin. cbn [In] in Hin.
    assert (Hcr : CALLS_MAX <= rt_credit RT Σ) by (unfold CALLS_MAX; lia).
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].      (* [comment removed for export] *)
    - exact (hkA_malloc_ok RT AF RTC PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk XP_INIT_nb (IMGSH_OK RT AF)).
    - exact (hkA_realloc_ok RT AF RTC LIVE_POS PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk XP_INIT_nb (IMGSH_OK RT AF)).
    - exact (hkA_free_ok RT AF RTC PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_ro XP_INIT_stk (IMGSH_OK RT AF)).
    - exact (hkA_memset_ok RT AF RTC PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk XP_INIT_ro (IMGSH_OK RT AF)).
    - exact (hkA_stack_malloc0_ok RT AF PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m (rt_credit RT Σ) _ XP_INIT Hr01 XP_INIT_stk Hcr (IMGSH_OK RT AF) (rc_stack_malloc_0 RT RTC)).
    - exact (hkA_release_ok RT AF PMc Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk).
    - exact (hkA_stack_malloc1_ok RT AF PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m (rt_credit RT Σ) _ XP_INIT Hr01 XP_INIT_stk Hcr (IMGSH_OK RT AF) (rc_stack_malloc_1 RT RTC)).
    - exact (hkA_posix_memalign_ok RT AF PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk XP_INIT_nb (IMGSH_OK RT AF) PMA).
    - exact (hkA_memcpy_ok RT AF RTC PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk XP_INIT_ro (IMGSH_OK RT AF)).
    - exact (hkA_strlen_ok RT AF RTC PMc Hfdfs Hmat T _ lo sp0 (to_Z ri) m _ _ XP_INIT Hr01 XP_INIT_stk XP_INIT_ro (IMGSH_OK RT AF)). }
  (* [comment removed for export] *)
  destruct (run_ok_inv ri (run_result ri) Hcert) as (icE & cdE & SE & Erun & Efr & Epc & Erv & Hregs & Hcalls & Hnb).
  pose proof Erun as Erun'. rewrite run_result_unfold in Erun'.
  refine (hxs_drive_sound_step ctasegs SHBW hookixA hooksA finalA (ghost RT) (J RT PMc T) _ (J_evt RT AF PMc Hmat T)
            (FInv_step RT AF (rt_live RT Σ) lo sp0 (to_Z ri) m (rt_credit RT Σ) (rt_sp0 RT Σ) XP_INIT Hr01 XP_INIT_ro XP_INIT_stk) Hks 23 4000 IEmpty icE (XCD [] [] 0 0) cdE (S0 ri) SE
            (GH RT Σ) rho0 ms0 (ic_ok_empty ctasegs) HXI Erun' _ c Hc).
  (* [comment removed for export] *)
  intros g' rho' ms' Hag' [[HRn' Hlaw'] [HF' (Hro' & Hnf')]]. cbn [S0 s_next] in Hag'.
  pose proof (LIBA_final ri icE cdE SE (rt_live RT Σ) lo sp0 m (rt_credit RT Σ) (rt_sp0 RT Σ) rho' (g_S RT g') ms' H_ri Erun (conj V_lib C_key)) as HLIBA.
  assert (Hgh : GH RT (g_S RT g') = g') by (destruct g'; reflexivity). rewrite Hgh in HLIBA.
  specialize (HLIBA (conj (conj HRn' Hlaw') (conj HF' (conj Hro' Hnf')))).
  apply (J_evt RT AF PMc Hmat T g' ms').
  pose proof (Rn_R ctasegs rho' SE ms' HRn') as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_final as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step ctasegs rho' IEmpty ic' SE ms' (ic_ok_empty ctasegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_one ctasegs _ _ Hstep)|].
  intros c2 Hc2. apply Hk.
  destruct HF' as (Hlive' & Hfr' & Hnd' & Htl' & Htags' & Hnx0' & Hnx' & Hcls' & Hlink' & Hrho' & HART' & Hmi' & Hstk' & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2n & Hc3 & Hc4) & Hagr' & Hanc' & _).
  rewrite Efr in Hfr'. cbn [frm_list map] in Hfr'.
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf' as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                    & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hro', Hrv in Ems2.
  destruct (final_regs_den rho' ri SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Hrho0 : forall t, to_Z t < to_Z NEXT0 -> rho' t = rho0 t) by exact Hag'.
  rewrite (pword_scalar rho' T_RA ra) in E1 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' T_GP gp) in E3 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' T_S0 s0) in E8 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 1)%uint63 s1) in E9 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 2)%uint63 s2) in E18 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 3)%uint63 s3) in E19 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 4)%uint63 s4) in E20 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 5)%uint63 s5) in E21 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 6)%uint63 s6) in E22 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 7)%uint63 s7) in E23 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 8)%uint63 s8) in E24 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 9)%uint63 s9) in E25 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 10)%uint63 s10) in E26 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 11)%uint63 s11) in E27 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. rewrite (Hrho0 T_STK) by (vm_compute; reflexivity). change (rho0 T_STK) with B.
    assert (Ew : wZ (W false (STK + ri)%uint63) = 262144 + to_Z ri) by (destruct H_ri as [-> | ->]; reflexivity). rewrite Ew.
    unfold B. replace (sp0 - to_Z ri - 262144 + (262144 + to_Z ri)) with sp0 by lia. apply Z_to_bv_bv_unsigned. }
  assert (E4' : y4 = tp) by (rewrite E4, Etp; exact TPV_wbv).
  subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2. rewrite E2', E4' in Ems2.
  exists (g_S RT g'), (blk_list rho' (s_mem SE) (x_blocks cdE)), y10.
  split.
  { apply (ASTA_conseq RT (g_S RT g') PMc (eq ms2) _ c2 Hc2). intros ms <-. exists (ms_mem ms').
    split; [exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, (ms_fregs ms'), (ms_fcsr ms'); exact Ems2|].
    split; [split; [exact HART' | split; [exact Hmi' | exact Hstk']]|].
    split; [|exact HLIBA].
    intros a Ha Hout. apply Hagr'. split; [exact Ha | split; [exact Hout | exact I]]. }
  split; [exact Hlive'|].
  split. { pose proof (psum_le_len (blk_list rho' (s_mem SE) (x_blocks cdE))) as WBL. pose proof (nbig_le_len (blk_list rho' (s_mem SE) (x_blocks cdE))) as NBL.
           unfold blk_list in *. rewrite length_map in *. unfold INIT_LIVE, LW_MAX in *. repeat split; lia. }      (* [comment removed for export] *)
  split; [exact Hfr'|]. split; [exact Hanc'|]. lia.
Qed.

(* [comment removed for export] *)
Theorem init_cps_hx : init_cps RT LIBA.
Proof.
  unfold init_cps. intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         Hfdfs Hmat Etp Hfr0 Hlive Hcred Hs0 Hlibp HART Hmi Hstk Hlo1 Hlo2 Hsp47 Hsp16.
  assert (Hres : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct Hres as [Hres|Hres].
  - exact (init_residue 0%uint63 (or_introl eq_refl) run_checked_0 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             Hfdfs Hmat Etp Hfr0 Hlive Hcred Hs0 Hlibp HART Hmi Hstk Hlo1 Hlo2 Hsp47 Hres).
  - exact (init_residue 16%uint63 (or_intror eq_refl) run_checked_16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             Hfdfs Hmat Etp Hfr0 Hlive Hcred Hs0 Hlibp HART Hmi Hstk Hlo1 Hlo2 Hsp47 Hres).
Qed.

End Main.
