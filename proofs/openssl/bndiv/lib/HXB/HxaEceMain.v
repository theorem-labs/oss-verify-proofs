(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface D_defs. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import SegRw.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require SiteData.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaEceInit HxaEceShCert HxaImage HxaInv HxaHooks HxaHk HxaHkFrame HxaHkRelease HxaImgSh HxaQuery HxaEceRun HxaEceIface HxaHandoffImg HxaHandoff HxaEceHandoff HxaMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rho_e (B : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (MK SA ND ES : Z) : valuation := fun t =>
  if (t =? T_STK)%uint63 then B else if (t =? 3)%uint63 then shad B
  else if (t =? TE_GP)%uint63 then bv_unsigned gp
  else if (t =? T_S0)%uint63 then bv_unsigned s0 else if (t =? T_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? T_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? T_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? T_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? T_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? T_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? T_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? T_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? T_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? T_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? T_S0 + 11)%uint63 then bv_unsigned s11
  else if (t =? 32)%uint63 then MK else if (t =? 33)%uint63 then shad MK
  else if (t =? 34)%uint63 then SA else if (t =? 35)%uint63 then shad SA
  else if (t =? 36)%uint63 then ND else if (t =? 37)%uint63 then shad ND
  else if (t =? 38)%uint63 then ES else if (t =? 39)%uint63 then shad ES
  else 0.

Lemma Rregs_initE (rho : valuation) (ri : int)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (B : Z) (MK SA ND ES : Z)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  ri = 0%uint63 \/ ri = 16%uint63 ->
  (forall t, to_Z t < to_Z NEXTE -> rho t = rho_e B gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 MK SA ND ES t) ->
  B = bv_unsigned sp - to_Z ri - 81920 ->
  tp = wbv TPV -> ra = wbv RA_ECE ->
  Rregs rho (regsE ri) (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros H_ri Hrho EB -> -> r.
  assert (Esp : pword rho T_STK (W false (ESTK + ri)%uint63) = sp).
  { unfold pword. rewrite (Hrho T_STK) by (vm_compute; reflexivity).
    change (rho_e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T_STK) with B.
    assert (Ew : wZ (W false (ESTK + ri)%uint63) = 81920 + to_Z ri) by (destruct H_ri as [-> | ->]; reflexivity). rewrite Ew, EB.
    replace (bv_unsigned sp - to_Z ri - 81920 + (81920 + to_Z ri)) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma final_regs_denE (rho : valuation) (ri : int) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_ok_E ri S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = wbv RA_ECE /\ x2 = pword rho T_STK (W false (ESTK + ri)%uint63) /\ x3 = pword rho TE_GP w_zero /\ x4 = wbv TPV
  /\ x8 = pword rho T_S0 w_zero /\ x9 = pword rho (T_S0 + 1)%uint63 w_zero /\ x18 = pword rho (T_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (T_S0 + 3)%uint63 w_zero /\ x20 = pword rho (T_S0 + 4)%uint63 w_zero /\ x21 = pword rho (T_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (T_S0 + 6)%uint63 w_zero /\ x23 = pword rho (T_S0 + 7)%uint63 w_zero /\ x24 = pword rho (T_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (T_S0 + 9)%uint63 w_zero /\ x26 = pword rho (T_S0 + 10)%uint63 w_zero /\ x27 = pword rho (T_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_ok_E, final_regs_E in Hok. cbn [forallb fst snd] in Hok.
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

Definition start_bE (ri : int) (k : Z) (rg : region) : bool :=
  (k <? 40) &&
  match rg_abs rg with
  | Some a => existsb (fun s => (fst (fst s) =? to_Z a) && (snd (fst s) =? to_Z a + to_Z (rg_size rg))) STATICS
              && negb (rg_wr rg) && (negb (to_Z a =? IMGSH_LO) || (k =? 11))
  | None => ((k =? 2) && (to_Z (rg_size rg) =? 81920 + to_Z ri) && rg_wr rg)
            || ((k =? 3) && (to_Z (rg_size rg) =? (81920 + to_Z ri) / 8) && negb (rg_wr rg))
            || existsb (fun e => (k =? to_Z (fst (fst e))) && (to_Z (rg_size rg) =? snd (fst e)) && Bool.eqb (rg_wr rg) (snd e)) CBT_E
            || existsb (fun e => (k =? to_Z (sh_tag (fst (fst e)))) && (to_Z (rg_size rg) =? snd (fst e) / 8) && negb (rg_wr rg)) CBT_E
  end.

Lemma ME_checked_0 : mem_check (start_bE 0) (ME 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ME_checked_16 : mem_check (start_bE 16) (ME 16) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ME_imgsh_0 : mget (ME 0) 11%uint63 = Some RG_IMGSH_E. Proof. vm_compute. reflexivity. Qed.
Lemma ME_imgsh_16 : mget (ME 16) 11%uint63 = Some RG_IMGSH_E. Proof. vm_compute. reflexivity. Qed.

Lemma ME_checked (ri : int) : ri = 0%uint63 \/ ri = 16%uint63 -> mem_check (start_bE ri) (ME ri) = true /\ mget (ME ri) 11%uint63 = Some RG_IMGSH_E.
Proof. intros [-> | ->]; [exact (conj ME_checked_0 ME_imgsh_0) | exact (conj ME_checked_16 ME_imgsh_16)]. Qed.

Lemma start_classE (ri : int) (H_ri : ri = 0%uint63 \/ ri = 16%uint63) (t : int) (rg : region) : mget (ME ri) t = Some rg ->
  to_Z t < 40 /\
  match rg_abs rg with
  | Some a => (exists w, static_ok (to_Z a) (to_Z a + to_Z (rg_size rg)) w) /\ rg_wr rg = false /\ (to_Z a = IMGSH_LO -> rg = RG_IMGSH_E)
  | None => (t = T_STK /\ to_Z (rg_size rg) = 81920 + to_Z ri /\ rg_wr rg = true)
            \/ (t = sh_tag T_STK /\ to_Z (rg_size rg) = (81920 + to_Z ri) / 8 /\ rg_wr rg = false)
            \/ (exists b n w, In (b, n, w) CBT_E /\ t = b /\ to_Z (rg_size rg) = n /\ rg_wr rg = w)
            \/ (exists b n w, In (b, n, w) CBT_E /\ t = sh_tag b /\ to_Z (rg_size rg) = n / 8 /\ rg_wr rg = false)
  end.
Proof.
  intros G. destruct (ME_checked ri H_ri) as [Hck Himg]. pose proof (mem_check_ok _ _ Hck t rg G) as H. unfold start_bE in H.
  apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. split; [exact H1|].
  destruct (rg_abs rg) as [a|].
  - apply andb_prop in H2 as [H2 H4]. apply andb_prop in H2 as [H2 H3]. split; [|split].
    + apply existsb_exists in H2 as ([[l h] w] & Hin & E). cbn [fst snd] in E. apply andb_prop in E as [E1 E2].
      apply Z.eqb_eq in E1, E2. subst l h. exists w. exact Hin.
    + apply negb_true_iff in H3. exact H3.
    + intros Ea. rewrite Ea, Z.eqb_refl in H4. cbn [negb orb] in H4. apply Z.eqb_eq in H4.
      assert (t = 11%uint63) by (apply to_Z_inj; exact H4). subst t. rewrite Himg in G. injection G as <-. reflexivity.
  - apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]|]|].
    + apply andb_prop in H2 as [H2 H5]; apply andb_prop in H2 as [H3 H4]; apply Z.eqb_eq in H3, H4.
      left. split; [apply to_Z_inj; exact H3 | split; [exact H4 | exact H5]].
    + apply andb_prop in H2 as [H2 H5]; apply andb_prop in H2 as [H3 H4]; apply Z.eqb_eq in H3, H4.
      right; left. split; [apply to_Z_inj; exact H3 | split; [exact H4 | apply negb_true_iff; exact H5]].
    + right; right; left. apply existsb_exists in H2 as ([[b n] w] & Hin & E). cbn [fst snd] in E.
      apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. apply Bool.eqb_prop in E3.
      exists b, n, w. split; [exact Hin|]. split; [apply to_Z_inj; exact E1 | split; [exact E2 | exact E3]].
    + right; right; right. apply existsb_exists in H2 as ([[b n] w] & Hin & E). cbn [fst snd] in E.
      apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. apply negb_true_iff in E3.
      exists b, n, w. split; [exact Hin|]. split; [apply to_Z_inj; exact E1 | split; [exact E2 | exact E3]].
Qed.

(* [comment removed for export] *)
Lemma CBT_E_cases (b : int) (n : Z) (w : bool) : In (b, n, w) CBT_E ->
  (b = 32%uint63 /\ n = 72 /\ w = false) \/ (b = 34%uint63 /\ n = 32 /\ w = false) \/ (b = 36%uint63 /\ n = 128 /\ w = false) \/ (b = 38%uint63 /\ n = 904 /\ w = true).
Proof.
  unfold CBT_E. cbn [In]. intros [E|[E|[E|[E|[]]]]]; injection E as <- <- <-; [left | right; left | right; right; left | right; right; right]; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma traces_checked_E : forallb (fun tr => existsb (zlist_eqb (map to_Z tr)) SiteData.SITE_TRACES) TRACES_E = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TRACES_OK_E : traces_ok TRACES_E.
Proof.
  intros tr Hin. pose proof (proj1 (forallb_forall _ _) traces_checked_E tr Hin) as H. cbv beta in H.
  apply existsb_exists in H as (l & Hl & E). apply zlist_eqb_eq in E. rewrite E. exact Hl.
Qed.

Lemma imgsh_checked_E : cells_check (cell_why_ok IMGSH_CERT_E) (rg_cells RG_IMGSH_E) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma TPV_wbv_E : wbv TPV = wz TP_A. Proof. reflexivity. Qed.
Lemma e_ece_pc : wz e_ece = wbv (W false 2048852). Proof. reflexivity. Qed.
Lemma RA_ECE_wz : wz ECE_RA = wbv RA_ECE. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma acc_zero_sh (m : word -> option byte) (p n : Z) : p mod 8 = 0 -> acc bsegs m p n ->
  forall i, 0 <= i < n / 8 -> mrd bsegs m (wa (shad p + i)) = Some z8.
Proof.
  intros Hp Hacc i Hi. rewrite <- (shad_add8 p i).
  apply acc_granule_zero; [rewrite Z.add_mod, Hp, Z.mul_comm, Z.mod_mul by lia; reflexivity|].
  intros j Hj. replace (p + 8 * i + j) with (p + (8 * i + j)) by lia. apply Hacc. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xpE (ES ncl : Z) : xpar := XP CBT_E [(ES, ES + 904)] [] (LIVE_MAX - ncl) RG_IMGSH_E 81920.
Lemma xpE_ro (ES ncl : Z) : rg_wr (xp_rgsh (xpE ES ncl)) = false. Proof. reflexivity. Qed.
Lemma xpE_stk (ES ncl : Z) : stk_okx (xp_stk (xpE ES ncl)). Proof. unfold stk_okx. cbn [xp_stk xpE]. split; [reflexivity | lia]. Qed.

Section Main.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma frel_E : frame_release_x RT.
Proof. exact (af_frame_release RT AF). Qed.

Lemma IMGSH_OK_E : forall (Σ : rts RT) (m : word -> option byte) (rho : valuation) (t : int), ART RT Σ m -> region_ok bsegs rho t RG_IMGSH_E m.
Proof. exact (imgsh_region_ok RT AF RG_IMGSH_E IMGSH_CERT_E eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl imgsh_checked_E). Qed.

Lemma ece_residue (ri : int) (H_ri : ri = 0%uint63 \/ ri = 16%uint63) (Hcert : run_ok_E ri (run_result_E ri) = true) :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (EA : err_addrs) (lo : Z),
    AHEAP Σ OW LB m -> stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - ECE_STACK ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = to_Z ri -> mem_inv bsegs m -> tp = wz TP_A ->
    ra = wz ECE_RA ->
    (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
    crypto_statics m -> err_inv m OW EA -> ECE_COST <= rt_credit RT Σ ->
    cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz e_ece) fc None m (seg_rom bsegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (ece_postA ECE_COST ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB EA lo m Σ') c).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB EA lo
         HAH Hstk Hceil Hlo2 Hsp47 Hsp32 Hmi Etp Era Hs0 HCS HERR Hcred.
  intros T c Hc Hk.
  assert (Hr01 : to_Z ri = 0 \/ to_Z ri = 16) by (destruct H_ri as [-> | ->]; [left | right]; reflexivity).
  pose proof HAH as (HART & Hanc & Hfr0 & Hperm & Hnd & HokOW & HposLB).
  unfold ECE_COST, ECE_STACK in *.
  set (sp0 := bv_unsigned sp) in *. set (B := sp0 - to_Z ri - 81920).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof (af_sp0_win RT AF _ _ HART) as Hsp0w.
  assert (Hlo1 : rt_sp0 RT Σ - STACK_WIN <= lo) by (unfold BnHeapA.ACEIL in Hceil; rewrite Hanc; exact Hceil).
  (* [comment removed for export] *)
  destruct EA as [MK SA ND ES pk ps pn pe].
  destruct HERR as [(C_stopped & C_optsdone & C_base_once & C_base_ret & C_master_once & C_master_key) (I_mk & I_sa & I_nd & I_es & C_slot & C_mk & [pad C_sa] & C_nd & C_es)].
  cbn [ea_MK ea_SA ea_ND ea_ES ea_pk ea_ps ea_pn ea_pe] in I_mk, I_sa, I_nd, I_es, C_slot, C_mk, C_sa, C_nd, C_es.
  destruct HCS as (C_memset & C_malloc & C_free & _).
  change (TSD_MAIN + 8 * TL_MASTER_KEY_IDX) with 12567056 in C_slot.
  (* [comment removed for export] *)
  assert (L_mk : In (MK, 72) (rt_live RT Σ)) by exact (AH_live Σ OW LB m (pk, MK, 72) HAH (in_or_app _ _ _ (or_introl I_mk))).
  assert (L_sa : In (SA, 32) (rt_live RT Σ)) by exact (AH_live Σ OW LB m (ps, SA, 32) HAH (in_or_app _ _ _ (or_introl I_sa))).
  assert (L_nd : In (ND, 128) (rt_live RT Σ)) by exact (AH_live Σ OW LB m (pn, ND, 128) HAH (in_or_app _ _ _ (or_introl I_nd))).
  assert (L_es : In (ES, 904) (rt_live RT Σ)) by exact (AH_live Σ OW LB m (pe, ES, 904) HAH (in_or_app _ _ _ (or_introl I_es))).
  assert (RNG : forall p A n, In (p, A, n) OW -> In (A, n) (rt_live RT Σ) -> chunk_rng lo A n).
  { intros p A n Hin HL. destruct (AH_range Σ OW LB m p A n HAH Hin) as (X1 & X2 & X3 & X4 & X5).
    pose proof (af_live_offshadow RT AF Σ m A n HART HL) as X6. unfold chunk_rng. unfold BnHeapA.ACEIL in X4, Hceil.
    split; [exact X1|]. split; [exact X2|]. split; [lia|]. split; [exact X5 | exact X6]. }
  pose proof (RNG pk MK 72 I_mk L_mk) as R_mk. pose proof (RNG ps SA 32 I_sa L_sa) as R_sa.
  pose proof (RNG pn ND 128 I_nd L_nd) as R_nd. pose proof (RNG pe ES 904 I_es L_es) as R_es. clear RNG.
  assert (APT : forall p A n, In (p, A, n) OW -> n <> 904 -> apart ES 904 A n).
  { intros p A n Hin Hne. unfold apart. apply (AH_disjoint Σ OW LB m pe ES 904 p A n HAH I_es Hin).
    intros E. subst p. destruct (AH_addr_unique OW pe ES 904 A n (AH_nodup_l Σ OW LB m HAH) I_es Hin) as [_ En]. exact (Hne (eq_sym En)). }
  pose proof (APT pk MK 72 I_mk ltac:(lia)) as D_mk. pose proof (APT ps SA 32 I_sa ltac:(lia)) as D_sa. pose proof (APT pn ND 128 I_nd ltac:(lia)) as D_nd. clear APT.
  destruct (AH_acc Σ OW LB m (pk, MK, 72) HAH (in_or_app _ _ _ (or_introl I_mk))) as [W_mk A_mk].
  destruct (AH_acc Σ OW LB m (ps, SA, 32) HAH (in_or_app _ _ _ (or_introl I_sa))) as [W_sa A_sa].
  destruct (AH_acc Σ OW LB m (pn, ND, 128) HAH (in_or_app _ _ _ (or_introl I_nd))) as [W_nd A_nd].
  destruct (AH_acc Σ OW LB m (pe, ES, 904) HAH (in_or_app _ _ _ (or_introl I_es))) as [W_es A_es].
  cbn [blk_addr blk_size fst snd] in W_mk, A_mk, W_sa, A_sa, W_nd, A_nd, W_es, A_es.
  pose proof (acc_zero_sh m MK 72 ltac:(pose proof R_mk as (_ & X & _); Z.div_mod_to_equations; lia) A_mk) as Z_mk.
  pose proof (acc_zero_sh m SA 32 ltac:(pose proof R_sa as (_ & X & _); Z.div_mod_to_equations; lia) A_sa) as Z_sa.
  pose proof (acc_zero_sh m ND 128 ltac:(pose proof R_nd as (_ & X & _); Z.div_mod_to_equations; lia) A_nd) as Z_nd.
  pose proof (acc_zero_sh m ES 904 ltac:(pose proof R_es as (_ & X & _); Z.div_mod_to_equations; lia) A_es) as Z_es.
  change (72 / 8) with 9 in Z_mk. change (32 / 8) with 4 in Z_sa. change (128 / 8) with 16 in Z_nd. change (904 / 8) with 113 in Z_es.
  (* [comment removed for export] *)
  destruct (af_client_consts RT AF _ _ HART) as (_ & C_shb & _ & C_uar & Hrelro).
  unfold g_shadow_memory_dynamic_address in C_shb. unfold g_detect_stack_use_after_return in C_uar.
  assert (V_relro : forall a, 5681152 <= a < 6172672 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a)).
  { intros a Ha. apply Hrelro. rewrite wa_unsigned by lia. unfold RELRO_LO, RELRO_HI. lia. }
  pose proof (af_tsd RT AF _ _ HART) as C_tsd.
  (* [comment removed for export] *)
  assert (Hlo : lo <= B) by (unfold B; lia).
  assert (Hlo0 : 0x7fff00000000 <= lo) by (unfold STACK_WIN in Hlo1; lia).
  assert (Z_stk : forall i, 0 <= i < (81920 + to_Z ri) / 8 -> mrd bsegs m (wa (shad B + i)) = Some z8).
  { intros i Hi. rewrite <- (shad_add8 B i).
    assert (HB32 : B mod 8 = 0).
    { unfold B. pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32 in D.
      replace (sp0 - to_Z ri - 81920) with (0 + (4 * (sp0 / 32) - 10240) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    apply acc_granule_zero; [rewrite Z.add_mod, HB32, Z.mul_comm, Z.mod_mul by lia; reflexivity|].
    apply (af_acc_stack RT AF Σ m _ _ HART); unfold B, USTACK_TOP, STACK_WIN in *; Z.div_mod_to_equations; lia. }
  set (rho0 := rho_e B gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 MK SA ND ES).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_ece) fc None m (seg_rom bsegs)) in Hc.
  set (xp := xpE ES (Z.of_nat (length (rt_live RT Σ)))).
  (* [comment removed for export] *)
  assert (HXI : XInv bsegs SHBW (ghost RT) (FInv RT (rt_live RT Σ) lo sp0 (to_Z ri) m (rt_credit RT Σ) (rt_sp0 RT Σ) xp) (GH RT Σ) rho0 (XCD [] [] 0 0) (SE0 ri) ms0).
  { (* [comment removed for export] *)
    unfold XInv, RSn, Rn, R, FInv. cbn [SE0 s_pc s_regs s_resv s_mem s_next].
    split; [split|split; [|split; [reflexivity | unfold ms0; cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
    - (* [comment removed for export] *)
      intros rho2 Hag.
      assert (Hrho : forall t, to_Z t < to_Z NEXTE -> rho2 t = rho0 t) by exact Hag.
      unfold ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS].
      split; [reflexivity|]. split; [exact e_ece_pc|]. split.
      { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS].
        apply (Rregs_initE rho2 ri ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 B MK SA ND ES F _ fc None H_ri Hrho eq_refl).
        - rewrite Etp. symmetry. exact TPV_wbv_E.
        - rewrite Era. exact RA_ECE_wz. }
      split; [reflexivity|].
      exact (rmemE rho2 m ri H_ri Hmi V_relro C_shb C_uar C_tsd C_memset C_malloc C_free C_stopped C_optsdone C_base_once C_base_ret C_master_once C_master_key
               (IMGSH_OK_E Σ m rho2 TE_IMGSH HART) lo sp0 Hstk (Hrho T_STK ltac:(vm_compute; reflexivity)) (Hrho 3%uint63 ltac:(vm_compute; reflexivity))
               Hlo Hlo0 Hsp47 Hsp32 Z_stk MK SA ND ES pad C_slot C_mk C_sa C_nd C_es W_mk W_sa W_nd Z_mk Z_sa Z_nd Z_es
               (Hrho 32%uint63 ltac:(vm_compute; reflexivity)) (Hrho 33%uint63 ltac:(vm_compute; reflexivity))
               (Hrho 34%uint63 ltac:(vm_compute; reflexivity)) (Hrho 35%uint63 ltac:(vm_compute; reflexivity))
               (Hrho 36%uint63 ltac:(vm_compute; reflexivity)) (Hrho 37%uint63 ltac:(vm_compute; reflexivity))
               (Hrho 38%uint63 ltac:(vm_compute; reflexivity)) (Hrho 39%uint63 ltac:(vm_compute; reflexivity))
               R_mk R_sa R_nd R_es D_mk D_sa D_nd).
    - (* [comment removed for export] *)
      intros rho2 Hag s rg G Ea Hodd.
      destruct (start_classE ri H_ri s rg G) as [_ C]. rewrite Ea in C. rewrite SHBW_Z.
      destruct C as [(-> & _)|[(-> & _)|[(b & n & w & Hin & -> & _)|(b & n & w & Hin & -> & _)]]].
      + discriminate Hodd.
      + rewrite (Hag (sh_tag T_STK)) by (vm_compute; reflexivity). change ((sh_tag T_STK - 1)%uint63) with T_STK.
        rewrite (Hag T_STK) by (vm_compute; reflexivity). reflexivity.
      + exfalso. destruct (CBT_E_cases b n w Hin) as [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]]; discriminate Hodd.
      + destruct (CBT_E_cases b n w Hin) as [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]].
        * rewrite (Hag (sh_tag 32%uint63)) by (vm_compute; reflexivity). change ((sh_tag 32 - 1)%uint63) with 32%uint63.
          rewrite (Hag 32%uint63) by (vm_compute; reflexivity). reflexivity.
        * rewrite (Hag (sh_tag 34%uint63)) by (vm_compute; reflexivity). change ((sh_tag 34 - 1)%uint63) with 34%uint63.
          rewrite (Hag 34%uint63) by (vm_compute; reflexivity). reflexivity.
        * rewrite (Hag (sh_tag 36%uint63)) by (vm_compute; reflexivity). change ((sh_tag 36 - 1)%uint63) with 36%uint63.
          rewrite (Hag 36%uint63) by (vm_compute; reflexivity). reflexivity.
        * rewrite (Hag (sh_tag 38%uint63)) by (vm_compute; reflexivity). change ((sh_tag 38 - 1)%uint63) with 38%uint63.
          rewrite (Hag 38%uint63) by (vm_compute; reflexivity). reflexivity.
    - (* [comment removed for export] *)
      unfold FMem. cbv zeta. cbn [x_blocks x_frames x_calls x_nb g_S ms_mem ms0 MS blk_list frm_list map app length].
      split; [reflexivity|]. split; [exact Hfr0|]. split; [constructor|]. split; [intros t []|].
      split; [intros t rg G; exact (proj1 (start_classE ri H_ri t rg G))|].
      split; [change (to_Z NEXT0) with 32; change (to_Z NEXTE) with 40; lia|]. split; [vm_compute; reflexivity|].
      split.
      { intros t rg G. destruct (start_classE ri H_ri t rg G) as [_ C]. destruct (rg_abs rg) as [a|].
        - destruct C as ([w C] & Cro & Cimg). right. split; [exists w; split; [exact C | intros X; rewrite Cro in X; discriminate X]|].
          split; [exact Cimg | intros X; rewrite Cro in X; discriminate X].
        - change (xp_stk xp) with 81920. change (xp_cbt xp) with CBT_E.
          destruct C as [C|[C|[(b & n & w & Hin & -> & Hsz & Hw)|(b & n & w & Hin & -> & Hsz & Hw)]]]; [left; exact C | right; left; exact C | |].
          + do 6 right. left. exists n, w. split; [exact Hin|]. split; [exact Hsz | intros X; rewrite <- Hw; exact X].
          + do 7 right. exists b, n, w. split; [exact Hin|]. split; [reflexivity|]. split; [exact Hsz | exact Hw]. }
      split; [split; intros t []|].
      split.
      { split; [reflexivity|]. split; [reflexivity|]. split; [intros t []|].
        change (rho0 T_S0) with (bv_unsigned s0). split; [pose proof (bv_unsigned_in_range 64 s0) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X | exact Hs0]. }
      split; [exact HART|]. split; [exact Hmi|]. split; [exact Hstk|].
      split; [unfold B0; change (xp_stk xp) with 81920; repeat split; lia|].
      split; [change (xp_nbmax xp) with (LIVE_MAX - Z.of_nat (length (rt_live RT Σ))); repeat split; lia|].
      split; [intros; reflexivity|]. split; [reflexivity|].
      (* [comment removed for export] *)
      change (xp_cbt xp) with CBT_E. change (xp_cbw xp) with [(ES, ES + 904)].
      intros t n w Hin. change (to_Z NEXT0) with 32. change (to_Z NEXTE) with 40.
      destruct (CBT_E_cases t n w Hin) as [(-> & -> & ->)|[(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]].
      + split; [exact L_mk|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [change (to_Z 32%uint63) with 32; lia|].
        split; [reflexivity | intros X; discriminate X].
      + split; [exact L_sa|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [change (to_Z 34%uint63) with 34; lia|].
        split; [reflexivity | intros X; discriminate X].
      + split; [exact L_nd|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [change (to_Z 36%uint63) with 36; lia|].
        split; [reflexivity | intros X; discriminate X].
      + split; [exact L_es|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [change (to_Z 38%uint63) with 38; lia|].
        split; [reflexivity | intros _; left; reflexivity]. }
  (* [comment removed for export] *)
  assert (Hks : forall h, In h hooksE -> xhook_ok bsegs SHBW (ghost RT) (J RT PMc T) (FInv RT (rt_live RT Σ) lo sp0 (to_Z ri) m (rt_credit RT Σ) (rt_sp0 RT Σ) xp) h).
  { intros h Hin. unfold hooksE in Hin. cbn [In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]].
    - exact (hkA_free_ok RT AF ar_RC PMc ar_PMc_fdfs ar_PMc_ms T _ lo sp0 (to_Z ri) m _ _ xp Hr01 (xpE_ro _ _) (xpE_stk _ _) IMGSH_OK_E TRACES_E TRACES_OK_E).
    - assert (Hcr : 2000 <= rt_credit RT Σ) by lia.
      exact (hkA_stack_malloc0_ok RT AF ar_RC PMc ar_PMc_fdfs ar_PMc_ms T _ lo sp0 (to_Z ri) m (rt_credit RT Σ) _ xp Hr01 (xpE_stk _ _) Hcr IMGSH_OK_E).
    - exact (hkA_release_ok RT AF frel_E PMc ar_PMc_ms T _ lo sp0 (to_Z ri) m _ _ xp Hr01 (xpE_stk _ _)). }
  (* [comment removed for export] *)
  destruct (run_ok_E_inv ri (run_result_E ri) Hcert) as (icE & cdE & SE & Erun & Efr & Ebl & Epc & Erv & Hregs & Hcalls & HQ).
  pose proof Erun as Erun'. rewrite run_result_E_unfold in Erun'.
  refine (hxs_drive_sound_step bsegs SHBW hookixE hooksE finalE (ghost RT) (J RT PMc T) _ (J_evt RT AF PMc ar_PMc_ms T)
            (FInv_step RT AF (rt_live RT Σ) lo sp0 (to_Z ri) m (rt_credit RT Σ) (rt_sp0 RT Σ) xp Hr01 (xpE_ro _ _) (xpE_stk _ _)) Hks 23 4000 IEmpty icE (XCD [] [] 0 0) cdE (SE0 ri) SE
            (GH RT Σ) rho0 ms0 (ic_ok_empty bsegs) HXI Erun' _ c Hc).
  (* [comment removed for export] *)
  intros g' rho' ms' Hag' [[HRn' Hlaw'] [HF' (Hro' & Hnf')]]. cbn [SE0 s_next] in Hag'.
  apply (J_evt RT AF PMc ar_PMc_ms T g' ms').
  pose proof (Rn_R bsegs rho' SE ms' HRn') as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_final_E as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step bsegs rho' IEmpty ic' SE ms' (ic_ok_empty bsegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_one bsegs _ _ Hstep)|].
  intros c2 Hc2. apply Hk.
  destruct HF' as (Hlive' & Hfr' & Hnd' & Htl' & Htags' & Hnx0' & Hnx' & Hcls' & Hlink' & Hrho' & HART' & Hmi' & Hstk' & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2n & Hc3 & Hc4) & Hagr' & Hanc' & _).
  rewrite Efr in Hfr'. cbn [frm_list map] in Hfr'. rewrite Ebl in Hlive'. cbn [blk_list map app] in Hlive'.
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf' as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                    & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hro', Hrv in Ems2.
  destruct (final_regs_denE rho' ri SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Hrho0 : forall t, to_Z t < to_Z NEXTE -> rho' t = rho0 t) by exact Hag'.
  rewrite (pword_scalar rho' TE_GP gp) in E3 by (rewrite Hrho0 by (vm_compute; reflexivity); reflexivity).
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
    assert (Ew : wZ (W false (ESTK + ri)%uint63) = 81920 + to_Z ri) by (destruct H_ri as [-> | ->]; reflexivity). rewrite Ew.
    unfold B. replace (sp0 - to_Z ri - 81920 + (81920 + to_Z ri)) with sp0 by lia. apply Z_to_bv_bv_unsigned. }
  assert (E4' : y4 = wz TP_A) by (rewrite E4; exact TPV_wbv_E).
  assert (E1' : y1 = ra) by (rewrite E1, Era; symmetry; exact RA_ECE_wz).
  clear E1 E2 E4. subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2.
  exists (g_S RT g').
  apply (ASTA_conseq RT (g_S RT g') PMc (eq ms2) _ c2 Hc2). intros ms <-.
  exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, (ms_fregs ms'), (ms_fcsr ms'), (ms_mem ms').
  split; [exact Ems2|].
  split.
  { (* [comment removed for export] *)
    split; [exact HART'|]. split; [rewrite Hanc'; exact Hanc|]. split; [exact Hfr'|]. split; [rewrite Hlive'; exact Hperm|].
    exact (conj Hnd (conj HokOW HposLB)). }
  split; [exact Hmi'|]. split; [exact Hstk'|].
  split.
  { (* [comment removed for export] *)
    intros a Ha [Hcl Hout]. apply Hagr'. unfold caller_mem. rewrite wa_unsigned by lia.
    split; [exact (aclient_of_addr_incl _ _ _ _ (AH_incl Σ OW LB m HAH) Hcl)|].
    split; [exact I|]. change (xp_cbw xp) with [(ES, ES + 904)]. cbn [outside]. split; [exact Hout | exact I]. }
  split.
  { (* [comment removed for export] *)
    pose proof (q_rw_cells rho' SE (ms_mem ms') Q_es_E [CB 904 ES_CLEARED] HRm HQ eq_refl ltac:(cbn; tauto) eq_refl) as X.
    cbn [q_tag q_off Q_es_E] in X. rewrite Z.add_0_r in X. rewrite (Hrho0 T_ES) in X by (vm_compute; reflexivity). change (rho0 T_ES) with ES in X.
    apply X. intros bs Hbs. rewrite (F2_bytes rho' _ bs Hbs). reflexivity. }
  lia.
Qed.

(* [comment removed for export] *)
Theorem ece_cps_AR : @ERR_clear_error_cpsA_stmt AR ECE_STACK ECE_COST.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB EA lo
         HAH Hstk Hceil Hlo2 Hsp47 Hsp16 Hmi Etp Era Hs0 HCS HERR Hcred.
  assert (Hres : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct Hres as [Hres|Hres].
  - exact (ece_residue 0%uint63 (or_introl eq_refl) run_checked_E0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB EA lo
             HAH Hstk Hceil Hlo2 Hsp47 Hres Hmi Etp Era Hs0 HCS HERR Hcred).
  - exact (ece_residue 16%uint63 (or_intror eq_refl) run_checked_E16 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB EA lo
             HAH Hstk Hceil Hlo2 Hsp47 Hres Hmi Etp Era Hs0 HCS HERR Hcred).
Qed.

End Main.

(* [comment removed for export] *)
Theorem ece_cps_proved : ece_cps.
Proof. intros AR. exact (@ece_cps_AR AR). Qed.
