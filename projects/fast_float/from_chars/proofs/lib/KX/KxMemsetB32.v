(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs FxPlan RefMemcpyLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2 B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Lemma MSB_wf_32 : state_wf MSB32_P0 = true /\ state_wf MSB32_Q = true /\ shape_eqb (s_rgs MSB32_P0) (s_rgs MSB32_Q) = true.
Proof. vm_compute. repeat split. Qed.

Section MS.
Variable E : valu.
Variable ms : machine_state.
Hypothesis Hd : sden BSEGS E MSB32_P0 ms.
Local Abbreviation u x := (bv_unsigned (E x%positive)).
Local Abbreviation m0 := (ms_mem ms).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

Ltac open_ms :=
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm);
  cbn [s_pc s_regs s_rgs s_facts s_resv MSB32_P0 msb_P0] in Hpc, Hresv, HR, HG, HD, HF;
  unfold rt_rgs, rt_tp, rt_tp0, relro_rgs in HG; cbn [app] in HG;
  apply Forall_cons_iff in HG as [R0 HG]; apply Forall_cons_iff in HG as [R1 HG]; apply Forall_cons_iff in HG as [R2 HG];
  apply Forall_cons_iff in HG as [R3 HG]; apply Forall_cons_iff in HG as [R4 HG]; apply Forall_cons_iff in HG as [R5 HG];
  apply Forall_cons_iff in HG as [R6 HG]; apply Forall_cons_iff in HG as [R7 HG]; apply Forall_cons_iff in HG as [R8 HG];
  apply Forall_cons_iff in HG as [R9 HG]; apply Forall_cons_iff in HG as [R10 HG]; apply Forall_cons_iff in HG as [R11 HG];
  apply Forall_cons_iff in HG as [R12 HG]; apply Forall_cons_iff in HG as [R13 HG]; apply Forall_cons_iff in HG as [R14 HG];
  apply Forall_cons_iff in HG as [R15 HG]; apply Forall_cons_iff in HG as [R16 HG]; clear HG.
Ltac open_facts :=
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _); cbn [s_facts MSB32_P0 msb_P0] in HF;
  unfold msb_F, spsh_fact, rt_facts, two_class, two_class4k, stack_facts in HF; cbn [app] in HF;
  apply Forall_cons_iff in HF as [F HF]; apply Forall_cons_iff in HF as [FSH0 HF]; apply Forall_cons_iff in HF as [FSH1 HF];
  apply Forall_cons_iff in HF as [FTOP HF];
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [?F H] end;
  cbn [fact_ok] in *;
  repeat match goal with H : context [lden E ?l] |- _ => progress lnorm_s_in H end;
  rewrite ?u_Z_to_bv in *; unfold vz in *; unfold KHI, KTOP, IMG_END, SH_LO in *.

#[using="Type"] Lemma rt_app_of_wrapped : forall x n, 6537216 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n /\ app2r x (x + n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. unfold rt_app, app2r, KHI, KTOP. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - split; right; lia.
  - assert (Hm : (-17594333495296 + (1 * x + 0)) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. split; left; lia.
Qed.
#[using="Type"] Lemma rt_app_of_wrapped4k : forall x n, 4096 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. unfold rt_app, KHI. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - right; lia.
  - left. assert (Hm : (-17594333495296 + (1 * x + 0)) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. lia.
Qed.

(* [comment removed for export] *)
#[using="ms Hd"] Lemma ms_facts :
  u 5 mod 2 = 0 /\ u 9 = 2147450880 + (u 4 - 64) / 8 /\
  6537216 <= 4096 * u 10 <= 2 ^ 47 - 11571200 /\
  6537216 <= u 15 <= 2 ^ 47 - 160 /\ 4096 <= u 16 <= 2 ^ 47 - 80 /\ 4096 <= u 17 <= 2 ^ 47 - 32 /\
  1 <= u 18 <= 2 ^ 64 - 1 /\ 1 <= u 21 <= 255 /\
  (u 15 + 160 <= 4096 * u 10 \/ 4096 * u 10 + 11571200 <= u 15) /\
  (u 16 + 80 <= 4096 * u 10 \/ 4096 * u 10 + 11571200 <= u 16) /\
  (u 17 + 32 <= 4096 * u 10 \/ 4096 * u 10 + 11571200 <= u 17) /\
  17594333495296 <= u 4 - 2208 /\ u 4 <= 2 ^ 47 /\ u 4 mod 16 = 0 /\
  2208 <= u 4 - u 23 <= 2 ^ 30 /\ 0 <= u 23 + u 24 - u 4 <= 2 ^ 30 /\
  0 <= u 4 - 2208 - 4096 * u 10 - 11571200 <= 2 ^ 47 /\
  app2r (4096 * u 10) (4096 * u 10 + 11571200) /\ rt_app (u 15) 160 /\ rt_app (u 16) 80 /\ rt_app (u 17) 32.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts.
  pose proof (Bnd 4%positive) as B4. pose proof (Bnd 10%positive) as B10.
  pose proof (Bnd 12%positive) as B12. pose proof (Bnd 15%positive) as B15. pose proof (Bnd 16%positive) as B16.
  pose proof (Bnd 17%positive) as B17. pose proof (Bnd 23%positive) as B23. pose proof (Bnd 24%positive) as B24.
  assert (X : 6537216 <= 4096 * u 10 <= 2 ^ 47 - 11571200)
    by (clear -F0; change (6537216 / 4096) with 1596 in F0; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F0; lia).
  change (2 ^ 1) with 2 in F. change (2 ^ 4) with 16 in F17.
  refine (conj F (conj _ (conj X (conj F2 (conj F4 (conj F6 (conj F8 (conj F9 (conj _ (conj _ (conj _ (conj _ (conj _ (conj F17 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))))).
  - pose proof (Bnd 9%positive) as B9. clear -FSH0 FSH1 F16 B4 B9. unfold two64, SHB in *. Z.div_mod_to_equations. lia.
  - clear -F13 B10 B15 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F14 B10 B16 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F15 B10 B17 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F16 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F16 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs MSB32_P0 msb_P0] in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F16 F18 F19 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs MSB32_P0 msb_P0] in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F16 F18 F19 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F20 B4 B10 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - apply (proj2 (rt_app_of_wrapped (4096 * u 10) 11571200 ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(replace (-17594333495296 + (1 * (4096 * u 10) + 0)) with (-17594333495296 + (4096 * u 10 + 0)) by ring; exact F1))).
  - exact (proj1 (rt_app_of_wrapped (u 15) 160 ltac:(lia) ltac:(lia) ltac:(lia) F3)).
  - exact ((rt_app_of_wrapped4k (u 16) 80 ltac:(lia) ltac:(lia) ltac:(lia) F5)).
  - exact ((rt_app_of_wrapped4k (u 17) 32 ltac:(lia) ltac:(lia) ltac:(lia) F7)).
Qed.

Definition Dv : Z := u 4 + 104.

#[using="ms Hd"] Lemma ms_top : u 4 + 256 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0). open_facts. pose proof (Bnd 4%positive) as B4. clear -FTOP B4. unfold two64 in *. Z.div_mod_to_equations. lia. Qed.

#[using="ms Hd"] Lemma ms_vals : bv_unsigned (lden E (laddc SP 104)) = Dv /\ u 9 = 2147450880 + (u 4 - 64) / 8 /\ Dv mod 8 = 0 /\
  u 4 mod 16 = 0 /\ 17594333495296 <= u 4 - 2208 /\ u 4 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof ms_facts as (_ & SH & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fsp & FspK & Fsp16 & _). pose proof (Bnd 4).
  refine (conj _ (conj SH (conj _ (conj Fsp16 (conj Fsp FspK))))).
  - unfold SP. ubase_s. rewrite Z.mod_small; [unfold Dv; ring | unfold two64 in *; lia].
  - unfold Dv. clear -Fsp16. Z.div_mod_to_equations. lia.
Qed.

#[using="Hd"] Lemma mset_regs : getr (ms_regs ms) 10 = lden E (laddc SP 104) /\ getr (ms_regs ms) 11 = Z_to_bv 64 0 /\
  getr (ms_regs ms) 12 = Z_to_bv 64 32 /\ getr (ms_regs ms) 1 = E 5%positive /\ getr (ms_regs ms) 2 = E 4%positive /\
  getr (ms_regs ms) 4 = Z_to_bv 64 6395968.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ms. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - pose proof (HR 10%bv) as X. rget_norm_in X. exact X.
  - pose proof (HR 11%bv) as X. rget_norm_in X. rewrite X. reflexivity.
  - pose proof (HR 12%bv) as X. rget_norm_in X. rewrite X. reflexivity.
  - pose proof (HR 1%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 2%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 4%bv) as X. rget_norm_in X. rewrite X. reflexivity.
Qed.

#[using="Hd"] Lemma ms_old : exists old, u8arr BSEGS m0 Dv old /\ length old = 32%nat.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ms. pose proof ms_vals as (V1 & _). apply (u8arr_of_stk BSEGS). apply (stk_of_rg BSEGS E _ _ _ _ R1 ltac:(left; reflexivity)).
  - exact V1.
  - unfold rsz. cbn [rg_size]. change (bv_unsigned (lden E (lconst 32))) with 32. lia.
Qed.

#[using="Type"] Lemma shz_of_bytesB : forall m a n, bytes_at BSEGS m a (repeat (Z_to_bv 8 0) n) -> shz BSEGS m a (Z.of_nat n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n X. split; [lia|]. rewrite Nat2Z.id. exact X.
Qed.

#[using="Hd"] Lemma ms_shz : shz BSEGS m0 (2147450880 + Dv / 8) ((32 + 7) / 8) /\ rdbl BSEGS m0 (u 9) 40.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ms. pose proof ms_vals as (_ & V2 & V3 & V4 & V5 & V6). split.
  - pose proof (zeros_bytes_of_rz BSEGS E m0 _ (u 9) 40 R2 eq_refl eq_refl ltac:(cbn [rg_base RGz]; unfold SPSH; rewrite lden_lvar; reflexivity)
                  ltac:(unfold rsz; cbn [rg_size RGz]; reflexivity)) as X.
    pose proof (shz_of_bytesB _ _ _ X) as Y. change (Z.of_nat 40) with 40 in Y.
    eapply shz_sub; [exact Y | | | ]; unfold Dv in *; clear -V2 V4 V5 V6; Z.div_mod_to_equations; lia.
  - pose proof (rg_flat BSEGS E _ _ R2) as (X1 & X2). unfold rsz in X2. cbn [rg_base rg_size RGz] in X2.
    unfold SPSH in X2. rewrite lden_lvar in X2. change (bv_unsigned (lden E (lconst 40))) with 40 in X2. unfold two64 in X2.
    split; [lia|]. split; [lia|].
    intros i Hi. pose proof (rd_of_rg BSEGS E m0 _ i R2) as Y. cbn [rg_base rg_kind RGz] in Y. unfold SPSH in Y. rewrite lden_lvar in Y.
    destruct (mrd BSEGS m0 (wa (u 9 + i))) as [b|]; [exists b; reflexivity|].
    exfalso. apply Y; [unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst 40))) with 40; lia | discriminate | reflexivity].
Qed.

#[using="Hd"] Lemma ms_stk : stk BSEGS m0 (u 4 - 2208) (u 4).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ms. pose proof ms_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & _).
  assert (S0 : stk BSEGS m0 (u 23) (u 23 + u 24)).
  { apply (stk_of_rg BSEGS E _ _ _ _ R0 ltac:(left; reflexivity)); cbn [rg_base]; [unfold SWB; rewrite lden_lvar; reflexivity|].
    unfold rsz. cbn [rg_size]. unfold SWS. rewrite lden_lvar. ring. }
  destruct (stk_split BSEGS _ _ (u 4 - 2208) _ S0 ltac:(lia)) as (_ & S1).
  destruct (stk_split BSEGS _ _ (u 4) _ S1 ltac:(lia)) as (S2 & _). exact S2.
Qed.

#[using="E Hd"] Lemma ms_pr : pristine m0 892928 917504 /\ pristine m0 918096 918488.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0).
  open_ms. split.
  - exact (pristine_of_rg_ro BSEGS E _ _ 892928 24576 R15 eq_refl eq_refl eq_refl).
  - exact (pristine_of_rg_ro BSEGS E _ _ 918096 392 R16 eq_refl eq_refl eq_refl).
Qed.

Definition v0 : rt_vals := RTV (4096 * u 10) (u 15) (u 16) (u 19) (u 20) (u 17) (u 18).

(* [comment removed for export] *)
Ltac const_cells G o :=
  let X := fresh "X" in
  pose proof (track_bytes_at BSEGS E m0 _ o _ G ltac:(clear; lia) ltac:(cbn; clear; lia)) as X;
  cbn [rg_base RGz track] in X; change (bv_unsigned (lden E (lconst ?z))) with (z mod two64) in X;
  rewrite Z.mod_small in X by (unfold two64; clear; lia);
  apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].

#[using="Hd"] Lemma ms_RT : RT m0 v0.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ms. unfold RT. cbn [rt_FS rt_ctx rt_thr rt_tlsb rt_tlse rt_blk rt_beg v0].
  pose proof ms_facts as FCT.
  destruct FCT as (_ & _ & Hf & Hc & Ht & Hb & Hg & Hfb & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fapp & Capp & Tapp & Bapp). unfold KHI, KTOP in *.
  unfold rt_tp, rt_tp0 in R10.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  - unfold sb_uar in R3. const_cells R3 0.
  - (* [comment removed for export] *)
    pose proof (track_bytes_at BSEGS E m0 _ 0 _ R4 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 941792))) with 941792 in X.
    pose proof (bytes_at_sub BSEGS _ _ _ 0 1 X ltac:(cbn; lia)) as Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - pose proof (track_bytes_at BSEGS E m0 _ 0 _ R4 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 941792))) with 941792 in X.
    pose proof (bytes_at_sub BSEGS _ _ _ 4 4 X ltac:(cbn; lia)) as Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - const_cells R5 0.
  - const_cells R6 0.
  - exists (Z_to_bv 8 (u 21)). split.
    + pose proof (track_bytes_at BSEGS E m0 _ 0 _ R8 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 1540657))) with 1540657 in X. rewrite Z.add_0_r in X.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. cbn [List.map bden] in X. lnorm_in X. rewrite Z.shiftr_0_r in X. exact X.
    + rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by (clear -Hfb; lia). clear -Hfb; lia.
  - const_cells R7 0.
  - const_cells R9 0.
  - (* [comment removed for export] *)
    split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_bytes_at BSEGS E m0 _ 0 (bk8 6396000) R10 ltac:(clear; lia) ltac:(cbn; clear; lia)
                    ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X. rewrite Z.add_0_r in X.
      apply (bytes_at_ext BSEGS _ _ _ _ X). apply bytes_eqb_eq. vm_compute. reflexivity.
    + pose proof (cont_le8 BSEGS E m0 _ 8 FS R10 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
      lnorm_in X. rewrite Z.add_0_l, Z.add_0_r in X. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 16 BLK R10 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - pose proof (cont_bytes_at BSEGS E m0 _ 48 (bk8 6398016) R10 ltac:(clear; lia) ltac:(cbn; clear; lia)
                  ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 0 CTX R11 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6532072))) with 6532072 in X.
    lnorm_in X. rewrite ?Z.add_0_r in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 152 THR R12 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_le8 BSEGS E m0 _ 48 TLSB R13 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
    + pose proof (cont_le8 BSEGS E m0 _ 56 TLSE R13 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. lnorm_in X. rewrite !Z_to_bv_bv_unsigned, length_le8.
      replace (u 16 + 48 + Z.of_nat 8) with (u 16 + 56) by lia. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 24 BEG R14 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fapp (conj _ (conj _ (conj Capp (conj _ (conj Tapp (conj _ (conj Bapp _))))))))))))).
    all: clear -Hf Hc Ht Hb Hg; unfold two64 in *; lia.
Qed.

#[using="Type"] Lemma rg_disj_sym : forall R1 R2, rg_disj E R1 R2 -> rg_disj E R2 R1.
Proof. LiaFast.lf_pins LiaFast.u0. unfold rg_disj. intros R1 R2 H. lia. Qed.



#[using="ms Hd"] Lemma ms_rtd1 : rt_disj v0 (u 4 - 2208) (u 4).
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_ms. pose proof ms_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & _).
  unfold rt_rgs, rt_tp, rt_tp0, relro_rgs in HD. cbn [app] in HD.
  pose proof (rgs_disj_nth E _ 0 12 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D1.
  pose proof (rgs_disj_nth E _ 0 13 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D2.
  pose proof (rgs_disj_nth E _ 0 14 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D3.
  unfold rg_disj, rsz in D1, D2, D3. cbn [rg_base rg_size track RGz] in D1, D2, D3.
  unfold SWB, SWS, CTX, THR, BLK in D1, D2, D3. repeat rewrite lden_lvar in D1. repeat rewrite lden_lvar in D2. repeat rewrite lden_lvar in D3.
  change (bv_unsigned (lden E (lconst 160))) with 160 in D1.
  change (bv_unsigned (lden E (lconst 80))) with 80 in D2.
  change (bv_unsigned (lden E (lconst 32))) with 32 in D3.
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -W1 W2 D1 D2 D3. repeat split; lia.
Qed.

#[using="ms Hd"] Lemma ms_rtd2 : rt_disj v0 Dv (Dv + 32).
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_ms. pose proof ms_vals as (V1 & _).
  unfold rt_rgs, relro_rgs in HD. cbn [app] in HD.
  pose proof (rgs_disj_nth E _ 1 12 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D1.
  pose proof (rgs_disj_nth E _ 1 13 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D2.
  pose proof (rgs_disj_nth E _ 1 14 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D3.
  unfold rg_disj, rsz in D1, D2, D3. cbn [rg_base rg_size track RGz] in D1, D2, D3. rewrite V1 in D1, D2, D3.
  unfold CTX, THR, BLK in D1, D2, D3. repeat rewrite lden_lvar in D1. repeat rewrite lden_lvar in D2. repeat rewrite lden_lvar in D3.
  change (bv_unsigned (lden E (lconst 32))) with 32 in D1, D2, D3.
  change (bv_unsigned (lden E (lconst 160))) with 160 in D1.
  change (bv_unsigned (lden E (lconst 80))) with 80 in D2.
  change (bv_unsigned (lden E (lconst 32))) with 32 in D3.
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -D1 D2 D3. repeat split; lia.
Qed.

Section Run.
Hypothesis AMS : asan_memset_stmt.

Definition Eq (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : valu :=
  upds E [(205%positive, t0); (206%positive, t1); (207%positive, t2); (210%positive, a0); (211%positive, a1); (212%positive, a2);
          (213%positive, a3); (214%positive, a4); (215%positive, a5); (216%positive, a6); (217%positive, a7); (228%positive, t3);
          (229%positive, t4); (230%positive, t5); (231%positive, t6)].
#[using="Type"] Lemma Eq_agree : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, agree 200 E (Eq t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.

#[using="Hd AMS"] Lemma ms_run : exists ms' E', isteps BSEGS ms ms' /\
  sden BSEGS E' (with_pc MSB32_Q (bv_unsigned (lden E (rget (s_regs MSB32_P0) ra_key)))) ms' /\
  agree (s_next MSB32_P0) E E' /\ (forall x, fr_pt E (s_rgs MSB32_P0) x -> ms_mem ms' x = ms_mem ms x).
Proof. LiaFast.lf_pins (fun (Hd AMS : LiaFast.U) => LiaFast.u0).
  pose proof mset_regs as (Ra0 & Ra1 & Ra2 & Rra & Rsp & Rtp). pose proof ms_vals as (V1 & V2 & V3 & _).
  pose proof ms_facts as (Fra & SH0 & FF & _ & _ & _ & _ & _ & _ & _ & _ & Fsp & FspK & Fsp16 & W1 & W2 & C18 & Fapp & _).
  destruct ms_old as (old & OLD & Lold). pose proof ms_pr as (PR1 & PR2). pose proof ms_shz as (SHZ & RDB). pose proof ms_top as TOP.
  open_ms.
  pose proof (AMS (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4) (getr (ms_regs ms) 5)
                 (getr (ms_regs ms) 6) (getr (ms_regs ms) 7) (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10)
                 (getr (ms_regs ms) 11) (getr (ms_regs ms) 12) (getr (ms_regs ms) 13) (getr (ms_regs ms) 14) (getr (ms_regs ms) 15)
                 (getr (ms_regs ms) 16) (getr (ms_regs ms) 17) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (getr (ms_regs ms) 28) (getr (ms_regs ms) 29) (getr (ms_regs ms) 30)
                 (getr (ms_regs ms) 31) (ms_fregs ms) (ms_fcsr ms) m0 v0 old 0 (u 9) 40) as K.
  assert (HK : evt BSEGS (asan_memset_post (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4)
                 (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19)
                 (getr (ms_regs ms) 20) (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24)
                 (getr (ms_regs ms) 25) (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (ms_fregs ms) (ms_fcsr ms) 0
                 (bv_unsigned (getr (ms_regs ms) 12)) m0) (kms BSEGS ms)).
  { unfold kms. rewrite Hpc, Hresv. apply K; clear K; rewrite ?Ra0, ?V1, ?Ra2, ?Rsp; change (bv_unsigned (Z_to_bv 64 32)) with 32.
    - exact Ra1.
    - lia.
    - exact OLD.
    - rewrite Lold. reflexivity.
    - exact V3.
    - apply app2r_intro_hi; unfold Dv, KHI, KTOP in *; lia.
    - unfold Dv in *; lia.
    - lia.
    - exact SHZ.
    - exact RDB.
    - rewrite V2. unfold Dv. clear -Fsp16 Fsp FspK. Z.div_mod_to_equations. lia.
    - rewrite V2. unfold Dv. clear -Fsp16 Fsp FspK. Z.div_mod_to_equations. lia.
    - exact ms_stk.
    - lia.
    - exact Fsp.
    - exact FspK.
    - exact Fsp16.
    - left. unfold Dv in *. lia.
    - exact PR1.
    - exact PR2.
    - exact ms_RT.
    - exact ms_rtd1.
    - exact ms_rtd2.
    - rewrite Rra. exact Fra. }
  clear K.
  destruct (kit_run BSEGS _ ms Hsvc HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms2 & MU & WM & ARR & STK).
  subst ms2. unfold asan_memset_W in MU. rewrite Ra0, V1, Ra2, Rsp in MU. rewrite Ra0, V1, Ra2 in ARR. rewrite Rsp in STK.
  change (bv_unsigned (Z_to_bv 64 32)) with 32 in MU, ARR.
  assert (Hmem : ms_mem ms1 = m') by (destruct Heq as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  set (E' := Eq t0 t1 t2 (getr (ms_regs ms) 10) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  assert (AG : agree 200 E E') by apply Eq_agree.
  exists ms1, E'. split; [exact Hst|]. split; [|split].
  - eapply (sden_of_kit BSEGS _ _ ms1); [ | | exact Heq | | exact Hfrm | | | | ].
    + rewrite state_wf_with_pc. exact (proj1 (proj2 MSB_wf_32)).
    + reflexivity.
    + cbn [s_pc with_pc s_regs MSB32_P0 msb_P0]. rget_norm. change (lden E {| l_c := 0; l_t := [(5%positive, 1)] |}) with (lden E (lvar 5)).
      rewrite lden_lvar, Z_to_bv_bv_unsigned, <- Rra. apply ret_pc_even_w. rewrite Rra. exact Fra.
    + (* [comment removed for export] *)
      apply regs_ok_of_cases. intros nr Hn. cbn [s_regs with_pc MSB32_Q msb_Q].
      do 32 (destruct nr as [|nr];
               [ getr_mkR_norm; rget_norm;
                 first [ reflexivity
                       | (rewrite (HR _); rget_norm; symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG])
                       | (symmetry; exact (lden_lvar E' _)) ]
               |]).
      lia.
    + (* [comment removed for export] *)
      cbn [s_rgs with_pc MSB32_Q msb_Q]. unfold rt_rgs, rt_tp, rt_tp0, relro_rgs. cbn [app].
      assert (UW : forall R, rg_ok BSEGS E m0 R -> rg_disj E R (RG SWB SWS RW TEmpty) -> rg_disj E R (RG (laddc SP 104) (lconst 32) RW TEmpty) ->
                 rwf 200 R = true -> rg_ok BSEGS E' m' R).
      { intros R HR0 Hd0 Hd1 Hw. apply (rg_ok_agree BSEGS 200 E _ _ R Hw AG). apply (rg_ok_munch BSEGS E m0 m' R _ HR0 MU).
        intros k Hk. unfold rg_disj, rsz in Hd0, Hd1. cbn [rg_base rg_size] in Hd0, Hd1. rewrite V1 in Hd1.
        unfold SWB, SWS in Hd0. repeat rewrite lden_lvar in Hd0.
        change (bv_unsigned (lden E (lconst 32))) with 32 in Hd1. unfold rsz in Hk. cbn [Frame.outside].
        pose proof (u_lden_range E (rg_base R)) as U. pose proof (rg_flat BSEGS E m0 R HR0) as (F1 & F2). unfold rsz in F2.
        split; [|split; [|exact I]]; lia. }
      assert (HDn : forall i j Ri Rj, i <> j -> nth_error (s_rgs MSB32_P0) i = Some Ri -> nth_error (s_rgs MSB32_P0) j = Some Rj -> rg_disj E Ri Rj).
      { intros i j Ri Rj Hij Hi Hj. exact (rgs_disj_nth E _ i j _ _ HD Hij Hi Hj). }
      constructor.
      { (* [comment removed for export] *)
        eapply (rg_ok_agree BSEGS 200 E _ _ _); [vm_compute; reflexivity | exact AG |].
        apply (rw_mix BSEGS E m0 m' _ _ (u 4 - 2208) (u 4) R0 eq_refl eq_refl MU STK).
        intros i Hi. unfold rsz in Hi. cbn [rg_base rg_size] in Hi |- *. unfold SWB, SWS in *. repeat rewrite lden_lvar in *.
        destruct (Z.ltb_spec (u 23 + i) (u 4 - 2208)) as [Hl|Hl]; [right | destruct (Z.ltb_spec (u 23 + i) (u 4)) as [Hl2|Hl2]; [left; lia | right]].
        - pose proof (HDn 0%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) as D. unfold rg_disj, rsz in D. cbn [rg_base rg_size] in D.
          rewrite V1 in D. unfold SWB, SWS in D. repeat rewrite lden_lvar in D. change (bv_unsigned (lden E (lconst 32))) with 32 in D.
          cbn [Frame.outside]. split; [lia | split; [lia | exact I]].
        - pose proof (HDn 0%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) as D. unfold rg_disj, rsz in D. cbn [rg_base rg_size] in D.
          rewrite V1 in D. unfold SWB, SWS in D. repeat rewrite lden_lvar in D. change (bv_unsigned (lden E (lconst 32))) with 32 in D.
          cbn [Frame.outside]. split; [lia | split; [lia | exact I]]. }
      constructor.
      { (* [comment removed for export] *)
        apply (track_of_bytes_at BSEGS E' m' _ 0 _); [ | lia | unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E' (lconst 32))) with 32; rewrite repeat_length, Z2Nat.id by lia; lia | ].
        - eapply (rg_ok_agree BSEGS 200 E _ _ _); [vm_compute; reflexivity | exact AG |].
          eapply (rg_ok_of_u8arr BSEGS E m' _ Dv); [reflexivity | reflexivity | exact V1 | | exact ARR].
          rewrite repeat_length. reflexivity.
        - cbn [rg_base]. assert (LB : lden E' (laddc SP 104) = lden E (laddc SP 104)) by (symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG]).
          rewrite LB, V1, Z.add_0_r. rewrite map_repeat. exact (proj1 ARR). }
      constructor.
      { apply UW; [exact R2 | apply rg_disj_sym; exact (HDn 0%nat 2%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 2%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]. }
      constructor; [apply UW; [exact R3 | exact (HDn 3%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 3%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R4 | exact (HDn 4%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 4%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R5 | exact (HDn 5%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 5%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R6 | exact (HDn 6%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 6%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R7 | exact (HDn 7%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 7%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R8 | exact (HDn 8%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 8%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R9 | exact (HDn 9%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 9%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R10 | exact (HDn 10%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 10%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R11 | exact (HDn 11%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 11%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R12 | exact (HDn 12%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 12%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R13 | exact (HDn 13%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 13%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R14 | exact (HDn 14%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 14%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R15 | exact (HDn 15%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 15%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R16 | exact (HDn 16%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) | exact (HDn 16%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) | vm_compute; reflexivity]|].
      constructor.
    + (* [comment removed for export] *)
      apply (rgs_disj_agree 200 E); [vm_compute; reflexivity | exact AG |].
      apply (rgs_disj_shape E (s_rgs MSB32_P0)); [apply shape_eqb_eq; exact (proj2 (proj2 MSB_wf_32)) | exact HD].
    + (* [comment removed for export] *)
      cbn [s_facts with_pc MSB32_Q msb_Q].
      assert (Hw : forallb (fwf 200) msb_F = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF |- *. intros f Hf.
      exact (fact_ok_agree 200 E _ f (Hw f Hf) AG (HF f Hf)).
  - exact AG.
  - intros x Hx. rewrite Hmem. apply MU. destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. cbn [s_rgs MSB32_P0 msb_P0] in Hout.
      apply Forall_cons_iff in Hout as [O0 Hout]. apply Forall_cons_iff in Hout as [O1 _].
      unfold rsz in O0, O1. cbn [rg_base rg_size] in O0, O1. rewrite V1 in O1. unfold SWB, SWS in O0. repeat rewrite lden_lvar in O0.
      change (bv_unsigned (lden E (lconst 32))) with 32 in O1.
      pose proof ms_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1' & W2' & _).
      cbn [Frame.outside]. split; [lia | split; [lia | exact I]].
    + exfalso. apply Exists_exists in Hrt as (R & HRin & Hrt & _). cbn [s_rgs MSB32_P0 msb_P0 rt_rgs rt_tp rt_tp0 relro_rgs app] in HRin.
      repeat (destruct HRin as [<-|HRin]; [cbn in Hrt; discriminate|]). destruct HRin.
Qed.
End Run.
End MS.

Theorem memset32_kfn : asan_memset_stmt -> kfn_ok BSEGS MSB32_P0 MSB32_Q.
Proof. intros AMS E ms Hd. exact (ms_run E ms Hd AMS). Qed.
