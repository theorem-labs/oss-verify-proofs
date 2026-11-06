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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs RefMemcpyLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_app2 B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt B_parse_mantissa_stmt B_negative_digit_comp_d_stmt B_dcf_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_app2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt.B_fakestack OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_dcf_d_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_dcf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_dcf.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma two_class_app2r : forall x n, 6537216 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (x - 17594333495296) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> app2r x (x + n).
Proof.
  intros x n H1 H2 H3 H4. unfold app2r, KHI, KTOP. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - right. lia.
  - left. split; [lia|].
    assert (Hm : (x - 17594333495296) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. lia.
Qed.

Section DCF.
Variable frac : bool.
Variable E : valu.
Variable ms : machine_state.
Hypothesis Hd : sden BSEGS E (DCF_P0 frac) ms.

Local Abbreviation u x := (bv_unsigned (E x%positive)).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

(* [comment removed for export] *)
Ltac open_dcf :=
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm);
  cbn [s_pc s_regs s_rgs s_facts s_resv DCF_P0] in Hpc, Hresv, HR, HG, HD, HF;
  unfold DCF_RGS, fks5_whole, rt_rgs, rt_tp, rt_tp0, relro_rgs in HG; cbn [app] in HG;
  apply Forall_cons_iff in HG as [R0 HG]; apply Forall_cons_iff in HG as [R1 HG]; apply Forall_cons_iff in HG as [R2 HG]; apply Forall_cons_iff in HG as [R3 HG]; apply Forall_cons_iff in HG as [R4 HG]; apply Forall_cons_iff in HG as [R5 HG]; apply Forall_cons_iff in HG as [R6 HG]; apply Forall_cons_iff in HG as [R7 HG]; apply Forall_cons_iff in HG as [R8 HG]; apply Forall_cons_iff in HG as [R9 HG]; apply Forall_cons_iff in HG as [R10 HG]; apply Forall_cons_iff in HG as [R11 HG];
  apply Forall_cons_iff in HG as [R12 HG]; apply Forall_cons_iff in HG as [R13 HG]; apply Forall_cons_iff in HG as [R14 HG]; apply Forall_cons_iff in HG as [R15 HG]; apply Forall_cons_iff in HG as [R16 HG]; apply Forall_cons_iff in HG as [R17 HG]; apply Forall_cons_iff in HG as [R18 HG]; apply Forall_cons_iff in HG as [R19 HG]; apply Forall_cons_iff in HG as [R20 HG]; apply Forall_cons_iff in HG as [R21 HG]; apply Forall_cons_iff in HG as [R22 HG]; apply Forall_cons_iff in HG as [R23 HG];
  apply Forall_cons_iff in HG as [R24 HG]; apply Forall_cons_iff in HG as [R25 HG]; apply Forall_cons_iff in HG as [R26 HG]; apply Forall_cons_iff in HG as [R27 HG]; apply Forall_cons_iff in HG as [R28 HG]; apply Forall_cons_iff in HG as [R29 HG]; apply Forall_cons_iff in HG as [R30 HG]; apply Forall_cons_iff in HG as [R31 HG]; apply Forall_cons_iff in HG as [R32 HG]; apply Forall_cons_iff in HG as [R33 HG]; apply Forall_cons_iff in HG as [R34 HG]; apply Forall_cons_iff in HG as [R35 HG]; apply Forall_cons_iff in HG as [R36 HG]; apply Forall_cons_iff in HG as [R37 HG]; apply Forall_cons_iff in HG as [R38 HG]; clear HG.


(* [comment removed for export] *)
Ltac open_facts :=
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _); cbn [s_facts DCF_P0] in HF;
  unfold dcf_facts, rt_facts, two_class, two_class4k, spsh_fact in HF; destruct frac; cbn [app List.flat_map] in HF;
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [?F H] end;
  cbn [fact_ok] in *;
  repeat match goal with H : context [lden E ?l] |- _ => progress lnorm_s_in H end;
  rewrite ?u_Z_to_bv in *; unfold vz in *; unfold KHI, KTOP, NDC_NEED, IMG_END, SH_LO in *;
  [ | rename F39 into F42, F38 into F41, F37 into F40, F36 into F39, F35 into F38, F34 into F37, F33 into F36, F32 into F35, F31 into F34, F30 into F33, F29 into F32, F28 into F31, F27 into F30, F26 into F29, F25 into F28, F24 into F27, F23 into F26, F22 into F25, F21 into F24, F20 into F23, F19 into F22 ].

#[using="frac ms Hd"] Lemma dcf_sp : u 4 mod 16 = 0 /\ 17594333495296 <= u 4 - 2768 /\ u 4 + 152 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 4) as B4; clear -F F0 B4; unfold two64 in *; change (2 ^ 4) with 16 in F;
  (split; [exact F|]); Z.div_mod_to_equations; lia.
Qed.

Definition se : Z := (u 124 + 342) mod two64 - 342.
Definition p2 : Z := (u 125 + 49152) mod two64 - 49152 + 32768.

#[using="frac ms Hd"] Lemma dcf_q : -342 <= se <= 358 /\ E 124%positive = Z_to_bv 64 se.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 124) as B; unfold se; clear -F2 B; unfold two64 in *.
  all: split; [lia|].
  all: rewrite <- (Z_to_bv_bv_unsigned (E 124%positive)) at 1; apply Z_to_bv_eqm; unfold eqm, two64;
       rewrite Zminus_mod, Zmod_mod, <- Zminus_mod, Z.add_simpl_r; reflexivity.
Qed.

#[using="frac ms Hd"] Lemma dcf_p2 : -2 ^ 14 <= p2 <= 2 ^ 14 /\ u 125 mod 2 ^ 32 = (p2 - 32768) mod 2 ^ 32.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 125) as B; unfold p2; clear -F3 B; unfold two64 in *.
  all: Z.div_mod_to_equations; split; lia.
Qed.

#[using="frac ms Hd"] Lemma dcf_spsh : 8 * (u 9 - 2147450880) = u 4 - 2768.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 4) as B4; pose proof (Bnd 9) as B9; clear -F0 F1 F4 B4 B9; unfold SHB, two64 in *.
  all: Z.div_mod_to_equations; lia.
Qed.

#[using="frac ms Hd"] Lemma dcf_text : 6537216 <= u 1 <= 2 ^ 47 - 256 /\ app2r (u 1) (u 1 + 256) /\ 1 <= u 2 <= 128 /\ u 1 + u 2 <= u 4 - 2768 /\
  (4096 * u 10 + 4231168 + 2097152 <= u 1 \/ u 1 + 128 <= 4096 * u 10 + 4231168) /\
  (4096 * u 10 + 36864 <= u 1 \/ u 1 + 256 <= 4096 * u 10) /\
  0 <= u 1 - 8 * u 7 <= 256 /\ 1 <= 8 * u 8 - (u 1 + u 2) <= 256 /\ 0 <= u 7 /\ 0 <= u 8 /\ 8 * u 8 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 1) as B1; pose proof (Bnd 2) as B2; pose proof (Bnd 4) as B4; pose proof (Bnd 10) as B10.
  all: pose proof (Bnd 7) as B7; pose proof (Bnd 8) as B8.
  all: assert (X : 6537216 <= 4096 * u 10 /\ 4096 * u 10 + 11571200 <= 2 ^ 47)
         by (clear -F24; change (6537216 / 4096) with 1596 in F24; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F24; lia).
  all: refine (conj F22 (conj _ (conj F8 _))).
  all: try (apply two_class_app2r; [lia | lia | lia | replace (u 1 - 17594333495296) with (-17594333495296 + (1 * u 1 + 0)) by ring; exact F23]).
  all: split; [clear -F22 F8 F11 B4; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F22 F12 B10 X; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F22 F13 B10 X; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F22 F9 F5 B7; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F22 F8 F10 F6 B8; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -B7; lia|]. all: split; [clear -B8; lia|].
  all: clear -F6; change (2 ^ 47 / 8) with 17592186044416 in F6; lia.
Qed.

#[using="ms Hd"] Lemma dcf_spanf : 0 <= u 25 - u 1 <= 256 /\ 0 <= u 1 + u 2 - (u 25 + u 26) <= 256 /\ 0 <= u 26 <= 128 /\
  (frac = true -> 0 <= u 27 - u 1 <= 256 /\ 0 <= u 1 + u 2 - (u 27 + u 28) <= 256 /\ 0 <= u 28 <= 128).
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 1) as B1; pose proof (Bnd 2) as B2; pose proof (Bnd 25) as B25; pose proof (Bnd 26) as B26.
  all: pose proof (Bnd 27) as B27; pose proof (Bnd 28) as B28.
  all: split; [clear -F22 F15 B25; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F7 F22 F8 F16 B25 B26; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [exact F7|].
  - intros _. split; [clear -F22 F19 B27; unfold two64 in *; Z.div_mod_to_equations; lia|].
    split; [clear -F22 F8 F20 F21 B27 B28; unfold two64 in *; Z.div_mod_to_equations; lia|]. exact F21.
  - intros X; discriminate X.
Qed.

#[using="frac ms Hd"] Lemma dcf_p4 : 0 <= u 12 <= 1023 /\ u 11 mod 1024 = u 12.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 11) as B11; pose proof (Bnd 12) as B12.
  all: clear -F17 F18 B11 B12; unfold two64 in *; change (2 ^ 10) with 1024 in F18; split; [exact F17|]; Z.div_mod_to_equations; lia.
Qed.

#[using="frac ms Hd"] Lemma dcf_fs : 6537216 <= 4096 * u 10 /\ 4096 * u 10 + 11571200 <= 2 ^ 47 /\ app2r (4096 * u 10) (4096 * u 10 + 11571200) /\
  4096 * u 10 + 11571200 <= u 4 - 2768.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 4) as B4; pose proof (Bnd 10) as B10.
  all: assert (X : 6537216 <= 4096 * u 10 /\ 4096 * u 10 + 11571200 <= 2 ^ 47)
         by (clear -F24; change (6537216 / 4096) with 1596 in F24; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F24; lia).
  all: refine (conj (proj1 X) (conj (proj2 X) (conj _ _))).
  2, 4: clear -F14 B4 B10 X; unfold two64 in *; Z.div_mod_to_equations; lia.
  all: apply two_class_app2r; try (clear -X; lia).
  all: replace (4096 * u 10 - 17594333495296) with (-17594333495296 + (4096 * u 10 + 0)) by ring; exact F25.
Qed.

#[using="Type"] Lemma rt_app_of_wrapped : forall x n, 6537216 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. pose proof (two_class_app2r x n H1 H2 H3) as X.
  assert (Y : app2r x (x + n)) by (apply X; replace (x - 17594333495296) with (-17594333495296 + (1 * x + 0)) by ring; exact H4).
  unfold app2r, rt_app in *. destruct Y as [[Y1 Y2]|[Y1 Y2]]; [left|right]; lia.
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

#[using="frac ms Hd"] Lemma dcf_rtf :
  rt_app (u 15) 160 /\ u 15 + 160 <= 2 ^ 47 /\ rt_app (u 16) 80 /\ u 16 + 80 <= 2 ^ 47 /\ rt_app (u 17) 32 /\ u 17 + 32 <= 2 ^ 47 /\
  6537216 <= u 15 /\ 4096 <= u 16 /\ 4096 <= u 17 /\
  1 <= u 18 <= 2 ^ 64 - 1 /\ 1 <= u 21 <= 255 /\
  (u 15 + 160 <= 4096 * u 10 \/ 4096 * u 10 + 11571200 <= u 15) /\
  (u 16 + 80 <= 4096 * u 10 \/ 4096 * u 10 + 11571200 <= u 16) /\
  (u 17 + 32 <= 4096 * u 10 \/ 4096 * u 10 + 11571200 <= u 17) /\
  (u 15 + 160 <= u 4 - 4032 \/ u 4 + 384 <= u 15) /\
  (u 16 + 80 <= u 4 - 4032 \/ u 4 + 384 <= u 16) /\
  (u 17 + 32 <= u 4 - 4032 \/ u 4 + 384 <= u 17).
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts; pose proof (Bnd 4) as B4; pose proof (Bnd 10) as B10; pose proof (Bnd 15) as B15; pose proof (Bnd 16) as B16;
    pose proof (Bnd 17) as B17.
  all: assert (X : 6537216 <= 4096 * u 10 /\ 4096 * u 10 + 11571200 <= 2 ^ 47)
         by (clear -F24; change (6537216 / 4096) with 1596 in F24; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F24; lia).
  all: split; [apply rt_app_of_wrapped; [lia | lia | lia | exact F27]|].
  all: split; [lia|].
  all: split; [apply rt_app_of_wrapped4k; [lia | lia | lia | exact F29]|].
  all: split; [lia|].
  all: split; [apply rt_app_of_wrapped4k; [lia | lia | lia | exact F31]|].
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [exact F32|]. all: split; [exact F33|].
  all: split; [clear -F37 B10 B15 X; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F38 B10 B16 X; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F39 B10 B17 X; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F40 B4 B15; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: split; [clear -F41 B4 B16; unfold two64 in *; Z.div_mod_to_equations; lia|].
  all: clear -F42 B4 B17; unfold two64 in *; Z.div_mod_to_equations; lia.
Qed.

Definition FSv : Z := 4096 * u 10.
Definition Fv : Z := FSv + 4231168 + 1024 * u 12.

#[using="frac ms Hd"] Lemma dcf_rng : 6537216 <= FSv /\ FSv + 11571200 <= 2 ^ 47 /\ 0 <= u 12 <= 1023 /\ FSv + 11571200 <= u 4 - 2768 /\
  17594333495296 <= u 4 - 2768 /\ u 4 + 152 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof dcf_fs as (X1 & X2 & _ & X4). pose proof dcf_p4 as (P & _). pose proof dcf_sp as (_ & S1 & S2).
  unfold FSv. lia.
Qed.

(* [comment removed for export] *)
Ltac uval := ubase_s; rewrite Z.mod_small; [ring | pose proof dcf_rng; pose proof (Bnd 10); pose proof (Bnd 12); unfold FSv, two64 in *; lia].

#[using="frac ms Hd"] Lemma dcf_vals :
  bv_unsigned (lden E (laddc SLOT4 32)) = Fv + 32 /\
  bv_unsigned (lden E (laddc SLOT4 608)) = Fv + 608 /\
  bv_unsigned (lden E SHSLOT4) = 2147450880 + Fv / 8 /\
  bv_unsigned (lden E (fsc 32)) = FSv + 32 /\ bv_unsigned (lden E (fsc 40)) = FSv + 40 /\ bv_unsigned (lden E (fsc 88)) = FSv + 88 /\
  bv_unsigned (lden E (fsc FL4)) = FSv + 34816 /\ bv_unsigned (lden E (ladd (fsc FL4) P4)) = FSv + 34816 + u 12 /\
  bv_unsigned (lden E (ladd (fsc (FL4 + 1)) P4)) = FSv + 34817 + u 12 /\
  bv_unsigned (lden E (fsc AR4)) = FSv + 4231168 /\ bv_unsigned (lden E (ladd (fsc (AR4 + 1024)) (lscale 1024 P4))) = Fv + 1024 /\
  bv_unsigned (lden E (fsh AR4)) = 2147450880 + FSv / 8 + 528896 /\
  bv_unsigned (lden E (ladd (fsh (AR4 + 1024)) (lscale 128 P4))) = 2147450880 + Fv / 8 + 128 /\
  bv_unsigned (lden E (fsh 0x309000)) = 2147450880 + FSv / 8 + 397824 /\
  bv_unsigned (lden E (fsc FL5)) = FSv + 35840 /\ bv_unsigned (lden E (fsc AR5)) = FSv + 5279744 /\
  bv_unsigned (lden E (fsh AR5)) = 2147450880 + FSv / 8 + 659968 /\
  bv_unsigned (lden E (laddc SP (- NDC_NEED))) = u 4 - 2768.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  assert (F8 : Fv = (512 * u 10 + 528896 + 128 * u 12) * 8) by (unfold Fv, FSv; ring).
  assert (S8 : FSv = (512 * u 10) * 8) by (unfold FSv; ring).
  rewrite F8, S8, !Z.div_mul by discriminate. unfold Fv, FSv. unfold SLOT4, SHSLOT4, fsc, fsh, FS, P4, AR4, FL4, FL5, AR5, SP, SHB, NDC_NEED.
  repeat split; uval.
Qed.

(* [comment removed for export] *)
Local Abbreviation m0 := (ms_mem ms).

#[using="frac Hd"] Lemma dcf_win : stk BSEGS m0 (u 4 - 2768) (u 4).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as V.
  apply (stk_of_rg BSEGS E _ _ _ _ R2 ltac:(left; reflexivity)); cbn [rg_base RGz].
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 V))))))))))))))))).
  - unfold rsz. cbn [rg_size RGz]. change (bv_unsigned (lden E (lconst NDC_NEED))) with 2768. lia.
Qed.

#[using="frac Hd"] Lemma dcf_spsh_bytes : bytes_at BSEGS m0 (2147450880 + (u 4 - 2768) / 8) (repeat (Z_to_bv 8 0) 365).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_spsh as S. pose proof dcf_sp as (S1 & _).
  assert (B : bv_unsigned (lden E (rg_base (RGz SPSH 365 RZ TEmpty))) = 2147450880 + (u 4 - 2768) / 8).
  { cbn [rg_base RGz]. unfold SPSH. rewrite lden_lvar. rewrite <- S. replace (8 * (u 9 - 2147450880)) with ((u 9 - 2147450880) * 8) by ring.
    rewrite Z.div_mul by discriminate. ring. }
  exact (zeros_bytes_of_rz BSEGS E _ _ _ 365%nat R3 eq_refl eq_refl B ltac:(reflexivity)).
Qed.




#[using="frac Hd"] Lemma dcf_slot : stk BSEGS m0 (Fv + 32) (Fv + 1016).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (V & _).
  apply (stk_of_rg BSEGS E _ _ _ _ R4 ltac:(left; reflexivity)); cbn [rg_base track].
  - exact V.
  - unfold rsz. cbn [rg_size track]. change (bv_unsigned (lden E (lconst 984))) with 984. lia.
Qed.

#[using="frac ms Hd"] Lemma dcf_sp104 : bv_unsigned (lden E (laddc SP 104)) = u 4 + 104 /\ bv_unsigned (lden E (laddc SP 144)) = u 4 + 144.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0).
  split; unfold SP; ubase_s; (rewrite Z.mod_small; [ring | pose proof dcf_rng; pose proof (Bnd 4); unfold two64 in *; lia]).
Qed.

#[using="Hd"] Lemma dcf_spans_bytes : bytes_at BSEGS m0 (u 4 + 104)
  (le8 (E 25%positive) ++ le8 (E 26%positive) ++ (if frac then le8 (E 27%positive) ++ le8 (E 28%positive) else repeat (Z_to_bv 8 0) 16)).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_sp104 as (V & _).
  pose proof (track_bytes_at BSEGS E m0 _ 0 _ R38 ltac:(lia) ltac:(destruct frac; cbn; lia)) as X.
  cbn [rg_base RGz] in X. rewrite V, Z.add_0_r in X.
  apply (bytes_at_ext BSEGS _ _ _ _ X). unfold dcf_spans. rewrite !map_app. unfold bv8. rewrite !map_bden_bv8.
  unfold IPTR, ILEN, FPTR, FLEN. rewrite !lden_lvar. destruct frac; [rewrite map_app, !map_bden_bv8, !lden_lvar; reflexivity|].
  cbn. reflexivity.
Qed.

#[using="frac Hd"] Lemma dcf_dg : exists dg, rw_cells BSEGS m0 (u 4 + 144) [C8 dg].
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. apply (word_of_stk BSEGS).
  apply (stk_of_rg BSEGS E _ _ _ _ R37 ltac:(left; reflexivity)); cbn [rg_base RGz].
  - unfold SP. ubase_s. rewrite Z.mod_small; [ring | pose proof dcf_rng; pose proof (Bnd 4); unfold two64 in *; lia].
  - unfold rsz. cbn [rg_size RGz]. change (bv_unsigned (lden E (lconst 8))) with 8. ring.
Qed.

#[using="frac Hd"] Lemma dcf_old : exists old, u8arr BSEGS m0 (Fv + 32) old /\ length old = 504%nat.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  apply (u8arr_of_stk BSEGS). destruct (stk_split BSEGS _ _ (Fv + 32 + Z.of_nat 504) _ dcf_slot ltac:(lia)) as (X & _). exact X.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdbl_of_rg : forall m R A n, rg_ok BSEGS E m R -> rg_kind R <> RO -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n ->
  rdbl BSEGS m A n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m R A n HR Hk Hb Hs. pose proof (rg_flat BSEGS E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
  pose proof (rd_of_rg BSEGS E m R i HR ltac:(lia) Hk) as X. rewrite Hb in X.
  destruct (mrd BSEGS m (wa (A + i))) as [b|]; [exists b; reflexivity | exfalso; exact (X eq_refl)].
Qed.
#[using="Type"] Lemma rdbl_app : forall m a n1 n2, rdbl BSEGS m a n1 -> rdbl BSEGS m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> rdbl BSEGS m a (n1 + n2).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n1 n2 (A1 & A2 & A) (B1 & B2 & B) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.ltb_spec0 i n1); [apply A; lia|]. replace (a + i) with (a + n1 + (i - n1)) by ring. apply B; lia.
Qed.
#[using="Type"] Lemma rdbl_sub : forall m a n a' n', rdbl BSEGS m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> rdbl BSEGS m a' n'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n a' n' (A1 & A2 & A) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by ring. apply A; lia.
Qed.
#[using="Type"] Lemma shz_of_bytes : forall m a n, bytes_at BSEGS m a (repeat (Z_to_bv 8 0) n) -> shz BSEGS m a (Z.of_nat n).
Proof. LiaFast.lf_pins LiaFast.u0. intros m a n X. split; [lia|]. rewrite Nat2Z.id. exact X. Qed.
#[using="Type"] Lemma bytes_at_zeros_sub : forall m a n k j, bytes_at BSEGS m a (repeat (Z_to_bv 8 0) n) -> (k + j <= n)%nat ->
  bytes_at BSEGS m (a + Z.of_nat k) (repeat (Z_to_bv 8 0) j).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n k j X H. replace n with (k + (j + (n - k - j)))%nat in X by lia. rewrite !repeat_app in X.
  apply bytes_at_app in X as (_ & X). rewrite repeat_length in X. apply bytes_at_app in X as (X & _). exact X.
Qed.

#[using="frac ms Hd"] Lemma dcf_Fv8 : Fv mod 8 = 0 /\ 0 <= Fv.
Proof. LiaFast.lf_pins (fun (frac ms Hd : LiaFast.U) => LiaFast.u0). pose proof dcf_rng. unfold Fv, FSv in *. split; [|lia]. replace (4096 * u 10 + 4231168 + 1024 * u 12) with ((512 * u 10 + 528896 + 128 * u 12) * 8) by ring. apply Z_mod_mult. Qed.

#[using="frac Hd"] Lemma dcf_shz_A : shz BSEGS m0 (2147450880 + (Fv + 32) / 8) 63.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (_ & _ & V & _). pose proof dcf_Fv8 as (F8 & _).
  assert (E1 : (Fv + 32) / 8 = Fv / 8 + 4) by (Z.div_mod_to_equations; lia).
  rewrite E1.
  pose proof (cont_bytes_at BSEGS E m0 _ 4 (repeat (BK 0) 63) R5 ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as X.
  cbn [rg_base track] in X. rewrite V in X.
  change 63 with (Z.of_nat 63). apply shz_of_bytes. rewrite map_repeat in X. rewrite Z.add_assoc. exact X.
Qed.

#[using="frac Hd"] Lemma dcf_rdbl_A : rdbl BSEGS m0 (2147450880 + (Fv + 32) / 8 - 8) 79.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (_ & _ & V3 & _ & _ & _ & _ & _ & _ & _ & _ & V12 & _ & V14 & _).
  pose proof dcf_Fv8 as (F8 & _). pose proof dcf_rng as RNG.
  assert (E1 : (Fv + 32) / 8 = Fv / 8 + 4) by (Z.div_mod_to_equations; lia).
  assert (E2 : Fv / 8 = FSv / 8 + 528896 + 128 * u 12) by (unfold Fv; unfold FSv in *; Z.div_mod_to_equations; lia).
  rewrite E1. replace (2147450880 + (Fv / 8 + 4) - 8) with (2147450880 + Fv / 8 - 4) by ring. change 79 with (4 + 75).
  apply rdbl_app; [ | | lia | lia].
  - destruct (Z.eqb_spec (u 12) 0) as [P0|P0].
    + (* [comment removed for export] *)
      eapply (rdbl_sub m0 (2147450880 + FSv / 8 + 397824) 131072); [ | lia | lia | lia].
      apply (rdbl_of_rg m0 _ _ _ R14); [discriminate | exact V14 | reflexivity].
    + eapply (rdbl_sub m0 (2147450880 + FSv / 8 + 528896) (128 * u 12)); [ | lia | lia | lia].
      apply (rdbl_of_rg m0 _ _ _ R12); [discriminate | exact V12 |].
      unfold rsz. cbn [rg_size]. unfold P4. ubase_s. rewrite Z.mod_small; [ring | pose proof (Bnd 12); unfold two64 in *; lia].
  - replace (2147450880 + Fv / 8 - 4 + 4) with (2147450880 + Fv / 8) by ring.
    eapply (rdbl_sub m0 (2147450880 + Fv / 8) 128); [ | lia | lia | lia].
    apply (rdbl_of_rg m0 _ _ _ R5); [discriminate | exact V3 | reflexivity].
Qed.

#[using="frac Hd"] Lemma dcf_shz_sp : shz BSEGS m0 (2147450880 + (u 4 - 2768) / 8) 346 /\ shz BSEGS m0 (2147450880 + (u 4 + 144) / 8) 1 /\
  shz BSEGS m0 (2147450880 + (u 4 + 104) / 8) 4.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  pose proof dcf_spsh_bytes as X. pose proof dcf_sp as (S16 & _).
  assert (E1 : (u 4 + 144) / 8 = (u 4 - 2768) / 8 + 364) by (Z.div_mod_to_equations; lia).
  assert (E2 : (u 4 + 104) / 8 = (u 4 - 2768) / 8 + 359) by (Z.div_mod_to_equations; lia).
  split; [|split].
  - change 346 with (Z.of_nat 346). apply shz_of_bytes.
    pose proof (bytes_at_zeros_sub m0 _ 365 0 346 X ltac:(lia)) as Y. rewrite Z.add_0_r in Y. exact Y.
  - change 1 with (Z.of_nat 1). apply shz_of_bytes. rewrite E1.
    pose proof (bytes_at_zeros_sub m0 _ 365 364 1 X ltac:(lia)) as Y. change (Z.of_nat 364) with 364 in Y. rewrite <- Z.add_assoc in Y. exact Y.
  - change 4 with (Z.of_nat 4). apply shz_of_bytes. rewrite E2.
    pose proof (bytes_at_zeros_sub m0 _ 365 359 4 X ltac:(lia)) as Y. change (Z.of_nat 359) with 359 in Y. rewrite <- Z.add_assoc in Y. exact Y.
Qed.

#[using="frac E Hd"] Lemma dcf_tabs : shz BSEGS m0 2147469908 20 /\ shz BSEGS m0 2147469932 32.
Proof. LiaFast.lf_pins (fun (frac E Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. split.
  - change 20 with (Z.of_nat 20). apply shz_of_bytes.
    exact (zeros_bytes_of_rz BSEGS E _ _ _ 20%nat R35 eq_refl eq_refl ltac:(reflexivity) ltac:(reflexivity)).
  - change 32 with (Z.of_nat 32). apply shz_of_bytes.
    exact (zeros_bytes_of_rz BSEGS E _ _ _ 32%nat R36 eq_refl eq_refl ltac:(reflexivity) ltac:(reflexivity)).
Qed.

#[using="frac Hd"] Lemma dcf_rdbl_fs : rdbl BSEGS m0 (2147450880 + FSv / 8 + 397824) 393216.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (_ & _ & V3 & _ & _ & _ & _ & _ & _ & _ & _ & V12 & V13 & V14 & _ & _ & V17 & _).
  pose proof dcf_Fv8 as (F8 & _). pose proof dcf_rng as RNG.
  assert (E2 : Fv / 8 = FSv / 8 + 528896 + 128 * u 12) by (unfold Fv; unfold FSv in *; Z.div_mod_to_equations; lia).
  replace 393216 with (131072 + (128 * u 12 + (128 + (128 * (1023 - u 12) + 131072)))) by ring.
  apply rdbl_app; [ | | lia | lia].
  { apply (rdbl_of_rg m0 _ _ _ R14); [discriminate | exact V14 | reflexivity]. }
  replace (2147450880 + FSv / 8 + 397824 + 131072) with (2147450880 + FSv / 8 + 528896) by ring.
  apply rdbl_app; [ | | lia | lia].
  { apply (rdbl_of_rg m0 _ _ _ R12); [discriminate | exact V12 |].
    unfold rsz. cbn [rg_size]. unfold P4. ubase_s. rewrite Z.mod_small; [ring | pose proof (Bnd 12); unfold two64 in *; lia]. }
  replace (2147450880 + FSv / 8 + 528896 + 128 * u 12) with (2147450880 + Fv / 8) by (rewrite E2; ring).
  apply rdbl_app; [ | | lia | lia].
  { apply (rdbl_of_rg m0 _ _ _ R5); [discriminate | exact V3 | reflexivity]. }
  apply rdbl_app; [ | | lia | lia].
  { apply (rdbl_of_rg m0 _ _ _ R13); [discriminate | exact V13 |].
    unfold rsz. cbn [rg_size]. unfold P4. ubase_s. rewrite Z.mod_small; [ring | pose proof (Bnd 12); unfold two64 in *; lia]. }
  replace (2147450880 + Fv / 8 + 128 + 128 * (1023 - u 12)) with (2147450880 + FSv / 8 + 659968) by (rewrite E2; ring).
  apply (rdbl_of_rg m0 _ _ _ R18); [discriminate | exact V17 | reflexivity].
Qed.

Definition v0 : rt_vals := RTV FSv (u 15) (u 16) (u 19) (u 20) (u 17) (u 18).

(* [comment removed for export] *)
Ltac const_cells G o :=
  let X := fresh "X" in
  pose proof (track_bytes_at BSEGS E m0 _ o _ G ltac:(clear; lia) ltac:(cbn; clear; lia)) as X;
  cbn [rg_base RGz track] in X; change (bv_unsigned (lden E (lconst ?z))) with (z mod two64) in X;
  rewrite Z.mod_small in X by (unfold two64; clear; lia);
  apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].

Ltac gdj HD k j :=
  let G := fresh "G" in
  pose proof (rgs_disj_nth E _ k j _ _ HD ltac:(discriminate) eq_refl eq_refl) as G;
  unfold rg_disj, rsz in G; cbn [rg_base rg_size track RGz] in G; lnorm_in G;
  repeat match type of G with context [bv_unsigned (Z_to_bv 64 (?a + 0))] =>
    let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 (a + 0))) in change (bv_unsigned (Z_to_bv 64 (a + 0))) with v in G end;
  exact G.
(* [comment removed for export] *)
#[using="frac Hd"] Lemma dcf_rtx : RTX v0 (ms_fcsr ms).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  pose proof dcf_rtf as (_ & _ & _ & _ & _ & _ & C1 & C2 & C3 & _).
  pose proof (sden_frm BSEGS E _ ms Hd) as Hfrm.
  assert (HDJ : (u 15 + 160 <= u 16 \/ u 16 + 80 <= u 15) /\ (u 15 + 160 <= u 17 \/ u 17 + 32 <= u 15) /\
                (u 16 + 80 <= u 17 \/ u 17 + 32 <= u 16)).
  { destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & HD & _). cbn [s_rgs DCF_P0] in HD.
    pose proof (rgs_disj_nth E _ 29 30 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D1.
    pose proof (rgs_disj_nth E _ 29 31 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D2.
    pose proof (rgs_disj_nth E _ 30 31 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D3.
    unfold rg_disj, rsz in D1, D2, D3. cbn [rg_base rg_size track RGz] in D1, D2, D3. lnorm_in D1. lnorm_in D2. lnorm_in D3.
    change (bv_unsigned (Z_to_bv 64 (160 + 0))) with 160 in D1, D2.
    change (bv_unsigned (Z_to_bv 64 (80 + 0))) with 80 in D1, D3.
    change (bv_unsigned (Z_to_bv 64 (32 + 0))) with 32 in D2, D3.
    clear -D1 D2 D3. split; [|split]; lia. }
  (* [comment removed for export] *)
  assert (HIMG : (forall b n, In (b, n) RT_IMG_IVS -> b + n <= u 16 \/ u 16 + 80 <= b) /\
                 (forall b n, In (b, n) RT_IMG_IVS -> b + n <= u 17 \/ u 17 + 32 <= b)).
  { destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & HD & _). cbn [s_rgs DCF_P0] in HD.
    split; intros b n Hin; cbn [RT_IMG_IVS In] in Hin;
      destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <-.
    1: gdj HD 34%nat 30%nat. 1: gdj HD 20%nat 30%nat. 1: gdj HD 21%nat 30%nat. 1: gdj HD 22%nat 30%nat. 1: gdj HD 23%nat 30%nat.
    1: gdj HD 24%nat 30%nat. 1: gdj HD 25%nat 30%nat. 1: gdj HD 26%nat 30%nat. 1: gdj HD 27%nat 30%nat. 1: gdj HD 28%nat 30%nat.
    1: gdj HD 32%nat 30%nat. 1: gdj HD 33%nat 30%nat.
    1: gdj HD 34%nat 31%nat. 1: gdj HD 20%nat 31%nat. 1: gdj HD 21%nat 31%nat. 1: gdj HD 22%nat 31%nat. 1: gdj HD 23%nat 31%nat.
    1: gdj HD 24%nat 31%nat. 1: gdj HD 25%nat 31%nat. 1: gdj HD 26%nat 31%nat. 1: gdj HD 27%nat 31%nat. 1: gdj HD 28%nat 31%nat.
    1: gdj HD 32%nat 31%nat. gdj HD 33%nat 31%nat. }
  destruct HIMG as (HIMGt & HIMGb).
  unfold RTX, v0. cbn [rt_ctx rt_thr rt_blk]. split; [|split; [exact Hfrm | exact (conj (proj1 HDJ) (conj (proj1 (proj2 HDJ)) (conj (proj2 (proj2 HDJ)) (conj HIMGt HIMGb))))]].
  open_facts. all: change (2 ^ 3) with 8 in F34, F35, F36.
  all: refine (conj C1 (conj C2 (conj C3 (conj F34 (conj F35 F36))))).
Qed.

#[using="frac Hd"] Lemma dcf_RT : RT m0 v0.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. unfold RT. cbn [rt_FS rt_ctx rt_thr rt_tlsb rt_tlse rt_blk rt_beg v0].
  pose proof dcf_rtf as (Ac & Ac2 & At & At2 & Ab & Ab2 & Lc & Lt & Lb & Hg & Hfb & _).
  pose proof dcf_fs as (Fs1 & Fs2 & Fs3 & _). unfold KHI, KTOP in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  - unfold sb_uar in R20. const_cells R20 0.
  - (* [comment removed for export] *)
    pose proof (track_bytes_at BSEGS E m0 _ 0 _ R21 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 941792))) with 941792 in X.
    pose proof (bytes_at_sub BSEGS _ _ _ 0 1 X ltac:(cbn; lia)) as Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - pose proof (track_bytes_at BSEGS E m0 _ 0 _ R21 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 941792))) with 941792 in X.
    pose proof (bytes_at_sub BSEGS _ _ _ 4 4 X ltac:(cbn; lia)) as Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - const_cells R22 0.
  - const_cells R23 0.
  - exists (Z_to_bv 8 (u 21)). split.
    + pose proof (track_bytes_at BSEGS E m0 _ 0 _ R25 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 1540657))) with 1540657 in X. rewrite Z.add_0_r in X.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. cbn [List.map bden] in X. lnorm_in X. rewrite Z.shiftr_0_r in X. exact X.
    + rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by (clear -Hfb; lia). clear -Hfb; lia.
  - const_cells R24 0.
  - const_cells R26 0.
  - (* [comment removed for export] *)
    split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_bytes_at BSEGS E m0 _ 0 (bk8 6396000) R27 ltac:(clear; lia) ltac:(cbn; clear; lia)
                    ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X. rewrite Z.add_0_r in X.
      apply (bytes_at_ext BSEGS _ _ _ _ X). apply bytes_eqb_eq. vm_compute. reflexivity.
    + pose proof (cont_le8 BSEGS E m0 _ 8 FS R27 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
      lnorm_in X. rewrite Z.add_0_l, Z.add_0_r in X. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 16 BLK R27 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - pose proof (cont_bytes_at BSEGS E m0 _ 48 (bk8 6398016) R27 ltac:(clear; lia) ltac:(cbn; clear; lia)
                  ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 0 CTX R28 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6532072))) with 6532072 in X.
    lnorm_in X. rewrite ?Z.add_0_r in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 152 THR R29 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_le8 BSEGS E m0 _ 48 TLSB R30 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
    + pose proof (cont_le8 BSEGS E m0 _ 56 TLSE R30 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. lnorm_in X. rewrite !Z_to_bv_bv_unsigned, length_le8.
      replace (u 16 + 48 + Z.of_nat 8) with (u 16 + 56) by lia. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E m0 _ 24 BEG R31 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - unfold FSv in *. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fs3 (conj Fs2 (conj _ (conj Ac (conj Ac2 (conj At (conj At2 (conj Ab Ab2))))))))))))).
    all: try (clear -Hg; unfold two64 in *; lia).
    all: try (clear -Lc; lia). all: try (clear -Lt; lia). all: try (clear -Lb Ab2; lia).
Qed.

#[using="frac Hd"] Lemma dcf_fshdr : fs_cells_ok FSv m0.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (_ & _ & _ & _ & _ & V6 & _). unfold fs_cells_ok, fs_hdr in *.
  pose proof (track_bytes_at BSEGS E m0 _ 0 _ R19 ltac:(lia) ltac:(cbn; lia)) as X.
  cbn [rg_base RGz] in X. rewrite V6, Z.add_0_r in X. apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
Qed.

#[using="Type"] Lemma stk_of_rgv : forall m R lo hi, rg_ok BSEGS E m R -> rg_kind R = RW -> bv_unsigned (lden E (rg_base R)) = lo -> rsz E R = hi - lo ->
  stk BSEGS m lo hi.
Proof. LiaFast.lf_pins LiaFast.u0. intros m R lo hi HR Hk Hb Hs. exact (stk_of_rg BSEGS E m R lo hi HR (or_introl Hk) Hb Hs). Qed.

#[using="frac Hd"] Lemma dcf_fk4 : fk4_nest m0 FSv (Z_to_bv 64 (u 11 + 1)) (u 12).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (_ & _ & V3 & V4 & _ & _ & V7 & V8 & V9 & V10 & V11 & V12 & V13 & _).
  pose proof dcf_rng as RNG. pose proof dcf_Fv8 as (F8 & _). pose proof (Bnd 12) as B12. pose proof (Bnd 11) as B11.
  assert (E2 : Fv / 8 = FSv / 8 + 528896 + 128 * u 12) by (unfold Fv; unfold FSv in *; Z.div_mod_to_equations; lia).
  unfold fk4_nest. refine (conj dcf_fshdr (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - (* [comment removed for export] *)
    pose proof (track_bytes_at BSEGS E m0 _ 0 _ R6 ltac:(lia) ltac:(cbn; lia)) as X. cbn [rg_base RGz] in X. rewrite V4, Z.add_0_r in X.
    unfold bv8 in X. rewrite map_bden_bv8 in X. split; [split; [exact (conj I I)|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. replace (Z_to_bv 64 (u 11 + 1)) with (lden E (laddc H4 1)); [exact X|].
      unfold H4. lnorm_s. unfold vz. f_equal. ring.
    + cbn [cells_size csize]. change (Z.of_nat (8 + 0)) with 8.
      exact (wr_at_of_rg BSEGS E _ _ _ _ R6 ltac:(left; reflexivity) ltac:(cbn [track rg_base RGz]; exact V4) eq_refl).
  - (* [comment removed for export] *)
    assert (Z2 : rsz E (RG (fsc FL4) P4 RZ TEmpty) = u 12) by (unfold rsz; cbn [rg_size]; unfold P4; rewrite lden_lvar; reflexivity).
    assert (Z4 : rsz E (RG (ladd (fsc (FL4 + 1)) P4) (laddc (lscale (-1) P4) 1023) RZ TEmpty) = 1023 - u 12)
      by (unfold rsz; cbn [rg_size]; unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
    assert (HB : forall i, 0 <= i < 1024 ->
               mrd BSEGS m0 (wa (FSv + 34816 + i)) = Some (if Z.eqb i (u 12) then Z_to_bv 8 1 else Z_to_bv 8 0) /\
               wview BSEGS m0 (wa (FSv + 34816 + i)) <> None).
    { intros i Hi. destruct (Z.ltb_spec i (u 12)) as [H1|H1]; [|destruct (Z.eqb_spec i (u 12)) as [H2|H2]].
      - rewrite (proj2 (Z.eqb_neq i (u 12))) by lia.
        pose proof (zero_bytes_of_rz BSEGS E _ _ i R7 eq_refl eq_refl ltac:(rewrite Z2; lia)) as X. cbn [rg_base] in X. rewrite V7 in X.
        split; [exact X|]. pose proof (rdwr_of_rg BSEGS E _ _ i R7 ltac:(right; left; reflexivity) ltac:(rewrite Z2; lia)) as (_ & W).
        cbn [rg_base] in W. rewrite V7 in W. exact W.
      - subst i.
        pose proof (track_bytes_at BSEGS E m0 _ 0 _ R8 ltac:(lia) ltac:(cbn; lia)) as X. cbn [rg_base] in X. rewrite V8, Z.add_0_r in X.
        destruct X as (_ & _ & X). specialize (X 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in X. cbn in X. split; [exact X|].
        pose proof (rdwr_of_rg BSEGS E _ _ 0 R8 ltac:(right; left; reflexivity) ltac:(unfold rsz; cbn [track rg_size]; change (bv_unsigned (lden E (lconst 1))) with 1; lia)) as (_ & W).
        cbn [rg_base track] in W. rewrite V8, Z.add_0_r in W. exact W.
      - pose proof (zero_bytes_of_rz BSEGS E _ _ (i - u 12 - 1) R9 eq_refl eq_refl ltac:(rewrite Z4; lia)) as X. cbn [rg_base] in X.
        rewrite V9 in X. replace (FSv + 34817 + u 12 + (i - u 12 - 1)) with (FSv + 34816 + i) in X by ring.
        split; [exact X|]. pose proof (rdwr_of_rg BSEGS E _ _ (i - u 12 - 1) R9 ltac:(right; left; reflexivity) ltac:(rewrite Z4; lia)) as (_ & W).
        cbn [rg_base] in W. rewrite V9 in W. replace (FSv + 34817 + u 12 + (i - u 12 - 1)) with (FSv + 34816 + i) in W by ring. exact W. }
    split.
    + split; [lia|]. split; [rewrite upd_length, zeros_length; unfold two64 in *; lia|].
      intros i Hi. rewrite upd_length, zeros_length in Hi. pose proof (HB (Z.of_nat i) ltac:(lia)) as (X & _). rewrite X.
      destruct (Z.eqb_spec (Z.of_nat i) (u 12)) as [He|He].
      * rewrite <- He, Nat2Z.id. rewrite nth_error_upd_same by (rewrite zeros_length; lia). reflexivity.
      * rewrite nth_error_upd_other by lia. rewrite nth_error_zeros by lia. reflexivity.
    + rewrite upd_length, zeros_length. split; [lia|]. split; [unfold two64 in *; lia|].
      intros i Hi. exact (proj2 (HB i ltac:(lia))).
  - apply (stk_of_rgv m0 _ _ _ R10 eq_refl V10). unfold rsz. cbn [rg_size]. unfold P4. ubase_s.
    rewrite Z.mod_small; [ring | unfold two64 in *; lia].
  - apply (stk_of_rgv m0 _ _ _ R11 eq_refl); cbn [rg_base].
    + rewrite V11. unfold Fv. ring.
    + unfold rsz. cbn [rg_size]. unfold P4. ubase_s. rewrite Z.mod_small; [ring | unfold two64 in *; lia].
  - apply (stk_of_rgv m0 _ _ _ R12 eq_refl V12). unfold rsz. cbn [rg_size]. unfold P4. ubase_s.
    rewrite Z.mod_small; [ring | unfold two64 in *; lia].
  - apply (stk_of_rgv m0 _ _ _ R13 eq_refl); cbn [rg_base].
    + rewrite V13, E2. ring.
    + unfold rsz. cbn [rg_size]. unfold P4. ubase_s. rewrite Z.mod_small; [ring | unfold two64 in *; lia].
Qed.

#[using="frac Hd"] Lemma dcf_fk5 : fk5_inv m0 FSv (E 13%positive).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (_ & _ & _ & _ & V5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & V15 & V16 & V17 & _).
  unfold fk5_inv. refine (conj dcf_fshdr (conj _ (conj _ (conj _ _)))).
  - pose proof (track_bytes_at BSEGS E m0 _ 0 _ R15 ltac:(lia) ltac:(cbn; lia)) as X. cbn [rg_base RGz] in X. rewrite V5, Z.add_0_r in X.
    unfold bv8 in X. rewrite map_bden_bv8 in X. unfold H5 in X. rewrite lden_lvar in X. split; [split; [exact (conj I I)|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact X.
    + cbn [cells_size csize]. change (Z.of_nat (8 + 0)) with 8.
      exact (wr_at_of_rg BSEGS E _ _ _ _ R15 ltac:(left; reflexivity) ltac:(cbn [track rg_base RGz]; exact V5) eq_refl).
  - split.
    + exact (zeros_bytes_of_rz BSEGS E _ _ _ 512%nat R16 eq_refl eq_refl V15 ltac:(reflexivity)).
    + rewrite zeros_length. exact (wr_at_of_rg BSEGS E _ _ _ _ R16 ltac:(right; left; reflexivity) V15 ltac:(reflexivity)).
  - apply (stk_of_rgv m0 _ _ _ R17 eq_refl V16). unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst (2 ^ 20)))) with 1048576; ring.
  - apply (stk_of_rgv m0 _ _ _ R18 eq_refl V17). unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst (2 ^ 17)))) with 131072; ring.
Qed.

#[using="frac E Hd"] Lemma dcf_pristine : pristine m0 65536 253952 /\ pristine m0 892928 917504 /\ pristine m0 918096 918488.
Proof. LiaFast.lf_pins (fun (frac E Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. split; [|split].
  - exact (pristine_of_rg_ro BSEGS E _ _ 65536 188416 R34 eq_refl eq_refl eq_refl).
  - exact (pristine_of_rg_ro BSEGS E _ _ 892928 24576 R32 eq_refl eq_refl eq_refl).
  - exact (pristine_of_rg_ro BSEGS E _ _ 918096 392 R33 eq_refl eq_refl eq_refl).
Qed.

#[using="frac Hd"] Lemma dcf_text_rd : forall a, u 1 <= a < u 1 + u 2 -> mrd BSEGS m0 (wa a) <> None.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. intros a Ha. pose proof (rd_of_rg BSEGS E m0 _ (a - u 1) R0) as X. cbn [rg_base rg_kind] in X.
  unfold T in X. rewrite lden_lvar in X. replace (u 1 + (a - u 1)) with a in X by ring. apply X; [|discriminate].
  unfold rsz. cbn [rg_size]. unfold L. rewrite lden_lvar. lia.
Qed.

#[using="frac Hd"] Lemma dcf_ibs : exists ibs, bytes_at BSEGS m0 (u 25) ibs /\ length ibs = Z.to_nat (u 26).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  pose proof dcf_text as (T1 & _ & T2 & _). pose proof dcf_spanf as (S1 & S2 & S3 & _).
  apply bytes_exist; [lia | rewrite Z2Nat.id by lia; lia |].
  intros i Hi. apply dcf_text_rd. lia.
Qed.

#[using="Hd"] Lemma dcf_fbs : frac = true -> exists fbs, bytes_at BSEGS m0 (u 27) fbs /\ length fbs = Z.to_nat (u 28).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  intros Hf. pose proof dcf_text as (T1 & _ & T2 & _). pose proof dcf_spanf as (_ & _ & _ & S4). specialize (S4 Hf) as (S1 & S2 & S3).
  apply bytes_exist; [lia | rewrite Z2Nat.id by lia; lia |].
  intros i Hi. apply dcf_text_rd. lia.
Qed.

#[using="frac Hd"] Lemma dcf_cshz : shz BSEGS m0 (2147450880 + u 7) (u 8 - u 7).
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_text as (T1 & _ & T2 & _ & _ & _ & Z1 & Z2 & Z3 & Z4 & Z5).
  assert (B : bv_unsigned (lden E (rg_base (RG (ladd Y0 (lconst SHB)) (lsub Y1 Y0) RZ TEmpty))) = 2147450880 + u 7).
  { cbn [rg_base]. unfold Y0, SHB. ubase_s. rewrite Z.mod_small; [ring | pose proof (Bnd 7); unfold two64 in *; lia]. }
  assert (S : rsz E (RG (ladd Y0 (lconst SHB)) (lsub Y1 Y0) RZ TEmpty) = Z.of_nat (Z.to_nat (u 8 - u 7))).
  { unfold rsz. cbn [rg_size]. unfold Y0, Y1. ubase_s. rewrite Z2Nat.id by lia. rewrite Z.mod_small; [ring | pose proof (Bnd 7); pose proof (Bnd 8); unfold two64 in *; lia]. }
  pose proof (zeros_bytes_of_rz BSEGS E _ _ _ _ R1 eq_refl eq_refl B S) as X.
  split; [lia|]. exact X.
Qed.

(* [comment removed for export] *)
#[using="frac Hd"] Lemma dcf_regs :
  getr (ms_regs ms) 4 = Z_to_bv 64 6395968 /\ getr (ms_regs ms) 2 = E 4%positive /\ getr (ms_regs ms) 9 = E 4%positive /\
  bv_unsigned (getr (ms_regs ms) 23) = Fv + 32 /\ getr (ms_regs ms) 24 = E 124%positive /\ getr (ms_regs ms) 25 = E 125%positive /\
  getr (ms_regs ms) 1 = E 101%positive.
Proof. LiaFast.lf_pins (fun (frac Hd : LiaFast.U) => LiaFast.u0).
  open_dcf. pose proof dcf_vals as (V1 & V2 & _).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - pose proof (HR 4%bv) as X. rget_norm_in X. rewrite X. reflexivity.
  - pose proof (HR 2%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 9%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 23%bv) as X. rget_norm_in X. rewrite X. exact V1.
  - pose proof (HR 24%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 25%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 1%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
Qed.

(* [comment removed for export] *)
Section Run.
Hypothesis DCFS : dcf_d_stmt.

Definition fptrv : word := if frac then E 27%positive else Z_to_bv 64 0.

#[using="Hd"] Lemma dcf_fbs_any : exists fbs, bytes_at BSEGS m0 (bv_unsigned fptrv) fbs /\
  (bv_unsigned fptrv + Z.of_nat (length fbs) < 2 ^ 64) /\ (Z.of_nat (length fbs) < 2 ^ 40) /\
  (bv_unsigned fptrv = 0 -> length fbs = 0%nat) /\
  (bv_unsigned fptrv <> 0 -> u 1 <= bv_unsigned fptrv /\ bv_unsigned fptrv + Z.of_nat (length fbs) <= u 1 + u 2) /\
  (bv_unsigned fptrv <> 0 -> shz BSEGS m0 (2147450880 + u 7) (u 8 - u 7) /\ 0 <= u 7 <= bv_unsigned fptrv / 8 /\
       bv_unsigned fptrv + Z.of_nat (length fbs) <= 8 * (u 7 + (u 8 - u 7)) <= 2 ^ 47) /\
  Z_to_bv 64 (Z.of_nat (length fbs)) = (if frac then E 28%positive else Z_to_bv 64 0).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  pose proof dcf_text as (T1 & _ & T2 & _ & _ & _ & Z1 & Z2 & Z3 & Z4 & Z5). pose proof dcf_cshz as CS. unfold fptrv.
  pose proof dcf_spanf as (_ & _ & _ & S4). pose proof dcf_fbs as FBL. pose proof (Bnd 27) as B27.
  destruct frac eqn:Hf.
  - specialize (S4 eq_refl) as (S1 & S2 & S3).
    destruct (FBL eq_refl) as (fbs & FB & Lf). exists fbs. rewrite Lf, Z2Nat.id by lia.
    refine (conj FB (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + unfold two64 in *; lia.
    + lia.
    + intros X. unfold two64 in *; lia.
    + intros _. lia.
    + intros _. split; [exact CS|]. split; [split; [lia|]; apply Z.div_le_lower_bound; lia | lia].
    + apply Z_to_bv_bv_unsigned.
  - exists []. change (bv_unsigned (Z_to_bv 64 0)) with 0. cbn [length Z.of_nat].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    all: first [ reflexivity | lia | (split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia)
               | (intros X; exfalso; exact (X eq_refl)) ].
Qed.

#[using="Hd DCFS"] Lemma dcf_kit : exists fbs : list byte, evt BSEGS (dcf_post (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4)
     (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
     (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (Z_to_bv 64 (se + 1)) (getr (ms_regs ms) 25)
     (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (ms_fregs ms) (ms_fcsr ms) (Fv + 32) v0 (u 12) m0) (kms BSEGS ms)
  /\ Z_to_bv 64 (Z.of_nat (length fbs)) = (if frac then E 28%positive else Z_to_bv 64 0).
Proof. LiaFast.lf_pins (fun (Hd DCFS : LiaFast.U) => LiaFast.u0).
  open_dcf.
  destruct dcf_ibs as (ibs & IBS & Lib). destruct dcf_old as (old & OLD & Lold). destruct dcf_dg as (dg & DG).
  destruct dcf_fbs_any as (fbs & FBS & FB1 & FB2 & FB3 & FB4 & FB5 & FB6).
  exists fbs. split; [|exact FB6].
  pose proof dcf_regs as (Rtp & Rsp & Rs1 & Rs7 & Rs8 & Rs9 & Rra).
  pose proof dcf_q as (Q1 & Q2). pose proof dcf_p2 as (P1 & P2). pose proof dcf_sp as (SP1 & SP2 & SP3).
  pose proof dcf_text as (T1 & Tapp & T2 & T3 & T4 & T4b & Z1 & Z2 & Z3 & Z4 & Z5). pose proof dcf_spanf as (S1 & S2 & S3 & _).
  pose proof dcf_rng as RNG. pose proof dcf_Fv8 as (F8 & _). pose proof dcf_p4 as (P4r & P4m).
  pose proof dcf_fs as (Fs1 & Fs2 & Fs3 & Fs4). pose proof dcf_rtf as RTF.
  pose proof (DCFS (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4) (getr (ms_regs ms) 5)
                 (getr (ms_regs ms) 6) (getr (ms_regs ms) 7) (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10)
                 (getr (ms_regs ms) 11) (getr (ms_regs ms) 12) (getr (ms_regs ms) 13) (getr (ms_regs ms) 14) (getr (ms_regs ms) 15)
                 (getr (ms_regs ms) 16) (getr (ms_regs ms) 17) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (getr (ms_regs ms) 28) (getr (ms_regs ms) 29) (getr (ms_regs ms) 30)
                 (getr (ms_regs ms) 31) (ms_fregs ms) (ms_fcsr ms) m0 v0 (Z_to_bv 64 (u 11 + 1)) (E 13%positive) (u 12) old
                 (E 25%positive) fptrv ibs fbs dg (u 1) (u 1 + u 2) (u 7) (u 8 - u 7) (u 7) (u 8 - u 7) se p2) as K.
  cbv zeta in K. cbn [rt_FS v0] in K. rewrite Rs7, Lib, Z2Nat.id in K by lia.
  unfold kms. rewrite Hpc, Hresv. apply K; clear K.
  all: rewrite ?Rsp.
  - exact Rtp.
  - exact Rs1.
  - rewrite Rs8. exact Q2.
  - exact Q1.
  - rewrite Rs9. exact P2.
  - exact P1.
  - exact dcf_win.
  - exact SP1.
  - lia.
  - exact SP2.
  - exact SP3.
  - exact (proj1 dcf_shz_sp).
  - exact DG.
  - exact (proj1 (proj2 dcf_shz_sp)).
  - exact OLD.
  - exact Lold.
  - clear -F8. Z.div_mod_to_equations; lia.
  - unfold Fv; lia.
  - unfold Fv; lia.
  - unfold Fv in *; lia.
  - exact dcf_shz_A.
  - exact dcf_rdbl_A.
  - (* [comment removed for export] *)
    pose proof dcf_spans_bytes as X. split.
    + split; [cbn [cells_wf cell_wf]; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold fptrv. rewrite FB6.
      replace (Z_to_bv 64 (u 26)) with (E 26%positive) by (symmetry; apply Z_to_bv_bv_unsigned).
      destruct frac; [exact X|]. apply (bytes_at_ext BSEGS _ _ _ _ X). reflexivity.
    + cbn [cells_size csize]. change (Z.of_nat (8 + (8 + (8 + (8 + 0))))) with 32.
      pose proof (wr_at_of_rg BSEGS E _ _ _ _ R38 ltac:(left; reflexivity) ltac:(cbn [rg_base track RGz]; exact (proj1 dcf_sp104))
                   ltac:(unfold rsz; cbn [rg_size track RGz]; reflexivity)) as (W1 & W2 & W).
      change (bv_unsigned (lden E (lconst 32))) with 32 in W2, W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - exact (proj2 (proj2 dcf_shz_sp)).
  - exact IBS.
  - lia.
  - pose proof (Bnd 25); unfold two64 in *; lia.
  - lia.
  - exact FBS.
  - exact FB1.
  - exact FB2.
  - exact FB3.
  - eapply app2r_sub; [exact Tapp | lia | lia].
  - lia.
  - lia.
  - exact FB4.
  - destruct T4 as [T4|T4]; [right | left]; unfold Fv, FSv in *; lia.
  - lia.
  - exact dcf_cshz.
  - split; [lia|]. apply Z.div_le_lower_bound; lia.
  - lia.
  - exact FB5.
  - exact (proj1 dcf_pristine).
  - exact (proj1 (proj2 dcf_pristine)).
  - exact (proj2 (proj2 dcf_pristine)).
  - exact dcf_RT.
  - unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. destruct RTF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & W3).
    clear -W1 W2 W3. repeat split; lia.
  - unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. destruct RTF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & _).
    assert (RA : FSv <= Fv /\ Fv + 536 <= FSv + 11571200) by (clear -RNG; unfold Fv in *; lia).
    unfold FSv in RA, O1, O2, O3. clear -RA O1 O2 O3. repeat split; lia.
  - unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. destruct RTF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & _).
    unfold FSv in *. clear -O1 O2 O3. repeat split; lia.
  - exact (proj1 dcf_tabs).
  - exact (proj2 dcf_tabs).
  - exact dcf_rdbl_fs.
  - exact dcf_fk4.
  - lia.
  - rewrite u_Z_to_bv. pose proof (Bnd 11). unfold two64 in *. rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2 ^ 54); reflexivity].
    rewrite Zplus_mod, P4m. clear -P4r. Z.div_mod_to_equations. lia.
  - exact dcf_fk5.
  - exact Fs4.
  - exact dcf_rtx.
Qed.

(* [comment removed for export] *)
Definition WS : list nat := [2%nat; 4%nat; 6%nat; 7%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 15%nat; 16%nat; 17%nat; 18%nat; 37%nat].
Local Abbreviation WD := (dcf_W (u 4) (Fv + 32) FSv (u 12)).

#[using="Type"] Lemma rsz_nth_base : forall j Rj x, nth_error (DCF_RGS false frac) j = Some Rj ->
  ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj) ->
  ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj).
Proof. LiaFast.lf_pins LiaFast.u0. intros; assumption. Qed.

#[using="ms Hd"] Lemma dcf_HW : forall x,
  (forall j Rj, In j WS -> nth_error (DCF_RGS false frac) j = Some Rj ->
     ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj)) ->
  Frame.outside WD x.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  intros x H. pose proof dcf_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18).
  pose proof dcf_rng as RNG. pose proof dcf_Fv8 as (F8 & _). pose proof (Bnd 12) as B12.
  assert (E2 : Fv / 8 = FSv / 8 + 528896 + 128 * u 12) by (unfold Fv; unfold FSv in *; Z.div_mod_to_equations; lia).
  pose proof (H 2%nat _ ltac:(cbn; tauto) eq_refl) as N2. pose proof (H 4%nat _ ltac:(cbn; tauto) ltac:(destruct frac; reflexivity)) as N4.
  pose proof (H 6%nat _ ltac:(cbn; tauto) eq_refl) as N6. pose proof (H 7%nat _ ltac:(cbn; tauto) eq_refl) as N7.
  pose proof (H 9%nat _ ltac:(cbn; tauto) eq_refl) as N9. pose proof (H 10%nat _ ltac:(cbn; tauto) eq_refl) as N10.
  pose proof (H 11%nat _ ltac:(cbn; tauto) eq_refl) as N11. pose proof (H 12%nat _ ltac:(cbn; tauto) eq_refl) as N12.
  pose proof (H 13%nat _ ltac:(cbn; tauto) eq_refl) as N13. pose proof (H 15%nat _ ltac:(cbn; tauto) eq_refl) as N15.
  pose proof (H 16%nat _ ltac:(cbn; tauto) eq_refl) as N16. pose proof (H 17%nat _ ltac:(cbn; tauto) eq_refl) as N17.
  pose proof (H 18%nat _ ltac:(cbn; tauto) eq_refl) as N18. pose proof (H 37%nat _ ltac:(cbn; tauto) eq_refl) as N37. clear H.
  unfold rsz in N2, N4, N6, N7, N9, N10, N11, N12, N13, N15, N16, N17, N18, N37.
  cbn [rg_base rg_size track RGz] in N2, N4, N6, N7, N9, N10, N11, N12, N13, N15, N16, N17, N18, N37.
  rewrite V18 in N2. rewrite V1 in N4. rewrite V4 in N6. rewrite V7 in N7. rewrite V9 in N9. rewrite V10 in N10.
  rewrite V11 in N11. rewrite V12 in N12. rewrite V13 in N13. rewrite V5 in N15. rewrite V15 in N16. rewrite V16 in N17.
  rewrite V17 in N18.
  change (bv_unsigned (lden E (lconst NDC_NEED))) with 2768 in N2. change (bv_unsigned (lden E (lconst 984))) with 984 in N4.
  change (bv_unsigned (lden E (lconst 8))) with 8 in N6, N15, N37. change (bv_unsigned (lden E (lconst 512))) with 512 in N16.
  change (bv_unsigned (lden E (lconst (2 ^ 20)))) with 1048576 in N17. change (bv_unsigned (lden E (lconst (2 ^ 17)))) with 131072 in N18.
  assert (U7 : bv_unsigned (lden E P4) = u 12) by (unfold P4; rewrite lden_lvar; reflexivity).
  assert (U9 : bv_unsigned (lden E (laddc (lscale (-1) P4) 1023)) = 1023 - u 12)
    by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
  assert (U10 : bv_unsigned (lden E (lscale 1024 P4)) = 1024 * u 12)
    by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
  assert (U11 : bv_unsigned (lden E (laddc (lscale (-1024) P4) (1024 * 1023))) = 1024 * (1023 - u 12))
    by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
  assert (U12 : bv_unsigned (lden E (lscale 128 P4)) = 128 * u 12)
    by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
  assert (U13 : bv_unsigned (lden E (laddc (lscale (-128) P4) (128 * 1023))) = 128 * (1023 - u 12))
    by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
  rewrite U7 in N7. rewrite U9 in N9. rewrite U10 in N10. rewrite U11 in N11. rewrite U12 in N12. rewrite U13 in N13.
  pose proof (proj2 dcf_sp104) as SP37.
  rewrite SP37 in N37.
  unfold dcf_W. cbn [Frame.outside].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ I)))))))))).
  - clear -N2. lia.
  - clear -N4. lia.
  - clear -N37. lia.
  - clear -N6 N15. lia.
  - clear -N7. lia.
  - clear -N9 N16 B12 RNG. lia.
  - clear -N10. lia.
  - clear -N11 N17. unfold Fv in *. lia.
  - clear -N12. lia.
  - rewrite E2 in N13. clear -N13 N18. lia.
Qed.




Definition Eq (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h4' h5' : word) : valu :=
  upds E [(229%positive, h4'); (230%positive, h5'); (241%positive, ra); (245%positive, t0); (246%positive, t1); (247%positive, t2);
          (250%positive, a0); (251%positive, a1); (252%positive, a2); (253%positive, a3); (254%positive, a4); (255%positive, a5);
          (256%positive, a6); (257%positive, a7); (268%positive, t3); (269%positive, t4); (270%positive, t5); (271%positive, t6)].
#[using="Type"] Lemma Eq_agree : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h4' h5',
  agree 200 E (Eq ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h4' h5').
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.

(* [comment removed for export] *)
#[using="Hd"] Lemma dcf_UW : forall m' (MU : munch WD m0 m') i R R', nth_error (DCF_RGS false frac) i = Some R ->
  rg_base R' = rg_base R -> rg_size R' = rg_size R -> ~ In i WS -> rg_ok BSEGS E m0 R' -> rg_ok BSEGS E m' R'.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  intros m' MU i R R' Hi Hb Hs Hni HR0. apply (rg_ok_munch BSEGS E m0 m' R' WD HR0 MU). intros k Hk.
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & HD & _). cbn [s_rgs DCF_P0] in HD.
  unfold rsz in Hk. rewrite Hs in Hk. rewrite Hb.
  apply dcf_HW. intros j Rj Hj HRj.
  assert (Hij : i <> j) by (intros ->; exact (Hni Hj)).
  pose proof (rgs_disj_nth E _ i j _ _ HD Hij Hi HRj) as D. unfold rg_disj, rsz in D |- *. lia.
Qed.



Ltac agE AG := eapply (rg_ok_agree BSEGS 200 _ _ _ _); [vm_compute; reflexivity | exact AG | ].
#[using="Hd DCFS"] Lemma dcf_run : exists ms' E', isteps BSEGS ms ms' /\ sden BSEGS E' (with_pc (DCF_Q frac) 0x94404) ms' /\
  agree (s_next (DCF_P0 frac)) E E' /\ (forall x, fr_pt E (s_rgs (DCF_P0 frac)) x -> ms_mem ms' x = ms_mem ms x).
Proof. LiaFast.lf_pins (fun (Hd DCFS : LiaFast.U) => LiaFast.u0).
  destruct dcf_kit as (fbs & K & FB6).
  pose proof dcf_regs as (Rtp & Rsp & Rs1 & Rs7 & Rs8 & Rs9 & Rra).
  pose proof dcf_rng as RNG. pose proof dcf_vals as VV. pose proof dcf_q as (Q1 & Q2).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv DCF_P0] in Hpc, Hresv, HR, HG, HD, HF.
  destruct (kit_run BSEGS _ ms Hsvc K) as (ms1 & ms2 & Hst & Heq & Hpost). clear K.
  destruct Hpost as (ra' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & h4' & h5' &
                     Hms2 & MU & WM & ST1 & ST2 & STA & PR & RTm & FK4 & FK5).
  subst ms2. rewrite Rsp in MU, ST1, ST2. cbn [rt_FS v0] in FK4, FK5, MU.
  assert (Hmem : ms_mem ms1 = m') by (destruct Heq as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  set (E' := Eq ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 h4' h5').
  assert (AG : agree 200 E E') by apply Eq_agree.
  assert (Hs8 : Z_to_bv 64 (se + 1) = lden E' (laddc (lvar 124) 1)).
  { assert (LB : lden E' (laddc (lvar 124) 1) = lden E (laddc (lvar 124) 1)) by (symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG]).
    rewrite LB. apply bv_eq. ubase_s.
    assert (X : u 124 = se mod two64) by (unfold u; rewrite Q2; apply u_Z_to_bv). rewrite X.
    rewrite Zplus_mod_idemp_r. f_equal. ring. }
  exists ms1, E'.
  split; [exact Hst|]. split; [|split].
  - eapply (sden_of_kit BSEGS _ _ ms1); [ | | exact Heq | | exact Hfrm | | | | ].
    + rewrite state_wf_with_pc. exact (proj1 (proj2 (DCF_wf frac))).
    + reflexivity.
    + reflexivity.
    + (* [comment removed for export] *)
      apply regs_ok_of_cases. intros n Hn. cbn [s_regs with_pc DCF_Q].
      do 32 (destruct n as [|n];
               [ getr_mkR_norm; rget_norm;
                 first [ reflexivity
                       | (rewrite (HR _); rget_norm; symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG])
                       | (symmetry; exact (lden_lvar E' _))
                       | exact Hs8 ]
               |]).
      lia.
    + (* [comment removed for export] *)
      cbn [s_rgs with_pc DCF_Q]. unfold DCF_RGS, fks5_whole, rt_rgs, rt_tp, rt_tp0, relro_rgs. cbn [app].
      assert (UWA : forall i R R', nth_error (DCF_RGS false frac) i = Some R -> rg_base R' = rg_base R -> rg_size R' = rg_size R ->
                      ~ In i WS -> rwf 200 R' = true -> rg_ok BSEGS E m0 R' -> rg_ok BSEGS E' m' R').
      { intros i R R' Hi Hb Hs Hni Hw HR0. apply (rg_ok_agree BSEGS 200 E _ _ R' Hw AG).
        exact (dcf_UW m' MU i R R' Hi Hb Hs Hni HR0). }
      pose proof HG as HG'. unfold DCF_RGS, fks5_whole, rt_rgs, rt_tp, rt_tp0, relro_rgs in HG'. cbn [app] in HG'.
      apply Forall_cons_iff in HG' as [R0 HG']; apply Forall_cons_iff in HG' as [R1 HG']; apply Forall_cons_iff in HG' as [R2 HG']; apply Forall_cons_iff in HG' as [R3 HG']; apply Forall_cons_iff in HG' as [R4 HG']; apply Forall_cons_iff in HG' as [R5 HG']; apply Forall_cons_iff in HG' as [R6 HG']; apply Forall_cons_iff in HG' as [R7 HG']; apply Forall_cons_iff in HG' as [R8 HG']; apply Forall_cons_iff in HG' as [R9 HG'];
      apply Forall_cons_iff in HG' as [R10 HG']; apply Forall_cons_iff in HG' as [R11 HG']; apply Forall_cons_iff in HG' as [R12 HG']; apply Forall_cons_iff in HG' as [R13 HG']; apply Forall_cons_iff in HG' as [R14 HG']; apply Forall_cons_iff in HG' as [R15 HG']; apply Forall_cons_iff in HG' as [R16 HG']; apply Forall_cons_iff in HG' as [R17 HG']; apply Forall_cons_iff in HG' as [R18 HG']; apply Forall_cons_iff in HG' as [R19 HG'];
      apply Forall_cons_iff in HG' as [R20 HG']; apply Forall_cons_iff in HG' as [R21 HG']; apply Forall_cons_iff in HG' as [R22 HG']; apply Forall_cons_iff in HG' as [R23 HG']; apply Forall_cons_iff in HG' as [R24 HG']; apply Forall_cons_iff in HG' as [R25 HG']; apply Forall_cons_iff in HG' as [R26 HG']; apply Forall_cons_iff in HG' as [R27 HG']; apply Forall_cons_iff in HG' as [R28 HG']; apply Forall_cons_iff in HG' as [R29 HG'];
      apply Forall_cons_iff in HG' as [R30 HG']; apply Forall_cons_iff in HG' as [R31 HG']; apply Forall_cons_iff in HG' as [R32 HG']; apply Forall_cons_iff in HG' as [R33 HG']; apply Forall_cons_iff in HG' as [R34 HG']; apply Forall_cons_iff in HG' as [R35 HG']; apply Forall_cons_iff in HG' as [R36 HG']; apply Forall_cons_iff in HG' as [R37 HG']; apply Forall_cons_iff in HG' as [R38 HG']; clear HG'.
      pose proof dcf_Fv8 as (F8 & _). pose proof (Bnd 12) as B12. pose proof dcf_fs as (Fs1 & Fs2 & Fs3 & Fs4).
      assert (E2 : Fv / 8 = FSv / 8 + 528896 + 128 * u 12) by (unfold Fv; unfold FSv in *; Z.div_mod_to_equations; lia).
      destruct VV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18).
      destruct FK4 as (K0 & K1 & K2 & K3 & K4 & K5 & K6). destruct FK5 as (J0 & J1 & J2 & J3 & J4).
      assert (U9 : bv_unsigned (lden E (laddc (lscale (-1) P4) 1023)) = 1023 - u 12)
        by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
      assert (U10 : bv_unsigned (lden E (lscale 1024 P4)) = 1024 * u 12)
        by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
      assert (U11 : bv_unsigned (lden E (laddc (lscale (-1024) P4) (1024 * 1023))) = 1024 * (1023 - u 12))
        by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
      assert (U12 : bv_unsigned (lden E (lscale 128 P4)) = 128 * u 12)
        by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
      assert (U13 : bv_unsigned (lden E (laddc (lscale (-128) P4) (128 * 1023))) = 128 * (1023 - u 12))
        by (unfold P4; ubase_s; rewrite Z.mod_small; [ring | unfold two64 in *; lia]).
      pose proof (proj2 dcf_sp104) as SP37.
      constructor. { apply (UWA 0%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R0]. }
      constructor. { apply (UWA 1%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R1]. }
      constructor. { (* [comment removed for export] *) agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (u 4 - 2768) (u 4)); [reflexivity | reflexivity | exact V18 | unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst NDC_NEED))) with 2768; lia | lia | exact ST1]. }
      constructor. { apply (UWA 3%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R3]. }
      constructor. { (* [comment removed for export] *) 
        agE AG. apply (rw_mix BSEGS E m0 m' _ WD (Fv + 32) (Fv + 536) R4 eq_refl eq_refl MU).
        { replace (Fv + 536) with (Fv + 32 + 504) by ring. exact STA. }
        intros i Hi. unfold rsz in Hi. cbn [rg_size track] in Hi. change (bv_unsigned (lden E (lconst 984))) with 984 in Hi.
        cbn [rg_base track]. rewrite V1. destruct (Z.ltb_spec i 504) as [Hl|Hl]; [left; lia | right].
        pose proof (app2r_lin _ _ Fs3) as (c & C1 & C2 & C3 & C4 & C5). pose proof dcf_sp as (S1 & S2 & S3).
        unfold dcf_W. cbn [Frame.outside]. unfold Fv in *. unfold FSv in *.
        clear -Hi Hl C1 C2 C3 C4 C5 RNG B12 S2 S3. repeat split; lia. }
      constructor. { eapply (UWA 5%nat); [reflexivity | reflexivity | reflexivity | cbn; intuition discriminate | vm_compute; reflexivity | exact (rg_ok_untrack BSEGS E _ _ _ _ _ _ R5)]. }
      constructor. { (* [comment removed for export] *) 
        apply (track_of_bytes_at BSEGS E' m' _ 0 _); [ | lia | unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E' (lconst 8))) with 8; cbn; lia | ].
        { agE AG. eapply (rg_ok_of_rw_cells BSEGS E m' _ (FSv + 32) [C8 h4']); [reflexivity | reflexivity | exact V4 | reflexivity | exact K1]. }
        cbn [rg_base RGz]. assert (LB : lden E' (fsc 32) = lden E (fsc 32)) by (symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG]).
        rewrite LB, V4, Z.add_0_r.
        unfold bv8. rewrite map_bden_bv8. rewrite lden_lvar. change (E' 229%positive) with h4'.
        destruct K1 as ((_ & B) & _). cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
      constructor. { (* [comment removed for export] *) 
        agE AG. eapply (rg_ok_rz_of BSEGS E m' _ (FSv + 34816) (u 12));
          [reflexivity | reflexivity | exact V7 | unfold rsz; cbn [rg_size]; unfold P4; rewrite lden_lvar; reflexivity | lia | unfold two64 in *; lia |].
        intros i Hi. destruct K2 as ((B1 & B2 & B) & (W1 & W2 & W)). rewrite upd_length, zeros_length in B2, W2, B, W. split.
        - pose proof (B (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia. rewrite X.
          rewrite nth_error_upd_other by lia. rewrite nth_error_zeros by lia. reflexivity.
        - exact (W i ltac:(lia)). }
      constructor. { apply (UWA 8%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R8]. }
      constructor. { (* [comment removed for export] *) 
        agE AG. eapply (rg_ok_rz_of BSEGS E m' _ (FSv + 34817 + u 12) (1023 - u 12));
          [reflexivity | reflexivity | exact V9 | unfold rsz; cbn [rg_size]; exact U9 | lia | unfold two64 in *; lia |].
        intros i Hi. destruct K2 as ((B1 & B2 & B) & (W1 & W2 & W)). rewrite upd_length, zeros_length in B2, W2, B, W. split.
        - pose proof (B (Z.to_nat (u 12 + 1 + i)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
          replace (FSv + 34816 + (u 12 + 1 + i)) with (FSv + 34817 + u 12 + i) in X by ring. rewrite X.
          rewrite nth_error_upd_other by lia. rewrite nth_error_zeros by lia. reflexivity.
        - pose proof (W (u 12 + 1 + i) ltac:(lia)) as X.
          replace (FSv + 34816 + (u 12 + 1 + i)) with (FSv + 34817 + u 12 + i) in X by ring. exact X. }
      constructor. { agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (FSv + 4231168) (FSv + 4231168 + u 12 * 1024)); [reflexivity | reflexivity | exact V10 |  unfold rsz; cbn [rg_size]; rewrite U10; lia | lia | exact K3 ]. }
      constructor. { agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (FSv + 4231168 + u 12 * 1024 + 1024) (FSv + 5279744)); [reflexivity | reflexivity | cbn [rg_base]; rewrite V11; unfold Fv; ring | | | exact K4 ]; unfold rsz; cbn [rg_size]; first [ rewrite U11; unfold Fv in *; lia | lia ]. }
      constructor. { agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (2147450880 + FSv / 8 + 528896) (2147450880 + FSv / 8 + 528896 + u 12 * 128)); [reflexivity | reflexivity | exact V12 |  unfold rsz; cbn [rg_size]; rewrite U12; lia | lia | exact K5 ]. }
      constructor. { agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (2147450880 + FSv / 8 + 528896 + u 12 * 128 + 128) (2147450880 + FSv / 8 + 659968)); [reflexivity | reflexivity | cbn [rg_base]; rewrite V13, E2; ring | | | exact K6 ]; unfold rsz; cbn [rg_size]; first [ rewrite U13; lia | lia ]. }
      constructor. { apply (UWA 14%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R14]. }
      constructor. { (* [comment removed for export] *) 
        apply (track_of_bytes_at BSEGS E' m' _ 0 _); [ | lia | unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E' (lconst 8))) with 8; cbn; lia | ].
        { agE AG. eapply (rg_ok_of_rw_cells BSEGS E m' _ (FSv + 40) [C8 h5']); [reflexivity | reflexivity | exact V5 | reflexivity | exact J1]. }
        cbn [rg_base RGz]. assert (LB : lden E' (fsc 40) = lden E (fsc 40)) by (symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG]).
        rewrite LB, V5, Z.add_0_r.
        unfold bv8. rewrite map_bden_bv8. rewrite lden_lvar. change (E' 230%positive) with h5'.
        destruct J1 as ((_ & B) & _). cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
      constructor. { (* [comment removed for export] *) 
        agE AG. eapply (rg_ok_rz_of BSEGS E m' _ (FSv + 35840) 512);
          [reflexivity | reflexivity | exact V15 | reflexivity | lia | unfold two64 in *; lia |].
        intros i Hi. destruct J2 as ((B1 & B2 & B) & (W1 & W2 & W)). rewrite zeros_length in B2, W2, B, W. split.
        - pose proof (B (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia. rewrite X. rewrite nth_error_zeros by lia. reflexivity.
        - exact (W i ltac:(lia)). }
      constructor. { agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (FSv + 5279744) (FSv + 6328320)); [reflexivity | reflexivity | exact V16 |  unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst (2 ^ 20)))) with 1048576; lia | lia | exact J3 ]. }
      constructor. { agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (2147450880 + FSv / 8 + 659968) (2147450880 + FSv / 8 + 791040)); [reflexivity | reflexivity | exact V17 |  unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst (2 ^ 17)))) with 131072; lia | lia | exact J4 ]. }
      constructor. { apply (UWA 19%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R19]. }
      constructor. { apply (UWA 20%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R20]. }
      constructor. { apply (UWA 21%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R21]. }
      constructor. { apply (UWA 22%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R22]. }
      constructor. { apply (UWA 23%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R23]. }
      constructor. { apply (UWA 24%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R24]. }
      constructor. { apply (UWA 25%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R25]. }
      constructor. { apply (UWA 26%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R26]. }
      constructor. { apply (UWA 27%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R27]. }
      constructor. { apply (UWA 28%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R28]. }
      constructor. { apply (UWA 29%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R29]. }
      constructor. { apply (UWA 30%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R30]. }
      constructor. { apply (UWA 31%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R31]. }
      constructor. { apply (UWA 32%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R32]. }
      constructor. { apply (UWA 33%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R33]. }
      constructor. { apply (UWA 34%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R34]. }
      constructor. { apply (UWA 35%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R35]. }
      constructor. { apply (UWA 36%nat _ _ eq_refl eq_refl eq_refl); [cbn; intuition discriminate | vm_compute; reflexivity | exact R36]. }
      constructor. { (* [comment removed for export] *) agE AG. eapply (rg_ok_of_stk BSEGS E m' _ (u 4 + 144) (u 4 + 152)); [reflexivity | reflexivity | exact SP37 | unfold rsz; cbn [rg_size RGz]; change (bv_unsigned (lden E (lconst 8))) with 8; lia | lia | exact ST2]. }
      constructor. { (* [comment removed for export] *)
        eapply (UWA 38%nat); [destruct frac; reflexivity | reflexivity | reflexivity | cbn; intuition discriminate | vm_compute; reflexivity | exact (rg_ok_untrack BSEGS E _ _ _ _ _ _ R38)]. }
      constructor.
    + (* [comment removed for export] *)
      apply (rgs_disj_shape E' (DCF_RGS false frac)); [apply shape_eqb_eq; exact (proj2 (proj2 (DCF_wf frac))) |].
      apply (rgs_disj_agree 200 E); [destruct frac; vm_compute; reflexivity | exact AG | exact HD].
    + (* [comment removed for export] *)
      cbn [s_facts with_pc DCF_Q].
      assert (Hw : forallb (fwf 200) (dcf_facts frac) = true) by (destruct frac; vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF |- *. intros f Hf.
      exact (fact_ok_agree 200 E _ f (Hw f Hf) AG (HF f Hf)).
  - exact AG.
  - (* [comment removed for export] *)
    intros x Hx. rewrite Hmem. apply MU. destruct Hx as [Hout|Hrt].
    + apply dcf_HW. intros j Rj Hj HRj. unfold FxStep.outside in Hout. rewrite Forall_forall in Hout.
      pose proof (Hout Rj (nth_error_In _ _ HRj)) as X. lia.
    + apply Exists_exists in Hrt as (R & HRin & Hrt & Hin).
      unfold DCF_RGS, fks5_whole, rt_rgs, rt_tp, rt_tp0, relro_rgs in HRin. cbn [app] in HRin.
      destruct HRin as [<-|HRin]; [|repeat (destruct HRin as [<-|HRin]; [try (destruct frac); cbn in Hrt; discriminate|]); destruct HRin].
      (* [comment removed for export] *)
      unfold FxStep.in_rg, rsz in Hin. cbn [rg_base rg_size] in Hin. unfold T, L in Hin. rewrite !lden_lvar in Hin.
      pose proof dcf_text as (T1 & Tapp & T2 & T3 & T4 & T4b & _). pose proof (app2r_lin _ _ (proj1 (proj2 (proj2 dcf_fs)))) as (c & C1 & C2 & C3 & C4 & C5).
      pose proof (app2r_lin _ _ Tapp) as (d & D1 & D2 & D3 & D4 & D5).
      pose proof dcf_sp as (S1 & S2 & S3).
      unfold dcf_W. cbn [Frame.outside]. unfold Fv in *. unfold FSv in *.
      clear -Hin T1 T2 T3 T4 T4b C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 RNG S2 S3. repeat split; lia.
Qed.

End Run.

End DCF.

(* [comment removed for export] *)
Theorem dcf_kfrag : dcf_d_stmt -> forall frac, kfrag_ok BSEGS (DCF_P0 frac) (DCF_Q frac) 0x94404.
Proof. intros DCFS frac E ms Hd. exact (dcf_run frac E ms Hd DCFS). Qed.
