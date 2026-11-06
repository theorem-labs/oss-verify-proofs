(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_app2 B_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.

Module B_sfree5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall l1 l2 : list byte,
  map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hb Hl. f_equal; [apply bv_eq; exact Hb | apply IH; exact Hl].
Qed.

Section Proof.
  Hypothesis M2S : m2s_stmt 0x4b690.

  #[using="M2S"] Lemma sfree5_spec : sfree5_stmt.
  Proof. LiaFast.lf_pins (fun (M2S : LiaFast.U) => LiaFast.u0).
    unfold sfree5_stmt.
    intros until junk'.
    intros RTH FRM PRE FLAG SH AL K1 K2 I1 I2 ST SP1 SP2 SP3 SEPF SEPL PRG PRD RDJ1 RDJ2 RA.
    unfold sfree5_post, sfree5_W.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
      pose proof (munch_refl [(bv_unsigned sp - SFREE_NEED, bv_unsigned sp); (fladdr, fladdr + 1);
                              (ASAN_B + bv_unsigned a0 / 8, ASAN_B + bv_unsigned a0 / 8 + 256)]%Z m0) as MU;
      pose proof (wmono_refl BSEGS m0) as WM
    end.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof RTH as RTH0. open_RT RTH0.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    clear RT2 RT2b RT3 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb RTH.
    unfold rt_disj in RDJ1, RDJ2.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FRM. destruct FRM as [FRMpre LAST].
    rewrite PRE in LAST. change (Z.of_nat 2040) with 2040%Z in LAST.
    clear FRMpre.
    carve_frame 16%nat ST.
    do 3 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply M2S | post_call BSEGS mc ] end.
    1:{ split; assumption. }
    1:{ assumption. }
    1:{ lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    step. step. (* [comment removed for export] *)
    do 32 step. (* [comment removed for export] *)
    do 3 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | H : rw_cells BSEGS mc (ASAN_B + bv_unsigned a0 / 8)%Z ?cs |- _ =>
          pose proof (rw_cells_merge BSEGS mc (ASAN_B + bv_unsigned a0 / 8)%Z [] cs [] ltac:(rewrite app_nil_r; cbn [app]; exact H)) as SHADOW;
          clear H; cbn [app cells_size csize Nat.add] in SHADOW;
          replace (cells_bytes cs) with (repeat (Z_to_bv 8 245) 256) in SHADOW by (apply bytes_eq_of_unsigned; vm_compute; reflexivity)
      end end.
    finish.
    all: try (match goal with H : rw_cells _ ?mc ?A [C1 ?b] |- rw_cells _ ?mc ?A [C1 (Z_to_bv 8 0)] =>
          replace (Z_to_bv 8 0) with b by (apply bv_eq; vm_compute; reflexivity); exact H end).
  Qed.
End Proof.
End B_sfree5.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_app2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.KX.KxSF5B.B_sfree5.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac KxRtB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition RGS0 : list region :=
  [ RG SWB SWS RW TEmpty;
    RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW (put_bytes TEmpty 2040 (bv8 FLB5));
    track (RG (ladd (fsc FL5) P5) (lconst 1) RZ TEmpty) 0 [BK 1];
    RG (ladd (fsh AR5) (lscale 256 P5)) (lconst 256) RW TEmpty;
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;
    sb_uar_t ] ++ rt_rgs_t ++ relro_rgs.
Lemma RGS0_eq : SF5_RGS false = RGS0. Proof. reflexivity. Qed.
Definition RGS1 : list region :=
  [ RG SWB SWS RW TEmpty;
    RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW TEmpty;
    track (RG (ladd (fsc FL5) P5) (lconst 1) RZ TEmpty) 0 [BK 0];
    track (RG (ladd (fsh AR5) (lscale 256 P5)) (lconst 256) RW TEmpty) 0 (List.repeat (BK 245) 256);
    RGz (lconst 0x10000) 0x2e000 RO TEmpty;
    sb_uar_t ] ++ rt_rgs_t ++ relro_rgs.
Lemma RGS1_eq : SF5_RGS true = RGS1. Proof. reflexivity. Qed.

Section SF5.
Variable E : valu.
Variable ms : machine_state.
Hypothesis Hd : sden BSEGS E SF5_P0 ms.

Local Abbreviation ra := (bv_unsigned (E 5%positive)).
Local Abbreviation sp := (bv_unsigned (E 4%positive)).
Local Abbreviation fsp := (bv_unsigned (E 10%positive)).
Local Abbreviation h5 := (bv_unsigned (E 13%positive)).
Local Abbreviation p5 := (bv_unsigned (E 14%positive)).
Local Abbreviation ctx := (bv_unsigned (E 15%positive)).
Local Abbreviation thr := (bv_unsigned (E 16%positive)).
Local Abbreviation blk := (bv_unsigned (E 17%positive)).
Local Abbreviation beg := (bv_unsigned (E 18%positive)).
Local Abbreviation tlsb := (bv_unsigned (E 19%positive)).
Local Abbreviation tlse := (bv_unsigned (E 20%positive)).
Local Abbreviation fbv := (bv_unsigned (E 21%positive)).
Local Abbreviation swb := (bv_unsigned (E 23%positive)).
Local Abbreviation sws := (bv_unsigned (E 24%positive)).
Local Abbreviation F := (4096 * fsp + 5279744 + p5 * 2048).
Local Abbreviation FLA := (4096 * fsp + 35840 + p5).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

(* [comment removed for export] *)
Ltac open_facts :=
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _); cbn [s_facts SF5_P0] in HF;
  unfold SF5_F, fks5_facts, rt_facts, two_class, two_class4k, stack_facts in HF; cbn [app] in HF;
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

#[using="ms Hd"] Lemma sf5_facts :
  ra mod 2 = 0 /\ 0 <= p5 <= 511 /\ h5 mod 512 = p5 /\
  6537216 <= 4096 * fsp <= 2 ^ 47 - 11571200 /\
  6537216 <= ctx <= 2 ^ 47 - 160 /\ 4096 <= thr <= 2 ^ 47 - 80 /\ 4096 <= blk <= 2 ^ 47 - 32 /\
  1 <= beg <= 2 ^ 64 - 1 /\ 1 <= fbv <= 255 /\
  (ctx + 160 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= ctx) /\
  (thr + 80 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= thr) /\
  (blk + 32 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= blk) /\
  17594333495296 <= sp - 16 /\ sp <= 2 ^ 47 /\ sp mod 16 = 0 /\
  16 <= sp - swb <= 2 ^ 30 /\ 0 <= swb + sws - sp <= 2 ^ 30 /\
  0 <= sp - 16 - 4096 * fsp - 11571200 <= 2 ^ 47 /\
  app2r (4096 * fsp) (4096 * fsp + 11571200) /\ rt_app ctx 160 /\ rt_app thr 80 /\ rt_app blk 32.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts.
  pose proof (Bnd 4%positive) as B4. pose proof (Bnd 10%positive) as B10. pose proof (Bnd 13%positive) as B11.
  pose proof (Bnd 14%positive) as B12. pose proof (Bnd 15%positive) as B15. pose proof (Bnd 16%positive) as B16.
  pose proof (Bnd 17%positive) as B17. pose proof (Bnd 23%positive) as B23. pose proof (Bnd 24%positive) as B24.
  assert (X : 6537216 <= 4096 * fsp <= 2 ^ 47 - 11571200)
    by (clear -F2; change (6537216 / 4096) with 1596 in F2; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F2; lia).
  change (2 ^ 1) with 2 in F. change (2 ^ 9) with 512 in F1. change (2 ^ 4) with 16 in F19.
  refine (conj F (conj F0 (conj _ (conj X (conj F4 (conj F6 (conj F8 (conj F10 (conj F11 (conj _ (conj _ (conj _ (conj _ (conj _ (conj F19 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))))))).
  - clear -F1 B11 B12 F0. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F15 B10 B15 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F16 B10 B16 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F17 B10 B17 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F18 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F18 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs SF5_P0] in HG. rewrite RGS0_eq in HG. unfold RGS0 in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F18 F20 F21 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs SF5_P0] in HG. rewrite RGS0_eq in HG. unfold RGS0 in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F18 F20 F21 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F22 B4 B10 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - apply (proj2 (rt_app_of_wrapped (4096 * fsp) 11571200 ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(replace (-17594333495296 + (1 * (4096 * fsp) + 0)) with (-17594333495296 + (4096 * fsp + 0)) by ring; exact F3))).
  - exact (proj1 (rt_app_of_wrapped ctx 160 ltac:(lia) ltac:(lia) ltac:(lia) F5)).
  - exact ((rt_app_of_wrapped4k thr 80 ltac:(lia) ltac:(lia) ltac:(lia) F7)).
  - exact ((rt_app_of_wrapped4k blk 32 ltac:(lia) ltac:(lia) ltac:(lia) F9)).
Qed.

Definition v0 : rt_vals := RTV (4096 * fsp) ctx thr tlsb tlse blk beg.

Ltac rget_norm_in H := repeat match type of H with context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v in H end.

(* [comment removed for export] *)
Ltac open_sf5 :=
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm);
  cbn [s_pc s_regs s_rgs s_facts s_resv SF5_P0] in Hpc, Hresv, HR, HG, HD, HF; rewrite RGS0_eq in HG, HD;
  pose proof sf5_facts as FCT;
  pose proof (Bnd 5%positive) as Bra; pose proof (Bnd 4%positive) as Bsp; pose proof (Bnd 10%positive) as Bfsp;
  pose proof (Bnd 13%positive) as Bh5; pose proof (Bnd 14%positive) as Bp5; pose proof (Bnd 15%positive) as Bctx;
  pose proof (Bnd 16%positive) as Bthr; pose proof (Bnd 17%positive) as Bblk; pose proof (Bnd 18%positive) as Bbeg;
  pose proof (Bnd 23%positive) as Bswb; pose proof (Bnd 24%positive) as Bsws;
  unfold RGS0, rt_rgs_t, relro_rgs in HG; cbn [app] in HG;
  apply Forall_cons_iff in HG as [G0 HG]; apply Forall_cons_iff in HG as [G1 HG]; apply Forall_cons_iff in HG as [G2 HG];
  apply Forall_cons_iff in HG as [G3 HG]; apply Forall_cons_iff in HG as [G4 HG]; apply Forall_cons_iff in HG as [G5 HG];
  apply Forall_cons_iff in HG as [G6 HG]; apply Forall_cons_iff in HG as [G7 HG]; apply Forall_cons_iff in HG as [G8 HG];
  apply Forall_cons_iff in HG as [G9 HG]; apply Forall_cons_iff in HG as [G10 HG]; apply Forall_cons_iff in HG as [G11 HG];
  apply Forall_cons_iff in HG as [G12 HG]; apply Forall_cons_iff in HG as [G13 HG]; apply Forall_cons_iff in HG as [G14 HG];
  apply Forall_cons_iff in HG as [G15 HG]; apply Forall_cons_iff in HG as [G16 HG]; apply Forall_cons_iff in HG as [G17 HG];
  apply Forall_cons_iff in HG as [G18 HG].

(* [comment removed for export] *)
Ltac ubase := lnorm; rewrite u_Z_to_bv; unfold vz; rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l.

#[using="ms Hd"] Lemma sf5_win : 16 <= sp - swb <= 2 ^ 30 /\ 0 <= swb + sws - sp <= 2 ^ 30.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sf5_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & _). exact (conj W1 W2).
Qed.

#[using="E Hd"] Lemma sf5_tp : getr (ms_regs ms) 4 = Z_to_bv 64 6395968.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0). open_sf5. pose proof (HR 4%bv) as X. rget_norm_in X. rewrite X. reflexivity. Qed.
#[using="Hd"] Lemma sf5_sp : getr (ms_regs ms) 2 = E 4%positive.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0). open_sf5. pose proof (HR 2%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar. Qed.
#[using="Hd"] Lemma sf5_ra : getr (ms_regs ms) 1 = E 5%positive.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0). open_sf5. pose proof (HR 1%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar. Qed.

(* [comment removed for export] *)
#[using="ms Hd"] Lemma sf5_vals :
  bv_unsigned (lden E (ladd (fsc FL5) P5)) = FLA /\
  bv_unsigned (lden E (ladd (fsc AR5) (lscale 2048 P5))) = F /\
  bv_unsigned (lden E (ladd (fsh AR5) (lscale 256 P5))) = 2147450880 + F / 8.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sf5_facts as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf. pose proof (Bnd 10%positive). pose proof (Bnd 14%positive).
  replace (4096 * fsp + 5279744 + p5 * 2048) with ((512 * fsp + 659968 + p5 * 256) * 8) by ring. rewrite Z.div_mul by discriminate.
  split; [|split]; ubase; rewrite Z.mod_small; try ring; clear -Hf Hp; unfold two64 in *; lia.
Qed.

#[using="Hd"] Lemma sf5_a0 : bv_unsigned (getr (ms_regs ms) 10) = F.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. pose proof (HR 10%bv) as X. rget_norm_in X. rewrite X. unfold SLOT5. exact (proj1 (proj2 sf5_vals)).
Qed.

(* [comment removed for export] *)
Ltac const_cells G o :=
  let X := fresh "X" in
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ o _ G ltac:(clear; lia) ltac:(cbn; clear; lia)) as X;
  cbn [rg_base RGz track] in X; change (bv_unsigned (lden E (lconst ?z))) with (z mod two64) in X;
  rewrite Z.mod_small in X by (unfold two64; clear; lia);
  apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].

#[using="Hd"] Lemma sf5_RT : RT (ms_mem ms) v0.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. unfold RT. cbn [rt_FS rt_ctx rt_thr rt_tlsb rt_tlse rt_blk rt_beg v0].
  destruct FCT as (_ & _ & _ & Hf & Hc & Ht & Hb & Hg & Hfb & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fapp & Capp & Tapp & Bapp). unfold KHI, KTOP in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  - unfold sb_uar_t in G5. const_cells G5 0.
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 0 [BK 1] G6 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base] in Y. change (bv_unsigned (lden E (lconst 941792))) with 941792 in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 4 (bkn 4 0) G6 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base] in Y. change (bv_unsigned (lden E (lconst 941792))) with 941792 in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - const_cells G7 0.
  - const_cells G8 0.
  - exists (Z_to_bv 8 fbv). split.
    + pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 0 _ G10 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 1540657))) with 1540657 in X. rewrite Z.add_0_r in X.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. cbn [List.map bden] in X. lnorm_in X. rewrite Z.shiftr_0_r in X. exact X.
    + rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by (clear -Hfb; lia). clear -Hfb; lia.
  - const_cells G9 0.
  - const_cells G11 0.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 0 (bk8 6396000) G12 ltac:(clear; lia) ltac:(cbn; clear; lia)
                    ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X. rewrite Z.add_0_r in X.
      apply (bytes_at_ext BSEGS _ _ _ _ X). apply bytes_eqb_eq. vm_compute. reflexivity.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 8 FS G12 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
      lnorm_in X. rewrite Z.add_0_l, Z.add_0_r in X. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 16 BLK G12 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 48 (bk8 6398016) G12 ltac:(clear; lia) ltac:(cbn; clear; lia)
                  ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 CTX G13 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6532072))) with 6532072 in X.
    lnorm_in X. rewrite ?Z.add_0_r in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 THR G14 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. rewrite (u_ctx152 E ltac:(clear -Hc; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 TLSB G15 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. rewrite (u_thr48 E ltac:(clear -Ht; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 8 TLSE G15 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. rewrite (u_thr48 E ltac:(clear -Ht; lia)) in X. lnorm_in X. rewrite !Z_to_bv_bv_unsigned, length_le8.
      replace (thr + 48 + Z.of_nat 8) with (thr + 48 + 8) by lia. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 BEG G16 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. rewrite (u_blk24 E ltac:(clear -Hb; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fapp (conj _ (conj _ (conj Capp (conj _ (conj Tapp (conj _ (conj Bapp _))))))))))))).
    all: clear -Hf Hc Ht Hb Hg; unfold two64 in *; lia.
Qed.

#[using="Hd"] Lemma sf5_stk : stk BSEGS (ms_mem ms) (sp - 16) sp.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. pose proof sf5_win as (W1 & W2).
  assert (S0 : stk BSEGS (ms_mem ms) swb (swb + sws)).
  { apply (stk_of_rg BSEGS E _ _ _ _ G0 ltac:(left; reflexivity)); cbn [rg_base]; [lnorm; reflexivity|].
    unfold rsz. cbn [rg_size]. lnorm. ring. }
  destruct (stk_split BSEGS _ _ (sp - 16) _ S0 ltac:(clear -W1 W2; lia)) as (_ & S1).
  destruct (stk_split BSEGS _ _ sp _ S1 ltac:(clear -W1 W2; lia)) as (S2 & _). exact S2.
Qed.

#[using="E Hd"] Lemma sf5_pr1 : pristine (ms_mem ms) 892928 917504.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. exact (pristine_of_rg_ro BSEGS E _ _ 892928 24576 G17 eq_refl eq_refl eq_refl).
Qed.
#[using="E Hd"] Lemma sf5_pr3 : pristine (ms_mem ms) 65536 253952.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. exact (pristine_of_rg_ro BSEGS E _ _ 65536 188416 G4 eq_refl eq_refl eq_refl).
Qed.

#[using="ms Hd"] Lemma sf5_rtd1 : rt_disj v0 (sp - 16) sp.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [s_facts SF5_P0] in HF.
  assert (HO : Forall (fact_ok E) (rt_out 16)).
  { rewrite Forall_forall in HF |- *. intros f Hf. apply HF. unfold SF5_F. apply in_cons. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hf. }
  destruct (rt_out_ok E 16 ltac:(lia) HO) as (O1 & O2 & O3).
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -O1 O2 O3. repeat split; lia.
Qed.

#[using="ms Hd"] Lemma sf5_rtd2 : rt_disj v0 FLA (FLA + 1).
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof sf5_facts as (_ & Hp & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & C3 & _).
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -C1 C2 C3 Hp. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="Hd"] Lemma sf5_frame : exists junk : list byte,
  rw_cells BSEGS (ms_mem ms) F ([CB 2040 junk] ++ [C8 (Z_to_bv 64 FLA)]) /\ cells_size [CB 2040 junk] = 2040%nat.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. pose proof sf5_vals as (V1 & V5 & V6). destruct FCT as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf.
  assert (G1t : rg_ok BSEGS E (ms_mem ms) (track (RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW TEmpty) 2040 (bv8 FLB5)))
    by exact G1.
  pose proof (rg_ok_untrack BSEGS E _ _ _ _ _ _ G1t) as G1u.
  destruct (bytes_exist BSEGS (ms_mem ms) F 2040 ltac:(clear -Hf Hp; lia) ltac:(clear -Hf Hp; unfold two64 in *; lia)) as (junk & J & Lj).
  { intros i Hi. rewrite <- rd1_mrd.
    pose proof (rd_of_rg BSEGS E _ _ (Z.of_nat i) G1u ltac:(unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E (lconst 2048))) with 2048; lia)
                  ltac:(discriminate)) as X.
    cbn [rg_base] in X. rewrite V5 in X. exact X. }
  exists junk. split; [|reflexivity].
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 2040 _ G1t ltac:(clear; lia) ltac:(cbn; clear; lia)) as T.
  cbn [rg_base track] in T. rewrite V5 in T. unfold bv8 in T. rewrite map_bden_bv8 in T.
  replace (lden E FLB5) with (Z_to_bv 64 FLA) in T by (unfold FLB5; lnorm; f_equal; unfold vz; ring).
  pose proof (wr_at_of_rg BSEGS E _ _ _ _ G1u ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact V5)
                ltac:(unfold rsz; cbn [rg_size]; reflexivity)) as (W1 & W2 & W).
  change (bv_unsigned (lden E (lconst 2048))) with 2048 in W2, W.
  split.
  - split; [cbn [cells_wf cell_wf]; split; [exact Lj | exact (conj I I)]|].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact J|].
    rewrite Lj. change (Z.of_nat 2040) with 2040. exact T.
  - cbn [cells_size csize app]. change (Z.of_nat (2040 + (8 + 0))) with 2048. split; [lia|]. split; [lia|]. exact W.
Qed.

#[using="Hd"] Lemma sf5_flag : rw_cells BSEGS (ms_mem ms) FLA [C1 (Z_to_bv 8 1)].
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. pose proof sf5_vals as (V1 & V5 & V6).
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 0 _ G2 ltac:(clear; lia) ltac:(cbn; clear; lia)) as T.
  cbn [rg_base track] in T. rewrite V1, Z.add_0_r in T.
  pose proof (wr_at_of_rg BSEGS E _ _ _ _ G2 ltac:(right; left; reflexivity) ltac:(cbn [rg_base track]; exact V1)
                ltac:(unfold rsz; cbn [rg_size track]; reflexivity)) as (W1 & W2 & W).
  change (bv_unsigned (lden E (lconst 1))) with 1 in W2, W.
  split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes app List.map bden] in T |- *. exact T.
  - cbn [cells_size csize]. change (Z.of_nat (1 + 0)) with 1. split; [lia|]. split; [lia|]. exact W.
Qed.

#[using="Hd"] Lemma sf5_shadow : exists junk : list byte, rw_cells BSEGS (ms_mem ms) (2147450880 + F / 8) [CB 256 junk].
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_sf5. pose proof sf5_vals as (V1 & V5 & V6). destruct FCT as (_ & Hp & _ & Hf & _). unfold KHI, KTOP in Hf.
  assert (E8 : F / 8 = 512 * fsp + 659968 + p5 * 256)
    by (replace (4096 * fsp + 5279744 + p5 * 2048) with ((512 * fsp + 659968 + p5 * 256) * 8) by ring; rewrite Z.div_mul by discriminate; reflexivity).
  destruct (bytes_exist BSEGS (ms_mem ms) (2147450880 + F / 8) 256 ltac:(clear -Hf Hp E8; lia) ltac:(clear -Hf Hp E8; unfold two64 in *; lia)) as (junk & J & Lj).
  { intros i Hi. rewrite <- rd1_mrd.
    pose proof (rd_of_rg BSEGS E _ _ (Z.of_nat i) G3 ltac:(unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E (lconst 256))) with 256; lia)
                  ltac:(discriminate)) as X.
    cbn [rg_base] in X. rewrite V6 in X. exact X. }
  exists junk.
  pose proof (wr_at_of_rg BSEGS E _ _ _ _ G3 ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact V6)
                ltac:(unfold rsz; cbn [rg_size]; reflexivity)) as (W1 & W2 & W).
  change (bv_unsigned (lden E (lconst 256))) with 256 in W2, W.
  split.
  - split; [cbn [cells_wf cell_wf]; split; [exact Lj | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact J.
  - cbn [cells_size csize]. change (Z.of_nat (256 + 0)) with 256. split; [lia|]. split; [lia|]. exact W.
Qed.

Ltac rget_norm := repeat match goal with |- context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v end.

Ltac getr_mkR_norm := rewrite getr_mkR;
  match goal with |- context [Z.to_nat (bv_unsigned ?r)] =>
    let v := eval vm_compute in (Z.to_nat (bv_unsigned r)) in change (Z.to_nat (bv_unsigned r)) with v end; cbn beta iota.

Definition Eq (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : valu :=
  upds E [(205%positive, t0); (206%positive, t1); (207%positive, t2); (210%positive, a0); (211%positive, a1); (212%positive, a2);
          (213%positive, a3); (214%positive, a4); (215%positive, a5); (216%positive, a6); (217%positive, a7); (228%positive, t3);
          (229%positive, t4); (230%positive, t5); (231%positive, t6)].

#[using="Type"] Lemma Eq_agree : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, agree 200 E (Eq t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.

#[using="ms Hd"] Lemma sf5_HW : forall x,
  (forall j Rj, In j [0%nat; 2%nat; 3%nat] -> nth_error RGS0 j = Some Rj ->
     ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj)) ->
  Frame.outside [(sp - 16, sp); (FLA, FLA + 1); (2147450880 + F / 8, 2147450880 + F / 8 + 256)] x.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  intros x H. pose proof sf5_win as (W1 & W2). pose proof sf5_vals as (V1 & V5 & V6).
  pose proof (H 0%nat _ ltac:(cbn; tauto) eq_refl) as N0. pose proof (H 2%nat _ ltac:(cbn; tauto) eq_refl) as N2.
  pose proof (H 3%nat _ ltac:(cbn; tauto) eq_refl) as N3. clear H.
  unfold rsz in N0, N2, N3. cbn [rg_base rg_size track RGz] in N0, N2, N3.
  rewrite V1 in N2. rewrite V6 in N3.
  lnorm_in N0. change (bv_unsigned (lden E (lconst 1))) with 1 in N2. change (bv_unsigned (lden E (lconst 256))) with 256 in N3.
  cbn [Frame.outside]. clear -N0 N2 N3 W1 W2. repeat split; lia.
Qed.

#[using="Hd"] Lemma sf5_run : exists ms' E', isteps BSEGS ms ms' /\
  sden BSEGS E' (with_pc SF5_Q (bv_unsigned (lden E (rget (s_regs SF5_P0) ra_key)))) ms' /\
  agree (s_next SF5_P0) E E' /\ (forall x, fr_pt E (s_rgs SF5_P0) x -> ms_mem ms' x = ms_mem ms x) /\ fpeq ms ms'.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv SF5_P0] in Hpc, Hresv, HR, HG, HD, HF. rewrite RGS0_eq in HG, HD. unfold rsv_ok in Hresv.
  pose proof sf5_facts as FCT. pose proof sf5_win as (W1 & W2). pose proof (Bnd 4%positive) as Bsp.
  pose proof (Bnd 10%positive) as Bfsp. pose proof (Bnd 13%positive) as Bh5. pose proof (Bnd 14%positive) as Bp5.
  destruct FCT as (Fra & Fp5 & _ & Ffsp & _ & _ & _ & _ & _ & _ & _ & _ & Fsp & FspK & Fsp16 & _ & _ & C18 & Fapp & _). unfold KHI, KTOP in Ffsp.
  pose proof (sfree5_spec m2s_spec) as SF. unfold sfree5_stmt in SF.
  destruct sf5_frame as (junk & FRM & PRE). destruct sf5_shadow as (junk' & SHD).
  specialize (SF (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4) (getr (ms_regs ms) 5)
                 (getr (ms_regs ms) 6) (getr (ms_regs ms) 7) (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10)
                 (getr (ms_regs ms) 11) (getr (ms_regs ms) 12) (getr (ms_regs ms) 13) (getr (ms_regs ms) 14) (getr (ms_regs ms) 15)
                 (getr (ms_regs ms) 16) (getr (ms_regs ms) 17) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (getr (ms_regs ms) 28) (getr (ms_regs ms) 29) (getr (ms_regs ms) 30)
                 (getr (ms_regs ms) 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) v0 FLA (Z_to_bv 8 1) [CB 2040 junk] junk').
  cbv zeta in SF. rewrite sf5_a0 in SF.
  assert (Husp : bv_unsigned (getr (ms_regs ms) 2) = sp) by (rewrite sf5_sp; reflexivity).
  assert (Hura : bv_unsigned (getr (ms_regs ms) 1) = ra) by (rewrite sf5_ra; reflexivity).
  rewrite Husp, Hura in SF.
  assert (HK : evt BSEGS (sfree5_post (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4)
                 (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (ms_fregs ms) (ms_fcsr ms) F FLA (ms_mem ms)) (kms BSEGS ms)).
  { unfold kms. rewrite Hpc, Hresv. apply SF.
    - exact sf5_RT.
    - exact FRM.
    - exact PRE.
    - exact sf5_flag.
    - exact SHD.
    - clear. replace (4096 * fsp + 5279744 + p5 * 2048) with (2048 * (2 * fsp + 2578 + p5)) by ring. rewrite Z.mul_comm. apply Z_mod_mult.
    - eapply app2r_sub; [exact Fapp | clear -Fp5; lia | clear -Fp5; lia].
    - clear -Ffsp Fp5. lia.
    - eapply app2r_sub; [exact Fapp | clear -Fp5; lia | clear -Fp5; lia].
    - clear -Ffsp Fp5. lia.
    - exact sf5_stk.
    - clear -Fsp. lia.
    - exact Fsp.
    - exact FspK.
    - right. clear -C18 Fp5. lia.
    - right. clear -C18 Fp5. lia.
    - exact sf5_pr1.
    - exact sf5_pr3.
    - exact sf5_rtd1.
    - exact sf5_rtd2.
    - exact Fra. }
  clear SF.
  destruct (kit_run BSEGS _ ms Hsvc HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  unfold sfree5_post in Hpost.
  destruct Hpost as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms2 & MU & WM & ST' & FL' & SH').
  subst ms2. unfold sfree5_W in MU. rewrite Husp in MU, ST'.
  assert (Hmem : ms_mem ms1 = m') by (destruct Heq as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  exists ms1, (Eq t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  split; [exact Hst|]. split; [|split; [|split]].
  - eapply (sden_of_kit BSEGS _ _ ms1); [ | | exact Heq | | exact Hfrm | | | | ].
    + rewrite state_wf_with_pc. exact (proj1 (proj2 SF5_wf)).
    + reflexivity.
    + cbn [s_pc with_pc s_regs SF5_P0]. rget_norm. lnorm. rewrite Z_to_bv_bv_unsigned. rewrite sf5_ra. apply ret_pc_even_w.
      exact (proj1 sf5_facts).
    + (* [comment removed for export] *)
      apply regs_ok_of_cases. intros n Hn. cbn [s_regs with_pc SF5_Q].
      do 32 (destruct n as [|n];
               [ getr_mkR_norm; rget_norm;
                 first [ reflexivity
                       | (rewrite (HR _); rget_norm; lnorm; reflexivity)
                       | (lnorm; reflexivity) ]
               |]).
      lia.
    + (* [comment removed for export] *)
      assert (Hwr : forallb (rwf 200) (s_rgs SF5_Q) = true) by (vm_compute; reflexivity).
      rewrite Forall_forall. intros R HRin. apply (rg_ok_agree BSEGS 200 E _ _ R); [rewrite forallb_forall in Hwr; exact (Hwr R HRin) | apply Eq_agree|].
      revert R HRin. rewrite <- Forall_forall. cbn [s_rgs with_pc SF5_Q]. rewrite RGS1_eq. unfold RGS1.
      pose proof HG as HG'. unfold RGS0, rt_rgs_t, relro_rgs in HG'. cbn [app] in HG'.
      assert (UW : forall i R, nth_error RGS0 i = Some R -> ~ In i [0%nat; 2%nat; 3%nat] -> rg_ok BSEGS E (ms_mem ms) R -> rg_ok BSEGS E m' R).
      { intros i R Hi Hni HR0. exact (rg_ok_unwritten BSEGS E (ms_mem ms) m' RGS0 _ _ i R HD Hi Hni MU sf5_HW HR0). }
      apply Forall_cons_iff in HG' as [G0 HG']. apply Forall_cons_iff in HG' as [G1 HG']. apply Forall_cons_iff in HG' as [G2 HG'].
      apply Forall_cons_iff in HG' as [G3 HG']. apply Forall_cons_iff in HG' as [G4 HG']. apply Forall_cons_iff in HG' as [G5 HG'].
      apply Forall_cons_iff in HG' as [G6 HG']. apply Forall_cons_iff in HG' as [G7 HG']. apply Forall_cons_iff in HG' as [G8 HG'].
      apply Forall_cons_iff in HG' as [G9 HG']. apply Forall_cons_iff in HG' as [G10 HG']. apply Forall_cons_iff in HG' as [G11 HG'].
      apply Forall_cons_iff in HG' as [G12 HG']. apply Forall_cons_iff in HG' as [G13 HG']. apply Forall_cons_iff in HG' as [G14 HG'].
      apply Forall_cons_iff in HG' as [G15 HG']. apply Forall_cons_iff in HG' as [G16 HG']. apply Forall_cons_iff in HG' as [G17 HG'].
      apply Forall_cons_iff in HG' as [G18 HG']. clear HG'.
      pose proof sf5_vals as (V1 & V5 & V6).
      unfold rt_rgs_t, relro_rgs. cbn [app].
      pose proof (rgs_disj_nth E _ 0 2 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D2.
      pose proof (rgs_disj_nth E _ 0 3 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D3.
      unfold rg_disj, rsz in D2, D3. cbn [rg_base rg_size track RGz] in D2, D3.
      rewrite V1 in D2. rewrite V6 in D3. lnorm_in D2. lnorm_in D3.
      change (bv_unsigned (Z_to_bv 64 (1 + 0))) with 1 in D2. change (bv_unsigned (Z_to_bv 64 (256 + 0))) with 256 in D3.
      constructor.
      { (* [comment removed for export] *)
        apply (rw_mix BSEGS E (ms_mem ms) m' _ _ (sp - 16) sp G0 eq_refl eq_refl MU ST').
        intros k Hk. unfold rsz in Hk. cbn [rg_base rg_size] in Hk |- *. lnorm_in Hk. lnorm.
        cbn [Frame.outside]. clear -Hk W1 W2 D2 D3. lia. }
      constructor.
      { (* [comment removed for export] *)
        assert (G1t : rg_ok BSEGS E (ms_mem ms) (track (RG (ladd (fsc AR5) (lscale 2048 P5)) (lconst 2048) RW TEmpty) 2040 (bv8 FLB5)))
          by exact G1.
        pose proof (rg_ok_untrack BSEGS E _ _ _ _ _ _ G1t) as G1u.
        apply (rg_ok_munch BSEGS E (ms_mem ms) m' _ _ G1u MU). intros k Hk.
        unfold rsz in Hk. cbn [rg_base rg_size] in Hk |- *. change (bv_unsigned (lden E (lconst 2048))) with 2048 in Hk. rewrite V5.
        pose proof sf5_facts as (_ & Hp & _ & Hf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C18' & Fapp' & _).
        assert (E8 : F / 8 = 512 * fsp + 659968 + p5 * 256)
          by (replace (4096 * fsp + 5279744 + p5 * 2048) with ((512 * fsp + 659968 + p5 * 256) * 8) by ring; rewrite Z.div_mul by discriminate; reflexivity).
        cbn [Frame.outside]. rewrite E8. unfold app2r in Fapp'. clear -Hk W1 W2 Hp Hf C18' Fapp'. unfold KHI, KTOP in *.
        destruct Fapp' as [[A1 A2]|[A1 A2]]; repeat split; lia. }
      constructor.
      { (* [comment removed for export] *)
        destruct FL' as ((FLwf & FLb) & FLw). cbn [cells_bytes cbytes cells_size csize] in FLb, FLw. rewrite app_nil_r in FLb.
        change (Z.of_nat (1 + 0)) with 1 in FLw.
        apply track_of_bytes_at; [ | clear; lia | apply Z.leb_le; vm_compute; reflexivity | ].
        - apply (rg_ok_rz_of BSEGS E m' _ FLA 1); [reflexivity | reflexivity | exact V1 | reflexivity | clear; lia | pose proof sf5_facts as (_ & Hp & _ & Hf & _); clear -Hp Hf; unfold KHI, KTOP, two64 in *; lia |].
          intros i Hi. assert (i = 0) by lia. subst i. split.
          + destruct FLb as (_ & _ & B). pose proof (B 0%nat ltac:(cbn; lia)) as X. rewrite Z.add_0_r in X |- *. exact X.
          + destruct FLw as (_ & _ & W). exact (W 0 ltac:(lia)).
        - cbn [rg_base]. rewrite V1, Z.add_0_r. apply (bytes_at_ext BSEGS _ _ _ _ FLb). apply bytes_eqb_eq. vm_compute. reflexivity. }
      constructor.
      { (* [comment removed for export] *)
        destruct SH' as ((SHwf & SHb) & SHw). cbn [cells_bytes cbytes cells_size csize] in SHb, SHw. rewrite app_nil_r in SHb.
        apply track_of_bytes_at; [ | clear; lia | apply Z.leb_le; vm_compute; reflexivity | ].
        - apply (rg_ok_of_u8arr BSEGS E m' _ (2147450880 + F / 8) (repeat (Z_to_bv 8 245) 256));
            [reflexivity | reflexivity | exact V6 | reflexivity | split; [exact SHb | exact SHw]].
        - cbn [rg_base]. rewrite V6, Z.add_0_r. apply (bytes_at_ext BSEGS _ _ _ _ SHb). apply bytes_eqb_eq. vm_compute. reflexivity. }
      constructor; [exact (UW 4%nat _ eq_refl ltac:(cbn; intuition discriminate) G4)|].
      constructor; [exact (UW 5%nat _ eq_refl ltac:(cbn; intuition discriminate) G5)|].
      constructor; [exact (UW 6%nat _ eq_refl ltac:(cbn; intuition discriminate) G6)|].
      constructor; [exact (UW 7%nat _ eq_refl ltac:(cbn; intuition discriminate) G7)|].
      constructor; [exact (UW 8%nat _ eq_refl ltac:(cbn; intuition discriminate) G8)|].
      constructor; [exact (UW 9%nat _ eq_refl ltac:(cbn; intuition discriminate) G9)|].
      constructor; [exact (UW 10%nat _ eq_refl ltac:(cbn; intuition discriminate) G10)|].
      constructor; [exact (UW 11%nat _ eq_refl ltac:(cbn; intuition discriminate) G11)|].
      constructor; [exact (UW 12%nat _ eq_refl ltac:(cbn; intuition discriminate) G12)|].
      constructor; [exact (UW 13%nat _ eq_refl ltac:(cbn; intuition discriminate) G13)|].
      constructor; [exact (UW 14%nat _ eq_refl ltac:(cbn; intuition discriminate) G14)|].
      constructor; [exact (UW 15%nat _ eq_refl ltac:(cbn; intuition discriminate) G15)|].
      constructor; [exact (UW 16%nat _ eq_refl ltac:(cbn; intuition discriminate) G16)|].
      constructor; [exact (UW 17%nat _ eq_refl ltac:(cbn; intuition discriminate) G17)|].
      constructor; [exact (UW 18%nat _ eq_refl ltac:(cbn; intuition discriminate) G18)|].
      constructor.
    + (* [comment removed for export] *)
      apply (rgs_disj_agree 200 E); [vm_compute; reflexivity | apply Eq_agree|].
      apply (rgs_disj_shape E (s_rgs SF5_P0)); [apply shape_eqb_eq; exact (proj2 (proj2 SF5_wf)) | exact HD].
    + (* [comment removed for export] *)
      cbn [s_facts with_pc SF5_Q].
      assert (Hw : forallb (fwf 200) SF5_F = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF |- *. intros f Hf.
      exact (fact_ok_agree 200 E _ f (Hw f Hf) (Eq_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (HF f Hf)).
  - apply upds_agree. repeat constructor; cbn [fst s_next SF5_P0]; lia.
  - (* [comment removed for export] *)
    intros x Hx. rewrite Hmem. apply MU.
    destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. cbn [s_rgs SF5_P0] in Hout. rewrite RGS0_eq in Hout. unfold RGS0, rt_rgs_t, relro_rgs in Hout. cbn [app] in Hout.
      apply Forall_cons_iff in Hout as [O0 Hout]. apply Forall_cons_iff in Hout as [O1 Hout].
      apply Forall_cons_iff in Hout as [O2 Hout]. apply Forall_cons_iff in Hout as [O3 Hout]. clear Hout.
      unfold rsz in O0, O2, O3. cbn [rg_base rg_size track RGz] in O0, O2, O3.
      lnorm_in O0. lnorm_in O2. lnorm_in O3.
      rewrite !u_Z_to_bv in O2, O3. unfold vz in *.
      rewrite !Z.mod_small in O2, O3 by (clear -Ffsp Fp5 Bfsp Bp5; unfold two64 in *; lia).
      assert (E8 : F / 8 = 512 * fsp + 659968 + p5 * 256)
        by (replace (4096 * fsp + 5279744 + p5 * 2048) with ((512 * fsp + 659968 + p5 * 256) * 8) by ring; rewrite Z.div_mul by discriminate; reflexivity).
      pose proof (bv_unsigned_in_range _ x) as Bx. unfold bv_modulus in Bx. change (2 ^ Z.of_N 64) with two64 in Bx.
      cbn [Frame.outside]. rewrite E8. clear -O0 O2 O3 W1 W2 Bx. unfold two64 in *. repeat split; lia.
    + apply sf5_HW. cbn [s_rgs SF5_P0] in Hrt. rewrite RGS0_eq in Hrt.
      exact (rt_frame E RGS0 [0%nat; 2%nat; 3%nat] x HD ltac:(vm_compute; reflexivity) Hrt).
  - destruct Heq as (_ & HFr & _ & _ & _ & HFc & _). cbn [ms_fregs ms_fcsr with_rom MS] in HFr, HFc. split; [exact HFr | exact HFc].
Qed.

End SF5.

Theorem sf5_kfn_fp : kfn_ok_fp BSEGS SF5_P0 SF5_Q.
Proof. intros E ms Hd. exact (sf5_run E ms Hd). Qed.
Theorem sf5_kfn : kfn_ok BSEGS SF5_P0 SF5_Q.
Proof. exact (kfn_okP_ok BSEGS fpeq _ _ sf5_kfn_fp). Qed.
