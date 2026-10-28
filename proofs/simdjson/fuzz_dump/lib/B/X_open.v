(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_clx D_rlkit X_openw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma nretA_MSsvc : forall R F pc x8 fc rv m ro r,
  nretA (MSsvc R F pc x8 fc rv m ro) (mkEffect r [] []) = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4)%bv fc rv m ro.
Proof. reflexivity. Qed.

Lemma pc_93368 : (Z_to_bv 64 0x16185c + Z_to_bv 64 4)%bv = Z_to_bv 64 0x161860.
Proof. apply lit_add_lit. Qed.

Lemma munch_merge : forall (W1 W2 W : list (Z * Z)) m1 m2 m3, munch W1 m1 m2 -> munch W2 m2 m3 ->
  (forall x, outside W x -> outside W1 x /\ outside W2 x) -> munch W m1 m3.
Proof. intros W1 W2 W m1 m2 m3 H1 H2 HW x Hx. destruct (HW _ Hx) as [A B]. rewrite (H2 x B). exact (H1 x A). Qed.

Section XOpen.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, TP_A, ERRNO_A, SSP_GUARD in *; lia.

Theorem open_ok : open_contract RT.
Proof using AF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path s lo ent
    Ha0 Ha1 HB HNZ HSL HDD HENT HFREE ST LO SPW ERRN (g & G1 & G2) ART0 MI0 HTP HSEP.
  subst a0 a1 tp.
  intros T1 T2 c Hc Hk1 Hk2.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  assert (SEG : SEGTOP_A <= lo) by ul.
  assert (UTOPsp : usp <= 2^47).
  { pose proof (wr_at_below bsegs m lo (usp - lo) MI0 (stk_wr m lo usp lo (usp - lo) ST ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)).
    unfold UTOP in *. lia. }
  pose proof (open_walkA usp path ra gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo g ST SEG LO ltac:(lia) G1 G2 MI0) as W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6ab368) (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0)
                       (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (-100)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16185c) (Z_to_bv 64 56) fc None m1 (seg_rom bsegs)) in *.
  assert (HB1 : bytes_at bsegs m1 path (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_agree bsegs m m1 _ _ HB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn.
    rewrite length_app in Hx. cbn [length] in Hx. split; [lia| exact I]. }
  unfold ASTA in Hc1'.
  apply (ast_open_br bsegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun e ms => nretA msA (efferr e) = ms) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun fdw ms => nretA msA (eff0 fdw) = ms) (fun fdw mo => fdw = alloc_fd F0 /\ (ARTM RT Σ mo /\ PMfd (fd_insert F0 fdw ent) fs0 mo))
           s fs0 ent); [| | exact HENT| | | exact Hc1'| |].
  - exact (ASTA_PM_mat_stable RT AF Σ F0 fs0).
  - intros fdw. apply mat_stable_and; [apply mat_stable_pure| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)].
  - intros ms <-. split; [| split; intros; reflexivity].
    split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [exact HNZ|]. split; [exact HSL|].
    split; [exact HDD|]. split; [reflexivity|].
    change (areg msA 11) with (Z_to_bv 64 path). pose proof (bytes_at_bound bsegs m1 path _ HB1) as BB.
    rewrite unsigned_lit by (rewrite length_app in BB; cbn [length] in BB; lia). exact HB1.
  - intros mo (HAR & HF & HFS). split; [exact HFS|]. split; [split; [exact HAR| split; assumption]|].
    rewrite HF. split; [exact HFREE|]. split; [reflexivity|].
    split; [apply (af_with_fds RT AF); exact HAR| split; [reflexivity| exact HFS]].
  -
    intros c2 (e & He & Hc2). pose proof (openat_errnos_range e He) as HeR.
    assert (EQ : nretA msA (efferr e) = MS (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6ab368) (Z_to_bv 64 path)
                   t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (- e)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0)
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x161860) fc None m1 (seg_rom bsegs)).
    { unfold msA, efferr, eff0, errno_ret. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2.
    assert (ERR0 : exists errv, rw_cells bsegs m (errno_cell (Z_to_bv 64 0x6ab368)) [C4 errv]) by (destruct ERRN as [H|H]; [eexists; exact H| exact H]).
    destruct ERR0 as (errv & ERR0).
    assert (EE : errno_cell (Z_to_bv 64 0x6ab368) = 0x6ab2c4) by (unfold errno_cell; rewrite unsigned_lit by lia; reflexivity).
    rewrite EE in ERR0.
    assert (ERR1 : rw_cells bsegs m1 (bv_unsigned (Z_to_bv 64 0x6ab368) + -164) [C4 errv]).
    { rewrite unsigned_lit by lia. apply (rw_cells_agree bsegs m m1 _ _ ERR0); [| exact WM1].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    assert (G2' : ro_cells bsegs m1 SSP_GUARD [C8 g]).
    { apply (ro_cells_agree bsegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (open_walkB_err usp path e ra gp (Z_to_bv 64 0x6ab368) t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m1 lo g errv junk ST1 SEG LO ltac:(lia) HeR FR1 G2' ERR1 ltac:(rewrite unsigned_lit; lia)
                  ltac:(rewrite unsigned_lit by lia; lia) MI1) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ F0 fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk1.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m2 & RS & MU2 & WM2 & MI2 & ERR2 & ST2) & Hc3').
    rewrite unsigned_lit in MU2, ERR2 by lia.
    assert (ART2 : ART RT Σ m2).
    { apply (af_frame RT AF Σ m m2 (usp - 128) ART0); [lia| | exact (wmono_trans bsegs m m1 m2 WM1 WM2)].
      intros a Ha. rewrite (MU2 a), (MU1 a); [reflexivity| |].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I].
        intros Hin. apply Ha. right; left. apply client_static_intro. lia. }
    exists e, m2. split; [exact He|].
    eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP; exact RS|].
    split; [| unfold errno_cell; rewrite unsigned_lit by lia; exact ERR2].
    split; [exact ART2|]. split; [exact MI2|]. split; [exact (wmono_trans bsegs m m1 m2 WM1 WM2)|].
    split; [exact ST2|].
    apply (munch_merge [(usp - 96, usp)] [(usp + -112, usp + -96); (0x6ab2c4, 0x6ab2c4 + 4)] _ m m1 m2 MU1 MU2).
    intros x Hx. unfold errno_cell in Hx. rewrite unsigned_lit in Hx by lia. cbn in Hx |- *. intuition lia.
  -
    intros c2 (fdw & Hc2).
    pose proof Hc2 as (_ & _ & (Efd & _) & _). subst fdw.
    assert (Hc2' : AST SEGTOP_A (rt_allow RT Σ) (fun ms => nretA msA (eff0 (alloc_fd F0)) = ms)
                     (fun mo => ARTM RT Σ mo /\ PMfd (fd_insert F0 (alloc_fd F0) ent) fs0 mo) c2).
    { apply (AST_conseq SEGTOP_A _ _ _ _ _ c2 Hc2); [intros ms H; exact H| intros mo (_ & H); exact H]. }
    clear Hc2. rename Hc2' into Hc2.
    pose proof (LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.alloc_fd_le F0) as AFL.
    set (fd := bv_unsigned (alloc_fd F0)) in *.
    assert (EFD : alloc_fd F0 = Z_to_bv 64 fd) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (FDR : 0 <= fd) by (pose proof (bv_unsigned_in_range 64 (alloc_fd F0)); lia).
    assert (EQ : nretA msA (eff0 (alloc_fd F0)) = MS (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6ab368)
                   (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 fd) (Z_to_bv 64 path) (Z_to_bv 64 0x8000)
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x161860) fc None m1 (seg_rom bsegs)).
    { unfold msA, eff0. rewrite nretA_MSsvc, mkR_set_a0, pc_93368, <- EFD. reflexivity. }
    rewrite EQ in Hc2.
    assert (G2' : ro_cells bsegs m1 SSP_GUARD [C8 g]).
    { apply (ro_cells_agree bsegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (open_walkB_ok usp path fd ra gp (Z_to_bv 64 0x6ab368) t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m1 lo g junk ST1 SEG LO ltac:(lia) ltac:(lia) FR1 G2' MI1) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk2.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (RS & ST2) & Hc3').
    assert (ART1 : ART RT Σ m1).
    { apply (af_frame RT AF Σ m m1 (usp - 128) ART0); [lia| | exact WM1].
      intros a Ha. rewrite (MU1 a); [reflexivity|]. cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I]. }
    exists m1. eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP, EFD; exact RS|].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact WM1|]. split; [exact ST2|].
    intros x Hx. apply MU1. cbn in Hx |- *. intuition lia.
Qed.

Theorem open_refused_ok : open_refused_contract RT.
Proof using AF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path s lo
    Ha0 Ha1 HB HNZ HSL HDD HENT ST LO SPW (errv & ERR0) (g & G1 & G2) ART0 MI0 HTP HSEP.
  subst a0 a1 tp.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  assert (SEG : SEGTOP_A <= lo) by ul.
  assert (UTOPsp : usp <= 2^47).
  { pose proof (wr_at_below bsegs m lo (usp - lo) MI0 (stk_wr m lo usp lo (usp - lo) ST ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)).
    unfold UTOP in *. lia. }
  pose proof (open_walkA usp path ra gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo g ST SEG LO ltac:(lia) G1 G2 MI0) as W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6ab368) (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0)
                       (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (-100)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16185c) (Z_to_bv 64 56) fc None m1 (seg_rom bsegs)) in *.
  assert (HB1 : bytes_at bsegs m1 path (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_agree bsegs m m1 _ _ HB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn.
    rewrite length_app in Hx. cbn [length] in Hx. split; [lia| exact I]. }
  unfold ASTA in Hc1'.
  apply (ast_open_fail bsegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun e ms => nretA msA (efferr e) = ms) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) s fs0); [| exact HENT| | | exact Hc1'|].
  - exact (ASTA_PM_mat_stable RT AF Σ F0 fs0).
  - intros ms <-. split; [| intros; reflexivity].
    split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [exact HNZ|]. split; [exact HSL|].
    split; [exact HDD|]. split; [reflexivity|].
    change (areg msA 11) with (Z_to_bv 64 path). pose proof (bytes_at_bound bsegs m1 path _ HB1) as BB.
    rewrite unsigned_lit by (rewrite length_app in BB; cbn [length] in BB; lia). exact HB1.
  - intros mo (HAR & HF & HFS). split; [exact HFS| split; [exact HAR| split; assumption]].
  - intros c2 (e & HeR & Hc2).
    assert (EQ : nretA msA (efferr e) = MS (mkR (Z_to_bv 64 0x14faf0) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6ab368) (Z_to_bv 64 path)
                   t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (- e)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0)
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x161860) fc None m1 (seg_rom bsegs)).
    { unfold msA, efferr, eff0, errno_ret. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2.
    assert (EE : errno_cell (Z_to_bv 64 0x6ab368) = 0x6ab2c4) by (unfold errno_cell; rewrite unsigned_lit by lia; reflexivity).
    rewrite EE in ERR0.
    assert (ERR1 : rw_cells bsegs m1 (bv_unsigned (Z_to_bv 64 0x6ab368) + -164) [C4 errv]).
    { rewrite unsigned_lit by lia. apply (rw_cells_agree bsegs m m1 _ _ ERR0); [| exact WM1].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    assert (G2' : ro_cells bsegs m1 SSP_GUARD [C8 g]).
    { apply (ro_cells_agree bsegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (open_walkB_err usp path e ra gp (Z_to_bv 64 0x6ab368) t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m1 lo g errv junk ST1 SEG LO ltac:(lia) HeR FR1 G2' ERR1 ltac:(rewrite unsigned_lit; lia)
                  ltac:(rewrite unsigned_lit by lia; lia) MI1) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ F0 fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m2 & RS & MU2 & WM2 & MI2 & ERR2 & ST2) & Hc3').
    rewrite unsigned_lit in MU2, ERR2 by lia.
    assert (ART2 : ART RT Σ m2).
    { apply (af_frame RT AF Σ m m2 (usp - 128) ART0); [lia| | exact (wmono_trans bsegs m m1 m2 WM1 WM2)].
      intros a Ha. rewrite (MU2 a), (MU1 a); [reflexivity| |].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I].
        intros Hin. apply Ha. right; left. apply client_static_intro. lia. }
    exists e, m2. split; [exact HeR|].
    eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP; exact RS|].
    split; [| unfold errno_cell; rewrite unsigned_lit by lia; exact ERR2].
    split; [exact ART2|]. split; [exact MI2|]. split; [exact (wmono_trans bsegs m m1 m2 WM1 WM2)|].
    split; [exact ST2|].
    apply (munch_merge [(usp - 96, usp)] [(usp + -112, usp + -96); (0x6ab2c4, 0x6ab2c4 + 4)] _ m m1 m2 MU1 MU2).
    intros x Hx. unfold errno_cell in Hx. rewrite unsigned_lit in Hx by lia. cbn in Hx |- *. intuition lia.
Qed.

End XOpen.
