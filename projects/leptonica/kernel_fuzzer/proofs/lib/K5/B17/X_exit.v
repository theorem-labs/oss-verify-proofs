(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Spec Require Import Prelim Monad Stdio Canon ProgDetTarget.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_frmkit RT_frmbridge RT_frmrom D_iface D_defs D_kit D_clx FX_Exit FX_Stdio_iface F_stdio_write F_stdio_exit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import X_bridge X_bridge2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import I_iodefs F_fwrite I_fwrite X_atexit X_xdefs X_unreg X_fini X_exitw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition so_id (so : stdout_st) : stdout_st := so.
Definition so_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.

Lemma TT_exit_flush : forall (so : stdout_st) (T : TSet),
  (so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 -> T [] ->
  t_eq (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => T)) (t_emit (evw 1 (so_buf so)) T).
Proof.
  intros so T H Hl HT. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  unfold so_id at 1.
  destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
  - destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
    unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
    unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
    rewrite TT_ebind. cbn [TT]. unfold so_id. unfold stdio_writev.
    assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
    rewrite (iov_start_cons (so_buf so) [] NE).
    eapply t_eq_trans.
    { apply (TT_wv_loop (WV_FUEL [so_buf so; []]) 1 [so_buf so; []] so (fun _ => T)); [cbn; lia| | | exact HT];
        unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia. }
    cbn [concat]. rewrite app_nil_r. rewrite <- evw_to_bytes. apply t_eq_refl.
  - assert (E : so_buf so = []) by (destruct (so_buf so); [reflexivity| cbn in Ge; unfold zlength in Ge; cbn in Ge; lia]).
    rewrite E. cbn [TT evw map]. apply t_eq_sym, t_emit_nil_eq. exact HT.
Qed.

Lemma tok_exit_flush : forall (so : stdout_st),
  (so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 ->
  tok [1] ((stdout_exit_flush so_id so_set : @M stdout_st unit) so).
Proof.
  intros so H Hl. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  unfold so_id at 1.
  destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
  - destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
    unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
    unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
    apply tok_ebind; [| intros x; exact I].
    unfold so_id. unfold stdio_writev.
    assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
    rewrite (iov_start_cons (so_buf so) [] NE).
    apply tok_wv_loop; [left; reflexivity| cbn; lia| |]; unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia.
  - cbn. exact I.
Qed.

Section XExit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_XIT : forall Σ m, ART RT Σ m -> xit_rt m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma exit_ok_ph : forall (ph : bool) (XEP : mem -> Prop),
  (forall m, XEP m -> XENVC m /\ atxA ph m /\ atexit_ph ph m) ->
  exit_contract RT XEP OUT_repA ERR_repA.
Proof using AF AF_XIT.
  intros ph XEP HXE.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo
    Ha0 Hcode Htp Hso HFD OUT ERR XE ART0 MI0 CALL SSP.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_XIT Σ m ART0) as (FA & GF & GCX & (dso & DSO) & GX & UG1 & UG2 & RG & MUX & SHC & AI & CP & THR & RMS & COV
                                 & SC1 & SC2 & SC3).
  destruct (HXE m XE) as (XC & ((p1 & p2 & ATX) & _) & PH).
  destruct XC as ((tid & HT & TID) & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & OFL & SEU & SOU & SIN & SINU
                  & GDS & (flag & FLGNZ & FLG) & CPL & (o1 & o2 & o3 & O1 & O2 & O3)).
  destruct SSP as (g & G1 & G2).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  assert (SOK : (so_first so = false \/ so_buf so = []) /\ zlength (so_buf so) <= 2^26).
  { destruct Hso as [->|(k & Hk5 & ->)].
    - split; [right; reflexivity| unfold zlength; cbn; lia].
    - split; [left; reflexivity|]. cbn [so_lines so_buf]. rewrite zlength_zeros_out. lia. }
  set (Qfin := fun (x : unit * stdout_st) (ms' : machine_state) =>
                 ms_svc_pending ms' = Some (Z_to_bv 64 94) /\ areg ms' 10 = Z_to_bv 64 code).
  assert (IMPL : impl asegs (at_node asegs) ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (epost Qfin)
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      t3 t4 t5 t6 F fc e_exit m)).
  { assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
    eapply impl_evt.
    { exact (exit_prefix_spec ph ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo code tid (Z_to_bv 8 0) p1 p2 cdt thr sec tm1 o1 o2 o3 flag dso Ha0 Htp ltac:(lia) ltac:(rewrite EU; exact ST)
               ltac:(rewrite EU; ul) ltac:(lia) TID HT ATX PH ATA EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (conj UG1 UG2) RG MUX SHC AI CP
               THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI0). }
    intros ms1 PO. unfold exit_prefix_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
    rewrite EU in MU1, ST1.
    assert (AG1 : agree_on (fun x => (0x627a98 <= x < 0x627aa0) \/ (0x627f00 <= x < 0x628758) \/ (0xcf248 <= x < 0xcf540)
                                     \/ (0xcb848 <= x < 0xcb850) \/ (0x627848 <= x < 0x627850)) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. ul. }
    Local Ltac tr AG1 WM1 H := apply (rw_cells_agree asegs _ _ _ _ H); [apply (agree_sub _ _ _ _ AG1); intros xa Hxa; cbn in Hxa; lia| exact WM1].
    assert (LIBC1 : rw_cells asegs m1 0x627a98 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]) by tr AG1 WM1 LIBC.
    assert (OFL1 : rw_cells asegs m1 0x627f00 [C8 (Z_to_bv 64 0)]) by tr AG1 WM1 OFL.
    assert (SINU1 : rw_cells asegs m1 0xcf510 [C8 (Z_to_bv 64 0xcf428)]) by tr AG1 WM1 SINU.
    assert (SOU1 : rw_cells asegs m1 0xcf420 [C8 (Z_to_bv 64 0xcf338)]) by tr AG1 WM1 SOU.
    assert (SEU1 : rw_cells asegs m1 0xcf330 [C8 (Z_to_bv 64 0xcf248)]) by tr AG1 WM1 SEU.
    assert (SIN1 : stdin_file m1).
    { destruct SIN as (j0 & j1 & j2 & j3 & j4 & C). exists j0, j1, j2, j3, j4. tr AG1 WM1 C. }
    assert (OUT1 : stdout_file m1 so).
    { apply (stdout_file_agree so m m1); [| exact WM1| exact OUT]. apply (agree_sub _ _ _ _ AG1). intros xa Hxa. lia. }
    assert (ERR1 : stderr_file m1).
    { apply stderr_wfile0_file. apply (stderr_wfile0_agree m m1); [| exact WM1| exact ERR]. apply (agree_sub _ _ _ _ AG1). intros xa Hxa. lia. }
    assert (G11 : ro_cells asegs m1 0xcb848 [C8 (Z_to_bv 64 0x627848)]).
    { apply (ro_cells_agree asegs m m1 _ _ G1). apply (agree_sub _ _ _ _ AG1). intros xa Hxa. cbn in Hxa. lia. }
    assert (G21 : ro_cells asegs m1 0x627848 [C8 g]).
    { apply (ro_cells_agree asegs m m1 _ _ G2). apply (agree_sub _ _ _ _ AG1). intros xa Hxa. cbn in Hxa. lia. }
    assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).
    pose proof (stdio_exit_proof so_id so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)) as SE.
    unfold stdio_exit_spec_stmt in SE.
    pose proof (SE (Z_to_bv 64 0xb7480) (Z_to_bv 64 (usp + -16)) gp tp u0 u1 u2 (Z_to_bv 64 code) s1 b0 b1 b2 b3 b4 b5 b6 b7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 lo so g cdt thr sec tm1
                  ltac:(rewrite EU16; exact ST1) LIBC1 OFL1 SINU1 SIN1 SOU1 SEU1 OUT1 ERR1 G11 G21 MI1 Htp
                  ltac:(rewrite EU16; ul) ltac:(ul)) as IM.
    clear SE. unfold implM in IM.
    rewrite EU.
    eapply impl_post_evt''; [exact IM|].
    intros [|[xr so']] ms2 H2; [apply evt_done; exact I|].
    cbn [epost fst snd] in H2 |- *. unfold stdio_exit_post in H2.
    destruct H2 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & so'' & m2 & -> & _ & _ & MI2 & _).
    rewrite (ret_pc_even 0xb7480) by lia.
    eapply evt_mono; [exact (exit_tail_spec (usp + -16) code gp tp v0 v1 v2 s1 c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               v3 v4 v5 v6 F fc m2 ltac:(lia) ltac:(assumption))|].
    intros ms3 (ra3 & ->). split; reflexivity. }
  assert (RZ : realizes asegs c (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => t_emit [] T))).
  { apply (impl_realizes_f asegs SEGTOP_A asegs_wx asegs_below asegs_frm [1] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) Qfin
             (fun _ => t_emit [] T)
             (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc e_exit m) c
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact (tok_exit_flush so (proj1 SOK) (proj2 SOK))| exact Hc| exact IMPL|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros x ms' c' (HS & HA0) Hc'.
      assert (R : realizes asegs c' T).
      { apply Hk.
        exists (rt_allow RT Σ), (frmW (eq ms')), (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo). split; [exact Hc'|]. split.
        + intros ms [<- _]. split; [right; exact HS| exact HA0].
        + intros mo (_ & _ & HFS). exact HFS. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty asegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  eapply t_eq_trans; [apply TT_exit_flush; [exact (proj1 SOK)| exact (proj2 SOK)| apply t_emit_has_nil]|].
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.

Theorem exit_ok : exit_contract RT XENVA OUT_repA ERR_repA.
Proof using AF AF_XIT.
  apply (exit_ok_ph false). intros m (XC & XA). split; [exact XC|]. split; [exact XA| exact I].
Qed.

Theorem exit_ok1 : exit_contract RT XENVA1x OUT_repA ERR_repA.
Proof using AF AF_XIT.
  apply (exit_ok_ph true). intros m ((XC & XA) & FL). split; [exact XC|]. split; [exact XA|].
  destruct XA as (_ & PF & PA). exact (conj PF (conj PA FL)).
Qed.

End XExit.
