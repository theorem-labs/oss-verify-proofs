(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_kit R_m2s R_setshadow R_poison I_memcpyw FX_Layout FX_Stdio_iface Imp_xifaceA X_ixdefs RT_trans F_fwrite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition g_REAL_fwrite : Z := 0x181d90.
Definition e_musl_fwrite : Z := 0x168e70.
Definition g_GOT_REAL_memcpy : Z := 0x17fef0.
Definition IOSBLK : Z := 0x6bc480.
Definition IOSBLK_LEN : Z := 1984.

Definition xcells (sp0 : Z) (m : mem) : Prop :=
  (0x7fff80000000 <= sp0 /\ sp0 <= USTACK_TOP)
  /\ rw_cells bsegs m g_REAL_fwrite [C8 (Z_to_bv 64 e_musl_fwrite)]
  /\ icells m
  /\ ro_cells bsegs m g_GOT_REAL_memcpy [C8 (Z_to_bv 64 0x181f38)]
  /\ acc bsegs m IOSBLK IOSBLK_LEN
  /\ acc bsegs m (sp0 - STACK_WIN) (USTACK_TOP - (sp0 - STACK_WIN)).

Definition ixit2 (sp0 : Z) (m : mem) : Prop := ixit_rt sp0 m /\ xcells sp0 m.

Local Ltac rwx C AGX WM := apply (rw_cells_agree bsegs _ _ _ _ C); [apply AGX; cbn [cells_size csize Nat.add]; try lia | exact WM].
Local Ltac rox C AGX := apply (ro_cells_agree bsegs _ _ _ _ C); apply AGX; cbn [cells_size csize Nat.add]; try lia.

Lemma IX_frame : forall sp0, IX_frame_stmt (ixit_rt sp0) (sp0 - STACK_WIN).
Proof.
  intros sp0 W lo hi m m' IX MU WM HLO SUB.
  assert (AGX : forall a n, (a + n <= lo) -> (a + n <= 0x184af0 \/ 0x184af0 + 232 <= a) -> (a + n <= 0x184cd0 \/ 0x184cd0 + 232 <= a) ->
                 (a + n <= 0x6be3b8 \/ 0x6be3b8 + 8 <= a) -> agree_on (fun x => a <= x < a + n) m m').
  { intros a n H1 H2 H3 H4 x Hx. apply MU. apply SUB. unfold XWI, XTPLOC. cbn [outside fst snd]. lia. }
  unfold ixit_rt, mtab_at in *.
  destruct IX as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & (T & M1 & M2 & T1 & T2 & T3 & M3 & M4) & D1 & V1 & V2 & PS).
  unfold ps_cells, m2s_cells, setshadow_cells, R_poison.g_got_common_flags, R_poison.g_can_poison, R_poison.g_cf_clear_shadow_mmap_threshold,
    R_setshadow.g_got_real_memset, R_setshadow.g_real_memset, R_setshadow.musl_memset_entry in *.
  destruct PS as (P1 & (P2 & P3 & P4) & (P5 & P6) & P7 & P8).
  unfold g_asan_inited, g_GOT_lsan_off, LSAN_CTR, g_GOT_flags, g_REAL_cxa_atexit, e_musl_cxa_atexit, g_REAL_fflush, e_musl_fflush,
    g_REAL_wcrtomb, e_musl_wcrtomb, g_GOT_mbstate_t_sz, g_mbstate_t_sz, g_flags_cio, g_icpt_mdmap, g_mdmem, MT_SIZE, MT_OFF_OUT, MT_OFF_ERR,
    g_flags_dco, g_GOT_verbosity, g_verbosity, SEGTOP_A, STACK_WIN, kHighMemEnd, SHB in *.
  split; [rwx Y1 AGX WM|]. split; [rwx Y2 AGX WM|]. split; [rwx Y3 AGX WM|]. split; [rwx Y4 AGX WM|]. split; [rwx Y5 AGX WM|].
  split; [rwx Y6 AGX WM|]. split; [rwx Y7 AGX WM|]. split; [rox Y8 AGX|]. split; [rwx Y9 AGX WM|]. split; [rwx Y10 AGX WM|].
  split.
  { exists T. split; [rwx M1 AGX WM|]. split; [rwx M2 AGX WM|]. split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
    split; [rwx M3 AGX WM| rwx M4 AGX WM]; rewrite Z15_size; lia. }
  split; [rox D1 AGX|]. split; [rwx V1 AGX WM|]. split; [rwx V2 AGX WM|].
  split; [rwx P1 AGX WM|]. split; [split; [rwx P2 AGX WM| split; [rwx P3 AGX WM| rwx P4 AGX WM]]|].
  split; [split; [rwx P5 AGX WM| rwx P6 AGX WM]|]. split; [rwx P7 AGX WM| rwx P8 AGX WM].
Qed.

Lemma xcells_frame : forall sp0 W lo hi m m',
  xcells sp0 m -> munch W m m' -> wmono bsegs m m' -> sp0 - STACK_WIN <= lo -> sub_fp W (XWI lo hi) -> xcells sp0 m'.
Proof.
  intros sp0 W lo hi m m' (SP & RF & (G2 & G1 & RM & SHC & RI) & GM & AB & AS) MU WM HLO SUB.
  assert (AGX : forall a n, (a + n <= lo) -> (a + n <= 0x184af0 \/ 0x184af0 + 232 <= a) -> (a + n <= 0x184cd0 \/ 0x184cd0 + 232 <= a) ->
                 (a + n <= 0x6be3b8 \/ 0x6be3b8 + 8 <= a) -> agree_on (fun x => a <= x < a + n) m m').
  { intros a n H1 H2 H3 H4 x Hx. apply MU. apply SUB. unfold XWI, XTPLOC. cbn [outside fst snd]. lia. }
  assert (MU' : munch (XWI lo hi) m m') by (intros x Hx; apply MU; apply SUB; exact Hx).
  unfold g_REAL_fwrite, e_musl_fwrite, g_GOT_REAL_memcpy, IOSBLK, IOSBLK_LEN, STACK_WIN, USTACK_TOP in *.
  split; [exact SP|]. split; [rwx RF AGX WM|].
  split; [split; [rox G2 AGX| split; [rox G1 AGX| split; [rox RM AGX| split; [rox SHC AGX| rox RI AGX]]]]|].
  split; [rox GM AGX|].
  split.
  - apply (acc_transport _ m m' _ _ AB MU'); [lia|]. unfold XWI, XTPLOC, shad, SHB. cbn. repeat split; try exact I; lia.
  - apply (acc_transport _ m m' _ _ AS MU'); [lia|]. unfold XWI, XTPLOC, shad, SHB. cbn.
    assert (H8 : forall z, 0 <= z -> z / 8 <= z) by (intros z Hz; apply Z.div_le_upper_bound; lia).
    pose proof (Z.div_pos (sp0 - 8388608) 8 ltac:(lia) ltac:(lia)).
    assert ((140737488355328 - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
    assert ((sp0 - 8388608 + (140737488355328 - (sp0 - 8388608)) - 1) / 8 = (140737488355328 - 1) / 8) by (f_equal; lia).
    repeat split; try exact I; lia.
Qed.

Lemma IX2_frame : forall sp0, IX_frame_stmt (ixit2 sp0) (sp0 - STACK_WIN).
Proof.
  intros sp0 W lo hi m m' [IX XC] MU WM HLO SUB. split; [exact (IX_frame sp0 W lo hi m m' IX MU WM HLO SUB)| exact (xcells_frame sp0 W lo hi m m' XC MU WM HLO SUB)].
Qed.

Section Lift.
  Variables (IX C : mem -> Prop) (XLO : Z).
  Hypothesis CF : forall lo sp Fp m m', C m -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono bsegs m m' -> XLO <= lo ->
    (Fp = RSTDOUT \/ Fp = RSTDERR) -> C m'.

  Lemma ifflush_idle_lift : ifflush_idle_stmt IX XLO -> ifflush_idle_stmt (fun m => IX m /\ C m) XLO.
  Proof.
    intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp flags mode wend wpos wfn bufp bufsize fd lbf tail lo
      FC Ha0 FPC Fp0 FpL WP ST LOD GLO XL SPH [IXm Cm] MI.
    eapply evt_mono; [exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp flags mode wend wpos wfn bufp bufsize fd lbf tail lo
                                FC Ha0 FPC Fp0 FpL WP ST LOD GLO XL SPH IXm MI)|].
    intros ms' PO. unfold ifflush_idle_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC' & IX').
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FC'|]. split; [exact IX'|].
    exact (CF lo (bv_unsigned sp) Fp m m' Cm MU WM XL FPC).
  Qed.

  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Lemma ifflush_stdout_lift : ifflush_stdout_stmt IX XLO get_so set_so -> ifflush_stdout_stmt (fun m => IX m /\ C m) XLO get_so set_so.
  Proof.
    intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st flags mode tail bufbytes lo canary
      so P1 P2 P3 P4 P5 P6 P7 ST LOD GLO XL SPH SSP [IXm Cm] MI.
    pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st flags mode tail bufbytes lo canary
                  P1 P2 P3 P4 P5 P6 P7 ST LOD GLO XL SPH SSP IXm MI) as IM.
    unfold implM in *. eapply impl_post_evt''; [exact IM|]. intros [|[xr st']] ms' PO; [apply evt_done; exact I|]. apply evt_done.
    cbn [epost fst snd] in *. unfold ifflush_stdout_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & m' & so' & -> & MU & WM & MI' & ST' & SO' & STE & FC' & SSP' & IX').
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, mode', m', so'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact SO'|]. split; [exact STE|]. split; [exact FC'|].
    split; [exact SSP'|]. split; [exact IX'|].
    exact (CF lo (bv_unsigned sp) RSTDOUT m m' Cm MU WM XL (or_introl eq_refl)).
  Qed.
End Lift.

Lemma xcells_CF : forall sp0 lo sp Fp m m', xcells sp0 m -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono bsegs m m' -> sp0 - STACK_WIN <= lo ->
  (Fp = RSTDOUT \/ Fp = RSTDERR) -> xcells sp0 m'.
Proof.
  intros sp0 lo sp Fp m m' XC MU WM HLO FPC. apply (xcells_frame sp0 _ lo sp m m' XC MU WM HLO).
  intros x Hx. unfold XWI, XTPLOC in Hx. cbn [outside] in Hx |- *. destruct FPC as [-> | ->]; lia.
Qed.

Lemma stk_top_le : forall (m : mem) lo hi, stk bsegs m lo hi -> lo < hi -> mem_inv bsegs m -> hi <= 2^47.
Proof.
  intros m lo hi (H0 & H1 & H) Hlt MI. destruct (H (hi - 1) ltac:(lia)) as [W _].
  pose proof (wview_below bsegs m (wa (hi - 1)) MI W) as X. unfold wa, UTOP in X. rewrite unsigned_lit in X by lia. lia.
Qed.

Lemma rw_cells_top_le : forall (m : mem) A cs, rw_cells bsegs m A cs -> mem_inv bsegs m -> (0 < cells_size cs)%nat -> A + Z.of_nat (cells_size cs) <= 2^47.
Proof.
  intros m A cs [[WF B] WR] MI Hn. pose proof (wr_at_below bsegs m A _ MI WR) as X. unfold UTOP in X.
  lia.
Qed.
