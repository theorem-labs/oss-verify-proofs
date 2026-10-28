(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section ExitW.
  Variable E : s2env.
  Hypothesis OK : env_ok E.

  Definition MEMXW (fc : bv 32) (m1 : mem) : Prop :=
    frm0 fc /\
    (exists jlo jhi, rw_cells asegs m1 (e_spa E) [CB 240 jlo; C8 (wz (e_FF E)); CB 32 jhi]) /\
    rw_cells asegs m1 (bv_unsigned (e_sp E) + -104) (saved_cells E) /\
    stk asegs m1 (e_spa E + 280) (bv_unsigned (e_sp E) + -104) /\
    wr_at asegs m1 (e_FF E) 8 /\
    (exists nxt, rw_cells asegs m1 (e_THIS E) (impl_cells E nxt)) /\
    mem_inv asegs m1 /\ munch (s2_W E) (e_m0 E) m1 /\ wmono asegs (e_m0 E) m1 /\
    stk asegs m1 (e_lo E) (e_spa E) /\
    tape_img E (e_tws E) (e_sbs E) m1.

  Lemma frw_weak : forall (m1 : mem) A c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 v c24 c25 c26 c27,
    rw_cells asegs m1 A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22; C8 v; c24; c25; c26; c27] ->
    cells_size [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22] = 240%nat ->
    cells_size [c24; c25; c26; c27] = 32%nat ->
    exists jlo jhi, rw_cells asegs m1 A [CB 240 jlo; C8 v; CB 32 jhi].
  Proof using.
    intros until c27. intros FR S1 S2.
    pose proof (rw_cells_merge asegs m1 A [] [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22]
                  [C8 v; c24; c25; c26; c27] FR) as M.
    rewrite S1 in M. cbn [app] in M.
    pose proof (rw_cells_merge asegs m1 A [_; C8 v] [c24; c25; c26; c27] [] ltac:(rewrite app_nil_r; exact M)) as M2.
    rewrite S2 in M2. cbn [app] in M2.
    eexists. eexists. exact M2.
  Qed.

  Lemma MEMX_W : forall fc m1, MEMX E fc m1 -> MEMXW fc m1.
  Proof using.
    intros fc m1 H. s2_open_memx H.
    unfold MEMXW. split; [exact FRM|]. split.
    - eapply frw_weak; [exact FR| reflexivity| reflexivity].
    - repeat (split; [first [eassumption | eexists; eassumption]|]). exact TIMG.
  Qed.

  Definition exit_kw (Q : machine_state -> Prop) : Prop :=
    forall err x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
           (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
      s2_errok E err ->
      MEMXW fc m1 ->
      evt asegs Q
        (S2R E 0xcb1dc x1 x5 x6 x7 (e_sp E) (Z_to_bv 64 (e_spa E)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E))
             x21 x22 (Z_to_bv 64 err) x24 x25 x26 x27 x28 x29 x30 x31 F fc m1).

  Lemma exit_k_of_w : forall Q, exit_kw Q -> exit_k E Q.
  Proof using.
    intros Q H. unfold exit_k. intros until m1. intros HE HM. apply H; [exact HE| apply MEMX_W; exact HM].
  Qed.

  Definition s2_xpostw : machine_state -> Prop :=
    fun ms' => exists err x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F' fc' m',
      ms' = MS (mkR (wz 0xcb1fc) (wz (e_spa E)) (e_gp E) (e_tp E) x5 x6 x7 (e_sp E) (wz (e_spa E)) (wz (e_FF E)) (wz 1312) x12 x13 x14 x15 x16 x17
                    x18 (wz (SHA (e_FF E))) (wz (e_FF E)) x21 x22 (wz err) x24 x25 x26 x27 x28 x29 x30 x31)
               F' (wz 0x6738c) fc' None m' (seg_rom asegs)
      /\ s2_errok E err /\ MEMXW fc' m'.

  Lemma s2_exitw : exit_kw s2_xpostw.
  Proof using OK.
    unfold exit_kw. intros until m1. intros HE H.
    s2_env OK.
    destruct H as (FRM & (jlo & jhi & FR) & SAV & GAP & FFW & (nxt & IMPL) & MI & MU & WM & ST & TIMG).
    unfold saved_cells in SAV. unfold impl_cells in IMPL. unfold s2_W in MU.
    grun_to 0xcb1ec%Z.
    zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
    grun_to 0x6738c%Z.
    apply evt_done. unfold s2_xpostw.
    do 24 eexists. split; [reflexivity|]. split; [exact HE|].
    unfold MEMXW. split; [exact FRM|]. split; [eexists; eexists; eassumption|].
    repeat (split; [first [eassumption | eexists; unfold impl_cells; eassumption]|]). exact TIMG.
  Qed.
End ExitW.

Ltac s2_close_memxw :=
  lazymatch goal with
  | |- MEMXW ?E _ ?m =>
      unfold MEMXW; split; [eassumption|]; split;
      [ lazymatch goal with FRh : rw_cells _ m (e_spa E) _ |- _ => eapply frw_weak; [exact FRh| reflexivity| reflexivity] end
      | repeat (split; [first [ unfold saved_cells; eassumption | unfold s2_W; eassumption | eexists; unfold impl_cells; eassumption ]|]); s2_timg_assumption ]
  end.
