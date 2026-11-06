(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_pstr_defs Od_pstr_enc Od_pstr_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Section Loop.
  Variable E : psenv.
  Hypothesis OK : ps_ok E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).
  Local Notation bs := (q_bs E) (only parsing).

  Definition ps_later (p : Z) : Prop :=
    forall p' d', PS bs (q_i E) (q_j E) p' d' -> (p < p')%Z -> ps_headk E d' p'.

  Lemma ps_esc : forall p d xra xs8 xs9 xs10 xs11 mm,
    PS bs (q_i E) (q_j E) p d -> B bs p = 92%Z -> PSINV E mm -> ps_later p ->
    evt psegs (ps_post E)
      (PSS E 0x398c0 xra (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + p)) (Z_to_bv 64 (B bs (p + 1))) xs8 xs9 xs10 xs11 mm).
  Proof using OK.
    intros until mm. intros HPS K INV HK. pose proof INV as INV0. ps_open INV0. pose proof OK as OK0. ps_env OK0.
    pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
    pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
    pose proof (B_range bs (p + 1) BOK) as HB1.
    pose proof (oesc_read mm (B bs (p + 1)) MI HB1) as RE. unfold OT_ESC in RE.
    pose proof (oesc_range (B bs (p + 1))) as HER.
    pstep. pstep. pstep.
    if_cases K2; zify_cond K2.
    -
      eapply evt_eq; [| eapply (ps_fail E OK)]; [s1_st_eq | exact INV].
    -
      pstep. pstep. pstep. pstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        eapply evt_eq; [| eapply (HK (p + 2)%Z (d + 1)%Z)]; [s1_st_eq | apply PS_esc; [exact HPS | exact K] | lia | ps_close] end.
  Qed.

  Lemma ps_head_body : forall p d xra xs7 xs8 xs9 xs10 xs11 mm,
    PS bs (q_i E) (q_j E) p d -> PSINV E mm -> ps_later p ->
    evt psegs (ps_post E) (PSS E 0x397c0 xra (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + p)) xs7 xs8 xs9 xs10 xs11 mm).
  Proof using OK.
    intros until mm. intros HPS INV HK. ps_open INV. pose proof OK as OK0. ps_env OK0.
    pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
    pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
    pose proof (B_range bs p BOK) as HB0.
    pstep. pstep. pstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV1 : PSINV E m1) by ps_close end.
    if_cases K; zify_cond K.
    -
      pose proof (B_range bs (p + 1) BOK) as HB1.
      pstep. pstep.
      if_cases K1; zify_cond K1.
      + eapply evt_eq; [| eapply (ps_esc p d)]; [s1_st_eq | exact HPS | exact K | exact INV1 | exact HK].
      + eapply evt_eq; [| eapply (ps_u E OK p d)]; [s1_st_eq | exact HPS | exact K | exact INV1 | exact HK].
    - pstep.
      if_cases K1; zify_cond K1.
      +
        destruct (PS_quote _ _ _ _ _ HPS K1) as [EJ HDJ].
        eapply evt_eq; [| eapply (ps_epi E OK (wz (SB + (sbo + d))))]; [unfold wz; s1_st_eq | exact INV1 |].
        right. exists (sbo + d)%Z. split; [reflexivity | lia].
      +
        pstep. pstep. pstep.
        eapply evt_eq; [| eapply (HK (p + 1)%Z (d + 1)%Z)]; [s1_st_eq | apply PS_ord; [exact HPS | lia | lia] | lia | exact INV1].
  Qed.

  Theorem ps_loop : forall (f : nat) p d xra xs7 xs8 xs9 xs10 xs11 mm,
    PS bs (q_i E) (q_j E) p d -> (q_j E - p < Z.of_nat f)%Z -> PSINV E mm ->
    evt psegs (ps_post E) (PSS E 0x397c0 xra (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + p)) xs7 xs8 xs9 xs10 xs11 mm).
  Proof using OK.
    induction f as [|f IH]; intros p d xra xs7 xs8 xs9 xs10 xs11 mm HPS HF INV.
    { pose proof (PS_measure _ _ _ _ _ HPS). lia. }
    apply ps_head_body; [exact HPS | exact INV |].
    intros p' d' HPS' HLT. unfold ps_headk. intros. apply IH; [exact HPS' | lia | assumption].
  Qed.

  Theorem ps_body : forall t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv psegs (q_m0 E) -> stk psegs (q_m0 E) (q_lo E) (q_SP E) -> bytes_at psegs (q_m0 E) BUF (padded_bytes bs) ->
    wr_at psegs (q_m0 E) SB (q_CAP E) ->
    evt psegs (ps_post E)
      (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0 t1 t2 (q_s0 E) (q_s1 E) a0 (wz (BUF + q_i E + 1)) (wz (SB + sbo)) (wz 0) a4 a5 a6 a7
               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3 t4 t5 t6)
          (q_F E) (Z_to_bv 64 PS_ENTRY) (q_fc E) None (q_m0 E) (seg_rom psegs)).
  Proof using OK.
    intros t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 MI ST BUFRO SBW.
    unfold PS_ENTRY, wz.
    pose proof (munch_refl (ps_W E) (q_m0 E)) as MU. pose proof (wmono_refl psegs (q_m0 E)) as WM.
    pose proof OK as OK0. ps_env OK0.
    pose proof (proj1 SBW : (0 <= _)%Z) as SBB. pose proof (proj1 (bytes_at_bound _ _ _ _ BUFRO)) as BFB.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := q_m0 E) in MI, ST, BUFRO, SBW, SBB, BFB, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 112%nat ST.
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk] =>
      apply (rw_cells_split_CB psegs m _ [] 112 jk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    do 28 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : PSINV E m1) by ps_close end.
    eapply evt_eq; [| eapply (ps_loop (Z.to_nat (q_j E - q_i E)) (q_i E + 1)%Z 0%Z)];
      [s1_st_eq | apply PS_init; exact CLS | lia | exact INV].
  Qed.
End Loop.

Theorem pstr_spec : pstr_stmt_g psegs PS_ENTRY PS_GTOP.
Proof.
  unfold pstr_stmt_g. intros until bs. intros MI ST ROOM GTOP BOK BUFRO BLO CLS SBW SBLO SBO CAPR SEP.
  set (E := mkPsEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc BUF SB CAP i j sbo lo bs m).
  assert (OK : ps_ok E) by (constructor; cbn; assumption).
  exact (ps_body E OK t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 MI ST BUFRO SBW).
Qed.
