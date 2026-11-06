(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout Od_pstr_defsB Od_pstr_encB Od_pstr_uB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Section Loop.
  Variable E : psenv.
  Hypothesis OK : psb_ok E.
  Hypothesis SHZ : psb_shz E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).
  Local Notation bs := (q_bs E) (only parsing).

  Definition psb_later (p : Z) : Prop :=
    forall p' d', PS bs (q_i E) (q_j E) p' d' -> (p < p')%Z -> psb_headk E d' p'.

  Lemma psb_esc : forall p d xra xs1 xa4 xa5 xa6 xs3 mm,
    PS bs (q_i E) (q_j E) p d -> B bs p = 92%Z -> PSBINV E mm -> psb_later p ->
    evt bsegs (psb_post E)
      (PSB E 0xd24f8 xra (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) xs1 (Z_to_bv 64 (B bs (p + 1))) (Z_to_bv 64 (BUF + p)) (Z_to_bv 64 (SB + sbo + d))
           xa4 xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    intros until mm. intros HPS K INV HK. pose proof INV as INV0. psb_open INV0. pose proof OK as OK0. psb_env OK0. psb_shzp SHZ.
    pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
    pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
    pose proof (B_range bs (p + 1) BOK) as HB1.
    pose proof (besc_read mm (B bs (p + 1)) MI HB1) as RE. unfold BT_ESC in RE.
    pose proof (oesc_range (B bs (p + 1))) as HER.

    pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa.
    if_cases K2; zify_cond K2.
    -
      eapply evt_eq; [| eapply (psb_fail E OK)]; [s1_st_eq | exact INV].
    -
      pa. pa. if_false. pa. pa. utrap. pa. pa. utrap. pa. pa.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        eapply evt_eq; [| eapply (psb_adv1 E OK d (p + 2)%Z)]; [s1_st_eq | psb_close | ] end.
      apply HK; [apply PS_esc; [exact HPS | exact K] | lia].
  Qed.

  Lemma psb_head_body : forall p d xra xs0 xs1 xa0 xa4 xa5 xa6 xs3 mm,
    PS bs (q_i E) (q_j E) p d -> PSBINV E mm -> psb_later p ->
    evt bsegs (psb_post E) (PSB E 0xd2200 xra xs0 xs1 xa0 (Z_to_bv 64 (BUF + p)) (Z_to_bv 64 (SB + sbo + d)) xa4 xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    intros until mm. intros HPS INV HK. psb_open INV. pose proof OK as OK0. psb_env OK0. psb_shzp SHZ.
    pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
    pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
    pose proof (B_range bs p BOK) as HB0.

    pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. if_false. pa.
    pa.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV1 : PSBINV E m1) by psb_close end.
    if_cases K; zify_cond K.
    -
      pose proof (B_range bs (p + 1) BOK) as HB1.
      pa. pa. utrap. pa. pa. pa. pa. if_false. pa.
      pa.
      if_cases K1; zify_cond K1.
      + eapply evt_eq; [| eapply (psb_esc p d)]; [s1_st_eq | exact HPS | exact K | exact INV1 | exact HK].
      + eapply evt_eq; [| eapply (psb_u E OK SHZ p d)]; [s1_st_eq | exact HPS | exact K | exact INV1 | exact HK].
    -
      pa.
      if_cases K1; zify_cond K1.
      +
        destruct (PS_quote _ _ _ _ _ HPS K1) as [EJ HDJ].
        eapply evt_eq; [| eapply (psb_epi E OK (wz (SB + (sbo + d))))]; [unfold wz; s1_st_eq | exact INV1 |].
        right. exists (sbo + d)%Z. split; [reflexivity | lia].
      +
        pa. pa. utrap. pa. pa. uok.
        eapply evt_eq; [| eapply (psb_adv1 E OK d (p + 1)%Z)]; [s1_st_eq | exact INV1 |].
        apply HK; [apply PS_ord; [exact HPS | lia | lia] | lia].
  Qed.

  Theorem psb_loop : forall (f : nat) p d xra xs0 xs1 xa0 xa4 xa5 xa6 xs3 mm,
    PS bs (q_i E) (q_j E) p d -> (q_j E - p < Z.of_nat f)%Z -> PSBINV E mm ->
    evt bsegs (psb_post E) (PSB E 0xd2200 xra xs0 xs1 xa0 (Z_to_bv 64 (BUF + p)) (Z_to_bv 64 (SB + sbo + d)) xa4 xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    induction f as [|f IH]; intros p d xra xs0 xs1 xa0 xa4 xa5 xa6 xs3 mm HPS HF INV.
    { pose proof (PS_measure _ _ _ _ _ HPS). lia. }
    apply psb_head_body; [exact HPS | exact INV |].
    intros p' d' HPS' HLT. unfold psb_headk. intros. apply IH; [exact HPS' | lia | assumption].
  Qed.

  Theorem psb_body : forall t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv bsegs (q_m0 E) -> stk bsegs (q_m0 E) (q_lo E) (q_SP E) -> bytes_at bsegs (q_m0 E) BUF (padded_bytes bs) ->
    wr_at bsegs (q_m0 E) SB (q_CAP E) ->
    ro_cells bsegs (q_m0 E) g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
    ro_cells bsegs (q_m0 E) g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    evt bsegs (psb_post E)
      (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0 t1 t2 (q_s0 E) (q_s1 E) a0 (wz (BUF + q_i E + 1)) (wz (SB + sbo)) (wz 0) a4 a5 a6 a7
               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3 t4 t5 t6)
          (q_F E) (Z_to_bv 64 PSB_ENTRY) (q_fc E) None (q_m0 E) (seg_rom bsegs)).
  Proof using OK SHZ.
    intros t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 MI ST BUFRO SBW G1 G2.
    unfold PSB_ENTRY, wz. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    pose proof (munch_refl (ps_W E) (q_m0 E)) as MU. pose proof (wmono_refl bsegs (q_m0 E)) as WM.
    pose proof OK as OK0. psb_env OK0.
    pose proof (proj1 SBW : (0 <= _)%Z) as SBB. pose proof (proj1 (bytes_at_bound _ _ _ _ BUFRO)) as BFB.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).
    set (m := q_m0 E) in MI, ST, BUFRO, SBW, SBB, BFB, G1, G2, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 112%nat ST.
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk] =>
      apply (rw_cells_split_CB bsegs m _ [] 112 jk [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.

    zstep. utrap. zstep. utrap.
    do 15 zstep.
    do 5 zstep.
    step. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store end.
    do 7 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : PSBINV E m1) by psb_close end.
    eapply evt_eq; [| eapply (psb_loop (Z.to_nat (q_j E - q_i E)) (q_i E + 1)%Z 0%Z)];
      [s1_st_eq | apply PS_init; exact CLS | lia | exact INV].
  Qed.
End Loop.

Theorem pstrb_spec : pstrb_stmt_g PSB_ENTRY PSB_GTOP.
Proof.
  unfold pstrb_stmt_g. intros until bs. intros MI ST ROOM GTOP BOK BUFRO BLO CLS SBW SBLO SBO CAPR SEP G1 G2 ZB ZS ZD ZE HB1 HS1.
  set (E := mkPsEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc BUF SB CAP i j sbo lo bs m).
  assert (OK : psb_ok E) by (constructor; [constructor; cbn; assumption | exact HB1 | exact HS1]).
  assert (SHZ : psb_shz E) by (constructor; cbn; assumption).
  exact (psb_body E OK SHZ t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 MI ST BUFRO SBW G1 G2).
Qed.
