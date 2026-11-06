(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Sj_stage1_kit Od_tables Od_pstr_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Definition PS_ENTRY : Z := 0x3970c.
Definition PS_GTOP : Z := 0xab000.
Notation ps_ok := (ps_ok_g PS_GTOP).
Notation ps_post E := (ps_post_g psegs E).

Definition ps_frame (E : psenv) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E); C8 (q_s3 E);
   C8 (q_s2 E); C8 (q_s1 E); C8 (q_s0 E); C8 (q_ra E)].

Definition PSINV (E : psenv) (mm : mem) : Prop :=
  (exists j0, rw_cells psegs mm (q_SP E + -112) (ps_frame E j0)) /\
  bytes_at psegs mm (q_BUF E) (padded_bytes (q_bs E)) /\
  wr_at psegs mm (q_SB E) (q_CAP E) /\
  mem_inv psegs mm /\ munch (ps_W E) (q_m0 E) mm /\ wmono psegs (q_m0 E) mm /\
  stk psegs mm (q_lo E) (q_SP E + -112).

Ltac ps_open H :=
  let j0 := fresh "j0" in
  destruct H as ((j0 & FR) & BUFRO & SBW & MI & MU & WM & ST);
  unfold ps_frame in FR; unfold PSTR_FRAME in MU;
  let SBB := fresh "SBB" in pose proof (proj1 SBW : (0 <= _)%Z) as SBB;
  let BFB := fresh "BFB" in pose proof (proj1 (bytes_at_bound _ _ _ _ BUFRO)) as BFB.
Ltac ps_close :=
  lazymatch goal with
  | |- PSINV _ _ =>
      unfold PSINV, ps_frame, PSTR_FRAME;
      split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac ps_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let BOK := fresh "BOK" in let BLO := fresh "BLO" in let CLS := fresh "CLS" in
  let SBLO := fresh "SBLO" in let SBO := fresh "SBO" in let CAPR := fresh "CAPR" in let SEP := fresh "SEP" in
  destruct OK as [ROOM GTOP BOK BLO CLS SBLO SBO CAPR SEP];
  unfold PSTR_FRAME, PS_GTOP in *;
  lazymatch goal with E : psenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let PBL := fresh "PBL" in pose proof (padded_bytes_blen (q_bs E)) as PBL;
    let CB0 := fresh "CB0" in pose proof (closes_bounds _ _ _ CLS) as CB0
  end.

Notation PSS E pc xra xa0 xa1 xs7 xs8 xs9 xs10 xs11 mm :=
  (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) (Z_to_bv 64 3) (Z_to_bv 64 127) (Z_to_bv 64 1) (Z_to_bv 64 55296) (Z_to_bv 64 23669)
           xa0 xa1 (Z_to_bv 64 92) (Z_to_bv 64 0) (Z_to_bv 64 117) (Z_to_bv 64 1023) (Z_to_bv 64 (-56557568)) (Z_to_bv 64 4)
           (Z_to_bv 64 (-56320)) (Z_to_bv 64 65533) (Z_to_bv 64 56320) (Z_to_bv 64 95738) (Z_to_bv 64 34) xs7 xs8 xs9 xs10 xs11
           (Z_to_bv 64 2047) (Z_to_bv 64 2) (Z_to_bv 64 16) (Z_to_bv 64 80360))
      (q_F E) (Z_to_bv 64 pc) (q_fc E) None mm (seg_rom psegs)).

Definition ps_res (E : psenv) (r : word) : Prop :=
  r = wz 0 \/ exists sbo', r = wz (q_SB E + sbo') /\ (q_sbo E <= sbo' <= q_sbo E + (q_j E - q_i E - 1))%Z.

Section Exits.
  Variable E : psenv.
  Hypothesis OK : ps_ok E.

  Lemma ps_epi : forall r xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSINV E mm -> ps_res E r ->
    evt psegs (ps_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 r xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0x399b0) (q_fc E) None mm (seg_rom psegs)).
  Proof using OK.
    intros until mm. intros INV RES. ps_open INV. pose proof OK as OK0. ps_env OK0.
    do 13 zstep. zstep.
    release_frame FR ST (q_SP E).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      apply evt_done; unfold pstr_post_g; do 15 eexists; exists m1;
      (split; [cbv delta [mkR]; reflexivity|]); unfold PSTR_FRAME;
      (split; [exact RES|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact SBW | exact ST])
    end.
  Qed.

  Lemma ps_fail : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSINV E mm ->
    evt psegs (ps_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0x399ac) (q_fc E) None mm (seg_rom psegs)).
  Proof using OK.
    intros until mm. intros INV.
    zstep.
    eapply evt_eq; [| eapply (ps_epi (wz 0))]; [s1_st_eq | exact INV | left; reflexivity].
  Qed.
End Exits.
