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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Export Od_pstr_tab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Definition pstru_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BUF SB CAP i j sbo lo : Z) (bs : list Z),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + PSTR_FRAME <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_ok bs -> bytes_at segs m BUF (padded_bytes bs) -> (BUF + blen bs + 64 <= lo)%Z ->
  closes bs (i + 1) j ->
  wr_at segs m SB CAP -> (SB + CAP <= lo)%Z -> (0 <= sbo)%Z -> (sbo + (j - i) <= CAP)%Z ->
  (BUF + blen bs + 64 <= SB \/ SB + CAP <= BUF)%Z ->
  (0 < BUF)%Z -> (0 < SB)%Z ->
  evt segs (pstr_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB CAP sbo i j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (BUF + i + 1)) (wz (SB + sbo)) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition PSU_ENTRY : Z := 0x43ba4.
Definition PSU_GTOP : Z := 0xb6000.
Record psu_ok (E : psenv) : Prop := mkPsuOk {
  pu_ok : ps_ok_g PSU_GTOP E;
  pu_buf : (0 < q_BUF E)%Z;
  pu_sb : (0 < q_SB E)%Z }.
Notation psu_post E := (ps_post_g usegs E).

Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof. intros x H. apply zb_lxor_ones. lia. Qed.

Definition psu_frame (E : psenv) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E); C8 (q_s3 E);
   C8 (q_s2 E); C8 (q_s1 E); C8 (q_s0 E); C8 (q_ra E)].

Definition PSUINV (E : psenv) (mm : mem) : Prop :=
  (exists j0, rw_cells usegs mm (q_SP E + -112) (psu_frame E j0)) /\
  bytes_at usegs mm (q_BUF E) (padded_bytes (q_bs E)) /\
  wr_at usegs mm (q_SB E) (q_CAP E) /\
  mem_inv usegs mm /\ munch (ps_W E) (q_m0 E) mm /\ wmono usegs (q_m0 E) mm /\
  stk usegs mm (q_lo E) (q_SP E + -112).

Ltac psu_open H :=
  let j0 := fresh "j0" in
  destruct H as ((j0 & FR) & BUFRO & SBW & MI & MU & WM & ST);
  unfold psu_frame in FR; unfold PSTR_FRAME in MU;
  let SBB := fresh "SBB" in pose proof (proj1 SBW : (0 <= _)%Z) as SBB;
  let BFB := fresh "BFB" in pose proof (proj1 (bytes_at_bound _ _ _ _ BUFRO)) as BFB.
Ltac psu_close :=
  lazymatch goal with
  | |- PSUINV _ _ =>
      unfold PSUINV, psu_frame, PSTR_FRAME;
      split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac psu_env OK :=
  let OKg := fresh "OKg" in let BUF1 := fresh "BUF1" in let SB1 := fresh "SB1" in
  destruct OK as [OKg BUF1 SB1];
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let BOK := fresh "BOK" in let BLO := fresh "BLO" in let CLS := fresh "CLS" in
  let SBLO := fresh "SBLO" in let SBO := fresh "SBO" in let CAPR := fresh "CAPR" in let SEP := fresh "SEP" in
  destruct OKg as [ROOM GTOP BOK BLO CLS SBLO SBO CAPR SEP];
  unfold PSTR_FRAME, PSU_GTOP in *;
  lazymatch goal with E : psenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let PBL := fresh "PBL" in pose proof (padded_bytes_blen (q_bs E)) as PBL;
    let CB0 := fresh "CB0" in pose proof (closes_bounds _ _ _ CLS) as CB0
  end.

Notation PSU E pc xra xs1 xa1 xa2 xs10 xs11 xt4 xt5 mm :=
  (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)) (Z_to_bv 64 4) (Z_to_bv 64 2047) xs1
           (Z_to_bv 64 92) xa1 xa2 (Z_to_bv 64 0) (Z_to_bv 64 2) (Z_to_bv 64 117) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1))
           (Z_to_bv 64 80360) (Z_to_bv 64 55296) (Z_to_bv 64 23669) (Z_to_bv 64 (-56320)) (Z_to_bv 64 65533) (Z_to_bv 64 56320)
           (Z_to_bv 64 18446744073709471255) (Z_to_bv 64 34) xs10 xs11
           (Z_to_bv 64 1023) xt4 xt5 (Z_to_bv 64 127))
      (q_F E) (Z_to_bv 64 pc) (q_fc E) None mm (seg_rom usegs)).

Definition psu_res (E : psenv) (r : word) : Prop :=
  r = wz 0 \/ exists sbo', r = wz (q_SB E + sbo') /\ (q_sbo E <= sbo' <= q_sbo E + (q_j E - q_i E - 1))%Z.

Section Exits.
  Variable E : psenv.
  Hypothesis OK : psu_ok E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).

  Lemma psu_epi : forall r xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSUINV E mm -> psu_res E r ->
    evt usegs (psu_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 r xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0x43f1c) (q_fc E) None mm (seg_rom usegs)).
  Proof using OK.
    intros until mm. intros INV RES. psu_open INV. pose proof OK as OK0. psu_env OK0.
    zstep.
    do 13 zstep. zstep.
    release_frame FR ST (q_SP E).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      apply evt_done; unfold pstr_post_g; do 15 eexists; exists m1;
      (split; [cbv delta [mkR]; reflexivity|]); unfold PSTR_FRAME;
      (split; [exact RES|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact SBW | exact ST])
    end.
  Qed.

  Lemma psu_fail : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSUINV E mm ->
    evt usegs (psu_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0x43f18) (q_fc E) None mm (seg_rom usegs)).
  Proof using OK.
    intros until mm. intros INV.
    zstep.
    eapply evt_eq; [| eapply (psu_epi (wz 0))]; [s1_st_eq | exact INV | left; reflexivity].
  Qed.

  Definition psu_headk (d' pn : Z) : Prop :=
    forall xra xs1 xs10 xs11 xt4 xt5 mm', PSUINV E mm' ->
      evt usegs (psu_post E) (PSU E 0x43c5c xra xs1 (Z_to_bv 64 (BUF + pn)) (Z_to_bv 64 (SB + sbo + d')) xs10 xs11 xt4 xt5 mm').

  Lemma psu_adv : forall d w pn xra xs1 xs11 xt4 xt5 mm,
    PSUINV E mm -> psu_headk (d + w) pn ->
    evt usegs (psu_post E) (PSU E 0x43c54 xra xs1 (Z_to_bv 64 w) (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + pn)) xs11 xt4 xt5 mm).
  Proof using OK.
    intros until mm. intros INV HK.
    zstep. zstep.
    eapply evt_eq; [| eapply HK]; [s1_st_eq | exact INV].
  Qed.

  Lemma psu_adv1 : forall d pn xra xs1 xa1 xs11 xt4 xt5 mm,
    PSUINV E mm -> psu_headk (d + 1) pn ->
    evt usegs (psu_post E) (PSU E 0x43c50 xra xs1 xa1 (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + pn)) xs11 xt4 xt5 mm).
  Proof using OK.
    intros until mm. intros INV HK.
    zstep.
    eapply evt_eq; [| eapply (psu_adv d 1 pn)]; [s1_st_eq | exact INV | exact HK].
  Qed.
End Exits.
