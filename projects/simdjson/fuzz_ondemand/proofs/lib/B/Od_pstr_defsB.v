(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Sj_stage1_kit Od_tables Od_pstr_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Export Sj_akit Sj_num_amem Od_pstr_tabB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Definition PSB_ENTRY : Z := 0xd2144.
Definition PSB_GTOP : Z := 0x679000.

Definition psb_W (sp : word) (SB sbo i j : Z) : list ivl :=
  [(bv_unsigned sp - PSTR_FRAME, bv_unsigned sp); (SB + sbo, SB + sbo + (j - i))]%Z.

Definition pstrb_stmt_g (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BUF SB CAP i j sbo lo : Z) (bs : list Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo + PSTR_FRAME <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_ok bs -> bytes_at bsegs m BUF (padded_bytes bs) -> (BUF + blen bs + 64 <= lo)%Z ->
  closes bs (i + 1) j ->
  wr_at bsegs m SB CAP -> (SB + CAP <= lo)%Z -> (0 <= sbo)%Z -> (sbo + (j - i) <= CAP)%Z ->
  (BUF + blen bs + 64 <= SB \/ SB + CAP <= BUF)%Z ->
  ro_cells bsegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  (forall m', munch (psb_W sp SB sbo i j) m m' -> wmono bsegs m m' -> shz m' BUF (blen bs + 12)) ->
  (forall m', munch (psb_W sp SB sbo i j) m m' -> wmono bsegs m m' -> shz m' SB CAP) ->
  (forall m', munch (psb_W sp SB sbo i j) m m' -> wmono bsegs m m' -> shz m' BT_DIG 3544) ->
  (forall m', munch (psb_W sp SB sbo i j) m m' -> wmono bsegs m m' -> shz m' BT_ESC 256) ->
  (0 < BUF)%Z -> (0 < SB)%Z ->
  evt bsegs (pstr_post_g bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB CAP sbo i j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (BUF + i + 1)) (wz (SB + sbo)) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Record psb_ok (E : psenv) : Prop := mkPsbOk {
  pb_ok : ps_ok_g PSB_GTOP E;
  pb_buf : (0 < q_BUF E)%Z;
  pb_sb : (0 < q_SB E)%Z }.
Notation psb_post E := (ps_post_g bsegs E).

Record psb_shz (E : psenv) : Prop := mkPsaShz {
  pz_buf : forall m', munch (ps_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' (q_BUF E) (q_len E + 12);
  pz_sb : forall m', munch (ps_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' (q_SB E) (q_CAP E);
  pz_dig : forall m', munch (ps_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' BT_DIG 3544;
  pz_esc : forall m', munch (ps_W E) (q_m0 E) m' -> wmono bsegs (q_m0 E) m' -> shz m' BT_ESC 256
}.

Definition PSB_K0 : cell := C8 (Z_to_bv 64 18446744073709495296).
Definition psb_frame (E : psenv) (c0 : cell) : list cell :=
  [c0; C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E); C8 (q_s3 E);
   C8 (q_s2 E); C8 (q_s1 E); C8 (q_s0 E); C8 (q_ra E)].

Definition PSBINV (E : psenv) (mm : mem) : Prop :=
  rw_cells bsegs mm (q_SP E + -112) (psb_frame E PSB_K0) /\
  bytes_at bsegs mm (q_BUF E) (padded_bytes (q_bs E)) /\
  wr_at bsegs mm (q_SB E) (q_CAP E) /\
  mem_inv bsegs mm /\ munch (ps_W E) (q_m0 E) mm /\ wmono bsegs (q_m0 E) mm /\
  stk bsegs mm (q_lo E) (q_SP E + -112).

Ltac psb_open H :=
  destruct H as (FR & BUFRO & SBW & MI & MU & WM & ST);
  unfold psb_frame, PSB_K0 in FR; unfold PSTR_FRAME in MU;
  let SBB := fresh "SBB" in pose proof (proj1 SBW : (0 <= _)%Z) as SBB;
  let BFB := fresh "BFB" in pose proof (proj1 (bytes_at_bound _ _ _ _ BUFRO)) as BFB.
Ltac psb_close :=
  lazymatch goal with
  | |- PSBINV _ _ =>
      unfold PSBINV, psb_frame, PSB_K0, PSTR_FRAME;
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac psb_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let BOK := fresh "BOK" in let BLO := fresh "BLO" in let CLS := fresh "CLS" in
  let SBLO := fresh "SBLO" in let SBO := fresh "SBO" in let CAPR := fresh "CAPR" in let SEP := fresh "SEP" in
  let OKg := fresh "OKg" in let BUF1 := fresh "BUF1" in let SB1 := fresh "SB1" in
  destruct OK as [OKg BUF1 SB1];
  destruct OKg as [ROOM GTOP BOK BLO CLS SBLO SBO CAPR SEP];
  unfold PSTR_FRAME, PSB_GTOP in *;
  lazymatch goal with E : psenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let PBL := fresh "PBL" in pose proof (padded_bytes_blen (q_bs E)) as PBL;
    let CB0 := fresh "CB0" in pose proof (closes_bounds _ _ _ CLS) as CB0
  end.

Ltac psb_shzp SHZ :=
  let ZB := fresh "ZBUF" in let ZS := fresh "ZSB" in let ZD := fresh "ZDIG" in let ZE := fresh "ZESC" in
  pose proof (pz_buf _ SHZ) as ZB; pose proof (pz_sb _ SHZ) as ZS; pose proof (pz_dig _ SHZ) as ZD; pose proof (pz_esc _ SHZ) as ZE;
  unfold BT_DIG, BT_ESC in ZD, ZE.

Notation PSB E pc xra xs0 xs1 xa0 xa1 xa2 xa4 xa5 xa6 xs3 mm :=
  (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) (Z_to_bv 64 2) (Z_to_bv 64 117) (Z_to_bv 64 (-2)) xs0 xs1
           xa0 xa1 xa2 (Z_to_bv 64 0) xa4 xa5 xa6 (Z_to_bv 64 92)
           (Z_to_bv 64 34) xs3 (Z_to_bv 64 146304) (Z_to_bv 64 55296) (Z_to_bv 64 23669) (Z_to_bv 64 127) (Z_to_bv 64 65533) (Z_to_bv 64 56320)
           (Z_to_bv 64 18446744073709405311) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)) (Z_to_bv 64 4))
      (q_F E) (Z_to_bv 64 pc) (q_fc E) None mm (seg_rom bsegs)).

Definition psb_res (E : psenv) (r : word) : Prop :=
  r = wz 0 \/ exists sbo', r = wz (q_SB E + sbo') /\ (q_sbo E <= sbo' <= q_sbo E + (q_j E - q_i E - 1))%Z.

Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof. intros x H. apply zb_lxor_ones. lia. Qed.
Ltac utrap := let G := fresh "UG" in if_cases G; zify_cond G; [exfalso; rewrite ?lxor_ones64 in G by lia; lia|]; try clear G.
Ltac uok := let G := fresh "UG" in if_cases G; zify_cond G; [|exfalso; rewrite ?lxor_ones64 in G by lia; lia]; try clear G.
Ltac pa := zstep; anorm; psnorm; ps_store_done_wr.

Section Exits.
  Variable E : psenv.
  Hypothesis OK : psb_ok E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).

  Lemma psb_epi : forall r xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSBINV E mm -> psb_res E r ->
    evt bsegs (psb_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 r xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0xd28b8) (q_fc E) None mm (seg_rom bsegs)).
  Proof using OK.
    intros until mm. intros INV RES. psb_open INV. pose proof OK as OK0. psb_env OK0.
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

  Lemma psb_fail : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSBINV E mm ->
    evt bsegs (psb_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0xd28b4) (q_fc E) None mm (seg_rom bsegs)).
  Proof using OK.
    intros until mm. intros INV.
    zstep.
    eapply evt_eq; [| eapply (psb_epi (wz 0))]; [s1_st_eq | exact INV | left; reflexivity].
  Qed.

  Definition psb_headk (d' pn : Z) : Prop :=
    forall xra xs0 xs1 xa0 xa4 xa5 xa6 xs3 mm', PSBINV E mm' ->
      evt bsegs (psb_post E) (PSB E 0xd2200 xra xs0 xs1 xa0 (Z_to_bv 64 (BUF + pn)) (Z_to_bv 64 (SB + sbo + d')) xa4 xa5 xa6 xs3 mm').

  Lemma psb_adv : forall d w pn xra xs0 xs1 xa4 xa5 xa6 xs3 mm,
    PSBINV E mm -> psb_headk (d + w) pn ->
    evt bsegs (psb_post E) (PSB E 0xd21f8 xra xs0 xs1 (Z_to_bv 64 (BUF + pn)) (Z_to_bv 64 w) (Z_to_bv 64 (SB + sbo + d)) xa4 xa5 xa6 xs3 mm).
  Proof using OK.
    intros until mm. intros INV HK.
    zstep. zstep.
    eapply evt_eq; [| eapply HK]; [s1_st_eq | exact INV].
  Qed.

  Lemma psb_adv1 : forall d pn xra xs0 xs1 xa1 xa4 xa5 xa6 xs3 mm,
    PSBINV E mm -> psb_headk (d + 1) pn ->
    evt bsegs (psb_post E) (PSB E 0xd21f4 xra xs0 xs1 (Z_to_bv 64 (BUF + pn)) xa1 (Z_to_bv 64 (SB + sbo + d)) xa4 xa5 xa6 xs3 mm).
  Proof using OK.
    intros until mm. intros INV HK.
    zstep.
    eapply evt_eq; [| eapply (psb_adv d 1 pn)]; [s1_st_eq | exact INV | exact HK].
  Qed.
End Exits.
