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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Export Sj_akit Sj_num_amem Od_pstr_tabA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Definition PSA_ENTRY : Z := 0xc4a1c.
Definition PSA_GTOP : Z := 0x66b000.

Definition psa_W (sp : word) (SB sbo i j : Z) : list ivl :=
  [(bv_unsigned sp - PSTR_FRAME, bv_unsigned sp); (SB + sbo, SB + sbo + (j - i))]%Z.

Definition pstra_stmt_g (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BUF SB CAP i j sbo lo : Z) (bs : list Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo + PSTR_FRAME <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_ok bs -> bytes_at asegs m BUF (padded_bytes bs) -> (BUF + blen bs + 64 <= lo)%Z ->
  closes bs (i + 1) j ->
  wr_at asegs m SB CAP -> (SB + CAP <= lo)%Z -> (0 <= sbo)%Z -> (sbo + (j - i) <= CAP)%Z ->
  (BUF + blen bs + 64 <= SB \/ SB + CAP <= BUF)%Z ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  (forall m', munch (psa_W sp SB sbo i j) m m' -> wmono asegs m m' -> shz m' BUF (blen bs + 12)) ->
  (forall m', munch (psa_W sp SB sbo i j) m m' -> wmono asegs m m' -> shz m' SB CAP) ->
  (forall m', munch (psa_W sp SB sbo i j) m m' -> wmono asegs m m' -> shz m' AT_DIG 3544) ->
  (forall m', munch (psa_W sp SB sbo i j) m m' -> wmono asegs m m' -> shz m' AT_ESC 256) ->
  evt asegs (pstr_post_g asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB CAP sbo i j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (BUF + i + 1)) (wz (SB + sbo)) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Notation psa_ok := (ps_ok_g PSA_GTOP).
Notation psa_post E := (ps_post_g asegs E).

Record psa_shz (E : psenv) : Prop := mkPsaShz {
  pz_buf : forall m', munch (ps_W E) (q_m0 E) m' -> wmono asegs (q_m0 E) m' -> shz m' (q_BUF E) (q_len E + 12);
  pz_sb : forall m', munch (ps_W E) (q_m0 E) m' -> wmono asegs (q_m0 E) m' -> shz m' (q_SB E) (q_CAP E);
  pz_dig : forall m', munch (ps_W E) (q_m0 E) m' -> wmono asegs (q_m0 E) m' -> shz m' AT_DIG 3544;
  pz_esc : forall m', munch (ps_W E) (q_m0 E) m' -> wmono asegs (q_m0 E) m' -> shz m' AT_ESC 256
}.

Definition psa_frame (E : psenv) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E); C8 (q_s3 E);
   C8 (q_s2 E); C8 (q_s1 E); C8 (q_s0 E); C8 (q_ra E)].

Definition PSAINV (E : psenv) (mm : mem) : Prop :=
  (exists j0, rw_cells asegs mm (q_SP E + -112) (psa_frame E j0)) /\
  bytes_at asegs mm (q_BUF E) (padded_bytes (q_bs E)) /\
  wr_at asegs mm (q_SB E) (q_CAP E) /\
  mem_inv asegs mm /\ munch (ps_W E) (q_m0 E) mm /\ wmono asegs (q_m0 E) mm /\
  stk asegs mm (q_lo E) (q_SP E + -112).

Ltac psa_open H :=
  let j0 := fresh "j0" in
  destruct H as ((j0 & FR) & BUFRO & SBW & MI & MU & WM & ST);
  unfold psa_frame in FR; unfold PSTR_FRAME in MU;
  let SBB := fresh "SBB" in pose proof (proj1 SBW : (0 <= _)%Z) as SBB;
  let BFB := fresh "BFB" in pose proof (proj1 (bytes_at_bound _ _ _ _ BUFRO)) as BFB.
Ltac psa_close :=
  lazymatch goal with
  | |- PSAINV _ _ =>
      unfold PSAINV, psa_frame, PSTR_FRAME;
      split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac psa_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let BOK := fresh "BOK" in let BLO := fresh "BLO" in let CLS := fresh "CLS" in
  let SBLO := fresh "SBLO" in let SBO := fresh "SBO" in let CAPR := fresh "CAPR" in let SEP := fresh "SEP" in
  destruct OK as [ROOM GTOP BOK BLO CLS SBLO SBO CAPR SEP];
  unfold PSTR_FRAME, PSA_GTOP in *;
  lazymatch goal with E : psenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let PBL := fresh "PBL" in pose proof (padded_bytes_blen (q_bs E)) as PBL;
    let CB0 := fresh "CB0" in pose proof (closes_bounds _ _ _ CLS) as CB0
  end.

Ltac psa_shzp SHZ :=
  let ZB := fresh "ZBUF" in let ZS := fresh "ZSB" in let ZD := fresh "ZDIG" in let ZE := fresh "ZESC" in
  pose proof (pz_buf _ SHZ) as ZB; pose proof (pz_sb _ SHZ) as ZS; pose proof (pz_dig _ SHZ) as ZD; pose proof (pz_esc _ SHZ) as ZE;
  unfold AT_DIG, AT_ESC in ZD, ZE.

Notation PSA E pc xra xa0 xa1 xa2 xa4 xa5 xt1 xt3 xs8 xs9 xs11 mm :=
  (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) (Z_to_bv 64 1023) xt1 (Z_to_bv 64 65536) (Z_to_bv 64 146208) (Z_to_bv 64 55296)
           xa0 xa1 xa2 (Z_to_bv 64 0) xa4 xa5 (Z_to_bv 64 92) (Z_to_bv 64 117)
           (Z_to_bv 64 23669) (Z_to_bv 64 (-56320)) (Z_to_bv 64 65533) (Z_to_bv 64 56320) (Z_to_bv 64 2147450880) (Z_to_bv 64 2047)
           xs8 xs9 (Z_to_bv 64 34) xs11 xt3 (Z_to_bv 64 3) (Z_to_bv 64 127) (Z_to_bv 64 1))
      (q_F E) (Z_to_bv 64 pc) (q_fc E) None mm (seg_rom asegs)).

Definition psa_res (E : psenv) (r : word) : Prop :=
  r = wz 0 \/ exists sbo', r = wz (q_SB E + sbo') /\ (q_sbo E <= sbo' <= q_sbo E + (q_j E - q_i E - 1))%Z.

Section Exits.
  Variable E : psenv.
  Hypothesis OK : psa_ok E.

  Lemma psa_epi : forall r xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSAINV E mm -> psa_res E r ->
    evt asegs (psa_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 r xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0xc50ac) (q_fc E) None mm (seg_rom asegs)).
  Proof using OK.
    intros until mm. intros INV RES. psa_open INV. pose proof OK as OK0. psa_env OK0.
    do 13 zstep. zstep.
    release_frame FR ST (q_SP E).
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      apply evt_done; unfold pstr_post_g; do 15 eexists; exists m1;
      (split; [cbv delta [mkR]; reflexivity|]); unfold PSTR_FRAME;
      (split; [exact RES|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact MI|]); (split; [exact SBW | exact ST])
    end.
  Qed.

  Lemma psa_fail : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    PSAINV E mm ->
    evt asegs (psa_post E)
      (MS (mkR xra (Z_to_bv 64 (q_SP E + -112)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          (q_F E) (Z_to_bv 64 0xc50a8) (q_fc E) None mm (seg_rom asegs)).
  Proof using OK.
    intros until mm. intros INV.
    zstep.
    eapply evt_eq; [| eapply (psa_epi (wz 0))]; [s1_st_eq | exact INV | left; reflexivity].
  Qed.
End Exits.
