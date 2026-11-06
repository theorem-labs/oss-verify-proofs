(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its addresses changed; 1141 of its 1278 lines of code are new or changed and 3098 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P12.v, with its module paths and module names changed; 147 of its 286 lines of code are new or changed and 1139 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P12.v blob 52985bf47a6f at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives P12.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type
   is the type of P12.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)
(* The footprint twins of Seg/P12.v p12_evt_a (0x81c84-0x81ce0: the two instrumented checks of the "?" string and
   the eight frame-shadow stores), p12_evt_b0 (0x81ce0 -> 0x82b04, the loop is not entered) and p12_evt_b1
   (0x81ce0-0x81d3c, the twelve spill stores and four spill loads). None of the three calls a routine, so each
   footprint premise comes from the run's own premises:
   - p12_evt_a: the two shadow bytes its checks load (the addresses its ov_read_bytes premises name), the two
     string bytes at QMARK and QMARK + 1, and the sixteen frame-shadow bytes at SF + 370 its rw_cells premise
     names (the eight one-byte stores lie in [SF + 370, SF + 386));
   - p12_evt_b0: none (one branch, no access);
   - p12_evt_b1: the three spill blocks its rw_cells premises name, [A + 48, A + 136), [A + 192, A + 256) and
     [A + 32, A + 40).
   p12F_join / p12F_chk are P12.v's p12_join / p12_chk with evtF in place of evt; the scripts are unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs P12.
(* Last: StepF's step / if_true / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LMS (lib.Lib's MState). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* P12.v:771 p12_addv, copied here: it is declared inside P12.v's Section S, so it does not reach this file. *)
Ltac p12F_addv :=
  first [ reflexivity
        | (rewrite LMS.lit_add_lit; reflexivity)
        | (rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap;
           rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r; reflexivity) ].

(* ---- P12.v's p12_join / p12_chk, with evtF in place of evt ---- *)

Ltac p12F_join G :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (getr R (Z_to_bv 5 12)))
  end.

Ltac p12F_chk k OK c :=
  step; step; step; step;
  unfold sxb; rewrite (RcAsanLib.rc_eqb0_signed (bv_signed k)) by (pose proof (RcAsanLib.rc_byte_signed k); lia);
  lazymatch goal with
  | |- ExecF.evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?Bc) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word,
                ExecF.evtF segs RNG Q (MS (bvmap_set (Z_to_bv 5 12) rr R) F Bc fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ p12F_join G
        | step; step;
          rewrite (RcAsanLib.rc_lts_signed c (bv_signed k))
            by (pose proof (RcAsanLib.rc_byte_signed k); lia);
          replace (c <? bv_signed k) with true
            by (symmetry; apply Z.ltb_lt; let O := fresh "O" in destruct OK as [O|O]; lia);
          p12F_join G ]
      | intros ?; simp_regs ]
  end.

(* ---- 0x81c84 - 0x81ce0 ---- *)

Lemma p12_evt_a_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SF : Z) (kb : byte) (junk : list byte),
    a0 = Z_to_bv 64 QMARK -> s10 = Z_to_bv 64 0x7fff8000 -> s3 = Z_to_bv 64 SF ->
    ov_read_bytes rsegs m (wa (QMARK / 8 + 0x7fff8000)) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa ((QMARK + 1) / 8 + 0x7fff8000)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ 0 < bv_signed kb) ->
    (bv_signed kb = 0 \/ 1 < bv_signed kb) ->
    ov_read_bytes rsegs m (wa QMARK) 1 = Some [Z_to_bv 8 63] ->
    ov_read_bytes rsegs m (wa (QMARK + 1)) 1 = Some [Z_to_bv 8 0] ->
    rw_cells rsegs m (SF + 370) [CB 16 junk] ->
    ExecF.rng RNG (QMARK / 8 + 0x7fff8000) 1 ->
    ExecF.rng RNG ((QMARK + 1) / 8 + 0x7fff8000) 1 ->
    ExecF.rng RNG QMARK 1 ->
    ExecF.rng RNG (QMARK + 1) 1 ->
    ExecF.rng RNG (SF + 370) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' s11' : word) (m' : word -> option byte) (sh16 : list byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81ce0) fc None m' (seg_rom rsegs) /\
         munch [(SF + 370, SF + 386)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (SF + 370) sh16 /\ length sh16 = 16%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c84) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m SF kb junk -> -> -> HK0 HK1 OK0 OK1 HQ0 HQ1 HC RK0 RK1 RQ0 RQ1 RSH.
  unfold QMARK in *.
  pose proof (munch_refl [(SF + 370, SF + 386)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  p12F_chk kb OK0 0.      (* 81c84 srli; 81c88 add; 81c8c lb; 81c90 bnez (slow path 82bfc / 82c00) *)
  step. step. step.       (* 81c94 lbu a1,0(a0); 81c98 li a2,63; 81c9c bne a1,a2,82bf4 *)
  rewrite p12_zxb63. if_false.
  step.                   (* 81ca0 addi a0,a0,1 *)
  p12F_chk kb OK1 1.      (* 81ca4 srli; 81ca8 add; 81cac lb; 81cb0 bnez (slow path 82c08 / 82c0c) *)
  step. step.             (* 81cb4 lbu a0,0(a0); 81cb8 bnez a0,82bf4 *)
  rewrite p12_zxb0. if_false.
  step.                   (* 81cbc li s11,-8 *)
  step. step. step. step. step. step. step. step.  (* 81cc0 .. 81cdc: the eight sb s11,K(s3) *)
  apply ExecF.evtF_done.
  destruct (p12_cells_bytes _ _ _ HC) as (HB & HL).
  do 6 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact HB | exact HL].
Qed.

Lemma p12_evt_a_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SF : Z) (kb : byte) (junk : list byte),
    a0 = Z_to_bv 64 QMARK -> s10 = Z_to_bv 64 0x7fff8000 -> s3 = Z_to_bv 64 SF ->
    ov_read_bytes rsegs m (wa (QMARK / 8 + 0x7fff8000)) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa ((QMARK + 1) / 8 + 0x7fff8000)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ 0 < bv_signed kb) ->
    (bv_signed kb = 0 \/ 1 < bv_signed kb) ->
    ov_read_bytes rsegs m (wa QMARK) 1 = Some [Z_to_bv 8 63] ->
    ov_read_bytes rsegs m (wa (QMARK + 1)) 1 = Some [Z_to_bv 8 0] ->
    rw_cells rsegs m (SF + 370) [CB 16 junk] ->
    LE.evt rsegs
      (fun ms' => exists (a0' a1' a2' s11' : word) (m' : word -> option byte) (sh16 : list byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81ce0) fc None m' (seg_rom rsegs) /\
         munch [(SF + 370, SF + 386)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (SF + 370) sh16 /\ length sh16 = 16%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c84) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m SF kb junk E0 E10 E3 HK0 HK1 OK0 OK1 HQ0 HQ1 HC.
  destruct (p12_cells_bytes _ _ _ HC) as (HB & HL).
  pose proof (bytes_at_bound rsegs m (SF + 370) (cells_bytes [CB 16 junk]) HB) as HSFb.
  rewrite HL in HSFb. cbn [cells_size csize] in HSFb.
  eapply ExecF.evtF_evt.
  apply (p12_evt_a_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 Fr fc m SF kb junk); try assumption.
  all: apply ExecF.rng_all; cbv [QMARK]; first [ lia | (Z.div_mod_to_equations; lia) ].
Qed.

(* ---- 0x81ce0 -> 0x82b04 ---- *)

Lemma p12_evt_b0_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned s9 = 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ce0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m Hs9.
  step. if_true.
  apply ExecF.evtF_done. reflexivity.
Qed.

Lemma p12_evt_b0_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned s9 = 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ce0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m Hs9.
  eapply ExecF.evtF_evt, (p12_evt_b0_F ExecF.RNG_all); exact Hs9.
Qed.

(* ---- 0x81ce0 - 0x81d3c ---- *)

Lemma p12_evt_b1_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f v o p : Z)
         (junk1 junk0 junk2 : list byte),
    s1 = Z_to_bv 64 A -> bv_unsigned s9 <> 0 ->
    rw_cells rsegs m (A + 48) [CB 88 junk1] ->
    rw_cells rsegs m (A + 192)
      [C8 (Z_to_bv 64 f); CB 8 junk0; C8 (Z_to_bv 64 v); CB 32 junk2; C8 (Z_to_bv 64 o)] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 p)] ->
    ExecF.rng RNG (A + 48) 88 ->
    ExecF.rng RNG (A + 192) 64 ->
    ExecF.rng RNG (A + 32) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte) (bs88 : list byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9
                       s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81d40) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 120); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 48) bs88 /\ length bs88 = 88%nat /\
         q64 m' (A + 104) 0 /\ q64 m' (A + 112) 0 /\
         q64 m' (A + 128) (v + 4) /\
         q64 m' (A + 64) (o + 4) /\ q64 m' (A + 72) (o + 10) /\
         q64 m' (A + 80) (f + 15) /\ q64 m' (A + 88) (f + 19) /\ q64 m' (A + 96) (f + 8) /\
         q64 m' (A + 48) (p + 10) /\ q64 m' (A + 56) (p + 9))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ce0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f v o p junk1 junk0 junk2 -> Hs9 HC1 HC2 HC3 R48 R192 R32.
  pose proof (munch_refl [(A + 48, A + 120); (A + 128, A + 136)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.                                  (* 81ce0 beqz s9,82b04 *)
  step.                                            (* 81ce4 li s5,0 *)
  step. step.                                      (* 81ce8 sd zero,112(s1); 81cec sd zero,104(s1) *)
  step. step. step. step. step. step. step.        (* 81cf0 ld a0,192(s1) .. 81d08 sd a0,80(s1) *)
  step. step. step. step. step.                    (* 81d0c ld a0,248(s1) .. 81d1c sd a0,64(s1) *)
  step. step. step.                                (* 81d20 ld a0,208(s1) .. 81d28 sd a0,128(s1) *)
  step. step. step. step. step.                    (* 81d2c ld a0,32(s1) .. 81d3c sd a0,48(s1) *)
  apply ExecF.evtF_done.
  destruct (p12_cells_bytes _ _ _ HC1) as (HB & HL).
  do 4 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact HB|]. split; [exact HL|].
  split.
  { replace (A + 104) with (A + 48 + Z.of_nat 56) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 56%nat); [exact HC1 | reflexivity | vm_compute; reflexivity]. }
  split.
  { replace (A + 112) with (A + 48 + Z.of_nat 64) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 64%nat); [exact HC1 | reflexivity | vm_compute; reflexivity]. }
  split.
  { replace (A + 128) with (A + 48 + Z.of_nat 80) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 80%nat); [exact HC1 | reflexivity | p12F_addv]. }
  split.
  { replace (A + 64) with (A + 48 + Z.of_nat 16) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 16%nat); [exact HC1 | reflexivity | p12F_addv]. }
  split.
  { replace (A + 72) with (A + 48 + Z.of_nat 24) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 24%nat); [exact HC1 | reflexivity | p12F_addv]. }
  split.
  { replace (A + 80) with (A + 48 + Z.of_nat 32) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 32%nat); [exact HC1 | reflexivity | p12F_addv]. }
  split.
  { replace (A + 88) with (A + 48 + Z.of_nat 40) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 40%nat); [exact HC1 | reflexivity | p12F_addv]. }
  split.
  { replace (A + 96) with (A + 48 + Z.of_nat 48) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 48%nat); [exact HC1 | reflexivity | p12F_addv]. }
  split.
  { pose proof (p12_cell_q64 _ (A + 48) _ 0%nat _ (p + 10) HC1 eq_refl) as Hq.
    change (Z.of_nat 0) with 0 in Hq. rewrite Z.add_0_r in Hq. apply Hq. p12F_addv. }
  { replace (A + 56) with (A + 48 + Z.of_nat 8) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 8%nat); [exact HC1 | reflexivity | p12F_addv]. }
Qed.

Lemma p12_evt_b1_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f v o p : Z)
         (junk1 junk0 junk2 : list byte),
    s1 = Z_to_bv 64 A -> bv_unsigned s9 <> 0 ->
    rw_cells rsegs m (A + 48) [CB 88 junk1] ->
    rw_cells rsegs m (A + 192)
      [C8 (Z_to_bv 64 f); CB 8 junk0; C8 (Z_to_bv 64 v); CB 32 junk2; C8 (Z_to_bv 64 o)] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 p)] ->
    LE.evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte) (bs88 : list byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9
                       s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81d40) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 120); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 48) bs88 /\ length bs88 = 88%nat /\
         q64 m' (A + 104) 0 /\ q64 m' (A + 112) 0 /\
         q64 m' (A + 128) (v + 4) /\
         q64 m' (A + 64) (o + 4) /\ q64 m' (A + 72) (o + 10) /\
         q64 m' (A + 80) (f + 15) /\ q64 m' (A + 88) (f + 19) /\ q64 m' (A + 96) (f + 8) /\
         q64 m' (A + 48) (p + 10) /\ q64 m' (A + 56) (p + 9))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ce0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f v o p junk1 junk0 junk2 E1 Hs9 HC1 HC2 HC3.
  destruct (p12_cells_bytes _ _ _ HC1) as (HB1 & HL1).
  destruct (p12_cells_bytes _ _ _ HC2) as (HB2 & HL2).
  destruct (p12_cells_bytes _ _ _ HC3) as (HB3 & HL3).
  pose proof (bytes_at_bound rsegs m (A + 48) _ HB1) as Hb1. rewrite HL1 in Hb1. cbn [cells_size csize] in Hb1.
  pose proof (bytes_at_bound rsegs m (A + 192) _ HB2) as Hb2. rewrite HL2 in Hb2. cbn [cells_size csize] in Hb2.
  pose proof (bytes_at_bound rsegs m (A + 32) _ HB3) as Hb3. rewrite HL3 in Hb3. cbn [cells_size csize] in Hb3.
  eapply ExecF.evtF_evt.
  apply (p12_evt_b1_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 Fr fc m A f v o p junk1 junk0 junk2); try assumption.
  all: apply ExecF.rng_all; lia.
Qed.

(* ---- The pins: each *_of_F states P12's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion). None of the three runs calls a routine, so no corollary takes a premise in place of one. *)
Example p12_evt_a_of_F_verbatim : True.
Proof.
  let a := type of P12.p12_evt_a in let b := type of p12_evt_a_of_F in constr_eq a b.
  exact I.
Qed.

Example p12_evt_b0_of_F_verbatim : True.
Proof.
  let a := type of P12.p12_evt_b0 in let b := type of p12_evt_b0_of_F in constr_eq a b.
  exact I.
Qed.

Example p12_evt_b1_of_F_verbatim : True.
Proof.
  let a := type of P12.p12_evt_b1 in let b := type of p12_evt_b1_of_F in constr_eq a b.
  exact I.
Qed.
