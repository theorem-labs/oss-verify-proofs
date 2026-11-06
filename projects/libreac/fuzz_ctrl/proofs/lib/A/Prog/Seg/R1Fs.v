(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and addresses changed; 2105 of its 2257 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A5.v, with its module paths and addresses changed; 1044 of its 1143 lines of code are new or changed and 2158 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R1F.v; 26 of its 131 lines of code are new or changed and 1038 lines of the source are left out. *)
(* lib/A/Prog/Seg/R1Fs.v -- a NARROWED footprint twin of a Theorem Labs lane's R1F.r1_mode_evt_F (Seg/R1F.v:341), written by
   a Theorem Labs lane's stage lane for the glue of seg_R1_turn (lib/A/ACtlG/R1_turn.v), approved by a Theorem Labs lane
   (2026-10-29 ~04:40Z) under the narrowed-stretch rule (two Theorem Labs lanes, 04:23Z / 04:34Z).
   rule 24: no function proved.  Requires only a Theorem Labs lane's R1F.v and its sources; a Theorem Labs lane's files are not edited.

   THE DEFECT IT NARROWS.  R1F.r1_mode_evt_F states its two footprint premises
     ExecF.rng RNG (pm / 8 + K) 1     and     ExecF.rng RNG pm 1
   UNGUARDED, but the run (0x814a4 -> 0x81b14 / 0x814d0) reads the mode byte pm and its shadow byte only when
   w <> 0 (its own source premises are `w <> 0 -> ov_read_bytes ...`, R1.v:341).  At input length n = 6 (w = 0) the
   walk has pm = in + 6, one byte past the 6-byte input block: no core law makes that byte visible, so the twin cannot
   be instantiated at the walk's footprint ProgBridge.RNG_W (w_H W) on that arm.

   WHAT THIS FILE STATES
   - r1_mode_evt_Fs: r1_mode_evt_F with exactly those two premises guarded by `w <> 0 ->`; binders, other premises
     and post are r1_mode_evt_F's.  Its proof is R1F.v:361-412 with the two guarded hypotheses specialised on the
     w <> 0 arm; on the w = 0 arm the run is the four register-only steps of R1F.v:367-374 (no data access).
   - r1_mode_evt_F_of_Fs: a Theorem Labs lane's r1_mode_evt_F re-derived from r1_mode_evt_Fs (each unguarded premise gives its
     guarded form), with r1_mode_evt_F_of_Fs_verbatim pinning its type to R1F.r1_mode_evt_F's by constr_eq: the
     narrowed twin is provably the same run.
   Footprint rows: R1Fs.rng.tsv. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R1 R1F.
(* Last: StepF's step / mem_after_store (evtF goals) shadow Step's (evt goals), as R1F.v:38 orders them. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Lemma r1_mode_evt_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pm w K : Z) (bm km : byte),
    s6 = Z_to_bv 64 (pm - 1) -> s7 = Z_to_bv 64 pm -> s8 = Z_to_bv 64 w -> s9 = Z_to_bv 64 (w + 1) ->
    s10 = Z_to_bv 64 K ->
    0 < pm -> pm + 2 < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> pm / 8 + K + 1 < 2 ^ 64 ->
    (w <> 0 -> ov_read_bytes rsegs m (wa (pm / 8 + K)) 1 = Some [km]) ->
    (w <> 0 -> bv_signed km = 0 \/ pm mod 8 < bv_signed km) ->
    (w <> 0 -> ov_read_bytes rsegs m (wa pm) 1 = Some [bm]) ->
    (w <> 0 -> ExecF.rng RNG (pm / 8 + K) 1) ->
    (w <> 0 -> ExecF.rng RNG pm 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 22 = Z_to_bv 64 (if w =? 0 then pm else pm + 1) /\
            getr R 25 = Z_to_bv 64 (if w =? 0 then 0 else w - 1)) \/
         (bv_unsigned bm mod 2 = 1 /\ 1 <= w /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                          (Z_to_bv 64 (pm + 1)) (zxb bm) (Z_to_bv 64 w) (Z_to_bv 64 (w - 1)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pm w K bm km -> -> -> -> -> Hpm0 Hpm Hw0 Hw HK Hshm HRk HOKk HRm Rshm Rpm.
  pose proof (rc_byte_signed km) as KRk.
  pose proof (bv_unsigned_in_range 8 bm) as HBM. unfold bv_modulus in HBM. cbn in HBM.
  lazymatch goal with |- ExecF.evtF _ _ ?QQ _ => set (Q := QQ) end.
  step.
  destruct (Z.eq_dec w 0) as [E0|N0].
  - (* w = 0: four register-only steps, no data access (R1F.v:367-374) *)
    subst w. r1_br.
    step. step. step.
    apply ExecF.evtF_done. unfold Q. cbv beta. left. eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; reflexivity.
  - (* w <> 0: R1F.v:375-411, with the guarded footprint premises specialised *)
    r1_br.
    specialize (HRk N0). specialize (HOKk N0). specialize (HRm N0).
    specialize (Rshm N0). specialize (Rpm N0).
    step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit pm) by lia. rewrite rc_shr3.
    step. step. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed km)) by lia.
    enough (KC : forall (x0 x1 : word),
      ExecF.evtF rsegs RNG Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                 (Z_to_bv 64 (pm - 1)) (Z_to_bv 64 pm) (Z_to_bv 64 w) (Z_to_bv 64 (w + 1))
                 (Z_to_bv 64 K) s11
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x814bc) fc None m (seg_rom rsegs))).
    { destruct (Z.eqb_spec (bv_signed km) 0) as [E|E]; cbn [negb]; [apply KC|].
      step. step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit pm) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed (pm mod 8) (bv_signed km)) by lia.
      replace (pm mod 8 <? bv_signed km) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. step. apply KC. }
    intros x0 x1.
    step. step. step.
    unfold zxb. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit (bv_unsigned bm)) by lia.
    rewrite r1_land1 by lia.
    step. step.
    destruct (Z.eq_dec (bv_unsigned bm mod 2) 0) as [Ev|Od].
    + rewrite Ev. r1_br.
      replace (Z_to_bv 64 (pm - 1 + 2)) with (Z_to_bv 64 (pm + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (w + 1 + -2)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
      apply ExecF.evtF_done. unfold Q. cbv beta. left. eexists.
      rewrite (proj2 (Z.eqb_neq w 0) N0).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    + r1_br.
      apply ExecF.evtF_done. unfold Q. cbv beta. right.
      split; [lia|]. split; [lia|].
      replace (Z_to_bv 64 (pm - 1 + 2)) with (Z_to_bv 64 (pm + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (w + 1 + -2)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
      do 2 eexists. reflexivity.
Qed.

(* a Theorem Labs lane's twin, re-derived from the narrowed one: an unguarded footprint premise gives the guarded one. *)
Lemma r1_mode_evt_F_of_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pm w K : Z) (bm km : byte),
    s6 = Z_to_bv 64 (pm - 1) -> s7 = Z_to_bv 64 pm -> s8 = Z_to_bv 64 w -> s9 = Z_to_bv 64 (w + 1) ->
    s10 = Z_to_bv 64 K ->
    0 < pm -> pm + 2 < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> pm / 8 + K + 1 < 2 ^ 64 ->
    (w <> 0 -> ov_read_bytes rsegs m (wa (pm / 8 + K)) 1 = Some [km]) ->
    (w <> 0 -> bv_signed km = 0 \/ pm mod 8 < bv_signed km) ->
    (w <> 0 -> ov_read_bytes rsegs m (wa pm) 1 = Some [bm]) ->
    ExecF.rng RNG (pm / 8 + K) 1 ->
    ExecF.rng RNG pm 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 22 = Z_to_bv 64 (if w =? 0 then pm else pm + 1) /\
            getr R 25 = Z_to_bv 64 (if w =? 0 then 0 else w - 1)) \/
         (bv_unsigned bm mod 2 = 1 /\ 1 <= w /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                          (Z_to_bv 64 (pm + 1)) (zxb bm) (Z_to_bv 64 w) (Z_to_bv 64 (w - 1)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pm w K bm km E6 E7 E8 E9 E10 Hpm0 Hpm Hw0 Hw HK Hshm HRk HOKk HRm Rshm Rpm.
  exact (r1_mode_evt_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m pm w K bm km E6 E7 E8 E9 E10 Hpm0 Hpm Hw0 Hw HK Hshm HRk HOKk HRm
           (fun _ => Rshm) (fun _ => Rpm)).
Qed.

Example r1_mode_evt_F_of_Fs_verbatim : True.
Proof.
  let a := type of R1F.r1_mode_evt_F in let b := type of r1_mode_evt_F_of_Fs in constr_eq a b.
  exact I.
Qed.
