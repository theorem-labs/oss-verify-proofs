(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v; 143 of its 279 lines of code are new or changed and 1661 lines of the source are left out. *)
(* lib/A/Prog/Seg/R6Fs.v -- the SPLIT of segment R6's run at the call of reac_ctrl_build_as (0x815e8), in footprint
   form.  Written by a Theorem Labs lane (stage seg_R6, lib/A/ACtlG/R6.v); single writer.  rule 24: no
   function proved (a segment run split; proves no function, kind: segment lemma).

   PROVENANCE.  Image A = fuzz_ctrl.asan, libreac v1.9.0 (pinned
   (internal path) sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d), FACTS ed6b6b7b0ab, PAU pau-libreac-v190.
   Source: Seg/R6.v (r6_evt :69, its script :144-205) and a Theorem Labs lane's Seg/R6F.v (r6_evt_F :47, whose script
   :161-176 is the same eight steps under StepF).  Tools: lib/Lib/StepF.v, lib/Lib/ExecF.v, The Rocq Prover 9.2.

   WHY A SPLIT.  reac_ctrl_build_as is one of the eight cgif-form fake-stack callees (split rule (a), a Theorem Labs lane
   04:01Z): the walk consumes its call through a Theorem Labs lane's caller-journal spec treac_ctrl_build_as_spec
   (lib/A/Prog/C_reac_ctrl_build_as.v), not through the plain / footprint contract that R6.r6_evt / R6F.r6_evt_F
   take as their first premise.  So the glue lifts only the stretch BEFORE the call and applies the spec at the
   callee entry.  The call's return address 0x815ec IS the exit cut (Inv_A815ec_at), so there is NO stretch after
   the call and no r6_evt_post_F.  Shape: segF-v19-spec.md (a working note, not in this delivery), with the
   NARROWED-STRETCH rule (a Theorem Labs lane via a Theorem Labs lane, 04:23Z / 04:37Z).

   THE LEMMAS
   - r6_evt_pre_Fs: the narrowed stretch.  0x815cc -> the callee entry 0x848ac with ra = 0x815ec: the four spill
     loads ld a1,112(s1) / ld a3,168(s1) / ld a4,104(s1) / ld a5,96(s1), mv a2,s7, li a6,0, li a7,0 and the jal.
     It carries ONLY the premises these eight steps use: s1 = A, A's two bounds (the ld address arithmetic), the
     four spill bytes, and one rng premise per spill load (the stretch's only data accesses; a jal and an
     instruction fetch are not accesses, ExecF.v:98-101).  Post: the callee-entry state, every register but
     ra / a1 / a3-a7 unchanged (a2 := s7 by name), memory unchanged.
   - r6_evt_pre_F: the full-premise pre-stretch of segF-v19-spec.md (a working note, not in this delivery) (R6.r6_evt's binders and premises with
     its callee-contract premise dropped, RNG first, the four rng premises appended, the same conclusion as
     r6_evt_pre_Fs), re-derived FROM r6_evt_pre_Fs (it is the `_pre_F_of_Fs` of the narrowed-stretch rule).
   - r6_evt_of_pre_post: R6.r6_evt's statement, verbatim, re-derived from r6_evt_pre_F at ExecF.RNG_all and the
     PLAIN callee contract BA.reac_ctrl_build_as_contract (R6.r6_evt's own first premise), with R6.v's own
     after-call script (R6.v:164-205).  No post stretch exists.
   - r6_evt_of_pre_post_verbatim: the pin, by constr_eq (syntactic), against the type of R6.r6_evt.

   Footprint rows: R6Fs.rng.tsv beside this file.  R6.v and R6F.v are unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcPorts RcBox RcSynth RcSynthLib RcLay
  RcFin RcFinLib RcEmit RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_build_as_c reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
(* The segment file and a Theorem Labs lane's footprint twin. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R6F.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* ---- the narrowed stretch: 0x815cc -> reac_ctrl_build_as's entry 0x848ac (= BA.REAC_CTRL_BUILD_AS,
   reac_ctrl_build_as_c.v:14; R6.v's step comment says 847e4), ra = 0x815ec ---- *)
Lemma r6_evt_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A mdv d : Z),
    s1 = Z_to_bv 64 A ->
    0 <= A -> A + 176 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 0x1234)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 0x21140)) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 mdv)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 d)) ->
    ExecF.rng RNG (A + 96) 8 ->
    ExecF.rng RNG (A + 104) 8 ->
    ExecF.rng RNG (A + 112) 8 ->
    ExecF.rng RNG (A + 168) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a3' a4' a5' a6' a7' : word),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1' s7 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x848ac) fc None m (seg_rom rsegs)
         /\ ra' = Z_to_bv 64 0x815ec /\ a1' = Z_to_bv 64 mdv /\ a3' = Z_to_bv 64 d /\
         a4' = Z_to_bv 64 0x21140 /\ a5' = Z_to_bv 64 0x1234 /\ a6' = Z_to_bv 64 0 /\ a7' = Z_to_bv 64 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A mdv d -> HA0 HA1 C96 C104 C112 C168 R96 R104 R112 R168.
  (* the spill base does not wrap: solve_accs needs it for the four ld at s1 + 96 / 104 / 112 / 168 (R6F.v:162) *)
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  pose proof (r6_q64_ro m (A + 96) 0x1234 C96) as RW96.
  pose proof (r6_q64_ro m (A + 104) 0x21140 C104) as RW104.
  pose proof (r6_q64_ro m (A + 112) mdv C112) as RW112.
  pose proof (r6_q64_ro m (A + 168) d C168) as RW168.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  step.                                (* 815cc ld a1,112(s1) *)
  step.                                (* 815d0 mv a2,s7 *)
  step.                                (* 815d4 ld a3,168(s1) *)
  step.                                (* 815d8 ld a4,104(s1) *)
  step.                                (* 815dc ld a5,96(s1) *)
  step.                                (* 815e0 li a6,0 *)
  step.                                (* 815e4 li a7,0 *)
  step.                                (* 815e8 jal 848ac reac_ctrl_build_as *)
  apply ExecF.evtF_done.
  do 7 eexists. split; [reflexivity|].
  repeat split; reflexivity.
Qed.

(* ---- the full-premise pre-stretch (segF-v19-spec.md (a working note, not in this delivery)): R6.r6_evt's binders and premises after its callee
   premise, RNG first, the four rng premises appended; re-derived from r6_evt_pre_Fs ---- *)
Lemma r6_evt_pre_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A spv TPv o mdv bb d FS n len Rv : Z) (Eb : bool) (mb nb db sb junk : list byte),
    n = bm_uw mdv (firstn 8 (skipn 16 mb)) ->
    len = 52 + 36 * n ->
    Eb = PB.ba_E n mb bb ->
    Rv = (if PB.ba_go o mdv bb && Eb then len else 0) ->
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv -> tp = Z_to_bv 64 TPv -> s7 = Z_to_bv 64 bb ->
    a0 = Z_to_bv 64 o ->
    0 <= A -> A + 176 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= mdv < 2 ^ 64 -> 0 <= bb <= 6 ->
    0 <= d < 2 ^ 64 -> 0 <= TPv < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 0x1234)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 0x21140)) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 mdv)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 d)) ->
    spv mod 16 = 0 ->
    stk rsegs m (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    bytes_at rsegs m (BA.BA_FR + 72) PB.ba_tbl ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (BA.BA_FR + 72) (BA.BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m 0x21140 sb ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv 0x21140 (0x21140 + 6) ->
    (mdv <> 0 -> mdv mod 8 = 0 /\ mdv + 296 <= 2 ^ 64 /\ length mb = 296%nat /\ bytes_at rsegs m mdv mb /\
                 ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv mdv (mdv + 296)) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2 ^ 64) ->
    (PB.ba_go o mdv bb && Eb = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv o (o + len) /\
       ly_dj o (o + len) (BA.BA_FR + 72) (BA.BA_FR + 240) /\ ly_dj o (o + len) mdv (mdv + 296) /\
       (((bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0) ->
          ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) 0x21140 (0x21140 + 6)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - BA.REAC_CTRL_BUILD_AS_K -> spv <= APPMEM_END ->
    addressable m (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K ->
    addressable m BA.BA_SW 56 -> addressable m (BA.BA_FR + 72) 168 -> addressable m d 6 ->
    addressable m 0x21140 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (0x21140 + 6) /\ app_mem (0x21140 + 7) ->
    (mdv <> 0 -> addressable m mdv 296) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))) ->
    (PB.ba_go o mdv bb && Eb = true ->
       addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (bb = 1 -> addressable m RBM.JOIN_0014 32) ->
    (bb = 2 -> addressable m RBM.JOIN_0013 32) ->
    fp [0%nat; 1%nat] m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
      [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
      [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)] ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    BA.reac_ctrl_build_as_tls m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    (* footprint: the segment's own four spill loads (R6F.v:105-108) *)
    ExecF.rng RNG (A + 96) 8 ->
    ExecF.rng RNG (A + 104) 8 ->
    ExecF.rng RNG (A + 112) 8 ->
    ExecF.rng RNG (A + 168) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a3' a4' a5' a6' a7' : word),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1' s7 a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x848ac) fc None m (seg_rom rsegs)
         /\ ra' = Z_to_bv 64 0x815ec /\ a1' = Z_to_bv 64 mdv /\ a3' = Z_to_bv 64 d /\
         a4' = Z_to_bv 64 0x21140 /\ a5' = Z_to_bv 64 0x1234 /\ a6' = Z_to_bv 64 0 /\ a7' = Z_to_bv 64 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk
    Hn Hlen HEb HRv Es1 Esp Etp Es7 Ea0 HA0 HA1 Ho Hmd Hbb Hd HTP Hspv C96 C104 C112 C168
    H16 ST HBA HBAdj Hdbl HD HDdj Hsbl HS HSdj HM HNM Hobnd HO HMI HAC HSW HHM HAE HAW HSW56 HAWba HAWd HAWs
    HDapp HSapp HMa HNa HOa HJ14 HJ13 HFP HFPN HTLS R96 R104 R112 R168.
  exact (r6_evt_pre_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m A mdv d Es1 HA0 HA1 C96 C104 C112 C168 R96 R104 R112 R168).
Qed.

(* ---- R6.r6_evt re-derived: r6_evt_pre_F at RNG_all, then the PLAIN callee contract at the callee entry and
   R6.v's own after-call script (R6.v:164-205); there is no post stretch (the return pc 0x815ec is the exit cut) ---- *)
Lemma r6_evt_of_pre_post : BA.reac_ctrl_build_as_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A spv TPv o mdv bb d FS n len Rv : Z) (Eb : bool) (mb nb db sb junk : list byte),
    n = bm_uw mdv (firstn 8 (skipn 16 mb)) ->
    len = 52 + 36 * n ->
    Eb = PB.ba_E n mb bb ->
    Rv = (if PB.ba_go o mdv bb && Eb then len else 0) ->
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv -> tp = Z_to_bv 64 TPv -> s7 = Z_to_bv 64 bb ->
    a0 = Z_to_bv 64 o ->
    0 <= A -> A + 176 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= mdv < 2 ^ 64 -> 0 <= bb <= 6 ->
    0 <= d < 2 ^ 64 -> 0 <= TPv < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 0x1234)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 0x21140)) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 mdv)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 d)) ->
    spv mod 16 = 0 ->
    stk rsegs m (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    bytes_at rsegs m (BA.BA_FR + 72) PB.ba_tbl ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (BA.BA_FR + 72) (BA.BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m 0x21140 sb ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv 0x21140 (0x21140 + 6) ->
    (mdv <> 0 -> mdv mod 8 = 0 /\ mdv + 296 <= 2 ^ 64 /\ length mb = 296%nat /\ bytes_at rsegs m mdv mb /\
                 ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv mdv (mdv + 296)) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2 ^ 64) ->
    (PB.ba_go o mdv bb && Eb = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv o (o + len) /\
       ly_dj o (o + len) (BA.BA_FR + 72) (BA.BA_FR + 240) /\ ly_dj o (o + len) mdv (mdv + 296) /\
       (((bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0) ->
          ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) 0x21140 (0x21140 + 6)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - BA.REAC_CTRL_BUILD_AS_K -> spv <= APPMEM_END ->
    addressable m (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K ->
    addressable m BA.BA_SW 56 -> addressable m (BA.BA_FR + 72) 168 -> addressable m d 6 ->
    addressable m 0x21140 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (0x21140 + 6) /\ app_mem (0x21140 + 7) ->
    (mdv <> 0 -> addressable m mdv 296) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))) ->
    (PB.ba_go o mdv bb && Eb = true ->
       addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (bb = 1 -> addressable m RBM.JOIN_0014 32) ->
    (bb = 2 -> addressable m RBM.JOIN_0013 32) ->
    fp [0%nat; 1%nat] m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
      [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
      [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)] ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    BA.reac_ctrl_build_as_tls m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x815ec) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Rv)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x815ec) fc None m' (seg_rom rsegs)
         /\ munch ([(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)] ++ fp_w [0%nat; 1%nat] FS ++
                   [(shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K), shadow_addr spv)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (spv - BA.REAC_CTRL_BUILD_AS_K) spv
         /\ asan_cells m' /\ shadow_rw m'
         /\ addressable m' (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
              [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
              [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)]
         /\ (forall x, o <= x < o + Rv -> exists bx, mrd rsegs m' (wa x) = Some bx)
         /\ (PB.ba_go o mdv bb && Eb = true ->
               bytes_at rsegs m' o (em_fr db sb 0x1234 (Z_to_bv 8 205) (Z_to_bv 8 234) (PB.ba_X mdv mb nb bb) len)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk
    Hn Hlen HEb HRv Es1 Esp Etp Es7 Ea0 HA0 HA1 Ho Hmd Hbb Hd HTP Hspv C96 C104 C112 C168
    H16 ST HBA HBAdj Hdbl HD HDdj Hsbl HS HSdj HM HNM Hobnd HO HMI HAC HSW HHM HAE HAW HSW56 HAWba HAWd HAWs
    HDapp HSapp HMa HNa HOa HJ14 HJ13 HFP HFPN HTLS.
  (* the pre-stretch at RNG_all: the four spill cells lie in [A, A + 176) *)
  eapply evt_cut.
  { eapply ExecF.evtF_evt.
    apply (r6_evt_pre_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk
             Hn Hlen HEb HRv Es1 Esp Etp Es7 Ea0 HA0 HA1 Ho Hmd Hbb Hd HTP Hspv C96 C104 C112 C168
             H16 ST HBA HBAdj Hdbl HD HDdj Hsbl HS HSdj HM HNM Hobnd HO HMI HAC HSW HHM HAE HAW HSW56 HAWba HAWd
             HAWs HDapp HSapp HMa HNa HOa HJ14 HJ13 HFP HFPN HTLS);
      apply ExecF.rng_all; lia. }
  intros ms1 (ra' & a1' & a3' & a4' & a5' & a6' & a7' & Ems1 & -> & -> & -> & -> & -> & -> & ->).
  subst ms1 s1 sp tp s7 a0.
  (* from here: R6.v:164-205, verbatim *)
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  subst Rv Eb len n.
  eapply evt_cut.
  { eapply BUILD with (o := o) (md := mdv) (b := bb) (d := d) (s := 0x21140) (ns := 0)
      (mb := mb) (nb := nb) (db := db) (sb := sb) (junk := junk) (FS := FS).
    all: rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia.
    all: try assumption.
    all: try reflexivity.
    all: try lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1'' & a2' & a3'' & a4'' & a5'' & a6'' & a7'' & t3' & t4' & t5' & t6' & m' &
                  Eq & MU & WM & MI & STp & ACp & SWp & AWp & FPp & _ & HOut).
  subst ms'.
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (Etp : bv_unsigned (Z_to_bv 64 TPv) = TPv) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  rewrite ?Esp in MU. rewrite ?Esp in STp. rewrite ?Esp in AWp.
  rewrite ?Esp, ?Etp in FPp.
  replace (ret_pc (Z_to_bv 64 0x815ec)) with (Z_to_bv 64 0x815ec)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STp|].
  split; [exact ACp|]. split; [exact SWp|]. split; [exact AWp|]. split; [exact FPp|].
  split.
  { intros x Hx. revert Hx.
    destruct (PB.ba_go o mdv bb && PB.ba_E (bm_uw mdv (firstn 8 (skipn 16 mb))) mb bb) eqn:HE;
      intros Hx; [|lia].
    destruct (HOut eq_refl) as (Hb & Hw & _).
    assert (Hmdne : mdv <> 0).
    { apply andb_true_iff in HE as [Hgo _]. unfold PB.ba_go in Hgo.
      apply andb_true_iff in Hgo as [Hg1 _]. apply andb_true_iff in Hg1 as [_ Hg2].
      apply negb_true_iff, Z.eqb_neq in Hg2. exact Hg2. }
    destruct (HM Hmdne) as (_ & _ & Hmbl & _ & _).
    destruct (em_wok_range _ Hw) as (Hnr & _).
    eapply (r6_present m' o _ x).
    + exact Hb.
    + apply r6_emfr_len; [exact Hdbl | exact Hsbl | exact (r6_baX_len mdv mb nb bb Hmbl) | lia].
    + lia. }
  (* the emitted frame: the count word c16 is [A + 96] = 0x1234, loaded into a5 at 0x815dc *)
  intros HE. destruct (HOut HE) as (Hb & _).
  match type of Hb with bytes_at _ _ _ (em_fr _ _ ?c _ _ _ _) =>
    replace c with 0x1234 in Hb by (vm_compute; reflexivity) end.
  exact Hb.
Qed.

(* The pin: r6_evt_of_pre_post states R6.r6_evt's v1.9 text exactly (constr_eq is syntactic, not up to
   conversion), so the split re-derives the segment's run with no weakening. *)
Example r6_evt_of_pre_post_verbatim : True.
Proof.
  lazymatch type of R6.r6_evt with ?T =>
    lazymatch type of r6_evt_of_pre_post with ?U => constr_eq T U end
  end.
  exact I.
Qed.
