(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1421 of its 1489 lines of code are new or changed and 943 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R21.v, with its module paths, module names, addresses and numbers changed; 626 of its 715 lines of code are new or changed and 1400 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R21.v 0dfe757c0918 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives R21.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of R21.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of R21's two run lemmas of record (segment-runs-A.tsv row S_R21): r21_latch_next
   (Seg/R21.v:113) and r21_latch_last (Seg/R21.v:145), the latch 0x81924 -> 0x815cc (turn b <= 5) and
   0x81924 -> 0x81990 (turn 6). Both runs touch two regions, both named by their own premises:
   - the eight 1-byte shadow stores, inside the window [SH + 296, SH + 313) of the stk premise: rng RNG (SH+296) 17;
   - the `ld a0,128(s1)` at 0x81950, the 8 bytes of the bytes_at premise at A + 128: rng RNG (A + 128) 8.
   The scripts are R21's, over StepF; r21_sb / r21_latch_pre are restated as r21F_sb / r21F_latch_pre because their
   goal patterns name evt.
   R21's third evt lemma r21_tail_evt (:203) is NOT in the segment list of record for R21 and takes
   strcmp_wrap_contract, which has no _F statement in this tree: blocked, see the lane report. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Norm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R21.
(* Last: StepF's step / if_true (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module LE21 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNr21 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module BZr21 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.BzBridge.
Module B3N21 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Norm.

(* R21.v's r21_sb with the goal pattern of evtF (the only change). *)
Ltac r21F_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r21_stk_store_ok mm (SHv + 296) (SHv + 313) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 296, SHv + 313)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite ?length_le1; cbn [length Z.of_nat]; lia
           | rewrite ?length_le1; cbn [inside length Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 296) (SHv + 313) (SHv + off) bs) in STh;
         [ | lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

(* R21.v's r21_latch_pre with the goal pattern of evtF and r21F_sb (the only changes). *)
Ltac r21F_latch_pre SHv A v HQh STh MUh WMh :=
  step;                                                        (* 81924 li a0,-8 *)
  r21F_sb SHv 300 STh MUh WMh; r21F_sb SHv 306 STh MUh WMh;
  r21F_sb SHv 308 STh MUh WMh; r21F_sb SHv 312 STh MUh WMh;
  r21F_sb SHv 296 STh MUh WMh; r21F_sb SHv 297 STh MUh WMh;
  r21F_sb SHv 298 STh MUh WMh; r21F_sb SHv 299 STh MUh WMh;
  step;                                                        (* 81948 li s8,36 *)
  step;                                                        (* 8194c addiw s7,s7,1 *)
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HQ2 := fresh "HQ2" in let HR := fresh "HR" in
      pose proof (bytes_at_transport rsegs [(SHv + 296, SHv + 313)] _ mm (A + 128) (le8 (Z_to_bv 64 v)) HQh MUh
                    ltac:(cbn [disjoint_from]; rewrite length_le8; cbn [Z.of_nat];
                          split; [right; lia | exact I])) as HQ2;
      pose proof (r21_rdn mm (A + 128) (le8 (Z_to_bv 64 v)) 8%nat HQ2 (length_le8 _)) as HR
  end;
  step;                                                        (* 81950 ld a0,128(s1) *)
  step.                                                        (* 81954 li a1,7 *)

Lemma r21_latch_next_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SH A bz v : Z),
    s3 = Z_to_bv 64 SH -> s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
    stk rsegs m (SH + 296) (SH + 313) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 v)) ->
    (* the eight shadow stores 0x81928 .. 0x81944, inside the window of the stk premise *)
    rng RNG (SH + 296) 17 ->
    (* the `ld a0,128(s1)` at 0x81950, the 8 bytes of the bytes_at premise *)
    rng RNG (A + 128) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815cc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = Z_to_bv 64 (bz + 1) /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 v /\ getr R 24 = Z_to_bv 64 36 /\
         munch [(SH + 296, SH + 313)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SH + 296) (SH + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81924) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SH A bz v -> -> -> Hb HS0 HSA HA ST HQ RSH RLD.
  pose proof (munch_refl [(SH + 296, SH + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  r21F_latch_pre SH A v HQ ST MU WM.

  step.                                  (* 81958 bne s7,a1,815cc *)

  rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit bz) by lia.
    rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_true.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 13 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

Lemma r21_latch_last_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SH A v : Z),
    s3 = Z_to_bv 64 SH -> s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 6 ->
    0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
    stk rsegs m (SH + 296) (SH + 313) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 v)) ->
    (* the eight shadow stores 0x81928 .. 0x81944, inside the window of the stk premise *)
    rng RNG (SH + 296) 17 ->
    (* the `ld a0,128(s1)` at 0x81950, the 8 bytes of the bytes_at premise *)
    rng RNG (A + 128) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81990) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(SH + 296, SH + 313)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SH + 296) (SH + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81924) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SH A v -> -> -> HS0 HSA HA ST HQ RSH RLD.
  pose proof (munch_refl [(SH + 296, SH + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  r21F_latch_pre SH A v HQ ST MU WM.
  step.                                  (* 81958 bne s7,a1,815cc *)
  rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 6) by lia.
    rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_false.
  step.                                  (* 8195c j 81990 *)
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 10 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* R21.r21_latch_next's statement, re-derived from r21_latch_next_F at RNG_all (each rng premise by rng_all; the
   bounds come from 0 <= SH, SH + 313 <= A and A + 136 <= 2 ^ 64). *)
Lemma r21_latch_next_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SH A bz v : Z),
    s3 = Z_to_bv 64 SH -> s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
    stk rsegs m (SH + 296) (SH + 313) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 v)) ->
    LE21.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815cc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = Z_to_bv 64 (bz + 1) /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 v /\ getr R 24 = Z_to_bv 64 36 /\
         munch [(SH + 296, SH + 313)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SH + 296) (SH + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81924) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SH A bz v Es3 Es1 Es7 Hb HS0 HSA HA ST HQ.
  apply (evtF_evt rsegs RNG_all).
  apply (r21_latch_next_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m SH A bz v Es3 Es1 Es7 Hb HS0 HSA HA ST HQ);
    apply rng_all; lia.
Qed.

Lemma r21_latch_last_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SH A v : Z),
    s3 = Z_to_bv 64 SH -> s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 6 ->
    0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
    stk rsegs m (SH + 296) (SH + 313) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 v)) ->
    LE21.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81990) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(SH + 296, SH + 313)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SH + 296) (SH + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81924) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SH A v Es3 Es1 Es7 HS0 HSA HA ST HQ.
  apply (evtF_evt rsegs RNG_all).
  apply (r21_latch_last_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m SH A v Es3 Es1 Es7 HS0 HSA HA ST HQ);
    apply rng_all; lia.
Qed.

(* The pins: each _of_F states R21's text, term for term (constr_eq: syntactic, not up to conversion). *)
Lemma r21_latch_next_of_F_verbatim : True.
Proof.
  let A := type of R21.r21_latch_next in let B := type of r21_latch_next_of_F in constr_eq A B.
  exact I.
Qed.

Lemma r21_latch_last_of_F_verbatim : True.
Proof.
  let A := type of R21.r21_latch_last in let B := type of r21_latch_last_of_F in constr_eq A B.
  exact I.
Qed.

(* ==== Split stretches of R21.r21_tail_evt (Seg/R21.v:203), the tail 0x81990 .. (0x81ac8 / 0x81ac0). It calls the
   strcmp wrapper at 0x81abc, and no strcmp_wrap_contract_F exists in this tree, so the glue splits at the call
   (SPLIT STRETCHES, a Theorem Labs lane 00:45Z / a Theorem Labs lane 00:48Z). callee strcmp_wrap, call pc 0x81abc, return pc 0x81ac0.
   - r21_tail_pre_F: the source run from 0x81990 to the h = 0 end (0x81ac8) OR, when h <> 0, the strcmp_wrap entry
     state (pc = STRCMP_WRAP, ra = 0x81ac0). The callee contract does not appear.
   - r21_tail_post_F: the empty stretch at the return pc 0x81ac0 (the wrapper's post state already is the run's
     exit), its premises the machine facts the source holds right after it applies the contract.
   - r21_tail_evt_of_pre_post: pre_F + post_F at RNG_all + the plain strcmp_wrap_contract re-derive R21.r21_tail_evt;
     the verbatim pin checks no weakening.
   Both stretches are cut from r21_tail_evt's own script; the h <> 0 rng premises are guarded by h <> 0 exactly as
     the source guards the matching reads. ==== *)

Ltac r21F_tail_beq_refl :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; apply r21_eqb_refl]
  end.

Lemma r21_tail_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm w144 : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ shadow_rw m /\ MNr21.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    (* the segment's own reads, one rng per load; the h <> 0 reads guarded by h <> 0 as the source guards them *)
    rng RNG (S5 + 2) 1 -> rng RNG (A + 144) 8 -> rng RNG (A + 112) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1 ->
    rng RNG S5 2 -> rng RNG (mr + 266) 2 -> rng RNG (S5 + 36) 1 ->
    rng RNG (S5 + 22) 2 -> rng RNG (mr + 268) 2 -> rng RNG (S5 + 24) 2 -> rng RNG (mr + 270) 2 ->
    rng RNG (S5 + 26) 2 -> rng RNG (mr + 272) 2 -> rng RNG (mr + 56) 4 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8) ->
    evtF rsegs RNG
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (c5 c6 c7 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 : word),
            ms' = MS (mkR (Z_to_bv 64 0x81ac0) sp gp tp c5 c6 c7 s0 s1
                          (Z_to_bv 64 (S5 + 3)) (Z_to_bv 64 nm) c12 c13 c14 c15 c16 c17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 w144) c28 c29 c30 c31)
                     F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx -> -> -> -> Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    G2 G144 G112 GK266 GK268 GK270 GK272 GK56 GK280 G0 GM266 G36 G22 GM268 G24 GM270 G26 GM272 GM56 GHN.
  step. step. step. if_true.            (* 81990 lbu; 81994 ld s11; 81998 bnez *)
  step. step. step. step. r21_shfix.     (* 819a0 ld; addi 266; srli; add *)
  step. step. step. if_true.           (* 819b0 lb (check); 819b4 lhu; 819b8 beqz *)
  step. step. r21F_tail_beq_refl.        (* 819c0 lhu; 819c4 beq *)
  step. step. if_true.                                         (* 819cc lbu 36; 819d0 bnez *)
  step. step. step. step. r21_shfix.                           (* 819d8 .. 819e4 *)
  step. step. step. if_true.                                   (* 819e8 lb; 819ec lhu 22; 819f0 beqz *)
  step. step. r21F_tail_beq_refl.                               (* 819f8 lhu; 819fc beq *)
  step. step. step. step. r21_shfix.                           (* 81a04 .. 81a10 *)
  step. step. step. if_true.                                   (* 81a14 lb; 81a18 lhu 24; 81a1c beqz *)
  step. step. r21F_tail_beq_refl.                               (* 81a24 lhu; 81a28 beq *)
  step. step. step. step. r21_shfix.                           (* 81a30 .. 81a3c *)
  step. step. step. if_true.                                   (* 81a40 lb; 81a44 lhu 26; 81a48 beqz *)
  step. step. r21F_tail_beq_refl.                               (* 81a50 lhu; 81a54 beq *)
  step. step. step. step. r21_shfix.                           (* 81a5c .. 81a68 *)
  step. step. if_true.                                         (* 81a6c lb; 81a70 beqz *)
  step. step.                           (* 81a78 lw; 81a7c beqz a0,81ac8 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    subst h. apply evtF_done. left. split; [reflexivity|]. eexists. split; [reflexivity|].
    do 10 (split; [reflexivity|]). reflexivity.
  - if_false_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HSW & HMIx & HGOT & HCF1 & HCF2).
    destruct (GHN E0) as (G20 & G280).
    step. step. if_true.                                       (* 81a80 lbu 20; 81a84 bnez *)
    step. step. step. step. r21_shfix.                         (* 81a8c .. 81a98 *)
    step. step. if_true.               (* 81a9c lbu (check); 81aa0 beqz *)
    step. step. step.                  (* 81aa8 ld a1; 81aac addi a0,s5,3; 81ab0 bnez *)
    if_true_by (f_equal negb (r21_eqb0 nm Hnm)).
    step.                               (* 81abc jal wrapper_strcmp, ra = 0x81ac0 *)
    apply evtF_done. right. split; [exact E0|]. do 13 eexists. reflexivity.
Qed.

(* The empty stretch at the return pc 0x81ac0 (STRCMP_WRAP + 4 = 0x81ac0). The premises are the machine-level facts
   the source holds right after it applies the wrapper contract (the destructured existential of the wrapper post
   plus the munch / wmono / stk it derives), each a universally bound variable with its facts. No instruction runs,
   so no rng premise is appended. *)
Lemma r21_tail_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte)
         (sp gp tp s0 s1 s3 s6 s9 s10 : word) (spv lo h w144 : Z),
    h <> 0 ->
    getr R 10 = Z_to_bv 64 0 -> getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 ->
    getr R 9 = s1 -> getr R 19 = s3 -> getr R 26 = s10 -> getr R 27 = Z_to_bv 64 w144 ->
    getr R 22 = s6 -> getr R 25 = s9 ->
    sp = Z_to_bv 64 spv ->
    munch [(spv - STRCMP_WRAP_K, spv)] m m' -> wmono rsegs m m' -> stk rsegs m' lo spv ->
    evtF rsegs RNG
      (fun ms' =>
         (h = 0 /\ exists R0 : bvmap 5 word,
            ms' = MS R0 F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R0 10 = Z_to_bv 64 0 /\
            getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\
            getr R0 19 = s3 /\ getr R0 26 = s10 /\ getr R0 27 = Z_to_bv 64 w144 /\
            getr R0 22 = s6 /\ getr R0 25 = s9) \/
         (h <> 0 /\ exists (R0 : bvmap 5 word) (m'0 : word -> option byte),
            ms' = MS R0 F (Z_to_bv 64 0x81ac0) fc None m'0 (seg_rom rsegs) /\ getr R0 10 = Z_to_bv 64 0 /\
            getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\
            getr R0 19 = s3 /\ getr R0 26 = s10 /\ getr R0 27 = Z_to_bv 64 w144 /\
            getr R0 22 = s6 /\ getr R0 25 = s9 /\
            munch [(spv - STRCMP_WRAP_K, spv)] m m'0 /\ wmono rsegs m m'0 /\ stk rsegs m'0 lo spv))
      (MS R F (Z_to_bv 64 0x81ac0) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m' sp gp tp s0 s1 s3 s6 s9 s10 spv lo h w144 E0
    H10 H2 H3 H4 H8 H9 H19 H26 H27 H22 H25 Esp MU WM ST.
  apply evtF_done. right. split; [exact E0|]. exists R, m'. split; [reflexivity|].
  split; [exact H10|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H8|].
  split; [exact H9|]. split; [exact H19|]. split; [exact H26|]. split; [exact H27|].
  split; [exact H22|]. split; [exact H25|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* pre_F (RNG_all) + the wrapper call (the source's own block) + post_F re-derive R21.r21_tail_evt. The plain
   strcmp_wrap_contract is the first premise, as in the source. *)
Lemma r21_tail_evt_of_pre_post : strcmp_wrap_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm w144 : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ shadow_rw m /\ MNr21.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    evt rsegs
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (R : bvmap 5 word) (m' : word -> option byte),
            ms' = MS R F (Z_to_bv 64 0x81ac0) fc None m' (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9 /\
            munch [(spv - STRCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo spv))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx Esp Es1 Es5 Es10 Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN.
  eapply LE21.evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    eapply (r21_tail_pre_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
              s10 s11 t3 t4 t5 t6 F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx);
      try eassumption;
      first [ intros _; split; apply rng_all;
              unfold ASAN_K, HIGHMEM_BEG, APPMEM_END in *;
              rewrite ?Z.shiftr_div_pow2 by lia; try (Z.div_mod_to_equations; lia); lia
            | apply rng_all; unfold ASAN_K in *;
              rewrite ?Z.shiftr_div_pow2 by lia; try (Z.div_mod_to_equations; lia); lia ]. }
  intros ms' [ (E0 & R' & E & Hr10 & Hr2 & Hr3 & Hr4 & Hr8 & Hr9 & Hr19 & Hr26 & Hr27 & Hr22 & Hr25)
             | (E0 & c5 & c6 & c7 & c12 & c13 & c14 & c15 & c16 & c17 & c28 & c29 & c30 & c31 & E) ].
  - subst ms'. apply evt_done. left. split; [exact E0|]. exists R'.
    split; [reflexivity|]. do 10 (split; [eassumption|]). assumption.
  - (* the wrapper call, exactly the source's block (r21_tail_evt, R21.v:294-342) *)
    subst ms'.
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HSW & HMIx & HGOT & HCF1 & HCF2).
    assert (HHMv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
    pose proof (MNr21.mem_rel_normalize rsegs m HMIx) as REL.
    assert (HS1x0 : bytes_at rsegs (MNr21.normalize rsegs m) (S5 + 3) (sx ++ [Z_to_bv 8 0]))
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HS1x).
    assert (HS2x0 : bytes_at rsegs (MNr21.normalize rsegs m) nm (sx ++ [Z_to_bv 8 0]))
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HS2x).
    assert (HAX0 : addressable (MNr21.normalize rsegs m) (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1))
      by exact (proj1 (B3N21.b3n_rel_ad m _ _ _ REL) HAX).
    assert (HAY0 : addressable (MNr21.normalize rsegs m) nm (Z.of_nat (strcmp_k sx sx) + 1))
      by exact (proj1 (B3N21.b3n_rel_ad m _ _ _ REL) HAY).
    assert (HST0 : stk rsegs (MNr21.normalize rsegs m) lo spv)
      by exact (proj1 (B3N21.b3n_rel_stk m (MNr21.normalize rsegs m) lo spv REL ltac:(lia) ltac:(lia)) HST).
    assert (HAC0 : asan_cells (MNr21.normalize rsegs m)) by exact (proj1 (B3N21.b3n_rel_cells m _ REL) HAC).
    assert (HSW0 : shadow_rw (MNr21.normalize rsegs m)) by exact (proj1 (B3N21.b3n_rel_sw m _ REL) HSW).
    assert (HMI0 : mem_inv rsegs (MNr21.normalize rsegs m)) by exact (MNr21.mem_inv_normalize rsegs m).
    assert (HGOT0 : bytes_at rsegs (MNr21.normalize rsegs m) GOT_CF (le8 (wa CF)))
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HGOT).
    assert (HCF10 : bytes_at rsegs (MNr21.normalize rsegs m) (CF + 250) [Z_to_bv 8 1])
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HCF1).
    assert (HCF20 : bytes_at rsegs (MNr21.normalize rsegs m) (CF + 245) [Z_to_bv 8 0])
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HCF2).
    eapply LE21.evt_cut.
    { eapply (MNr21.evt_normalize rsegs _ _ _ _ _ _ _ _ BZr21.wx_apart_asan HMIx).
      eapply SC with (sx := sx) (sy := sx) (lo := lo);
        rewrite ?Esp;
        rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (S5 + 3)) by lia;
          rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit nm) by lia;
        rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
        first [ exact HS1x0 | exact HS0x | exact HS2x0 | exact HK | exact HAX0 | exact HEX | exact HAY0
              | exact HEY | exact HX7 | exact HY7 | exact HST0 | exact HLO | exact HHM | exact HAE
              | exact HSEPx | exact HSEPy | exact HAC0 | exact HSW0 | exact HMI0 | exact HGOT0
              | exact HCF10 | exact HCF20 | assumption ]. }
    intros ms' (s0' & PO & HREL & HROS).
    destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E' & Hr & Hr0' & MU0 & WM0 & _ & STq0 & _).
    assert (Er : r = Z_to_bv 64 0) by (apply Hr0'; reflexivity). subst s0'.
    destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ERg, EF, EP, ES, EV, EC,
      ERo, HMR.
    assert (EPc : ms_pc_val ms' = Z_to_bv 64 0x81ac0).
    { rewrite EP. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; [lia | reflexivity].
      }
    pose proof (B3N21.b3n_ms_eta ms' ES) as Ems.
    rewrite ERg, EF, EPc, EC, EV, ERo, Er in Ems.
    remember (ms_mem ms') as m' eqn:Em'. clear Em'.
    rewrite ?Esp in MU0, STq0. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv)
      in MU0, STq0 by lia.
    assert (MUf : munch [(spv - STRCMP_WRAP_K, spv)] m m')
      by exact (B3N21.b3n_rel_munch _ m _ m' m0' REL HMR MU0 HROS).
    assert (WMf : wmono rsegs m m').
    { apply (B3N21.b3n_rel_wmono [(spv - STRCMP_WRAP_K, spv)] m _ m' m0' REL HMR MUf WM0).
      intros x Ex. apply (B3N21.b3n_W_ro _ x); [|exact Ex].
      intros p [<-|[]]. cbn [fst]. lia. }
    assert (STf : stk rsegs m' lo spv)
      by exact (proj2 (B3N21.b3n_rel_stk m' m0' lo spv HMR ltac:(lia) ltac:(lia)) STq0).
    rewrite Ems.
    apply (evtF_evt rsegs RNG_all).
    eapply (r21_tail_post_F RNG_all _ F fc m m' sp gp tp s0 s1 s3 s6 s9 s10 spv lo h w144 E0);
      try eassumption; try reflexivity.
Qed.

(* The pin (split-stretch form): r21_tail_evt_of_pre_post states R21.r21_tail_evt term for term, first premise the
   plain strcmp_wrap_contract by name (constr_eq: syntactic). *)
Lemma r21_tail_evt_of_pre_post_verbatim : True.
Proof.
  lazymatch type of R21.r21_tail_evt with ?P -> ?A =>
  lazymatch type of r21_tail_evt_of_pre_post with ?Q -> ?B =>
    constr_eq P OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.strcmp_wrap_c.strcmp_wrap_contract;
    constr_eq Q OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.strcmp_wrap_c.strcmp_wrap_contract;
    constr_eq A B
  end end.
  exact I.
Qed.

(* ==== route (C) (a Theorem Labs lane 09:20Z; form a Theorem Labs lane 09:38Z / 10:34Z; writer a Theorem Labs lane): the _on twins of r21_tail_pre_F
   and r21_tail_evt_of_pre_post. The lemmas above keep their statements and proofs, except that r21_tail_evt_of_pre_post's proof now names MState by its full path.
   - r21_tail_pre_F_on: the stretch 0x81990 .. 0x81abc reads its shadow bytes (the lb checks at 0x819b0 .. 0x81a9c)
     through its own ov_read_bytes premises, stores none, and only destructs the h <> 0 conjunct's `shadow_rw m`
     (HSW) without using it. No shadow byte goes through the premise, so it is DROPPED.
   - r21_tail_evt_of_pre_post_on: the only use of `shadow_rw m` is the strcmp wrapper call at 0x81abc (a0 = S5 + 3,
     a1 = nm, sx = sy = sx), after the move to MemNorm.normalize. So R is the callee's own region at the call's
     arguments, strcmp_wrap_c_on.strcmp_wrap_shadow_R (S5 + 3) nm (Z.of_nat (strcmp_k sx sx) + 1) (a Theorem Labs lane's leaf
     lib/A/Prog/strcmp_wrap_c_on.v 0156a822960 (the blob this tree had at release c5e779efe8c) at 49e1a946522), moved to normalize m by
     A.ShadowRwOnT.shadow_rw_on_rel; the callee hypothesis is strcmp_wrap_c_on.strcmp_wrap_contract_on. The run's
     post states no shadow_rw, so it is unchanged. ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require strcmp_wrap_c_on.

Lemma r21_tail_pre_F_on :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm w144 : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ MNr21.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    (* the segment's own reads, one rng per load; the h <> 0 reads guarded by h <> 0 as the source guards them *)
    rng RNG (S5 + 2) 1 -> rng RNG (A + 144) 8 -> rng RNG (A + 112) 8 ->
    rng RNG (Z.shiftr (mr + 266) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 268) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 270) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 272) 3 + ASAN_K) 1 ->
    rng RNG (Z.shiftr (mr + 56) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 280) 3 + ASAN_K) 1 ->
    rng RNG S5 2 -> rng RNG (mr + 266) 2 -> rng RNG (S5 + 36) 1 ->
    rng RNG (S5 + 22) 2 -> rng RNG (mr + 268) 2 -> rng RNG (S5 + 24) 2 -> rng RNG (mr + 270) 2 ->
    rng RNG (S5 + 26) 2 -> rng RNG (mr + 272) 2 -> rng RNG (mr + 56) 4 ->
    (h <> 0 -> rng RNG (S5 + 20) 1 /\ rng RNG (mr + 280) 8) ->
    evtF rsegs RNG
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (c5 c6 c7 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 : word),
            ms' = MS (mkR (Z_to_bv 64 0x81ac0) sp gp tp c5 c6 c7 s0 s1
                          (Z_to_bv 64 (S5 + 3)) (Z_to_bv 64 nm) c12 c13 c14 c15 c16 c17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 w144) c28 c29 c30 c31)
                     F (Z_to_bv 64 STRCMP_WRAP) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx -> -> -> -> Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    G2 G144 G112 GK266 GK268 GK270 GK272 GK56 GK280 G0 GM266 G36 G22 GM268 G24 GM270 G26 GM272 GM56 GHN.
  step. step. step. if_true.            (* 81990 lbu; 81994 ld s11; 81998 bnez *)
  step. step. step. step. r21_shfix.     (* 819a0 ld; addi 266; srli; add *)
  step. step. step. if_true.           (* 819b0 lb (check); 819b4 lhu; 819b8 beqz *)
  step. step. r21F_tail_beq_refl.        (* 819c0 lhu; 819c4 beq *)
  step. step. if_true.                                         (* 819cc lbu 36; 819d0 bnez *)
  step. step. step. step. r21_shfix.                           (* 819d8 .. 819e4 *)
  step. step. step. if_true.                                   (* 819e8 lb; 819ec lhu 22; 819f0 beqz *)
  step. step. r21F_tail_beq_refl.                               (* 819f8 lhu; 819fc beq *)
  step. step. step. step. r21_shfix.                           (* 81a04 .. 81a10 *)
  step. step. step. if_true.                                   (* 81a14 lb; 81a18 lhu 24; 81a1c beqz *)
  step. step. r21F_tail_beq_refl.                               (* 81a24 lhu; 81a28 beq *)
  step. step. step. step. r21_shfix.                           (* 81a30 .. 81a3c *)
  step. step. step. if_true.                                   (* 81a40 lb; 81a44 lhu 26; 81a48 beqz *)
  step. step. r21F_tail_beq_refl.                               (* 81a50 lhu; 81a54 beq *)
  step. step. step. step. r21_shfix.                           (* 81a5c .. 81a68 *)
  step. step. if_true.                                         (* 81a6c lb; 81a70 beqz *)
  step. step.                           (* 81a78 lw; 81a7c beqz a0,81ac8 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    subst h. apply evtF_done. left. split; [reflexivity|]. eexists. split; [reflexivity|].
    do 10 (split; [reflexivity|]). reflexivity.
  - if_false_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HMIx & HGOT & HCF1 & HCF2).
    destruct (GHN E0) as (G20 & G280).
    step. step. if_true.                                       (* 81a80 lbu 20; 81a84 bnez *)
    step. step. step. step. r21_shfix.                         (* 81a8c .. 81a98 *)
    step. step. if_true.               (* 81a9c lbu (check); 81aa0 beqz *)
    step. step. step.                  (* 81aa8 ld a1; 81aac addi a0,s5,3; 81ab0 bnez *)
    if_true_by (f_equal negb (r21_eqb0 nm Hnm)).
    step.                               (* 81abc jal wrapper_strcmp, ra = 0x81ac0 *)
    apply evtF_done. right. split; [exact E0|]. do 13 eexists. reflexivity.
Qed.

(* pre_F_on (RNG_all) + the wrapper call under strcmp_wrap_contract_on + post_F re-derive r21_tail_evt's run with
   the region premise in the h <> 0 conjunct. *)
Lemma r21_tail_evt_of_pre_post_on : strcmp_wrap_c_on.strcmp_wrap_contract_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm w144 : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\
       A.ShadowRwOn.shadow_rw_on
         (strcmp_wrap_c_on.strcmp_wrap_shadow_R (S5 + 3) nm (Z.of_nat (strcmp_k sx sx) + 1)) m /\
       MNr21.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    evt rsegs
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (R : bvmap 5 word) (m' : word -> option byte),
            ms' = MS R F (Z_to_bv 64 0x81ac0) fc None m' (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9 /\
            munch [(spv - STRCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo spv))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx Esp Es1 Es5 Es10 Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN.
  eapply LE21.evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    eapply (r21_tail_pre_F_on RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
              s10 s11 t3 t4 t5 t6 F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx);
      try eassumption;
      first [ (* the h <> 0 conjunct without the region premise, from HN's *)
              intros E0; specialize (HN E0); tauto
            | intros _; split; apply rng_all;
              unfold ASAN_K, HIGHMEM_BEG, APPMEM_END in *;
              rewrite ?Z.shiftr_div_pow2 by lia; try (Z.div_mod_to_equations; lia); lia
            | apply rng_all; unfold ASAN_K in *;
              rewrite ?Z.shiftr_div_pow2 by lia; try (Z.div_mod_to_equations; lia); lia ]. }
  intros ms' [ (E0 & R' & E & Hr10 & Hr2 & Hr3 & Hr4 & Hr8 & Hr9 & Hr19 & Hr26 & Hr27 & Hr22 & Hr25)
             | (E0 & c5 & c6 & c7 & c12 & c13 & c14 & c15 & c16 & c17 & c28 & c29 & c30 & c31 & E) ].
  - subst ms'. apply evt_done. left. split; [exact E0|]. exists R'.
    split; [reflexivity|]. do 10 (split; [eassumption|]). assumption.
  - (* the wrapper call, the source's block (r21_tail_evt_of_pre_post above) with the region premise *)
    subst ms'.
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HSW & HMIx & HGOT & HCF1 & HCF2).
    assert (HHMv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
    pose proof (MNr21.mem_rel_normalize rsegs m HMIx) as REL.
    assert (HS1x0 : bytes_at rsegs (MNr21.normalize rsegs m) (S5 + 3) (sx ++ [Z_to_bv 8 0]))
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HS1x).
    assert (HS2x0 : bytes_at rsegs (MNr21.normalize rsegs m) nm (sx ++ [Z_to_bv 8 0]))
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HS2x).
    assert (HAX0 : addressable (MNr21.normalize rsegs m) (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1))
      by exact (proj1 (B3N21.b3n_rel_ad m _ _ _ REL) HAX).
    assert (HAY0 : addressable (MNr21.normalize rsegs m) nm (Z.of_nat (strcmp_k sx sx) + 1))
      by exact (proj1 (B3N21.b3n_rel_ad m _ _ _ REL) HAY).
    assert (HST0 : stk rsegs (MNr21.normalize rsegs m) lo spv)
      by exact (proj1 (B3N21.b3n_rel_stk m (MNr21.normalize rsegs m) lo spv REL ltac:(lia) ltac:(lia)) HST).
    assert (HAC0 : asan_cells (MNr21.normalize rsegs m)) by exact (proj1 (B3N21.b3n_rel_cells m _ REL) HAC).
    assert (HSW0 : A.ShadowRwOn.shadow_rw_on
                     (strcmp_wrap_c_on.strcmp_wrap_shadow_R (S5 + 3) nm (Z.of_nat (strcmp_k sx sx) + 1))
                     (MNr21.normalize rsegs m))
      by exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    assert (HMI0 : mem_inv rsegs (MNr21.normalize rsegs m)) by exact (MNr21.mem_inv_normalize rsegs m).
    assert (HGOT0 : bytes_at rsegs (MNr21.normalize rsegs m) GOT_CF (le8 (wa CF)))
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HGOT).
    assert (HCF10 : bytes_at rsegs (MNr21.normalize rsegs m) (CF + 250) [Z_to_bv 8 1])
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HCF1).
    assert (HCF20 : bytes_at rsegs (MNr21.normalize rsegs m) (CF + 245) [Z_to_bv 8 0])
      by exact (proj1 (MNr21.bytes_at_rel rsegs m _ _ _ REL) HCF2).
    eapply LE21.evt_cut.
    { eapply (MNr21.evt_normalize rsegs _ _ _ _ _ _ _ _ BZr21.wx_apart_asan HMIx).
      eapply SC with (sx := sx) (sy := sx) (lo := lo);
        rewrite ?Esp;
        rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (S5 + 3)) by lia;
          rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit nm) by lia;
        rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
        first [ exact HS1x0 | exact HS0x | exact HS2x0 | exact HK | exact HAX0 | exact HEX | exact HAY0
              | exact HEY | exact HX7 | exact HY7 | exact HST0 | exact HLO | exact HHM | exact HAE
              | exact HSEPx | exact HSEPy | exact HAC0 | exact HSW0 | exact HMI0 | exact HGOT0
              | exact HCF10 | exact HCF20 | assumption ]. }
    intros ms' (s0' & PO & HREL & HROS).
    destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E' & Hr & Hr0' & MU0 & WM0 & _ & STq0 & _).
    assert (Er : r = Z_to_bv 64 0) by (apply Hr0'; reflexivity). subst s0'.
    destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ERg, EF, EP, ES, EV, EC,
      ERo, HMR.
    assert (EPc : ms_pc_val ms' = Z_to_bv 64 0x81ac0).
    { rewrite EP. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; [lia | reflexivity].
      }
    pose proof (B3N21.b3n_ms_eta ms' ES) as Ems.
    rewrite ERg, EF, EPc, EC, EV, ERo, Er in Ems.
    remember (ms_mem ms') as m' eqn:Em'. clear Em'.
    rewrite ?Esp in MU0, STq0. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv)
      in MU0, STq0 by lia.
    assert (MUf : munch [(spv - STRCMP_WRAP_K, spv)] m m')
      by exact (B3N21.b3n_rel_munch _ m _ m' m0' REL HMR MU0 HROS).
    assert (WMf : wmono rsegs m m').
    { apply (B3N21.b3n_rel_wmono [(spv - STRCMP_WRAP_K, spv)] m _ m' m0' REL HMR MUf WM0).
      intros x Ex. apply (B3N21.b3n_W_ro _ x); [|exact Ex].
      intros p [<-|[]]. cbn [fst]. lia. }
    assert (STf : stk rsegs m' lo spv)
      by exact (proj2 (B3N21.b3n_rel_stk m' m0' lo spv HMR ltac:(lia) ltac:(lia)) STq0).
    rewrite Ems.
    apply (evtF_evt rsegs RNG_all).
    eapply (r21_tail_post_F RNG_all _ F fc m m' sp gp tp s0 s1 s3 s6 s9 s10 spv lo h w144 E0);
      try eassumption; try reflexivity.
Qed.
