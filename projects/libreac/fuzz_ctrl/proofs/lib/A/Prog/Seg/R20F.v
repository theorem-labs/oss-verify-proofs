(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names, addresses and numbers changed; 541 of its 632 lines of code are new or changed and 1411 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R20.v; 46 of its 90 lines of code are new or changed and 588 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R20.v e5176224c2a7 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives R20.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of R20.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of R20's one run lemma r20_evt (Seg/R20.v:62), the run 0x818e8 -> 0x8191c: the taken
   `beqz a0,818f0`, `li a0,-8` and the six 1-byte shadow stores into S(fr) + 316, + 317, + 320 .. + 323, then
   `j 8191c`. The run reads no memory; it writes only inside the window [SHv + 316, SHv + 324) that its own stk
   premise names, so the single appended premise is rng RNG (SHv + 316) 8. The script is R20's, over StepF; the
   store tactic r20_sb is restated as r20F_sb because its goal pattern names evt. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R20.
(* Last: StepF's step / if_true (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module LE20 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* R20.v's r20_sb with the goal pattern of evtF (the only change). *)
Ltac r20F_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r20_stk_store_ok mm (SHv + 316) (SHv + 324) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 316, SHv + 324)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite ?length_le1; cbn [length Z.of_nat]; lia
           | rewrite ?length_le1; cbn [inside length Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 316) (SHv + 324) (SHv + off) bs) in STh;
         [ | lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

(* 0x818e8 beqz a0,818f0 (a0 = 0, taken) ; 0x818f0 li a0,-8 ; the six shadow stores ; 0x8190c j 8191c. *)
Lemma r20_evt_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SHv : Z),
    a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 SHv -> 0 <= SHv -> SHv + 324 <= 2 ^ 64 ->
    stk rsegs m (SHv + 316) (SHv + 324) ->
    (* the six stores, inside the window of the stk premise *)
    rng RNG (SHv + 316) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8191c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(SHv + 316, SHv + 324)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SHv + 316) (SHv + 324))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818e8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SHv -> -> HS0 HS1 ST RW.
  pose proof (munch_refl [(SHv + 316, SHv + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_true.                           (* 818e8 beqz a0,818f0 *)
  step.                                    (* 818f0 li a0,-8 *)
  r20F_sb SHv 322 ST MU WM.                (* 818f4 sb a0,322(s3) *)
  r20F_sb SHv 323 ST MU WM.                (* 818f8 sb a0,323(s3) *)
  r20F_sb SHv 316 ST MU WM.                (* 818fc sb a0,316(s3) *)
  r20F_sb SHv 317 ST MU WM.                (* 81900 sb a0,317(s3) *)
  r20F_sb SHv 320 ST MU WM.                (* 81904 sb a0,320(s3) *)
  r20F_sb SHv 321 ST MU WM.                (* 81908 sb a0,321(s3) *)
  step.                                    (* 8190c j 8191c *)
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 12 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* R20.r20_evt's statement, re-derived from r20_evt_F at RNG_all (the rng premise by rng_all). *)
Lemma r20_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SHv : Z),
    a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 SHv -> 0 <= SHv -> SHv + 324 <= 2 ^ 64 ->
    stk rsegs m (SHv + 316) (SHv + 324) ->
    LE20.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8191c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(SHv + 316, SHv + 324)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SHv + 316) (SHv + 324))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SHv Ea0 Es3 HS0 HS1 ST.
  apply (evtF_evt rsegs RNG_all).
  apply (r20_evt_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m SHv Ea0 Es3 HS0 HS1 ST).
  apply rng_all; lia.
Qed.

(* The pin: r20_evt_of_F's statement is R20.r20_evt's, term for term (constr_eq: syntactic, not up to conversion). *)
Lemma r20_evt_of_F_verbatim : True.
Proof.
  let A := type of R20.r20_evt in let B := type of r20_evt_of_F in constr_eq A B.
  exact I.
Qed.
