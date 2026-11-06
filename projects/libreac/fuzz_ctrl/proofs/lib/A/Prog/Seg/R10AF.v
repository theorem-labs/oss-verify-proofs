(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2252 of its 2377 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10A.v; 289 of its 510 lines of code are new or changed and 2156 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R10A.v c865c4581e03 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives R10A.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of R10A.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* Footprint (_F) twins of R10A.v's run lemmas, each the owner's script over lib.Lib StepF as an ExecF.evtF under a
   universally quantified footprint RNG, with the owner's premises unchanged, RNG first, and one rng premise per
   region the run writes (instruction fetch is not an access):
   - r10a_evt0_F   (R10A.v:108, arm b = 0): the five one-byte stores S(fr) + 306, 308, 312, 316, 317, all inside the
     12 cells the premise `rw_cells rsegs m (Sh + 306) (map C1 xs)` (length xs = 12) names: rng RNG (Sh + 306) 12.
   - r10a_evt12_F  (R10A.v:168, arm b = 1, 2): the three one-byte stores S(fr) + 306, 308, 312, inside the 7 cells of
     the same premise (length xs = 7): rng RNG (Sh + 306) 7.
   - r10a_head34_F (R10A.v:219, arm b = 3, 4, head): the same three stores: rng RNG (Sh + 306) 7.
   Every other instruction of the three runs is register-only (li / addi / mv and the taken or untaken branches), so
   no further region is read. Each <r>_of_F re-derives R10A.<r> at ExecF.RNG_all (bounds from the owner's own
   0 <= Sh and Sh + 318 <= 2 ^ 64 / Sh + 313 <= 2 ^ 64), and each pin checks it by constr_eq.

   NOT re-run here: R10A.r10a_call34 (R10A.v:1060), the `jal reac_ctrl_identity_reply` at 0x816c0. It takes
   reac_ctrl_identity_reply_c.reac_ctrl_identity_reply_contract as its first premise, and no footprint contract
   `reac_ctrl_identity_reply_contract_F` exists (neither on this base fdd2ed9f9d7 nor on a Theorem Labs lane's
   working branch 28b0af0a5b2). Per the spec that run stays plain: blocked, reac_ctrl_identity_reply has no _F.
   R10A.v itself is unchanged apart from comment text; two comment lines (:63, :1058) differ from the source blob. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memset asan_memcpy.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R10A.
(* Last: StepF's step / if_true_by / if_false_by / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* R10A.r10a_fix / r10a_sb restated for evtF goals (the owner's match is on `evt _ _ (MS ...)`, which an evtF goal
   does not meet); the bodies are the owner's, with R10A's own r10a_le1_lit / r10a_le1. *)
Ltac r10aF_fix :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (R10A.r10a_le1_lit z) by lia; mem_after_store
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (R10A.r10a_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac r10aF_sb := step; r10aF_fix.

(* ---- arm b = 0: 0x81680 .. 0x81740 (bnez s7 not taken) .. 0x81764, to the block-sum head 0x81768. ---- *)
Lemma r10a_evt0_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh phi : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 0 -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 9 ->
    s8 = Z_to_bv 64 phi -> 0 <= phi -> phi + 18 < 2 ^ 64 -> 0 <= Sh -> Sh + 318 <= 2 ^ 64 ->
    length xs = 12%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    ExecF.rng RNG (Sh + 306) 12 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l12 : list byte) (c4 c5 : byte),
         ms' = MS R F (Z_to_bv 64 0x81768) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
         munch [(Sh + 306, Sh + 318)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) l12 /\ length l12 = 12%nat /\
         bytes_at rsegs m' (Sh + 316) [c4] /\ bv_signed c4 = 0 /\
         bytes_at rsegs m' (Sh + 317) [c5] /\ bv_signed c5 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh phi xs -> -> -> -> -> Hphi0 Hphi1 HSh0 HSh1 Hxs CH Rsh.
  do 12 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (munch_refl [(Sh + 306, Sh + 318)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  step.
  r10aF_sb. r10aF_sb. r10aF_sb.
  step.
  step. if_false_by (R10A.r10a_blt_f 4 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_true_by (R10A.r10a_bgeu_t (0 + -3) 2 ltac:(rewrite
    !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap; lia)).
  step. if_false_by (R10A.r10a_bne_f 0 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  r10aF_sb. r10aF_sb.
  step.
  step. if_true_by (R10A.r10a_beq_t 9 9 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step. step. step.
  destruct CH as ((Hwfc & Hbc) & Hwrc). cbn [cells_bytes cbytes app] in Hbc.
  apply ExecF.evtF_done. do 5 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact Hbc|]. split; [reflexivity|].
  split; [exact (R10A.r10a_bat_idx _ _ _ 10%nat _ (Sh + 316) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact (R10A.r10a_bat_idx _ _ _ 11%nat _ (Sh + 317) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  vm_compute; reflexivity.
Qed.

Lemma r10a_evt0_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh phi : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 0 -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 9 ->
    s8 = Z_to_bv 64 phi -> 0 <= phi -> phi + 18 < 2 ^ 64 -> 0 <= Sh -> Sh + 318 <= 2 ^ 64 ->
    length xs = 12%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l12 : list byte) (c4 c5 : byte),
         ms' = MS R F (Z_to_bv 64 0x81768) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
         munch [(Sh + 306, Sh + 318)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) l12 /\ length l12 = 12%nat /\
         bytes_at rsegs m' (Sh + 316) [c4] /\ bv_signed c4 = 0 /\
         bytes_at rsegs m' (Sh + 317) [c5] /\ bv_signed c5 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh phi xs E3 E7 E11 E0 E8 Hphi0 Hphi1 HSh0 HSh1 Hxs CH.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (r10a_evt0_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m Sh phi xs E3 E7 E11 E0 E8 Hphi0 Hphi1 HSh0 HSh1 Hxs CH).
  apply ExecF.rng_all; lia.
Qed.

Example r10a_evt0_of_F_verbatim : True.
Proof.
  let a := type of R10A.r10a_evt0 in let b := type of r10a_evt0_of_F in constr_eq a b.
  exact I.
Qed.

(* ---- arm b = 1, 2: 0x81680 .. 0x81740 (bnez s7 taken) .. 0x817d0 .. 0x817e8, to 0x817ec. ---- *)
Lemma r10a_evt12_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh phi bb : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 bb -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 5 ->
    s8 = Z_to_bv 64 phi -> 1 <= bb <= 2 -> 0 <= phi -> phi + 18 < 2 ^ 64 -> 0 <= Sh -> Sh + 313 <= 2 ^ 64 ->
    length xs = 7%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    ExecF.rng RNG (Sh + 306) 7 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l7 : list byte),
         ms' = MS R F (Z_to_bv 64 0x817ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
         munch [(Sh + 306, Sh + 313)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh phi bb xs -> -> -> -> -> Hbb Hphi0 Hphi1 HSh0 HSh1 Hxs CH Rsh.
  do 7 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (munch_refl [(Sh + 306, Sh + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  step.
  r10aF_sb. r10aF_sb. r10aF_sb.
  step.
  step. if_false_by (R10A.r10a_blt_f 4 bb ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_true_by (R10A.r10a_bgeu_t (bb + -3) 2 ltac:(rewrite
    !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap; lia)).
  step. if_true_by (R10A.r10a_bne_t bb 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_true_by (R10A.r10a_beq_t 5 5 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step. step. step.
  destruct CH as ((Hwfc & Hbc) & Hwrc). cbn [cells_bytes cbytes app] in Hbc.
  apply ExecF.evtF_done. do 3 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact Hbc | reflexivity].
Qed.

Lemma r10a_evt12_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh phi bb : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 bb -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 5 ->
    s8 = Z_to_bv 64 phi -> 1 <= bb <= 2 -> 0 <= phi -> phi + 18 < 2 ^ 64 -> 0 <= Sh -> Sh + 313 <= 2 ^ 64 ->
    length xs = 7%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l7 : list byte),
         ms' = MS R F (Z_to_bv 64 0x817ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 13 = Z_to_bv 64 32 /\
         munch [(Sh + 306, Sh + 313)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh phi bb xs E3 E7 E11 E0 E8 Hbb Hphi0 Hphi1 HSh0 HSh1 Hxs CH.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (r10a_evt12_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m Sh phi bb xs E3 E7 E11 E0 E8 Hbb Hphi0 Hphi1 HSh0 HSh1 Hxs CH).
  apply ExecF.rng_all; lia.
Qed.

Example r10a_evt12_of_F_verbatim : True.
Proof.
  let a := type of R10A.r10a_evt12 in let b := type of r10a_evt12_of_F in constr_eq a b.
  exact I.
Qed.

(* ---- arm b = 3, 4, head: 0x81680 .. 0x816a4 (beq a0,5 taken) to 0x816ac. ---- *)
Lemma r10a_head34_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh bb : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 bb -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 5 ->
    3 <= bb <= 4 -> 0 <= Sh -> Sh + 313 <= 2 ^ 64 ->
    length xs = 7%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    ExecF.rng RNG (Sh + 306) 7 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS R F (Z_to_bv 64 0x816ac) fc None m' (seg_rom rsegs) /\
         R = mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (getr R 11) (getr R 12) (getr R 13) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 /\
         munch [(Sh + 306, Sh + 313)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m' (Sh + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m' (Sh + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m' (Sh + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh bb xs E3 E7 E11 E0 Hbb HSh0 HSh1 Hxs CH Rsh.
  subst s3 s7 s11 a0.
  do 7 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (munch_refl [(Sh + 306, Sh + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  step.
  r10aF_sb. r10aF_sb. r10aF_sb.
  step.
  step. if_false_by (R10A.r10a_blt_f 4 bb ltac:(lia) ltac:(lia) ltac:(lia)).
  step.
  step. if_false_by (R10A.r10a_bgeu_f (bb + -3) 2 ltac:(rewrite
    !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap; lia)).
  step.
  step. if_true_by (R10A.r10a_beq_t 5 5 ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct CH as ((Hwfc & Hbc) & Hwrc). cbn [cells_bytes cbytes app] in Hbc.
  apply ExecF.evtF_done. do 6 eexists.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact (R10A.r10a_bat_idx _ _ _ 0%nat _ (Sh + 306) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact (R10A.r10a_bat_idx _ _ _ 2%nat _ (Sh + 308) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact (R10A.r10a_bat_idx _ _ _ 6%nat _ (Sh + 312) Hbc ltac:(reflexivity)
                  ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))|].
  split; [vm_compute; reflexivity|].
  split; [exact Hbc | reflexivity].
Qed.

Lemma r10a_head34_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh bb : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s7 = Z_to_bv 64 bb -> s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 5 ->
    3 <= bb <= 4 -> 0 <= Sh -> Sh + 313 <= 2 ^ 64 ->
    length xs = 7%nat -> rw_cells rsegs m (Sh + 306) (map C1 xs) ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS R F (Z_to_bv 64 0x816ac) fc None m' (seg_rom rsegs) /\
         R = mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (getr R 11) (getr R 12) (getr R 13) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 /\
         munch [(Sh + 306, Sh + 313)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (Sh + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m' (Sh + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m' (Sh + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m' (Sh + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh bb xs E3 E7 E11 E0 Hbb HSh0 HSh1 Hxs CH.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (r10a_head34_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m Sh bb xs E3 E7 E11 E0 Hbb HSh0 HSh1 Hxs CH).
  apply ExecF.rng_all; lia.
Qed.

Example r10a_head34_of_F_verbatim : True.
Proof.
  let a := type of R10A.r10a_head34 in let b := type of r10a_head34_of_F in constr_eq a b.
  exact I.
Qed.

(* R10A.v's own mid-file Require block (R10A.v:272-280), repeated here so the split stretches below are stated in
   the same environment as R10A.r10a_call34 (R10A.v:1060): YK11's getr, SlotInv's q64. ExecF / StepF are imported
   again after it, so StepF's step still shadows Step's, and YK11 last, as the spec asks. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs B3Rtm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* ---- SPLIT STRETCHES for R10A.r10a_call34 (a Theorem Labs lane ruling 00:45Z, shape by a Theorem Labs lane 00:48Z).
   reac_ctrl_identity_reply (0x83f8c) has no _F contract of record, so the glue splits the run at the call
   0x816c0 (return 0x816c4). Both stretches are cut from r10a_call34's own script, no new reasoning:
   - r10a_call34_pre_F: the six instructions 0x816ac mv a0,s8 ; 0x816b0 mv a1,s2 ; 0x816b4 ld a2,88(s1) ;
     0x816b8 ld a3,80(s1) ; 0x816bc ld a4,72(s1) ; 0x816c0 jal, ending in the CALLEE ENTRY state
     (pc = REAC_CTRL_IDENTITY_REPLY, ra = 0x816c4); the three 8-byte spill reads are its only accesses, and the
     callee contract does not appear. This is the source's `step. step. step. step. step. step.` prefix.
   - r10a_call34_post_F: the zero-step stretch from the RETURN pc 0x816c4 at a universally quantified canonical
     register map, with exactly the machine-level facts the source script holds right after it applies the
     contract (the fifteen register equalities and MU2 / WM2 / ST2 / RWo / SW2 / Awin2 / FP2 of the callee post;
     the callee's MI2 / AC2 / TLS2 are not used by the source conclusion, so they are not premises). This is the
     source's `apply evt_done. do 2 eexists. ...` tail. No access, so no rng premise.
     The start keeps the source's F (float registers) and fc (fcsr) binders rather than fp_regs / fp_csr, because
     r10a_call34_of_pre_post has to rebuild R10A.r10a_call34 for the source's own F and fc (the no-weakening pin).
   - r10a_call34_of_pre_post: pre_F and post_F at ExecF.RNG_all with the PLAIN contract in the source's own first
     premise position, re-deriving R10A.r10a_call34; pinned by constr_eq. *)
Lemma r10a_call34_pre_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi nb pa pp pn A spv FS : Z) (g ja jp jn : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb -> s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv ->
    0 <= A -> A + 96 <= 2 ^ 64 ->
    q64 m (A + 88) pa -> q64 m (A + 80) pp -> q64 m (A + 72) pn ->
    0 <= phi < 2 ^ 64 -> 0 <= nb < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= spv -> stk rsegs m (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args phi pa pp pn = true -> 50 <= nb ->
       phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi g /\
       (phi + 50 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= phi)) ->
    (reply_args phi pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= phi \/ phi + 50 <= pa) /\ (pp + 8 <= phi \/ phi + 50 <= pp) /\
       (pn + 8 <= phi \/ phi + 50 <= pn) /\
       (pa + 2 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pa) /\
       (pp + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pp) /\
       (pn + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pn)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_REPLY_K -> spv <= APPMEM_END ->
    addressable m (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    (reply_args phi pa pp pn = true -> 50 <= nb -> addressable m phi 50) ->
    (reply_args phi pa pp pn = true ->
       addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
      (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn) ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 80) 8 -> ExecF.rng RNG (A + 72) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x816c4) sp gp tp t0 t1 t2 s0 s1
                               s8 s2 (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x816ac) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi nb pa pp pn A spv FS g ja jp jn -> -> -> -> HA0 HAE Qa Qp Qn
    Hphi Hnb Hpa Hpp Hpn Hsp Hsp16 HK ST HMI Hg50 Hgb Hcells HAC HSW HHM HAPP Awin Hga Haddr Abc BCM MCM GCF
    CF254 CF255 HFP HTLS Ra88 Ra80 Ra72.
  pose proof (R10A.r10a_q64_ro m (A + 88) pa Qa) as Rpa.
  pose proof (R10A.r10a_q64_ro m (A + 80) pp Qp) as Rpp.
  pose proof (R10A.r10a_q64_ro m (A + 72) pn Qn) as Rpn.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  step. step. step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* The return stretch: no instruction, the source's post rebuilt from the callee's post facts. *)
Lemma r10a_call34_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (phi nb pa pp pn spv FS : Z) (g : list byte),
    getr regs 2 = sp -> getr regs 3 = gp -> getr regs 4 = tp -> getr regs 8 = s0 -> getr regs 9 = s1 ->
    getr regs 18 = s2 -> getr regs 19 = s3 -> getr regs 21 = s5 -> getr regs 22 = s6 -> getr regs 23 = s7 ->
    getr regs 24 = s8 -> getr regs 25 = s9 -> getr regs 26 = s10 -> getr regs 27 = s11 ->
    getr regs 10 = Z_to_bv 64 (reply_ret phi nb pa pp pn g) ->
    munch (reac_ctrl_identity_reply_fp phi nb pa pp pn spv g ++ fp_w [1%nat] FS ++
           [(shadow_addr (spv - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m mem ->
    wmono rsegs m mem ->
    stk rsegs mem (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    (reply_ok phi nb pa pp pn g = true ->
       rw_cells rsegs mem pa [CB 2 (reply_addr g)] /\
       rw_cells rsegs mem pp [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
       rw_cells rsegs mem pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) ->
    shadow_rw mem ->
    addressable mem (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
      (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816c4) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (reply_ret phi nb pa pp pn g) /\
         munch (reac_ctrl_identity_reply_fp phi nb pa pp pn spv g ++ fp_w [1%nat] FS ++
                [(shadow_addr (spv - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ stk rsegs m' (spv - REAC_CTRL_IDENTITY_REPLY_K) spv /\
         (reply_ok phi nb pa pp pn g = true ->
            rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
            rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
            rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) /\
         shadow_rw m' /\
         addressable m' (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
           (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn))
      (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x816c4) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc m phi nb pa pp pn spv FS g
    K2 K3 K4 K8 K9 K18 K19 K21 K22 K23 K24 K25 K26 K27 K10 MU2 WM2 ST2 RWo SW2 Awin2 FP2.
  apply ExecF.evtF_done.
  exists (Regs6ss.mkR_of regs), mem.
  split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K18|]. split; [exact K19|]. split; [exact K21|]. split; [exact K22|]. split; [exact K23|].
  split; [exact K24|]. split; [exact K25|]. split; [exact K26|]. split; [exact K27|].
  split; [exact K10|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2|]. split; [exact RWo|].
  split; [exact SW2|]. split; [exact Awin2 | exact FP2].
Qed.

(* The two stretches and the PLAIN contract rebuild R10A.r10a_call34. *)
Lemma r10a_call34_of_pre_post : reac_ctrl_identity_reply_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi nb pa pp pn A spv FS : Z) (g ja jp jn : list byte),
    s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb -> s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv ->
    0 <= A -> A + 96 <= 2 ^ 64 ->
    q64 m (A + 88) pa -> q64 m (A + 80) pp -> q64 m (A + 72) pn ->
    0 <= phi < 2 ^ 64 -> 0 <= nb < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    spv < 2 ^ 64 -> spv mod 16 = 0 ->
    REAC_CTRL_IDENTITY_REPLY_K <= spv -> stk rsegs m (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    mem_inv rsegs m ->
    length g = 50%nat ->
    (reply_args phi pa pp pn = true -> 50 <= nb ->
       phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi g /\
       (phi + 50 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= phi)) ->
    (reply_args phi pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= phi \/ phi + 50 <= pa) /\ (pp + 8 <= phi \/ phi + 50 <= pp) /\
       (pn + 8 <= phi \/ phi + 50 <= pn) /\
       (pa + 2 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pa) /\
       (pp + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pp) /\
       (pn + 8 <= spv - REAC_CTRL_IDENTITY_REPLY_K \/ spv <= pn)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_REPLY_K -> spv <= APPMEM_END ->
    addressable m (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    (reply_args phi pa pp pn = true -> 50 <= nb -> addressable m phi 50) ->
    (reply_args phi pa pp pn = true ->
       addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
      (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn) ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816c4) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 10 = Z_to_bv 64 (reply_ret phi nb pa pp pn g) /\
         munch (reac_ctrl_identity_reply_fp phi nb pa pp pn spv g ++ fp_w [1%nat] FS ++
                [(shadow_addr (spv - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m m' /\
         wmono rsegs m m' /\ stk rsegs m' (spv - REAC_CTRL_IDENTITY_REPLY_K) spv /\
         (reply_ok phi nb pa pp pn g = true ->
            rw_cells rsegs m' pa [CB 2 (reply_addr g)] /\
            rw_cells rsegs m' pp [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
            rw_cells rsegs m' pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))]) /\
         shadow_rw m' /\
         addressable m' (spv - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (spv - REAC_CTRL_IDENTITY_REPLY_K) spv
           (reac_ctrl_identity_reply_W phi pa pp pn spv) (reac_ctrl_identity_reply_D phi nb pa pp pn))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x816ac) fc None m (seg_rom rsegs)).
Proof.
  intros REPLY0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi nb pa pp pn A spv FS g ja jp jn E8 E2 E1 Esp HA0 HAE Qa Qp Qn
    Hphi Hnb Hpa Hpp Hpn Hsp Hsp16 HK ST HMI Hg50 Hgb Hcells HAC HSW HHM HAPP Awin Hga Haddr Abc BCM MCM GCF
    CF254 CF255 HFP HTLS.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (r10a_call34_pre_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
             s8 s9 s10 s11 t3 t4 t5 t6 F fc m phi nb pa pp pn A spv FS g ja jp jn
             E8 E2 E1 Esp HA0 HAE Qa Qp Qn Hphi Hnb Hpa Hpp Hpn Hsp Hsp16 HK ST HMI Hg50 Hgb Hcells HAC HSW
             HHM HAPP Awin Hga Haddr Abc BCM MCM GCF CF254 CF255 HFP HTLS);
      apply ExecF.rng_all; lia. }
  intros ms' ->.
  subst s8 s2 s1 sp.
  eapply LE.evt_cut.
  { eapply (REPLY0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              phi nb pa pp pn spv FS g ja jp jn).
    all: first [ reflexivity | assumption ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RWo & AC2 & SW2 & Awin2 & FP2 & TLS2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x816c4)) with (Z_to_bv 64 0x816c4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (r10a_call34_post_F ExecF.RNG_all
           (mkR (Z_to_bv 64 0x816c4) (Z_to_bv 64 spv) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                (Z_to_bv 64 (reply_ret phi nb pa pp pn g)) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 nb) s3 s4 s5 s6 s7 (Z_to_bv 64 phi) s9 s10 s11 t3' t4' t5' t6')
           m' (Z_to_bv 64 spv) gp tp s0 (Z_to_bv 64 A) (Z_to_bv 64 nb) s3 s5 s6 s7 (Z_to_bv 64 phi) s9 s10 s11
           F fc m phi nb pa pp pn spv FS g);
    try reflexivity.
  - exact MU2.
  - exact WM2.
  - exact ST2.
  - exact RWo.
  - exact SW2.
  - exact Awin2.
  - exact FP2.
Qed.

Example r10a_call34_of_pre_post_verbatim : True.
Proof.
  let a := type of R10A.r10a_call34 in let b := type of r10a_call34_of_pre_post in constr_eq a b.
  exact I.
Qed.
