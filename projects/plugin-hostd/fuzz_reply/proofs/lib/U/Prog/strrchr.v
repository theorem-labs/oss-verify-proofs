From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strlen_c memrchr_c strrchr_c.
Import ListNotations.
Open Scope Z_scope.

Lemma strrchr_memrchr_res : forall A c (str slack : list byte),
  memrchr_res A c (Z.of_nat (length str) + 1) (str ++ Z_to_bv 8 0 :: slack) = strrchr_res A c str.
Proof.
  intros A c str slack. unfold memrchr_res, strrchr_res.
  replace (Z.to_nat (Z.of_nat (length str) + 1)) with (length str + 1)%nat by lia.
  rewrite firstn_app, firstn_all2 by lia.
  replace (length str + 1 - length str)%nat with 1%nat by lia. reflexivity.
Qed.

Theorem strrchr_holds : strlen_contract -> memrchr_contract -> strrchr_contract.
Proof.
  intros HSTRLEN HMEMRCHR. unfold strrchr_contract, STRRCHR, STRRCHR_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    str slack lo BA NZ PAD MI ST LO DJ.
  pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_app in BB. cbn [length] in BB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HSTRLEN with (str := str) (slack := slack); eassumption | post_call rsegs mm] end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  eapply evt_cut.
  { eapply HMEMRCHR with (buf := str ++ Z_to_bv 8 0 :: slack).
    - eassumption.
    - rewrite unsigned_lit by lia. rewrite length_app. cbn [length]. lia.
    - eassumption. }
  intros ms' PM. unfold memrchr_post in PM.
  destruct PM as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & -> & MU4 & WM4 & MI4 & BA4).
  apply evt_done. unfold strrchr_post, STRRCHR_K.
  rewrite (unsigned_lit (Z.of_nat (length str) + 1)) by lia.
  rewrite strrchr_memrchr_res.
  exists u0, u1, u2, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m4.
  split; [reflexivity|].
  split.
  { eapply munch_weaken; [| eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU4]]].
    - intros z Hz. cbn [outside] in *. destruct Hz as [Hz _]. split; [lia | exact I].
    - intros z Hz. cbn [outside]. exact I. }
  split; [eapply wmono_trans; [eassumption | exact WM4]|].
  split; [exact MI4|].
  split; [eapply stk_transport_disjoint; [eassumption | exact MU4 | exact WM4 | exact I]|].
  exact BA4.
Qed.
