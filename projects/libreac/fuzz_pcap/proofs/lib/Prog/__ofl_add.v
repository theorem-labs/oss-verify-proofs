From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel __ofl_lock_c __ofl_unlock_c __ofl_add_c.
Import ListNotations.
Open Scope Z_scope.

Theorem __ofl_add_holds : __ofl_lock_contract -> __ofl_unlock_contract -> __ofl_add_contract.
Proof.
  intros HOL HOU. unfold __ofl_add_contract, OFL_ADD, OFL_ADD_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nx [HT [HN HL]] HE MI HLK A0 A1 A2 A3 ST LO.
  unfold ofl_empty in HE.
  unfold A_OFL_HEAD in *. unfold A_LIBC, A_OFL_LOCK in HT, HN, HL. unfold A_LIBC in A1.
  replace ((symaddr Symbols.Plain.s___libc) + 3) with (symaddr (Symbols.Plain.s___libc + 0x3)%Z) in HN by reflexivity.
  replace ((symaddr Symbols.Plain.s___libc) + 1) with (symaddr (Symbols.Plain.s___libc + 0x1)%Z) in HT by reflexivity.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a0 + 112, bv_unsigned a0 + 120);
              ((symaddr Symbols.Plain.s_ofl_head), (symaddr Symbols.Plain.s_ofl_head) + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep. zstep.
  assert (U16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HOL with (lo := lo); [ unfold stdio_ok, A_LIBC, A_OFL_LOCK; refine (conj _ (conj _ _)); eassumption
                                                 | eassumption | rewrite unsigned_lit by lia; eassumption
                                                 | rewrite unsigned_lit by lia; unfold OFL_LOCK_K; lia
                                                 | unfold A_OFL_HEAD; lia ]
                    | unfold __ofl_lock_post, OFL_LOCK_K; post_call rsegs mm] end.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U16 in H; rename H into ST end.
  unfold wz, A_OFL_HEAD in *.
  zstep. zstep. zstep. if_true. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HOU; unfold stdio_ok, A_LIBC, A_OFL_LOCK; refine (conj _ (conj _ _)); eassumption
                    | intros ms' [a0' [a1' ->]]] end.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  apply evt_done. unfold __ofl_add_post, ofl_one, stdio_ok, A_OFL_HEAD, A_LIBC, A_OFL_LOCK, OFL_ADD_K.
  do 15 eexists. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))));
    first [ eassumption | unfold wz; rewrite Z_to_bv_bv_unsigned; eassumption ].
Qed.
