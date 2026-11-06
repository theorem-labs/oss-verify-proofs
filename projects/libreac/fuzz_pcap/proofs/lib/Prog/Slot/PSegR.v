From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PSegW PSegE.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* Segment R (0x1310c-0x131b0): after the walk's pcap_source_close, the reader is reopened and read once
   more, closed, read once while closed, then buf and b are freed and the function returns 0. Each lemma
   runs from one call's return to the next call; none reaches the stop path 0x131c4. *)

(* R1: the closed reader's f cell is 0; reopen (pcap_source_open, ra 0x13124). *)
Lemma pcap_R1_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z),
    bv_unsigned sp = sp_h -> bytes_at rsegs m (sp_h + 32) (le8 (wz 0)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 32)) (wz (symaddr (Symbols.Plain.Sec.s_rodata + 0xe9)%Z)) a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open)) fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h HSP HF0.
  subst sp_h. pose proof (bytes_at_ov8 _ _ _ HF0) as RF0. clear HF0. unfold wz in RF0 |- *.
  step. step. if_false. do 4 step.
  apply evt_done. reflexivity.
Qed.

(* R2: the reopen answered 0; read the first record again (pcap_source_next with ts NULL, ra 0x1313c). *)
Lemma pcap_R2_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z),
    bv_unsigned sp = sp_h -> a0 = wz 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 32)) s2 s1 (wz 0) a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next)) fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h HSP E0.
  subst sp_h a0. unfold wz.
  step. if_false. do 5 step.
  apply evt_done. reflexivity.
Qed.

(* R3: the second read answered the first answer s3; close (pcap_source_close, ra 0x13148). *)
Lemma pcap_R3_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z),
    bv_unsigned sp = sp_h -> a0 = s3 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 32)) a1 a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close)) fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h HSP E0.
  subst sp_h a0. unfold wz.
  step. if_false. do 2 step.
  apply evt_done. reflexivity.
Qed.

(* R4: read the closed reader (pcap_source_next with ts NULL, ra 0x1315c). *)
Lemma pcap_R4_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z),
    bv_unsigned sp = sp_h ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 32)) s2 s1 (wz 0) a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next)) fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h HSP.
  subst sp_h. unfold wz.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

(* R5: the closed reader answered -1; free(buf) (ra 0x1316c). *)
Lemma pcap_R5_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = wz (-1) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z)) sp gp tp t0 t1 t2 s0 s1 s2 (wz (-1)) a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_free)) fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m E0.
  subst a0. unfold wz.
  step. step. if_false. do 2 step.
  apply evt_done. reflexivity.
Qed.

(* R6: free(b) (ra 0x13174). *)
Lemma pcap_R6_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z)) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Plain.s_free)) fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m.
  unfold wz. do 2 step.
  apply evt_done. reflexivity.
Qed.

(* R7: a0 = 0, the saved registers back from S - 104, sp = S, return to the saved ra. *)
Lemma pcap_R7_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (S : Z),
    bv_unsigned sp = S - 160 ->
    bytes_at rsegs m (S - 104) (saved_regs ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra' (wz S) gp tp t0 t1 t2 s0' s1' (wz 0) a1 a2 a3 a4 a5 a6 a7
                               s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6) FR (ret_pc ra') fc None m
                          (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' S HSP HSV.
  assert (ES : S = bv_unsigned sp + 160) by lia. subst S.
  replace (bv_unsigned sp + 160 - 104) with (bv_unsigned sp + 56) in HSV by lia.
  assert (RC : ro_cells rsegs m (bv_unsigned sp + 56)
                 [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1';
                  C8 s0'; C8 ra']).
  { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HSV. }
  clear HSV.
  unfold wz.
  do 16 step.
  apply evt_done. rewrite ?Z_to_bv_plus0. reflexivity.
Qed.
