From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* Segments R1-R6 of the fuzz_pcap ubsan slot (entry_fn 0x12c4c): the pieces between the calls of
   pcap_source_open, pcap_source_next, pcap_source_close and free after the end loop (0x1306c-0x130d4).
   sp_h is the body sp; the frame cells are those of USPLIT.md (sha256 8fdc0d163942; internal record) (f at sp_h + 48, buf at sp_h + 24). *)

Lemma bytes_at_ov8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia) ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. all: try (apply firstn_all2; rewrite length_le8; lia).
Qed.

Lemma bytes_at_ov4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia) ltac:(rewrite length_le4; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. all: try (apply firstn_all2; rewrite length_le4; lia).
Qed.

(* R1: 0x1306c, the f cell of ps is 0 after pcap_source_close; to the call of pcap_source_open (0x1321c)
   with the file name 0x10381. *)
Lemma ubs_R1_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z),
    bv_unsigned sp = sp_h -> bytes_at rsegs m (sp_h + 48) (le8 (wz 0)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 48)) (wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z)) a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open)) fc None m
                         (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h HSP HF.
  subst sp_h. pose proof (bytes_at_ov8 _ _ _ HF) as RF. clear HF. unfold wz in *.
  step. step. if_false. do 4 step. apply evt_done. reflexivity.
Qed.

(* R2: 0x13084, pcap_source_open answered 0; to the call of pcap_source_next (0x13318) with ps, buf (the cell
   at sp_h + 24), the capacity s1 and no ts pointer. *)
Lemma ubs_R2_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h buf : Z),
    bv_unsigned sp = sp_h -> a0 = wz 0 -> bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 48)) (wz buf) s1 (wz 0) a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) fc None m
                         (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h buf HSP EA0 HB.
  subst sp_h a0. pose proof (bytes_at_ov8 _ _ _ HB) as RB. clear HB. unfold wz in *.
  step. if_false. do 5 step. apply evt_done. reflexivity.
Qed.

(* R3: 0x1309c, pcap_source_next answered the first answer again (a0 = s11); to the call of
   pcap_source_close (0x13600). *)
Lemma ubs_R3_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h : Z),
    bv_unsigned sp = sp_h -> a0 = s11 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 48)) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close)) fc None m
                         (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h HSP EA0.
  subst sp_h a0. unfold wz.
  step. if_false. do 2 step. apply evt_done. reflexivity.
Qed.

(* R4: 0x130a8, after pcap_source_close; to the call of pcap_source_next (0x13318) as in R2. *)
Lemma ubs_R4_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h buf : Z),
    bv_unsigned sp = sp_h -> bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 48)) (wz buf) s1 (wz 0) a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) fc None m
                         (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h buf HSP HB.
  subst sp_h. pose proof (bytes_at_ov8 _ _ _ HB) as RB. clear HB. unfold wz in *.
  do 5 step. apply evt_done. reflexivity.
Qed.

(* R5: 0x130bc, pcap_source_next on a closed ps answered -1; to the call of free (0x140ac) with buf. *)
Lemma ubs_R5_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h buf : Z),
    bv_unsigned sp = sp_h -> a0 = wz (-1) -> bytes_at rsegs m (sp_h + 24) (le8 (wz buf)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz buf) (wz (-1)) a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fc None m
                         (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m sp_h buf HSP EA0 HB.
  subst sp_h a0. pose proof (bytes_at_ov8 _ _ _ HB) as RB. clear HB. unfold wz in *.
  step. step. if_false. do 2 step. apply evt_done. reflexivity.
Qed.

(* R6: 0x130cc, after free(buf); to the call of free (0x140ac) with the file copy s0. *)
Lemma ubs_R6_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fc None m
                         (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m.
  unfold wz. do 2 step. apply evt_done. reflexivity.
Qed.
