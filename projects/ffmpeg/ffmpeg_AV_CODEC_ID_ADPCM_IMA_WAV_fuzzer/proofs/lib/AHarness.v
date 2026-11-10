(* SPDX-License-Identifier: MIT *)
(** ADPCM_IMA_WAV's LLVMFuzzerTestOneInput, run symbolically from its entry to
    its return for every value of the FFmpeg globals it reads and writes
    ([ms_hw]): 3 branches, 6 paths, each returning 0 to the driver with the
    callee-saved registers restored, having written only its 144-byte frame
    and those globals.  The structure follows ZFuzzerBounds/ZBoundaryContract
    of proofs/zlib/checksum_fuzzer. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import
  YK11 YK0i YP0m YP0e YP09 YP0l YP0k YP02 YP03 YP08 YP06 YH03 YL0s.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib Require Import ZImage.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YAddr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section Run.
Context {fx : FPState}.
(* atoms: 0..31 the registers at entry; 40 and 41 the 32-bit words at 0x14d950
   (reset_cpu_flags.default_cpu_flags) and 0x14d954 (cpu_flags); 42 the codec pointer c *)
Definition ah_regs : list sv :=
  map (fun n => if Nat.eqb n 0 then SLit 0 else if Nat.eqb n 1 then SLit RA_LIB else SOff n 0) (seq 0 32).
Definition AH_FRAME : Z := 144.
Definition ah_stack : region := mkRegion (Some 2%nat) (-AH_FRAME) 0 (-AH_FRAME) 0 [].
Definition ah_flags : region :=
  mkRegion None (AX_reset_cpu_flags_default_cpu_flags) (AX_cpu_count) (AX_reset_cpu_flags_default_cpu_flags) (AX_cpu_count)
    [mkChunk (AX_reset_cpu_flags_default_cpu_flags) (CVal 4 (SOff 40 0)); mkChunk (AX_cpu_flags) (CVal 4 (SOff 41 0))].
Definition ah_level : region := mkRegion None (AX_av_log_level) (AX_av_log_level_end) (AX_av_log_level) (AX_av_log_level_end) [].
Definition ah_c : region := mkRegion None (AX_c) (AX_av_cpu_count_printed) (AX_c) (AX_av_cpu_count_printed) [mkChunk (AX_c) (CVal 8 (SOff 42 0))].
Definition ah_list : region := mkRegion None (AX_codec_list) (AX_codec_list_8) (AX_codec_list) (AX_codec_list_8) [].
Definition ah_type : region := mkRegion None (AX_ff_adpcm_ima_wav_encoder_10) (AX_ff_adpcm_ima_wav_encoder_14) 0 0 [mkChunk (AX_ff_adpcm_ima_wav_encoder_10) (CImg 4)].
Definition ah_got : region := mkRegion None (AX_got_ff_adpcm_ima_wav_encoder) (AX_got_avcodec_default_execute) 0 0 [mkChunk (AX_got_ff_adpcm_ima_wav_encoder) (CImg 16)].
Definition ah_mem : smem := [ah_stack; ah_flags; ah_level; ah_c; ah_list; ah_type; ah_got].
Definition ah_facts : facts := mkFacts [(2%nat, mkAF 65536 (2^63-1) 4)] [] [].
Definition ah_entry : sstate := mkSS LIBPC ah_regs ah_mem None ah_facts.

Definition AH_FUEL : N := 300.
Definition run_ (ss : sstate) := sym_run_toN zsegs ztbl AH_FUEL RA_LIB ss.
Definition C_def_ge : acond := mkAC BC_GE (SExt true 32 (SOff 40 0)) (SLit 0).
Definition C_def_lt : acond := mkAC BC_LT (SExt true 32 (SOff 40 0)) (SLit 0).
Definition C_cpu_m1 : acond := mkAC BC_EQ (SExt true 32 (SOff 41 0)) (SLit (2^64-1)).
Definition C_cpu_set : acond := mkAC BC_NE (SExt true 32 (SOff 41 0)) (SLit (2^64-1)).
Definition C_c_set : acond := mkAC BC_NE (SOff 42 0) (SLit 0).
Definition C_c_null : acond := mkAC BC_EQ (SOff 42 0) (SLit 0).
(* the tree: s0 stops at bgez on default_cpu_flags; s1 (>= 0) and s3/s4 (< 0, after
   av_get_cpu_flags' test of cpu_flags == -1) stop at the test of c; the leaves return *)
Definition ah_s0 : sstate := Eval vm_compute in fst (run_ ah_entry).
Definition ah_s1 : sstate := Eval vm_compute in fst (run_ (add_cond ah_s0 C_def_ge)).
Definition ah_s2 : sstate := Eval vm_compute in fst (run_ (add_cond ah_s0 C_def_lt)).
Definition ah_s3 : sstate := Eval vm_compute in fst (run_ (add_cond ah_s2 C_cpu_m1)).
Definition ah_s4 : sstate := Eval vm_compute in fst (run_ (add_cond ah_s2 C_cpu_set)).
Definition ah_leaf (ss : sstate) (c : acond) : sstate := fst (run_ (add_cond ss c)).
Lemma run_s0 : run_ ah_entry = (ah_s0, RS_stopped (SR_branch BC_GE (SExt true 32 (SOff 40 0)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_s1 : run_ (add_cond ah_s0 C_def_ge) = (ah_s1, RS_stopped (SR_branch BC_NE (SOff 42 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_s2 : run_ (add_cond ah_s0 C_def_lt) =
  (ah_s2, RS_stopped (SR_branch BC_EQ (SExt true 32 (SOff 41 0)) (SLit (2^64-1)))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_s3 : run_ (add_cond ah_s2 C_cpu_m1) = (ah_s3, RS_stopped (SR_branch BC_NE (SOff 42 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_s4 : run_ (add_cond ah_s2 C_cpu_set) = (ah_s4, RS_stopped (SR_branch BC_NE (SOff 42 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma run_leaf : forall ss c, In ss [ah_s1; ah_s3; ah_s4] -> In c [C_c_set; C_c_null] ->
  run_ (add_cond ss c) = (ah_leaf ss c, RS_running).
Proof.
  intros ss c Hs Hc. cbn [In] in Hs, Hc.
  destruct Hs as [<-|[<-|[<-|[]]]]; destruct Hc as [<-|[<-|[]]]; vm_compute; reflexivity.
Qed.

(* what is checked of every leaf and every intermediate state *)
Definition AH_SAVED : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition leaf_facts (ss : sstate) : Prop :=
  ss_pc ss = RA_LIB /\ ss_resv ss = None /\ sr_get (ss_regs ss) (Z_to_bv 5 10) = SLit 0 /\
  map (fun r => sr_get (ss_regs ss) (Z_to_bv 5 r)) AH_SAVED = map (fun r => sr_get ah_regs (Z_to_bv 5 r)) AH_SAVED /\
  skeleton (ss_mem ss) = skeleton ah_mem.
Lemma leaves_ok : forall ss c, In ss [ah_s1; ah_s3; ah_s4] -> In c [C_c_set; C_c_null] ->
  leaf_facts (ah_leaf ss c).
Proof.
  intros ss c Hs Hc. cbn [In] in Hs, Hc.
  destruct Hs as [<-|[<-|[<-|[]]]]; destruct Hc as [<-|[<-|[]]]; vm_compute; repeat split; reflexivity.
Qed.
Lemma skeletons_ok :
  skeleton (ss_mem ah_s0) = skeleton ah_mem /\ skeleton (ss_mem ah_s1) = skeleton ah_mem /\
  skeleton (ss_mem ah_s2) = skeleton ah_mem /\ skeleton (ss_mem ah_s3) = skeleton ah_mem /\
  skeleton (ss_mem ah_s4) = skeleton ah_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
End Run.
