From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_main_inv
  LLVMFuzzerTestOneInput_c memset_c memcpy_c diginet_personality_of_c check_personality_c
  check_refusal_c check_range_c check_bytes_c check_text_masks_c check_text_scribble_c
  check_text_seg7_c check_text_counter_c owed_counter_text_c text_arg_c owe_sysex_c
  diginet_fader_encode_c diginet_button_encode_c diginet_touch_encode_c diginet_vpot_encode_c
  diginet_jog_encode_c diginet_ring_encode_c diginet_meter_encode_c diginet_strip_leds_encode_c
  diginet_counter_leds_encode_c diginet_scribble_encode_c diginet_counter_encode_c
  diginet_sysex_encode_c.
Import ListNotations.
Open Scope Z_scope.

Section Compose.

(** The segment obligations. *)
Hypothesis SEXIT : seg_exit_stmt.
Hypothesis SLATCH : seg_latch_stmt.
Hypothesis SENTRY : seg_entry_stmt.
Hypothesis SHEAD : seg_head_stmt.
Hypothesis SRD0 : seg_rd0_stmt.
Hypothesis SRD1 : seg_rd1_stmt.
Hypothesis SRD3 : seg_rd3_stmt.
Hypothesis SRD5 : seg_rd5_stmt.
Hypothesis SRD6 : seg_rd6_stmt.
Hypothesis SRD8 : seg_rd8_stmt.
Hypothesis SRD9 : seg_rd9_stmt.
Hypothesis SRD11 : seg_rd11_stmt.
Hypothesis SRD12 : seg_rd12_stmt.
Hypothesis SRD13 : seg_rd13_stmt.
Hypothesis SRD14 : seg_rd14_stmt.
Hypothesis SRUN : seg_run_stmt.
Hypothesis SOWEHD : seg_owehd_stmt.
Hypothesis SOWE0 : seg_owe0_stmt.
Hypothesis SOWE5 : seg_owe5_stmt.
Hypothesis SOWE6 : seg_owe6_stmt.
Hypothesis SOWE7 : seg_owe7_stmt.
Hypothesis SOWE9 : seg_owe9_stmt.
Hypothesis SOWE10 : seg_owe10_stmt.
Hypothesis SOWE11 : seg_owe11_stmt.
Hypothesis SCHK : seg_chk_stmt.

(** The contracts of main's direct callees. *)
Hypothesis CPERS : check_personality_contract.
Hypothesis MEMS : memset_contract.
Hypothesis MEMC : memcpy_contract.
Hypothesis PERSOF : diginet_personality_of_contract.
Hypothesis TARG : text_arg_contract.
Hypothesis CTS : check_text_scribble_contract.
Hypothesis CT7 : check_text_seg7_contract.
Hypothesis CTC : check_text_counter_contract.
Hypothesis OCT : owed_counter_text_contract.
Hypothesis CTM : check_text_masks_contract.
Hypothesis OSX : owe_sysex_contract.
Hypothesis CREF : check_refusal_contract.
Hypothesis CRNG : check_range_contract.
Hypothesis CBYT : check_bytes_contract.
Hypothesis ENC0 : diginet_fader_encode_contract.
Hypothesis ENC1 : diginet_button_encode_contract.
Hypothesis ENC2 : diginet_touch_encode_contract.
Hypothesis ENC3 : diginet_vpot_encode_contract.
Hypothesis ENC4 : diginet_jog_encode_contract.
Hypothesis ENC5 : diginet_ring_encode_contract.
Hypothesis ENC6 : diginet_meter_encode_contract.
Hypothesis ENC7 : diginet_strip_leds_encode_contract.
Hypothesis ENC8 : diginet_counter_leds_encode_contract.
Hypothesis ENC9 : diginet_scribble_encode_contract.
Hypothesis ENC10 : diginet_counter_encode_contract.
Hypothesis ENC11 : diginet_sysex_encode_contract.

Variable E : cenv.
Hypothesis ENV : env_ok E.

Lemma compose_exit : exit_ok E.
Proof. apply SEXIT. exact ENV. Qed.

(** Every case of owe(), by the kind the reader left. *)
Lemma compose_owe : forall n, chk_ok E n -> forall k, rec_wf k -> owe_ok E n k.
Proof.
  intros n CH k RW.
  pose proof RW as RW'. destruct RW' as [HK _].
  destruct (Z_le_dec (k_kind k) 4) as [Hle|Hg4];
    [exact (SOWE0 E n ENV CH k RW Hle)|].
  destruct (Z.eq_dec (k_kind k) 5) as [H|N5]; [exact (SOWE5 E n ENV CH k RW H)|].
  destruct (Z.eq_dec (k_kind k) 6) as [H|N6]; [exact (SOWE6 E n ENV CH k RW H)|].
  destruct (Z.eq_dec (k_kind k) 7) as [H|N7]; [exact (SOWE7 E n ENV CH k RW (or_introl H))|].
  destruct (Z.eq_dec (k_kind k) 8) as [H|N8]; [exact (SOWE7 E n ENV CH k RW (or_intror H))|].
  destruct (Z.eq_dec (k_kind k) 9) as [H|N9]; [exact (SOWE9 E n ENV MEMC OSX CH k RW H)|].
  destruct (Z.eq_dec (k_kind k) 10) as [H|N10]; [exact (SOWE10 E n ENV MEMC CH k RW H)|].
  assert (H : k_kind k = 11) by lia. exact (SOWE11 E n ENV OSX CH k RW H).
Qed.

(** Every reader of the switch of fuzz_codec.c:578, plus its default. *)
Lemma compose_rd : forall n,
  rd_run E n -> rd_run_arm E n -> latch_ok E n 0x14a54 -> latch_ok E n 0x14b1c ->
  forall kind i, 0 <= kind <= 14 -> 0 <= i <= 2 -> rd_ok E n kind i.
Proof.
  intros n RR RRA LA LB kind i Hk Hi.
  destruct (Z.eq_dec kind 0) as [->|N0]; [exact (proj1 (SRD0 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 1) as [->|N1]; [exact (proj1 (SRD1 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 2) as [->|N2]; [exact (proj2 (SRD1 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 3) as [->|N3]; [exact (proj1 (SRD3 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 4) as [->|N4]; [exact (proj2 (SRD3 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 5) as [->|N5]; [exact (SRD5 E n ENV RR i Hi)|].
  destruct (Z.eq_dec kind 6) as [->|N6]; [exact (SRD6 E n ENV RR i Hi)|].
  destruct (Z.eq_dec kind 7) as [->|N7]; [exact (proj2 (SRD0 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 8) as [->|N8]; [exact (SRD8 E n ENV RR i Hi)|].
  destruct (Z.eq_dec kind 9) as [->|N9]; [exact (proj1 (SRD9 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 10) as [->|N10]; [exact (proj2 (SRD9 E n ENV RR i Hi))|].
  destruct (Z.eq_dec kind 11) as [->|N11]; [exact (SRD11 E n ENV MEMC RR i Hi)|].
  destruct (Z.eq_dec kind 12) as [->|N12]; [exact (SRD12 E n ENV PERSOF TARG CTS RRA i Hi)|].
  destruct (Z.eq_dec kind 13) as [->|N13]; [exact (SRD13 E n ENV PERSOF TARG CT7 CTC OCT RRA LA i Hi)|].
  assert (kind = 14) as -> by lia. exact (SRD14 E n ENV CTM LB i Hi).
Qed.

(** The loop, by induction on 256 - ops: at fuel 0 the head is unreachable, and one iteration of
    the body spends exactly one unit at the latch. *)
Lemma compose_loop : forall n, loop_ok E n.
Proof.
  induction n as [|n IH].
  { unfold loop_ok. intros. exfalso. lia. }
  destruct (SLATCH E n ENV compose_exit IH) as [LA LB].
  assert (CH : chk_ok E (S n)) by exact (SCHK E (S n) ENV CREF CRNG CBYT LA).
  assert (OW : forall k, rec_wf k -> owe_ok E (S n) k) by exact (compose_owe (S n) CH).
  assert (JO : forall k, rec_wf k -> join_ok E (S n) k) by exact (SOWEHD E (S n) ENV CH OW).
  destruct (SRUN E (S n) ENV ENC0 ENC1 ENC2 ENC3 ENC4 ENC5 ENC6 ENC7 ENC8 ENC9 ENC10 ENC11 JO)
    as [RR RRA].
  exact (SHEAD E (S n) ENV MEMS PERSOF (compose_rd (S n) RR RRA LA LB)).
Qed.

Lemma compose_entry : entry_ok E.
Proof. exact (SENTRY E ENV CPERS compose_exit (compose_loop 256)). Qed.

End Compose.

(** The walk of LLVMFuzzerTestOneInput, from its segments and its callees' contracts. *)
Theorem codec_main_of_segments :
  seg_exit_stmt -> seg_latch_stmt -> seg_entry_stmt -> seg_head_stmt ->
  seg_rd0_stmt -> seg_rd1_stmt -> seg_rd3_stmt -> seg_rd5_stmt -> seg_rd6_stmt -> seg_rd8_stmt ->
  seg_rd9_stmt -> seg_rd11_stmt -> seg_rd12_stmt -> seg_rd13_stmt -> seg_rd14_stmt ->
  seg_run_stmt -> seg_owehd_stmt ->
  seg_owe0_stmt -> seg_owe5_stmt -> seg_owe6_stmt -> seg_owe7_stmt -> seg_owe9_stmt ->
  seg_owe10_stmt -> seg_owe11_stmt -> seg_chk_stmt ->
  check_personality_contract -> memset_contract -> memcpy_contract ->
  diginet_personality_of_contract -> text_arg_contract -> check_text_scribble_contract ->
  check_text_seg7_contract -> check_text_counter_contract -> owed_counter_text_contract ->
  check_text_masks_contract -> owe_sysex_contract ->
  check_refusal_contract -> check_range_contract -> check_bytes_contract ->
  diginet_fader_encode_contract -> diginet_button_encode_contract ->
  diginet_touch_encode_contract -> diginet_vpot_encode_contract ->
  diginet_jog_encode_contract -> diginet_ring_encode_contract ->
  diginet_meter_encode_contract -> diginet_strip_leds_encode_contract ->
  diginet_counter_leds_encode_contract -> diginet_scribble_encode_contract ->
  diginet_counter_encode_contract -> diginet_sysex_encode_contract ->
  codec_main_contract.
Proof.
  intros SEXIT SLATCH SENTRY SHEAD SRD0 SRD1 SRD3 SRD5 SRD6 SRD8 SRD9 SRD11 SRD12 SRD13 SRD14
         SRUN SOWEHD SOWE0 SOWE5 SOWE6 SOWE7 SOWE9 SOWE10 SOWE11 SCHK
         CPERS MEMS MEMC PERSOF TARG CTS CT7 CTC OCT CTM OSX CREF CRNG CBYT
         ENC0 ENC1 ENC2 ENC3 ENC4 ENC5 ENC6 ENC7 ENC8 ENC9 ENC10 ENC11.
  unfold codec_main_contract, LLVM_CODEC, LLVM_CODEC_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc m lo data HD HN HMI ST LO SPA DJ HPB HPNZ RI DJR.
  assert (ENV : env_ok (mkCenv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc m lo data)).
  { unfold env_ok. cbn [c_ra c_sp c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9
                        c_s10 c_s11 c_p c_F c_fc c_m c_lo c_data].
    split; [exact HD|]. split; [exact HMI|]. split; [exact ST|]. split; [exact LO|].
    split; [exact SPA|]. split; [exact DJ|]. split; [exact HPB|]. split; [exact HPNZ|].
    split; [exact RI | exact DJR]. }
  change (evt rsegs
            (Qk (mkCenv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc m lo data))
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                     s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x132b8) fc None m (seg_rom rsegs))).
  apply (compose_entry SEXIT SLATCH SENTRY SHEAD SRD0 SRD1 SRD3 SRD5 SRD6 SRD8 SRD9 SRD11 SRD12
           SRD13 SRD14 SRUN SOWEHD SOWE0 SOWE5 SOWE6 SOWE7 SOWE9 SOWE10 SOWE11 SCHK
           CPERS MEMS MEMC PERSOF TARG CTS CT7 CTC OCT CTM OSX CREF CRNG CBYT
           ENC0 ENC1 ENC2 ENC3 ENC4 ENC5 ENC6 ENC7 ENC8 ENC9 ENC10 ENC11 _ ENV).
  cbn [c_data]. exact HN.
Qed.
