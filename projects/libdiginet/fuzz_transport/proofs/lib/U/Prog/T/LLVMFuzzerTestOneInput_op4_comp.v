(* Case 4 of the ubsan LLVMFuzzerTestOneInput (0x13a48, op_submit inlined, fuzz_transport.c:1068-1122), from the case
   entry to the latch 0x14574: the composition of
     op4_begin      (_op4_pre.v)      0x13a48 .. 0x13a94  before, op_begin, the struct zeroed
     op4_bytes      (_op4_bytes.v)    0x13a94 .. 0x13e94  kb, ab
     op4_key_lem    (_op4_key.v)      0x13e94 .. the split: key, display, g_raw, the raw arm's u16
     llvm_op4_tag_stmt (_op4_mid.v; proved in _op4_tag.v)   the tagged arm 0x141a4 .. the latch
     op4_raw_head   (_op4_raw.v)      0x14488 .. 0x144d0  w % 25, the take
     op4_raw_tail   (_op4_rawtail.v)  0x144d0 .. the latch: memcpy, submit, check_refusal_submit, settle
   against the model's op 4 (TOps.v op_submit_m, split by _op4_mid.v op_submit_split). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs LLVMFuzzerTestOneInput_op4_pre LLVMFuzzerTestOneInput_op4_bytes
  LLVMFuzzerTestOneInput_op4_key LLVMFuzzerTestOneInput_op4_raw LLVMFuzzerTestOneInput_op4_rawtail.
Import ListNotations.
Open Scope Z_scope.

Lemma fu8_range : forall D c c' b, fuzz_u8_m D c = (c', b) -> 0 <= b < 256.
Proof.
  intros D c c' b H. unfold fuzz_u8_m in H. destruct (fi_n c =? 0).
  - injection H as _ <-. lia.
  - injection H as _ <-. apply at8_range.
Qed.

(* the model's raw arm, its three calls named *)
Lemma op4_raw_model : forall B1 D c3 c3' lo8 c4 hi8 before display key B4 c5 nn,
  fuzz_u8_m D c3 = (c3', lo8) -> fuzz_u8_m D c3' = (c4, hi8) ->
  op4_raw_m B1 D c3 before display key = Some (B4, c5) ->
  nn = (if (lo8 + 256 * hi8) mod 25 <? fi_n c4 then (lo8 + 256 * hi8) mod 25 else fi_n c4) -> 0 <= fi_n c4 ->
  exists B2 B3 rc,
    diginet_session_submit_m B1
      (cmd_struct (sub D (fi_off c4) (Z.to_nat nn) ++ repeat (b8 0) (Z.to_nat (24 - nn))) nn display key)
      = Some (B2, rc) /\
    check_refusal_submit_m B2
      (cmd_struct (sub D (fi_off c4) (Z.to_nat nn) ++ repeat (b8 0) (Z.to_nat (24 - nn))) nn display key)
      rc before = Some (B3, tt) /\
    settle_m B3 0 = Some (B4, tt) /\
    c5 = FuzzIn (fi_off c4 + nn) (fi_n c4 - nn).
Proof.
  intros B1 D c3 c3' lo8 c4 hi8 before display key B4 c5 nn E1 E2 H Hnn HN4.
  pose proof (fu8_range _ _ _ _ E1) as R1. pose proof (fu8_range _ _ _ _ E2) as R2.
  unfold op4_raw_m, fuzz_u16_m in H. rewrite E1 in H. cbv beta iota in H.
  rewrite E2 in H. cbv beta iota in H.
  rewrite (op4_u16_model lo8 hi8 R1 R2) in H.
  change (SPEC_CMD_MAX + 1) with 25 in H.
  cbv beta iota zeta delta [fuzz_take_m] in H.
  rewrite <- Hnn in H.
  assert (HNN : 0 <= nn <= 24).
  { rewrite Hnn. pose proof (Z.mod_pos_bound (lo8 + 256 * hi8) 25 ltac:(lia)).
    destruct (Z.ltb_spec ((lo8 + 256 * hi8) mod 25) (fi_n c4)) as [L|L]; cbv beta iota; lia. }
  replace (nn mod 2 ^ 8) with nn in H by (symmetry; apply Z.mod_small; cbn; lia).
  set (cs := cmd_struct (sub D (fi_off c4) (Z.to_nat nn) ++ repeat (b8 0) (Z.to_nat (24 - nn))) nn display key)
    in H |- *.
  destruct (diginet_session_submit_m B1 cs) as [[B2 rc]|] eqn:ES1; [|discriminate H].
  destruct (check_refusal_submit_m B2 cs rc before) as [[B3 []]|] eqn:ES2; [|discriminate H].
  destruct (settle_m B3 0) as [[B4' []]|] eqn:ES3; [|discriminate H].
  apply opt_pair_inv in H. destruct H as [-> ->].
  exists B2, B3, rc. split; [reflexivity|]. split; [exact ES2|]. split; [exact ES3 | reflexivity].
Qed.

(* LLVMFuzzerTestOneInput_op_m at op 4 *)
Lemma op_m_4 : forall I B A D c k c1 opb, fuzz_u8_m D c = (c1, opb) -> opb mod 9 = 4 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k =
  match op_submit_m B D c1 with Some (B1, c2) => Some (B1, (c2, k)) | None => None end.
Proof.
  intros I B A D c k c1 opb E H4. unfold LLVMFuzzerTestOneInput_op_m. rewrite E. cbv beta iota zeta.
  rewrite H4. cbn [Z.eqb Pos.eqb]. reflexivity.
Qed.

(* op 4 from the case entry to the latch, given the tagged arm *)
Lemma llvm_op4_of_tag : memset_contract -> memcpy_contract -> diginet_session_submit_contract ->
  check_refusal_submit_contract -> settle_contract -> llvm_op4_tag_stmt -> llvm_op_stmt 4.
Proof.
  intros MSC MCP SUB CRS STL TAG.
  unfold llvm_op_stmt.
  intros data D regs0 m0 Sp lo ops c c1 B F fc ms A k B1' c2 k1 HC HOP.
  pose proof HC as HC0.
  destruct HC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                   _ & _ & _ & _ & HC1 & HOP4 & _).
  (* the model: op 4 is op_submit_m on the cursor after the op byte *)
  assert (EFU : fuzz_u8_m D c = (c1, snd (fuzz_u8_m D c)))
    by (rewrite HC1; destruct (fuzz_u8_m D c); reflexivity).
  rewrite (op_m_4 timg_ubsan B A D c k c1 (snd (fuzz_u8_m D c)) EFU HOP4) in HOP.
  destruct (op_submit_m B D c1) as [[Bx cx]|] eqn:ESUB; [|discriminate HOP].
  apply opt_pair_inv in HOP. destruct HOP as [-> HPK]. injection HPK as -> _.
  clear EFU.
  (* the model's op_submit, split at op_begin and the three bytes *)
  rewrite op_submit_split in ESUB.
  destruct (op_begin_m B) as [[B1 []]|] eqn:EB; [|discriminate ESUB].
  destruct (fuzz_u8_m D c1) as [c1' kb] eqn:E1.
  destruct (fuzz_u8_m D c1') as [c2' ab] eqn:E2.
  destruct (fuzz_u8_m D c2') as [c3 db] eqn:E3.
  destruct (fuzz_u8_m D c3) as [c3' lo8] eqn:E4.
  destruct (fuzz_u8_m D c3') as [c4 hi8] eqn:E5.
  (* the machine *)
  eapply op4_begin; [exact MSC | exact HC | exact EB |]. intros ms1 HS1.
  eapply op4_bytes; [exact HS1 | exact E1 | exact E2 |]. intros ms2 HS2.
  eapply (op4_key_lem data D regs0 m0 Sp lo ops c2' kb ab (S_queued B) B1 F fc ms2 c3 db c3' lo8 c4 hi8);
    [exact HS2 | exact E3 | exact E4 | exact E5 | |].
  - (* the tagged arm *)
    intros R0 ms3 HS3.
    rewrite R0 in ESUB. cbn [Z.eqb negb] in ESUB.
    exact (TAG data D regs0 m0 Sp lo ops (S_queued B) c3 B1 (Z.land db 1) (KEY (kb mod 9 + 1) ab) F fc ms3
             Bx cx HS3 ESUB).
  - (* the raw arm *)
    intros R0 ms3 HS3.
    assert (HN4 : 0 <= fi_n c4).
    { pose proof HS3 as HS3'.
      destruct HS3' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                        _ & _ & HC4 & _).
      unfold llvm_cursor in HC4. lia. }
    replace (negb (g_raw B1 =? 0)) with true in ESUB by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; exact R0).
    destruct (op4_raw_model B1 D c3 c3' lo8 c4 hi8 (S_queued B) (Z.land db 1) (KEY (kb mod 9 + 1) ab) Bx cx _
                E4 E5 ESUB eq_refl HN4) as (B2 & B3 & rc & ES1 & ES2 & ES3 & ->).
    eapply op4_raw_head; [exact HS3 |]. intros ms4 HS4.
    exact (op4_raw_tail data D regs0 m0 Sp lo ops c4 _ (S_queued B) B1 (Z.land db 1) (KEY (kb mod 9 + 1) ab)
             B2 B3 Bx rc F fc ms4 MCP SUB CRS STL HS4 ES1 ES2 ES3).
Qed.
