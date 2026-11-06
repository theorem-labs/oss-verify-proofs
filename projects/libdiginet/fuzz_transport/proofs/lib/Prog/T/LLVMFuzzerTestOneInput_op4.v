(* Case 4 of the op loop of LLVMFuzzerTestOneInput in the plain image (fuzz_transport.c:1187-1189
   `case 4: op_submit(&in); break;`, op_submit at :1065-1119 inlined), from the case entry 0x13910 to the latch
   0x1428c: llvm_op4. The model is the op =? 4 branch of TOps.v LLVMFuzzerTestOneInput_op_m, op_submit_m.

   The walk is cut at the program points of LLVMFuzzerTestOneInput_op4k.v (op4_j 0x13df4, op4_t1 0x1400c, op4_t2
   0x1408c, op4_t3 0x140ec, op4_t4 0x14260), one file per segment:
     _op4e.v   0x13910 -> 0x13df4   op_begin, the struct zeroed, before saved, the three bytes (op4_entry)
     _op4r.v   0x13df4 -> latch     the raw arm, g_raw != 0 (op4_raw)
     _op4t1.v  0x13df4 -> 0x1400c   memset(&g_cmd[serial]), lb, the struct, memcpy, the F0 13 xx 70 scan (op4_tag1)
     _op4t2.v  0x1400c -> 0x1408c   the coalescable test and the queue scan (op4_tag2)
     _op4t3.v  0x1408c -> 0x140ec   want, submit, check_refusal_submit, check_latest_submit (op4_tag3)
     _op4t4.v  0x140ec -> 0x14260   the record of the command (op4_tag4)
     _op4t5.v  0x14260 -> latch     g_ncmd++, the cursor, settle (op4_tag5)
   The two scan loops are TR6Op4Scan's LLVMFuzzerTestOneInput_op4scan.v (op4_sys_scan, op4_sys_short, op4_find_scan).
   llvm_op4_from chains the segment statements along the model; llvm_op4 discharges them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract
  diginet_session_submit_c check_refusal_submit_c check_latest_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4k LLVMFuzzerTestOneInput_op4scan
  LLVMFuzzerTestOneInput_op4e LLVMFuzzerTestOneInput_op4r LLVMFuzzerTestOneInput_op4t1 LLVMFuzzerTestOneInput_op4t2
  LLVMFuzzerTestOneInput_op4t3 LLVMFuzzerTestOneInput_op4t4 LLVMFuzzerTestOneInput_op4t5.
Import ListNotations.
Open Scope Z_scope.

Section OP4.
Context (data : Z) (D : list byte).

(* op4_tagged_m (op4k, TOps.v:237-275) through the o4_* names of the program points *)
Lemma o4_tagged_eq : forall B1 c3 before display key,
  op4_tagged_m B1 D c3 before display key =
  if CMDS_MAX <=? g_ncmd B1 then None else
  match o4_atopt B1 key with
  | None => None
  | Some at_ =>
    match diginet_session_submit_m (o4_B2 B1) (o4_cs D B1 c3 display key) with
    | None => None
    | Some (B3, rc) =>
      match check_refusal_submit_m B3 (o4_cs D B1 c3 display key) rc before with
      | None => None
      | Some (B4, _) =>
        match (if o4_sys D B1 c3 then Some (B4, tt) else check_latest_submit_m B4 rc (o4_want D B1 c3 at_)) with
        | None => None
        | Some (B5, _) =>
          match (if o4_want D B1 c3 at_ =? SPEC_OK then o4_rec D B5 B1 c3 display key at_ else Some B5) with
          | None => None
          | Some B6 =>
            match settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0 with
            | None => None
            | Some (B8, _) => Some (B8, o4_c5 D c3)
            end
          end
        end
      end
    end
  end.
Proof.
  intros B1 c3 before display key.
  unfold op4_tagged_m, o4_atopt, o4_want, o4_rec, o4_sys, o4_cs, o4_cb, o4_B2, o4_c5, o4_off, o4_n, o4_tk,
    o4_len, o4_c4.
  destruct (fuzz_u8_m D c3) as [c4 lb]. cbn [fst snd].
  destruct (fuzz_take_m c4 (lb mod 22 + 3 - 3)) as [[c5 off] n]. cbn [fst snd].
  reflexivity.
Qed.

(* the queue position the coalescing search gives is -1 or an index of g_q / g_cmd *)
Lemma o4_atopt_rng : forall B1 key at_, o4_atopt B1 key = Some at_ -> at_ = -1 \/ 0 <= at_ < CMDS_MAX.
Proof.
  intros B1 key at_ H. unfold o4_atopt in H.
  destruct (negb (h_coalescable_m key =? 0)).
  - destruct (op4_find_rng _ _ _ 0 at_ ltac:(lia) H) as [E|E]; [left; exact E | right; lia].
  - left. injection H as <-. reflexivity.
Qed.

(* The case, from the segment statements. *)
Lemma llvm_op4_from :
  op4_entry_stmt data D -> op4_raw_stmt data D -> op4_tag1_stmt data D -> op4_tag2_stmt data D ->
  op4_tag3_stmt data D -> op4_tag4_stmt data D -> op4_tag5_stmt data D ->
  forall Sp lo ops c c1 B B' cout m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  memset_contract -> memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract ->
  check_latest_submit_contract -> settle_contract ->
  llvm_case data D m0 gp tp 4 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  op_submit_m B D c1 = Some (B', cout) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops cout B'
                 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros SE SR ST1 ST2 ST3 ST4 ST5 Sp lo ops c c1 B B' cout m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    F fc ms Q MSC MCC SBC CRC CLC STC H HOP HK.
  rewrite op_submit_split in HOP.
  destruct (op_begin_m B) as [[B1 u]|] eqn:EB1; try rewrite EB1 in HOP; [|discriminate HOP]. destruct u.
  cbv beta iota in HOP.
  destruct (fuzz_u8_m D c1) as [c1' kb] eqn:E1. try rewrite E1 in HOP. cbv beta iota in HOP.
  destruct (fuzz_u8_m D c1') as [c2' ab] eqn:E2. try rewrite E2 in HOP. cbv beta iota in HOP.
  destruct (fuzz_u8_m D c2') as [c3 db] eqn:E3. try rewrite E3 in HOP. cbv beta iota in HOP.
  eapply SE; [exact MSC | exact H | exact EB1 |].
  intros ms' HJ.
  unfold o4_c3, o4_display, o4_key in HJ. rewrite E1 in HJ. cbn [fst snd] in HJ.
  rewrite E2 in HJ. cbn [fst snd] in HJ. rewrite E3 in HJ. cbn [fst snd] in HJ.
  destruct (Z.eqb_spec (g_raw B1) 0) as [GR|GR].
  - (* g_raw == 0: the tagged arm (:1083-1118) *)
    assert (EG : (g_raw B1 =? 0) = true) by (apply Z.eqb_eq; exact GR).
    try rewrite EG in HOP. cbn [negb] in HOP.
    rewrite o4_tagged_eq in HOP.
    destruct (CMDS_MAX <=? g_ncmd B1) eqn:NC; try rewrite NC in HOP; [discriminate HOP|]. apply Z.leb_gt in NC.
    destruct (o4_atopt B1 (KEY (kb mod 9 + 1) ab)) as [at_|] eqn:EA; try rewrite EA in HOP; [|discriminate HOP].
    cbv beta iota in HOP.
    pose proof (o4_atopt_rng _ _ _ EA) as HAT.
    destruct (diginet_session_submit_m (o4_B2 B1) (o4_cs D B1 c3 (Z.land db 1) (KEY (kb mod 9 + 1) ab)))
      as [[B3 rc]|] eqn:ES; try rewrite ES in HOP; [|discriminate HOP].
    cbv beta iota in HOP.
    destruct (check_refusal_submit_m B3 (o4_cs D B1 c3 (Z.land db 1) (KEY (kb mod 9 + 1) ab)) rc (S_queued B))
      as [[B4 u4]|] eqn:ER; try rewrite ER in HOP; [|discriminate HOP]. destruct u4.
    cbv beta iota in HOP.
    destruct (if o4_sys D B1 c3 then Some (B4, tt) else check_latest_submit_m B4 rc (o4_want D B1 c3 at_))
      as [[B5 u5]|] eqn:EL; try rewrite EL in HOP; [|discriminate HOP]. destruct u5.
    cbv beta iota in HOP.
    destruct (if o4_want D B1 c3 at_ =? SPEC_OK then o4_rec D B5 B1 c3 (Z.land db 1) (KEY (kb mod 9 + 1) ab) at_
              else Some B5) as [B6|] eqn:E6; try rewrite E6 in HOP; [|discriminate HOP].
    cbv beta iota in HOP.
    destruct (settle_m (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) 0) as [[B8 u8]|] eqn:E8;
      try rewrite E8 in HOP; [|discriminate HOP].
    destruct u8. injection HOP as <- <-.
    eapply ST1; [exact MSC | exact MCC | exact op4_sys_scan | exact op4_sys_short | exact HJ | exact GR | exact NC |].
    intros ms1 H1.
    eapply ST2; [exact op4_find_scan | exact H1 | exact EA |].
    intros ms2 H2.
    eapply ST3; [exact SBC | exact CRC | exact CLC | exact H2 | exact HAT | exact ES | exact ER | exact EL |].
    intros ms3 H3.
    eapply ST4; [exact MCC | exact H3 | exact HAT | exact E6 |].
    intros ms4 H4.
    eapply ST5; [exact STC | exact H4 | exact E8 | exact HK].
  - (* g_raw != 0: the raw arm (:1075-1081) *)
    assert (EG : (g_raw B1 =? 0) = false) by (apply Z.eqb_neq; exact GR).
    try rewrite EG in HOP. cbn [negb] in HOP.
    eapply SR; [exact MCC | exact SBC | exact CRC | exact STC | exact HJ | exact GR | exact HOP | exact HK].
Qed.

End OP4.

(* Case 4: from the case entry 0x13910 to the latch 0x1428c along op_submit_m (the statement with gp before
   tp, the type the final wiring takes). *)
Lemma llvm_op4 : forall data D Sp lo ops c c1 c2 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q,
  memset_contract -> memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract ->
  check_latest_submit_contract -> settle_contract ->
  llvm_case data D m0 gp tp 4 Sp lo ops c c1 B ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms ->
  op_submit_m B D c1 = Some (B1, c2) ->
  (forall ms', llvm_latch data D m0 gp tp Sp lo ops c2 B1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms' ->
               evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D Sp lo ops c c1 c2 B B1 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q.
  exact (llvm_op4_from data D (op4_entry data D) (op4_raw data D) (op4_tag1 data D) (op4_tag2 data D)
           (op4_tag3 data D) (op4_tag4 data D) (op4_tag5 data D)
           Sp lo ops c c1 B B1 c2 m0 gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ms Q).
Qed.
