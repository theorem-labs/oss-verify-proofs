From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model disco_json_text reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_defs slot_ser_pure slot_ser_tokb slot_ser_Pq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_P1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c snprintf_c snprintf_stk_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import jtok_is_c reac_box_name_c disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_pure uslot_ser_tokb uslot_ser uslot_ser_Pq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_P1 uslot_ser_P2 uslot_ser_P3 uslot_ser_P4.
Import ListNotations.
Open Scope Z_scope.

Lemma uobj_body : reac_box_name_contract -> snprintf_stk_contract -> jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count k : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (Q : machine_state -> Prop),
  up3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s9 = Z_to_bv 64 count -> s0 = Z_to_bv 64 k -> s11 = Z_to_bv 64 1 ->
  upinv X lo buf now T os vpad canary m0 k m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 : word),
     upinv X lo buf now T os vpad canary m0 (k + 1) m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 (k + 1)) y9 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 y20 y21 y22 y23 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 (if k + 1 =? count then 0x14174 else 0x13f38)) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13f38) fc None m (seg_rom rsegs)).
Proof.
  intros BNC SNK JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F0 F fc m0 m canary X lo buf now count k T os vpad Q CX Hk Esp Es9 Es0 Es11 PI TM FC FL K.
  destruct (up3_count X lo buf now count T os vpad CX) as (Ec & Hc & _).
  pose proof CX as (HX0 & HX16 & HX1 & Hnow & Hb & LT & TOK & LV & JR & Hbl & HLO & HI).
  pose proof PI as (HT & _).
  pose proof (rd_sub m (X + 544) T 384 4 HT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  subst sp s9 s0 s11.
  step. rewrite lw_val by (apply length_sub; rewrite ?LT; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T). rewrite <- Ec.
  step. rewrite lts_lit by lia. replace (0 <? count) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  step. step. step. step. step. step. step. step.
  replace (Z_to_bv 64 (X + 1056 + bv_unsigned (Z_to_bv 64 k) * 144)) with (Z_to_bv 64 (X + 1056 + 144 * k))
    by (rewrite unsigned_lit by lia; f_equal; lia).
  eapply (umac_loop SNK JT (Z.to_nat k)) with (j := 0) (k := k) (X := X) (count := count) (lo := lo) (buf := buf)
    (now := now) (T := T) (os := os) (vpad := vpad) (m0 := m0) (F0 := F0) (canary := canary);
    [ first [ exact CX | exact PI | exact TM | exact FC | exact FL | reflexivity | (f_equal; lia) | lia ] .. |].
  intros m1 F1 fc1 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y28 y29 y30 y31 PI1 TM1 FC1 FL1.
  eapply (urole_seg JT) with (k := k) (X := X) (count := count) (lo := lo) (buf := buf) (now := now) (T := T)
    (os := os) (vpad := vpad) (m0 := m0) (canary := canary);
    [ first [ exact CX | exact PI1 | exact TM1 | reflexivity | lia ] .. |].
  intros m2 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 PI2 TM2.
  eapply (umodel_seg BNC SNK JT) with (k := k) (kk := k + 1) (X := X) (count := count) (lo := lo) (buf := buf)
    (now := now) (T := T) (os := os) (vpad := vpad) (m0 := m0) (F0 := F0) (canary := canary);
    [ first [ exact CX | exact PI2 | exact TM2 | exact FC1 | exact FL1 | reflexivity | lia ] .. |].
  intros m3 F3 fc3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w21 w28 w29 w30 w31 PI3 TM3 FC3 FL3.
  eapply (utail_seg SNK JT) with (k := k) (kk := k + 1) (X := X) (count := count) (lo := lo) (buf := buf)
    (now := now) (T := T) (os := os) (vpad := vpad) (m0 := m0) (F0 := F0) (canary := canary);
    [ first [ exact CX | exact PI3 | exact TM3 | exact FC3 | exact FL3 | reflexivity | lia ] .. |].
  intros m4 F4 fc4 v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 PI4 TM4 FC4 FL4.
  eapply K; [exact PI4 | exact TM4 | exact FC4 | exact FL4].
Qed.

Lemma uobj_loop : reac_box_name_contract -> snprintf_stk_contract -> jtok_is_contract ->
  forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F0 F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (canary : word)
    (X lo buf now count k : Z) (T : list byte) (os : list jobj) (vpad : list byte)
    (Q : machine_state -> Prop),
  Z.of_nat n = count - k -> up3ctx X lo buf now count T os vpad -> 0 <= k < count ->
  sp = Z_to_bv 64 X -> s9 = Z_to_bv 64 count -> s0 = Z_to_bv 64 k -> s11 = Z_to_bv 64 1 ->
  upinv X lo buf now T os vpad canary m0 k m -> MemNorm.task_mem rsegs m -> frm0 fc -> fl F0 F ->
  (forall (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
          (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 : word),
     upinv X lo buf now T os vpad canary m0 count m' -> MemNorm.task_mem rsegs m' -> frm0 fc' -> fl F0 F' ->
     evt rsegs Q (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 count) y9 y10 y11 y12 y13 y14 y15 y16 y17
                         s2 s3 y20 y21 y22 y23 s8 s9 s10 s11 y28 y29 y30 y31)
                     F' (Z_to_bv 64 0x14174) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13f38) fc None m (seg_rom rsegs)).
Proof.
  intros BNC SNK JT n. induction n as [|n IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F0 F fc m0 m canary X lo buf now count k T os vpad Q En CX Hk Esp Es9 Es0 Es11 PI TM FC FL K; [lia|].
  eapply (uobj_body BNC SNK JT) with (k := k) (X := X) (count := count) (lo := lo) (buf := buf) (now := now)
    (T := T) (os := os) (vpad := vpad) (m0 := m0) (F0 := F0) (canary := canary);
    [ first [ exact CX | exact PI | exact TM | exact FC | exact FL | eassumption | lia ] .. |].
  intros m1 F1 fc1 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 PI1 TM1 FC1 FL1.
  destruct (Z.eqb_spec (k + 1) count) as [E|E].
  - rewrite E in PI1 |- *. eapply K; [exact PI1 | exact TM1 | exact FC1 | exact FL1].
  - eapply (IH y1 sp gp tp y5 y6 y7 (Z_to_bv 64 (k + 1)) y9 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 y20 y21 y22 y23 s8
             s9 s10 s11 y28 y29 y30 y31 F0 F1 fc1 m0 m1 canary X lo buf now count (k + 1) T os vpad Q);
      [ first [ exact CX | exact PI1 | exact TM1 | exact FC1 | exact FL1 | eassumption | reflexivity | lia ] .. |].
    exact K.
Qed.
