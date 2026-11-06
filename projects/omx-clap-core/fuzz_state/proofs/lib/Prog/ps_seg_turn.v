From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import ReaderRes parse_string_loops.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
Import ListNotations.
Open Scope Z_scope.

Definition pst_esc (e : Z) : option Z :=
  if e =? 34 then Some 34 else if e =? 92 then Some 92 else if e =? 47 then Some 47
  else if e =? 98 then Some 8 else if e =? 102 then Some 12 else if e =? 110 then Some 10
  else if e =? 114 then Some 13 else if e =? 116 then Some 9 else None.

Lemma pst_br : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma pst_le1 : forall v, 0 <= v < 256 -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma pst_sx : forall b : byte, bv_signed (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intros b. pose proof (pst_br b) as H.
  rewrite zb_signed. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec (bv_unsigned b) (2 ^ 63)); lia.
Qed.

Lemma pst_end_read : forall m (o : Z) bs (A : Z) (v : word),
  bytes_at rsegs m A (le8 v) -> 0 <= o -> o + Z.of_nat (length bs) <= 2 ^ 64 ->
  (A + 8 <= o \/ o + Z.of_nat (length bs) <= A) ->
  ov_read_bytes rsegs (write_to_mem m (wa o) bs) (wa A) 8 = Some (le8 v).
Proof.
  intros m o bs A v HB Ho Hl HD.
  assert (HB' : bytes_at rsegs (write_to_mem m (wa o) bs) A (le8 v)).
  { apply bytes_at_write_other; assumption. }
  replace (wa A) with (wa (A + 0)) by (rewrite Z.add_0_r; reflexivity).
  rewrite (bytes_at_read rsegs _ A (le8 v) 0 8 HB') by (rewrite ?length_le8; lia).
  change (Z.to_nat 0) with 0%nat. rewrite skipn_O.
  rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
Qed.

Lemma pst_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (st O q e : Z),
  s0 = Z_to_bv 64 st -> a0 = Z_to_bv 64 (O + 1) -> s10 = Z_to_bv 64 q ->
  0 <= q < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (st + 8)) 8 = Some (le8 (Z_to_bv 64 e)) ->
  Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (O + 1)) s3 s4 s5 s6 s7
             (Z_to_bv 64 q) s9 (Z_to_bv 64 q) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (if q <? e then 0x153a8 else 0x15474)) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x15464) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q st O q e
    Es0 Ea0 Es10 Hq He RE KQ.
  subst s0 a0 s10.
  step. step. step. step.
  rewrite (psl_ltu q e) by lia.
  revert KQ. destruct (Z.ltb_spec q e); cbv iota; intros KQ; apply evt_done; exact KQ.
Qed.

Local Ltac cf H := zify_cond H; rewrite ?unsigned_lit_wrap in H; rewrite ?pst_sx in H; rewrite ?Z.mod_small in H by lia.

Local Ltac fin :=
  cbv beta iota; cbv beta delta [pst_esc]; decide_tests; cbv beta delta [zxb];
  repeat match goal with H : bv_unsigned ?x = ?v |- context [bv_unsigned ?x] => rewrite H end;
  rewrite ?pst_le1 by lia; reflexivity.

Local Ltac tail x0 x1 x2 x3 HE :=
  eapply pst_tail with (st := x0) (O := x1) (q := x2) (e := x3);
  [ reflexivity | reflexivity | reflexivity | lia | lia
  | apply pst_end_read; [ exact HE | lia | rewrite length_le1; lia | rewrite length_le1; lia ]
  | fin ].

Lemma ps_turn : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len st P O : Z) (tb : list byte),
  ra = Z_to_bv 64 117 -> t0 = Z_to_bv 64 113 -> t1 = Z_to_bv 64 102 -> t2 = Z_to_bv 64 12 ->
  s0 = Z_to_bv 64 st -> a0 = Z_to_bv 64 (text + len) ->
  a4 = Z_to_bv 64 91 -> a5 = Z_to_bv 64 47 -> a6 = Z_to_bv 64 98 -> a7 = Z_to_bv 64 8 ->
  s2 = Z_to_bv 64 O -> s3 = Z_to_bv 64 9 -> s4 = Z_to_bv 64 34 -> s5 = Z_to_bv 64 32 -> s6 = Z_to_bv 64 92 ->
  s7 = Z_to_bv 64 101 -> s8 = Z_to_bv 64 P -> s9 = Z_to_bv 64 10 -> s11 = Z_to_bv 64 6 ->
  t3 = Z_to_bv 64 110 -> t4 = Z_to_bv 64 114 -> t5 = Z_to_bv 64 13 -> t6 = Z_to_bv 64 116 ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= P < text + len ->
  bytes_at rsegs m (st + 8) (le8 a0) -> wr_at rsegs m O 1 -> (O + 1 <= st + 8 \/ st + 16 <= O) ->
  evt rsegs
    (fun ms' => match rest_at tb text P with
     | [] => False
     | c :: r =>
       if c =? 34 then
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 34) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x155d8) fc None m (seg_rom rsegs)
       else if c <? 32 then
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x1558c) fc None m (seg_rom rsegs)
       else if c =? 92 then
         match r with
         | [] =>
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 92) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                         (Z_to_bv 64 (P + 1)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1558c) fc None m (seg_rom rsegs)
         | e :: _ =>
           if e =? 117 then
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 117) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                           (Z_to_bv 64 (P + 2)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x153dc) fc None m (seg_rom rsegs)
           else match pst_esc e with
           | Some b =>
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (O + 1)) s3 s4 s5 s6
                           s7 (Z_to_bv 64 (P + 2)) s9 (Z_to_bv 64 (P + 2)) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 (if P + 2 <? text + len then 0x153a8 else 0x15474)) fc None
                      (write_to_mem m (wa O) [Z_to_bv 8 b]) (seg_rom rsegs)
           | None =>
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                           (Z_to_bv 64 (P + 2)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1558c) fc None m (seg_rom rsegs)
           end
         end
       else
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (O + 1)) s3 s4 s5 s6 s7
                       (Z_to_bv 64 (P + 1)) s9 (Z_to_bv 64 (P + 1)) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if P + 1 <? text + len then 0x153a8 else 0x15474)) fc None
                  (write_to_mem m (wa O) [Z_to_bv 8 c]) (seg_rom rsegs)
     end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len st P O tb
    Era Et0 Et1 Et2 Es0 Ea0 Ea4 Ea5 Ea6 Ea7 Es2 Es3 Es4 Es5 Es6 Es7 Es8 Es9 Es11 Et3 Et4 Et5 Et6 HB HL Hend HP HE HW HD.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  pose proof HW as (Ho0 & Ho1 & _).
  pose proof (wr_at_store_ok rsegs m O 1 0 1 HW ltac:(lia) ltac:(lia)) as HS. rewrite Z.add_0_r in HS.
  subst ra t0 t1 t2 s0 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6.
  destruct (nth_error tb (Z.to_nat (P - text))) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  pose proof (psl_read m text tb P c HB ltac:(lia) Hc) as RD.
  rewrite (psl_rest_cons tb text P c ltac:(lia) Hc).
  pose proof (pst_br c) as HZ.
  step. step. clear RD.
  if_cases HC1.
  - cf HC1. apply evt_done. fin.
  - cf HC1. step. if_cases HC2.
    + cf HC2. apply evt_done. fin.
    + cf HC2. step. step. if_cases HC3.
      * cf HC3. step. step. tail st O (P + 1) (text + len) HE.
      * cf HC3. step. if_cases HC4.
        -- cf HC4. apply evt_done. rewrite (psl_rest_end tb text (P + 1)) by lia. fin.
        -- cf HC4.
           destruct (nth_error tb (Z.to_nat (P + 1 - text))) as [e|] eqn:He; [|apply nth_error_None in He; lia].
           pose proof (psl_read m text tb (P + 1) e HB ltac:(lia) He) as RD1.
           rewrite (psl_rest_cons tb text (P + 1) e ltac:(lia) He).
           pose proof (pst_br e) as HZe.
           step. step. clear RD1. step. if_cases HC5.
           ++ cf HC5. step. if_cases HC6.
              ** cf HC6. step. if_cases HC7.
                 --- cf HC7. step. step. step. tail st O (P + 2) (text + len) HE.
                 --- cf HC7. step. if_cases HC8.
                     +++ cf HC8. apply evt_done. fin.
                     +++ cf HC8. step. step. step. tail st O (P + 2) (text + len) HE.
              ** cf HC6. step. if_cases HC7.
                 --- cf HC7. step. step. step. tail st O (P + 2) (text + len) HE.
                 --- cf HC7. step. if_cases HC8.
                     +++ cf HC8. apply evt_done. fin.
                     +++ cf HC8. step. step. step. tail st O (P + 2) (text + len) HE.
           ++ cf HC5. step. if_cases HC6.
              ** cf HC6. step. if_cases HC7.
                 --- cf HC7. step. step. step. tail st O (P + 2) (text + len) HE.
                 --- cf HC7. step. if_cases HC8.
                     +++ cf HC8. apply evt_done. fin.
                     +++ cf HC8. step. step. step. tail st O (P + 2) (text + len) HE.
              ** cf HC6. step. if_cases HC7.
                 --- cf HC7. step. step. step. tail st O (P + 2) (text + len) HE.
                 --- cf HC7. step. if_cases HC8.
                     +++ cf HC8. step. step. step. tail st O (P + 2) (text + len) HE.
                     +++ cf HC8. step. if_cases HC9.
                         *** cf HC9. apply evt_done. fin.
                         *** cf HC9. apply evt_done. fin.
Qed.
