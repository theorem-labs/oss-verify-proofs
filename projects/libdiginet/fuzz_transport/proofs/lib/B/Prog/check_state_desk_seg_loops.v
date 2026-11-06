(* check_state_desk_seg_loops: the two inlined spec_strz_len loops of check_state_desk in image B
   (fuzz_transport.asan-ubsan, 0x855e8 .. 0x8569c): s1 = OW.desk_body and its UBSan NULL and wrap tests, then the
   checked 1-byte loads of OW.desk_body + 15 + i and OW.desk_body + 24 + i, i = 0 .. 8, up to the first 0 (s2 = vn,
   s3 = nn), each after its UBSan wrap test. Image B's twin of lib/A/Prog/check_state_desk_seg_loops.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section Pieces.
Variables (RNG : ExecF.footprint)
  (sp gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Local Notation ST pc x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 mm :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
           s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* ---- the two inlined spec_strz_len loops: 0x855e8 .. 0x8569c ---- *)

Local Notation DB Bw := (TW.u_at Bw TW.A_OW_desk_body 8).
Local Notation XONES x := (Z_to_bv 64 (Z.lxor x 18446744073709551615)).

Lemma csd_loops_F : forall (m : word -> option byte) (p : Z) (NB Bw : list byte) (fr : TI.tframe) (vn nn : nat)
    (ra s1 x10 x11 x12 x14 x15 x16 x17 s2 s3 : word) (Q : machine_state -> Prop),
  csd_mem m p NB Bw fr vn nn -> csd_rng RNG (bv_unsigned sp) p NB fr vn nn -> csd_bnd p NB Bw fr ->
  TC.frame_strz_len (Some fr) (DB Bw + 15) = Some vn ->
  TC.frame_strz_len (Some fr) (DB Bw + 24) = Some nn ->
  (forall y10 y12 y13 y14 y15 : word,
     ExecF.evtF rsegs RNG Q (ST 0x8569c ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw + 24))
                               y10 (Z_to_bv 64 (DB Bw + 15)) y12 y13 y14 y15 x16 x17
                               (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 (Z.of_nat nn)) (Z_to_bv 64 ASAN_K) m)) ->
  ExecF.evtF rsegs RNG Q (ST 0x855e8 ra (Z_to_bv 64 (TW.u_at NB 24 8)) s1 x10 x11 x12 (Z_to_bv 64 TB_OW)
                            x14 x15 x16 x17 s2 s3 (Z_to_bv 64 ASAN_K) m).
Proof.
  intros m p NB Bw fr vn nn ra s1 x10 x11 x12 x14 x15 x16 x17 s2 s3 Q MEM RNGH BND HVN HNN CONT.
  csd_prep MEM RNGH BND.
  pose proof (PW.csd_strz fr _ vn HVN) as (SV1 & SV2 & SV3 & SV4 & SV5).
  pose proof (PW.csd_strz fr _ nn HNN) as (SN1 & SN2 & SN3 & SN4 & SN5).
  change (DS.b8 0) with (Z_to_bv 8 0) in SV4, SV5, SN4, SN5.
  pose proof (TWL.u_at_range Bw TW.A_OW_desk_body 8) as RDB. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RDB.
  assert (RD7 : ov_read_bytes rsegs m (wa (TB_OW + 248)) 8 = Some (TW.sub Bw TW.A_OW_desk_body 8))
    by (apply csd_rdall; [exact M7 | apply csd_len_sub; unfold TW.A_OW_desk_body, TW.OFF_OW, TW.W_LEN in *; lia]).
  set (LF := Z.of_nat (length (TI.tf_bytes fr))) in *.
  assert (FRB : forall x, TI.tf_addr fr <= x < TI.tf_addr fr + LF ->
    ExecF.rng RNG x 1 /\ ExecF.rng RNG (x / 8 + 2147450880) 1 /\
    exists k : byte, mrd rsegs m (wa (x / 8 + 2147450880)) = Some k /\ (bv_signed k = 0 \/ x mod 8 < bv_signed k)).
  { intros x Hx. split; [apply RA; do 7 right; left; exact Hx|].
    split; [apply RA; do 8 right; left; exists x; split; [exact Hx | reflexivity]|]. exact (M16 x Hx). }
  assert (HDB : DB Bw + 25 <= 2 ^ 63) by lia.
  unfold TB_OW, ASAN_K in *.
  (* ---- 0x85660: the loop over name, at OW.desk_body + 24 + i (s1 = OW.desk_body + 24, s3 = 9) ---- *)
  assert (LOOP2 : forall (k i : nat), (k = nn - i)%nat -> (i <= nn)%nat -> (i < 9)%nat ->
    forall (y10 y14 y15 : word),
    ExecF.evtF rsegs RNG Q (ST 0x85660 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw + 24))
                              y10 (Z_to_bv 64 (DB Bw + 15)) (Z_to_bv 64 (Z.of_nat i)) (XONES (DB Bw + 24)) y14 y15
                              x16 x17 (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 9) (Z_to_bv 64 2147450880) m)).
  { induction k as [|k IH]; intros i Hk Hi H9 y10 y14 y15.
    - (* i = nn: the byte is the 0 that ends the name; s3 = nn *)
      assert (XI : TI.tf_addr fr <= DB Bw + 24 + Z.of_nat i < TI.tf_addr fr + LF) by lia.
      destruct (FRB _ XI) as (RX & RXS & kx & MKX & SKX).
      pose proof (Z.mod_pos_bound (DB Bw + 24 + Z.of_nat i) 8 ltac:(lia)) as MBX.
      assert (BODY : forall y14' y15' : word,
        ExecF.evtF rsegs RNG Q (ST 0x85678 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw + 24))
                                  (Z_to_bv 64 (DB Bw + 24 + Z.of_nat i)) (Z_to_bv 64 (DB Bw + 15))
                                  (Z_to_bv 64 (Z.of_nat i)) (XONES (DB Bw + 24)) y14' y15'
                                  x16 x17 (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 9) (Z_to_bv 64 2147450880) m)).
      { intros y14' y15'.
        pose proof (csd_rd1 m _ _ (Z.to_nat (DB Bw + 24 - TI.tf_addr fr) + i) (DB Bw + 24 + Z.of_nat i) M15
                      ltac:(lia) ltac:(lia)) as RB.
        step. clear RB. step. rewrite PW.csd_zxb0.
        assert (Ei : i = nn) by lia. subst i.
        rewrite (SN5 H9), Z.eqb_refl. cbv iota.
        step. try rewrite (unsigned_lit (Z.of_nat nn)) by lia. try rewrite Z.add_0_r.
        apply CONT. }
      step. br_false ltac:(exact (csd_ltu_xor (DB Bw + 24) (Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia))).
      csd_chk1 ltac:(try rewrite (unsigned_lit (DB Bw + 24)) by lia; try rewrite (unsigned_lit (Z.of_nat i)) by lia)
        (DB Bw + 24 + Z.of_nat i) MKX SKX RXS BODY.
    - (* i < nn: a byte that is not 0; on to i + 1, or out of the loop at i + 1 = 9 = nn *)
      assert (XI : TI.tf_addr fr <= DB Bw + 24 + Z.of_nat i < TI.tf_addr fr + LF) by lia.
      destruct (FRB _ XI) as (RX & RXS & kx & MKX & SKX).
      pose proof (Z.mod_pos_bound (DB Bw + 24 + Z.of_nat i) 8 ltac:(lia)) as MBX.
      assert (BODY : forall y14' y15' : word,
        ExecF.evtF rsegs RNG Q (ST 0x85678 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw + 24))
                                  (Z_to_bv 64 (DB Bw + 24 + Z.of_nat i)) (Z_to_bv 64 (DB Bw + 15))
                                  (Z_to_bv 64 (Z.of_nat i)) (XONES (DB Bw + 24)) y14' y15'
                                  x16 x17 (Z_to_bv 64 (Z.of_nat vn)) (Z_to_bv 64 9) (Z_to_bv 64 2147450880) m)).
      { intros y14' y15'.
        pose proof (csd_rd1 m _ _ (Z.to_nat (DB Bw + 24 - TI.tf_addr fr) + i) (DB Bw + 24 + Z.of_nat i) M15
                      ltac:(lia) ltac:(lia)) as RB.
        step. clear RB. step. rewrite PW.csd_zxb0.
        rewrite (proj2 (Z.eqb_neq _ 0) (SN4 i ltac:(lia))). cbv iota.
        step. try rewrite (unsigned_lit (Z.of_nat i)) by lia.
        step. rewrite PW.csd_eqb_lit by lia.
        destruct (Z.eqb_spec (Z.of_nat i + 1) 9) as [E9|E9]; cbn [negb]; cbv iota.
        + step. replace (Z_to_bv 64 9) with (Z_to_bv 64 (Z.of_nat nn)) by (f_equal; lia). apply CONT.
        + replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
          apply (IH (S i)); lia. }
      step. br_false ltac:(exact (csd_ltu_xor (DB Bw + 24) (Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia))).
      csd_chk1 ltac:(try rewrite (unsigned_lit (DB Bw + 24)) by lia; try rewrite (unsigned_lit (Z.of_nat i)) by lia)
        (DB Bw + 24 + Z.of_nat i) MKX SKX RXS BODY. }
  (* ---- 0x85648: the UBSan wrap test of OW.desk_body + 24 and the second loop's set-up: a2 = 0,
     s1 = OW.desk_body + 24, a3 = 2^64 - 1 - s1, s3 = 9 ---- *)
  assert (ENT2 : forall (y10 y12 y13 y14 y15 y19 : word),
    ExecF.evtF rsegs RNG Q (ST 0x85648 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw))
                              y10 (Z_to_bv 64 (DB Bw + 15)) y12 y13 y14 y15
                              x16 x17 (Z_to_bv 64 (Z.of_nat vn)) y19 (Z_to_bv 64 2147450880) m)).
  { intros y10 y12 y13 y14 y15 y19.
    step. step. br_false ltac:(exact (proj1 (csd_ltu_neg 25 (DB Bw) ltac:(lia) ltac:(lia)))).
    step. step. try rewrite (unsigned_lit (DB Bw)) by lia. step. step.
    try rewrite (unsigned_lit (DB Bw + 24)) by lia.
    apply (LOOP2 nn 0%nat); lia. }
  (* ---- 0x85608: the loop over version, at OW.desk_body + 15 + i (a1 = OW.desk_body + 15, s2 = 9) ---- *)
  assert (LOOP1 : forall (k i : nat), (k = vn - i)%nat -> (i <= vn)%nat -> (i < 9)%nat ->
    forall (y10 y14 y15 : word),
    ExecF.evtF rsegs RNG Q (ST 0x85608 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw))
                              y10 (Z_to_bv 64 (DB Bw + 15)) (Z_to_bv 64 (Z.of_nat i)) (XONES (DB Bw + 15)) y14 y15
                              x16 x17 (Z_to_bv 64 9) s3 (Z_to_bv 64 2147450880) m)).
  { induction k as [|k IH]; intros i Hk Hi H9 y10 y14 y15.
    - (* i = vn: the byte is the 0 that ends the version; s2 = vn *)
      assert (XI : TI.tf_addr fr <= DB Bw + 15 + Z.of_nat i < TI.tf_addr fr + LF) by lia.
      destruct (FRB _ XI) as (RX & RXS & kx & MKX & SKX).
      pose proof (Z.mod_pos_bound (DB Bw + 15 + Z.of_nat i) 8 ltac:(lia)) as MBX.
      assert (BODY : forall y14' y15' : word,
        ExecF.evtF rsegs RNG Q (ST 0x85620 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw))
                                  (Z_to_bv 64 (DB Bw + 15 + Z.of_nat i)) (Z_to_bv 64 (DB Bw + 15))
                                  (Z_to_bv 64 (Z.of_nat i)) (XONES (DB Bw + 15)) y14' y15'
                                  x16 x17 (Z_to_bv 64 9) s3 (Z_to_bv 64 2147450880) m)).
      { intros y14' y15'.
        step. try rewrite (unsigned_lit (DB Bw)) by lia. try rewrite (unsigned_lit (Z.of_nat i)) by lia.
        pose proof (csd_rd1 m _ _ (Z.to_nat (DB Bw + 15 - TI.tf_addr fr) + i) (DB Bw + Z.of_nat i + 15) M15
                      ltac:(lia) ltac:(lia)) as RB.
        step. clear RB. step. rewrite PW.csd_zxb0.
        assert (Ei : i = vn) by lia. subst i.
        rewrite (SV5 H9), Z.eqb_refl. cbv iota.
        step. try rewrite (unsigned_lit (Z.of_nat vn)) by lia. try rewrite Z.add_0_r.
        apply ENT2. }
      step. br_false ltac:(exact (csd_ltu_xor (DB Bw + 15) (Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia))).
      csd_chk1 ltac:(try rewrite (unsigned_lit (DB Bw + 15)) by lia; try rewrite (unsigned_lit (Z.of_nat i)) by lia)
        (DB Bw + 15 + Z.of_nat i) MKX SKX RXS BODY.
    - (* i < vn: a byte that is not 0; on to i + 1, or out of the loop at i + 1 = 9 = vn *)
      assert (XI : TI.tf_addr fr <= DB Bw + 15 + Z.of_nat i < TI.tf_addr fr + LF) by lia.
      destruct (FRB _ XI) as (RX & RXS & kx & MKX & SKX).
      pose proof (Z.mod_pos_bound (DB Bw + 15 + Z.of_nat i) 8 ltac:(lia)) as MBX.
      assert (BODY : forall y14' y15' : word,
        ExecF.evtF rsegs RNG Q (ST 0x85620 ra (Z_to_bv 64 (TW.u_at NB 24 8)) (Z_to_bv 64 (DB Bw))
                                  (Z_to_bv 64 (DB Bw + 15 + Z.of_nat i)) (Z_to_bv 64 (DB Bw + 15))
                                  (Z_to_bv 64 (Z.of_nat i)) (XONES (DB Bw + 15)) y14' y15'
                                  x16 x17 (Z_to_bv 64 9) s3 (Z_to_bv 64 2147450880) m)).
      { intros y14' y15'.
        step. try rewrite (unsigned_lit (DB Bw)) by lia. try rewrite (unsigned_lit (Z.of_nat i)) by lia.
        pose proof (csd_rd1 m _ _ (Z.to_nat (DB Bw + 15 - TI.tf_addr fr) + i) (DB Bw + Z.of_nat i + 15) M15
                      ltac:(lia) ltac:(lia)) as RB.
        step. clear RB. step. rewrite PW.csd_zxb0.
        rewrite (proj2 (Z.eqb_neq _ 0) (SV4 i ltac:(lia))). cbv iota.
        step. try rewrite (unsigned_lit (Z.of_nat i)) by lia.
        step. rewrite PW.csd_eqb_lit by lia.
        destruct (Z.eqb_spec (Z.of_nat i + 1) 9) as [E9|E9]; cbn [negb]; cbv iota.
        + step. replace (Z_to_bv 64 9) with (Z_to_bv 64 (Z.of_nat vn)) by (f_equal; lia). apply ENT2.
        + replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
          apply (IH (S i)); lia. }
      step. br_false ltac:(exact (csd_ltu_xor (DB Bw + 15) (Z.of_nat i) ltac:(lia) ltac:(lia) ltac:(lia))).
      csd_chk1 ltac:(try rewrite (unsigned_lit (DB Bw + 15)) by lia; try rewrite (unsigned_lit (Z.of_nat i)) by lia)
        (DB Bw + 15 + Z.of_nat i) MKX SKX RXS BODY. }
  (* ---- 0x855e8: s1 = OW.desk_body; its UBSan NULL test (the model's) and wrap test of + 15; a2 = 0,
     a1 = s1 + 15, a3 = 2^64 - 1 - a1, s2 = 9 ---- *)
  step. rewrite ld_world.
  step. br_false ltac:(rewrite PW.csd_eqb_lit by lia; apply Z.eqb_neq; exact BDB).
  step. step. br_false ltac:(exact (f_equal negb (proj2 (csd_ltu_neg 15 (DB Bw) ltac:(lia) ltac:(lia))))).
  step. step. try rewrite (unsigned_lit (DB Bw)) by lia. step. step.
  try rewrite (unsigned_lit (DB Bw + 15)) by lia.
  apply (LOOP1 vn 0%nat); lia.
Qed.

End Pieces.
