(* crt_mid_stmt of check_round_trip in fuzz_frame.ubsan from crt_m1_stmt, crt_m2_stmt and crt_m3_stmt. *)
(* check_round_trip (fuzz_frame.ubsan) from 0x13240 to the free of want at 0x134bc or the
   malloc of shy at 0x1344c: crt_mid_stmt from crt_m1_stmt, crt_m2_stmt and crt_m3_stmt
   (U/Prog/crt_defs.v). Each segment runs on the end state of the one before it; the facts that
   a later segment needs move across the earlier footprints, and the three footprints join in
   the window of crt_mid_post. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c memset_c bcmp_c
  diginet_frame_build_c spec_build_frame_c crt_defs.
Import ListNotations.
Open Scope Z_scope.

Lemma crt_mid_of : crt_m1_stmt -> crt_m2_stmt -> crt_m3_stmt -> crt_mid_stmt.
Proof.
  unfold crt_m1_stmt, crt_m2_stmt, crt_m3_stmt, crt_mid_stmt.
  intros M1 M2 M3 MSET BCMP DFB SBF ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m w buf out want n b j sv HC HL HN LAY RO BY SO SW SS HJ HSV RW MI.
  pose proof LAY as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
  (* crt_m1: 0x13240 .. 0x1333c *)
  eapply evt_cut.
  { exact (M1 MSET DFB ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m w buf out want n b j sv HC HL HN LAY RO BY SO SS HJ HSV RW MI). }
  intros ms1 (ra1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v4 & u3 & u4 & u5 & u6 & j1 & m1 & -> &
    MU1 & WM1 & MI1 & RW1 & OUT1 & SS1).
  assert (RO1 : ro_cells rsegs m1 w (spec_cells buf b)).
  { apply (ro_cells_transport rsegs _ m m1 w _ RO MU1).
    change (Z.of_nat (cells_size (spec_cells buf b))) with 80. cbn [disjoint_from]. lia. }
  assert (BY1 : bytes_at rsegs m1 buf b).
  { apply (bytes_at_transport rsegs _ m m1 buf b BY MU1). cbn [disjoint_from]. lia. }
  assert (SW1 : stk rsegs m1 want (want + n)).
  { apply (stk_transport_disjoint rsegs _ m m1 want (want + n) SW MU1 WM1). cbn [disjoint_from]. lia. }
  (* crt_m2: 0x1333c .. 0x133c4 *)
  eapply evt_cut.
  { exact (M2 BCMP SBF ra1 sp gp tp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 v4 s7 s8 s9 s10 s11 u3 u4 u5 u6
      F fc m1 w buf out want n b j1 sv HC HL HN LAY RO1 BY1 OUT1 SW1 SS1 HSV RW1 MI1). }
  intros ms2 (ra2 & x0 & x1 & x2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y4 & x3 & x4 & x5 & x6 & j2 & m2 & -> &
    MU2 & WM2 & MI2 & RW2 & OUT2 & WT2 & SS2).
  assert (RO2 : ro_cells rsegs m2 w (spec_cells buf b)).
  { apply (ro_cells_transport rsegs _ m1 m2 w _ RO1 MU2).
    change (Z.of_nat (cells_size (spec_cells buf b))) with 80. cbn [disjoint_from]. lia. }
  assert (BY2 : bytes_at rsegs m2 buf b).
  { apply (bytes_at_transport rsegs _ m1 m2 buf b BY1 MU2). cbn [disjoint_from]. lia. }
  (* crt_m3: 0x133c4 .. 0x134bc or the jal of malloc at 0x1344c *)
  eapply evt_mono.
  { exact (M3 MSET BCMP DFB SBF ra2 sp gp tp x0 x1 x2 c0 c1 c2 c3 c4 c5 c6 c7 y4 s7 s8 s9 s10 s11 x3 x4 x5 x6
      F fc m2 w buf out want n b j2 _ _ sv HC HL HN LAY RO2 BY2 OUT2 WT2 SS2 HSV RW2 MI2). }
  intros ms3 (ra3 & z0 & z1 & z2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & e3 & e4 & e5 & e6 & z3 & z4 & z5 & z6 &
    pc & j3 & m3 & EQ3 & BR3 & MU3 & WM3 & MI3 & RW3).
  exists ra3, z0, z1, z2, d0, d1, d2, d3, d4, d5, d6, d7, e3, e4, e5, e6, z3, z4, z5, z6, pc, j3, m3.
  split; [exact EQ3|]. split; [exact BR3|]. split.
  { apply (munch_trans _ m m2 m3); [apply (munch_trans _ m m1 m2) | exact MU3].
    - refine (munch_weaken _ _ m m1 _ MU1). intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [lia|]. split; [exact H2 | exact I].
    - refine (munch_weaken _ _ m1 m2 _ MU2). intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & H2 & H3 & _). split; [lia|]. split; [exact H3 | exact I]. }
  split; [exact (wmono_trans rsegs m m2 m3 (wmono_trans rsegs m m1 m2 WM1 WM2) WM3)|].
  split; [exact MI3 | exact RW3].
Qed.
