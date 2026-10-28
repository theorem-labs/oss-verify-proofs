(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41b RZ_huf_dx41c RZ_huf_dx41d RZ_huf_dx41e huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41F.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).


  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation BDAT mm A c b pad p st lm :=
    (rw_cells usegs mm A [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (BDAT mm (SPV + -376) c b pad p st lm).
  Notation BD2 mm c b pad p st lm := (BDAT mm (SPV + -144) c b pad p st lm).
  Notation BD3 mm c b pad p st lm := (BDAT mm (SPV + -184) c b pad p st lm).
  Notation BD4 mm c b pad p st lm := (BDAT mm (SPV + -224) c b pad p st lm).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Definition X41P (mm : fmem) (rest : list byte) : Prop :=
    rw_cells usegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk usegs mm lo (SPV + -512) /\ rw_cells usegs mm (SPV + -336) [CB 112 rest] /\
    munch [(DST, DST + dcap); (SPV - 912, SPV)] m0 mm /\ wmono usegs m0 mm.

  Definition SBUF (mm : fmem) (S len : Z) (bs : list byte) : Prop :=
    bytes_at usegs mm S bs /\ zlen bs = len /\ 4096 <= S /\ S + len < 2^47 /\ len < 2^32 /\
    (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S).

  Lemma x41p_transport : forall mm mm' rest, X41P mm rest -> munch WDF mm mm' -> wmono usegs mm mm' -> X41P mm' rest.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' rest (SV & STK & RS & MU & WM) MU' WM'.
    split; [|split; [|split; [|split]]].
    - eapply (rw_cells_transport usegs _ mm mm' _ _ SV MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (stk_transport_disjoint usegs _ mm mm' _ _ STK MU' WM'); cbn [disjoint_from]; lia.
    - eapply (rw_cells_transport usegs _ mm mm' _ _ RS MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
    - exact (wmono_trans usegs m0 mm mm' WM WM').
  Qed.

  Lemma sbuf_transport : forall mm mm' S len bs, SBUF mm S len bs -> munch WDF mm mm' -> SBUF mm' S len bs.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' S len bs (SB & SL & R0 & R1' & R2 & D1 & D2) MU'.
    split; [|repeat split; assumption].
    eapply (bytes_at_transport usegs _ mm mm' S bs SB MU'); cbn [disjoint_from]; lia.
  Qed.

  Lemma x41_einv : forall mm rest (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word)
      c1 b1 pad1 p1 st1 lm1 c2 b2 pad2 p2 st2 lm2 c3 b3 pad3 p3 st3 lm3 c4 b4 pad4 p4 st4 lm4,
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    BDAT mm (SPV + -376) c1 b1 pad1 p1 st1 lm1 -> BDAT mm (SPV + -144) c2 b2 pad2 p2 st2 lm2 ->
    BDAT mm (SPV + -184) c3 b3 pad3 p3 st3 lm3 -> BDAT mm (SPV + -224) c4 b4 pad4 p4 st4 lm4 -> EINV mm.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      c1 b1 pad1 p1 st1 lm1 c2 b2 pad2 p2 st2 lm2 c3 b3 pad3 p3 st3 lm3 c4 b4 pad4 p4 st4 lm4
      (SV & STK & RS & MU & WM) MI OUT FA B1 B2 B3 B4.
    pose proof (stk_of_rw_cells usegs mm _ _ FA) as H1.
    pose proof (stk_of_rw_cells usegs mm _ _ B1) as H2.
    pose proof (stk_of_rw_cells usegs mm _ _ RS) as H3.
    pose proof (stk_of_rw_cells usegs mm _ _ B4) as H4.
    pose proof (stk_of_rw_cells usegs mm _ _ B3) as H5.
    pose proof (stk_of_rw_cells usegs mm _ _ B2) as H6.
    cbn [cells_size csize Nat.add] in H1, H2, H3, H4, H5, H6.
    change (Z.of_nat 136) with 136 in H1. change (Z.of_nat 40) with 40 in H2, H4, H5, H6. change (Z.of_nat 112) with 112 in H3.
    replace (SPV + -512 + 136) with (SPV + -376) in H1 by lia.
    replace (SPV + -376 + 40) with (SPV + -336) in H2 by lia.
    replace (SPV + -336 + 112) with (SPV + -224) in H3 by lia.
    replace (SPV + -224 + 40) with (SPV + -184) in H4 by lia.
    replace (SPV + -184 + 40) with (SPV + -144) in H5 by lia.
    replace (SPV + -144 + 40) with (SPV + -104) in H6 by lia.
    unfold RZ_huf_dx41.EINV. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU|split; [exact WM|exact MI]]].
    eapply (stk_merge usegs mm lo (SPV + -144)); [|exact H6|lia].
    eapply (stk_merge usegs mm lo (SPV + -184)); [|exact H5|lia].
    eapply (stk_merge usegs mm lo (SPV + -224)); [|exact H4|lia].
    eapply (stk_merge usegs mm lo (SPV + -336)); [|exact H3|lia].
    eapply (stk_merge usegs mm lo (SPV + -376)); [|exact H2|lia].
    eapply (stk_merge usegs mm lo (SPV + -512)); [exact STK|exact H1|lia].
  Qed.

  Ltac rc_tr H MU WM :=
    let T := fresh "T" in
    pose proof (rw_cells_transport usegs _ _ _ _ _ H MU WM) as T;
    specialize (T ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia));
    clear H; rename T into H.
  Ltac sb_tr SB MU m' :=
    let T := fresh "T" in
    pose proof (sbuf_transport _ m' _ _ _ SB) as T;
    specialize (T ltac:(eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia));
    clear SB; rename T into SB.
  Ltac x41p_tr PV MU WM m' :=
    let T := fresh "T" in
    pose proof (x41p_transport _ m' _ PV) as T;
    specialize (T ltac:(eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia) WM);
    clear PV; rename T into PV.
  Ltac intro_words := repeat lazymatch goal with |- forall _ : word, _ => intro end.

  (* [comment removed for export] *)
  Lemma x41_c0 : forall mm rest j1 j2 j3 j4 e1 e2 e3 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x1 x5 x6 x8 x9 x11 x12 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w12 w15 w16 : word),
    X41P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + dcap - 3))
      (Z_to_bv 64 (DST + e2)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    SINV o1 n1 c1 -> SINV o2 n2 c2 -> SINV o3 n3 c3 -> SINV o4 n4 c4 ->
    0 <= c1 < 2^31 -> 0 <= c2 < 2^31 -> 0 <= c3 < 2^31 -> 0 <= c4 < 2^31 ->
    0 <= j1 <= dcap -> 0 <= j2 <= dcap -> 0 <= j3 <= dcap -> 0 <= j4 <= dcap ->
    0 <= e1 <= dcap -> 0 <= e2 <= dcap -> 0 <= e3 <= dcap ->
    dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    SPV mod 16 = 0 -> DT mod 4 = 0 ->
    evt usegs POST (ST 0x24024 mm x1 x5 x6 (Z_to_bv 64 DST) x8 x9 (Z_to_bv 64 (-20)) x11 x12 (Z_to_bv 64 (DST + e1)) x14 x15 x16 x17
                     (Z_to_bv 64 (DST + j1)) (Z_to_bv 64 dl) x20 (Z_to_bv 64 (DST + j4)) (Z_to_bv 64 (DST + j3)) (Z_to_bv 64 (DST + j2))
                     (Z_to_bv 64 (DST + e3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 e1) (Z_to_bv 64 (DST + dcap)) x28 x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j1 j2 j3 j4 e1 e2 e3 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl tl rsv
      k1 k2 k3 k4 pad1 pad2 pad3 pad4 x1 x5 x6 x8 x9 x11 x12 x14 x15 x16 x17 x20 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w12 w15 w16
      PV MI OUT DTB FA B1 B2 B3 B4 SB1 SB2 SB3 SB4 HS1 HS2 HS3 HS4 HC1 HC2 HC3 HC4 HJ1 HJ2 HJ3 HJ4 HE1 HE2 HE3 HDL HTL HRSV SPVA DTA.
    kx_autoLx [0x23594; 0x24034] 20%nat
      [KZRange j1 0 (2^32); KZRange j2 0 (2^32); KZRange j3 0 (2^32); KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32);
       KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SPV - 512, 136)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ _ _) =>
             try replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity);
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm);
             [eapply (x41_einv mm rest); eassumption | right; split; reflexivity]
         | _ => idtac
         end.
    clear KXK KXA KXRD.
    pose proof SB1 as (B1s & L1 & R10 & R11 & R12 & D11 & D12).
    eapply (x41_d1_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm mm j1 e1 o1 S1 n1 b1 dl tl rsv c1 k1 pad1);
      try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
    intro mm1; intro_words; intros pad1' MU1 WM1 MI1 OUT1 DTB1 FA1 BD1'.
    rc_tr B2 MU1 WM1. rc_tr B3 MU1 WM1. rc_tr B4 MU1 WM1.
    sb_tr SB2 MU1 mm1. sb_tr SB3 MU1 mm1. sb_tr SB4 MU1 mm1. x41p_tr PV MU1 WM1 mm1.
    pose proof SB2 as (B2s & L2 & R20 & R21 & R22 & D21 & D22).
    eapply (x41_d2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm1 mm1 j2 e2 o2 S2 n2 b2 dl tl rsv c2 k2 pad2);
      try eassumption; try lia; try apply munch_refl; try apply wmono_refl; try exact (rsk_al_i _ _ SPVA).
    intro mm2; intro_words; intros MU2 WM2 MI2 OUT2 DTB2 FA2 BD2'.
    rc_tr BD1' MU2 WM2. rc_tr B3 MU2 WM2. rc_tr B4 MU2 WM2.
    sb_tr SB3 MU2 mm2. sb_tr SB4 MU2 mm2. x41p_tr PV MU2 WM2 mm2.
    pose proof SB3 as (B3s & L3 & R30 & R31 & R32 & D31 & D32).
    eapply (x41_d3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm2 mm2 j3 e3 o3 S3 n3 b3 dl tl rsv c3 k3 pad3);
      try eassumption; try lia; try apply munch_refl; try apply wmono_refl; try exact (rsk_al_i _ _ SPVA).
    intros mm3 j3'; intro_words; intros MU3 WM3 MI3 OUT3 DTB3 FA3 BD3' SB3' HJ3'.
    rc_tr BD1' MU3 WM3. rc_tr BD2' MU3 WM3. rc_tr B4 MU3 WM3.
    sb_tr SB4 MU3 mm3. x41p_tr PV MU3 WM3 mm3.
    pose proof SB4 as (B4s & L4 & R40 & R41 & R42 & D41 & D42).
    eapply (x41_d4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 mm3 mm3 j4 o4 S4 n4 b4 dl tl rsv c4 k4 pad4);
      try eassumption; try lia; try apply munch_refl; try apply wmono_refl; try exact (rsk_al_i _ _ SPVA).
    intro mm4; intro_words; intros MU4 WM4 MI4 OUT4 BD4'.
    rc_tr FA3 MU4 WM4. rc_tr BD1' MU4 WM4. rc_tr BD2' MU4 WM4. rc_tr BD3' MU4 WM4. x41p_tr PV MU4 WM4 mm4.
    eapply (x41_end ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 mm4);
      [eapply (x41_einv mm4 rest); eassumption | exact FA3 | exact BD1' | exact BD2' | exact BD3' | exact BD4'].
  Qed.

End DX41F.
