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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41q RZ_huf_fkit RZ_huf_dx41r huf41_kit_x41ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41R2.
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


  Notation WD4 := [(DST, DST + dcap); (SPV - 224, SPV - 184)].
  Notation WDF := [(DST, DST + dcap); (SPV - 512, SPV - 336); (SPV - 224, SPV - 104)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells usegs mm (SPV + -376) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2; C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41r_hide := RZ_huf_dx41r.x41r_hide.
  Notation x41pf_transport := (RZ_huf_dx41r.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x41_einv_f := (RZ_huf_dx41r.x41_einv_f ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x41_f3_2 := (RZ_huf_dx41r.x41_f3_2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_f3_1 : forall mm eprev q SRC n src i1 o1 i2 o2 i3 o3
      (ip0 op0 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x5 x6 x8 x9 x12 x13 x14 x15 x17 x18 x19 x20 x22 x26 x27 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w14 : word) (lj : list byte),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 dcap) w14 (Z_to_bv 64 151050438420815295) (Z_to_bv 64 (DST + dcap)) ->
    ARGS mm ip0 (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) op0 (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    rw_cells usegs mm (SPV + -224) [CB 120 lj] ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= eprev <= dcap -> 0 <= q < 2^32 -> 0 < dcap -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap ->
    1 <= bv_unsigned bt1 -> 9 <= bv_unsigned ie1 -> 1 <= bv_unsigned bt2 -> 9 <= bv_unsigned ie2 -> 1 <= bv_unsigned bt3 -> 9 <= bv_unsigned ie3 ->
    evt usegs POST (ST 0x226fc mm x1 x5 x6 (Z_to_bv 64 2) x8 x9 (Z_to_bv 64 HUF_CTZ_TBL) (Z_to_bv 64 1) x12 x13 x14 x15 (Z_to_bv 64 (-1 * DT + -5)) x17 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 (Z_to_bv 64 9) (Z_to_bv 64 4) (Z_to_bv 64 (DST + eprev)) x26 x27 (Z_to_bv 64 (-1)) (Z_to_bv 64 q) (Z_to_bv 64 64) x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm eprev q SRC n src i1 o1 i2 o2 i3 o3
      ip0 op0 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x5 x6 x8 x9 x12 x13 x14 x15 x17 x18 x19 x20 x22 x26 x27 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w14 lj PV MI OUT DTB FA AR LC SB SL S0 S1 SL32 DJS DKS HEP HQ HDC
      HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HB1 HE1 HB2 HE2 HB3 HE3.
    assert (MRG : x41r_hide (forall mx (c1 c2 c3 : list cell) (A B C : Z),
                    rw_cells usegs mx A c1 -> rw_cells usegs mx B c2 -> rw_cells usegs mx C c3 ->
                    B = A + Z.of_nat (cells_size c1) -> C = B + Z.of_nat (cells_size c2) -> rw_cells usegs mx A (c1 ++ c2 ++ c3))).
    { unfold x41r_hide. intros mx c1 c2 c3 A B C H1 H2 H3 -> ->.
      apply (proj2 (ZdWalkKit.rw_cells_app usegs mx A c1 (c2 ++ c3))). split; [exact H1|].
      apply (proj2 (ZdWalkKit.rw_cells_app usegs mx _ c2 c3)). split; [exact H2|exact H3]. }
    assert (MU : munch WD mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    assert (TBLC : tbl_in usegs mm HUF_CTZ_TBL 64 1 0 0 63) by exact (huf_ctz_tbl mm MI).
    assert (KS : SRC + n <= SPV - 512 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 512 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 512 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    clear OS1 DJ2. change (x41r_hide (SRC + n <= lo \/ SPV <= SRC)) in DKS. change (x41r_hide (DT + 16388 <= lo \/ SPV <= DT)) in DJ3.
    kx_autoLx [0x22824; 0x229d0; 0x23594; 0x253c0] 120%nat
      [KZTbl HUF_CTZ_TBL 64 1 0 0 63; KZImg u_ro_lo u_ro_hi; KZRange i1 0 (2^32); KZRange (n - i1) 8 (2^32); KZRange o1 0 (2^32); KZRange eprev 0 (2^32); KZRange q 0 (2^32); KZRange dcap 1 (2^32);
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SRC, n); (SPV - 512, 136); (SPV - 376, 152); (HUF_CTZ_TBL, 64)].
    all: x41_ck.
    all: unfold x41r_hide in MRG.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?mm' _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
             [ eapply (x41_einv_f mm');
               first [ exact PV | exact KXMI | exact OUT | reflexivity
                     | eapply MRG; [exact FA | exact AR | exact LC
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia] ]
             | right; split; reflexivity ]
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR (Z_to_bv 64 ?PP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?T4) _ ?Q _ _ _ _) _ _ _ _ _ _) =>
             replace PP with (SRC + (PP - SRC)) by lia;
             replace T4 with (DST + (T4 - DST)) by lia;
             replace Q with (Z_to_bv 64 (bv_unsigned Q)) by apply Z_to_bv_bv_unsigned;
             kx_ev_ranges
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ (Z_to_bv 64 ?BC) _ _ _ _) _ (Z_to_bv 64 0x229d0) _ _ _ _) =>
             assert (HPE : 0 <= o1 <= PE /\ PE <= dcap) by lia;
             eapply (x41_fe ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm mm o1 PE OFF BC SRC n src)
         | |- evt _ _ (MS (mkR (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ (Z_to_bv 64 ?BC) _ _ _ _) _ (Z_to_bv 64 0x22824) _ _ _ _) =>
             assert (HPE : 0 <= o1 <= PE /\ PE <= dcap) by lia;
             eapply (x41_fl ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX (Z.to_nat dcap) mm mm o1 PE OFF BC SRC n src)
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | exact KXMI | exact OUT | exact DTB | exact SB | exact SL | exact DJS | lia
                      | unfold RZ_huf_dx41.SINV; lia | exact (bv_unsigned_in_range 64 _) ]
         end.
    (* [comment removed for export] *)
    all: intros mm'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end); intros MU' WM' MI' OUT' DTB'.
    all: pose proof (bytes_at_transport usegs _ mm mm' SRC src SB MU') as SB'; cbn [disjoint_from] in SB'; specialize (SB' ltac:(lia)).
    all: clear - MU' WM' MI' OUT' DTB' FA AR LC PV SB' SL S0 S1 SL32 DJS DKS HDC HEP HQ KD KT KS HPE LO SPB R1 R3 DL CTX DJ3
                 HI2 HJ2 HO2 HI3 HJ3 HO3 HB2 HE2 HB3 HE3 MRG.
    all: pose proof (rw_cells_transport usegs _ mm mm' _ _ FA MU' WM') as FA';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ AR MU' WM') as AR';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ LC MU' WM') as LC';
         pose proof (x41pf_transport mm mm' PV MU' WM') as PV'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA', AR', LC'.
    all: specialize (FA' ltac:(lia)); specialize (AR' ltac:(lia)); specialize (LC' ltac:(lia)).
    all: clear FA AR LC PV MU' WM'.
    all: destruct PV' as (SV' & STK' & MUP' & WMP').
    all: change (x41r_hide (DST + dcap <= SRC \/ SRC + n <= DST)) in DJS.
    all: kx_autoLx [0x226fc; 0x23594; 0x253c0] 40%nat
           [KZRange dcap 1 (2^32); KZRange o1 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 376) 152]
           [(SPV - 512, 136); (SPV - 376, 152)].
    all: x41_ck.
    all: kx_mem.
    all: unfold x41r_hide in *.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?m2 _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m2);
             [ eapply (x41_einv_f m2);
               first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | reflexivity
                     | eapply MRG; [exact FA' | exact AR' | exact LC'
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia] ]
             | first [left; reflexivity | right; split; reflexivity] ]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A1) _ _ _ _ _ _) _ (Z_to_bv 64 0x226fc) _ _ ?m2 _) =>
             replace A1 with (DST + (A1 - DST)) by lia;
             eapply (x41_f3_2 m2 (A1 - DST) q SRC n src i2 o2 i3 o3)
         end.
    all: first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | exact DTB' | exact FA' | exact AR' | exact LC'
               | exact SB' | exact SL | exact DJS | exact DKS | lia ].
  Qed.

  Lemma x41_f3_0 : forall mm eprev q SRC n src i0 o0 i1 o1 i2 o2 i3 o3
      (bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x5 x6 x8 x9 x12 x13 x14 x15 x17 x18 x19 x20 x22 x26 x27 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w14 : word) (lj : list byte),
    X41PF mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 (Z_to_bv 64 dcap) w14 (Z_to_bv 64 151050438420815295) (Z_to_bv 64 (DST + dcap)) ->
    ARGS mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    rw_cells usegs mm (SPV + -224) [CB 120 lj] ->
    bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= eprev <= dcap -> 0 <= q < 2^32 -> 0 < dcap -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap ->
    1 <= bv_unsigned bt0 -> 9 <= bv_unsigned ie0 -> 1 <= bv_unsigned bt1 -> 9 <= bv_unsigned ie1 -> 1 <= bv_unsigned bt2 -> 9 <= bv_unsigned ie2 -> 1 <= bv_unsigned bt3 -> 9 <= bv_unsigned ie3 ->
    evt usegs POST (ST 0x226fc mm x1 x5 x6 (Z_to_bv 64 2) x8 x9 (Z_to_bv 64 HUF_CTZ_TBL) (Z_to_bv 64 0) x12 x13 x14 x15 (Z_to_bv 64 (-1 * DT + -5)) x17 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 (Z_to_bv 64 9) (Z_to_bv 64 4) (Z_to_bv 64 (DST + eprev)) x26 x27 (Z_to_bv 64 (-1)) (Z_to_bv 64 q) (Z_to_bv 64 64) x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm eprev q SRC n src i0 o0 i1 o1 i2 o2 i3 o3
      bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x5 x6 x8 x9 x12 x13 x14 x15 x17 x18 x19 x20 x22 x26 x27 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w14 lj PV MI OUT DTB FA AR LC SB SL S0 S1 SL32 DJS DKS HEP HQ HDC
      HI0 HJ0 HO0 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HB0 HE0 HB1 HE1 HB2 HE2 HB3 HE3.
    assert (MRG : x41r_hide (forall mx (c1 c2 c3 : list cell) (A B C : Z),
                    rw_cells usegs mx A c1 -> rw_cells usegs mx B c2 -> rw_cells usegs mx C c3 ->
                    B = A + Z.of_nat (cells_size c1) -> C = B + Z.of_nat (cells_size c2) -> rw_cells usegs mx A (c1 ++ c2 ++ c3))).
    { unfold x41r_hide. intros mx c1 c2 c3 A B C H1 H2 H3 -> ->.
      apply (proj2 (ZdWalkKit.rw_cells_app usegs mx A c1 (c2 ++ c3))). split; [exact H1|].
      apply (proj2 (ZdWalkKit.rw_cells_app usegs mx _ c2 c3)). split; [exact H2|exact H3]. }
    assert (MU : munch WD mm mm) by apply munch_refl.
    assert (WM : wmono usegs mm mm) by apply wmono_refl.
    assert (TBLC : tbl_in usegs mm HUF_CTZ_TBL 64 1 0 0 63) by exact (huf_ctz_tbl mm MI).
    assert (KS : SRC + n <= SPV - 512 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 512 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 512 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    clear OS1 DJ2. change (x41r_hide (SRC + n <= lo \/ SPV <= SRC)) in DKS. change (x41r_hide (DT + 16388 <= lo \/ SPV <= DT)) in DJ3.
    kx_autoLx [0x22824; 0x229d0; 0x23594; 0x253c0] 120%nat
      [KZTbl HUF_CTZ_TBL 64 1 0 0 63; KZImg u_ro_lo u_ro_hi; KZRange i0 0 (2^32); KZRange (n - i0) 8 (2^32); KZRange o0 0 (2^32); KZRange eprev 0 (2^32); KZRange q 0 (2^32); KZRange dcap 1 (2^32);
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SRC, n); (SPV - 512, 136); (SPV - 376, 152); (HUF_CTZ_TBL, 64)].
    all: x41_ck.
    all: unfold x41r_hide in MRG.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?mm' _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
             [ eapply (x41_einv_f mm');
               first [ exact PV | exact KXMI | exact OUT | reflexivity
                     | eapply MRG; [exact FA | exact AR | exact LC
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia] ]
             | right; split; reflexivity ]
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR (Z_to_bv 64 ?PP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?T4) _ ?Q _ _ _ _) _ _ _ _ _ _) =>
             replace PP with (SRC + (PP - SRC)) by lia;
             replace T4 with (DST + (T4 - DST)) by lia;
             replace Q with (Z_to_bv 64 (bv_unsigned Q)) by apply Z_to_bv_bv_unsigned;
             kx_ev_ranges
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ (Z_to_bv 64 ?BC) _ _ _ _) _ (Z_to_bv 64 0x229d0) _ _ _ _) =>
             assert (HPE : 0 <= o0 <= PE /\ PE <= dcap) by lia;
             eapply (x41_fe ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm mm o0 PE OFF BC SRC n src)
         | |- evt _ _ (MS (mkR (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ (Z_to_bv 64 ?BC) _ _ _ _) _ (Z_to_bv 64 0x22824) _ _ _ _) =>
             assert (HPE : 0 <= o0 <= PE /\ PE <= dcap) by lia;
             eapply (x41_fl ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX (Z.to_nat dcap) mm mm o0 PE OFF BC SRC n src)
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | exact KXMI | exact OUT | exact DTB | exact SB | exact SL | exact DJS | lia
                      | unfold RZ_huf_dx41.SINV; lia | exact (bv_unsigned_in_range 64 _) ]
         end.
    (* [comment removed for export] *)
    all: intros mm'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end); intros MU' WM' MI' OUT' DTB'.
    all: pose proof (bytes_at_transport usegs _ mm mm' SRC src SB MU') as SB'; cbn [disjoint_from] in SB'; specialize (SB' ltac:(lia)).
    all: clear - MU' WM' MI' OUT' DTB' FA AR LC PV SB' SL S0 S1 SL32 DJS DKS HDC HEP HQ KD KT KS HPE LO SPB R1 R3 DL CTX DJ3
                 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HB1 HE1 HB2 HE2 HB3 HE3 MRG.
    all: pose proof (rw_cells_transport usegs _ mm mm' _ _ FA MU' WM') as FA';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ AR MU' WM') as AR';
         pose proof (rw_cells_transport usegs _ mm mm' _ _ LC MU' WM') as LC';
         pose proof (x41pf_transport mm mm' PV MU' WM') as PV'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA', AR', LC'.
    all: specialize (FA' ltac:(lia)); specialize (AR' ltac:(lia)); specialize (LC' ltac:(lia)).
    all: clear FA AR LC PV MU' WM'.
    all: destruct PV' as (SV' & STK' & MUP' & WMP').
    all: change (x41r_hide (DST + dcap <= SRC \/ SRC + n <= DST)) in DJS.
    all: kx_autoLx [0x226fc; 0x23594; 0x253c0] 40%nat
           [KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 376) 152]
           [(SPV - 512, 136); (SPV - 376, 152)].
    all: x41_ck.
    all: kx_mem.
    all: unfold x41r_hide in *.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23594) _ _ ?m2 _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m2);
             [ eapply (x41_einv_f m2);
               first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | reflexivity
                     | eapply MRG; [exact FA' | exact AR' | exact LC'
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                   | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia] ]
             | first [left; reflexivity | right; split; reflexivity] ]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A1) _ _ _ _ _ _) _ (Z_to_bv 64 0x226fc) _ _ ?m2 _) =>
             replace A1 with (DST + (A1 - DST)) by lia;
             eapply (x41_f3_1 m2 (A1 - DST) q SRC n src i1 o1 i2 o2 i3 o3)
         end.
    all: first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | exact DTB' | exact FA' | exact AR' | exact LC'
               | exact SB' | exact SL | exact DJS | exact DKS | lia ].
  Qed.

End DX41R2.
