(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41q RZ_huf_fkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41R.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw ilo oew ie0 ie1 ie2 ie3 :=
    (rw_cells psegs mm (SPV + -256) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 bt0; C8 bt1; C8 bt2; C8 bt3; C8 dtw; C8 ilo; C8 oew; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).

  (* [comment removed for export] *)
  Definition X41PF (mm : fmem) : Prop :=
    rw_cells psegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk psegs mm lo (SPV + -416) /\ munch [(DST, DST + dcap); (SPV - 432, SPV)] m0 mm /\ wmono psegs m0 mm.

  Lemma x41pf_transport : forall mm mm', X41PF mm -> munch WD mm mm' -> wmono psegs mm mm' -> X41PF mm'.
  Proof.
    clear DJ3. pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm mm' (SV & STK & MU & WM) MU' WM'.
    split; [|split; [|split]].
    - eapply (rw_cells_transport psegs _ mm mm' _ _ SV MU' WM');
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - eapply (stk_transport_disjoint psegs _ mm mm' _ _ STK MU' WM'); cbn [disjoint_from]; lia.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia.
    - exact (wmono_trans psegs m0 mm mm' WM WM').
  Qed.

  Lemma x41_einv_f : forall mm (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word) csA,
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 -> rw_cells psegs mm (SPV + -256) csA -> cells_size csA = 152%nat -> EINV mm.
  Proof.
    clear DJ3. pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 csA (SV & STK & MU & WM) MI OUT FA BD SZ.
    pose proof (stk_of_rw_cells psegs mm _ _ FA) as H1.
    pose proof (stk_of_rw_cells psegs mm _ _ BD) as H2.
    rewrite SZ in H2. cbn [cells_size csize Nat.add] in H1.
    change (Z.of_nat 160) with 160 in H1. change (Z.of_nat 152) with 152 in H2.
    replace (SPV + -416 + 160) with (SPV + -256) in H1 by lia.
    replace (SPV + -256 + 152) with (SPV + -104) in H2 by lia.
    unfold RZ_huf_dx41.EINV. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU|split; [exact WM|exact MI]]].
    eapply (stk_merge psegs mm lo (SPV + -256)); [|exact H2|lia].
    eapply (stk_merge psegs mm lo (SPV + -416)); [exact STK|exact H1|lia].
  Qed.

  Definition x41r_hide (P : Prop) : Prop := P.
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Lemma x41_f3_3 : forall mm eprev q SRC n src i3 o3
      (ip0 ip1 ip2 op0 op1 op2 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x8 x9 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (DST + dcap)) w17 w18 w19 ->
    ARGS mm ip0 ip1 ip2 (Z_to_bv 64 (SRC + i3)) op0 op1 op2 (Z_to_bv 64 (DST + o3)) bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= eprev <= dcap -> 0 <= q < 2^32 -> 0 < dcap -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap ->
    evt psegs POST (ST 0x2233c mm x1 (Z_to_bv 64 q) (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 4) x8 x9 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + eprev)) x12 x13 (Z_to_bv 64 69944) (Z_to_bv 64 3) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 151050438420815295) x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 dcap) (Z_to_bv 64 64) x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm eprev q SRC n src i3 o3
      ip0 ip1 ip2 op0 op1 op2 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x8 x9 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HEP HQ HDC HI3 HJ3 HO3.
    assert (MU : munch WD mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    assert (TBLC : tbl_in psegs mm HUF_CTZ_TBL 64 1 0 0 63) by exact (huf_ctz_tbl mm MI).
    assert (KS : SRC + n <= SPV - 416 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 416 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 416 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    clear OS1 DJ2. change (x41r_hide (SRC + n <= lo \/ SPV <= SRC)) in DKS. change (x41r_hide (DT + 16388 <= lo \/ SPV <= DT)) in DJ3.
    kx_autoLx [0x23454; 0x22414; 0x22548] 120%nat
      [KZTbl HUF_CTZ_TBL 64 1 0 0 63; KZImg 0x10000 0x14000; KZRange i3 0 (2^32); KZRange (n - i3) 8 (2^32); KZRange o3 0 (2^32); KZRange eprev 0 (2^32); KZRange q 0 (2^32); KZRange dcap 1 (2^32);
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SRC, n); (SPV - 416, 160); (SPV - 256, 152); (0x11138, 64)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ ?mm' _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
             [ eapply (x41_einv_f mm'); first [ exact PV | exact KXMI | exact OUT | exact FA | exact AR | reflexivity ]
             | right; split; reflexivity ]
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?PP) _ _ _ _ _ _ _ _ _ _ _ ?Q _ _ _ _ _ _ _ (Z_to_bv 64 ?T4) _ _) _ _ _ _ _ _) =>
             replace PP with (SRC + (PP - SRC)) by lia;
             replace T4 with (DST + (T4 - DST)) by lia;
             replace Q with (Z_to_bv 64 (bv_unsigned Q)) by apply Z_to_bv_bv_unsigned;
             kx_ev_ranges
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ _) _ (Z_to_bv 64 140616) _ _ _ _) =>
             assert (HPE : 0 <= PE <= dcap) by lia;
             eapply (x41_fe ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm mm o3 PE OFF BC SRC n src)
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ _) _ (Z_to_bv 64 140308) _ _ _ _) =>
             assert (HPE : 0 <= PE <= dcap) by lia;
             eapply (x41_fl ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX (Z.to_nat dcap) mm mm o3 PE OFF BC SRC n src)
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | exact KXMI | exact OUT | exact DTB | exact SB | exact SL | exact DJS | lia
                      | unfold RZ_huf_dx41.SINV; lia | exact (bv_unsigned_in_range 64 _) ]
         end.
    (* [comment removed for export] *)
    all: intros mm'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end); intros MU' WM' MI' OUT' DTB'.
    all: pose proof (bytes_at_transport psegs _ mm mm' SRC src SB MU') as SB'; cbn [disjoint_from] in SB'; specialize (SB' ltac:(lia)).
    all: clear - MU' WM' MI' OUT' DTB' FA AR PV SB' SL S0 S1 SL32 DJS DKS HDC HEP HQ KD KT KS HPE LO SPB R1 R3 DL CTX DJ3 HI3 HJ3 HO3.
    all: pose proof (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM') as FA';
         pose proof (rw_cells_transport psegs _ mm mm' _ _ AR MU' WM') as AR';
         pose proof (x41pf_transport mm mm' PV MU' WM') as PV'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA', AR'.
    all: specialize (FA' ltac:(lia)); specialize (AR' ltac:(lia)).
    all: clear FA AR PV MU' WM'.
    all: destruct PV' as (SV' & STK' & MUP' & WMP').
    all: change (x41r_hide (DST + dcap <= SRC \/ SRC + n <= DST)) in DJS.
    all: kx_autoLx [0x23454; 0x226c0] 40%nat
           [KZRange dcap 1 (2^32); KZRange o3 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 256) 152]
           [(SPV - 416, 160); (SPV - 256, 152)].
    all: kx_mem.
    all: unfold x41r_hide in *.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ ?m2 _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m2);
             [ eapply (x41_einv_f m2);
               first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | exact FA' | exact AR' | reflexivity ]
             | first [left; reflexivity | right; split; reflexivity] ]
         end.
  Qed.

  Lemma x41_f3_2 : forall mm eprev q SRC n src i2 o2 i3 o3
      (ip0 ip1 op0 op1 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x8 x9 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (DST + dcap)) w17 w18 w19 ->
    ARGS mm ip0 ip1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) op0 op1 (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 <= eprev <= dcap -> 0 <= q < 2^32 -> 0 < dcap -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap ->
    evt psegs POST (ST 0x2233c mm x1 (Z_to_bv 64 q) (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 4) x8 x9 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + eprev)) x12 x13 (Z_to_bv 64 69944) (Z_to_bv 64 2) (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 151050438420815295) x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 dcap) (Z_to_bv 64 64) x29 x30 x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm eprev q SRC n src i2 o2 i3 o3
      ip0 ip1 op0 op1 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x8 x9 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w17 w18 w19 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HEP HQ HDC HI2 HJ2 HO2 HI3 HJ3 HO3.
    assert (MU : munch WD mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    assert (TBLC : tbl_in psegs mm HUF_CTZ_TBL 64 1 0 0 63) by exact (huf_ctz_tbl mm MI).
    assert (KS : SRC + n <= SPV - 416 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 416 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 416 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    clear OS1 DJ2. change (x41r_hide (SRC + n <= lo \/ SPV <= SRC)) in DKS. change (x41r_hide (DT + 16388 <= lo \/ SPV <= DT)) in DJ3.
    kx_autoLx [0x23454; 0x22414; 0x22548] 120%nat
      [KZTbl HUF_CTZ_TBL 64 1 0 0 63; KZImg 0x10000 0x14000; KZRange i2 0 (2^32); KZRange (n - i2) 8 (2^32); KZRange o2 0 (2^32); KZRange eprev 0 (2^32); KZRange q 0 (2^32); KZRange dcap 1 (2^32);
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SRC, n); (SPV - 416, 160); (SPV - 256, 152); (0x11138, 64)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ ?mm' _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm');
             [ eapply (x41_einv_f mm'); first [ exact PV | exact KXMI | exact OUT | exact FA | exact AR | reflexivity ]
             | right; split; reflexivity ]
         | _ => idtac
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?PP) _ _ _ _ _ _ _ _ _ _ _ ?Q _ _ _ _ _ _ _ (Z_to_bv 64 ?T4) _ _) _ _ _ _ _ _) =>
             replace PP with (SRC + (PP - SRC)) by lia;
             replace T4 with (DST + (T4 - DST)) by lia;
             replace Q with (Z_to_bv 64 (bv_unsigned Q)) by apply Z_to_bv_bv_unsigned;
             kx_ev_ranges
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ _) _ (Z_to_bv 64 140616) _ _ _ _) =>
             assert (HPE : 0 <= PE <= dcap) by lia;
             eapply (x41_fe ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm mm o2 PE OFF BC SRC n src)
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + ?OFF)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?BC) _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?PE)) _ _) _ (Z_to_bv 64 140308) _ _ _ _) =>
             assert (HPE : 0 <= PE <= dcap) by lia;
             eapply (x41_fl ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX (Z.to_nat dcap) mm mm o2 PE OFF BC SRC n src)
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | exact KXMI | exact OUT | exact DTB | exact SB | exact SL | exact DJS | lia
                      | unfold RZ_huf_dx41.SINV; lia | exact (bv_unsigned_in_range 64 _) ]
         end.
    (* [comment removed for export] *)
    all: intros mm'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end); intros MU' WM' MI' OUT' DTB'.
    all: pose proof (bytes_at_transport psegs _ mm mm' SRC src SB MU') as SB'; cbn [disjoint_from] in SB'; specialize (SB' ltac:(lia)).
    all: clear - MU' WM' MI' OUT' DTB' FA AR PV SB' SL S0 S1 SL32 DJS DKS HDC HEP HQ KD KT KS HPE LO SPB R1 R3 DL CTX DJ3 HI2 HJ2 HO2 HI3 HJ3 HO3.
    all: pose proof (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM') as FA';
         pose proof (rw_cells_transport psegs _ mm mm' _ _ AR MU' WM') as AR';
         pose proof (x41pf_transport mm mm' PV MU' WM') as PV'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA', AR'.
    all: specialize (FA' ltac:(lia)); specialize (AR' ltac:(lia)).
    all: clear FA AR PV MU' WM'.
    all: destruct PV' as (SV' & STK' & MUP' & WMP').
    all: change (x41r_hide (DST + dcap <= SRC \/ SRC + n <= DST)) in DJS.
    all: kx_autoLx [0x23454; 0x2233c] 40%nat
           [KZRange dcap 1 (2^32); KZRange o2 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 256) 152]
           [(SPV - 416, 160); (SPV - 256, 152)].
    all: kx_mem.
    all: unfold x41r_hide in *.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144468) _ _ ?m2 _) =>
             eapply (x41_ret_c ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX m2);
             [ eapply (x41_einv_f m2);
               first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | exact FA' | exact AR' | reflexivity ]
             | first [left; reflexivity | right; split; reflexivity] ]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 140092) _ _ ?m2 _) =>
             replace A1 with (DST + (A1 - DST)) by lia;
             eapply (x41_f3_3 m2 (A1 - DST) q SRC n src i3 o3)
         end.
    all: first [ exact (conj SV' (conj STK' (conj MUP' WMP'))) | exact KXMI | exact OUT' | exact DTB' | exact FA' | exact AR'
               | exact SB' | exact SL | exact DJS | exact DKS | lia ].
  Qed.

End DX41R.
