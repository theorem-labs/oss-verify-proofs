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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41q RZ_huf_fkit RZ_huf_dx41r RZ_huf_dx41r2 RZ_huf_dx41t.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41U.
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

  Notation X41PF := (RZ_huf_dx41r.X41PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41pf_transport := (RZ_huf_dx41r.x41pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x41_f3_0 := (RZ_huf_dx41r2.x41_f3_0).
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  (* [comment removed for export] *)
  Ltac x41_mulhu_rb :=
    repeat match goal with
    | KXA : atoms_ok ?zs ?E |- _ =>
        let go a b :=
            let nz := kx_len zs in let ua := kx_uz E zs nz a in let ub := kx_uz E zs nz b in
            let HD := fresh "HD" in
            assert (HD : bv_unsigned (edenot E (EMd M_MULHU a b)) = ua * ub / 2 ^ 64)
              by (change (edenot E (EMd M_MULHU a b)) with (mul_div M_MULHU (edenot E a) (edenot E b)); rewrite KXS.u_mulhu64;
                  rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA); reflexivity);
            rewrite HD in *; clear HD in
        match goal with
        | |- context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] => go a b
        | H : context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] |- _ => go a b
        end
    end.

  Lemma x41_f2 : forall mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
      (ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x8 x9 x11 x12 x13 x15 x16 x18 x19 x20 x22 x23 x25 x26 x27 x28 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w13 w14 w15 w17 w18 w19 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w13 w14 w15 (Z_to_bv 64 (DST + dcap)) w17 w18 w19 ->
    ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap ->
    evt psegs POST (ST 0x222e0 mm x1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0)) x8 x9 (Z_to_bv 64 (DT + 4)) x11 x12 x13 (Z_to_bv 64 69944) x15 x16 (Z_to_bv 64 (SRC + i3)) x18 x19 x20 (Z_to_bv 64 (DST + o3)) x22 x23 (Z_to_bv 64 69156) x25 x26 x27 x28 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2))).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
      ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x8 x9 x11 x12 x13 x15 x16 x18 x19 x20 x22 x23 x25 x26 x27 x28
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w13 w14 w15 w17 w18 w19 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HDC HI0 HJ0 HO0 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3.
    assert (KS : SRC + n <= SPV - 416 \/ SPV <= SRC) by (clear - DKS LO; lia).
    assert (KD : DST + dcap <= SPV - 416 \/ SPV <= DST) by (clear - OS1 LO; lia).
    assert (KT : DT + 16388 <= SPV - 416 \/ SPV <= DT) by (clear - DJ3 LO; lia).
    destruct PV as (SV & STK & MUP & WMP).
    kx_autoLx [0x2233c] 60%nat
      [KZImg 0x10000 0x14000; KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 256) 152]
      [(SPV - 416, 160); (SPV - 256, 152); (0x110e0, 8)].
    kx_mem. kx_strip_mod.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
        let HF := fresh "HF" in
        pose proof (x41_f3_0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX DJ3 m2 0 ((dcap + 3) / 4) SRC n src i0 o0 i1 o1 i2 o2 i3 o3) as HF;
        replace (DST + 0) with DST in HF by lia; eapply HF
    end.
    all: first [ exact (conj SV (conj STK (conj MUP WMP))) | exact KXMI | exact OUT | exact DTB | exact FA | exact AR | exact SB | exact SL
               | exact DJS | exact DKS | lia ].
  Qed.

  Lemma x41_fo : forall (k : nat) mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
      (ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3 : word)
      (x1 x8 x9 x11 x12 x13 x14 x15 x16 x18 x20 x22 x25 x26 x27 x28 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w13 w14 w15 : word),
    X41PF mm -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) w13 w14 w15 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 2635249153387078803) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 SRC) ->
    ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw (Z_to_bv 64 SRC) oew ie0 ie1 ie2 ie3 ->
    bytes_at psegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
    (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
    0 < dcap -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap ->
    o0 <= o3 -> o1 <= o3 -> o2 <= o3 -> dcap - o3 < Z.of_nat k ->
    evt psegs POST (ST 0x21e28 mm x1 (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i0)) x8 x9 (Z_to_bv 64 (DT + 4)) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (SRC + i3)) x18 (Z_to_bv 64 (DT + 4)) x20 (Z_to_bv 64 (DST + o3)) x22 (Z_to_bv 64 14757395258967641293) (Z_to_bv 64 69156) x25 x26 x27 x28 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2))).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    induction k as [|k IH]; intros mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
      ip0 ip1 ip2 ip3 op0 op1 op2 op3 bt0 bt1 bt2 bt3 dtw oew ie0 ie1 ie2 ie3
      x1 x8 x9 x11 x12 x13 x14 x15 x16 x18 x20 x22 x25 x26 x27 x28
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w13 w14 w15 PV MI OUT DTB FA AR SB SL S0 S1 SL32 DJS DKS HDC HI0 HJ0 HO0 HI1 HJ1 HO1 HI2 HJ2 HO2 HI3 HJ3 HO3 HL0 HL1 HL2 HK; [exfalso; lia|].
    kx_autoLx [0x222e0; 0x21e84] 60%nat
      [KZImg 0x10000 0x14000; KZRange o3 0 (2^32); KZRange i0 0 (2^32); KZRange i1 0 (2^32); KZRange i2 0 (2^32); KZRange i3 0 (2^32);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange SRC 4096 (2^47); KZRange SPV 4096 (2^47)]
      [(SPV - 416, 160)].
    all: x41_mulhu_rb.
    all: kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 140000) _ _ _ _) =>
             eapply (x41_f2 mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3);
             first [ exact PV | exact MI | exact OUT | exact DTB | exact FA | exact AR | exact SB | exact SL | exact DJS | exact DKS | lia ]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + (_ + 5 * ?R))) _ _ _ _ _ _) _ (Z_to_bv 64 138884) _ _ _ _) =>
             assert (HR1 : 1 <= R) by lia;
             assert (HR5 : 5 * R <= dcap - o3) by lia;
             assert (HR7 : 7 * R <= i0) by lia;
             let RR := fresh "RR" in set (RR := R) in *; clearbody RR;
             eapply (x41_fi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX (Z.to_nat RR) mm mm SRC n src i0 i1 i2 i3 o0 o1 o2 o3
                       (o0 + 5 * RR) (o1 + 5 * RR) (o2 + 5 * RR) (o3 + 5 * RR))
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ apply munch_refl | apply wmono_refl | exact MI | exact OUT | exact DTB | exact SB | exact SL | exact DJS | lia ]
         end.
    (* [comment removed for export] *)
    all: intros mm' I0 I1 I2 I3; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros MU' WM' MI' OUT' DTB' HI0' HI1' HI2' HI3' HN0' HN1' HN2' HN3'.
    all: pose proof (rw_cells_transport psegs _ mm mm' _ _ FA MU' WM') as FA';
         pose proof (rw_cells_transport psegs _ mm mm' _ _ AR MU' WM') as AR';
         pose proof (x41pf_transport mm mm' PV MU' WM') as PV';
         pose proof (bytes_at_transport psegs _ mm mm' SRC src SB MU') as SB'.
    all: cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FA', AR', SB'.
    all: specialize (FA' ltac:(clear - OS1 LO; lia)); specialize (AR' ltac:(clear - OS1 LO; lia)); specialize (SB' ltac:(clear - DJS SL; lia)).
    all: eapply (IH mm' SRC n src I0 I1 I2 I3 (o0 + 5 * RR) (o1 + 5 * RR) (o2 + 5 * RR) (o3 + 5 * RR));
         first [ exact PV' | exact MI' | exact OUT' | exact DTB' | exact FA' | exact AR' | exact SB' | exact SL | exact DJS | exact DKS | lia ].
  Qed.

End DX41U.
