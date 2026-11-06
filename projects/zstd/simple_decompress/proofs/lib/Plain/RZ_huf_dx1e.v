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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX1E.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 48 [] m0 huf_noQ).
  Notation DINVc := (DINV s0 s1 s2 s3 s4 s5 m0 SPV DST dcap SRC DT lo src dtb).
  Notation STpc pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold DINV; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Lemma x1_main : forall mm pend dl (x5 x6 x7 x8 x9 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINVc mm -> 1 <= n -> pend = DST + dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (STpc 0x1e360 mm x5 x6 x7 x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
                         (Z_to_bv 64 DT) (Z_to_bv 64 dl) (Z_to_bv 64 pend) (Z_to_bv 64 8) x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm pend dl x5 x6 x7 x8 x9 x18 x19 x20 x21 x28 x29 x30 x31 DI HN PE HDL.
    pose proof CTX as CTX'. x1_ctx_open CTX'.
    pose proof DI as DI'. dinv_open DI'.
    Time kx_auto_v 8 [0x1e458; 0x1e608; 0x1e764; 0x1e768; 0x1e7a4; 0x1e7bc] 300%nat
      [KZRange n 1 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange pend 4096 (2^47); KZRange dl 0 65535;
       KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange DT 4096 (2^47); KZImg 0x10000 0x14000]
      [(SRC, n)].
    all: subst pend dl; rewrite ?(neg_dl_sh tl rsv TL).
    Time all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124860) _ _ _ _) => apply (x1_err_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [exact DI | split; [vm_compute; reflexivity | reflexivity]]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124772) _ _ _ _) => eapply (x1_698p_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [exact DI | lia | lia | reflexivity]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124424) _ _ _ _) =>
             replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
             replace (DST + dcap + -3) with (DST + dcap - 3) by lia;
             eapply (x1_loop_off0_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [exact DI | lia | reflexivity]
         | |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                          _ (Z_to_bv 64 123992) _ _ _ _) =>
             let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
             kx_read_ranges;
             lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 8))%bool end;
             cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
             eapply (x1_init8_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [exact DI | split; [exact B1 | exact B2] | lia | lia | reflexivity]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv psegs m0 -> stk psegs m0 lo SPV -> stk psegs m0 DST (DST + dcap) -> bytes_at psegs m0 SRC src -> bytes_at psegs m0 DT dtb ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e328) fc None m0 (seg_rom psegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x1_ctx_open CTX'.
    assert (MU : munch [(DST, DST + dcap); (SPV - 48, SPV)] m0 m0) by apply munch_refl.
    assert (WM : wmono psegs m0 m0) by apply wmono_refl.
    assert (N0 : 0 <= n) by lia.
    carve_frame 48%nat STK.
    assert (LEAF : forall P : Prop, P -> P) by (intros P p; exact p).
    destruct (Z.eq_dec dcap 0) as [DC0|DC1].
    - Time kx_autoLx [0x1e360; 0x1e7bc] 60%nat
        [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 0; KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
         KZRange DT 4096 (2^47); KZWr (SPV - 48) 48; KZDisj (SPV - 48) 48 DT 16388]
        [(DT, 16388)].
      + kx_mem. apply (x1_err_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [dinv_close | split; [vm_compute; reflexivity | reflexivity]].
      + kx_read_eq 31%nat RD.
        rewrite (rdval_bytes_at psegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
                (dl_read_c _ _ _ _ _ _ _ _ _ _ _ CTX) in RD.
        rewrite RD. kx_mem.
        eapply x1_main; [dinv_close | lia | lia | reflexivity].
    - Time kx_autoLx [0x1e360; 0x1e7bc] 60%nat
        [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
         KZRange DT 4096 (2^47); KZWr (SPV - 48) 48; KZDisj (SPV - 48) 48 DT 16388]
        [(DT, 16388)].
      + kx_mem. apply (x1_err_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX); [dinv_close | split; [vm_compute; reflexivity | reflexivity]].
      + kx_read_eq 31%nat RD.
        rewrite (rdval_bytes_at psegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
                (dl_read_c _ _ _ _ _ _ _ _ _ _ _ CTX) in RD.
        rewrite RD. kx_mem.
        eapply x1_main; [dinv_close | lia | lia | reflexivity].
  Qed.
End DX1E.

(* [comment removed for export] *)
Theorem huf_1x1_proof : huf_1x1_stmt.
Proof.
  unfold huf_1x1_stmt, huf_int_stmt_at, PHUF_1X1.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1)
         (DTB & DL & T0 & T1 & OS3 & DJ2) DT2 TL _ _.
  unfold HUF_DTABLE_BYTES in *.
  destruct (nth_error dtb 3) as [b3|] eqn:DT3;
    [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x1_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x1_ctx. rewrite EB. repeat split; try assumption; lia. }
  exact (x1_entry ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb CTX
                  t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.
