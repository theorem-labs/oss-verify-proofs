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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX2E.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) (b0 b1 : byte).
  Hypothesis CTX : x2_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis DT0 : nth_error dtb 0 = Some b0.
  Hypothesis DT1 : nth_error dtb 1 = Some b1.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 48 [] m0 huf_noQ).
  Notation DINV := (RZ_huf_dx1.DINV s0 s1 s2 s3 s4 s5 m0 SPV DST dcap SRC DT lo src dtb).
  Notation LINV := (RZ_huf_dx2.LINV n).
  Notation STpc pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold RZ_huf_dx1.DINV; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Lemma hdr_read : extz false 4 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat 0) dtb)))
                   = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv.
  Proof.
    pose proof CTX as CTX'. x2_ctx_open CTX'.
    assert (E : firstn 4 (skipn (Z.to_nat 0) dtb) = [b0; b1; Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 0) with 0%nat.
      destruct dtb as [|y0 [|y1 [|y2 [|y3 r]]]]; cbn in DT0, DT1, DT2, DT3; try discriminate.
      injection DT0 as ->. injection DT1 as ->. injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !(Z_to_bv_unsigned 8), !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  Notation C29 f := (f ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).

  (* [comment removed for export] *)
  Ltac x2_mb_leaf DI :=
    repeat match goal with H : ?x = DST + dcap |- _ => subst x | H : ?x = tl + 256 * rsv |- _ => subst x end;
    rewrite ?(neg_dl_sh tl rsv) by lia;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 123032) _ _ _ _) =>
        eapply (C29 x2_fcc_p_c); [exact DI | lia | lia | reflexivity | lia |
          let B := fresh "B" in intro B;
          first [ exfalso; lia
                | lazymatch goal with
                  | |- exists o, Z_to_bv 64 ?X = Z_to_bv 64 (SRC + o) /\ _ =>
                      exists (X - SRC); split; [f_equal; lia | unfold OINV; lia]
                  end ] ]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 121968) _ _ _ _) =>
        replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
        replace (DST + dcap + -9) with (DST + dcap - 9) by lia;
        eapply (C29 x2_loop5_c (Z.to_nat dcap)); [exact DI | lia | lia | reflexivity | reflexivity | lia | unfold RZ_huf_dx2.LINV; lia]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 122556) _ _ _ _) =>
        replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
        replace (DST + dcap + -7) with (DST + dcap - 7) by lia;
        eapply (C29 x2_loop4_c (Z.to_nat dcap)); [exact DI | lia | lia | reflexivity | reflexivity | lia | unfold RZ_huf_dx2.LINV; lia]
    end.

  (* [comment removed for export] *)
  Lemma x2_main_b : forall mm pend dl off bc (x6 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> pend = DST + dcap -> dl = tl + 256 * rsv -> 0 <= bc < 2^64 -> LINV off bc ->
    evt psegs POST (STpc 0x1dc40 mm (Z_to_bv 64 off) x6 (Z_to_bv 64 8) x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
                         (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl) (Z_to_bv 64 pend) (Z_to_bv 64 bc) x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm pend dl off bc x6 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI PE HDL HB INV.
    pose proof CTX as CTX'. x2_ctx_open CTX'.
    pose proof DI as DI'. dinv_open DI'.
    destruct INV as [-> | (O1 & O2 & B1)].
    - kx_autoLx [0x1dc70; 0x1debc; 0x1e098] 100%nat
        [KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange pend 4096 (2^47); KZRange dl 0 65535; KZRange SRC 4096 (2^47)]
        (@nil (Z * Z)).
      all: x2_mb_leaf DI.
    - Time kx_autoLx [0x1dc70; 0x1debc; 0x1e098] 100%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 (2^32); KZRange bc 0 64; KZRange n 9 (2^32);
         KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange pend 4096 (2^47); KZRange dl 0 65535;
         KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47)]
        [(SRC, n)].
      all: rewrite ?(Z.mod_small bc (2^64)) in * by lia; kx_land_ranges; kx_strip_mod.
      all: x2_mb_leaf DI.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_main_a : forall off bc (t1 t2 a3 a5 a7 t3 t4 t5 t6 : word),
    mem_inv psegs m0 -> stk psegs m0 lo SPV -> stk psegs m0 DST (DST + dcap) -> bytes_at psegs m0 SRC src -> bytes_at psegs m0 DT dtb ->
    0 <= bc < 2^64 -> LINV off bc ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp (Z_to_bv 64 off) t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) a3
               (Z_to_bv 64 DT) a5 (Z_to_bv 64 bc) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1dc04) fc None m0 (seg_rom psegs)).
  Proof.
    intros off bc t1 t2 a3 a5 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB HB INV.
    pose proof CTX as CTX'. x2_ctx_open CTX'.
    assert (MU : munch [(DST, DST + dcap); (SPV - 48, SPV)] m0 m0) by apply munch_refl.
    assert (WM : wmono psegs m0 m0) by apply wmono_refl.
    assert (B0 : 0 <= bv_unsigned b0 <= 255) by (pose proof (bv_unsigned_in_range 8 b0) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 8) with 256 in X; lia).
    assert (B1 : 0 <= bv_unsigned b1 <= 255) by (pose proof (bv_unsigned_in_range 8 b1) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 8) with 256 in X; lia).
    carve_frame 48%nat STK.
    assert (FIN : forall mm pend (x : Z) (x6 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
              DINV mm -> pend = DST + dcap -> x = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv ->
              evt psegs POST (STpc 0x1dc40 mm (Z_to_bv 64 off) x6 (Z_to_bv 64 8) x8 x9 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
                                   (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (x / 65536)) (Z_to_bv 64 pend) (Z_to_bv 64 bc)
                                   x17 x18 x19 x20 x21 x28 x29 x30 x31)).
    { intros mm pend x x6 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI PE HX.
      eapply x2_main_b; [exact DI | exact PE | subst x; lia | exact HB | exact INV]. }
    assert (LEAF : True) by exact I.
    destruct (Z.eq_dec dcap 0) as [DC0|DC1].
    - kx_autoLx [0x1dc40] 40%nat
        [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 0; KZRange DT 4096 (2^47); KZWr (SPV - 48) 48;
         KZDisj (SPV - 48) 48 DT 16388]
        [(DT, 16388)].
      kx_read_eq 31%nat RD.
      rewrite (rdval_bytes_at psegs _ DT dtb 0 4 false DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)), hdr_read in RD.
      assert (HX : bv_unsigned (ev KXE 31) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv)
        by (rewrite RD, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
      kx_mem. eapply FIN; [dinv_close | lia | exact HX].
    - kx_autoLx [0x1dc40] 40%nat
        [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange DT 4096 (2^47); KZWr (SPV - 48) 48;
         KZDisj (SPV - 48) 48 DT 16388]
        [(DT, 16388)].
      kx_read_eq 31%nat RD.
      rewrite (rdval_bytes_at psegs _ DT dtb 0 4 false DTB ltac:(lia) ltac:(change (Z.to_nat 0) with 0%nat; lia)), hdr_read in RD.
      assert (HX : bv_unsigned (ev KXE 31) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * tl + 16777216 * rsv)
        by (rewrite RD, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
      kx_mem. eapply FIN; [dinv_close | lia | exact HX].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv psegs m0 -> stk psegs m0 lo SPV -> stk psegs m0 DST (DST + dcap) -> bytes_at psegs m0 SRC src -> bytes_at psegs m0 DT dtb ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1da04) fc None m0 (seg_rom psegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB.
    pose proof CTX as CTX'. x2_ctx_open CTX'.
    assert (N0 : 0 <= n) by lia.
    Time kx_auto_v 8 [0x1dc04] 300%nat
      [KZRange SRC 4096 (2^47); KZRange n 0 (2^32); KZRange (SRC + n) 4096 (2^47); KZImg 0x10000 0x14000]
      [(SRC, n)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 121860) _ _ _ _) => idtac
         | _ => zstep; apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end);
                (split; [reflexivity|]); (split; [apply munch_refl|]); (split; [apply wmono_refl|]); (split; [exact MI|]);
                (split; [exact STK|]); (split; [exact OUT|]); (split; [right; vm_compute; reflexivity | split; [lia | exact I]])
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
             eapply x2_main_a; [exact MI | exact STK | exact OUT | exact SRCB | exact DTB | kx_lia | left; reflexivity]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned (edenot ?E ?e))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
             let BCE := fresh "BCE" in let B1 := fresh "B1" in let B2 := fresh "B2" in
             kx_read_ranges;
             lazymatch e with context [EVar ?j] => kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v) && (v <=? 8))%bool end;
             cbv beta in BCE; apply andb_prop in BCE as [B1 B2]; apply Z.leb_le in B1, B2;
             eapply x2_main_a; [exact MI | exact STK | exact OUT | exact SRCB | exact DTB | lia | unfold RZ_huf_dx2.LINV; lia]
         end.
  Qed.
End DX2E.

(* [comment removed for export] *)
Theorem huf_1x2_proof : huf_1x2_stmt.
Proof.
  unfold huf_1x2_stmt, huf_int_stmt_at, PHUF_1X2.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1)
         (DTB & DL & T0 & T1 & OS3 & DJ2) DT2 TL X2 _.
  unfold HUF_DTABLE_BYTES in *.
  destruct (nth_error dtb 0) as [b0|] eqn:DT0; [| apply nth_error_None in DT0; exfalso; lia].
  destruct (nth_error dtb 1) as [b1|] eqn:DT1; [| apply nth_error_None in DT1; exfalso; lia].
  destruct (nth_error dtb 3) as [b3|] eqn:DT3; [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x2_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    split; [|exact (X2 eq_refl)].
    unfold x1_ctx. rewrite EB. repeat split; try assumption; lia. }
  exact (x2_entry ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb b0 b1
                  CTX DT0 DT1 t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT SRCB DTB).
Qed.
