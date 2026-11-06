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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_iface2 RZ_huf_dx41 RZ_huf_fkit RZ_huf_dx41f RZ_huf_dx41r RZ_huf_dx42_14 RZ_huf_dx42_24.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

Theorem huf_4x2_proof : bit_init_stmt -> fast_args_stmt2 -> huf_4x2_stmt.
Proof.
  intros BITINIT FASTARGS. unfold huf_4x2_stmt, huf_int_stmt_at, PHUF_4X2, HUF_4X_STACK.
  intros ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT tl lo src dtb
    PRE DTP DT2 HTL X2OK' NBOK.
  pose proof (X2OK' eq_refl) as X2OK. clear X2OK'.
  destruct PRE as (MI & STK & LO0 & LO1 & SPB & OUT & D0 & D1 & D2 & SRCB & SRCL & S0 & SN & S1 & OS1 & OS2 & DJ1).
  destruct DTP as (DTB & DL & T0 & T1 & OS3 & DJ2). unfold HUF_DTABLE_BYTES in *.
  assert (CTX : x41_ctx SPV DST dcap DT lo dtb) by (unfold x41_ctx; repeat split; try assumption; lia).
  destruct (nth_error dtb 3) as [b3|] eqn:E3; [|apply nth_error_None in E3; lia].
  set (rsv := bv_unsigned b3).
  assert (DT3 : nth_error dtb 3 = Some (Z_to_bv 8 rsv)) by (subst rsv; rewrite definitions.Z_to_bv_bv_unsigned; exact E3).
  assert (HRSV : 0 <= rsv <= 255) by (subst rsv; pose proof (bv_unsigned_in_range 8 b3) as HB; unfold bv_modulus in HB; change (2 ^ Z.of_N 8) with 256 in HB; lia).
  clearbody rsv. clear E3.
  assert (MU : munch [(DST, DST + dcap); (SPV - 432, SPV)] m m) by apply munch_refl.
  assert (WM : wmono psegs m m) by apply wmono_refl.
  carve_frame 416%nat STK.
  (* [comment removed for export] *)
  destruct (cb_carve psegs m (SPV + -416) 416 junk 160 152 FR ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & C1 & C2 & C3).
  change (Z.to_nat 160) with 160%nat in C1. change (Z.to_nat 152) with 152%nat in C2.
  change (416 - Z.to_nat 160 - Z.to_nat 152)%nat with 104%nat in C3.
  replace (SPV + -416 + 160) with (SPV + -256) in C2 by lia. replace (SPV + -416 + 160 + 152) with (SPV + -104) in C3 by lia.
  destruct (cb160_as_c8s m _ j1 C1) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17
                                         & w18 & w19 & FA).
  clear FR C1.
  kx_autoLx [0x1f538; 0x24398] 60%nat
    [KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 104) 104]
    [(SPV - 416, 160)].
  all: kx_mem.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 128312) _ _ ?m2 _) =>
           destruct (cb_carve psegs m2 (SPV + -256) 152 j2 40 112 C2 ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & B1 & B2 & _);
           change (Z.to_nat 40) with 40%nat in B1; change (Z.to_nat 112) with 112%nat in B2;
           replace (SPV + -256 + 40) with (SPV + -216) in B2 by lia;
           eapply (x42_s0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT m2 k2 SRC n src k1);
           first [ exact (conj C3 (conj STK (conj B2 (conj MU WM)))) | exact KXMI | exact OUT | exact DTB | exact DT2 | exact DT3
                 | exact FA | exact B1 | exact SRCB | exact SRCL | exact DJ1 | exact OS2 | lia ]
       | _ => idtac
       end.
  (* [comment removed for export] *)
  assert (DTH : bytes_at psegs m0 DT (firstn 4 dtb)).
  { pose proof DTB as DTB'. rewrite <- (firstn_skipn 4 dtb) in DTB'. apply bytes_at_app in DTB'. exact (proj1 DTB'). }
  assert (DTHL : zlen (firstn 4 dtb) = 4) by (rewrite firstn_length; lia).
  clear KXK KXA KXRD.
  eapply evt_cut; [eapply FASTARGS with (SPV := SPV + -416) (ARGS := SPV + -256) (src := src) (dth := firstn 4 dtb) (junk := j2) (lo := lo)
                  | unfold fast_args_post2; post_call psegs m0].
  1-25: first [exact KXMI | exact STK | exact C2 | exact SRCB | exact SRCL | exact DTH | exact DTHL | lia].
  lazymatch type of POST with context [rw_cells psegs ?mmm (SPV + -256)] => rename mmm into m1 end.
  lazymatch type of POST with (?rr = 1 /\ _) \/ _ => rename rr into r end.
  destruct POST as [(HR & l1 & l2 & l3 & b0 & b1 & b2 & b3' & HL1 & HL2 & HL3 & HLN & HQ3 & AR & HLOG) | (HR & HRB & bs & AR)].
  - subst r.
    assert (TL11 : tl = 11).
    { assert (E : nth_error (firstn 4 dtb) 2 = nth_error dtb 2).
      { destruct dtb as [|y0 [|y1 [|y2 [|y3 rr]]]]; reflexivity. }
      rewrite E, DT2 in HLOG.
      assert (HLOG' : Z_to_bv 8 tl = Z_to_bv 8 11) by (clear - HLOG; congruence).
      apply (f_equal bv_unsigned) in HLOG'.
      rewrite !Z_to_bv_unsigned, !bv_wrap_small in HLOG' by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). exact HLOG'. }
    eapply (x42_f0_ok ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT)
      with (l1 := l1) (l2 := l2) (l3 := l3);
    first [ exact TL11 | exact (conj C3 (conj PC (conj MU WM))) | exact MI | exact OUT | exact DTB | exact FA
          | exact AR | exact SRCB | exact SRCL | exact DJ1 | exact OS2 | lia ].
  - eapply (x42_f0_no ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT);
    first [ exact (conj C3 (conj PC (conj MU WM))) | exact MI | exact OUT | exact DTB
          | exact DT2 | exact DT3 | exact FA | exact AR | exact SRCB | exact SRCL | exact DJ1 | exact OS2
          | exact HR | lia ].
Qed.
