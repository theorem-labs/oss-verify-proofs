(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_iface2 RZ_huf_dx41 RZ_huf_fkit RZ_huf_dx41f RZ_huf_dx41r RZ_huf_dx42_14 RZ_huf_dx42_24 huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

Lemma x25_cb128 : forall m A bs, rw_cells usegs m A [CB 128 bs] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : word,
    rw_cells usegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                        C8 w14; C8 w15].
Proof.
  intros m A bs H. pose proof (cb_as_c8s m A 16 bs H) as H2. cbn [c8s_of] in H2.
  do 16 eexists. exact H2.
Qed.

Ltac x25_at off := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
      let b := eval vm_compute in (Z.eqb p (PHUF_4X2 + off)) in lazymatch b with true => idtac end
  end.

Theorem huf_4x2_proof : bit_init_stmt -> fast_args_stmt2 -> huf_4x2_stmt.
Proof.
  intros BITINIT FASTARGS. unfold huf_4x2_stmt, huf_int_stmt_at, PHUF_4X2, HUF_4X_STACK.
  intros ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT tl lo src dtb
    PRE DTP DT2 HTL X2OK' NBOK.
  pose proof (X2OK' eq_refl) as X2OK. clear X2OK'.
  destruct PRE as (MI & STK & LO0 & LO1 & SPB & OUT & D0 & D1 & D2 & SRCB & SRCL & S0 & SN & S1 & OS1 & OS2 & DJ1 & SA16).
  destruct DTP as (DTB & DL & T0 & T1 & OS3 & DJ2 & DA4). unfold HUF_DTABLE_BYTES in *.
  pose proof (rsk_al_i _ _ SA16) as SPVA. pose proof (rsk_al_i _ _ DA4) as DTA. clear SA16 DA4.
  assert (CTX : x41_ctx SPV DST dcap DT lo dtb) by (unfold x41_ctx; repeat split; try assumption; lia).
  destruct (nth_error dtb 3) as [b3|] eqn:E3; [|apply nth_error_None in E3; lia].
  set (rsv := bv_unsigned b3).
  assert (DT3 : nth_error dtb 3 = Some (Z_to_bv 8 rsv)) by (subst rsv; rewrite definitions.Z_to_bv_bv_unsigned; exact E3).
  assert (HRSV : 0 <= rsv <= 255) by (subst rsv; pose proof (bv_unsigned_in_range 8 b3) as HB; unfold bv_modulus in HB; change (2 ^ Z.of_N 8) with 256 in HB; lia).
  clearbody rsv. clear E3.
  assert (MU : munch [(DST, DST + dcap); (SPV - 912, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  carve_frame 512%nat STK.
  (* [comment removed for export] *)
  destruct (cb_carve usegs m (SPV + -512) 512 junk 408 104 FR ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & C1 & C2 & _).
  change (Z.to_nat 408) with 408%nat in C1. change (Z.to_nat 104) with 104%nat in C2.
  replace (SPV + -512 + 408) with (SPV + -104) in C2 by lia.
  clear FR.
  kx_autoLx [PHUF_4X2 + 76; PHUF_4X2 + 4848] 60%nat
    [KZRange SPV 4096 (2^47); KZWr (SPV - 104) 104]
    [].
  all: kx_mem.
  (* [comment removed for export] *)
  all: tryif x25_at 4848 then
         (eapply (x42_s0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT
                    SPVA DTA _ j1 SRC n src);
          first [ exact (conj C2 (conj C1 (conj STK (conj MU WM)))) | exact KXMI | exact OUT | exact DTB | exact DT2 | exact DT3
                | exact SRCB | exact SRCL | exact DJ1 | exact OS2 | lia ])
       else idtac.
  (* [comment removed for export] *)
  clear KXK KXA KXRD.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (cb_carve usegs m1 (SPV + -512) 408 j1 128 152 C1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & B1 & B2 & B3)
  end.
  change (Z.to_nat 128) with 128%nat in B1. change (Z.to_nat 152) with 152%nat in B2.
  change (408 - Z.to_nat 128 - Z.to_nat 152)%nat with 128%nat in B3.
  replace (SPV + -512 + 128) with (SPV + -384) in B2 by lia. replace (SPV + -512 + 128 + 152) with (SPV + -232) in B3 by lia.
  destruct (x25_cb128 _ _ k1 B1) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & FA).
  destruct (x25_cb128 _ _ k3 B3) as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & u15 & LA).
  clear C1 B1 B3.
  assert (DTHL : zlen (firstn 4 dtb) = 4) by (rewrite firstn_length; lia).
  destruct (Z.eq_dec dcap 0) as [DC0 | DC1];
    [ kx_autoLx [PHUF_FASTARGS] 60%nat
        [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 0; KZRange DT 4096 (2^47); KZWr (SPV - 512) 128]
        [(SPV - 512, 128)]
    | kx_autoLx [PHUF_FASTARGS] 60%nat
        [KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange DT 4096 (2^47); KZWr (SPV - 512) 128]
        [(SPV - 512, 128)] ].
  all: kx_mem.
  all: clear KXK KXA KXRD.
  
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
           assert (DTH : bytes_at usegs mc DT (firstn 4 dtb))
             by (pose proof DTB as DTB'; rewrite <- (firstn_skipn 4 dtb) in DTB'; apply bytes_at_app in DTB'; exact (proj1 DTB'));
           eapply evt_cut;
           [ eapply FASTARGS with (SPV := SPV + -512) (ARGS := SPV + -384) (src := src) (dth := firstn 4 dtb) (junk := k2) (lo := lo);
             first [ assumption | exact (rsk_al_e _ _ DTA)
                   | lia | (pose proof (rsk_al_e _ _ SPVA); lia) ]
           | unfold fast_args_post2; post_call usegs mc ]
       end.
  all: lazymatch type of POST with (?rr = 1 /\ _) \/ _ => rename rr into r end.
  all: destruct POST as [(HR & l1 & l2 & l3 & b0 & b1 & b2 & b3' & HL1 & HL2 & HL3 & HLN & HQ3 & AR & HLOG & HM0 & HM1 & HM2 & HM3)
                        | (HR & HRB & bs & AR)].
  - exfalso. clear - DC0 HQ3. subst dcap. Z.div_mod_to_equations. lia.
  - subst dcap.
    eapply (x42_f0_no ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST 0 DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT SPVA DTA);
    first [ exact (conj C2 (conj PC (conj MU WM))) | (match goal with H : mem_inv _ _ |- _ => exact H end) | exact OUT | exact DTB
          | exact DT2 | exact DT3 | exact FA | exact AR | exact LA | exact SRCB | exact SRCL | exact DJ1 | exact OS2
          | exact HR | exact HRB | lia ].
  - subst r.
    assert (TL11 : tl = 11).
    { assert (E : nth_error (firstn 4 dtb) 2 = nth_error dtb 2).
      { destruct dtb as [|y0 [|y1 [|y2 [|y3 rr]]]]; reflexivity. }
      rewrite E, DT2 in HLOG.
      assert (HLOG' : Z_to_bv 8 tl = Z_to_bv 8 11) by (clear - HLOG; congruence).
      apply (f_equal bv_unsigned) in HLOG'.
      rewrite !Z_to_bv_unsigned, !bv_wrap_small in HLOG' by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). exact HLOG'. }
    eapply (x42_f0_ok ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT SPVA DTA)
      with (l1 := l1) (l2 := l2) (l3 := l3);
    first [ exact TL11 | exact (conj C2 (conj PC (conj MU WM))) | (match goal with H : mem_inv _ _ |- _ => exact H end) | exact OUT | exact DTB | exact FA
          | exact AR | exact LA | exact SRCB | exact SRCL | exact DJ1 | exact OS2 | exact HM0 | exact HM1 | exact HM2 | exact HM3 | lia ].
  - eapply (x42_f0_no ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap DT lo dtb CTX tl rsv HTL HRSV X2OK OS3 NBOK BITINIT SPVA DTA);
    first [ exact (conj C2 (conj PC (conj MU WM))) | (match goal with H : mem_inv _ _ |- _ => exact H end) | exact OUT | exact DTB
          | exact DT2 | exact DT3 | exact FA | exact AR | exact LA | exact SRCB | exact SRCL | exact DJ1 | exact OS2
          | exact HR | exact HRB | lia ].
Qed.

