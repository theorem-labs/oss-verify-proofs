(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition x2_dinv (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) (m0 : fmem) (SPV DST dcap SRC DT lo : Z) (src dtb : list byte) (mm : fmem) : Prop :=
  stk usegs mm DST (DST + dcap) /\
  rw_cells usegs mm (SPV + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk usegs mm lo (SPV + -112) /\
  bytes_at usegs mm SRC src /\ bytes_at usegs mm DT dtb /\
  munch [(DST, DST + dcap); (SPV - 144, SPV)] m0 mm /\ wmono usegs m0 mm /\ mem_inv usegs mm.

(* [comment removed for export] *)
Definition x2_bdc (SPV SRC : Z) (mm : fmem) (cw bcw : word) (pad : list byte) (pw : word) : Prop :=
  rw_cells usegs mm (SPV + -112) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (SRC + 8))].

(* [comment removed for export] *)
Definition x2_pinv (SRC n P : Z) : Prop := P = SRC \/ (SRC + 1 <= P /\ P + 8 <= SRC + n).

Section DX2.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.

  (* [comment removed for export] *)
  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 144 [] m0 huf_noQ).
  Notation DINV2 := (x2_dinv ra s0 s1 s2 s3 s4 s5 s6 s7 m0 SPV DST dcap SRC DT lo src dtb).
  Notation BDC2 := (x2_bdc SPV SRC).
  Notation PINV := (x2_pinv SRC n).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold x2_dinv; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Ltac tp_close := lazymatch goal with |- context [Z_to_bv 64 0x20714] => kx_trap_fast | _ => idtac end.

  (* [comment removed for export] *)
  Lemma x2_tbl : forall mm, bytes_at usegs mm DT dtb -> tbl_in_log usegs mm DT (64 - tl) 4 7 1 2.
  Proof.
    intros mm DTB. apply (tbl_in_log_bytes_at usegs mm DT dtb (64 - tl) 4 7 1 2 DTB); [lia | lia |].
    intros i Hi. replace (64 - (64 - tl)) with tl in Hi by lia. exact (X2OK i Hi).
  Qed.

  (* [comment removed for export] *)
  Lemma x2_ret : forall mm w cs (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    DINV2 mm -> rw_cells usegs mm (SPV + -112) cs -> cells_size cs = 40%nat ->
    (bv_unsigned w = dcap \/ zd_is_error (bv_unsigned w) = true) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SPV + -112)) gp tp x5 x6 x7 x8 x9 w x11 x12 x13 x14 x15 x16 x17
                            x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x206e8) fc None mm (seg_rom usegs)).
  Proof.
    intros mm w cs x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 DI BD SZ HR.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    dinv_open DI.
    pose proof (stk_of_rw_cells usegs mm _ _ BD) as HB. rewrite SZ in HB. change (Z.of_nat 40) with 40 in HB.
    replace (SPV + -112 + 40) with (SPV + -72) in HB by lia.
    assert (STK2 : stk usegs mm lo (SPV + -72)) by (eapply stk_merge; [exact STK | exact HB | lia]).
    clear STK HB BD. rename STK2 into STK.
    pose proof (bv_unsigned_in_range 64 w) as RW. unfold bv_modulus in RW. change (2 ^ Z.of_N 64) with (2^64) in RW.
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47)] [(SPV + -72, 72)].
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evt_done; unfold huf_dec_post; rewrite <- (Z_to_bv_bv_unsigned w);
         repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [exact HR|]); (split; [exact RW | exact I]).
  Qed.

  (* [comment removed for export] *)
  Lemma x2_err : forall mm w cs (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    DINV2 mm -> rw_cells usegs mm (SPV + -112) cs -> cells_size cs = 40%nat ->
    (bv_unsigned w = dcap \/ zd_is_error (bv_unsigned w) = true) ->
    evt usegs POST (ST 0x206e8 mm x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm w cs x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 DI BD SZ HR.
    exact (x2_ret mm w cs x1 x5 x6 x7 (Z_to_bv 64 dcap) x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                  x28 x29 x30 x31 DI BD SZ HR).
  Qed.

  (* [comment removed for export] *)
  Lemma x2_end : forall mm cw bcw pad pw (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    DINV2 mm -> BDC2 mm cw bcw pad pw ->
    evt usegs POST (ST 0x206c4 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm cw bcw pad pw x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 DI BD.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    kx_autoLx [0x206e8] 20%nat [KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange dcap 0 (2^32)] [(SPV + -112, 40)].
    all: kx_mem.
    all: eapply x2_ret; [exact DI | exact BD | reflexivity | ].
    all: first [ left; rewrite bvu_mod; apply Z.mod_small; lia | right; vm_compute; reflexivity ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma x2_last : forall mm j cw bcw pad pw (x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                    (e9 e10 e11 e12 e13 : Z),
    DINV2 mm -> BDC2 mm cw bcw pad pw -> 0 <= j <= dcap ->
    e9 mod 2^64 = (DST + j) mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    evt usegs POST (ST 0x2063c mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                       (Z_to_bv 64 e13) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13
      DI BD HJ H9 H10 H11 H12 H13.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm e9 _ H9), (zbv_eqm e10 _ H10), (zbv_eqm e11 _ H11),
            (zbv_eqm e12 2305843009213693952 ltac:(rewrite H12; reflexivity)), (zbv_eqm e13 _ H13).
    clear H9 H10 H11 H12 H13.
    destruct (Z_lt_le_dec j dcap) as [ROOM|FULL]; cycle 1.
    - assert (HJD : j = dcap) by lia. subst j.
      kx_autoLx [0x206c4] 6%nat [KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47)]
        (@nil (Z * Z)).
      all: eapply x2_end; [exact DI | exact BD].
    - assert (TLC : tl = 1 \/ tl = 2 \/ tl = 3 \/ tl = 4 \/ tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
      repeat (destruct TLC as [TLC|TLC]); rewrite TLC;
        kx_autoLx [0x206c4] 60%nat
          [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47);
           KZRange (DST + j) 4096 (2^47); KZRange DT 4096 (2^47); KZRange rsv 0 255; KZRange SPV 4096 (2^47);
           KZWr DST dcap; KZWr (SPV + -112) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -112) 40;
           KZDisj (SPV + -112) 40 DT 16388]
          [(DT, 16388); (SPV + -112, 40)].
      all: tp_close.
      all: kx_mem.
      all: eapply x2_end; [dinv_close | unfold x2_bdc; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma x2_tloop : forall (k : nat) mm j cw bcw pad pw (x1 x5 x6 x7 x14 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                     (e9 e10 e11 e12 e13 e15 e16 e17 : Z),
    DINV2 mm -> BDC2 mm cw bcw pad pw -> dcap - j <= Z.of_nat k -> 0 <= j -> j + 2 <= dcap ->
    e9 mod 2^64 = (DST + j) mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    e15 mod 2^64 = (DST + dcap - 2) mod 2^64 -> e16 mod 2^64 = (-1 * DT + -5) mod 2^64 -> e17 mod 2^64 = (64 - tl) mod 2^64 ->
    evt usegs POST (ST 0x205e4 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                       (Z_to_bv 64 e13) x14 (Z_to_bv 64 e15) (Z_to_bv 64 e16) (Z_to_bv 64 e17) x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mm j cw bcw pad pw x1 x5 x6 x7 x14 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
      e9 e10 e11 e12 e13 e15 e16 e17 DI BD HK HJ0 HJ H9 H10 H11 H12 H13 H15 H16 H17; [exfalso; lia|].
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold x2_bdc in BD.
    rewrite (zbv_eqm e9 _ H9), (zbv_eqm e10 _ H10), (zbv_eqm e11 _ H11),
            (zbv_eqm e12 2305843009213693952 ltac:(rewrite H12; reflexivity)), (zbv_eqm e13 _ H13),
            (zbv_eqm e15 _ H15), (zbv_eqm e16 _ H16), (zbv_eqm e17 _ H17).
    clear H9 H10 H11 H12 H13 H15 H16 H17.
    remember (64 - tl) as sh eqn:HSH.
    assert (TBL : tbl_in_log usegs mm DT sh 4 7 1 2) by (rewrite HSH; apply x2_tbl; exact DTB).
    Time kx_autoLx [0x205e4; 0x2063c] 40%nat
      [KZRange (dcap - j) 2 (2^32); KZRange j 0 (2^32); KZRange dcap 2 (2^32); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47);
       KZRange (DST + j) 4096 (2^47); KZRange DT 4096 (2^47); KZRange sh 52 63; KZRange tl 1 12; KZRange rsv 0 255;
       KZWr DST dcap; KZWr (SPV + -112) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -112) 40;
       KZDisj (SPV + -112) 40 DT 16388; KZTblLog DT sh 4 7 1 2]
      [(DT, 16388); (SPV + -112, 40)].
    all: tp_close.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x205e4) _ _ _ _) =>
             eapply (IH _ (E - DST)); [dinv_close | unfold x2_bdc; eassumption | ..]
         | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?E) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x2063c) _ _ _ _) =>
             eapply (x2_last _ (E - DST)); [dinv_close | unfold x2_bdc; eassumption | ..]
         end.
    all: subst sh; first [reflexivity | lia | f_equal; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_tail : forall mm j cw bcw pad pw (x1 x5 x6 x7 x14 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word)
                    (e9 e10 e11 e12 e13 e15 e16 e17 : Z),
    DINV2 mm -> BDC2 mm cw bcw pad pw -> 0 <= j <= dcap ->
    e9 mod 2^64 = (DST + j) mod 2^64 -> e10 mod 2^64 = (DT + 4) mod 2^64 -> e11 mod 2^64 = (DST + dcap) mod 2^64 ->
    e12 mod 2^64 = 2^61 -> e13 mod 2^64 = (tl + 256 * rsv) mod 2^64 ->
    e15 mod 2^64 = (DST + dcap - 2) mod 2^64 -> e16 mod 2^64 = (-1 * DT + -5) mod 2^64 -> e17 mod 2^64 = (64 - tl) mod 2^64 ->
    evt usegs POST (ST 0x205e0 mm x1 x5 x6 x7 (Z_to_bv 64 e9) (Z_to_bv 64 e10) (Z_to_bv 64 e11) (Z_to_bv 64 e12)
                       (Z_to_bv 64 e13) x14 (Z_to_bv 64 e15) (Z_to_bv 64 e16) (Z_to_bv 64 e17) x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros mm j cw bcw pad pw x1 x5 x6 x7 x14 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 e9 e10 e11 e12 e13 e15 e16 e17
      DI BD HJ H9 H10 H11 H12 H13 H15 H16 H17.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    rewrite (zbv_eqm e9 _ H9), (zbv_eqm e15 _ H15).
    kx_autoLx [0x205e4; 0x2063c] 6%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
       KZRange (DST + dcap - 2) 4094 (2^47)] (@nil (Z * Z)).
    all: lazymatch goal with
         | |- context [Z_to_bv 64 0x205e4] => eapply (x2_tloop (Z.to_nat (dcap - j)) mm j); [exact DI | exact BD | ..]
         | |- _ => eapply (x2_last mm j); [exact DI | exact BD | ..]
         end.
    all: first [reflexivity | eassumption | lia].
  Qed.
End DX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x2_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb /\ huf_x2_ok dtb tl.

Ltac x2_ctx_open CTX :=
  let X2OK := fresh "X2OK" in let C1 := fresh "C1" in
  destruct CTX as (C1 & X2OK); x1_ctx_open C1.
