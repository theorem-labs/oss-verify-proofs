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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma neg_dl_sh : forall tl rsv, 1 <= tl <= 12 -> Z.land ((-1 * (tl + 256 * rsv)) mod 2^64) 63 = 64 - tl.
Proof.
  intros tl rsv H. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists (2^58); reflexivity].
  replace (-1 * (tl + 256 * rsv)) with ((64 - tl) + (-1 - 4 * rsv) * 2^6) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section DX1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis LO : 4096 <= lo /\ lo <= SPV - 48.
  Hypothesis SPB : SPV < 2^47.
  Hypothesis SL : zlen src = n.
  Hypothesis DL : zlen dtb = 16388.
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47.
  Hypothesis R2 : 4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47.
  Hypothesis R3 : 4096 <= DT /\ DT + 16388 < 2^47.
  Hypothesis OS1 : DST + dcap <= lo \/ SPV <= DST.
  Hypothesis OS2 : SRC + n <= lo \/ SPV <= SRC.
  Hypothesis OS3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis DJ1 : DST + dcap <= SRC \/ SRC + n <= DST.
  Hypothesis DJ2 : DST + dcap <= DT \/ DT + 16388 <= DST.
  Hypothesis DT2 : nth_error dtb 2 = Some (Z_to_bv 8 tl).
  Hypothesis DT3 : nth_error dtb 3 = Some (Z_to_bv 8 rsv).

  (* [comment removed for export] *)
  Lemma dl_read : extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
  Proof.
    assert (E : firstn 2 (skipn (Z.to_nat 2) dtb) = [Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 2) with 2%nat.
      destruct dtb as [|x0 [|x1 [|x2 [|x3 r]]]]; cbn in DT2, DT3; try discriminate.
      injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 48 [] m0 huf_noQ).

  (* [comment removed for export] *)
  Definition DINV (mm : fmem) : Prop :=
    stk psegs mm DST (DST + dcap) /\
    rw_cells psegs mm (SPV + -48) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] /\
    stk psegs mm lo (SPV + -48) /\
    bytes_at psegs mm SRC src /\ bytes_at psegs mm DT dtb /\
    munch [(DST, DST + dcap); (SPV - 48, SPV)] m0 mm /\ wmono psegs m0 mm /\ mem_inv psegs mm.

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold DINV; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Notation STpc pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x1_end : forall mm (x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm ->
    evt psegs POST (STpc 0x1e7a4 mm x5 x6 x7 x8 x9 x10 (Z_to_bv 64 dcap) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI.
    dinv_open DI.
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47); KZRange dcap 0 (2^32)] [(SPV - 48, 48)].
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [|split; [clear - R1; lia|exact I]]).
    all: first [left; reflexivity | right; vm_compute; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tail : forall (k : nat) mm j sh (x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> dcap - j <= Z.of_nat k -> 0 <= j < dcap -> 52 <= sh <= 63 ->
    evt psegs POST (STpc 0x1e774 mm x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 (Z_to_bv 64 sh) (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 (dcap - j)) x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mm j sh x5 x6 x7 x8 x9 x12 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HK HJ HSH;
      [exfalso; lia|].
    dinv_open DI.
    Time kx_autoLx [0x1e774; 0x1e7a4] 30%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32);
       KZRange SPV 4096 (2^47); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange sh 52 63;
       KZRange DT 4096 (2^47); KZWr DST dcap; KZDisj DST dcap DT 16388]
      [(DT, 16388)].
    Time all: kx_mem.
    - replace (DST + j + 1) with (DST + (j + 1)) by lia.
      replace (-1 * j + dcap + -1) with (dcap - (j + 1)) by lia.
      apply IH; [dinv_close | lia | lia | lia].
    - apply x1_end. dinv_close.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_69c : forall mm j dl (x5 x6 x7 x8 x9 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j < dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (STpc 0x1e768 mm x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 x13 (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm j dl x5 x6 x7 x8 x9 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ HDL.
    kx_autoLx [0x1e774] 30%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535] (@nil (Z * Z)).
    subst dl. rewrite (neg_dl_sh tl rsv TL). replace (-1 * j + dcap) with (dcap - j) by lia.
    eapply (x1_tail (Z.to_nat (dcap - j))); [exact DI | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_698 : forall mm j dl (x5 x6 x7 x8 x9 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (STpc 0x1e764 mm x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 x13 (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm j dl x5 x6 x7 x8 x9 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HJ HDL.
    kx_autoLx [0x1e768; 0x1e7a4] 30%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535] (@nil (Z * Z)).
    - apply x1_end. exact DI.
    - apply x1_69c; [exact DI | lia | exact HDL].
  Qed.

  (* [comment removed for export] *)
  Notation LOOPST mm bc x6 off x8 x9 j dl x17 x18 x19 x20 x21 :=
    (STpc 0x1e608 mm (Z_to_bv 64 bc) x6 (Z_to_bv 64 off) x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
          (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dl) (Z_to_bv 64 (DST + dcap)) x17 x18 x19 x20 x21
          (Z_to_bv 64 0x11320) (Z_to_bv 64 8) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 64)).
  Definition LINV (off bc : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= n /\ 0 <= bc <= 64).

  (* [comment removed for export] *)
  Lemma x1_loop_off0 : forall mm j dl bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> 0 <= j <= dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (LOOPST mm bc x6 0 x8 x9 j dl x17 x18 x19 x20 x21).
  Proof.
    intros mm j dl bc x6 x8 x9 x17 x18 x19 x20 x21 DI HJ HDL.
    kx_autoLx [0x1e608; 0x1e764; 0x1e768; 0x1e7a4] 100%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535] (@nil (Z * Z)).
    apply x1_698; [exact DI | lia | exact HDL].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_loop_small : forall mm j dl off bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> 0 <= j <= dcap -> dcap - j < 4 -> dl = tl + 256 * rsv -> LINV off bc ->
    evt psegs POST (LOOPST mm bc x6 off x8 x9 j dl x17 x18 x19 x20 x21).
  Proof.
    intros mm j dl off bc x6 x8 x9 x17 x18 x19 x20 x21 DI HJ SM HDL INV.
    destruct INV as [-> | (O1 & O2 & B1)]; [apply x1_loop_off0; assumption|].
    dinv_open DI.
    kx_autoLx [0x1e608; 0x1e764; 0x1e768; 0x1e7a4] 100%nat
      [KZRange (dcap - j) 0 3; KZRange (n - off) 8 (2^32); KZRange off 1 (2^32); KZRange bc 0 64; KZRange n 9 (2^32);
       KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535;
       KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (SRC + n) 4096 (2^47);
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n]
      [(DT, 16388); (SRC, n)].
    all: apply x1_698; [dinv_close | lia | exact HDL].
  Qed.

  Lemma x1_loop : forall (k : nat) mm j dl off bc (x6 x8 x9 x17 x18 x19 x20 x21 : word),
    DINV mm -> dcap - j <= Z.of_nat k -> 0 <= j <= dcap -> dl = tl + 256 * rsv -> LINV off bc ->
    evt psegs POST (LOOPST mm bc x6 off x8 x9 j dl x17 x18 x19 x20 x21).
  Proof.
    induction k as [|k IH]; intros mm j dl off bc x6 x8 x9 x17 x18 x19 x20 x21 DI HK HJ HDL INV.
    { apply x1_loop_small; [exact DI | lia | lia | exact HDL | exact INV]. }
    destruct (Z_lt_le_dec (dcap - j) 4) as [SM|BG]; [apply x1_loop_small; [exact DI | lia | lia | exact HDL | exact INV]|].
    destruct INV as [-> | (O1 & O2 & B1)]; [apply x1_loop_off0; assumption|].
    dinv_open DI.
    Time kx_autoLx [0x1e608; 0x1e764; 0x1e768; 0x1e7a4] 100%nat
      [KZRange (dcap - j) 4 (2^32); KZRange (n - off) 8 (2^32); KZRange off 1 (2^32); KZRange bc 0 64; KZRange n 9 (2^32);
       KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange dl 0 65535; KZRange SPV 4096 (2^47);
       KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (SRC + n) 4096 (2^47);
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap SRC n; KZDisj DST dcap (SPV - 48) 48]
      [(DT, 16388); (SRC, n)].
    all: kx_read_ranges; kx_opaque_ranges; kx_mem; kx_srlw.
    all: rewrite ?(Z.mod_small bc (2^64)) in * by lia.
    all: kx_land_ranges; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124836) _ _ _ _) => apply x1_end; dinv_close
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124772) _ _ _ _) => apply x1_698; [dinv_close | lia | exact HDL]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124776) _ _ _ _) =>
             replace (DST + j + 4) with (DST + (j + 4)) by lia; apply x1_69c; [dinv_close | lia | exact HDL]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124424) _ _ _ _) =>
             replace (DST + j + 4) with (DST + (j + 4)) by lia;
             eapply IH; [dinv_close | lia | lia | exact HDL | unfold LINV; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_err : forall mm r (x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> zd_is_error r = true /\ r < 2^64 ->
    evt psegs POST (STpc 0x1e7bc mm x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 r) x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm r x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HR.
    dinv_open DI.
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47)] [(SPV - 48, 48)].
    kx_mem. zstep. release_frame FR STK SPV.
    apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
    (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
      (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - right. exact (proj1 HR).
    - destruct HR as [HR1 HR2]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_698p : forall mm p pe dl (x5 x6 x7 x8 x9 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word),
    DINV mm -> DST <= p <= DST + dcap -> pe = DST + dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (STpc 0x1e764 mm x5 x6 x7 x8 x9 (Z_to_bv 64 p) (Z_to_bv 64 dcap) x12 x13 (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 dl) (Z_to_bv 64 pe) x17 x18 x19 x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm p pe dl x5 x6 x7 x8 x9 x12 x13 x17 x18 x19 x20 x21 x28 x29 x30 x31 DI HP PE HDL.
    subst pe. replace p with (DST + (p - DST)) by lia. apply x1_698; [exact DI | lia | exact HDL].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_init8 : forall mm bc pend dl (x8 x9 x17 x18 x19 x20 x21 x28 x30 x31 : word),
    DINV mm -> 1 <= bc <= 8 -> 8 <= n -> pend = DST + dcap -> dl = tl + 256 * rsv ->
    evt psegs POST (STpc 0x1e458 mm (Z_to_bv 64 bc) (Z_to_bv 64 (SRC + n + -8)) (Z_to_bv 64 (n + -8)) x8 x9
                         (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 (DT + 4))
                         (Z_to_bv 64 dl) (Z_to_bv 64 pend) x17 x18 x19 x20 x21 x28 (Z_to_bv 64 3) x30 x31).
  Proof.
    intros mm bc pend dl x8 x9 x17 x18 x19 x20 x21 x28 x30 x31 DI HB HN PE HDL.
    dinv_open DI.
    kx_autoLx [0x1e608; 0x1e764; 0x1e768; 0x1e7a4] 200%nat
      [KZRange bc 1 8; KZRange n 8 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange pend 4096 (2^47);
       KZRange dl 0 65535; KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47); KZRange (SRC + n) 4096 (2^47)]
      [(DT, 16388); (SRC, n)].
    all: subst pend dl; rewrite ?(neg_dl_sh tl rsv TL).
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124836) _ _ _ _) => apply x1_end; dinv_close
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124772) _ _ _ _) => apply x1_698; [dinv_close | lia | reflexivity]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124776) _ _ _ _) => apply x1_69c; [dinv_close | lia | reflexivity]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 124424) _ _ _ _) =>
             replace (DST + dcap + -3) with (DST + dcap - 3) by lia;
             eapply (x1_loop (Z.to_nat dcap)); [dinv_close | lia | lia | reflexivity | unfold LINV; lia]
         end.
  Qed.

End DX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x1_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 48) /\ SPV < 2^47 /\ zlen src = n /\ zlen dtb = 16388 /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + 16388 < 2^47) /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + 16388 <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + 16388 <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ nth_error dtb 3 = Some (Z_to_bv 8 rsv).

Ltac x1_ctx_open CTX :=
  destruct CTX as (LO & SPB & SL & DL & TL & RSV & R1 & R2 & R3 & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DT3).

Section DX1C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.

  Definition x1_err_c := ltac:(x1_ctx_open CTX;
    exact (x1_err ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT lo src dtb
                  LO SPB SL R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2)).
  Definition x1_698p_c := ltac:(x1_ctx_open CTX;
    exact (x1_698p ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
                   LO SPB SL DL TL RSV R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2)).
  Definition x1_loop_off0_c := ltac:(x1_ctx_open CTX;
    exact (x1_loop_off0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
                        LO SPB SL DL TL RSV R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2)).
  Definition x1_init8_c := ltac:(x1_ctx_open CTX;
    exact (x1_init8 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb
                    LO SPB SL DL TL RSV R1 R2 R3 OS1 OS2 OS3 DJ1 DJ2)).
  Lemma dl_read_c : extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
  Proof. x1_ctx_open CTX. eapply dl_read; eassumption. Qed.
End DX1C.
