(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
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

Lemma zbv_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv64_mod a), <- (Z_to_bv64_mod b), H. reflexivity. Qed.

Lemma bvu_mod : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2^64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x1_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 144) /\ SPV < 2^47 /\ SPV mod 16 = 0 /\ zlen src = n /\ zlen dtb = 16388 /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + 16388 < 2^47) /\ DT mod 4 = 0 /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + 16388 <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + 16388 <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ nth_error dtb 3 = Some (Z_to_bv 8 rsv).

Ltac x1_ctx_open CTX :=
  destruct CTX as (LO & SPB & SPA & SL & DL & TL & RSV & R1 & R2 & R3 & DTA & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DT3).

Section DX1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.

  (* [comment removed for export] *)
  Lemma dl_read : extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
  Proof.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    assert (E : firstn 2 (skipn (Z.to_nat 2) dtb) = [Z_to_bv 8 tl; Z_to_bv 8 rsv]).
    { change (Z.to_nat 2) with 2%nat.
      destruct dtb as [|x0 [|x1 [|x2 [|x3 r]]]]; cbn in DT2, DT3; try discriminate.
      injection DT2 as ->. injection DT3 as ->. reflexivity. }
    rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
  Qed.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 144 [] m0 huf_noQ).

  (* [comment removed for export] *)
  Definition DINV (mm : fmem) : Prop :=
    stk usegs mm DST (DST + dcap) /\
    rw_cells usegs mm (SPV + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk usegs mm lo (SPV + -136) /\
    bytes_at usegs mm SRC src /\ bytes_at usegs mm DT dtb /\
    munch [(DST, DST + dcap); (SPV - 144, SPV)] m0 mm /\ wmono usegs m0 mm /\ mem_inv usegs mm.

  Definition BDC (mm : fmem) (cw bcw : word) (pad : list byte) (pw : word) : Prop :=
    rw_cells usegs mm (SPV + -136) [C8 cw; C4 bcw; CB 4 pad; C8 pw; C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (SRC + 8))].

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold DINV; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * rsv)) x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma x1_err : forall mm w cs (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINV mm -> rw_cells usegs mm (SPV + -136) cs -> cells_size cs = 40%nat ->
    (bv_unsigned w = dcap \/ zd_is_error (bv_unsigned w) = true) ->
    evt usegs POST (ST 0x20d1c mm x1 x5 x6 x7 x8 x9 w x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros mm w cs x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD SZ HR.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    dinv_open DI.
    pose proof (stk_of_rw_cells usegs mm _ _ BD) as HB. rewrite SZ in HB. change (Z.of_nat 40) with 40 in HB.
    replace (SPV + -136 + 40) with (SPV + -96) in HB by lia.
    assert (STK2 : stk usegs mm lo (SPV + -96)) by (eapply stk_merge; [exact STK | exact HB | lia]).
    clear STK HB BD. rename STK2 into STK.
    pose proof (bv_unsigned_in_range 64 w) as RW. unfold bv_modulus in RW. change (2 ^ Z.of_N 64) with (2^64) in RW.
    kx_autoLx [] 30%nat [KZRange SPV 4096 (2^47)] [(SPV + -96, 96)].
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evt_done; unfold huf_dec_post; rewrite <- (Z_to_bv_bv_unsigned w);
         repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [exact HR|]); (split; [exact RW | exact I]).
  Qed.

  (* [comment removed for export] *)
  Lemma x1_end : forall mm cw bcw pad pw (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw ->
    evt usegs POST (ST 0x20cfc mm x1 x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros mm cw bcw pad pw x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD.
    kx_autoLx [0x20d1c] 20%nat [KZRange SPV 4096 (2^47); KZRange SRC 4096 (2^47); KZRange dcap 0 (2^32)] [(SPV + -136, 40)].
    all: kx_mem.
    all: eapply x1_err; [exact DI | exact BD | reflexivity | ].
    all: first [ left; rewrite bvu_mod; apply Z.mod_small; lia | right; vm_compute; reflexivity ].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tail : forall (k : nat) mm j p q cnt sh nd c62 c2 cw bcw pad pw
                    (x1 x5 x6 x7 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw -> dcap - j <= Z.of_nat k -> 0 <= j < dcap ->
    p mod 2^64 = (DST + j) mod 2^64 -> q mod 2^64 = (DST + j) mod 2^64 -> cnt mod 2^64 = (dcap - j) mod 2^64 ->
    sh mod 2^64 = (64 - tl) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    c62 mod 2^64 = 4611686018427387904 -> c2 mod 2^64 = 2 ->
    evt usegs POST (ST 0x20ca4 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 p) (Z_to_bv 64 nd) (Z_to_bv 64 cnt) (Z_to_bv 64 c62)
                      (Z_to_bv 64 sh) (Z_to_bv 64 c2) (Z_to_bv 64 q) x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mm j p q cnt sh nd c62 c2 cw bcw pad pw x1 x5 x6 x7 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      DI BD HK HJ HP HQ HC HSH HND H62 H2; [exfalso; lia|].
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD.
    rewrite (zbv_eqm p _ HP), (zbv_eqm q _ HQ), (zbv_eqm cnt _ HC), (zbv_eqm sh _ HSH), (zbv_eqm nd _ HND),
            (zbv_eqm c62 4611686018427387904 ltac:(rewrite H62; reflexivity)), (zbv_eqm c2 2 ltac:(rewrite H2; reflexivity)).
    Time kx_autoLx [0x20ca4; 0x20cfc] 40%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange SPV 4096 (2^47); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47);
       KZRange (DST + j) 4096 (2^47); KZRange tl 1 12; KZRange DT 4096 (2^47); KZWr DST dcap; KZWr (SPV + -136) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -136) 40; KZDisj (SPV + -136) 40 DT 16388]
      [(DT, 16388); (SPV + -136, 40)].
    all: lazymatch goal with |- context [Z_to_bv 64 0x20d74] => kx_trap_fast | _ => idtac end.
    Time all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20cfc) _ _ _ _) => eapply x1_end; [dinv_close | unfold BDC; eassumption]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20ca4) _ _ _ _) =>
             eapply (IH _ (j + 1)); [dinv_close | unfold BDC; eassumption | lia | lia | lia | lia | lia | lia | lia | lia | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tset : forall mm j p q cw bcw pad pw
                    (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 0 <= j <= dcap ->
    p mod 2^64 = (DST + j) mod 2^64 -> q mod 2^64 = (DST + j) mod 2^64 ->
    evt usegs POST (ST 0x20c80 mm x1 x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 p) x10 x11 (Z_to_bv 64 q) x13 x14 x15 x16 x17
                      x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros mm j p q cw bcw pad pw x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 DI BD HJ HP HQ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    rewrite (zbv_eqm p _ HP), (zbv_eqm q _ HQ).
    kx_autoLx [0x20ca4; 0x20cfc] 20%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47); KZRange DT 4096 (2^47);
       KZRange tl 1 12; KZRange rsv 0 255] (@nil (Z * Z)).
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20cfc) _ _ _ _) => eapply x1_end; [exact DI | exact BD]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20ca4) _ _ _ _) =>
             eapply (x1_tail (Z.to_nat (dcap - j)) mm j); [exact DI | exact BD | lia | lia | lia | lia | lia | | lia | lia | lia];
             rewrite ?(neg_dl_sh tl rsv TL); lia
         end.
  Qed.

  (* [comment removed for export] *)
  Ltac trap_close := lazymatch goal with |- context [Z_to_bv 64 0x20d74] => kx_trap_fast | _ => idtac end.

  (* [comment removed for export] *)
  Notation LST pc mm x1 x9 x10 x11 p p3 x21 x22 x23 x24 x25 x26 :=
    (ST pc mm x1 (Z_to_bv 64 65) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 dcap) x9 x10 x11
        (Z_to_bv 64 p) (Z_to_bv 64 SRC) (Z_to_bv 64 (SRC + 8)) (Z_to_bv 64 (dcap + DST + -3)) (Z_to_bv 64 (-1 * DT + -5))
        (Z_to_bv 64 p3) x21 x22 x23 x24 x25 x26
        (Z_to_bv 64 70160) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 18446744073709551615)).

  (* [comment removed for export] *)
  Definition LINV (P bc : Z) : Prop := 0 <= bc <= 64 /\ (P = SRC \/ (SRC + 1 <= P /\ P + 8 <= SRC + n)).

  (* [comment removed for export] *)
  Lemma x1_body : forall mm j bc bcr P Pr fl flr cw pad (x1 x9 x22 x24 x25 x26 : word),
    DINV mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 0 <= j <= dcap -> (fl = 0 \/ fl = 1) -> 0 <= bc <= 64 ->
    bcr mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> flr mod 2^64 = fl mod 2^64 ->
    (j + 4 <= dcap -> forall mm' bcn bcr' bcs' p' p3' Pr' (y9 y23 y24 y25 y26 : word),
        DINV mm' -> BDC mm' cw (Z_to_bv 64 bcn) pad (Z_to_bv 64 P) -> 0 <= bcn <= 64 ->
        p' mod 2^64 = (DST + (j + 4)) mod 2^64 -> p3' mod 2^64 = (DST + (j + 4) + 3) mod 2^64 ->
        bcr' mod 2^64 = bcn mod 2^64 -> bcs' mod 2^64 = bcn mod 2^64 -> Pr' mod 2^64 = P mod 2^64 ->
        evt usegs POST (LST 0x208f8 mm' x1 y9 (Z_to_bv 64 bcr') (Z_to_bv 64 bcs') p' p3' cw (Z_to_bv 64 Pr') y23 y24 y25 y26)) ->
    evt usegs POST (LST 0x20a6c mm x1 x9 (Z_to_bv 64 bcr) (Z_to_bv 64 Pr) (DST + j) (DST + j + 3) cw x22 (Z_to_bv 64 flr) x24 x25 x26).
  Proof.
    intros mm j bc bcr P Pr fl flr cw pad x1 x9 x22 x24 x25 x26 DI BD HJ HFL HBC HBR HPR HFR KH.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD.
    rewrite (zbv_eqm bcr _ HBR), (zbv_eqm Pr _ HPR), (zbv_eqm flr _ HFR).
    destruct (Z_lt_le_dec (dcap - j) 4) as [SM|BG].
    - clear KH.
      destruct HFL as [-> | ->].
      all: kx_autoLx [0x20c80] 20%nat
             [KZRange (dcap - j) 0 3; KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47);
              KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
      all: trap_close.
      all: kx_mem.
      all: eapply (x1_tset _ j); [dinv_close | unfold BDC; eassumption | | |]; lia.
    - destruct HFL as [-> | ->].
      + clear KH.
        kx_autoLx [0x20c80] 20%nat
          [KZRange (dcap - j) 4 (2^32); KZRange j 0 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47);
           KZRange (DST + dcap) 4096 (2^47)] (@nil (Z * Z)).
        all: trap_close.
        all: kx_mem.
        all: eapply (x1_tset _ j); [dinv_close | unfold BDC; eassumption | | |]; lia.
      + Time kx_autoLx [0x20c80; 0x208f8] 160%nat
          [KZRange (dcap - j) 4 (2^32); KZRange j 0 (2^32); KZRange (DST + j) 4096 (2^47 - 4); KZRange dcap 4 (2^32);
           KZRange DST 4096 (2^47); KZRange (DST + dcap) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange tl 1 12; KZRange bc 0 64;
           KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
           KZWr DST dcap; KZWr (SPV + -136) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -136) 40; KZDisj (SPV + -136) 40 DT 16388;
           KZDisj DST dcap SRC n; KZDisj (SPV + -136) 40 SRC n]
          [(DT, 16388); (SPV + -136, 40)].
        all: trap_close.
        Time all: kx_mem.
        all: kx_read_ranges.
        all: lazymatch goal with
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x208f8) _ _ _ _) =>
                 eapply KH; [lia | dinv_close | unfold BDC; eassumption | lia | lia | lia | lia | lia | lia]
             | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20c80) _ _ _ _) =>
                 eapply (x1_tset _ (j + 4)); [dinv_close | unfold BDC; eassumption | | |]; lia
             end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_reload : forall mm j p p3 P Pr bc bcr bcs cw pad (x1 x9 x23 x24 x25 x26 : word),
    DINV mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap ->
    p mod 2^64 = (DST + j) mod 2^64 -> p3 mod 2^64 = (DST + j + 3) mod 2^64 ->
    bcr mod 2^64 = bc mod 2^64 -> bcs mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> LINV P bc ->
    (forall mm' fl flr bc' bcr' P' Pr' cw' pad' (y9 y22 y24 y25 y26 : word),
        DINV mm' -> BDC mm' cw' (Z_to_bv 64 bc') pad' (Z_to_bv 64 P') -> (fl = 0 \/ fl = 1) -> flr mod 2^64 = fl mod 2^64 ->
        bcr' mod 2^64 = bc' mod 2^64 -> Pr' mod 2^64 = P' mod 2^64 -> LINV P' bc' ->
        evt usegs POST (LST 0x20a6c mm' x1 y9 (Z_to_bv 64 bcr') (Z_to_bv 64 Pr') (DST + j) (DST + j + 3) cw' y22 (Z_to_bv 64 flr) y24 y25 y26)) ->
    evt usegs POST (LST 0x208f8 mm x1 x9 (Z_to_bv 64 bcr) (Z_to_bv 64 bcs) p p3 cw (Z_to_bv 64 Pr) x23 x24 x25 x26).
  Proof.
    intros mm j p p3 P Pr bc bcr bcs cw pad x1 x9 x23 x24 x25 x26 DI BD HN HJ HP HP3 HBR HBS HPR INV KB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. clear SPA DTA.
    pose proof DI as DI'. dinv_open DI'. unfold BDC in BD.
    rewrite (zbv_eqm p _ HP), (zbv_eqm p3 _ HP3), (zbv_eqm bcr _ HBR), (zbv_eqm bcs _ HBS), (zbv_eqm Pr _ HPR).
    destruct INV as (HBC & INV).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & HQ & HR).
    destruct INV as [-> | (O1 & O2)].
    - Time kx_autoLx [0x20a6c] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
        [(SRC, n); (SPV + -136, 40)].
      all: trap_close.
      all: kx_mem.
      all: first [ eapply (KB _ 0); [dinv_close | unfold BDC; eassumption | | | | | unfold LINV]; lia
                 | eapply (KB _ 1); [dinv_close | unfold BDC; eassumption | | | | | unfold LINV]; lia ].
    - assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia). destruct O as (off & ->).
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      3: kx_autoLx [0x20a6c] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
        [(SRC, n); (SPV + -136, 40)].
      2: kx_autoLx [0x20a6c] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
        [(SRC, n); (SPV + -136, 40)].
      1: kx_autoLx [0x20a6c] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
         KZRange n 9 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
         KZRange DT 4096 (2^47); KZWr (SPV + -136) 40; KZDisj (SPV + -136) 40 SRC n; KZDisj (SPV + -136) 40 DT 16388]
        [(SRC, n); (SPV + -136, 40)].
      all: trap_close.
      all: kx_mem.
      all: kx_read_ranges.
      all: first [ eapply (KB _ 0); [dinv_close | unfold BDC; eassumption | | | | | unfold LINV]; lia
                 | eapply (KB _ 1); [dinv_close | unfold BDC; eassumption | | | | | unfold LINV]; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_loop : forall (k : nat) mm j p p3 P Pr bc bcr bcs cw pad (x1 x9 x23 x24 x25 x26 : word),
    DINV mm -> BDC mm cw (Z_to_bv 64 bc) pad (Z_to_bv 64 P) -> 1 <= n -> 0 <= j <= dcap -> dcap - j <= Z.of_nat k ->
    p mod 2^64 = (DST + j) mod 2^64 -> p3 mod 2^64 = (DST + j + 3) mod 2^64 ->
    bcr mod 2^64 = bc mod 2^64 -> bcs mod 2^64 = bc mod 2^64 -> Pr mod 2^64 = P mod 2^64 -> LINV P bc ->
    evt usegs POST (LST 0x208f8 mm x1 x9 (Z_to_bv 64 bcr) (Z_to_bv 64 bcs) p p3 cw (Z_to_bv 64 Pr) x23 x24 x25 x26).
  Proof.
    induction k as [|k IH]; intros mm j p p3 P Pr bc bcr bcs cw pad x1 x9 x23 x24 x25 x26 DI BD HN HJ HK HP HP3 HBR HBS HPR INV.
    all: eapply x1_reload; [exact DI | exact BD | exact HN | exact HJ | exact HP | exact HP3 | exact HBR | exact HBS | exact HPR | exact INV |].
    all: intros mm' fl flr bc' bcr' P' Pr' cw' pad' y9 y22 y24 y25 y26 DI' BD' HFL HFR HBR' HPR' INV'.
    all: pose proof INV' as INV2; destruct INV2 as (HBC' & _).
    all: eapply x1_body; [exact DI' | exact BD' | exact HJ | exact HFL | exact HBC' | exact HBR' | exact HPR' | exact HFR |].
    - intros HR. exfalso. lia.
    - intros HR mm'' bcn bcr'' bcs'' p' p3' Pr'' z9 z23 z24 z25 z26 DI'' BD'' HBCN HP' HP3' HBR'' HBS'' HPR''.
      eapply (IH _ (j + 4)); [exact DI'' | exact BD'' | exact HN | lia | lia | exact HP' | exact HP3' | exact HBR'' | exact HBS'' | exact HPR'' |].
      destruct INV' as (_ & HP2). split; [exact HBCN | exact HP2].
  Qed.

End DX1.
