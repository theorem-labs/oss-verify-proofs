(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit AZ_huf_dx1.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.
Section DX1L.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x1_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2352 [] m0 huf_noQ).
  Notation W0 := [(DST, DST + dcap); (SPV - 2352, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation DINV := (AZ_huf_dx1.DINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 SPV DST dcap SRC DT lo src dtb).
  Notation BDC := (AZ_huf_dx1.BDC SPV SRC).
  Notation x1_end := (AZ_huf_dx1.x1_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_4d8 := (AZ_huf_dx1.x1_4d8 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold AZ_huf_dx1.DINV; repeat (split; [eassumption|]); eassumption.
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333497648 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333495296 <= SPV - 2352) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  Ltac afacts MU0 UDT RDTS RSTK DSTA R3 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (eapply unp_carryS; [exact UDT | exact MU0 | clear - R3; lia | clear - R3; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 128) 128) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  Ltac dfacts MU0 UDST RDST RDSTS DSTA R1 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let D := fresh "DPOS" in
    assert (D : 0 < dcap) by lia;
    assert (UDSTc : unpoisoned mm DST (DST + dcap))
      by (eapply unp_carryS; [exact (UDST D) | exact MU0 | clear - R1; lia | clear - R1; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (RDST D) as RDSTc; pose proof (RDSTS D) as RDSTSc;
    assert (DSTAc : DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST) by (clear - D DSTA; lia);
    pose proof (rng_shspanZ _ _ _ RDSTSc) as RDSTz;
    pose proof (unpoisoned_unpZ _ _ _ DST (DST + dcap) UDSTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R1; lia)) as UDSTz;
    clear D.
  Ltac sfacts MU0 USRC RSRC RSRCS DSTA R1 R2 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (eapply unp_carryS; [exact (USRC N) | exact MU0 | clear - R2; lia | clear - R2; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (RSRC N) as RSRCc; pose proof (RSRCS N) as RSRCSc;
    pose proof (rng_shspanZ _ _ _ RSRCSc) as RSRCz;
    pose proof (unpoisoned_unpZ _ _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2 N; lia)) as USRCz;
    clear N.
  Ltac ffacts OS1 OS2 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 128 \/ SPV - 128 + 128 <= DST) /\ (SPV - 128 + 40 <= DT \/ DT + 16388 <= SPV - 128) /\
                 (SPV - 128 + 40 <= SRC \/ SRC + n <= SPV - 128) /\ (SPV - 128 + 128 <= DT \/ DT + 16388 <= SPV - 128))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4).
  Ltac kclean :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : DT mod 4 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < _ -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < _ -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac trap_close := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c4dc) _ _ _ _) => kx_trap_fast | _ => idtac end.

  Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 (Z_to_bv 64 dcap) x9 x10 x11 x12 x13 x14 x15 x16 x17
             SB (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (tl + 256 * rsv)) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation LST pc mm x1 sh x10 x11 x12 x13 x14 j pm3 nd x22 x23 x24 x25 :=
    (ST pc mm x1 (Z_to_bv 64 65) (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 sh) (Z_to_bv 64 DST) x10 x11 x12 x13 x14 (Z_to_bv 64 j)
        (Z_to_bv 64 pm3) (Z_to_bv 64 nd) x22 x23 x24 x25
        (Z_to_bv 64 140352) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 18446744073709551615)).

  (* [comment removed for export] *)
  Lemma x1_body : forall mm j sh pm3 nd fl bc cw bcw pad pw (x1 xp x11 x14 x22 x23 x24 x25 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 0 <= j <= dcap -> 52 <= sh <= 63 -> pm3 = DST + dcap - 3 -> nd = -1 * DT + -5 ->
    (fl = 0 \/ fl = 1) -> 0 <= bc <= 64 ->
    (j + 4 <= dcap -> forall mm' bcn cw' bcw' pad' pw' (x10 x12 x14' x23' x24' x25' : word),
        DINV mm' -> BDC mm' cw' bcw' pad' pw' -> 0 <= bcn <= 64 ->
        evtF bsegs RNG POST (LST 0x9bdc8 mm' x1 sh x10 xp x12 (Z_to_bv 64 bcn) x14' (j + 4) pm3 nd x22 x23' x24' x25')) ->
    evtF bsegs RNG POST (LST 0x9bf8c mm x1 sh xp x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc) x14 j pm3 nd x22 x23 x24 x25).
  Proof.
    intros mm j sh pm3 nd fl bc cw bcw pad pw x1 xp x11 x14 x22 x23 x24 x25 DI BD HJ HSH HPM3 HND HFL HBC KH.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. unfold AZ_huf_dx1.BDC in BD. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. ffacts OS1 OS2 OS3 LO.
    subst pm3 nd.
    destruct (Z_lt_le_dec (dcap - j) 4) as [SM|BG].
    - (* [comment removed for export] *)
      clear KH. kclean.
      destruct HFL as [-> | ->].
      all: kx_autoFLAx (@nil kza) [0x9c2e8; 0x9bdc8] 20%nat
             [KZRange (dcap - j) 0 3; KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
      all: aside.
      all: eapply x1_4d8; [exact DI | unfold AZ_huf_dx1.BDC; exact BD | lia].
    - destruct HFL as [-> | ->].
      + (* [comment removed for export] *)
        clear KH. kclean.
        kx_autoFLAx (@nil kza) [0x9c2e8; 0x9bdc8] 20%nat
          [KZRange (dcap - j) 4 (2^32); KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
        all: aside.
        all: eapply x1_4d8; [exact DI | unfold AZ_huf_dx1.BDC; exact BD | lia].
      + (* [comment removed for export] *)
        dfacts MU UDST RDST RDSTS DSTA R1 LO KLO. kclean.
        Time kx_autoFLAx [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 128) 128] [0x9c2e8; 0x9bdc8] 160%nat
          [KZRange (dcap - j) 4 (2^32); KZRange j 0 (2^32); KZRange (DST + j) 4096 (2^47 - 4); KZRange dcap 4 (2^32);
           KZRange DST 4096 (2^47); KZRange SPV 17594333497648 (2^47); KZRange sh 52 63; KZRange bc 0 64;
           KZRange DT 4096 (2^47 - 16388); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
           KZWr DST dcap; KZWr (SPV - 128) 40; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 128) 128; KZDisj (SPV - 128) 40 DT 16388;
           KZDisj DST dcap SRC n; KZDisj (SPV - 128) 40 SRC n]
          [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 128, 128)].
        all: aside.
        all: trap_close.
        Time all: kx_mem.
        all: kx_read_ranges; kx_abs.
        all: lazymatch goal with
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9bdc8) _ _ _ _) =>
                 lazymatch goal with BR : (?x mod 2 ^ 64 < 65) |- _ => rewrite (Z.mod_small x (2^64)) in BR by lia end;
                 eapply KH; [lia | dinv_close | unfold AZ_huf_dx1.BDC; eassumption | lia]
             | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c2e8) _ _ _ _) =>
                 replace (DST + j + 4) with (DST + (j + 4)) by lia; eapply x1_4d8; [dinv_close | unfold AZ_huf_dx1.BDC; eassumption | lia]
             end.
  Qed.
  (* [comment removed for export] *)
  Definition LINV (P bc : Z) : Prop := 0 <= bc <= 64 /\ (P = SRC \/ (SRC + 1 <= P /\ P + 8 <= SRC + n)).

  (* [comment removed for export] *)
  Lemma x1_reload : forall mm j sh pm3 nd P bc cw bcw pad pw (x1 x10 x12 x14 x22 x23 x24 x25 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 1 <= n -> 0 <= j <= dcap -> 52 <= sh <= 63 -> pm3 = DST + dcap - 3 -> nd = -1 * DT + -5 ->
    LINV P bc ->
    (forall mm' fl bc' P' cw' bcw' pad' pw' (x11 x14' x22' x23' x24' x25' : word),
        DINV mm' -> BDC mm' cw' bcw' pad' pw' -> (fl = 0 \/ fl = 1) -> LINV P' bc' ->
        evtF bsegs RNG POST (LST 0x9bf8c mm' x1 sh (Z_to_bv 64 P') x11 (Z_to_bv 64 fl) (Z_to_bv 64 bc') x14' j pm3 nd x22' x23' x24' x25')) ->
    evtF bsegs RNG POST (LST 0x9bdc8 mm x1 sh x10 (Z_to_bv 64 P) x12 (Z_to_bv 64 bc) x14 j pm3 nd x22 x23 x24 x25).
  Proof.
    intros mm j sh pm3 nd P bc cw bcw pad pw x1 x10 x12 x14 x22 x23 x24 x25 DI BD HN HJ HSH HPM3 HND INV KB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. unfold AZ_huf_dx1.BDC in BD. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO. ffacts OS1 OS2 OS3 LO.
    subst pm3 nd. destruct INV as (HBC & INV).
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
    destruct QR as (q & r & -> & HQ & HR).
    destruct INV as [-> | (O1 & O2)].
    - (* [comment removed for export] *)
      kclean.
      Time kx_autoFLAx [KAApp (SPV - 128) 128] [0x9bf8c] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
         KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 16388);
         KZWr (SPV - 128) 40; KZDisj (SPV - 128) 40 SRC n; KZDisj (SPV - 128) 40 DT 16388; KZDisj DST dcap (SPV - 128) 128]
        [(SRC, n); (SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      all: aside.
      all: kx_mem.
      all: eapply KB; [dinv_close | unfold AZ_huf_dx1.BDC; eassumption | left; reflexivity | unfold LINV; lia].
    - assert (O : exists off, P = SRC + off) by (exists (P - SRC); lia). destruct O as (off & ->).
      kclean.
      (* [comment removed for export] *)
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      (* [comment removed for export] *)
      3: kx_autoFLAx [KAUnp SRC n; KAApp (SPV - 128) 128] [0x9bf8c] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 8 (2^32); KZRange (off - q) 0 (2^32); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 9 (2^32);
         KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 16388);
         KZWr (SPV - 128) 40; KZDisj (SPV - 128) 40 SRC n; KZDisj (SPV - 128) 40 DT 16388; KZDisj DST dcap (SPV - 128) 128]
        [(SRC, n); (SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      2: kx_autoFLAx [KAUnp SRC n; KAApp (SPV - 128) 128] [0x9bf8c] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 9 (2^32);
         KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 16388);
         KZWr (SPV - 128) 40; KZDisj (SPV - 128) 40 SRC n; KZDisj (SPV - 128) 40 DT 16388; KZDisj DST dcap (SPV - 128) 128]
        [(SRC, n); (SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      1: kx_autoFLAx [KAUnp SRC n; KAApp (SPV - 128) 128] [0x9bf8c] 120%nat
        [KZRange (n - off) 8 (2^32); KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 9 (2^32);
         KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + off) 4097 (2^47 - 8);
         KZRange SPV 17594333497648 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange j 0 (2^32); KZRange DT 4096 (2^47 - 16388);
         KZWr (SPV - 128) 40; KZDisj (SPV - 128) 40 SRC n; KZDisj (SPV - 128) 40 DT 16388; KZDisj DST dcap (SPV - 128) 128]
        [(SRC, n); (SPV - 128, 40)] [(SRC, n); (SPV - 128, 128)].
      all: aside.
      all: trap_close.
      all: kx_mem.
      all: kx_abs.
      all: eapply KB; [dinv_close | unfold AZ_huf_dx1.BDC; eassumption | first [left; reflexivity | right; reflexivity] | unfold LINV; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_loop : forall (k : nat) mm j sh pm3 nd P bc cw bcw pad pw (x1 x10 x12 x14 x22 x23 x24 x25 : word),
    DINV mm -> BDC mm cw bcw pad pw -> 1 <= n -> 0 <= j <= dcap -> dcap - j <= Z.of_nat k -> 52 <= sh <= 63 ->
    pm3 = DST + dcap - 3 -> nd = -1 * DT + -5 -> LINV P bc ->
    evtF bsegs RNG POST (LST 0x9bdc8 mm x1 sh x10 (Z_to_bv 64 P) x12 (Z_to_bv 64 bc) x14 j pm3 nd x22 x23 x24 x25).
  Proof.
    induction k as [|k IH]; intros mm j sh pm3 nd P bc cw bcw pad pw x1 x10 x12 x14 x22 x23 x24 x25 DI BD HN HJ HK HSH HPM3 HND INV.
    all: eapply x1_reload; [exact DI | exact BD | exact HN | exact HJ | exact HSH | exact HPM3 | exact HND | exact INV |].
    all: intros mm' fl bc' P' cw' bcw' pad' pw' x11 x14' x22' x23' x24' x25' DI' BD' HFL INV'.
    all: pose proof INV' as INV2; destruct INV2 as (HBC' & _).
    all: eapply x1_body; [exact DI' | exact BD' | exact HJ | exact HSH | exact HPM3 | exact HND | exact HFL | exact HBC' |].
    - intros HR. exfalso. lia.
    - intros HR mm'' bcn cw'' bcw'' pad'' pw'' y10 y12 y14 y23 y24 y25 DI'' BD'' HBCN.
      eapply IH; [exact DI'' | exact BD'' | exact HN | lia | lia | exact HSH | exact HPM3 | exact HND |].
      destruct INV' as (_ & HP'). split; [exact HBCN | exact HP'].
  Qed.

End DX1L.
End CANSEC1.
