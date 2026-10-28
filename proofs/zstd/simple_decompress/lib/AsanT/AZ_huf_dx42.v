(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit42.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x42b_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 3136) /\ SPV < 2^47 /\ SPV mod 16 = 0 /\ 0x10007fff8000 <= lo /\
  zlen src = n /\ zlen dtb = 16388 /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ 0 <= n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + 16388 < 2^47) /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + 16388 <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + 16388 <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ nth_error dtb 3 = Some (Z_to_bv 8 rsv) /\
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) /\ DT mod 4 = 0 /\
  (0 < dcap -> 0x625000 <= DST).      (* [comment removed for export] *)
Ltac x42b_ctx_open CTX :=
  destruct CTX as (LO & SPB & SPA & KLO & SL & DL & TL & RSV & R1 & R2 & R3 & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DT3 & DSTA & DTA & DHI).

Definition x42b_actx (RNG : footprint) (m0 : amem) (SPV DST dcap SRC n DT lo : Z) : Prop :=
  unpoisoned m0 SRC (SRC + n) /\ unpoisoned m0 DT (DT + 16388) /\ (0 < dcap -> unpoisoned m0 DST (DST + dcap)) /\
  rng RNG SRC n /\ rng RNG (shad SRC) (shspan SRC n) /\ rng RNG DT 16388 /\ rng RNG (shad DT) (shspan DT 16388) /\
  (0 < dcap -> rng RNG DST dcap) /\ (0 < dcap -> rng RNG (shad DST) (shspan DST dcap)) /\
  rng RNG lo (SPV - lo) /\ rng_aimg RNG /\ azstk RNG m0 lo SPV /\ aro_client RNG m0 /\ art m0.
Ltac x42b_actx_open ACTX :=
  destruct ACTX as (USRC & UDT & UDST & RSRC & RSRCS & RDT & RDTS & RDST & RDSTS & RSTK & RI & AZS & ARC & ART).

Section CANSEC1. Context {rc : runConstT}.
Section DX42B.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).

  (* [comment removed for export] *)
  Definition EINVB (mm : amem) : Prop :=
    stk bsegs mm DST (DST + dcap) /\
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk bsegs mm lo (SPV + -104) /\
    munch [(DST, DST + dcap); (SPV - 3136, SPV)] m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm.

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 :=
    (rw_cells bsegs mm (SPV + -408) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18]).
  (* [comment removed for export] *)
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRA mm j0 d j1 := (rw_cells bsegs mm (SPV + -576) [CB 40 j0; C8 d; CB 120 j1]).
  Notation FRJ mm j2 := (rw_cells bsegs mm (SPV + -216) [CB 112 j2]).
  Notation SB := (Z_to_bv 64 0x7fff8000).

  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 2^47) /\ (0 <= dcap <= 2^32) /\ (4096 <= DT <= 2^47 - 16388) /\ (4096 <= SRC <= 2^47) /\
                 (4096 <= SRC + n <= 2^47) /\ (0 <= n <= 2^32) /\ (0x10007fff8000 <= SPV <= 2^47) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11).
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.

  (* [comment removed for export] *)
  Lemma x42_ret : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVB mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evtF bsegs RNG POST (ST 0x9fd64 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HR.
    destruct EI as (OUT & FR & STK & MU & WM & MI). facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RSTKf : rng RNG (SPV - 104) 104) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kx_autoFLA FR [KAApp (SPV - 104) 104] (@nil Z) 30%nat [KZRange SPV 0x10007fff8000 (2^47)] [(SPV - 104, 104)] [(SPV - 104, 104)].
    all: aside.
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - destruct HR as [HR|[HR _]]; [left; exact HR | right; exact HR].
    - destruct HR as [->|[HR1 HR2]]; [clear - R1; lia|]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_reta0 : forall mm r (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVB mm -> (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evtF bsegs RNG POST (ST 0x9fd60 mm x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 r) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    intros mm r x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI HR.
    zstep. eapply x42_ret; [exact EI | exact HR].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_err : forall mm (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVB mm ->
    evtF bsegs RNG POST (ST 0x9fd5c mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    intros mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 EI.
    zstep. zstep. replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity).
    eapply x42_ret; [exact EI | right; split; [vm_compute; reflexivity | lia]].
  Qed.

  (* [comment removed for export] *)
  Lemma x42_end : forall mm (c4 b4 p4 st4 lm4 : word) pad4
      (x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EINVB mm -> BD4 mm c4 b4 pad4 p4 st4 lm4 ->
    evtF bsegs RNG POST (ST 0xa3488 mm x1 (Z_to_bv 64 dcap) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                            x28 x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros until x31. intros EI B4. facts R1 R2 R3 TL RSV LO SPB KLO.
    pose proof EI as EI'. destruct EI' as (OUT & FR & STK & MU & WM & MI).
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kx_autoFLA B4 [KAApp (SPV - 256) 40] [0x9fd60] 60%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange dcap 0 (2^32)]
      [(SPV - 256, 40)] [(SPV - 576, 576)].
    all: aside.
    all: try clear KXBR; try clear KXBR0; try clear KXBR1; try clear KXBR2; try clear KXBR3; try clear KXBR4; try clear KXBR5; try clear KXBR6; try clear KXBR7.
    all: kx_mem.
    all: try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity)).
    all: first [ eapply x42_reta0; [split; [exact OUT | split; [exact FR | split; [exact STK | split; [eassumption | split; [eassumption | eassumption]]]]] | left; reflexivity]
               | eapply x42_reta0; [split; [exact OUT | split; [exact FR | split; [exact STK | split; [eassumption | split; [eassumption | eassumption]]]]] | right; split; [vm_compute; reflexivity | lia]] ].
  Qed.
End DX42B.
End CANSEC1.
