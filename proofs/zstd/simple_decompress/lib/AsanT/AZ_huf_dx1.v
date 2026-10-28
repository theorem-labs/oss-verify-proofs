(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x1_ctx (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte) : Prop :=
  (4096 <= lo /\ lo <= SPV - 2352) /\ SPV < 2^47 /\ SPV mod 16 = 0 /\ 0x10007fff8000 <= lo /\
  zlen src = n /\ zlen dtb = 16388 /\ 1 <= tl <= 12 /\ 0 <= rsv <= 255 /\
  (4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47) /\ (4096 <= SRC /\ 0 <= n < 2^32 /\ SRC + n < 2^47) /\
  (4096 <= DT /\ DT + 16388 < 2^47) /\ DT mod 4 = 0 /\
  (DST + dcap <= lo \/ SPV <= DST) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (DT + 16388 <= lo \/ SPV <= DT) /\
  (DST + dcap <= SRC \/ SRC + n <= DST) /\ (DST + dcap <= DT \/ DT + 16388 <= DST) /\
  nth_error dtb 2 = Some (Z_to_bv 8 tl) /\ nth_error dtb 3 = Some (Z_to_bv 8 rsv) /\
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
Ltac x1_ctx_open CTX :=
  destruct CTX as (LO & SPB & SPA & KLO & SL & DL & TL & RSV & R1 & R2 & R3 & DTA & OS1 & OS2 & OS3 & DJ1 & DJ2 & DT2 & DT3 & DSTA).

Definition x1_actx (RNG : footprint) (m0 : amem) (SPV DST dcap SRC n DT lo : Z) : Prop :=
  (0 < n -> unpoisoned m0 SRC (SRC + n)) /\ unpoisoned m0 DT (DT + 16388) /\ (0 < dcap -> unpoisoned m0 DST (DST + dcap)) /\
  (0 < n -> rng RNG SRC n) /\ (0 < n -> rng RNG (shad SRC) (shspan SRC n)) /\ rng RNG DT 16388 /\ rng RNG (shad DT) (shspan DT 16388) /\
  (0 < dcap -> rng RNG DST dcap) /\ (0 < dcap -> rng RNG (shad DST) (shspan DST dcap)) /\
  rng RNG lo (SPV - lo) /\ rng_aimg RNG /\ azstk RNG m0 lo SPV /\ art m0.
Ltac x1_actx_open ACTX :=
  destruct ACTX as (USRC & UDT & UDST & RSRC & RSRCS & RDT & RDTS & RDST & RDSTS & RSTK & RI & AZS & ART).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma munch_drop_empty : forall (m mm : amem) A W, munch ((A, A) :: W) m mm -> munch W m mm.
Proof.
  intros m mm A W MU. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside]. split; [lia | exact Hx].
Qed.

Section DX1.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x1_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2352 [] m0 huf_noQ).
  Notation W0 := [(DST, DST + dcap); (SPV - 2352, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).

  (* [comment removed for export] *)
  Definition DINV (mm : amem) : Prop :=
    stk bsegs mm DST (DST + dcap) /\
    rw_cells bsegs mm (SPV + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk bsegs mm lo (SPV + -64) /\
    bytes_at bsegs mm SRC src /\ bytes_at bsegs mm DT dtb /\
    munch W0 m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm.

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in
    destruct DI as (OUT & FR & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold DINV; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333497648 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333495296 <= SPV - 2352) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 UDT RDTS RSTK DSTA R3 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (eapply unp_carryS; [exact UDT | exact MU0 | clear - R3; lia | clear - R3; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS2 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 64 \/ SPV <= DST) /\ (SPV <= DT \/ DT + 16388 <= SPV - 64) /\
                 (SPV <= SRC \/ SRC + n <= SPV - 64))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3).
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma x1_ret : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm -> (r = dcap \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evtF bsegs RNG POST (ST 0x9b8e4 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI HR HR2.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    dinv_open DI. facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kclean.
    kx_autoFLAx [KAApp (SPV - 64) 64] [] 30%nat [KZRange SPV 17594333497648 (2^47)] [(SPV - 64, 64)] [(SPV - 64, 64)].
    all: aside.
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [exact HR|]); split; [exact HR2 | exact I].
  Qed.


  (* [comment removed for export] *)
  Lemma x1_end : forall mm (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm ->
    evtF bsegs RNG POST (ST 0x9b8c8 mm x1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 dcap) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    kclean.
    kx_autoFLAx (@nil kza) [0x9b8e4] 30%nat [KZRange SPV 17594333497648 (2^47); KZRange dcap 0 (2^32)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: first [ eapply x1_ret; [exact DI | left; reflexivity | clear - GF2; lia]
               | eapply x1_ret; [exact DI | right; vm_compute; reflexivity | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tail : forall (k : nat) mm j (x1 x7 x8 x9 x12 x13 x15 x16 x18 x19 x20 x21 x22 x29 x30 x31 : word),
    DINV mm -> 0 <= j < dcap -> dcap - j <= Z.of_nat k ->
    evtF bsegs RNG POST (ST 0x9b828 mm x1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 x13
                           (Z_to_bv 64 (DST + j)) x15 x16 SB x18 x19 x20 x21 x22 (Z_to_bv 64 (64 - tl)) x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros mm j x1 x7 x8 x9 x12 x13 x15 x16 x18 x19 x20 x21 x22 x29 x30 x31 DI HJ HK;
      [exfalso; lia|].
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. dfacts MU UDST RDST RDSTS DSTA R1 LO KLO. ffacts OS1 OS2 OS3 LO.
    kclean.
    Time kx_autoFLAx [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0x9b828; 0x9b8c8] 60%nat
      [KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange (DST + j) 4096 (2^47 - 1); KZRange SPV 17594333497648 (2^47);
       KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange DT 4096 (2^47 - 16388);
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64; KZDisj (SPV - 64) 64 DT 16388;
       KZDisj DST dcap SRC n]
      [(DT, 16388)] [(DT, 16388); (DST, dcap)].
    all: aside.
    Time all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8c8) _ _ _ _) => eapply x1_end; dinv_close
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b828) _ _ _ _) =>
             replace (DST + j + 1) with (DST + (j + 1)) by lia;
             eapply IH; [dinv_close | lia | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_tset : forall mm j (x1 x7 x8 x9 x12 x13 x14 x15 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j < dcap ->
    evtF bsegs RNG POST (ST 0x9b81c mm x1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 x13 x14 x15
                           (Z_to_bv 64 (tl + 256 * rsv)) SB x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm j x1 x7 x8 x9 x12 x13 x14 x15 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI HJ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    kx_autoFLAx (@nil kza) [0x9b828] 12%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange (tl + 256 * rsv) 1 65535; KZRange DT 4096 (2^47 - 16388)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: kit_sh_fix.
    all: eapply (x1_tail (Z.to_nat (dcap - j))); [exact DI | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_594 : forall mm j (x1 x7 x8 x9 x12 x13 x14 x15 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j <= dcap ->
    evtF bsegs RNG POST (ST 0x9b818 mm x1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap) x12 x13 x14 x15
                           (Z_to_bv 64 (tl + 256 * rsv)) SB x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm j x1 x7 x8 x9 x12 x13 x14 x15 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI HJ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    kx_autoFLAx (@nil kza) [0x9b81c; 0x9b8c8] 6%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8c8) _ _ _ _) => eapply x1_end; exact DI
         | |- _ => eapply x1_tset; [exact DI | lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_4d8 : forall mm j (x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    DINV mm -> 0 <= j <= dcap ->
    evtF bsegs RNG POST (ST 0x9b784 mm x1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) x7 x8 x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 dcap)
                           (Z_to_bv 64 (DST + j)) x13 x14 x15 (Z_to_bv 64 (tl + 256 * rsv)) SB x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm j x1 x7 x8 x9 x13 x14 x15 x18 x19 x20 x21 x22 x28 x29 x30 x31 DI HJ.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    kx_autoFLAx (@nil kza) [0x9b81c; 0x9b8c8] 6%nat
      [KZRange j 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47)] (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8c8) _ _ _ _) => eapply x1_end; exact DI
         | |- _ => eapply x1_tset; [exact DI | lia]
         end.
  Qed.

End DX1.
End CANSEC1.
