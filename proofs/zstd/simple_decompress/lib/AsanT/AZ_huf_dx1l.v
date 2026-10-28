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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit AZ_huf_dx1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Notation DINV := (AZ_huf_dx1.DINV ra s0 s1 s2 s3 s4 s5 s6 m0 SPV DST dcap SRC DT lo src dtb).
  Notation x1_end := (AZ_huf_dx1.x1_end RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_tset := (AZ_huf_dx1.x1_tset RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x1_594 := (AZ_huf_dx1.x1_594 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).

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
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
    assert (FF : (DST + dcap <= SPV - 64 \/ SPV <= DST) /\ (SPV <= DT \/ DT + 16388 <= SPV - 64) /\
                 (SPV <= SRC \/ SRC + n <= SPV - 64))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3).
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
  Ltac x1_zmod := repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2^64)) by lia end.
  Ltac x1_zland := repeat match goal with |- context [Z.land ?x 7] =>
    replace (Z.land x 7) with (x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity) end.
  Ltac x1_bits :=
    first [ lia
          | lazymatch goal with BR : (?x mod 2 ^ 64 < 65) |- _ => rewrite (Z.mod_small x (2^64)) in BR by lia end; lia
          | idtac "X1BITS"; lazymatch goal with |- ?g => idtac g end;
            try (match goal with H : ?T |- _ => lazymatch T with context [65] => idtac "HYP" T end; fail end); fail 1 ].

  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation LST pc mm x1 c q x13 x15 x18 x19 x20 x21 x22 pt bits :=
    (ST pc mm x1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) c (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 64)
        (Z_to_bv 64 (DST + q)) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) x13 (Z_to_bv 64 (DST + q)) x15 (Z_to_bv 64 (tl + 256 * rsv)) SB
        x18 x19 x20 x21 x22 pt bits (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 8)).

  (* [comment removed for export] *)
  Lemma x1_body : forall mm q pt bits (c x1 x13 x15 x18 x19 x20 x21 x22 : word),
    DINV mm -> 0 <= q -> q + 4 <= dcap -> 0 <= pt < 2^32 -> 0 <= bits <= 64 ->
    (forall mm' bits' (c' x13' x15' x18' x19' x20' x21' x22' : word),
        DINV mm' -> 0 <= bits' <= 64 ->
        evtF bsegs RNG POST (LST 0x9b484 mm' x1 c' (q + 4) x13' x15' x18' x19' x20' x21' x22' (Z_to_bv 64 pt) (Z_to_bv 64 bits'))) ->
    evtF bsegs RNG POST (LST 0x9b558 mm x1 c q x13 x15 x18 x19 x20 x21 x22 (Z_to_bv 64 pt) (Z_to_bv 64 bits)).
  Proof.
    intros mm q pt bits c x1 x13 x15 x18 x19 x20 x21 x22 DI HQ HQ4 HP HB KH.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. dfacts MU UDST RDST RDSTS DSTA R1 LO KLO. ffacts OS1 OS2 OS3 LO.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    kclean.
    Time kx_autoFLAx [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0x9b484; 0x9b81c; 0x9b8c8] 300%nat
      [KZRange (dcap - q) 4 (2^32); KZRange q 0 (2^32); KZRange (DST + q) 4096 (2^47 - 4); KZRange SPV 17594333497648 (2^47);
       KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange DT 4096 (2^47 - 16388);
       KZRange pt 0 (2^32); KZRange bits 0 64;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64; KZDisj (SPV - 64) 64 DT 16388; KZDisj DST dcap SRC n]
      [(DT, 16388)] [(DT, 16388); (DST, dcap)].
    all: aside.
    Time all: kx_mem.
    all: kx_read_ranges; kx_abs.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b484) _ _ _ _) =>
             replace (DST + q + 4) with (DST + (q + 4)) by lia;
             eapply KH; [dinv_close | x1_bits]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b81c) _ _ _ _) =>
             replace (DST + q + 4) with (DST + (q + 4)) by lia;
             eapply x1_tset; [dinv_close | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b8c8) _ _ _ _) => eapply x1_end; dinv_close
         end.
  Qed.
  (* [comment removed for export] *)
  Definition LINV (pt bits : Z) : Prop := 0 <= bits <= 64 /\ (pt = 0 \/ (1 <= pt /\ pt + 8 <= n)).

  (* [comment removed for export] *)
  Lemma x1_reload : forall mm q pt nb bits stt (x1 x13 x18 x19 x20 x21 x22 : word),
    DINV mm -> 0 <= q <= dcap -> 4 <= dcap -> 0 <= nb <= 8 -> nb <= pt -> pt - nb + 8 <= n -> 0 <= bits <= 64 -> (stt = 0 \/ stt = 1) ->
    (q + 4 <= dcap -> forall mm' bits' (c' x13' x15' x18' x19' x20' x21' x22' : word),
        DINV mm' -> 0 <= bits' <= 64 ->
        evtF bsegs RNG POST (LST 0x9b484 mm' x1 c' (q + 4) x13' x15' x18' x19' x20' x21' x22' (Z_to_bv 64 (pt - nb)) (Z_to_bv 64 bits'))) ->
    evtF bsegs RNG POST (LST 0x9b4c0 mm x1 (Z_to_bv 64 stt) q x13 (Z_to_bv 64 nb) x18 x19 x20 x21 x22 (Z_to_bv 64 pt) (Z_to_bv 64 bits)).
  Proof.
    intros mm q pt nb bits stt x1 x13 x18 x19 x20 x21 x22 DI HQ HD HNB HNB2 HNB3 HB HS KB.
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    pose proof DI as DI'. dinv_open DI'. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU UDT RDTS RSTK DSTA R3 LO KLO. sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO. ffacts OS1 OS2 OS3 LO.
    kclean.
    destruct (Z_lt_le_dec (dcap - 3 - q) 1) as [CQ|CQ]; destruct HS as [-> | ->].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    3-4: kx_autoFLAx [KAUnp DT 16388; KAUnp SRC n] [0x9b558; 0x9b818] 80%nat
      [KZRange (dcap - 3 - q) 1 (2^32);
       KZRange (dcap - q) 0 (2^32); KZRange q 0 (2^32); KZRange (DST + q) 4096 (2^47); KZRange SPV 17594333497648 (2^47);
       KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4100 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange DT 4096 (2^47 - 16388);
       KZRange pt 0 (2^32); KZRange nb 0 8; KZRange (pt - nb) 0 (2^32); KZRange (n - (pt - nb)) 8 (2^32); KZRange bits 0 64;
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + (pt - nb)) 4096 (2^47 - 8);
       KZDisj (SPV - 64) 64 DT 16388; KZDisj (SPV - 64) 64 SRC n; KZDisj DST dcap SRC n]
      [(DT, 16388); (SRC, n)] [(DT, 16388); (SRC, n)].
    (* [comment removed for export] *)
    1-2: kx_autoFLAx [KAUnp DT 16388; KAUnp SRC n] [0x9b558; 0x9b818] 80%nat
      [KZRange (q + 3 - dcap) 0 (2^32);
       KZRange (dcap - q) 0 (2^32); KZRange q 0 (2^32); KZRange (DST + q) 4096 (2^47); KZRange SPV 17594333497648 (2^47);
       KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + dcap) 4100 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63;
       KZRange DT 4096 (2^47 - 16388);
       KZRange pt 0 (2^32); KZRange nb 0 8; KZRange (pt - nb) 0 (2^32); KZRange (n - (pt - nb)) 8 (2^32); KZRange bits 0 64;
       KZRange n 8 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange (SRC + (pt - nb)) 4096 (2^47 - 8);
       KZDisj (SPV - 64) 64 DT 16388; KZDisj (SPV - 64) 64 SRC n; KZDisj DST dcap SRC n]
      [(DT, 16388); (SRC, n)] [(DT, 16388); (SRC, n)].
    all: aside.
    all: kx_mem.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b818) _ _ _ _) => eapply x1_594; [dinv_close | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b558) _ _ _ _) =>
             replace (-1 * nb + pt) with (pt - nb) by lia;
             eapply x1_body; [dinv_close | lia | lia | lia | lia |];
             intros mm' bits' c' x13' x15' x18' x19' x20' x21' x22' DI' HB'; eapply KB; [lia | exact DI' | exact HB']
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_loop : forall (k : nat) mm q pt bits (c x1 x13 x15 x18 x19 x20 x21 x22 : word),
    DINV mm -> 0 <= q <= dcap -> dcap - q < Z.of_nat k -> 4 <= dcap -> LINV pt bits ->
    evtF bsegs RNG POST (LST 0x9b484 mm x1 c q x13 x15 x18 x19 x20 x21 x22 (Z_to_bv 64 pt) (Z_to_bv 64 bits)).
  Proof.
    induction k as [|k IH]; intros mm q pt bits c x1 x13 x15 x18 x19 x20 x21 x22 DI HQ HK HD INV; [exfalso; lia|].
    pose proof CTX as CTX'. x1_ctx_open CTX'. pose proof ACTX as ACTX'. x1_actx_open ACTX'.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    destruct INV as (HB & HP).
    assert (QR : exists qb rb, bits = 8 * qb + rb /\ 0 <= qb <= 8 /\ 0 <= rb <= 7) by (exists (bits / 8), (bits mod 8); clear - HB; lia).
    destruct QR as (qb & rb & -> & HQB & HRB).
    kclean.
    destruct HP as [-> | (HP1 & HP2)]; [| destruct (Z_lt_le_dec pt 8) as [P8|P8]; [destruct (Z_lt_le_dec pt qb) as [PQ|PQ]|]].
    4: kx_autoFLAx (@nil kza) [0x9b4c0; 0x9b818] 60%nat
      [KZRange pt 8 (2^32); KZRange (SRC + pt) 4104 (2^47);
       KZRange q 0 (2^32); KZRange (dcap - q) 0 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + q) 4096 (2^47);
       KZRange (DST + dcap) 4100 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47 - 16388);
       KZRange qb 0 8; KZRange rb 0 7; KZRange (8 * qb + rb) 0 64; KZRange SPV 17594333497648 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    3: kx_autoFLAx (@nil kza) [0x9b4c0; 0x9b818] 60%nat
      [KZRange pt 1 7; KZRange (pt - qb) 0 7; KZRange (SRC + pt) 4097 (2^47);
       KZRange q 0 (2^32); KZRange (dcap - q) 0 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + q) 4096 (2^47);
       KZRange (DST + dcap) 4100 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47 - 16388);
       KZRange qb 0 8; KZRange rb 0 7; KZRange (8 * qb + rb) 0 64; KZRange SPV 17594333497648 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    2: kx_autoFLAx (@nil kza) [0x9b4c0; 0x9b818] 60%nat
      [KZRange pt 1 7; KZRange (qb - pt) 1 8; KZRange (SRC + pt) 4097 (2^47);
       KZRange q 0 (2^32); KZRange (dcap - q) 0 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + q) 4096 (2^47);
       KZRange (DST + dcap) 4100 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47 - 16388);
       KZRange qb 0 8; KZRange rb 0 7; KZRange (8 * qb + rb) 0 64; KZRange SPV 17594333497648 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    1: kx_autoFLAx (@nil kza) [0x9b4c0; 0x9b818] 60%nat
      [KZRange q 0 (2^32); KZRange (dcap - q) 0 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47); KZRange (DST + q) 4096 (2^47);
       KZRange (DST + dcap) 4100 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange SRC 4096 (2^47); KZRange DT 4096 (2^47 - 16388);
       KZRange qb 0 8; KZRange rb 0 7; KZRange (8 * qb + rb) 0 64; KZRange SPV 17594333497648 (2^47)]
      (@nil (Z * Z)) (@nil (Z * Z)).
    all: aside.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b818) _ _ _ _) => eapply x1_594; [exact DI | lia]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9b4c0) _ _ _ _) =>
             x1_zmod; x1_zland;
             eapply x1_reload; [exact DI | lia | exact HD | lia | lia | lia | lia | first [left; reflexivity | right; reflexivity] |];
             intros HQ4 mm' bits' c' x13' x15' x18' x19' x20' x21' x22' DI' HB';
             eapply IH; [exact DI' | lia | lia | exact HD | unfold LINV; split; [exact HB' | lia]]
         end.
  Qed.

End DX1L.
End CANSEC1.
