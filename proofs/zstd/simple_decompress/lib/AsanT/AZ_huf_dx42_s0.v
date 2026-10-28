(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_hufkit42e2 AZ_huf_dx42 AZ_huf_dx42_i4 AZ_huf_dx42_i3 AZ_huf_dx42_i2 AZ_huf_dx42_i1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
#[local] Ltac kx_sx3 ::= kx_rr_dedup; repeat kx_sx3_1.     (* [comment removed for export] *)
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
#[local] Ltac kxl_rd_exact ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : rw_cells segs m A _ |- _ => apply (kxl_rd_rw segs m A _ N H); reflexivity
      | H : ro_cells segs m A _ |- _ => apply (kxl_rd_ro segs m A _ N H); reflexivity
      | H : bytes_at segs m A ?bs, L : Z.of_nat (length ?bs) = N |- _ => rewrite <- L; exact (rd_at_bytes_at segs m A bs H)
      end
  end.
(* [comment removed for export] *)
#[local] Ltac kxl_lia ::= first [kxl_hyp | solve [kxl_lia_small] | kx_lia].

Section CANSEC1. Context {rc : runConstT}.
Section DX42BS0.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 :=
    (rw_cells bsegs mm (SPV + -408) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRA mm j0 d j1 := (rw_cells bsegs mm (SPV + -576) [CB 40 j0; C8 d; CB 120 j1]).
  Notation FRJ mm j2 := (rw_cells bsegs mm (SPV + -216) [CB 112 j2]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis BITINIT : bit_init_stmtA.

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333497904 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 2608, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 400) 400) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  (* [comment removed for export] *)
  Ltac dfacts MU0 UDST RDST RDSTS DSTA AW0 R1 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let D := fresh "DPOS" in
    assert (D : 0 < dcap) by lia;
    assert (UDSTc : unpoisoned mm DST (DST + dcap))
      by (eapply unp_carryW; [exact (UDST D) | exact MU0 | apply aappW_cons_D; [exact DSTA | exact D | exact AW0] | clear - R1; lia | clear - R1 D; lia | clear - R1; lia]);
    pose proof (RDST D) as RDSTc; pose proof (RDSTS D) as RDSTSc;
    assert (DSTAc : DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST) by (clear - D DSTA; lia);
    pose proof (rng_shspanZ _ _ _ RDSTSc) as RDSTz;
    pose proof (unpoisoned_unpZ _ _ _ DST (DST + dcap) UDSTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R1; lia)) as UDSTz;
    clear D.
  (* [comment removed for export] *)
  Ltac sfacts0 MU0 USRC DSTA AW0 R1 R2 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact USRC | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R2; lia | clear - R2 N; lia | clear - R2; lia]
          | eapply unp_carryW; [exact USRC | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R2; lia | clear - R2 N; lia | clear - R2; lia] ]);
    clear N.
  Ltac sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      assert (SF : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 264 + 160 <= S \/ S + len <= SPV - 264) /\ (SPV - 400 + 136 <= S \/ S + len <= SPV - 400))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      destruct SF as (S0 & S1 & SL32 & S2 & DJS & DJK & DJB & DJFr);
      assert (RS : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia)) as RSz;
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia)) as USz
      end
    end.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 400 \/ SPV - 400 + 136 <= DST) /\ (DST + dcap <= SPV - 264 \/ SPV - 264 + 160 <= DST) /\
                 (SPV - 264 + 160 <= DT \/ DT + 16388 <= SPV - 264) /\ (SPV - 400 + 136 <= DT \/ DT + 16388 <= SPV - 400) /\
                 (DST + dcap <= SPV - 400 \/ SPV - 400 + 400 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
  (* [comment removed for export] *)
  Ltac kclean :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : DT mod 4 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : Z.of_nat (length src) = n |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
  (* [comment removed for export] *)
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [lia | kx_lia | idtac]
    | |- _ \/ _ => try lia
    | |- Z.le _ _ => lia
    | |- Z.lt _ _ => lia
    | |- _ => eassumption
    end.
  Notation HINV o len b := (0 <= o /\ ((o + 8 <= len /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64))).
  Hypothesis KM : forall (dl pe1 pe2 pe3 S1 n1 S2 n2 S3 n3 S4 n4 : Z) (bs1 bs2 bs3 bs4 : list byte) (mb : amem)
      (o1 b1 o2 b2 o3 b3 o4 b4 : Z) (k1 k2 k3 k4 : word) (pad4 j0 j1 j2 : list byte)
      (w0 w8 w9 w10 w11 w12 w13 w14 w16 w18 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x29 x30 x31 : word),
    dl = tl + 256 * rsv -> pe1 = (dcap + 3) / 4 -> pe2 = 2 * pe1 -> pe3 = 3 * pe1 -> pe3 <= dcap ->
    zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 ->
    zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 ->
    zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 ->
    zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 ->
    S1 = SRC + 6 -> S2 = S1 + n1 -> S3 = S2 + n2 -> S4 = S3 + n3 -> S4 + n4 = SRC + n ->
    FRQ mb -> munch W0 m0 mb -> wmono bsegs m0 mb -> mem_inv bsegs mb -> stk bsegs mb DST (DST + dcap) ->
    bytes_at bsegs mb DT dtb -> stk bsegs mb lo (SPV + -576) ->
    FRA mb j0 (Z_to_bv 64 dcap) j1 ->
    FRS mb w0 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 S1)
        (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (S3 + o3)) w16 k1 w18 ->
    BD4 mb k4 (Z_to_bv 64 b4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mb j2 ->
    bytes_at bsegs mb S1 bs1 -> bytes_at bsegs mb S2 bs2 -> bytes_at bsegs mb S3 bs3 -> bytes_at bsegs mb S4 bs4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    evtF bsegs RNG POST (ST 0x9e6cc mb x1 x5 x6 x7 (Z_to_bv 64 dl) (Z_to_bv 64 b1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (DST + dcap)) x17
                            (Z_to_bv 64 b3) k3 (Z_to_bv 64 SRC) (Z_to_bv 64 b2) (Z_to_bv 64 (S2 + o2)) k2 (Z_to_bv 64 DST) (Z_to_bv 64 DT)
                            (Z_to_bv 64 (S1 + o1)) SB (Z_to_bv 64 (DST + pe3)) x29 x30 x31).
  Notation EINVB := (AZ_huf_dx42.EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42_einvS := (AZ_huf_dx42_i4.x42_einvS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x42_ret := (AZ_huf_dx42.x42_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x42_i1 := (AZ_huf_dx42_i1.x42_i1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX BITINIT KM).
  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  Notation x42_err := (AZ_huf_dx42.x42_err RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Ltac ret_err := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    eapply (x42_err m2); eapply (x42_einvS m2);
    [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | tostk (SPV + -576) | tostk (SPV + -408) | tostk (SPV + -256) | tostk (SPV + -216) ] end.
  (* [comment removed for export] *)
  Lemma x42_sbufA : forall mm A bs B k len, bytes_at bsegs mm A bs -> 0 <= k -> 0 <= len -> k + len <= zlen bs -> B = A + k ->
    bytes_at bsegs mm B (firstn (Z.to_nat len) (skipn (Z.to_nat k) bs)).
  Proof.
    intros mm A bs B k len HB HK HLEN HKL ->.
    rewrite <- (firstn_skipn (Z.to_nat k) bs) in HB. apply bytes_at_app in HB as [_ HB].
    rewrite firstn_length in HB. rewrite Nat.min_l in HB by lia. rewrite Z2Nat.id in HB by lia.
    rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat k) bs)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
  Qed.
  Lemma x42_sbufL : forall (bs : list byte) k len, 0 <= k -> 0 <= len -> k + len <= zlen bs ->
    zlen (firstn (Z.to_nat len) (skipn (Z.to_nat k) bs)) = len.
  Proof. intros bs k len HK HLEN HKL. rewrite firstn_length, skipn_length. lia. Qed.

  (* [comment removed for export] *)
  Ltac kcleanS :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac ret20 := lazymatch goal with SV1 : rw_cells bsegs ?m2 (SPV + -104) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity));
    eapply (x42_ret m2 _);
    [ eapply (x42_einvS m2);
      [ exact SV1 | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -576) | tostk (SPV + -408) | tostk (SPV + -256) | tostk (SPV + -216) ]
    | right; split; [vm_compute; reflexivity | clear; lia] ] end.
  Ltac fixaddr H a := lazymatch type of H with rw_cells _ _ ?x _ => replace x with a in H by (cbn; lia) end.
  (* [comment removed for export] *)
  Ltac fix_s3 E := lazymatch goal with |- evtF ?a ?b ?c (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 (Z_to_bv 64 ?X) ?r20 ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) ?f ?pc ?fc ?o ?m ?sr) =>
    first [constr_eq X E | refine (@eq_rect_r _ (Z_to_bv 64 E) (fun z => evtF a b c (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 z r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) f pc fc o m sr)) _ (Z_to_bv 64 X) ltac:(f_equal; lia)); cbv beta] end.
  Ltac fix_s4 E := lazymatch goal with |- evtF ?a ?b ?c (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 (Z_to_bv 64 ?X) ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) ?f ?pc ?fc ?o ?m ?sr) =>
    first [constr_eq X E | refine (@eq_rect_r _ (Z_to_bv 64 E) (fun z => evtF a b c (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 z r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) f pc fc o m sr)) _ (Z_to_bv 64 X) ltac:(f_equal; lia)); cbv beta] end.
  Ltac fix_t3 E := lazymatch goal with |- evtF ?a ?b ?c (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20 ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 (Z_to_bv 64 ?X) ?r29 ?r30 ?r31) ?f ?pc ?fc ?o ?m ?sr) =>
    first [constr_eq X E | refine (@eq_rect_r _ (Z_to_bv 64 E) (fun z => evtF a b c (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 z r29 r30 r31) f pc fc o m sr)) _ (Z_to_bv 64 X) ltac:(f_equal; lia)); cbv beta] end.
  Ltac fix_t4 E := lazymatch goal with |- evtF ?a ?b ?c (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20 ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 (Z_to_bv 64 ?X) ?r30 ?r31) ?f ?pc ?fc ?o ?m ?sr) =>
    first [constr_eq X E | refine (@eq_rect_r _ (Z_to_bv 64 E) (fun z => evtF a b c (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 z r30 r31) f pc fc o m sr)) _ (Z_to_bv 64 X) ltac:(f_equal; lia)); cbv beta] end.
  (* [comment removed for export] *)
  Ltac lsideS := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- bytes_at _ _ _ (firstn _ _) => eapply x42_sbufA; [eassumption | lia | lia | lia | lia]
    | |- zlen (firstn _ _) = _ => apply x42_sbufL; lia
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z.le _ _ => first [assumption | lia]
    | |- _ => first [eassumption | lia]
    end.

(* [comment removed for export] *)
  Lemma x42_s0 : forall mm j0 dw j1 j2 junk4
      (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : word),
    FRQ mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    stk bsegs mm lo (SPV + -576) ->
    FRA mm j0 dw j1 ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 ->
    rw_cells bsegs mm (SPV + -256) [CB 40 junk4] -> FRJ mm j2 ->
    bytes_at bsegs mm SRC src -> 10 <= n ->
    evtF bsegs RNG POST (ST 646200 mm (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DT) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 DST) x25 x26 SB x28 x29 x30 (Z_to_bv 64 SRC)).
  Proof using CTX ACTX BITINIT KM rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm j0 dw j1 j2 junk4 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
      SV MU0 WM0 MI OUT DTB STK FA FR BJ4 FJ SRCB N10.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    destruct (Z_lt_le_dec dcap 6) as [DC|DC].
    - (* [comment removed for export] *)
      kx_autoFLA tt (@nil kza) [654692] 20%nat [KZRange dcap 0 5; KZRange n 10 (2^32); KZRange SPV 4096 (2^47)] (@nil (Z * Z)) [(SPV - 576, 576)].
      all: aside.
      all: kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat].
      all: intros; kx_mem.
      all: ret20.
    - (* [comment removed for export] *)
      sfacts0 MU0 USRC DSTA AW0 R1 R2.
      assert (UDTc : unpoisoned mm DT (DT + 16388))
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
            | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                 | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]).
      pose proof (rng_shspanZ _ _ _ RDTS) as RDTz.
      pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz.
      (* [comment removed for export] *)
      kx_autoFLA tt [KAUnp SRC n; KAUnp DT 16388] [646488; 654692; 654684] 180%nat
        [KZRange n 10 (2^32); KZRange dcap 6 (2^32); KZRange (dcap + 3) 9 (2^33); KZRange (DST + dcap) 4096 (2^47);
         KZRange DST 4096 (2^47); KZRange DT 4096 (2^47); KZAlign DT 4; KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47);
         KZRange SPV 4096 (2^47); KZDisj (SPV - 576) 576 SRC n; KZDisj (SPV - 576) 576 DT 16388; KZDisj DST dcap (SPV - 576) 576]
        [(SRC, n); (DT, 16388)] [(SPV - 576, 576)].
      all: aside.
      all: try (lazymatch goal with |- sc_resid _ _ _ (SCReadBase _ _ _ _) => first [kx_sh_rd USRCc | kx_sh_rd UDTc] end).
      all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RSRC | kx_acc RDT | kx_sh_acc RSRCS | kx_sh_acc RDTS] end).
      all: try (lazymatch goal with |- evtF _ _ _ _ => first [kx_sh_dead USRCc 8 | kx_sh_dead UDTc 8] end).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 646488) _ _ _ _) => kx_gen_regsF [7%nat; 8%nat; 9%nat; 10%nat; 15%nat; 16%nat; 17%nat; 18%nat; 21%nat; 22%nat; 23%nat; 25%nat; 26%nat; 30%nat]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 654692) _ _ _ _) => kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 654684) _ _ _ _) => kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
           end.
      all: intros; evr; kx_mem.
      (* [comment removed for export] *)
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 654692) _ _ _ _) => ret20
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 654684) _ _ _ _) => ret_err
           | |- _ => idtac
           end.
      all: kx_sx3; kx_strip_mod.
      all: try rewrite (Z.mod_small (dcap + 3) (2^64)) in * by lia.
      (* [comment removed for export] *)
      all: fix_s3 (DST + (dcap + 3) / 4). all: fix_s4 (DST + dcap). all: fix_t3 (DST + 3 * ((dcap + 3) / 4)). all: fix_t4 (DST + 2 * ((dcap + 3) / 4)).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?N1) (Z_to_bv 64 ?TOT) (Z_to_bv 64 ?N3) (Z_to_bv 64 ?N2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m2 _) =>
               let E1 := constr:((dcap + 3) / 4) in
               assert (0 <= N1) by (first [lia | apply Z.lor_nonneg; split; lia | apply Z.lor_nonneg; split; [apply Z.mul_nonneg_nonneg | ]; lia]); assert (0 <= N2) by (first [lia | apply Z.lor_nonneg; split; lia | apply Z.lor_nonneg; split; [apply Z.mul_nonneg_nonneg | ]; lia]); assert (0 <= N3) by (first [lia | apply Z.lor_nonneg; split; lia | apply Z.lor_nonneg; split; [apply Z.mul_nonneg_nonneg | ]; lia]);
               eapply (x42_i1 m2 E1 TOT (tl + 256 * rsv)
                         (SRC + 6) N1 (firstn (Z.to_nat N1) (skipn (Z.to_nat 6) src))
                         (SRC + 6 + N1) N2 (firstn (Z.to_nat N2) (skipn (Z.to_nat (6 + N1)) src))
                         (SRC + 6 + N1 + N2) N3 (firstn (Z.to_nat N3) (skipn (Z.to_nat (6 + N1 + N2)) src))
                         (SRC + 6 + N1 + N2 + N3) (n - TOT) (firstn (Z.to_nat (n - TOT)) (skipn (Z.to_nat TOT) src)));
               lsideS
           end.
  Qed.

(* [comment removed for export] *)
  Lemma x42_pro : forall (m1 : amem) (junk : list byte)
      (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 : word),
    10 <= n ->
    stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    munch [(SPV - 624, SPV)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m1 lo (SPV + -576) ->
    evtF bsegs RNG POST (ST 646200 m1 (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DT) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 DST) x25 x26 SB x28 x29 x30 (Z_to_bv 64 SRC)).
  Proof using CTX ACTX BITINIT KM rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'.
    intros m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 N10 OUT0 SRCB0 DTB0 MU01 WM01 MI1 FRALL STK1.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (OUT : stk bsegs m1 DST (DST + dcap)) by (eapply stk_transport_disjoint; [exact OUT0 | exact MU01 | exact WM01 | cbn [disjoint_from fst snd]; clear - OS1 LO; lia]).
    assert (SRCB : bytes_at bsegs m1 SRC src) by (eapply bytes_at_transport; [exact SRCB0 | exact MU01 | cbn [disjoint_from fst snd]; clear - OS2 LO SL; lia]).
    assert (DTB : bytes_at bsegs m1 DT dtb) by (eapply bytes_at_transport; [exact DTB0 | exact MU01 | cbn [disjoint_from fst snd]; clear - OS3 LO DL; lia]).
    assert (MU0 : munch W0 m0 m1) by (eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
    clear OUT0 SRCB0 DTB0 MU01.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs m1 _ [] 472 junk _ [40; 8; 120; 152; 40; 112]%nat) in FRALL; [| reflexivity]. cbn [mk_CB_cells app] in FRALL.
    apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in FRALL. destruct FRALL as [FA1 FRALL].
    apply (proj1 (rw_cells_app bsegs _ _ [CB 8 _] _)) in FRALL. destruct FRALL as [FA2 FRALL].
    apply (proj1 (rw_cells_app bsegs _ _ [CB 120 _] _)) in FRALL. destruct FRALL as [FA3 FRALL].
    apply (proj1 (rw_cells_app bsegs _ _ [CB 152 _] _)) in FRALL. destruct FRALL as [FRb FRALL]. fixaddr FRb (SPV + -408).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in FRALL. destruct FRALL as [BJ4 FRALL]. fixaddr BJ4 (SPV + -256).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 112 _] _)) in FRALL. destruct FRALL as [FJ SV]. fixaddr FJ (SPV + -216). fixaddr SV (SPV + -104).
    pose proof (e42_cb_as_c8s m1 _ 1 _ FA2) as FA2w. cbn [e42_c8s_of] in FA2w. clear FA2.
    pose proof (proj2 (rw_cells_app bsegs m1 _ [CB 40 _] _) (conj FA1 (proj2 (rw_cells_app bsegs m1 _ [C8 _] _) (conj FA2w FA3)))) as FA.
    cbn [app] in FA. clear FA1 FA2w FA3.
    pose proof (e42_cb_as_c8s m1 _ 19 _ FRb) as FR. cbn [e42_c8s_of] in FR. clear FRb.
    eapply (x42_s0 m1); eassumption.
  Qed.

  Lemma x42_pro_small : forall (m1 : amem) (junk : list byte)
      (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 : word),
    n < 10 ->
    unpoisoned m0 DT (DT + 16388) -> (0 < dcap -> unpoisoned m0 DST (DST + dcap)) ->
    rng RNG DT 16388 -> rng RNG (shad DT) (shspan DT 16388) ->
    (0 < dcap -> rng RNG DST dcap) -> (0 < dcap -> rng RNG (shad DST) (shspan DST dcap)) ->
    rng RNG lo (SPV - lo) -> rng_aimg RNG -> azstk RNG m0 lo SPV -> aro_client RNG m0 -> art m0 ->
    stk bsegs m0 DST (DST + dcap) ->
    munch [(SPV - 624, SPV)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SPV + -576) [CB 472 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk bsegs m1 lo (SPV + -576) ->
    evtF bsegs RNG POST (ST 646200 m1 (Z_to_bv 64 n) (Z_to_bv 64 dcap) (Z_to_bv 64 DT) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                            (Z_to_bv 64 DST) x25 x26 SB x28 x29 x30 (Z_to_bv 64 SRC)).
  Proof using CTX rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'.
    intros m1 junk x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 N10 UDT UDST RDT RDTS RDST RDSTS RSTK RI AZS ARC ART OUT0 MU01 WM01 MI1 FRALL STK1.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (CTXd : x42b_ctx SPV DST dcap DT 16388 DT tl rsv lo dtb dtb) by (unfold x42b_ctx; repeat split; first [assumption | lia]).
    assert (ACTXd : x42b_actx RNG m0 SPV DST dcap DT 16388 DT lo) by exact (conj UDT (conj UDT (conj UDST (conj RDT (conj RDTS (conj RDT (conj RDTS (conj RDST (conj RDSTS (conj RSTK (conj RI (conj AZS (conj ARC ART))))))))))))).
    assert (OUT : stk bsegs m1 DST (DST + dcap)) by (eapply stk_transport_disjoint; [exact OUT0 | exact MU01 | exact WM01 | cbn [disjoint_from fst snd]; clear - OS1 LO; lia]).
    assert (MU0 : munch W0 m0 m1) by (eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
    clear OUT0 MU01.
    apply (rw_cells_split_CB bsegs m1 _ [] 472 junk _ [168; 152; 40; 112]%nat) in FRALL; [| reflexivity]. cbn [mk_CB_cells app] in FRALL.
    apply (proj1 (rw_cells_app bsegs _ _ [CB 168 _] _)) in FRALL. destruct FRALL as [FA FRALL].
    apply (proj1 (rw_cells_app bsegs _ _ [CB 152 _] _)) in FRALL. destruct FRALL as [FR FRALL]. fixaddr FR (SPV + -408).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in FRALL. destruct FRALL as [BJ4 FRALL]. fixaddr BJ4 (SPV + -256).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 112 _] _)) in FRALL. destruct FRALL as [FJ SV]. fixaddr FJ (SPV + -216). fixaddr SV (SPV + -104).
    (* [comment removed for export] *)
    kx_autoFLA tt (@nil kza) [654692] 20%nat [KZRange n 0 9; KZRange dcap 0 (2^32); KZRange SPV 4096 (2^47)] (@nil (Z * Z)) [(SPV - 576, 576)].
    all: aside.
    all: kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat].
    all: intros; kx_mem.
    all: lazymatch goal with SV1 : rw_cells bsegs ?m2 (SPV + -104) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
      try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 (2^64 - 20)) by (apply bv64_eqm_k; reflexivity));
      eapply (AZ_huf_dx42.x42_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT 16388 DT tl rsv lo dtb dtb CTXd ACTXd m2 _);
      [ eapply (x42_einvS m2);
        [ exact SV1 | eassumption | eassumption | eassumption | eassumption | eassumption
        | tostk (SPV + -576) | tostk (SPV + -408) | tostk (SPV + -256) | tostk (SPV + -216) ]
      | right; split; [vm_compute; reflexivity | clear; lia] ] end.
  Qed.
End DX42BS0.
End CANSEC1.
