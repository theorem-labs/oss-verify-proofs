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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 ZdWalkKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42  AZ_hufkit42e2 AZ_huf_dx1e AZ_huf_dx42_mh AZ_huf_dx42_m0 AZ_huf_dx42_c0 AZ_huf_dx42_i4 AZ_huf_dx42_i3 AZ_huf_dx42_i2 AZ_huf_dx42_i1.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis HRL : huf_reload_int_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2608 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation STC ra mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 678828) fc None mm (seg_rom bsegs)).
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 :=
    (rw_cells bsegs mm (SPV + -384) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -264) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -224) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -184) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -144) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2608, SPV)].
  Notation WD4 := [(DST, DST + dcap); (SPV - 264, SPV - 224); (SPV - 400, SPV - 384)].
  Notation WD3 := [(DST, DST + dcap); (SPV - 224, SPV - 184); (SPV - 400, SPV - 384)].
  Notation WD2 := [(DST, DST + dcap); (SPV - 184, SPV - 144); (SPV - 400, SPV - 384)].
  Notation WD1 := [(DST, DST + dcap); (SPV - 144, SPV - 104); (SPV - 296, SPV - 280); (SPV - 400, SPV - 384)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis NBOK : huf_nb_ok true dtb tl.
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
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 706616) _ _ _ _) => kx_trap_fast end).
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
  (* [comment removed for export] *)
  Ltac aclean :=
    repeat match goal with
           | H : unpZ _ _ _ |- _ => clear H
           | H : unpoisoned _ _ _ |- _ => clear H
           | H : rng _ (KXSHLO + _ / 8) _ |- _ => clear H
           | H : rng _ (shad _) _ |- _ => clear H
           | H : aappW _ |- _ => clear H
           | H : _ + _ <= _ \/ _ + _ <= _ |- _ => clear H
           | H : _ + _ + _ <= _ \/ _ + _ <= _ + _ |- _ => clear H
           end.
  Notation x42_ret := (AZ_huf_dx42.x42_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation EINVB := (AZ_huf_dx42.EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42_einvS := (AZ_huf_dx42_i4.x42_einvS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x42_i1 := (AZ_huf_dx42_i1.x42_i1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK BITINIT).

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
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac ret20 := lazymatch goal with SV1 : rw_cells bsegs ?m2 (SPV + -104) _ |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv64_eqm_k; reflexivity));
    eapply (x42_ret m2 _);
    [ eapply (x42_einvS m2);
      [ exact SV1 | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -384) | tostk (SPV + -264) | tostk (SPV + -224) | tostk (SPV + -184) | tostk (SPV + -144) ]
    | right; split; [vm_compute; reflexivity | clear; lia] ] end.
  Ltac fix_s10 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac lsideS := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- bytes_at _ _ _ (firstn _ _) => eapply x42_sbufA; [eassumption | lia | lia | lia | lia]
    | |- zlen (firstn _ _) = _ => apply x42_sbufL; lia
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z.le _ _ => first [assumption | lia]
    | |- _ => first [eassumption | lia]
    end.
  (* [comment removed for export] *)
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 384 - -384 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV - 384 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -384 - -384 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV + -384 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 384 - -384 < 2 ^ 64 /\ 0 <= 384 < 2 ^ 64 /\ 0 <= SPV - 384 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333497904 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  Notation WS0 := [(SPV - 384, SPV - 264)].

  (* [comment removed for export] *)
  Lemma x42_s0 : forall mm junk1 junk2 junk3 junk4
      (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : word),
    FRQ mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    stk bsegs mm lo (SPV + -384) ->
    FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ->
    rw_cells bsegs mm (SPV + -144) [CB 40 junk1] -> rw_cells bsegs mm (SPV + -184) [CB 40 junk2] ->
    rw_cells bsegs mm (SPV + -224) [CB 40 junk3] -> rw_cells bsegs mm (SPV + -264) [CB 40 junk4] ->
    bytes_at bsegs mm SRC src -> 1 <= n ->
    evtF bsegs RNG POST (ST 0xa5d74 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX X2OK ACTX HRL NBOK BITINIT rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm junk1 junk2 junk3 junk4
      x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
      SV MU0 WM0 MI OUT DTB STK FR BJ1 BJ2 BJ3 BJ4 SRCB N1.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    ffacts OS1 OS3 LO.
    assert (SFD : (DST + dcap <= SRC \/ SRC + n <= DST) /\ (SPV - 384 + 120 <= SRC \/ SRC + n <= SPV - 384) /\ (SPV - 384 + 120 <= DT \/ DT + 16388 <= SPV - 384))
      by (clear - DJ1 OS2 OS3 LO R1 R2 R3; lia).
    destruct SFD as (SFD1 & SFD2 & SFD3).
    (* [comment removed for export] *)
    assert (ARTmm : art mm).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply (art_transportW42 _ m0 mm ART MU0 WM0). constructor; [cbn [fst]; pose proof (DHI Hd); lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]].
      - eapply (art_transportW42 [(SPV - 2608, SPV)] m0 mm ART); [| exact WM0 |].
        + eapply munch_drop_empty. replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia). exact MU0.
        + constructor; [cbn [fst]; clear - LO KLO; lia | constructor]. }
    pose proof ARTmm as ART1. destruct ART1 as (GOT & RIC & SHB & INI & LAY & REAL). clear RIC INI LAY REAL.
    destruct (Z_lt_le_dec dcap 6) as [DC|DC]; [| destruct (Z_lt_le_dec n 10) as [N10|N10]].
    - (* [comment removed for export] *)
      kclean. clear ARTmm.
      kx_autoFLA (FR, GOT, SHB) (@nil kza) [0xa5f98; 0xa7444; 0xac838] 20%nat
        [KZRange dcap 0 5; KZRange n 0 4294967296; KZRange SPV 17594333497904 140737488355328; KZWr (SPV + -384) 120] [(SPV + -384, 120)] [(SPV - 384, 384)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: ret20.
    - (* [comment removed for export] *)
      kclean. clear ARTmm.
      kx_autoFLA (FR, GOT, SHB) (@nil kza) [0xa5f98; 0xa7444; 0xac838] 20%nat
        [KZRange dcap 6 4294967296; KZRange n 0 9; KZRange SPV 17594333497904 140737488355328; KZWr (SPV + -384) 120] [(SPV + -384, 120)] [(SPV - 384, 384)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: ret20.
    - (* [comment removed for export] *)
      sfacts0 MU0 USRC DSTA AW0 R1 R2.
      pose proof (unpoisoned_unpZ mm _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2; lia)) as USz.
      pose proof (rng_shspanZ _ _ _ RSRCS) as RSRCz.
      assert (ZSS : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (clear - R2; lia).
      zsfacts. kcleanS. clear ARTmm.
      assert (KF : (9 <= dcap + 3 <= 4294967299) /\ (4096 <= DST + dcap <= 140737488355328) /\ (10 <= n <= 4294967296) /\ (6 <= dcap <= 4294967296) /\
                   (0 <= DT < 2 ^ 64) /\ (4100 <= DT + 4 <= 140737488338944) /\ (0 <= SRC < 2 ^ 64) /\ (0 <= SPV - 384 < 2 ^ 64) /\
                   (0 <= SPV - 384 - -384 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV - 384 < 2 ^ 64))
        by (clear - DC N10 R1 R2 R3 GF7; lia).
      pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9).
      (* [comment removed for export] *)
      repeat match goal with H : _ \/ _ |- _ => apply iheld_intro in H end.
      unfold iheld in SFD2, SFD3, DJF5.
      kx_autoFLA (FR, GOT, SHB) [KAUnp SRC n; KAUnp DT 16388; KAApp (SPV - 384) 120] [0xa5f98; 0xa7444; 0xac838] 180%nat
        [KZRange n 10 4294967296; KZRange dcap 6 4294967296; KZRange (dcap + 3) 9 4294967299; KZRange (DST + dcap) 4096 140737488355328;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange (DT + 4) 4100 140737488338944;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange SPV 17594333497904 140737488355328;
         KZRange tl 1 12; KZRange rsv 0 255;
         KZWr (SPV + -384) 120; KZDisj (SPV - 384) 120 SRC n; KZDisj (SPV - 384) 120 DT 16388; KZDisj DST dcap (SPV - 384) 384]
        [(SRC, n); (DT, 16388); (SPV + -384, 120)] [(SRC, n); (DT, 16388); (SPV - 384, 384)].
      all: [> aside ..].
      all: traps.
      all: unfold iheld in *.
      all: try clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9.
      (* [comment removed for export] *)
      all: try (lazymatch goal with
                | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ev _ ?J) _ _ _ _ _ _) _ (Z_to_bv 64 0xa5f98) _ _ _ _) =>
                    kx_read_eq J RD;
                    rewrite (rdval_bytes_at bsegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
                            (dl_read_g dtb tl rsv DT2 DT3 ltac:(lia) ltac:(lia)) in RD;
                    rewrite RD; clear RD
                end).
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: try clear USz RSRCz ZSS; aclean.
      all: [> lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa5f98) _ _ _ _) => kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 10%nat; 12%nat; 13%nat; 14%nat; 16%nat; 17%nat; 24%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
           | |- _ => kx_gen_regsF [1%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
           end ..].
      all: [> intros; evr; kx_mem ..].
      all: [> kx_sx3; kx_strip_mod ..].
      all: try rewrite (Z.mod_small (dcap + 3) (2^64)) in * by lia.
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7444) _ _ _ _) => ret20
           | FR' : rw_cells bsegs ?m1 (SPV + -384) _ |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?S3) _ _ _ _ _ (Z_to_bv 64 ?N1) _ _ (Z_to_bv 64 ?N3) (Z_to_bv 64 ?N2) (Z_to_bv 64 ?S2) _ (Z_to_bv 64 ?TOT) _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xa5f98) _ _ ?m1 _) =>
               (* [comment removed for export] *)
               let E1 := constr:((dcap + 3) / 4) in
               fix_s10 (DST + 3 * E1);
               lazymatch type of FR' with rw_cells _ _ _ [_; _; _; _; _; _; _; _; _; _; C8 (Z_to_bv 64 ?W10); _; _; _; _] =>
                 first [ constr_eq W10 (DST + 2 * E1) | replace (Z_to_bv 64 W10) with (Z_to_bv 64 (DST + 2 * E1)) in FR' by (f_equal; lia) ] end;
               try (replace (Z_to_bv 64 (dcap + DST)) with (Z_to_bv 64 (DST + dcap)) in FR' by (f_equal; lia));
               eapply (x42_i1 m1 E1 TOT (tl + 256 * rsv)
                         (SRC + 6) N1 (firstn (Z.to_nat N1) (skipn (Z.to_nat 6) src))
                         S2 N2 (firstn (Z.to_nat N2) (skipn (Z.to_nat (6 + N1)) src))
                         S3 N3 (firstn (Z.to_nat N3) (skipn (Z.to_nat (6 + N1 + N2)) src))
                         (S3 + N3) (n - TOT) (firstn (Z.to_nat (n - TOT)) (skipn (Z.to_nat TOT) src))
                         junk1 junk2 junk3 junk4);
               first [ lsideS ]
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_pro : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    1 <= n ->
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa5d3c) fc None m0 (seg_rom bsegs)).
  Proof using CTX X2OK ACTX HRL NBOK BITINIT rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 N1 MI STK OUT SRCB DTB.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (MU0 : munch W0 m0 m0) by apply munch_refl. assert (WM0 : wmono bsegs m0 m0) by apply wmono_refl.
    assert (RFR : rng RNG (SPV - 384) 384) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    carve_frame 384%nat STK.
    lazymatch goal with H : rw_cells bsegs m0 (SPV + -384) [CB 384 ?jj] |- _ =>
      apply (rw_cells_split_CB bsegs m0 _ [] 384 jj _ [120; 40; 40; 40; 40; 104]%nat) in H; [| reflexivity]; cbn [mk_CB_cells app] in H;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 120 _] _)) in H; destruct H as [FRb H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -264) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ4 H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -224) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ3 H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -184) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ2 H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -144) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ1 SVb];
      lazymatch type of SVb with rw_cells _ _ ?x _ => replace x with (SPV + -104) in SVb by (cbn; lia) end end.
    pose proof (e42_cb_as_c8s m0 _ 15 _ FRb) as FRW. cbn [e42_c8s_of] in FRW. clear FRb.
    pose proof (e42_cb_as_c8s m0 _ 13 _ SVb) as SVW. cbn [e42_c8s_of] in SVW. clear SVb.
    assert (SFD : (SPV - 384 + 384 <= SRC \/ SRC + n <= SPV - 384) /\ (SPV - 384 + 384 <= DT \/ DT + 16388 <= SPV - 384) /\
                  (DST + dcap <= SPV - 384 \/ SPV - 384 + 384 <= DST) /\ (4096 <= DST + dcap <= 140737488355328))
      by (clear - OS1 OS2 OS3 LO R1 R2 R3; lia).
    destruct SFD as (SFD1 & SFD2 & SFD3 & SFD4).
    kcleanS.
    kx_autoFLA (FRW, SVW) [KAApp (SPV - 384) 384] [0xa5d74] 30%nat
      [KZRange SPV 17594333497904 140737488355328; KZRange DST 4096 140737488355328; KZRange (DST + dcap) 4096 140737488355328;
       KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZWr (SPV + -384) 120; KZWr (SPV + -104) 104;
       KZDisj (SPV - 384) 384 SRC n; KZDisj (SPV - 384) 384 DT 16388; KZDisj DST dcap (SPV - 384) 384]
      [(SPV + -384, 120); (SPV + -104, 104)] [(SPV - 384, 384)].
    all: aside.
    all: kx_mem.
    all: lazymatch goal with SV' : rw_cells bsegs ?m1 (SPV + -104) _ |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa5d74) _ _ ?m1 _) =>
           eapply (x42_s0 m1); first [exact SV' | eassumption | exact N1] end.
  Qed.
End DX42BS0.
End CANSEC1.
