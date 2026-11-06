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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42  AZ_huf_dx1e AZ_huf_dx42_mh AZ_huf_dx42_m0 AZ_huf_dx42_c0 AZ_huf_dx42_i4.
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
Section DX42BI.
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
  Notation x42_reta0 := (AZ_huf_dx42.x42_reta0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation HINV := AZ_huf_dx42_mh.HINV.
  Notation EINVB := (AZ_huf_dx42.EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42_einvS := (AZ_huf_dx42_i4.x42_einvS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x42_i4 := (AZ_huf_dx42_i4.x42_i4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX HRL NBOK BITINIT).
  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac err_ret SV1 HER HRB := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    eapply (x42_reta0 m2 _);
    [ eapply (x42_einvS m2);
      [ exact SV1 | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -384) | tostk (SPV + -264) | tostk (SPV + -224) | tostk (SPV + -184) | tostk (SPV + -144) ]
    | right; split; [exact HER | exact HRB] ] end.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  (* [comment removed for export] *)
  Ltac hold_ors := repeat match goal with H : _ \/ _ |- _ => apply iheld_intro in H end.
  Ltac unhold_ors := repeat match goal with H : iheld _ |- _ => unfold iheld in H end.

  (* [comment removed for export] *)
  Ltac lsideI HN1 HB1 HB2 NK := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- HINV _ _ _ => first [ assumption | unfold AZ_huf_dx42_mh.HINV; unfold bitd_ptr; clear - HN1 HB1 HB2; destruct (Z.leb_spec 8 NK); lia ]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- _ /\ _ => first [lia | idtac]
    | |- Z.le _ _ => lia
    | |- Z.lt _ _ => lia
    | |- _ => first [eassumption | lia | idtac]
    end.

  (* [comment removed for export] *)
  Lemma x42_i3 : forall mm e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 b2 o2 S3 n3 bs3 S4 n4 bs4 (c1 c2 : word) pad1 pad2 junk3 junk4
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w7 w8 w11 w12 : word),
    FRQ mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    stk bsegs mm lo (SPV + -384) ->
    (FRS mm w0 w1 w2 w3 w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + 2 * e1)) w11 w12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (dcap))) ->
    (BD1 mm c1 (Z_to_bv 64 b1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8))) ->
    (BD2 mm c2 (Z_to_bv 64 b2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8))) ->
    rw_cells bsegs mm (SPV + -224) [CB 40 junk3] ->
    rw_cells bsegs mm (SPV + -264) [CB 40 junk4] ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 0 <= n3 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 0 <= n4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> 
    0 <= e1 -> 3 * e1 <= dcap -> e1 = (dcap + 3) / 4 -> dl = tl + 256 * rsv -> S1 = SRC + 6 -> S2 = S1 + n1 -> S3 = S2 + n2 -> S4 = S3 + n3 -> tot = 6 + n1 + n2 + n3 -> n4 = n - tot ->
    evtF bsegs RNG POST (ST 0xa5fc8 mm x1 x5 x6 x7 (Z_to_bv 64 (DST)) (Z_to_bv 64 (S3)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (n3)) (Z_to_bv 64 (n2)) (Z_to_bv 64 (S2)) SB (Z_to_bv 64 (tot)) (Z_to_bv 64 (n)) (Z_to_bv 64 18446744073709551496) (Z_to_bv 64 (dl)) (Z_to_bv 64 (DST + 3 * e1)) x27 x28 x29 x30 x31).
  Proof using CTX X2OK ACTX HRL NBOK BITINIT rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 b2 o2 S3 n3 bs3 S4 n4 bs4 c1 c2 pad1 pad2 junk3 junk4
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w7 w8 w11 w12
      SV MU0 WM0 MI OUT DTB STK FR B1 B2 BJ3 BJ4 SB1 BL1 SS1 SE1 LN1 SB2 BL2 SS2 SE2 LN2 SB3 BL3 SS3 SE3 LN3 SB4 BL4 SS4 SE4 LN4 HI1 HI2 HE1 HE3 HE HDL HS1 HS2 HS3 HS4 HTOT HN4.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 384) 384) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : (0 <= n4 <= 4294967296) /\ (4096 <= S4 <= 140737488355328) /\ (0 <= tot <= 4294967296) /\ (4096 <= S3 <= 140737488355328) /\ (0 <= n3 <= 4294967296)
                 /\ (4096 <= S2 <= 140737488355328) /\ (0 <= n2 <= 4294967296) /\ (4096 <= S1 <= 140737488355328) /\ (0 <= n1 <= 4294967296))
      by (clear - R2 SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 HTOT HN4; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9).
    (* [comment removed for export] *)
    kx_autoFLA tt (@nil kza) [0xa55d8] 12%nat
      [KZRange n 0 4294967296; KZRange tot 0 4294967296; KZRange (n - tot) 0 4294967296; KZRange n4 0 4294967296; KZRange S3 4096 140737488355328;
       KZRange n3 0 4294967296; KZRange (S3 + n3) 4096 140737488355328; KZRange S4 4096 140737488355328; KZRange S2 4096 140737488355328;
       KZRange n2 0 4294967296; KZRange S1 4096 140737488355328; KZRange n1 0 4294967296; KZRange SPV 17594333497904 140737488355328]
      (@nil (Z * Z)) [(SPV - 384, 384)].
    all: [> aside ..].
    all: [> kx_mem ..].
    all: try clear KXK KXA KXRD; try clear KXE.
    (* [comment removed for export] *)
    assert (AW0 : aappW [(SPV - 2608, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    assert (AZmm : azstk RNG mm lo SPV).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - LO; lia].
      - eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                | exact WM0 | exact AW0 | clear - LO; lia]. }
    assert (ARTmm : art mm).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply (art_transportW42 _ m0 mm ART MU0 WM0). constructor; [cbn [fst]; pose proof (DHI Hd); lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]].
      - eapply (art_transportW42 [(SPV - 2608, SPV)] m0 mm ART); [| exact WM0 |].
        + eapply munch_drop_empty. replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia). exact MU0.
        + constructor; [cbn [fst]; clear - LO KLO; lia | constructor]. }
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    assert (AROS : 0 < n3 -> aro RNG mm S3 n3).
    { intros Hn. eapply aro_sub; [split; [exact USRCc | split; [exact RSRC | exact RSRCS]] | exact SS3 | exact LN3 | exact SE3]. }
    assert (RBD : rng RNG (SPV + -224) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (AROB : aro RNG mm (SPV + -224) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBD]).
    assert (AHB : ahull RNG mm (SPV + -224) 40) by (eapply azstk_ahull; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
    assert (APB : app_blk (SPV + -224) (SPV + -224 + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
    assert (ASTK' : astk RNG lo (SPV + -384)).
    { split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - LO; lia] | exact RI]]. }
    assert (BDA : (SPV + -224) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
    assert (NUMS : (4096 <= SPV + -224) /\ (SPV + -224 + 40 < 2^47) /\ (4096 <= S3) /\ (S3 + n3 < 2^47) /\ (n3 < 2^32) /\
                   (SPV + -224 + 40 <= S3 \/ S3 + n3 <= SPV + -224) /\ (lo <= SPV + -384 - 2224) /\ (SPV + -384 < 2^47) /\
                   (SPV + -224 + 40 <= lo \/ SPV + -384 <= SPV + -224) /\ (S3 + n3 <= lo \/ SPV + -384 <= S3))
      by (clear - LO SPB R2 SS3 SE3 LN3 OS2; lia).
    destruct NUMS as (P6 & P7 & P8 & P9 & P10 & P11 & P13 & P14 & P15 & P16).
    clear USRCc AZmm AW0 RBD KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9.
    clear AZS ARC ART USRC UDT UDST RDST RDSTS RDT RDTS RSRC RSRCS.
    hold_ors. unfold iheld in OS1, OS2, OS3.
    eapply evtF_cut;
      [ eapply (bit_init_g BITINIT RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (SPV + -384) (SPV + -224) S3 n3 lo bs3 junk3);
        [ exact MI | exact BJ3 | exact BDA | exact SB3 | exact BL3 | exact P6 | exact P7 | exact P8 | exact P9 | exact P10 | exact P11
        | exact STK | exact P13 | exact P14 | exact P15 | exact P16 | exact APB | exact AROB | exact AHB | exact AROS | exact ARTmm | exact ASTK' ]
      | clear ARTmm AROS AROB AHB APB ASTK' BDA P6 P7 P8 P9 P10 P11 P13 P14 P15 P16 BJ3 STK;
        unfold bit_init_postA; post_call bsegs mm ].
    unhold_ors. try clear MI.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    (* [comment removed for export] *)
    lazymatch goal with SV' : rw_cells _ m2 (SPV + -104) _, ST' : stk _ m2 lo (SPV + -384) |- _ => rename SV' into SV1; rename ST' into STK1 end.
    destruct POST as [(HR & HN1 & cont & bc & pad & HB1 & HB2 & BDC) | (HER & HRB & bs & BDC)].
    - (* [comment removed for export] *)
      lazymatch type of HR with ?rr = n3 => subst rr end. unfold bitd_cells in BDC.
      replace (bitd_ptr S3 n3) with (S3 + (bitd_ptr S3 n3 - S3)) in BDC by lia.
      kx_autoFLA tt (@nil kza) [0xa5fe4; 0xa7440] 12%nat
        [KZRange n3 1 4294967296; KZRange SPV 17594333497904 140737488355328] (@nil (Z * Z)) [(SPV - 384, 384)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa5fe4) _ _ _ _) =>
             eapply (x42_i4 m2 e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 b2 o2 S3 n3 bs3 bc (bitd_ptr S3 n3 - S3) S4 n4 bs4 c1 c2 cont pad1 pad2 pad junk4);
             first [ exact SV1 | eassumption | lsideI HN1 HB1 HB2 n3 ] end.
    - (* [comment removed for export] *)
      lazymatch type of HER with zd_is_error ?rr = true => rename rr into r end.
      assert (HERR : 18446744073709551497 <= r <= 18446744073709551615) by (unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; clear - HER HRB; lia).
      kx_autoFLA tt (@nil kza) [0xa5fe4; 0xa7440] 12%nat
        [KZRange r 18446744073709551497 18446744073709551615; KZRange SPV 17594333497904 140737488355328] (@nil (Z * Z)) [(SPV - 384, 384)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7440) _ _ _ _) => err_ret SV1 HER HRB end.
  Qed.
End DX42BI.
End CANSEC1.
