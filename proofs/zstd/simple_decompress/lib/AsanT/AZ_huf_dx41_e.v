(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_iface3 AZ_huf_dx41_c0 AZ_huf_dx41_m0 AZ_huf_dx41_i4 AZ_huf_dx41_i3 AZ_huf_dx41_i2 AZ_huf_dx41_i1 AZ_huf_dx41_s0.
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
(* [comment removed for export] *)
#[local] Ltac kx_wr_at ::=
  lazymatch goal with
  | |- wr_at ?segs ?m ?A ?N =>
      first [ match goal with
              | H : wr_at segs m A ?N0 |- _ => apply (wr_at_sub segs m A N0 A N H); kx_lia
              | H : rw_cells segs m A ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (wr_at_sub segs m A n A N (proj2 H)); kx_lia
              | H : stk segs m A ?hi |- _ => apply (wr_at_sub segs m A (hi - A) A N); [apply (wr_at_stk segs m A hi H); kx_lia | kx_lia | kx_lia]
              end
            | match goal with
              | H : wr_at segs m ?A0 ?N0 |- _ => apply (wr_at_sub segs m A0 N0 A N H); kx_lia
              | H : u8arr segs m ?A0 ?bs |- _ => apply (wr_at_sub segs m A0 (Z.of_nat (length bs)) A N (proj2 H)); kx_lia
              | H : rw_cells segs m ?A0 ?cs |- _ =>
                  let n := eval lazy in (Z.of_nat (cells_size cs)) in apply (wr_at_sub segs m A0 n A N (proj2 H)); kx_lia
              | H : stk segs m ?lo ?hi |- _ => apply (wr_at_sub segs m lo (hi - lo) A N); [apply (wr_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
              end ]
  end.

(* [comment removed for export] *)
Fixpoint c8s_of (k : nat) (bs : list byte) : list cell :=
  match k with O => [] | S k' => C8 (le_bytes_to_word (firstn 8 bs)) :: c8s_of k' (skipn 8 bs) end.
Lemma c8s_of_props : forall k bs, length bs = (8 * k)%nat ->
  cells_wf (c8s_of k bs) /\ cells_bytes (c8s_of k bs) = bs /\ cells_size (c8s_of k bs) = (8 * k)%nat.
Proof.
  induction k as [|k IH]; intros bs HL.
  - destruct bs; [|discriminate]. cbn. repeat split; try constructor.
  - cbn [c8s_of]. assert (L2 : length (skipn 8 bs) = (8 * k)%nat) by (rewrite skipn_length; lia).
    destruct (IH _ L2) as (W & B & S'). split; [|split].
    + split; [exact I | exact W].
    + cbn [cells_bytes cbytes]. rewrite B, le8_of_bytes by (rewrite firstn_length; lia). apply firstn_skipn.
    + cbn [cells_size csize]. rewrite S'. lia.
Qed.
Section CANSEC0. Context {rc : runConstT}.
Lemma cb_as_c8s : forall m A (k : nat) bs, rw_cells bsegs m A [CB (8 * k) bs] -> rw_cells bsegs m A (c8s_of k bs).
Proof.
  intros m A k bs H. assert (HL : length bs = (8 * k)%nat).
  { destruct H as [[W _] _]. exact (proj1 W). }
  destruct (c8s_of_props k bs HL) as (W & B & S').
  apply (rw_cells_recast bsegs m A _ _ H W).
  - rewrite B. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite S'. cbn [cells_size csize]. lia.
Qed.
Lemma cb104_as_c8s : forall m A bs, rw_cells bsegs m A [CB 104 bs] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word,
    rw_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12].
Proof. intros m A bs H. pose proof (cb_as_c8s m A 13 bs H) as H2. cbn [c8s_of] in H2. do 13 eexists. exact H2. Qed.
(* [comment removed for export] *)
Lemma frame480_split : forall m A junk, rw_cells bsegs m A [CB 496 junk] ->
  exists j1 j2 j3 j4 j6,
    rw_cells bsegs m A [CB 136 j1] /\ rw_cells bsegs m (A + 136) [CB 8 j2] /\ rw_cells bsegs m (A + 144) [CB 96 j3] /\
    rw_cells bsegs m (A + 240) [CB 152 j4] /\ rw_cells bsegs m (A + 392) [CB 104 j6].
Proof.
  intros m A junk H.
  destruct (cb_carve bsegs m A 496 junk 136 8 H ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & r1 & C1 & C2 & R1).
  change (Z.to_nat 136) with 136%nat in C1. change (Z.to_nat 8) with 8%nat in C2. change (496 - Z.to_nat 136 - Z.to_nat 8)%nat with 352%nat in R1.
  replace (A + 136 + 8) with (A + 144) in R1 by lia.
  destruct (cb_carve bsegs m (A + 144) 352 r1 96 152 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (j3 & j4 & j6 & C3 & C4 & C6).
  change (Z.to_nat 96) with 96%nat in C3. change (Z.to_nat 152) with 152%nat in C4. change (352 - Z.to_nat 96 - Z.to_nat 152)%nat with 104%nat in C6.
  replace (A + 144 + 96) with (A + 240) in C4 by lia. replace (A + 144 + 96 + 152) with (A + 392) in C6 by lia.
  exists j1, j2, j3, j4, j6. exact (conj C1 (conj C2 (conj C3 (conj C4 C6)))).
Qed.
(* [comment removed for export] *)
Lemma args152_split : forall m A bs, rw_cells bsegs m A [CB 152 bs] ->
  exists k1 k2, rw_cells bsegs m A [CB 40 k1] /\ rw_cells bsegs m (A + 40) [CB 112 k2].
Proof.
  intros m A bs H.
  destruct (cb_carve bsegs m A 152 bs 0 40 H ltac:(lia) ltac:(lia) ltac:(lia)) as (j0 & k1 & k2 & _ & C1 & C2).
  change (Z.to_nat 40) with 40%nat in C1. change (152 - Z.to_nat 0 - Z.to_nat 40)%nat with 112%nat in C2.
  replace (A + 0) with A in C1 by lia. replace (A + 0 + 40) with (A + 40) in C2 by lia.
  exists k1, k2. exact (conj C1 C2).
Qed.
End CANSEC0.
Section CANSEC1. Context {rc : runConstT}.
Section DX41AM.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis DHI : dst_hi dcap DST.
  Hypothesis NBOK : huf_nb_ok false dtb tl.
  Hypothesis BITINIT : bit_init_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)

  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\ (4096 <= SRC <= 140737488355328) /\
                 (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\ (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\
                 (0 <= rsv <= 255) /\ (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333498016 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 480) 480) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
  (* [comment removed for export] *)
  Ltac sfactsF BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      let sf := fresh "SF" in
      assert (sf : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 480 + 144 <= S \/ S + len <= SPV - 480) /\ (SPV - 224 + 120 <= S \/ S + len <= SPV - 224) /\
                   (0 <= S - 0 < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= S < 2 ^ 64))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      let a1 := fresh "SF" in let a2 := fresh "SF" in let a3 := fresh "SF" in let a4 := fresh "SF" in
      let a5 := fresh "SF" in let a6 := fresh "SF" in let a7 := fresh "SF" in let a8 := fresh "SF" in let a9 := fresh "SF" in
      destruct sf as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9);
      let rs := fresh "RS" in
      assert (rs : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia));
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia))
      end
    end.
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 144 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -480 - -480 < 2 ^ 64 /\ 0 <= 144 < 2 ^ 64 /\ 0 <= SPV + -480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 224 - -224 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV - 224 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -224 - -224 < 2 ^ 64 /\ 0 <= 120 < 2 ^ 64 /\ 0 <= SPV + -224 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 480 - -480 < 2 ^ 64 /\ 0 <= 480 < 2 ^ 64 /\ 0 <= SPV - 480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia);
    assert (ZS9 : 0 <= SPV + -480 - -480 < 2 ^ 64 /\ 0 <= 104 < 2 ^ 64 /\ 0 <= SPV + -480 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS10 : 0 <= SPV + -376 - -376 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -376 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS11 : 0 <= SPV + -144 - -144 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -144 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS12 : 0 <= SPV + -184 - -184 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -184 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS13 : 0 <= SPV + -224 - -224 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -224 < 2 ^ 64) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 480 \/ SPV - 480 + 144 <= DST) /\ (DST + dcap <= SPV - 224 \/ SPV - 224 + 120 <= DST) /\
                 (SPV - 224 + 120 <= DT \/ DT + 16388 <= SPV - 224) /\ (SPV - 480 + 144 <= DT \/ DT + 16388 <= SPV - 480) /\
                 (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
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
           | H : 0 <= _ - 0 < 2 ^ 64 /\ _ |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac kx_lia_or1 :=
    match goal with
    | H : _ \/ _ |- _ =>
        solve [ repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end;
                repeat match goal with H' : _ -> _ |- _ => clear H' end; lia ]
    end.
  Ltac kx_lia_m1 := first [ solve [kx_clear_or; lia] | solve [kx_lia_or1] | kx_bv_ranges; solve [kx_clear_or; lia] | solve [kx_bv_ranges; kx_lia_or1] ].
  #[local] Ltac kx_lia ::= kx_lia_m1.
  #[local] Ltac kxl_lia ::= first [ kxl_hyp | solve [kx_clear_or; lia] | solve [kxl_lia_small] | kx_lia_m1 ].
  (* [comment removed for export] *)
  Ltac lclean2 :=
    repeat match goal with H : ?o = 0 \/ _ |- _ => revert H end;
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : rng _ _ _ |- _ => clear H
           | H : rng_aimg _ |- _ => clear H
           | H : 4096 <= _ <= _ |- _ => clear H
           | H : 17594333495296 <= _ <= _ |- _ => clear H
           | H : 17594333498016 <= _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           | H : atoms_ok _ _ |- _ => clear H
           | H : reads_ok _ _ _ _ _ |- _ => clear H
           | H : know_ok _ _ _ _ |- _ => clear H
           end;
    intros.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [assumption | lia | kx_lia | idtac]
    | |- _ \/ _ => first [assumption | lia | idtac]
    | |- Z.le _ _ => first [assumption | lia]
    | |- Z.lt _ _ => first [assumption | lia]
    | |- _ => eassumption
    end.
  Hypothesis FASTARGS : fast_args_stmt3A.
  Notation x41_ret := (AZ_huf_dx41.x41_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation X41PA := (AZ_huf_dx41_c0.X41PA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV).
  Notation x41pa_transport := (AZ_huf_dx41_c0.x41pa_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_einvS := (AZ_huf_dx41_i4.x41_einvS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x41_s0 := (AZ_huf_dx41_s0.x41_s0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK).
  Notation x41_i1 := (AZ_huf_dx41_i1.x41_i1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK).
  Notation x41_i2 := (AZ_huf_dx41_i2.x41_i2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK).
  Notation x41_i3 := (AZ_huf_dx41_i3.x41_i3 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK).
  Notation x41_i4 := (AZ_huf_dx41_i4.x41_i4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK BITINIT).
  Notation x41_m0 := (AZ_huf_dx41_m0.x41_m0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX DHI NBOK).
  Notation SVS mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac hold_ors := repeat match goal with H : _ \/ _ |- _ => apply x41_held_intro in H end.
  Ltac unhold_ors := repeat match goal with H : x41_held _ |- _ => unfold x41_held in H end.

  (* [comment removed for export] *)
  Notation x41_fast_stmt := (AZ_huf_dx41.x41_fast_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb).
  Hypothesis XFAST : x41_fast_stmt.

  (* [comment removed for export] *)
  Lemma x41_f0_no : forall mm r bs j3
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (w0 w3 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    SVS mm -> stk bsegs mm lo (SPV + -496) ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> bytes_at bsegs mm SRC src ->
    X41SA SPV mm w0 (Z_to_bv 64 n) (Z_to_bv 64 SRC) w3 (Z_to_bv 64 dcap) w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    X41SH SPV mm -> rw_cells bsegs mm (SPV + -352) [CB 96 j3] -> rw_cells bsegs mm (SPV + -256) [CB 152 bs] ->
    (r = 0 \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evtF bsegs RNG POST (ST 0xa4d4c mm x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 DT) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31).
  Proof using CTX ACTX DHI NBOK BITINIT rc.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm r bs j3
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      w0 w3 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      SV STK MU0 WM0 MI OUT DTB SRCB SA SH SBJ ARGS HR HRB.
    facts R1 R2 R3 TL RSV LO SPB KLO. kclean.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    (* [comment removed for export] *)
    destruct (args152_split mm (SPV + -256) bs ARGS) as (k1 & k2 & BJ4 & RS).
    replace (SPV + -256 + 40) with (SPV + -216) in RS by lia. clear ARGS.
    assert (PV : X41PA mm k2) by (split; [exact SV | exact RS]). clear SV RS.
    destruct HR as [HR0 | HRE].
    - subst r.
      kx_autoFLA (SA, SH) (@nil kza) [0xa605c; 0xa7af8] 30%nat
          [KZRange n 0 4294967296; KZRange SPV 17594333498016 140737488355328] [(SPV + -496, 136); (SPV + -360, 8)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: [> kx_gen_regsF [5%nat; 7%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 15%nat; 16%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa605c) _ _ ?m1 _) =>
        assert (EI : EINVA m1) by (eapply (x41_einvS m1 k2);
          [ exact PV | eassumption | eassumption | eassumption | eassumption | eassumption
          | tostk (SPV + -496) | tostk (SPV + -360) | tostk (SPV + -352) | tostk (SPV + -256) ]);
        destruct EI as (_ & SVm & STK104 & _);
        eapply (x41_s0 (x41_i1 (x41_i2 (x41_i3 (x41_i4 x41_m0)))) m1); eassumption end.
    - assert (HERR : 18446744073709551497 <= r <= 18446744073709551615) by (unfold zd_is_error, ZE_maxCode in HRE; apply Z.ltb_lt in HRE; clear - HRE HRB; lia).
      kx_autoFLA (SA, SH) (@nil kza) [0xa605c; 0xa7af8] 30%nat
          [KZRange r 18446744073709551497 18446744073709551615; KZRange SPV 17594333498016 140737488355328] [(SPV + -496, 136); (SPV + -360, 8)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ ?m2 _) =>
        eapply (x41_ret m2 r);
        [ eapply (x41_einvS m2 _);
          [ exact PV | eassumption | eassumption | eassumption | eassumption | eassumption
          | tostk (SPV + -496) | tostk (SPV + -360) | tostk (SPV + -352) | tostk (SPV + -256) ]
        | right; split; [exact HRE | clear - HRB; lia] ] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_entry : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    1 <= n ->
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa4cbc) fc None m0 (seg_rom bsegs)).
  Proof using CTX ACTX DHI NBOK BITINIT FASTARGS XFAST rc.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 N1 MI STK OUT SRCB DTB.
    pose proof ART as ART'. destruct ART' as (GOT & RIC & SHB & INI & LAY & REAL).
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (MU0 : munch W0 m0 m0) by apply munch_refl. assert (WM0 : wmono bsegs m0 m0) by apply wmono_refl.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    carve_frame 496%nat STK.
    destruct (frame480_split m0 _ junk FR) as (j1 & j2 & j3 & j4 & j6 & C1 & C2 & SBJ & ARGS & C6). clear FR.
    replace (SPV + -496 + 136) with (SPV + -360) in C2 by lia. replace (SPV + -496 + 144) with (SPV + -352) in SBJ by lia.
    replace (SPV + -496 + 240) with (SPV + -256) in ARGS by lia. replace (SPV + -496 + 392) with (SPV + -104) in C6 by lia.
    assert (SAX : exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word,
               X41SA SPV m0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16)
      by (pose proof (cb_as_c8s m0 _ 17 j1 C1) as H2; cbn [c8s_of] in H2; do 17 eexists; exact H2).
    destruct SAX as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & SAW).
    assert (SHX : exists hsh : word, rw_cells bsegs m0 (SPV + -360) [C8 hsh])
      by (pose proof (cb_as_c8s m0 _ 1 j2 C2) as H2; cbn [c8s_of] in H2; eexists; exact H2).
    destruct SHX as (hsh & SHW).
    destruct (cb104_as_c8s m0 _ j6 C6) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & SVW).
    clear C1 C2 C6.
    ffacts OS1 OS3 LO.
    assert (SFD : (SPV - 496 + 496 <= SRC \/ SRC + n <= SPV - 496) /\ (SPV - 496 + 496 <= DT \/ DT + 16388 <= SPV - 496))
      by (clear - OS2 OS3 LO R2 R3; lia).
    destruct SFD as [SFD1 SFD2].
    assert (KF : (1 <= n <= 4294967296) /\ (4096 <= DST + dcap <= 140737488355328)) by (clear - N1 R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2).
    destruct (Z_lt_le_dec 0 dcap) as [DC|DC].
    - kx_autoFLA (GOT, SHB, SAW, SHW, SVW) [KAApp (SPV - 496) 496] [0xa605c; 0xaa0d8] 50%nat
        [KZRange n 1 4294967296; KZRange dcap 1 4294967296; KZRange (DST + dcap) 4097 140737488355328; KZRange DST 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944; KZRange SRC 4096 140737488355328; KZRange SPV 17594333498016 140737488355328;
         KZDisj (SPV - 496) 496 SRC n; KZDisj (SPV - 496) 496 DT 16388; KZDisj DST dcap (SPV - 496) 496;
         KZWr (SPV + -496) 136; KZWr (SPV + -360) 8; KZWr (SPV + -104) 104]
        [(SPV + -496, 136); (SPV + -360, 8); (SPV + -104, 104)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: try clear KF KF1 KF2.
      all: [> kx_mem ..].
      (* [comment removed for export] *)
      all: try (replace (Z_to_bv 64 0) with (Z_to_bv 64 dcap) by (f_equal; clear - DC R1; lia)).
      (* [comment removed for export] *)
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa605c) _ _ ?m2 _) =>
               destruct (args152_split m2 (SPV + -256) j4 ltac:(eassumption)) as (k1 & k2 & BJ4 & RS);
               replace (SPV + -256 + 40) with (SPV + -216) in RS by lia;
               try replace (DST + 0) with DST in * by (clear; lia);
               kx_gen_regsF [5%nat; 7%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 15%nat; 16%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 31%nat]; intros;
               assert (EI : EINVA m2) by (eapply (x41_einvS m2 k2);
                 [ split; [eassumption | exact RS] | eassumption | eassumption | eassumption | eassumption | eassumption
                 | tostk (SPV + -496) | tostk (SPV + -360) | tostk (SPV + -352) | tostk (SPV + -256) ]);
               destruct EI as (_ & _ & STK104 & _);
               eapply (x41_s0 (x41_i1 (x41_i2 (x41_i3 (x41_i4 x41_m0)))) m2); eassumption
           | |- _ => idtac
           end.
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaa0d8) _ _ ?m2 _) => rename m2 into m1 end.
      try replace (DST + 0) with DST in * by (clear; lia).
      lazymatch goal with D : bytes_at bsegs m1 DT dtb |- _ =>
        assert (DTH : bytes_at bsegs m1 DT (firstn 4 dtb)) by (pose proof D as D'; rewrite <- (firstn_skipn 4 dtb) in D'; apply bytes_at_app in D'; exact (proj1 D'));
        assert (DTHL : zlen (firstn 4 dtb) = 4) by (rewrite firstn_length; clear - DL; lia) end.
      assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
      lazymatch goal with MU1 : munch W0 m0 m1, WM1 : wmono bsegs m0 m1 |- _ =>
        assert (AZmm : azstk RNG m1 lo SPV);
        [ destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply azstk_transport; [exact AZS | exact MU1 | exact WM1 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - LO; lia]
          | eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU1 by (clear - Hd R1; lia); exact MU1
                                    | exact WM1 | exact AW0 | clear - LO; lia] ]
        | assert (ARTmm : art m1);
          [ (* [comment removed for export] *)
            lazymatch goal with G' : rt_got m1, S' : rt_shbase m1 |- _ => exact (conj G' (conj RIC (conj S' (conj INI (conj LAY REAL))))) end
          | sfacts0 MU1 USRC DSTA AW0 R1 R2 ] ] end.
      lazymatch goal with MU1 : munch W0 m0 m1 |- _ =>
        assert (UDTc : unpoisoned m1 DT (DT + 16388));
        [ destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU1 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU1 by (clear - Hd R1; lia); exact MU1
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ] | ] end.
      assert (AROS : aro RNG m1 SRC n) by (split; [exact USRCc | split; [exact RSRC | exact RSRCS]]).
      assert (AROD : aro RNG m1 DT 4) by (eapply aro_sub; [split; [exact UDTc | split; [exact RDT | exact RDTS]] | clear; lia | clear; lia | clear - R3; lia]).
      assert (RBA : rng RNG (SPV + -256) 152) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
      assert (AROA : aro RNG m1 (SPV + -256) 152) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBA]).
      assert (APA : app_blk (SPV + -256) (SPV + -256 + 152)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
      assert (ASTK' : astk RNG lo (SPV + -496)) by (split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - LO; lia] | exact RI]]).
      assert (ARA : (SPV + -256) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
      assert (NUMS : (4096 <= lo) /\ (lo <= SPV + -496 - 48) /\ (SPV + -496 < 2^47) /\ (4096 <= SPV + -256) /\ (SPV + -256 + 152 < 2^47) /\
                     (SPV + -256 + 152 <= lo \/ SPV + -496 <= SPV + -256) /\ (4096 <= SRC) /\ (SRC + n < 2^47) /\ (SRC + n <= lo \/ SPV + -496 <= SRC) /\ (n < 2^32) /\
                     (4096 <= DT) /\ (DT + 4 < 2^47) /\ (DT + 4 <= lo \/ SPV + -496 <= DT) /\ (4096 <= DST) /\ (0 <= dcap < 2^32) /\ (DST + dcap < 2^47) /\
                     (SPV + -256 + 152 <= SRC \/ SRC + n <= SPV + -256) /\ (SPV + -256 + 152 <= DT \/ DT + 4 <= SPV + -256))
        by (clear - LO SPB R1 R2 R3 OS2 OS3; lia).
      destruct NUMS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18).
      clear AZmm USRCc UDTc AW0 RBA; clear AZS ARC ART USRC UDT UDST RDST RDSTS RDT RDTS RSRC RSRCS GOT SHB RIC INI LAY REAL.
      try clear KXK KXA KXRD; try clear KXE.
      hold_ors; unfold x41_held in OS1, OS2, OS3.
      lazymatch goal with SRCB1 : bytes_at bsegs m1 SRC src, MI1 : mem_inv bsegs m1, STK1 : stk bsegs m1 lo (SPV + -496), AR : rw_cells bsegs m1 (SPV + -256) [CB 152 j4] |- _ =>
      eapply evtF_cut;
        [ eapply (FASTARGS RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -496) (SPV + -256) DST dcap SRC n DT lo src (firstn 4 dtb) j4);
          [ exact MI1 | exact STK1 | exact Q1 | exact Q2 | exact Q3 | exact AR | exact ARA | exact DTA | exact SRCB1 | exact SL | exact DTH | exact DTHL
          | exact Q4 | exact Q5 | exact Q6 | exact Q7 | exact Q8 | exact Q9 | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15 | exact Q16
          | exact Q17 | exact Q18 | exact APA | exact AROA | exact AROS | exact AROD | exact ARTmm | exact ASTK' ]
        | clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 Q18 APA AROA AROS AROD ARTmm ASTK' AR STK1 DTH DTHL;
          unfold fast_args_post3A; post_call bsegs m1 ] end.
      unhold_ors. try clear MI1.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mm2 end.
      lazymatch goal with P : (_ /\ _) \/ (_ /\ _) |- _ =>
        destruct P as [(HR & l1 & l2 & l3 & b0 & b1 & b2 & b3 & HL1 & HL2 & HL3 & HLN & HQ3 & AR2 & HLOG & NZ0 & NZ1 & NZ2 & NZ3) | (HR & HRB & bs & AR2)] end.
      + (* [comment removed for export] *)
        lazymatch type of HR with ?rr = 1 => subst rr end.
        first [ exfalso; clear - HQ3 DC R1; lia
              | assert (TL11 : tl = 11) by
                  (clear - HLOG DT2 TL; rewrite nth_error_firstn in HLOG by lia; rewrite DT2 in HLOG;
                   apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in HLOG;
                   change ((2 <? 4)%nat) with true in HLOG; cbn beta iota in HLOG;
                   rewrite !Z_to_bv_unsigned, !bv_wrap_small in HLOG by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia); lia);
                lazymatch goal with SVW' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -496), SB' : rw_cells bsegs mm2 (SPV + -352) [CB 96 ?jj] |- _ =>
                  pose proof (cb_as_c8s mm2 _ 12 jj SB') as SBW; cbn [c8s_of] in SBW;
                  eapply (XFAST mm2 l1 l2 l3 b0 b1 b2 b3); first [exact SVW' | exact PC' | eassumption | exact TL11 | lia] end ].
      + (* [comment removed for export] *)
        lazymatch goal with SVW' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -496) |- _ =>
          eapply (x41_f0_no mm2 _ bs j3); first [ exact SVW' | exact PC' | eassumption | exact HRB | exact HR ] end.
    - kx_autoFLA (GOT, SHB, SAW, SHW, SVW) [KAApp (SPV - 496) 496] [0xa605c; 0xaa0d8] 50%nat
        [KZRange n 1 4294967296; KZRange dcap 0 0; KZRange DST 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944; KZRange SRC 4096 140737488355328; KZRange SPV 17594333498016 140737488355328;
         KZDisj (SPV - 496) 496 SRC n; KZDisj (SPV - 496) 496 DT 16388; KZDisj DST dcap (SPV - 496) 496;
         KZWr (SPV + -496) 136; KZWr (SPV + -360) 8; KZWr (SPV + -104) 104]
        [(SPV + -496, 136); (SPV + -360, 8); (SPV + -104, 104)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: try clear KF KF1 KF2.
      all: [> kx_mem ..].
      (* [comment removed for export] *)
      all: try (replace (Z_to_bv 64 0) with (Z_to_bv 64 dcap) by (f_equal; clear - DC R1; lia)).
      (* [comment removed for export] *)
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa605c) _ _ ?m2 _) =>
               destruct (args152_split m2 (SPV + -256) j4 ltac:(eassumption)) as (k1 & k2 & BJ4 & RS);
               replace (SPV + -256 + 40) with (SPV + -216) in RS by lia;
               try replace (DST + 0) with DST in * by (clear; lia);
               kx_gen_regsF [5%nat; 7%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 15%nat; 16%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 31%nat]; intros;
               assert (EI : EINVA m2) by (eapply (x41_einvS m2 k2);
                 [ split; [eassumption | exact RS] | eassumption | eassumption | eassumption | eassumption | eassumption
                 | tostk (SPV + -496) | tostk (SPV + -360) | tostk (SPV + -352) | tostk (SPV + -256) ]);
               destruct EI as (_ & _ & STK104 & _);
               eapply (x41_s0 (x41_i1 (x41_i2 (x41_i3 (x41_i4 x41_m0)))) m2); eassumption
           | |- _ => idtac
           end.
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaa0d8) _ _ ?m2 _) => rename m2 into m1 end.
      try replace (DST + 0) with DST in * by (clear; lia).
      lazymatch goal with D : bytes_at bsegs m1 DT dtb |- _ =>
        assert (DTH : bytes_at bsegs m1 DT (firstn 4 dtb)) by (pose proof D as D'; rewrite <- (firstn_skipn 4 dtb) in D'; apply bytes_at_app in D'; exact (proj1 D'));
        assert (DTHL : zlen (firstn 4 dtb) = 4) by (rewrite firstn_length; clear - DL; lia) end.
      assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
      lazymatch goal with MU1 : munch W0 m0 m1, WM1 : wmono bsegs m0 m1 |- _ =>
        assert (AZmm : azstk RNG m1 lo SPV);
        [ destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply azstk_transport; [exact AZS | exact MU1 | exact WM1 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - LO; lia]
          | eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU1 by (clear - Hd R1; lia); exact MU1
                                    | exact WM1 | exact AW0 | clear - LO; lia] ]
        | assert (ARTmm : art m1);
          [
      (* [comment removed for export] *)
            lazymatch goal with G' : rt_got m1, S' : rt_shbase m1 |- _ => exact (conj G' (conj RIC (conj S' (conj INI (conj LAY REAL))))) end
          | sfacts0 MU1 USRC DSTA AW0 R1 R2 ] ] end.
      lazymatch goal with MU1 : munch W0 m0 m1 |- _ =>
        assert (UDTc : unpoisoned m1 DT (DT + 16388));
        [ destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU1 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU1 by (clear - Hd R1; lia); exact MU1
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ] | ] end.
      assert (AROS : aro RNG m1 SRC n) by (split; [exact USRCc | split; [exact RSRC | exact RSRCS]]).
      assert (AROD : aro RNG m1 DT 4) by (eapply aro_sub; [split; [exact UDTc | split; [exact RDT | exact RDTS]] | clear; lia | clear; lia | clear - R3; lia]).
      assert (RBA : rng RNG (SPV + -256) 152) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
      assert (AROA : aro RNG m1 (SPV + -256) 152) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBA]).
      assert (APA : app_blk (SPV + -256) (SPV + -256 + 152)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
      assert (ASTK' : astk RNG lo (SPV + -496)) by (split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - LO; lia] | exact RI]]).
      assert (ARA : (SPV + -256) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
      assert (NUMS : (4096 <= lo) /\ (lo <= SPV + -496 - 48) /\ (SPV + -496 < 2^47) /\ (4096 <= SPV + -256) /\ (SPV + -256 + 152 < 2^47) /\
                     (SPV + -256 + 152 <= lo \/ SPV + -496 <= SPV + -256) /\ (4096 <= SRC) /\ (SRC + n < 2^47) /\ (SRC + n <= lo \/ SPV + -496 <= SRC) /\ (n < 2^32) /\
                     (4096 <= DT) /\ (DT + 4 < 2^47) /\ (DT + 4 <= lo \/ SPV + -496 <= DT) /\ (4096 <= DST) /\ (0 <= dcap < 2^32) /\ (DST + dcap < 2^47) /\
                     (SPV + -256 + 152 <= SRC \/ SRC + n <= SPV + -256) /\ (SPV + -256 + 152 <= DT \/ DT + 4 <= SPV + -256))
        by (clear - LO SPB R1 R2 R3 OS2 OS3; lia).
      destruct NUMS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18).
      clear AZmm USRCc UDTc AW0 RBA; clear AZS ARC ART USRC UDT UDST RDST RDSTS RDT RDTS RSRC RSRCS GOT SHB RIC INI LAY REAL.
      try clear KXK KXA KXRD; try clear KXE.
      hold_ors; unfold x41_held in OS1, OS2, OS3.
      lazymatch goal with SRCB1 : bytes_at bsegs m1 SRC src, MI1 : mem_inv bsegs m1, STK1 : stk bsegs m1 lo (SPV + -496), AR : rw_cells bsegs m1 (SPV + -256) [CB 152 j4] |- _ =>
      eapply evtF_cut;
        [ eapply (FASTARGS RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -496) (SPV + -256) DST dcap SRC n DT lo src (firstn 4 dtb) j4);
          [ exact MI1 | exact STK1 | exact Q1 | exact Q2 | exact Q3 | exact AR | exact ARA | exact DTA | exact SRCB1 | exact SL | exact DTH | exact DTHL
          | exact Q4 | exact Q5 | exact Q6 | exact Q7 | exact Q8 | exact Q9 | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15 | exact Q16
          | exact Q17 | exact Q18 | exact APA | exact AROA | exact AROS | exact AROD | exact ARTmm | exact ASTK' ]
        | clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 Q18 APA AROA AROS AROD ARTmm ASTK' AR STK1 DTH DTHL;
          unfold fast_args_post3A; post_call bsegs m1 ] end.
      unhold_ors. try clear MI1.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mm2 end.
      lazymatch goal with P : (_ /\ _) \/ (_ /\ _) |- _ =>
        destruct P as [(HR & l1 & l2 & l3 & b0 & b1 & b2 & b3 & HL1 & HL2 & HL3 & HLN & HQ3 & AR2 & HLOG & NZ0 & NZ1 & NZ2 & NZ3) | (HR & HRB & bs & AR2)] end.
      +
      (* [comment removed for export] *)
        lazymatch type of HR with ?rr = 1 => subst rr end.
        first [ exfalso; clear - HQ3 DC R1; lia
              | assert (TL11 : tl = 11) by
                  (clear - HLOG DT2 TL; rewrite nth_error_firstn in HLOG by lia; rewrite DT2 in HLOG;
                   apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in HLOG;
                   change ((2 <? 4)%nat) with true in HLOG; cbn beta iota in HLOG;
                   rewrite !Z_to_bv_unsigned, !bv_wrap_small in HLOG by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia); lia);
                lazymatch goal with SVW' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -496), SB' : rw_cells bsegs mm2 (SPV + -352) [CB 96 ?jj] |- _ =>
                  pose proof (cb_as_c8s mm2 _ 12 jj SB') as SBW; cbn [c8s_of] in SBW;
                  eapply (XFAST mm2 l1 l2 l3 b0 b1 b2 b3); first [exact SVW' | exact PC' | eassumption | exact TL11 | lia] end ].
      +
      (* [comment removed for export] *)
        lazymatch goal with SVW' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -496) |- _ =>
          eapply (x41_f0_no mm2 _ bs j3);
            first [ exact SVW' | exact PC' | eassumption | exact HRB | exact HR
                  | replace (Z_to_bv 64 dcap) with (Z_to_bv 64 0) by (f_equal; clear - DC R1; lia); eassumption ] end.
  Qed.
End DX41AM.
End CANSEC1.
