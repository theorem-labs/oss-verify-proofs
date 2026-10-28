(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_dx41 AZ_huf_dx41_4a.
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
Tactic Notation "kx_autoFLA_v" constr(VMAX) constr(CH) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFLA_core (VMAX : Z) stops (FUEL : nat) true CH aks kzs rrs wws.
Section CANSEC1. Context {rc : runConstT}.
Section DX41AM.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x41a_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x41a_actx RNG m0 SPV DST dcap SRC n DT lo.
  Hypothesis DHI : dst_hi dcap DST.
  Hypothesis NBOK : huf_nb_ok false dtb tl.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).

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
                 (DST + dcap <= SPV - 480 \/ SPV - 480 + 480 <= DST))
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
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa413c) _ _ _ _) => kx_trap_fast end).
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
  Notation x41_ret := (AZ_huf_dx41.x41_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation x41_i2_stmt := (AZ_huf_dx41.x41_i2_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb).
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_i3_stmt := (AZ_huf_dx41.x41_i3_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb).
  Lemma x41i2_slice : forall (m : amem) a (bs : list byte) off k,
    bytes_at bsegs m a bs -> (off + k <= length bs)%nat -> bytes_at bsegs m (a + Z.of_nat off) (firstn k (skipn off bs)).
  Proof.
    intros m a bs off k H Hk. rewrite <- (firstn_skipn off bs) in H.
    apply OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.Mem.bytes_at_app in H. destruct H as [_ H].
    rewrite length_firstn in H. replace (Nat.min off (length bs)) with off in H by lia.
    rewrite <- (firstn_skipn k (skipn off bs)) in H.
    apply OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.Mem.bytes_at_app in H. destruct H as [H _]. exact H.
  Qed.
  Lemma x41i2_einv : forall mm rest jb (ca cb : list cell),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> stk bsegs mm lo (SPV + -496) ->
    rw_cells bsegs mm (SPV + -496) ca -> Z.of_nat (cells_size ca) = 136 -> X41SH SPV mm ->
    rw_cells bsegs mm (SPV + -352) cb -> Z.of_nat (cells_size cb) = 96 -> rw_cells bsegs mm (SPV + -256) [CB 40 jb] ->
    EINVA mm.
  Proof using CTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'.
    intros mm rest jb ca cb SV RS MU WM MI OUT STK XSA LA XSH XSB LB BJ.
    assert (MG : forall a b c d e, stk bsegs mm a b -> stk bsegs mm c e -> b = c -> e = d -> a <= b <= d -> stk bsegs mm a d)
      by (intros a b c d e H1 H2 E1 E2 HL; subst c e; exact (stk_merge bsegs mm a b d H1 H2 HL)).
    pose proof (stk_of_rw_cells bsegs mm _ _ XSA) as K1. rewrite LA in K1.
    pose proof (stk_of_rw_cells bsegs mm _ _ XSH) as K2.
    pose proof (stk_of_rw_cells bsegs mm _ _ XSB) as K3. rewrite LB in K3.
    pose proof (stk_of_rw_cells bsegs mm _ _ BJ) as K4.
    pose proof (stk_of_rw_cells bsegs mm _ _ RS) as K5.
    cbn [cells_size csize Nat.add] in K2, K4, K5.
    unfold AZ_huf_dx41.EINVA. split; [exact OUT|]. split; [exact SV|].
    split; [|split; [exact MU | split; [exact WM | exact MI]]].
    eapply MG; [| exact K5 | reflexivity | lia | lia].
    eapply MG; [| exact K4 | reflexivity | lia | lia].
    eapply MG; [| exact K3 | reflexivity | lia | lia].
    eapply MG; [| exact K2 | reflexivity | lia | lia].
    eapply MG; [exact STK | exact K1 | reflexivity | lia | lia].
  Qed.
  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac err_ret := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m2 _) =>
    rewrite <- (Z_to_bv_mod64 X);
    eapply (x41_ret m2 _);
    [ eapply (x41i2_einv m2); first [eassumption | reflexivity]
    | right; split; vm_compute; reflexivity ] end.
  Ltac setr8 E := lazymatch goal with |- context CC [mkR ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 (Z_to_bv 64 ?X) ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 ?a25 ?a26 ?a27 ?a28 ?a29 ?a30 ?a31] =>
    first [ constr_eq X E
          | let G := context CC [mkR a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 E) a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31] in
            let EQ := fresh "EQ" in let HG := fresh "HG" in
            assert (EQ : X = E) by (kx_clear_or; lia); enough (HG : G) by (rewrite <- EQ in HG; exact HG); clear EQ ] end.
  Ltac setr25 E := lazymatch goal with |- context CC [mkR ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 (Z_to_bv 64 ?X) ?a26 ?a27 ?a28 ?a29 ?a30 ?a31] =>
    first [ constr_eq X E
          | let G := context CC [mkR a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 (Z_to_bv 64 E) a26 a27 a28 a29 a30 a31] in
            let EQ := fresh "EQ" in let HG := fresh "HG" in
            assert (EQ : X = E) by (kx_clear_or; lia); enough (HG : G) by (rewrite <- EQ in HG; exact HG); clear EQ ] end.
  Ltac b2enum B :=
    let BCE := fresh "BCE" in
    kx_read_ranges;
    lazymatch B with
    | -1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + ?c =>
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? -1 * Z.lxor v 31 + c) && (-1 * Z.lxor v 31 + c <=? 8))%bool end
    | bv_unsigned (edenot ?E ?e) + ?c =>
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (0 <=? v + c) && (v + c <=? 64))%bool end
    | bv_unsigned (edenot ?E ?e) =>
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (0 <=? v) && (v <=? 64))%bool end
    end;
    cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  (* [comment removed for export] *)
  Ltac hold_ors := repeat match goal with H : _ \/ _ |- _ => apply x41_held_intro in H end.
  Ltac unhold_ors := repeat match goal with H : x41_held _ |- _ => unfold x41_held in H end.

  (* [comment removed for export] *)
  Lemma x41_i2 : x41_i3_stmt -> x41_i2_stmt.
  Proof using CTX ACTX DHI NBOK rc.
    intros HI3. unfold AZ_huf_dx41.x41_i3_stmt in HI3. unfold AZ_huf_dx41.x41_i2_stmt.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm rest jb dl l1 l2 l3 LL o1 b1 c1 w0 w8 w16 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128
      w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 x5 x6 x7 x11 x12 x16 x17 x22 x24 x25
      SV RS MU0 WM0 MI OUT DTB SRCB STK XSA XSH XSB BJ HDC HN HL1 HL2 HL3 HLL HLN HSG HDL HL2p HO1 HO1b HB1 HB1b.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    (* [comment removed for export] *)
    assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    remember (SRC + 6 + l1) as S2 eqn:HS2.
    assert (SB2 : bytes_at bsegs mm S2 (firstn (Z.to_nat l2) (skipn (Z.to_nat (6 + l1)) src))).
    { rewrite HS2. replace (SRC + 6 + l1) with (SRC + Z.of_nat (Z.to_nat (6 + l1))) by lia.
      apply x41i2_slice; [exact SRCB | lia]. }
    set (bs2 := firstn (Z.to_nat l2) (skipn (Z.to_nat (6 + l1)) src)) in SB2.
    assert (BL2 : Z.of_nat (length bs2) = l2) by (subst bs2; rewrite length_firstn, length_skipn; lia).
    clearbody bs2.
    assert (RS2 : rng RNG S2 l2) by (rewrite HS2; eapply rng_sub; [exact RSRC | lia | lia]).
    pose proof (unpoisoned_unpZ mm _ _ S2 (S2 + l2) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; lia)) as US2.
    pose proof (rng_shspanZ_sub RNG SRC n S2 l2 RSRCS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RSS2.
    assert (RW1 : rng RNG (SPV + -496) 136) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (RW2 : rng RNG (SPV + -352) 96) by (eapply rng_sub; [exact RSTK | lia | lia]).
    assert (RW3 : rng RNG (SPV + -360) 8) by (eapply rng_sub; [exact RSTK | lia | lia]).
    clear USRC UDT UDST RDT RDTS RDST RDSTS AZS ARC ART.
    assert (HC : l2 = 1 \/ l2 = 2 \/ l2 = 3 \/ l2 = 4 \/ l2 = 5 \/ l2 = 6 \/ l2 = 7 \/ 8 <= l2) by lia.
    (* [comment removed for export] *)
    destruct HC as [E2|[E2|[E2|[E2|[E2|[E2|[E2|E2]]]]]]].
    8: kx_autoFLA XSH [KAUnp S2 l2] [0xa67f4; 0xa7af8] 260%nat
         [KZRange l2 8 65535; KZRange S2 4096 (2^47); KZRange l3 0 65535;
          KZRange SPV 17594333498016 140737488355328; KZDisj (SPV - 496) 496 S2 l2]
         [(SPV + -360, 8); (S2, l2)] [(SPV + -496, 136); (SPV + -352, 96)].
    1-7: lazymatch type of E2 with _ = ?k => rewrite E2;
           kx_autoFLA_v 8 XSH [KAUnp S2 l2] [0xa67f4; 0xa7af8] 260%nat
             [KZRange l2 k k; KZRange S2 4096 (2^47); KZRange l3 0 65535;
              KZRange SPV 17594333498016 140737488355328; KZDisj (SPV - 496) 496 S2 l2; KZImg 0x22418 0x22430]
             [(SPV + -360, 8); (S2, l2)] [(SPV + -496, 136); (SPV + -352, 96)] end.
    all: aside.
    all: try (lazymatch goal with
         | |- sc_resid _ _ _ _ => first [kx_rd SB2 | kx_rd XSH | kx_wr XSA | kx_wr XSB]
         | |- accP _ _ _ => first [kx_acc RS2 | kx_acc RW1 | kx_acc RW2 | kx_acc RW3]
         end).
    (* [comment removed for export] *)
    all: try (lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa67f4) _ _ _ _) =>
             kx_gen_regsF [5%nat; 6%nat; 7%nat; 11%nat; 12%nat; 14%nat; 15%nat; 16%nat; 17%nat; 22%nat; 24%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) =>
             kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat;
                           21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
         end).
    all: try (intros; kx_mem).
    (* [comment removed for export] *)
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) => err_ret end).
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xa67f4) _ _ _ _) =>
             b2enum B; subst S2;
             lazymatch type of E2 with
             | 8 <= _ =>
                 setr25 (SRC + 6 + l1 + (l2 - 8)); setr8 (SRC + 6 + l1 + l2);
                 eapply (HI3 _ rest jb dl l1 l2 l3 LL o1 b1 (l2 - 8) B)
             | _ = _ =>
                 setr25 (SRC + 6 + l1 + 0); setr8 (SRC + 6 + l1 + l2);
                 eapply (HI3 _ rest jb dl l1 l2 l3 LL o1 b1 0 B)
             end;
             first [ eassumption | solve [kx_clear_or; lia] | (left; reflexivity) | (right; kx_clear_or; lia)
                   | (intros; kx_clear_or; lia) ]
         end.
  Qed.
End DX41AM.
End CANSEC1.
