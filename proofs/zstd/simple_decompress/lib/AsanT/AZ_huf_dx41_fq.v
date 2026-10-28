(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_libc_iface AZ_huf_lbkit AZ_huf_dx41 AZ_huf_dx41_4a.
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
Definition ACTZ_TBL41 : Z := 0x22378.
Section CANSEC0. Context {rc : runConstT}.
Lemma actz_tbl41 : forall m, mem_inv bsegs m -> tbl_in bsegs m ACTZ_TBL41 64 1 0 0 63.
Proof.
  intros m MI. unfold ACTZ_TBL41.
  destruct (image_bytes bsegs 0x22378 64) as [bs|] eqn:EB; [|vm_compute in EB; discriminate EB].
  assert (LB : length bs = 64%nat) by exact (image_bytes_length bsegs 64 _ _ EB).
  assert (HB : bytes_at bsegs m 0x22378 bs).
  { apply ro_bytes_at; [exact MI | lia | rewrite LB; lia |]. apply ro_bytes_b_sound.
    vm_compute in EB. injection EB as <-. vm_compute. reflexivity. }
  pose proof (tbl_in_bytes_at bsegs m 0x22378 bs 1 0 0 63 HB ltac:(lia) ltac:(lia)) as T. rewrite LB in T. apply T.
  intros i Hi Hs. vm_compute in EB. injection EB as <-.
  assert (Hn : (Z.to_nat (1 * i + 0) < 64)%nat) by lia.
  remember (Z.to_nat (1 * i + 0)) as k eqn:Ek. clear - Hn.
  do 64 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; split; discriminate]|]). lia.
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
  Hypothesis TL11 : tl = 11.
  Hypothesis XMC : zd_memcpyZ_stmtA.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].
  (* [comment removed for export] *)
  Notation WDM := [(DST, DST + dcap); (SPV - 496, SPV - 256)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).

  (* [comment removed for export] *)
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -256) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  (* [comment removed for export] *)
  Notation SVS mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation WDF := [(DST, DST + dcap); (SPV - 496, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation TBLV := (Z_to_bv 64 ACTZ_TBL41).
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
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
                   (SPV - 496 + 240 <= S \/ S + len <= SPV - 496) /\ (SPV - 256 + 152 <= S \/ S + len <= SPV - 256) /\
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
    assert (ZS3 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 240 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 240 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV - 256 - -256 < 2 ^ 64 /\ 0 <= 152 < 2 ^ 64 /\ 0 <= SPV - 256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 152 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia);
    assert (ZS9 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS10 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS11 : 0 <= SPV + -352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV + -352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS12 : 0 <= SPV + -104 - -104 < 2 ^ 64 /\ 0 <= 104 < 2 ^ 64 /\ 0 <= SPV + -104 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS13 : 0 <= SPV + -256 - -256 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= SPV + -256 < 2 ^ 64) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 496 \/ SPV - 496 + 240 <= DST) /\ (DST + dcap <= SPV - 256 \/ SPV - 256 + 152 <= DST) /\
                 (SPV - 256 + 152 <= DT \/ DT + 16388 <= SPV - 256) /\ (SPV - 496 + 240 <= DT \/ DT + 16388 <= SPV - 496) /\
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

  (* [comment removed for export] *)
  Ltac sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS :=
    sfacts0 MU0 USRC DSTA AW0 R1 R2;
    pose proof (rng_shspanZ _ _ _ RSRCS) as RSz;
    lazymatch goal with U : unpoisoned ?mm SRC (SRC + n) |- _ =>
      pose proof (unpoisoned_unpZ mm _ _ SRC (SRC + n) U ltac:(lia) ltac:(clear - R2; lia) ltac:(unfold KXKEND; clear - R2; lia)) as USz end.
  (* [comment removed for export] *)
  Ltac kcleanF :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac lclean3 :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
           end.
  Ltac lsideF := lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- _ => lside
    end.
  Ltac zsfactsF :=
    assert (ZF1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF3 : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF4 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 256 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZF5 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
  (* [comment removed for export] *)
  Notation KW mb x5 x6 x8 x9 x14 x15 x16 x17 x25 x28 x30 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 :=
    (forall mm' (y1 y7 y10 y11 y12 y13 y18 y19 y20 y21 y22 y23 y24 y26 y27 y29 y31 : word),
        munch WD mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (X41SA SPV mm' (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) OEND w6 w7 w8 w9
          (Z_to_bv 64 (DT + 4)) w11 w12 w13 w14 w15 w16) -> X41SH SPV mm' -> bytes_at bsegs mm' SRC src ->
        evtF bsegs RNG POST (ST 0xa5fc0 mm' y1 x5 x6 y7 x8 x9 y10 y11 y12 y13 x14 x15 x16 x17 y18 y19 y20 y21 y22 y23 y24 x25 y26 y27 x28 y29 x30 y31)).
  (* [comment removed for export] *)
  Definition X41PF (mm : amem) : Prop := SVS mm /\ stk bsegs mm lo (SPV + -496).
  Lemma x41pf_transport : forall mm mm' W, X41PF mm -> munch W mm mm' -> wmono bsegs mm mm' ->
    disjoint_from W (SPV + -104) 104 -> disjoint_from W lo (SPV + -496 - lo) -> X41PF mm'.
  Proof.
    intros mm mm' W (SV & STK) MU WM D1 D2. split.
    - eapply (rw_cells_transport bsegs _ mm mm' _ _ SV MU WM). exact D1.
    - eapply (stk_transport_disjoint bsegs _ mm mm' _ _ STK MU WM). exact D2.
  Qed.
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_ret := (AZ_huf_dx41.x41_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  (* [comment removed for export] *)
  Lemma x41_einvF : forall mm (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : word) csA,
    X41PF mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm ->
    X41SA SPV mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    X41SH SPV mm ->
    X41SB SPV mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 ->
    rw_cells bsegs mm (SPV + -256) csA -> cells_size csA = 152%nat -> EINVA mm.
  Proof using CTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'.
    intros mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 csA (SV & STK) MI OUT MU0 WM0 SA SH SB AR SZA.
    pose proof (stk_of_rw_cells bsegs mm _ _ SA) as H1.
    pose proof (stk_of_rw_cells bsegs mm _ _ SH) as H2.
    pose proof (stk_of_rw_cells bsegs mm _ _ SB) as H3.
    pose proof (stk_of_rw_cells bsegs mm _ _ AR) as H4.
    rewrite SZA in H4. cbn [cells_size csize Nat.add] in H1, H2, H3.
    change (Z.of_nat 136) with 136 in H1. change (Z.of_nat 8) with 8 in H2. change (Z.of_nat 96) with 96 in H3. change (Z.of_nat 152) with 152 in H4.
    replace (SPV + -496 + 136) with (SPV + -360) in H1 by lia.
    replace (SPV + -360 + 8) with (SPV + -352) in H2 by lia.
    replace (SPV + -352 + 96) with (SPV + -256) in H3 by lia.
    replace (SPV + -256 + 152) with (SPV + -104) in H4 by lia.
    unfold AZ_huf_dx41.EINVA. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU0|split; [exact WM0|exact MI]]].
    eapply (stk_merge bsegs mm lo (SPV + -256)); [|exact H4|lia].
    eapply (stk_merge bsegs mm lo (SPV + -352)); [|exact H3|lia].
    eapply (stk_merge bsegs mm lo (SPV + -360)); [|exact H2|lia].
    eapply (stk_merge bsegs mm lo (SPV + -496)); [exact STK|exact H1|lia].
  Qed.
  Ltac fix_a0 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_t0 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a3 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.

  (* [comment removed for export] *)
  Lemma x41_ferr : forall mm (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : word) csA (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    X41PF mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm ->
    X41SA SPV mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    X41SH SPV mm ->
    X41SB SPV mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 ->
    rw_cells bsegs mm (SPV + -256) csA -> cells_size csA = 152%nat ->
    evtF bsegs RNG POST (ST 0xa7af4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    intros mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 csA x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PV MI OUT MU0 WM0 SA SH SB AR SZA.
    zstep. try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv64_eqm_k; reflexivity)).
    eapply (x41_ret mm 18446744073709551596);
      [ eapply (x41_einvF mm); first [exact PV | exact MI | exact OUT | exact MU0 | exact WM0 | exact SA | exact SH | exact SB | exact AR | exact SZA]
      | right; split; [vm_compute; reflexivity | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_fx : forall mm (w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : word) csA (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    X41PF mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm ->
    (X41SA SPV mm (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16) ->
    X41SH SPV mm ->
    X41SB SPV mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 ->
    rw_cells bsegs mm (SPV + -256) csA -> cells_size csA = 152%nat -> 0 < dcap ->
    evtF bsegs RNG POST (ST 0xa6034 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 csA x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 PV MI OUT MU0 WM0 SA SH SB AR SZA DP.
    facts R1 R2 R3 TL RSV LO SPB KLO. kcleanF.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kx_autoFLA (SA, SH) (@nil kza) [0xa7af8; 0xa605c] 16%nat
      [KZRange dcap 1 4294967296; KZRange SPV 17594333498016 140737488355328]
      [(SPV + -496, 136); (SPV + -360, 8)] [(SPV - 496, 496)].
    all: aside.
    all: eapply (x41_ret mm dcap);
      [ eapply (x41_einvF mm); first [exact PV | exact MI | exact OUT | exact MU0 | exact WM0 | exact SA | exact SH | exact SB | exact AR | exact SZA]
      | left; reflexivity ].
  Qed.

  (* [comment removed for export] *)
  Lemma x41_ft : forall (k : nat) mb mm j pe (x1 x7 x8 x9 x11 x12 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x29 x31 : word) (w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 : word),
    munch WD mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (X41SA SPV mm (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) OEND w6 w7 w8 w9
      (Z_to_bv 64 (DT + 4)) w11 w12 w13 w14 w15 w16) -> X41SH SPV mm -> bytes_at bsegs mm SRC src ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap ->
    KW mb (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 (4)) x8 x9 (Z_to_bv 64 (SPV + -136)) x15 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 ((dcap + 3) / 4)) (Z_to_bv 64 (64)) (Z_to_bv 64 ACTZ_TBL41) (Z_to_bv 64 (DST + pe))
       w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 ->
    evtF bsegs RNG POST (ST 0xa5f2c mm x1 (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 (4)) x7 x8 x9 (Z_to_bv 64 (DST + j)) x11 x12 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (SPV + -136)) x15 (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 ((dcap + 3) / 4))
      x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (64)) x26 x27 (Z_to_bv 64 ACTZ_TBL41) x29 (Z_to_bv 64 (DST + pe)) x31).
  Proof using CTX ACTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    induction k as [|k IH]; intros mb mm j pe x1 x7 x8 x9 x11 x12 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x29 x31
      w6 w7 w8 w9 w11 w12 w13 w14 w15 w16
      MU WM MU0 WM0 MI OUT DTB SA SH SRCB HK HJ HPE K; [exfalso; lia|].
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS3 LO.
    dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. zsfactsF. kcleanF.
    assert (KF : 1 <= pe - j <= 4294967296 /\ 1 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 1 <= pe <= 4294967296 /\
                 4096 <= DST + j <= 140737488355327 /\ 1 <= dcap <= 4294967296 /\ 4096 <= DST + pe <= 140737488355328)
      by (clear - HJ HPE R1; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7).
    kx_autoFLA (SA, SH) [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0xa5f2c; 0xa5fc0] 45%nat
      [KZRange (pe - j) 1 4294967296; KZRange (dcap - j) 1 4294967296; KZRange j 0 4294967296; KZRange pe 1 4294967296; KZRange dcap 1 4294967296;
       KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355327; KZRange (DST + pe) 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZRange (DT + 4) 4100 140737488338944; KZRange SPV 17594333498016 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328;
       KZRange n 0 4294967296; KZWr DST dcap;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 496) 496; KZDisj DST dcap SRC n]
      [(DT, 16388); (SPV + -496, 136); (SPV + -360, 8)] [(DT, 16388); (DST, dcap); (SPV - 496, 496)].
    all: [> aside ..].
    all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear DJS DJK DJB DJFr DJW RS RSz USz; try clear DJF1 DJF2 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz; try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8; try clear ZS9.
    all: try clear ZF1 ZF2 ZF3 ZF4 ZF5.
    all: aclean.
    all: [> kx_gen_regsF [1%nat; 7%nat; 11%nat; 12%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 26%nat; 27%nat; 29%nat; 31%nat] ..].
    all: [> intros; evr; kx_mem ..].
    all: [> kx_strip_mod ..].
    all: lclean2.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa5fc0) _ _ _ _) => eapply K; lsideF
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa5f2c) _ _ _ _) =>
             fix_a0 (DST + (j + 1)); fix_a3 (DST + (j + 1));
             eapply (IH mb); lsideF; exact K
         end.
  Qed.
End DX41AM.
End CANSEC1.
