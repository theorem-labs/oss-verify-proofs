(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 SepHide ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_huf_dx42_fq AZ_huf_dx42_fa AZ_huf_dx42_fb AZ_huf_dx42_fc.
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
Section DX42FD.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 :=
    (rw_cells bsegs mm (SPV + -576) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9;
                                     C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19;
                                     C8 w20; C8 w21; C8 w22; C8 w23; C8 w24; C8 w25; C8 w26; C8 w27; C8 w28; C8 w29;
                                     C8 w30; C8 w31; C8 w32; C8 w33; C8 w34; C8 w35; C8 w36; C8 w37; C8 w38; C8 w39]).
  (* [comment removed for export] *)
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -256) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  (* [comment removed for export] *)
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WDF := [(DST, DST + dcap); (SPV - 576, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis TL11 : tl = 11.

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333498432 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (52 <= 64 - tl <= 63) /\
                 (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF11 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
  Ltac sfacts0 MU0 USRC DSTA AW0 R1 R2 RSRCS :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact USRC | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R2; lia | clear - R2 N; lia | clear - R2; lia]
          | eapply unp_carryW; [exact USRC | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R2; lia | clear - R2 N; lia | clear - R2; lia] ]);
    pose proof (rng_shspanZ _ _ _ RSRCS) as RSRCz;
    pose proof (unpoisoned_unpZ _ _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2; lia)) as USRCz;
    clear N.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS2 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 576 \/ SPV - 576 + 472 <= DST) /\ (SPV - 576 + 472 <= DT \/ DT + 16388 <= SPV - 576) /\
                 (SPV - 576 + 472 <= SRC \/ SRC + n <= SPV - 576) /\ (DST + dcap <= SPV - 576 \/ SPV - 576 + 576 <= DST))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF3 & DJF4 & DJF5).
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
           | H : 0 < dcap -> 0x625000 <= DST |- _ => clear H
           end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  Ltac traps := idtac.
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
  Ltac sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS := sfacts0 MU0 USRC DSTA AW0 R1 R2 RSRCS; rename RSRCz into RSz; rename USRCz into USz.
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
           | H : 0 < dcap -> 0x625000 <= DST |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac lclean2 :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : rng _ _ _ |- _ => clear H
           | H : rng_aimg _ |- _ => clear H
           | H : 4096 <= _ <= _ |- _ => clear H
           | H : 17594333498432 <= _ <= _ |- _ => clear H
           | H : _ + _ < 2 ^ 47 |- _ => clear H
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
  (* [comment removed for export] *)
  Ltac trapsF := idtac.

  (* [comment removed for export] *)
  Ltac kx_lia_or1 :=
    match goal with
    | H : _ \/ _ |- _ =>
        solve [ repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end;
                repeat match goal with H' : _ -> _ |- _ => clear H' end; lia ]
    end.
  Ltac kx_lia_m1 := first [ solve [kx_clear_or; lia] | solve [kx_lia_or1] | kx_bv_ranges; solve [kx_clear_or; lia] | solve [kx_bv_ranges; kx_lia_or1] ].
  (* [comment removed for export] *)
  Ltac mdh_hyp := lazymatch goal with |- ?G => match goal with H : G |- _ => exact H | H : mdh G |- _ => exact H end end.
  Ltac kx_lia_m2 :=
    lazymatch goal with
    | |- _ /\ _ => first [ mdh_hyp | solve [kx_clear_or; lia] | split; kx_lia_m2 ]
    | |- _ \/ _ => first [ mdh_hyp | kx_lia_m1 ]
    | |- _ <= _ <= _ => first [ mdh_hyp | kx_lia_m1 ]
    | |- _ => kx_lia_m1
    end.
  #[local] Ltac kx_lia ::= kx_lia_m2.
  #[local] Ltac kxl_lia ::= first [ mdh_hyp | kx_lia_m2 ].
  #[local] Ltac kxl_hyp ::= mdh_hyp.
  #[local] Ltac kxa_hyp ::= mdh_hyp.
  (* [comment removed for export] *)
  Ltac evw := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end);
    repeat match goal with
    | KXK : know_ok _ ?E _ _ |- context [ev ?E ?j] =>
        lazymatch goal with
        | _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail
        | _ => let H := fresh "KXVR" in kx_erange H (EVar j); cbn [edenot] in H
        end
    end.
  (* [comment removed for export] *)
  #[local] Ltac kx_rd_at ::=
    lazymatch goal with
    | |- rd_at ?segs ?m ?A ?N =>
        lazymatch A with
        | Zpos _ => apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
        | _ =>
          match goal with
          | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
          | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
          | H : rw_cells segs m ?A0 ?cs |- _ =>
              let n := eval lazy in (Z.of_nat (cells_size cs)) in
              apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
          | H : ro_cells segs m ?A0 ?cs |- _ =>
              let n := eval lazy in (Z.of_nat (cells_size cs)) in
              apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
          | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
          end
        end
    end.
  (* [comment removed for export] *)
  #[local] Ltac kxl_wr_exact ::=
    lazymatch goal with
    | |- wr_at ?segs ?m ?A ?N =>
        match goal with
        | H : wr_at segs m A N |- _ => exact H
        | H : rw_cells segs m A ?cs |- _ => let n := eval lazy in (Z.of_nat (cells_size cs)) in lazymatch n with N => exact (proj2 H) end
        end
    end.
  (* [comment removed for export] *)
  Notation KW mb pe jp x5 x6 x14 x15 x16 x17 x18 x19 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 :=
    (forall mm' j' (y1 y9 y10 y11 y13 y21 y23 y24 y25 y26 y28 y31 : word),
        munch WD mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39) -> bytes_at bsegs mm' SRC src -> jp <= j' <= pe ->
        evtF bsegs RNG POST (ST 0x9da68 mm' y1 x5 x6 (Z_to_bv 64 (64)) (Z_to_bv 64 (DST + pe)) y9 y10 y11 (Z_to_bv 64 (DST + j')) y13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC)) y21 (Z_to_bv 64 (SRC + 8)) y23 y24 y25 y26 SB y28 (Z_to_bv 64 (2)) x30 y31)).
  Notation X42PF := (AZ_huf_dx42_fq.X42PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation x42pf_transport := (AZ_huf_dx42_fq.x42pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation EINVE := (AZ_huf_dx42_fq.EINVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42e_einvF := (AZ_huf_dx42_fq.x42e_einvF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl lo src dtb CTX).
  (* [comment removed for export] *)
  Lemma x42f_idx11 : forall (w : word), 0 <= bv_unsigned w / 2251799813685248 / 4 < 2 ^ 11.
  Proof.
    intros w. pose proof (bv_unsigned_in_range 64 w) as HX. unfold bv_modulus in HX. change (2 ^ Z.of_N 64) with (2^64) in HX.
    split; [apply Z.div_pos; [apply Z.div_pos; lia | lia] |].
    apply Z.div_lt_upper_bound; [lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2251799813685248 * (4 * 2 ^ 11)) with (2^64). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma x42f_tbl : forall mm, bytes_at bsegs mm DT dtb -> tbl_in bsegs mm DT 8196 4 7 1 2.
  Proof using X2OK TL11.
    intros mm DTB i I0 I1.
    destruct (X2OK i) as (b & Hn & Hr); [rewrite TL11; lia|].
    replace (DT + 4 * i + 7) with (DT + (4 * i + 7)) by lia.
    rewrite (rdval_bytes_at_1 bsegs mm DT dtb (4 * i + 7) b DTB ltac:(lia) Hn). exact Hr.
  Qed.
  Lemma x42f_tbn : forall mm, bytes_at bsegs mm DT dtb -> tbl_in bsegs mm DT 8196 4 6 0 11.
  Proof using NBOK TL11.
    intros mm DTB i I0 I1.
    destruct (NBOK i) as (b & Hn & Hr); [rewrite TL11; lia|].
    replace (DT + 4 * i + 6) with (DT + (4 * i + 6)) by lia.
    rewrite (rdval_bytes_at_1 bsegs mm DT dtb (4 * i + 6) b DTB ltac:(lia) Hn). pose proof (bv_unsigned_in_range 8 b). rewrite TL11 in Hr. lia.
  Qed.
  Notation x42e_fz := (AZ_huf_dx42_fa.x42e_fz RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fu := (AZ_huf_dx42_fa.x42e_fu RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fp := (AZ_huf_dx42_fb.x42e_fp RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fpe := (AZ_huf_dx42_fb.x42e_fpe RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_f5m2 := (AZ_huf_dx42_fc.x42e_f5m2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  (* [comment removed for export] *)
  Notation HK5 jb mb pe x5 x6 x14 x15 x16 x17 x18 x19 x30
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 :=
    (forall mm' j' off' bc' (p0' : word) (y1 y9 y11 y13 y23 y25 y26 y28 y31 : word),
        munch WD mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39) -> bytes_at bsegs mm' SRC src ->
        p0' = Z_to_bv 64 (SRC + off') -> jb < j' -> 0 <= j' <= pe -> 0 <= bc' <= 64 -> SINVA off' n bc' ->
        evtF bsegs RNG POST (ST 0x9d258 mm' y1 x5 x6 (Z_to_bv 64 (64)) (Z_to_bv 64 (DST + pe)) y9 p0' y11 (Z_to_bv 64 (DST + j')) y13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + pe - 9)) (Z_to_bv 64 (SRC + 8)) y23 (Z_to_bv 64 (bc')) y25 y26 SB y28 (Z_to_bv 64 (2)) x30 y31)).
  (* [comment removed for export] *)
  Lemma x42e_f5_off0 : forall mb mm j pe jp nd off bc
      (x1 x5 x6 x9 x11 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x28 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : word),
    munch WD mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39) -> bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 <= jp <= j -> j <= pe -> pe <= dcap -> off = 0 -> 0 <= bc <= 64 ->
    KW mb pe jp x5 x6 x14 x15 x16 x17 x18 x19 x30
       w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 ->
    evtF bsegs RNG POST (ST 0x9d258 mm x1 x5 x6 (Z_to_bv 64 (64)) (Z_to_bv 64 (DST + pe)) x9 (Z_to_bv 64 (SRC + off)) x11 (Z_to_bv 64 (DST + j)) x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + pe - 9)) (Z_to_bv 64 (SRC + 8)) x23 (Z_to_bv 64 (bc)) x25 x26 SB x28 (Z_to_bv 64 (2)) x30 x31).
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mb mm j pe jp nd off bc x1 x5 x6 x9 x11 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x28 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
      MU WM MU0 WM0 MI OUT DTB FR SRCB HND HJP HJ HPE HO HB K. subst off. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. kcleanF. replace (SRC + 0) with SRC by lia.
    assert (KF : 0 <= pe - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 0 <= pe <= 4294967296 /\ 0 <= dcap - pe <= 4294967296) by (clear - HJP HJ HPE R1; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4).
    kx_autoFLA FR (@nil kza) [0x9d89c; 0x9da68] 20%nat
      [KZRange bc 0 64; KZRange (pe - j) 0 4294967296; KZRange j 0 4294967296; KZRange pe 0 4294967296; KZRange (dcap - pe) 0 4294967296;
       KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
      [(SPV + -576, 320)] [(SPV - 576, 576)].
    all: aside.
    all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: trapsF.
      all: lclean2.
      all: try replace (Z_to_bv 64 (j + DST)) with (Z_to_bv 64 (DST + j)) by (f_equal; lia).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d89c) _ _ ?m1 _) =>
               eapply (x42e_fpe mb m1 jl pe jp (-1 * DT + -5) (X - SRC) B); lsideF; first [exact K | reflexivity | unfold SINVA; lia | lia]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9da68) _ _ ?m1 _) => eapply (x42e_fz mb m1 jl pe jp (-1 * DT + -5)); lsideF; first [exact K | reflexivity | lia]
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42e_f5_small : forall mb mm j pe jp nd off bc
      (x1 x5 x6 x9 x11 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x28 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : word),
    munch WD mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39) -> bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 <= jp <= j -> j <= pe -> pe <= dcap -> pe - j < 10 -> 1 <= off -> off + 8 <= n -> 0 <= bc <= 64 ->
    KW mb pe jp x5 x6 x14 x15 x16 x17 x18 x19 x30
       w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 ->
    evtF bsegs RNG POST (ST 0x9d258 mm x1 x5 x6 (Z_to_bv 64 (64)) (Z_to_bv 64 (DST + pe)) x9 (Z_to_bv 64 (SRC + off)) x11 (Z_to_bv 64 (DST + j)) x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + pe - 9)) (Z_to_bv 64 (SRC + 8)) x23 (Z_to_bv 64 (bc)) x25 x26 SB x28 (Z_to_bv 64 (2)) x30 x31).
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mb mm j pe jp nd off bc x1 x5 x6 x9 x11 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x28 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
      MU WM MU0 WM0 MI OUT DTB FR SRCB HND HJP HJ HPE HF O1 O2 HB K. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS2 OS3 LO.
    sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS. kcleanF.
    assert (KF : 0 <= pe - j <= 9 /\ 8 <= n - off <= 4294967296 /\ 9 <= n <= 4294967296 /\ 0 <= j <= 4294967296 /\ 0 <= dcap - pe <= 4294967296 /\
                 0 <= pe <= 4294967296) by (clear - HF HJP HJ HPE O1 O2 R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
    destruct (Z_lt_le_dec off 8) as [O8|O8].
    - kx_autoFLA FR [KAUnp SRC n] [0x9d89c; 0x9da68] 160%nat
          [KZRange (pe - j) 0 9; KZRange (dcap - j) 0 4294967296; KZRange (dcap - pe) 0 4294967296; KZRange (n - off) 8 4294967296; KZRange off 1 7; KZRange bc 0 64;
           KZRange n 9 4294967296; KZRange j 0 4294967296; KZRange pe 0 4294967296; KZRange dcap 0 4294967296; KZRange (DST + j) 4096 140737488355328; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
          [(SRC, n); (SPV + -576, 320)] [(SRC, n); (SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: trapsF.
      all: aclean.
      all: kx_gen_regsF [1%nat; 9%nat; 11%nat; 13%nat; 21%nat; 23%nat; 25%nat; 26%nat; 28%nat; 31%nat]; intros.
      all: evr. all: evw. all: kx_mem. all: kx_sx3. all: rewrite ?(Z.mod_small bc (2^64)) in * by lia. all: kx_land_ranges. all: kx_strip_mod. all: land7_lin.
      all: lclean2.
      all: try replace (Z_to_bv 64 (j + DST)) with (Z_to_bv 64 (DST + j)) by (f_equal; lia).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d89c) _ _ ?m1 _) =>
               eapply (x42e_fpe mb m1 jl pe jp (-1 * DT + -5) (X - SRC) B); lsideF; first [exact K | reflexivity | unfold SINVA; lia | lia]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9da68) _ _ ?m1 _) => eapply (x42e_fz mb m1 jl pe jp (-1 * DT + -5)); lsideF; first [exact K | reflexivity | lia]
           end.
    - kx_autoFLA FR [KAUnp SRC n] [0x9d89c; 0x9da68] 160%nat
          [KZRange (pe - j) 0 9; KZRange (dcap - j) 0 4294967296; KZRange (dcap - pe) 0 4294967296; KZRange (n - off) 8 4294967296; KZRange off 8 4294967296; KZRange bc 0 64;
           KZRange n 9 4294967296; KZRange j 0 4294967296; KZRange pe 0 4294967296; KZRange dcap 0 4294967296; KZRange (DST + j) 4096 140737488355328; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
          [(SRC, n); (SPV + -576, 320)] [(SRC, n); (SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: trapsF.
      all: aclean.
      all: kx_gen_regsF [1%nat; 9%nat; 11%nat; 13%nat; 21%nat; 23%nat; 25%nat; 26%nat; 28%nat; 31%nat]; intros.
      all: evr. all: evw. all: kx_mem. all: kx_sx3. all: rewrite ?(Z.mod_small bc (2^64)) in * by lia. all: kx_land_ranges. all: kx_strip_mod. all: land7_lin.
      all: lclean2.
      all: try replace (Z_to_bv 64 (j + DST)) with (Z_to_bv 64 (DST + j)) by (f_equal; lia).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d89c) _ _ ?m1 _) =>
               eapply (x42e_fpe mb m1 jl pe jp (-1 * DT + -5) (X - SRC) B); lsideF; first [exact K | reflexivity | unfold SINVA; lia | lia]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9da68) _ _ ?m1 _) => eapply (x42e_fz mb m1 jl pe jp (-1 * DT + -5)); lsideF; first [exact K | reflexivity | lia]
           end.

  Qed.

  (* [comment removed for export] *)
  Lemma x42e_f5 : forall (k : nat) mb mm j pe jp nd off bc
      (x1 x5 x6 x9 x11 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x28 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : word),
    munch WD mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39) -> bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    pe - j <= Z.of_nat k -> 0 <= jp <= j -> j <= pe -> pe <= dcap -> SINVA off n bc -> 0 <= bc <= 64 ->
    KW mb pe jp x5 x6 x14 x15 x16 x17 x18 x19 x30
       w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 ->
    evtF bsegs RNG POST (ST 0x9d258 mm x1 x5 x6 (Z_to_bv 64 (64)) (Z_to_bv 64 (DST + pe)) x9 (Z_to_bv 64 (SRC + off)) x11 (Z_to_bv 64 (DST + j)) x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + pe - 9)) (Z_to_bv 64 (SRC + 8)) x23 (Z_to_bv 64 (bc)) x25 x26 SB x28 (Z_to_bv 64 (2)) x30 x31).
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    induction k as [|k IH]; intros mb mm j pe jp nd off bc x1 x5 x6 x9 x11 x13 x14 x15 x16 x17 x18 x19 x23 x25 x26 x28 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
      MU WM MU0 WM0 MI OUT DTB FR SRCB HND HK HJP HJ HPE HS HB K.
    all: destruct HS as [O0 | (O1 & O2 & B1)]; [eapply (x42e_f5_off0 mb mm j pe jp nd off bc); lsideF; first [exact K | exact HND | exact O0 | lia]|].
    all: destruct (Z_lt_le_dec (pe - j) 10) as [SM|ROOM]; [eapply (x42e_f5_small mb mm j pe jp nd off bc); lsideF; first [exact K | exact HND | lia]|].
    1: exfalso; lia.
    subst nd.
    facts R1 R2 R3 TL LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS2 OS3 LO.
    sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kcleanF.
    assert (TBL : tbl_in bsegs mm DT 8196 4 7 1 2) by (apply x42f_tbl; exact DTB).
    assert (KF : 10 <= pe - j <= 4294967296 /\ 4096 <= DST + j <= 140737488355318 /\ 8 <= n - off <= 4294967296 /\ 9 <= n <= 4294967296 /\
                 0 <= j <= 4294967296 /\ 0 <= dcap - pe <= 4294967296 /\ 10 <= dcap - j <= 4294967296 /\ 0 <= pe <= 4294967296)
      by (clear - ROOM HJP HJ HPE O1 O2 R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8).
    destruct (Z_lt_le_dec off 8) as [O8|O8].
    - kx_autoFLA FR [KAUnp SRC n; KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0x9d3d4; 0x9d89c; 0x9da68] 160%nat
          [KZRange (pe - j) 10 4294967296; KZRange (dcap - j) 10 4294967296; KZRange (dcap - pe) 0 4294967296; KZRange (n - off) 8 4294967296; KZRange off 1 7; KZRange bc 0 64;
           KZRange n 9 4294967296; KZRange j 0 4294967296; KZRange pe 0 4294967296; KZRange dcap 0 4294967296; KZRange (DST + j) 4096 140737488355318;
           KZTbl DT 8196 4 7 1 2; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
          [(DT, 16388); (SRC, n); (SPV + -576, 320)] [(DT, 16388); (SRC, n); (DST, dcap); (SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: trapsF.
      all: aclean.
      all: kx_gen_regsF [1%nat; 9%nat; 23%nat; 25%nat; 26%nat; 28%nat; 31%nat]; intros.
      all: evr. all: evw. all: kx_mem. all: kx_sx3. all: rewrite ?(Z.mod_small bc (2^64)) in * by lia. all: kx_land_ranges. all: kx_strip_mod. all: land7_lin.
      all: lclean2.
      all: try replace (Z_to_bv 64 (j + DST)) with (Z_to_bv 64 (DST + j)) by (f_equal; lia).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) ?L _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d3d4) _ _ ?m1 _) =>
               eapply (x42e_f5m2 j mb m1 jl pe jp (X - SRC) (-1 * DT + -5) B L); lsideF;
               first [ exact K | reflexivity
                     | (* [comment removed for export] *)
                       intros mm2 j2 off2 bc2 p2; intros; subst p2; eapply (IH mb mm2 j2 pe jp (-1 * DT + -5) off2 bc2); lsideF; first [exact K | reflexivity | lia]
                     | lia | lazymatch goal with |- 0 <= bv_unsigned ?w / 2251799813685248 / 4 <= 2047 => pose proof (x42f_idx11 w); lia end ]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d89c) _ _ ?m1 _) =>
               eapply (x42e_fpe mb m1 jl pe jp (-1 * DT + -5) (X - SRC) B); lsideF; first [exact K | reflexivity | unfold SINVA; lia | lia]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9da68) _ _ ?m1 _) => eapply (x42e_fz mb m1 jl pe jp (-1 * DT + -5)); lsideF; first [exact K | reflexivity | lia]
           end.
    - kx_autoFLA FR [KAUnp SRC n; KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap] [0x9d3d4; 0x9d89c; 0x9da68] 160%nat
          [KZRange (pe - j) 10 4294967296; KZRange (dcap - j) 10 4294967296; KZRange (dcap - pe) 0 4294967296; KZRange (n - off) 8 4294967296; KZRange off 8 4294967296; KZRange bc 0 64;
           KZRange n 9 4294967296; KZRange j 0 4294967296; KZRange pe 0 4294967296; KZRange dcap 0 4294967296; KZRange (DST + j) 4096 140737488355318;
           KZTbl DT 8196 4 7 1 2; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
          [(DT, 16388); (SRC, n); (SPV + -576, 320)] [(DT, 16388); (SRC, n); (DST, dcap); (SPV - 576, 576)].
      all: aside.
      all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
      all: trapsF.
      all: aclean.
      all: kx_gen_regsF [1%nat; 9%nat; 23%nat; 25%nat; 26%nat; 28%nat; 31%nat]; intros.
      all: evr. all: evw. all: kx_mem. all: kx_sx3. all: rewrite ?(Z.mod_small bc (2^64)) in * by lia. all: kx_land_ranges. all: kx_strip_mod. all: land7_lin.
      all: lclean2.
      all: try replace (Z_to_bv 64 (j + DST)) with (Z_to_bv 64 (DST + j)) by (f_equal; lia).
      all: lazymatch goal with
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) ?L _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d3d4) _ _ ?m1 _) =>
               eapply (x42e_f5m2 j mb m1 jl pe jp (X - SRC) (-1 * DT + -5) B L); lsideF;
               first [ exact K | reflexivity
                     | (* [comment removed for export] *)
                       intros mm2 j2 off2 bc2 p2; intros; subst p2; eapply (IH mb mm2 j2 pe jp (-1 * DT + -5) off2 bc2); lsideF; first [exact K | reflexivity | lia]
                     | lia | lazymatch goal with |- 0 <= bv_unsigned ?w / 2251799813685248 / 4 <= 2047 => pose proof (x42f_idx11 w); lia end ]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?B) _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9d89c) _ _ ?m1 _) =>
               eapply (x42e_fpe mb m1 jl pe jp (-1 * DT + -5) (X - SRC) B); lsideF; first [exact K | reflexivity | unfold SINVA; lia | lia]
           | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?jl)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9da68) _ _ ?m1 _) => eapply (x42e_fz mb m1 jl pe jp (-1 * DT + -5)); lsideF; first [exact K | reflexivity | lia]
           end.
  Qed.

End DX42FD.
End CANSEC1.
