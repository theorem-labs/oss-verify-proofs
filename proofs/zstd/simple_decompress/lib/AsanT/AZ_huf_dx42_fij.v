(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 SepHide ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_hufkit42e AZ_huf_dx42_fq AZ_huf_dx42_fi0.
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
Section DX42FIJ.
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
  Notation X42PF := (AZ_huf_dx42_fq.X42PF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation x42pf_transport := (AZ_huf_dx42_fq.x42pf_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo).
  Notation EINVE := (AZ_huf_dx42_fq.EINVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42e_einvF := (AZ_huf_dx42_fq.x42e_einvF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl lo src dtb CTX).
  Notation WDL := [(DST, DST + dcap); (SPV - 456, SPV - 256)].
  Notation KOR mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y5 y7 y8 y9 y10 y11 y12 y13 y14 y23 y25 y28 y29 y30 : word) (w'0 w'15 w'16 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 w'38 w'39 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) w'15 w'16 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 (Z_to_bv 64 (DT + 4)) w'38 w'39) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        bytes_at bsegs mm' SRC src ->
        0 <= i0' <= i0 -> 0 <= i1' <= i1 -> 0 <= i2' <= i2 -> 0 <= i3' <= i3 ->
        o0 + 5 <= o0' <= q -> o1 + 5 <= o1' <= 2 * q -> o2 + 5 <= o2' <= 3 * q -> o3 + 5 <= o3' <= dcap -> OL <= o3' ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' ->
        evtF bsegs RNG POST (ST 0x9bc40 mm' (Z_to_bv 64 (SRC + i3')) y5 (Z_to_bv 64 (DST + o0')) y7 y8 y9 y10 y11 y12 y13 y14 (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (DT + 4)) c2' c0' y23 c3' y25 (Z_to_bv 64 (SRC + i1')) SB y28 y29 y30 c1')).
  Notation x42e_fi0 := (AZ_huf_dx42_fi0.x42e_fi0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).

  (* [comment removed for export] *)
  Lemma x42e_fi : forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x5 x7 x8 x9 x10 x11 x12 x13 x14 x23 x28 x29 x30 : word)
      (w0 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w39 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (64772)) w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (140088)) w39) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    KOR mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x9bd48 mm (Z_to_bv 64 (SRC + i3)) x5 (Z_to_bv 64 (DST + o0)) x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (DT + 4)) c2 c0 x23 c3 (Z_to_bv 64 (140088)) (Z_to_bv 64 (SRC + i1)) SB x28 x29 x30 c1).
  Proof using CTX X2OK NBOK ACTX TL11.
    induction r as [|r IH]; intros mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 x5 x7 x8 x9 x10 x11 x12 x13 x14 x23 x28 x29 x30
      w0 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w39
      MU WM MU0 WM0 MI OUT DTB FR AR SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN HLB0 HLB1 HLB2 HLB3 KOR; [exfalso; clear - HR; lia|].
    eapply (x42e_fi0 (S r) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3); try eassumption; try lia.
    - (* [comment removed for export] *)
      intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
        intros MU' WM' MU0' WM0' MI' OUT' DTB' FR' AR' SRCB' HI0' HI1' HI2' HI3' HO0' HO1' HO2' HO3' HL0' HL1' HL2' HL3' HOL' HR2.
      eapply (IH mb mm' q OL nd l1 l2 l3 i0' i1' i2' i3' o0' o1' o2' o3'); try eassumption; try lia.
      intros mm'' i0'' i1'' i2'' i3'' o0'' o1'' o2'' o3'' c0'' c1'' c2'' c3''; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
        intros MU'' WM'' MU0'' WM0'' MI'' OUT'' DTB'' FR'' AR'' SRCB'' GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 GOL GL0 GL1 GL2 GL3.
      eapply (KOR mm'' i0'' i1'' i2'' i3'' o0'' o1'' o2'' o3''); try eassumption; lia.
    - (* [comment removed for export] *)
      intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
        intros MU' WM' MU0' WM0' MI' OUT' DTB' FR' AR' SRCB' HI0' HI1' HI2' HI3' HO0' HO1' HO2' HO3' HL0' HL1' HL2' HL3' HOL'.
      eapply (KOR mm' i0' i1' i2' i3' o0' o1' o2' o3'); try eassumption; lia.
  Qed.
End DX42FIJ.
End CANSEC1.
