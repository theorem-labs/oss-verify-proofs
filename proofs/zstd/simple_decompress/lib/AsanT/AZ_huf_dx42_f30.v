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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_huf_dx42_fq AZ_huf_dx42_fa AZ_huf_dx42_fb AZ_huf_dx42_fc AZ_huf_dx42_fd AZ_huf_dx42_fe AZ_huf_dx42_f33 AZ_huf_dx42_f32 AZ_huf_dx42_f31.
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
Section DX42F30.
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
  Notation x42e_fz := (AZ_huf_dx42_fa.x42e_fz RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fu := (AZ_huf_dx42_fa.x42e_fu RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fp := (AZ_huf_dx42_fb.x42e_fp RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fpe := (AZ_huf_dx42_fb.x42e_fpe RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_f5 := (AZ_huf_dx42_fd.x42e_f5 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_fs := (AZ_huf_dx42_fe.x42e_fs RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_xok := (AZ_huf_dx42_fq.x42e_xok RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX ACTX).
  Notation x42e_err := (AZ_huf_dx42_fq.x42e_err RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX ACTX).
  Notation x42e_ret := (AZ_huf_dx42_fq.x42e_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX ACTX).
  Notation x42e_f3_1 := (AZ_huf_dx42_f31.x42e_f3_1 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation WDA := [(DST, DST + dcap); (SPV - 256, SPV - 104)].
  (* [comment removed for export] *)
  Lemma x42e_fw_0 : forall mm pe q nd j' l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (b0 b1 b2 b3 : word)
      (x1 x9 x10 x11 x13 x20 x21 x22 x23 x24 x25 x26 x28 x31 : word)
      (w0 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w39 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 (Z_to_bv 64 (140088)) w39) ->
    (ARGS mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) b0 b1 b2 b3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 <= pe <= dcap -> q = (dcap + 3) / 4 -> DST + 3 * q < DST + dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 1 <= bv_unsigned b0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 1 <= bv_unsigned b1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 1 <= bv_unsigned b2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 1 <= bv_unsigned b3 -> o0 <= j' <= pe ->
    evtF bsegs RNG POST (ST 0x9da68 mm x1 (Z_to_bv 64 (0)) (Z_to_bv 64 (q)) (Z_to_bv 64 (64)) (Z_to_bv 64 (DST + pe)) x9 x10 x11 (Z_to_bv 64 (DST + j')) x13 (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (8)) (Z_to_bv 64 (SPV + -224)) (Z_to_bv 64 (DST + o0)) x20 x21 x22 x23 x24 x25 x26 SB x28 (Z_to_bv 64 (2)) (Z_to_bv 64 (4)) x31).
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mm pe q nd j' l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 b0 b1 b2 b3
      x1 x9 x10 x11 x13 x20 x21 x22 x23 x24 x25 x26 x28 x31
      w0 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w39
      PV MU0 WM0 MI OUT DTB FR AR SRCB HND HPE HQ H3Q HL1 HL2 HL3 HLN HI0 HN0 HO0 HB0 HI1 HN1 HO1 HB1 HI2 HN2 HO2 HB2 HI3 HN3 HO3 HB3 HJ'. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    assert (PVD : disjoint_from WDA (SPV + -104) 104 /\ disjoint_from WDA lo (SPV + -576 - lo)) by (cbn [disjoint_from]; clear - R1 LO OS1; lia).
    destruct PVD as (PVD1 & PVD2).
    pose proof (munch_refl WDA mm) as MUA. pose proof (wmono_refl bsegs mm) as WMA.
    assert (KWF : (SPV - 256 + 152 <= SRC \/ SRC + n <= SPV - 256) /\ (SPV - 256 + 152 <= DT \/ DT + 16388 <= SPV - 256) /\
                  (DST + dcap <= SPV - 256 \/ SPV - 256 + 152 <= DST)) by (clear - OS1 OS2 OS3 LO; lia).
    destruct KWF as (KWF1 & KWF2 & KWF3).
    assert (KW1 : 0 <= pe <= 4294967296 /\ 0 <= o0 <= 4294967296 /\ 0 <= j' <= 4294967296 /\ 0 <= dcap - pe <= 4294967296 /\ 1 <= dcap <= 4294967296 /\
                  0 <= j' - o0 <= 4294967296 /\ 0 <= pe - j' <= 4294967296 /\ 4096 <= DST + j' <= 140737488355328)
      by (clear - HO0 HPE H3Q HQ R1 HJ'; lia); destruct KW1 as (KW1 & KW2 & KW3 & KW4 & KW5 & KW6 & KW7 & KW8).
    destruct (Z_lt_le_dec j' pe) as [ROOM|FULL].
    2: kcleanF; assert (HJE : j' = pe) by (clear - FULL HJ'; lia); subst j';
      kx_autoFLA (FR, AR) [KAApp (SPV - 256) 152] [0x9dc08; 0x9d164; 0x9dc10] 30%nat
           [KZRange pe 0 4294967296; KZRange o0 0 4294967296; KZRange (dcap - pe) 0 4294967296; KZRange dcap 1 4294967296;
            KZRange (pe - o0) 0 4294967296; KZRange (DST + pe) 4096 140737488355328;
            KZWr (SPV + -256) 152; KZDisj (SPV - 256) 152 SRC n; KZDisj (SPV - 256) 152 DT 16388; KZDisj DST dcap (SPV - 256) 152; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
           [(SPV + -576, 320); (SPV + -256, 152)] [(SPV - 576, 576)].
    1: dfacts MU0 UDST RDST RDSTS DSTA AW0 R1; kcleanF;
      assert (KR : 1 <= pe - j' <= 4294967296 /\ 1 <= dcap - j' <= 4294967296 /\ 4096 <= DST + j' <= 140737488355327)
        by (clear - ROOM HO0 HPE H3Q HQ R1 HJ'; lia); destruct KR as (KR1 & KR2 & KR3);
      kx_autoFLA (FR, AR) [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 256) 152] [0x9dc08; 0x9d164; 0x9dc10] 60%nat
           [KZRange (pe - j') 1 4294967296; KZRange (dcap - j') 1 4294967296; KZRange pe 0 4294967296; KZRange o0 0 4294967296; KZRange j' 0 4294967296;
            KZRange (dcap - pe) 0 4294967296; KZRange dcap 1 4294967296; KZRange (j' - o0) 0 4294967296; KZRange (DST + j') 4096 140737488355327;
            KZWr (SPV + -256) 152; KZDisj (SPV - 256) 152 SRC n; KZDisj (SPV - 256) 152 DT 16388; KZDisj DST dcap (SPV - 256) 152; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
           [(DT, 16388); (SPV + -576, 320); (SPV + -256, 152)] [(DT, 16388); (DST, dcap); (SPV - 576, 576)].
    all: aside.
    all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: trapsF.
    all: aclean.
    all: kx_mem.
    all: lclean2.
    (* [comment removed for export] *)
    all: lazymatch goal with MUA : munch WDA ?m1 ?m2, WMA : wmono bsegs ?m1 ?m2, PV' : X42PF ?m1 |- _ =>
           pose proof (x42pf_transport m1 m2 _ PV' MUA WMA PVD1 PVD2) as PV2; clear PV' MUA WMA;
           lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9dc08) _ _ _ _) =>
               eapply (x42e_err m2); eapply (x42e_einvF m2); first [exact PV2 | eassumption | reflexivity]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9dc10) _ _ _ _) =>
               eapply (x42e_xok m2); first [exact PV2 | eassumption | reflexivity | lia]
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9d164) _ _ _ _) =>
               eapply (x42e_f3_1 m2 pe q (-1 * DT + -5) l1 l2 l3); first [exact PV2 | eassumption | reflexivity | lia | idtac]
           end end.
  Qed.


  (* [comment removed for export] *)
  Lemma x42e_f3_0 : forall mm eprev q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (b0 b1 b2 b3 : word)
      (x1 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x26 x28 x31 : word)
      (w0 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w39 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 (Z_to_bv 64 (140088)) w39) ->
    (ARGS mm (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) b0 b1 b2 b3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 <= eprev <= dcap -> q = (dcap + 3) / 4 -> DST + 3 * q < DST + dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n -> 0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 1 <= bv_unsigned b0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 1 <= bv_unsigned b1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 1 <= bv_unsigned b2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 1 <= bv_unsigned b3 ->
    evtF bsegs RNG POST (ST 0x9d164 mm x1 (Z_to_bv 64 (0)) (Z_to_bv 64 (q)) (Z_to_bv 64 (64)) x8 x9 (Z_to_bv 64 (DST + eprev)) x11 x12 x13 (Z_to_bv 64 (SPV + -136)) (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (8)) x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (140088)) x26 SB x28 (Z_to_bv 64 (2)) (Z_to_bv 64 (4)) x31).
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mm eprev q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 b0 b1 b2 b3
      x1 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x26 x28 x31
      w0 w7 w8 w9 w10 w11 w12 w13 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w39
      PV MU0 WM0 MI OUT DTB FR AR SRCB HND HEP HQ H3Q HL1 HL2 HL3 HLN HI0 HN0 HO0 HB0 HI1 HN1 HO1 HB1 HI2 HN2 HO2 HB2 HI3 HN3 HO3 HB3. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS2 OS3 LO.
    sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS.
    dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kcleanF.
    assert (TBLC : tbl_in bsegs mm ACTZ_TBLB 64 1 0 0 63) by exact (actz_tblb mm MI).
    (* [comment removed for export] *)
    assert (PVD : disjoint_from WDA (SPV + -104) 104 /\ disjoint_from WDA lo (SPV + -576 - lo) /\
                  disjoint_from WD (SPV + -104) 104 /\ disjoint_from WD lo (SPV + -576 - lo) /\ disjoint_from WD (SPV + -256) 152)
      by (cbn [disjoint_from]; clear - R1 LO OS1; lia).
    destruct PVD as (PVD1 & PVD2 & PVD3 & PVD4 & PVD5).
    (* [comment removed for export] *)
    destruct (Z_lt_le_dec (dcap - eprev) q) as [SG|SG].
    all: lazymatch type of SG with
         | Z.lt _ _ =>
             assert (KF : (0 <= eprev <= 4294967296) /\ (0 <= q <= 4294967296) /\ (1 <= q - (dcap - eprev) <= 4294967296) /\ (1 <= dcap <= 4294967296) /\
                          (38 <= n <= 4294967296)  /\ (0 <= i0 <= 4294967296) /\ (8 <= n - i0 <= 4294967296) /\ (0 <= o0 <= 4294967296) /\
                          (0 <= dcap - o0 <= 4294967296) /\ (0 <= l1 <= 4294967296) /\ (0 <= l2 <= 4294967296) /\ (0 <= l3 <= 4294967296) /\
                          (0 <= dcap - eprev <= 4294967296))
               by (clear - HEP HQ H3Q HLN HL1 HL2 HL3 SG R1 R2 HI0 HN0 HO0; lia)
         | Z.le _ _ =>
             assert (KF : (0 <= eprev <= 4294967296) /\ (0 <= q <= 4294967296) /\ (0 <= dcap - eprev - q <= 4294967296) /\ (1 <= dcap <= 4294967296) /\
                          (38 <= n <= 4294967296)  /\ (0 <= i0 <= 4294967296) /\ (8 <= n - i0 <= 4294967296) /\ (0 <= o0 <= 4294967296) /\
                          (0 <= dcap - o0 <= 4294967296) /\ (0 <= l1 <= 4294967296) /\ (0 <= l2 <= 4294967296) /\ (0 <= l3 <= 4294967296) /\
                          (4096 <= DST + eprev + q <= 140737488355328))
               by (clear - HEP HQ H3Q HLN HL1 HL2 HL3 SG R1 R2 HI0 HN0 HO0; lia)
         end.
    all: pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KI & KN & KO & KO2 & KL1 & KL2 & KL3 & KF6).
    all: lazymatch type of KF3 with ?lo3 <= ?e3 <= ?hi3 => lazymatch type of KF6 with ?lo6 <= ?e6 <= ?hi6 =>
         kx_autoFLA (FR, AR) [KAUnp SRC n] [0x9dc08; 0x9d258; 0x9d754] 120%nat
           [KZRange eprev 0 4294967296; KZRange q 0 4294967296; KZRange e3 lo3 hi3; KZRange e6 lo6 hi6; KZRange dcap 1 4294967296; KZRange n 38 4294967296;
            KZRange i0 0 4294967296; KZRange (n - i0) 8 4294967296; KZRange o0 0 4294967296; KZRange (dcap - o0) 0 4294967296;
            KZRange l1 0 4294967296; KZRange l2 0 4294967296; KZRange l3 0 4294967296; KZRange (bv_unsigned b0) 1 18446744073709551615;
            KZTbl ACTZ_TBLB 64 1 0 0 63; KZImg 0x22338 0x22378; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296; KZAlign DT 4;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 576) 472; KZDisj DST dcap SRC n]
           [(SRC, n); (SPV + -576, 320); (SPV + -256, 152); (0x22338, 64)] [(SRC, n); (SPV - 576, 576)] end end.
    all: aside.
    all: clear KF KF1 KF2 KF3 KF4 KF5 KI KN KO KO2 KL1 KL2 KL3 KF6.
    all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: trapsF.
    all: aclean.
    (* [comment removed for export] *)
    all: try solve [exfalso; clear - SG KXBR; lia].
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9dc08) _ _ _ _) =>
             kx_mem; lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) =>
               eapply (x42e_err mq); eapply (x42e_einvF mq); first [exact PV | eassumption | reflexivity] end
         | |- _ => idtac
         end.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9d258) _ _ _ _) => kx_gen_regsF [1%nat; 9%nat; 11%nat; 13%nat; 23%nat; 25%nat; 26%nat; 28%nat; 31%nat]
         | |- _ => kx_gen_regsF [1%nat; 9%nat; 12%nat; 13%nat; 21%nat; 23%nat; 25%nat; 26%nat; 28%nat; 31%nat]
         end.
    all: intros; kx_ev_ranges.
    all: kx_mem.
    all: kx_sx3; kx_strip_mod.
    all: lclean3.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 ?S0) _ (Z_to_bv 64 ?P0) _ _ _ _ _ _ _ _ _ _ _ _ _ ?BC _ _ _ _ _ _ _) _ (Z_to_bv 64 ?pc) _ _ ?m1 _) =>
             replace S0 with (DST + (S0 - DST)) by (clear; lia);
             replace P0 with (SRC + i0) by (clear; lia);
             replace BC with (Z_to_bv 64 (bv_unsigned BC)) by (apply Z_to_bv_bv_unsigned);
             lazymatch BC with ev _ ?J => kx_erange KXW (EVar J); cbn [edenot] in KXW end;
             first [ constr_eq pc 643672;
                     lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?S5) _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
                       replace S5 with (DST + (S0 - DST) - 9) by (clear; lia) end;
                     try replace (Z_to_bv 64 (o0 + DST)) with (Z_to_bv 64 (DST + o0)) by (f_equal; lia);
                     eapply (x42e_f5 (Z.to_nat dcap) m1 m1 o0 (S0 - DST) o0 (-1 * DT + -5) i0)
                   | constr_eq pc 644948;
                     lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?A1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
                       replace A1 with (S0 - DST - o0) by (clear; lia) end;
                     eapply (x42e_fs m1 m1 o0 (S0 - DST) o0 (-1 * DT + -5) i0) ];
             lazymatch goal with
             | |- SINVA _ _ _ => unfold SINVA; clear - HI0 HN0 KXW; lia
             | |- 0 <= bv_unsigned _ <= 64 => clear - KXW; lia
             | |- 0 <= bv_unsigned _ <= 63 => clear - KXW; lia
             | |- forall _, _ => idtac
             | |- _ => lsideF
             end
         end.
    (* [comment removed for export] *)
    all: intros mm' j'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros MU' WM' MU0' WM0' MI' OUT' DTB' FR' SRCB' HJ'.
    all: lazymatch goal with
         | MU1 : munch WD ?m1 ?m2, WM1 : wmono bsegs ?m1 ?m2, AR1 : rw_cells bsegs ?m1 (SPV + -256) _, PV1 : X42PF ?m1 |- _ =>
           pose proof (rw_cells_transport bsegs _ m1 m2 _ _ AR1 MU1 WM1) as AR'; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in AR';
           specialize (AR' PVD5);
           pose proof (x42pf_transport m1 m2 _ PV1 MU1 WM1 PVD3 PVD4) as PV';
           clear AR1 PV1 MU1 WM1
         end.
    all: lazymatch goal with PV' : X42PF ?m2 |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?pe)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m2 _) =>
           eapply (x42e_fw_0 m2 pe q (-1 * DT + -5) j' l1 l2 l3); first [exact PV' | eassumption | reflexivity | lia | idtac] end.
  Qed.
End DX42F30.
End CANSEC1.
