(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 SepHide ZdWalkKit ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_hufkit42e AZ_hufkit42e2 AZ_huf_dx42_fq AZ_huf_dx42_fa AZ_huf_dx42_fb AZ_huf_dx42_fc AZ_huf_dx42_fd AZ_huf_dx42_fe AZ_huf_dx42_f33 AZ_huf_dx42_f32 AZ_huf_dx42_f31 AZ_huf_dx42_f30 AZ_huf_dx42_ff2 AZ_huf_dx42_fi0 AZ_huf_dx42_fij AZ_huf_dx42_ffo.
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
Section DX42FFV.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.
  Hypothesis ACTX : x42e_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -528)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 :=
    (rw_cells bsegs mm (SPV + -528) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17]).
  (* [comment removed for export] *)
  Notation ARGS mm ip0 ip1 ip2 ip3 op0 op1 op2 op3 b0 b1 b2 b3 adt ilow oend ie0 ie1 ie2 ie3 :=
    (rw_cells bsegs mm (SPV + -384) [C8 ip0; C8 ip1; C8 ip2; C8 ip3; C8 op0; C8 op1; C8 op2; C8 op3; C8 b0; C8 b1; C8 b2; C8 b3;
                                     C8 adt; C8 ilow; C8 oend; C8 ie0; C8 ie1; C8 ie2; C8 ie3]).
  (* [comment removed for export] *)
  Notation LOC mm e0 e1 e2 e3 p0 p1 p2 p3 i0 i1 i2 i3 c0 c1 c2 c3 :=
    (rw_cells bsegs mm (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3; C8 p0; C8 p1; C8 p2; C8 p3; C8 i0; C8 i1; C8 i2; C8 i3;
                                     C8 c0; C8 c1; C8 c2; C8 c3]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation WDF := [(DST, DST + dcap); (SPV - 528, SPV - 104)].
  Notation WD := [(DST, DST + dcap)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis XFA : fast_args_stmt3A.
  Hypothesis XMC : zd_memcpyZ_stmtA.
  Hypothesis X42B : huf_int_stmtA_at 0xa5d3c 2608 true.
  Hypothesis PRE0 : huf_dec_preA RNG m0 SPV lo 3136 DST dcap SRC n src.
  Hypothesis DTP0 : huf_dt_preA RNG m0 SPV lo DST dcap DT dtb.

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
    assert (RFR : rng RNG (SPV - 528) 528) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
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
    assert (FF : (DST + dcap <= SPV - 528 \/ SPV - 528 + 424 <= DST) /\ (SPV - 528 + 424 <= DT \/ DT + 16388 <= SPV - 528) /\
                 (SPV - 528 + 424 <= SRC \/ SRC + n <= SPV - 528) /\ (DST + dcap <= SPV - 528 \/ SPV - 528 + 528 <= DST))
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
           | H : 0 < dcap -> 0x629000 <= DST |- _ => clear H
           end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650940) _ _ _ _) => kx_trap_fast end).
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
           | H : 0 < dcap -> 0x629000 <= DST |- _ => clear H
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
  Ltac trapsF := try (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650624) _ _ _ _) => kx_trap_fast
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650836) _ _ _ _) => kx_trap_fast
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650876) _ _ _ _) => kx_trap_fast
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650924) _ _ _ _) => kx_trap_fast
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650932) _ _ _ _) => kx_trap_fast
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 650940) _ _ _ _) => kx_trap_fast
    end).

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
  Notation WDL := [(DST, DST + dcap); (SPV - 232, SPV - 104)].
  Notation x42e_ret := (AZ_huf_dx42_fq.x42e_ret RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX ACTX).
  Notation x42e_body_call := (AZ_huf_4x2.x42e_body_call X42B).
  Notation x42e_fo TL11 := (AZ_huf_dx42_ffo.x42e_fo RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11 XMC).

  (* [comment removed for export] *)
  Ltac asan_now MU0 WM0 AZS ART DSTA DHI LO KLO R1 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (AZmm : azstk RNG mm lo SPV)
      by (eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply aappW_cons_D; [exact DSTA | lia | exact AW0] | clear - LO; lia]);
    assert (ARTmm : art mm)
      by (eapply (art_transportW42 _ m0 mm ART MU0 WM0); constructor; [cbn [fst]; pose proof (DHI ltac:(lia)); lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]]);
    clear AW0.

  Ltac fixaddr H a := lazymatch type of H with rw_cells _ _ ?x _ => replace x with a in H by (cbn; lia) end.
  (* [comment removed for export] *)
  Ltac asan_nowF MU WM AZS ART LO KLO :=
    let mm := lazymatch type of MU with munch _ _ ?mm => mm end in
    let W := lazymatch type of MU with munch [(SPV - ?W, SPV)] _ _ => W end in
    assert (AZmm : azstk RNG mm lo SPV)
      by (eapply azstk_transport; [exact AZS | exact MU | exact WM | apply aappW_frameN; unfold KHIGH; clear - LO KLO; lia | clear - LO; lia]);
    assert (ARTmm : art mm) by (eapply (art_frameN m0 mm SPV W); [exact ART | exact MU | exact WM | unfold KHIGH; clear - LO KLO; lia]).
  Ltac mc_side SB2 A2 STK AZmm ARTmm RSTK RI ASTK LO GS :=
    first [ lazymatch goal with
            | |- evtF _ _ _ _ => idtac
            | |- bytes_at _ _ _ _ => exact SB2
            | |- length _ = _ => cbn [cells_bytes cbytes app]; rewrite !length_app, !length_le8; reflexivity
            | |- rw_cells _ _ _ _ => exact A2
            | |- mem_inv _ _ => assumption
            | |- stk _ _ _ _ => exact STK
            | |- app_blk _ _ => eapply (azstk_app _ _ _ _ _ _ AZmm); clear - LO; lia
            | |- aro _ _ _ _ => eapply (azstk_aro _ _ _ _ _ _ AZmm); [clear - LO; lia | clear; lia | clear - LO; lia | eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]]
            | |- ahull _ _ _ _ => eapply (azstk_ahull _ _ _ _ _ _ AZmm); clear - LO; lia
            | |- art _ => exact ARTmm
            | |- astk _ _ _ => exact ASTK
            | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
            | |- _ \/ _ => clear - LO GS; lia
            | |- _ => clear - LO GS; lia
            end
          | lazymatch goal with |- ?G => idtac "MCSIDE-LEFT:" G end ].

  (* [comment removed for export] *)
  Ltac pre_rng PRE0 :=
    let P := fresh "PREx" in pose proof PRE0 as P;
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ASTK0 & _ & _ & _);
    destruct ASTK0 as (KLO0 & RSTK & RI).

  (* [comment removed for export] *)
  Lemma x42e_ret0 : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    stk bsegs mm DST (DST + dcap) -> FRQ mm -> stk bsegs mm lo (SPV + -104) ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evtF bsegs RNG POST (ST 0x9ed3c mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (r)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX PRE0.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pre_rng PRE0.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 OUT FR STK MU WM MI HR.
    facts R1 R2 R3 TL LO SPB KLO.
    assert (RSTKf : rng RNG (SPV - 104) 104) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kclean.
    kx_autoFLA FR [KAApp (SPV - 104) 104] (@nil Z) 30%nat [KZRange SPV 17594333498432 140737488355328] [(SPV - 104, 104)] [(SPV - 104, 104)].
    all: aside.
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - destruct HR as [HR|[HR _]]; [left; exact HR | right; exact HR].
    - destruct HR as [->|[HR1 HR2]]; [clear - R1; lia|]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x42e_body_callG : forall mm junkA (x1 x5 x6 x7 x8 x9 x10 x11 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    munch [(SPV - 576, SPV)] m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    rw_cells bsegs mm (SPV + -528) [CB 424 junkA] -> FRQ mm -> stk bsegs mm lo (SPV + -528) ->
    evtF bsegs RNG POST (ST 0x9ed30 mm x1 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) x15 x16 x17 x18 (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX X2OK NBOK X42B PRE0 DTP0.
    pose proof CTX as CTX'. x42e_ctx_open CTX'.
    intros mm junkA x1 x5 x6 x7 x8 x9 x10 x11 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 MU0 WM0 MI1 FRA SV STK2.
    zstep. zstep. zstep.
    eapply evtF_cut;
    [ eapply (X42B RNG (Z_to_bv 64 0x9ed3c) gp tp);
      [ eapply (huf_dec_preA_call RNG m0 mm SPV 528 576 lo 3136); [exact PRE0 | clear; lia | reflexivity | clear; lia | exact MU0 | exact WM0 | exact MI1 | exact STK2]
      | eapply (huf_dt_preA_call RNG m0 mm SPV 528 576 lo); [exact DTP0 | unfold KHIGH; clear - KLO; lia | clear - LO; lia | clear; lia | exact MU0]
      | exact DT2 | exact TL | intros _; exact X2OK | exact NBOK ]
    | ].
    cbv beta. intros ms' P. unfold huf_dec_postA in P.
    destruct P as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & r & -> & MU2 & WM2 & MI2 & STK3 & OUT2 & RR & RB & _).
    replace (ret_pc (Z_to_bv 64 0x9ed3c)) with (Z_to_bv 64 0x9ed3c) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU2 WM2) as FRA2.
    cbn [disjoint_from fst snd app cells_size csize Nat.add length] in FRA2. specialize (FRA2 ltac:(clear - OS1 LO; lia)).
    pose proof (rw_cells_transport _ _ _ _ _ _ SV MU2 WM2) as SV2.
    cbn [disjoint_from fst snd app cells_size csize Nat.add length] in SV2. specialize (SV2 ltac:(clear - OS1 LO; lia)).
    pose proof (stk_of_rw_cells bsegs m2 _ _ FRA2) as SK. cbn [cells_size csize Nat.add] in SK. change (Z.of_nat 424) with 424 in SK.
    eapply (x42e_ret0 m2 r);
    [ exact OUT2 | exact SV2
    | replace (SPV + -104) with (SPV + -528 + 424) by (clear; lia); eapply (stk_merge bsegs m2 lo (SPV + -528)); [exact STK3 | exact SK | clear - LO; lia]
    | eapply munch_trans; [ eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside fst snd app]; intros; lia
                          | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside fst snd app]; intros; lia ]
    | eapply wmono_trans; [exact WM0 | exact WM2]
    | exact MI2
    | destruct RR as [RR|RR]; [left; exact RR | right; split; [exact RR | clear - RB; lia]] ].
  Qed.

  (* [comment removed for export] *)
  Lemma x42e_f0_no : forall mm r bs (e0 e1 e2 e3 lp0 lp1 lp2 lp3 li0 li1 li2 li3 lc0 lc1 lc2 lc3 : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : word),
    X42PF mm -> munch [(SPV - 576, SPV)] m0 mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) ->
    (FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) ->
    rw_cells bsegs mm (SPV + -384) [CB 152 bs] ->
    (LOC mm e0 e1 e2 e3 lp0 lp1 lp2 lp3 li0 li1 li2 li3 lc0 lc1 lc2 lc3) ->
    (r = 0 \/ zd_is_error r = true) -> 0 <= r < 2^64 ->
    evtF bsegs RNG POST (ST 0x9c6f4 mm x1 x5 x6 x7 (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (r)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX X2OK NBOK X42B PRE0 DTP0.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pre_rng PRE0.
    intros mm r bs e0 e1 e2 e3 lp0 lp1 lp2 lp3 li0 li1 li2 li3 lc0 lc1 lc2 lc3
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
      PV MUw MU0 WM0 MI OUT FR AR LC HR HRB.
    destruct PV as (SV & STK).
    facts R1 R2 R3 TL LO SPB KLO. kclean.
    assert (RFR : rng RNG (SPV - 528) 528) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    destruct HR as [HR0 | HRE].
    - subst r.
      kx_autoFLA FR (@nil kza) [0x9ed30; 0x9ed3c] 30%nat [KZRange SPV 17594333498432 140737488355328] [(SPV + -528, 144)] [(SPV - 528, 528)].
      all: aside.
      all: kx_mem.
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9ed30) _ _ ?mq _) =>
        assert (J : rw_cells bsegs mq (SPV + -528) ([C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15; C8 w16; C8 w17]
                  ++ ([CB 152 bs] ++ [C8 e0; C8 e1; C8 e2; C8 e3; C8 lp0; C8 lp1; C8 lp2; C8 lp3; C8 li0; C8 li1; C8 li2; C8 li3; C8 lc0; C8 lc1; C8 lc2; C8 lc3])));
        [ apply (proj2 (rw_cells_app bsegs _ (SPV + -528) _ _)); split; [eassumption|];
          lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -384) by (cbn; clear; lia) end;
          apply (proj2 (rw_cells_app bsegs _ (SPV + -384) [CB 152 bs] _)); split; [eassumption|];
          lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -232) by (cbn; clear; lia) end; eassumption
        | destruct (rw_cells_forget _ _ _ _ J) as [junkA JA]; cbn [cells_size csize Nat.add app] in JA; clear J;
          eapply (x42e_body_callG mq junkA); first [exact JA | eassumption] ] end.
    - assert (HERR : 18446744073709551497 <= r <= 18446744073709551615) by (unfold zd_is_error, ZE_maxCode in HRE; apply Z.ltb_lt in HRE; clear - HRE HRB; lia).
      kx_autoFLA FR (@nil kza) [0x9ed30; 0x9ed3c] 30%nat
          [KZRange r 18446744073709551497 18446744073709551615; KZRange SPV 17594333498432 140737488355328] [(SPV + -528, 144)] [(SPV - 528, 528)].
      all: aside.
      all: kx_mem.
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9ed3c) _ _ ?mq _) =>
        eapply (x42e_ret0 mq r);
        [ eassumption | eassumption
        | lazymatch goal with F' : rw_cells bsegs mq (SPV + -528) _, A' : rw_cells bsegs mq (SPV + -384) _, L' : rw_cells bsegs mq (SPV + -232) _, S' : stk bsegs mq lo (SPV + -528) |- _ =>
            pose proof (stk_of_rw_cells bsegs mq _ _ F') as K1; pose proof (stk_of_rw_cells bsegs mq _ _ A') as K2; pose proof (stk_of_rw_cells bsegs mq _ _ L') as K3;
            cbn [cells_size csize Nat.add] in K1, K2, K3;
            change (Z.of_nat 144) with 144 in K1; change (Z.of_nat 152) with 152 in K2; change (Z.of_nat 128) with 128 in K3;
            replace (SPV + -528 + 144) with (SPV + -384) in K1 by (clear; lia); replace (SPV + -384 + 152) with (SPV + -232) in K2 by (clear; lia);
            replace (SPV + -232 + 128) with (SPV + -104) in K3 by (clear; lia);
            eapply (stk_merge bsegs mq lo (SPV + -232)); [|exact K3|clear - LO; lia];
            eapply (stk_merge bsegs mq lo (SPV + -384)); [|exact K2|clear - LO; lia];
            eapply (stk_merge bsegs mq lo (SPV + -528)); [exact S'|exact K1|clear - LO; lia] end
        | eassumption | eassumption | eassumption
        | right; split; [exact HRE | clear - HRB; lia] ] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42e_f0b : forall mm l1 l2 l3 (b0 b1 b2 b3 : word) (e0 e1 e2 e3 lp0 lp1 lp2 lp3 li0 li1 li2 li3 lc0 lc1 lc2 lc3 : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w9 w10 w11 w12 w13 w14 w15 w17 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb -> bytes_at bsegs mm SRC src ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (DT + 4)) w17) ->
    rw_cells bsegs mm (SPV + -384) (fast_args_cells DST dcap SRC n DT l1 l2 l3 b0 b1 b2 b3) ->
    (LOC mm e0 e1 e2 e3 lp0 lp1 lp2 lp3 li0 li1 li2 li3 lc0 lc1 lc2 lc3) ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n -> DST + 3 * ((dcap + 3) / 4) < DST + dcap -> tl = 11 ->
    LBW 8 b0 -> LBW 8 b1 -> LBW 8 b2 -> LBW 8 b3 ->
    evtF bsegs RNG POST (ST 0x9c6f4 mm x1 x5 x6 x7 (Z_to_bv 64 (DT)) (Z_to_bv 64 (n)) (Z_to_bv 64 (1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) x21 x22 SB x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX X2OK NBOK ACTX XMC.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mm l1 l2 l3 b0 b1 b2 b3 e0 e1 e2 e3 lp0 lp1 lp2 lp3 li0 li1 li2 li3 lc0 lc1 lc2 lc3
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w1 w2 w9 w10 w11 w12 w13 w14 w15 w17
      PV MU0 WM0 MI OUT DTB SRCB FR AR LC HL1 HL2 HL3 HLN H3Q TL11 HLB0 HLB1 HLB2 HLB3.
    destruct PV as (SV & STK).
    unfold fast_args_cells in AR. cbv zeta in AR.
    facts R1 R2 R3 TL LO SPB KLO.
    remember ((dcap + 3) / 4) as q eqn:HQ.
    assert (KF : (0 <= q <= 4294967296) /\ (8 <= l1 <= 4294967296) /\ (8 <= l2 <= 4294967296) /\ (8 <= l3 <= 4294967296) /\ (38 <= n <= 4294967296) /\
                 (1 <= dcap <= 4294967296) /\ (3 * q < dcap)) by (clear - HL1 HL2 HL3 HLN H3Q HQ R1 R2; subst q; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7).
    replace (SRC + 6 + l1 - 8) with (SRC + (l1 - 2)) in AR by (clear; lia).
    replace (SRC + 6 + l1 + l2 - 8) with (SRC + (l1 + l2 - 2)) in AR by (clear; lia).
    replace (SRC + 6 + l1 + l2 + l3 - 8) with (SRC + (l1 + l2 + l3 - 2)) in AR by (clear; lia).
    replace (SRC + n - 8) with (SRC + (n - 8)) in AR by (clear; lia).
    assert (ASTK' : astk RNG lo (SPV + -528)) by (split; [exact KLO | split; [eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia] | exact RI]]).
    assert (RFR : rng RNG (SPV - 528) 528) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (DP : 0 < dcap) by (clear - KF6; lia).
    (* [comment removed for export] *)
    kx_autoFLA (FR, AR) [KAApp (SPV - 528) 424] [0x538a8; 0x9ed20; 0x9ed80; 0x9ee54; 0x9ee7c; 0x9eeac; 0x9eeb4; 0x9eebc] 30%nat
      [KZRange SPV 17594333498432 140737488355328; KZRange DT 4096 140737488338940; KZRange SRC 4096 140737488355328; KZWr (SPV + -528) 144]
      [(SPV + -528, 144); (SPV + -384, 152)] [(SPV - 528, 528)].
    all: aside.
    all: trapsF.
    all: kx_mem.
    (* [comment removed for export] *)
    asan_now MU0 WM0 AZS ART DSTA DHI LO KLO R1.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] _)) in AR.
    destruct AR as [AR1 AR']. fixaddr AR' (SPV + -320).
    apply (proj1 (rw_cells_app bsegs _ _ [C8 b0; C8 b1; C8 b2; C8 b3] _)) in AR'.
    destruct AR' as [AR2 AR3]. fixaddr AR3 (SPV + -288).
    pose proof (proj2 (proj1 AR2)) as SBb.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 e0; C8 e1; C8 e2; C8 e3; C8 lp0; C8 lp1; C8 lp2; C8 lp3; C8 li0; C8 li1; C8 li2; C8 li3] _)) in LC.
    destruct LC as [LC1 LC4]. fixaddr LC4 (SPV + -136).
    destruct (rw_cells_forget _ _ _ _ LC4) as [jb4 D4]. cbn [cells_size csize Nat.add] in D4. clear LC4.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -528) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK1 end.
    call (XMC RNG (SPV + -136) (SPV + -320) 32 (SPV + -528)).
    all: mc_side SBb D4 STK1 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK1. clear AZmm ARTmm; try clear SBb; try clear D4; try clear jb4.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -136) [CB _ _] |- _ =>
      assert (LCb : rw_cells bsegs m (SPV + -136) [C8 b0; C8 b1; C8 b2; C8 b3])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    try clear POST POST0 POST1.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- _ => asan_now MU WM AZS ART DSTA DHI LO KLO R1 end.
    zstep. zstep. zstep. zstep. kx_mkR_fold.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 _; C8 _; C8 _; C8 _] _)) in AR1. destruct AR1 as [AR0 AR1]. fixaddr AR1 (SPV + -352).
    pose proof (proj2 (proj1 AR0)) as SBi.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 e0; C8 e1; C8 e2; C8 e3; C8 lp0; C8 lp1; C8 lp2; C8 lp3] _)) in LC1. destruct LC1 as [LC1 LC3]. fixaddr LC3 (SPV + -168).
    destruct (rw_cells_forget _ _ _ _ LC3) as [jb3 D3]. cbn [cells_size csize Nat.add] in D3. clear LC3.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -528) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK2 end.
    call (XMC RNG (SPV + -168) (SPV + -384) 32 (SPV + -528)).
    all: mc_side SBi D3 STK2 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK2. clear AZmm ARTmm; try clear SBi; try clear D3; try clear jb3.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -168) [CB _ _] |- _ =>
      assert (LCi : rw_cells bsegs m (SPV + -168) [C8 (Z_to_bv 64 (SRC + (l1 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))); C8 (Z_to_bv 64 (SRC + (n - 8)))])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    try clear POST POST0 POST1.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- _ => asan_now MU WM AZS ART DSTA DHI LO KLO R1 end.
    zstep. zstep. zstep. zstep. zstep. kx_mkR_fold.
    pose proof (proj2 (proj1 AR1)) as SBo.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 e0; C8 e1; C8 e2; C8 e3] _)) in LC1. destruct LC1 as [LC1 LC2]. fixaddr LC2 (SPV + -200).
    destruct (rw_cells_forget _ _ _ _ LC2) as [jb2 D2]. cbn [cells_size csize Nat.add] in D2. clear LC2.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -528) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK3 end.
    call (XMC RNG (SPV + -200) (SPV + -352) 32 (SPV + -528)).
    all: mc_side SBo D2 STK3 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK3. clear AZmm ARTmm; try clear SBo; try clear D2; try clear jb2.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -200) [CB _ _] |- _ =>
      assert (LCo : rw_cells bsegs m (SPV + -200) [C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + q)); C8 (Z_to_bv 64 (DST + 2 * q)); C8 (Z_to_bv 64 (DST + 3 * q))])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    try clear POST POST0 POST1. try clear KXK KXA KXRD; try clear KXE.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => assert (AR : rw_cells bsegs m (SPV + -384)
      ([C8 (Z_to_bv 64 (SRC + (l1 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))); C8 (Z_to_bv 64 (SRC + (n - 8)))]
       ++ ([C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + q)); C8 (Z_to_bv 64 (DST + 2 * q)); C8 (Z_to_bv 64 (DST + 3 * q))]
       ++ ([C8 b0; C8 b1; C8 b2; C8 b3]
       ++ [C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 SRC); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (SRC + 6)); C8 (Z_to_bv 64 (SRC + 6 + l1)); C8 (Z_to_bv 64 (SRC + 6 + l1 + l2)); C8 (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))])))) end.
    { apply (proj2 (rw_cells_app bsegs _ (SPV + -384) _ _)). split; [exact AR0|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -352) by (cbn; clear; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -352) _ _)). split; [exact AR1|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -320) by (cbn; clear; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -320) [C8 b0; C8 b1; C8 b2; C8 b3] _)). split; [exact AR2|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -288) by (cbn; clear; lia) end. exact AR3. }
    cbn [app] in AR. clear AR0 AR1 AR2 AR3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => assert (LC : rw_cells bsegs m (SPV + -232)
      ([C8 e0; C8 e1; C8 e2; C8 e3]
       ++ ([C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + q)); C8 (Z_to_bv 64 (DST + 2 * q)); C8 (Z_to_bv 64 (DST + 3 * q))]
       ++ ([C8 (Z_to_bv 64 (SRC + (l1 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 - 2))); C8 (Z_to_bv 64 (SRC + (l1 + l2 + l3 - 2))); C8 (Z_to_bv 64 (SRC + (n - 8)))]
       ++ [C8 b0; C8 b1; C8 b2; C8 b3])))) end.
    { apply (proj2 (rw_cells_app bsegs _ (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3] _)). split; [exact LC1|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -200) by (cbn; clear; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -200) _ _)). split; [exact LCo|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -168) by (cbn; clear; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -168) _ _)). split; [exact LCi|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -136) by (cbn; clear; lia) end. exact LCb. }
    cbn [app] in LC. clear LC1 LCo LCi LCb.
    try clear POST; try clear POST0; try clear POST1.
    (* [comment removed for export] *)
    kcleanF.
    kx_autoFLA (FR, AR, LC) [KAApp (SPV - 528) 424] [0x9c848; 0x9ed80; 0x9ee54; 0x9ee7c; 0x9eeac; 0x9eeb4; 0x9eebc] 100%nat
      [KZRange q 0 4294967296; KZRange l1 8 4294967296; KZRange l2 8 4294967296; KZRange l3 8 4294967296; KZRange n 38 4294967296; KZRange dcap 1 4294967296;
       KZRange DST 4096 140737488355328; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZRange SPV 17594333498432 140737488355328; KZWr (SPV + -528) 144; KZWr (SPV + -232) 128; KZImg 0x103a8 0x103b0]
      [(SPV + -528, 144); (SPV + -384, 152); (SPV + -232, 128); (0x103a8, 8)] [(SPV - 528, 528)].
    all: aside.
    all: trapsF.
    all: kx_mem.
    all: kx_strip_mod.
    all: lazymatch goal with F' : rw_cells bsegs ?mq (SPV + -528) _, L' : rw_cells bsegs ?mq (SPV + -232) _ |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c848) _ _ ?mq _) =>
      try replace (dcap + DST) with (DST + dcap) in F' by (clear; lia);
      replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) in L' by (f_equal; clear; lia);
      replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; clear; lia);
      try replace (SRC + (l1 + (l2 + l3)) + -2) with (SRC + (l1 + l2 + l3 - 2)) by (clear; lia);
      try replace (n + SRC + -8) with (SRC + (n - 8)) by (clear; lia);
      try replace (SRC + l1 + -2) with (SRC + (l1 - 2)) by (clear; lia);
      try replace (SRC + (l1 + l2) + -2) with (SRC + (l1 + l2 - 2)) by (clear; lia) end.
    all: lazymatch goal with SV' : rw_cells bsegs ?mq (SPV + -104) _, PC' : stk bsegs ?mq lo (SPV + -528) |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9c848) _ _ ?mq _) =>
      eapply ((x42e_fo TL11) (Z.to_nat (dcap - 3 * q + 1)) mq q (-1 * DT + -5) l1 l2 l3 (l1 - 2) (l1 + l2 - 2) (l1 + l2 + l3 - 2) (n - 8) 0 q (2 * q) (3 * q));
      first [ split; [exact SV' | exact PC'] | eassumption | reflexivity
            | rewrite Z2Nat.id by (clear - KF7; lia); clear - KF7; lia
            | clear - KF1 KF2 KF3 KF4 KF5 KF6 KF7 HQ H3Q HLN R1; lia ] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x42e_f0 : forall (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word) (flags : word) (m1 : amem) (junk : list byte),
    munch [(SPV - 528, SPV)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SPV + -528) (CB 424 junk :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) -> stk bsegs m1 lo (SPV + -528) ->
    stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb -> 0 < n ->
    evtF bsegs RNG POST (ST 0x9c664 m1 ra x5 x6 x7 s0 s1 (Z_to_bv 64 (DST)) (Z_to_bv 64 (0)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) flags x16 x17 s2 (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31).
  Proof using CTX X2OK NBOK ACTX XFA XMC X42B PRE0 DTP0.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros x5 x6 x7 x16 x17 x28 x29 x30 x31 flags m1 junk MU01 WM01 MI1 FRALL STK1 OUT0 SRCB0 DTB0 NPOS.
    facts R1 R2 R3 TL LO SPB KLO.
    assert (OUT : stk bsegs m1 DST (DST + dcap)) by (eapply stk_transport_disjoint; [exact OUT0 | exact MU01 | exact WM01 | cbn [disjoint_from fst snd]; clear - OS1 LO; lia]).
    assert (SRCB : bytes_at bsegs m1 SRC src) by (eapply bytes_at_transport; [exact SRCB0 | exact MU01 | cbn [disjoint_from fst snd]; clear - OS2 LO SL; lia]).
    assert (DTB : bytes_at bsegs m1 DT dtb) by (eapply bytes_at_transport; [exact DTB0 | exact MU01 | cbn [disjoint_from fst snd]; clear - OS3 LO DL; lia]).
    clear OUT0 SRCB0 DTB0.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs m1 _ [] 424 junk _ [144; 152; 128]%nat) in FRALL; [| reflexivity]. cbn [mk_CB_cells app] in FRALL.
    apply (proj1 (rw_cells_app bsegs _ _ [CB 144 _] _)) in FRALL. destruct FRALL as [FRb FRALL]. fixaddr FRALL (SPV + -384).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 152 _] _)) in FRALL. destruct FRALL as [A2 FRALL]. fixaddr FRALL (SPV + -232).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 128 _] _)) in FRALL. destruct FRALL as [LCb SV]. fixaddr SV (SPV + -104).
    destruct (e42_cb144_as_c8s _ _ _ FRb) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & FR). clear FRb.
    destruct (e42_cb128_as_c8s _ _ _ LCb) as (e0 & e1 & e2 & e3 & lp0 & lp1 & lp2 & lp3 & li0 & li1 & li2 & li3 & lc0 & lc1 & lc2 & lc3 & LC). clear LCb.
    (* [comment removed for export] *)
    asan_nowF MU01 WM01 AZS ART LO KLO.
    pose proof ARTmm as ART1. destruct ART1 as (GOT & RIC & SHB & INI & LAY & REAL).
    assert (UDT1 : unpoisoned m1 DT (DT + 16388)) by (eapply unpoisoned_frameN; [exact UDT | exact MU01 | unfold KHIGH; clear - LO KLO; lia | clear - R3; lia | unfold KEND; clear - R3; lia]).
    assert (USRC1 : unpoisoned m1 SRC (SRC + n)) by (eapply unpoisoned_frameN; [exact USRC | exact MU01 | unfold KHIGH; clear - LO KLO; lia | clear - R2; lia | unfold KEND; clear - R2; lia]).
    assert (RFR : rng RNG (SPV - 528) 528) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (ASTK' : astk RNG lo (SPV + -528)) by (split; [exact KLO | split; [eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia] | exact RI]]).
    assert (MUw : munch [(SPV - 576, SPV)] m0 m1) by (eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
    assert (MU0 : munch W0 m0 m1) by (eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
    pose proof WM01 as WM0. clear MU01.
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz.
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDT1 ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz.
    (* [comment removed for export] *)
    destruct (Z.eq_dec dcap 0) as [DC0|DC1].
    - kx_autoFLA (FR, GOT, SHB) [KAApp (SPV - 528) 424] [0xad708; 0x9ed80; 0x9ee54; 0x9ee7c; 0x9eeac; 0x9eeb4; 0x9eebc] 40%nat
        [KZRange dcap 0 0; KZRange DST 4096 140737488355327; KZRange DT 4096 140737488338940;
         KZRange SRC 4096 140737488355328; KZRange n 1 4294967296; KZRange (SRC + n) 4096 140737488355328; KZRange SPV 17594333498432 140737488355328;
         KZWr (SPV + -528) 144; KZDisj (SPV - 528) 144 DT 16388; KZDisj (SPV - 528) 144 SRC n; KZDisj DST dcap (SPV - 528) 424]
        [(SPV + -528, 144)] [(SPV - 528, 528)].
      all: aside.
      all: trapsF.
      all: kx_mem.
      all: try (replace (Z_to_bv 64 0) with (Z_to_bv 64 dcap) by (f_equal; clear - DC0; lia)).

      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad708) _ _ ?mq _) => rename mq into mc end.
      clear AZmm ARTmm UDT1 USRC1 UDTz RDTz; try clear KXK KXA KXRD; try clear KXE.
      clear GOT RIC SHB INI LAY REAL.
      lazymatch goal with D : bytes_at bsegs mc DT dtb |- _ =>
        assert (DTB4 : bytes_at bsegs mc DT (firstn 4 dtb)) by (pose proof D as D'; rewrite <- (firstn_skipn 4 dtb) in D'; apply bytes_at_app in D'; exact (proj1 D'));
        assert (DTHL : Z.of_nat (length (firstn 4 dtb)) = 4) by (rewrite firstn_length; clear - DL; lia) end.
      asan_nowF MUw WM0 AZS ART LO KLO.
      assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
      assert (UDTc : unpoisoned mc DT (DT + 16388))
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
            | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                 | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]).
      sfacts0 MU0 USRC DSTA AW0 R1 R2 RSRCS.
      assert (AROS : aro RNG mc SRC n) by (split; [exact USRCc | split; [exact RSRC | exact RSRCS]]).
      assert (AROD : aro RNG mc DT 4) by (eapply aro_sub; [split; [exact UDTc | split; [exact RDT | exact RDTS]] | clear; lia | clear; lia | clear - R3; lia]).
      assert (RBA : rng RNG (SPV + -384) 152) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
      assert (AROA : aro RNG mc (SPV + -384) 152) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBA]).
      assert (APA : app_blk (SPV + -384) (SPV + -384 + 152)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
      assert (ARA : (SPV + -384) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
      assert (NUMS : (4096 <= lo) /\ (lo <= SPV + -528 - 48) /\ (SPV + -528 < 2^47) /\ (4096 <= SPV + -384) /\ (SPV + -384 + 152 < 2^47) /\
                     (SPV + -384 + 152 <= lo \/ SPV + -528 <= SPV + -384) /\ (4096 <= SRC) /\ (SRC + n < 2^47) /\ (SRC + n <= lo \/ SPV + -528 <= SRC) /\ (n < 2^32) /\
                     (4096 <= DT) /\ (DT + 4 < 2^47) /\ (DT + 4 <= lo \/ SPV + -528 <= DT) /\ (4096 <= DST) /\ (0 <= dcap < 2^32) /\ (DST + dcap < 2^47) /\
                     (SPV + -384 + 152 <= SRC \/ SRC + n <= SPV + -384) /\ (SPV + -384 + 152 <= DT \/ DT + 4 <= SPV + -384))
        by (clear - LO SPB R1 R2 R3 OS2 OS3; lia).
      destruct NUMS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18).
      clear USRCc UDTc AW0 RBA RSRCz USRCz.
      hide_all_disj. unfold hidden in OS1, OS2, OS3.
      lazymatch goal with MI' : mem_inv bsegs mc, STK' : stk bsegs mc lo (SPV + -528), AR' : rw_cells bsegs mc (SPV + -384) [CB 152 _], SRCB' : bytes_at bsegs mc SRC src |- _ =>
      eapply evtF_cut;
        [ eapply (XFA RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc (SPV + -528) (SPV + -384) DST dcap SRC n DT lo src (firstn 4 dtb) _);
          [ exact MI' | exact STK' | exact Q1 | exact Q2 | exact Q3 | exact AR' | exact ARA | exact DTA | exact SRCB' | exact SL | exact DTB4 | exact DTHL
          | exact Q4 | exact Q5 | exact Q6 | exact Q7 | exact Q8 | exact Q9 | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15 | exact Q16
          | exact Q17 | exact Q18 | exact APA | exact AROA | exact AROS | exact AROD | exact ARTmm | exact ASTK' ]
        | clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 Q18 APA AROA AROS AROD ARTmm AR' STK' DTB4 DTHL AZmm;
          unfold fast_args_post3A; post_call bsegs mc ] end.
      unhide.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mm2 end.
      lazymatch goal with P : (_ /\ _) \/ (_ /\ _) |- _ =>
        destruct P as [(HR & l1 & l2 & l3 & b0 & b1 & b2 & b3 & HL1 & HL2 & HL3 & HLN & HQ3 & AR2 & HLOG & NZ0 & NZ1 & NZ2 & NZ3) | (HR & HRB & bs & AR2)] end.
      + (* [comment removed for export] *)
        lazymatch type of HR with ?rr = 1 => subst rr end.
        first [ exfalso; clear - HQ3 DC0 R1; lia
              | assert (TL11 : tl = 11) by
                  (clear - HLOG DT2 TL; rewrite nth_error_firstn in HLOG by lia; rewrite DT2 in HLOG;
                   apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in HLOG;
                   change ((2 <? 4)%nat) with true in HLOG; cbn beta iota in HLOG;
                   rewrite !Z_to_bv_unsigned, !bv_wrap_small in HLOG by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia); lia);
                lazymatch goal with SV' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -528) |- _ =>
                  eapply (x42e_f0b mm2 l1 l2 l3 b0 b1 b2 b3);
                  first [ split; [exact SV' | exact PC'] | eassumption | exact TL11 | unfold LBW; apply lb_of_mod512; assumption | idtac ] end ].
      + (* [comment removed for export] *)
        lazymatch goal with SV' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -528) |- _ =>
          eapply (x42e_f0_no mm2 _ bs); first [ split; [exact SV' | exact PC'] | eassumption | exact HR | exact HRB ] end.

    - kx_autoFLA (FR, GOT, SHB) [KAApp (SPV - 528) 424] [0xad708; 0x9ed80; 0x9ee54; 0x9ee7c; 0x9eeac; 0x9eeb4; 0x9eebc] 40%nat
        [KZRange dcap 1 4294967295; KZRange DST 4096 140737488355327; KZRange (DST + dcap) 4097 140737488355327; KZRange DT 4096 140737488338940;
         KZRange SRC 4096 140737488355328; KZRange n 1 4294967296; KZRange (SRC + n) 4096 140737488355328; KZRange SPV 17594333498432 140737488355328;
         KZWr (SPV + -528) 144; KZDisj (SPV - 528) 144 DT 16388; KZDisj (SPV - 528) 144 SRC n; KZDisj DST dcap (SPV - 528) 424]
        [(SPV + -528, 144)] [(SPV - 528, 528)].
      all: aside.
      all: trapsF.
      all: kx_mem.

      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xad708) _ _ ?mq _) => rename mq into mc end.
      clear AZmm ARTmm UDT1 USRC1 UDTz RDTz; try clear KXK KXA KXRD; try clear KXE.
      clear GOT RIC SHB INI LAY REAL.
      lazymatch goal with D : bytes_at bsegs mc DT dtb |- _ =>
        assert (DTB4 : bytes_at bsegs mc DT (firstn 4 dtb)) by (pose proof D as D'; rewrite <- (firstn_skipn 4 dtb) in D'; apply bytes_at_app in D'; exact (proj1 D'));
        assert (DTHL : Z.of_nat (length (firstn 4 dtb)) = 4) by (rewrite firstn_length; clear - DL; lia) end.
      asan_nowF MUw WM0 AZS ART LO KLO.
      assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
      assert (UDTc : unpoisoned mc DT (DT + 16388))
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
            | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                 | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]).
      sfacts0 MU0 USRC DSTA AW0 R1 R2 RSRCS.
      assert (AROS : aro RNG mc SRC n) by (split; [exact USRCc | split; [exact RSRC | exact RSRCS]]).
      assert (AROD : aro RNG mc DT 4) by (eapply aro_sub; [split; [exact UDTc | split; [exact RDT | exact RDTS]] | clear; lia | clear; lia | clear - R3; lia]).
      assert (RBA : rng RNG (SPV + -384) 152) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
      assert (AROA : aro RNG mc (SPV + -384) 152) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBA]).
      assert (APA : app_blk (SPV + -384) (SPV + -384 + 152)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
      assert (ARA : (SPV + -384) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
      assert (NUMS : (4096 <= lo) /\ (lo <= SPV + -528 - 48) /\ (SPV + -528 < 2^47) /\ (4096 <= SPV + -384) /\ (SPV + -384 + 152 < 2^47) /\
                     (SPV + -384 + 152 <= lo \/ SPV + -528 <= SPV + -384) /\ (4096 <= SRC) /\ (SRC + n < 2^47) /\ (SRC + n <= lo \/ SPV + -528 <= SRC) /\ (n < 2^32) /\
                     (4096 <= DT) /\ (DT + 4 < 2^47) /\ (DT + 4 <= lo \/ SPV + -528 <= DT) /\ (4096 <= DST) /\ (0 <= dcap < 2^32) /\ (DST + dcap < 2^47) /\
                     (SPV + -384 + 152 <= SRC \/ SRC + n <= SPV + -384) /\ (SPV + -384 + 152 <= DT \/ DT + 4 <= SPV + -384))
        by (clear - LO SPB R1 R2 R3 OS2 OS3; lia).
      destruct NUMS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18).
      clear USRCc UDTc AW0 RBA RSRCz USRCz.
      hide_all_disj. unfold hidden in OS1, OS2, OS3.
      lazymatch goal with MI' : mem_inv bsegs mc, STK' : stk bsegs mc lo (SPV + -528), AR' : rw_cells bsegs mc (SPV + -384) [CB 152 _], SRCB' : bytes_at bsegs mc SRC src |- _ =>
      eapply evtF_cut;
        [ eapply (XFA RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc (SPV + -528) (SPV + -384) DST dcap SRC n DT lo src (firstn 4 dtb) _);
          [ exact MI' | exact STK' | exact Q1 | exact Q2 | exact Q3 | exact AR' | exact ARA | exact DTA | exact SRCB' | exact SL | exact DTB4 | exact DTHL
          | exact Q4 | exact Q5 | exact Q6 | exact Q7 | exact Q8 | exact Q9 | exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15 | exact Q16
          | exact Q17 | exact Q18 | exact APA | exact AROA | exact AROS | exact AROD | exact ARTmm | exact ASTK' ]
        | clear Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 Q18 APA AROA AROS AROD ARTmm AR' STK' DTB4 DTHL AZmm;
          unfold fast_args_post3A; post_call bsegs mc ] end.
      unhide.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mm2 end.
      lazymatch goal with P : (_ /\ _) \/ (_ /\ _) |- _ =>
        destruct P as [(HR & l1 & l2 & l3 & b0 & b1 & b2 & b3 & HL1 & HL2 & HL3 & HLN & HQ3 & AR2 & HLOG & NZ0 & NZ1 & NZ2 & NZ3) | (HR & HRB & bs & AR2)] end.
      + (* [comment removed for export] *)
        lazymatch type of HR with ?rr = 1 => subst rr end.
        first [ exfalso; clear - HQ3 DC0 R1; lia
              | assert (TL11 : tl = 11) by
                  (clear - HLOG DT2 TL; rewrite nth_error_firstn in HLOG by lia; rewrite DT2 in HLOG;
                   apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in HLOG;
                   change ((2 <? 4)%nat) with true in HLOG; cbn beta iota in HLOG;
                   rewrite !Z_to_bv_unsigned, !bv_wrap_small in HLOG by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia); lia);
                lazymatch goal with SV' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -528) |- _ =>
                  eapply (x42e_f0b mm2 l1 l2 l3 b0 b1 b2 b3);
                  first [ split; [exact SV' | exact PC'] | eassumption | exact TL11 | unfold LBW; apply lb_of_mod512; assumption | idtac ] end ].
      + (* [comment removed for export] *)
        lazymatch goal with SV' : rw_cells bsegs mm2 (SPV + -104) _, PC' : stk bsegs mm2 lo (SPV + -528) |- _ =>
          eapply (x42e_f0_no mm2 _ bs); first [ split; [exact SV' | exact PC'] | eassumption | exact HR | exact HRB ] end.

  Qed.
End DX42FFV.
End CANSEC1.
