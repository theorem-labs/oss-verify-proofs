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
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_huf_dx42_fq AZ_huf_dx42_fa AZ_huf_dx42_fb AZ_huf_dx42_fc AZ_huf_dx42_fd AZ_huf_dx42_fe AZ_huf_dx42_f33 AZ_huf_dx42_f32 AZ_huf_dx42_f31 AZ_huf_dx42_f30.
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
Section DX42FF2.
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
  Hypothesis TL11 : tl = 11.
  Hypothesis XMC : zd_memcpyZ_stmtA.

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
  Notation x42e_f3_0 := (AZ_huf_dx42_f30.x42e_f3_0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).

  (* [comment removed for export] *)
  Ltac asan_now MU0 WM0 AZS ART DSTA DHI LO KLO R1 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (AZmm : azstk RNG mm lo SPV)
      by (eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply aappW_cons_D; [exact DSTA | lia | exact AW0] | clear - LO; lia]);
    assert (ARTmm : art mm)
      by (eapply (art_transportW42 _ m0 mm ART MU0 WM0); constructor; [cbn [fst]; pose proof (DHI ltac:(lia)); lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]]);
    clear AW0.

  (* [comment removed for export] *)
  Ltac fixaddr H a := lazymatch type of H with rw_cells _ _ ?x _ => replace x with a in H by (cbn; lia) end.
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
  Lemma x42e_f2 : forall mm l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 : word)
      (e0 e1 e2 e3 c0 c1 c2 c3 : word)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word)
      (w0 w1 w2 w9 w10 w11 w12 w13 w14 w15 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 w1 w2 (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) w9 w10 w11 w12 w13 w14 w15 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (67908))) ->
    (ARGS mm ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (LOC mm e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3) ->
    bytes_at bsegs mm SRC src ->
    DST + 3 * ((dcap + 3) / 4) < DST + dcap -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= o0 <= dcap -> 1 <= bv_unsigned c0 -> 0 <= i1 -> i1 + 8 <= n -> 0 <= o1 <= dcap -> 1 <= bv_unsigned c1 -> 0 <= i2 -> i2 + 8 <= n -> 0 <= o2 <= dcap -> 1 <= bv_unsigned c2 -> 0 <= i3 -> i3 + 8 <= n -> 0 <= o3 <= dcap -> 1 <= bv_unsigned c3 ->
    evtF bsegs RNG POST (ST 0x9e0b8 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 SB x24 x25 (Z_to_bv 64 (139879)) x27 x28 x29 x30 x31).
  Proof using CTX X2OK NBOK ACTX TL11 XMC.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mm l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 ipa0 ipa1 ipa2 ipa3 opa0 opa1 opa2 opa3 ba0 ba1 ba2 ba3 e0 e1 e2 e3 c0 c1 c2 c3
      x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31
      w0 w1 w2 w9 w10 w11 w12 w13 w14 w15
      PV MU0 WM0 MI OUT DTB FR AR LC SRCB H3Q HL1 HL2 HL3 HLN HI0 HN0 HO0 HB0 HI1 HN1 HO1 HB1 HI2 HN2 HO2 HB2 HI3 HN3 HO3 HB3.
    destruct PV as (SV & STK).
    facts R1 R2 R3 TL LO SPB KLO.
    assert (ASTK' : astk RNG lo (SPV + -528)) by (split; [exact KLO | split; [eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia] | exact RI]]).
    assert (DP : 0 < dcap) by (clear - H3Q R1; lia).
    (* [comment removed for export] *)
    asan_now MU0 WM0 AZS ART DSTA DHI LO KLO R1.
    zstep. zstep. zstep. zstep. kx_mkR_fold.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3; C8 opa0; C8 opa1; C8 opa2; C8 opa3] _)) in AR.
    destruct AR as [AR1 AR']. fixaddr AR' (SPV + -320).
    apply (proj1 (rw_cells_app bsegs _ _ [C8 ba0; C8 ba1; C8 ba2; C8 ba3] _)) in AR'.
    destruct AR' as [AR2 AR3]. fixaddr AR3 (SPV + -288).
    destruct (rw_cells_forget _ _ _ _ AR2) as [jb2 A2]. cbn [cells_size csize Nat.add] in A2. clear AR2.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 e0; C8 e1; C8 e2; C8 e3; C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3)); C8 (Z_to_bv 64 (SRC + i0)); C8 (Z_to_bv 64 (SRC + i1)); C8 (Z_to_bv 64 (SRC + i2)); C8 (Z_to_bv 64 (SRC + i3))] _)) in LC.
    destruct LC as [LC1 LC4]. fixaddr LC4 (SPV + -136).
    pose proof (proj2 (proj1 LC4)) as SB4.
    call (XMC RNG (SPV + -320) (SPV + -136) 32 (SPV + -528)).
    all: mc_side SB4 A2 STK AZmm ARTmm RSTK RI ASTK' LO GF7.
    clear AZmm ARTmm SB4; try clear A2; try clear STK; try clear jb2.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -320) [CB _ _] |- _ =>
      assert (ARb : rw_cells bsegs m (SPV + -320) [C8 c0; C8 c1; C8 c2; C8 c3])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- _ => asan_now MU WM AZS ART DSTA DHI LO KLO R1 end.
    zstep. zstep. zstep. zstep. kx_mkR_fold.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 ipa0; C8 ipa1; C8 ipa2; C8 ipa3] _)) in AR1.
    destruct AR1 as [AR0 AR1]. fixaddr AR1 (SPV + -352).
    destruct (rw_cells_forget _ _ _ _ AR0) as [jb0 A0]. cbn [cells_size csize Nat.add] in A0. clear AR0.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 e0; C8 e1; C8 e2; C8 e3; C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] _)) in LC1.
    destruct LC1 as [LC1 LC3]. fixaddr LC3 (SPV + -168).
    pose proof (proj2 (proj1 LC3)) as SB3.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -528) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK2 end.
    call (XMC RNG (SPV + -384) (SPV + -168) 32 (SPV + -528)).
    all: mc_side SB3 A0 STK2 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK2.
    clear AZmm ARTmm SB3; try clear A0; try clear jb0.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -384) [CB _ _] |- _ =>
      assert (ARi : rw_cells bsegs m (SPV + -384) [C8 (Z_to_bv 64 (SRC + i0)); C8 (Z_to_bv 64 (SRC + i1)); C8 (Z_to_bv 64 (SRC + i2)); C8 (Z_to_bv 64 (SRC + i3))])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch W0 m0 ?m, WM : wmono bsegs m0 ?m |- _ => asan_now MU WM AZS ART DSTA DHI LO KLO R1 end.
    zstep. zstep. zstep. zstep. kx_mkR_fold.
    destruct (rw_cells_forget _ _ _ _ AR1) as [jb1 A1]. cbn [cells_size csize Nat.add] in A1. clear AR1.
    apply (proj1 (rw_cells_app bsegs _ _ [C8 e0; C8 e1; C8 e2; C8 e3] _)) in LC1.
    destruct LC1 as [LC1 LC2]. fixaddr LC2 (SPV + -200).
    pose proof (proj2 (proj1 LC2)) as SB2.
    lazymatch goal with H : stk bsegs ?m lo (SPV + -528) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => rename H into STK3 end.
    call (XMC RNG (SPV + -352) (SPV + -200) 32 (SPV + -528)).
    all: mc_side SB2 A1 STK3 AZmm ARTmm RSTK RI ASTK' LO GF7.
    try clear STK3.
    clear AZmm ARTmm SB2; try clear A1; try clear jb1.
    lazymatch goal with H : rw_cells bsegs ?m (SPV + -352) [CB _ _] |- _ =>
      assert (ARo : rw_cells bsegs m (SPV + -352) [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))])
        by (eapply rw_cells_recell; [exact H | clear; cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]); clear H end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => assert (AR : (ARGS m (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) c0 c1 c2 c3 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3)))) end.
    { apply (proj2 (rw_cells_app bsegs _ (SPV + -384) [C8 (Z_to_bv 64 (SRC + i0)); C8 (Z_to_bv 64 (SRC + i1)); C8 (Z_to_bv 64 (SRC + i2)); C8 (Z_to_bv 64 (SRC + i3))] _)). split; [exact ARi|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -352) by (cbn; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -352) [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] _)). split; [exact ARo|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -320) by (cbn; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -320) [C8 c0; C8 c1; C8 c2; C8 c3] _)). split; [exact ARb|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -288) by (cbn; lia) end. exact AR3. }
    clear ARi ARo ARb AR3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m _) => assert (LCA : (LOC m e0 e1 e2 e3 (Z_to_bv 64 (DST + o0)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i1)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (SRC + i3)) c0 c1 c2 c3)) end.
    { apply (proj2 (rw_cells_app bsegs _ (SPV + -232) [C8 e0; C8 e1; C8 e2; C8 e3] _)). split; [exact LC1|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -200) by (cbn; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -200) [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3))] _)). split; [exact LC2|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -168) by (cbn; lia) end.
      apply (proj2 (rw_cells_app bsegs _ (SPV + -168) [C8 (Z_to_bv 64 (SRC + i0)); C8 (Z_to_bv 64 (SRC + i1)); C8 (Z_to_bv 64 (SRC + i2)); C8 (Z_to_bv 64 (SRC + i3))] _)). split; [exact LC3|].
      lazymatch goal with |- rw_cells _ _ ?x _ => replace x with (SPV + -136) by (cbn; lia) end. exact LC4. }
    clear LC1 LC2 LC3 LC4.
    destruct (rw_cells_forget _ _ _ _ LCA) as [junkL LOCB]. cbn [cells_size csize Nat.add] in LOCB. clear LCA.
    try clear POST POST0 POST1.
    (* [comment removed for export] *)
    kcleanF.
    kx_autoFLA FR (@nil kza) [0x9e120] 20%nat
      [KZRange SPV 17594333498432 140737488355328; KZRange dcap 1 4294967296; KZRange DT 4096 140737488338940; KZRange DST 4096 140737488355328; KZImg 0x103e8 0x103f0]
      [(SPV + -528, 144); (0x103e8, 8)] [(SPV - 528, 528)].
    all: aside.
    all: kx_mem.
    all: kx_strip_mod.
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    all: lazymatch goal with SV : FRQ ?m, PC : stk bsegs ?m lo (SPV + -528) |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      eapply (x42e_f3_0 m 0 ((dcap + 3) / 4) (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3);
      first [exact (conj SV PC) | exact LOCB | eassumption | reflexivity | lia | idtac] end.
  Qed.
End DX42FF2.
End CANSEC1.
