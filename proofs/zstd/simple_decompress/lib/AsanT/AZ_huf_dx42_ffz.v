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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_hufkit42e AZ_hufkit42e2 AZ_huf_dx42_fq AZ_huf_dx42_ffo AZ_huf_dx42_ffv AZ_huf_fastargs AZ_libc.
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
Section DX42FFZ.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42e_ctx SPV DST dcap SRC n DT tl lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis NBOK : huf_nb_ok true dtb tl.

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
  Hypothesis X42D : x42d_seg_stmt.
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
  Notation x42e_f0_no := (AZ_huf_dx42_ffv.x42e_f0_no RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK X42D PRE0 DTP0).

  Ltac fixaddr H a := lazymatch type of H with rw_cells _ _ ?x _ => replace x with a in H by (cbn; lia) end.
  Ltac asan_nowF MU WM AZS ART LO KLO :=
    let mm := lazymatch type of MU with munch _ _ ?mm => mm end in
    let W := lazymatch type of MU with munch [(SPV - ?W, SPV)] _ _ => W end in
    assert (AZmm : azstk RNG mm lo SPV)
      by (eapply azstk_transport; [exact AZS | exact MU | exact WM | apply aappW_frameN; unfold KHIGH; clear - LO KLO; lia | clear - LO; lia]);
    assert (ARTmm : art mm) by (eapply (art_frameN m0 mm SPV W); [exact ART | exact MU | exact WM | unfold KHIGH; clear - LO KLO; lia]).
  (* [comment removed for export] *)
  Ltac trapsZ := idtac.

  (* [comment removed for export] *)
  Lemma x42e_n0 : forall (x7 x16 x17 x28 x29 x30 : word) (flags : word) (m1 : amem) (junk : list byte),
    munch [(SPV - 576, SPV)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    rw_cells bsegs m1 (SPV + -576) (CB 472 junk :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) -> stk bsegs m1 lo (SPV + -576) ->
    stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 SRC src -> bytes_at bsegs m0 DT dtb -> n = 0 ->
    evtF bsegs RNG POST (ST 0x9bb64 m1 (Z_to_bv 64 (n)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DT)) x7 s0 s1 (Z_to_bv 64 (DST)) (Z_to_bv 64 (0)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (n)) (Z_to_bv 64 (DT)) flags x16 x17 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (DST)) s9 s10 SB x28 x29 x30 (Z_to_bv 64 (SRC))).
  Proof using CTX X2OK NBOK X42D PRE0 DTP0.
    pose proof CTX as CTX'. x42e_ctx_open CTX'.
    pose proof PRE0 as PRE'. destruct PRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ART & ASTK0 & AZS & ARC & _).
    destruct ASTK0 as (KLO0 & RSTK & RI).
    pose proof DTP0 as DTP'. destruct DTP' as (_ & _ & _ & _ & _ & _ & ARODT & _). destruct ARODT as (UDT & RDT & RDTS).
    intros x7 x16 x17 x28 x29 x30 flags m1 junk MU01 WM01 MI1 FRALL STK1 OUT0 SRCB0 DTB0 N0.
    facts R1 R2 R3 TL LO SPB KLO.
    assert (OUT : stk bsegs m1 DST (DST + dcap)) by (eapply stk_transport_disjoint; [exact OUT0 | exact MU01 | exact WM01 | cbn [disjoint_from fst snd]; clear - OS1 LO; lia]).
    assert (SRCB : bytes_at bsegs m1 SRC src) by (eapply bytes_at_transport; [exact SRCB0 | exact MU01 | cbn [disjoint_from fst snd]; clear - OS2 LO SL; lia]).
    assert (DTB : bytes_at bsegs m1 DT dtb) by (eapply bytes_at_transport; [exact DTB0 | exact MU01 | cbn [disjoint_from fst snd]; clear - OS3 LO DL; lia]).
    clear OUT0 SRCB0 DTB0.
    apply (rw_cells_split_CB bsegs m1 _ [] 472 junk _ [320; 152]%nat) in FRALL; [| reflexivity]. cbn [mk_CB_cells app] in FRALL.
    apply (proj1 (rw_cells_app bsegs _ _ [CB 320 _] _)) in FRALL. destruct FRALL as [FRb FRALL]. fixaddr FRALL (SPV + -256).
    apply (proj1 (rw_cells_app bsegs _ _ [CB 152 _] _)) in FRALL. destruct FRALL as [A2 SV]. fixaddr SV (SPV + -104).
    assert (FRX : exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : word,
               FRS m1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39)
      by (pose proof (e42_cb_as_c8s m1 _ 40 _ FRb) as FRc; cbn [e42_c8s_of] in FRc; do 40 eexists; exact FRc).
    destruct FRX as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & FR). clear FRb.
    asan_nowF MU01 WM01 AZS ART LO KLO.
    pose proof ARTmm as ART1. destruct ART1 as (GOT & RIC & SHB & INI & LAY & REAL).
    assert (UDT1 : unpoisoned m1 DT (DT + 16388)) by (eapply unpoisoned_frameN; [exact UDT | exact MU01 | unfold KHIGH; clear - LO KLO; lia | clear - R3; lia | unfold KEND; clear - R3; lia]).
    assert (RFR : rng RNG (SPV - 624) 624) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (MUw : munch [(SPV - 624, SPV)] m0 m1) by (eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
    assert (MU0 : munch W0 m0 m1) by (eapply munch_weaken; [| exact MU01]; unfold sub_fp; cbn [outside fst snd app]; intros; lia).
    pose proof WM01 as WM0. clear MU01.
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz.
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDT1 ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz.
    (* [comment removed for export] *)
    carve_frame 48%nat STK1.
    lazymatch goal with H : rw_cells bsegs m1 (SPV + -624) [CB 48 ?jj] |- _ =>
      pose proof (e42_cb_as_c8s m1 _ 6 jj H) as FAW; cbn [e42_c8s_of] in FAW; clear H end.
    unfold HUF_DTABLE_BYTES in *.
    lazymatch type of FAW with rw_cells _ _ _ [C8 ?a0; C8 ?a1; C8 ?a2; C8 ?a3; C8 ?a4; C8 ?a5] =>
      set (u0 := a0) in FAW; set (u1 := a1) in FAW; set (u2 := a2) in FAW; set (u3 := a3) in FAW; set (u4 := a4) in FAW; set (u5 := a5) in FAW;
      clearbody u0 u1 u2 u3 u4 u5 end.
    assert (KF : (4100 <= DT + 4 <= 140737488338944) /\ (4096 <= DST + dcap <= 140737488355328)) by (clear - R1 R3; lia).
    destruct KF as (KF1 & KF2).
    kx_autoFLA (FR, FAW, GOT, SHB) [KAUnp DT 16388; KAApp (SPV - 624) 624] [0x9bb94] 120%nat
        [KZRange dcap 0 4294967296; KZRange DST 4096 140737488355327; KZRange (DST + dcap) 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange (DT + 4) 4100 140737488338944; KZRange SRC 4096 140737488355328; KZRange n 0 0;
         KZRange SPV 17594333498432 140737488355328; KZWr (SPV + -576) 320; KZWr (SPV + -624) 48;
         KZDisj (SPV - 624) 624 DT 16388; KZDisj DST dcap (SPV - 624) 624]
        [(SPV + -624, 48); (SPV + -576, 320); (DT, 16388)] [(DT, 16388); (SPV - 624, 624)].
    all: aside.
    all: kx_mem.
    all: try clear KXK KXA KXRD; try clear KXE.
    all: clear UDTz UDT1 AZmm ARTmm RIC INI LAY REAL.
    all: assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    all: lazymatch goal with MU : munch W0 m0 ?mm |- _ =>
      assert (UDTc : unpoisoned mm DT (DT + 16388))
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply unp_carryW; [exact UDT | exact MU | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
            | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU by (clear - Hd R1; lia); exact MU
                                 | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
      pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz; clear UDTc AW0 end.
    all: kx_autoFLA (FR, FAW, GOT, SHB) [KAUnp DT 16388; KAApp (SPV - 624) 624] [0x9bb94] 200%nat
        [KZRange dcap 0 4294967296; KZRange DST 4096 140737488355327; KZRange (DST + dcap) 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange (DT + 4) 4100 140737488338944; KZRange SRC 4096 140737488355328; KZRange n 0 0;
         KZRange SPV 17594333498432 140737488355328; KZWr (SPV + -576) 320; KZWr (SPV + -624) 48;
         KZDisj (SPV - 624) 624 DT 16388; KZDisj DST dcap (SPV - 624) 624]
        [(SPV + -624, 48); (SPV + -576, 320); (DT, 16388)] [(DT, 16388); (SPV - 624, 624)].
    all: aside.
    all: kx_mem.
    all: try clear KXK KXA KXRD; try clear KXE.
    all: lazymatch goal with FA' : rw_cells bsegs ?mq (SPV + -624) _, ST' : stk bsegs ?mq lo (SPV + -624) |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9bb94) _ _ ?mq _) =>
           release_frame FA' ST' (SPV + -576) end.
    all: lazymatch goal with SV' : rw_cells bsegs ?mq (SPV + -104) _, ST' : stk bsegs ?mq lo (SPV + -576) |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9bb94) _ _ ?mq _) =>
           first [ eapply evtF_eq; cycle 1;
                   [ eapply (x42e_f0_no mq 18446744073709551596); first [ split; [exact SV' | exact ST'] | eassumption | right; vm_compute; reflexivity | clear; lia ]
                   | f_equal; f_equal; try reflexivity; f_equal; clear - N0; lia ]
                 | eapply evtF_eq; cycle 1;
                   [ eapply (x42e_f0_no mq 0); first [ split; [exact SV' | exact ST'] | eassumption | left; reflexivity | clear; lia ]
                   | f_equal; f_equal; try reflexivity; f_equal;
                     first [ clear - N0; lia
                           | clear - KXBR N0; lia ] ] ] end.
  Qed.
End DX42FFZ.

(* [comment removed for export] *)
Theorem x42e_fast_proofB : fast_args_stmt3A -> zd_memcpyZ_stmtA -> x42d_seg_stmt -> x42e_fast_stmt.
Proof.
  intros XFA XMC X42D. unfold x42e_fast_stmt.
  intros RNG ra gp tp t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m m1 SPV DST dcap SRC n DT tl lo src dtb junk
         PRE DTP DT2 TL X2 NB MU WM MI1 FR STK1.
  pose proof PRE as PRE'.
  destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA).
  pose proof DTP as DTP'. destruct DTP' as (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA). unfold HUF_DTABLE_BYTES in *.
  destruct AST as (KLO & RSTK & RI). destruct ARODT as (UDT & RDT & RDTS).
  assert (DSTA : dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
  { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd]; [| left; lia]. right.
    destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  assert (DHI : 0 < dcap -> 0x625000 <= DST).
  { intros Hd. destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  assert (CTX : x42e_ctx SPV DST dcap SRC n DT tl lo src dtb).
  { unfold x42e_ctx. unfold KHIGH in KLO. repeat split; try assumption; lia. }
  destruct (Z.eq_dec n 0) as [N0|N1].
  { exact (x42e_n0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl lo src dtb CTX X2 NB X42D PRE DTP
             t2 a6 a7 t3 t4 t5 flags m1 junk MU WM MI1 FR STK1 OUT SRCB DTB N0). }
  destruct (ARS ltac:(lia)) as (ABS & USRC & RSRC & RSRCS).
  assert (ACTX : x42e_actx RNG m SPV DST dcap SRC n DT lo).
  { unfold x42e_actx. unfold KHIGH in KLO |- *.
    split; [exact USRC|]. split; [exact UDT|].
    split; [intros Hd; destruct (ARD Hd) as (_ & U & _); exact U|].
    split; [exact RSRC|]. split; [exact RSRCS|]. split; [exact RDT|]. split; [exact RDTS|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & R & _); exact R|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & _ & R); exact R|].
    split; [exact RSTK|]. split; [exact RI|]. split; [exact AZS|]. split; [exact ARC | exact ART]. }
  exact (AZ_huf_dx42_ffv.x42e_f0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl lo src dtb CTX X2 NB ACTX XFA XMC X42D PRE DTP
           t2 a6 a7 t3 t4 t5 flags m1 junk MU WM MI1 FR STK1 OUT SRCB DTB ltac:(lia)).
Qed.

(* [comment removed for export] *)
Theorem x42e_fast : x42d_seg_stmt -> x42e_fast_stmt.
Proof. intros X42D. exact (x42e_fast_proofB fast_args_proof3A zd_memcpyZ_proofA X42D). Qed.
End CANSEC1.
