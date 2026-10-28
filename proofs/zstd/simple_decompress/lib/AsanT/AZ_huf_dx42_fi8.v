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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_hufkit42e AZ_huf_dx42_fq AZ_huf_dx42_fi9.
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
Section DX42FI8.
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
  (* [comment removed for export] *)
  Ltac izsh :=
    lazymatch goal with
    | |- sc_resid _ _ _ (SCDisj _ _ _ _) =>
        kx_side_pre;
        repeat match goal with H : mdh (_ + _ <= 2147450880 \/ _) |- _ => unfold mdh in H; revert H end;
        repeat match goal with H : _ <= bv_unsigned (ev _ _) <= _ |- _ => revert H end;
        repeat match goal with H : 0 <= bv_unsigned _ <= 63 |- _ => revert H end;
        repeat match goal with H : 4096 <= ?a <= _ |- _ => is_var a; revert H end;
        lazymatch goal with K : (10 <= _ - _ <= 4294967296) /\ _ |- _ => revert K end;
        repeat match goal with H : 17594333498432 <= SPV <= _ |- _ => revert H end;
        repeat match goal with H : 4096 <= SRC /\ _ |- _ => revert H end;
        repeat match goal with H : _ |- _ => clear H end;
        intros; lia
    end.
  Lemma x42f_idx11 : forall (w : word), 0 <= bv_unsigned w / 9007199254740992 < 2 ^ 11.
  Proof.
    intros w. pose proof (bv_unsigned_in_range 64 w) as HX. unfold bv_modulus in HX. change (2 ^ Z.of_N 64) with (2^64) in HX.
    split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; [lia|]. change (9007199254740992 * 2 ^ 11) with (2^64). lia.
  Qed.
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
  Ltac x42f_entg :=
    first [ solve [
      evw;
      repeat match goal with H : _ <= bv_unsigned (ev _ _) <= _ |- _ => revert H end;
      repeat match goal with H : _ |- _ => clear H end; intros;
      rewrite u_small by lia; Z.div_mod_to_equations; lia ]
    | lazymatch goal with |- ?G => fail 100 "x42f_entg:" G end ].
  Ltac x42f_zc :=
    repeat match goal with
    | |- context [(Zpos ?a mod Zpos ?b)%Z] => let v := eval vm_compute in (Zpos a mod Zpos b)%Z in change (Zpos a mod Zpos b)%Z with v
    | |- context [(2 ^ Zpos ?a)%Z] => let v := eval vm_compute in (2 ^ Zpos a)%Z in change (2 ^ Zpos a)%Z with v
    | |- context [Z.land ?x 255] => replace (Z.land x 255) with (x mod 256) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity)
    | |- context [Z.land ?x 63] => replace (Z.land x 63) with (x mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity)
    end.
  Ltac x42f_amt KXA :=
    first [ solve [ cbn [edenot];
              repeat match goal with |- context [ev ?E ?j] => rewrite (KXA j) by (cbn [length]; lia) end;
              cbn [znth nth]; rewrite ?Z_to_bv_bv_unsigned;
              rewrite ?u_srl64, ?u_and64, ?u_add64; rewrite ?u_small by lia; x42f_zc;
              repeat match goal with H : (bv_unsigned _ / 65536) mod 256 <= 11 |- _ => revert H end;
              repeat match goal with H : _ |- _ => clear H end; intros;
              Z.div_mod_to_equations; lia ]
          | e42_amt ].
  Ltac x42f_lbc KXA :=
    lazymatch goal with
    | |- LBW ?p (edenot ?E (EAlu ALU_SLL ?a ?b)) =>
        change (LBW p (alu64 ALU_SLL (edenot E a) (edenot E b)));
        let q := eval vm_compute in (p - 11) in
        change p with (q + 11);
        apply (lbw_sll q 11 (edenot E a) (edenot E b)); [x42f_lbc KXA | x42f_amt KXA | lia ]
    | |- LBW ?p (edenot ?E (EVar ?a)) => e42_lb_atom KXA
    | |- ?G => fail 100 "x42f_lbc:" G
    end.
  Notation KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y5 y7 y8 y9 y10 y11 y12 y13 y14 y23 y28 y29 y30 : word) (w'0 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 w'39 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (64772)) w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (140088)) w'39) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        bytes_at bsegs mm' SRC src ->
        i0 - 7 <= i0' <= i0 -> i1 - 7 <= i1' <= i1 -> i2 - 7 <= i2' <= i2 -> i3 - 7 <= i3' <= i3 ->
        o0 + 5 <= o0' <= o0 + 10 -> o1 + 5 <= o1' <= o1 + 10 -> o2 + 5 <= o2' <= o2 + 10 -> o3 + 5 <= o3' <= o3 + 10 ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' -> o3' < OL -> (2 <= r)%nat ->
        evtF bsegs RNG POST (ST 0x9bd48 mm' (Z_to_bv 64 (SRC + i3')) y5 (Z_to_bv 64 (DST + o0')) y7 y8 y9 y10 y11 y12 y13 y14 (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (DT + 4)) c2' c0' y23 c3' (Z_to_bv 64 (140088)) (Z_to_bv 64 (SRC + i1')) SB y28 y29 y30 c1')).
  Notation KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y5 y7 y8 y9 y10 y11 y12 y13 y14 y23 y25 y28 y29 y30 : word) (w'0 w'15 w'16 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 w'38 w'39 : word),
        munch WDL mb mm' -> wmono bsegs mb mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' ->
        stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) w'15 w'16 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 (Z_to_bv 64 (DT + 4)) w'38 w'39) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        bytes_at bsegs mm' SRC src ->
        i0 - 7 <= i0' <= i0 -> i1 - 7 <= i1' <= i1 -> i2 - 7 <= i2' <= i2 -> i3 - 7 <= i3' <= i3 ->
        o0 + 5 <= o0' <= o0 + 10 -> o1 + 5 <= o1' <= o1 + 10 -> o2 + 5 <= o2' <= o2 + 10 -> o3 + 5 <= o3' <= o3 + 10 ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' -> OL <= o3' ->
        evtF bsegs RNG POST (ST 0x9bc40 mm' (Z_to_bv 64 (SRC + i3')) y5 (Z_to_bv 64 (DST + o0')) y7 y8 y9 y10 y11 y12 y13 y14 (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (DT + 4)) c2' c0' y23 c3' y25 (Z_to_bv 64 (SRC + i1')) SB y28 y29 y30 c1')).
  Notation x42e_fi9 := (AZ_huf_dx42_fi9.x42e_fi9 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).

  (* [comment removed for export] *)
  Lemma x42e_fi8 : forall (r : nat) mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 (c1 c2 c3 : word) (en0 en1 en2 en3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x6 x7 x8 x12 x13 x14 x23 x24 x28 x29 x30 : word)
      (w0 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 : word),
    munch WDL mb mm -> wmono bsegs mb mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DST + OL)) (Z_to_bv 64 (64772)) w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 (Z_to_bv 64 (SRC + i3)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (140088)) en2) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    (bv_unsigned en0 / 65536) mod 256 <= 11 -> 1 <= bv_unsigned en0 / 16777216 <= 2 ->
    (bv_unsigned en1 / 65536) mod 256 <= 11 -> 1 <= bv_unsigned en1 / 16777216 <= 2 ->
    (bv_unsigned en2 / 65536) mod 256 <= 11 -> 1 <= bv_unsigned en2 / 16777216 <= 2 ->
    (bv_unsigned en3 / 65536) mod 256 <= 11 -> 1 <= bv_unsigned en3 / 16777216 <= 2 ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    (1 <= r)%nat -> OL - o3 <= 5 * Z.of_nat r -> 0 <= o0 -> 0 <= o1 -> 0 <= o2 -> 0 <= o3 ->
    o0 + 10 * Z.of_nat r <= q -> o1 + 10 * Z.of_nat r <= 2 * q -> o2 + 10 * Z.of_nat r <= 3 * q -> o3 + 10 * Z.of_nat r <= dcap ->
    3 * q <= dcap -> 0 <= q -> 0 <= OL <= dcap ->
    7 * Z.of_nat r <= i0 -> 7 * Z.of_nat r <= i1 -> 7 * Z.of_nat r <= i2 -> 7 * Z.of_nat r <= i3 ->
    i0 + 8 <= n -> i1 + 8 <= n -> i2 + 8 <= n -> i3 + 8 <= n -> 8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    o0 + 4 <= u0 <= o0 + 8 ->
    o1 + 4 <= u1 <= o1 + 8 ->
    o2 + 4 <= u2 <= o2 + 8 ->
    o3 + 1 <= u3 <= o3 + 2 ->
    i0 - 7 <= j0 <= i0 ->
    LBW 52 c1 ->
    LBW 52 c2 ->
    LBW 19 c3 ->
    KHI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    KOI r mb q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x9c77c mm (Z_to_bv 64 (151050438420815295)) (Z_to_bv 64 (DST + u2)) x6 x7 x8 en0 c3 en3 x12 x13 x14 (Z_to_bv 64 (DST + u3)) (Z_to_bv 64 (DST + u0)) (Z_to_bv 64 (DST + u1)) (Z_to_bv 64 (SRC + j0)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (DT + 4)) en1 c1 x23 x24 (Z_to_bv 64 (140088)) (Z_to_bv 64 (SRC + i1)) SB x28 x29 x30 c2).
  Proof using CTX X2OK NBOK ACTX TL11.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros r mb mm q OL nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 u0 u1 u2 u3 j0 c1 c2 c3 en0 en1 en2 en3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x6 x7 x8 x12 x13 x14 x23 x24 x28 x29 x30
      w0 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35
      MU WM MU0 WM0 MI OUT DTB FR AR HEN0 HEL0 HEN1 HEL1 HEN2 HEL2 HEN3 HEL3 SRCB HND HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN
      HU0 HU1 HU2 HU3 HJ0 HLBc1 HLBc2 HLBc3 KH KO. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO. ffacts OS1 OS2 OS3 LO.
    sfactsW MU0 USRC DSTA AW0 R1 R2 RSRCS. dfacts MU0 UDST RDST RDSTS DSTA AW0 R1. kcleanF.
    assert (TBL : tbl_in bsegs mm DT 8196 4 7 1 2) by (apply x42f_tbl; exact DTB).
    assert (TBN : tbl_in bsegs mm DT 8196 4 6 0 11) by (apply x42f_tbn; exact DTB).
    assert (TBLC : tbl_in bsegs mm ACTZ_TBLB 64 1 0 0 63) by exact (actz_tblb mm MI).
    pose proof (lbw_pos _ _ HLBc1) as HLPc1.
    pose proof (lbw_pos _ _ HLBc2) as HLPc2.
    pose proof (lbw_pos _ _ HLBc3) as HLPc3.
    assert (KEN0 : 16777216 <= bv_unsigned en0 <= 50331647) by (clear - HEL0; Z.div_mod_to_equations; lia).
    assert (KEN1 : 16777216 <= bv_unsigned en1 <= 50331647) by (clear - HEL1; Z.div_mod_to_equations; lia).
    assert (KEN2 : 16777216 <= bv_unsigned en2 <= 50331647) by (clear - HEL2; Z.div_mod_to_equations; lia).
    assert (KEN3 : 16777216 <= bv_unsigned en3 <= 50331647) by (clear - HEL3; Z.div_mod_to_equations; lia).
    assert (KF : (10 <= q - o0 <= 4294967296) /\ (10 <= 2 * q - o1 <= 4294967296) /\ (10 <= 3 * q - o2 <= 4294967296) /\ (10 <= dcap - o3 <= 4294967296) /\ (10 <= dcap - o0 <= 4294967296) /\ (10 <= dcap - o1 <= 4294967296) /\ (10 <= dcap - o2 <= 4294967296) /\ (0 <= o0 <= 4294967296) /\ (0 <= o1 <= 4294967296) /\ (0 <= o2 <= 4294967296) /\ (0 <= o3 <= 4294967296) /\ (0 <= OL <= 4294967296) /\ (7 <= i0 <= 4294967296) /\ (7 <= i1 <= 4294967296) /\ (7 <= i2 <= 4294967296) /\ (7 <= i3 <= 4294967296) /\ (8 <= n - i0 <= 4294967296) /\ (8 <= n - i1 <= 4294967296) /\ (8 <= n - i2 <= 4294967296) /\ (8 <= n - i3 <= 4294967296) /\ (38 <= n <= 4294967296) /\ (10 <= dcap <= 4294967296) /\ (0 <= q <= 4294967296) /\ (4096 <= DST + o0 <= 140737488355317) /\ (4096 <= DST + o1 <= 140737488355317) /\ (4096 <= DST + o2 <= 140737488355317) /\ (4096 <= DST + o3 <= 140737488355317) /\ (4104 <= SRC + n <= 140737488355327) /\ (4096 <= SRC + i0 <= 140737488355319) /\ (4096 <= SRC + i1 <= 140737488355319) /\ (4096 <= SRC + i2 <= 140737488355319) /\ (4096 <= SRC + i3 <= 140737488355319))
      by (clear - HR HOL HO0 HO1 HO2 HO3 HE0 HE1 HE2 HE3 HQ3 HQ0 HOLR HI0 HI1 HI2 HI3 HN0 HN1 HN2 HN3 HL1 HL2 HL3 HLN R1 R2 HU0 HU1 HU2 HU3 HJ0 HLBc1 HLBc2 HLBc3; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12 & KF13 & KF14 & KF15 & KF16 & KF17 & KF18 & KF19 & KF20 & KF21 & KF22 & KF23 & KF24 & KF25 & KF26 & KF27 & KF28 & KF29 & KF30 & KF31 & KF32).
    remember (DST + u3) as A0 eqn:HA0 in |- *.
    assert (KA : (4096 <= A0 <= 140737488355319) /\ (DST <= A0 /\ A0 + 8 <= DST + dcap))
      by (clear - HA0 KF R1 HU0 HU1 HU2 HU3; lia).
    destruct KA as (KA0 & KA0r).
    assert (KB0 : mdh (A0 + 8 <= SPV - 576 \/ SPV - 576 + 472 <= A0)) by (unfold mdh; clear - KA0r DJF1; lia).
    assert (KD0 : mdh (A0 + 8 <= DT \/ DT + 16388 <= A0)) by (unfold mdh; clear - KA0r DJ2; lia).
    assert (KP0 : mdh (A0 + 8 <= 2147450880 \/ 17594333495296 <= A0)) by (unfold mdh; clear - KA0r DSTAc; lia).
    assert (KS0 : mdh (A0 + 8 <= SRC \/ SRC + n <= A0)) by (unfold mdh; clear - KA0r DJ1; lia).
    assert (KSF : mdh (SPV - 576 + 472 <= SRC \/ SRC + n <= SPV - 576)) by (unfold mdh; clear - OS2 LO; lia).
    assert (WAD : wr_at bsegs mm DST dcap)
      by (pose proof (wr_at_stk bsegs mm DST (DST + dcap) OUT ltac:(clear - KF; lia)) as W; replace (DST + dcap - DST) with dcap in W by (clear; lia); exact W).
    assert (UA0 : unpZ mm A0 (A0 + 8)) by (apply (unpoisoned_unpZ mm DST (DST + dcap) A0 (A0 + 8) UDSTc); [clear - KA0r; lia | clear - KA0r; lia | unfold KXKEND; clear - KA0; lia]).
    assert (RZ0 : rng RNG (KXSHLO + A0 / 8) (shspanZ A0 8)) by (apply (rng_sub' RNG _ _ _ _ RDSTz); unfold shspanZ; clear - KA0 KA0r GF1; Z.div_mod_to_equations; lia).
    assert (RW0 : rng RNG A0 8) by (apply (rng_sub RNG DST dcap A0 8 RDSTc); clear - KA0r; lia).
    assert (WA0 : wr_at bsegs mm A0 8) by (apply (wr_at_sub bsegs mm DST dcap A0 8 WAD); clear - KA0r; lia).
    kx_autoFLA (FR, AR) [KAUnp SRC n; KAUnp DT 16388; KAApp (SPV - 576) 472; KAUnp A0 8; KAApp A0 8] [0x9c898] 300%nat
          [KZRange (q - o0) 10 4294967296; KZRange (2 * q - o1) 10 4294967296; KZRange (3 * q - o2) 10 4294967296; KZRange (dcap - o3) 10 4294967296; KZRange (dcap - o0) 10 4294967296;
           KZRange (dcap - o1) 10 4294967296; KZRange (dcap - o2) 10 4294967296; KZRange (o0) 0 4294967296; KZRange (o1) 0 4294967296; KZRange (o2) 0 4294967296;
           KZRange (o3) 0 4294967296; KZRange (OL) 0 4294967296; KZRange (i0) 7 4294967296; KZRange (i1) 7 4294967296; KZRange (i2) 7 4294967296;
           KZRange (i3) 7 4294967296; KZRange (n - i0) 8 4294967296; KZRange (n - i1) 8 4294967296; KZRange (n - i2) 8 4294967296; KZRange (n - i3) 8 4294967296;
           KZRange (n) 38 4294967296; KZRange (dcap) 10 4294967296; KZRange (q) 0 4294967296; KZRange (SRC + n) 4104 140737488355327; KZRange (SRC + i0) 4096 140737488355319;
           KZRange (SRC + i1) 4096 140737488355319; KZRange (SRC + i2) 4096 140737488355319; KZRange (SRC + i3) 4096 140737488355319; KZTbl DT 8196 4 7 1 2;
           KZTbl DT 8196 4 6 0 11; KZTbl ACTZ_TBLB 64 1 0 0 63; KZImg 0x22338 0x22378; KZImg 0x103e8 0x103f0; KZWr (SPV + -576) 320;
           KZDisj (SPV - 576) 472 DT 16388; KZDisj (SPV - 576) 472 SRC n; KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZRange SPV 17594333498432 140737488355328;
           KZRange SRC 4096 140737488355328; KZAlign DT 4; KZRange A0 4096 140737488355319; KZWr A0 8; KZDisj A0 8 (SPV - 576) 472;
           KZDisj A0 8 DT 16388; KZDisj A0 8 SRC n; KZRange (i0 - j0) 0 7; KZRange j0 0 4294967296; KZRange (n - j0) 8 4294967296; KZRange (bv_unsigned c1) 1 18446744073709551615;
           KZRange (bv_unsigned c2) 1 18446744073709551615; KZRange (bv_unsigned c3) 1 18446744073709551615; KZRange (bv_unsigned en0) 16777216 50331647; KZRange (bv_unsigned en1) 16777216 50331647;
            KZRange (bv_unsigned en2) 16777216 50331647; KZRange (bv_unsigned en3) 16777216 50331647]
          [(DT, 16388); (SRC, n); (SPV + -576, 320); (SPV + -256, 152); (0x22338, 64); (0x103e8, 8)] [(DT, 16388); (SRC, n); (A0, 8); (SPV - 576, 576)].
    all: try izsh.
    all: aside.
    all: clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12 KF13 KF14 KF15 KF16 KF17 KF18 KF19 KF20 KF21 KF22 KF23 KF24 KF25 KF26 KF27 KF28 KF29 KF30 KF31 KF32.
    all: clear KSF WAD KA0 KA0r KB0 KD0 KP0 KS0 UA0 RZ0 RW0 WA0.
    all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: trapsF.
    all: aclean.
    all: kx_gen_regsF [6%nat; 7%nat; 8%nat; 9%nat; 12%nat; 13%nat; 14%nat; 22%nat; 23%nat; 24%nat; 28%nat; 29%nat; 30%nat]; intros.
    all: evw. all: kx_mem. all: kx_sx3. all: kx_strip_mod.
    (* [comment removed for export] *)
    all: rewrite ?Z_to_bv_bv_unsigned.
    all: lazymatch goal with H : rw_cells _ _ (SPV + -576) _ |- _ => rewrite ?Z_to_bv_bv_unsigned in H end.
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => set (W3 := X) in *; assert (LW3 : LBW 30 W3) by (subst W3; x42f_lbc KXA); clearbody W3 end.
    all: lclean2.
    all: subst A0.
    all: try clear KXRD; try clear KXA; try clear KXLF.
    all: (lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 (DST + ?X + ?Y)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => replace (DST + X + Y) with (DST + (X + Y)) in * by (clear; lia) | |- _ => idtac end);
         (lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?X + ?Y)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => replace (DST + X + Y) with (DST + (X + Y)) in * by (clear; lia) | |- _ => idtac end);
         (lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?X + ?Y)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => replace (DST + X + Y) with (DST + (X + Y)) in * by (clear; lia) | |- _ => idtac end);
         (lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + ?X + ?Y)) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => replace (DST + X + Y) with (DST + (X + Y)) in * by (clear; lia) | |- _ => idtac end).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
           eapply (x42e_fi9 r mb m1 q OL (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3); first [ eassumption | reflexivity
            | lazymatch goal with
              | |- LBW _ _ => first [assumption | eapply lbw_mono; [eassumption | lia]]
              | |- 0 <= bv_unsigned ?w / 9007199254740992 <= 2047 => pose proof (x42f_idx11 w); lia
              | |- (_ <= _)%nat => lia | |- (_ = _)%nat => lia
              | |- (bv_unsigned _ / 65536) mod 256 <= 11 => x42f_entg | |- 1 <= bv_unsigned _ / 16777216 <= 2 => x42f_entg | |- _ => lia
              end ] end.
    all: try exact KH. all: try exact KO.
  Qed.
End DX42FI8.
End CANSEC1.
