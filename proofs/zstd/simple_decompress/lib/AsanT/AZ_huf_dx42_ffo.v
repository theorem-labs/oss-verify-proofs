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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_huf_iface3 AZ_libc_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42_mh AZ_huf_4x2 AZ_hufkit42e AZ_huf_dx42_fq AZ_huf_dx42_fa AZ_huf_dx42_fb AZ_huf_dx42_fc AZ_huf_dx42_fd AZ_huf_dx42_fe AZ_huf_dx42_f33 AZ_huf_dx42_f32 AZ_huf_dx42_f31 AZ_huf_dx42_f30 AZ_huf_dx42_ff2 AZ_huf_dx42_fi0 AZ_huf_dx42_fij.
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
Section DX42FFO.
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

  Ltac x42_mulhu_rb :=
    repeat match goal with
    | KXA : atoms_ok ?zs ?E |- _ =>
        let go a b :=
            let nz := kx_len zs in let ua := kx_uz E zs nz a in let ub := kx_uz E zs nz b in
            let HD := fresh "HD" in
            assert (HD : bv_unsigned (edenot E (EMd M_MULHU a b)) = ua * ub / 2 ^ 64)
              by (change (edenot E (EMd M_MULHU a b)) with (mul_div M_MULHU (edenot E a) (edenot E b)); rewrite KXS.u_mulhu64;
                  rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA); reflexivity);
            rewrite HD in *; clear HD in
        match goal with
        | |- context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] => go a b
        | H : context [bv_unsigned (edenot E (EMd M_MULHU ?a ?b))] |- _ => go a b
        end
    end.
  Lemma x42_l10 : forall x, 0 <= x < 2^64 -> x mod 2^64 * 14757395258967641293 / 2^64 / 8 = x / 10.
  Proof using. intros x Hx. rewrite (Z.mod_small x) by lia. Z.div_mod_to_equations; lia. Qed.
  Lemma x42_l7 : forall x, 0 <= x < 2^64 ->
    ((x + -1 * (x mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + x mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = x / 7.
  Proof using.
    intros x Hx. rewrite (Z.mod_small x) by lia.
    set (h := x * 2635249153387078803 / 2^64).
    assert (Hh : 0 <= h <= x) by (subst h; Z.div_mod_to_equations; lia).
    replace (x + -1 * h) with (x - h) by lia. rewrite (Z.mod_small (x - h)) by lia.
    rewrite (Z.mod_small ((x - h) / 2 + h)) by (Z.div_mod_to_equations; lia).
    subst h. Z.div_mod_to_equations; lia.
  Qed.
  Lemma x42_fo_eqs : forall q dcap o0 o1 o2 o3 i0 n,
    0 <= o0 <= q -> 0 <= o1 <= 2 * q -> 0 <= o2 <= 3 * q -> 0 <= o3 <= dcap -> 0 <= q -> 3 * q <= dcap -> dcap < 2^32 ->
    0 <= i0 -> i0 + 8 <= n -> n < 2^32 ->
    ((-1 * o0 + q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (q - o0) / 10) /\
    ((-1 * o1 + 2 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (2 * q - o1) / 10) /\
    ((-1 * o2 + 3 * q) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (3 * q - o2) / 10) /\
    ((-1 * o3 + dcap) mod 2^64 * 14757395258967641293 / 2^64 / 8 = (dcap - o3) / 10) /\
    (((i0 + -1 * (i0 mod 2^64 * 2635249153387078803 / 2^64)) mod 2^64 / 2 + i0 mod 2^64 * 2635249153387078803 / 2^64) mod 2^64 / 4 = i0 / 7) /\
    (0 <= (q - o0) / 10 /\ 10 * ((q - o0) / 10) <= q - o0) /\ (0 <= (2 * q - o1) / 10 /\ 10 * ((2 * q - o1) / 10) <= 2 * q - o1) /\
    (0 <= (3 * q - o2) / 10 /\ 10 * ((3 * q - o2) / 10) <= 3 * q - o2) /\ (0 <= (dcap - o3) / 10 /\ 10 * ((dcap - o3) / 10) <= dcap - o3) /\
    (0 <= i0 / 7 /\ 7 * (i0 / 7) <= i0).
  Proof using.
    intros q dcap' o0 o1 o2 o3 i0 n' H0 H1 H2 H3 HQ HQ3 HD HI HJ HN.
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [rewrite x42_l10 by lia; f_equal; lia|]. split; [rewrite x42_l10 by lia; f_equal; lia|].
    split; [apply x42_l7; lia|].
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
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
  (* [comment removed for export] *)
  Notation KOUT q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 :=
    (forall mm' i0' i1' i2' i3' o0' o1' o2' o3' (c0' c1' c2' c3' : word) (y5 y7 y8 y9 y10 y11 y12 y13 y14 y23 y25 y28 y29 y30 : word) (w'0 w'15 w'16 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 w'38 w'39 : word),
        X42PF mm' -> munch W0 m0 mm' -> wmono bsegs m0 mm' -> mem_inv bsegs mm' -> stk bsegs mm' DST (DST + dcap) -> bytes_at bsegs mm' DT dtb ->
        (FRS mm' w'0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) w'15 w'16 w'17 w'18 w'19 w'20 w'21 w'22 w'23 w'24 w'25 w'26 w'27 w'28 w'29 w'30 w'31 w'32 w'33 w'34 w'35 w'36 (Z_to_bv 64 (DT + 4)) w'38 w'39) ->
        (ARGS mm' av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
        bytes_at bsegs mm' SRC src ->
        0 <= i0' <= i0 -> 0 <= i1' <= i1 -> 0 <= i2' <= i2 -> 0 <= i3' <= i3 ->
        o0 + 5 <= o0' <= q -> o1 + 5 <= o1' <= 2 * q -> o2 + 5 <= o2' <= 3 * q -> o3 + 5 <= o3' <= dcap ->
        LBW 8 c0' -> LBW 8 c1' -> LBW 8 c2' -> LBW 8 c3' ->
        evtF bsegs RNG POST (ST 0x9bc40 mm' (Z_to_bv 64 (SRC + i3')) y5 (Z_to_bv 64 (DST + o0')) y7 y8 y9 y10 y11 y12 y13 y14 (Z_to_bv 64 (DST + o3')) (Z_to_bv 64 (DST + o2')) (Z_to_bv 64 (DST + o1')) (Z_to_bv 64 (SRC + i0')) (Z_to_bv 64 (SRC + i2')) (Z_to_bv 64 (DT + 4)) c2' c0' y23 c3' y25 (Z_to_bv 64 (SRC + i1')) SB y28 y29 y30 c1')).
  Notation x42e_fi := (AZ_huf_dx42_fij.x42e_fi RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11).
  Notation x42e_f2 := (AZ_huf_dx42_ff2.x42e_f2 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl lo src dtb CTX X2OK NBOK ACTX TL11 XMC).
  Notation WDA := [(DST, DST + dcap); (SPV - 576, SPV - 104)].

  (* [comment removed for export] *)
  Lemma x42e_fo_b : forall mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x5 x7 x8 x9 x11 x13 x14 x23 x25 x28 x29 x30 : word)
      (w0 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w38 w39 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 (Z_to_bv 64 (DT + 4)) w38 w39) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 < dcap -> 38 <= n -> 0 <= q -> 3 * q < dcap -> q = (dcap + 3) / 4 -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    0 <= R -> 10 * R <= q - o0 -> 10 * R <= 2 * q - o1 -> 10 * R <= 3 * q - o2 -> 10 * R <= dcap - o3 -> 7 * R <= i0 ->
    KOUT q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 ->
    evtF bsegs RNG POST (ST 0x9bd04 mm (Z_to_bv 64 (SRC + i3)) x5 (Z_to_bv 64 (DST + o0)) x7 x8 x9 (Z_to_bv 64 (R)) x11 (Z_to_bv 64 (14757395258967641293)) x13 x14 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (DT + 4)) c2 c0 x23 c3 x25 (Z_to_bv 64 (SRC + i1)) SB x28 x29 x30 c1).
  Proof using CTX X2OK NBOK ACTX TL11 XMC.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    intros mm q R nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x5 x7 x8 x9 x11 x13 x14 x23 x25 x28 x29 x30
      w0 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w38 w39
      PV MU0 WM0 MI OUT DTB FR AR SRCB HND DP N38 HQ0 HQ3 HQ H3Q HL1 HL2 HL3 HLN HI0 HN0 HI1 HN1 HI2 HN2 HI3 HN3 HO0 HO1 HO2 HO3 HLB0 HLB1 HLB2 HLB3 HR0 HRA HRB HRC HRD HR7 KO. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. kcleanF.
    pose proof (lbw_pos _ _ HLB0) as HLP0. pose proof (lbw_pos _ _ HLB1) as HLP1. pose proof (lbw_pos _ _ HLB2) as HLP2. pose proof (lbw_pos _ _ HLB3) as HLP3.
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (PVD : disjoint_from WDF (SPV + -104) 104 /\ disjoint_from WDF lo (SPV + -576 - lo))
      by (cbn [disjoint_from]; clear - R1 LO OS1; lia).
    destruct PVD as (PVD1 & PVD2).
    assert (KF : (0 <= o0 <= 4294967296) /\ (0 <= o1 <= 4294967296) /\ (0 <= o2 <= 4294967296) /\ (0 <= o3 <= 4294967296) /\
                 (0 <= i0 <= 4294967296) /\ (0 <= i1 <= 4294967296) /\ (0 <= i2 <= 4294967296) /\ (0 <= i3 <= 4294967296) /\
                 (0 <= q <= 4294967296) /\ (1 <= dcap <= 4294967296) /\ (0 <= R <= 4294967296) /\ (0 <= o3 + 5 * R <= 4294967296))
      by (clear - DP N38 HQ0 HQ3 HQ HI0 HN0 HI1 HN1 HI2 HN2 HI3 HN3 HO0 HO1 HO2 HO3 HR0 HRD R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10 & KF11 & KF12).
    pose proof (munch_refl WDF mm) as MUS. pose proof (wmono_refl bsegs mm) as WMS.
    kx_autoFLA (FR, AR) [KAApp (SPV - 576) 472] [0x9bd48; 0x9d0dc] 40%nat
      [KZRange R 0 4294967296; KZRange o0 0 4294967296; KZRange o1 0 4294967296; KZRange o2 0 4294967296; KZRange o3 0 4294967296;
       KZRange i0 0 4294967296; KZRange i1 0 4294967296; KZRange i2 0 4294967296; KZRange i3 0 4294967296; KZRange (o3 + 5 * R) 0 4294967296;
       KZRange dcap 1 4294967296; KZRange DST 4096 140737488355328; KZRange SRC 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZRange SPV 17594333498432 140737488355328; KZWr (SPV + -576) 320; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZDisj (SPV - 576) 320 DT 16388; KZDisj (SPV - 576) 320 SRC n; KZDisj DST dcap (SPV - 576) 472]
      [(SPV + -576, 320); (SPV + -256, 152)] [(SPV - 576, 576)].
    all: aside.
    all: clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10 KF11 KF12.
    all: try clear GF8 GF11 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc RSRCz USRCz; try clear DJF1 DJF3 DJF4 DJF5; try clear UDSTc RDSTc RDSTSc DSTAc RDSTz UDSTz.
    all: trapsF.
    all: aclean.
    all: kx_mem.
    all: kx_strip_mod.
    all: lclean3.
    all: lazymatch goal with
         | MUS : munch WDF ?m1 ?m2, WMS : wmono bsegs ?m1 ?m2 |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9d0dc) _ _ _ _) =>
             pose proof (x42pf_transport m1 m2 _ PV MUS WMS PVD1 PVD2) as PV2;
             eapply (x42e_f2 m2 l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3); first [exact PV2 | eassumption | lia | idtac]
         | MUS : munch WDF ?m1 ?m2 |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9bd48) _ _ _ _) =>
             assert (HR1 : 1 <= R) by lia;
             eapply (x42e_fi (Z.to_nat R) m2 m2 q (5 * R + o3) (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3);
             lazymatch goal with
             | |- forall _, _ => idtac
             | |- evtF _ _ _ _ => idtac
             | |- munch _ ?a ?a => apply munch_refl
             | |- wmono _ ?a ?a => apply wmono_refl
             | |- LBW _ _ => assumption
             | |- (1 <= Z.to_nat _)%nat => clear - HR1; lia
             | |- context [Z.of_nat (Z.to_nat ?X)] => rewrite (Z2Nat.id X) by lia; lia
             | |- _ => first [eassumption | reflexivity | lia]
             end
         end.
    (* [comment removed for export] *)
    all: intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros MU' WM' MU0' WM0' MI' OUT' DTB' FR' AR' SRCB' GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 GOL GL0 GL1 GL2 GL3.
    all: lazymatch goal with MU1 : munch WDL ?m2 ?m3, WM1 : wmono bsegs ?m2 ?m3, MUS : munch WDF ?m1 ?m2, WMS : wmono bsegs ?m1 ?m2 |- _ =>
           assert (MU1' : munch WDF m2 m3) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside fst snd app]; intros; lia);
           pose proof (x42pf_transport m1 m3 _ PV (munch_trans _ _ _ _ MUS MU1') (wmono_trans _ _ _ _ WMS WM1) PVD1 PVD2) as PV' end.
    all: eapply (KO _ i0' i1' i2' i3' o0' o1' o2' o3'); first [exact PV' | eassumption | lia | idtac].
  Qed.

  (* [comment removed for export] *)
  Lemma x42e_fo : forall (k : nat) mm q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 (c0 c1 c2 c3 : word) (av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 : word)
      (x5 x7 x8 x9 x10 x11 x12 x13 x14 x23 x25 x28 x29 x30 : word)
      (w0 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w38 w39 : word),
    X42PF mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    (FRS mm w0 (Z_to_bv 64 (DT)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (n)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (dcap)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (14757395258967641293)) (Z_to_bv 64 (2635249153387078803)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + 3 * q)) (Z_to_bv 64 (DST + 2 * q)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (DT + 4)) w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 (Z_to_bv 64 (DT + 4)) w38 w39) ->
    (ARGS mm av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (SRC + 6)) (Z_to_bv 64 (SRC + 6 + l1)) (Z_to_bv 64 (SRC + 6 + l1 + l2)) (Z_to_bv 64 (SRC + 6 + l1 + l2 + l3))) ->
    bytes_at bsegs mm SRC src -> nd = -1 * DT + -5 ->
    0 < dcap -> 38 <= n -> 0 <= q -> 3 * q < dcap -> q = (dcap + 3) / 4 -> DST + 3 * ((dcap + 3) / 4) < DST + dcap ->
    8 <= l1 -> 8 <= l2 -> 8 <= l3 -> 6 + l1 + l2 + l3 + 8 <= n ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    0 <= o0 <= q -> q <= o1 <= 2 * q -> 2 * q <= o2 <= 3 * q -> 3 * q <= o3 <= dcap ->
    LBW 8 c0 -> LBW 8 c1 -> LBW 8 c2 -> LBW 8 c3 ->
    dcap - o3 < Z.of_nat k ->
    evtF bsegs RNG POST (ST 0x9bc40 mm (Z_to_bv 64 (SRC + i3)) x5 (Z_to_bv 64 (DST + o0)) x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DST + o3)) (Z_to_bv 64 (DST + o2)) (Z_to_bv 64 (DST + o1)) (Z_to_bv 64 (SRC + i0)) (Z_to_bv 64 (SRC + i2)) (Z_to_bv 64 (DT + 4)) c2 c0 x23 c3 x25 (Z_to_bv 64 (SRC + i1)) SB x28 x29 x30 c1).
  Proof using CTX X2OK NBOK ACTX TL11 XMC.
    pose proof CTX as CTX'. x42e_ctx_open CTX'. pose proof ACTX as ACTX'. x42e_actx_open ACTX'.
    induction k as [|k IH]; intros mm q nd l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3 c0 c1 c2 c3 av0 av1 av2 av3 av4 av5 av6 av7 av8 av9 av10 av11
      x5 x7 x8 x9 x10 x11 x12 x13 x14 x23 x25 x28 x29 x30
      w0 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w38 w39
      PV MU0 WM0 MI OUT DTB FR AR SRCB HND DP N38 HQ0 HQ3 HQ H3Q HL1 HL2 HL3 HLN HI0 HN0 HI1 HN1 HI2 HN2 HI3 HN3 HO0 HO1 HO2 HO3 HLB0 HLB1 HLB2 HLB3 HK; [exfalso; clear - HK HO3; lia|]. subst nd.
    facts R1 R2 R3 TL LO SPB KLO. kcleanF.
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : (0 <= o0 <= 4294967296) /\ (0 <= o1 <= 4294967296) /\ (0 <= o2 <= 4294967296) /\ (0 <= o3 <= 4294967296) /\
                 (0 <= i0 <= 4294967296) /\ (0 <= i1 <= 4294967296) /\ (0 <= i2 <= 4294967296) /\ (0 <= i3 <= 4294967296) /\
                 (0 <= q <= 4294967296) /\ (1 <= dcap <= 4294967296)) by (clear - DP N38 HQ0 HQ3 HQ HI0 HN0 HI1 HN1 HI2 HN2 HI3 HN3 HO0 HO1 HO2 HO3 R1 R2; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9 & KF10).
    kx_autoFLA (FR, AR) [KAApp (SPV - 576) 472] [0x9bd04] 120%nat
      [KZRange o0 0 4294967296; KZRange o1 0 4294967296; KZRange o2 0 4294967296; KZRange o3 0 4294967296;
       KZRange i0 0 4294967296; KZRange i1 0 4294967296; KZRange i2 0 4294967296; KZRange i3 0 4294967296; KZRange q 0 4294967296;
       KZRange dcap 1 4294967296; KZRange DST 4096 140737488355328; KZRange SRC 4096 140737488355328; KZRange DT 4096 140737488338940;
       KZRange SPV 17594333498432 140737488355328; KZWr (SPV + -576) 320; KZRange (q - o0) 0 4294967296; KZRange (2 * q - o1) 0 4294967296;
       KZRange (3 * q - o2) 0 4294967296; KZRange (dcap - o3) 0 4294967296; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZDisj (SPV - 576) 320 DT 16388; KZDisj (SPV - 576) 320 SRC n; KZDisj DST dcap (SPV - 576) 472]
      [(SPV + -576, 320); (SPV + -256, 152)] [(SPV - 576, 576)].
    all: aside.
    all: clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9 KF10.
    all: trapsF.
    all: x42_mulhu_rb.
    all: kx_mem.
    (* [comment removed for export] *)
    all: pose proof (x42_fo_eqs q dcap o0 o1 o2 o3 i0 n ltac:(clear - HO0; lia) ltac:(clear - HO1 HQ0; lia) ltac:(clear - HO2 HQ0; lia)
                       ltac:(clear - HO3 HQ0; lia) HQ0 ltac:(clear - HQ3; lia) ltac:(clear - R1; lia) HI0 HN0 ltac:(clear - R2; lia)) as (E0 & E1 & E2 & E3 & E7 & HQA & HQB & HQC & HQD & HQ7).
    all: rewrite ?E0, ?E1, ?E2, ?E3, ?E7 in *.
    all: clear E0 E1 E2 E3 E7.
    all: set (Q0 := (q - o0) / 10) in *; set (Q1 := (2 * q - o1) / 10) in *; set (Q2 := (3 * q - o2) / 10) in *;
         set (Q3 := (dcap - o3) / 10) in *; set (Q7 := i0 / 7) in *.
    all: clearbody Q0 Q1 Q2 Q3 Q7.
    all: kx_strip_mod.
    all: lclean3.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9bd04) _ _ ?m2 _) =>
             try replace (DST + o3 + 5 * R) with (DST + (o3 + 5 * R)) by (clear; lia);
             eapply (x42e_fo_b m2 q R (-1 * DT + -5) l1 l2 l3 i0 i1 i2 i3 o0 o1 o2 o3);
             first [ exact PV | eassumption | reflexivity | lazymatch goal with |- forall _, _ => idtac end | lia ]
         end.
    all: intros mm' i0' i1' i2' i3' o0' o1' o2' o3' c0' c1' c2' c3'; repeat (let y := fresh "yy" in intro y; lazymatch type of y with word => idtac end);
         intros PV' MU0' WM0' MI' OUT' DTB' FR' AR' SRCB' GI0 GI1 GI2 GI3 GO0 GO1 GO2 GO3 GL0 GL1 GL2 GL3.
    all: eapply (IH mm' q (-1 * DT + -5) l1 l2 l3 i0' i1' i2' i3' o0' o1' o2' o3'); first [exact PV' | exact FR' | exact AR' | eassumption | reflexivity | lia].
  Qed.
End DX42FFO.
End CANSEC1.
