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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a AZ_hufkit42e2.
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
  Ltac zsfacts :=
    assert (ZS1 : 0 <= DST - 0 < 2 ^ 64 /\ 0 <= dcap < 2 ^ 64 /\ 0 <= DST < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS2 : 0 <= DT - 0 < 2 ^ 64 /\ 0 <= 16388 < 2 ^ 64 /\ 0 <= DT < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS3 : 0 <= SPV - 352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV - 352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS4 : 0 <= SPV + -352 - -352 < 2 ^ 64 /\ 0 <= 96 < 2 ^ 64 /\ 0 <= SPV + -352 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS5 : 0 <= SPV + -496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV + -496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS6 : 0 <= SPV + -360 - -360 < 2 ^ 64 /\ 0 <= 8 < 2 ^ 64 /\ 0 <= SPV + -360 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS7 : 0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 496 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64) by (kx_clear_or; lia);
    assert (ZS8 : 17594333498016 <= SPV <= 140737488355328) by (kx_clear_or; lia).
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
  Notation EINVA := (AZ_huf_dx41.EINVA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x41_i1_stmt := (AZ_huf_dx41.x41_i1_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb).
  Notation x41_s0_stmt := (AZ_huf_dx41.x41_s0_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT lo src dtb).

  (* [comment removed for export] *)
  Lemma x41_sbufA : forall mm A bs B k len, bytes_at bsegs mm A bs -> 0 <= k -> 0 <= len -> k + len <= zlen bs -> B = A + k ->
    bytes_at bsegs mm B (firstn (Z.to_nat len) (skipn (Z.to_nat k) bs)).
  Proof.
    intros mm A bs B k len HB HK HLEN HKL ->.
    rewrite <- (firstn_skipn (Z.to_nat k) bs) in HB. apply bytes_at_app in HB as [_ HB].
    rewrite firstn_length in HB. rewrite Nat.min_l in HB by lia. rewrite Z2Nat.id in HB by lia.
    rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat k) bs)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
  Qed.
  Lemma x41_sbufL : forall (bs : list byte) k len, 0 <= k -> 0 <= len -> k + len <= zlen bs ->
    zlen (firstn (Z.to_nat len) (skipn (Z.to_nat k) bs)) = len.
  Proof. intros bs k len HK HLEN HKL. rewrite firstn_length, skipn_length. lia. Qed.

  (* [comment removed for export] *)
  Ltac kcleanS :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac err_ret := lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m2 _) =>
        replace a0 with (Z_to_bv 64 (bv_unsigned a0)) by (apply Z_to_bv_bv_unsigned);
        eapply (x41_ret m2 (bv_unsigned a0));
        [ unfold AZ_huf_dx41.EINVA; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
          split; [eassumption|]; split; eassumption
        | right; split; vm_compute; reflexivity ]
    end.
  Lemma x41_regs_cast : forall sg R Q r r' F1 p fc1 m rom,
    evtF sg R Q (MS r' F1 p fc1 None m rom) -> r' = r -> evtF sg R Q (MS r F1 p fc1 None m rom).
  Proof. intros sg R Q r r' F1 p fc1 m rom H E. subst r'. exact H. Qed.
  Ltac x41_zv y := lazymatch y with Z_to_bv 64 ?e => e | _ => constr:(bv_unsigned y) end.
  Ltac regeq := first [ reflexivity | apply Z_to_bv_bv_unsigned | f_equal; lia | apply bv64_eqm_k; reflexivity ].
  Ltac s0side := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- _ => first [ eassumption | reflexivity | lia | Z.div_mod_to_equations; lia ]
    end.
  Ltac fix_s2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_s11 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac lsideS := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- bytes_at _ _ _ (firstn _ _) => eapply x41_sbufA; [eassumption | lia | lia | lia | lia]
    | |- zlen (firstn _ _) = _ => apply x41_sbufL; lia
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z.le _ _ => first [assumption | lia]
    | |- _ => first [eassumption | lia]
    end.

  (* [comment removed for export] *)
  Lemma x41_s0 : x41_i1_stmt -> x41_s0_stmt.
  Proof using CTX ACTX DHI NBOK rc.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros I1. unfold AZ_huf_dx41.x41_i1_stmt in I1. unfold AZ_huf_dx41.x41_s0_stmt.
    intros mm x5 x7 x9 x10 x11 x12 x13 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x31
      SV SH MU0 WM0 MI OUT DTB SRCB STK.
    facts R1 R2 R3 TL RSV LO SPB KLO. afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    destruct (ZdCellKit.stk_open bsegs mm lo (SPV + -104) (SPV + -216) 112 STK ltac:(clear - LO; lia)
                ltac:(change (Z.of_nat 112) with 112; clear - LO; lia)) as (jk & JK & STK1 & _).
    destruct (ZdCellKit.stk_open bsegs mm lo (SPV + -216) (SPV + -256) 40 STK1 ltac:(clear - LO; lia)
                ltac:(change (Z.of_nat 40) with 40; clear - LO; lia)) as (jb & BJ & STK2 & _).
    destruct (ZdCellKit.stk_open bsegs mm lo (SPV + -256) (SPV + -352) 96 STK2 ltac:(clear - LO; lia)
                ltac:(change (Z.of_nat 96) with 96; clear - LO; lia)) as (jsb & SB0 & STK3 & _).
    destruct (ZdCellKit.stk_open bsegs mm lo (SPV + -352) (SPV + -360) 8 STK3 ltac:(clear - LO; lia)
                ltac:(change (Z.of_nat 8) with 8; clear - LO; lia)) as (jsh & _ & STK4 & _).
    destruct (ZdCellKit.stk_open bsegs mm lo (SPV + -360) (SPV + -496) 136 STK4 ltac:(clear - LO; lia)
                ltac:(change (Z.of_nat 136) with 136; clear - LO; lia)) as (jsa & SA0 & STK5 & _).
    clear STK1 STK2 STK3 STK4 jsh.
    assert (SAx : exists w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word,
                    X41SA SPV mm w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128)
      by (pose proof (e42_cb_as_c8s mm _ 17 jsa SA0) as HC; cbn [e42_c8s_of] in HC; do 17 eexists; exact HC).
    destruct SAx as (w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & SA).
    assert (SBx : exists w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word,
                    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232)
      by (pose proof (e42_cb_as_c8s mm _ 12 jsb SB0) as HC; cbn [e42_c8s_of] in HC; do 12 eexists; exact HC).
    destruct SBx as (w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & w216 & w224 & w232 & SBK).
    clear SA0 SB0 jsa jsb.
    assert (SFD : (SPV - 496 + 136 <= SRC \/ SRC + n <= SPV - 496) /\ (SPV - 496 + 136 <= DT \/ DT + 16388 <= SPV - 496) /\
                  (DST + dcap <= SPV - 496 \/ SPV - 496 + 496 <= DST))
      by (clear - OS1 OS2 OS3 LO; lia).
    destruct SFD as (SFD1 & SFD2 & SFD3).
    destruct (Z_lt_le_dec dcap 6) as [DC|DC]; [| destruct (Z_lt_le_dec n 10) as [N10|N10]].
    - (* [comment removed for export] *)
      kclean.
      kx_autoFLA SA (@nil kza) [0xa61a8; 0xa62d0; 0xa7af8] 70%nat
        [KZRange dcap 0 5; KZRange n 0 4294967296; KZRange SPV 17594333498016 140737488355328; KZWr (SPV + -496) 136]
        [(SPV + -496, 136)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: err_ret.
    - (* [comment removed for export] *)
      kclean.
      kx_autoFLA SA (@nil kza) [0xa61a8; 0xa62d0; 0xa7af8] 70%nat
        [KZRange dcap 6 4294967296; KZRange n 0 9; KZRange SPV 17594333498016 140737488355328; KZWr (SPV + -496) 136]
        [(SPV + -496, 136)] [(SPV - 496, 496)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: err_ret.
    - (* [comment removed for export] *)
      sfacts0 MU0 USRC DSTA AW0 R1 R2.
      pose proof (unpoisoned_unpZ _ _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2; lia)) as USz.
      pose proof (rng_shspanZ _ _ _ RSRCS) as RSRCz.
      assert (ZSS : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (clear - R2; lia).
      zsfacts. kcleanS.
      assert (HSG : 3 * ((dcap + 3) / 4) <= dcap) by (clear - DC; Z.div_mod_to_equations; lia).
      assert (KF : (9 <= dcap + 3 <= 4294967299) /\ (4096 <= DST + dcap <= 140737488355328) /\ (10 <= n <= 4294967296) /\ (6 <= dcap <= 4294967296) /\
                   (0 <= DT < 2 ^ 64) /\ (4100 <= DT + 4 <= 140737488338944) /\ (0 <= SRC < 2 ^ 64) /\ (0 <= SPV - 496 < 2 ^ 64) /\
                   (0 <= SPV - 496 - -496 < 2 ^ 64 /\ 0 <= 136 < 2 ^ 64 /\ 0 <= SPV - 496 < 2 ^ 64))
        by (clear - DC N10 R1 R2 R3 GF7; lia).
      pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9).
      (* [comment removed for export] *)
      repeat match goal with H : _ \/ _ |- _ => apply x41_held_intro in H end.
      unfold x41_held in SFD1, SFD2, SFD3.
      kx_autoFLA SA [KAUnp SRC n; KAUnp DT 16388; KAApp (SPV - 496) 136] [0xa61a8; 0xa62d0; 0xa7af8] 120%nat
        [KZRange n 10 4294967296; KZRange dcap 6 4294967296; KZRange (dcap + 3) 9 4294967299; KZRange (DST + dcap) 4096 140737488355328;
         KZRange DST 4096 140737488355328; KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange (DT + 4) 4100 140737488338944;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange SPV 17594333498016 140737488355328;
         KZRange tl 1 12; KZRange rsv 0 255;
         KZWr (SPV + -496) 136; KZDisj (SPV - 496) 136 SRC n; KZDisj (SPV - 496) 136 DT 16388; KZDisj DST dcap (SPV - 496) 496]
        [(SRC, n); (DT, 16388); (SPV + -496, 136)] [(SRC, n); (DT, 16388); (SPV - 496, 496)].
      all: [> aside ..].
      all: unfold x41_held in *.
      all: try clear KF KF1 KF2 KF3 KF4 KF5 KF6 KF7 KF8 KF9.
      (* [comment removed for export] *)
      all: repeat match goal with
           | |- context [ev _ ?J] =>
               let RD := fresh "RD" in
               kx_read_eq J RD;
               rewrite (rdval_bytes_at bsegs _ DT dtb 2 2 false DTB ltac:(lia) ltac:(change (Z.to_nat 2) with 2%nat; lia)),
                       (dl_read_g dtb tl rsv DT2 DT3 ltac:(lia) ltac:(lia)) in RD;
               rewrite RD; clear RD
           end.
      all: try clear GF8 GF9 GF10 GF11 GF12 GF13; try clear AW0 UDTc RDTz UDTz RFR; try clear USRCc; try clear USz RSRCz ZSS;
           try clear ZS1 ZS2 ZS3 ZS4 ZS5 ZS6 ZS7 ZS8.
      all: aclean.
      all: [> lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) =>
               kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
           | |- _ => kx_gen_regsF [5%nat; 7%nat; 17%nat; 22%nat; 24%nat; 25%nat; 26%nat; 27%nat]
           end ..].
      all: [> intros; evr; kx_mem ..].
      all: [> kx_sx3; kx_strip_mod ..].
      all: try rewrite (Z.mod_small (dcap + 3) (2^64)) in * by lia.
      (* [comment removed for export] *)
      all: lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) => err_ret
           | |- evtF _ _ _ (MS (mkR _ _ _ _ ?y5 _ ?y7 _ _ _ _ _ _ _ ?y15 ?y16 ?y17 _ _ _ _ ?y22 _ ?y24 ?y25 ?y26 ?y27 _ _ _ ?y31) _ _ _ _ ?m1 _) =>
               (* [comment removed for export] *)
               let L1 := x41_zv y16 in let L2 := x41_zv y15 in let L3 := x41_zv y31 in
               eapply x41_regs_cast;
               [ eapply (I1 m1 jk jb _ (tl + 256 * rsv) L1 L2 L3 (L1 + L2 + L3 + 6)
                          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y5 y7 y17 y22 y24 y25 y26 y27); s0side
               | f_equal; regeq ]
           end.
  Qed.
End DX41AM.
End CANSEC1.
