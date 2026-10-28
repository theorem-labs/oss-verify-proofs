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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a.
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
  Hypothesis BITINIT : bit_init_stmtA.

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
    assert (ZS1 : 0 <= SRC - 0 < 2 ^ 64 /\ 0 <= n < 2 ^ 64 /\ 0 <= SRC < 2 ^ 64) by (kx_clear_or; lia);
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
  Notation x41_i4_stmt := (AZ_huf_dx41.x41_i4_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb).
  Notation x41_m0_stmt := (AZ_huf_dx41.x41_m0_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo dtb).

  (* [comment removed for export] *)
  Lemma x41_einvS : forall mm rest,
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ X41JK SPV mm rest ->
    mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm ->
    stk bsegs mm lo (SPV + -496) ->
    stk bsegs mm (SPV + -496) (SPV + -496 + Z.of_nat 136) -> stk bsegs mm (SPV + -360) (SPV + -360 + Z.of_nat 8) ->
    stk bsegs mm (SPV + -352) (SPV + -352 + Z.of_nat 96) -> stk bsegs mm (SPV + -256) (SPV + -256 + Z.of_nat 40) -> EINVA mm.
  Proof using CTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'.
    intros mm rest (SV & RS) MI OUT MU0 WM0 STK H1 H2 H3 H4.
    pose proof (stk_of_rw_cells bsegs mm _ _ RS) as H5. cbn [cells_size csize Nat.add] in H5.
    change (Z.of_nat 136) with 136 in H1. change (Z.of_nat 8) with 8 in H2. change (Z.of_nat 96) with 96 in H3.
    change (Z.of_nat 40) with 40 in H4. change (Z.of_nat 112) with 112 in H5.
    replace (SPV + -496 + 136) with (SPV + -360) in H1 by lia.
    replace (SPV + -360 + 8) with (SPV + -352) in H2 by lia.
    replace (SPV + -352 + 96) with (SPV + -256) in H3 by lia.
    replace (SPV + -256 + 40) with (SPV + -216) in H4 by lia.
    replace (SPV + -216 + 112) with (SPV + -104) in H5 by lia.
    unfold AZ_huf_dx41.EINVA. split; [exact OUT|]. split; [exact SV|]. split; [|split; [exact MU0|split; [exact WM0|exact MI]]].
    eapply (stk_merge bsegs mm lo (SPV + -216)); [|exact H5|lia].
    eapply (stk_merge bsegs mm lo (SPV + -256)); [|exact H4|lia].
    eapply (stk_merge bsegs mm lo (SPV + -352)); [|exact H3|lia].
    eapply (stk_merge bsegs mm lo (SPV + -360)); [|exact H2|lia].
    eapply (stk_merge bsegs mm lo (SPV + -496)); [exact STK|exact H1|lia].
  Qed.
  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac err_ret PV1 HER HRB := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    eapply (x41_ret m2 _);
    [ eapply (x41_einvS m2 _);
      [ exact PV1 | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -496) | tostk (SPV + -360) | tostk (SPV + -352) | tostk (SPV + -256) ]
    | right; split; [exact HER | exact HRB] ] end.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a0 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  (* [comment removed for export] *)
  Ltac hold_ors := repeat match goal with H : _ \/ _ |- _ => apply x41_held_intro in H end.
  Ltac unhold_ors := repeat match goal with H : x41_held _ |- _ => unfold x41_held in H end.
  Lemma x41i4_slice : forall (m : amem) a (bs : list byte) off k,
    bytes_at bsegs m a bs -> (off + k <= length bs)%nat -> bytes_at bsegs m (a + Z.of_nat off) (firstn k (skipn off bs)).
  Proof.
    intros m a bs off k H Hk. rewrite <- (firstn_skipn off bs) in H.
    apply OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.Mem.bytes_at_app in H. destruct H as [_ H].
    rewrite length_firstn in H. replace (Nat.min off (length bs)) with off in H by lia.
    rewrite <- (firstn_skipn k (skipn off bs)) in H.
    apply OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.Mem.bytes_at_app in H. destruct H as [H _]. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_i4 : x41_m0_stmt -> x41_i4_stmt.
  Proof using CTX ACTX DHI NBOK BITINIT rc.
    intros HM0. unfold AZ_huf_dx41.x41_m0_stmt in HM0. unfold AZ_huf_dx41.x41_i4_stmt.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros mm rest jb dl l1 l2 l3 LL o1 b1 o2 b2 o3 b3 c1 c2 c3
      w8 w16 w40 w48 w56 w64 w72 w80 w88 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192
      x5 x6 x7 x10 x12 x14 x15 x16 x17
      SV RS MU0 WM0 MI OUT DTB SRCB STK XSA XSH XSB BJ HDC HN HL1 HL2 HL3 HLL HLN HSG HDL HL2p HL3p
      HO1 HO1b HB1 HB1b HO2 HO2b HB2 HB2b HO3 HO3b HB3 HB3b.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    remember (SRC + 6 + l1 + l2 + l3) as S4 eqn:HS4.
    assert (EX4 : exists n4, n4 = n - LL) by (exists (n - LL); reflexivity).
    destruct EX4 as (n4 & HN4).
    assert (KF : SRC <= S4 /\ S4 + n4 <= SRC + n /\ 0 <= n4 /\ 4096 <= S4 <= 140737488355328 /\ n4 <= 4294967296)
      by (clear - HS4 HN4 HLL HLN HL1 HL2 HL3 R2; lia).
    destruct KF as (SS4 & SE4 & LN4 & KF1 & KF2).
    hold_ors. unfold x41_held in OS1, OS2, OS3.
    (* [comment removed for export] *)
    kx_autoFLA tt (@nil kza) [APHUF_BITINIT] 12%nat
      [KZRange n 10 4294967296; KZRange LL 0 4294967296; KZRange (n - LL) 0 4294967296; KZRange n4 0 4294967296;
       KZRange S4 4096 140737488355328; KZRange SPV 17594333498016 140737488355328]
      (@nil (Z * Z)) [(SPV - 496, 496)].
    all: [> aside ..].
    all: [> kx_mem ..].
    all: try clear KXK KXA KXRD; try clear KXE.
    all: fix_a2 n4. all: fix_a1 S4. all: fix_a0 (SPV + -256).
    (* [comment removed for export] *)
    assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    assert (AZmm : azstk RNG mm lo SPV).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply azstk_transport; [exact AZS | exact MU0 | exact WM0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - LO; lia].
      - eapply azstk_transport; [exact AZS | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                                | exact WM0 | exact AW0 | clear - LO; lia]. }
    assert (ARTmm : art mm).
    { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd].
      - eapply (art_transportW W0 m0 mm ART MU0 WM0). constructor; [cbn [fst]; pose proof (DHI Hd); unfold dst_hi in *; lia | constructor; [cbn [fst]; clear - LO KLO; lia | constructor]].
      - eapply (art_transportW [(SPV - 2720, SPV)] m0 mm ART); [| exact WM0 |].
        + eapply munch_drop_empty. replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia). exact MU0.
        + constructor; [cbn [fst]; clear - LO KLO; lia | constructor]. }
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    assert (SB1 : bytes_at bsegs mm (SRC + 6) (firstn (Z.to_nat l1) (skipn 6 src))).
    { change (SRC + 6) with (SRC + Z.of_nat 6). apply x41i4_slice; [exact SRCB | clear - SL HLL HLN HL1 HL2 HL3; lia]. }
    assert (SB2 : bytes_at bsegs mm (SRC + 6 + l1) (firstn (Z.to_nat l2) (skipn (Z.to_nat (6 + l1)) src))).
    { replace (SRC + 6 + l1) with (SRC + Z.of_nat (Z.to_nat (6 + l1))) by (clear - HL1; lia).
      apply x41i4_slice; [exact SRCB | clear - SL HLL HLN HL1 HL2 HL3; lia]. }
    assert (SB3 : bytes_at bsegs mm (SRC + 6 + l1 + l2) (firstn (Z.to_nat l3) (skipn (Z.to_nat (6 + l1 + l2)) src))).
    { replace (SRC + 6 + l1 + l2) with (SRC + Z.of_nat (Z.to_nat (6 + l1 + l2))) by (clear - HL1 HL2; lia).
      apply x41i4_slice; [exact SRCB | clear - SL HLL HLN HL1 HL2 HL3; lia]. }
    assert (SB4 : bytes_at bsegs mm S4 (firstn (Z.to_nat n4) (skipn (Z.to_nat LL) src))).
    { replace S4 with (SRC + Z.of_nat (Z.to_nat LL)) by (clear - HS4 HLL HL1 HL2 HL3; lia).
      apply x41i4_slice; [exact SRCB | clear - SL HN4 HLL HLN HL1 HL2 HL3; lia]. }
    set (bs1 := firstn (Z.to_nat l1) (skipn 6 src)) in SB1.
    set (bs2 := firstn (Z.to_nat l2) (skipn (Z.to_nat (6 + l1)) src)) in SB2.
    set (bs3 := firstn (Z.to_nat l3) (skipn (Z.to_nat (6 + l1 + l2)) src)) in SB3.
    set (bs4 := firstn (Z.to_nat n4) (skipn (Z.to_nat LL) src)) in SB4.
    assert (BL1 : Z.of_nat (length bs1) = l1) by (subst bs1; rewrite length_firstn, length_skipn; clear - SL HLL HLN HL1 HL2 HL3; lia).
    assert (BL2 : Z.of_nat (length bs2) = l2) by (subst bs2; rewrite length_firstn, length_skipn; clear - SL HLL HLN HL1 HL2 HL3; lia).
    assert (BL3 : Z.of_nat (length bs3) = l3) by (subst bs3; rewrite length_firstn, length_skipn; clear - SL HLL HLN HL1 HL2 HL3; lia).
    assert (BL4 : Z.of_nat (length bs4) = n4) by (subst bs4; rewrite length_firstn, length_skipn; clear - SL HN4 HLL HLN HL1 HL2 HL3; lia).
    clearbody bs1 bs2 bs3 bs4.
    assert (AROS : 0 < n4 -> aro RNG mm S4 n4).
    { intros Hn. eapply aro_sub; [split; [exact USRCc | split; [exact RSRC | exact RSRCS]] | exact SS4 | exact LN4 | exact SE4]. }
    assert (RBD : rng RNG (SPV + -256) 40) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (AROB : aro RNG mm (SPV + -256) 40) by (eapply azstk_aro; [exact AZmm | clear - LO; lia | clear; lia | clear; lia | exact RBD]).
    assert (AHB : ahull RNG mm (SPV + -256) 40) by (eapply azstk_ahull; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
    assert (APB : app_blk (SPV + -256) (SPV + -256 + 40)) by (eapply azstk_app; [exact AZmm | clear - LO; lia | clear; lia | clear; lia]).
    assert (ASTK' : astk RNG lo (SPV + -496)).
    { split; [unfold KHIGH; clear - KLO; lia | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - LO; lia] | exact RI]]. }
    assert (BDA : (SPV + -256) mod 8 = 0) by (clear - SPA SPB LO; Z.div_mod_to_equations; lia).
    assert (NUMS : (4096 <= SPV + -256) /\ (SPV + -256 + 40 < 2^47) /\ (4096 <= S4) /\ (S4 + n4 < 2^47) /\ (n4 < 2^32) /\
                   (SPV + -256 + 40 <= S4 \/ S4 + n4 <= SPV + -256) /\ (lo <= SPV + -496 - 2224) /\ (SPV + -496 < 2^47) /\
                   (SPV + -256 + 40 <= lo \/ SPV + -496 <= SPV + -256) /\ (S4 + n4 <= lo \/ SPV + -496 <= S4))
      by (clear - LO SPB R2 SS4 SE4 LN4 OS2; lia).
    destruct NUMS as (P6 & P7 & P8 & P9 & P10 & P11 & P13 & P14 & P15 & P16).
    clear USRCc AZmm AW0 RBD KF1 KF2.
    clear AZS ARC ART USRC UDT UDST RDST RDSTS RDT RDTS RSRC RSRCS.
    eapply evtF_cut;
      [ eapply (bit_init_g BITINIT RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (SPV + -496) (SPV + -256) S4 n4 lo bs4 jb);
        [ exact MI | exact BJ | exact BDA | exact SB4 | exact BL4 | exact P6 | exact P7 | exact P8 | exact P9 | exact P10 | exact P11
        | exact STK | exact P13 | exact P14 | exact P15 | exact P16 | exact APB | exact AROB | exact AHB | exact AROS | exact ARTmm | exact ASTK' ]
      | clear ARTmm AROS AROB AHB APB ASTK' BDA P6 P7 P8 P9 P10 P11 P13 P14 P15 P16 BJ STK;
        unfold bit_init_postA; post_call bsegs mm ].
    unhold_ors. try clear MI.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    (* [comment removed for export] *)
    lazymatch goal with SV' : rw_cells _ m2 (SPV + -104) _, RS' : rw_cells _ m2 (SPV + -216) [CB 112 rest], ST' : stk _ m2 lo (SPV + -496) |- _ =>
      pose proof (conj SV' RS') as PV1; rename ST' into STK1 end.
    destruct POST as [(HR & HN1 & cont & bc & pad & HC1 & HC2 & BDC) | (HER & HRB & bs & BDC)].
    - (* [comment removed for export] *)
      lazymatch type of HR with ?rr = n4 => subst rr end. unfold bitd_cells in BDC.
      replace (bitd_ptr S4 n4) with (S4 + (bitd_ptr S4 n4 - S4)) in BDC by ring.
      kx_autoFLA tt (@nil kza) [0xa6b54; 0xa7af8] 12%nat
        [KZRange n4 1 4294967296; KZRange SPV 17594333498016 140737488355328] (@nil (Z * Z)) [(SPV - 496, 496)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa6b54) _ _ _ _) =>
             eapply (HM0 m2 rest dl (SRC + 6) l1 bs1 o1 b1 (SRC + 6 + l1) l2 bs2 o2 b2 (SRC + 6 + l1 + l2) l3 bs3 o3 b3 S4 n4 bs4 (bitd_ptr S4 n4 - S4) bc
                         c1 c2 c3 cont pad w8 w16 w40 w48 w56 w64 w72 w80 w88 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192);
             first [ eassumption
                   | unfold AZ_huf_dx41.HINVA; unfold bitd_ptr; clear - HN1 HC1 HC2; destruct (Z.leb_spec 8 n4); lia
                   | unfold AZ_huf_dx41.HINVA; clear - HO1 HO1b HB1 HB1b; lia
                   | unfold AZ_huf_dx41.HINVA; clear - HO2 HO2b HB2 HB2b; lia
                   | unfold AZ_huf_dx41.HINVA; clear - HO3 HO3b HB3 HB3b; lia
                   | kx_lia_m1 ] end.
    - (* [comment removed for export] *)
      lazymatch type of HER with zd_is_error ?rr = true => rename rr into r end.
      assert (HERR : 18446744073709551497 <= r <= 18446744073709551615) by (unfold zd_is_error, ZE_maxCode in HER; apply Z.ltb_lt in HER; clear - HER HRB; lia).
      kx_autoFLA tt (@nil kza) [0xa6b54; 0xa7af8] 12%nat
        [KZRange r 18446744073709551497 18446744073709551615; KZRange SPV 17594333498016 140737488355328] (@nil (Z * Z)) [(SPV - 496, 496)].
      all: [> aside ..].
      all: [> kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] ..].
      all: [> intros; kx_mem ..].
      all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) => err_ret PV1 HER HRB end.
  Qed.
End DX41AM.
End CANSEC1.
