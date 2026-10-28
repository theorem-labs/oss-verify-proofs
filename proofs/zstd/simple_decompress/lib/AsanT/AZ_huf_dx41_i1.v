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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx41 AZ_huf_dx41_4a.
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
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H | H : rng _ _ _ |- accP _ _ _ => kx_acc H end.
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
  Notation x41_i2_stmt := (AZ_huf_dx41.x41_i2_stmt RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb).
  Lemma x41_einvJ : forall mm rest jb (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
    rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    X41JK SPV mm rest -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> munch W0 m0 mm -> wmono bsegs m0 mm ->
    stk bsegs mm lo (SPV + -496) ->
    X41SA SPV mm w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 -> X41SH SPV mm ->
    X41SB SPV mm w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 -> rw_cells bsegs mm (SPV + -256) [CB 40 jb] ->
    EINVA mm.
  Proof using CTX.
    pose proof CTX as CTX'. x41a_ctx_open CTX'.
    intros until w232. intros SV RS MI OUT MU0 WM0 STK SA SH SB4 B4.
    pose proof (stk_of_rw_cells bsegs mm _ _ SA) as H1.
    pose proof (stk_of_rw_cells bsegs mm _ _ SH) as H2.
    pose proof (stk_of_rw_cells bsegs mm _ _ SB4) as H3.
    pose proof (stk_of_rw_cells bsegs mm _ _ B4) as H4.
    pose proof (stk_of_rw_cells bsegs mm _ _ RS) as H5.
    cbn [cells_size csize Nat.add] in H1, H2, H3, H4, H5.
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
  (* [comment removed for export] *)
  Ltac err_ret := lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m2 _) =>
        replace a0 with (Z_to_bv 64 (bv_unsigned a0)) by (apply Z_to_bv_bv_unsigned);
        eapply (x41_ret m2 (bv_unsigned a0));
        [ eapply x41_einvJ; eassumption | right; split; vm_compute; reflexivity ]
    end.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac hb_brute :=
    cbn [edenot];
    lazymatch goal with |- context [ev ?E ?j] =>
      let HR := fresh "HR" in let HB := fresh "HB" in
      assert (HR : 1 <= bv_unsigned (ev E j) < 1 + Z.of_nat 255) by (evr; first [lia | kx_lia]);
      replace (ev E j) with (Z_to_bv 64 (bv_unsigned (ev E j)))
        by (first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]);
      lazymatch goal with |- Z.le ?lo ?W /\ Z.le _ ?hi =>
        let f := eval pattern (bv_unsigned (ev E j)) in W in
        lazymatch f with ?g _ =>
          pose proof (kx_enum_ok E (EVar j) j 1 255%nat (fun r0 => andb (Z.leb lo (g r0)) (Z.leb (g r0) hi))
                        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HR) as HB;
          cbn [edenot] in HB; cbv beta in HB; apply andb_prop in HB; destruct HB as [HBa HBb];
          apply Z.leb_le in HBa, HBb; lia
        end
      end
    end.
  Ltac fix_r2627 E26 E27 := lazymatch goal with
    | |- evtF ?s ?R ?Q (MS (mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21
                             ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31) ?fr ?pc ?fc ?rv ?m ?rom) =>
        replace (evtF s R Q (MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21
                                  y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) fr pc fc rv m rom))
          with (evtF s R Q (MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21
                                  y22 y23 y24 y25 (Z_to_bv 64 E26) (Z_to_bv 64 E27) y28 y29 y30 y31) fr pc fc rv m rom))
          by (f_equal; f_equal; f_equal;
              first [ apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned
                    | f_equal; lia | f_equal; kx_strip_mod; lia ])
    end.
  Ltac i1_fin I2 O1 H :=
    lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r27 _ _ _ _) _ _ _ _ _ _) =>
        let HW := fresh "HW" in
        assert (HW : 0 <= bv_unsigned r27 <= H) by hb_brute;
        fix_r2627 (SRC + 6 + O1) (bv_unsigned r27);
        try match goal with HQ : ?p = ((_ + 3) / 4)%Z |- _ => subst p end;
        eapply (I2 _ _ _ _ _ _ _ _ O1 (bv_unsigned r27)); lside; try (intros; lia); try kx_lia
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma x41_i1 : x41_i2_stmt -> x41_i1_stmt.
  Proof using CTX ACTX DHI NBOK rc.
    pose proof CTX as CTX'. x41a_ctx_open CTX'. pose proof ACTX as ACTX'. x41a_actx_open ACTX'.
    intros I2. unfold AZ_huf_dx41.x41_i2_stmt in I2. unfold AZ_huf_dx41.x41_i1_stmt.
    intros mm rest jb pc dl l1 l2 l3 LL w0 w8 w16 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128
      w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 x5 x7 x17 x22 x24 x25 x26 x27
      SV JK MU0 WM0 MI OUT DTB SRCB STK SA SH SBK BJ HD6 HN HL1 HL2 HL3 HLL HLN HSG HDL HPC.
    subst dl LL. facts R1 R2 R3 TL RSV LO SPB KLO.
    afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO.
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    pose proof (rng_shspanZ _ _ _ RSRCS) as RSz.
    pose proof (unpoisoned_unpZ _ _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2; lia)) as USz.
    zsfacts.
    remember ((dcap + 3) / 4) as pe eqn:HPE.
    assert (RJ : 2 <= pe <= 4294967296 /\ 4096 <= DST + pe <= 140737488355328 /\ 4096 <= DST + 2 * pe <= 140737488355328 /\
                 4096 <= DST + 3 * pe <= 140737488355328) by (subst pe; clear - HD6 HSG R1; Z.div_mod_to_equations; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4).
    destruct HPC as [(-> & HB) | (-> & HS)].
    (* [comment removed for export] *)
    2: (assert (HL : l1 = 1 \/ l1 = 2 \/ l1 = 3 \/ l1 = 4 \/ l1 = 5 \/ l1 = 6 \/ l1 = 7) by lia;
        destruct HL as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]).
    2-8: lazymatch goal with HL1 : 1 <= ?k < _ |- _ =>
          kx_autoFLA (SA, SH, SBK) [KAUnp (SRC + 6) k; KAApp (SPV - 496) 240] [0xa64b8; 0xa7af8] 160%nat
             [KZRange l2 0 65535; KZRange l3 0 65535; KZRange n 10 4294967296; KZRange SRC 4096 140737488355328;
              KZRange pe 2 4294967296; KZRange DST 4096 140737488355328; KZRange dcap 6 4294967296; KZRange DT 4096 140737488338940;
              KZRange tl 1 12; KZRange rsv 0 255; KZRange SPV 17594333498016 140737488355328;
              KZWr (SPV - 496) 136; KZWr (SPV - 352) 96; KZDisj (SPV - 496) 496 (SRC + 6) k; KZImg 0x22400 (0x22400 + 24)]
             [(SRC + 6, k); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96)] [(SRC + 6, k); (SPV - 496, 496)] end.
    (* [comment removed for export] *)
    1: kx_autoFLA (SA, SH, SBK) [KAUnp (SRC + 6 + l1 + -8) 8; KAApp (SPV - 496) 240] [0xa64b8; 0xa7af8] 90%nat
        [KZRange l1 8 65535; KZRange l2 0 65535; KZRange l3 0 65535; KZRange n 10 4294967296; KZRange SRC 4096 140737488355328;
         KZRange pe 2 4294967296; KZRange DST 4096 140737488355328; KZRange dcap 6 4294967296; KZRange DT 4096 140737488338940;
         KZRange tl 1 12; KZRange rsv 0 255; KZRange SPV 17594333498016 140737488355328;
         KZWr (SPV - 496) 136; KZWr (SPV - 352) 96; KZDisj (SPV - 496) 496 (SRC + 6 + l1 + -8) 8]
        [(SRC + 6 + l1 + -8, 8); (SPV + -496, 136); (SPV + -360, 8); (SPV + -352, 96)] [(SRC + 6 + l1 + -8, 8); (SPV - 496, 496)].
    (* [comment removed for export] *)
    all: aside.
    all: lazymatch goal with
         | |- accP _ _ _ => first [kx_acc RSRC | kx_acc RFR]
         | |- sc_resid _ _ _ _ => first [kx_rd SRCB | kx_rd SH | kx_rd SA | kx_rd SBK | kx_wr SA | kx_wr SBK]
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    all: try (lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa64b8) _ _ _ _) =>
             kx_gen_regsF [5%nat; 6%nat; 7%nat; 11%nat; 12%nat; 16%nat; 17%nat; 22%nat; 24%nat; 25%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) =>
             kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat;
                           19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
         end).
    all: try (intros; kx_mem).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ _ _) => err_ret
         | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (SRC + 6 + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _) _
                             (Z_to_bv 64 0xa64b8) _ _ _ _) =>
             tryif is_var k then i1_fin I2 constr:(k + -8) constr:(8) else i1_fin I2 constr:(0) constr:(64)
         end.
    (* [comment removed for export] *)
  Qed.
End DX41AM.
End CANSEC1.
