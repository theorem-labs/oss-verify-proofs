(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_reloadi AZ_huf_dx1e AZ_huf_dx41 AZ_huf_dx41_4a AZ_huf_dx41_e.
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
Lemma cb48_as_c8s : forall m A bs, rw_cells bsegs m A [CB 48 bs] ->
  exists w0 w1 w2 w3 w4 w5 : word, rw_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5].
Proof. intros m A bs H. pose proof (cb_as_c8s m A 6 bs H) as H2. cbn [c8s_of] in H2. do 6 eexists. exact H2. Qed.
Section DX41N0.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC DT lo : Z) (dtb : list byte).
  Hypotheses (LO0 : 4096 <= lo) (LO : lo <= SPV - 2720) (SPB : SPV < 2^47) (KLO : 0x10007fff8000 <= lo) (SPA : SPV mod 16 = 0)
             (D0 : 4096 <= DST) (D1 : 0 <= dcap < 2^32) (D2 : DST + dcap < 2^47) (OS1 : DST + dcap <= lo \/ SPV <= DST)
             (T0 : 4096 <= DT) (T1 : DT + 16388 < 2^47) (OS3 : DT + 16388 <= lo \/ SPV <= DT) (DJ2 : DST + dcap <= DT \/ DT + 16388 <= DST)
             (DTA : DT mod 4 = 0) (DL : zlen dtb = 16388)
             (SR0 : 4096 <= SRC) (SR1 : SRC < 2^47)
             (DSTA : dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST))
             (RSTK : rng RNG lo (SPV - lo)) (RI : rng_aimg RNG) (RDT : rng RNG DT 16388) (RDTS : rng RNG (shad DT) (shspan DT 16388)).

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2720 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -496)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation SVS mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2720, SPV)].

  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  Ltac restk :=
    lazymatch goal with
    | FR' : rw_cells bsegs ?mq (SPV + -496) _, SH' : rw_cells bsegs ?mq (SPV + -360) _, SB' : rw_cells bsegs ?mq (SPV + -352) _,
      AR' : rw_cells bsegs ?mq (SPV + -256) _, ST' : stk bsegs ?mq lo (SPV + -496) |- _ =>
        pose proof (stk_of_rw_cells bsegs mq _ _ FR') as H1; pose proof (stk_of_rw_cells bsegs mq _ _ SH') as H2;
        pose proof (stk_of_rw_cells bsegs mq _ _ SB') as H4; pose proof (stk_of_rw_cells bsegs mq _ _ AR') as H5;
        cbn [cells_size csize Nat.add] in H1, H2, H4, H5;
        change (Z.of_nat 136) with 136 in H1; change (Z.of_nat 8) with 8 in H2; change (Z.of_nat 96) with 96 in H4;
        change (Z.of_nat 152) with 152 in H5;
        replace (SPV + -496 + 136) with (SPV + -360) in H1 by lia; replace (SPV + -360 + 8) with (SPV + -352) in H2 by lia;
        replace (SPV + -352 + 96) with (SPV + -256) in H4 by lia; replace (SPV + -256 + 152) with (SPV + -104) in H5 by lia;
        assert (STKF : stk bsegs mq lo (SPV + -104))
          by (eapply (stk_merge bsegs mq lo (SPV + -256)); [| exact H5 | lia];
              eapply (stk_merge bsegs mq lo (SPV + -352)); [| exact H4 | lia];
              eapply (stk_merge bsegs mq lo (SPV + -360)); [| exact H2 | lia];
              eapply (stk_merge bsegs mq lo (SPV + -496)); [exact ST' | exact H1 | lia]);
        clear H1 H2 H4 H5 FR' SH' SB' AR' ST'
    end.

  (* [comment removed for export] *)
  Lemma x41_ret0 : forall mm r (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    stk bsegs mm DST (DST + dcap) -> SVS mm -> stk bsegs mm lo (SPV + -104) ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evtF bsegs RNG POST (ST 0xa7af8 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros mm r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 OUT FR STK MU WM MI HR.
    assert (RSTKf : rng RNG (SPV - 104) 104) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    kx_autoFLA FR [KAApp (SPV - 104) 104] (@nil Z) 30%nat [KZRange SPV 0x10007fff8000 (2^47)] [(SPV - 104, 104)] [(SPV - 104, 104)].
    all: aside.
    all: kx_mem.
    all: zstep.
    all: release_frame FR STK SPV.
    all: apply evtF_done; unfold huf_dec_postA; repeat (lazymatch goal with |- ex _ => eexists end).
    all: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact STK|]);
         (split; [exact OUT|]); (split; [|split; [|exact I]]).
    - destruct HR as [HR|[HR _]]; [left; exact HR | right; exact HR].
    - destruct HR as [->|[HR1 HR2]]; [clear - D1; lia|]. unfold zd_is_error, ZE_maxCode in HR1. apply Z.ltb_lt in HR1. clear - HR1 HR2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_fa0 : forall mm bs jb hsh (d2 : Z) (x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (w0 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word),
    d2 = dcap ->
    stk bsegs mm DST (DST + dcap) -> SVS mm -> stk bsegs mm lo (SPV + -496) ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> bytes_at bsegs mm DT dtb ->
    X41SA SPV mm w0 (Z_to_bv 64 (0)) w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 ->
    rw_cells bsegs mm (SPV + -360) [C8 hsh] -> rw_cells bsegs mm (SPV + -352) [CB 96 jb] ->
    rw_cells bsegs mm (SPV + -256) [CB 152 bs] ->
    rt_got mm -> rt_shbase mm -> unpoisoned mm DT (DT + 16388) ->
    evtF bsegs RNG POST (ST 0xaa0d8 mm (Z_to_bv 64 (0xa4d4c)) x5 x6 x7 x8 x9 (Z_to_bv 64 (SPV + -256)) (Z_to_bv 64 (DST)) (Z_to_bv 64 (d2)) (Z_to_bv 64 (SRC)) (Z_to_bv 64 (0)) (Z_to_bv 64 (DT)) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros mm bs jb hsh d2 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w0 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      HD2 OUT SV STK MU WM MI DTB SAW SHW SBJ AR GOT SHB UDT. subst d2.
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz.
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDT ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - T1; lia)) as UDTz.
    assert (RFR : rng RNG (SPV - 544) 544) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : (4100 <= DT + 4 <= 140737488338944) /\ (0 <= DT < 2 ^ 64) /\ (4096 <= DST + dcap <= 140737488355328) /\
                 (SPV - 544 + 544 <= DT \/ DT + 16388 <= SPV - 544)) by (clear - T0 T1 D0 D1 D2 OS3 LO; lia).
    destruct KF as (KF1 & KF2 & KF3 & KF4).
    (* [comment removed for export] *)
    carve_frame 48%nat STK.
    destruct (cb48_as_c8s mm _ junk FR) as (u0 & u1 & u2 & u3 & u4 & u5 & FAW). clear FR.
    kx_autoFLA (GOT, SHB, FAW, SAW, SHW) [KAUnp DT 16388; KAApp (SPV - 544) 544] [0xa7af8] 90%nat
        [KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + dcap) 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZAlign DT 4; KZRange (DT + 4) 4100 140737488338944; KZRange SRC 4096 140737488355328;
         KZRange SPV 17594333498016 140737488355328; KZWr (SPV + -544) 48; KZWr (SPV + -496) 136; KZDisj (SPV - 544) 544 DT 16388;
         KZDisj DST dcap (SPV - 544) 544]
        [(SPV + -544, 48); (SPV + -496, 136); (SPV + -360, 8); (DT, 16388)] [(DT, 16388); (SPV - 544, 544)].
    all: aside.
    all: try clear RDTz UDTz KF1 KF2 KF3 KF4.
    all: kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]; intros.
    all: kx_mem.
    (* [comment removed for export] *)
    all: lazymatch goal with FA' : rw_cells bsegs ?mq (SPV + -544) _, ST' : stk bsegs ?mq lo (SPV + -544) |- _ =>
           release_frame FA' ST' (SPV + -496) end.
    all: restk.
    all: try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv64_eqm_k; reflexivity)).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ ?m1 _) =>
           eapply (x41_ret0 m1 18446744073709551596); [ eassumption | eassumption | exact STKF | eassumption | eassumption | eassumption
                                                     | right; split; [vm_compute; reflexivity | lia] ] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x41_n0 : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 DT dtb ->
    rt_got m0 -> rt_shbase m0 -> unpoisoned m0 DT (DT + 16388) ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 0)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa4cbc) fc None m0 (seg_rom bsegs)).
  Proof.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK OUT DTB GOT SHB UDT.
    assert (MU0 : munch W0 m0 m0) by apply munch_refl. assert (WM0 : wmono bsegs m0 m0) by apply wmono_refl.
    assert (RFR : rng RNG (SPV - 496) 496) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : (4100 <= DT + 4 <= 140737488338944) /\ (4096 <= DST + dcap <= 140737488355328) /\
                 (SPV - 496 + 496 <= DT \/ DT + 16388 <= SPV - 496)) by (clear - T0 T1 D0 D1 D2 OS3 LO; lia).
    destruct KF as (KF1 & KF2 & KF3).
    carve_frame 496%nat STK.
    destruct (frame480_split m0 _ junk FR) as (j1 & j2 & j3 & j4 & j6 & C1 & C2 & SBJ & ARGS & C6). clear FR.
    replace (SPV + -496 + 136) with (SPV + -360) in C2 by lia. replace (SPV + -496 + 144) with (SPV + -352) in SBJ by lia.
    replace (SPV + -496 + 240) with (SPV + -256) in ARGS by lia. replace (SPV + -496 + 392) with (SPV + -104) in C6 by lia.
    assert (SAX : exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word,
               X41SA SPV m0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16)
      by (pose proof (cb_as_c8s m0 _ 17 j1 C1) as H2; cbn [c8s_of] in H2; do 17 eexists; exact H2).
    destruct SAX as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & SAW).
    assert (SHX : exists hsh : word, rw_cells bsegs m0 (SPV + -360) [C8 hsh])
      by (pose proof (cb_as_c8s m0 _ 1 j2 C2) as H2; cbn [c8s_of] in H2; eexists; exact H2).
    destruct SHX as (hsh & SHW).
    destruct (cb104_as_c8s m0 _ j6 C6) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & SVW).
    clear C1 C2 C6.
    kx_autoFLA (GOT, SHB, SAW, SHW, SVW) [KAApp (SPV - 496) 496] [0xa7af8; 0xaa0d8] 90%nat
        [KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + dcap) 4096 140737488355328;
         KZRange DT 4096 140737488338940; KZRange (DT + 4) 4100 140737488338944;
         KZRange SRC 4096 140737488355328; KZRange SPV 17594333498016 140737488355328;
         KZWr (SPV + -496) 136; KZWr (SPV + -360) 8; KZWr (SPV + -104) 104; KZDisj (SPV - 496) 496 DT 16388;
         KZDisj DST dcap (SPV - 496) 496]
        [(SPV + -496, 136); (SPV + -360, 8); (SPV + -104, 104)] [(SPV - 496, 496)].
    all: aside.
    all: try clear KF1 KF2 KF3.
    all: kx_mem.
    all: try replace (DST + 0) with DST in * by (clear; lia).
    all: try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv64_eqm_k; reflexivity)).
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7af8) _ _ ?m1 _) =>
             restk;
             eapply (x41_ret0 m1 18446744073709551596); [ eassumption | eassumption | exact STKF | eassumption | eassumption | eassumption
                                                       | right; split; [vm_compute; reflexivity | lia] ]
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    all: lazymatch goal with MU1 : munch W0 m0 ?m1 |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xaa0d8) _ _ ?m1 _) =>
      assert (AW0 : aappW [(SPV - 2720, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
      assert (UDTc : unpoisoned m1 DT (DT + 16388))
        by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
            [ eapply unp_carryW; [exact UDT | exact MU1 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - T0; lia | clear - T0; lia | clear - T1; lia]
            | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU1 by (clear - Hd D1; lia); exact MU1
                                 | exact AW0 | clear - T0; lia | clear - T0; lia | clear - T1; lia] ]);
      clear UDT;
      kx_gen_regsF [5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat;
                    25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]; intros;
      eapply (x41_fa0 m1 j4 j3); first [exact UDTc | eassumption | clear - KXBR D1; lia | lia]
    end.
  Qed.
End DX41N0.
End CANSEC1.
