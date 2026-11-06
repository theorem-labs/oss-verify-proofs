(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2 ZdWalkKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_reloadi AZ_huf_dx42  AZ_hufkit42e2 AZ_huf_dx1e AZ_huf_bitinit AZ_huf_dx42_mh AZ_huf_dx42_m0 AZ_huf_dx42_c0 AZ_huf_dx42_i4 AZ_huf_dx42_i3 AZ_huf_dx42_i2 AZ_huf_dx42_i1 AZ_huf_dx42_s0.
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
Section DX42BZ.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis PRE0 : huf_dec_preA RNG m0 SPV lo 2608 DST dcap SRC n src.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2608 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 2608, SPV)].
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  Ltac traps := try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 706616) _ _ _ _) => kx_trap_fast end).
  Ltac pre_rng PRE0 :=
    let P := fresh "PREx" in pose proof PRE0 as P;
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ASTK0 & _ & _ & _);
    destruct ASTK0 as (KLO0 & RSTK & RI).
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.

  (* [comment removed for export] *)
  Lemma x42b_ret0 : forall mm r (x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    stk bsegs mm DST (DST + dcap) -> FRQ mm -> stk bsegs mm lo (SPV + -104) ->
    munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm ->
    (r = dcap \/ (zd_is_error r = true /\ r < 2^64)) ->
    evtF bsegs RNG POST (ST 0xa7444 mm x1 (Z_to_bv 64 r) x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                            x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using CTX PRE0 rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pre_rng PRE0.
    intros mm r x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 OUT FR STK MU WM MI HR.
    assert (GF7 : 17594333497904 <= SPV <= 140737488355328) by (clear - LO SPB KLO; lia).
    assert (RSTKf : rng RNG (SPV - 104) 104) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    clear SPA DTA DT2 DT3 DSTA DHI.
    kx_autoFLA FR [KAApp (SPV - 104) 104] (@nil Z) 30%nat [KZRange SPV 0x10007fff8000 (2^47)] [(SPV - 104, 104)] [(SPV - 104, 104)].
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
  Lemma x42b_n0 : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    n = 0 ->
    mem_inv bsegs m0 -> stk bsegs m0 lo SPV -> stk bsegs m0 DST (DST + dcap) -> bytes_at bsegs m0 DT dtb ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa5d3c) fc None m0 (seg_rom bsegs)).
  Proof using CTX PRE0 rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pre_rng PRE0.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 N0 MI STK OUT DTB.
    assert (GF7 : 17594333497904 <= SPV <= 140737488355328) by (clear - LO SPB KLO; lia).
    assert (MU0 : munch W0 m0 m0) by apply munch_refl. assert (WM0 : wmono bsegs m0 m0) by apply wmono_refl.
    assert (RFR : rng RNG (SPV - 384) 384) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (SFD : (SPV - 384 + 384 <= DT \/ DT + 16388 <= SPV - 384) /\ (DST + dcap <= SPV - 384 \/ SPV - 384 + 384 <= DST) /\
                  (4096 <= DST + dcap <= 140737488355328) /\ (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940))
      by (clear - OS1 OS3 LO R1 R3; lia).
    destruct SFD as (SFD1 & SFD2 & SFD3 & SFD4 & SFD5 & SFD6).
    carve_frame 384%nat STK.
    lazymatch goal with H : rw_cells bsegs m0 (SPV + -384) [CB 384 ?jj] |- _ =>
      apply (rw_cells_split_CB bsegs m0 _ [] 384 jj _ [120; 40; 40; 40; 40; 104]%nat) in H; [| reflexivity]; cbn [mk_CB_cells app] in H;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 120 _] _)) in H; destruct H as [FRb H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -264) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ4 H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -224) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ3 H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -184) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ2 H];
      lazymatch type of H with rw_cells _ _ ?x _ => replace x with (SPV + -144) in H by (cbn; lia) end;
      apply (proj1 (rw_cells_app bsegs _ _ [CB 40 _] _)) in H; destruct H as [BJ1 SVb];
      lazymatch type of SVb with rw_cells _ _ ?x _ => replace x with (SPV + -104) in SVb by (cbn; lia) end end.
    pose proof (e42_cb_as_c8s m0 _ 15 _ FRb) as FRW. cbn [e42_c8s_of] in FRW. clear FRb.
    pose proof (e42_cb_as_c8s m0 _ 13 _ SVb) as SVW. cbn [e42_c8s_of] in SVW. clear SVb.
    clear SPA DTA DT2 DT3 DSTA DHI.
    kx_autoFLA (FRW, SVW) [KAApp (SPV - 384) 384] [0xa7444; 0xa5f98; 0xac838] 40%nat
      [KZRange SPV 17594333497904 140737488355328; KZRange DST 4096 140737488355328; KZRange (DST + dcap) 4096 140737488355328;
       KZRange dcap 0 4294967296; KZRange n 0 0; KZRange DT 4096 140737488338940;
       KZWr (SPV + -384) 120; KZWr (SPV + -104) 104;
       KZDisj (SPV - 384) 384 DT 16388; KZDisj DST dcap (SPV - 384) 384]
      [(SPV + -384, 120); (SPV + -104, 104)] [(SPV - 384, 384)].
    all: aside.
    all: traps.
    all: kx_mem.
    all: try (replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv64_eqm_k; reflexivity)).
    all: lazymatch goal with SV' : rw_cells bsegs ?m1 (SPV + -104) _, ST' : stk bsegs ?m1 lo (SPV + -384),
           F' : rw_cells bsegs ?m1 (SPV + -384) _, B4 : rw_cells bsegs ?m1 (SPV + -264) _, B3 : rw_cells bsegs ?m1 (SPV + -224) _,
           B2 : rw_cells bsegs ?m1 (SPV + -184) _, B1 : rw_cells bsegs ?m1 (SPV + -144) _ |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa7444) _ _ ?m1 _) =>
      pose proof (stk_of_rw_cells bsegs m1 _ _ F') as K0; pose proof (stk_of_rw_cells bsegs m1 _ _ B4) as K4; pose proof (stk_of_rw_cells bsegs m1 _ _ B3) as K3;
      pose proof (stk_of_rw_cells bsegs m1 _ _ B2) as K2; pose proof (stk_of_rw_cells bsegs m1 _ _ B1) as K1;
      cbn [cells_size csize Nat.add length] in K0, K4, K3, K2, K1;
      change (Z.of_nat 120) with 120 in K0; change (Z.of_nat 40) with 40 in K4, K3, K2, K1;
      replace (SPV + -384 + 120) with (SPV + -264) in K0 by (clear; lia); replace (SPV + -264 + 40) with (SPV + -224) in K4 by (clear; lia);
      replace (SPV + -224 + 40) with (SPV + -184) in K3 by (clear; lia); replace (SPV + -184 + 40) with (SPV + -144) in K2 by (clear; lia);
      replace (SPV + -144 + 40) with (SPV + -104) in K1 by (clear; lia);
      eapply (x42b_ret0 m1 18446744073709551596);
      [ eassumption | exact SV'
      | eapply (stk_merge bsegs m1 lo (SPV + -144)); [| exact K1 | clear - LO; lia];
        eapply (stk_merge bsegs m1 lo (SPV + -184)); [| exact K2 | clear - LO; lia];
        eapply (stk_merge bsegs m1 lo (SPV + -224)); [| exact K3 | clear - LO; lia];
        eapply (stk_merge bsegs m1 lo (SPV + -264)); [| exact K4 | clear - LO; lia];
        eapply (stk_merge bsegs m1 lo (SPV + -384)); [exact ST' | exact K0 | clear - LO; lia]
      | eassumption | eassumption | eassumption
      | right; split; [vm_compute; reflexivity | clear; lia] ] end.
  Qed.
End DX42BZ.

(* [comment removed for export] *)
Theorem x42b_proofB : bit_init_stmtA -> huf_reload_int_stmtA -> huf_int_stmtA_at 0xa5d3c 2608 true.
Proof.
  intros BITINIT HRL. unfold huf_int_stmtA_at.
  intros RNG ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT tl lo src dtb PRE DTP DT2 TL X2 NB.
  pose proof PRE as PRE'.
  destruct PRE' as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & ARD & ARS & ART & AST & AZS & ARC & SPA).
  pose proof DTP as DTP'. destruct DTP' as (DTB & DL & T0 & T1 & OS3 & DJ2 & ARODT & DTA). unfold HUF_DTABLE_BYTES in *.
  destruct AST as (KLO & RSTK & RI). destruct ARODT as (UDT & RDT & RDTS).
  assert (DSTA : dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)).
  { destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd]; [| left; lia]. right.
    destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  assert (DHI : 0 < dcap -> 0x629000 <= DST).
  { intros Hd. destruct (ARD Hd) as (ABD & _). unfold ablk, AIMG_HI, KLS, KHIGH in ABD |- *. lia. }
  destruct (nth_error dtb 3) as [b3|] eqn:DT3; [| apply nth_error_None in DT3; exfalso; lia].
  assert (CTX : x42b_ctx SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb).
  { pose proof (bv_unsigned_in_range 8 b3) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
    assert (EB : Z_to_bv 8 (bv_unsigned b3) = b3)
      by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    unfold x42b_ctx. rewrite EB. unfold KHIGH in KLO. repeat split; try assumption; lia. }
  destruct (Z.eq_dec n 0) as [N0|N1].
  { exact (x42b_n0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb CTX PRE
             t0 t1 t2 flags a6 a7 t3 t4 t5 t6 N0 MI STK OUT DTB). }
  destruct (ARS ltac:(lia)) as (ABS & USRC & RSRC & RSRCS).
  assert (ACTX : x42b_actx RNG m SPV DST dcap SRC n DT lo).
  { unfold x42b_actx. unfold KHIGH in KLO |- *.
    split; [exact USRC|]. split; [exact UDT|].
    split; [intros Hd; destruct (ARD Hd) as (_ & U & _); exact U|].
    split; [exact RSRC|]. split; [exact RSRCS|]. split; [exact RDT|]. split; [exact RDTS|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & R & _); exact R|].
    split; [intros Hd; destruct (ARD Hd) as (_ & _ & _ & R); exact R|].
    split; [exact RSTK|]. split; [exact RI|]. split; [exact AZS|]. split; [exact ARC | exact ART]. }
  exact (AZ_huf_dx42_s0.x42_pro RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV DST dcap SRC n DT tl (bv_unsigned b3) lo src dtb
           CTX (X2 eq_refl) ACTX HRL NB BITINIT t0 t1 t2 flags a6 a7 t3 t4 t5 t6 ltac:(lia) MI STK OUT SRCB DTB).
Qed.

(* [comment removed for export] *)
Theorem x42b_proof : huf_int_stmtA_at 0xa5d3c 2608 true.
Proof. exact (x42b_proofB bit_init_proofA huf_reload_int_proofA). Qed.
End CANSEC1.
