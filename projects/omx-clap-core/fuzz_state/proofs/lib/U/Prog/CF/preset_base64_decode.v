(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 1101 of its 1204 lines of code are new or changed and 636 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/put_string.v, with its module paths and module names changed; 1314 of its 1437 lines of code are new or changed and 1081 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YI04 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import fuzz_malloc_c fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import preset_base64_decode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c memchr_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import preset_base64_decode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling (only parsing).

Definition dec_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (text lenp : Z) (tb : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 m',
    ms' = MS (mkR (Z_to_bv 64 0x15468) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) s1
                  (Z_to_bv 64 (b64_M tb)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 text) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x14064) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp - 112) (CB 8 j0 :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma dec_M_bits : forall L, 0 <= L <= 2 ^ 28 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 L)) 2))) 1 +
              Z.shiftr (bv_unsigned (Z_to_bv 64 L)) 2 + 3) = Z_to_bv 64 (L / 4 * 3 + 3).
Proof.
  intros L HL. rewrite (unsigned_lit L) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  rewrite (unsigned_lit (L / 4)) by (Z.div_mod_to_equations; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. f_equal. lia.
Qed.

Lemma dec_run1 : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (text lenp : Z) (tb : list Z) (slack : list byte),
  bytes_at rsegs m text (map (Z_to_bv 8) tb ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) tb) ->
  (- (text + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
  Z.of_nat (length tb) <= 2 ^ 28 ->
  stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp) -> 112 <= bv_unsigned sp ->
  text + Z.of_nat (length (map (Z_to_bv 8) tb ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= text ->
  0 <= lenp < 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (dec_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc text lenp tb m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 text) (Z_to_bv 64 lenp) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15410) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m text lenp tb slack BS NONUL PAD HL ST SP112 DISJ HLP MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB, DISJ. cbn [length] in SB, DISJ.
  rewrite length_map in SB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UT : bv_unsigned (Z_to_bv 64 text) = text) by (apply unsigned_lit; lia).
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 112%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 17 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (map (Z_to_bv 8) tb) slack).
  1-4: rewrite ?UT, ?length_map; first [eassumption | lia].
  cbv delta [mkR].
  do 5 step.
  rewrite (dec_M_bits (Z.of_nat (length (map (Z_to_bv 8) tb)))) by (rewrite length_map; lia).
  rewrite length_map. change (Z.of_nat (length tb) / 4 * 3 + 3) with (b64_M tb).
  apply evt_done. unfold dec_mid.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma stk_empty : forall m a, 0 <= a <= 2 ^ 64 -> stk rsegs m a a.
Proof. intros m a Ha. split; [lia|]. split; [lia|]. intros x Hx. lia. Qed.

Definition dec_free_pre (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lenp q : Z) (tb : list Z) (lb : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x1554c) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 x8 (Z_to_bv 64 q)
                  (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14378) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' lenp lb /\
    rw_cells rsegs m' (bv_unsigned sp - 112) (C8 (Z_to_bv 64 lenp) :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
    munch [(q, q + b64_M tb); (bv_unsigned sp - 112, bv_unsigned sp - 104)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m'.

Lemma dec_go_fail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lenp q tx : Z) (tb : list Z) (lb j0 : list byte),
  memchr_contract -> b64_dec tb = None ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2^31 - 1 ->
  tx <> 0 -> q <> 0 -> lenp <> 0 -> lenp mod 8 = 0 ->
  bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) ->
  bytes_at rsegs m lenp lb -> length lb = 8%nat -> wr_at rsegs m lenp 8 ->
  wr_at rsegs m q (b64_M tb) ->
  rw_cells rsegs m (bv_unsigned sp - 112) (CB 8 j0 :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  112 <= bv_unsigned sp ->
  mem_inv rsegs m ->
  q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q ->
  q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q ->
  q + b64_M tb <= lenp \/ lenp + 8 <= q ->
  q + b64_M tb <= bv_unsigned sp - 112 \/ bv_unsigned sp <= q ->
  lenp + 8 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= lenp ->
  tx + Z.of_nat (length tb) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= tx ->
  evt rsegs (dec_free_pre ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lenp q tb lb m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) x9 (Z_to_bv 64 q)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15468) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7
    x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m lenp q tx tb lb j0 MC HB. intros.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply dec_loop_fail with (lo := bv_unsigned sp - 112); try eassumption; [apply stk_empty; lia | lia]|].
  intros ms' (y1 & u0 & u1 & u2 & y8 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y18 & y19 & y20 & y21 & y22 & y23
    & y24 & y25 & y26 & y27 & u3 & u4 & u5 & u6 & m' & -> & L1 & FR1 & MU1 & WM1 & MI1 & _).
  step.
  apply evt_done. unfold dec_free_pre.
  do 26 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma dec_after_free : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (v : word),
  rw_cells rsegs m (bv_unsigned sp - 112) (C8 v :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> 112 <= bv_unsigned sp ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x1554c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m v FR SP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  step.
  eapply evt_mono; [eapply dec_epi with (c0 := C8 v) (lo := bv_unsigned sp - 112);
    [reflexivity | lia | apply stk_empty; lia | exact FR] | intros ms' [H _]; exact H].
Qed.

Lemma dec_null_ret : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp - 112) (CB 8 j0 :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> 112 <= bv_unsigned sp ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x15468) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7
    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m j0 FR SP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_mono; [eapply dec_null with (lo := bv_unsigned sp - 112); [exact FR | apply stk_empty; lia | lia]
    | intros ms' [H _]; exact H].
Qed.

Lemma fs_some : forall segs a n s, find_segment segs a n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= a /\ a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 segs IH]; intros a n s H; cbn in H; [discriminate|].
  destruct (Z.of_N (seg_base s0) <=? a) eqn:E1; destruct (a + n <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) eqn:E2;
    cbn in H;
    try (destruct (IH _ _ _ H) as (I1 & I2 & I3); split; [right; exact I1 | split; assumption]).
  inversion H; subst. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | split; assumption].
Qed.

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 32) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_seg_top : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 2 ^ 32.
Proof. intros s H. pose proof rsegs_top as T. rewrite forallb_forall in T. apply Z.leb_le. exact (T s H). Qed.

Lemma fs_low : forall a n s, find_segment rsegs a n = Some s -> a + n <= 2 ^ 32.
Proof. intros a n s H. destruct (fs_some _ _ _ _ H) as (Hin & H1 & H2). pose proof (rsegs_seg_top s Hin). lia. Qed.

Lemma fs_hi : forall a, 2 ^ 32 <= a -> find_segment rsegs a 1 = None.
Proof. intros a Ha. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity]. apply fs_low in E. lia. Qed.

Lemma mrd_nofs : forall m x, find_segment rsegs (bv_unsigned x) 1 = None -> mrd rsegs m x = m x.
Proof.
  intros m x H. unfold mrd. destruct (m x); [reflexivity|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity.
Qed.

Lemma wview_nofs : forall m x, find_segment rsegs (bv_unsigned x) 1 = None -> wview rsegs m x = m x.
Proof. intros m x H. unfold wview. destruct (m x); [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma ro_addr_nofs : forall x, find_segment rsegs (bv_unsigned x) 1 = None -> ro_addr rsegs x = false.
Proof. intros x H. unfold ro_addr. rewrite H. reflexivity. Qed.

Lemma ro_addr_low : forall x, ro_addr rsegs x = true -> bv_unsigned x < 2 ^ 32.
Proof.
  intros x H. unfold ro_addr in H. destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|discriminate].
  apply fs_low in E. lia.
Qed.

Lemma mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof. reflexivity. Qed.

Lemma bytes_at_of_mbyte : forall m a xs, 0 <= a -> a + Z.of_nat (length xs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length xs) -> mbyte rsegs m (a + i) = nth_error xs (Z.to_nat i)) ->
  bytes_at rsegs m a xs.
Proof.
  intros m a xs H1 H2 H. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- mbyte_mrd. rewrite H by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma mbyte_of_bytes_at : forall m a xs i, bytes_at rsegs m a xs -> 0 <= i < Z.of_nat (length xs) ->
  mbyte rsegs m (a + i) = nth_error xs (Z.to_nat i).
Proof.
  intros m a xs i (H1 & H2 & H) Hi. rewrite mbyte_mrd.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. apply H. lia.
Qed.

Lemma bytes_at_keep : forall m m' a xs, bytes_at rsegs m a xs ->
  (forall i, 0 <= i < Z.of_nat (length xs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a xs.
Proof.
  intros m m' a xs Hb H. pose proof (bytes_at_bound _ _ _ _ Hb).
  apply bytes_at_of_mbyte; [lia | lia |]. intros i Hi. rewrite H by lia. apply mbyte_of_bytes_at; assumption.
Qed.

Lemma wr_at_keep : forall m m' a n, wr_at rsegs m a n ->
  (forall i, 0 <= i < n -> writable_at rsegs m (a + i) -> writable_at rsegs m' (a + i)) -> wr_at rsegs m' a n.
Proof. intros m m' a n (H1 & H2 & H) K. split; [lia|]. split; [lia|]. intros i Hi. apply (K i Hi). apply H. exact Hi. Qed.

Lemma rw_cells_keep : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte rsegs m' (A + i) = mbyte rsegs m (A + i) /\
     (writable_at rsegs m (A + i) -> writable_at rsegs m' (A + i))) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf Hb] Hw] K. split; [split; [exact Hwf|]|].
  - eapply bytes_at_keep; [exact Hb|]. intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. apply K. exact Hi.
  - eapply wr_at_keep; [exact Hw|]. intros i Hi. apply K. exact Hi.
Qed.

Lemma stk_of_writable : forall m lo hi, 2 ^ 32 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi H1 H2 H. split; [lia|]. split; [lia|]. intros a Ha. split; [apply H; exact Ha|].
  pose proof (H a Ha) as W. unfold writable_at in W.
  assert (F : find_segment rsegs (bv_unsigned (wa a)) 1 = None) by (rewrite wa_unsigned by lia; apply fs_hi; lia).
  change (Z_to_bv 64 a) with (wa a) in W. rewrite wview_nofs in W by exact F. rewrite mrd_nofs by exact F.
  destruct (m (wa a)) as [b|]; [exists b; reflexivity | congruence].
Qed.

Lemma getr_reg : forall regs (r : bv 5), bv_unsigned r <> 0 -> YK11.getr regs r = reg_get regs r.
Proof.
  intros regs r H. unfold YK11.getr. destruct (bv_eqb r 0) eqn:E; [|reflexivity].
  exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. apply H. rewrite E. reflexivity.
Qed.

Lemma bv5_nz : forall r, 0 < r < 32 -> bv_unsigned (Z_to_bv 5 r) <> 0.
Proof. intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn; lia). lia. Qed.

Lemma getr_eqv : forall X R r, xregs_eqv X R -> 0 < r < 32 -> YK11.getr R (Z_to_bv 5 r) = reg_get X (Z_to_bv 5 r).
Proof.
  intros X R r H Hr. rewrite getr_reg by (apply bv5_nz; exact Hr). symmetry. apply H.
  unfold is_x0. apply Z.eqb_neq. apply bv5_nz. exact Hr.
Qed.

Lemma reg_pres : forall R1 R2 X r v, regs_preserved R1 R2 -> callee_saved r -> xregs_eqv X R1 -> 0 < r < 32 ->
  reg_get X (Z_to_bv 5 r) = v -> reg_get R2 (Z_to_bv 5 r) = v.
Proof.
  intros R1 R2 X r v HP Hc HX Hr Hv. rewrite <- getr_reg by (apply bv5_nz; exact Hr).
  rewrite (HP r Hc). rewrite (getr_eqv X R1 r HX Hr). exact Hv.
Qed.

Lemma mkR_of_eq : forall R, mkR_of R =
  mkR (reg_get R (Z_to_bv 5 1)) (reg_get R (Z_to_bv 5 2)) (reg_get R (Z_to_bv 5 3)) (reg_get R (Z_to_bv 5 4))
      (reg_get R (Z_to_bv 5 5)) (reg_get R (Z_to_bv 5 6)) (reg_get R (Z_to_bv 5 7)) (reg_get R (Z_to_bv 5 8))
      (reg_get R (Z_to_bv 5 9)) (reg_get R (Z_to_bv 5 10)) (reg_get R (Z_to_bv 5 11)) (reg_get R (Z_to_bv 5 12))
      (reg_get R (Z_to_bv 5 13)) (reg_get R (Z_to_bv 5 14)) (reg_get R (Z_to_bv 5 15)) (reg_get R (Z_to_bv 5 16))
      (reg_get R (Z_to_bv 5 17)) (reg_get R (Z_to_bv 5 18)) (reg_get R (Z_to_bv 5 19)) (reg_get R (Z_to_bv 5 20))
      (reg_get R (Z_to_bv 5 21)) (reg_get R (Z_to_bv 5 22)) (reg_get R (Z_to_bv 5 23)) (reg_get R (Z_to_bv 5 24))
      (reg_get R (Z_to_bv 5 25)) (reg_get R (Z_to_bv 5 26)) (reg_get R (Z_to_bv 5 27)) (reg_get R (Z_to_bv 5 28))
      (reg_get R (Z_to_bv 5 29)) (reg_get R (Z_to_bv 5 30)) (reg_get R (Z_to_bv 5 31)).
Proof. intros R. reflexivity. Qed.

Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H.
  pose proof (bv_unsigned_in_range 64 k) as Hk. unfold bv_modulus in Hk.
  assert (H' : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned k + 0) (-2))) = bv_unsigned k) by exact (f_equal bv_unsigned H).
  assert (L2 : Z.land (bv_unsigned k + 0) (-2) = bv_unsigned k / 2 * 2).
  { rewrite Z.add_0_r. change (-2) with (Z.lnot (Z.ones 1)).
    rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite L2, Z_to_bv_unsigned in H'. unfold bv_wrap, bv_modulus in H'.
  assert (E : bv_unsigned k mod 2 = 0).
  { rewrite Z.mod_small in H' by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]|]; Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia. }
  transitivity (ret_pc (Z_to_bv 64 (bv_unsigned k))); [f_equal; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite ret_pc_even by (lia || exact E). apply Z_to_bv_bv_unsigned.
Qed.

Lemma eqv_getr : forall X R r v, xregs_eqv X R -> 0 < r < 32 -> reg_get X (Z_to_bv 5 r) = v -> YK11.getr R (Z_to_bv 5 r) = v.
Proof. intros X R r v H Hr E. rewrite (getr_eqv X R r H Hr). exact E. Qed.

Lemma rp_of_eqv : forall regs R (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  xregs_eqv (mkR x1 (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3)) (reg_get regs (Z_to_bv 5 4)) x5 x6 x7
     (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9)) x10 x11 x12 x13 x14 x15 x16 x17
     (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20))
     (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23))
     (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26))
     (reg_get regs (Z_to_bv 5 27)) x28 x29 x30 x31) R ->
  regs_preserved regs R.
Proof.
  intros regs R x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H r Hr.
  unfold callee_saved in Hr.
  assert (Hr' : 0 < r < 32) by lia.
  rewrite (getr_eqv _ _ r H Hr'), (getr_reg regs (Z_to_bv 5 r)) by (apply bv5_nz; exact Hr').
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; try reflexivity.
  assert (E : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.

Ltac qr RP X r := apply (reg_pres _ _ _ r _ RP ltac:(unfold callee_saved; lia) X ltac:(lia)); reflexivity.

Lemma outside1 : forall lo hi x, x < lo \/ hi <= x -> outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact I]. Qed.

Lemma outside2 : forall l1 h1 l2 h2 x, x < l1 \/ h1 <= x -> x < l2 \/ h2 <= x -> outside [(l1, h1); (l2, h2)] x.
Proof. intros l1 h1 l2 h2 x H1 H2. cbn. split; [lia | split; [lia | exact I]]. Qed.

Lemma ro_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x : word, ro_addr rsegs x = true -> outside W (bv_unsigned x)) -> ro_agree rsegs m'.
Proof.
  intros W m m' RO MU K. apply (ro_agree_same rsegs m m' RO). intros x Hx. exact (MU x (K x Hx)).
Qed.

Lemma ro_high : forall m m' lo hi, ro_agree rsegs m -> munch [(lo, hi)] m m' -> 2 ^ 32 <= lo -> ro_agree rsegs m'.
Proof.
  intros m m' lo hi RO MU Hlo. apply (ro_munch _ m m' RO MU). intros x Hx.
  pose proof (ro_addr_low x Hx). apply outside1. lia.
Qed.

Lemma ro_image : forall m a bs, ro_agree rsegs m -> (forall m0, mem_inv rsegs m0 -> bytes_at rsegs m0 a bs) ->
  bytes_at rsegs m a bs.
Proof.
  intros m a bs RO H. apply (proj2 (bytes_at_rel rsegs m (normalize rsegs m) a bs (mem_rel_normalize rsegs m RO))).
  apply H. apply mem_inv_normalize.
Qed.

Lemma mbyte_ro : forall m m' a, ro_agree rsegs m -> ro_agree rsegs m' -> ro_addr rsegs (Z_to_bv 64 a) = true ->
  mbyte rsegs m' a = mbyte rsegs m a.
Proof.
  intros m m' a H H' R. transitivity (seg_rom rsegs (Z_to_bv 64 a)); [exact (H' _ R) | symmetry; exact (H _ R)].
Qed.

Lemma got_owned : forall (B : malloc_syms) L A i, 0 <= i < 8 -> owned B L A (ms_got_guard B + i).
Proof. intros B L A i Hi. right. unfold static_owned. right; right; right; right; left. lia. Qed.

Lemma nth_error_map8 : forall (l : list Z) k, (k < length l)%nat ->
  nth_error (map (Z_to_bv 8) l) k = Some (Z_to_bv 8 (nth k l 0)).
Proof. intros l k Hk. rewrite nth_error_map, (nth_error_nth' l 0 Hk). reflexivity. Qed.

Lemma rsegs_bot : forallb (fun s => 0 <? Z.of_N (seg_base s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_pos : forall x, 0 <= x < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 x) = true -> 0 < x.
Proof.
  intros x Hx H. unfold ro_addr in H. rewrite unsigned_lit in H by lia.
  destruct (find_segment rsegs x 1) as [s|] eqn:F; [|discriminate].
  destruct (fs_some _ _ _ _ F) as (Hin & H1 & _). pose proof rsegs_bot as T. rewrite forallb_forall in T.
  specialize (T s Hin). apply Z.ltb_lt in T. lia.
Qed.


Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma eqv_shape : forall R pc m ms', ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (seg_rom rsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom rsegs) /\ xregs_eqv R (ms_regs ms').
Proof.
  intros R pc m ms' H. destruct ms'. unfold ms_eqv in H. cbn in H |- *.
  destruct H as (HR & HF & Hp & Hs & Hrv & Hfc & Hm & Hro). subst. split; [reflexivity | exact HR].
Qed.

Lemma table_ro : forallb (fun i => ro_addr rsegs (Z_to_bv 64 (0x104a4 + Z.of_nat i))) (seq 0 65) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_ro_at : forall a, 0x104a4 <= a < 0x104a4 + 65 -> ro_addr rsegs (Z_to_bv 64 a) = true.
Proof.
  intros a Ha. pose proof table_ro as T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat (a - 0x104a4)) ltac:(apply in_seq; lia)).
  replace (0x104a4 + Z.of_nat (Z.to_nat (a - 0x104a4))) with a in T by lia. exact T.
Qed.

End P.

Lemma pairwise_mid : forall {X} (R : X -> X -> Prop) b1 x b2 y,
  pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) -> R x y \/ R y x.
Proof.
  intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y H Hy; cbn in *.
  - left. apply (proj1 H). exact Hy.
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH x b2 y H2 Hy).
Qed.

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HSEG : ms_segs B = rsegs.

Lemma ceil_val : 2 ^ 33 <= alloc_ceiling < 2 ^ 47.
Proof. pose proof (@YM05.alloc_ceiling_val rc) as H. lia. Qed.

Lemma seg_img : forall s a, In s rsegs ->
  Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> in_img B a.
Proof.
  intros s a Hin Ha. pose proof (rsegs_seg_top s Hin) as T. unfold in_img. rewrite HSEG.
  split; [intros E; rewrite E in Hin; exact Hin|].
  exists (segment_reservation s). split; [apply in_map; exact Hin|].
  unfold segment_reservation. cbn [fst snd]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). unfold page_round_down_Z, page_round_up_Z, page_size.
  rewrite (Z.mod_small (Z.of_N (seg_base s) / 4096 * 4096)) by (Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma fs_img : forall a s, find_segment rsegs a 1 = Some s -> in_img B a.
Proof. intros a s H. destruct (fs_some _ _ _ _ H) as (Hin & H1 & H2). apply (seg_img s); [exact Hin | lia]. Qed.

Lemma noimg_fs : forall a, ~ in_img B a -> find_segment rsegs a 1 = None.
Proof. intros a H. destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity]. exfalso. apply H. eapply fs_img; exact E. Qed.

Lemma img_bound : forall a, in_img B a -> 0 <= a < 2 ^ 33.
Proof.
  intros a (_ & s & Hs & H1 & H2). rewrite HSEG in Hs. unfold segments_reserved in Hs.
  apply in_map_iff in Hs as (s0 & <- & Hin). pose proof (rsegs_seg_top s0 Hin) as T.
  unfold segment_reservation in H1, H2. cbn [fst snd] in H1, H2.
  rewrite !Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
  unfold page_round_down_Z, page_round_up_Z, page_size in H1, H2.
  assert (0 <= Z.of_N (seg_base s0)) by lia. assert (0 <= Z.of_N (seg_size s0)) by lia.
  split; [pose proof (Z.mod_pos_bound (Z.of_N (seg_base s0) / 4096 * 4096) (2 ^ 64)); lia|].
  rewrite Z_to_bv_unsigned in H2. unfold bv_wrap in H2. change (bv_modulus 64) with (2 ^ 64) in H2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma MR_keep : forall L A mem mem' md, aa_MR API L A mem md ->
  (forall a, owned B L A a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> present mem' (ptr_addr L p + i)) ->
  aa_MR API L A mem' md.
Proof.
  intros L A mem mem' md HM Ho Hb. destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hm).
  eapply (mr_frame B _ (aa_laws API) L A mem mem' md md HM).
  - intros a Ha. unfold mbyte. rewrite (Ho a Ha). reflexivity.
  - intros a Ha (b0 & Hb0). exists b0. rewrite (Ho a Ha). exact Hb0.
  - exact Hb.
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hm.
Qed.

Lemma owned_low : forall L A mem md a, aa_MR API L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof. intros L A mem md a HM Ho. exact (mr_owned_low B _ (aa_laws API) L A mem md a HM Ho). Qed.

Lemma blk_user : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn [fst snd] in E.
  injection E as E1 E2. subst k'. exists p. split; assumption.
Qed.

Lemma blk_of_user : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply (in_map (fun b => (ptr_addr L (fst b), snd b))) in H. exact H. Qed.

Lemma blk_facts : forall L A mem md a k, aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> present mem (a + i) /\ ~ owned B L A (a + i)).
Proof.
  intros L A mem md a k HM Hin. destruct (blk_user L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks_range B _ (aa_laws API) L A mem md p k HM Hp) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (mr_blocks B _ (aa_laws API) L A mem md p k i HM Hp Hi) as (P & _ & _ & N). split; assumption.
Qed.

Lemma blk_disj : forall L A mem md b1 x b2 y, aa_MR API L A mem md -> blocks L A = b1 ++ x :: b2 -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros L A mem md b1 x b2 y HM E Hy. pose proof (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) as P.
  rewrite E in P. destruct (pairwise_mid _ _ _ _ _ P Hy) as [D|D]; unfold ranges_disjoint in D; lia.
Qed.

Lemma word_mem_keep : forall m m' a v, word_mem (ms_segs B) m a v ->
  (forall k, 0 <= k < 8 -> mbyte (ms_segs B) m' (a + k) = mbyte (ms_segs B) m (a + k)) -> word_mem (ms_segs B) m' a v.
Proof. intros m m' a v H K k Hk. rewrite K by lia. apply H. exact Hk. Qed.

Lemma ledger_keep : forall L A m m' Lam peak cnt fail, ledger B L A m Lam peak cnt fail ->
  (forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  (forall a k i, 0 <= k -> In (a - 16, k + 16) (blocks L A) -> 0 <= i < 8 ->
     mbyte (ms_segs B) m' (a - 16 + i) = mbyte (ms_segs B) m (a - 16 + i)) ->
  ledger B L A m' Lam peak cnt fail.
Proof.
  intros L A m m' Lam peak cnt fail (AW & R1 & R2 & R3 & ND & FA) HS HH.
  destruct AW as (W1 & W2 & W3 & W4).
  split; [|split; [exact R1|split; [exact R2|split; [exact R3|split; [exact ND|]]]]].
  - split; [|split; [|split]]; eapply word_mem_keep; try eassumption; intros k Hk; apply HS;
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia.
  - eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Hni). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact Hin|]. split; [|exact Hni].
    eapply word_mem_keep; [exact Hw|]. intros j Hj. apply (HH a k j Hk Hin Hj).
Qed.

Lemma munch_at : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros W m m' a H Ha Ho. apply H. rewrite unsigned_lit by lia. exact Ho. Qed.

Lemma mbyte_eq_of : forall segs m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros segs m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma wr_eq_of : forall segs m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof. intros segs m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.

Lemma wr_of_present : forall segs m a, present m a -> writable_at segs m a.
Proof. intros segs m a (b0 & Hb). unfold writable_at, wview. rewrite Hb. discriminate. Qed.

Lemma mem_inv_keep : forall m m', mem_inv rsegs m ->
  (forall x b, m' x = Some b -> m x <> None \/ find_segment rsegs (bv_unsigned x) 1 = None) -> mem_inv rsegs m'.
Proof.
  intros m m' MI K x b Hx. destruct (K x b Hx) as [H|H].
  - destruct (m x) as [b0|] eqn:E; [exact (MI x b0 E) | congruence].
  - apply ro_addr_nofs. exact H.
Qed.

Lemma chain3 : forall m0 m1 m2 m3 a, m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a) ->
  mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a) ->
  m3 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a) ->
  mbyte rsegs m3 a = mbyte rsegs m0 a /\ (writable_at rsegs m0 a <-> writable_at rsegs m3 a).
Proof.
  intros m0 m1 m2 m3 a E1 [E2 W2] E3.
  pose proof (wr_eq_of rsegs _ _ _ E1) as W1. pose proof (wr_eq_of rsegs _ _ _ E3) as W3. split; [|tauto].
  rewrite (mbyte_eq_of _ _ _ _ E3), E2. exact (mbyte_eq_of _ _ _ _ E1).
Qed.

Lemma MR_high : forall L A mem mem' md lo hi, aa_MR API L A mem md -> munch [(lo, hi)] mem mem' -> alloc_ceiling <= lo ->
  aa_MR API L A mem' md.
Proof.
  intros L A mem mem' md lo hi HM MU Hlo. pose proof ceil_val as HC.
  apply (MR_keep L A mem mem' md HM).
  - intros a Ho. pose proof (owned_low L A mem md a HM Ho). apply (munch_at _ _ _ _ MU); [lia | apply outside1; lia].
  - intros p n i Hp Hi. destruct (blk_facts L A mem md _ _ HM (blk_of_user L A p n Hp)) as (H1 & H2 & H3).
    destruct (H3 i Hi) as ((b0 & Hb) & _). exists b0.
    rewrite (munch_at _ _ _ (ptr_addr L p + i) MU); [exact Hb | lia | apply outside1; lia].
Qed.

Lemma ledger_high : forall L A mem mem' md Lam peak cnt fail lo hi, aa_MR API L A mem md ->
  ledger B L A mem Lam peak cnt fail -> munch [(lo, hi)] mem mem' -> alloc_ceiling <= lo ->
  ledger B L A mem' Lam peak cnt fail.
Proof.
  intros L A mem mem' md Lam peak cnt fail lo hi HM HL MU Hlo. pose proof ceil_val as HC.
  apply (ledger_keep L A mem mem' Lam peak cnt fail HL).
  - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
    apply mbyte_eq_of. apply (munch_at _ _ _ _ MU); [lia | apply outside1; lia].
  - intros a k i Hk Hin Hi. destruct (blk_facts L A mem md _ _ HM Hin) as (H1 & H2 & _).
    apply mbyte_eq_of. apply (munch_at _ _ _ _ MU); [lia | apply outside1; lia].
Qed.

Lemma auxv_high : forall L A mem mem' md sec lo lo' hi, aa_MR API L A mem md -> auxv_pre B sec lo mem ->
  munch [(lo', hi)] mem mem' -> alloc_ceiling <= lo' -> hi <= lo -> lo' <= lo -> auxv_pre B sec lo' mem'.
Proof.
  intros L A mem mem' md sec lo lo' hi HM (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) MU Hlo' Hhi Hle.
  pose proof ceil_val as HC.
  assert (K : forall a v, 0 <= a -> a + 8 <= lo' \/ hi <= a -> a + 8 <= 2 ^ 64 ->
    word_mem (ms_segs B) mem a v -> word_mem (ms_segs B) mem' a v).
  { intros a v Ha0 Ha1 Ha2 W. apply (word_mem_keep mem mem' a v W). intros k Hk.
    apply mbyte_eq_of. apply (munch_at _ _ _ _ MU); [lia | apply outside1; lia]. }
  assert (LB : 0 <= ms_libc B + 8 /\ ms_libc B + 16 <= alloc_ceiling).
  { pose proof (owned_low L A mem md (ms_libc B + 8) HM ltac:(right; unfold static_owned; lia)).
    pose proof (owned_low L A mem md (ms_libc B + 15) HM ltac:(right; unfold static_owned; lia)). lia. }
  exists av, ar. split; [apply K; [lia | lia | lia | exact H1]|].
  split; [intros k Hk; apply K; [lia | lia | lia | apply H2; exact Hk]|].
  split; [apply K; [lia | lia | lia | exact H3]|].
  split; [apply K; [lia | lia | lia | exact H4]|].
  repeat split; lia.
Qed.

Lemma ro_img : forall x, 0 <= x < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 x) = true -> in_img B x.
Proof.
  intros x Hx H. unfold ro_addr in H. rewrite unsigned_lit in H by lia.
  destruct (find_segment rsegs x 1) as [s|] eqn:F; [exact (fs_img x s F) | discriminate].
Qed.

Lemma present_of_mbyte : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> mbyte rsegs m a <> None -> present m a.
Proof.
  intros m a Ha Hi H. rewrite mbyte_mrd, mrd_nofs in H by (rewrite wa_unsigned by lia; apply noimg_fs; exact Hi).
  destruct (m (wa a)) as [b0|] eqn:E; [exists b0; first [exact E | reflexivity] | congruence].
Qed.

End H.

Lemma outside3 : forall l1 h1 l2 h2 l3 h3 x, x < l1 \/ h1 <= x -> x < l2 \/ h2 <= x -> x < l3 \/ h3 <= x ->
  outside [(l1, h1); (l2, h2); (l3, h3)] x.
Proof. intros l1 h1 l2 h2 l3 h3 x H1 H2 H3. cbn. split; [lia | split; [lia | split; [lia | exact I]]]. Qed.

Lemma ms_rel_MS : forall s R F pc fc rv m0 ro, ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  exists m, s = MS R F pc fc rv m ro /\ mem_rel rsegs m m0.
Proof.
  intros [R' F' pc' sv' rv' fc' m' ro'] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. exists m'. split; [reflexivity | exact H8].
Qed.

Lemma ro_false_hi : forall a, 2 ^ 32 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (ro_addr_low _ E) as L. rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb)] | exact (wr_at_rel rsegs m m0 A _ HR Hw)].
Qed.

Lemma stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [W (b0 & Hb)]. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ HR (ro_false_of_wview rsegs m m0 _ HR W)). exact W.
  - exists b0. rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma stk_norm : forall m lo hi, ro_agree rsegs m -> 2 ^ 32 <= lo -> stk rsegs m lo hi ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RO Hlo (H1 & H2 & H). pose proof (mem_rel_normalize rsegs m RO) as HR.
  split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [W (b0 & Hb)]. split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ HR (ro_false_hi a ltac:(lia))). exact W.
  - exists b0. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ HR). exact Hb.
Qed.

Lemma rw_cells_norm : forall m A cs, ro_agree rsegs m -> 2 ^ 32 <= A -> rw_cells rsegs m A cs ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RO HA [[Hwf Hb] Hw]. pose proof (mem_rel_normalize rsegs m RO) as HR.
  pose proof Hw as (W1 & W2 & _).
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ RO Hb)]|].
  apply (wr_at_norm rsegs m _ A _ HR Hw). intros i Hi. apply ro_false_hi. lia.
Qed.

Definition dec_mid_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (text lenp : Z) (tb : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 m',
    ms' = MS (mkR (Z_to_bv 64 0x15468) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) s1
                  (Z_to_bv 64 (b64_M tb)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 text) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x14064) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp - 112) (CB 8 j0 :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma dec_run1_ro : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (text lenp : Z) (tb : list Z) (slack : list byte),
  bytes_at rsegs m text (map (Z_to_bv 8) tb ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) tb) ->
  (- (text + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
  Z.of_nat (length tb) <= 2 ^ 28 ->
  stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp) -> 2 ^ 32 <= bv_unsigned sp - 112 ->
  text + Z.of_nat (length (map (Z_to_bv 8) tb ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= text ->
  0 <= lenp < 2 ^ 64 ->
  ro_agree rsegs m ->
  evt rsegs (dec_mid_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc text lenp tb m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 text) (Z_to_bv 64 lenp) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15410) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m text lenp tb slack BS NONUL PAD HL ST SPH DISJ HLP RO.
  pose proof (mem_rel_normalize rsegs m RO) as HR.
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply (dec_run1 SLEN); [apply bytes_at_normalize; [exact RO | exact BS] | exact NONUL | exact PAD | exact HL |
      apply stk_norm; [exact RO | lia | exact ST] | lia | exact DISJ | exact HLP | apply mem_inv_normalize]. }
  intros s (s0' & Q & RS & RSAME).
  destruct Q as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j0 & m0' & -> & MU & WM & _ & FR).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ RS) as (m1 & -> & HR').
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m1 m0' HR HR' RSAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' HR HR' RSAME WM)|].
  split; [exact (ro_agree_same rsegs m m1 RO RSAME)|].
  exact (rw_cells_rel m1 m0' _ _ HR' FR).
Qed.

Definition dec_ok_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo lenp q : Z) (tb bs : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' lenp (le8 (Z_to_bv 64 (Z.of_nat (length bs)))) /\
    bytes_at rsegs m' q (map (Z_to_bv 8) bs) /\
    munch [(q, q + b64_M tb); (lenp, lenp + 8); (bv_unsigned sp - 112, bv_unsigned sp - 104)] m m' /\
    wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Lemma dec_go_ok_ro : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lenp q tx : Z) (tb bs : list Z) (lb j0 : list byte),
  memchr_contract -> b64_dec tb = Some bs -> 0 < q < 2 ^ 64 ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2^31 - 1 ->
  tx <> 0 -> lenp <> 0 -> lenp mod 8 = 0 ->
  bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) ->
  bytes_at rsegs m lenp lb -> length lb = 8%nat -> wr_at rsegs m lenp 8 ->
  wr_at rsegs m q (b64_M tb) ->
  rw_cells rsegs m (bv_unsigned sp - 112) (CB 8 j0 :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  2 ^ 32 <= bv_unsigned sp - 112 -> 2 ^ 32 <= lenp ->
  (forall i, 0 <= i < b64_M tb -> ro_addr rsegs (wa (q + i)) = false) ->
  ro_agree rsegs m ->
  q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q ->
  q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q ->
  q + b64_M tb <= lenp \/ lenp + 8 <= q ->
  q + b64_M tb <= bv_unsigned sp - 112 \/ bv_unsigned sp <= q ->
  lenp + 8 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= lenp ->
  tx + Z.of_nat (length tb) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= tx ->
  evt rsegs (dec_ok_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp - 112) lenp q tb bs m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) x9 (Z_to_bv 64 q)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15468) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7
    x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m lenp q tx tb bs lb j0
    MC HB HQ NZ BOK HLEN HTX HL0 HL8 TX LB LB8 WL WQ FR SPH LPH QRO RO D1 D2 D3 D4 D5 D6.
  pose proof (mem_rel_normalize rsegs m RO) as HR. pose proof WL as (WL1 & WL2 & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply dec_loop_ok with (lo := bv_unsigned sp - 112); [exact MC | exact HB | exact NZ | exact BOK | exact HLEN |
      exact HTX | lia | exact HL0 | exact HL8 |
      apply bytes_at_normalize; [exact RO | exact TX] |
      apply bytes_at_normalize; [exact RO | exact LB] | exact LB8 |
      apply (wr_at_norm rsegs m _ lenp 8 HR WL); intros i Hi; apply ro_false_hi; lia |
      exact (wr_at_norm rsegs m _ q _ HR WQ QRO) |
      apply rw_cells_norm; [exact RO | exact SPH | exact FR] | apply stk_empty; lia | lia | apply mem_inv_normalize |
      exact D1 | exact D2 | exact D3 | exact D4 | exact D5 | exact D6]. }
  intros s (s0' & Q & RS & RSAME).
  destruct Q as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & -> & L0 & BY0 & MU & WM & _ & ST0).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ RS) as (m1 & -> & HR').
  do 14 eexists. exists m1. split; [reflexivity|].
  split; [exact (proj2 (bytes_at_rel rsegs m1 m0' _ _ HR') L0)|].
  split; [exact (proj2 (bytes_at_rel rsegs m1 m0' _ _ HR') BY0)|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m1 m0' HR HR' RSAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' HR HR' RSAME WM)|].
  split; [exact (ro_agree_same rsegs m m1 RO RSAME)|].
  exact (stk_rel m1 m0' _ _ HR' ST0).
Qed.

Definition dec_free_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lenp q : Z) (tb : list Z) (lb : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x1554c) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 x8 (Z_to_bv 64 q)
                  (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14378) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' lenp lb /\
    rw_cells rsegs m' (bv_unsigned sp - 112) (C8 (Z_to_bv 64 lenp) :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
    munch [(q, q + b64_M tb); (bv_unsigned sp - 112, bv_unsigned sp - 104)] m m' /\ wmono rsegs m m' /\
    ro_agree rsegs m'.

Lemma dec_go_fail_ro : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (lenp q tx : Z) (tb : list Z) (lb j0 : list byte),
  memchr_contract -> b64_dec tb = None -> 0 < q < 2 ^ 64 ->
  no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2^31 - 1 ->
  tx <> 0 -> lenp <> 0 -> lenp mod 8 = 0 ->
  bytes_at rsegs m tx (map (Z_to_bv 8) (tb ++ [0])) ->
  bytes_at rsegs m lenp lb -> length lb = 8%nat -> wr_at rsegs m lenp 8 ->
  wr_at rsegs m q (b64_M tb) ->
  rw_cells rsegs m (bv_unsigned sp - 112) (CB 8 j0 :: dec_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  2 ^ 32 <= bv_unsigned sp - 112 -> 2 ^ 32 <= lenp ->
  (forall i, 0 <= i < b64_M tb -> ro_addr rsegs (wa (q + i)) = false) ->
  ro_agree rsegs m ->
  q + b64_M tb <= tx \/ tx + Z.of_nat (length tb) + 1 <= q ->
  q + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= q ->
  q + b64_M tb <= lenp \/ lenp + 8 <= q ->
  q + b64_M tb <= bv_unsigned sp - 112 \/ bv_unsigned sp <= q ->
  lenp + 8 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= lenp ->
  tx + Z.of_nat (length tb) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= tx ->
  evt rsegs (dec_free_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lenp q tb lb m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 (Z_to_bv 64 lenp) x9 (Z_to_bv 64 q)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tx) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15468) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7
    x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m lenp q tx tb lb j0
    MC HB HQ NZ BOK HLEN HTX HL0 HL8 TX LB LB8 WL WQ FR SPH LPH QRO RO D1 D2 D3 D4 D5 D6.
  pose proof (mem_rel_normalize rsegs m RO) as HR. pose proof WL as (WL1 & WL2 & _).
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply dec_go_fail; [exact MC | exact HB | exact NZ | exact BOK | exact HLEN |
      exact HTX | lia | exact HL0 | exact HL8 |
      apply bytes_at_normalize; [exact RO | exact TX] |
      apply bytes_at_normalize; [exact RO | exact LB] | exact LB8 |
      apply (wr_at_norm rsegs m _ lenp 8 HR WL); intros i Hi; apply ro_false_hi; lia |
      exact (wr_at_norm rsegs m _ q _ HR WQ QRO) |
      apply rw_cells_norm; [exact RO | exact SPH | exact FR] | lia | apply mem_inv_normalize |
      exact D1 | exact D2 | exact D3 | exact D4 | exact D5 | exact D6]. }
  intros s (s0' & Q & RS & RSAME).
  destruct Q as (u0' & u1' & u2' & y8 & c1' & c2' & c3' & c4' & c5' & c6' & c7' & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & u3' & u4' & u5' & u6' & m0' & -> & L0 & FR0 & MU & WM & _).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ RS) as (m1 & -> & HR').
  do 25 eexists. exists m1. split; [reflexivity|].
  split; [exact (proj2 (bytes_at_rel rsegs m1 m0' _ _ HR') L0)|].
  split; [exact (rw_cells_rel m1 m0' _ _ HR' FR0)|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m1 m0' HR HR' RSAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' HR HR' RSAME WM)|].
  exact (ro_agree_same rsegs m m1 RO RSAME).
Qed.

Lemma chain2 : forall m0 m1 m2 a, m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a) ->
  mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a) ->
  mbyte rsegs m2 a = mbyte rsegs m0 a /\ (writable_at rsegs m0 a <-> writable_at rsegs m2 a).
Proof. intros m0 m1 m2 a E1 E2. exact (chain3 m0 m1 m2 m2 a E1 E2 eq_refl). Qed.

Lemma chain5 : forall m0 m1 m2 m3 m4 a, m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a) ->
  mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a) ->
  m3 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a) ->
  mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a) ->
  mbyte rsegs m4 a = mbyte rsegs m0 a /\ (writable_at rsegs m0 a <-> writable_at rsegs m4 a).
Proof.
  intros m0 m1 m2 m3 m4 a E1 E2 E3 [E4 W4].
  destruct (chain3 m0 m1 m2 m3 a E1 E2 E3) as [F W]. split; [rewrite E4; exact F | tauto].
Qed.

Lemma layout_le_trans : forall A A1 L L1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (H1 & H2 & H3 & H4) (K1 & K2 & K3 & K4) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (K4 r ltac:(lia)). apply H4. exact Hr.
Qed.

Lemma uniq_mid : forall (b1 b2 c1 c2 : list (Z * Z)) x, 0 < snd x ->
  pairwise ranges_disjoint (b1 ++ x :: b2) -> b1 ++ x :: b2 = c1 ++ x :: c2 -> b1 ++ b2 = c1 ++ c2.
Proof.
  intros b1. induction b1 as [|z b1 IH]; intros b2 c1 c2 x Hx P E; destruct c1 as [|y c1]; cbn in *.
  - injection E as E. exact E.
  - injection E as E1 E2. subst y. exfalso. destruct P as [P _].
    assert (I : In x b2) by (rewrite E2; apply in_or_app; right; left; reflexivity).
    specialize (P x I). unfold ranges_disjoint in P. lia.
  - injection E as E1 E2. subst z. exfalso. destruct P as [P _].
    assert (I : In x (b1 ++ x :: b2)) by (apply in_or_app; right; left; reflexivity).
    specialize (P x I). unfold ranges_disjoint in P. lia.
  - injection E as E1 E2. subst y. f_equal. destruct P as [_ P]. exact (IH b2 c1 c2 x Hx P E2).
Qed.

Lemma lam_mid : forall (Lam l1 l2 : list (Z * Z)) q k, ~ In q (map fst Lam) ->
  (q, k) :: Lam = l1 ++ (q, k) :: l2 -> l1 ++ l2 = Lam.
Proof.
  intros Lam l1 l2 q k N E. destruct l1 as [|y l1]; cbn in E.
  - injection E as E. cbn. symmetry. exact E.
  - injection E as E1 E2. exfalso. apply N. rewrite E2, map_app. apply in_or_app. right. left. reflexivity.
Qed.

Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis CO : ctx_owned B API.

Lemma own_mid : forall L A m md L1 A1 m1 md1 a, aa_MR API L A m md -> aa_MR API L1 A1 m1 md1 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L1 A1 a.
Proof.
  intros L A m md L1 A1 m1 md1 a HM HM1 Hr Hn Ho.
  destruct Hr as [Hr | Hr].
  - pose proof (owned_low B API L1 A1 m1 md1 a HM1 Ho). lia.
  - destruct Ho as [Ho | Ho].
    + apply Hn. apply (CO L A m md a HM). exact (YL01.ax_img AX L1 A1 m1 md1 a HM1 Hr Ho).
    + apply Hn. right. exact Ho.
Qed.

Lemma present_of_wr : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> writable_at rsegs m a -> present m a.
Proof.
  intros m a Ha Hi W. unfold writable_at in W. change (Z_to_bv 64 a) with (wa a) in W.
  rewrite wview_nofs in W by (rewrite wa_unsigned by lia; apply (noimg_fs B HSEG); exact Hi).
  destruct (m (wa a)) as [b0|] eqn:E; [exists b0; exact E | congruence].
Qed.

End X.

(* lia case-splits every disjunction and mod fact in the context. rs_hide_all wraps each one in Stdlib's id, an atom
   lia does not look into; a use site does `unfold id in H` first. A tactic only: no new constant. *)
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => let P := type of H in change (id P) in H
  | H : _ mod _ = _ |- _ => let P := type of H in change (id P) in H end.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Theorem preset_base64_decode_holds : strlen_contract -> memchr_contract -> fuzz_malloc_contract B API RF ->
  fuzz_free_contract B API RF -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  preset_base64_decode_contract B API RF.
Proof.
  intros SLEN MC FM FF AX CO L A regs mem md text lenp tb slack b Lam peak cnt fail HSEG HERR RO PRE R10 R11
    NZ BOK HLEN TXT PAD WHERE LP LP8 LPW LPD LED RES ROOM.
  pose proof ceil_val as HC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCE & H63 & HWS & HTP & HER & HAUX).
  unfold DEC_STACK, ALLOC_STACK in HCE, HWS.
  rewrite HSEG in HWS, HER, TXT, LPW.
  remember (spZ regs) as sp eqn:Esp0.
  assert (Esp : bv_unsigned (reg_get regs (Z_to_bv 5 2)) = sp).
  { rewrite Esp0. unfold spZ. rewrite getr_reg by (vm_compute; discriminate). reflexivity. }
  assert (E10 : reg_get regs (Z_to_bv 5 10) = Z_to_bv 64 text).
  { rewrite <- getr_reg by (vm_compute; discriminate). exact R10. }
  assert (E11 : reg_get regs (Z_to_bv 5 11) = Z_to_bv 64 lenp).
  { rewrite <- getr_reg by (vm_compute; discriminate). exact R11. }
  assert (ERA : ret_pc (reg_get regs (Z_to_bv 5 1)) = YK11.getr regs 1).
  { rewrite <- (getr_reg regs (Z_to_bv 5 1)) by (vm_compute; discriminate). apply ret_pc_ok. exact HRA. }
  assert (ROm : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (HM : dec_size tb + 16 <= 2 ^ 28) by (unfold dec_size; Z.div_mod_to_equations; lia).
  assert (HM0 : 3 <= dec_size tb) by (unfold dec_size; Z.div_mod_to_equations; lia).
  assert (EM : b64_M tb = dec_size tb) by reflexivity.
  assert (LP8' : lenp + 8 <= 2 ^ 64) by (Z.div_mod_to_equations; lia).
  assert (TB0 : bytes_at rsegs mem text (map (Z_to_bv 8) (tb ++ [0]))).
  { apply bytes_at_app in TXT. exact (proj1 TXT). }
  pose proof (bytes_at_bound _ _ _ _ TB0) as TBB. rewrite length_map, length_app in TBB. cbn [length] in TBB.
  pose proof (Z.mod_pos_bound (- (text + Z.of_nat (length tb) + 1)) 8 ltac:(lia)) as K0B.
  pose (slack' := firstn (Z.to_nat ((- (text + Z.of_nat (length tb) + 1)) mod 8)) slack).
  assert (LS' : Z.of_nat (length slack') = (- (text + Z.of_nat (length tb) + 1)) mod 8).
  { unfold slack'. rewrite length_firstn. lia. }
  assert (BS1 : bytes_at rsegs mem text (map (Z_to_bv 8) tb ++ Z_to_bv 8 0 :: slack')).
  { rewrite <- (firstn_skipn (Z.to_nat ((- (text + Z.of_nat (length tb) + 1)) mod 8)) slack) in TXT.
    rewrite app_assoc in TXT. apply bytes_at_app in TXT. destruct TXT as [T _].
    eapply bytes_at_ext; [exact T|]. rewrite map_app, <- app_assoc. reflexivity. }
  assert (NONUL : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) tb)).
  { intros Hin. apply in_map_iff in Hin as (x & Ex & Hx).
    unfold no_zero, bytes_ok in NZ, BOK. rewrite Forall_forall in NZ, BOK.
    specialize (NZ x Hx). specialize (BOK x Hx). cbv beta in NZ, BOK.
    apply (f_equal bv_unsigned) in Ex. rewrite !Z_to_bv_unsigned in Ex. unfold bv_wrap in Ex.
    change (bv_modulus 8) with 256 in Ex. rewrite (Z.mod_small x 256) in Ex by lia. cbn in Ex. lia. }
  assert (TW : sp <= text \/ text + Z.of_nat (length tb) + 1 <= alloc_ceiling).
  { unfold dec_text_where in WHERE. rewrite HSEG in WHERE.
    destruct WHERE as [Hro | [Hsp | [(a & k & Hin & H1 & H2) | (a & k & Hin & H1 & H2)]]].
    - right. pose proof (img_bound B HSEG (text + Z.of_nat (length tb))
        (ro_img B HSEG (text + Z.of_nat (length tb)) ltac:(lia) (Hro (Z.of_nat (length tb)) ltac:(lia)))). lia.
    - left. lia.
    - right. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HMR LED Hin). lia.
    - right. destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & B2 & _). lia. }
  assert (DW : forall i, 0 <= i <= Z.of_nat (length tb) ->
    (exists a k, In (a, k) (blocks L A) /\ a <= text + i < a + k) \/
    ro_addr rsegs (Z_to_bv 64 (text + i)) = true \/ sp <= text + i).
  { intros i Hi. unfold dec_text_where in WHERE. rewrite HSEG in WHERE.
    destruct WHERE as [Hro | [Hsp | [(a & k & Hin & H1 & H2) | (a & k & Hin & H1 & H2)]]].
    - right. left. apply Hro. lia.
    - right. right. lia.
    - left. destruct LED as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
      destruct (FA _ Hin) as (Hk & Hb & _). cbn [fst snd] in *.
      exists (a - 16), (k + 16). split; [exact Hb | lia].
    - left. exists a, k. split; [exact Hin | lia]. }
  assert (TX0 : text <> 0).
  { destruct (DW 0 ltac:(lia)) as [(a & k & Hin & H1) | [Hro | Hsp]].
    - destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & _). lia.
    - pose proof (ro_pos (text + 0) ltac:(lia) Hro). lia.
    - lia. }
  rs_hide_all.
  rewrite HSEG.
  eapply (evt_SR_canon rsegs _ _ md _).
  { change (RegisterBridge.canonical_register_state
              (@YK11.mkst fx regs (Z_to_bv 64 PRESET_BASE64_DECODE) mem (YK11.seg_rom rsegs)))
      with (MS (mkR_of regs) (@fp_regs fx) (Z_to_bv 64 0x15410) (@fp_csr fx) None mem (seg_rom rsegs)).
    rewrite mkR_of_eq, E10, E11.
    eapply (dec_run1_ro SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem text lenp tb slack').
    - exact BS1.
    - exact NONUL.
    - lia.
    - lia.
    - rewrite Esp. apply stk_of_writable; [lia | lia |]. intros a Ha. apply HWS. lia.
    - rewrite Esp. lia.
    - rewrite Esp, length_app, length_map. cbn [length]. unfold id in TW. destruct TW as [TW | TW]; lia.
    - lia.
    - exact ROm. }
  { exact Hh. }
  { exact Hl. }
  intros ms1 (c1 & (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & j0 & m1 & -> & MU1 & WM1 & RO1 & FR1)
    & EQV1).
  destruct (eqv_shape _ _ _ _ EQV1) as (S1' & X1). rewrite S1'. clear S1' EQV1.
  remember (ms_regs ms1) as R1 eqn:ER1. clear ER1 ms1.
  rewrite Esp in MU1, FR1.
  assert (G1 : YK11.getr R1 1 = Z_to_bv 64 0x15468) by exact (eqv_getr _ _ 1 _ X1 ltac:(lia) eq_refl).
  assert (G2 : YK11.getr R1 2 = Z_to_bv 64 (sp - 112)).
  { apply (eqv_getr _ _ 2 _ X1 ltac:(lia)).
    change (Z_to_bv 64 (bv_unsigned (reg_get regs (Z_to_bv 5 2)) - 112) = Z_to_bv 64 (sp - 112)).
    rewrite Esp. reflexivity. }
  assert (G4 : YK11.getr R1 4 = YK11.getr regs 4).
  { apply (eqv_getr _ _ 4 _ X1 ltac:(lia)). rewrite getr_reg by (vm_compute; discriminate). reflexivity. }
  assert (G10 : YK11.getr R1 10 = Z_to_bv 64 (dec_size tb)) by exact (eqv_getr _ _ 10 _ X1 ltac:(lia) eq_refl).
  assert (S1 : spZ R1 = sp - 112) by (unfold spZ; rewrite G2, unsigned_lit by lia; reflexivity).
  assert (HM1 : aa_MR API L A m1 md) by (apply (MR_high B API L A mem m1 md (sp - 112) sp HMR MU1); lia).
  assert (LED1 : ledger B L A m1 Lam peak cnt fail)
    by (apply (ledger_high B API L A mem m1 md Lam peak cnt fail (sp - 112) sp HMR LED MU1); lia).
  pose proof (FM L A R1 m1 md (dec_size tb) b Lam peak cnt fail) as FM1.
  rewrite HSEG in FM1.
  eapply SR_bind; [apply FM1; clear FM1 | clear FM1].
  - unfold call_pre_k. rewrite S1, G1, G4, HSEG.
    split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [apply ret_ok_even; vm_compute; reflexivity|].
    split; [unfold id in HAL; Z.div_mod_to_equations; lia|].
    split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a Ha; unfold writable_at; apply WM1; apply HWS; unfold ALLOC_STACK in Ha; lia|].
    split; [exact HTP|].
    split; [intros a Ha; unfold writable_at; apply WM1; apply HER; exact Ha|].
    intros Hf. apply (auxv_high B API L A mem m1 md (ly_sec L) sp (sp - 112) sp HMR (HAUX Hf) MU1); lia.
  - exact G10.
  - lia.
  - exact LED1.
  - exact RO1.
  - exact RES.
  - exact ROOM.
  - lia.
  - intros c2 (L1 & A1 & R2 & m2 & md1 & res & -> & RO2 & GK1 & INIT1 & LI1 & CP1 & LEN1 & R2a & KEEP1 & UBK1
      & ARMS).
    pose proof CP1 as (HM2 & HWF2 & HBD2 & HLL1 & HPA1 & RP1 & HMD1 & FR2 & BK2 & SC2).
    rewrite HSEG in FR2, SC2.
    unfold keeps in KEEP1. rewrite HSEG in KEEP1.
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    rewrite G1.
    assert (RRES : res = 0 \/ (4096 <= res - 16 /\ res + dec_size tb <= alloc_ceiling)).
    { destruct ARMS as [(_ & -> & _) | (_ & _ & _ & _ & _ & _ & _ & (b1 & b2 & EB2 & _) & _)]; [left; reflexivity | right].
      assert (Hin : In (res - 16, dec_size tb + 16) (blocks L1 A1))
        by (rewrite EB2; apply in_or_app; right; left; reflexivity).
      destruct (blk_facts B API L1 A1 m2 md1 _ _ HM2 Hin) as (H1 & H2 & _). lia. }
    rs_hide_all.
    assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - 8336 <= a < sp - 112) ->
      mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
    { intros a Ha Hs. apply FR2.
      - left. exact Ha.
      - intros Ho. pose proof (owned_low B API L A m1 md a HM1 Ho). lia.
      - intros Ho. pose proof (owned_low B API L1 A1 m2 md1 a HM2 Ho). lia.
      - unfold scratch_k. rewrite S1. unfold ALLOC_STACK. lia.
      - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL.
        unfold id in RRES. destruct RRES as [RRES | RRES]; lia. }
    assert (WR2 : forall a, sp - 8336 <= a < sp -> writable_at rsegs m2 a).
    { intros a Ha. destruct (Z_lt_le_dec a (sp - 112)) as [H1|H1].
      - apply SC2. unfold scratch_k. left. rewrite S1. unfold ALLOC_STACK. lia.
      - apply (proj1 (proj2 (HI2 a ltac:(lia) ltac:(lia)))). unfold writable_at. apply WM1. apply HWS. lia. }
    lazymatch type of FR1 with rw_cells _ _ _ ?cs =>
      assert (FRm2 : rw_cells rsegs m2 (sp - 112) cs) end.
    { apply (rw_cells_keep m1 m2 _ _ FR1). intros i Hi. cbn in Hi.
      destruct (HI2 (sp - 112 + i) ltac:(lia) ltac:(lia)) as [E1 E2]. split; [exact E1 | exact (proj1 E2)]. }
    assert (KM2 : forall a k i, In (a, k) (blocks L A) -> a <> 0 -> 0 <= i < k ->
      mbyte rsegs m2 (a + i) = mbyte rsegs mem (a + i)).
    { intros a k i Hin Ha Hi. destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & B2 & _).
      rewrite (KEEP1 a k i Hin Ha Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
    assert (DK2 : forall i, 0 <= i <= Z.of_nat (length tb) -> mbyte rsegs m2 (text + i) = mbyte rsegs mem (text + i)).
    { intros i Hi. destruct (DW i Hi) as [(a & k & Hin & H1) | [Hro | Hsp]].
      - destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & B2 & _).
        replace (text + i) with (a + (text + i - a)) by lia. apply (KM2 a k); [exact Hin | lia | lia].
      - exact (mbyte_ro mem m2 _ ROm RO2 Hro).
      - rewrite (proj1 (HI2 (text + i) ltac:(lia) ltac:(lia))).
        apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
    assert (LK2 : forall i, 0 <= i < 8 -> mbyte rsegs m2 (lenp + i) = mbyte rsegs mem (lenp + i) /\
      (writable_at rsegs mem (lenp + i) <-> writable_at rsegs m2 (lenp + i))).
    { intros i Hi. apply (chain2 mem m1 m2 (lenp + i)).
      - apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
      - apply HI2; lia. }
    assert (Q2 : reg_get R2 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (reg_get regs (Z_to_bv 5 2)) - 112)) by qr RP1 X1 2.
    assert (Q3 : reg_get R2 (Z_to_bv 5 3) = reg_get regs (Z_to_bv 5 3)) by qr RP1 X1 3.
    assert (Q4 : reg_get R2 (Z_to_bv 5 4) = reg_get regs (Z_to_bv 5 4)) by qr RP1 X1 4.
    assert (Q8 : reg_get R2 (Z_to_bv 5 8) = Z_to_bv 64 lenp) by qr RP1 X1 8.
    assert (Q18 : reg_get R2 (Z_to_bv 5 18) = Z_to_bv 64 text) by qr RP1 X1 18.
    assert (Q27 : reg_get R2 (Z_to_bv 5 27) = reg_get regs (Z_to_bv 5 27)) by qr RP1 X1 27.
    assert (Q10 : reg_get R2 (Z_to_bv 5 10) = Z_to_bv 64 res).
    { rewrite <- getr_reg by (vm_compute; discriminate). exact R2a. }
    destruct ARMS as [(EC & ER & _ & _ & _ & RSb1 & _ & EBL & LED2) | (NC & RNZ & RAL & SLOT1 & NST & NIMG & NIN & (b1 & b2 & EB2 & EB1) & LED2)].
    + subst res.
      eapply (evt_SR_canon rsegs _ _ md1 _).
      { change (RegisterBridge.canonical_register_state
                  (@YK11.mkst fx R2 (Z_to_bv 64 0x15468) m2 (YK11.seg_rom rsegs)))
          with (MS (mkR_of R2) (@fp_regs fx) (Z_to_bv 64 0x15468) (@fp_csr fx) None m2 (seg_rom rsegs)).
        rewrite mkR_of_eq, Q2, Q3, Q4, Q10, Q27.
        eapply (dec_null_ret (reg_get regs (Z_to_bv 5 1)) (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3)) (reg_get regs (Z_to_bv 5 4)) (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9)) (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20)) (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23)) (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26)) (reg_get regs (Z_to_bv 5 27)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2).
        - rewrite Esp. exact FRm2.
        - rewrite Esp. lia. }
      { exact Hh2. }
      { exact Hl2. }
      intros ms3 (can & -> & EQV3).
      destruct (eqv_shape _ _ _ _ EQV3) as (S3 & X3). rewrite S3. clear S3 EQV3.
      remember (ms_regs ms3) as R3 eqn:ER3. clear ER3 ms3.
      apply SR_ret. cbv beta.
      exists L1, A1, R3, m2, md1, 0.
      split; [rewrite ERA; reflexivity|].
      split; [exact RO2|].
      split.
      { unfold guard_kept. rewrite HSEG. intros i Hi. unfold guard_kept in GK1. rewrite HSEG in GK1.
        pose proof (owned_low B API L A mem md _ HMR (got_owned B L A i Hi)) as Hg.
        rewrite (GK1 i Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
      split; [exact INIT1|].
      split.
      { unfold call_post_k. rewrite HSEG.
        split; [exact HM2|]. split; [exact HWF2|]. split; [exact HBD2|]. split; [exact HLL1|]. split; [exact HPA1|].
        split; [exact (rp_of_eqv regs R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3)|].
        split; [exact HMD1|].
        split.
        { intros a Hr Ho1 Ho2 Hsc Hw.
          assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (img_bound B HSEG a Hr); lia]).
          unfold scratch_k, DEC_STACK, ALLOC_STACK in Hsc.
          apply (chain2 mem m1 m2 a).
          - apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
          - apply FR2; [exact Hr | exact Ho1 | exact Ho2 | unfold scratch_k; rewrite S1; unfold ALLOC_STACK; lia |].
            unfold alloc_writes. intros [Hx | (Hx & _)]; [apply Hw; left; exact Hx | lia]. }
        split.
        { intros p k i Hp Hp2 Hi.
          destruct (blk_facts B API L A mem md _ _ HMR (blk_of_user L A p k Hp)) as (B1 & _).
          apply (KM2 _ k); [apply blk_of_user; exact Hp | lia | exact Hi]. }
        intros a Hs. unfold scratch_k, DEC_STACK, ALLOC_STACK in Hs. destruct Hs as [Hs|Hs].
        - apply WR2. lia.
        - exact (SC2 a (or_intror Hs)). }
      split; [exact LEN1|].
      split; [unfold keeps; rewrite HSEG; intros a k i Hin Ha Hi; exact (KM2 a k i Hin Ha Hi)|].
      split; [exact DK2|].
      left. split; [exact EC|]. split; [reflexivity|].
      split; [exact (eqv_getr _ _ 10 _ X3 ltac:(lia) eq_refl)|].
      split; [exact EBL|]. split; [exact UBK1|].
      split; [intros i Hi; exact (proj1 (LK2 i Hi))|].
      split; [exact LED2|]. exact RSb1.
    + assert (Hin : In (res - 16, dec_size tb + 16) (blocks L1 A1))
        by (rewrite EB2; apply in_or_app; right; left; reflexivity).
      destruct (blk_facts B API L1 A1 m2 md1 _ _ HM2 Hin) as (NB1 & NB2 & NB3).
      assert (WRB : wr_at rsegs m2 res (b64_M tb)).
      { rewrite EM. split; [lia|]. split; [lia|]. intros i Hi.
        destruct (NB3 (i + 16) ltac:(lia)) as (P & _).
        replace (res - 16 + (i + 16)) with (res + i) in P by lia.
        exact (wr_of_present _ _ _ P). }
      assert (WRB' : forall a, res <= a < res + dec_size tb -> writable_at rsegs m2 a).
      { intros a Ha. destruct (NB3 (a - (res - 16)) ltac:(lia)) as (P & _).
        replace (res - 16 + (a - (res - 16))) with a in P by lia. exact (wr_of_present _ _ _ P). }
      assert (NI : forall x, res <= x < res + dec_size tb -> ~ in_img B x).
      { intros x Hx. replace x with (res - 16 + (x - (res - 16))) by lia. apply NIMG. lia. }
      assert (DQD : res + b64_M tb <= text \/ text + Z.of_nat (length tb) + 1 <= res).
      { rewrite EM. unfold dec_text_where in WHERE. rewrite HSEG in WHERE.
        destruct WHERE as [Hro | [Hsp | [(a & k & Hin1 & H1 & H2) | (a & k & Hin1 & H1 & H2)]]].
        - destruct (Z_le_gt_dec (res + dec_size tb) text) as [D|D]; [left; exact D|].
          destruct (Z_le_gt_dec (text + Z.of_nat (length tb) + 1) res) as [D'|D']; [right; exact D'|]. exfalso.
          apply (NI (Z.max res text)); [lia|].
          replace (Z.max res text) with (text + (Z.max res text - text)) by lia.
          apply (ro_img B HSEG); [lia|]. apply Hro. lia.
        - left. lia.
        - destruct LED as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
          destruct (FA _ Hin1) as (Hk & Hb & _). cbn [fst snd] in *.
          assert (Hy : In (a - 16, k + 16) (b1 ++ b2)) by (rewrite <- EB1; exact Hb).
          destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a - 16, k + 16) HM2 EB2 Hy)
            as [D|D]; cbn [fst snd] in D; [left | right]; lia.
        - assert (Hy : In (a, k) (b1 ++ b2)) by (rewrite <- EB1; exact Hin1).
          destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a, k) HM2 EB2 Hy)
            as [D|D]; cbn [fst snd] in D; [left | right]; lia. }
      assert (DQT : res + b64_M tb <= 0x104a4 \/ 0x104a4 + 65 <= res).
      { rewrite EM.
        destruct (Z_le_gt_dec (res + dec_size tb) 0x104a4) as [D|D]; [left; exact D|].
        destruct (Z_le_gt_dec (0x104a4 + 65) res) as [D'|D']; [right; exact D'|]. exfalso.
        apply (NI (Z.max res 0x104a4)); [lia|].
        apply (ro_img B HSEG); [lia|]. apply table_ro_at. lia. }
      rs_hide_all.
      assert (TX2 : bytes_at rsegs m2 text (map (Z_to_bv 8) (tb ++ [0]))).
      { apply (bytes_at_keep mem m2 text _ TB0). intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi.
        apply DK2. lia. }
      assert (QRO : forall i, 0 <= i < b64_M tb -> ro_addr rsegs (wa (res + i)) = false).
      { intros i Hi. rewrite EM in Hi. destruct (ro_addr rsegs (wa (res + i))) eqn:E; [|reflexivity]. exfalso.
        apply (NI (res + i)); [lia|]. apply (ro_img B HSEG); [lia|]. exact E. }
      assert (LW2 : forall i, 0 <= i < 8 -> writable_at rsegs m2 (lenp + i)).
      { intros i Hi. apply (proj2 (LK2 i Hi)). apply LPW. exact Hi. }
      assert (LST2 : stk rsegs m2 lenp (lenp + 8)).
      { apply stk_of_writable; [lia | lia |]. intros a Ha. replace a with (lenp + (a - lenp)) by lia. apply LW2. lia. }
      destruct (stk_bytes rsegs m2 lenp (lenp + 8) LST2 ltac:(lia)) as (lb & Hlb & LB2).
      assert (WL2 : wr_at rsegs m2 lenp 8) by (split; [lia|]; split; [lia|]; intros i Hi; exact (LW2 i Hi)).
      destruct (b64_dec tb) as [bs|] eqn:HB.
      * eapply (evt_SR_canon rsegs _ _ md1 _).
        { change (RegisterBridge.canonical_register_state
                    (@YK11.mkst fx R2 (Z_to_bv 64 0x15468) m2 (YK11.seg_rom rsegs)))
            with (MS (mkR_of R2) (@fp_regs fx) (Z_to_bv 64 0x15468) (@fp_csr fx) None m2 (seg_rom rsegs)).
          rewrite mkR_of_eq, Q2, Q3, Q4, Q8, Q10, Q18, Q27.
          eapply (dec_go_ok_ro (reg_get regs (Z_to_bv 5 1)) (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3)) (reg_get regs (Z_to_bv 5 4)) (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9)) (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20)) (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23)) (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26)) (reg_get regs (Z_to_bv 5 27)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lenp res text tb bs lb _).
          - exact MC.
          - exact HB.
          - lia.
          - exact NZ.
          - exact BOK.
          - lia.
          - exact TX0.
          - lia.
          - exact LP8.
          - exact TX2.
          - exact LB2.
          - lia.
          - exact WL2.
          - exact WRB.
          - rewrite Esp. exact FRm2.
          - rewrite Esp. lia.
          - lia.
          - exact QRO.
          - exact RO2.
          - exact DQD.
          - exact DQT.
          - rewrite EM. left. lia.
          - rewrite Esp, EM. left. lia.
          - rewrite Esp. right. lia.
          - rewrite Esp. unfold id in TW. destruct TW as [TW | TW]; lia. }
        { exact Hh2. }
        { exact Hl2. }
        intros ms3 (can & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
          -> & LEN3 & BY3 & MU3 & WM3 & RO3 & ST3) & EQV3).
        destruct (eqv_shape _ _ _ _ EQV3) as (S3 & X3). rewrite S3. clear S3 EQV3.
        remember (ms_regs ms3) as R3 eqn:ER3. clear ER3 ms3.
        rewrite EM in MU3.
        assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (res <= x < res + dec_size tb) -> ~ (lenp <= x < lenp + 8) ->
          (x < sp - 112 \/ sp - 104 <= x) -> m3 (Z_to_bv 64 x) = m2 (Z_to_bv 64 x)).
        { intros x Hx H1 H2 H3. apply (munch_at _ _ _ _ MU3); [exact Hx | apply outside3; lia]. }
        assert (KEEP3 : forall a k i, In (a, k) (blocks L A) -> a <> 0 -> 0 <= i < k ->
          mbyte rsegs m3 (a + i) = mbyte rsegs mem (a + i)).
        { intros a k i Hin1 Ha Hi. destruct (blk_facts B API L A mem md a k HMR Hin1) as (B1 & B2 & _).
          assert (Hy : In (a, k) (b1 ++ b2)) by (rewrite <- EB1; exact Hin1).
          destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a, k) HM2 EB2 Hy) as [D|D];
            cbn [fst snd] in D;
            (transitivity (mbyte rsegs m2 (a + i));
             [apply mbyte_eq_of; apply OUT; lia | exact (KM2 a k i Hin1 Ha Hi)]). }
        assert (DK3 : forall i, 0 <= i <= Z.of_nat (length tb) -> mbyte rsegs m3 (text + i) = mbyte rsegs mem (text + i)).
        { intros i Hi. rewrite <- (DK2 i Hi). apply mbyte_eq_of.
          unfold id in DQD, LPD, TW. destruct DQD as [DQD | DQD]; destruct LPD as [LPD | LPD];
            destruct TW as [TW | TW]; apply OUT; lia. }
        assert (MR3 : aa_MR API L1 A1 m3 md1).
        { apply (MR_keep B API L1 A1 m2 m3 md1 HM2).
          - intros a Ho. pose proof (owned_low B API L1 A1 m2 md1 a HM2 Ho) as Hlo. apply OUT; [lia | | lia | lia].
            intros Hx. destruct (NB3 (a - (res - 16)) ltac:(lia)) as (_ & NO).
            replace (res - 16 + (a - (res - 16))) with a in NO by lia. exact (NO Ho).
          - intros p k i Hp Hi.
            destruct (mr_blocks B _ (aa_laws API) L1 A1 m2 md1 p k i HM2 Hp Hi) as (P & C3 & C4 & _).
            apply (present_of_wr B HSEG); [lia | exact (YL01.ax_blocks_img AX L1 A1 m2 md1 p k i HM2 Hp Hi) |].
            unfold writable_at. apply WM3. exact (wr_of_present _ _ _ P). }
        apply SR_ret. cbv beta.
        exists L1, A1, R3, m3, md1, res.
        split; [rewrite ERA; reflexivity|].
        split; [exact RO3|].
        split.
        { unfold guard_kept. rewrite HSEG. intros i Hi. unfold guard_kept in GK1. rewrite HSEG in GK1.
          pose proof (owned_low B API L A mem md _ HMR (got_owned B L A i Hi)) as Hg.
          transitivity (mbyte rsegs m2 (ms_got_guard B + i)).
          - apply mbyte_eq_of. apply OUT; [lia | | lia | lia]. intros Hx.
            destruct (NB3 (ms_got_guard B + i - (res - 16)) ltac:(lia)) as (_ & NO). apply NO.
            replace (res - 16 + (ms_got_guard B + i - (res - 16))) with (ms_got_guard B + i) by lia.
            apply got_owned. exact Hi.
          - rewrite (GK1 i Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
        split; [exact INIT1|].
        split.
        { unfold call_post_k. rewrite HSEG.
          split; [exact MR3|]. split; [exact HWF2|]. split; [exact HBD2|]. split; [exact HLL1|]. split; [exact HPA1|].
          split; [exact (rp_of_eqv regs R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3)|].
          split; [exact HMD1|].
          split.
          { intros a Hr Ho1 Ho2 Hsc Hw.
            assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (img_bound B HSEG a Hr); lia]).
            assert (Hq : ~ (res <= a < res + dec_size tb)) by (destruct Hr as [Hr|Hr]; [lia | intros Hx; exact (NI a Hx Hr)]).
            unfold scratch_k, DEC_STACK, ALLOC_STACK in Hsc.
            apply (chain3 mem m1 m2 m3 a).
            - apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
            - apply FR2; [exact Hr | exact Ho1 | exact Ho2 | unfold scratch_k; rewrite S1; unfold ALLOC_STACK; lia |].
              unfold alloc_writes. intros [Hx | (Hx1 & Hx2)]; apply Hw; [left; exact Hx | right; left; split; [exact Hx1 | lia]].
            - apply OUT; [lia | exact Hq | intros Hx; apply Hw; right; right; exact Hx | lia]. }
          split.
          { intros p k i Hp Hp2 Hi.
            destruct (blk_facts B API L A mem md _ _ HMR (blk_of_user L A p k Hp)) as (B1 & _).
            apply (KEEP3 _ k); [apply blk_of_user; exact Hp | lia | exact Hi]. }
          intros a Hs. unfold scratch_k, DEC_STACK, ALLOC_STACK in Hs. unfold writable_at. apply WM3.
          destruct Hs as [Hs|Hs].
          - exact (WR2 a ltac:(lia)).
          - exact (SC2 a (or_intror Hs)). }
        split; [exact LEN1|].
        split; [unfold keeps; rewrite HSEG; intros a k i Hin1 Ha Hi; exact (KEEP3 a k i Hin1 Ha Hi)|].
        split; [exact DK3|].
        right. right. exists bs.
        split; [exact NC|]. split; [reflexivity|]. split; [exact RNZ|].
        split; [exact (eqv_getr _ _ 10 _ X3 ltac:(lia) eq_refl)|].
        split; [exact RAL|]. split; [exact NIN|]. split; [exact NST|]. split; [exact NIMG|].
        split; [exists b1, b2; split; [exact EB2 | exact EB1]|].
        split; [exact UBK1|].
        split.
        { apply (ledger_keep B L1 A1 m2 m3 _ _ _ _ LED2).
          - intros a Hs. apply mbyte_eq_of.
            assert (Hsb : 0 <= a < 0x33b58) by (unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs; lia).
            apply OUT; [lia | | lia | lia]. intros Hx. apply (NST (a - (res - 16))); [lia|].
            replace (res - 16 + (a - (res - 16))) with a by lia. exact Hs.
          - intros a k i Hk Hin1 Hi.
            destruct (blk_facts B API L1 A1 m2 md1 _ _ HM2 Hin1) as (C1 & C2 & _).
            rewrite EB2 in Hin1. apply in_app_or in Hin1.
            assert (D : a - 16 = res - 16 \/ res + dec_size tb <= a - 16 \/ a + k <= res - 16).
            { destruct Hin1 as [Hin1 | [Ex | Hin1]].
              - destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a - 16, k + 16) HM2 EB2
                  ltac:(apply in_or_app; left; exact Hin1)) as [D|D]; cbn [fst snd] in D; right; lia.
              - injection Ex as Ex1 _. left. lia.
              - destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a - 16, k + 16) HM2 EB2
                  ltac:(apply in_or_app; right; exact Hin1)) as [D|D]; cbn [fst snd] in D; right; lia. }
            apply mbyte_eq_of. apply OUT; lia. }
        split; [exact BY3|]. split; [exact LEN3|]. exact SLOT1.
      * eapply (evt_SR_canon rsegs _ _ md1 _).
        { change (RegisterBridge.canonical_register_state
                    (@YK11.mkst fx R2 (Z_to_bv 64 0x15468) m2 (YK11.seg_rom rsegs)))
            with (MS (mkR_of R2) (@fp_regs fx) (Z_to_bv 64 0x15468) (@fp_csr fx) None m2 (seg_rom rsegs)).
          rewrite mkR_of_eq, Q2, Q3, Q4, Q8, Q10, Q18, Q27.
          eapply (dec_go_fail_ro (reg_get regs (Z_to_bv 5 1)) (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3)) (reg_get regs (Z_to_bv 5 4)) (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9)) (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20)) (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23)) (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26)) (reg_get regs (Z_to_bv 5 27)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lenp res text tb lb _).
          - exact MC.
          - exact HB.
          - lia.
          - exact NZ.
          - exact BOK.
          - lia.
          - exact TX0.
          - lia.
          - exact LP8.
          - exact TX2.
          - exact LB2.
          - lia.
          - exact WL2.
          - exact WRB.
          - rewrite Esp. exact FRm2.
          - rewrite Esp. lia.
          - lia.
          - exact QRO.
          - exact RO2.
          - exact DQD.
          - exact DQT.
          - rewrite EM. left. lia.
          - rewrite Esp, EM. left. lia.
          - rewrite Esp. right. lia.
          - rewrite Esp. unfold id in TW. destruct TW as [TW | TW]; lia. }
        { exact Hh2. }
        { exact Hl2. }
        intros ms3 (can & (u0' & u1' & u2' & y8 & c1' & c2' & c3' & c4' & c5' & c6' & c7' & y18 & y19 & y20 & y21 & y22 &
          y23 & y24 & y25 & y26 & y27 & u3' & u4' & u5' & u6' & m3 & -> & L3 & FR3 & MU3 & WM3 & RO3) & EQV3).
        destruct (eqv_shape _ _ _ _ EQV3) as (S3' & X3). rewrite S3'. clear S3' EQV3.
        remember (ms_regs ms3) as R3 eqn:ER3. clear ER3 ms3.
        rewrite Esp in FR3. rewrite EM in MU3.
        assert (G31 : YK11.getr R3 1 = Z_to_bv 64 0x1554c) by exact (eqv_getr _ _ 1 _ X3 ltac:(lia) eq_refl).
        assert (G32 : YK11.getr R3 2 = Z_to_bv 64 (sp - 112)).
        { apply (eqv_getr _ _ 2 _ X3 ltac:(lia)).
          change (Z_to_bv 64 (bv_unsigned (reg_get regs (Z_to_bv 5 2)) - 112) = Z_to_bv 64 (sp - 112)).
          rewrite Esp. reflexivity. }
        assert (G34 : YK11.getr R3 4 = YK11.getr regs 4).
        { apply (eqv_getr _ _ 4 _ X3 ltac:(lia)). rewrite getr_reg by (vm_compute; discriminate). reflexivity. }
        assert (G310 : YK11.getr R3 10 = Z_to_bv 64 res) by exact (eqv_getr _ _ 10 _ X3 ltac:(lia) eq_refl).
        assert (S3 : spZ R3 = sp - 112) by (unfold spZ; rewrite G32, unsigned_lit by lia; reflexivity).
        assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (res <= x < res + dec_size tb) ->
          (x < sp - 112 \/ sp - 104 <= x) -> m3 (Z_to_bv 64 x) = m2 (Z_to_bv 64 x)).
        { intros x Hx H1 H2. apply (munch_at _ _ _ _ MU3); [exact Hx | apply outside2; lia]. }
        assert (MR3 : aa_MR API L1 A1 m3 md1).
        { apply (MR_keep B API L1 A1 m2 m3 md1 HM2).
          - intros a Ho. pose proof (owned_low B API L1 A1 m2 md1 a HM2 Ho) as Hlo. apply OUT; [lia | | lia].
            intros Hx. destruct (NB3 (a - (res - 16)) ltac:(lia)) as (_ & NO).
            replace (res - 16 + (a - (res - 16))) with a in NO by lia. exact (NO Ho).
          - intros p k i Hp Hi.
            destruct (mr_blocks B _ (aa_laws API) L1 A1 m2 md1 p k i HM2 Hp Hi) as (P & C3 & C4 & _).
            apply (present_of_wr B HSEG); [lia | exact (YL01.ax_blocks_img AX L1 A1 m2 md1 p k i HM2 Hp Hi) |].
            unfold writable_at. apply WM3. exact (wr_of_present _ _ _ P). }
        assert (LED3 : ledger B L1 A1 m3 ((res, dec_size tb) :: Lam) (Z.max peak (lsum Lam + dec_size tb))
          ((cnt + 1) mod 2 ^ 64) fail).
        { apply (ledger_keep B L1 A1 m2 m3 _ _ _ _ LED2).
          - intros a Hs. apply mbyte_eq_of.
            assert (Hsb : 0 <= a < 0x33b58) by (unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs; lia).
            apply OUT; [lia | | lia]. intros Hx. apply (NST (a - (res - 16))); [lia|].
            replace (res - 16 + (a - (res - 16))) with a by lia. exact Hs.
          - intros a k i Hk Hin1 Hi.
            destruct (blk_facts B API L1 A1 m2 md1 _ _ HM2 Hin1) as (C1 & C2 & _).
            rewrite EB2 in Hin1. apply in_app_or in Hin1.
            assert (D : a - 16 = res - 16 \/ res + dec_size tb <= a - 16 \/ a + k <= res - 16).
            { destruct Hin1 as [Hin1 | [Ex | Hin1]].
              - destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a - 16, k + 16) HM2 EB2
                  ltac:(apply in_or_app; left; exact Hin1)) as [D|D]; cbn [fst snd] in D; right; lia.
              - injection Ex as Ex1 _. left. lia.
              - destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a - 16, k + 16) HM2 EB2
                  ltac:(apply in_or_app; right; exact Hin1)) as [D|D]; cbn [fst snd] in D; right; lia. }
            apply mbyte_eq_of. apply OUT; lia. }
        assert (INIT1' : st_init_done A1 = true).
        { destruct (blk_user L1 A1 _ _ Hin) as (p0 & Hp0 & _). eapply YI04.init_done_of_block; [exact HWF2 | exact Hp0]. }
        pose proof (FF L1 A1 R3 m3 md1 res (dec_size tb) (rf_malloc RF b (dec_size tb + 16)) ((res, dec_size tb) :: Lam)
          (Z.max peak (lsum Lam + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail) as FF1.
        rewrite HSEG in FF1.
        eapply SR_bind; [apply FF1; clear FF1 | clear FF1].
        -- unfold call_pre_k. rewrite S3, G31, G34, HSEG.
           split; [exact MR3|]. split; [exact HWF2|]. split; [exact HBD2|].
           split; [apply ret_ok_even; vm_compute; reflexivity|].
           split; [unfold id in HAL; Z.div_mod_to_equations; lia|].
           split; [unfold ALLOC_STACK; lia|]. split; [lia|].
           split; [intros a Ha; unfold writable_at; apply WM3; exact (WR2 a ltac:(unfold ALLOC_STACK in Ha; lia))|].
           split; [exact HTP|].
           split; [intros a Ha; unfold writable_at; apply WM3; exact (SC2 a (or_intror Ha))|].
           intros Hf. rewrite INIT1' in Hf. discriminate.
        -- exact G310.
        -- exact LED3.
        -- exact RO3.
        -- right. left. reflexivity.
        -- exact SLOT1.
        -- intros c4 (L2 & A2 & R4 & m4 & md2 & -> & RO4 & GK2 & INIT2 & LI2 & CP2 & LEN2 & KEEP2 & UBK2 & ARMS2).
           destruct ARMS2 as [(P0 & _) | (_ & (c1 & c2 & EC1 & EC2) & (l1 & l2 & EL & LED4) & SLOT2)];
             [exfalso; exact (RNZ P0)|].
           pose proof CP2 as (HM4 & HWF4 & HBD4 & HLL2 & HPA2 & RP2 & HMD2 & FR4 & BK4 & SC4).
           rewrite HSEG in FR4, SC4.
           unfold keeps in KEEP2. rewrite HSEG in KEEP2.
           destruct (mr_model B _ (aa_laws API) _ _ _ _ HM4) as (Hh4 & Hl4 & _).
           rewrite G31.
           assert (HI4 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - 8304 <= a < sp - 112) ->
             mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
           { intros a Ha Hs. apply FR4.
             - left. exact Ha.
             - intros Ho. pose proof (owned_low B API L1 A1 m3 md1 a MR3 Ho). lia.
             - intros Ho. pose proof (owned_low B API L2 A2 m4 md2 a HM4 Ho). lia.
             - unfold scratch_k. rewrite S3. unfold ALLOC_STACK. lia.
             - unfold free_writes, G_LIVE. lia. }
           lazymatch type of FR3 with rw_cells _ _ _ ?cs =>
             assert (FRm4 : rw_cells rsegs m4 (sp - 112) cs) end.
           { apply (rw_cells_keep m3 m4 _ _ FR3). intros i Hi. cbn in Hi.
             destruct (HI4 (sp - 112 + i) ltac:(lia) ltac:(lia)) as [E1 E2]. split; [exact E1 | exact (proj1 E2)]. }
           assert (Q'2 : reg_get R4 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (reg_get regs (Z_to_bv 5 2)) - 112))
             by qr RP2 X3 2.
           assert (Q'3 : reg_get R4 (Z_to_bv 5 3) = reg_get regs (Z_to_bv 5 3)) by qr RP2 X3 3.
           assert (Q'4 : reg_get R4 (Z_to_bv 5 4) = reg_get regs (Z_to_bv 5 4)) by qr RP2 X3 4.
           assert (FRAME4 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ owned B L2 A2 a -> ~ (sp - 8336 <= a < sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ alloc_statics a -> ~ (res - 16 <= a < res + dec_size tb) ->
             mbyte rsegs m4 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m4 a)).
           { intros a Hr Ho1 Ho2 Hs He Hst Hq.
             assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (img_bound B HSEG a Hr); lia]).
             assert (Ho1' : ~ owned B L1 A1 a) by exact (own_mid B API AX CO L A mem md L1 A1 m2 md1 a HMR HM2 Hr Ho1).
             apply (chain5 mem m1 m2 m3 m4 a).
             - apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
             - apply FR2; [exact Hr | exact Ho1 | exact Ho1' | unfold scratch_k; rewrite S1; unfold ALLOC_STACK; lia |].
               unfold alloc_writes. intros [Hx | (_ & Hx)]; [exact (Hst Hx) | lia].
             - apply OUT; lia.
             - apply FR4; [exact Hr | exact Ho1' | exact Ho2 | unfold scratch_k; rewrite S3; unfold ALLOC_STACK; lia |].
               unfold free_writes. intros [Hx | (_ & Hx)]; [apply Hst; unfold alloc_statics; left; exact Hx | lia]. }
           assert (KEEP4 : forall a k i, In (a, k) (blocks L A) -> a <> 0 -> 0 <= i < k ->
             mbyte rsegs m4 (a + i) = mbyte rsegs mem (a + i)).
           { intros a k i Hin1 Ha Hi. destruct (blk_facts B API L A mem md a k HMR Hin1) as (B1 & B2 & _).
             assert (Hy : In (a, k) (b1 ++ b2)) by (rewrite <- EB1; exact Hin1).
             assert (Hy1 : In (a, k) (blocks L1 A1)).
             { rewrite EB2. apply in_app_or in Hy. apply in_or_app.
               destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy]. }
             destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 (a, k) HM2 EB2 Hy) as [D|D];
               cbn [fst snd] in D;
               (rewrite (KEEP2 a k i Hy1 ltac:(lia) Hi);
                transitivity (mbyte rsegs m2 (a + i));
                [apply mbyte_eq_of; apply OUT; lia | exact (KM2 a k i Hin1 Ha Hi)]). }
           eapply (evt_SR_canon rsegs _ _ md2 _).
           { change (RegisterBridge.canonical_register_state
                       (@YK11.mkst fx R4 (Z_to_bv 64 0x1554c) m4 (YK11.seg_rom rsegs)))
               with (MS (mkR_of R4) (@fp_regs fx) (Z_to_bv 64 0x1554c) (@fp_csr fx) None m4 (seg_rom rsegs)).
             rewrite mkR_of_eq, Q'2, Q'3, Q'4.
             eapply (dec_after_free (reg_get regs (Z_to_bv 5 1)) (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3)) (reg_get regs (Z_to_bv 5 4)) (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9)) (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20)) (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23)) (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26)) (reg_get regs (Z_to_bv 5 27)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4); [rewrite Esp; exact FRm4 | rewrite Esp; lia]. }
           { exact Hh4. }
           { exact Hl4. }
           intros ms5 (can & -> & EQV5).
           destruct (eqv_shape _ _ _ _ EQV5) as (S5 & X5). rewrite S5. clear S5 EQV5.
           remember (ms_regs ms5) as R5 eqn:ER5. clear ER5 ms5.
           apply SR_ret. cbv beta.
           exists L2, A2, R5, m4, md2, res.
           split; [rewrite ERA; reflexivity|].
           split; [exact RO4|].
           split.
           { unfold guard_kept. rewrite HSEG. intros i Hi. unfold guard_kept in GK1, GK2. rewrite HSEG in GK1, GK2.
             pose proof (owned_low B API L A mem md _ HMR (got_owned B L A i Hi)) as Hg.
             rewrite (GK2 i Hi).
             transitivity (mbyte rsegs m2 (ms_got_guard B + i)).
             - apply mbyte_eq_of. apply OUT; [lia | | lia]. intros Hx.
               destruct (NB3 (ms_got_guard B + i - (res - 16)) ltac:(lia)) as (_ & NO). apply NO.
               replace (res - 16 + (ms_got_guard B + i - (res - 16))) with (ms_got_guard B + i) by lia.
               apply got_owned. exact Hi.
             - rewrite (GK1 i Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
           split; [intros Hi0; apply INIT2; apply INIT1; exact Hi0|].
           split.
           { unfold call_post_k. rewrite HSEG.
             split; [exact HM4|]. split; [exact HWF4|]. split; [exact HBD4|].
             split; [exact (layout_le_trans A A1 L L1 L2 HLL1 HLL2 LEN1)|].
             split.
             { intros p k Hp Hp2.
               assert (Hp1 : In (p, k) (user_blocks A1)).
               { apply (UBK1 p k Hp). intros E. injection E as E1 _.
                 destruct (blk_facts B API L A mem md _ _ HMR (blk_of_user L A p k Hp)) as (B1 & _). lia. }
               rewrite (HPA2 p k Hp1 Hp2). exact (HPA1 p k Hp Hp1). }
             split; [exact (rp_of_eqv regs R5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5)|].
             split; [destruct HMD1 as (vm1 & ->); destruct HMD2 as (vm2 & ->); exists vm2; reflexivity|].
             split.
             { intros a Hr Ho1 Ho2 Hsc Hw. unfold scratch_k, DEC_STACK, ALLOC_STACK in Hsc.
               apply FRAME4; [exact Hr | exact Ho1 | exact Ho2 | intros Hx; apply Hsc; left; lia |
                 intros Hx; apply Hsc; right; exact Hx | intros Hx; apply Hw; left; exact Hx |
                 intros Hx; apply Hw; right; left; split; [exact RNZ | lia]]. }
             split.
             { intros p k i Hp Hp2 Hi.
               destruct (blk_facts B API L A mem md _ _ HMR (blk_of_user L A p k Hp)) as (B1 & _).
               apply (KEEP4 _ k); [apply blk_of_user; exact Hp | lia | exact Hi]. }
             intros a Hs. unfold scratch_k, DEC_STACK, ALLOC_STACK in Hs. destruct Hs as [Hs|Hs].
             - destruct (Z_lt_le_dec a (sp - 8304)) as [D|D]; [|destruct (Z_lt_le_dec a (sp - 112)) as [D'|D']].
               + apply (proj1 (proj2 (HI4 a ltac:(lia) ltac:(lia)))). unfold writable_at. apply WM3. exact (WR2 a ltac:(lia)).
               + apply SC4. unfold scratch_k. rewrite S3. unfold ALLOC_STACK. left. lia.
               + apply (proj1 (proj2 (HI4 a ltac:(lia) ltac:(lia)))). unfold writable_at. apply WM3. exact (WR2 a ltac:(lia)).
             - apply SC4. right. exact Hs. }
           split; [lia|].
           split; [unfold keeps; rewrite HSEG; intros a k i Hin1 Ha Hi; exact (KEEP4 a k i Hin1 Ha Hi)|].
           split.
           { intros i Hi. destruct (DW i Hi) as [(a & k & Hin1 & H1) | [Hro | Hsp]].
             - destruct (blk_facts B API L A mem md a k HMR Hin1) as (B1 & B2 & _).
               replace (text + i) with (a + (text + i - a)) by lia. apply (KEEP4 a k); [exact Hin1 | lia | lia].
             - exact (mbyte_ro mem m4 _ ROm RO4 Hro).
             - apply (FRAME4 (text + i)); [left; lia | intros Ho; pose proof (owned_low B API L A mem md _ HMR Ho); lia |
                 intros Ho; pose proof (owned_low B API L2 A2 m4 md2 _ HM4 Ho); lia | lia | lia |
                 unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | lia]. }
           right. left.
           split; [exact NC|]. split; [reflexivity|]. split; [exact RNZ|]. split; [lia|]. split; [exact NIMG|].
           split; [exact (eqv_getr _ _ 10 _ X5 ltac:(lia) eq_refl)|].
           split.
           { rewrite EC2, EB1. symmetry.
             apply (uniq_mid b1 b2 c1 c2 (res - 16, dec_size tb + 16)); [cbn; lia | |].
             - rewrite <- EB2. exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 m2 md1 HM2).
             - rewrite <- EB2. exact EC1. }
           split.
           { intros p k Hp Hz.
             assert (Hp1 : In (p, k) (user_blocks A1)).
             { apply (UBK1 p k Hp). exact Hz. }
             apply (UBK2 p k Hp1). rewrite (HPA1 p k Hp Hp1). intros E. injection E as E1 E2.
             assert (Hb : In (ptr_addr L p, k) (b1 ++ b2)) by (rewrite <- EB1; apply blk_of_user; exact Hp).
             destruct (blk_disj B API L1 A1 m2 md1 b1 (res - 16, dec_size tb + 16) b2 _ HM2 EB2 Hb) as [D|D];
               cbn [fst snd] in D; lia. }
           split.
           { intros i Hi. apply (FRAME4 (lenp + i)); [left; lia | intros Ho; pose proof (owned_low B API L A mem md _ HMR Ho); lia |
               intros Ho; pose proof (owned_low B API L2 A2 m4 md2 _ HM4 Ho); lia | lia | lia |
               unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | lia]. }
           split; [rewrite (lam_mid Lam l1 l2 res (dec_size tb) NIN EL) in LED4; exact LED4|].
           exact SLOT2.
Qed.

End M.
