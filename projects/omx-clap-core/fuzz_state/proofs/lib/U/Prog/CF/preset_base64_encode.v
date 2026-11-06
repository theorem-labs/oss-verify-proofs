(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 1101 of its 1204 lines of code are new or changed and 636 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/put_string.v, with its module paths and module names changed; 729 of its 819 lines of code are new or changed and 1114 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import fuzz_malloc_c preset_base64_encode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Open Scope Z_scope.
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling (only parsing).

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

Theorem enc_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo data len : Z) (m : word -> option byte),
  0 <= len <= 2^62 ->
  bytes_at rsegs m ENC_KMAGIC (le8 (Z_to_bv 64 ENC_MAGIC)) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ENC_FRAME <= bv_unsigned sp ->
  (ENC_KMAGIC + 8 <= bv_unsigned sp - ENC_FRAME \/ bv_unsigned sp <= ENC_KMAGIC) ->
  evt rsegs (fun ms' => exists junk m',
      ms' = MS (mkR (Z_to_bv 64 0x151f8) (Z_to_bv 64 (bv_unsigned sp - ENC_FRAME)) gp tp t0 t1 t2
                 (Z_to_bv 64 len) (Z_to_bv 64 data) (Z_to_bv 64 (enc_M len)) (Z_to_bv 64 (len + 2)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14064) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - ENC_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      stk rsegs m' lo (bv_unsigned sp - ENC_FRAME) /\
      rw_cells rsegs m' (bv_unsigned sp - ENC_FRAME) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 data) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x151c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo data len m
    HL KM ST LO DK.
  eapply evt_cut; [eapply enc_prologue; eassumption |].
  intros ms' (junk & m' & -> & MU & WM & ST' & FR).
  zstep. apply evt_done. exists junk, m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST'|exact FR].
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma eqv_shape : forall R pc m ms', ms_eqv (MS R (@fp_regs fx) pc (@fp_csr fx) None m (seg_rom rsegs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom rsegs) /\ xregs_eqv R (ms_regs ms').
Proof.
  intros R pc m ms' H. destruct ms'. unfold ms_eqv in H. cbn in H |- *.
  destruct H as (HR & HF & Hp & Hs & Hrv & Hfc & Hm & Hro). subst. split; [reflexivity | exact HR].
Qed.

Lemma table_ro : forallb (fun i => ro_addr rsegs (Z_to_bv 64 (G_B64 + Z.of_nat i))) (seq 0 65) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_ro_at : forall a, G_B64 <= a < G_B64 + 65 -> ro_addr rsegs (Z_to_bv 64 a) = true.
Proof.
  intros a Ha. pose proof table_ro as T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat (a - G_B64)) ltac:(apply in_seq; unfold G_B64 in *; lia)).
  replace (G_B64 + Z.of_nat (Z.to_nat (a - G_B64))) with a in T by lia. exact T.
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

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Theorem preset_base64_encode_holds : fuzz_malloc_contract B API RF -> preset_base64_encode_contract B API RF.
Proof.
  intros FM L A regs mem md data len bs b Lam peak cnt fail HSEG HERR RO PRE R10 R11 HD HDL HB HN HL DATA WHERE LED
    RES ROOM.
  pose proof ceil_val as HC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCE & H63 & HWS & HTP & HER & HAUX).
  unfold ENC_STACK, ALLOC_STACK in HCE, HWS.
  rewrite HSEG in HWS, HER, DATA.
  remember (spZ regs) as sp eqn:Esp0.
  assert (Esp : bv_unsigned (reg_get regs (Z_to_bv 5 2)) = sp).
  { rewrite Esp0. unfold spZ. rewrite getr_reg by (vm_compute; discriminate). reflexivity. }
  assert (E10 : reg_get regs (Z_to_bv 5 10) = Z_to_bv 64 data).
  { rewrite <- getr_reg by (vm_compute; discriminate). exact R10. }
  assert (E11 : reg_get regs (Z_to_bv 5 11) = Z_to_bv 64 len).
  { rewrite <- getr_reg by (vm_compute; discriminate). exact R11. }
  assert (ERA : ret_pc (reg_get regs (Z_to_bv 5 1)) = YK11.getr regs 1).
  { rewrite <- (getr_reg regs (Z_to_bv 5 1)) by (vm_compute; discriminate). apply ret_pc_ok. exact HRA. }
  assert (ROm : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (HM : enc_size len + 16 <= 2 ^ 28) by (unfold enc_size; Z.div_mod_to_equations; lia).
  assert (Hlen : 0 <= len) by lia.
  assert (HS1 : 1 <= enc_size len) by (unfold enc_size; Z.div_mod_to_equations; lia).
  assert (EM : enc_M len = enc_size len) by reflexivity.
  assert (DW : forall i, 0 <= i < len ->
    (exists a k, In (a, k) (blocks L A) /\ a <= data + i < a + k) \/
    ro_addr rsegs (Z_to_bv 64 (data + i)) = true \/ sp <= data + i).
  { intros i Hi. unfold enc_data_where in WHERE. rewrite HSEG in WHERE.
    destruct WHERE as [E0 | [(a & k & Hin & H1 & H2) | [Hro | Hsp]]].
    - lia.
    - left. exists a, k. split; [exact Hin | lia].
    - right. left. exact (Hro i Hi).
    - right. right. lia. }
  assert (HDZ : 0 < len -> data <> 0).
  { intros Hp. destruct (DW 0 ltac:(lia)) as [(a & k & Hin & H1) | [Hro | Hsp]].
    - destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & _). lia.
    - rewrite Z.add_0_r in Hro. pose proof (ro_pos data HD Hro). lia.
    - lia. }
  rewrite HSEG.
  eapply (evt_SR_canon rsegs _ _ md _).
  { change (RegisterBridge.canonical_register_state
              (@YK11.mkst fx regs (Z_to_bv 64 PRESET_BASE64_ENCODE) mem (YK11.seg_rom rsegs)))
      with (MS (mkR_of regs) (@fp_regs fx) (Z_to_bv 64 0x151c0) (@fp_csr fx) None mem (seg_rom rsegs)).
    rewrite mkR_of_eq, E10, E11.
    eapply (enc_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - 8256) data len).
    - lia.
    - apply ro_image; [exact ROm | exact enc_magic_image].
    - rewrite Esp. apply stk_of_writable; [lia | lia |]. intros a Ha. apply HWS. lia.
    - rewrite Esp. unfold ENC_FRAME. lia.
    - left. rewrite Esp. unfold ENC_KMAGIC, ENC_FRAME. lia. }
  { exact Hh. }
  { exact Hl. }
  intros ms1 (c1 & (junk & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQV1).
  destruct (eqv_shape _ _ _ _ EQV1) as (S1' & X1). rewrite S1'. clear S1' EQV1.
  remember (ms_regs ms1) as R1 eqn:ER1. clear ER1 ms1.
  rewrite Esp in MU1, ST1, FR1. unfold ENC_FRAME in MU1, ST1, FR1.
  assert (G1 : YK11.getr R1 1 = Z_to_bv 64 0x151f8) by exact (eqv_getr _ _ 1 _ X1 ltac:(lia) eq_refl).
  assert (G2 : YK11.getr R1 2 = Z_to_bv 64 (sp - 32)).
  { apply (eqv_getr _ _ 2 _ X1 ltac:(lia)).
    change (Z_to_bv 64 (bv_unsigned (reg_get regs (Z_to_bv 5 2)) - ENC_FRAME) = Z_to_bv 64 (sp - 32)).
    rewrite Esp. reflexivity. }
  assert (G4 : YK11.getr R1 4 = YK11.getr regs 4).
  { apply (eqv_getr _ _ 4 _ X1 ltac:(lia)). rewrite getr_reg by (vm_compute; discriminate). reflexivity. }
  assert (G10 : YK11.getr R1 10 = Z_to_bv 64 (enc_size len)) by exact (eqv_getr _ _ 10 _ X1 ltac:(lia) eq_refl).
  assert (S1 : spZ R1 = sp - 32) by (unfold spZ; rewrite G2, unsigned_lit by lia; reflexivity).
  assert (HM1 : aa_MR API L A m1 md) by (apply (MR_high B API L A mem m1 md (sp - 32) sp HMR MU1); lia).
  assert (LED1 : ledger B L A m1 Lam peak cnt fail)
    by (apply (ledger_high B API L A mem m1 md Lam peak cnt fail (sp - 32) sp HMR LED MU1); lia).
  assert (RO1 : ro_agree rsegs m1) by (apply (ro_high mem m1 (sp - 32) sp ROm MU1); lia).
  pose proof (FM L A R1 m1 md (enc_size len) b Lam peak cnt fail) as FM1.
  rewrite HSEG in FM1.
  eapply SR_bind; [apply FM1; clear FM1 | clear FM1].
  - unfold call_pre_k. rewrite S1, G1, G4, HSEG.
    split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [apply ret_ok_even; vm_compute; reflexivity|].
    split; [Z.div_mod_to_equations; lia|].
    split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a Ha; unfold writable_at; apply WM1; apply HWS; unfold ALLOC_STACK in Ha; lia|].
    split; [exact HTP|].
    split; [intros a Ha; unfold writable_at; apply WM1; apply HER; exact Ha|].
    intros Hf. apply (auxv_high B API L A mem m1 md (ly_sec L) sp (sp - 32) sp HMR (HAUX Hf) MU1); lia.
  - exact G10.
  - lia.
  - exact LED1.
  - exact RO1.
  - exact RES.
  - exact ROOM.
  - lia.
  - intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & RO2 & GK2 & INIT2 & LB8 & CP2 & LEN2 & R2a & KEEP2
      & UBK2 & ARMS).
    pose proof CP2 as (HM2 & HWF2 & HBD2 & HLL2 & HPA2 & RP2 & HMD2 & FR2 & BK2 & SC2).
    rewrite HSEG in FR2, SC2.
    unfold keeps in KEEP2. rewrite HSEG in KEEP2.
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    rewrite G1.
    assert (RRES : res = 0 \/ (4096 <= res - 16 /\ res + enc_size len <= alloc_ceiling)).
    { destruct ARMS as [(_ & -> & _) | (_ & _ & _ & _ & _ & _ & _ & (b1 & b2 & EB2 & _) & _)]; [left; reflexivity | right].
      assert (Hin : In (res - 16, enc_size len + 16) (blocks L2 A2))
        by (rewrite EB2; apply in_or_app; right; left; reflexivity).
      destruct (blk_facts B API L2 A2 mem2 md2 _ _ HM2 Hin) as (H1 & H2 & _). lia. }
    assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - 8256 <= a < sp - 32) ->
      mbyte rsegs mem2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs mem2 a)).
    { intros a Ha Hs. apply FR2.
      - left. exact Ha.
      - intros Ho. pose proof (owned_low B API L A m1 md a HM1 Ho). lia.
      - intros Ho. pose proof (owned_low B API L2 A2 mem2 md2 a HM2 Ho). lia.
      - unfold scratch_k. rewrite S1. unfold ALLOC_STACK. lia.
      - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
    assert (WR2 : forall a, sp - 8256 <= a < sp -> writable_at rsegs mem2 a).
    { intros a Ha. destruct (Z_lt_le_dec a (sp - 32)) as [H1|H1].
      - apply SC2. unfold scratch_k. left. rewrite S1. unfold ALLOC_STACK. lia.
      - apply (proj1 (proj2 (HI2 a ltac:(lia) ltac:(lia)))). unfold writable_at. apply WM1. apply HWS. lia. }
    assert (STm2 : stk rsegs mem2 (sp - 8256) (sp - 32))
      by (apply stk_of_writable; [lia | lia | intros a Ha; apply WR2; lia]).
    lazymatch type of FR1 with rw_cells _ _ _ ?cs =>
      assert (FRm2 : rw_cells rsegs mem2 (sp - 32) cs) end.
    { apply (rw_cells_keep m1 mem2 _ _ FR1). intros i Hi. cbn in Hi.
      destruct (HI2 (sp - 32 + i) ltac:(lia) ltac:(lia)) as [E1 E2]. split; [exact E1 | exact (proj1 E2)]. }
    assert (DK2 : forall i, 0 <= i < len -> mbyte rsegs mem2 (data + i) = mbyte rsegs mem (data + i)).
    { intros i Hi. destruct (DW i Hi) as [(a & k & Hin & H1) | [Hro | Hsp]].
      - destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & B2 & _).
        replace (data + i) with (a + (data + i - a)) by lia.
        rewrite (KEEP2 a k (data + i - a) Hin ltac:(lia) ltac:(lia)).
        apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
      - exact (mbyte_ro mem mem2 _ ROm RO2 Hro).
      - rewrite (proj1 (HI2 (data + i) ltac:(lia) ltac:(lia))).
        apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
    assert (Q2 : reg_get regs2 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (reg_get regs (Z_to_bv 5 2)) - ENC_FRAME))
      by qr RP2 X1 2.
    assert (Q3 : reg_get regs2 (Z_to_bv 5 3) = reg_get regs (Z_to_bv 5 3)) by qr RP2 X1 3.
    assert (Q4 : reg_get regs2 (Z_to_bv 5 4) = reg_get regs (Z_to_bv 5 4)) by qr RP2 X1 4.
    assert (Q8 : reg_get regs2 (Z_to_bv 5 8) = Z_to_bv 64 len) by qr RP2 X1 8.
    assert (Q9 : reg_get regs2 (Z_to_bv 5 9) = Z_to_bv 64 data) by qr RP2 X1 9.
    assert (Q18 : reg_get regs2 (Z_to_bv 5 18) = reg_get regs (Z_to_bv 5 18)) by qr RP2 X1 18.
    assert (Q19 : reg_get regs2 (Z_to_bv 5 19) = reg_get regs (Z_to_bv 5 19)) by qr RP2 X1 19.
    assert (Q20 : reg_get regs2 (Z_to_bv 5 20) = reg_get regs (Z_to_bv 5 20)) by qr RP2 X1 20.
    assert (Q21 : reg_get regs2 (Z_to_bv 5 21) = reg_get regs (Z_to_bv 5 21)) by qr RP2 X1 21.
    assert (Q22 : reg_get regs2 (Z_to_bv 5 22) = reg_get regs (Z_to_bv 5 22)) by qr RP2 X1 22.
    assert (Q23 : reg_get regs2 (Z_to_bv 5 23) = reg_get regs (Z_to_bv 5 23)) by qr RP2 X1 23.
    assert (Q24 : reg_get regs2 (Z_to_bv 5 24) = reg_get regs (Z_to_bv 5 24)) by qr RP2 X1 24.
    assert (Q25 : reg_get regs2 (Z_to_bv 5 25) = reg_get regs (Z_to_bv 5 25)) by qr RP2 X1 25.
    assert (Q26 : reg_get regs2 (Z_to_bv 5 26) = reg_get regs (Z_to_bv 5 26)) by qr RP2 X1 26.
    assert (Q27 : reg_get regs2 (Z_to_bv 5 27) = reg_get regs (Z_to_bv 5 27)) by qr RP2 X1 27.
    assert (Q10 : reg_get regs2 (Z_to_bv 5 10) = Z_to_bv 64 res).
    { rewrite <- getr_reg by (vm_compute; discriminate). exact R2a. }
    change (RegisterBridge.canonical_register_state
              (@YK11.mkst fx regs2 (Z_to_bv 64 0x151f8) mem2 (YK11.seg_rom rsegs)))
      with (MS (mkR_of regs2) (@fp_regs fx) (Z_to_bv 64 0x151f8) (@fp_csr fx) None mem2 (seg_rom rsegs)).
    destruct ARMS as [(EC & ER & EL2 & EA2 & Emd2 & RSb2 & WO2 & EBL & LED2)
                     | (NC & RNZ & RAL & SLOT2 & NST & NIMG & NIN & (b1 & b2 & EB2 & EB1) & LED2)].
    + subst res.
      eapply (evt_SR_canon rsegs _ _ md2 _).
      { change (RegisterBridge.canonical_register_state
                  (@YK11.mkst fx regs2 (Z_to_bv 64 0x151f8) mem2 (YK11.seg_rom rsegs)))
          with (MS (mkR_of regs2) (@fp_regs fx) (Z_to_bv 64 0x151f8) (@fp_csr fx) None mem2 (seg_rom rsegs)).
        rewrite mkR_of_eq, Q2, Q3, Q4, Q8, Q9, Q10, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
        eapply (enc_body_null (reg_get regs (Z_to_bv 5 1)) (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3))
                  (reg_get regs (Z_to_bv 5 4)) (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9))
                  _ _ _ _ _ _ _ _ _ _ _ _ _
                  (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20))
                  (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23))
                  (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26))
                  (reg_get regs (Z_to_bv 5 27)) _ _ _ _ _ _ (sp - 8256) junk mem2).
        - rewrite Esp. unfold ENC_FRAME. exact FRm2.
        - rewrite Esp. unfold ENC_FRAME. exact STm2.
        - rewrite Esp. unfold ENC_FRAME. lia. }
      { exact Hh2. }
      { exact Hl2. }
      intros ms3 (can & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
        -> & MU3 & WM3 & ST3 & _) & EQV3).
      destruct (eqv_shape _ _ _ _ EQV3) as (S3 & X3). rewrite S3. clear S3 EQV3.
      remember (ms_regs ms3) as R3 eqn:ER3. clear ER3 ms3.
      rewrite Esp in MU3, ST3. unfold ENC_FRAME in MU3.
      assert (RO3 : ro_agree rsegs m3) by (apply (ro_high mem2 m3 (sp - 32) sp RO2 MU3); lia).
      assert (KEEP3 : forall a k i, In (a, k) (blocks L A) -> a <> 0 -> 0 <= i < k ->
        mbyte rsegs m3 (a + i) = mbyte rsegs mem (a + i)).
      { intros a k i Hin Ha Hi. destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & B2 & _).
        transitivity (mbyte rsegs mem2 (a + i)).
        { apply mbyte_eq_of. apply (munch_at _ _ _ _ MU3); [lia | apply outside1; lia]. }
        rewrite (KEEP2 a k i Hin Ha Hi).
        apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
      assert (DK3 : forall i, 0 <= i < len -> mbyte rsegs m3 (data + i) = mbyte rsegs mem (data + i)).
      { intros i Hi. destruct (DW i Hi) as [(a & k & Hin & H1) | [Hro | Hsp]].
        - destruct (blk_facts B API L A mem md a k HMR Hin) as (B1 & B2 & _).
          replace (data + i) with (a + (data + i - a)) by lia. apply (KEEP3 a k); [exact Hin | lia | lia].
        - exact (mbyte_ro mem m3 _ ROm RO3 Hro).
        - rewrite <- (DK2 i Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU3); [lia | apply outside1; lia]. }
      apply SR_ret. cbv beta.
      exists L2, A2, R3, m3, md2, 0.
      split; [rewrite ERA; reflexivity|].
      split; [exact RO3|].
      split.
      { unfold guard_kept. rewrite HSEG. intros i Hi. unfold guard_kept in GK2. rewrite HSEG in GK2.
        pose proof (owned_low B API L A mem md _ HMR (got_owned B L A i Hi)) as Hg.
        transitivity (mbyte rsegs mem2 (ms_got_guard B + i)).
        - apply mbyte_eq_of. apply (munch_at _ _ _ _ MU3); [lia | apply outside1; lia].
        - rewrite (GK2 i Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
      split; [exact INIT2|].
      split.
      { unfold call_post_k. rewrite HSEG.
        split; [apply (MR_high B API L2 A2 mem2 m3 md2 (sp - 32) sp HM2 MU3); lia|].
        split; [exact HWF2|]. split; [exact HBD2|]. split; [exact HLL2|]. split; [exact HPA2|].
        split; [exact (rp_of_eqv regs R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3)|].
        split; [exact HMD2|].
        split.
        { intros a Hr Ho1 Ho2 Hsc Hw.
          assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (img_bound B HSEG a Hr); lia]).
          unfold scratch_k, ENC_STACK, ALLOC_STACK in Hsc.
          apply (chain3 mem m1 mem2 m3 a).
          - apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
          - apply FR2; [exact Hr | exact Ho1 | exact Ho2 | unfold scratch_k; rewrite S1; unfold ALLOC_STACK; lia |].
            intros Hx. apply Hw. left. exact Hx.
          - apply (munch_at _ _ _ _ MU3); [lia | apply outside1; lia]. }
        split.
        { intros p k i Hp Hp2 Hi.
          destruct (blk_facts B API L A mem md _ _ HMR (blk_of_user L A p k Hp)) as (B1 & _).
          apply (KEEP3 _ k); [apply blk_of_user; exact Hp | lia | exact Hi]. }
        intros a Hs. unfold scratch_k, ENC_STACK, ALLOC_STACK in Hs. destruct Hs as [Hs|Hs].
        - destruct ST3 as (_ & _ & STK). exact (proj1 (STK a ltac:(lia))).
        - exact (WM3 _ (SC2 a (or_intror Hs))). }
      split; [exact LEN2|].
      split; [exact (eqv_getr _ _ 10 _ X3 ltac:(lia) eq_refl)|].
      split; [unfold keeps; rewrite HSEG; intros a k i Hin Ha Hi; exact (KEEP3 a k i Hin Ha Hi)|].
      split; [exact UBK2|].
      split; [exact DK3|].
      left. split; [exact EC|]. split; [reflexivity|]. split; [exact RSb2|]. split; [exact EBL|].
      apply (ledger_high B API L2 A2 mem2 m3 md2 Lam peak _ _ (sp - 32) sp HM2 LED2 MU3). lia.
    + assert (Hin : In (res - 16, enc_size len + 16) (blocks L2 A2))
        by (rewrite EB2; apply in_or_app; right; left; reflexivity).
      destruct (blk_facts B API L2 A2 mem2 md2 _ _ HM2 Hin) as (NB1 & NB2 & NB3).
      assert (WRB : wr_at rsegs mem2 res (enc_M len)).
      { rewrite EM. split; [lia|]. split; [lia|]. intros i Hi.
        destruct (NB3 (i + 16) ltac:(lia)) as (P & _).
        replace (res - 16 + (i + 16)) with (res + i) in P by lia.
        exact (wr_of_present _ _ _ P). }
      assert (NI : forall x, res <= x < res + enc_size len -> ~ in_img B x).
      { intros x Hx. replace x with (res - 16 + (x - (res - 16))) by lia. apply NIMG. lia. }
      assert (DQD : res + enc_M len <= data \/ data + len <= res).
      { rewrite EM. destruct (Z.eq_dec len 0) as [N0|N0].
        { assert (Z0 : enc_size len = 1) by (unfold enc_size; rewrite N0; reflexivity). lia. }
        unfold enc_data_where in WHERE. rewrite HSEG in WHERE.
        destruct WHERE as [E0 | [(a & k & Hin1 & H1 & H2) | [Hro | Hsp]]].
        - lia.
        - assert (Hy : In (a, k) (b1 ++ b2)) by (rewrite <- EB1; exact Hin1).
          destruct (blk_disj B API L2 A2 mem2 md2 b1 (res - 16, enc_size len + 16) b2 (a, k) HM2 EB2 Hy) as [D|D];
            cbn [fst snd] in D; lia.
        - destruct (Z_le_gt_dec (res + enc_size len) data) as [D|D]; [left; exact D|].
          destruct (Z_le_gt_dec (data + len) res) as [D'|D']; [right; exact D'|]. exfalso.
          apply (NI (Z.max res data)); [lia|].
          replace (Z.max res data) with (data + (Z.max res data - data)) by lia.
          apply (ro_img B HSEG); [lia|]. apply Hro. lia.
        - left. lia. }
      assert (DQT : res + enc_M len <= ENC_TABLE \/ ENC_TABLE + 65 <= res).
      { rewrite EM. unfold ENC_TABLE.
        destruct (Z_le_gt_dec (res + enc_size len) 66724) as [D|D]; [left; exact D|].
        destruct (Z_le_gt_dec (66724 + 65) res) as [D'|D']; [right; exact D'|]. exfalso.
        apply (NI (Z.max res 66724)); [lia|].
        apply (ro_img B HSEG); [lia|]. apply table_ro_at. unfold G_B64. lia. }
      assert (DATA2 : bytes_at rsegs mem2 data (map (Z_to_bv 8) bs)).
      { apply bytes_at_of_mbyte; [lia | rewrite length_map; lia |].
        intros i Hi. rewrite length_map in Hi. rewrite (DK2 i ltac:(lia)), (DATA i ltac:(lia)).
        rewrite nth_error_map8 by lia. reflexivity. }
      assert (LXS : Z.of_nat (length (map (Z_to_bv 8) (b64_enc bs ++ [0]))) = enc_size len).
      { rewrite length_map, length_app, Nat2Z.inj_add, b64_enc_len, HN. cbn [length]. unfold enc_size. lia. }
      eapply (evt_SR_canon rsegs _ _ md2 _).
      { change (RegisterBridge.canonical_register_state
                  (@YK11.mkst fx regs2 (Z_to_bv 64 0x151f8) mem2 (YK11.seg_rom rsegs)))
          with (MS (mkR_of regs2) (@fp_regs fx) (Z_to_bv 64 0x151f8) (@fp_csr fx) None mem2 (seg_rom rsegs)).
        rewrite mkR_of_eq, Q2, Q3, Q4, Q8, Q9, Q10, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
        eapply (enc_body (reg_get regs (Z_to_bv 5 1)) (reg_get regs (Z_to_bv 5 2)) (reg_get regs (Z_to_bv 5 3))
                  (reg_get regs (Z_to_bv 5 4)) (reg_get regs (Z_to_bv 5 8)) (reg_get regs (Z_to_bv 5 9))
                  _ _ _ _ _ _ _ _ _ _ _
                  (reg_get regs (Z_to_bv 5 18)) (reg_get regs (Z_to_bv 5 19)) (reg_get regs (Z_to_bv 5 20))
                  (reg_get regs (Z_to_bv 5 21)) (reg_get regs (Z_to_bv 5 22)) (reg_get regs (Z_to_bv 5 23))
                  (reg_get regs (Z_to_bv 5 24)) (reg_get regs (Z_to_bv 5 25)) (reg_get regs (Z_to_bv 5 26))
                  (reg_get regs (Z_to_bv 5 27)) _ _ _ _ _ _ (sp - 8256) data len res junk bs mem2).
        - exact HB.
        - exact HN.
        - lia.
        - exact RNZ.
        - exact HDZ.
        - exact DATA2.
        - exact (ro_image mem2 _ _ RO2 enc_table_image).
        - exact WRB.
        - rewrite Esp. unfold ENC_FRAME. exact FRm2.
        - rewrite Esp. unfold ENC_FRAME. exact STm2.
        - rewrite Esp. unfold ENC_FRAME. lia.
        - exact DQD.
        - exact DQT.
        - rewrite Esp, EM. unfold ENC_FRAME. left. lia. }
      { exact Hh2. }
      { exact Hl2. }
      intros ms3 (can & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
        -> & MU3 & WM3 & ST3 & BY3) & EQV3).
      destruct (eqv_shape _ _ _ _ EQV3) as (S3 & X3). rewrite S3. clear S3 EQV3.
      remember (ms_regs ms3) as R3 eqn:ER3. clear ER3 ms3.
      rewrite Esp, EM in MU3. rewrite Esp in ST3. unfold ENC_FRAME in MU3.
      assert (OUT : forall x, 0 <= x < 2 ^ 64 -> ~ (res <= x < res + enc_size len) -> ~ (sp - 32 <= x < sp) ->
        m3 (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)).
      { intros x Hx H1 H2. apply (munch_at _ _ _ _ MU3); [exact Hx | apply outside2; lia]. }
      assert (RO3 : ro_agree rsegs m3).
      { apply (ro_munch _ mem2 m3 RO2 MU3). intros x Hx.
        pose proof (ro_addr_low x Hx) as Hlo. pose proof (bv_unsigned_in_range 64 x) as Hr.
        apply outside2; [|lia].
        destruct (Z_lt_le_dec (bv_unsigned x) res) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec (bv_unsigned x) (res + enc_size len)) as [H2|H2]; [|right; exact H2].
        exfalso. apply (NI (bv_unsigned x)); [lia|]. apply (ro_img B HSEG); [lia|].
        rewrite Z_to_bv_bv_unsigned. exact Hx. }
      assert (KEEP3 : forall a k i, In (a, k) (blocks L A) -> a <> 0 -> 0 <= i < k ->
        mbyte rsegs m3 (a + i) = mbyte rsegs mem (a + i)).
      { intros a k i Hin1 Ha Hi. destruct (blk_facts B API L A mem md a k HMR Hin1) as (B1 & B2 & _).
        assert (Hy : In (a, k) (b1 ++ b2)) by (rewrite <- EB1; exact Hin1).
        destruct (blk_disj B API L2 A2 mem2 md2 b1 (res - 16, enc_size len + 16) b2 (a, k) HM2 EB2 Hy) as [D|D];
          cbn [fst snd] in D;
          (transitivity (mbyte rsegs mem2 (a + i));
           [apply mbyte_eq_of; apply OUT; lia
           | rewrite (KEEP2 a k i Hin1 Ha Hi); apply mbyte_eq_of; apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]]). }
      assert (DK3 : forall i, 0 <= i < len -> mbyte rsegs m3 (data + i) = mbyte rsegs mem (data + i)).
      { intros i Hi. destruct (DW i Hi) as [(a & k & Hin1 & H1) | [Hro | Hsp]].
        - destruct (blk_facts B API L A mem md a k HMR Hin1) as (B1 & B2 & _).
          replace (data + i) with (a + (data + i - a)) by lia. apply (KEEP3 a k); [exact Hin1 | lia | lia].
        - exact (mbyte_ro mem m3 _ ROm RO3 Hro).
        - rewrite <- (DK2 i Hi). apply mbyte_eq_of. apply OUT; lia. }
      assert (MR3 : aa_MR API L2 A2 m3 md2).
      { apply (MR_keep B API L2 A2 mem2 m3 md2 HM2).
        - intros a Ho. pose proof (owned_low B API L2 A2 mem2 md2 a HM2 Ho) as Hlo. apply OUT; [lia | | lia].
          intros Hx. destruct (NB3 (a - (res - 16)) ltac:(lia)) as (_ & NO).
          replace (res - 16 + (a - (res - 16))) with a in NO by lia. exact (NO Ho).
        - intros p k i Hp Hi.
          destruct (mr_blocks B _ (aa_laws API) L2 A2 mem2 md2 p k i HM2 Hp Hi) as (P & C3 & C4 & _).
          destruct (Z_lt_le_dec (ptr_addr L2 p + i) res) as [H1|H1];
            [|destruct (Z_lt_le_dec (ptr_addr L2 p + i) (res + enc_size len)) as [H2|H2]].
          + destruct P as (b0 & Hb). exists b0. rewrite OUT by lia. exact Hb.
          + apply (present_of_mbyte B HSEG); [lia | apply NI; lia |].
            replace (ptr_addr L2 p + i) with (res + (ptr_addr L2 p + i - res)) by lia.
            rewrite (mbyte_of_bytes_at m3 res _ _ BY3) by (rewrite LXS; lia).
            apply (proj2 (nth_error_Some _ _)). lia.
          + destruct P as (b0 & Hb). exists b0. rewrite OUT by lia. exact Hb. }
      apply SR_ret. cbv beta.
      exists L2, A2, R3, m3, md2, res.
      split; [rewrite ERA; reflexivity|].
      split; [exact RO3|].
      split.
      { unfold guard_kept. rewrite HSEG. intros i Hi. unfold guard_kept in GK2. rewrite HSEG in GK2.
        pose proof (owned_low B API L A mem md _ HMR (got_owned B L A i Hi)) as Hg.
        transitivity (mbyte rsegs mem2 (ms_got_guard B + i)).
        - apply mbyte_eq_of. apply OUT; [lia | | lia]. intros Hx.
          destruct (NB3 (ms_got_guard B + i - (res - 16)) ltac:(lia)) as (_ & NO). apply NO.
          replace (res - 16 + (ms_got_guard B + i - (res - 16))) with (ms_got_guard B + i) by lia.
          apply got_owned. exact Hi.
        - rewrite (GK2 i Hi). apply mbyte_eq_of. apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia]. }
      split; [exact INIT2|].
      split.
      { unfold call_post_k. rewrite HSEG.
        split; [exact MR3|].
        split; [exact HWF2|]. split; [exact HBD2|]. split; [exact HLL2|]. split; [exact HPA2|].
        split; [exact (rp_of_eqv regs R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3)|].
        split; [exact HMD2|].
        split.
        { intros a Hr Ho1 Ho2 Hsc Hw.
          assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (img_bound B HSEG a Hr); lia]).
          unfold scratch_k, ENC_STACK, ALLOC_STACK in Hsc.
          apply (chain3 mem m1 mem2 m3 a).
          - apply (munch_at _ _ _ _ MU1); [lia | apply outside1; lia].
          - apply FR2; [exact Hr | exact Ho1 | exact Ho2 | unfold scratch_k; rewrite S1; unfold ALLOC_STACK; lia |].
            intros Hx. apply Hw. left. exact Hx.
          - apply OUT; [lia | | lia]. intros Hx. apply Hw. right. split; [exact RNZ | lia]. }
        split.
        { intros p k i Hp Hp2 Hi.
          destruct (blk_facts B API L A mem md _ _ HMR (blk_of_user L A p k Hp)) as (B1 & _).
          apply (KEEP3 _ k); [apply blk_of_user; exact Hp | lia | exact Hi]. }
        intros a Hs. unfold scratch_k, ENC_STACK, ALLOC_STACK in Hs. destruct Hs as [Hs|Hs].
        - destruct ST3 as (_ & _ & STK). exact (proj1 (STK a ltac:(lia))).
        - exact (WM3 _ (SC2 a (or_intror Hs))). }
      split; [exact LEN2|].
      split; [exact (eqv_getr _ _ 10 _ X3 ltac:(lia) eq_refl)|].
      split; [unfold keeps; rewrite HSEG; intros a k i Hin1 Ha Hi; exact (KEEP3 a k i Hin1 Ha Hi)|].
      split; [exact UBK2|].
      split; [exact DK3|].
      right. split; [exact NC|]. split; [exact RNZ|]. split; [exact RAL|]. split; [exact SLOT2|].
      split; [exact NST|]. split; [exact NIMG|]. split; [exact NIN|].
      split; [exists b1, b2; split; [exact EB2 | exact EB1]|].
      split.
      { apply (ledger_keep B L2 A2 mem2 m3 _ _ _ _ LED2).
        - intros a Hs. apply mbyte_eq_of.
          assert (Hsb : 0 <= a < 0x33b58) by (unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs; lia).
          apply OUT; [lia | | lia]. intros Hx. apply (NST (a - (res - 16))); [lia|].
          replace (res - 16 + (a - (res - 16))) with a by lia. exact Hs.
        - intros a k i Hk Hin1 Hi.
          destruct (blk_facts B API L2 A2 mem2 md2 _ _ HM2 Hin1) as (C1 & C2 & _).
          rewrite EB2 in Hin1. apply in_app_or in Hin1.
          assert (D : a - 16 = res - 16 \/ res + enc_size len <= a - 16 \/ a + k <= res - 16).
          { destruct Hin1 as [Hin1 | [Ex | Hin1]].
            - destruct (blk_disj B API L2 A2 mem2 md2 b1 (res - 16, enc_size len + 16) b2 (a - 16, k + 16) HM2 EB2
                ltac:(apply in_or_app; left; exact Hin1)) as [D|D]; cbn [fst snd] in D; right; lia.
            - injection Ex as Ex1 _. left. lia.
            - destruct (blk_disj B API L2 A2 mem2 md2 b1 (res - 16, enc_size len + 16) b2 (a - 16, k + 16) HM2 EB2
                ltac:(apply in_or_app; right; exact Hin1)) as [D|D]; cbn [fst snd] in D; right; lia. }
          apply mbyte_eq_of. apply OUT; lia. }
      intros i Hi. rewrite (mbyte_of_bytes_at m3 res _ i BY3) by (rewrite LXS; lia). reflexivity.
Qed.

End M.
