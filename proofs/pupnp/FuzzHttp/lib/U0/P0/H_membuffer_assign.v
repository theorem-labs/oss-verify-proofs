(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy H_str_alloc HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition membuffer_assign_entry := 0x16708%Z.
Lemma firstn_pref : forall {X} (src : list X) z rest n, Z.of_nat (length src) = n ->
  firstn (Z.to_nat (n + 1)) (src ++ [z] ++ rest) = src ++ [z].
Proof.
  intros. replace (Z.to_nat (n + 1)) with (length (src ++ [z])) by (rewrite length_app; cbn; lia).
  rewrite app_assoc. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. now rewrite app_nil_r.
Qed.
Ltac sstep := step; fix_lit_store.

Notation AFR m q j s3 s2 s1 s0 ra := (rw_cells rsegs m q [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition asegA_post (lo MB SRC n A len cap : Z) (ra sp gp tp s0 s1 s2 s3 : word)
    (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' j (a0' a1' a2' x18 : word) (pc nsz : Z),
    ms' = MS (mkR (if pc =? 0x167ec then ra else wz (if pc =? 0x16764 then 0x16764 else 0x167c8))
                  (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz MB) (wz n) a0' a1' a2' a3 a4 a5 a6 a7
                  x18 (wz nsz) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz (if pc =? 0x167ec then 0x167ec else 0x1995c)) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ AFR m' (bv_unsigned sp + -48) j s3 s2 s1 s0 ra
    /\ rw_cells rsegs m' MB (mbuf_cells A len cap)
    /\ ( (pc = 0x167ec /\ a1' = wz SRC /\ n <= cap)
       \/ ((pc = 0x16764 \/ pc = 0x167c8) /\ x18 = wz SRC /\ a0' = wz A /\ a1' = wz (nsz + 1) /\ n <= nsz /\ nsz <= n + cap + 5) )%Z.

Lemma asegA : forall (lo MB SRC n A len cap : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 < MB)%Z -> (MB mod 8 = 0)%Z ->
  (0 < SRC < 2^64)%Z -> (0 <= n < 2^32 - 8)%Z -> (0 <= len <= cap)%Z -> (cap < 2^32)%Z -> (0 <= A < 2^64)%Z ->
  evt rsegs (asegA_post lo MB SRC n A len cap ra sp gp tp s0 s1 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_assign_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI MBC MBLO MBHI MBNZ MBAL HS HN HL HC HA. unfold membuffer_assign_entry. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  carve_frame 48%nat ST.
  do 6 sstep. zstep. zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  ub_null. ub_align.
  zstep. zstep. zstep. if_cases K1; zify_cond K1.
  -   zstep. zstep. if_cases K2; zify_cond K2.
    +
      apply evt_done. unfold asegA_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. eexists _, _, _, _, _, _, 0x167ec, cap. split; [reflexivity|].
      repeat (split; [eassumption|]). left. repeat split; lia.
    + zstep. zstep. zstep. if_cases K3; zify_cond K3.
      *   zstep. zstep. zstep. zstep. zstep.
        apply evt_done. unfold asegA_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. eexists _, _, _, _, _, _, 0x167c8, (5 + cap)%Z. split; [reflexivity|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity; try lia.
      * zstep. zstep. zstep. zstep. zstep. zstep.
        apply evt_done. unfold asegA_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. eexists _, _, _, _, _, _, 0x167c8, (n - len + cap)%Z. split; [reflexivity|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity; try lia.
  -   zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
    + apply evt_done. unfold asegA_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. eexists _, _, _, _, _, _, 0x167ec, 5. split; [reflexivity|].
      repeat (split; [eassumption|]). left. repeat split; lia.
    + zstep. zstep. zstep. zstep. zstep.
      apply evt_done. unfold asegA_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. eexists _, _, _, _, _, _, 0x16764, (5 + n)%Z. split; [reflexivity|].
      repeat (split; [eassumption|]). right. repeat split; try reflexivity; try lia.
Qed.

Definition asegD_post (lo MB n A' cap' : Z) (bs' : list byte) (W : list ivl) (ra sp gp tp s0 s1 s2 s3 : word)
    (t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 t0' t1' t2' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' MB (mbuf_cells A' n cap')
    /\ (n >= 1 -> rw_cells rsegs m' A' [CB (Z.to_nat (cap' + 1)) bs']).

Lemma asegD0 : forall (lo MB SRC A' len0 cap' : Z) (j : list byte) x1 x18 x19 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -48) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFR m (bv_unsigned sp + -48) j s3 s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A' len0 cap') -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z ->
  evt rsegs (asegD_post lo MB 0 A' cap' [] [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32)]%Z ra sp gp tp s0 s1 s2 s3 t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz MB) (wz 0) a0 (wz SRC) a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x167ec) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  zstep. lit_branch. zstep. sstep. do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold asegD_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. repeat (split; [eassumption|]). intros; lia.
Qed.

Lemma asegD1 : forall (lo MB SRC n A' len0 cap' : Z) (src bs j : list byte) x1 x18 x19 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -48) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFR m (bv_unsigned sp + -48) j s3 s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A' len0 cap') -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z ->
  bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (1 <= n <= cap')%Z -> (cap' < 2^32)%Z ->
  rw_cells rsegs m A' [CB (Z.to_nat (cap' + 1)) bs] -> (0 < A')%Z -> (A' + (cap' + 1) <= lo)%Z -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB)%Z ->
  (SRC + n <= A' \/ A' + (cap' + 1) <= SRC)%Z -> (SRC + n <= bv_unsigned sp - 48)%Z -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
  evt rsegs (asegD_post lo MB n A' cap' (src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (n + 1)) bs)
               [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z ra sp gp tp s0 s1 s2 s3 t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz MB) (wz n) a0 (wz SRC) a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x167ec) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI BSRC LEN HN HC BLK A0 AHI DJM DJ DJ2 DJS. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.
  pose proof (rw_cells_bound rsegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
  assert (LBS : length bs = Z.to_nat (cap' + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).

  apply (rw_cells_split_CB rsegs m A' [] (Z.to_nat (cap' + 1)) bs [] [Z.to_nat n; 1%nat; Z.to_nat (cap' - n)]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
    destruct (proj1 (rw_cells_app rsegs m A' [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
  cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
  zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  zstep. zstep. zstep.
  call (memcpy_call A' SRC n src).
  all: side (first [exact BSRC | exact BLK1 | exact MI | reflexivity | lia]).
  zstep. zstep. step. ubr. step. ubr. step. ubr.
  rewrite (Z.add_comm n A'). remember (A' + n)%Z as V eqn:EV. sstep. subst V.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (BLK : rw_cells rsegs mm A' [CB (Z.to_nat (cap' + 1)) (src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (n + 1)) bs)])
  end.
  { lazymatch type of BLK23 with rw_cells _ ?mm _ [?c2; ?c3] =>
      pose proof (proj2 (rw_cells_app rsegs mm A' [CB (Z.to_nat n) src] [c2; c3])) as J;
      cbn [cells_size csize Nat.add] in J; rewrite Nat.add_0_r, Z2Nat.id in J by lia;
      specialize (J (conj PC BLK23)); cbn [app] in J;
      pose proof (rw_cells_merge rsegs mm A' [] [CB (Z.to_nat n) src; c2; c3] []) as M
    end.
    rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
    replace (Z.to_nat n + S (Z.to_nat (cap' - n) + 0))%nat with (Z.to_nat (cap' + 1)) in M by lia.
    replace (firstn (Z.to_nat (cap' - n)) (skipn 1 (skipn (Z.to_nat n) bs))) with (skipn (Z.to_nat (n + 1)) bs) in *.
    2:{ rewrite skipn_skipn. replace (1 + Z.to_nat n)%nat with (Z.to_nat (n + 1)) by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
    pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ. }
  clear PC BLK23.
  zstep. sstep. do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold asegD_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. repeat (split; [eassumption|]). intros _; exact BLK.
Qed.

Lemma asegC0 : forall (lo MB SRC A A' len0 cap cap' : Z) (j : list byte) x1 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -48) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFR m (bv_unsigned sp + -48) j s3 s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A len0 cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 <= A' < 2^64)%Z -> (0 <= cap' < 2^64)%Z ->
  evt rsegs (asegD_post lo MB 0 A' cap' [] [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32)]%Z ra sp gp tp s0 s1 s2 s3 t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz MB) (wz 0) (wz A') a1 a2 a3 a4 a5 a6 a7 (wz SRC) (wz cap') s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x167e0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI HA HC. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  sstep. sstep. zstep.
  eapply evt_cut. { eapply (asegD0 lo MB SRC A' len0 cap'); try eassumption; lia. }
  intros ms' P. unfold asegD_post in *. destruct_exs P. destruct P as (-> & MU2 & WM2 & P).
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| exact MU2]. } split. { eapply wmono_trans; [exact WM| exact WM2]. } exact P.
Qed.

Lemma asegC1 : forall (lo MB SRC n A A' len0 cap cap' : Z) (src bs j : list byte) x1 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -48) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFR m (bv_unsigned sp + -48) j s3 s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A len0 cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z ->
  bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (1 <= n <= cap')%Z -> (cap' < 2^32)%Z ->
  rw_cells rsegs m A' [CB (Z.to_nat (cap' + 1)) bs] -> (0 < A')%Z -> (A' + (cap' + 1) <= lo)%Z -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB)%Z ->
  (SRC + n <= A' \/ A' + (cap' + 1) <= SRC)%Z -> (SRC + n <= bv_unsigned sp - 48)%Z -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
  evt rsegs (asegD_post lo MB n A' cap' (src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (n + 1)) bs)
               [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z ra sp gp tp s0 s1 s2 s3 t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz MB) (wz n) (wz A') a1 a2 a3 a4 a5 a6 a7 (wz SRC) (wz cap') s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x167e0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI BSRC LEN HN HC BLK A0 AHI DJM DJ DJ2 DJS. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.
  pose proof (rw_cells_bound rsegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
  sstep. sstep. zstep.
  eapply evt_cut. { eapply (asegD1 lo MB SRC n A' len0 cap' src bs); try eassumption; lia. }
  intros ms' P. unfold asegD_post in *. destruct_exs P. destruct P as (-> & MU2 & WM2 & P).
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| exact MU2]. } split. { eapply wmono_trans; [exact WM| exact WM2]. } exact P.
Qed.

Lemma asegE : forall (lo : Z) (j : list byte) x1 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -48) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFR m (bv_unsigned sp + -48) j s3 s2 s1 s0 ra ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-104)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs)
                       /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x167d8) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. lit_branch. zstep. zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma asegF : forall (pc MB A len0 cap : Z) (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m (n : Z),
  (pc = 0x16764 \/ pc = 0x167c8)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len0 cap) -> (0 < MB /\ MB + 32 < 2^64)%Z -> (0 <= n /\ n + 1 < 2^63)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x167d8) sp gp tp t0 t1 t2 (wz MB) (wz n) (wz A) (wz (n + 1)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x1995c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz MB) (wz n) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros PC MI MBC MBR HN. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct PC as [-> | ->].
  - zstep. lit_branch. zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  - zstep. lit_branch. zstep. zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma asegG : forall (pc A' : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  (pc = 0x16764 \/ pc = 0x167c8)%Z -> (0 < A' < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x167e0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros PC HA. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct PC as [-> | ->]; (zstep; if_cases K; zify_cond K; [| exfalso; lia]); apply evt_done; reflexivity.
Qed.

Lemma asegH : forall (A' n : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  (0 < A' < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz n) (wz A') a1 a2 a3 a4 a5 a6 a7 s2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x167e0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz n) (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x167d8) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HA. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep. apply evt_done. reflexivity.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis REALLOCPC : al_realloc_pc L = 0x1995c.

  Definition mown (m : mem) (LB : list (block K)) (A cap : Z) (ok : option K) (bs : list byte) : Prop :=
    match ok with
    | None => A = 0 /\ cap = 0 /\ bs = []
    | Some k => In (k, A, cap + 1) LB /\ rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs]
    end.

  Definition mfresh (LB : list (block K)) (ok ok' : option K) (A' cap' : Z) : Prop :=
    forall b, In b (lb_keep AI ok LB) -> match ok' with Some k' => b <> (k', A', cap' + 1) | None => True end.

  Definition membuffer_assign_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list (block K)) (ok : option K) (MB A len cap n lo B : Z) (src bs : list byte) (m : mem)
      : ai_PS rsegs AI -> list (block K) -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r A' len' cap' : Z) (ok' : option K) (bs' : list byte),
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L) [C4 errv'])
      /\ hpx AI [(MB, MB + 32)] (lb_keep AI ok LB) (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ (forall b, In b (lb_keep AI ok LB) -> In b LB')
      /\ rw_cells rsegs m' MB (mbuf_cells A' len' cap') /\ (0 <= len' <= cap')%Z /\ (cap' < 2^32)%Z /\ (cap' <= cap + n + 5)%Z
      /\ mown m' LB' A' cap' ok' bs' /\ mfresh LB ok ok' A' cap'
      /\ ( (r = 0 /\ len' = n /\ (n >= 1 -> firstn (Z.to_nat (n + 1)) bs' = src ++ [Z_to_bv 8 0]))
         \/ (r = -104 /\ A' = A /\ len' = len /\ cap' = cap /\ ok' = ok /\ bs' = bs /\ LB' = LB) )%Z.

  #[using="AC LOK REALLOCPC"] Theorem membuffer_assign_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (ok : option K) (MB SRC n A len cap lo B : Z) (src bs : list byte) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 48 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> (0 <= len <= cap)%Z -> (cap + n + 8 < 2^32)%Z -> mown m LB A cap ok bs ->
    mbloc AI (lb_keep AI ok LB) (bv_unsigned sp) B MB 32 -> (MB mod 8 = 0)%Z ->
    bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (0 < SRC)%Z -> (SRC + n <= alloc_ceiling)%Z ->
    client_range AI (lb_keep AI ok LB) (bv_unsigned sp) SRC n -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
    a0 = wz MB -> a1 = wz SRC -> a2 = wz n ->
    SREACH AI (membuffer_assign_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_assign_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI MBC HLC HNC OWN MBL MBAL BSRC LEN S0 SHI CR DJS -> -> ->.
    pose proof (word_lt64 sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (SUB : forall b, In b (lb_keep AI ok LB) -> In b LB) by (intros b Hb; eapply lb_keep_sub; exact Hb).
    pose proof (mbloc_lo rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL) as MBLO.
    pose proof (mbloc_pos rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL ltac:(lia)) as MBP.
    pose proof (mbloc_errno rsegs AI _ _ _ _ _ _ _ _ LOK HR SUB MBL ltac:(lia)) as MBE.
    assert (MBB : (MB + 32 <= B)%Z).
    { destruct MBL as [H|(b & Hb & H1 & H2)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). cbn in R4. lia. }
    assert (SUBNE : forall k, ok = Some k -> forall b, In b (lb_keep AI ok LB) -> In b LB /\ b <> (k, A, cap + 1)).
    { intros k -> b Hb. split; [apply SUB; exact Hb|]. cbn in Hb. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl). }

    assert (DJM0 : forall k, ok = Some k -> (MB + 32 <= A \/ A + (cap + 1) <= MB)%Z).
    { intros k Hk. destruct ok as [k0|]; [| discriminate]. cbn in OWN. destruct OWN as [HIN _].
      exact (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (k0, A, cap + 1) HR (SUBNE k0 eq_refl) HIN MBL ltac:(lia)). }

    assert (MBCR : forall SP' LB' A1 l1 c1, (SP' <= bv_unsigned sp)%Z -> (forall b, In b (lb_keep AI ok LB) -> In b LB') ->
                   client_range AI LB' SP' MB (Z.of_nat (cells_size (mbuf_cells A1 l1 c1)))).
    { intros SP' LB' A1 l1 c1 HS HL. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mbloc_client rsegs AI). eapply (mbloc_weaken rsegs AI); [exact MBL| exact HS| exact HL]. }
    assert (ARNG : (0 <= A < 2^64)%Z).
    { destruct ok as [k|]; cbn in OWN.
      - destruct OWN as [HIN _]. destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4. lia.
      - lia. }

    eapply sreach_evt. { eapply (asegA lo MB SRC n A len cap); try eassumption; lia. }
    intros ms' (m1 & j & a0' & a1' & a2' & x18 & pc & nsz & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1 & CASES).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (bytes_at_transport rsegs _ m m1 _ _ BSRC MU1 ltac:(cbn; lia)) as BSRC1.
    assert (OWN1 : mown m1 LB A cap ok bs).
    { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
      destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
      eapply (rw_cells_transport rsegs _ m m1); [exact BLK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. lia. }
    assert (HP1 : hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    clear MU1 WM1 HR HE ERR MI BSRC ST OWN.

    assert (FIN : forall sx LBx m2 m3 (A' cap' : Z) (okx : option K) (bs' : list byte) (W : list ivl)
                   (t0' t1' t2' a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
      hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m2 ->
      RHEAP rsegs AI sx LBx m2 ->
      (forall b, In b (lb_keep AI ok LB) -> In b LBx /\ match okx with Some kx => b <> (kx, A', cap' + 1) | None => True end) ->
      RENV rsegs AI m2 B -> (exists e, rw_cells rsegs m2 (al_errno L) [C4 e]) ->
      ((n = 0 /\ W = [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32)] /\ mown m2 LBx A' cap' okx bs')
        \/ (n >= 1 /\ W = [(bv_unsigned sp - 48, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))] /\ exists kx, okx = Some kx /\ In (kx, A', cap' + 1) LBx))%Z ->
      (0 <= n <= cap')%Z -> (cap' < 2^32)%Z -> (cap' <= cap + n + 5)%Z ->
      munch W m2 m3 -> wmono rsegs m2 m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp) ->
      rw_cells rsegs m3 MB (mbuf_cells A' n cap') ->
      (n >= 1 -> rw_cells rsegs m3 A' [CB (Z.to_nat (cap' + 1)) bs'] /\ firstn (Z.to_nat (n + 1)) bs' = src ++ [Z_to_bv 8 0])%Z ->
      membuffer_assign_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m sx LBx
        (MS (mkR ra sp gp (wz (al_tp L)) t0' t1' t2' s0 s1 (wz 0) a1_ a2_ a3_ a4_ a5_ a6_ a7_ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
            F (ret_pc ra) fc None m3 (seg_rom rsegs))).
    { intros until t6_. intros HP2 HR2 SUB2 HE2 [e2 ERR2] OWN2 HNC' HC' HCB MU3 WM3 MI3 ST3 MBC3 BLK3.
      assert (WOK : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= bv_unsigned sp)
                    \/ (forall a, fst iv <= a < snd iv -> ~ client_addr AI (lb_keep AI ok LB) (bv_unsigned sp) a)
                    \/ inside [(MB, MB + 32)] (fst iv) (snd iv - fst iv))%Z W).
      { destruct OWN2 as [(N0 & -> & _)|(N1 & -> & (kx & -> & HIN))].
        - constructor. { left. cbn. lia. } constructor; [| constructor]. right; right. cbn. lia.
        - constructor. { left. cbn. lia. } constructor. { right; right. cbn. lia. } constructor; [| constructor].
          right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR2| exact HIN| exact SUB2| lia| cbn; lia]. }
      assert (WOK2 : Forall (fun iv => alloc_ceiling <= fst iv
                    \/ (exists lo hi, al_client_static L lo hi /\ lo <= fst iv /\ snd iv <= hi)
                    \/ (al_errno L <= fst iv /\ snd iv <= al_errno L + 4)
                    \/ (exists b, In b LBx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b))%Z W).
      { destruct OWN2 as [(N0 & -> & _)|(N1 & -> & (kx & -> & HIN))].
        - constructor. { left. cbn. lia. } constructor; [| constructor]. eapply (mbloc_hf rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb].
        - constructor. { left. cbn. lia. } constructor. { eapply (mbloc_hf rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb]. } constructor; [| constructor].
          right; right; right. exists (kx, A', cap' + 1). split; [exact HIN|]. cbn. lia. }
      assert (ERR3 : rw_cells rsegs m3 (al_errno L) [C4 e2]).
      { eapply (rw_cells_transport rsegs _ m2 m3); [exact ERR2| exact MU3| exact WM3|].
        destruct OWN2 as [(N0 & -> & _)|(N1 & -> & (kx & -> & HIN))]; cbn; [lia|].
        pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR2 HIN) as DE. cbn in DE. lia. }
      unfold membuffer_assign_post.
      do 15 eexists. exists 0, A', n, cap', okx, bs'.
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
        destruct OWN2 as [(N0 & -> & _)|(N1 & -> & (kx & -> & HIN))].
        - constructor. { left. cbn. lia. } constructor; [| constructor]. eapply (mbloc_ef rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb].
        - constructor. { left. cbn. lia. } constructor. { eapply (mbloc_ef rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb]. } constructor; [| constructor].
          right; right; right. exists (kx, A', cap' + 1). split; [exact HIN|]. cbn. lia. }
      split; [eexists; exact ERR3|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; apply SUB2; exact Hb| exact MU3| exact WM3| exact WOK]. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3| exact WOK2]. }
      split; [intros b Hb; apply SUB2; exact Hb|]. split; [exact MBC3|]. split; [lia|]. split; [lia|]. split; [exact HCB|].
      split.
      { destruct OWN2 as [(N0 & -> & OW)|(N1 & _ & (kx & -> & HIN))].
        - destruct okx as [kx|]; cbn in OW |- *; [| exact OW]. destruct OW as [HIN BLK2]. split; [exact HIN|].
          destruct (ai_block_range rsegs AI _ _ _ _ HR2 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
          pose proof (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (kx, A', cap' + 1) HR2 SUB2 HIN MBL ltac:(lia)) as DJx. cbn in DJx.
          eapply (rw_cells_transport rsegs _ m2 m3); [exact BLK2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
        - cbn. split; [exact HIN|]. apply BLK3. lia. }
      split. { intros b Hb. exact (proj2 (SUB2 b Hb)). }
      left. split; [reflexivity|]. split; [reflexivity|]. intros N1. apply BLK3. lia. }

    destruct CASES as [(-> & -> & HNcap)|(PCS & -> & -> & -> & N1 & N2)].
    - cbn [Z.eqb Pos.eqb].
      destruct (Z.eq_dec n 0) as [->|NZ].
      + eapply sreach_evt. { eapply (asegD0 lo MB SRC A len cap j); try eassumption; lia. }
        intros ms' P. unfold asegD_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & _).
        apply sreach_ret. assert (CAPB : (cap <= cap + 0 + 5)%Z) by lia. eapply (FIN s LB m1 _ A cap ok bs); try eassumption.
        * intros b Hb. split; [apply SUB; exact Hb|]. destruct ok as [k|]; [| exact I]. cbn in Hb. intros ->.
          exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl).
        * eexists; exact ERR1.
        * left. split; [reflexivity|]. split; [reflexivity|]. exact OWN1.
        * lia. * lia.
        * intros; lia.
      + destruct ok as [k|]; cbn in OWN1; [| lia]. destruct OWN1 as [HIN BLK1].
        destruct (ai_block_range rsegs AI _ _ _ _ HR1 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
        assert (DJ : SRC + n <= A \/ A + (cap + 1) <= SRC).
        { destruct (Z.lt_ge_cases (SRC + n) (A + 1)) as [|G1]; [lia|]. destruct (Z.lt_ge_cases (A + cap) SRC) as [|G2]; [lia|].
          exfalso.
          destruct (Z.lt_ge_cases SRC A).
          - apply (fresh_block_not_client rsegs AI _ _ (lb_keep AI (Some k) LB) (k, A, cap + 1) (bv_unsigned sp) m1 (A) LOK HR1 HIN); [| lia| cbn; lia|].
            { intros b0 Hb0. split; [apply SUB; exact Hb0|]. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb0 eq_refl). }
            apply CR. lia.
          - apply (fresh_block_not_client rsegs AI _ _ (lb_keep AI (Some k) LB) (k, A, cap + 1) (bv_unsigned sp) m1 SRC LOK HR1 HIN); [| lia| cbn; lia|].
            { intros b0 Hb0. split; [apply SUB; exact Hb0|]. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb0 eq_refl). }
            apply CR. lia. }
        pose proof (DJM0 k eq_refl) as DJM.
        eapply sreach_evt. { eapply (asegD1 lo MB SRC n A len cap src bs j); try eassumption; lia. }
        intros ms' P. unfold asegD_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & BLK3).
        apply sreach_ret. assert (CAPB : (cap <= cap + n + 5)%Z) by lia. eapply (FIN s LB m1 _ A cap (Some k)); try eassumption.
        * intros b Hb. split; [apply SUB; exact Hb|]. cbn in Hb. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl).
        * eexists; exact ERR1.
        * right. split; [lia|]. split; [reflexivity|]. exists k. split; [reflexivity| exact HIN].
        * lia. * lia.
        * intros N1. split; [apply BLK3; lia|]. apply firstn_pref. exact LEN.
    -

      assert (CDFC : forall sx m2 (k' : K) (A' cap' A0 len0 cap0 : Z) (bs2 jx : list byte)
                      (x1 t0' t1' t2' a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
        hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m2 ->
        RHEAP rsegs AI sx ((k', A', cap' + 1) :: lb_keep AI ok LB) m2 -> block_range AI A' (cap' + 1) ->
        RENV rsegs AI m2 B -> (exists e, rw_cells rsegs m2 (al_errno L) [C4 e]) -> mem_inv rsegs m2 ->
        stk rsegs m2 lo (bv_unsigned sp + -48) -> AFR m2 (bv_unsigned sp + -48) jx s3 s2 s1 s0 ra ->
        rw_cells rsegs m2 MB (mbuf_cells A0 len0 cap0) -> bytes_at rsegs m2 SRC src ->
        rw_cells rsegs m2 A' [CB (Z.to_nat (cap' + 1)) bs2] -> (n <= cap')%Z -> (cap' < 2^32)%Z -> (cap' <= cap + n + 5)%Z ->
        SREACH AI (membuffer_assign_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m)
          (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp (wz (al_tp L)) t0' t1' t2' (wz MB) (wz n) (wz A') a1_ a2_ a3_ a4_ a5_ a6_ a7_ (wz SRC) (wz cap') s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
              F (wz 0x167e0) fc None m2 (seg_rom rsegs)) sx ((k', A', cap' + 1) :: lb_keep AI ok LB)).
      { intros until t6_. intros HP2 HR2 BR2 HE2 ERR2 MI2 ST2 FR2 MBC2 BSRC2 BLK2 NC' HC' CAPB0.
        destruct BR2 as (U1 & U2 & U3 & U4 & U5).
        assert (NEW : In (k', A', cap' + 1) ((k', A', cap' + 1) :: lb_keep AI ok LB)) by (left; reflexivity).
        assert (SUB2 : forall b, In b (lb_keep AI ok LB) -> In b ((k', A', cap' + 1) :: lb_keep AI ok LB) /\ b <> (k', A', cap' + 1)).
        { intros b Hb. split; [right; exact Hb|]. intros ->.
          pose proof (ai_blocks_nodup rsegs AI _ _ _ HR2) as ND. cbn in ND. inversion ND as [|xk xl NI ND']; subst.
          apply NI. apply base.list_elem_of_In. exact (in_map blk_id _ _ Hb). }
        destruct (Z.eq_dec n 0) as [->|NZ].
        - eapply sreach_evt. { eapply (asegC0 lo MB SRC A0 A' len0 cap0 cap' jx); try eassumption; lia. }
          intros ms' P. unfold asegD_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & _).
          apply sreach_ret. eapply (FIN sx _ m2 _ A' cap' (Some k') bs2); try eassumption.
          + left. split; [reflexivity|]. split; [reflexivity|]. cbn. split; [exact NEW| exact BLK2].
          + lia. + intros; lia.
        - assert (DJ : SRC + n <= A' \/ A' + (cap' + 1) <= SRC).
          { destruct (Z.lt_ge_cases (SRC + n) (A' + 1)) as [|G1]; [lia|]. destruct (Z.lt_ge_cases (A' + cap') SRC) as [|G2]; [lia|].
            exfalso. destruct (Z.lt_ge_cases SRC A').
            - apply (fresh_block_not_client rsegs AI _ _ (lb_keep AI ok LB) (k', A', cap' + 1) (bv_unsigned sp) m2 A' LOK HR2 NEW SUB2); [lia| cbn; lia|].
              apply CR. lia.
            - apply (fresh_block_not_client rsegs AI _ _ (lb_keep AI ok LB) (k', A', cap' + 1) (bv_unsigned sp) m2 SRC LOK HR2 NEW SUB2); [lia| cbn; lia|].
              apply CR. lia. }
          pose proof (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (k', A', cap' + 1) HR2 SUB2 NEW MBL ltac:(lia)) as DJM. cbn in DJM.
          eapply sreach_evt. { eapply (asegC1 lo MB SRC n A0 A' len0 cap0 cap' src bs2 jx); try eassumption; lia. }
          intros ms' P. unfold asegD_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & BLK3).
          apply sreach_ret. eapply (FIN sx _ m2 _ A' cap' (Some k')); try eassumption.
          + right. split; [lia|]. split; [reflexivity|]. exists k'. split; [reflexivity| exact NEW].
          + lia.
          + intros _. split; [apply BLK3; lia|]. apply firstn_pref. exact LEN. }

      assert (CRW : client_range AI LB (bv_unsigned sp + -48) SRC n).
      { intros a Ha. destruct (CR a Ha) as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
        exists b. split; [apply SUB; exact Hb| exact Hr]. }
      assert (CRK : client_range AI (lb_keep AI ok LB) (bv_unsigned sp + -48) SRC n).
      { intros a Ha. destruct (CR a Ha) as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc]. }
      assert (OKH : forall mm, mown mm LB A cap ok bs ->
                match ok with None => A = 0 /\ (match ok with Some _ => cap + 1 | None => 0 end) = 0 /\ bs = []
                            | Some k => In (k, A, match ok with Some _ => cap + 1 | None => 0 end) LB
                                        /\ rw_cells rsegs mm A [CB (Z.to_nat (match ok with Some _ => cap + 1 | None => 0 end)) bs] end).
      { intros mm OW. destruct ok as [k|]; cbn in OW |- *; [exact OW|]. destruct OW as (? & ? & ?). repeat split; auto. }
      assert (PCr : (if pc =? 92140 then ra else wz (if pc =? 92004 then 92004 else 92104)) = wz pc /\ (if pc =? 92140 then 92140 else 104796) = 104796).
      { destruct PCS as [-> | ->]; cbn; auto. }
      destruct PCr as [-> ->].

      eapply sreach_bind.
      { rewrite <- REALLOCPC. eapply (orealloc_spec rsegs AI AC) with (lo := lo) (B := B) (ok := ok); try eassumption; try reflexivity;
          rewrite ?unsigned_lit by lia; try lia; try eassumption. apply OKH. exact OWN1. }
      intros sx2 LB2 ms2 POST. unfold orealloc_post in POST. destruct_exs POST. destruct POST as (-> & CASES2).
      replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc) by (symmetry; apply ret_pc_even; [lia| destruct PCS as [-> | ->]; reflexivity]).
      destruct CASES2 as [(-> & -> & AF & HR2)|(k' & A' & junk & -> & -> & BR & AF & HR2 & BLK2)].
      +
        destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC1 ltac:(apply MBCR; [lia| auto])) as MBC2.
        pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPF BSRC1 ltac:(rewrite (proj1 (conj LEN I)) ; exact CRW)) as BSRC2.
        assert (OWN2 : mown m2 LB A cap ok bs).
        { destruct ok as [k|]; cbn in OWN1 |- *; [| exact OWN1]. destruct OWN1 as [HIN BLK]. split; [exact HIN|].
          destruct (ai_block_range rsegs AI _ _ _ _ HR1 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
          eapply (heap_pres_rw_cells rsegs AI); [exact HPF| exact BLK|]. eapply client_range_block; [exact HIN| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
        assert (HP2 : hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m2).
        { eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact SUB]. }
        clear HPF FR1 MBC1 BSRC1 OWN1 HP1 ERR1 HE1 MI1 ST1.
        eapply sreach_evt. { eapply (asegF pc MB A len cap); try eassumption; lia. }
        intros ms' ->.

        eapply sreach_bind.
        { rewrite <- REALLOCPC. eapply (orealloc_spec rsegs AI AC) with (lo := lo) (B := B) (ok := ok); try eassumption; try reflexivity;
            rewrite ?unsigned_lit by lia; try lia; try eassumption. apply OKH. exact OWN2. }
        intros sx3 LB3 ms3 POST. unfold orealloc_post in POST. destruct_exs POST. destruct POST as (-> & CASES3).
        replace (ret_pc (Z_to_bv 64 92120)) with (Z_to_bv 64 92120) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        destruct CASES3 as [(-> & -> & AF & HR3)|(k' & A' & junk & -> & -> & BR & AF & HR3 & BLK3)].
        *
          destruct AF as (MI3 & ST3 & HE3 & [errv3 ERR3] & HPF). rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPF by lia.
          lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR2 ltac:(apply client_range_above; cbn; lia)) as FR3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC2 ltac:(apply MBCR; [lia| auto])) as MBC3.
          assert (OWN3 : mown m3 LB A cap ok bs).
          { destruct ok as [k|]; cbn in OWN2 |- *; [| exact OWN2]. destruct OWN2 as [HIN BLK]. split; [exact HIN|].
            destruct (ai_block_range rsegs AI _ _ _ _ HR2 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
            eapply (heap_pres_rw_cells rsegs AI); [exact HPF| exact BLK|]. eapply client_range_block; [exact HIN| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
          eapply sreach_evt. { eapply (asegE lo j); try eassumption; lia. }
          intros ms' [-> ST4]. apply sreach_ret. unfold membuffer_assign_post.
          do 15 eexists. exists (-104), A, len, cap, ok, bs. split; [reflexivity|].
          split; [exact MI3|]. split; [exact ST4|]. split; [exact HE3|]. split; [eexists; exact ERR3|]. split.
          { eapply (hpx_trans rsegs AI); [exact HP2|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact SUB]. }
          split; [exact HR3|]. split; [exact SUB|]. split; [exact MBC3|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact OWN3|].
          split. { intros b Hb. destruct ok as [k0|]; [exact (proj2 (SUBNE k0 eq_refl b Hb))| exact I]. }
          right. repeat split; reflexivity.
        *
          destruct AF as (MI3 & ST3 & HE3 & [errv3 ERR3] & HPF). rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPF by lia.
          lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
          pose proof BR as BR'. destruct BR' as (U1 & _ & _ & U4 & _).
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR2 ltac:(apply client_range_above; cbn; lia)) as FR3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC2 ltac:(apply MBCR; [lia| auto])) as MBC3.
          pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPF BSRC2 ltac:(rewrite (proj1 (conj LEN I)); exact CRK)) as BSRC3.
          eapply sreach_evt. { eapply (asegH A' n); lia. }
          intros ms' ->.
          eapply CDFC; try eassumption.
          -- eapply (hpx_trans rsegs AI); [exact HP2|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| auto].
          -- eexists; exact ERR3.
          -- lia.
          -- lia.
          -- lia.
      +
        destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        pose proof BR as BR'. destruct BR' as (U1 & _ & _ & U4 & _).
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC1 ltac:(apply MBCR; [lia| auto])) as MBC2.
        pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPF BSRC1 ltac:(rewrite (proj1 (conj LEN I)); exact CRK)) as BSRC2.
        eapply sreach_evt. { eapply (asegG pc A'); lia. }
        intros ms' ->.
        replace (Z.to_nat (nsz + 1)) with (Z.to_nat (nsz + 1)) in BLK2 by reflexivity.
        eapply (CDFC _ _ k' A' nsz); try eassumption.
        * eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| auto].
        * eexists; exact ERR2.
        * lia.
        * lia.
  Qed.
End W.
