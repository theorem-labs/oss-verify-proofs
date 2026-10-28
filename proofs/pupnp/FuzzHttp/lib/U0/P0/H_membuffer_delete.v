(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memmove H_str_alloc H_membuffer_assign HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition membuffer_delete_entry := 0x16a64%Z.
Ltac sstep := step; fix_lit_store.
Ltac mbd_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac mbd_b2z_if := step; mbd_b2z; lit_branch.

Notation DFR m q s2 s1 s0 ra := (rw_cells rsegs m q [C8 s2; C8 s1; C8 s0; C8 ra]).

Definition del_bytes (bs : list byte) (idx num len : Z) : list byte :=
  mm_result bs (Z.to_nat (idx + num)) (Z.to_nat idx) (Z.to_nat (len - idx - num)).

Lemma memmove_call : forall (D SX n U : Z) (us : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  u8arr rsegs m U us -> (8 <= U)%Z ->
  (U <= SX /\ SX + n <= U + Z.of_nat (length us))%Z -> (U <= D /\ D + n <= U + Z.of_nat (length us))%Z ->
  (0 <= n < 2^62)%Z -> (U + Z.of_nat (length us) < 2^64)%Z ->
  mem_inv rsegs m -> a0 = wz D -> a1 = wz SX -> a2 = wz n ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ u8arr rsegs m' U (mm_result us (Z.to_nat (SX - U)) (Z.to_nat (D - U)) (Z.to_nat n)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x244e4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ARR HU HS HD HN HUB MI -> -> ->.
  pose proof (u8arr_bound _ _ _ _ ARR) as UB.
  assert (E0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 SX) = SX) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memmove_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 SX) (Z_to_bv 64 n)); rewrite ?E0, ?E1, ?E2; eauto; lia. }
  intros ms' P. unfold memmove_post in P. rewrite !E0, !E1, !E2 in P. exact P.
Qed.

Definition dsegA_post (lo MB A idx num len cap : Z) (bs : list byte) (ra sp gp tp s0 s1 s2 : word)
    (t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' =>
    (len = 0 /\ exists a0' a1' a2' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
    \/ (exists m' (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (pc nsz : Z),
       (1 <= len)%Z /\
       ms' = MS (mkR x1 (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' (wz MB) (wz nsz) a0' a1' a2' a3' a4' a5' a6' a7'
                     (wz (len - num)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz pc) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + (cap + 1))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ stk rsegs m' lo (bv_unsigned sp + -32)
       /\ DFR m' (bv_unsigned sp + -32) s2 s1 s0 ra
       /\ rw_cells rsegs m' MB (mbuf_cells A len cap)
       /\ rw_cells rsegs m' A [CB (Z.to_nat (cap + 1)) (del_bytes bs idx num len)]
       /\ ( (pc = 0x16b60)
          \/ (pc = 0x1995c /\ x1 = wz 0x16b10 /\ a0' = wz A /\ a1' = wz (nsz + 1) /\ nsz = len - num + 5 /\ nsz < cap /\ 1 <= num) )%Z).

Lemma dsegA : forall (lo MB A idx num len cap : Z) (bs : list byte) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (0 < MB /\ MB + 32 < 2^64)%Z -> (MB mod 8 = 0)%Z ->
  (0 <= idx)%Z -> (0 <= num)%Z -> (idx + num <= len)%Z -> (0 <= len <= cap)%Z -> (cap + 8 < 2^32)%Z ->
  (len >= 1 -> rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs] /\ 16 <= A /\ A + (cap + 1) <= lo /\ (MB + 32 <= A \/ A + (cap + 1) <= MB))%Z ->
  evt rsegs (dsegA_post lo MB A idx num len cap bs ra sp gp tp s0 s1 s2 t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) (wz idx) (wz num) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_delete_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI MBC MBLO MBHI MB8 HI HN HIN HL HC BLKH. unfold membuffer_delete_entry. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (word_lt64 sp) as SPB.
  pose proof (rw_cells_bound rsegs _ _ _ MBC) as MBB. cbn [cells_size csize Nat.add] in MBB.
  destruct (Z.eq_dec len 0) as [L0|L1].
  -
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST. do 5 sstep. zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
    zstep. ub_align. zstep. zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso; lia. }
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold dsegA_post. left. split; [lia|]. eexists _, _, _, _. split; [reflexivity|]. repeat (split; [assumption|]). exact ST.
  - destruct (BLKH ltac:(lia)) as (BLK & A16 & AHI & DJM).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + (cap + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    carve_frame 32%nat ST. do 5 sstep. zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
    zstep. ub_align. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
    zstep. zstep. ub_null. zstep. zstep. zstep. mbd_b2z_if.
    zstep. ub_null. zstep. zstep. mbd_b2z_if.
    zstep. zstep. zstep. zstep. zstep.
    replace (len <? len - (num + idx)) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
    replace (len - (num + idx))%Z with (len - idx - num)%Z by lia.
    replace (num + (A + idx))%Z with (A + idx + num)%Z by lia.
    call (memmove_call (A + idx) (A + idx + num) (len - idx - num) A bs).
    all: side (first [eapply u8arr_of_rw_cells; exact BLK | exact MI | reflexivity | rewrite ?LBS; lia]).
    rename MI0 into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    pose proof (rw_cells_of_u8arr rsegs _ _ _ POST) as BLK2.
    replace (A + idx + num - A)%Z with (idx + num)%Z in BLK2 by lia. replace (A + idx - A)%Z with idx in BLK2 by lia.
    replace (length (mm_result bs (Z.to_nat (idx + num)) (Z.to_nat idx) (Z.to_nat (len - idx - num)))) with (Z.to_nat (cap + 1)) in BLK2.
    2:{ unfold mm_result. rewrite upd_bytes_length; rewrite ?slice_length; rewrite ?LBS; lia. }
    fold (del_bytes bs idx num len) in BLK2. clear POST.
    zstep. zstep. zstep. if_cases K3; zify_cond K3.
    +
      zstep. zstep. if_cases K4; zify_cond K4. 2:{ exfalso; lia. }
      apply evt_done. unfold dsegA_post. right. do 17 eexists. exists 0x16b60%Z, num. split; [lia|]. split; [reflexivity|].
      repeat (split; [eassumption|]). left. reflexivity.
    + zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4.
      * apply evt_done. unfold dsegA_post. right. do 17 eexists. exists 0x16b60%Z, 5%Z. split; [lia|]. split; [reflexivity|].
        repeat (split; [eassumption|]). left. reflexivity.
      * zstep. zstep. zstep. zstep.
        apply evt_done. unfold dsegA_post. right. do 17 eexists. exists 0x1995c%Z, (5 + (len - num))%Z. split; [lia|]. split; [reflexivity|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity; lia.
Qed.

Definition dsegZ_post (lo MB A' nl cap' : Z) (bsF : list byte) (ra sp gp tp s0 s1 s2 : word)
    (s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' MB (mbuf_cells A' nl cap')
    /\ rw_cells rsegs m' A' [CB (Z.to_nat (cap' + 1)) bsF].

Definition nul_at (bs : list byte) (nl : Z) : list byte :=
  firstn (Z.to_nat nl) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (nl + 1)) bs.

Lemma dsegZ : forall (lo MB A' lenX nl cap' : Z) (bs2 : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x9
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  DFR m (bv_unsigned sp + -32) s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A' lenX cap') -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 <= lenX < 2^64)%Z ->
  (0 <= nl <= cap')%Z -> (cap' < 2^32)%Z ->
  rw_cells rsegs m A' [CB (Z.to_nat (cap' + 1)) bs2] -> (8 <= A')%Z -> (A' + (cap' + 1) <= lo)%Z -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB)%Z ->
  evt rsegs (dsegZ_post lo MB A' nl cap' (nul_at bs2 nl) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz MB) x9 a0 a1 a2 a3 a4 a5 a6 a7 (wz nl) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16b60) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI HLX HNL HC BLK A8 AHI DJM. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  assert (LBS : length bs2 = Z.to_nat (cap' + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
  zstep. zstep. sstep. ub_null. zstep. zstep. zstep. mbd_b2z_if. ub_null.

  pose proof BLK as BLK1.
  apply (rw_cells_split_CB rsegs m0 A' [] (Z.to_nat (cap' + 1)) bs2 [] [Z.to_nat nl; 1%nat; Z.to_nat (cap' - nl)]) in BLK1; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK1.
  lazymatch type of BLK1 with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
    destruct (proj1 (rw_cells_app rsegs m0 A' [c1] [c2; c3]) BLK1) as [BLKa BLKc];
    cbn [cells_size csize] in BLKc; rewrite Nat.add_0_r, Z2Nat.id in BLKc by lia end.
  clear BLK1 BLK.
  remember (A' + nl)%Z as V eqn:EV. sstep. subst V.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (BLK : rw_cells rsegs m1 A' [CB (Z.to_nat (cap' + 1)) (nul_at bs2 nl)]).
  { lazymatch type of BLKc with rw_cells _ _ _ [?c2; ?c3] =>
      pose proof (proj2 (rw_cells_app rsegs m1 A' [CB (Z.to_nat nl) (firstn (Z.to_nat nl) bs2)] [c2; c3])) as J2;
      cbn [cells_size csize Nat.add] in J2; rewrite Nat.add_0_r, Z2Nat.id in J2 by lia;
      specialize (J2 (conj BLKa BLKc)); cbn [app] in J2;
      pose proof (rw_cells_merge rsegs m1 A' [] [CB (Z.to_nat nl) (firstn (Z.to_nat nl) bs2); c2; c3] []) as M
    end.
    rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
    specialize (M J2).
    replace (Z.to_nat nl + S (Z.to_nat (cap' - nl) + 0))%nat with (Z.to_nat (cap' + 1)) in M by lia.
    replace (firstn (Z.to_nat (cap' - nl)) (skipn 1 (skipn (Z.to_nat nl) bs2))) with (skipn (Z.to_nat (nl + 1)) bs2) in M.
    2:{ rewrite !skipn_skipn. replace (1 + Z.to_nat nl)%nat with (Z.to_nat (nl + 1)) by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
    rewrite ?app_nil_r in M. exact M. }
  clear BLKa BLKc.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold dsegZ_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. repeat (split; [eassumption|]). exact BLK.
Qed.

Lemma dsegY : forall (lo MB A A' lenX nl cap cap' : Z) (bs2 : list byte) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  DFR m (bv_unsigned sp + -32) s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A lenX cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 <= lenX < 2^64)%Z ->
  (0 <= nl <= cap')%Z -> (cap' < 2^32)%Z -> (0 <= A < 2^64)%Z -> (0 <= cap < 2^64)%Z ->
  rw_cells rsegs m A' [CB (Z.to_nat (cap' + 1)) bs2] -> (8 <= A')%Z -> (A' + (cap' + 1) <= lo)%Z -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB)%Z ->
  evt rsegs (dsegZ_post lo MB A' nl cap' (nul_at bs2 nl) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz MB) (wz cap') (wz A') a1 a2 a3 a4 a5 a6 a7 (wz nl) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16b58) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI HLX HNL HC HA HCA BLK A8 AHI DJM. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  pose proof (rw_cells_bound rsegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
  sstep. sstep.
  eapply evt_cut. { eapply (dsegZ lo MB A' lenX nl cap' bs2); try eassumption; lia. }
  intros ms' P. unfold dsegZ_post in *. destruct_exs P. destruct P as (-> & MU2 & WM2 & P).
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| exact MU2]. } split. { eapply wmono_trans; [exact WM| exact WM2]. } exact P.
Qed.

Lemma dsegG : forall (A' : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  (0 < A' < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x16b58) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16b10) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HA. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K; zify_cond K; [| exfalso; lia]. apply evt_done. reflexivity.
Qed.

Lemma dsegH : forall (A' : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  (0 < A' < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s2 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x16b58) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16b50) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HA. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep. apply evt_done. reflexivity.
Qed.

Lemma dsegF : forall (MB A lenX cap nl : Z) (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m MB (mbuf_cells A lenX cap) -> (0 < MB /\ MB + 32 < 2^64)%Z -> (0 <= nl /\ nl + 1 < 2^63)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x16b50) sp gp tp t0 t1 t2 (wz MB) s1 (wz A) (wz (nl + 1)) a2 a3 a4 a5 a6 a7 (wz nl) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x1995c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz MB) s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz nl) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16b10) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI MBC MBR HN. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. lit_branch. zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma dsegE : forall (lo : Z) ra0 ra sp gp tp t0 t1 t2 s0 s1 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  DFR m (bv_unsigned sp + -32) s2 s1 s0 ra ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs)
                        /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR ra0 (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16b50) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. lit_branch. do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma firstn_nul_at : forall bs nl, (Z.to_nat nl <= length bs)%nat -> (0 <= nl)%Z ->
  firstn (Z.to_nat (nl + 1)) (nul_at bs nl) = firstn (Z.to_nat nl) bs ++ [Z_to_bv 8 0].
Proof.
  intros bs nl H H0. unfold nul_at. rewrite firstn_app, firstn_firstn, firstn_length.
  replace (Init.Nat.min (Z.to_nat (nl + 1)) (Z.to_nat nl)) with (Z.to_nat nl) by lia.
  replace (Init.Nat.min (Z.to_nat nl) (length bs)) with (Z.to_nat nl) by lia.
  replace (Z.to_nat (nl + 1) - Z.to_nat nl)%nat with 1%nat by lia. cbn. reflexivity.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis REALLOCPC : al_realloc_pc L = 0x1995c.
  Notation mown := (mown AI).

  Definition membuffer_delete_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list (block K)) (ok : option K) (MB A len cap idx num lo B : Z) (bs : list byte) (m : mem)
      : ai_PS rsegs AI -> list (block K) -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A' len' cap' : Z) (ok' : option K) (bs' : list byte),
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L) [C4 errv'])
      /\ hpx AI [(MB, MB + 32)] (lb_keep AI ok LB) (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ (forall b, In b (lb_keep AI ok LB) -> In b LB')
      /\ rw_cells rsegs m' MB (mbuf_cells A' len' cap') /\ (0 <= len' <= cap')%Z /\ (cap' < 2^32)%Z /\ (cap' <= cap)%Z
      /\ mown m' LB' A' cap' ok' bs' /\ mfresh AI LB ok ok' A' cap'
      /\ ( (len = 0 /\ A' = A /\ len' = len /\ cap' = cap /\ ok' = ok /\ bs' = bs /\ LB' = LB)
         \/ (1 <= len /\ len' = len - num /\ firstn (Z.to_nat (len' + 1)) bs' = firstn (Z.to_nat len') (del_bytes bs idx num len) ++ [Z_to_bv 8 0])
         \/ (1 <= len /\ 1 <= num /\ len' = len /\ A' = A /\ cap' = cap /\ ok' = ok /\ LB' = LB /\ bs' = del_bytes bs idx num len) )%Z.

  #[using="AC LOK REALLOCPC"] Theorem membuffer_delete_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (ok : option K) (MB idx num A len cap lo B : Z) (bs : list byte) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 32 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> (0 <= len <= cap)%Z -> (cap + 8 < 2^32)%Z -> mown m LB A cap ok bs ->
    mbloc AI (lb_keep AI ok LB) (bv_unsigned sp) B MB 32 -> (MB mod 8 = 0)%Z ->
    (0 <= idx)%Z -> (0 <= num)%Z -> (idx + num <= len)%Z ->
    a0 = wz MB -> a1 = wz idx -> a2 = wz num ->
    SREACH AI (membuffer_delete_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap idx num lo B bs m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_delete_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI MBC HLC HNC OWN MBL MB8 HI HN HIN -> -> ->.
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (SUB : forall b, In b (lb_keep AI ok LB) -> In b LB) by (intros b Hb; eapply lb_keep_sub; exact Hb).
    assert (SUBNE : forall k, ok = Some k -> forall b, In b (lb_keep AI ok LB) -> In b LB /\ b <> (k, A, cap + 1)).
    { intros k -> b Hb. split; [apply SUB; exact Hb|]. cbn in Hb. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl). }
    pose proof (mbloc_lo rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL) as MBLO.
    pose proof (mbloc_pos rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL ltac:(lia)) as MBP.
    pose proof (mbloc_errno rsegs AI _ _ _ _ _ _ _ _ LOK HR SUB MBL ltac:(lia)) as MBE.
    assert (MBB : (MB + 32 <= B)%Z).
    { destruct MBL as [H|(b & Hb & H1 & H2)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). cbn in R4. lia. }
    assert (DJM0 : forall k, ok = Some k -> (MB + 32 <= A \/ A + (cap + 1) <= MB)%Z).
    { intros k Hk. destruct ok as [k0|]; [| discriminate]. cbn in OWN. destruct OWN as [HIN0 _].
      exact (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (k0, A, cap + 1) HR (SUBNE k0 eq_refl) HIN0 MBL ltac:(lia)). }
    assert (MBCR : forall SP' LB' A1 l1 c1, (SP' <= bv_unsigned sp)%Z -> (forall b, In b (lb_keep AI ok LB) -> In b LB') ->
                   client_range AI LB' SP' MB (Z.of_nat (cells_size (mbuf_cells A1 l1 c1)))).
    { intros SP' LB' A1 l1 c1 HS HL. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mbloc_client rsegs AI). eapply (mbloc_weaken rsegs AI); [exact MBL| exact HS| exact HL]. }

    assert (OKS : (1 <= len)%Z -> exists k, ok = Some k).
    { intros H1. destruct ok as [k|]; [exists k; reflexivity|]. cbn in OWN. exfalso. lia. }
    assert (BLKH : (len >= 1 -> rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs] /\ 16 <= A /\ A + (cap + 1) <= lo /\ (MB + 32 <= A \/ A + (cap + 1) <= MB))%Z).
    { intros H1. destruct (OKS ltac:(lia)) as [k Hk]. pose proof (DJM0 k Hk) as DJMk. subst ok. cbn in OWN. destruct OWN as [HINb BLK].
      destruct (ai_block_range rsegs AI s LB m _ HR HINb) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
      split; [exact BLK|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. exact DJMk. }

    eapply sreach_evt. { eapply (dsegA lo MB A idx num len cap bs); try eassumption; lia. }
    intros ms' [(L0 & a0' & a1' & a2' & m1 & -> & MU1 & WM1 & MI1 & ST1)|(m1 & x1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & pc & nsz & L1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1 & BLK1 & CASES)].
    {
      assert (HR1 : RHEAP rsegs AI s LB m1).
      { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      assert (HE1 : RENV rsegs AI m1 B).
      { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ MBC MU1 WM1 ltac:(cbn; lia)) as MBC1.
      assert (OWN1 : mown m1 LB A cap ok bs).
      { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HINb BLK]. split; [exact HINb|].
        destruct (ai_block_range rsegs AI s LB m _ HR HINb) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
        eapply (rw_cells_transport rsegs _ m m1); [exact BLK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. lia. }
      apply sreach_ret. unfold membuffer_delete_post.
      do 16 eexists. exists A, len, cap, ok, bs. split; [reflexivity|].
      split; [exact MI1|]. split; [exact ST1|]. split; [exact HE1|]. split; [eexists; exact ERR1|]. split.
      { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      split; [exact HR1|]. split; [exact SUB|]. split; [exact MBC1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact OWN1|].
      split. { intros b Hb. destruct ok as [k0|]; [| exact I]. cbn in Hb. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl). }
      left. repeat split; first [reflexivity| lia]. }

    destruct (OKS L1) as [k ->]. cbn in OWN. destruct OWN as [HINb BLK]. cbn [lb_keep] in *.
    destruct (ai_block_range rsegs AI s LB m _ HR HINb) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
    pose proof (SUBNE k eq_refl) as SUBK. cbn [lb_keep] in SUBK.
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor. { left. cbn. lia. } constructor; [| constructor].
      right; right; right. exists (k, A, cap + 1). split; [exact HINb|]. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor. { left. cbn. lia. } constructor; [| constructor].
      right; right; right. exists (k, A, cap + 1). split; [exact HINb|]. cbn. lia. }
    pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR HINb) as DE. cbn in DE.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    assert (HP1 : hpx AI [(MB, MB + 32)]%Z (lb_remove (ai_K_eqb rsegs AI) k LB) (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU1| exact WM1|]. constructor. { left. cbn. lia. } constructor; [| constructor].
      right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact HINb| exact SUBK| lia| cbn; lia]. }
    clear MU1 WM1 HE ERR MI ST BLKH OKS SUBNE.

    assert (FIN : forall sx LBx m2 m3 (A' cap' : Z) (kx : K) (bs2 : list byte)
                   (t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
      hpx AI [(MB, MB + 32)]%Z (lb_remove (ai_K_eqb rsegs AI) k LB) (bv_unsigned sp) m m2 ->
      RHEAP rsegs AI sx LBx m2 -> (forall b, In b (lb_remove (ai_K_eqb rsegs AI) k LB) -> In b LBx /\ b <> (kx, A', cap' + 1)) ->
      In (kx, A', cap' + 1) LBx ->
      RENV rsegs AI m2 B -> (exists e, rw_cells rsegs m2 (al_errno L) [C4 e]) ->
      (len - num <= cap')%Z -> (cap' < 2^32)%Z -> (cap' <= cap)%Z -> (Z.to_nat (len - num) <= length bs2)%nat ->
      firstn (Z.to_nat (len - num)) bs2 = firstn (Z.to_nat (len - num)) (del_bytes bs idx num len) ->
      munch [(bv_unsigned sp - 32, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m2 m3 -> wmono rsegs m2 m3 ->
      mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp) ->
      rw_cells rsegs m3 MB (mbuf_cells A' (len - num) cap') ->
      rw_cells rsegs m3 A' [CB (Z.to_nat (cap' + 1)) (nul_at bs2 (len - num))] ->
      membuffer_delete_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (Some k) MB A len cap idx num lo B bs m sx LBx
        (MS (mkR ra sp gp (wz (al_tp L)) t0_ t1_ t2_ s0 s1 a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
            F (ret_pc ra) fc None m3 (seg_rom rsegs))).
    { intros until t6_. intros HP2 HR2 SUB2 HIN2 HE2 [e2 ERR2] HNC' HC' HCB LB2 PFX MU3 WM3 MI3 ST3 MBC3 BLK3.
      pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR2 HIN2) as DE2. cbn in DE2.
      pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
      unfold membuffer_delete_post. cbn [lb_keep].
      do 16 eexists. exists A', (len - num)%Z, cap', (Some kx), (nul_at bs2 (len - num)).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor. { eapply (mbloc_ef rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb]. } constructor; [| constructor].
        right; right; right. exists (kx, A', cap' + 1). split; [exact HIN2|]. cbn. lia. }
      split; [eexists; exact ERR3|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; apply SUB2; exact Hb| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor. { right; right. cbn. lia. } constructor; [| constructor].
        right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR2| exact HIN2| exact SUB2| lia| cbn; lia]. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor. { eapply (mbloc_hf rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb]. } constructor; [| constructor].
        right; right; right. exists (kx, A', cap' + 1). split; [exact HIN2|]. cbn. lia. }
      split; [intros b Hb; apply SUB2; exact Hb|]. split; [exact MBC3|]. split; [lia|]. split; [lia|]. split; [exact HCB|].
      split. { cbn. split; [exact HIN2| exact BLK3]. }
      split. { intros b Hb. exact (proj2 (SUB2 b Hb)). }
      right; left. split; [lia|]. split; [reflexivity|]. rewrite <- PFX. apply firstn_nul_at; lia. }
    destruct CASES as [->|(-> & -> & -> & -> & NS1 & NS2 & NUM1)].
    -
      pose proof (rw_cells_bound rsegs _ _ _ BLK1) as AB. cbn [cells_size csize Nat.add] in AB.
      assert (LBS1 : length (del_bytes bs idx num len) = Z.to_nat (cap + 1)) by (destruct BLK1 as [[W _] _]; cbn in W; LiaTuning.ctauto).
      pose proof (DJM0 k eq_refl) as DJM.
      eapply sreach_evt. { eapply (dsegZ lo MB A len (len - num) cap (del_bytes bs idx num len)); try eassumption; try LiaTuning.alia. }
      intros ms' P. unfold dsegZ_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & BLK3).
      apply sreach_ret. eapply (FIN s LB m1 _ A cap k); try eassumption; try LiaTuning.alia.
      all: first [eexists; exact ERR1 | rewrite LBS1; lia | reflexivity | idtac].
    -

      assert (CS : forall sx m2 (k' : K) (A' cap' : Z) (bs2 : list byte) (x1 t0_ t1_ t2_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
        hpx AI [(MB, MB + 32)]%Z (lb_remove (ai_K_eqb rsegs AI) k LB) (bv_unsigned sp) m m2 ->
        RHEAP rsegs AI sx ((k', A', cap' + 1) :: lb_remove (ai_K_eqb rsegs AI) k LB) m2 -> block_range AI A' (cap' + 1) ->
        RENV rsegs AI m2 B -> (exists e, rw_cells rsegs m2 (al_errno L) [C4 e]) -> mem_inv rsegs m2 ->
        stk rsegs m2 lo (bv_unsigned sp + -32) -> DFR m2 (bv_unsigned sp + -32) s2 s1 s0 ra ->
        rw_cells rsegs m2 MB (mbuf_cells A len cap) ->
        rw_cells rsegs m2 A' [CB (Z.to_nat (cap' + 1)) bs2] -> firstn (Z.to_nat (len - num)) bs2 = firstn (Z.to_nat (len - num)) (del_bytes bs idx num len) ->
        (len - num <= cap')%Z -> (cap' < 2^32)%Z -> (cap' <= cap)%Z ->
        SREACH AI (membuffer_delete_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (Some k) MB A len cap idx num lo B bs m)
          (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp (wz (al_tp L)) t0_ t1_ t2_ (wz MB) (wz cap') (wz A') a1_ a2_ a3_ a4_ a5_ a6_ a7_ (wz (len - num)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
              F (wz 0x16b58) fc None m2 (seg_rom rsegs)) sx ((k', A', cap' + 1) :: lb_remove (ai_K_eqb rsegs AI) k LB)).
      { intros until t6_. intros HP2 HR2 BR2 HE2 ERR2 MI2 ST2 FR2 MBC2 BLK2 PFX2 NC' HC' HCB.
        destruct BR2 as (U1 & U2 & U3 & U4 & U5).
        assert (NEW : In (k', A', cap' + 1) ((k', A', cap' + 1) :: lb_remove (ai_K_eqb rsegs AI) k LB)) by (left; reflexivity).
        assert (SUB2 : forall b, In b (lb_remove (ai_K_eqb rsegs AI) k LB) -> In b ((k', A', cap' + 1) :: lb_remove (ai_K_eqb rsegs AI) k LB) /\ b <> (k', A', cap' + 1)).
        { intros b Hb. split; [right; exact Hb|]. intros ->.
          pose proof (ai_blocks_nodup rsegs AI _ _ _ HR2) as ND. cbn in ND. inversion ND as [|xk xl NI ND']; subst.
          apply NI. apply base.list_elem_of_In. exact (in_map blk_id _ _ Hb). }
        assert (LBS2 : length bs2 = Z.to_nat (cap' + 1)) by (destruct BLK2 as [[W _] _]; cbn in W; LiaTuning.ctauto).
        pose proof (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (k', A', cap' + 1) HR2 SUB2 NEW MBL ltac:(lia)) as DJM. cbn in DJM.
        eapply sreach_evt. { eapply (dsegY lo MB A A' len (len - num) cap cap' bs2); try eassumption; try LiaTuning.alia. all: Z.div_mod_to_equations; lia. }
        intros ms' P. unfold dsegZ_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & BLK3).
        apply sreach_ret. eapply (FIN sx _ m2 _ A' cap' k' bs2); try eassumption; try LiaTuning.alia. all: rewrite LBS2; lia. }

      assert (LBS1 : length (del_bytes bs idx num len) = Z.to_nat (cap + 1)) by (destruct BLK1 as [[W _] _]; cbn in W; LiaTuning.ctauto).
      assert (PFXR : forall nsz' junk, (len - num <= nsz')%Z ->
        firstn (Z.to_nat (len - num)) (firstn (Z.to_nat (Z.min (nsz' + 1) (cap + 1))) (del_bytes bs idx num len) ++ junk) = firstn (Z.to_nat (len - num)) (del_bytes bs idx num len)).
      { intros nsz' junk Hn.
        rewrite firstn_app, firstn_firstn, firstn_length. replace (Init.Nat.min (Z.to_nat (len - num)) (Z.to_nat (Z.min (nsz' + 1) (cap + 1)))) with (Z.to_nat (len - num)) by lia.
        replace (Z.to_nat (len - num) - Init.Nat.min (Z.to_nat (Z.min (nsz' + 1) (cap + 1))) (length (del_bytes bs idx num len)))%nat with 0%nat by lia. cbn. apply app_nil_r. }
      assert (CRK : forall LBy, client_range AI LBy (bv_unsigned sp + -32) (bv_unsigned sp + -32) 32) by (intros LBy; apply client_range_above; lia).

      eapply sreach_bind.
      { rewrite <- REALLOCPC. eapply (orealloc_spec rsegs AI AC) with (lo := lo) (B := B) (ok := Some k); try eassumption; try reflexivity;
          rewrite ?unsigned_lit by lia; try lia; try eassumption. cbn. split; [exact HINb| exact BLK1]. }
      intros sx2 LB2 ms2 POST. unfold orealloc_post in POST. destruct_exs POST. destruct POST as (-> & CASES2).
      replace (ret_pc (Z_to_bv 64 0x16b10)) with (Z_to_bv 64 0x16b10) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [lb_keep] in CASES2.
      destruct CASES2 as [(-> & -> & AF & HR2)|(k' & A' & junk & -> & -> & BR & AF & HR2 & BLK2)].
      +
        destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC1 ltac:(apply MBCR; [lia| auto])) as MBC2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF BLK1 ltac:(eapply client_range_block; [exact HINb| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as BLK2.
        assert (HP2 : hpx AI [(MB, MB + 32)]%Z (lb_remove (ai_K_eqb rsegs AI) k LB) (bv_unsigned sp) m m2).
        { eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact SUB]. }
        eapply sreach_evt. { eapply (dsegF MB A len cap (len - num)); try eassumption; lia. }
        intros ms' ->.
        eapply sreach_bind.
        { rewrite <- REALLOCPC. eapply (orealloc_spec rsegs AI AC) with (lo := lo) (B := B) (ok := Some k); try eassumption; try reflexivity;
            rewrite ?unsigned_lit by lia; try lia; try eassumption. cbn. split; [exact HINb| exact BLK2]. }
        intros sx3 LB3 ms3 POST. unfold orealloc_post in POST. destruct_exs POST. destruct POST as (-> & CASES3).
        replace (ret_pc (Z_to_bv 64 0x16b50)) with (Z_to_bv 64 0x16b50) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        cbn [lb_keep] in CASES3.
        destruct CASES3 as [(-> & -> & AF & HR3)|(k' & A' & junk & -> & -> & BR & AF & HR3 & BLK3)].
        *
          destruct AF as (MI3 & ST3 & HE3 & [errv3 ERR3] & HPF2). rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPF2 by lia.
          lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 FR2 ltac:(apply client_range_above; cbn; lia)) as FR3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 MBC2 ltac:(apply MBCR; [lia| auto])) as MBC3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 BLK2 ltac:(eapply client_range_block; [exact HINb| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as BLK3.
          eapply sreach_evt. { eapply (dsegE lo); try eassumption; lia. }
          intros ms' [-> ST4]. apply sreach_ret. unfold membuffer_delete_post. cbn [lb_keep].
          do 16 eexists. exists A, len, cap, (Some k), (del_bytes bs idx num len). split; [reflexivity|].
          split; [exact MI3|]. split; [exact ST4|]. split; [exact HE3|]. split; [eexists; exact ERR3|]. split.
          { eapply (hpx_trans rsegs AI); [exact HP2|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF2| lia| exact SUB]. }
          split; [exact HR3|]. split; [exact SUB|]. split; [exact MBC3|]. split; [lia|]. split; [lia|]. split; [lia|]. split. { cbn. split; [exact HINb| exact BLK3]. }
          split. { intros b Hb. cbn in Hb |- *. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl). }
          right; right. repeat split; first [reflexivity| lia].
        *
          destruct AF as (MI3 & ST3 & HE3 & [errv3 ERR3] & HPF2). rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPF2 by lia.
          lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
          pose proof BR as BR'. destruct BR' as (U1 & _ & _ & U4 & _).
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 FR2 ltac:(apply client_range_above; cbn; lia)) as FR3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 MBC2 ltac:(apply MBCR; [lia| auto])) as MBC3.
          eapply sreach_evt. { eapply (dsegH A'); lia. }
          intros ms' ->.
          replace (len - num + 1)%Z with (len - num + 1)%Z in BLK3 by lia.
          eapply (CS _ _ k' A' (len - num)); try eassumption; try LiaTuning.alia.
          -- eapply (hpx_trans rsegs AI); [exact HP2|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF2| lia| auto].
          -- eexists; exact ERR3.
          -- apply PFXR. lia.
      +
        destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        pose proof BR as BR'. destruct BR' as (U1 & _ & _ & U4 & _).
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC1 ltac:(apply MBCR; [lia| auto])) as MBC2.
        eapply sreach_evt. { eapply (dsegG A'); lia. }
        intros ms' ->.
        eapply (CS _ _ k' A' nsz); try eassumption; try LiaTuning.alia.
        * eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| auto].
        * eexists; exact ERR2.
        * apply PFXR. lia.
  Qed.
End W.
