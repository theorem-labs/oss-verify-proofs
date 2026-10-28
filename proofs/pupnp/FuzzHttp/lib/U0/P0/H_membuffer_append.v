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
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memmove H_str_alloc H_membuffer_assign HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition membuffer_append_entry := 0x1684c%Z.
Definition membuffer_insert_entry := 0x16864%Z.
Lemma firstn_pref3 : forall {X} (a b : list X) z rest k, k = (length a + length b + 1)%nat ->
  firstn k (a ++ b ++ [z] ++ rest) = a ++ b ++ [z].
Proof.
  intros X a b z rest k ->.
  rewrite firstn_app. rewrite firstn_all2 by lia. f_equal.
  rewrite firstn_app. rewrite firstn_all2 by lia. f_equal.
  replace (length a + length b + 1 - length a - length b)%nat with 1%nat by lia. reflexivity.
Qed.
Ltac sstep := step; fix_lit_store.
Ltac mb_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac mb_b2z_br := mb_b2z; lit_branch.

Notation IFR m q j s5 s4 s3 s2 s1 s0 ra := (rw_cells rsegs m q [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition isegA_post (lo MB SRC n A len cap : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 : word)
    (t0 t1 t2 a4 a5 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' =>
    (n = 0 /\ exists m' a2' a4' a6',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz SRC) a2' (wz len) a4' a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ stk rsegs m' lo (bv_unsigned sp)
       /\ rw_cells rsegs m' MB (mbuf_cells A len cap))
    \/ (exists m' j (x1 a0' a1' a4' a6' x19 x20 : word) (pc nsz : Z),
       ms' = MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz MB) (wz n) a0' a1' (wz len) (wz len) a4' a5 a6' a7
                     (wz (len + n)) x19 x20 (wz nsz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz pc) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ stk rsegs m' lo (bv_unsigned sp + -64)
       /\ IFR m' (bv_unsigned sp + -64) j s5 s4 s3 s2 s1 s0 ra
       /\ rw_cells rsegs m' MB (mbuf_cells A len cap)
       /\ (1 <= n)%Z
       /\ ( (pc = 0x16940 /\ nsz = cap /\ a1' = wz SRC /\ x1 = ra /\ len + n <= cap)
          \/ (pc = 0x1995c /\ x1 = wz 0x16918 /\ x19 = wz len /\ x20 = wz SRC /\ a0' = wz A /\ a1' = wz (nsz + 1)
              /\ len + n <= nsz /\ nsz <= n + cap + 5 /\ cap < len + n) )%Z).

Lemma isegA : forall (lo MB SRC n A len cap : Z) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 < MB)%Z -> (MB mod 8 = 0)%Z ->
  (0 < SRC < 2^64)%Z -> (0 <= n)%Z -> (0 <= len <= cap)%Z -> (cap + n + 8 < 2^32)%Z -> (0 <= A < 2^64)%Z ->
  evt rsegs (isegA_post lo MB SRC n A len cap ra sp gp tp s0 s1 s2 s3 s4 s5 t0 t1 t2 a4 a5 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz n) (wz len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_insert_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI MBC MBLO MBHI MBNZ MBAL HS HN HL HC HA. unfold membuffer_insert_entry. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  carve_frame 64%nat ST.
  do 8 sstep. ub_null. zstep. ub_align.
  zstep. zstep. zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
  zstep. if_cases K2; zify_cond K2.
  { do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold isegA_post. left. split; [lia|]. eexists _, _, _, _. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption. }
  zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso; lia. }
  zstep. zstep. if_cases K4; zify_cond K4.
  -
    apply evt_done. unfold isegA_post. right. eexists _, _, _, _, _, _, _, _, _, 0x16940, cap. split; [reflexivity|].
    repeat (split; [eassumption|]). split; [lia|]. left. repeat split; try reflexivity; lia.
  - zstep. zstep. if_cases K5; zify_cond K5.
    +   zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. unfold isegA_post. right. eexists _, _, _, _, _, _, _, _, _, 0x1995c, (5 + cap)%Z. split; [reflexivity|].
      repeat (split; [eassumption|]). split; [lia|]. right. repeat split; try reflexivity; lia.
    + zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. unfold isegA_post. right. eexists _, _, _, _, _, _, _, _, _, 0x1995c, (n + cap)%Z. split; [reflexivity|].
      repeat (split; [eassumption|]). split; [lia|]. right. repeat split; try reflexivity; lia.
Qed.

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

Definition isegM_post (lo MB n A' len cap' : Z) (bsF : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 : word)
    (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' MB (mbuf_cells A' (len + n) cap')
    /\ rw_cells rsegs m' A' [CB (Z.to_nat (cap' + 1)) bsF].

Lemma isegM : forall (lo MB SRC n A' len cap' : Z) (src bs j : list byte) x1 ra sp gp tp t0 t1 t2 s0 s1 x8 x9 a4 a5 a6 a7 x18 x19 x20 x21 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -64) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  IFR m (bv_unsigned sp + -64) j s5 s4 s3 s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A' len cap') -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z ->
  bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (1 <= n)%Z -> (0 <= len)%Z -> (len + n <= cap')%Z -> (cap' < 2^32)%Z ->
  rw_cells rsegs m A' [CB (Z.to_nat (cap' + 1)) bs] -> (8 <= A')%Z -> (A' + (cap' + 1) <= lo)%Z -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB)%Z ->
  (SRC + n <= A' \/ A' + (cap' + 1) <= SRC)%Z -> (SRC + n <= bv_unsigned sp - 64)%Z -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
  evt rsegs (isegM_post lo MB n A' len cap' (firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs)
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz MB) (wz n) x8 (wz SRC) x9 (wz len) a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16940) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI BSRC LEN HN HL0 HLN HC BLK A8 AHI DJM DJ DJ2 DJS. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.
  assert (LBS : length bs = Z.to_nat (cap' + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
  zstep. zstep. zstep. step. ubr.
  zstep. zstep. zstep. step. mb_b2z_br.
  zstep. step. ubr.
  zstep. zstep. step. mb_b2z_br.
  zstep. zstep. zstep. zstep.
  replace (len - len)%Z with 0%Z by lia.
  call (memmove_call (n + (A' + len)) (A' + len) 0 A' bs).
  all: side (first [eapply u8arr_of_rw_cells; exact BLK | exact MI | reflexivity | rewrite ?LBS; lia]).
  rename MI0 into MI. cbn [Z.to_nat] in POST. unfold mm_result in POST. rewrite slice_0, upd_bytes_nil in POST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (rw_cells_of_u8arr rsegs _ _ _ POST) as BLK1. rewrite LBS in BLK1. clear POST.

  apply (rw_cells_split_CB rsegs m1 A' [] (Z.to_nat (cap' + 1)) bs [] [Z.to_nat len; Z.to_nat n; 1%nat; Z.to_nat (cap' - len - n)]) in BLK1; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK1.
  lazymatch type of BLK1 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4] =>
    destruct (proj1 (rw_cells_app rsegs m1 A' [c1] [c2; c3; c4]) BLK1) as [BLKa BLKb];
    cbn [cells_size csize] in BLKb; rewrite Nat.add_0_r, Z2Nat.id in BLKb by lia;
    destruct (proj1 (rw_cells_app rsegs m1 (A' + len) [c2] [c3; c4]) BLKb) as [BLKn BLKc];
    cbn [cells_size csize] in BLKc; rewrite Nat.add_0_r, Z2Nat.id in BLKc by lia end.
  clear BLK1 BLKb.
  zstep. zstep. step. ubr.
  zstep. zstep. zstep. step. mb_b2z_br.
  zstep. zstep. zstep.
  rewrite (Z.add_comm len A').
  call (memcpy_call (A' + len) SRC n src).
  all: side (first [exact BSRC | exact BLKn | exact MI | reflexivity | lia]).
  zstep. zstep. zstep. zstep. sstep.
  step. ubr.
  zstep. zstep. zstep. step. mb_b2z_br.
  step. ubr.
  zstep.
  replace (A' + (len + n))%Z with (A' + len + n)%Z by lia.
  remember (A' + len + n)%Z as V eqn:EV. sstep. subst V.
  assert (BLK : rw_cells rsegs m1 A' [CB (Z.to_nat (cap' + 1)) (firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs)]).
  { lazymatch type of BLKc with rw_cells _ _ _ [?c3; ?c4] =>
      pose proof (proj2 (rw_cells_app rsegs m1 (A' + len) [CB (Z.to_nat n) src] [c3; c4])) as J1;
      cbn [cells_size csize Nat.add] in J1; rewrite Nat.add_0_r, Z2Nat.id in J1 by lia;
      specialize (J1 (conj PC BLKc)); cbn [app] in J1;
      pose proof (proj2 (rw_cells_app rsegs m1 A' [CB (Z.to_nat len) (firstn (Z.to_nat len) bs)] [CB (Z.to_nat n) src; c3; c4])) as J2;
      cbn [cells_size csize Nat.add] in J2; rewrite Nat.add_0_r, Z2Nat.id in J2 by lia;
      specialize (J2 (conj BLKa J1)); cbn [app] in J2;
      pose proof (rw_cells_merge rsegs m1 A' [] [CB (Z.to_nat len) (firstn (Z.to_nat len) bs); CB (Z.to_nat n) src; c3; c4] []) as M
    end.
    rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
    specialize (M J2).
    replace (Z.to_nat len + (Z.to_nat n + S (Z.to_nat (cap' - len - n) + 0)))%nat with (Z.to_nat (cap' + 1)) in M by lia.
    replace (firstn (Z.to_nat (cap' - len - n)) (skipn 1 (skipn (Z.to_nat n) (skipn (Z.to_nat len) bs)))) with (skipn (Z.to_nat (len + n + 1)) bs) in M.
    2:{ rewrite !skipn_skipn. replace (1 + Z.to_nat n + Z.to_nat len)%nat with (Z.to_nat (len + n + 1)) by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
    rewrite app_nil_r in M. exact M. }
  clear PC BLKa BLKc.
  do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold isegM_post, mbuf_cells, MEMBUF_DEF_SIZE_INC. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. repeat (split; [eassumption|]). exact BLK.
Qed.

Lemma isegS : forall (lo MB SRC n A A' len cap cap' : Z) (src bs j : list byte) x1 ra sp gp tp t0 t1 t2 s0 s1 x8 x10 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -64) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  IFR m (bv_unsigned sp + -64) j s5 s4 s3 s2 s1 s0 ra ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z ->
  bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (1 <= n)%Z -> (0 <= len)%Z -> (len + n <= cap')%Z -> (cap' < 2^32)%Z ->
  rw_cells rsegs m A' [CB (Z.to_nat (cap' + 1)) bs] -> (8 <= A')%Z -> (A' + (cap' + 1) <= lo)%Z -> (MB + 32 <= A' \/ A' + (cap' + 1) <= MB)%Z ->
  (SRC + n <= A' \/ A' + (cap' + 1) <= SRC)%Z -> (SRC + n <= bv_unsigned sp - 64)%Z -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
  evt rsegs (isegM_post lo MB n A' len cap' (firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs)
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz MB) (wz n) (wz A') x10 x12 x13 a4 a5 a6 a7 x8 (wz len) (wz SRC) (wz cap') s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16930) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBLO MBHI BSRC LEN HN HL0 HLN HC BLK A8 AHI DJM DJ DJ2 DJS. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.
  pose proof (rw_cells_bound rsegs _ _ _ BLK) as AB. cbn [cells_size csize Nat.add] in AB.
  sstep. sstep. zstep. zstep.
  eapply evt_cut. { eapply (isegM lo MB SRC n A' len cap' src bs j); try eassumption; lia. }
  intros ms' P. unfold isegM_post in *. destruct_exs P. destruct P as (-> & MU2 & WM2 & P).
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| exact MU2]. } split. { eapply wmono_trans; [exact WM| exact WM2]. } exact P.
Qed.

Lemma isegE : forall (lo : Z) (j : list byte) x1 ra sp gp tp t0 t1 t2 s0 s1 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -64) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  IFR m (bv_unsigned sp + -64) j s5 s4 s3 s2 s1 s0 ra ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (-104)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs)
                       /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16928) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. lit_branch. zstep. zstep. do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Lemma isegF : forall (MB A len0 cap newlen : Z) (ra sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m MB (mbuf_cells A len0 cap) -> (0 < MB /\ MB + 32 < 2^64)%Z -> (0 <= newlen /\ newlen + 1 < 2^63)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x16928) sp gp tp t0 t1 t2 (wz MB) x9 (wz A) (wz (newlen + 1)) a2 a3 a4 a5 a6 a7 (wz newlen) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x1995c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz MB) x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz newlen) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16918) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI MBC MBR HN. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. lit_branch. zstep. zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma isegG : forall (A' : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  (0 < A' < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x16930) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16918) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HA. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K; zify_cond K; [| exfalso; lia]. apply evt_done. reflexivity.
Qed.

Lemma isegH : forall (A' : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  (0 < A' < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x16930) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16928) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HA. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep. apply evt_done. reflexivity.
Qed.

Lemma iseg58 : forall (MB A len cap : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m MB (mbuf_cells A len cap) -> (0 < MB /\ MB + 32 < 2^64)%Z -> (0 <= len < 2^64)%Z -> (MB mod 8 = 0)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) a1 a2 (wz len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_insert_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_append_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI MBC MBR HL MBAL. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, membuffer_append_entry, membuffer_insert_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  ub_null. ub_align. zstep. zstep. apply evt_done. reflexivity.
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

  Definition membuffer_append_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
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
      /\ mown m' LB' A' cap' ok' bs' /\ mfresh AI LB ok ok' A' cap'
      /\ firstn (Z.to_nat len) bs' = firstn (Z.to_nat len) bs
      /\ ( (r = 0 /\ len' = len + n /\ (n >= 1 -> firstn (Z.to_nat (len' + 1)) bs' = firstn (Z.to_nat len) bs ++ src ++ [Z_to_bv 8 0]))
         \/ (r = -104 /\ A' = A /\ len' = len /\ cap' = cap /\ ok' = ok /\ bs' = bs /\ LB' = LB) )%Z.

  #[using="AC LOK REALLOCPC"] Theorem membuffer_insert_end_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (ok : option K) (MB SRC n A len cap lo B : Z) (src bs : list byte) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 64 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> (0 <= len <= cap)%Z -> (cap + n + 8 < 2^32)%Z -> mown m LB A cap ok bs ->
    (ok <> None -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)) ->
    mbloc AI (lb_keep AI ok LB) (bv_unsigned sp) B MB 32 -> (MB mod 8 = 0)%Z ->
    bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (0 < SRC)%Z -> (SRC + n <= alloc_ceiling)%Z ->
    src_ok AI (lb_keep AI ok LB) (bv_unsigned sp) SRC n src -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
    a0 = wz MB -> a1 = wz SRC -> a2 = wz n -> a3 = wz len ->
    SREACH AI (membuffer_append_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_insert_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI MBC HLC HNC OWN NUL MBL MBAL BSRC LEN S0 SHI CR DJS -> -> -> ->.
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
    assert (MBCR : forall SP' LB' A1 l1 c1, (SP' <= bv_unsigned sp)%Z -> (forall b, In b (lb_keep AI ok LB) -> In b LB') ->
                   client_range AI LB' SP' MB (Z.of_nat (cells_size (mbuf_cells A1 l1 c1)))).
    { intros SP' LB' A1 l1 c1 HS HL. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mbloc_client rsegs AI). eapply (mbloc_weaken rsegs AI); [exact MBL| exact HS| exact HL]. }
    assert (ARNG : (0 <= A < 2^64)%Z /\ (ok <> None -> 16 <= A)%Z).
    { destruct ok as [k|]; cbn in OWN.
      - destruct OWN as [HIN _]. destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
        split; [lia|]. intros _. Z.div_mod_to_equations. lia.
      - split; [lia|]. intros X; exfalso; apply X; reflexivity. }
    destruct ARNG as [ARNG A16].

    eapply sreach_evt. { eapply (isegA lo MB SRC n A len cap); try eassumption; lia. }
    intros ms' [(N0 & m1 & a2' & a4' & a6' & -> & MU1 & WM1 & MI1 & ST1 & MBC1)|(m1 & j & x1 & a0' & a1' & a4' & a6' & x19 & x20 & pc & nsz & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1 & N1 & CASES)].
    {
      assert (HR1 : RHEAP rsegs AI s LB m1).
      { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      assert (HE1 : RENV rsegs AI m1 B).
      { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
      assert (OWN1 : mown m1 LB A cap ok bs).
      { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
        destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
        eapply (rw_cells_transport rsegs _ m m1); [exact BLK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. lia. }
      assert (HP1 : hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m1).
      { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      apply sreach_ret. unfold membuffer_append_post.
      do 15 eexists. exists 0, A, len, cap, ok, bs. split; [subst n; reflexivity|].
      split; [exact MI1|]. split; [exact ST1|]. split; [exact HE1|]. split; [eexists; exact ERR1|]. split; [exact HP1|].
      split; [exact HR1|]. split; [exact SUB|]. split; [exact MBC1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact OWN1|].
      split. { intros b Hb. destruct ok as [k0|]; [| exact I]. cbn in Hb. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl). }
      split; [reflexivity|]. left. split; [reflexivity|]. split; [lia|]. intros; lia. }
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

    assert (FIN : forall sx LBx m2 m3 (A' cap' : Z) (kx : K) (bs2 : list byte)
                   (t0' t1' t2' a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
      hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m2 ->
      RHEAP rsegs AI sx LBx m2 -> (forall b, In b (lb_keep AI ok LB) -> In b LBx /\ b <> (kx, A', cap' + 1)) ->
      In (kx, A', cap' + 1) LBx ->
      RENV rsegs AI m2 B -> (exists e, rw_cells rsegs m2 (al_errno L) [C4 e]) ->
      (len + n <= cap')%Z -> (cap' < 2^32)%Z -> (cap' <= cap + n + 5)%Z -> firstn (Z.to_nat len) bs2 = firstn (Z.to_nat len) bs ->
      munch [(bv_unsigned sp - 64, bv_unsigned sp); (MB, MB + 32); (A', A' + (cap' + 1))]%Z m2 m3 -> wmono rsegs m2 m3 ->
      mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp) ->
      rw_cells rsegs m3 MB (mbuf_cells A' (len + n) cap') ->
      rw_cells rsegs m3 A' [CB (Z.to_nat (cap' + 1)) (firstn (Z.to_nat len) bs2 ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs2)] ->
      membuffer_append_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m sx LBx
        (MS (mkR ra sp gp (wz (al_tp L)) t0' t1' t2' s0 s1 (wz 0) a1_ a2_ a3_ a4_ a5_ a6_ a7_ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
            F (ret_pc ra) fc None m3 (seg_rom rsegs))).
    { intros until t6_. intros HP2 HR2 SUB2 HIN HE2 [e2 ERR2] HNC' HC' HCB PFX MU3 WM3 MI3 ST3 MBC3 BLK3.
      assert (LBS2 : (Z.to_nat len <= length bs2)%nat).
      { apply (f_equal (@length byte)) in PFX. rewrite !firstn_length in PFX.
        destruct ok as [k|]; cbn in OWN1.
        - destruct OWN1 as [_ BLK]. destruct BLK as [[W _] _]. cbn in W. destruct W as [W _]. lia.
        - destruct OWN1 as (_ & -> & ->). cbn in PFX |- *. lia. }
      pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR2 HIN) as DE. cbn in DE.
      pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
      unfold membuffer_append_post.
      do 15 eexists. exists 0, A', (len + n)%Z, cap', (Some kx), (firstn (Z.to_nat len) bs2 ++ src ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (len + n + 1)) bs2).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor. { eapply (mbloc_ef rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb]. } constructor; [| constructor].
        right; right; right. exists (kx, A', cap' + 1). split; [exact HIN|]. cbn. lia. }
      split; [eexists; exact ERR3|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; apply SUB2; exact Hb| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor. { right; right. cbn. lia. } constructor; [| constructor].
        right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR2| exact HIN| exact SUB2| lia| cbn; lia]. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor. { eapply (mbloc_hf rsegs AI); [exact MBL| lia| intros b Hb; apply SUB2; exact Hb]. } constructor; [| constructor].
        right; right; right. exists (kx, A', cap' + 1). split; [exact HIN|]. cbn. lia. }
      split; [intros b Hb; apply SUB2; exact Hb|]. split; [exact MBC3|]. split; [lia|]. split; [lia|]. split; [exact HCB|].
      split. { cbn. split; [exact HIN| exact BLK3]. }
      split. { intros b Hb. exact (proj2 (SUB2 b Hb)). }
      split. { rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length, Nat.min_l, Nat.sub_diag by lia. cbn. rewrite app_nil_r. exact PFX. }
      left. split; [reflexivity|]. split; [reflexivity|]. intros _.
      rewrite <- PFX. apply firstn_pref3. rewrite firstn_length. lia. }

    assert (CRK : src_ok AI (lb_keep AI ok LB) (bv_unsigned sp + -64) SRC n src).
    { eapply (src_ok_weaken rsegs AI); [exact CR| lia| auto]. }
    assert (SUBNE : forall k, ok = Some k -> forall b, In b (lb_keep AI ok LB) -> In b LB /\ b <> (k, A, cap + 1)).
    { intros k -> b Hb. split; [apply SUB; exact Hb|]. cbn in Hb. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb eq_refl). }

    assert (DJOF : forall sx LBx mx (kx : K) (A' cap' : Z),
      RHEAP rsegs AI sx LBx mx -> In (kx, A', cap' + 1) LBx ->
      (forall b, In b (lb_keep AI ok LB) -> In b LBx /\ b <> (kx, A', cap' + 1)) -> (0 <= cap')%Z ->
      (SRC + n <= A' \/ A' + (cap' + 1) <= SRC)%Z).
    { intros sx LBx mx kx A' cap' HRx HINx SUBx HC'.
      pose proof (src_ok_fresh rsegs AI _ _ _ _ _ sx LBx mx (kx, A', cap' + 1) LOK CR HRx HINx SUBx ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as X.
      cbn in X. exact X. }
    destruct CASES as [(-> & -> & -> & -> & HNcap)|(-> & -> & -> & -> & -> & -> & N2 & N3 & N4)].
    -
      destruct ok as [k|]; cbn in OWN1; [| lia]. destruct OWN1 as [HIN BLK1].
      destruct (ai_block_range rsegs AI _ _ _ _ HR1 HIN) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
      pose proof (DJOF s LB m1 k A cap HR1 HIN (SUBNE k eq_refl) ltac:(lia)) as DJ.
      pose proof (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (k, A, cap + 1) HR1 (SUBNE k eq_refl) HIN MBL ltac:(lia)) as DJM. cbn in DJM.
      eapply sreach_evt. { eapply (isegM lo MB SRC n A len cap src bs j); try eassumption; try LiaTuning.alia. all: Z.div_mod_to_equations; lia. }
      intros ms' P. unfold isegM_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & BLK3).
      apply sreach_ret. eapply (FIN s LB m1 _ A cap k bs); try eassumption; try LiaTuning.alia.
      + exact (SUBNE k eq_refl).
      + eexists; exact ERR1.
      + reflexivity.
    -

      assert (CS : forall sx m2 (k' : K) (A' cap' : Z) (bs2 jx : list byte) (x1 t0' t1' t2' x8 x10 x12 x13 a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
        hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m2 ->
        RHEAP rsegs AI sx ((k', A', cap' + 1) :: lb_keep AI ok LB) m2 -> block_range AI A' (cap' + 1) ->
        RENV rsegs AI m2 B -> (exists e, rw_cells rsegs m2 (al_errno L) [C4 e]) -> mem_inv rsegs m2 ->
        stk rsegs m2 lo (bv_unsigned sp + -64) -> IFR m2 (bv_unsigned sp + -64) jx s5 s4 s3 s2 s1 s0 ra ->
        rw_cells rsegs m2 MB (mbuf_cells A len cap) -> bytes_at rsegs m2 SRC src ->
        rw_cells rsegs m2 A' [CB (Z.to_nat (cap' + 1)) bs2] -> firstn (Z.to_nat len) bs2 = firstn (Z.to_nat len) bs ->
        (len + n <= cap')%Z -> (cap' < 2^32)%Z -> (cap' <= cap + n + 5)%Z ->
        SREACH AI (membuffer_append_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m)
          (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz (al_tp L)) t0' t1' t2' (wz MB) (wz n) (wz A') x10 x12 x13 a4_ a5_ a6_ a7_ x8 (wz len) (wz SRC) (wz cap') s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
              F (wz 0x16930) fc None m2 (seg_rom rsegs)) sx ((k', A', cap' + 1) :: lb_keep AI ok LB)).
      { intros until t6_. intros HP2 HR2 BR2 HE2 ERR2 MI2 ST2 FR2 MBC2 BSRC2 BLK2 PFX2 NC' HC' HCB.
        destruct BR2 as (U1 & U2 & U3 & U4 & U5).
        assert (NEW : In (k', A', cap' + 1) ((k', A', cap' + 1) :: lb_keep AI ok LB)) by (left; reflexivity).
        assert (SUB2 : forall b, In b (lb_keep AI ok LB) -> In b ((k', A', cap' + 1) :: lb_keep AI ok LB) /\ b <> (k', A', cap' + 1)).
        { intros b Hb. split; [right; exact Hb|]. intros ->.
          pose proof (ai_blocks_nodup rsegs AI _ _ _ HR2) as ND. cbn in ND. inversion ND as [|xk xl NI ND']; subst.
          apply NI. apply base.list_elem_of_In. exact (in_map blk_id _ _ Hb). }
        pose proof (DJOF sx _ m2 k' A' cap' HR2 NEW SUB2 ltac:(lia)) as DJ.
        pose proof (mbloc_other_block rsegs AI _ _ _ _ _ _ _ _ (k', A', cap' + 1) HR2 SUB2 NEW MBL ltac:(lia)) as DJM. cbn in DJM.
        eapply sreach_evt. { eapply (isegS lo MB SRC n A A' len cap cap' src bs2 jx); try eassumption; try LiaTuning.alia. all: Z.div_mod_to_equations; lia. }
        intros ms' P. unfold isegM_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & MBC3 & BLK3).
        apply sreach_ret. eapply (FIN sx _ m2 _ A' cap' k' bs2); try eassumption; lia. }
      assert (OKH : forall mm, mown mm LB A cap ok bs ->
                match ok with None => A = 0 /\ (match ok with Some _ => cap + 1 | None => 0 end) = 0 /\ bs = []
                            | Some k => In (k, A, match ok with Some _ => cap + 1 | None => 0 end) LB
                                        /\ rw_cells rsegs mm A [CB (Z.to_nat (match ok with Some _ => cap + 1 | None => 0 end)) bs] end).
      { intros mm OW. destruct ok as [k|]; cbn in OW |- *; [exact OW|]. destruct OW as (? & ? & ?). repeat split; auto. }

      assert (PFXR : forall nsz' junk, (len <= nsz')%Z ->
        firstn (Z.to_nat len) (firstn (Z.to_nat (Z.min (nsz' + 1) (match ok with Some _ => cap + 1 | None => 0 end))) bs ++ junk) = firstn (Z.to_nat len) bs).
      { intros nsz' junk Hn. destruct ok as [k|]; cbn in OWN1.
        - destruct OWN1 as [_ BLK]. destruct BLK as [[W _] _]. cbn in W. destruct W as [W _].
          rewrite firstn_app, firstn_firstn, firstn_length. replace (Init.Nat.min (Z.to_nat len) (Z.to_nat (Z.min (nsz' + 1) (cap + 1)))) with (Z.to_nat len) by lia.
          replace (Z.to_nat len - Init.Nat.min (Z.to_nat (Z.min (nsz' + 1) (cap + 1))) (length bs))%nat with 0%nat by lia. cbn. apply app_nil_r.
        - destruct OWN1 as (_ & -> & ->). cbn. replace (Z.to_nat len) with 0%nat by lia. reflexivity. }

      eapply sreach_bind.
      { rewrite <- REALLOCPC. eapply (orealloc_spec rsegs AI AC) with (lo := lo) (B := B) (ok := ok); try eassumption; try reflexivity;
          rewrite ?unsigned_lit by lia; try lia; try eassumption. apply OKH. exact OWN1. }
      intros sx2 LB2 ms2 POST. unfold orealloc_post in POST. destruct_exs POST. destruct POST as (-> & CASES2).
      replace (ret_pc (Z_to_bv 64 92440)) with (Z_to_bv 64 92440) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct CASES2 as [(-> & -> & AF & HR2)|(k' & A' & junk & -> & -> & BR & AF & HR2 & BLK2)].
      +
        destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC1 ltac:(apply MBCR; [lia| auto])) as MBC2.
        assert (CRW : src_ok AI LB (bv_unsigned sp + -64) SRC n src).
        { eapply (src_ok_weaken rsegs AI); [exact CR| lia| exact SUB]. }
        pose proof (src_ok_pres rsegs AI _ _ _ _ _ _ _ CRW LEN HPF MI2 BSRC1) as BSRC2.
        assert (OWN2 : mown m2 LB A cap ok bs).
        { destruct ok as [k|]; cbn in OWN1 |- *; [| exact OWN1]. destruct OWN1 as [HIN BLK]. split; [exact HIN|].
          destruct (ai_block_range rsegs AI _ _ _ _ HR1 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
          eapply (heap_pres_rw_cells rsegs AI); [exact HPF| exact BLK|]. eapply client_range_block; [exact HIN| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
        assert (HP2 : hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m2).
        { eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact SUB]. }
        eapply sreach_evt. { eapply (isegF MB A len cap (len + n)); try eassumption; lia. }
        intros ms' ->.
        eapply sreach_bind.
        { rewrite <- REALLOCPC. eapply (orealloc_spec rsegs AI AC) with (lo := lo) (B := B) (ok := ok); try eassumption; try reflexivity;
            rewrite ?unsigned_lit by lia; try lia; try eassumption. apply OKH. exact OWN2. }
        intros sx3 LB3 ms3 POST. unfold orealloc_post in POST. destruct_exs POST. destruct POST as (-> & CASES3).
        replace (ret_pc (Z_to_bv 64 92456)) with (Z_to_bv 64 92456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        destruct CASES3 as [(-> & -> & AF & HR3)|(k' & A' & junk & -> & -> & BR & AF & HR3 & BLK3)].
        *
          destruct AF as (MI3 & ST3 & HE3 & [errv3 ERR3] & HPF2). rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPF2 by lia.
          lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 FR2 ltac:(apply client_range_above; cbn; lia)) as FR3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 MBC2 ltac:(apply MBCR; [lia| auto])) as MBC3.
          assert (OWN3 : mown m3 LB A cap ok bs).
          { destruct ok as [k|]; cbn in OWN2 |- *; [| exact OWN2]. destruct OWN2 as [HIN BLK]. split; [exact HIN|].
            destruct (ai_block_range rsegs AI _ _ _ _ HR2 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
            eapply (heap_pres_rw_cells rsegs AI); [exact HPF2| exact BLK|]. eapply client_range_block; [exact HIN| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
          eapply sreach_evt. { eapply (isegE lo j); try eassumption; lia. }
          intros ms' [-> ST4]. apply sreach_ret. unfold membuffer_append_post.
          do 15 eexists. exists (-104), A, len, cap, ok, bs. split; [reflexivity|].
          split; [exact MI3|]. split; [exact ST4|]. split; [exact HE3|]. split; [eexists; exact ERR3|]. split.
          { eapply (hpx_trans rsegs AI); [exact HP2|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF2| lia| exact SUB]. }
          split; [exact HR3|]. split; [exact SUB|]. split; [exact MBC3|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact OWN3|].
          split. { intros b Hb. destruct ok as [k0|]; [exact (proj2 (SUBNE k0 eq_refl b Hb))| exact I]. }
          split; [reflexivity|]. right. repeat split; reflexivity.
        *
          destruct AF as (MI3 & ST3 & HE3 & [errv3 ERR3] & HPF2). rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPF2 by lia.
          lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
          pose proof BR as BR'. destruct BR' as (U1 & _ & _ & U4 & _).
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 FR2 ltac:(apply client_range_above; cbn; lia)) as FR3.
          pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF2 MBC2 ltac:(apply MBCR; [lia| auto])) as MBC3.
          pose proof (src_ok_pres rsegs AI _ _ _ _ _ _ _ CRK LEN HPF2 MI3 BSRC2) as BSRC3.
          eapply sreach_evt. { eapply (isegH A'); lia. }
          intros ms' ->.
          eapply CS; try eassumption; try LiaTuning.alia.
          -- eapply (hpx_trans rsegs AI); [exact HP2|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF2| lia| auto].
          -- eexists; exact ERR3.
          -- apply PFXR. lia.
      +
        destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
        lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
        pose proof BR as BR'. destruct BR' as (U1 & _ & _ & U4 & _).
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
        pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBC1 ltac:(apply MBCR; [lia| auto])) as MBC2.
        pose proof (src_ok_pres rsegs AI _ _ _ _ _ _ _ CRK LEN HPF MI2 BSRC1) as BSRC2.
        eapply sreach_evt. { eapply (isegG A'); lia. }
        intros ms' ->.
        eapply (CS _ _ k' A' nsz); try eassumption; try LiaTuning.alia.
        * eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| auto].
        * eexists; exact ERR2.
        * apply PFXR. lia.
  Qed.

  #[using="AC LOK REALLOCPC"] Theorem membuffer_append_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (ok : option K) (MB SRC n A len cap lo B : Z) (src bs : list byte) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 64 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> (0 <= len <= cap)%Z -> (cap + n + 8 < 2^32)%Z -> mown m LB A cap ok bs ->
    (ok <> None -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)) ->
    mbloc AI (lb_keep AI ok LB) (bv_unsigned sp) B MB 32 -> (MB mod 8 = 0)%Z ->
    bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (0 < SRC)%Z -> (SRC + n <= alloc_ceiling)%Z ->
    client_range AI (lb_keep AI ok LB) (bv_unsigned sp) SRC n -> (SRC + n <= MB \/ MB + 32 <= SRC)%Z ->
    a0 = wz MB -> a1 = wz SRC -> a2 = wz n ->
    SREACH AI (membuffer_append_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap n lo B src bs m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_append_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI MBC HLC HNC OWN NUL MBL MBAL BSRC LEN S0 SHI CR DJS -> -> ->.
    pose proof (word_lt64 sp) as SPR.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (SUB : forall b, In b (lb_keep AI ok LB) -> In b LB) by (intros b Hb; eapply lb_keep_sub; exact Hb).
    pose proof (mbloc_pos rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL ltac:(lia)) as MBP.
    assert (MBB : (MB + 32 <= B)%Z).
    { destruct MBL as [H|(b & Hb & H1 & H2)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). cbn in R4. lia. }
    eapply sreach_evt. { eapply (iseg58 MB A len cap); try eassumption; lia. }
    intros ms' ->. eapply membuffer_insert_end_spec; try eassumption; try reflexivity; try lia. apply (src_ok_client rsegs AI). exact CR.
  Qed.
End W.
