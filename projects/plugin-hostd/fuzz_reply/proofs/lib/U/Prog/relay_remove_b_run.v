(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, addresses and numbers changed; 405 of its 473 lines of code are new or changed and 1161 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_remove_b_seg.v, with its addresses and numbers changed; 158 of its 191 lines of code are new or changed and 440 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c memcpy_c memcpy_same_c wake_c relay_remove_b_seg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rm_rd : forall m A bs, bytes_at rsegs m A bs -> ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace (wa A) with (wa (A + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m A bs 0 (length bs) H ltac:(lia)) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma rm_rd4 : forall m A (w : word), bytes_at rsegs m A (le4 w) -> ov_read_bytes rsegs m (Z_to_bv 64 A) 4 = Some (le4 w).
Proof. intros m A w H. pose proof (rm_rd _ _ _ H) as R. rewrite length_le4 in R. exact R. Qed.

Lemma rm_rd8 : forall m A (w : word), bytes_at rsegs m A (le8 w) -> ov_read_bytes rsegs m (Z_to_bv 64 A) 8 = Some (le8 w).
Proof. intros m A w H. pose proof (rm_rd _ _ _ H) as R. rewrite length_le8 in R. exact R. Qed.

Lemma rm_rd44 : forall m A (x y : list byte), bytes_at rsegs m A (x ++ y) -> length x = 4%nat -> length y = 4%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) 4 = Some x /\ ov_read_bytes rsegs m (Z_to_bv 64 (A + 4)) 4 = Some y.
Proof.
  intros m A x y H Lx Ly. apply bytes_at_app in H as [H1 H2]. rewrite Lx in H2.
  split; [rewrite <- Lx; exact (rm_rd _ _ _ H1) | rewrite <- Ly; exact (rm_rd _ _ _ H2)].
Qed.

Lemma rm_munch_mono : forall W W' m m', munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' H S x Hx. apply H. apply S. exact Hx. Qed.

Lemma rm_signed_lit : forall z, 0 <= z < 2 ^ 31 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite YK11.bv_signed_small by (rewrite unsigned_lit; lia). apply unsigned_lit. lia. Qed.


Definition rm_hq (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FD G N : Z) (fdk eofk : nat -> Z) (m : word -> option byte) (ms' : machine_state) : Prop :=
  exists m1 jf, wmono rsegs m m1 /\
    ((munch [(bv_unsigned sp + -48, bv_unsigned sp); (203004, 203008)] m m1 /\ mem_inv rsegs m1 /\
      rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 jf; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      rw_cells rsegs m1 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
      exists i, (i < Z.to_nat N)%nat /\ fdk i = FD /\ (forall k, (k < i)%nat -> fdk k <> FD) /\
      exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
        (eofk i = 0 /\
         ms' = MS (mkR (Z_to_bv 64 0x13fbc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 203000)
                       (Z_to_bv 64 FD) (Z_to_bv 64 (G + 56 * Z.of_nat i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 202912)
                       (Z_to_bv 64 (56 * Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x138c0) fc None m1 (seg_rom rsegs)) \/
        (eofk i <> 0 /\
         ms' = MS (mkR (Z_to_bv 64 0x13fe0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 203000)
                       (Z_to_bv 64 FD) (Z_to_bv 64 (G + 56 * Z.of_nat i)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 202912) (Z_to_bv 64 (56 * Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13200) fc None m1 (seg_rom rsegs))) \/
     ((forall k, (k < Z.to_nat N)%nat -> fdk k <> FD) /\
      munch [(bv_unsigned sp - 144, bv_unsigned sp); (203004, 203008)] m m1 /\
      rw_cells rsegs m1 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
      exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m1 (seg_rom rsegs))).

Lemma rm_head : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract -> wake_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo FD G N : Z) (fdk eofk : nat -> Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 203012 <= lo ->
  a0 = Z_to_bv 64 FD -> 0 <= FD < 2 ^ 31 ->
  rw_cells rsegs m 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] -> mem_inv rsegs m ->
  0 < G -> G mod 8 = 0 -> G + 896 <= lo -> (G + 896 <= 202912 \/ 203040 <= G) -> 0 <= N <= 4 ->
  (forall k, (k < Z.to_nat N)%nat -> 0 <= fdk k < 2 ^ 31 /\ 0 <= eofk k < 2 ^ 31 /\
     bytes_at rsegs m (G + 56 * Z.of_nat k) (le4 (Z_to_bv 64 (fdk k)) ++ le4 (Z_to_bv 64 (eofk k)))) ->
  bytes_at rsegs m 202936 (le4 (Z_to_bv 64 N)) ->
  bytes_at rsegs m 202960 (le8 (Z_to_bv 64 G)) ->
  bytes_at rsegs m 136748 (le4 (Z_to_bv 64 (-1))) ->
  evt rsegs (rm_hq ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FD G N fdk eofk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs)).
Proof.
  intros SPL SPU SPW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FD G N fdk eofk ST LO LOL -> HFD GL MI G0 GA GT GI HN HT RN RG RW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  eapply evt_cut.
  { eapply (rm_seg1 SPL); [exact ST | lia | lia | rewrite rm_signed_lit by lia; lia | exact GL | exact MI]. }
  intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & jf
    & -> & MU1 & WM1 & MI1 & ST1 & FR1 & GL1).
  assert (W1 : forall a n, 0 <= a -> a + n <= lo -> (a + n <= 203004 \/ 203008 <= a) ->
             disjoint_from [(bv_unsigned sp + -48, bv_unsigned sp); (203004, 203008)] a n).
  { intros a n H0 H1 H2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (RD : rm_reads m1 G N fdk eofk).
  { intros k Hk. destruct (HT k Hk) as (Hf & He & B).
    assert (B1 : bytes_at rsegs m1 (G + 56 * Z.of_nat k) (le4 (Z_to_bv 64 (fdk k)) ++ le4 (Z_to_bv 64 (eofk k)))).
    { apply (bytes_at_transport rsegs _ m m1 _ _ B MU1). rewrite length_app, !length_le4.
      apply W1; [lia | lia | lia]. }
    destruct (rm_rd44 _ _ _ _ B1 (length_le4 _) (length_le4 _)) as [R0 R1].
    split; [exact Hf|]. split; [exact He|]. split; [exact R0 | exact R1]. }
  assert (RN1 : ov_read_bytes rsegs m1 (Z_to_bv 64 202936) 4 = Some (le4 (Z_to_bv 64 N))).
  { apply rm_rd4. apply (bytes_at_transport rsegs _ m m1 _ _ RN MU1). rewrite length_le4. apply W1; lia. }
  assert (RG1 : ov_read_bytes rsegs m1 (Z_to_bv 64 202960) 8 = Some (le8 (Z_to_bv 64 G))).
  { apply rm_rd8. apply (bytes_at_transport rsegs _ m m1 _ _ RG MU1). rewrite length_le8. apply W1; lia. }
  assert (RW1 : bytes_at rsegs m1 136748 (le4 (Z_to_bv 64 (-1)))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ RW MU1). rewrite length_le4. apply W1; lia. }
  eapply evt_cut.
  { eapply rm_seg2; [exact G0 | exact GA | lia | exact HFD | exact HN | exact RD | exact RN1 | exact RG1]. }
  intros ms2 HD. unfold rm_disp in HD.
  destruct HD as (x1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z3 & u3 & u4 & u5 & u6 & HD).
  destruct HD as [[NF ->] | (i & Hi & Hfi & Hb & [[He ->] | [He ->]])].
  - assert (US : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (rm_end SPU SPW) with (lo := lo); [rewrite US; exact FR1 | exact GL1 | exact RW1 | rewrite US; exact ST1
        | rewrite US; lia | lia | rewrite US; lia | exact MI1]. }
    intros ms3 (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & ST3 & GL3).
    rewrite US in MU3 |- *. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in MU3 |- * by lia.
    rewrite Z_to_bv_bv_unsigned.
    apply evt_done. exists m3, jf. split; [exact (wmono_trans rsegs _ _ _ WM1 WM3)|]. right.
    split; [exact NF|].
    split.
    { intros x Hx. cbn [outside] in Hx. rewrite (MU3 x) by (cbn [outside]; lia).
      apply MU1. cbn [outside]. lia. }
    split; [exact GL3|]. do 15 eexists. reflexivity.
  - apply evt_done. exists m1, jf. split; [exact WM1|]. left.
    split; [exact MU1|]. split; [exact MI1|]. split; [exact FR1|]. split; [exact GL1|].
    exists i. split; [exact Hi|]. split; [exact Hfi|]. split; [exact Hb|].
    do 14 eexists. left. split; [exact He | reflexivity].
  - apply evt_done. exists m1, jf. split; [exact WM1|]. left.
    split; [exact MU1|]. split; [exact MI1|]. split; [exact FR1|]. split; [exact GL1|].
    exists i. split; [exact Hi|]. split; [exact Hfi|]. split; [exact Hb|].
    do 14 eexists. right. split; [exact He | reflexivity].
Qed.

Lemma rm_tail2 : memcpy_contract -> memcpy_same_contract -> pthread_mutex_unlock_contract -> wake_contract ->
  forall x1 sp1 gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo G N : Z) (i : nat) (src dj jf : list byte)
    (w1 w8 w9 w18 w19 : word),
  0 < G -> G + 896 <= lo -> (G + 896 <= 202912 \/ 203040 <= G) -> (G + 896 <= 136748 \/ 136752 <= G) ->
  1 <= N <= 4 -> Z.of_nat i < N ->
  rw_cells rsegs m 202936 [C4 (Z_to_bv 64 N)] ->
  bytes_at rsegs m 202960 (le8 (Z_to_bv 64 G)) ->
  length src = 56%nat ->
  ((Z.of_nat i < N - 1 /\ bytes_at rsegs m (G + 56 * (N - 1)) src /\ rw_cells rsegs m (G + 56 * Z.of_nat i) [CB 56 dj]) \/
   (Z.of_nat i = N - 1 /\ rw_cells rsegs m (G + 56 * Z.of_nat i) [CB 56 src])) ->
  rw_cells rsegs m (bv_unsigned sp1) [CB 8 jf; C8 w19; C8 w18; C8 w9; C8 w8; C8 w1] ->
  rw_cells rsegs m 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 136748 (le4 (Z_to_bv 64 (-1))) ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 203012 <= lo -> bv_unsigned sp1 + 48 < 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp1 + 48)) gp tp t0' t1' t2' w8 w9 a0' a1' a2' a3' a4' a5' a6' a7'
                    w18 w19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc w1) fc None m' (seg_rom rsegs) /\
      munch [(G + 56 * Z.of_nat i, G + 56 * Z.of_nat i + 56); (202936, 202940);
             (bv_unsigned sp1 - 96, bv_unsigned sp1 + 48); (203004, 203008)] m m' /\
      wmono rsegs m m' /\
      rw_cells rsegs m' 202936 [C4 (Z_to_bv 64 (N - 1))] /\
      rw_cells rsegs m' (G + 56 * Z.of_nat i) [CB 56 src] /\
      rw_cells rsegs m' 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR x1 sp1 gp tp t0 t1 t2 (Z_to_bv 64 203000) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 202912)
             (Z_to_bv 64 (56 * Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14014) fc None m (seg_rom rsegs)).
Proof.
  intros MCP MCS SPU WAKEC x1 sp1 gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo G N i src dj jf w1 w8 w9 w18 w19 G0 GL GI GW HN HI CN RG LS HC FR LK WK ST LO LOL SPB MI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (W2 : forall a n, (a + n <= 202936 \/ 202940 <= a) ->
             (a + n <= G + 56 * Z.of_nat i \/ G + 56 * Z.of_nat i + 56 <= a) ->
             disjoint_from [(G + 56 * Z.of_nat i, G + 56 * Z.of_nat i + 56); (202936, 202940)] a n).
  { intros a n H2 H3. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  eapply evt_cut.
  { eapply (rm_segf MCP MCS) with (src := src) (dj := dj);
      [exact G0 | lia | exact GI | exact HN | exact HI | exact CN | apply rm_rd8; exact RG | exact LS | exact HC
      | exact MI]. }
  intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & NS1
    & SL1 & _).
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp1) [CB 8 jf; C8 w19; C8 w18; C8 w9; C8 w8; C8 w1]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1). cbn [cells_size csize]. apply W2; lia. }
  assert (LK1 : rw_cells rsegs m1 203000 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ LK MU1 WM1). cbn [cells_size csize]. apply W2; lia. }
  assert (WK1 : bytes_at rsegs m1 136748 (le4 (Z_to_bv 64 (-1)))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ WK MU1). rewrite length_le4. apply W2; lia. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp1)).
  { destruct ST as (S0 & S1 & S). split; [exact S0|]. split; [exact S1|]. intros a Ha.
    destruct (S a Ha) as [Sw [b Sb]].
    assert (O : outside [(G + 56 * Z.of_nat i, G + 56 * Z.of_nat i + 56); (202936, 202940)] (bv_unsigned (wa a))).
    { unfold wa. rewrite unsigned_lit by lia. cbn [outside]. lia. }
    split.
    - unfold wview in *. rewrite (MU1 _ O). exact Sw.
    - exists b. unfold mrd in *. rewrite (MU1 _ O). exact Sb. }
  eapply evt_cut.
  { eapply (rm_end SPU WAKEC) with (lo := lo); [exact FR1 | exact LK1 | exact WK1 | exact ST1 | exact LO | exact LOL
      | exact SPB | exact MI1]. }
  intros ms2 (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & ST2
    & GL2).
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split.
  { intros x Hx. cbn [outside] in Hx. rewrite (MU2 x) by (cbn [outside]; lia). apply MU1. cbn [outside]. lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ NS1 MU2 WM2). cbn [disjoint_from cells_size csize]. lia. }
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ SL1 MU2 WM2). cbn [disjoint_from cells_size csize]. lia. }
  exact GL2.
Qed.
