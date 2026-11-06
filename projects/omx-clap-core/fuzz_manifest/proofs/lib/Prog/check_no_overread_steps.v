From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import memcpy_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Definition cpy (ub : list byte) (fill : Z) : list byte :=
  ub ++ Z_to_bv 8 0 :: repeat (Z_to_bv 8 fill) 16 ++ [Z_to_bv 8 0].

Lemma rwcb_split : forall segs m A (n1 n2 : nat) junk,
  rw_cells segs m A [CB (n1 + n2) junk] ->
  rw_cells segs m A [CB n1 (firstn n1 junk)] /\ rw_cells segs m (A + Z.of_nat n1) [CB n2 (skipn n1 junk)].
Proof.
  intros segs m A n1 n2 junk [[[Hl _] Hb] (Ha & Hn & Hw)].
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hn, Hw. rewrite app_nil_r in Hb. rewrite Nat.add_0_r in Hn, Hw.
  rewrite <- (firstn_skipn n1 junk) in Hb. apply bytes_at_app in Hb as [H1 H2].
  assert (E1 : length (firstn n1 junk) = n1)
    by (rewrite length_firstn; apply Nat.min_l; rewrite Hl; apply Nat.le_add_r).
  assert (E2 : length (skipn n1 junk) = n2)
    by (rewrite length_skipn, Hl, Nat.add_comm; apply Nat.add_sub).
  rewrite E1 in H2.
  split.
  - split; [split|].
    + cbn. split; [exact E1 | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H1.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split|].
    + cbn. split; [exact E2 | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H2.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_bytes : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Lemma cpy_bytes : forall segs m res ub (un fill : Z) c16,
  Z.of_nat (length ub) = un -> bytes_at segs m res ub ->
  bytes_at segs m (res + un) [Z_to_bv 8 0] -> bytes_at segs m (res + un + 1) c16 ->
  c16 = repeat (Z_to_bv 8 fill) 16 ->
  bytes_at segs m (res + (un + 18) + -1) [Z_to_bv 8 0] ->
  bytes_at segs m res (cpy ub fill).
Proof.
  intros segs m res ub un fill c16 Hl H0 H1 H2 -> H3. unfold cpy.
  apply bytes_at_app. split; [exact H0|]. rewrite Hl.
  change (Z_to_bv 8 0 :: repeat (Z_to_bv 8 fill) 16 ++ [Z_to_bv 8 0])
    with ([Z_to_bv 8 0] ++ repeat (Z_to_bv 8 fill) 16 ++ [Z_to_bv 8 0]).
  apply bytes_at_app. split; [exact H1|].
  apply bytes_at_app. split.
  - match goal with |- bytes_at _ _ ?X _ => replace X with (res + un + 1) by (cbn [length]; lia) end. exact H2.
  - rewrite repeat_length.
    match goal with |- bytes_at _ _ ?X _ => replace X with (res + (un + 18) + -1) by (cbn [length]; lia) end.
    exact H3.
Qed.

Lemma cno_s0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo un : Z),
  a1 = Z_to_bv 64 un -> 0 <= un <= 255 ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists m',
     ms' = MS (mkR (Z_to_bv 64 0x130b0) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 a3
                   (Z_to_bv 64 (un + 18)) a1 a2 a3 a4 a5 a6 a7 a2 s3 a1 s5 a0
                   (Z_to_bv 64 (un + 18)) (Z_to_bv 64 (un + 18)) s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     rw_cells rsegs m' (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
     munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
     stk rsegs m' lo (bv_unsigned sp + -80))
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13060) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo un
    -> HU HMI ST LO.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as LO0.
  carve_frame 80%nat ST.
  do 11 zstep.
  do 9 zstep.
  replace (un + 18 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z]. rewrite Z.add_0_r.
  finish.
Qed.

Lemma cno_s1_tail : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res un tn : Z) (ub j1 j2 j3 : list byte),
  s0 = Z_to_bv 64 res -> s4 = Z_to_bv 64 un -> s8 = Z_to_bv 64 (un + 18) -> s1 = Z_to_bv 64 tn ->
  4096 <= res -> res + un + 18 < 2 ^ 63 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length ub) = un ->
  bytes_at rsegs m res ub ->
  rw_cells rsegs m (res + un) [CB 1 j1] -> rw_cells rsegs m (res + un + 1) [CB 16 j2] ->
  rw_cells rsegs m (res + (un + 18) + -1) [CB 1 j3] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x130f8) sp gp tp t0' t1' t2' (Z_to_bv 64 res) (Z_to_bv 64 tn)
                   (Z_to_bv 64 (tn + 18)) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 un)
                   (Z_to_bv 64 (tn + 18)) s6 s7 (Z_to_bv 64 (un + 18)) s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy ub 97) /\
     munch [(res, res + (un + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x130cc) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res un tn ub j1 j2 j3 -> -> -> -> HR HR2 HU HT HL C0 B1 B2 B3 HMI.
  pose proof (munch_refl [(res, res + (un + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep.
  remember (res + un) as p eqn:Hp.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 4 zstep.
  assert (UA : bv_unsigned (Z_to_bv 64 (p + 1)) = p + 1) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MEMSET; [| exact HMI]. rewrite UA. exact B2. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MUc & WMc & MIc & RW1).
  subst ms'. rewrite UA in MUc, RW1.
  change (bv_unsigned (Z_to_bv 64 16)) with 16 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 16))) with 16%nat in RW1.
  change (bv_unsigned (Z_to_bv 64 97) mod 256) with 97 in RW1.
  replace (ret_pc (Z_to_bv 64 78052)) with (Z_to_bv 64 78052) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m0 m1 MUc WMc.
  clear MUc WMc HMI.
  zstep.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 3 zstep.
  assert (CP : bytes_at rsegs m2 res (cpy ub 97)).
  { subst p. apply rw_cells_bytes in B1, RW1, B3. cbn [cells_bytes cbytes app] in B1, RW1, B3.
    rewrite app_nil_r in RW1. eapply cpy_bytes; [exact HL | exact C0 | exact B1 | exact RW1 | reflexivity | exact B3]. }
  finish.
Qed.

Lemma blk_split4 : forall segs m res un junk, 0 <= un ->
  rw_cells segs m res [CB (Z.to_nat (un + 18)) junk] ->
  exists j0 j1 j2 j3, rw_cells segs m res [CB (Z.to_nat un) j0] /\ rw_cells segs m (res + un) [CB 1 j1] /\
    rw_cells segs m (res + un + 1) [CB 16 j2] /\ rw_cells segs m (res + (un + 18) + -1) [CB 1 j3].
Proof.
  intros segs m res un junk Hu H.
  rewrite (Z2Nat.inj_add un 18) in H by lia. change (Z.to_nat 18) with (1 + (16 + 1))%nat in H.
  apply rwcb_split in H as [B0 H]. rewrite Z2Nat.id in H by lia.
  apply rwcb_split in H as [B1 H]. apply rwcb_split in H as [B2 B3].
  change (Z.of_nat 1) with 1 in B2, B3. change (Z.of_nat 16) with 16 in B3.
  replace (res + un + 1 + 16) with (res + (un + 18) + -1) in B3 by lia.
  eexists _, _, _, _. split; [exact B0|]. split; [exact B1|]. split; [exact B2|exact B3].
Qed.

Lemma cno_s1 : memcpy_contract -> memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res un tn : Z) (ub junk : list byte),
  a0 = Z_to_bv 64 res -> s4 = Z_to_bv 64 un -> s8 = Z_to_bv 64 (un + 18) -> s1 = Z_to_bv 64 tn ->
  4096 <= res -> res + un + 18 < 2 ^ 63 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length ub) = un ->
  bytes_at rsegs m (bv_unsigned s6) ub ->
  (un = 0 \/ bv_unsigned s6 + un <= res \/ res + (un + 18) <= bv_unsigned s6) ->
  rw_cells rsegs m res [CB (Z.to_nat (un + 18)) junk] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x130f8) sp gp tp t0' t1' t2' (Z_to_bv 64 res) (Z_to_bv 64 tn)
                   (Z_to_bv 64 (tn + 18)) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 un)
                   (Z_to_bv 64 (tn + 18)) s6 s7 (Z_to_bv 64 (un + 18)) s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy ub 97) /\
     munch [(res, res + (un + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x130b0) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m res un tn ub junk -> -> -> -> HR HR2 HU HT HL SRC DJ BLK HMI.
  destruct (blk_split4 rsegs m res un junk ltac:(lia) BLK) as (j0 & j1 & j2 & j3 & B0 & B1 & B2 & B3). clear BLK.
  pose proof (munch_refl [(res, res + (un + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (UU : bv_unsigned (Z_to_bv 64 un) = un) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep.
  destruct (Z.eq_dec un 0) as [U0|U0].
  - if_true.
    assert (C0 : bytes_at rsegs m res ub).
    { destruct ub; [apply bytes_at_nil; lia | cbn [length] in HL; lia]. }
    eapply (cno_s1_tail MEMSET) with (res := res) (un := un) (tn := tn) (ub := ub);
      first [reflexivity | eassumption | lia].
  - if_false. do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY.
      - exact SRC.
      - rewrite UU, <- HL, Nat2Z.id. reflexivity.
      - rewrite UR, UU. exact B0.
      - rewrite UR, UU. lia.
      - exact HMI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MUc & WMc & MIc & RW0 & SRC1).
    subst ms'. rewrite UR, UU in MUc, RW0. clear SRC1.
    replace (ret_pc (Z_to_bv 64 78028)) with (Z_to_bv 64 78028) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m m1 MUc WMc.
    clear MUc WMc HMI.
    apply rw_cells_bytes in RW0. cbn [cells_bytes cbytes] in RW0. rewrite app_nil_r in RW0.
    eapply evt_mono.
    { eapply (cno_s1_tail MEMSET) with (res := res) (un := un) (tn := tn) (ub := ub);
        first [reflexivity | eassumption | lia]. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                E & CP & MU2 & WM2 & MI2).
    exists t0'', t1'', t2'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact E|]. split; [exact CP|]. split; [eapply munch_trans; eassumption|].
    split; [eapply wmono_trans; eassumption | exact MI2].
Qed.

Lemma cno_s2_tail : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res un tn : Z) (tb j1 j2 j3 : list byte),
  s3 = Z_to_bv 64 res -> s1 = Z_to_bv 64 tn -> s5 = Z_to_bv 64 (tn + 18) -> s7 = Z_to_bv 64 (un + 18) ->
  4096 <= res -> res + tn + 18 < 2 ^ 63 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length tb) = tn ->
  bytes_at rsegs m res tb ->
  rw_cells rsegs m (res + tn) [CB 1 j1] -> rw_cells rsegs m (res + tn + 1) [CB 16 j2] ->
  rw_cells rsegs m (res + (tn + 18) + -1) [CB 1 j3] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x1313c) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 tn)
                   (Z_to_bv 64 (un + 18)) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 res) s4
                   (Z_to_bv 64 (tn + 18)) s6 (Z_to_bv 64 (un + 18)) s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy tb 97) /\
     munch [(res, res + (tn + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13114) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res un tn tb j1 j2 j3 -> -> -> -> HR HR2 HU HT HL C0 B1 B2 B3 HMI.
  pose proof (munch_refl [(res, res + (tn + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep.
  remember (res + tn) as p eqn:Hp.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 4 zstep.
  assert (UA : bv_unsigned (Z_to_bv 64 (p + 1)) = p + 1) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MEMSET; [| exact HMI]. rewrite UA. exact B2. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MUc & WMc & MIc & RW1).
  subst ms'. rewrite UA in MUc, RW1.
  change (bv_unsigned (Z_to_bv 64 16)) with 16 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 16))) with 16%nat in RW1.
  change (bv_unsigned (Z_to_bv 64 97) mod 256) with 97 in RW1.
  replace (ret_pc (Z_to_bv 64 78124)) with (Z_to_bv 64 78124) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m0 m1 MUc WMc.
  clear MUc WMc HMI.
  zstep.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 2 zstep.
  assert (CP : bytes_at rsegs m2 res (cpy tb 97)).
  { subst p. apply rw_cells_bytes in B1, RW1, B3. cbn [cells_bytes cbytes app] in B1, RW1, B3.
    rewrite app_nil_r in RW1. eapply cpy_bytes; [exact HL | exact C0 | exact B1 | exact RW1 | reflexivity | exact B3]. }
  finish.
Qed.

Lemma cno_s2 : memcpy_contract -> memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res un tn : Z) (tb junk : list byte),
  a0 = Z_to_bv 64 res -> s1 = Z_to_bv 64 tn -> s5 = Z_to_bv 64 (tn + 18) -> s7 = Z_to_bv 64 (un + 18) ->
  4096 <= res -> res + tn + 18 < 2 ^ 63 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length tb) = tn ->
  bytes_at rsegs m (bv_unsigned s2) tb ->
  (tn = 0 \/ bv_unsigned s2 + tn <= res \/ res + (tn + 18) <= bv_unsigned s2) ->
  rw_cells rsegs m res [CB (Z.to_nat (tn + 18)) junk] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x1313c) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 tn)
                   (Z_to_bv 64 (un + 18)) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 res) s4
                   (Z_to_bv 64 (tn + 18)) s6 (Z_to_bv 64 (un + 18)) s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy tb 97) /\
     munch [(res, res + (tn + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x130f8) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m res un tn tb junk -> -> -> -> HR HR2 HU HT HL SRC DJ BLK HMI.
  destruct (blk_split4 rsegs m res tn junk ltac:(lia) BLK) as (j0 & j1 & j2 & j3 & B0 & B1 & B2 & B3). clear BLK.
  pose proof (munch_refl [(res, res + (tn + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (UT : bv_unsigned (Z_to_bv 64 tn) = tn) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep.
  destruct (Z.eq_dec tn 0) as [T0|T0].
  - if_true.
    assert (C0 : bytes_at rsegs m res tb).
    { destruct tb; [apply bytes_at_nil; lia | cbn [length] in HL; lia]. }
    eapply (cno_s2_tail MEMSET) with (res := res) (un := un) (tn := tn) (tb := tb);
      first [reflexivity | eassumption | lia].
  - if_false. do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY.
      - exact SRC.
      - rewrite UT, <- HL, Nat2Z.id. reflexivity.
      - rewrite UR, UT. exact B0.
      - rewrite UR, UT. lia.
      - exact HMI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MUc & WMc & MIc & RW0 & SRC1).
    subst ms'. rewrite UR, UT in MUc, RW0. clear SRC1.
    replace (ret_pc (Z_to_bv 64 78100)) with (Z_to_bv 64 78100) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m m1 MUc WMc.
    clear MUc WMc HMI.
    apply rw_cells_bytes in RW0. cbn [cells_bytes cbytes] in RW0. rewrite app_nil_r in RW0.
    eapply evt_mono.
    { eapply (cno_s2_tail MEMSET) with (res := res) (un := un) (tn := tn) (tb := tb);
        first [reflexivity | eassumption | lia]. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                E & CP & MU2 & WM2 & MI2).
    exists t0'', t1'', t2'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact E|]. split; [exact CP|]. split; [eapply munch_trans; eassumption|].
    split; [eapply wmono_trans; eassumption | exact MI2].
Qed.

Lemma blk_split3 : forall segs m res un junk, 0 <= un ->
  rw_cells segs m res [CB (Z.to_nat (un + 18)) junk] ->
  exists j0 j1 j2, rw_cells segs m res [CB (Z.to_nat un) j0] /\ rw_cells segs m (res + un) [CB 17 j1] /\
    rw_cells segs m (res + (un + 18) + -1) [CB 1 j2].
Proof.
  intros segs m res un junk Hu H.
  rewrite (Z2Nat.inj_add un 18) in H by lia. change (Z.to_nat 18) with (17 + 1)%nat in H.
  apply rwcb_split in H as [B0 H]. rewrite Z2Nat.id in H by lia.
  apply rwcb_split in H as [B1 B2].
  change (Z.of_nat 17) with 17 in B2.
  replace (res + un + 17) with (res + (un + 18) + -1) in B2 by lia.
  eexists _, _, _. split; [exact B0|]. split; [exact B1|exact B2].
Qed.

Lemma cpy0_bytes : forall segs m res ub (un : Z) c17,
  Z.of_nat (length ub) = un -> bytes_at segs m res ub ->
  bytes_at segs m (res + un) c17 -> c17 = repeat (Z_to_bv 8 0) 17 ->
  bytes_at segs m (res + (un + 18) + -1) [Z_to_bv 8 0] ->
  bytes_at segs m res (cpy ub 0).
Proof.
  intros segs m res ub un c17 Hl H0 H1 -> H3. unfold cpy.
  change (Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) 16 ++ [Z_to_bv 8 0])
    with (repeat (Z_to_bv 8 0) 17 ++ [Z_to_bv 8 0]).
  apply bytes_at_app. split; [exact H0|]. rewrite Hl.
  apply bytes_at_app. split; [exact H1|].
  rewrite repeat_length.
  match goal with |- bytes_at _ _ ?X _ => replace X with (res + (un + 18) + -1) by lia end.
  exact H3.
Qed.

Lemma cno_s3_tail : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res un tn : Z) (ub j1 j2 : list byte),
  s7 = Z_to_bv 64 res -> s4 = Z_to_bv 64 un -> s8 = Z_to_bv 64 (un + 18) -> s5 = Z_to_bv 64 (tn + 18) ->
  4096 <= res -> res + un + 18 < 2 ^ 63 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length ub) = un ->
  bytes_at rsegs m res ub ->
  rw_cells rsegs m (res + un) [CB 17 j1] -> rw_cells rsegs m (res + (un + 18) + -1) [CB 1 j2] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x13178) sp gp tp t0' t1' t2' s0 s1
                   (Z_to_bv 64 (tn + 18)) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 un)
                   (Z_to_bv 64 (tn + 18)) s6 (Z_to_bv 64 res) (Z_to_bv 64 (res + (un + 18))) s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy ub 0) /\
     munch [(res, res + (un + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13158) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res un tn ub j1 j2 -> -> -> -> HR HR2 HU HT HL C0 B1 B2 HMI.
  pose proof (munch_refl [(res, res + (un + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 zstep.
  assert (UA : bv_unsigned (Z_to_bv 64 (res + un)) = res + un) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MEMSET; [| exact HMI]. rewrite UA. exact B1. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MUc & WMc & MIc & RW1).
  subst ms'. rewrite UA in MUc, RW1.
  change (bv_unsigned (Z_to_bv 64 17)) with 17 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 17))) with 17%nat in RW1.
  change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW1.
  replace (ret_pc (Z_to_bv 64 78188)) with (Z_to_bv 64 78188) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m m1 MUc WMc.
  clear MUc WMc HMI.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 2 zstep.
  assert (CP : bytes_at rsegs m0 res (cpy ub 0)).
  { apply rw_cells_bytes in RW1, B2. cbn [cells_bytes cbytes app] in RW1, B2.
    rewrite app_nil_r in RW1. eapply cpy0_bytes; [exact HL | exact C0 | exact RW1 | reflexivity | exact B2]. }
  finish.
Qed.

Lemma cno_s3 : memcpy_contract -> memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res un tn : Z) (ub junk : list byte),
  a0 = Z_to_bv 64 res -> s4 = Z_to_bv 64 un -> s8 = Z_to_bv 64 (un + 18) -> s5 = Z_to_bv 64 (tn + 18) ->
  4096 <= res -> res + un + 18 < 2 ^ 63 -> 0 <= un <= 255 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length ub) = un ->
  bytes_at rsegs m (bv_unsigned s6) ub ->
  (un = 0 \/ bv_unsigned s6 + un <= res \/ res + (un + 18) <= bv_unsigned s6) ->
  rw_cells rsegs m res [CB (Z.to_nat (un + 18)) junk] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x13178) sp gp tp t0' t1' t2' s0 s1
                   (Z_to_bv 64 (tn + 18)) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 un)
                   (Z_to_bv 64 (tn + 18)) s6 (Z_to_bv 64 res) (Z_to_bv 64 (res + (un + 18))) s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x14ce0) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy ub 0) /\
     munch [(res, res + (un + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x1313c) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m res un tn ub junk -> -> -> -> HR HR2 HU HT HL SRC DJ BLK HMI.
  destruct (blk_split3 rsegs m res un junk ltac:(lia) BLK) as (j0 & j1 & j2 & B0 & B1 & B2). clear BLK.
  pose proof (munch_refl [(res, res + (un + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (UU : bv_unsigned (Z_to_bv 64 un) = un) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep.
  destruct (Z.eq_dec un 0) as [U0|U0].
  - if_true.
    assert (C0 : bytes_at rsegs m res ub).
    { destruct ub; [apply bytes_at_nil; lia | cbn [length] in HL; lia]. }
    eapply (cno_s3_tail MEMSET) with (res := res) (un := un) (tn := tn) (ub := ub);
      first [reflexivity | eassumption | lia].
  - if_false. do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY.
      - exact SRC.
      - rewrite UU, <- HL, Nat2Z.id. reflexivity.
      - rewrite UR, UU. exact B0.
      - rewrite UR, UU. lia.
      - exact HMI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MUc & WMc & MIc & RW0 & SRC1).
    subst ms'. rewrite UR, UU in MUc, RW0. clear SRC1.
    replace (ret_pc (Z_to_bv 64 78168)) with (Z_to_bv 64 78168) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m m1 MUc WMc.
    clear MUc WMc HMI.
    apply rw_cells_bytes in RW0. cbn [cells_bytes cbytes] in RW0. rewrite app_nil_r in RW0.
    eapply evt_mono.
    { eapply (cno_s3_tail MEMSET) with (res := res) (un := un) (tn := tn) (ub := ub);
        first [reflexivity | eassumption | lia]. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                E & CP & MU2 & WM2 & MI2).
    exists t0'', t1'', t2'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact E|]. split; [exact CP|]. split; [eapply munch_trans; eassumption|].
    split; [eapply wmono_trans; eassumption | exact MI2].
Qed.

Lemma cno_s4_tail : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res tn : Z) (tb j1 j2 : list byte),
  s4 = Z_to_bv 64 res -> s1 = Z_to_bv 64 tn -> s5 = Z_to_bv 64 (tn + 18) ->
  4096 <= res -> res + tn + 18 < 2 ^ 63 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length tb) = tn ->
  bytes_at rsegs m res tb ->
  rw_cells rsegs m (res + tn) [CB 17 j1] -> rw_cells rsegs m (res + (tn + 18) + -1) [CB 1 j2] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x131b8) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 tn)
                   s3 s0 a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 res)
                   (Z_to_bv 64 (res + (tn + 18))) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x13c1c) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy tb 0) /\
     munch [(res, res + (tn + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13194) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    res tn tb j1 j2 -> -> -> HR HR2 HT HL C0 B1 B2 HMI.
  pose proof (munch_refl [(res, res + (tn + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 zstep.
  assert (UA : bv_unsigned (Z_to_bv 64 (res + tn)) = res + tn) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply MEMSET; [| exact HMI]. rewrite UA. exact B1. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MUc & WMc & MIc & RW1).
  subst ms'. rewrite UA in MUc, RW1.
  change (bv_unsigned (Z_to_bv 64 17)) with 17 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 17))) with 17%nat in RW1.
  change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW1.
  replace (ret_pc (Z_to_bv 64 78248)) with (Z_to_bv 64 78248) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m m1 MUc WMc.
  clear MUc WMc HMI.
  zstep.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  mem_after_store.
  do 3 zstep.
  assert (CP : bytes_at rsegs m0 res (cpy tb 0)).
  { apply rw_cells_bytes in RW1, B2. cbn [cells_bytes cbytes app] in RW1, B2.
    rewrite app_nil_r in RW1. eapply cpy0_bytes; [exact HL | exact C0 | exact RW1 | reflexivity | exact B2]. }
  finish.
Qed.

Lemma cno_s4 : memcpy_contract -> memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res tn : Z) (tb junk : list byte),
  a0 = Z_to_bv 64 res -> s1 = Z_to_bv 64 tn -> s5 = Z_to_bv 64 (tn + 18) ->
  4096 <= res -> res + tn + 18 < 2 ^ 63 -> 0 <= tn <= 2 ^ 22 -> Z.of_nat (length tb) = tn ->
  bytes_at rsegs m (bv_unsigned s2) tb ->
  (tn = 0 \/ bv_unsigned s2 + tn <= res \/ res + (tn + 18) <= bv_unsigned s2) ->
  rw_cells rsegs m res [CB (Z.to_nat (tn + 18)) junk] ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
     ms' = MS (mkR (Z_to_bv 64 0x131b8) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 tn)
                   s3 s0 a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 res)
                   (Z_to_bv 64 (res + (tn + 18))) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x13c1c) fc None m' (seg_rom rsegs) /\
     bytes_at rsegs m' res (cpy tb 0) /\
     munch [(res, res + (tn + 18))] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x13178) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m res tn tb junk -> -> -> HR HR2 HT HL SRC DJ BLK HMI.
  destruct (blk_split3 rsegs m res tn junk ltac:(lia) BLK) as (j0 & j1 & j2 & B0 & B1 & B2). clear BLK.
  pose proof (munch_refl [(res, res + (tn + 18))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (UT : bv_unsigned (Z_to_bv 64 tn) = tn) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep.
  destruct (Z.eq_dec tn 0) as [T0|T0].
  - if_true.
    assert (C0 : bytes_at rsegs m res tb).
    { destruct tb; [apply bytes_at_nil; lia | cbn [length] in HL; lia]. }
    eapply (cno_s4_tail MEMSET) with (res := res) (tn := tn) (tb := tb);
      first [reflexivity | eassumption | lia].
  - if_false. do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY.
      - exact SRC.
      - rewrite UT, <- HL, Nat2Z.id. reflexivity.
      - rewrite UR, UT. exact B0.
      - rewrite UR, UT. lia.
      - exact HMI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                    E & MUc & WMc & MIc & RW0 & SRC1).
    subst ms'. rewrite UR, UT in MUc, RW0. clear SRC1.
    replace (ret_pc (Z_to_bv 64 78228)) with (Z_to_bv 64 78228) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m m1 MUc WMc.
    clear MUc WMc HMI.
    apply rw_cells_bytes in RW0. cbn [cells_bytes cbytes] in RW0. rewrite app_nil_r in RW0.
    eapply evt_mono.
    { eapply (cno_s4_tail MEMSET) with (res := res) (tn := tn) (tb := tb);
        first [reflexivity | eassumption | lia]. }
    intros ms' (t0'' & t1'' & t2'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 &
                E & CP & MU2 & WM2 & MI2).
    exists t0'', t1'', t2'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact E|]. split; [exact CP|]. split; [eapply munch_trans; eassumption|].
    split; [eapply wmono_trans; eassumption | exact MI2].
Qed.

Lemma cno_s5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x131c8) sp gp tp t0 t1 t2 s0 a0 s4 s7 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x13c1c) fc None m (seg_rom rsegs))
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x131b8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 4 zstep. apply evt_done. reflexivity.
Qed.

Lemma cno_s6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  s1 = a0 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x131d4) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs))
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x131c8) fc None m (seg_rom rsegs)).
Proof.
  intros. subst s1. zstep. if_false. do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma cno_s7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x131dc) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs))
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x131d4) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma cno_s8 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x131e4) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs))
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x131dc) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 zstep. apply evt_done. reflexivity.
Qed.

Lemma cno_s9 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 v1 v2 v3 v4 v5 v6 v7 v8 vra : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  evt rsegs (fun ms' => ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 v0 v1 s4 a1 a2 a3 a4 a5 a6 a7
                                      v2 v3 v4 v5 v6 v7 v8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x14ba0) fc None m (seg_rom rsegs))
   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x131e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 v1 v2 v3 v4 v5 v6 v7 v8 vra FR.
  do 13 zstep.
  idtac "S9-a".
  match goal with |- evt _ _ ?S => idtac S end.
  apply evt_done. reflexivity.
Qed.
