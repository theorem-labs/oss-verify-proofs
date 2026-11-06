(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput.v
   at bc49657c087a (its entry segment e0_evt and the tactics usub / solve_c / take); module path, this harness's code. *)
(* The plain image's harness body LLVMFuzzerTestOneInput (fuzz_egress.c:143-157), 0x12c60, from its entry to the
   call of malloc for f = fuzz_dup(data + 53 * (size > 53), n) at 0x12d54, for size < 2^26 (the larger sizes return
   at once: LLVMFuzzerTestOneInput_early.v). One evt segment, in three lemmas:
   - eA_evt: the 192-byte frame (ra, s0..s8 saved at sp + 112), head[53] = {0} (memset at sp + 0x3b), then the
     size < 53 branch;
   - eA_cpy: memcpy(head, data, min (size, 53));
   - eA_tail: slot = head[0] - 2 kept in s4, the counter bytes, the loop v[s] = le32(head + 5 + 4s) for s < 12 (stored
     at sp + 8 + 4s), n = min (size > 53 ? size - 53 : 0, 1600) in s2, and malloc(n ? n : 1).
   The values of the counter and of v do not matter to the rest of the walk (check_restamp takes any counter,
   check_inject any v); the slot byte does (check_gate and check_inject take -2 <= slot <= 253). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import memset_c memcpy_c FuzzDup lt_glue.
Import ListNotations.
Open Scope Z_scope.

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; usub; fold_lit_ux; solve_cond_rec.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
Ltac qreg := split; [first [reflexivity | (simp_regs; f_equal; lia)] |].

Lemma eA_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sltu_lo : forall n, 0 <= n < 53 -> v_sltu (Z_to_bv 64 n) (Z_to_bv 64 (n + -53)) = Z_to_bv 64 1.
Proof.
  intros n Hn. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit n) by lia. rewrite unsigned_lit_wrap.
  replace ((n + -53) mod 2 ^ 64) with (n + -53 + 2 ^ 64).
  - destruct (Z.ltb_spec n (n + -53 + 2 ^ 64)); [reflexivity | lia].
  - rewrite <- (Z.mod_add (n + -53) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sltu_hi : forall n, 53 <= n < 2 ^ 64 -> v_sltu (Z_to_bv 64 n) (Z_to_bv 64 (n + -53)) = Z_to_bv 64 0.
Proof.
  intros n Hn. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec n (n + -53)); [lia | reflexivity].
Qed.

Lemma land_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx.
Qed.

Lemma seqz_lit : forall x, 0 <= x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (if x =? 0 then 1 else 0).
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec x 0) as [->|H]; [reflexivity|].
  destruct (Z.ltb_spec x 1); [lia | reflexivity].
Qed.

Lemma fds_eq : forall x, 0 <= x -> x + (if x =? 0 then 1 else 0) = fuzz_dup_size x.
Proof. intros x Hx. unfold fuzz_dup_size. destruct (Z.eqb_spec x 0); lia. Qed.

(* the state at malloc's entry: ra = 0x12d58, s2 = n, a0 = n ? n : 1, s4 = head[0] *)
Definition qA (F : bvmap 5 word) (fc : bv 32) (gp tp x19 x25 x26 x27 : word) (m0 : word -> option byte)
    (Sp n p : Z) (sv : list cell) (ms : machine_state) : Prop :=
  exists R m' (b0 : byte) nn, ms = MS R F (Z_to_bv 64 0x14010) fc None m' (seg_rom rsegs) /\
    reg_get R 1 = Z_to_bv 64 0x12d58 /\ reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    reg_get R 8 = Z_to_bv 64 p /\ reg_get R 9 = Z_to_bv 64 n /\ reg_get R 10 = Z_to_bv 64 (fuzz_dup_size nn) /\
    reg_get R 18 = Z_to_bv 64 nn /\ reg_get R 19 = x19 /\ reg_get R 20 = Z_to_bv 64 (bv_unsigned b0) /\
    reg_get R 25 = x25 /\ reg_get R 26 = x26 /\ reg_get R 27 = x27 /\
    nn = Z.min (Z.max (n - 53) 0) 1600 /\
    munch [(Sp, Sp + 192)] m0 m' /\ wmono rsegs m0 m' /\ rw_cells rsegs m' (Sp + 112) sv.

Lemma eA_tail :
  forall (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) (y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp n p : Z) (ja hd : list byte),
    0 <= Sp -> Sp + 192 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> length hd = 53%nat ->
    rw_cells rsegs m Sp (CB 59 ja :: map C1 hd) ->
    rw_cells rsegs m (Sp + 112) [C8 y24; C8 y23; C8 y22; C8 y21; C8 y20; C8 y19; C8 y18; C8 y9; C8 y8; C8 y1] ->
    mem_inv rsegs m -> munch [(Sp, Sp + 192)] mb m -> wmono rsegs mb m ->
    evt rsegs (qA F fc x3 x4 x19 x25 x26 x27 mb Sp n p
                 [C8 y24; C8 y23; C8 y22; C8 y21; C8 y20; C8 y19; C8 y18; C8 y9; C8 y8; C8 y1])
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17 x18
               x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12cc4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 F fc mb m Sp n p ja hd H0 H1 Hn HL FR FS MI MU WM.
  destruct hd as [|h0 hd]; [cbn in HL; discriminate|].
  do 52 (destruct hd as [|?b hd]; [cbn in HL; discriminate|]).
  destruct hd as [|? hd]; [|cbn in HL; discriminate]. clear HL.
  cbn [map] in FR.
  do 12 step.
  do 11 (do 15 step; take true).
  do 15 step. take false.
  destruct (Z_lt_le_dec n 53) as [H53|H53].
  - step. step. rewrite (sltu_lo n) by lia. step. step. rewrite Z.land_0_l.
    step. step. take true.
    step. rewrite (seqz_lit 0) by lia. step. step.
    apply evt_done. unfold qA. do 2 eexists. exists h0, 0.
    split; [reflexivity|]. do 13 qreg.
    split; [lia|]. split; [exact MU|]. split; [exact WM | exact FS].
  - step. step. rewrite (sltu_hi n) by lia. step. step. rewrite (unsigned_lit (n + -53)) by lia.
    rewrite (land_ones64 (n + -53)) by lia.
    step. step.
    destruct (Z_lt_le_dec (n - 53) 1600) as [H16|H16].
    + take true.
      step. rewrite (seqz_lit (n + -53)) by lia. step. step.
      apply evt_done. unfold qA. do 2 eexists. exists h0, (n + -53).
      split; [reflexivity|]. do 6 qreg.
      split; [f_equal; rewrite <- (fds_eq (n + -53)) by lia; first [reflexivity | lia | ring] |]. do 6 qreg.
      split; [lia|]. split; [exact MU|]. split; [exact WM | exact FS].
    + take false.
      step. step. rewrite (seqz_lit 1600) by lia. step. step.
      apply evt_done. unfold qA. do 2 eexists. exists h0, 1600.
      split; [reflexivity|]. do 13 qreg.
      split; [lia|]. split; [exact MU|]. split; [exact WM | exact FS].
Qed.

Lemma eA_cpy : memcpy_contract ->
  forall (x1 x3 x4 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) (y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 : word)
         (F : bvmap 5 word) (fc : bv 32) (mb m : word -> option byte) (Sp n p k : Z) (pl ja jz : list byte),
    0 <= Sp -> Sp + 192 <= 2 ^ 63 -> 0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> n = Z.of_nat (length pl) ->
    k = Z.min n 53 ->
    (0 < n -> bytes_at rsegs mb p pl) -> (0 < n -> p + n <= Sp) ->
    rw_cells rsegs m Sp [CB 59 ja] -> rw_cells rsegs m (Sp + 59) [CB 53 jz] ->
    rw_cells rsegs m (Sp + 112) [C8 y24; C8 y23; C8 y22; C8 y21; C8 y20; C8 y19; C8 y18; C8 y9; C8 y8; C8 y1] ->
    mem_inv rsegs m -> munch [(Sp, Sp + 192)] mb m -> wmono rsegs mb m ->
    evt rsegs (qA F fc x3 x4 x19 x25 x26 x27 mb Sp n p
                 [C8 y24; C8 y23; C8 y22; C8 y21; C8 y20; C8 y19; C8 y18; C8 y9; C8 y8; C8 y1])
      (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 p) (Z_to_bv 64 n) x10 x11 (Z_to_bv 64 k) x13 x14 x15
               x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12cb8) fc None m (seg_rom rsegs)).
Proof.
  intros MC x1 x3 x4 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 F fc mb m Sp n p k pl ja jz H0 H1 Hn Hp Hlen Hk HPB HPL FRa FRh FRs MI MU WM.
  pose proof FRh as [[[Hjz _] _] _]. cbn [cell_wf] in Hjz.
  destruct (rwc_cut rsegs m (Sp + 59) 53 jz (Z.to_nat k) FRh ltac:(lia)) as [FRk FRt]. clear FRh.
  replace (Sp + 59 + Z.of_nat (Z.to_nat k)) with (Sp + 59 + k) in FRt by lia.
  set (src := firstn (Z.to_nat k) pl).
  assert (BS : bytes_at rsegs m p src).
  { destruct (Z.eq_dec n 0) as [N0|N0].
    - assert (Epl : pl = []) by (destruct pl as [|x pl]; [reflexivity | cbn [length] in Hlen; lia]).
      unfold src. rewrite Epl, firstn_nil. split; [lia|]. split; [cbn [length]; lia|].
      intros i Hi. cbn [length] in Hi. lia.
    - pose proof (bytes_at_transport rsegs [(Sp, Sp + 192)] mb m p pl (HPB ltac:(lia)) MU
        ltac:(cbn [disjoint_from]; split; [pose proof (HPL ltac:(lia)); lia | exact I])) as BA.
      unfold src. rewrite <- (firstn_skipn (Z.to_nat k) pl) in BA. apply bytes_at_app in BA as [BA _]. exact BA. }
  assert (LS : length src = Z.to_nat k) by (unfold src; rewrite length_firstn; lia).
  do 3 step.
  eapply evt_cut.
  { eapply (MC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m src).
    - rewrite unsigned_lit by lia. exact BS.
    - rewrite (unsigned_lit k) by lia. exact LS.
    - rewrite !unsigned_lit by lia. exact FRk.
    - rewrite !unsigned_lit by lia. destruct (Z.eq_dec n 0) as [N0|N0]; [lia | pose proof (HPL ltac:(lia)); lia].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & RW2 & _).
  rewrite !unsigned_lit in MU2, RW2 by lia.
  replace (ret_pc (Z_to_bv 64 0x12cc4)) with (Z_to_bv 64 0x12cc4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (rw_cells_transport rsegs [(Sp + 59, Sp + 59 + k)] m m2 Sp _) in FRa;
    [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I] ].
  apply (rw_cells_transport rsegs [(Sp + 59, Sp + 59 + k)] m m2 (Sp + 59 + k) _) in FRt;
    [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I] ].
  apply (rw_cells_transport rsegs [(Sp + 59, Sp + 59 + k)] m m2 (Sp + 112) _) in FRs;
    [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I] ].
  pose proof (munch_trans _ mb m m2 MU (munch_weaken [(Sp + 59, Sp + 59 + k)] [(Sp, Sp + 192)] m m2
    ltac:(unfold sub_fp; cbn [outside]; intros x [Hx _]; split; [lia | exact I]) MU2)) as MU'.
  pose proof (wmono_trans rsegs mb m m2 WM WM2) as WM'.
  replace (Sp + 59 + k) with (Sp + 59 + Z.of_nat (Z.to_nat k)) in FRt by lia.
  pose proof (rwc_join rsegs m2 (Sp + 59) (Z.to_nat k) (53 - Z.to_nat k) src (skipn (Z.to_nat k) jz) RW2 FRt) as RH.
  replace (Z.to_nat k + (53 - Z.to_nat k))%nat with 53%nat in RH by lia.
  apply rwc_c1 in RH.
  assert (FR : rw_cells rsegs m2 Sp (CB 59 ja :: map C1 (src ++ skipn (Z.to_nat k) jz))).
  { apply (rw_cells_app rsegs m2 Sp [CB 59 ja]); [exact FRa|]. cbn [cells_size csize].
    replace (Sp + Z.of_nat (59 + 0)) with (Sp + 59) by lia. exact RH. }
  eapply eA_tail; [exact H0 | exact H1 | exact Hn | | exact FR | exact FRs | exact MI2 | exact MU' | exact WM'].
  rewrite length_app, LS, length_skipn. lia.
Qed.

Lemma eA_evt : memset_contract -> memcpy_contract ->
  forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo Sp p n : Z) (pl : list byte),
    stk rsegs m lo (Sp + 192) -> 0 <= lo <= Sp -> Sp + 192 <= 2 ^ 63 -> mem_inv rsegs m ->
    0 <= n < 2 ^ 26 -> 0 <= p < 2 ^ 64 -> n = Z.of_nat (length pl) ->
    (0 < n -> bytes_at rsegs m p pl) -> (0 < n -> p + n <= lo) ->
    evt rsegs (qA F fc gp tp s3 s9 s10 s11 m Sp n p
                 [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra (Z_to_bv 64 (Sp + 192)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12c60) fc None m (seg_rom rsegs)).
Proof.
  intros MS_OK MC ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Sp p n pl ST Hlo H63 MI Hn Hp Hlen HPB HPL.
  pose proof (munch_refl [(Sp, Sp + 192)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 192%nat ST.
  replace (Sp + 0) with Sp in * by lia.
  do 14 step.
  rewrite (unsigned_lit n) by lia. if_false_by (eA_cond n ltac:(lia)).
  do 5 step.
  apply (rw_cells_split_CB rsegs _ Sp [] 112 _ _ [59; 53]%nat) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  destruct (rwc_cons _ _ _ _ _ FR) as [FRa FR1]. clear FR.
  destruct (rwc_cons _ _ _ _ _ FR1) as [FRh FRs]. clear FR1.
  cbn [csize] in FRh, FRs. change (Z.of_nat 59) with 59 in FRh, FRs. change (Z.of_nat 53) with 53 in FRs.
  replace (Sp + 59 + 53) with (Sp + 112) in FRs by lia.
  eapply evt_cut.
  { eapply MS_OK; [rewrite !unsigned_lit by lia; exact FRh | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & RW2).
  rewrite !unsigned_lit in MU2, RW2 by lia. change (Z.to_nat 53) with 53%nat in RW2.
  replace (ret_pc (Z_to_bv 64 0x12cac)) with (Z_to_bv 64 0x12cac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (rw_cells_transport rsegs [(Sp + 59, Sp + 59 + 53)] _ m2 Sp _) in FRa;
    [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I] ].
  apply (rw_cells_transport rsegs [(Sp + 59, Sp + 59 + 53)] _ m2 (Sp + 112) _) in FRs;
    [ | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I] ].
  pose proof (munch_trans _ m _ m2 MU (munch_weaken [(Sp + 59, Sp + 59 + 53)] [(Sp, Sp + 192)] _ m2
    ltac:(unfold sub_fp; cbn [outside]; intros x [Hx _]; split; [lia | exact I]) MU2)) as MU'.
  pose proof (wmono_trans rsegs m _ m2 WM WM2) as WM'.
  clear MU WM MU2 WM2.
  step. step.
  destruct (Z_lt_le_dec n 53) as [H53|H53].
  - take true.
    eapply (eA_cpy MC) with (k := n) (pl := pl);
      [ lia | lia | lia | lia | exact Hlen | lia | exact HPB | intros Hn0; pose proof (HPL Hn0); lia
      | exact FRa | exact RW2 | exact FRs | exact MI2 | exact MU' | exact WM' ].
  - take false. step.
    eapply (eA_cpy MC) with (k := 53) (pl := pl);
      [ lia | lia | lia | lia | exact Hlen | lia | exact HPB | intros Hn0; pose proof (HPL Hn0); lia
      | exact FRa | exact RW2 | exact FRs | exact MI2 | exact MU' | exact WM' ].
Qed.
