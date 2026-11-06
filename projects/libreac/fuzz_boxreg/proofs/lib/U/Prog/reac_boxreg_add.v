From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep lowest_free_base_c
  mac_is_zero_c reac_boxreg_find_c memset_c memcpy_c reac_boxreg_add_c reac_boxreg_add_inv.
Import ListNotations.
Open Scope Z_scope.

Ltac bx_cond :=
  try (match goal with |- context [MS _ _ (if ?c then _ else _) _ _ _ _] =>
    let c' := eval vm_compute in c in change c with c' end; cbv beta iota).


Lemma uadd_zl : forall (d : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (q : Z) (M : list byte),
  d = Z.to_nat (6 - j) -> 0 <= j <= 5 -> bytes_at rsegs m q M -> length M = 6%nat ->
  a7 = Z_to_bv 64 j -> a4 = Z_to_bv 64 q -> a3 = Z_to_bv 64 5 ->
  a5 = Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 q)) 18446744073709551615) ->
  (forall i, 0 <= i < j -> nth_error M (Z.to_nat i) = Some (Z_to_bv 8 0)) ->
  (forall x16 x17 v, 0 <= v < 256 -> (v = 0 <-> M = zero6) ->
     evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 v) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13ec4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ea8) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros j ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q
      q M Hd Hj HB HML E7 E4 E3 E5 HZ K; [lia|].
  subst a7 a4 a3 a5.
  pose proof (bytes_at_bound rsegs m q M HB) as QB. rewrite HML in QB.
  destruct (nth_error M (Z.to_nat j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (bx_byte1 m q M j b HB ltac:(lia) Eb) as RD.
  step. rewrite bx_lxor_ltu by lia. bx_cond.
  step. step. step. step.
  unfold zxb. pose proof (bx_byte_range b) as Rb. rewrite bx_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [Bz|Bnz]; cbn [negb].
  - assert (Eb0 : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Bz; reflexivity).
    step. step. rewrite bx_eqb by lia.
    destruct (Z.eqb_spec j 5) as [J5|J5]; bx_cond.
    + subst j.
      eapply (K _ _ (bv_unsigned b)); [lia|]. split; [|intros; lia]. intros _.
      apply bx_zero6_of; [exact HML|]. intros i Hi.
      destruct (Nat.eq_dec i 5) as [->|Ni]; [subst b; exact Eb|].
      replace i with (Z.to_nat (Z.of_nat i)) by lia. apply HZ. lia.
    + eapply (IH (j + 1)); [lia | lia | exact HB | exact HML | f_equal; lia | reflexivity | reflexivity | reflexivity
                           | | exact K].
      intros i Hi. destruct (Z.eq_dec i j) as [->|Ni]; [subst b; exact Eb|]. apply HZ. lia.
  - eapply (K _ _ (bv_unsigned b)); [lia|]. split; [intros; lia|].
    intros EZ. rewrite EZ in Eb. apply bx_zero6_nth in Eb. subst b. reflexivity.
Qed.

Lemma uadd_loop : forall (d : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (r n k : Z) (bs : list byte),
  d = Z.to_nat (n - i) -> 0 <= i < n -> n = bx_n bs -> n <= 5 -> bytes_at rsegs m r bs -> length bs = 288%nat ->
  -2^31 <= k < 2^31 ->
  s3 = Z_to_bv 64 i -> a4 = Z_to_bv 64 (r + 56 * i) -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 5 ->
  s2 = Z_to_bv 64 r -> s0 = Z_to_bv 64 k ->
  s5 = Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615) ->
  (forall j, 0 <= j < i -> ~ (bx_mac bs j = zero6 /\ bx_nch bs j = k)) ->
  (forall j (x5 x12 x13 x14 x15 x16 x17 : word), add_unbound bs k j ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 t1 t2 (Z_to_bv 64 k) s1 (Z_to_bv 64 (r + 56 * j)) a1 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 j) s4
                          (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615))
                          s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13f58) fc None m (seg_rom rsegs))) ->
  ((forall j, 0 <= j < n -> ~ (bx_mac bs j = zero6 /\ bx_nch bs j = k)) ->
   forall (x5 x10 x12 x13 x14 x15 x16 x17 : word),
     evt rsegs Q (MS (mkR ra sp gp tp x5 t1 t2 (Z_to_bv 64 k) s1 x10 a1 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 n) s4
                          (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615))
                          s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13edc) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13e88) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q
      r n k bs Hd Hi Hn Hn5 HB HL Hk E19 E14 E12 E13 E18 E8 E21 HP KB KN; [lia|].
  subst s3 a4 a2 a3 s2 s0 s5.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB. rewrite HL in RB.
  assert (NEXT : ~ (bx_mac bs i = zero6 /\ bx_nch bs i = k) -> forall x5 x10 x15 x16 x17 : word,
     evt rsegs Q (MS (mkR ra sp gp tp x5 t1 t2 (Z_to_bv 64 k) s1 x10 a1 (Z_to_bv 64 n) (Z_to_bv 64 5)
                          (Z_to_bv 64 (r + 56 * i)) x15 x16 x17 (Z_to_bv 64 r) (Z_to_bv 64 i) s4
                          (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615))
                          s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13ed0) fc None m (seg_rom rsegs))).
  { intros NU x5 x10 x15 x16 x17. step. step. step.
    rewrite bx_eqb by lia. destruct (Z.eqb_spec (i + 1) n) as [En|En]; bx_cond.
    - rewrite En. apply KN. intros j Hj. destruct (Z.eq_dec j i) as [->|Nj]; [exact NU|]. apply HP. lia.
    - eapply (IH (i + 1)) with (r := r) (n := n) (k := k) (bs := bs);
        [lia | lia | exact Hn | exact Hn5 | exact HB | exact HL | exact Hk | reflexivity
        | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact KB | exact KN].
      intros j Hj. destruct (Z.eq_dec j i) as [->|Nj]; [exact NU|]. apply HP. lia. }
  step. rewrite bx_eqb by lia. replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; lia). bx_cond.
  step. step. step. rewrite bx_off56 by lia.
  step. rewrite bx_lxor_ltu by lia. bx_cond.
  step. step. step.
  assert (HX : bytes_at rsegs m (r + 56 * i) (bx_mac bs i))
    by (apply bytes_at_bsub; [exact HB | lia | lia | rewrite HL; lia]).
  assert (HXL : length (bx_mac bs i) = 6%nat) by (apply bsub_length; rewrite ?HL; lia).
  eapply (uadd_zl 6%nat 0) with (q := r + 56 * i) (M := bx_mac bs i);
    [reflexivity | lia | exact HX | exact HXL | reflexivity | reflexivity | reflexivity | reflexivity | intros; lia | ].
  intros x16 x17 v Hv HZv.
  step. rewrite bx_eqb by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; bx_cond.
  - pose proof (rd4_bytes_at m r bs (56 * i + 12) HB ltac:(lia) ltac:(rewrite HL; lia)) as BC.
    replace (r + (56 * i + 12)) with (r + 56 * i + 12) in BC by lia.
    change (rd4 bs (56 * i + 12)) with (bx_nch bs i) in BC.
    pose proof (bx_ov4 _ _ _ BC) as RC.
    step. rewrite bx_sx32 by (apply rd4_range).
    step. rewrite bx_eqb by (pose proof (rd4_range bs (56 * i + 12)); unfold bx_nch; lia).
    destruct (Z.eqb_spec (bx_nch bs i) k) as [C1|C1]; bx_cond.
    + apply KB. split; [lia|]. split; [apply HZv; exact V0|]. split; [exact C1|]. exact HP.
    + apply NEXT. intros [_ C]. exact (C1 C).
  - apply NEXT. intros [Z _]. apply V0. apply HZv. exact Z.
Qed.


Lemma bx_mask : forall n, 0 < n < 2^63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 n)))))
                     (bv_unsigned (Z_to_bv 64 n))) = Z_to_bv 64 n.
Proof.
  intros n Hn. unfold v_slt. try unfold c_lts. rewrite bx_lts by lia.
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite (unsigned_lit n) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Theorem reac_boxreg_add_holds :
  mac_is_zero_contract -> reac_boxreg_find_contract -> lowest_free_base_contract -> memset_contract ->
  memcpy_contract -> reac_boxreg_add_contract.
Proof.
  intros MZ FIND LFB MEMS MEMC. unfold reac_boxreg_add_contract, REAC_BOXREG_ADD, ADD_K.
  unfold mac_is_zero_contract, MAC_IS_ZERO in MZ.
  unfold reac_boxreg_find_contract, REAC_BOXREG_FIND, REAC_BOXREG_FIND_FRAME in FIND.
  unfold lowest_free_base_contract, LOWEST_FREE_BASE, LOWEST_FREE_BASE_FRAME in LFB.
  unfold memset_contract, MEMSET in MEMS. unfold memcpy_contract, memcpy_entry in MEMC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r p k lo bs M -> -> -> Hk Hr8 Hr0 Hp0 HB HW HI HM HML DJ1 ST LO DJ2 DJ3 MI.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB.
  pose proof (bytes_at_bound rsegs m p M HM) as PB.
  destruct HI as [[HL [H1 [H2 [H3 [H4 [H5 H6]]]]]] H7].
  rewrite HL in RB. rewrite HML in PB.
  assert (Hn : 0 <= bx_n bs <= 5) by exact H1.
  assert (R4 : r mod 4 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (rd4_bytes_at m r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)) as BF.
  pose proof (rd4_bytes_at m r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as BN.
  change (rd4 bs 284) with (bx_fabric bs) in BF. change (rd4 bs 280) with (bx_n bs) in BN.
  pose proof (rd4_range bs 284) as RFb. change (rd4 bs 284) with (bx_fabric bs) in RFb.
  pose proof (munch_refl [(lo, bv_unsigned sp); (r, r + 288)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EPI : forall (m' : word -> option byte) (z : Z) (bs' j0 : list byte)
     (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 : word),
     -2^31 <= z < 2^31 -> add_out bs M k z bs' -> bytes_at rsegs m' r bs' ->
     rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     stk rsegs m' lo (bv_unsigned sp + -64) ->
     munch [(lo, bv_unsigned sp); (r, r + 288)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                           x18 (Z_to_bv 64 z) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x13e28) fc None m' (seg_rom rsegs))).
  { intros m' z bs' j0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31
      Hz HO HB' FR' ST' MU' WM' MI'.
    do 8 step. release_frame FR' ST' (bv_unsigned sp). step. step.
    apply evt_done. unfold QQ. do 15 eexists. exists m', z, bs'. split; [reflexivity|].
    split; [f_equal; apply bx_swrap_z; exact Hz|].
    split; [exact HO|]. split; [exact HB'|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|exact ST']. }
  carve_frame 64%nat ST.
  do 13 step.
  rewrite bx_wtest by lia.
  destruct (Z.leb_spec 2 k) as [Hk2|Hk2]; [destruct (Z.leb_spec k 40) as [Hk40|Hk40]|]; cbn [andb negb].
  2,3: (step; eapply EPI with (bs' := bs); [lia | left; split; [left; intros (_ & Hw & _); lia | split; reflexivity]
          | exact HB | exact FR | exact ST | exact MU | exact WM | exact MI]).
  do 3 step.
  rewrite bx_land1 by lia. rewrite bx_eqb by (pose proof (Z.mod_pos_bound k 2); lia).
  destruct (Z.eqb_spec (k mod 2) 0) as [Hev|Hod]; cbn [negb].
  2: (step; eapply EPI with (bs' := bs);
        [lia | left; split; [left; intros (He & _); apply Hod, bx_even, He | split; reflexivity]
        | exact HB | exact FR | exact ST | exact MU | exact WM | exact MI]).
  step. rewrite eqb_lit by lia. destruct (Z.eqb_spec r 0) as [Rz|Rz]; [lia|]. bx_cond.
  step. rewrite bx_land3 by lia. rewrite R4. step. bx_cond.
  pose proof (bx_ov4 _ _ _ BF) as RF.
  step. rewrite bx_sx32 by lia.
  step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec (bx_fabric bs) k) as [Hfk|Hfk]; bx_cond.
  { step; eapply EPI with (bs' := bs); [lia | left; split; [left; intros (_ & _ & Hw); lia | split; reflexivity]
          | exact HB | exact FR | exact ST | exact MU | exact WM | exact MI]. }
  assert (WOK : add_width_ok k (bx_fabric bs)) by (split; [apply bx_even; exact Hev | lia]).
  step. step.
  eapply evt_cut.
  { eapply MZ; [reflexivity | exact Hp0 | exact HM | exact HML]. }
  intros ms' PO.
  destruct PO as (y5 & y6 & y7 & res & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & E & RR).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 81440)) with (Z_to_bv 64 81440) by (apply bv_eq; vm_compute; reflexivity).
  destruct RR as [(Z6 & ->) | (MNZ & ->)].
  { step. bx_cond. step. eapply EPI with (bs' := bs); [lia | left; split; [right; exact Z6 | split; reflexivity]
          | exact HB | exact FR | exact ST | exact MU | exact WM | exact MI]. }
  step. bx_cond.
  step. step. step.
  assert (SPL : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply FIND; [reflexivity | reflexivity | exact HB | exact HL | exact H1 | exact HM | exact HML | exact Hr0 | exact R4
                 | exact Hp0 | rewrite SPL; exact ST | rewrite SPL; lia | rewrite SPL; lia | rewrite SPL; lia | exact MI]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & res & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
                  & E & MUc & WMc & MI1 & ST1 & HB1 & HM1 & z & Ez & Hfr).
  subst ms' res. rewrite SPL in MUc, ST1.
  replace (ret_pc (Z_to_bv 64 81500)) with (Z_to_bv 64 81500) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m0 m1 MUc WMc. clear MUc WMc MI.
  assert (Hz : -1 <= z < 5).
  { destruct Hfr as [(? & ->) | [(_ & Hz & _) | (_ & -> & _)]]; lia. }
  step. step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec z 0) as [Zn|Zn]; bx_cond.
  2: { eapply EPI with (bs' := bs); [lia | | exact HB1 | exact FR | exact ST1 | exact MU | exact WM | exact MI1].
       right; left. split; [exact WOK|]. split; [exact MNZ|]. split; [|reflexivity].
       destruct Hfr as [(E0 & _) | [(_ & Hf) | (_ & E1 & _)]]; [exfalso; exact (MNZ E0) | exact Hf | lia]. }
  assert (Zm : z = -1) by lia.
  assert (NH : add_none_held bs M).
  { destruct Hfr as [(E0 & _) | [(_ & Hf & _) | (_ & _ & Hnh)]]; [exfalso; exact (MNZ E0) | lia | exact Hnh]. }
  pose proof (bx_ov4 _ _ _ BN) as RN.
  step. rewrite bx_sx32 by (apply rd4_range).
  assert (NEWROW : add_none_unbound bs k ->
    forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 k)
                          (Z_to_bv 64 p) x10 (Z_to_bv 64 (bx_n bs)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 s4
                          (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 r)) 18446744073709551615))
                          s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13edc) fc None m1 (seg_rom rsegs))).
  { intros NU x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31.
    step. step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec 4 (bx_n bs)) as [N5|N5]; bx_cond.
    { step. eapply EPI with (bs' := bs); [lia | | exact HB1 | exact FR | exact ST1 | exact MU | exact WM | exact MI1].
      right; right; right; left. split; [exact WOK|]. split; [exact MNZ|]. split; [exact NH|]. split; [exact NU|].
      split; [left; lia | split; reflexivity]. }
    assert (KB1 : bx_keep (bytes_at rsegs m1 r bs)) by exact HB1.
    pose proof (bx_rw_sub m1 r bs (56 * bx_n bs) 56 HB1 ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as ROW.
    pose proof (bx_rw_sub m1 r bs 280 4 HB1 ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as NF.
    rewrite <- le4_rd4 in NF by (apply bsub_length; rewrite ?HL; lia).
    change (rd4 bs 280) with (bx_n bs) in NF. change (Z.to_nat 56) with 56%nat in ROW.
    change (Z.to_nat 4) with 4%nat in NF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (r + 56 * bx_n bs, r + 56 * bx_n bs + 56); (r + 280, r + 284)] m1)
      as MU1.
    step. step. step.
    eapply evt_cut.
    { eapply LFB; [reflexivity | reflexivity | lia | exact HB1 | exact HL | exact H1 | exact H2 | exact H3 | exact R4
                  | rewrite SPL; exact ST1 | rewrite SPL; lia | rewrite SPL; lia | exact MI1]. }
    intros ms' PO.
    destruct PO as (u5 & u6 & u7 & res & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2 & E
                    & MUc & WMc & MI2 & ST2 & lf & Elf & Hlf).
    subst ms' res. rewrite SPL in MUc, ST2.
    replace (ret_pc (Z_to_bv 64 81648)) with (Z_to_bv 64 81648) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI1.
    assert (Hlfr : -1 <= lf <= 40) by (destruct Hlf as [(-> & _) | (HA & HB' & _)]; unfold boxreg_B2 in H2; lia).
    step. step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec lf 0) as [Ln|Ln]; bx_cond.
    { eapply EPI with (bs' := bs); [lia | | exact HB1 | exact FR | exact ST2 | exact MU | exact WM | exact MI2].
      right; right; right; left. split; [exact WOK|]. split; [exact MNZ|]. split; [exact NH|]. split; [exact NU|].
      split; [right; replace (-1) with lf by lia; exact Hlf | split; reflexivity]. }
    step.
    step. rewrite bx_sx32 by lia.
    step. step. rewrite bx_ltu by lia. replace (5 <? bx_n bs) with false by (symmetry; apply Z.ltb_ge; lia). bx_cond.
    step. step. step. rewrite bx_off56 by lia.
    step. rewrite bx_lxor_ltu by lia. bx_cond.
    do 5 step.
    eapply evt_cut.
    { eapply MEMS; [ | exact MI2 ].
      rewrite (unsigned_lit (r + 56 * bx_n bs)) by lia. rewrite (unsigned_lit 56) by lia. exact ROW. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m3 & E & MUc & WMc
                    & MI3 & RZ).
    subst ms'.
    rewrite (unsigned_lit (r + 56 * bx_n bs)) in MUc, RZ by lia. rewrite (unsigned_lit 56) in MUc, RZ by lia.
    try rewrite (unsigned_lit 0) in RZ by lia. change (Z.to_nat 56) with 56%nat in RZ.
    try change (0 mod 256) with 0 in RZ.
    replace (ret_pc (Z_to_bv 64 81708)) with (Z_to_bv 64 81708) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2.
    change 56%nat with (6 + 50)%nat in RZ. apply bx_rw_split in RZ. destruct RZ as [R6 R50].
    rewrite bx_firstn_repeat in R6. rewrite bx_skipn_repeat in R50.
    do 4 step.
    eapply evt_cut.
    { eapply MEMC; [ | | | | exact MI3 ].
      - rewrite (unsigned_lit p) by lia. exact HM1.
      - rewrite (unsigned_lit 6) by lia. exact HML.
      - rewrite (unsigned_lit (r + 56 * bx_n bs)) by lia. rewrite (unsigned_lit 6) by lia. exact R6.
      - rewrite (unsigned_lit (r + 56 * bx_n bs)) by lia. rewrite (unsigned_lit p) by lia.
        rewrite (unsigned_lit 6) by lia. lia. }
    intros ms' PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & E & MUc & WMc
                    & MI4 & RC & HM4).
    subst ms'.
    rewrite (unsigned_lit (r + 56 * bx_n bs)) in MUc, RC by lia. rewrite (unsigned_lit 6) in MUc, RC by lia.
    rewrite (unsigned_lit p) in HM4 by lia. change (Z.to_nat 6) with 6%nat in RC.
    replace (ret_pc (Z_to_bv 64 81724)) with (Z_to_bv 64 81724) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3.
    pose proof (bx_rw_app m4 _ _ _ RC R50) as ROWC. clear RC R50. cbn [app] in ROWC.
    step. rewrite bx_sx32 by lia.
    step. rewrite swrap_addi by lia.
    step. step.
    step. rewrite bx_lts by lia. replace (bx_n bs + 1 <? bx_n bs) with false by (symmetry; apply Z.ltb_ge; lia).
    bx_cond.
    step. step.
    pose proof (bx_rw_bytes _ _ _ ROWC) as RWB. cbn [cells_bytes cbytes] in RWB.
    pose proof (bx_rw_bytes _ _ _ NF) as NFB. cbn [cells_bytes cbytes] in NFB. rewrite app_nil_r in NFB.
    eapply EPI with (bs' := add_bytes bs M lf k); [lia | | | exact FR | exact ST2 | exact MU | exact WM | exact MI4].
    + right; right; right; right. split; [exact WOK|]. split; [exact MNZ|]. split; [exact NH|]. split; [exact NU|].
      split; [lia|]. split; [reflexivity|]. exists lf. split; [lia|]. split; [exact Hlf | reflexivity].
    + unfold add_bytes. eapply bx_patch2; [exact KB1 | exact MU1 | | | | | ].
      * replace (r + Z.of_nat (Z.to_nat (56 * bx_n bs))) with (r + 56 * bx_n bs) by lia.
        eapply bytes_at_ext; [exact RWB|].
        unfold add_row. rewrite app_nil_r.
        replace (firstn 2 (repeat (Z_to_bv 8 0) 50)) with (repeat (Z_to_bv 8 0) 2) by reflexivity.
        replace (skipn 4 (skipn 6 (repeat (Z_to_bv 8 0) 50)))
          with (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 32) by (vm_compute; reflexivity).
        reflexivity.
      * replace (r + Z.of_nat 280) with (r + 280) by lia. exact NFB.
      * rewrite add_row_length by exact HML. lia.
      * rewrite length_le4, HL. lia.
      * intros i Hi Ha Hb. rewrite add_row_length in Ha by exact HML. rewrite length_le4 in Hb. rewrite HL in Hi.
        cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  step. step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec 0 (bx_n bs)) as [Np|Np]; bx_cond.
  2: { apply NEWROW. intros j Hj; lia. }
  do 6 step. rewrite bx_mask by lia.
  eapply (uadd_loop (Z.to_nat (bx_n bs)) 0) with (r := r) (n := bx_n bs) (k := k) (bs := bs);
    [lia | lia | reflexivity | lia | exact HB1 | exact HL | lia | reflexivity | f_equal; lia | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | intros; lia | | ].
  - intros j x5 x12 x13 x14 x15 x16 x17 HU.
    assert (Hj : 0 <= j < bx_n bs) by (destruct HU; lia).
    assert (KB1 : bx_keep (bytes_at rsegs m1 r bs)) by exact HB1.
    pose proof (bx_rw_sub m1 r bs (56 * j) 6 HB1 ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as ROW6.
    change (Z.to_nat 6) with 6%nat in ROW6.
    pose proof (munch_refl [(lo, bv_unsigned sp); (r + 56 * j, r + 56 * j + 6)] m1) as MU1.
    step. step. step.
    eapply evt_cut.
    { eapply MEMC; [ | | | | exact MI1 ].
      - rewrite (unsigned_lit p) by lia. exact HM1.
      - rewrite (unsigned_lit 6) by lia. exact HML.
      - rewrite (unsigned_lit (r + 56 * j)) by lia. rewrite (unsigned_lit 6) by lia. exact ROW6.
      - rewrite (unsigned_lit (r + 56 * j)) by lia. rewrite (unsigned_lit p) by lia.
        rewrite (unsigned_lit 6) by lia. lia. }
    intros ms' PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m2 & E & MUc & WMc
                    & MI2 & RC & HM2).
    subst ms'.
    rewrite (unsigned_lit (r + 56 * j)) in MUc, RC by lia. rewrite (unsigned_lit 6) in MUc, RC by lia.
    rewrite (unsigned_lit p) in HM2 by lia. change (Z.to_nat 6) with 6%nat in RC.
    replace (ret_pc (Z_to_bv 64 81764)) with (Z_to_bv 64 81764) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI1.
    pose proof (bx_rw_bytes _ _ _ RC) as RCB. cbn [cells_bytes cbytes] in RCB. rewrite app_nil_r in RCB.
    step.
    eapply EPI with (bs' := upd_bytes bs (Z.to_nat (56 * j)) M);
      [lia | | | exact FR | exact ST1 | exact MU | exact WM | exact MI2].
    + right; right; left. split; [exact WOK|]. split; [exact MNZ|]. split; [exact NH|]. split; [exact HU|reflexivity].
    + eapply bx_patch1; [exact KB1 | exact MU1 | | | ].
      * replace (r + Z.of_nat (Z.to_nat (56 * j))) with (r + 56 * j) by lia. exact RCB.
      * rewrite HL, HML. lia.
      * intros i Hi Hni. rewrite HL in Hi. rewrite HML in Hni. cbn [outside]. split; [lia|]. split; [lia | exact I].
  - intros NUall x5 x10 x12 x13 x14 x15 x16 x17. apply NEWROW. exact NUall.
Qed.
