From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame strcmp_c bcmp_c same_c.
Import ListNotations.
Open Scope Z_scope.

Lemma memcmp_zero : forall n l r v, memcmp_model l r n = Some v -> length l = n -> length r = n -> (v = 0 <-> l = r).
Proof.
  induction n as [|n IH]; intros l r v H Hl Hr.
  - destruct l; [|cbn in Hl; lia]. destruct r; [|cbn in Hr; lia]. cbn in H. injection H as <-. tauto.
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [memcmp_model] in H. cbn [length] in Hl, Hr.
    destruct (bv_unsigned a =? bv_unsigned b) eqn:E.
    + apply Z.eqb_eq in E. rewrite (IH l r v H ltac:(lia) ltac:(lia)). split; intros G.
      * subst r. f_equal. apply bv_eq. exact E.
      * injection G as _ G. exact G.
    + apply Z.eqb_neq in E. injection H as <-. split; intros G; [lia|]. injection G as G _. subst b. lia.
Qed.

Lemma depth_k : forall u t, (depth u < depth t)%nat -> same_k u + 80 <= same_k t.
Proof. intros u t H. unfold same_k, SAME_FS. lia. Qed.

Lemma memcmp_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H; cbn in H.
  - injection H as <-. lia.
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    destruct (bv_unsigned a =? bv_unsigned b); [exact (IH l r v H)|].
    injection H as <-. pose proof (byte_range a). pose proof (byte_range b). lia.
Qed.

Definition same_at (ta : jv) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L : Z -> Z -> Prop) (lo pa pb : Z)
         (tb : jv) (Da Db : list (Z * Z)),
    a0 = Z_to_bv 64 pa -> a1 = Z_to_bv 64 pb ->
    pj_node rsegs m L pa ta Da -> pj_node rsegs m L pb tb Db ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + same_k ta <= bv_unsigned sp ->
    (forall z, pj_foot pa Da z -> outside [(bv_unsigned sp - same_k ta, bv_unsigned sp)] z) ->
    (forall z, pj_foot pb Db z -> outside [(bv_unsigned sp - same_k ta, bv_unsigned sp)] z) ->
    evt rsegs (same_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L lo pa pb ta tb Da Db)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SAME) fc None m (seg_rom rsegs)).

Section Body.
Hypothesis HSTR : strcmp_contract.
Hypothesis HBCMP : bcmp_contract.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (L : Z -> Z -> Prop) (lo pa pb : Z) (ta tb : jv) (Da Db : list (Z * Z)).
Hypothesis PA : pj_node rsegs m L pa ta Da.
Hypothesis PB : pj_node rsegs m L pb tb Db.
Hypothesis LO : lo + same_k ta <= bv_unsigned sp.
Hypothesis LO0 : 0 <= lo.
Hypothesis OA : forall z, pj_foot pa Da z -> outside [(bv_unsigned sp - same_k ta, bv_unsigned sp)] z.
Hypothesis OB : forall z, pj_foot pb Db z -> outside [(bv_unsigned sp - same_k ta, bv_unsigned sp)] z.
Hypothesis IH : forall u, (depth u < depth ta)%nat -> same_at u.

Lemma now_a : forall m1, munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m1 -> pj_node rsegs m1 L pa ta Da.
Proof using PA OA.
  intros m1 MU.
  exact (pj_node_munch rsegs _ m L m1 L pa ta Da PA (pj_node_blocks rsegs ta m L pa Da PA) MU OA).
Qed.

Lemma now_b : forall m1, munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m1 -> pj_node rsegs m1 L pb tb Db.
Proof using PB OB.
  intros m1 MU.
  exact (pj_node_munch rsegs _ m L m1 L pb tb Db PB (pj_node_blocks rsegs tb m L pb Db PB) MU OB).
Qed.

Lemma same_epi : forall m1 (junk : list byte) r ra1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23
    t3 t4 t5 t6,
  munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (ta = tb /\ r = Z_to_bv 64 1 \/ ta <> tb /\ r = Z_to_bv 64 0) ->
  evt rsegs (same_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L lo pa pb ta tb Da Db)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 r a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14304) fc None m1 (seg_rom rsegs)).
Proof using PA PB OA OB LO LO0.
  intros m1 junk r ra1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 MU WM MI ST FR RES.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (now_a m1 MU) as QA. pose proof (now_b m1 MU) as QB.
  assert (K80 : 80 <= same_k ta) by (unfold same_k, SAME_FS; lia).
  do 11 zstep.
  release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.

Definition loop_at (k i : nat) : Prop :=
  forall m1 (junk : list byte) ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x8 x9 x18 x19 x20 x21 x22 x23,
  (i + k = length (slots ta))%nat ->
  x8 = Z_to_bv 64 pb -> x9 = Z_to_bv 64 1 -> x18 = Z_to_bv 64 pa -> x19 = Z_to_bv 64 (tag ta) ->
  x20 = Z_to_bv 64 (Z.of_nat k) -> x21 = Z_to_bv 64 (8 * Z.of_nat i) -> x22 = Z_to_bv 64 (56 * Z.of_nat i) ->
  x23 = Z_to_bv 64 6 ->
  firstn i (slots ta) = firstn i (slots tb) ->
  munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (same_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L lo pa pb ta tb Da Db)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14344) fc None m1 (seg_rom rsegs)).

Lemma same_tail : forall k i o ua ub,
  (i + S k = length (slots ta))%nat -> (k = 0%nat \/ loop_at k (S i)) ->
  tag ta = tag tb -> (tag ta = 5 \/ tag ta = 6) -> length (slots ta) = length (slots tb) ->
  nth_error (slots ta) i = Some (o, ua) -> nth_error (slots tb) i = Some (o, ub) ->
  forall m1 (junk : list byte) ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x8 x9 x18 x19 x20 x21 x22 x23,
  x8 = Z_to_bv 64 pb -> x9 = Z_to_bv 64 1 -> x18 = Z_to_bv 64 pa -> x19 = Z_to_bv 64 (tag ta) ->
  x20 = Z_to_bv 64 (Z.of_nat (S k)) -> x21 = Z_to_bv 64 (8 * Z.of_nat i) -> x22 = Z_to_bv 64 (56 * Z.of_nat i) ->
  x23 = Z_to_bv 64 6 ->
  firstn i (slots ta) = firstn i (slots tb) ->
  munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -80) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (same_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L lo pa pb ta tb Da Db)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14368) fc None m1 (seg_rom rsegs)).
Proof using IH PA PB OA OB LO LO0.
  intros k i o ua ub HI HK ET TG LEN Ha Hb m1 junk ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    x8 x9 x18 x19 x20 x21 x22 x23 E8 E9 E18 E19 E20 E21 E22 E23 PRE MU WM MI ST FR.
  subst x8 x9 x18 x19 x20 x21 x22 x23.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (tag_range ta) as TGa.
  pose proof (now_a m1 MU) as QA. pose proof (now_b m1 MU) as QB.
  destruct (pj_slot _ _ _ _ _ _ _ _ _ QA Ha) as (numa & stra & kidsa & keysa & na & capa & D1a & HA & _ & _ & IA & FA & _).
  destruct (pj_slot _ _ _ _ _ _ _ _ _ QB Hb) as (numb & strb & kidsb & keysb & nb & capb & D1b & HB & _ & _ & IB & FB & _).
  destruct HA as ((ALa & (A0 & A1 & _)) & _ & _ & _ & KDa & _ & _ & _).
  destruct HB as ((ALb & (B0 & B1 & _)) & _ & _ & _ & KDb & _ & _ & _).
  pose proof (rd8 _ _ _ _ KDa) as RKa. pose proof (rd8 _ _ _ _ KDb) as RKb.
  pose proof (proj1 KDa) as Rka. pose proof (proj1 KDb) as Rkb.
  assert (RIa : 0 <= kidsa + 56 * Z.of_nat i /\ kidsa + 56 * Z.of_nat i + 56 <= 2 ^ 64).
  { cbn [pj_node] in IA. destruct ua; cbn [pj_node] in IA;
      destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & ((_ & (I0 & I1 & _)) & _) & _); lia. }
  assert (RIb : 0 <= kidsb + 56 * Z.of_nat i /\ kidsb + 56 * Z.of_nat i + 56 <= 2 ^ 64).
  { cbn [pj_node] in IB. destruct ub; cbn [pj_node] in IB;
      destruct IB as (_ & _ & _ & _ & _ & _ & _ & _ & ((_ & (I0 & I1 & _)) & _) & _); lia. }
  pose proof (slot_depth _ _ _ _ Ha) as DA. pose proof (depth_k _ _ DA) as KA.
  assert (K80 : 80 <= same_k ta) by (unfold same_k, SAME_FS; lia).
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  do 5 zstep.
  eapply evt_cut.
  { eapply (IH ua DA) with (pa := kidsa + 56 * Z.of_nat i) (pb := kidsb + 56 * Z.of_nat i) (tb := ub)
      (Da := D1a) (Db := D1b) (L := L) (lo := lo).
    - word_eq_tac.
    - word_eq_tac.
    - exact IA.
    - exact IB.
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. lia.
    - rewrite SPU. intros z Hz. pose proof (OA z (FA z Hz)) as Oz. cbn [outside] in Oz |- *. lia.
    - rewrite SPU. intros z Hz. pose proof (OB z (FB z Hz)) as Oz. cbn [outside] in Oz |- *. lia. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & ST2 & RES & _ & _).
  subst ms'. rewrite SPU in MU2, ST2.
  replace (ret_pc (Z_to_bv 64 0x1437c)) with (Z_to_bv 64 0x1437c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (FR2 := rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)).
  assert (MUF : munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU2]; intros x Hx; cbn [outside] in Hx |- *; lia]).
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMF.
  clear FR MU WM MI ST.
  zstep.
  destruct RES as [(EU & Er)|(NU & Er)]; subst r.
  - if_false. do 4 zstep.
    assert (PRE' : firstn (S i) (slots ta) = firstn (S i) (slots tb)).
    { apply (firstn_snoc_eq _ _ _ i (o, ua)); [exact Ha | rewrite EU; exact Hb | exact PRE]. }
    assert (LB : Z.of_nat (length (slots ta)) < 2 ^ 64).
    { destruct (pj_view _ _ _ _ _ _ QA) as (u1 & u2 & u3 & u4 & nA & u6 & HA' & NA' & _).
      destruct HA' as (_ & _ & _ & _ & _ & _ & (Rn & _) & _). lia. }
    destruct k as [|k].
    + if_true. eapply same_epi; try eassumption.
      left. split; [|reflexivity]. apply slots_eq; [exact ET | exact TG |].
      rewrite <- (firstn_all (slots ta)), <- (firstn_all (slots tb)), <- LEN.
      replace (length (slots ta)) with (S i) by lia. exact PRE'.
    + destruct HK as [HK|HL]; [lia|].
      replace (bv_eqb (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) (Z_to_bv 64 0)) with false
        by (rewrite bv_eqb_lit by lia; symmetry; apply Z.eqb_neq; lia).
      cbv beta iota. zstep.
      unfold loop_at in HL.
      eapply HL; first [exact PRE' | exact MUF | exact WMF | exact MI2 | exact ST2 | exact FR2 | lia | word_eq_tac].
  - if_true. zstep. eapply same_epi; try eassumption.
    right. split; [|reflexivity]. intros EQ. apply NU. rewrite EQ in Ha. rewrite Ha in Hb. congruence.
Qed.

Lemma same_iter : forall k i, (k = 0%nat \/ loop_at k (S i)) ->
  tag ta = tag tb -> (tag ta = 5 \/ tag ta = 6) -> length (slots ta) = length (slots tb) -> loop_at (S k) i.
Proof using HSTR IH PA PB OA OB LO LO0.
  intros k i HK ET TG LEN. unfold loop_at.
  intros m1 junk ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x8 x9 x18 x19 x20 x21 x22 x23
    HI E8 E9 E18 E19 E20 E21 E22 E23 PRE MU WM MI ST FR.
  subst x8 x9 x18 x19 x20 x21 x22 x23.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (K80 : 80 <= same_k ta) by (unfold same_k, SAME_FS; lia).
  pose proof (tag_range ta) as TGa.
  destruct (nth_error (slots ta) i) as [[oa ua]|] eqn:Ha; [|apply nth_error_None in Ha; lia].
  destruct (nth_error (slots tb) i) as [[ob ub]|] eqn:Hb; [|apply nth_error_None in Hb; lia].
  destruct (slot_kind _ _ _ _ Ha) as (KA6 & KA5). destruct (slot_kind _ _ _ _ Hb) as (KB6 & KB5).
  zstep.
  destruct TG as [T5|T6].
  - rewrite (KA5 T5) in Ha. rewrite (KB5 ltac:(lia)) in Hb.
    rewrite T5. if_true.
    eapply (same_tail k i None ua ub); first [eassumption | lia | reflexivity | (rewrite T5; reflexivity)].
  - destruct (KA6 T6) as (nma & Ea). destruct (KB6 ltac:(lia)) as (nmb & Eb). subst oa ob.
    pose proof (now_a m1 MU) as QA. pose proof (now_b m1 MU) as QB.
    destruct (pj_slot _ _ _ _ _ _ _ _ _ QA Ha)
      as (numa & stra & kidsa & keysa & na & capa & D1a & HA & _ & _ & _ & _ & (_ & xa & ka & Xa & Ca)).
    destruct (pj_slot _ _ _ _ _ _ _ _ _ QB Hb)
      as (numb & strb & kidsb & keysb & nb & capb & D1b & HB & _ & _ & _ & _ & (_ & xb & kb & Xb & Cb)).
    destruct HA as ((ALa & (A0 & A1 & _)) & _ & _ & _ & _ & KYa & _ & _).
    destruct HB as ((ALb & (B0 & B1 & _)) & _ & _ & _ & _ & KYb & _ & _).
    pose proof (rd8 _ _ _ _ KYa) as RYa. pose proof (rd8 _ _ _ _ KYb) as RYb.
    pose proof (rd8 _ _ _ _ Xa) as RXa. pose proof (rd8 _ _ _ _ Xb) as RXb.
    pose proof (proj1 KYa) as Rya. pose proof (proj1 KYb) as Ryb.
    pose proof (proj1 Xa) as Rxa. pose proof (proj1 Xb) as Rxb.
    assert (RKa : 0 <= keysa + 8 * Z.of_nat i /\ keysa + 8 * Z.of_nat i + 8 <= 2 ^ 64)
      by (destruct Xa as (_ & (Z0 & Z1 & _)); rewrite length_le8 in Z1; lia).
    assert (RKb : 0 <= keysb + 8 * Z.of_nat i /\ keysb + 8 * Z.of_nat i + 8 <= 2 ^ 64)
      by (destruct Xb as (_ & (Z0 & Z1 & _)); rewrite length_le8 in Z1; lia).
    rewrite T6. if_false.
    do 7 zstep.
    destruct (cstr_bytes _ _ _ _ _ _ Ca) as (BYa & NZa). destruct (cstr_bytes _ _ _ _ _ _ Cb) as (BYb & NZb).
    eapply evt_cut.
    { eapply HSTR with (sx := map (Z_to_bv 8) nma) (sy := map (Z_to_bv 8) nmb).
      - rewrite unsigned_lit by lia. exact BYa.
      - exact NZa.
      - rewrite unsigned_lit by lia. exact BYb.
      - exact NZb. }
    intros ms' (r & x11 & x12 & x13 & E & RE). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x14364)) with (Z_to_bv 64 0x14364) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zstep.
    destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER; cbv beta iota; cbn [negb].
    + apply bv_eqb_true in ER. subst r.
      assert (NM : nma = nmb)
        by (apply (map8_inj _ _ (cstr_forall _ _ _ _ _ _ Ca) (cstr_forall _ _ _ _ _ _ Cb)); apply RE; reflexivity).
      subst nmb.
      eapply (same_tail k i (Some nma) ua ub); first [eassumption | lia | reflexivity | (rewrite T6; reflexivity)].
    + apply bv_eqb_false in ER.
      zstep. eapply same_epi; try eassumption.
      right. split; [|reflexivity]. intros EQ. apply ER. apply RE. rewrite EQ in Ha. rewrite Ha in Hb.
      injection Hb as NM _. subst nmb. reflexivity.
Qed.

Lemma loop_all : forall k i, (0 < k)%nat -> tag ta = tag tb -> (tag ta = 5 \/ tag ta = 6) ->
  length (slots ta) = length (slots tb) -> loop_at k i.
Proof using HSTR IH PA PB OA OB LO LO0.
  induction k as [|k IHk]; intros i Hk ET TG LEN; [lia|].
  apply same_iter; try assumption.
  destruct k as [|k]; [left; reflexivity | right; apply IHk; auto; lia].
Qed.

Lemma same_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs (same_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L lo pa pb ta tb Da Db)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pa) (Z_to_bv 64 pb) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SAME) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI ST.
  unfold SAME.
  assert (K80 : 80 <= same_k ta) by (unfold same_k, SAME_FS; lia).
  pose proof (munch_refl [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  carve_frame 80%nat ST.
  do 10 zstep.
  pose proof (now_a m0 MU) as QA. pose proof (now_b m0 MU) as QB.
  destruct (pj_view _ _ _ _ _ _ QA) as (numa & stra & kidsa & keysa & na & capa & HA & NA & XA).
  destruct (pj_view _ _ _ _ _ _ QB) as (numb & strb & kidsb & keysb & nb & capb & HB & NB & XB).
  destruct HA as ((ALa & (A0 & A1 & _)) & Ta & NMa & SRa & KDa & KYa & Na & CPa).
  destruct HB as ((ALb & (B0 & B1 & _)) & Tb & NMb & SRb & KDb & KYb & Nb & CPb).
  pose proof (rd4 _ _ _ _ Ta) as RTa. pose proof (rd4 _ _ _ _ Tb) as RTb.
  pose proof (rd8 _ _ _ _ Na) as RNa. pose proof (rd8 _ _ _ _ Nb) as RNb.
  pose proof (tag_range ta) as TGa. pose proof (tag_range tb) as TGb.
  do 3 zstep.
  rewrite !sx32_small by lia.
  zstep.
  rewrite bv_eqb_lit by lia.
  destruct (Z.eqb_spec (tag ta) (tag tb)) as [ET|ET]; cbn [negb].
  2: { zstep. eapply same_epi; try eassumption.
       right. split; [intros E; apply ET; rewrite E; reflexivity | reflexivity]. }
  do 4 zstep.
  pose proof (proj1 Na) as Rna. pose proof (proj1 Nb) as Rnb.
  rewrite bv_eqb_lit by lia.
  destruct (Z.eqb_spec na nb) as [EN|EN]; cbn [negb].
  2: { zstep. eapply same_epi; try eassumption.
       right. split; [intros E; apply EN; rewrite NA, NB, E; reflexivity | reflexivity]. }
  destruct (tag_cases ta) as [Tg|[Tg|[Tg|[Tg|[Tg|[Tg|Tg]]]]]].
  1-3: (rewrite Tg; do 3 zstep; if_false; do 2 zstep; if_false; do 2 zstep; if_true;
        eapply same_epi; try eassumption; left; split; [apply scalar_eq; lia | reflexivity]).
  - rewrite Tg. do 3 zstep. if_false. do 2 zstep. if_false. do 2 zstep. if_false.
    destruct (tag_num ta Tg) as (txa & bta & Eta). destruct (tag_num tb ltac:(lia)) as (txb & btb & Etb).
    rewrite Eta in XA. rewrite Etb in XB. destruct XA as (Ena & ka & Ca). destruct XB as (Enb & kb & Cb).
    pose proof (rd8 _ _ _ _ SRa) as RSa. pose proof (rd8 _ _ _ _ SRb) as RSb.
    pose proof (proj1 SRa) as Rsa. pose proof (proj1 SRb) as Rsb.
    pose proof (proj1 NMa) as Rma. pose proof (proj1 NMb) as Rmb.
    do 3 zstep.
    destruct (cstr_bytes _ _ _ _ _ _ Ca) as (BYa & NZa). destruct (cstr_bytes _ _ _ _ _ _ Cb) as (BYb & NZb).
    eapply evt_cut.
    { eapply HSTR with (sx := map (Z_to_bv 8) txa) (sy := map (Z_to_bv 8) txb).
      - rewrite unsigned_lit by lia. exact BYa.
      - exact NZa.
      - rewrite unsigned_lit by lia. exact BYb.
      - exact NZb. }
    intros ms' (r & x11 & x12 & x13 & E & RE). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x142fc)) with (Z_to_bv 64 0x142fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zstep.
    destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER.
    + apply bv_eqb_true in ER. subst r.
      assert (TX : txa = txb)
        by (apply (map8_inj _ _ (cstr_forall _ _ _ _ _ _ Ca) (cstr_forall _ _ _ _ _ _ Cb)); apply RE; reflexivity).
      do 4 zstep.
      destruct (memcmp_model_total (le8 (Z_to_bv 64 numa)) (le8 (Z_to_bv 64 numb)) 8
                  ltac:(rewrite length_le8; lia) ltac:(rewrite length_le8; lia)) as (v & HV).
      eapply evt_cut.
      { eapply HBCMP with (ls := le8 (Z_to_bv 64 numa)) (rs := le8 (Z_to_bv 64 numb)) (v := v).
        - rewrite unsigned_lit by lia. exact (proj2 NMa).
        - rewrite unsigned_lit by lia. exact (proj2 NMb).
        - exact HV.
        - exact MI. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E2 & MU2 & WM2 & MI2 & _ & _).
      subst ms'.
      replace (ret_pc (Z_to_bv 64 0x143b4)) with (Z_to_bv 64 0x143b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      assert (FR2 := rw_cells_transport rsegs [] m0 m2 _ _ FR MU2 WM2 I).
      assert (ST2 := stk_transport_disjoint rsegs [] m0 m2 _ _ ST MU2 WM2 I).
      assert (MUF : munch [(bv_unsigned sp - same_k ta, bv_unsigned sp)] m m2)
        by (eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU2]; intros x _; exact I]).
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMF.
      do 2 zstep.
      eapply same_epi; try eassumption.
      pose proof (memcmp_range _ _ _ _ HV) as RV.
      pose proof (memcmp_zero 8 _ _ v HV ltac:(rewrite length_le8; reflexivity) ltac:(rewrite length_le8; reflexivity)) as ZV.
      destruct (Z.eq_dec v 0) as [V0|V0].
      * left. split.
        -- rewrite Eta, Etb, TX. f_equal. rewrite <- Ena, <- Enb. apply le8_inj; [lia | lia |]. apply ZV. exact V0.
        -- subst v. reflexivity.
      * right. split.
        -- intros EQ. rewrite Eta, Etb in EQ. injection EQ as E1 E2. apply V0. apply ZV. rewrite Ena, Enb, E2. reflexivity.
        -- f_equal. replace (v mod 18446744073709551616 <? 1) with false; [reflexivity|].
           symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
    + apply bv_eqb_false in ER.
      zstep. eapply same_epi; try eassumption.
      right. split; [|reflexivity]. intros EQ. apply ER. apply RE. rewrite Eta, Etb in EQ. injection EQ as E1 E2.
      subst. reflexivity.
  - rewrite Tg. do 3 zstep. if_false. do 2 zstep. if_true.
    destruct (tag_str ta Tg) as (sa & Eta). destruct (tag_str tb ltac:(lia)) as (sb & Etb).
    rewrite Eta in XA. rewrite Etb in XB. destruct XA as (ka & Ca). destruct XB as (kb & Cb).
    pose proof (rd8 _ _ _ _ SRa) as RSa. pose proof (rd8 _ _ _ _ SRb) as RSb.
    pose proof (proj1 SRa) as Rsa. pose proof (proj1 SRb) as Rsb.
    do 3 zstep.
    destruct (cstr_bytes _ _ _ _ _ _ Ca) as (BYa & NZa). destruct (cstr_bytes _ _ _ _ _ _ Cb) as (BYb & NZb).
    eapply evt_cut.
    { eapply HSTR with (sx := map (Z_to_bv 8) sa) (sy := map (Z_to_bv 8) sb).
      - rewrite unsigned_lit by lia. exact BYa.
      - exact NZa.
      - rewrite unsigned_lit by lia. exact BYb.
      - exact NZb. }
    intros ms' (r & x11 & x12 & x13 & E & RE). subst ms'.
    replace (ret_pc (Z_to_bv 64 0x143a0)) with (Z_to_bv 64 0x143a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    do 3 zstep.
    eapply same_epi; try eassumption.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rr.
    destruct (Z.eq_dec (bv_unsigned r) 0) as [R0|R0].
    + assert (Er : r = Z_to_bv 64 0) by (apply bv_eq; rewrite R0; reflexivity).
      left. split.
      * rewrite Eta, Etb. f_equal. apply (map8_inj _ _ (cstr_forall _ _ _ _ _ _ Ca) (cstr_forall _ _ _ _ _ _ Cb)).
        apply RE. exact Er.
      * rewrite R0. reflexivity.
    + right. split.
      * intros EQ. apply R0. rewrite Eta, Etb in EQ. injection EQ as EQ. subst sb.
        assert (Er : r = Z_to_bv 64 0) by (apply RE; reflexivity). rewrite Er. reflexivity.
      * replace (bv_unsigned r <? 1) with false; [reflexivity|]. symmetry. apply Z.ltb_ge. lia.
  - rewrite Tg. do 3 zstep. if_true. zstep.
    rewrite bv_eqb_lit by lia. destruct (Z.eqb_spec na 0) as [N0|N0]; cbv beta iota.
    + eapply same_epi; try eassumption.
      left. split; [|reflexivity]. apply slots_eq; [exact ET | lia |].
      assert (L0a : length (slots ta) = 0%nat) by lia. assert (L0b : length (slots tb) = 0%nat) by lia.
      apply length_zero_iff_nil in L0a, L0b. rewrite L0a, L0b. reflexivity.
    + do 3 zstep.
      pose proof (loop_all (length (slots ta)) 0 ltac:(lia) ET ltac:(lia) ltac:(lia)) as LP. unfold loop_at in LP.
      eapply LP; first [eassumption | reflexivity | lia | (rewrite Tg; reflexivity) | word_eq_tac].
  - rewrite Tg. do 3 zstep. if_true. zstep.
    rewrite bv_eqb_lit by lia. destruct (Z.eqb_spec na 0) as [N0|N0]; cbv beta iota.
    + eapply same_epi; try eassumption.
      left. split; [|reflexivity]. apply slots_eq; [exact ET | lia |].
      assert (L0a : length (slots ta) = 0%nat) by lia. assert (L0b : length (slots tb) = 0%nat) by lia.
      apply length_zero_iff_nil in L0a, L0b. rewrite L0a, L0b. reflexivity.
    + do 3 zstep.
      pose proof (loop_all (length (slots ta)) 0 ltac:(lia) ET ltac:(lia) ltac:(lia)) as LP. unfold loop_at in LP.
      eapply LP; first [eassumption | reflexivity | lia | (rewrite Tg; reflexivity) | word_eq_tac].
Qed.

End Body.

Lemma same_all : strcmp_contract -> bcmp_contract -> forall n ta, (depth ta < n)%nat -> same_at ta.
Proof.
  intros HS HB n. induction n as [|n IHn]; intros ta Hd; [lia|].
  unfold same_at.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m L lo pa pb tb Da Db E0 E1 PA PB MI ST LO OA OB.
  subst a0 a1.
  eapply same_body; first [exact HS | exact HB | eassumption | exact (proj1 ST) | (intros u Hu; apply IHn; lia)].
Qed.

Theorem same_holds : strcmp_contract -> bcmp_contract -> same_contract.
Proof.
  intros HS HB. unfold same_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m L lo pa pb ta tb Da Db.
  exact (same_all HS HB (S (depth ta)) ta (Nat.lt_succ_diag_r _) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L lo pa pb tb Da Db).
Qed.
