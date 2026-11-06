From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct parse_items_shape pj_get_c memcpy_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Definition PS_ENTRY : Z := 0x14718.
Definition PS_FREE_RET : Z := 0x1474c.
Definition PS_GROW_RET : Z := 0x1477c.
Definition PS_FREEW_RET : Z := 0x14788.
Definition PS_SD_RET : Z := 0x147b0.
Definition PS_PJ_FREE : Z := 0x145a4.
Definition PS_GROW : Z := 0x147e8.
Definition PS_STRDUP : Z := 0x1416c.

Lemma ps_node_hdr : forall m lblk p t D, pj_node rsegs m lblk p t D ->
  exists num str kids keys n cap, pj_hdr rsegs m p (tag t) num str kids keys n cap.
Proof.
  intros m lblk p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _); exists num, str, kids, keys, n, cap; exact Hh.
Qed.

Lemma ps_node_range : forall m lblk p t D, pj_node rsegs m lblk p t D -> 0 <= p /\ p + 56 <= 2 ^ 64 /\ p mod 8 = 0.
Proof.
  intros m lblk p t D H. destruct (ps_node_hdr m lblk p t D H) as (num & str & kids & keys & n & cap & ((A & B0 & B1 & _) & _)).
  lia.
Qed.

Lemma ps_hit_pos : forall m lblk o ms D kname z,
  (forall a n, lblk a n -> 0 < a) -> pj_node rsegs m lblk o (JObj ms) D -> pj_get_hit m lblk o ms D kname z ->
  0 < z /\ z + 56 <= 2 ^ 64.
Proof.
  intros m lblk o ms D kname z HL HN (i & v & kids & Di & Hi & _ & Hk & -> & Hv & _).
  pose proof (ps_node_range m lblk _ v Di Hv) as (R0 & R1 & _).
  cbn [pj_node] in HN. destruct HN as (_ & _ & num & str & kids' & keys & n & cap & Hh & Es & En & Hc & Hcap & _).
  pose proof Hh as (_ & _ & _ & _ & Hk' & _).
  pose proof (pj_u64_uniq rsegs m (o + 24) kids kids' Hk Hk') as <-.
  assert (Hl : (i < length ms)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  destruct Hcap as [(C0 & _)|(Cp & L0 & _)]; [lia|].
  pose proof (HL _ _ L0). lia.
Qed.

Definition sa_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lblk : Z -> Z -> Prop) (lo o k w : Z) (ms : list (list Z * jv))
    (D : list (Z * Z)) (kname : list Z) : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte)
                   (junk : list byte) (z : Z),
    munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -48) /\
    rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    pj_node rsegs m1 lblk o (JObj ms) D /\ pj_cbytes rsegs m1 k kname /\
    pj_get_res m1 lblk o (JObj ms) D kname z /\ 0 <= z < 2 ^ 64 /\
    ((z = 0 /\
      st = MS (mkR (Z_to_bv 64 PS_GROW_RET) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                 (Z_to_bv 64 w) (Z_to_bv 64 o) (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 k) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PS_GROW) fc None m1 (seg_rom rsegs))
     \/ (z <> 0 /\
      st = MS (mkR (Z_to_bv 64 PS_FREE_RET) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                 (Z_to_bv 64 w) (Z_to_bv 64 o) (Z_to_bv 64 z) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 k) (Z_to_bv 64 z) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PS_PJ_FREE) fc None m1 (seg_rom rsegs))).

Lemma ps_sa : pj_get_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lblk : Z -> Z -> Prop)
         (lo o k w : Z) (ms : list (list Z * jv)) (D : list (Z * Z)) (kname : list Z),
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 w -> o <> 0 ->
    pj_node rsegs m lblk o (JObj ms) D -> pj_cbytes rsegs m k kname ->
    (forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\
       disjoint_from [(a, a + n)] (bv_unsigned sp - 96) 96) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
    disjoint_from [(o, o + 56); (k, k + Z.of_nat (length kname) + 1)] (bv_unsigned sp - 96) 96 ->
    mem_inv rsegs m ->
    evt rsegs (sa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lblk lo o k w ms D kname)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PS_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros HGET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lblk
    lo o k w ms D kname A0 A1 A2 ONZ HN HC HL SPA ST LO DJ MI. subst a0 a1 a2.
  unfold PS_ENTRY.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  cbn [disjoint_from] in DJ.
  pose proof ST as (STa & STb & _).
  carve_frame 48%nat ST.
  do 10 step.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HN0 : pj_node rsegs m0 lblk o (JObj ms) D).
  { apply (pj_node_munch rsegs [(bv_unsigned sp + -96, bv_unsigned sp)] m lblk m0 lblk o (JObj ms) D HN);
      [intros a n Hb; exact (pis_node_lblk rsegs _ m lblk o D HN (a, n) Hb) | exact MU |].
    intros zz Hz. cbn [outside]. split; [|exact I].
    destruct Hz as [Hz|([a n] & Hb & Hz)]; [lia|]. unfold pj_holds in Hz; cbn [fst snd] in Hz.
    destruct (HL a n (pis_node_lblk rsegs _ m lblk o D HN (a, n) Hb)) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd. lia. }
  assert (HC0 : pj_cbytes rsegs m0 k kname).
  { destruct HC as (HF & HB). split; [exact HF|]. eapply bytes_at_transport; [exact HB | exact MU |].
    rewrite length_map, length_app. cbn [length disjoint_from]. lia. }
  eapply evt_cut.
  { apply (HGET (Z_to_bv 64 0x14740) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 w) (Z_to_bv 64 o)
      (Z_to_bv 64 o) (Z_to_bv 64 k) (Z_to_bv 64 w) a3 a4 a5 a6 a7 (Z_to_bv 64 k) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m0 lblk o k kname (JObj ms) D lo); rewrite ?USP.
    - reflexivity.
    - reflexivity.
    - right. exact HN0.
    - exact HC0.
    - intros a n Hb. destruct (HL a n Hb) as (H1 & H2 & H3 & H4). cbn [disjoint_from] in H4 |- *. lia.
    - replace (bv_unsigned sp + -48) with (bv_unsigned sp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact SPA.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. lia.
    - exact MI. }
  intros st (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E & MU1 & WM1 & MI1 &
             ST1 & HC1 & RES).
  subst st. rewrite USP in MU1, ST1.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR1.
  assert (MU2 : munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m1)
    by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU1]; unfold sub_fp; cbn [outside]; intros; lia).
  pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM2.
  replace (ret_pc (Z_to_bv 64 0x14740)) with (Z_to_bv 64 0x14740) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RES as [(O0 & _)|(_ & HN1 & z & -> & HR)]; [exact (False_ind _ (ONZ O0))|].
  assert (ZR : 0 <= z < 2 ^ 64 /\ (z <> 0 -> 0 < z)).
  { cbn [pj_get_res] in HR. destruct HR as [(_ & ->)|HH]; [lia|].
    pose proof (ps_hit_pos m1 lblk o ms D kname z ltac:(intros a n Hb; exact (proj1 (HL a n Hb))) HN1 HH). lia. }
  step.
  if_cases HZ; zify_cond HZ.
  - assert (Z0 : z = 0) by lia. subst z.
    do 2 step. apply evt_done. unfold sa_post.
    do 14 eexists. exists m1, (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))), 0.
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1|].
    split; [exact HN1|]. split; [exact HC1|]. split; [exact HR|]. split; [lia|].
    left. split; [reflexivity|]. reflexivity.
  - assert (Z1 : z <> 0) by (intros ->; apply HZ; reflexivity).
    do 2 step. apply evt_done. unfold sa_post.
    do 14 eexists. exists m1, (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))), z.
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1|].
    split; [exact HN1|]. split; [exact HC1|]. split; [exact HR|]. split; [lia|].
    right. split; [exact Z1|]. reflexivity.
Qed.

Definition sb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (dst w : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
    munch [(dst, dst + 56); (w, w + 56)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
    bytes_at rsegs m1 dst bs /\ rw_cells rsegs m1 w [CB 56 (repeat (Z_to_bv 8 0) 56)].

Lemma ps_sb : memcpy_contract -> memset_contract ->
  forall (ra1 spr sp gp tp t0 t1 t2 s0r s1r a0r a1 a2r a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst w : Z) (bs jd jw : list byte)
         (ra s0 s1 s2 s3 : word) (junk : list byte),
    spr = Z_to_bv 64 (bv_unsigned sp + -48) -> s0r = Z_to_bv 64 w -> a0r = Z_to_bv 64 dst -> a2r = Z_to_bv 64 56 ->
    rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    length bs = 56%nat -> bytes_at rsegs m w bs ->
    rw_cells rsegs m dst [CB 56 jd] -> rw_cells rsegs m w [CB 56 jw] ->
    (w + 56 <= dst \/ dst + 56 <= w) ->
    (dst + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= dst) ->
    (w + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= w) ->
    48 <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs (sb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst w bs m)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r a0r a1 a2r a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14754) fc None m (seg_rom rsegs)).
Proof.
  intros HMC HMS ra1 spr sp gp tp t0 t1 t2 s0r s1r a0r a1 a2r a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m dst w bs jd jw ra s0 s1 s2 s3 junk ESP ES0 EA0 EA2 FR LB WB RD RW DW DD WD SP MI. subst spr s0r a0r a2r.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (cells_at_bound rsegs _ _ _ (proj1 RD)) as (D0 & D1). cbn [cells_size csize] in D1.
  pose proof (cells_at_bound rsegs _ _ _ (proj1 RW)) as (W0 & W1). cbn [cells_size csize] in W1.
  step. step.
  assert (SRC : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 w)) bs) by (rewrite unsigned_lit by lia; exact WB).
  assert (DST : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 dst)) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) jd])
    by (rewrite !unsigned_lit by lia; exact RD).
  assert (LEN : length bs = Z.to_nat (bv_unsigned (Z_to_bv 64 56))) by (rewrite unsigned_lit by lia; exact LB).
  eapply evt_cut; [apply (HMC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs jd SRC LEN DST
                           ltac:(rewrite !unsigned_lit by lia; lia) MI)|].
  intros st (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & E & MU1 & WM1 & MI1 & RW1 & SB1).
  subst st. rewrite !unsigned_lit in MU1, RW1, SB1 by lia. change (Z.to_nat 56) with 56%nat in RW1.
  replace (ret_pc (Z_to_bv 64 0x1475c)) with (Z_to_bv 64 0x1475c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR1.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ RW MU1 WM1 ltac:(cbn [disjoint_from cells_size csize]; lia)) as RW2.
  clear FR RW RD DST SRC.
  do 4 step.
  assert (WS : rw_cells rsegs m1 (bv_unsigned (Z_to_bv 64 w)) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) jw])
    by (rewrite !unsigned_lit by lia; exact RW2).
  eapply evt_cut; [apply (HMS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jw WS MI1)|].
  intros st (u0' & u1' & u2' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3' & u4' & u5' & u6' & m2 & E & MU2 & WM2 & MI2 & RW3).
  subst st. rewrite !unsigned_lit in MU2, RW3 by lia. change (Z.to_nat 56) with 56%nat in RW3.
  change (0 mod 256) with 0 in RW3.
  replace (ret_pc (Z_to_bv 64 0x1476c)) with (Z_to_bv 64 0x1476c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR1 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR2.
  pose proof (proj2 (proj1 RW1)) as DB0. cbn [cells_bytes cbytes] in DB0. rewrite app_nil_r in DB0.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ DB0 MU2 ltac:(rewrite LB; cbn [disjoint_from]; lia)) as DB.
  assert (MU : munch [(dst, dst + 56); (w, w + 56)] m m2).
  { eapply munch_trans; eapply munch_weaken; [| exact MU1 | | exact MU2]; unfold sub_fp; cbn [outside]; intros; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WM.
  clear FR1 MU1 MU2 RW2 WS SB1 DB0 RW1.
  do 9 step.
  apply evt_done. unfold sb_post. do 14 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact DB | exact RW3].
Qed.

Lemma ps_sbh : memcpy_contract -> memset_contract ->
  forall (ra1 spr sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst w : Z) (bs jd jw : list byte)
         (ra s0 s1 s2 s3 : word) (junk : list byte),
    spr = Z_to_bv 64 (bv_unsigned sp + -48) -> s0r = Z_to_bv 64 w -> s3r = Z_to_bv 64 dst ->
    rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    length bs = 56%nat -> bytes_at rsegs m w bs ->
    rw_cells rsegs m dst [CB 56 jd] -> rw_cells rsegs m w [CB 56 jw] ->
    (w + 56 <= dst \/ dst + 56 <= w) ->
    (dst + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= dst) ->
    (w + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= w) ->
    48 <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs (sb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst w bs m)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PS_FREE_RET) fc None m (seg_rom rsegs)).
Proof.
  intros HMC HMS ra1 spr sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m dst w bs jd jw ra s0 s1 s2 s3 junk ESP ES0 ES3 FR LB WB RD RW DW DD WD SP MI. subst s3r.
  unfold PS_FREE_RET. do 2 step.
  eapply (ps_sb HMC HMS); try reflexivity; eassumption.
Qed.

Definition sc_post (spr gp tp s0r s1r s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (res k w : Z) : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (res = 0 /\
     st = MS (mkR (Z_to_bv 64 PS_SD_RET) spr gp tp t0 t1 t2 s0r s1r (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PS_STRDUP) fc None m (seg_rom rsegs))
    \/ (res = -1 /\
     st = MS (mkR (Z_to_bv 64 PS_FREEW_RET) spr gp tp t0 t1 t2 s0r s1r (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7
                s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PS_PJ_FREE) fc None m (seg_rom rsegs)).

Lemma ps_sc :
  forall (ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (res k w : Z),
    a0 = Z_to_bv 64 res -> (res = 0 \/ res = -1) -> s0r = Z_to_bv 64 w -> s2r = Z_to_bv 64 k ->
    evt rsegs (sc_post spr gp tp s0r s1r s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 F fc m res k w)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PS_GROW_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m res k w E0 HR ES0 ES2. subst a0 s0r s2r. unfold PS_GROW_RET.
  destruct HR as [->| ->].
  - step. if_true. do 2 step. apply evt_done. unfold sc_post. do 14 eexists. left. split; [reflexivity|]. reflexivity.
  - step. if_false. do 2 step. apply evt_done. unfold sc_post. do 14 eexists. right. split; [reflexivity|]. reflexivity.
Qed.

Definition se_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs).

Lemma ps_se :
  forall (ra1 spr sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ra s0 s1 s2 s3 : word) (junk : list byte),
    spr = Z_to_bv 64 (bv_unsigned sp + -48) ->
    rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> 48 <= bv_unsigned sp ->
    evt rsegs (se_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PS_FREEW_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 spr sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ra s0 s1 s2 s3 junk ESP FR SP. subst spr. unfold PS_FREEW_RET.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  do 8 step.
  apply evt_done. unfold se_post. do 14 eexists. reflexivity.
Qed.

Lemma ps_rd8 : forall m a x, bytes_at rsegs m a (le8 x) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 x).
Proof.
  intros m a x H. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 x) 0 8 H) by (try rewrite length_le8; lia). reflexivity.
Qed.

Lemma ps_shl : forall x k, 0 <= x -> 0 <= k -> x * 2 ^ k < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) k) = Z_to_bv 64 (x * 2 ^ k).
Proof. intros x k H0 H1 H2. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Definition sd_post (ra1 spr gp tp s0r s1r s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o w res n keys kids : Z) : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte),
    wmono rsegs m m1 /\ mem_inv rsegs m1 /\ bytes_at rsegs m1 (keys + 8 * n) (le8 (Z_to_bv 64 res)) /\
    ((res = 0 /\ munch [(keys + 8 * n, keys + 8 * n + 8)] m m1 /\
      st = MS (mkR (Z_to_bv 64 PS_FREEW_RET) spr gp tp t0 t1 t2 s0r s1r (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7
                 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PS_PJ_FREE) fc None m1 (seg_rom rsegs))
     \/ (res <> 0 /\ munch [(keys + 8 * n, keys + 8 * n + 8); (o + 40, o + 48)] m m1 /\
      bytes_at rsegs m1 (o + 40) (le8 (Z_to_bv 64 (n + 1))) /\
      st = MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r (Z_to_bv 64 (kids + 56 * n)) a1 (Z_to_bv 64 56) a3 a4 a5 a6 a7
                 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14754) fc None m1 (seg_rom rsegs))).

Lemma ps_sd :
  forall (ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o w res n keys kids : Z),
    a0 = Z_to_bv 64 res -> 0 <= res < 2 ^ 64 -> s0r = Z_to_bv 64 w -> s1r = Z_to_bv 64 o ->
    bytes_at rsegs m (o + 40) (le8 (Z_to_bv 64 n)) -> bytes_at rsegs m (o + 32) (le8 (Z_to_bv 64 keys)) ->
    bytes_at rsegs m (o + 24) (le8 (Z_to_bv 64 kids)) ->
    wr_at rsegs m (keys + 8 * n) 8 -> wr_at rsegs m (o + 40) 8 ->
    0 <= o -> o + 56 <= 2 ^ 64 -> 0 <= n <= 2 ^ 54 -> 0 <= keys -> keys + 8 * n + 8 <= 2 ^ 64 ->
    0 <= kids -> kids + 56 * n + 56 <= 2 ^ 64 ->
    (keys + 8 * n + 8 <= o \/ o + 56 <= keys + 8 * n) ->
    mem_inv rsegs m ->
    evt rsegs (sd_post ra1 spr gp tp s0r s1r s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 F fc m o w res n keys kids)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PS_SD_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o w res n keys kids E0 RR ES0 ES1 BN BK BD WK WO O0 O1 N0 K0 K1 D0 D1 KO MI. subst a0 s0r s1r.
  unfold PS_SD_RET.
  pose proof (munch_refl [(keys + 8 * n, keys + 8 * n + 8); (o + 40, o + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (RN : ov_read_bytes rsegs m (wa (o + 40)) 8 = Some (le8 (Z_to_bv 64 n))) by (apply ps_rd8; exact BN).
  assert (RK : ov_read_bytes rsegs m (wa (o + 32)) 8 = Some (le8 (Z_to_bv 64 keys))) by (apply ps_rd8; exact BK).
  do 3 step.
  rewrite (ps_shl n 3) by lia.
  step.
  assert (HS : store_ok rsegs m (wa (keys + 8 * n)) 8 = true).
  { rewrite <- (Z.add_0_r (keys + 8 * n)) at 1. apply (wr_at_store_ok rsegs m (keys + 8 * n) 8 0 8); [exact WK | lia | cbn; lia]. }
  step.
  remember (write_to_mem m (wa (keys + 8 * n)) (le8 (Z_to_bv 64 res))) as m1 eqn:Hm1.
  assert (MI1 : mem_inv rsegs m1) by (subst m1; apply mem_inv_store; [exact MI | rewrite length_le8; exact HS]).
  assert (MU1 : munch [(keys + 8 * n, keys + 8 * n + 8); (o + 40, o + 48)] m m1)
    by (subst m1; apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]).
  assert (MU1' : munch [(keys + 8 * n, keys + 8 * n + 8)] m m1)
    by (subst m1; apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]).
  assert (WM1 : wmono rsegs m m1) by (subst m1; apply wmono_write; exact WM).
  assert (BK1 : bytes_at rsegs m1 (keys + 8 * n) (le8 (Z_to_bv 64 res)))
    by (subst m1; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (BD1 : bytes_at rsegs m1 (o + 24) (le8 (Z_to_bv 64 kids)))
    by (subst m1; apply bytes_at_write_other; [exact BD | lia | rewrite length_le8; lia | rewrite !length_le8; lia]).
  assert (WO1 : wr_at rsegs m1 (o + 40) 8) by (subst m1; apply wr_at_write; exact WO).
  clear Hm1 HS MU WM RN RK BN BK.
  step.
  if_cases HZ; zify_cond HZ.
  - assert (R0 : res = 0) by lia. subst res.
    do 2 step. apply evt_done. unfold sd_post. do 14 eexists. exists m1.
    split; [exact WM1|]. split; [exact MI1|]. split; [exact BK1|]. left.
    split; [reflexivity|]. split; [exact MU1'|]. reflexivity.
  - assert (R1 : res <> 0) by (intros ->; apply HZ; reflexivity).
    assert (RD : ov_read_bytes rsegs m1 (wa (o + 24)) 8 = Some (le8 (Z_to_bv 64 kids))) by (apply ps_rd8; exact BD1).
    do 2 step.
    assert (HS2 : store_ok rsegs m1 (wa (o + 40)) 8 = true).
    { rewrite <- (Z.add_0_r (o + 40)) at 1. apply (wr_at_store_ok rsegs m1 (o + 40) 8 0 8); [exact WO1 | lia | cbn; lia]. }
    step.
    remember (write_to_mem m1 (Z_to_bv 64 (o + 40)) (le8 (Z_to_bv 64 (n + 1)))) as m2 eqn:Hm2.
    change (Z_to_bv 64 (o + 40)) with (wa (o + 40)) in Hm2.
    assert (MI2 : mem_inv rsegs m2) by (subst m2; apply mem_inv_store; [exact MI1 | rewrite length_le8; exact HS2]).
    assert (MU2 : munch [(keys + 8 * n, keys + 8 * n + 8); (o + 40, o + 48)] m m2)
      by (subst m2; apply munch_write; [exact MU1 | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]).
    assert (WM2 : wmono rsegs m m2) by (subst m2; apply wmono_write; exact WM1).
    assert (BN2 : bytes_at rsegs m2 (o + 40) (le8 (Z_to_bv 64 (n + 1))))
      by (subst m2; apply bytes_at_write_same; rewrite ?length_le8; lia).
    assert (BK2 : bytes_at rsegs m2 (keys + 8 * n) (le8 (Z_to_bv 64 res)))
      by (subst m2; apply bytes_at_write_other; [exact BK1 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]).
    clear Hm2 HS2 MU1 MU1' WM1 RD BD1 WO1 BK1.
    step. rewrite (ps_shl n 6) by lia.
    do 4 step.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8.
    rewrite (unsigned_lit (n * 64)), (unsigned_lit (n * 8)) by lia.
    replace (kids + (n * 64 - n * 8)) with (kids + 56 * n) by lia.
    apply evt_done. unfold sd_post. do 14 eexists. exists m2.
    split; [exact WM2|]. split; [exact MI2|]. split; [exact BK2|]. right.
    split; [exact R1|]. split; [exact MU2|]. split; [exact BN2|]. reflexivity.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition sdx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (spr s0r s1r s2r s3r : word) (m : word -> option byte) (o w res n keys kids : Z) (bs : list byte)
    : machine_state -> Prop :=
  fun st =>
    (res = 0 /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte),
       munch [(keys + 8 * n, keys + 8 * n + 8)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
       bytes_at rsegs m1 (keys + 8 * n) (le8 (Z_to_bv 64 0)) /\
       st = MS (mkR (Z_to_bv 64 PS_FREEW_RET) spr gp tp t0 t1 t2 s0r s1r (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7
                  s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PS_PJ_FREE) fc None m1 (seg_rom rsegs))
    \/ (res <> 0 /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte),
       munch [(keys + 8 * n, keys + 8 * n + 8); (o + 40, o + 48); (kids + 56 * n, kids + 56 * n + 56); (w, w + 56)] m m1 /\
       wmono rsegs m m1 /\ mem_inv rsegs m1 /\
       bytes_at rsegs m1 (keys + 8 * n) (le8 (Z_to_bv 64 res)) /\ bytes_at rsegs m1 (o + 40) (le8 (Z_to_bv 64 (n + 1))) /\
       bytes_at rsegs m1 (kids + 56 * n) bs /\ rw_cells rsegs m1 w [CB 56 (repeat (Z_to_bv 8 0) 56)] /\
       st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom rsegs)).

Lemma ps_sdx : memcpy_contract -> memset_contract ->
  forall (ra1 spr sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o w res n keys kids : Z) (bs jd jw : list byte)
         (ra s0 s1 s2 s3 : word) (junk : list byte),
    spr = Z_to_bv 64 (bv_unsigned sp + -48) ->
    a0 = Z_to_bv 64 res -> 0 <= res < 2 ^ 64 -> s0r = Z_to_bv 64 w -> s1r = Z_to_bv 64 o ->
    bytes_at rsegs m (o + 40) (le8 (Z_to_bv 64 n)) -> bytes_at rsegs m (o + 32) (le8 (Z_to_bv 64 keys)) ->
    bytes_at rsegs m (o + 24) (le8 (Z_to_bv 64 kids)) ->
    wr_at rsegs m (keys + 8 * n) 8 -> wr_at rsegs m (o + 40) 8 ->
    0 <= o -> o + 56 <= 2 ^ 64 -> 0 <= n <= 2 ^ 54 -> 0 <= keys -> keys + 8 * n + 8 <= 2 ^ 64 ->
    0 <= kids -> kids + 56 * n + 56 <= 2 ^ 64 ->
    (keys + 8 * n + 8 <= o \/ o + 56 <= keys + 8 * n) ->
    rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    length bs = 56%nat -> bytes_at rsegs m w bs ->
    rw_cells rsegs m (kids + 56 * n) [CB 56 jd] -> rw_cells rsegs m w [CB 56 jw] ->
    (w + 56 <= kids + 56 * n \/ kids + 56 * n + 56 <= w) ->
    (kids + 56 * n + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= kids + 56 * n) ->
    (w + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= w) ->
    (keys + 8 * n + 8 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= keys + 8 * n) ->
    (o + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= o) ->
    (keys + 8 * n + 8 <= w \/ w + 56 <= keys + 8 * n) -> (o + 56 <= w \/ w + 56 <= o) ->
    (keys + 8 * n + 8 <= kids + 56 * n \/ kids + 56 * n + 56 <= keys + 8 * n) ->
    (o + 56 <= kids + 56 * n \/ kids + 56 * n + 56 <= o) ->
    48 <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs (sdx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc spr s0r s1r s2r s3r m o w res n keys kids bs)
      (MS (mkR ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PS_SD_RET) fc None m (seg_rom rsegs)).
Proof.
  intros HMC HMS ra1 spr sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o w res n keys kids bs jd jw ra s0 s1 s2 s3 junk ESP E0 RR ES0 ES1 BN BK BD WK WO O0 O1 N0 K0 K1 D0 D1 KO
    FR LB WB RD RW DW DD WD KD OD KW OW KK OK SP MI.
  eapply evt_cut.
  { apply (ps_sd ra1 spr gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m o w res n keys kids); assumption. }
  intros st (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & WM1 & MI1 & BK1 & CASES).
  destruct CASES as [(R0 & MU1 & ->)|(R1 & MU1 & BN1 & ->)].
  - apply evt_done. left. split; [exact R0|]. subst res.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1.
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact BK1 | reflexivity].
  - assert (TR : forall a l, a + Z.of_nat l <= keys + 8 * n \/ keys + 8 * n + 8 <= a ->
                   a + Z.of_nat l <= o + 40 \/ o + 48 <= a -> 0 <= a ->
                   forall c, cells_size c = l -> rw_cells rsegs m a c -> rw_cells rsegs m1 a c).
    { intros a l H1 H2 H3 c Hc Hrw. apply (rw_cells_transport rsegs _ _ _ _ _ Hrw MU1 WM1). rewrite Hc.
      cbn [disjoint_from]. lia. }
    pose proof (cells_at_bound rsegs _ _ _ (proj1 RW)) as (W0 & _).
    eapply evt_cut.
    { apply (ps_sb HMC HMS ra1 spr sp gp tp u0 u1 u2 s0r s1r _ b1 _ b3 b4 b5 b6 b7 s2r s3r s4 s5 s6 s7 s8 s9 s10 s11
               u3 u4 u5 u6 F fc m1 (kids + 56 * n) w bs jd jw ra s0 s1 s2 s3 junk ESP ES0 eq_refl eq_refl).
      - apply (TR _ 48%nat); [lia | lia | lia | reflexivity | exact FR].
      - exact LB.
      - apply (bytes_at_transport rsegs _ _ _ _ _ WB MU1). rewrite LB. cbn [disjoint_from]. lia.
      - apply (TR _ 56%nat); [lia | lia | lia | reflexivity | exact RD].
      - apply (TR _ 56%nat); [lia | lia | lia | reflexivity | exact RW].
      - exact DW.
      - exact DD.
      - exact WD.
      - exact SP.
      - exact MI1. }
    intros st (c0 & c1 & c2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & c3 & c4 & c5 & c6 & m2 & -> & MU2 & WM2 & MI2 & DB & WZ).
    apply evt_done. right. split; [exact R1|].
    exists c0, c1, c2, d1, d2, d3, d4, d5, d6, d7, c3, c4, c5, c6, m2.
    split.
    { eapply munch_trans; eapply munch_weaken; [| exact MU1 | | exact MU2]; unfold sub_fp; cbn [outside]; intros; lia. }
    split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|]. split; [exact MI2|].
    split; [apply (bytes_at_transport rsegs _ _ _ _ _ BK1 MU2); rewrite length_le8; cbn [disjoint_from]; lia|].
    split; [apply (bytes_at_transport rsegs _ _ _ _ _ BN1 MU2); rewrite length_le8; cbn [disjoint_from]; lia|].
    split; [exact DB|]. split; [exact WZ | reflexivity].
Qed.
