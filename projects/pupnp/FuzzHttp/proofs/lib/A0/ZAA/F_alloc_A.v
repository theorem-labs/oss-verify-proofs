(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv ATacFix F_alloc_env.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition allocate_entry : Z := 0x33658.

Definition al_n (n : Z) : Z := if n =? 0 then 1 else n.
Definition al_rz (n : Z) : Z := Z.shiftl 16 (a0_rzlog n).
Definition al_prim (n : Z) : bool := a0_need n <=? 65536.
Definition al_need (n : Z) : Z := if al_prim n then a0_need n else a0_need n + al_rz n.

Lemma a0_rzlog_range : forall n, 0 <= a0_rzlog n <= 7.
Proof. intros n. unfold a0_rzlog. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

Lemma al_land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = (x / 8) * 8.
Proof.
  intros x Hx.
  assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
  assert (D : forall a b, Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b).
  { intros a b. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Section RZL.
  Context {HC : HasCeiling}.
  Variables (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q : Z) (m0 : mem).

  Definition rzl_post (lo r : Z) : machine_state -> Prop :=
    fun ms' => exists a1 a2 a3 a4 m', ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 16, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

  #[using="Type"] Lemma rzl_spec : forall lo v r a1 a2 a3 a4,
    (v = 16 /\ r = 0) \/ (v = 2048 /\ r = 7) ->
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 16 -> q mod 16 = 0 -> q <= 2^47 -> mem_inv asegs m0 ->
    evt asegs (rzl_post lo r)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x38bc0) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo v r a1 a2 a3 a4 VR ST CLO LO AL QH MI.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 16, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- EQ in ST. carve_frame 16%nat ST. rewrite !EQ in *.
    destruct VR as [[-> ->]|[-> ->]].
    - zstep. sstep.
      zstep. zstep. zstep. zstep. if_false.
      zstep. zstep. zstep. if_false.
      zstep. zstep. zstep. if_false.
      zstep. zstep. zstep.
      do 7 zstep.
      cbv beta. change (bv_unsigned (4%bv : bv 8)) with 4.
      zstep. zstep. zstep. if_false.
      zstep. zstep. change (bv_swrap 32 16) with 16.
      zstep. if_false.
      zstep. zstep. zstep.
      replace (q + -16 + 16) with q by lia.
      zstep.
      release_frame FR ST q.
      apply evt_done. unfold rzl_post. eexists _, _, _, _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; assumption.
    - zstep. sstep.
      zstep. zstep. zstep. zstep. if_false.
      zstep. zstep. zstep. if_false.
      zstep. zstep. zstep. if_false.
      zstep. zstep. zstep.
      do 7 zstep.
      cbv beta. change (bv_unsigned (11%bv : bv 8)) with 11.
      zstep. zstep. zstep. if_false.
      zstep. zstep. change (bv_swrap 32 2048) with 2048.
      zstep. if_false.
      zstep. zstep. zstep.
      replace (q + -16 + 16) with q by lia.
      zstep.
      release_frame FR ST q.
      apply evt_done. unfold rzl_post. eexists _, _, _, _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; assumption.
  Qed.
End RZL.

Section LADDER.
  Context {HC : HasCeiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (n : Z) (m : mem).

  Definition ladder_post : machine_state -> Prop :=
    fun ms' => exists a0, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz (a0_rzlog n)) s4 (wz n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (wz 0x337c4) fc None m (seg_rom asegs).

  #[using="Type"] Lemma ladder_spec : forall s3, 0 <= n < 2^63 ->
    evt asegs ladder_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x336f0) fc None m (seg_rom asegs)).
  Proof.
    intros s3 N. unfold ladder_post, a0_rzlog.
    zstep. if_cases K1; zify_cond K1.
    2:{ zstep. zstep. apply evt_done. eexists. replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    zstep. zstep. if_cases K2; zify_cond K2.
    2:{ zstep. zstep. apply evt_done. eexists. replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    zstep. zstep. if_cases K3; zify_cond K3.
    2:{ zstep. zstep. apply evt_done. eexists. replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    zstep. zstep. zstep. if_cases K4; zify_cond K4.
    2:{ zstep. zstep. apply evt_done. eexists. replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia). replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    zstep. zstep. zstep. if_cases K5; zify_cond K5.
    2:{ zstep. zstep. apply evt_done. eexists. replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia). replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    zstep. zstep. zstep. if_cases K6; zify_cond K6.
    2:{ zstep. zstep. apply evt_done. eexists. replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia). replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia). replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
        replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    zstep. zstep. zstep. zstep.
    apply evt_done. replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
    replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia). replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
    replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia). replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
    replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (Z.ltb_spec n 64513) as [K7|K7].
    - replace (n <=? 64512) with true by (symmetry; apply Z.leb_le; lia). eexists. reflexivity.
    - replace (n <=? 64512) with false by (symmetry; apply Z.leb_gt; lia). eexists. reflexivity.
  Qed.
End LADDER.

Section FRONT.
  Context {HC : HasCeiling}.
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo n STK : Z).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - 144.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.
  Hypothesis NR : 0 <= n <= A0_MAXREQ.
  Hypothesis STKR : 0 < STK < 2^64.

  Definition front_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j,
      ms' = MS (mkR ra' (wz (q - 128)) gp (wz A0_TP) t0 t1 t2 (wz (if al_prim n then 1 else 0)) (wz (al_n n)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz 8) (wz (al_need n)) (wz (al_rz n)) (wz n) (wz INSTANCE) (wz STK) (Z_to_bv 64 (-8)) (wz 7) (wz (INSTANCE + 2047)) (wz 1) t3 t4 t5 t6)
               F_ (wz 0x338d8) fc None m' (seg_rom asegs)
      /\ munch [(q - 144, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q - 128)
      /\ rw_cells asegs m' (q - 128) [CB 8 j; C8 (wz 1); C8 (wz 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  #[using="HC CLO LOQ QH Q16 NR STKR"] Lemma front_spec : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo q -> mem_inv asegs m ->
    rw_cells asegs m A0_ASAN_INITED [C1 (Z_to_bv 8 1)] -> alloc_env m ->
    evt asegs (front_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz n) (wz 8) (wz STK) (wz 1) (wz 1) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz allocate_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m ST MI INI AE.
    unfold allocate_entry. unfold A0_MAXREQ in NR.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    ae_split AE.
    pose proof (munch_refl [(q - 144, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- EQ in ST. carve_frame 128%nat ST. rewrite !EQ in *.
    zstep. do 13 zstep.
    do 6 zstep.
    zstep. zstep. zstep.
    replace (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    zstep. zstep. zstep. zstep.
    zstep. if_false.
    zstep. zstep. zstep.
    replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    zstep. zstep.
    zstep. if_false.
    zstep. if_cases KS; zify_cond KS. { exfalso. clear - KS STKR. lia. } clear KS.
    zstep. zstep. if_true.
    zstep. zstep. zstep. if_true.
    zstep. zstep. zstep. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    cbv beta. change (bv_unsigned (3%bv : bv 8)) with 3.
    zstep. zstep. zstep. zstep.
    zstep. if_true.
    zstep. zstep. zstep. zstep. if_false.
    zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 24 ?jj :: ?post) =>
      apply (rw_cells_split_CB asegs m0 (q + -128) [] 24 jj post [8; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j1 :: CB 8 ?j2 :: CB 8 ?j3 :: _) =>
      remember j1 as f1 eqn:Ef1; remember j2 as f2 eqn:Ef2; remember j3 as f3 eqn:Ef3 end.
    clear Ef1 Ef2 Ef3.
    sstep. sstep.
    eapply evt_cut.
    { eapply (ladder_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc n m0). clear - NR. lia. }
    cbv beta. unfold ladder_post. intros msL (l0 & ->).
    pose proof (a0_rzlog_range n) as RZL. remember (a0_rzlog n) as rzl eqn:Erzl.
    zstep.
    replace (sx16 (Z_to_bv 64 16)) with (Z_to_bv 64 16) by (apply bv_eq; vm_compute; reflexivity).
    zstep. zstep. zstep. zstep.
    zstep.
    call (rzl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q + -128) m0 lo 16 0 _ _ _ _);
      [ left; split; reflexivity | exact ST | exact CLO | clear - LOQ; lia | clear - Q16; Z.div_mod_to_equations; lia | clear - QH; lia | exact MI | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end. rename POST into ST1, MI0 into MI1.
    zstep. zstep.
    replace (sx16 (Z_to_bv 64 2048)) with (Z_to_bv 64 2048) by (apply bv_eq; vm_compute; reflexivity).
    zstep. zstep. zstep.
    call (rzl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q + -128) m1 lo 2048 7 _ _ _ _);
      [ right; split; reflexivity | exact ST1 | exact CLO | clear - LOQ; lia | clear - Q16; Z.div_mod_to_equations; lia | clear - QH; lia | exact MI1 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with Hs : stk asegs m2 _ _ |- _ => rename Hs into ST2 end. lazymatch goal with Hs : mem_inv asegs m2 |- _ => rename Hs into MI2 end.
    zstep.

    eapply (evt_cut asegs (fun ms' => exists y2 y3 y4, ms' =
       MS (mkR (wz 210928) (wz (q + -128)) gp (wz 6187376) t0 t1 t2 (wz 8) (wz 0) (wz (Z.max n 8)) (wz 8) y2 y3 y4 (wz 1) a6 a7
               (wz 8) (wz rzl) (wz 65536) (wz n) (wz 721560) (wz STK) (wz 65535) (wz 7) (wz 723607) (wz 1) t3 t4 t5 t6)
          F_ (wz 0x3380c) fc None m2 (seg_rom asegs))).
    { if_cases KA; zify_cond KA.
      - zstep. if_cases KB; zify_cond KB.
        + zstep. zstep. zstep. if_cases KC; zify_cond KC.
          * apply evt_done. eexists _, _, _. replace (Z.max n 8) with n by lia. reflexivity.
          * zstep. apply evt_done. eexists _, _, _. replace (Z.max n 8) with 8 by lia. reflexivity.
        + zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC.
          * zstep. apply evt_done. eexists _, _, _. replace (Z.max n 8) with 8 by lia. replace rzl with 7 by lia. reflexivity.
          * zstep. apply evt_done. eexists _, _, _. replace (Z.max n 8) with n by lia. replace rzl with 7 by lia. reflexivity.
      - zstep. zstep. if_false. zstep. zstep. zstep. if_cases KC; zify_cond KC.
        + apply evt_done. eexists _, _, _. replace (Z.max n 8) with n by lia. replace rzl with 0 by lia. reflexivity.
        + zstep. apply evt_done. eexists _, _, _. replace (Z.max n 8) with 8 by lia. replace rzl with 0 by lia. reflexivity. }
    cbv beta. intros msC (y2 & y3 & y4 & ->).
    assert (MX : 8 <= Z.max n 8 <= 2^28) by (clear - NR; lia). remember (Z.max n 8) as mx eqn:Emx.
    do 8 zstep.
    replace (Z.land ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) 8) with 0 by (vm_compute; reflexivity).
    rewrite (al_land_m8 (mx + 7)) by (clear - MX; lia). rewrite Z.add_0_r.
    assert (RND : exists k, (mx + 7) / 8 * 8 = 8 * k /\ mx <= 8 * k < mx + 8) by (exists ((mx + 7) / 8); clear; Z.div_mod_to_equations; lia).
    destruct RND as (rk & -> & RK).
    zstep.
    replace (Z.land (8 * rk) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear; Z.div_mod_to_equations; lia).
    zstep. if_false.
    do 4 zstep.
    assert (SW : bv_swrap 32 (Z.shiftl 16 (rzl mod 32)) = Z.shiftl 16 rzl).
    { clear - RZL. assert (C : rzl = 0 \/ rzl = 1 \/ rzl = 2 \/ rzl = 3 \/ rzl = 4 \/ rzl = 5 \/ rzl = 6 \/ rzl = 7) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity. }
    rewrite SW. clear SW.
    assert (RZR : 16 <= Z.shiftl 16 rzl <= 2048 /\ Z.shiftl 16 rzl mod 16 = 0).
    { clear - RZL. assert (C : rzl = 0 \/ rzl = 1 \/ rzl = 2 \/ rzl = 3 \/ rzl = 4 \/ rzl = 5 \/ rzl = 6 \/ rzl = 7) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (split; [split; apply Z.leb_le; reflexivity| reflexivity]). }
    remember (Z.shiftl 16 rzl) as rz eqn:Erz.
    assert (SZ : n + Z.b2z (n <? 1) = al_n n).
    { unfold al_n. clear - NR. destruct (Z.ltb_spec n 1), (Z.eqb_spec n 0); cbn [Z.b2z]; lia. }
    do 5 zstep.
    assert (NEED : a0_need n = 8 * rk + rz).
    { unfold a0_need. rewrite <- Emx, <- Erzl, <- Erz. clear - RK. Z.div_mod_to_equations. lia. }
    replace (Z.b2z (8 <? 65537)) with 1 by reflexivity.
    unfold front_post, al_need, al_rz, al_prim. rewrite <- Erzl, <- Erz, NEED, <- SZ.
    destruct (Z.ltb_spec (8 * rk + rz) 65537) as [KP|KP].
    - replace (8 * rk + rz <=? 65536) with true by (symmetry; apply Z.leb_le; clear - KP; lia). cbn [Z.b2z].
      do 5 zstep.
      rewrite Z.land_0_l, Z.add_0_l.
      zstep. if_cases KN; zify_cond KN. { exfalso. clear - KN NR. lia. } clear KN.
      zstep. if_cases KN; zify_cond KN. { exfalso. clear - KN KP. lia. } clear KN.
      zstep.
      zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear - KN NR. destruct (n <? 1); cbn [Z.b2z] in KN; lia. } clear KN.
      apply evt_done. replace (q - 128) with (q + -128) by lia.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2, f1. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2| exact FR].
    - replace (8 * rk + rz <=? 65536) with false by (symmetry; apply Z.leb_gt; clear - KP; lia). cbn [Z.b2z].
      do 5 zstep.
      replace (Z.land 18446744073709551615 rz) with rz
        by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small; [reflexivity| clear - RZR; lia]).
      replace (rz + (8 * rk + rz)) with (8 * rk + rz + rz) by lia.
      zstep. if_cases KN; zify_cond KN. { exfalso. clear - KN NR. lia. } clear KN.
      zstep. if_cases KN; zify_cond KN. { exfalso. clear - KN RK MX RZR. lia. } clear KN.
      zstep.
      zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear - KN NR. destruct (n <? 1); cbn [Z.b2z] in KN; lia. } clear KN.
      apply evt_done. replace (q - 128) with (q + -128) by lia.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2, f1. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2| exact FR].
  Qed.
End FRONT.

