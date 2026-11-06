(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit F_gates M_memsetZ.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition NO_ODR : Z := 18446744073709551615.
Definition desc_glob (d : Z * Z * Z * Z * Z * Z * Z * Z) : Z * Z * Z :=
  match d with (b, _, srz, _, _, _, _, odr) => (b, srz, if odr =? NO_ODR then 0 else odr) end.
Lemma A0_DESCS_globals : map desc_glob A0_DESCS = A0_GLOBALS.
Proof. vm_compute. reflexivity. Qed.

Lemma canpoison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m -> rw_cells asegs m 0xb3d9c [C1 (Z_to_bv 8 1)] ->
  evt asegs (inited_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x597ec) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI CP.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  rewrite (sxb_small 1) by lia. zstep.
  zstep. fold_lits. zstep. finish.
Qed.

Notation desc := (Z * Z * Z * Z * Z * Z * Z * Z)%type (only parsing).
Fixpoint gfacts (mc : mem) (fl ofl : Z) (ds : list desc) : Prop :=
  match ds with
  | [] => True
  | d :: r => match d with (b, _, srz, _, _, _, _, odr) =>
      b mod 8 = 0 /\ srz mod 8 = 0 /\ 8 <= srz /\ fl <= b /\ b + srz <= 0x7fff8000
      /\ (exists junk, rw_cells asegs mc (sh b) [CB (Z.to_nat (srz / 8)) junk])
      /\ (odr = NO_ODR \/ (ofl <= odr < 0x5e6be3 /\ exists c, rw_cells asegs mc odr [C1 c]))
      /\ gfacts mc (b + srz) (if odr =? NO_ODR then ofl else odr + 1) r
      end
  end.

Definition floor_ok (fl ofl : Z) (iv : ivl) : Prop :=
  (0x7fff8000 <= fst iv /\ snd iv <= sh fl) \/ (snd iv <= ofl /\ snd iv <= 0x5e6be3) \/ 0x10007fff8000 <= fst iv.

Lemma floor_disjoint_sh : forall W fl ofl b n, Forall (floor_ok fl ofl) W -> 0 <= fl -> fl <= b -> sh b + n <= 0x10007fff8000 -> disjoint_from W (sh b) n.
Proof.
  induction W as [|[lo hi] W IH]; intros fl ofl b n FA F0 FB NB; cbn [disjoint_from]; [exact I|].
  inversion FA as [|x l P1 P2]; subst. split; [| eapply IH; eassumption].
  pose proof (sh_mono fl b FB). unfold floor_ok in P1; cbn [fst snd] in P1. unfold sh, SHADOW_OFF in *.
  assert (0 <= b / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma floor_disjoint_odr : forall W fl ofl o, Forall (floor_ok fl ofl) W -> ofl <= o < 0x5e6be3 -> disjoint_from W o 1.
Proof.
  induction W as [|[lo hi] W IH]; intros fl ofl o FA FO; cbn [disjoint_from]; [exact I|].
  inversion FA as [|x l P1 P2]; subst. split; [| eapply IH; eassumption].
  unfold floor_ok in P1; cbn [fst snd] in P1. lia.
Qed.
Lemma floor_ok_mono : forall W fl ofl fl' ofl', Forall (floor_ok fl ofl) W -> fl <= fl' -> ofl <= ofl' -> Forall (floor_ok fl' ofl') W.
Proof.
  intros W fl ofl fl' ofl' FA H1 H2. eapply Forall_impl; [| exact FA]. intros [lo hi] P. unfold floor_ok in *; cbn [fst snd] in *.
  pose proof (sh_mono fl fl' H1). lia.
Qed.

Lemma gfacts_frame : forall ds fl ofl mc mc' W, 0 <= fl -> gfacts mc fl ofl ds -> munch W mc mc' -> wmono asegs mc mc' ->
  Forall (floor_ok fl ofl) W -> gfacts mc' fl ofl ds.
Proof.
  induction ds as [|d r IH]; intros fl ofl mc mc' W F0 G MU WM FA; [exact I|].
  destruct d as [[[[[[[b sz] srz] nm] md] dy] loc] odr]. cbn [gfacts] in *.
  destruct G as (B8 & S8 & SZ & FB & BH & (junk & SHC) & OD0 & GN).
  split; [exact B8|]. split; [exact S8|]. split; [exact SZ|]. split; [exact FB|]. split; [exact BH|].
  split.
  { exists junk. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. eapply floor_disjoint_sh; try eassumption.
    cbn [cells_size csize Nat.add]. clear - B8 S8 SZ FB BH F0. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. }
  split.
  { destruct OD0 as [ON|[OR [c OC]]]; [left; exact ON| right]. split; [exact OR|].
    exists c. eapply rw_cells_transport; [exact OC| exact MU| exact WM|]. eapply floor_disjoint_odr; eassumption. }
  eapply IH; [| exact GN| exact MU| exact WM|]; [lia|]. eapply floor_ok_mono; [exact FA| lia|].
  destruct (odr =? NO_ODR) eqn:E; [lia|]. destruct OD0 as [ON|[OR _]]; [apply Z.eqb_neq in E; contradiction| lia].
Qed.

Definition desc_fp1 (d : desc) : list ivl :=
  match d with (b, _, srz, _, _, _, _, odr) => (sh b, sh b + srz / 8) :: (if odr =? NO_ODR then [] else [(odr, odr + 1)]) end.
Definition loop_fp (ds : list desc) : list ivl := flat_map desc_fp1 ds.

Definition dtor_xenv (m : mem) : Prop :=
  rw_cells asegs m 0xab9b8 [C8 (wz 0xafa20); C8 (wz 0xb0e60)]
  /\ rw_cells asegs m 0xaad50 [C8 (wz 0xacbe0)]
  /\ rw_cells asegs m 0xaad10 [C8 (wz 0x143fe0)]
  /\ rw_cells asegs m 0x1460e0 [C8 (wz 18446744073709551615)]
  /\ rw_cells asegs m 0xb3d9c [C1 (Z_to_bv 8 1)].
Definition LENV (m : mem) : Prop := icpt_env m /\ dtor_xenv m.

Lemma dtor_xenv_frame : forall W m m', dtor_xenv m -> munch W m m' -> wmono asegs m m' -> env_band_safe W -> dtor_xenv m'.
Proof.
  intros W m m' (X1 & X2 & X3 & X4 & X5) MU WM SAFE. unfold dtor_xenv.
  split; [ecf X1 MU WM SAFE|]. split; [ecf X2 MU WM SAFE|]. split; [ecf X3 MU WM SAFE|]. split; [ecf X4 MU WM SAFE| ecf X5 MU WM SAFE].
Qed.
Lemma LENV_frame : forall W m m', LENV m -> munch W m m' -> wmono asegs m m' -> env_band_safe W -> LENV m'.
Proof. intros W m m' [IE XE] MU WM SAFE. split; [eapply icpt_env_frame; eassumption| eapply dtor_xenv_frame; eassumption]. Qed.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.
Lemma sub_fp_app_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x H. apply outside_app in H. tauto. Qed.
Lemma sub_fp_app_r : forall W1 W2, sub_fp W2 (W1 ++ W2).
Proof. intros W1 W2 x H. apply outside_app in H. tauto. Qed.
Lemma cells_size_desc : forall ds, Z.of_nat (cells_size (desc_cells ds)) = 64 * Z.of_nat (length ds).
Proof.
  induction ds as [|d r IH]; [reflexivity|]. destruct d as [[[[[[[b sz] srz] nm] md] dy] loc] odr].
  change (desc_cells ((b, sz, srz, nm, md, dy, loc, odr) :: r)) with (desc_cells1 (b, sz, srz, nm, md, dy, loc, odr) ++ desc_cells r).
  rewrite cells_size_app, Nat2Z.inj_add, IH. cbn [desc_cells1 cells_size csize Nat.add length]. lia.
Qed.
Lemma sh_end_al : forall b srz, b mod 8 = 0 -> srz mod 8 = 0 -> sh b + srz / 8 = sh (b + srz).
Proof.
  intros b srz B8 S8. unfold sh. apply Z.mod_divide in B8; [| lia]. destruct B8 as [kb ->]. apply Z.mod_divide in S8; [| lia]. destruct S8 as [ks ->].
  replace (kb * 8 + ks * 8) with ((kb + ks) * 8) by lia. rewrite !Z.div_mul by lia. lia.
Qed.

Definition odr_keep (mc mc' : mem) : Prop :=
  forall o, 0x5e6be0 <= o < 0x5e6be3 -> (exists c, rw_cells asegs mc o [C1 c]) -> exists c', rw_cells asegs mc' o [C1 c'].
Lemma odr_keep_refl : forall m, odr_keep m m. Proof. intros m o _ H. exact H. Qed.
Lemma odr_keep_trans : forall m1 m2 m3, odr_keep m1 m2 -> odr_keep m2 m3 -> odr_keep m1 m3.
Proof. intros m1 m2 m3 H1 H2 o Ho H. exact (H2 o Ho (H1 o Ho H)). Qed.

Section Loop.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (q : Z) (s5 s6 : word).
  Variable Q : machine_state -> Prop.
  Notation LST pc mm x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 D cnt x28 x29 x30 x31 :=
    (MS (mkR x1 (wz q) gp tp x5 x6 x7 x8 (wz 0x146068) x10 x11 x12 x13 x14 x15 x16 x17 (wz 2) (wz 0x1b5d5) (wz D) s5 s6
             (wz 0xacbe0) (wz 0xb1df0) (wz 0xb1d38) (wz 0xb4538) (wz cnt) x28 x29 x30 x31)
        F (wz pc) fc None mm (seg_rom asegs)) (only parsing).

  Definition loop_K (D : Z) (ds : list desc) (mc : mem) : Prop :=
    forall (mc' : mem) x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      munch (loop_fp ds) mc mc' -> wmono asegs mc mc' -> odr_keep mc mc' -> mem_inv asegs mc' ->
      evt asegs Q (LST 0x41e38 mc' x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 (D + 64 * Z.of_nat (length ds)) 0 x28 x29 x30 x31).

  #[using="Type"] Lemma loop_K_step : forall d r D (mc m1 : mem), munch (desc_fp1 d) mc m1 -> wmono asegs mc m1 -> odr_keep mc m1 -> loop_K D (d :: r) mc -> loop_K (D + 64) r m1.
  Proof.
    intros d r D mc m1 MU WM OK K. unfold loop_K in *. intros until x31. intros MU' WM' OK' MI'.
    replace (D + 64 + 64 * Z.of_nat (length r)) with (D + 64 * Z.of_nat (length (d :: r))) by (cbn [length]; lia).
    apply K; [| eapply wmono_trans; eassumption| eapply odr_keep_trans; eassumption| exact MI'].
    change (loop_fp (d :: r)) with (desc_fp1 d ++ loop_fp r).
    eapply munch_trans; [eapply munch_weaken; [apply sub_fp_app_l| exact MU]| eapply munch_weaken; [apply sub_fp_app_r| exact MU']].
  Qed.

  #[using="Type"] Lemma dloop : forall ds D fl ofl (mc : mem) x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    ds <> [] -> 0 <= fl -> 0x147000 <= ofl ->
    gfacts mc fl ofl ds -> rw_cells asegs mc D (desc_cells ds) -> 0xafa20 <= D -> D + 64 * Z.of_nat (length ds) <= 0xb0e60 ->
    LENV mc -> mem_inv asegs mc -> loop_K D ds mc ->
    evt asegs Q (LST 0x41c34 mc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 D (Z.of_nat (length ds)) x28 x29 x30 x31).
  Proof.
    induction ds as [|d r IH]; intros until x31; intros NE F0 OF0 G DC DLO DHI LE MI K; [congruence|]. clear NE.
    destruct d as [[[[[[[b sz] srz] nm] md] dy] loc] odr]. cbn [gfacts] in G.
    destruct G as (B8 & S8 & SZ & FB & BH & (junk & SHC) & OD0 & GN).
    assert (OD : (odr = NO_ODR /\ gfacts mc (b + srz) ofl r)
                 \/ (ofl <= odr < 0x5e6be3 /\ (exists c, rw_cells asegs mc odr [C1 c]) /\ gfacts mc (b + srz) (odr + 1) r)).
    { destruct OD0 as [ON|[OR OC]].
      - left. split; [exact ON|]. subst odr. rewrite Z.eqb_refl in GN. exact GN.
      - right. split; [exact OR|]. split; [exact OC|].
        replace (odr =? NO_ODR) with false in GN by (symmetry; apply Z.eqb_neq; unfold NO_ODR; lia). exact GN. }
    clear OD0 GN.
    change (desc_cells ((b, sz, srz, nm, md, dy, loc, odr) :: r)) with (desc_cells1 (b, sz, srz, nm, md, dy, loc, odr) ++ desc_cells r) in DC.
    cbn [desc_cells1] in DC.
    apply (proj1 (rw_cells_app asegs mc D _ _)) in DC. destruct DC as [DH DT]. cbn [cells_size csize Nat.add] in DT.
    change (Z.of_nat 64) with 64 in DT.
    assert (SHLO : 2147450880 <= sh b) by (unfold sh, SHADOW_OFF; assert (0 <= b / 8) by (apply Z.div_pos; lia); lia).
    assert (NEXT : forall (m1 : mem) (oflN : Z) y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
      munch (desc_fp1 (b, sz, srz, nm, md, dy, loc, odr)) mc m1 -> wmono asegs mc m1 -> odr_keep mc m1 -> mem_inv asegs m1 ->
      env_band_safe (desc_fp1 (b, sz, srz, nm, md, dy, loc, odr)) -> Forall (floor_ok (b + srz) oflN) (desc_fp1 (b, sz, srz, nm, md, dy, loc, odr)) ->
      0x147000 <= oflN -> gfacts mc (b + srz) oflN r ->
      (r <> [] -> evt asegs Q (LST 0x41c34 m1 y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 (D + 64) (Z.of_nat (length r)) y28 y29 y30 y31))
      /\ (r = [] -> evt asegs Q (LST 0x41e38 m1 y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 (D + 64) 0 y28 y29 y30 y31))).
    { intros until y31. intros MU1 WM1 OK1 MI1 SAFE FLO OFN G1. split; intros RE.
      - eapply (IH (D + 64) (b + srz) oflN m1); [exact RE| lia| exact OFN| | | lia| | | exact MI1| ].
        + eapply gfacts_frame; [| exact G1| exact MU1| exact WM1| exact FLO]. lia.
        + eapply env_cell_frame; [exact DT| exact MU1| exact WM1| exact SAFE| lia| rewrite cells_size_desc; cbn [length] in DHI; lia].
        + cbn [length] in DHI. lia.
        + eapply LENV_frame; eassumption.
        + eapply loop_K_step; eassumption.
      - subst r. pose proof (loop_K_step _ _ _ _ _ MU1 WM1 OK1 K) as K1. unfold loop_K in K1. cbn [length] in K1.
        replace (D + 64) with (D + 64 + 64 * Z.of_nat 0) by lia. apply K1; [apply munch_refl| apply wmono_refl| apply odr_keep_refl| exact MI1]. }
    ihide DT. ihide OD. ihide K.
    destruct LE as [IE XE]. pose proof (ie_inited _ IE) as INI. pose proof (ie_aflags _ IE) as AFL. pose proof (ie_shadow _ IE) as [_ SHB].
    pose proof (ie_real_mem _ IE) as RM. pose proof XE as (X1 & X2 & X3 & X4 & X5).
    unfold env_aflags in AFL. unfold env_real_mem in RM.
    pose proof (munch_refl [(sh b, sh b + srz / 8)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep.
    call inited_spec; [assumption | exact INI |].
    zstep. lit_branch.
    zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). zstep. lit_branch. zstep. lit_branch.
    do 6 zstep.
    replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879 by (vm_compute; reflexivity).
    zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
    zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. rewrite land7_mod8 in K2. lia. }
    pose proof (bytes_at_read asegs mc D _ 16 1 (proj2 (proj1 DH)) ltac:(lia) ltac:(cbn; lia)) as HR.
    cbv [cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app] in HR. change (Z.to_nat 16) with 16%nat in HR. cbn [skipn firstn] in HR.
    rewrite unsigned_lit in HR by lia.
    zstep. cbv beta. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    zstep. zstep. if_cases K3; zify_cond K3.
    { exfalso. rewrite land7_mod8 in K3. clear - K3 S8 SZ. Z.div_mod_to_equations. lia. }
    clear HR.
    zstep.
    call canpoison_spec; [assumption | exact X5 |].
    zstep. lit_branch.
    do 6 zstep. do 6 zstep.
    assert (EA : 2147450880 + b ≫ 3 = sh b) by (unfold sh, SHADOW_OFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    assert (EL : (2147450880 + (b + srz + -8) ≫ 3 + 1) mod 18446744073709551616 - (2147450880 + b ≫ 3) mod 18446744073709551616 = srz / 8).
    { clear - B8 S8 SZ FB F0 BH. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      apply Z.mod_divide in B8; [| lia]. destruct B8 as [kb ->]. apply Z.mod_divide in S8; [| lia]. destruct S8 as [ks ->].
      replace (kb * 8 + ks * 8 + -8) with ((kb + ks - 1) * 8) by lia. rewrite !Z.div_mul by lia.
      rewrite !Z.mod_small by lia. lia. }
    rewrite EL, EA.
    zstep. if_cases K4; zify_cond K4.
    2:{ exfalso. clear - K4 S8 SZ BH F0 FB. Z.div_mod_to_equations. lia. }
    do 3 zstep.
    assert (NB : 0 <= srz / 8 < 2^64) by (clear - SZ BH F0 FB; Z.div_mod_to_equations; lia).
    assert (SHHI : sh b + srz / 8 <= 2^40) by (clear - SZ BH F0 FB S8 B8; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
    call memset_specZ; [ exact SHC | assumption | lia | lia | lia |].
    assert (SAFE1 : env_band_safe [(sh b, sh b + srz / 8)]) by (unfold env_band_safe; repeat constructor; cbn [fst snd]; lia).
    assert (FLO1 : forall o, Forall (floor_ok (b + srz) o) [(sh b, sh b + srz / 8)]).
    { intros o. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. rewrite <- (sh_end_al b srz B8 S8). lia. }
    iunhide OD. destruct OD as [[ON G']|[OR [[c OC] G']]].
    -   subst odr. unfold NO_ODR in *.
      zstep. zstep. zstep. lit_branch. zstep. zstep.
      replace (Z.of_nat (length ((b, sz, srz, nm, md, dy, loc, 18446744073709551615) :: r)) + -1) with (Z.of_nat (length r)) by (cbn [length]; lia).
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        edestruct (NEXT m1 ofl) as [NX1 NX2]; [ exact MU | exact WM | | eassumption | exact SAFE1 | apply FLO1 | exact OF0 | exact G' | ] end.
      { intros o Ho [c0 Hc]. exists c0. eapply rw_cells_transport; [exact Hc| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      destruct r as [|d' r'].
      + cbn [length]. change (Z.of_nat 0) with 0. lit_branch. apply NX2. reflexivity.
      + if_cases K5; zify_cond K5.
        { exfalso. cbn [length] in K5, DHI. rewrite Z.mod_small in K5 by lia. lia. }
        apply NX1. discriminate.
    -
      assert (ONE : (odr =? NO_ODR) = false) by (apply Z.eqb_neq; unfold NO_ODR; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        assert (OC1 : rw_cells asegs m1 odr [C1 c]) by (eapply rw_cells_transport; [exact OC| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]) end.
      apply (munch_weaken _ [(sh b, sh b + srz / 8); (odr, odr + 1)]) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
      zstep. zstep. zstep. if_cases K6; zify_cond K6.
      2:{ exfalso. lia. }
      zstep.
      fix_lit_store.
      zstep. zstep.
      replace (Z.of_nat (length ((b, sz, srz, nm, md, dy, loc, odr) :: r)) + -1) with (Z.of_nat (length r)) by (cbn [length]; lia).
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        edestruct (NEXT m1 (odr + 1)) as [NX1 NX2]; [ | exact WM | | eassumption | | | | exact G' | ] end.
      { cbn [desc_fp1]. rewrite ONE. exact MU. }
      { intros o Ho [c0 Hc]. destruct (Z.eq_dec o odr) as [->|NEo]; [eexists; exact OC1|].
        exists c0. eapply rw_cells_transport; [exact Hc| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      { cbn [desc_fp1]. rewrite ONE. unfold env_band_safe. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
      { cbn [desc_fp1]. rewrite ONE. apply Forall_cons; [left; cbn [fst snd]; rewrite <- (sh_end_al b srz B8 S8); lia|].
        apply Forall_cons; [right; cbn [fst snd]; lia| apply Forall_nil]. }
      { lia. }
      destruct r as [|d' r'].
      + cbn [length]. change (Z.of_nat 0) with 0. lit_branch. zstep. apply NX2. reflexivity.
      + if_cases K5; zify_cond K5.
        2:{ exfalso. cbn [length] in K5, DHI. rewrite Z.mod_small in K5 by lia. lia. }
        apply NX1. discriminate.
  Qed.
End Loop.

Definition DESC_LO : Z := 0xafa20.
Definition DESC_SH : Z := 2147540804.
Definition psd_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (2147540804, 2147541452)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' 2147540804 [CB 648 (repeat (Z_to_bv 8 0) 648)].

Lemma psd_spec : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (junk : list byte),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 64 -> 0x10007fff8000 <= lo -> q < 2^64 ->
  LENV m -> rw_cells asegs m 2147540804 [CB 648 junk] ->
  evt asegs (psd_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0xafa20) (wz 5184) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x59800) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI ST LO KLO Q64 [IE XE] SHD.
  pose proof (ie_shadow _ IE) as [GSH SHB]. pose proof (ie_real_mem _ IE) as RM. pose proof (ie_cf _ IE) as CF.
  destruct XE as (X1 & X2 & X3 & X4 & X5). unfold env_real_mem in RM. unfold env_cf in CF. clear IE.
  pose proof (munch_refl [(lo, q); (2147540804, 2147541452)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  do 8 zstep.
  zstep. lit_branch.
  zstep. zstep. lit_branch.
  do 7 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879 by (vm_compute; reflexivity).
  zstep. lit_branch.
  zstep. zstep. lit_branch. zstep. zstep. zstep. lit_branch.
  do 3 zstep. zstep. lit_branch.
  do 5 zstep. zstep. lit_branch.
  do 3 zstep. zstep.
  lit_branch. zstep. zstep.
  do 10 zstep.
  release_frame FR ST q.
  call memset_specZ; [ exact SHD | assumption | lia | lia | lia |].
  unfold psd_post. finish.
Qed.

Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.
Ltac amo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_decide; exec_cbv; simp_is_x0; simp_regs; amo_decide; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Definition mid_band (W : list ivl) : Prop := Forall (fun iv => 0x147000 <= fst iv /\ snd iv <= 0x10007fff8000) W.
Lemma mid_band_disjoint : forall W A n, mid_band W -> (A + n <= 0x147000 \/ 0x10007fff8000 <= A) -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n MB H; cbn [disjoint_from]; [exact I|].
  inversion MB as [|x l P1 P2]; subst. cbn [fst snd] in P1. split; [lia| apply IH; assumption].
Qed.
Lemma mid_band_env_safe : forall W, mid_band W -> env_band_safe W.
Proof. intros W MB. unfold env_band_safe. eapply Forall_impl; [| exact MB]. intros [lo hi] P; cbn [fst snd] in *. lia. Qed.
Lemma mid_band_b : forall W, forallb (fun iv => (0x147000 <=? fst iv) && (snd iv <=? 0x10007fff8000)) W = true -> mid_band W.
Proof.
  intros W H. unfold mid_band. apply Forall_forall. intros iv HIn. rewrite forallb_forall in H. specialize (H iv HIn).
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma disjoint_from_b : forall W A n, forallb (fun iv => (A + n <=? fst iv) || (snd iv <=? A)) W = true -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n H; cbn [disjoint_from]; [exact I|]. cbn [forallb fst snd] in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply orb_true_iff in H1. split; [| apply IH; exact H2].
  destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.
Definition WL0 : list ivl := loop_fp A0_DESCS.
Lemma WL0_band : mid_band WL0.
Proof. apply mid_band_b. vm_compute. reflexivity. Qed.
Lemma WL0_desc_sh : disjoint_from WL0 2147540804 648.
Proof. apply disjoint_from_b. vm_compute. reflexivity. Qed.

Definition xband_safe (W : list ivl) : Prop :=
  Forall (fun iv => snd iv <= 0xaa000 \/ 0x147000 <= fst iv \/ (728560 <= fst iv /\ snd iv <= 728568) \/ (724608 <= fst iv /\ snd iv <= 724616)) W.
Lemma xband_disjoint : forall W A n, xband_safe W -> 0xaa000 <= A -> A + n <= 0x147000 -> (A + n <= 728560 \/ 728568 <= A) ->
  (A + n <= 724608 \/ 724616 <= A) -> disjoint_from W A n.
Proof.
  intros W A n SAFE H1 H2 H3 H4. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SAFE as [|x l S1 S2]; subst. split; [cbn in S1; lia| apply IH; exact S2].
Qed.
Ltac ecfx H MU WM SAFE := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply xband_disjoint; [exact SAFE| lia| cbn [cells_size csize Nat.add]; lia| cbn [cells_size csize Nat.add]; lia| cbn [cells_size csize Nat.add]; lia]].
Lemma LENV_frame_x : forall W m m', LENV m -> munch W m m' -> wmono asegs m m' -> xband_safe W -> LENV m'.
Proof.
  intros W m m' [IE (X1 & X2 & X3 & X4 & X5)] MU WM SAFE.
  destruct IE as ((G1 & G2) & (L1 & L2) & I1 & R1 & M1 & C1 & F1 & (S1 & S2 & S3) & (O1 & O2) & K1 & A1 & (B1 & B2 & B3 & B4) & B5 & B6 & B7 & (B8a & B8b)).
  unfold LENV, dtor_xenv, icpt_env, env_shadow, env_layout, env_inited, env_ric, env_real_mem, env_cf, env_flags, env_real_str, env_real_io, env_ckpf, env_aflags, env_real_lib, env_real_lib2, env_got_rms, env_got_rmem, env_real_cmp in *.
  split.
  - split; [split; [ecfx G1 MU WM SAFE | ecfx G2 MU WM SAFE]|]. split; [split; [ecfx L1 MU WM SAFE | ecfx L2 MU WM SAFE]|].
    split; [ecfx I1 MU WM SAFE|]. split; [ecfx R1 MU WM SAFE|]. split; [ecfx M1 MU WM SAFE|]. split; [ecfx C1 MU WM SAFE|]. split; [ecfx F1 MU WM SAFE|].
    split; [split; [ecfx S1 MU WM SAFE| split; [ecfx S2 MU WM SAFE| ecfx S3 MU WM SAFE]]|]. split; [split; [ecfx O1 MU WM SAFE| ecfx O2 MU WM SAFE]|].
    split; [ecfx K1 MU WM SAFE|]. split; [ecfx A1 MU WM SAFE|].
    split; [split; [ecfx B1 MU WM SAFE| split; [ecfx B2 MU WM SAFE| split; [ecfx B3 MU WM SAFE| ecfx B4 MU WM SAFE]]]|].
    split; [ecfx B5 MU WM SAFE|]. split; [ecfx B6 MU WM SAFE|]. split; [ecfx B7 MU WM SAFE|]. split; [ecfx B8a MU WM SAFE| ecfx B8b MU WM SAFE].
  - split; [ecfx X1 MU WM SAFE|]. split; [ecfx X2 MU WM SAFE|]. split; [ecfx X3 MU WM SAFE|]. split; [ecfx X4 MU WM SAFE| ecfx X5 MU WM SAFE].
Qed.

Definition MUTEX : Z := 0xb1df0.
Definition unreg_W (lo q : Z) (WL : list ivl) : list ivl := (lo, q) :: (728560, 728568) :: (2147540804, 2147541452) :: WL.
Definition unreg_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (WL : list ivl) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (unreg_W lo q WL) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' 728560 [C8 (wz 0)]
    /\ exists c0 c1 c2, rw_cells asegs m' 6188000 [C1 c0; C1 c1; C1 c2].

Section Unreg.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis LO : lo <= q - 176 - 64.
  Hypothesis KLO : 0x10007fff8000 <= lo.
  Hypothesis Q64 : q < 2^64.
  Variable ds : list desc.
  Hypothesis DLEN : length ds = 81%nat.
  Hypothesis WLB : mid_band (loop_fp ds).
  Hypothesis WLD : disjoint_from (loop_fp ds) 2147540804 648.
  Variables (junkD : list byte) (b0 b1 b2 : byte).
  Notation WL := (loop_fp ds).
  Notation APOST := (unreg_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo WL m).
  Notation W := (unreg_W lo q WL).

  #[using="LO KLO Q64 DLEN"] Lemma unreg_tail : forall (mt : mem) (j8 junkS : list byte) (c0 c1 c2 : byte) x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
    rw_cells asegs mt (q + -176) [CB 8 j8; C8 (wz 728568); C8 (wz 728496); C8 (wz 81); C8 (wz 719392); C8 (wz 741920); C8 (wz 1327072);
                                  C8 (wz 741936); C8 (wz 741928); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mt lo (q + -176) -> mem_inv asegs mt -> munch W m mt -> wmono asegs m mt ->
    rw_cells asegs mt 6188000 [C1 c0; C1 c1; C1 c2] -> LENV mt -> rw_cells asegs mt 728560 [C8 (wz 1152921504606846976)] -> rw_cells asegs mt 2147540804 [CB 648 junkS] ->
    evt asegs APOST (MS (mkR x1 (wz (q + -176)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (wz 728560) x25 x26 x27 x28 x29 x30 x31)
                       F (wz 0x41e38) fc None mt (seg_rom asegs)).
  Proof.
    intros until x31. intros FR STt MIt MU WM ODRt LEt MTXt SHDt. unfold unreg_W in MU.
    do 6 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply evt_cut;
      [ eapply psd_spec with (lo := lo) (junk := junkS); [ exact MIt | exact STt | lia | lia | lia | exact LEt | exact SHDt ]
      | post_call asegs mm ] end.
    do 15 zstep.
    zstep. zstep. zstep. lit_branch. zstep. zstep. lit_branch.
    do 7 zstep. zstep. lit_branch.
    amo_step. zstep. lit_branch. amo_step. fix_lit_store. zstep. lit_branch. zstep. lit_branch. zstep. lit_branch.
    do 15 zstep.
    release_frame FR PC q.
    unfold unreg_post, unreg_W. finish.
    exists c0, c1, c2. exact ODRt.
  Qed.

  #[using="LO KLO Q64 DLEN WLB WLD"] Lemma unreg_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    mem_inv asegs m -> stk asegs m lo q -> LENV m -> rw_cells asegs m 728560 [C8 (wz 0)] ->
    rw_cells asegs m 719392 (desc_cells ds) -> gfacts m 0 0x5e6be0 ds ->
    rw_cells asegs m 2147540804 [CB 648 junkD] -> rw_cells asegs m 6188000 [C1 b0; C1 b1; C1 b2] ->
    evt asegs APOST (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 719392) (wz 81) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz 0x41a78) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros MI ST LE MTX DC GF SHD ODR. pose proof (munch_refl [(lo, q); (728560, 728568)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct LE as [IE XE]. pose proof (ie_cf _ IE) as CF. pose proof (ie_aflags _ IE) as AFL. pose proof (ie_shadow _ IE) as [GSH SHB].
    pose proof (ie_layout _ IE) as [GLAY LAY].
    pose proof XE as (X1 & X2 & X3 & X4 & X5). unfold env_cf in CF. unfold env_aflags in AFL.
    pose proof DC as DC0. ihide DC0.
    carve_frame 176%nat ST.
    do 14 zstep.
    do 4 zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). zstep. fix_lit_store. zstep. lit_branch.
    do 8 zstep. zstep. do 3 zstep.
    zstep. zstep. fix_lit_store. do 5 zstep. zstep. lit_branch. zstep. zstep.
    amo_step.
    zstep. lit_branch.
    amo_step.
    fix_lit_store.
    zstep. lit_branch. zstep. lit_branch.
    zstep. fix_lit_store. zstep. fix_lit_store. zstep. lit_branch.
    do 7 zstep. zstep. zstep.
    zstep. fix_lit_store. zstep. zstep. fix_lit_store. zstep. zstep. fix_lit_store.
    zstep. zstep. zstep. zstep. fix_lit_store.
    do 6 zstep.
    assert (SAFE0 : env_band_safe [(lo, q)]) by (unfold env_band_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]).
    assert (FL0 : Forall (floor_ok 0 6188000) [(lo, q); (728560, 728568)]).
    { apply Forall_cons; [right; right; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia| apply Forall_nil]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (gfacts_frame ds 0 6188000 m m1 _ ltac:(lia) GF MU WM FL0) as GF1 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (DC1 : rw_cells asegs m1 719392 (desc_cells ds)) end.
    { iunhide DC0. eapply rw_cells_transport; [exact DC0| exact MU| exact WM|]. rewrite cells_size_desc, DLEN. cbn [disjoint_from]. lia. }
    clear DC0.
    assert (XS0 : xband_safe [(lo, q); (728560, 728568)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [right; right; left; cbn [fst snd]; lia| apply Forall_nil]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (LENV_frame_x _ m m1 (conj IE XE) MU WM XS0) as LE1 end.
    replace 81 with (Z.of_nat (length ds)) by (rewrite DLEN; reflexivity).
    eapply dloop with (fl := 0) (ofl := 6188000).
    - intros E. rewrite E in DLEN. discriminate.
    - lia.
    - lia.
    - exact GF1.
    - exact DC1.
    - lia.
    - rewrite DLEN. lia.
    - exact LE1.
    - exact MI.
    - unfold loop_K. intros until x31. intros MU' WM' OK' MI'.
      assert (HI0 : 0x10007fff8000 <= q + -176) by lia.
      assert (FRt := rw_cells_transport asegs _ _ _ _ _ FR MU' WM' (mid_band_disjoint _ _ _ WLB (or_intror HI0))).
      assert (STt := stk_transport_disjoint asegs _ _ _ _ _ ST MU' WM' (mid_band_disjoint _ _ _ WLB (or_intror KLO))).
      assert (MTXt : rw_cells asegs mc' 728560 [C8 (wz 1152921504606846976)]).
      { eapply rw_cells_transport; [exact MTX| exact MU'| exact WM'|]. apply mid_band_disjoint; [exact WLB|]. left. cbn [cells_size csize Nat.add]. lia. }
      assert (SHDt := rw_cells_transport asegs _ _ _ _ _ SHD MU' WM' WLD).
      assert (LEt := LENV_frame _ _ _ LE1 MU' WM' (mid_band_env_safe _ WLB)).
      assert (ODRt : exists c0 c1 c2, rw_cells asegs mc' 6188000 [C1 c0; C1 c1; C1 c2]).
      { apply (proj1 (rw_cells_app asegs _ 6188000 [C1 b0] [C1 b1; C1 b2])) in ODR. destruct ODR as [O0 O12].
        cbn [cells_size csize Nat.add] in O12. change (6188000 + Z.of_nat 1) with 6188001 in O12.
        apply (proj1 (rw_cells_app asegs _ 6188001 [C1 b1] [C1 b2])) in O12. destruct O12 as [O1 O2].
        cbn [cells_size csize Nat.add] in O2. change (6188001 + Z.of_nat 1) with 6188002 in O2.
        destruct (OK' 6188000 ltac:(lia) (ex_intro _ b0 O0)) as [c0 P0].
        destruct (OK' 6188001 ltac:(lia) (ex_intro _ b1 O1)) as [c1 P1].
        destruct (OK' 6188002 ltac:(lia) (ex_intro _ b2 O2)) as [c2 P2].
        exists c0, c1, c2.
        apply (proj2 (rw_cells_app asegs _ 6188000 [C1 c0] [C1 c1; C1 c2])). split; [exact P0|].
        cbn [cells_size csize Nat.add]. change (6188000 + Z.of_nat 1) with 6188001.
        apply (proj2 (rw_cells_app asegs _ 6188001 [C1 c1] [C1 c2])). split; [exact P1|].
        cbn [cells_size csize Nat.add]. change (6188001 + Z.of_nat 1) with 6188002. exact P2. }
      destruct ODRt as (c0 & c1 & c2 & ODRt).
      eapply unreg_tail; [exact FRt| exact STt| exact MI'| | | exact ODRt| exact LEt| exact MTXt| exact SHDt].
      + eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']];
          unfold unreg_W, sub_fp; intros x HX; cbn [outside] in *; tauto.
      + eapply wmono_trans; eassumption.
  Qed.
End Unreg.

Fixpoint desc_okb (fl ofl : Z) (ds : list desc) : bool :=
  match ds with
  | [] => true
  | d :: r => match d with (b, _, srz, _, _, _, _, odr) =>
      (b mod 8 =? 0) && (srz mod 8 =? 0) && (8 <=? srz) && (fl <=? b) && (b + srz <=? 0x7fff8000)
      && ((odr =? NO_ODR) || ((ofl <=? odr) && (odr <? 0x5e6be3) && (0x5e6be0 <=? odr)))
      && desc_okb (b + srz) (if odr =? NO_ODR then ofl else odr + 1) r
      end
  end.

Lemma gfacts_intro : forall (m : mem) ds fl ofl, desc_okb fl ofl ds = true ->
  Forall (fun g => match g with (b, srz, _) => exists bs, rw_cells asegs m (sh b) [CB (Z.to_nat (srz / 8)) bs] end) (map desc_glob ds) ->
  (forall o, 0x5e6be0 <= o < 0x5e6be3 -> exists c, rw_cells asegs m o [C1 c]) ->
  gfacts m fl ofl ds.
Proof.
  intros m. induction ds as [|d r IH]; intros fl ofl OKB FA OC; [exact I|].
  destruct d as [[[[[[[b sz] srz] nm] md] dy] loc] odr]. cbn [desc_okb] in OKB. cbn [map desc_glob] in FA.
  inversion FA as [|x l P1 P2]; subst. cbn [gfacts].
  apply andb_true_iff in OKB. destruct OKB as [OKB ONX].
  apply andb_true_iff in OKB. destruct OKB as [OKB OOD].
  apply andb_true_iff in OKB. destruct OKB as [OKB O5].
  apply andb_true_iff in OKB. destruct OKB as [OKB O4].
  apply andb_true_iff in OKB. destruct OKB as [OKB O3].
  apply andb_true_iff in OKB. destruct OKB as [O1 O2].
  apply Z.eqb_eq in O1, O2. apply Z.leb_le in O3, O4, O5.
  split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [exact O5|].
  split; [exact P1|]. split; [| apply IH; assumption].
  apply orb_true_iff in OOD. destruct OOD as [OE|OR].
  - left. apply Z.eqb_eq in OE. exact OE.
  - right. apply andb_true_iff in OR. destruct OR as [OR R3]. apply andb_true_iff in OR. destruct OR as [R1 R2].
    apply Z.leb_le in R1, R3. apply Z.ltb_lt in R2. split; [lia|]. apply OC. lia.
Qed.
Lemma A0_DESCS_ok : desc_okb 0 0x5e6be0 A0_DESCS = true.
Proof. vm_compute. reflexivity. Qed.

Definition dtor_Wx (lo q : Z) : list ivl := (lo, q) :: (724608, 724616) :: (728560, 728568) :: (2147540804, 2147541452) :: WL0.
Definition dtor_post_x (ra0 : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch (dtor_Wx lo q) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q
    /\ rw_cells asegs m' 728560 [C8 (wz 0)]
    /\ (exists c0 c1 c2, rw_cells asegs m' 6188000 [C1 c0; C1 c1; C1 c2])
    /\ (exists fw', rw_cells asegs m' 724608 [C8 fw']).

Lemma asan_dtor_spec : forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (fw : word) (b0 b1 b2 : byte) (junkD : list byte),
  mem_inv asegs m -> stk asegs m lo q -> lo <= q - 272 -> 0x10007fff8000 <= lo -> q < 2^64 ->
  LENV m -> rw_cells asegs m 728560 [C8 (wz 0)] -> rw_cells asegs m 719392 (desc_cells A0_DESCS) ->
  gfacts m 0 0x5e6be0 A0_DESCS -> rw_cells asegs m 2147540804 [CB 648 junkD] ->
  rw_cells asegs m 6188000 [C1 b0; C1 b1; C1 b2] -> rw_cells asegs m 724608 [C8 fw] ->
  evt asegs (dtor_post_x ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8ba48) fc None m (seg_rom asegs)).
Proof.
  intros until junkD. intros MI ST LO KLO Q64 LE MTX DC GF SHD ODR FLAG.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof LE as [IE (X1 & X2 & X3 & X4 & X5)].
  pose proof DC as DC0. ihide DC0. clear DC.
  carve_frame 16%nat ST.
  do 8 zstep.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. fix_lit_store. zstep. zstep. lit_branch. zstep. zstep.
  zstep.
  if_cases KF.
  -
    do 4 zstep.
    release_frame FR0 ST (q + -16).
    do 3 zstep.
    release_frame FR ST q.
    apply (munch_weaken _ (dtor_Wx lo q)) in MU; [| unfold dtor_Wx, sub_fp; intros x HX; cbn [outside] in *; tauto].
    unfold dtor_post_x. finish.
    + exists b0, b1, b2. exact ODR.
    + exists fw. exact FLAG.
  -
    zstep. zstep. zstep. lit_branch. do 4 zstep.
    assert (SAFE0 : env_band_safe [(lo, q)]) by (unfold env_band_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]).
    assert (FL0 : Forall (floor_ok 0 6188000) [(lo, q)]) by (apply Forall_cons; [right; right; cbn [fst snd]; lia| apply Forall_nil]).
    pose proof (LENV_frame _ _ _ LE MU WM SAFE0) as LE1.
    pose proof (gfacts_frame _ 0 6188000 _ _ _ ltac:(lia) GF MU WM FL0) as GF1.
    assert (DC1 : rw_cells asegs m0 719392 (desc_cells A0_DESCS)).
    { iunhide DC0. eapply env_cell_frame; [exact DC0| exact MU| exact WM| exact SAFE0| lia| rewrite cells_size_desc; change (length A0_DESCS) with 81%nat; lia]. }
    clear DC0.
    eapply evt_cut.
    { eapply unreg_body with (lo := lo) (ds := A0_DESCS) (junkD := junkD) (b0 := b0) (b1 := b1) (b2 := b2);
        [ lia | exact KLO | lia | reflexivity | exact WL0_band | exact WL0_desc_sh | exact MI | exact ST | exact LE1 | exact MTX | exact DC1 | exact GF1 | exact SHD | exact ODR ]. }
    intros ms' PO. unfold unreg_post in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & E & MUc & WMc & MIc & STc & MTXc & ODRc).
    subst ms'. change (loop_fp A0_DESCS) with WL0 in MUc.
    destruct ODRc as (c0 & c1 & c2 & ODRc).
    assert (DJ : forall A n, (A + n <= 1339392 \/ q + -32 <= A) -> A + n <= lo \/ q + -32 <= A -> A + n <= 728560 \/ 728568 <= A ->
                 disjoint_from (unreg_W lo (q + -32) WL0) A n).
    { intros A n H1 H2 H3. unfold unreg_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
      apply mid_band_disjoint; [exact WL0_band| lia]. }
    eapply rw_cells_transport in FR; [| exact MUc| exact WMc| apply DJ; cbn [cells_size csize Nat.add]; lia].
    eapply rw_cells_transport in FR0; [| exact MUc| exact WMc| apply DJ; cbn [cells_size csize Nat.add]; lia].
    eapply rw_cells_transport in FLAG; [| exact MUc| exact WMc| apply DJ; cbn [cells_size csize Nat.add]; lia].
    assert (MU' : munch (dtor_Wx lo q) m m').
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUc]]; clear;
        unfold dtor_Wx, unreg_W; generalize WL0; intros WLx;
        unfold sub_fp; intros x HX; cbn [outside] in HX |- *; destruct HX as (H1 & H2 & H3 & H4 & H5).
      - split; [exact H1| exact I].
      - split; [lia|]. split; [exact H3|]. split; [exact H4| exact H5]. }
    pose proof (wmono_trans asegs _ _ _ WM WMc) as WM'.
    clear MU WM MUc WMc MI ST LE LE1 IE GF GF1 DC1 MTX SHD ODR DJ. clear X1 X2 X3 X4 X5. unfold dtor_Wx in MU'.
    replace (ret_pc (Z_to_bv 64 270568)) with (Z_to_bv 64 270568) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    fix_lit_store.
    do 4 zstep.
    release_frame FR0 STc (q + -16).
    do 3 zstep.
    release_frame FR STc q.
    unfold dtor_post_x, dtor_Wx. finish.
    + exists c0, c1, c2. exact ODRc.
    + eexists. exact FLAG.
Qed.

Lemma dtor_Wx_xband : forall lo q, 0x147000 <= lo -> xband_safe (dtor_Wx lo q).
Proof.
  intros lo q H. unfold dtor_Wx, xband_safe.
  apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [right; right; right; cbn [fst snd]; lia|].
  apply Forall_cons; [right; right; left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; lia|].
  eapply Forall_impl; [| exact WL0_band]. intros [a b] P; cbn [fst snd] in *. lia.
Qed.
