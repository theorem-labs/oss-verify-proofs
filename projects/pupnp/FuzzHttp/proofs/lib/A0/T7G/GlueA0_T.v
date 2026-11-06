(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling RunWord InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Stdio.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import A0LZ AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface RDriverA_kit RDriverA_ctx RDriverA_main.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require GlueIcpt GlueDtor.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation z64 := (Z_to_bv 64 0).

Lemma stderr_wfile0_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> stderr_wfile0 m.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [| split; [vm_compute; reflexivity| split; [left; reflexivity| lia]]].
  aimg V m HM 0xaeac8 (file_cells (Z_to_bv 64 5) 0 0 0 0x9a800 0x607078 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) H. exact H.
Qed.

Lemma stdout_file_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> stdout_file m stdout_init.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  cbn [so_active so_buf so_lbf_nl so_first stdout_init Prelim.zlength length Z.of_nat Z.add].
  split. { aimg V m HM 0xaebb8 (file_cells (Z_to_bv 64 5) 0 0 0 0x9b204 0x607080 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) H. exact H. }
  split; [vm_compute; reflexivity|].
  split. { aimg V m HM 0x607080 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] H. exact H. }
  split; [reflexivity|]. split; [unfold zlength; cbn; lia| intros _; reflexivity].
Qed.

Lemma stdin_file_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> stdin_file m.
Proof. intros V m HM. unfold stdin_file. aimg V m HM 0xaeca8 stdin_cells H. exact H. Qed.

Lemma rw_cells_app2 : forall (m : mem) A cs1 cs2 B, rw_cells asegs m A cs1 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells asegs m B cs2 ->
  rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A cs1 cs2 B H1 -> H2. apply (proj2 (rw_cells_app asegs m A cs1 cs2)). split; assumption. Qed.

Lemma exitc_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> EXITC (V 44%nat) m.
Proof.
  intros V m HM. unfold EXITC.
  split. { mf V m HM (MCell (ZLit 6187208) 4 (ZV 44)) H. exact H. }
  split. { aimg V m HM 0x606be0 [C4 z64] H. exact H. }
  split.
  { exists (repeat (Z_to_bv 8 0) 3), (repeat (Z_to_bv 8 0) 4).
    aimg V m HM 0x6069c0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64] H1.
    mf V m HM (MCell (ZLit 6318536) 4 (ZLit 1)) H2.
    aimg V m HM 0x6069cc [CB 4 (repeat (Z_to_bv 8 0) 4)] H3.
    mf V m HM (MCell (ZLit 6318544) 8 (ZLit 6318552)) H4.
    aimg V m HM 0x6069d8 [C8 z64] H5.
    mf V m HM (MCell (ZLit 6318560) 8 (ZLit 608816)) H6.
    aimg V m HM 0x6069e8 [C8 z64] H7.
    pose proof (rw_cells_app2 m _ _ _ 0x6069e8 H6 eq_refl H7) as J6.
    pose proof (rw_cells_app2 m _ _ _ 0x6069e0 H5 eq_refl J6) as J5.
    pose proof (rw_cells_app2 m _ _ _ 0x6069d8 H4 eq_refl J5) as J4.
    pose proof (rw_cells_app2 m _ _ _ 0x6069d0 H3 eq_refl J4) as J3.
    pose proof (rw_cells_app2 m _ _ _ 0x6069cc H2 eq_refl J3) as J2.
    pose proof (rw_cells_app2 m _ _ _ 0x6069c8 H1 eq_refl J2) as J1.
    exact J1. }
  split.
  { mf V m HM (MCell (ZLit 6318816) 8 (ZLit 482004)) H1.
    aimg V m HM 0x606ae8 [C8 z64] H2.
    exact (rw_cells_app2 m _ _ _ 0x606ae8 H1 eq_refl H2). }
  split. { aimg V m HM 0x1457a0 [C1 (Z_to_bv 8 0)] H. exact H. }
  split.
  { exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), z64.
    mf V m HM (MCell (ZLit 6319104) 1 (ZLit 1)) H1.
    aimg V m HM 0x606c01 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64] H2.
    exact (rw_cells_app2 m _ _ _ 0x606c01 H1 eq_refl H2). }
  split. { aimg V m HM 0xaad98 [C8 (Z_to_bv 64 0xa9ae8); C8 (Z_to_bv 64 0xa9ad8)] H. exact H. }
  split. { aimg V m HM 0xa9ad8 [C8 (Z_to_bv 64 0x8b360); C8 (Z_to_bv 64 0x324d0)] H. exact H. }
  split. { aimg V m HM 0xaa0a0 [C8 (Z_to_bv 64 0x94968); C8 z64] H. exact H. }
  split. { exists (Z_to_bv 64 0xabde0). aimg V m HM 0xabde0 [C8 (Z_to_bv 64 0xabde0)] H. exact H. }
  split. { aimg V m HM 0x607068 [C8 z64] H. exact H. }
  split. { aimg V m HM 0xaed90 [C8 (Z_to_bv 64 0xaeca8)] H. exact H. }
  split. { aimg V m HM 0xaeca0 [C8 (Z_to_bv 64 0xaebb8)] H. exact H. }
  aimg V m HM 0xaebb0 [C8 (Z_to_bv 64 0xaeac8)] H. exact H.
Qed.

Lemma ssp_guard_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m ssp_guard [C8 (Z_to_bv 64 (V 45%nat))].
Proof.
  intros V m HM. mf V m HM (MRo (ZLit 6318512) 8 (ZV 45)) H. unfold ssp_guard.
  apply rw_cell_of_bytes; [cbn; repeat split; exact I| | lia| cbn; lia].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma mainc_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> MAINC (Z_to_bv 64 (V 45%nat)) m.
Proof.
  intros V m HM. unfold MAINC, ssp_cells.
  split. { aimg V m HM 0xaad30 [C8 (Z_to_bv 64 0xa9fc8); C8 z64] H. exact H. }
  split. { aimg V m HM 0xa9fc8 [C8 (Z_to_bv 64 0xaeac8)] H. exact H. }
  split. { split; [| apply (ssp_guard_init V m HM)]. unfold got_ssp, ssp_guard. aimg V m HM 0xaad68 [C8 (Z_to_bv 64 0x6069b0)] H. exact H. }
  split. { aimg V m HM 0x5e5f50 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)] H. exact H. }
  aimg V m HM 0x5e5f60 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H.
Qed.

Lemma errno_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m 0x5e68cc [C4 z64].
Proof. intros V m HM. aimg V m HM 0x5e68cc [C4 z64] H. exact H. Qed.

Lemma rsva_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> stk asegs m RSVA (RSVA + 65536).
Proof.
  intros V m HM.
  mimg V m HM 0x5d5f50 0x5e5f50 NONE.
  assert (H : rw_cells asegs m RSVA [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) (repeat (Z_to_bv 8 0) (Z.to_nat 65536))]).
  { apply (InitMem.rw_cells_image0 asegs m RSVA (repeat (Z_to_bv 8 0) (Z.to_nat 65536)));
      [ intros a Ha; rewrite repeat_length, Z2Nat.id in Ha by lia; rewrite <- (Z_to_bv_bv_unsigned a); apply NONE; unfold RSVA in Ha; lia
      | vm_compute; reflexivity | unfold RSVA; lia | rewrite repeat_length, Z2Nat.id by lia; unfold RSVA; lia ]. }
  pose proof (stk_of_rw_cells asegs _ _ _ H) as ST.
  lazymatch type of ST with stk _ _ _ ?hi => replace hi with (RSVA + 65536) in ST; [exact ST|] end.
  cbn [cells_size csize]. rewrite Nat.add_0_r, repeat_length, Z2Nat.id by lia. reflexivity.
Qed.

Lemma shz_of_cover : forall V (m : mem) l fuel lo hi, Forall (mfact_ok asegs V m) l -> cover true l fuel lo hi = true -> shz m lo hi.
Proof. intros V m l fuel lo hi HF C a Ha. exact (proj2 (cover_sound V m true l fuel lo hi HF C a Ha) eq_refl). Qed.
Lemma shr_of_cover : forall V (m : mem) l fuel lo hi, Forall (mfact_ok asegs V m) l -> cover false l fuel lo hi = true -> shr m lo hi.
Proof. intros V m l fuel lo hi HF C a Ha. exact (proj1 (cover_sound V m false l fuel lo hi HF C a Ha)). Qed.

Section SHZ_init.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp0 := (bv_unsigned sp0).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).

  #[using="Type"] Lemma shz_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts ->
    32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp0 -> 0 <= V 6%nat < 256 -> 0 <= V 10%nat < 8 ->
    alloc_ceiling = usp0 - 8388608 -> 0x7fff80000000 <= usp0 ->
    SHZ sp0 argv envp uid hw rnd m.
  Proof.
    intros V m HM PSP R6 R10 CEIL SPLO. unfold SHZ.
    split. { split; [eapply (shz_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]
                    | eapply (shr_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]]. }
    split. { split; [eapply (shz_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]
                    | eapply (shr_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]]. }
    split. { split; [eapply (shz_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]
                    | eapply (shr_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]]. }
    mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
                      (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZS.
    assert (Z0 : forall a, sh alloc_ceiling - sh alloc_ceiling mod 8 <= a < SH_HI -> mrd asegs m (wa a) = Some (Z_to_bv 8 0)).
    { intros a Ha. unfold mrd.
      specialize (ZS (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))).
      replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) with a in ZS by lia.
      rewrite ZS; [reflexivity|]. unfold sh, SHADOW_OFF, SH_HI in Ha. rewrite CEIL in Ha. Z.div_mod_to_equations. lia. }
    split.
    - intros a Ha. apply Z0. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). pose proof (Z.le_min_r (sh (usp0 + Z.of_nat (length IMGB)) + 1) SH_HI). lia.
    - intros a Ha. exists (Z_to_bv 8 0). apply Z0. pose proof (Z.le_min_r (sh (usp0 + Z.of_nat (length IMGB)) + 8) SH_HI). lia.
  Qed.
End SHZ_init.

Lemma wr_at_sub0 : forall (m : mem) a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

Lemma globals_shadow_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> globals_shadow m.
Proof.
  intros V m HM. unfold globals_shadow.
  pose proof (mwr_find asegs V m _ (ZLit 2147459072) 782848 HM ltac:(vm_compute; reflexivity)) as W. cbn [zv] in W.
  assert (R : shr m (sh 0x213e0) (sh 0x5e6060)) by (eapply (shr_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]).
  split; [|
    destruct (readable_bytes m 656%nat (sh 0xaedc0)) as (bsd & Ld & Bd);
      [ intros y Hy; apply R; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia
      | unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia
      | unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia
      | exists bsd; split; [split; [cbn; split; [exact Ld| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Bd]|];
        cbn [cells_size csize]; rewrite Nat.add_0_r; eapply wr_at_sub0; [exact W| | |]; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia ] ].
  apply Forall_forall. intros [[b srz] odr] Hin.
  pose proof (proj1 (Forall_forall _ _) globals_bounds _ Hin) as (B1 & B2 & B3 & B4). cbn beta iota in B1, B2, B3, B4.
  destruct (readable_bytes m (Z.to_nat (srz / 8)) (sh b)) as (bs & L & B).
  { intros y Hy. apply R. unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
  { unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. }
  { unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia. }
  exists bs. split; [split; [cbn; split; [exact L| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_sub0; [exact W| | |]; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia.
Qed.

Section IMGK_init.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Notation IMGB := (build_stack_bytes rph sp argv envp uid hw rnd).
  Hypothesis FIT : usp + Z.of_nat (length IMGB) <= 2^64.
  Hypothesis ARGC : 1 <= Z.of_nat (length argv) <= 1024.
  Hypothesis L0R : Z.of_nat (length (nth 0 argv [])) <= 131071.

  #[using="uid hw rnd FIT ARGC L0R"] Lemma argv_first2 : firstn 2 (argv_ptrs sp argv envp ++ [Z_to_bv 64 0]) =
    [Z_to_bv 64 (usp + 8 * argc argv + 8 * envc envp + 184);
     Z_to_bv 64 (Z.b2z (1 <? argc argv) * (usp + 8 * argc argv + 8 * envc envp + Z.of_nat (length (nth 0 argv [])) + 185))].
  Proof.
    unfold argv_ptrs, str_base, struct_size. destruct argv as [|a0 [|a1 r]]; [cbn in ARGC; lia| |].
    - cbn [str_ptrs map app firstn nth length]. unfold argc. cbn [length Z.of_nat Pos.of_succ_nat]. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont Z.b2z Z.mul].
      do 2 f_equal. lia.
    - cbn [str_ptrs map app firstn nth]. replace (1 <? argc (a0 :: a1 :: r)) with true by (symmetry; apply Z.ltb_lt; unfold argc; cbn [length]; lia).
      cbn [Z.b2z]. f_equal; [f_equal; lia|]. f_equal. f_equal. lia.
  Qed.

  #[using="FIT ARGC L0R"] Lemma imgk_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts ->
    32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp ->
    V 1%nat = argc argv -> V 2%nat = envc envp -> V 3%nat = Z.of_nat (length (nth 0 argv [])) ->
    (forall a, usp + struct_size argv envp <= a < usp + Z.of_nat (length IMGB) - 16 ->
       m (wa a) = wrap_mem rph sp argv envp uid hw rnd (wa a)) ->
    IMGK sp argv envp uid hw rnd m.
  Proof.
    intros V m HM PSP P1 P2 P3 HID.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    split; [lia|]. split; [exact FIT|]. intros i [Hi|Hi].
    -
      mf V m HM (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))) F1.
      mf V m HM (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8 (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185)))) F2.
      rewrite P1, P2 in F1. rewrite P1, P2, P3 in F2.
      replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + 8) with (usp + 8) in F1 by lia.
      replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + 16) with (usp + 8 + Z.of_nat (length (le8 (Z_to_bv 64 (usp + 8 * argc argv + 8 * envc envp + 184))))) in F2 by (rewrite length_le8; lia).
      replace (32768 * V 0%nat + (8 * argc argv + (8 * envc envp + (16 * V 6%nat + 4096 * V 10%nat))) + 184) with (usp + 8 * argc argv + 8 * envc envp + 184) in F1 by lia.
      replace (1 mod two64 <? argc argv mod two64) with (1 <? argc argv) in F2
        by (unfold two64; rewrite !Z.mod_small by (unfold argc; lia); reflexivity).
      replace (32768 * V 0%nat + (8 * argc argv + (8 * envc envp + (Z.of_nat (length (nth 0 argv [])) + (16 * V 6%nat + 4096 * V 10%nat)))) + 185)
        with (usp + 8 * argc argv + 8 * envc envp + Z.of_nat (length (nth 0 argv [])) + 185) in F2 by lia.
      pose proof (proj2 (bytes_at_app asegs m (usp + 8) _ _) (conj F1 F2)) as F12.
      destruct F12 as (_ & _ & FB).

      pose proof (stack_argv2 sp argv envp uid hw rnd _ (IMGK_of_bytes_at sp argv envp uid hw rnd _ (mcan_img sp argv envp uid hw rnd FIT)) ltac:(lia)) as S.
      rewrite argv_first2 in S. cbn [u64s] in S. rewrite app_nil_r in S. destruct S as (_ & _ & SB).
      destruct (mcan_img sp argv envp uid hw rnd FIT) as (_ & _ & MB).
      assert (L16 : length (le8 (Z_to_bv 64 (usp + 8 * argc argv + 8 * envc envp + 184)) ++
                            le8 (Z_to_bv 64 (Z.b2z (1 <? argc argv) * (usp + 8 * argc argv + 8 * envc envp + Z.of_nat (length (nth 0 argv [])) + 185)))) = 16%nat)
        by (rewrite length_app, !length_le8; reflexivity).
      specialize (FB (i - 8)%nat ltac:(unfold word_to_le_bytes in *; rewrite L16; lia)).
      specialize (SB (i - 8)%nat ltac:(rewrite L16; lia)).
      pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
      pose proof (raw_len_nonneg rph sp argv envp uid hw rnd) as RN.
      specialize (MB i ltac:(unfold raw_len, struct_size, argc, envc in *; lia)).
      replace (usp + 8 + Z.of_nat (i - 8)) with (usp + Z.of_nat i) in FB, SB by lia.
      rewrite FB. rewrite <- MB. rewrite SB. reflexivity.
    -
      pose proof (HID (usp + Z.of_nat i) ltac:(lia)) as E.
      rewrite (init_at_block rph sp argv envp uid hw rnd) in E by (rewrite wa_unsigned by lia; lia).
      rewrite wa_unsigned in E by lia. replace (Z.to_nat (usp + Z.of_nat i - usp)) with i in E by lia.
      unfold mrd. rewrite E. destruct (nth_error IMGB i) as [b|] eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  Qed.
End IMGK_init.

Lemma asan_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> asan_env asegs m.
Proof.
  intros V m HM. unfold asan_env. split; [| split; [| exact (GlueIcpt.icpt_env_init V m HM)]].
  - unfold asan_globals, A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL, SHADOW_OFF. split; [| split; [| split]].
    + aimg V m HM 0xaa0d0 [C8 (Z_to_bv 64 0xb38f8)] H. exact H.
    + mf V m HM (MCell (ZLit 735480) 8 (ZLit 2147450880)) H. exact H.
    + aimg V m HM 0xaa128 [C8 (Z_to_bv 64 0xb3900)] H. exact H.
    + mf V m HM (MCell (ZLit 735488) 4 (ZLit 1)) H. exact H.
  - unfold dtor_cells. split; [| split; [| exact (GlueDtor.dtor_cells6_init V m HM)]].
    + exists (Z_to_bv 64 1). mf V m HM (MCell (ZLit 721472) 8 (ZLit 1)) H. exact H.
    + exists (Z_to_bv 8 1), (Z_to_bv 8 1), (Z_to_bv 8 1).
      mf V m HM (MCell (ZLit 6184864) 1 (ZLit 1)) H1. mf V m HM (MCell (ZLit 6184865) 1 (ZLit 1)) H2. mf V m HM (MCell (ZLit 6184866) 1 (ZLit 1)) H3.
      exact (rw_cells_app2 m _ _ _ 6184865 H1 eq_refl (rw_cells_app2 m _ _ _ 6184866 H2 eq_refl H3)).
Qed.

Lemma a0_H0_false : forall V sp fs mo (a : word), amodel V sp fs mo ->
  (bv_unsigned sp - 8388608 <= bv_unsigned a \/ AIMG_LO <= bv_unsigned a < AIMG_HI) -> a0_H0 V mo a = false.
Proof.
  intros V sp fs mo a AM Ha. destruct (a0_H0 V mo a) eqn:E; [|reflexivity]. exfalso.
  unfold a0_H0 in E. apply andb_prop in E as [Hlz _].
  destruct (lazy_page_range mo a Hlz) as (r & Hr & Hin).
  pose proof (proj1 (Forall_forall _ _) (am_lazy_bounds _ _ _ _ AM) r Hr) as (Hc & Hs). lia.
Qed.

Lemma mem_inv_mrestrict : forall H (m : mem), mem_inv asegs m -> mem_inv asegs (mrestrict H m).
Proof. intros H m MI a b Hab. unfold mrestrict in Hab. destruct (H a); [discriminate|]. exact (MI a b Hab). Qed.

Lemma stk_mrestrict : forall H (m : mem) lo hi, stk asegs m lo hi -> (forall a, lo <= a < hi -> H (wa a) = false) -> stk asegs (mrestrict H m) lo hi.
Proof.
  intros H m lo hi (S0 & S1 & S) HF. split; [exact S0|]. split; [exact S1|]. intros a Ha.
  destruct (S a Ha) as [W R]. unfold wview, mrd, mrestrict in *. rewrite (HF a Ha). split; [exact W| exact R].
Qed.

Lemma bytes_at_le8_inj : forall (m : mem) A (x y : word), bytes_at asegs m A (le8 x) -> bytes_at asegs m A (le8 y) -> x = y.
Proof.
  intros m A x y (_ & _ & BX) (_ & _ & BY).
  rewrite <- (le_bytes_to_word_le8 x), <- (le_bytes_to_word_le8 y). f_equal.
  apply nth_error_ext. intros n. destruct (Nat.lt_ge_cases n 8) as [Hn|Hn].
  - rewrite <- (BX n) by (rewrite length_le8; exact Hn). rewrite <- (BY n) by (rewrite length_le8; exact Hn). reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_le8; exact Hn).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite length_le8; exact Hn). reflexivity.
Qed.

