(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the 27- or 29-pair auxv; the launch's input, mmap base and entry draw); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling RunWord InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Stdio.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsBoth B0Img MainEntryBoth B0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import B0LZ AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface RDriverA_kit RDriverA_ctx RDriverA_main.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require GlueIcpt GlueDtor.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation z64 := (Z_to_bv 64 0).

Lemma stderr_wfile0_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> stderr_wfile0 m.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [| split; [vm_compute; reflexivity| split; [left; reflexivity| lia]]].
  aimg V m HM 0xaf728 (file_cells (Z_to_bv 64 5) 0 0 0 0x9b464 0x607cb8 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) H. exact H.
Qed.

Lemma stdout_file_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> stdout_file m stdout_init.
Proof.
  intros V m HM. exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  cbn [so_active so_buf so_lbf_nl so_first stdout_init Prelim.zlength length Z.of_nat Z.add].
  split. { aimg V m HM 0xaf818 (file_cells (Z_to_bv 64 5) 0 0 0 0x9be68 0x607cc0 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) H. exact H. }
  split; [vm_compute; reflexivity|].
  split. { aimg V m HM 0x607cc0 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] H. exact H. }
  split; [reflexivity|]. split; [unfold zlength; cbn; lia| intros _; reflexivity].
Qed.

Lemma stdin_file_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> stdin_file m.
Proof. intros V m HM. unfold stdin_file. aimg V m HM 0xaf908 stdin_cells H. exact H. Qed.

Lemma rw_cells_app2 : forall (m : mem) A cs1 cs2 B, rw_cells asegs m A cs1 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells asegs m B cs2 ->
  rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A cs1 cs2 B H1 -> H2. apply (proj2 (rw_cells_app asegs m A cs1 cs2)). split; assumption. Qed.

Lemma exitc_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> EXITC (V 44%nat) m.
Proof.
  intros V m HM. unfold EXITC.
  split. { mf V m HM (MCell (ZLit 6190344) 4 (ZV 44)) H. exact H. }
  split. { aimg V m HM 0x607820 [C4 z64] H. exact H. }
  split.
  { exists (repeat (Z_to_bv 8 0) 3), (repeat (Z_to_bv 8 0) 4).
    aimg V m HM 0x607600 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 z64] H1.
    mf V m HM (MCell (ZLit 6321672) 4 (ZLit 1)) H2.
    aimg V m HM 0x60760c [CB 4 (repeat (Z_to_bv 8 0) 4)] H3.
    mf V m HM (MCell (ZLit 6321680) 8 (ZLit 6321688)) H4.
    aimg V m HM 0x607618 [C8 z64] H5.
    mf V m HM (MCell (ZLit 6321696) 8 (ZLit 611988)) H6.
    aimg V m HM 0x607628 [C8 z64] H7.
    pose proof (rw_cells_app2 m _ _ _ 0x607628 H6 eq_refl H7) as J6.
    pose proof (rw_cells_app2 m _ _ _ 0x607620 H5 eq_refl J6) as J5.
    pose proof (rw_cells_app2 m _ _ _ 0x607618 H4 eq_refl J5) as J4.
    pose proof (rw_cells_app2 m _ _ _ 0x607610 H3 eq_refl J4) as J3.
    pose proof (rw_cells_app2 m _ _ _ 0x60760c H2 eq_refl J3) as J2.
    pose proof (rw_cells_app2 m _ _ _ 0x607608 H1 eq_refl J2) as J1.
    exact J1. }
  split.
  { mf V m HM (MCell (ZLit 6321952) 8 (ZLit 481980)) H1.
    aimg V m HM 0x607728 [C8 z64] H2.
    exact (rw_cells_app2 m _ _ _ 0x607728 H1 eq_refl H2). }
  split. { aimg V m HM 0x1463e0 [C1 (Z_to_bv 8 0)] H. exact H. }
  split.
  { exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), z64.
    mf V m HM (MCell (ZLit 6322240) 1 (ZLit 1)) H1.
    aimg V m HM 0x607841 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64] H2.
    exact (rw_cells_app2 m _ _ _ 0x607841 H1 eq_refl H2). }
  split. { aimg V m HM 0xab9f8 [C8 (Z_to_bv 64 0xaa750); C8 (Z_to_bv 64 0xaa740)] H. exact H. }
  split. { aimg V m HM 0xaa740 [C8 (Z_to_bv 64 0x8ba48); C8 (Z_to_bv 64 0x324b8)] H. exact H. }
  split. { aimg V m HM 0xaad00 [C8 (Z_to_bv 64 0x955cc); C8 z64] H. exact H. }
  split. { exists (Z_to_bv 64 0xaca40). aimg V m HM 0xaca40 [C8 (Z_to_bv 64 0xaca40)] H. exact H. }
  split. { aimg V m HM 0x607ca8 [C8 z64] H. exact H. }
  split. { aimg V m HM 0xaf9f0 [C8 (Z_to_bv 64 0xaf908)] H. exact H. }
  split. { aimg V m HM 0xaf900 [C8 (Z_to_bv 64 0xaf818)] H. exact H. }
  aimg V m HM 0xaf810 [C8 (Z_to_bv 64 0xaf728)] H. exact H.
Qed.

Lemma ssp_guard_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> rw_cells asegs m ssp_guard [C8 (Z_to_bv 64 (V 45%nat))].
Proof.
  intros V m HM. mf V m HM (MRo (ZLit 6321648) 8 (ZV 45)) H. unfold ssp_guard.
  apply rw_cell_of_bytes; [cbn; repeat split; exact I| | lia| cbn; lia].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma mainc_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> MAINC (Z_to_bv 64 (V 45%nat)) m.
Proof.
  intros V m HM. unfold MAINC, ssp_cells.
  split. { aimg V m HM 0xab990 [C8 (Z_to_bv 64 0xaac28); C8 z64] H. exact H. }
  split. { aimg V m HM 0xaac28 [C8 (Z_to_bv 64 0xaf728)] H. exact H. }
  split. { split; [| apply (ssp_guard_init V m HM)]. unfold got_ssp, ssp_guard. aimg V m HM 0xab9c8 [C8 (Z_to_bv 64 0x6075f0)] H. exact H. }
  split. { aimg V m HM 0x5e6b90 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)] H. exact H. }
  aimg V m HM 0x5e6ba0 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H.
Qed.

Lemma errno_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> rw_cells asegs m 0x5e750c [C4 z64].
Proof. intros V m HM. aimg V m HM 0x5e750c [C4 z64] H. exact H. Qed.

Lemma rsva_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> stk asegs m RSVA (RSVA + 65536).
Proof.
  intros V m HM.
  mimg V m HM 0x5d6b90 0x5e6b90 NONE.
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
  Variables (sp0 : word) (argv envp : list (list byte)) (inp : ProcInput) (mbase : word) (rnd : EntryDraw).
  Notation usp0 := (bv_unsigned sp0).
  Notation IMGB := (build_stack_bytes (launch_auxv inp sp0 mbase) rph AENTRY sp0 (ed_top rnd) argv envp (in_execfn inp) (in_uid inp) (in_gid inp) (in_hwcap inp) rnd).

  #[using="Type"] Lemma shz_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts ->
    32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp0 -> 0 <= V 6%nat < 256 -> 0 <= V 10%nat < 8 ->
    alloc_ceiling = usp0 - 8388608 -> 0x7fff80000000 <= usp0 ->
    SHZ sp0 argv envp inp mbase rnd m.
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

Lemma globals_shadow_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> globals_shadow m.
Proof.
  intros V m HM. unfold globals_shadow.
  pose proof (mwr_find asegs V m _ (ZLit 2147459072) 782848 HM ltac:(vm_compute; reflexivity)) as W. cbn [zv] in W.
  assert (R : shr m (sh 0x213e0) (sh 0x5e6ca0)) by (eapply (shr_of_cover V m _ 1200%nat); [exact HM| vm_compute; reflexivity]).
  split; [|
    destruct (readable_bytes m 648%nat (sh 0xafa20)) as (bsd & Ld & Bd);
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

Lemma stack_to_mem_in : forall (base : word) (bytes : list byte) (a : word),
  bv_unsigned base <= bv_unsigned a < bv_unsigned base + Z.of_nat (length bytes) ->
  stack_to_mem base bytes a = nth_error bytes (Z.to_nat (bv_unsigned a - bv_unsigned base)).
Proof.
  intros base bytes a H. unfold stack_to_mem. cbv beta zeta.
  replace (Z.leb (bv_unsigned base) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb (bv_unsigned a - bv_unsigned base) (Z.of_nat (length bytes))) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(* The block the program reads at main, from the launch: the first two argv pointers (the start-up chain's
   cells) and the string area from argv[0] to the stack top, which nothing writes before main. *)
Section IMGK_init.
  Variables (sp : word) (inp : ProcInput) (mbase : word) (rnd : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Notation AV := (in_argv inp).
  Notation EV := (in_envp inp).
  Notation EFN := (in_execfn inp).
  Notation TOP := (ed_top rnd).
  Notation IMGB := (build_stack_bytes (launch_auxv inp sp mbase) rph AENTRY sp (ed_top rnd) AV EV (in_execfn inp) (in_uid inp) (in_gid inp) (in_hwcap inp) rnd).
  Hypothesis FIT : img_fits sp AV EV inp mbase rnd.
  Hypothesis ARGC : 1 <= Z.of_nat (length AV).

  #[using="ARGC"] Lemma argv_first2 : firstn 2 (argv_ptrs TOP AV EV EFN ++ [Z_to_bv 64 0]) =
    [Z_to_bv 64 (str_base TOP AV EV EFN);
     Z_to_bv 64 (Z.b2z (1 <? argc AV) * (str_base TOP AV EV EFN + Z.of_nat (length (nth 0 AV [])) + 1))].
  Proof.
    unfold argv_ptrs. clear FIT. destruct (in_argv inp) as [|a0 [|a1 r]] eqn:EA; [pose proof ARGC as A'; try rewrite EA in A'; cbn in A'; lia| |].
    - cbn [str_ptrs map app firstn nth]. replace (1 <? argc [a0]) with false by reflexivity. reflexivity.
    - cbn [str_ptrs map app firstn nth]. replace (1 <? argc (a0 :: a1 :: r)) with true by (symmetry; apply Z.ltb_lt; unfold argc; cbn [length]; lia).
      cbn [Z.b2z]. rewrite Z.mul_1_l. reflexivity.
  Qed.

  #[using="FIT ARGC"] Lemma imgk_init : forall (m : mem),
    bytes_at asegs m (usp + 8) (le8 (Z_to_bv 64 (str_base TOP AV EV EFN))) ->
    bytes_at asegs m (usp + 16) (le8 (Z_to_bv 64 (Z.b2z (1 <? argc AV) * (str_base TOP AV EV EFN + Z.of_nat (length (nth 0 AV [])) + 1)))) ->
    (forall a, str_base TOP AV EV EFN <= a < bv_unsigned TOP -> m (wa a) = wrap_mem inp mbase rph AENTRY sp rnd (wa a)) ->
    IMGK sp AV EV inp mbase rnd m.
  Proof.
    intros m C1 C2 HID.
    pose proof (fits_facts sp AV EV inp mbase rnd FIT) as (L & S & X1 & X2 & T1 & T2 & T3).
    assert (0 <= argc AV /\ 0 <= envc EV) by (unfold argc, envc; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (FIT64 : usp + Z.of_nat (length IMGB) <= 2^64) by lia.
    split; [exact FIT|]. split; [lia|]. split; [exact FIT64|]. intros i [Hi|Hi].
    - replace (usp + 16) with (usp + 8 + Z.of_nat (length (le8 (Z_to_bv 64 (str_base TOP AV EV EFN))))) in C2 by (rewrite length_le8; lia).
      pose proof (proj2 (bytes_at_app asegs m (usp + 8) _ _) (conj C1 C2)) as F12.
      destruct F12 as (_ & _ & FB).
      pose proof (stack_argv2 sp AV EV inp mbase rnd _ (IMGK_of_bytes_at sp AV EV inp mbase rnd _ FIT (mcan_img sp AV EV inp mbase rnd FIT64)) ltac:(lia)) as SA.
      rewrite argv_first2 in SA. cbn [u64s] in SA. rewrite app_nil_r in SA. destruct SA as (_ & _ & SB).
      destruct (mcan_img sp AV EV inp mbase rnd FIT64) as (_ & _ & MB).
      assert (L16 : length (le8 (Z_to_bv 64 (str_base TOP AV EV EFN)) ++
                            le8 (Z_to_bv 64 (Z.b2z (1 <? argc AV) * (str_base TOP AV EV EFN + Z.of_nat (length (nth 0 AV [])) + 1)))) = 16%nat)
        by (rewrite length_app, !length_le8; reflexivity).
      specialize (FB (i - 8)%nat ltac:(rewrite L16; lia)).
      specialize (SB (i - 8)%nat ltac:(rewrite L16; lia)).
      specialize (MB i ltac:(lia)).
      replace (usp + 8 + Z.of_nat (i - 8)) with (usp + Z.of_nat i) in FB, SB by lia.
      rewrite FB. rewrite <- MB. rewrite SB. reflexivity.
    - pose proof (HID (usp + Z.of_nat i) ltac:(lia)) as E.
      rewrite wrap_above_sp in E by (rewrite wa_unsigned by lia; lia).
      rewrite stack_to_mem_in in E by (rewrite wa_unsigned by lia; unfold entry_stack_image; lia).
      rewrite wa_unsigned in E by lia. replace (Z.to_nat (usp + Z.of_nat i - usp)) with i in E by lia.
      unfold mrd. rewrite E. unfold entry_stack_image.
      destruct (nth_error IMGB i) as [b|] eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  Qed.
End IMGK_init.

Lemma asan_env_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts -> asan_env asegs m.
Proof.
  intros V m HM. unfold asan_env. split; [| split; [| exact (GlueIcpt.icpt_env_init V m HM)]].
  - unfold asan_globals, A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL, SHADOW_OFF. split; [| split; [| split]].
    + aimg V m HM 0xaad30 [C8 (Z_to_bv 64 0xb4538)] H. exact H.
    + mf V m HM (MCell (ZLit 738616) 8 (ZLit 2147450880)) H. exact H.
    + aimg V m HM 0xaad88 [C8 (Z_to_bv 64 0xb4540)] H. exact H.
    + mf V m HM (MCell (ZLit 738624) 4 (ZLit 1)) H. exact H.
  - unfold dtor_cells. split; [| split; [| exact (GlueDtor.dtor_cells6_init V m HM)]].
    + exists (Z_to_bv 64 1). mf V m HM (MCell (ZLit 724608) 8 (ZLit 1)) H. exact H.
    + exists (Z_to_bv 8 1), (Z_to_bv 8 1), (Z_to_bv 8 1).
      mf V m HM (MCell (ZLit 6188000) 1 (ZLit 1)) H1. mf V m HM (MCell (ZLit 6188001) 1 (ZLit 1)) H2. mf V m HM (MCell (ZLit 6188002) 1 (ZLit 1)) H3.
      exact (rw_cells_app2 m _ _ _ 6188001 H1 eq_refl (rw_cells_app2 m _ _ _ 6188002 H2 eq_refl H3)).
Qed.

Lemma a0_H0_false : forall V sp fs mo (a : word), bmodel V sp fs mo ->
  (bv_unsigned sp - 8388608 <= bv_unsigned a \/ BIMG_LO <= bv_unsigned a < BIMG_HI) -> b0_H0 V mo a = false.
Proof.
  intros V sp fs mo a AM Ha. destruct (b0_H0 V mo a) eqn:E; [|reflexivity]. exfalso.
  unfold b0_H0 in E. apply andb_prop in E as [Hlz _].
  destruct (lazy_page_range mo a Hlz) as (r & Hr & Hin).
  pose proof (proj1 (Forall_forall _ _) (bm_lazy_bounds _ _ _ _ AM) r Hr) as (Hc & Hs). lia.
Qed.

Lemma mem_inv_mrestrict : forall H (m : mem), mem_inv asegs m -> mem_inv asegs (mrestrict H m).
Proof. intros H m MI a b Hab. unfold mrestrict in Hab. destruct (H a); [discriminate|]. exact (MI a b Hab). Qed.

Lemma stk_mrestrict : forall H (m : mem) lo hi, stk asegs m lo hi -> (forall a, lo <= a < hi -> H (wa a) = false) -> stk asegs (mrestrict H m) lo hi.
Proof.
  intros H m lo hi (S0 & S1 & S) HF. split; [exact S0|]. split; [exact S1|]. intros a Ha.
  destruct (S a Ha) as [W R]. unfold wview, mrd, mrestrict in *. rewrite (HF a Ha). split; [exact W| exact R].
Qed.

Lemma bytes_at_mrestrict : forall H (m : mem) A bs, bytes_at asegs m A bs ->
  (forall i, (i < length bs)%nat -> H (wa (A + Z.of_nat i)) = false) -> bytes_at asegs (mrestrict H m) A bs.
Proof.
  intros H m A bs (B0 & B1 & B) HF. split; [exact B0|]. split; [exact B1|]. intros i Hi.
  pose proof (B i Hi) as Bi. unfold mrd, mrestrict in *. rewrite (HF i Hi). exact Bi.
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

