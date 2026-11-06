(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrMem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TU Require Import G3Pure G3Lem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.TUB Require Import DgWalkB DgSpecB G3PureB G3WalkB G3SpecB G3EntryB.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkB.rsegs.

Lemma fabs_pos : forall a : word, feq_d a (Z_to_bv 64 0) = false -> (1 <= bv_unsigned (fabs_d a) < 2 ^ 63)%Z.
Proof.
  intros a H. unfold fabs_d. pose proof (bv_unsigned_in_range _ a) as Ra. unfold bv_modulus in Ra. cbn -[Z.pow] in Ra.
  assert (Hl : Z.land (bv_unsigned a) (Z.ones 63) = (bv_unsigned a mod 2 ^ 63)%Z) by (apply Z.land_ones; lia).
  rewrite Hl. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63)); lia).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63) ltac:(lia)) as Rm. split; [|lia].
  destruct (Z.eq_dec (bv_unsigned a mod 2 ^ 63) 0) as [E|E]; [|lia]. exfalso.
  assert (Ha : bv_unsigned a = 0%Z \/ bv_unsigned a = (2 ^ 63)%Z).
  { pose proof (Z.div_mod (bv_unsigned a) (2 ^ 63) ltac:(lia)) as D. rewrite E in D.
    assert (Q : (0 <= bv_unsigned a / 2 ^ 63 < 2)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). nia. }
  assert (Ea : a = Z_to_bv 64 (bv_unsigned a)) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct Ha as [Ha|Ha]; rewrite Ea, Ha in H; vm_compute in H; discriminate H.
Qed.

Ltac exs := repeat (lazymatch goal with |- ex _ => eexists end).

Ltac shst := zstep; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa ?A) (le1 (Z_to_bv 64 ?v))) _) =>
    replace (le1 (Z_to_bv 64 v)) with [Z_to_bv 8 v] by (symmetry; apply le1_lit); mem_after_store end).

Lemma cb4_c4 : forall m A bs, rw_cells rsegs m A [CB 4 bs] -> exists w, rw_cells rsegs m A [C4 w].
Proof.
  intros m A bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; cbn in Hn; try lia.
  destruct (le4_of_bytes b0 b1 b2 b3) as (w & Hw4). exists w. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite Hw4. exact Hb.
  - exact Hw.
Qed.
Ltac peel H := lazymatch type of H with rw_cells _ ?m ?A (?c :: ?rest) =>
  let H1 := fresh "PC" in
  change (c :: rest) with ([c] ++ rest) in H; apply (proj1 (rw_cells_app m A [c] rest)) in H; destruct H as [H1 H]; cbn [cells_size csize Nat.add] in H end.
Lemma rw_glue : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.

Lemma rw_mrd : forall m A cs (k : nat) b, rw_cells rsegs m A cs -> nth_error (cells_bytes cs) k = Some b -> mrd rsegs m (wa (A + Z.of_nat k)) = Some b.
Proof. intros m A cs k b [[_ (_ & _ & HB)] _] Hn. rewrite HB; [exact Hn|]. apply nth_error_Some. rewrite Hn. discriminate. Qed.

Definition SHZ : list byte := map (Z_to_bv 8) ([-15; -15; -15; -15] ++ repeat (-8) 13 ++ repeat (-13) 7)%Z.
Definition SHG : list byte := map (Z_to_bv 8) ([-15; -15; -15; -15] ++ repeat 0 12 ++ [4] ++ repeat (-13) 7)%Z.

Section DTH.

Variables gp tp s0 s2 s3 s4 s5 s8 s9 s10 s11 : word.
Variables FR GSP : Z.
Local Notation SH := (FR / 8 + 2147450880)%Z.
Hypothesis FRR : (0x6b4000 <= FR /\ FR mod 64 = 0 /\ (FR + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FR) /\ FR + 256 <= GSP - 192)%Z.
Hypothesis GSPR : (0x10007fff8000 <= GSP - 192 /\ GSP + 16 <= 2 ^ 47 /\ GSP mod 32 = 0)%Z.

Definition dt_z0 (ra t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists F' fc' m',
    ms' = MS (mkR ra (Z_to_bv 64 GSP) gp tp t0 t1 t2 s0 (Z_to_bv 64 GSP) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) (Z_to_bv 64 1) a3 (Z_to_bv 64 (-15)) a5 a6 a7
                  s2 s3 s4 s5 (Z_to_bv 64 SH) (Z_to_bv 64 FR) s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0xd25c4) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ rw_cells rsegs m' SH (map C1 SHZ) /\ munch [(SH, SH + 24)%Z] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'.

Lemma dt_head_z0 : forall ra t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte),
  frm0 fc -> rw_cells rsegs m SH [CB 24 (repeat (Z_to_bv 8 0) 24)] -> mem_inv rsegs m ->
  feq_d (reg_get F 8) (Z_to_bv 64 0) = true ->
  evt rsegs (dt_z0 ra t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 GSP) gp tp t0 t1 t2 s0 (Z_to_bv 64 GSP) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 SH) (Z_to_bv 64 FR) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd2558) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros FRM SHC MI FQ.
  pose proof (munch_refl [(SH, SH + 24)%Z] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. do 4 shst.
  zstep. lazymatch goal with |- context [feq_d ?x ?y] => replace (feq_d x y) with true by (symmetry; exact FQ) end. cbn [bword].
  do 20 shst.
  zstep. replace (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false by reflexivity.
  apply evt_done. unfold dt_z0. exs. split; [reflexivity|].
  split; [exact FRM|]. split; [exact SHC|]. split; [exact MU|]. split; [exact WM | exact MI].
Qed.

Local Notation BUF := (FR + 32)%Z.
Definition DT_W : list (Z * Z) := [(SH, SH + 24); (GSP - 192, GSP); (BUF, BUF + 22); (GSP + 8, GSP + 16)]%Z.
Definition dt_g3 (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (res len K : Z) (bs : list byte),
    ms' = MS (mkR (Z_to_bv 64 0xd2644) (Z_to_bv 64 GSP) gp tp t0' t1' t2' s0 (Z_to_bv 64 GSP) (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 (Z_to_bv 64 BUF) (Z_to_bv 64 SH) (Z_to_bv 64 FR) s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0xd2644) fc' None m' (seg_rom rsegs)
    /\ frm0 fc' /\ rw_cells rsegs m' SH (map C1 SHG) /\ rw_cells rsegs m' (GSP + 8) [C4 (Z_to_bv 64 K); C4 (Z_to_bv 64 len)]
    /\ u8arr rsegs m' BUF bs /\ length bs = 22%nat /\ stk rsegs m' (GSP - 192) GSP
    /\ munch DT_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ (1 <= len <= 21)%Z /\ (-343 <= K <= 309)%Z /\ (res = 0 \/ res = 1)%Z.

Lemma dt_head_g3 : forall ra t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (kl bs : list byte),
  frm0 fc -> rw_cells rsegs m SH [CB 24 (repeat (Z_to_bv 8 0) 24)] -> rw_cells rsegs m (GSP + 8) [CB 8 kl] ->
  u8arr rsegs m BUF bs -> length bs = 22%nat -> stk rsegs m (GSP - 192) GSP ->
  ro_cells rsegs m 0x154500 [C8 (Z_to_bv 64 0x15dcf8)] -> ro_cells rsegs m 0x15dcf8 [C8 (Z_to_bv 64 2147450880)] -> mem_inv rsegs m ->
  mrd rsegs m (wa (Z.shiftr (GSP + 8) 3 + 2147450880)) = Some (Z_to_bv 8 0) ->
  (forall i, (0 <= i < 687)%Z -> mrd rsegs m (wa (Z.shiftr (G3PureB.PT_BASE + 8 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0)) ->
  (forall i, (0 <= i < 686)%Z -> mrd rsegs m (wa (Z.shiftr (G3PureB.PE_BASE + 4 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0)) ->
  feq_d (reg_get F 8) (Z_to_bv 64 0) = false ->
  evt rsegs (dt_g3 m)
    (MS (mkR ra (Z_to_bv 64 GSP) gp tp t0 t1 t2 s0 (Z_to_bv 64 GSP) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 SH) (Z_to_bv 64 FR) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd2558) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros FRM SHC KLC BU BL ST GOT SHV MI SHS SHPT SHPE FQ.
  pose proof (munch_refl [(SH, SH + 24); (GSP + 8, GSP + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. do 4 shst.
  zstep. lazymatch goal with |- context [feq_d ?x ?y] => replace (feq_d x y) with false by (symmetry; exact FQ) end. cbn [bword].
  do 20 shst.
  zstep. replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity.
  zstep.
  zstep.
  do 12 shst. zstep. shst.
  zstep. do 3 zstep. zstep.

  lazymatch goal with H : rw_cells _ ?mm (GSP + 8) _ |- _ => rename H into KL2 end.
  peel KL2. destruct (cb4_c4 _ _ _ PC) as (kj & KC). clear PC.
  pose proof (fabs_pos _ FQ) as Hb.
  assert (USP : bv_unsigned (Z_to_bv 64 GSP) = GSP) by (apply unsigned_lit; lia).
  assert (F64 : (FR = 64 * (FR / 64))%Z) by (pose proof (Z.div_mod FR 64 ltac:(lia)); lia).
  assert (F8 : (FR / 8 = 8 * (FR / 64))%Z) by (rewrite F64 at 1; replace (64 * (FR / 64))%Z with ((8 * (FR / 64)) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (DF8 : (FR / 8 * 8 = FR)%Z) by lia.
  assert (G32 : (GSP = 32 * (GSP / 32))%Z) by (pose proof (Z.div_mod GSP 32 ltac:(lia)); lia).
  assert (G8 : (GSP / 8 = 4 * (GSP / 32))%Z) by (rewrite G32 at 1; replace (32 * (GSP / 32))%Z with ((4 * (GSP / 32)) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (DG8 : ((GSP + 8) / 8 = GSP / 8 + 1 /\ (GSP + 12) / 8 = GSP / 8 + 1)%Z)
    by (split; [symmetry; apply (Zdiv_unique _ 8 _ 0) | symmetry; apply (Zdiv_unique _ 8 _ 4)]; lia).
  assert (GB : (GSP / 8 <= 2 ^ 44 /\ 2 ^ 41 <= GSP / 8)%Z) by (split; [apply Z.div_le_upper_bound; lia | apply Z.div_le_lower_bound; lia]).
  assert (FB : (0xd2848 <= FR / 8 /\ FR / 8 + 32 <= GSP / 8)%Z) by lia.

  assert (SHS1 : forall mm, munch [(SH, SH + 24); (GSP + 8, GSP + 16)]%Z m mm -> mrd rsegs mm (wa (Z.shiftr (GSP + 12) 3 + 2147450880)) = Some (Z_to_bv 8 0)).
  { intros mm MUx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. rewrite (proj2 DG8). unfold mrd. rewrite (MUx (wa (GSP / 8 + 1 + 2147450880))).
    - rewrite Z.shiftr_div_pow2 in SHS by lia. change (2 ^ 3)%Z with 8%Z in SHS. rewrite (proj1 DG8) in SHS. exact SHS.
    - cbn [outside]. rewrite wa_unsigned by lia. repeat split; lia. }
  eapply evt_cut.
  { eapply (g3_spec (Z_to_bv 64 0xd2644) (Z_to_bv 64 GSP) gp tp s0 (Z_to_bv 64 GSP) s2 s3 s4 (Z_to_bv 64 BUF) (Z_to_bv 64 SH) (Z_to_bv 64 FR) s8 s9 s10 s11 _ _ BUF (GSP + 12) (GSP + 8)).
    all: unfold G3WalkB.GSP, G3WalkB.app_buf22; rewrite ?USP.
    all: try (clear - FRR GSPR; lia).
    - exact (SHS1 _ MU).
    - replace (Z.shiftr (GSP + 8) 3) with (Z.shiftr (GSP + 12) 3) by (rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; rewrite (proj1 DG8), (proj2 DG8); reflexivity). exact (SHS1 _ MU).
    - intros k Hk. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      replace ((FR + 32 + k) / 8)%Z with (FR / 8 + (4 + k / 8))%Z
        by (pose proof (Z.div_mod k 8 ltac:(lia)); pose proof (Z.mod_pos_bound k 8 ltac:(lia)); apply (Zdiv_unique _ 8 _ (k mod 8)); lia).
      assert (Hk8 : (0 <= k / 8 <= 2)%Z) by (pose proof (Z.div_mod k 8 ltac:(lia)); pose proof (Z.mod_pos_bound k 8 ltac:(lia)); lia).
      replace (FR / 8 + (4 + k / 8) + 2147450880)%Z with (SH + Z.of_nat (Z.to_nat (4 + k / 8)))%Z by lia.
      apply (rw_mrd _ SH _ _ _ SHC). destruct (Z_le_gt_dec (k / 8) 0) as [H0|H0]; [replace (Z.to_nat (4 + k / 8)) with 4%nat by lia; reflexivity|].
      destruct (Z_le_gt_dec (k / 8) 1) as [H1|H1]; [replace (Z.to_nat (4 + k / 8)) with 5%nat by lia; reflexivity|]. replace (Z.to_nat (4 + k / 8)) with 6%nat by lia; reflexivity.
    - intros i Hi. unfold mrd. rewrite (MU (wa (Z.shiftr (G3PureB.PT_BASE + 8 * i) 3 + 2147450880))); [exact (SHPT i Hi)|].
      rewrite Z.shiftr_div_pow2 by (unfold G3PureB.PT_BASE; lia). change (2 ^ 3)%Z with 8%Z. unfold G3PureB.PT_BASE in *.
      assert ((156160 + 8 * i) / 8 <= 20206)%Z by (apply Z.div_le_upper_bound; lia). assert (0 <= (156160 + 8 * i) / 8)%Z by (apply Z.div_pos; lia).
      cbn [outside]. rewrite wa_unsigned by lia. repeat split; lia.
    - intros i Hi. unfold mrd. rewrite (MU (wa (Z.shiftr (G3PureB.PE_BASE + 4 * i) 3 + 2147450880))); [exact (SHPE i Hi)|].
      rewrite Z.shiftr_div_pow2 by (unfold G3PureB.PE_BASE; lia). change (2 ^ 3)%Z with 8%Z. unfold G3PureB.PE_BASE in *.
      assert ((163008 + 4 * i) / 8 <= 20720)%Z by (apply Z.div_le_upper_bound; lia). assert (0 <= (163008 + 4 * i) / 8)%Z by (apply Z.div_pos; lia).
      cbn [outside]. rewrite wa_unsigned by lia. repeat split; lia.
    - reflexivity.
    - rewrite freg_get_same by reflexivity. exact Hb.
    - eassumption.
    - eassumption.
    - eassumption.
    - exact BL.
    - match goal with H : rw_cells _ ?mm ?A [C4 (Z_to_bv 64 0)] |- rw_cells _ ?mm ?B _ => replace B with A by (cbn; lia); exact H end.
    - exact KC.
    - eassumption.
    - eassumption.
    - eassumption.
    - reflexivity. }
  cbv beta. intros ms' P. unfold g3_post, G3_W, G3WalkB.GSP in P. rewrite USP in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & res & len & K & bs2 & -> & MUc & WMc & MI2 & FRM2 & ST2 & BU2 & BL2 & _ & LE2 & Hlen & KC2 & HK & Hres).
  replace (ret_pc (Z_to_bv 64 861764)) with (Z_to_bv 64 0xd2644) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SHC2 : rw_cells rsegs m2 SH (map C1 SHG)).
  { apply (rw_cells_transport rsegs _ m1 m2 SH _ SHC MUc WMc). cbn [disjoint_from cells_size csize map Nat.add]. cbn. repeat split; lia. }
  apply evt_done. unfold dt_g3. exs. split; [reflexivity|].
  split; [exact FRM2|]. split; [exact SHC2|].
  split; [apply (rw_glue m2 (GSP + 8) (GSP + 12) [C4 (Z_to_bv 64 K)] [C4 (Z_to_bv 64 len)] KC2 LE2); cbn; lia|].
  split; [exact BU2|]. split; [exact BL2|]. split; [exact ST2|].
  split.
  { apply (munch_trans DT_W m m1 m2).
    - refine (munch_weaken _ DT_W m m1 _ MU). intros x Hx. unfold DT_W in Hx. cbn [outside] in *. tauto.
    - refine (munch_weaken _ DT_W m1 m2 _ MUc). intros x Hx. unfold DT_W in Hx. cbn [outside] in *. lia. }
  split; [exact (wmono_trans rsegs m m1 m2 WM WMc)|]. split; [exact MI2|]. split; [exact Hlen|]. split; [exact HK | exact Hres].
Qed.
End DTH.
