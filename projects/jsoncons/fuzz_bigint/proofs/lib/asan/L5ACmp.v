(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun As0_code_91368_92368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5Cmp L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5ACmpP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ACMP.
Import L5A. Import L5CA. Import L5SA. Import L5ACMPP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Definition CMP : Z := 0x915c4.
Definition LHEAD : Z := 0x916d8.
Definition RET : Z := 0x91738.
Definition MAXW : Z := L5CMP.MAXW.
(* [comment removed for export] *)
Definition cmp_kept : list nat := [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition cmp_objA (M : word -> option byte) (sp o : Z) (b : L5.bigobj) : Prop :=
  L5.big_at RSEGS M o b /\ Z.testbit (L5.bo_fb b) 1 = false /\ (1 <= L5.bo_len b)%nat /\ Z.of_nat (L5.bo_len b) <= 300 /\
  o mod 8 = 0 /\ 4096 <= o <= 140737488355296 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\
  (sp - 16 + 16 <= o \/ o + 32 <= sp - 16) /\ L5KA.zeros_at M (o / 8 + SB) 4 /\
  (4096 <= L5.bo_data o b /\ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 140737488355328) /\ L5.bo_data o b mod 8 = 0 /\
  (2147446784 + 17592186048512 <= L5.bo_data o b \/ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 2147446784) /\
  (sp <= L5.bo_data o b \/ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= sp - 16) /\
  L5KA.zeros_at M (L5.bo_data o b / 8 + SB) (Z.of_nat (L5.bo_len b)).

Definition cmp_postA (M M' : word -> option byte) (R R' : bvmap 5 word) (sp : Z) (nx ny : nat) (wx wy : list Z) : Prop :=
  (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R'
  /\ (exists c, getr R' (reg 10) = Z_to_bv 64 c /\ L5CMP.res_sized c nx ny /\ (nx = ny -> c = L5CMP.cmp_val wx wy))
  /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma fz segs (p : word) (z : Z) w : fetch_word segs p = Some w -> p = Z_to_bv 64 z -> fetch_word segs (Z_to_bv 64 z) = Some w.
Proof. intros H E. rewrite <- E. exact H. Qed.
Lemma rl (k : nat) (b : bv 5) : bv_unsigned b = Z.of_nat k -> (k < 32)%nat -> b = reg k.
Proof. intros H Hk. apply bv_eq. rewrite H. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
Lemma br_any fx R M (pc : Z) w c rs1 rs2 (imm : bv 13) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  msteps RSEGS (st fx R pc M)
               (@mkst fx R (if branch_taken c (getr R rs1) (getr R rs2) then btgt (Z_to_bv 64 pc) (bv_signed imm) else v_addi (Z_to_bv 64 pc) 4) M (seg_rom RSEGS)).
Proof.
  intros Hf He Hd. destruct (branch_taken c (getr R rs1) (getr R rs2)) eqn:Hb.
  - eapply mst_step; [reflexivity | exact (step_branch_tk_gen RSEGS R _ M (seg_rom RSEGS) w c rs1 rs2 imm Hf He Hd Hb) | apply mst_refl].
  - eapply mst_step; [reflexivity | exact (step_branch_ft_gen RSEGS R _ M (seg_rom RSEGS) w c rs1 rs2 imm Hf He Hd Hb) | apply mst_refl].
Qed.
Lemma br_site fx R M (pc tk : Z) (wpc : word) w c (rs1 rs2 : bv 5) (imm : bv 13) :
  wpc = Z_to_bv 64 pc -> fetch_word RSEGS wpc = Some w -> is_ecall w = false -> decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  btgt wpc (bv_signed imm) = Z_to_bv 64 tk -> v_addi wpc 4 = Z_to_bv 64 (pc + 4) ->
  msteps RSEGS (st fx R pc M) (st fx R (if branch_taken c (getr R rs1) (getr R rs2) then tk else pc + 4) M).
Proof.
  intros Hpc HF HE HD Htk Hft. pose proof (br_any fx R M pc w c rs1 rs2 imm (fz _ _ pc _ HF Hpc) HE HD) as ST.
  subst wpc. destruct (branch_taken c (getr R rs1) (getr R rs2)); [rewrite Htk in ST | rewrite Hft in ST]; exact ST.
Qed.
Local Ltac bveq := apply bv_eq; vm_compute; reflexivity.
Lemma r0 : (0%bv : bv 5) = reg 0. Proof. bveq. Qed.
Lemma r5 : (5%bv : bv 5) = reg 5. Proof. bveq. Qed.
Lemma r6 : (6%bv : bv 5) = reg 6. Proof. bveq. Qed.
Lemma r10' : (10%bv : bv 5) = reg 10. Proof. bveq. Qed.
Lemma r11' : (11%bv : bv 5) = reg 11. Proof. bveq. Qed.
Lemma r15 : (15%bv : bv 5) = reg 15. Proof. bveq. Qed.
Lemma br_91330 fx R M : msteps RSEGS (st fx R 0x91684 M) (st fx R (if branch_taken BC_EQ (getr R (reg 10)) (getr R (reg 0)) then 0x91730 else 0x91688) M).
Proof. rewrite <- r10', <- r0. apply (br_site fx R M 0x91684 0x91730 (0x91684%bv : word) _ BC_EQ 10 0 _ ltac:(bveq) F_91684 eq_refl D_91684); bveq. Qed.
Lemma br_91358 fx R M : msteps RSEGS (st fx R 0x916ac M) (st fx R (if branch_taken BC_LTU (getr R (reg 15)) (getr R (reg 11)) then 0x91728 else 0x916b0) M).
Proof. rewrite <- r15, <- r11'. apply (br_site fx R M 0x916ac 0x91728 (0x916ac%bv : word) _ BC_LTU 15 11 _ ltac:(bveq) F_916ac eq_refl D_916ac); bveq. Qed.
Lemma br_9135c fx R M : msteps RSEGS (st fx R 0x916b0 M) (st fx R (if branch_taken BC_GEU (getr R (reg 11)) (getr R (reg 15)) then 0x916bc else 0x916b4) M).
Proof. rewrite <- r15, <- r11'. apply (br_site fx R M 0x916b0 0x916bc (0x916b0%bv : word) _ BC_GEU 11 15 _ ltac:(bveq) F_916b0 eq_refl D_916b0); bveq. Qed.
Lemma br_913b4 fx R M : msteps RSEGS (st fx R 0x91708 M) (st fx R (if branch_taken BC_LTU (getr R (reg 6)) (getr R (reg 5)) then 0x916b4 else 0x9170c) M).
Proof. rewrite <- r5, <- r6. apply (br_site fx R M 0x91708 0x916b4 (0x91708%bv : word) _ BC_LTU 6 5 _ ltac:(bveq) F_91708 eq_refl D_91708); bveq. Qed.
Lemma br_913c8 fx R M : msteps RSEGS (st fx R 0x9171c M) (st fx R (if branch_taken BC_GEU (getr R (reg 5)) (getr R (reg 6)) then 0x916d8 else 0x91720) M).
Proof. rewrite <- r5, <- r6. apply (br_site fx R M 0x9171c 0x916d8 (0x9171c%bv : word) _ BC_GEU 5 6 _ ltac:(bveq) F_9171c eq_refl D_9171c); bveq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record lfacts (M : word -> option byte) (sp xd yd : Z) (n : nat) : Prop := LF {
  lf_sp : 140735332487184 <= sp <= 140737488355328 /\ sp mod 16 = 0;
  lf_w16 : L5.writable RSEGS M (sp - 16) 16;
  lf_st : L5.img_clear M 860160 880640 /\ L5.u64_at RSEGS M 908088 2147450880 /\ L5.u32_at RSEGS M 908096 1;
  lf_x : 4096 <= xd <= 140737488355328 /\ xd mod 8 = 0 /\ (2147446784 + 17592186048512 <= xd \/ xd + 8 * Z.of_nat n <= 2147446784);
  lf_xz : L5KA.zeros_at M (xd / 8 + SB) (Z.of_nat n);
  lf_y : 4096 <= yd <= 140737488355328 /\ yd mod 8 = 0 /\ (2147446784 + 17592186048512 <= yd \/ yd + 8 * Z.of_nat n <= 2147446784);
  lf_yz : L5KA.zeros_at M (yd / 8 + SB) (Z.of_nat n) }.

(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (sp xd yd : Z) (k : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R (reg 11) = Z_to_bv 64 (xd + 8 * Z.of_nat k - 8) /\ getr R (reg 12) = Z_to_bv 64 (yd + 8 * Z.of_nat k - 8) /\
  getr R (reg 13) = Z_to_bv 64 SB /\ getr R (reg 14) = Z_to_bv 64 0 /\ getr R (reg 15) = Z_to_bv 64 (Z.of_nat k + 1) /\
  getr R (reg 16) = Z_to_bv 64 (yd + 8 * Z.of_nat k - 8) /\ getr R (reg 17) = Z_to_bv 64 (xd + 8 * Z.of_nat k - 8).
(* [comment removed for export] *)
Definition KL : list nat := [1; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Local Ltac kl KS := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; revert Hx; apply (L5K.incl_b _ KS); vm_compute; reflexivity.

Lemma wloop (k : nat) : forall fx R M (sp xd yd : Z) (n : nat) (wx wy : list Z),
  at_head R sp xd yd k -> getr R (reg 10) = Z_to_bv 64 MAXW -> (k <= n)%nat -> (1 <= n)%nat -> Z.of_nat n <= 300 ->
  lfacts M sp xd yd n -> L5.u64_at RSEGS M (sp - 8) (U R 1) ->
  L5.limbs_at RSEGS M xd wx -> L5.limbs_at RSEGS M yd wy -> length wx = n -> length wy = n -> L5W.words_ok wx -> L5W.words_ok wy ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall x, In x KL -> getr R' (reg x) = getr R (reg x)) /\ getr R' (reg 2) = Z_to_bv 64 sp
    /\ getr R' (reg 10) = Z_to_bv 64 (L5CMP.enc (BigModel.compare_loop k wx wy))
    /\ (forall a, M' a = M a).
Proof.
  induction k as [|k IH]; intros fx R M sp xd yd n wx wy AT A10 Hkn Hn1 Hn2 LFM C8 Lx Ly Nx Ny Wx Wy.
  all: pose proof LFM as [[SPR A16] W16 [IMGC [CSB CUAR]] (XR & X8 & XBIG) XZ (YR & Y8 & YBIG) YZ].
  all: destruct AT as (A2 & A11 & A12 & A13 & A14 & A15 & A16r & A17).
  all: assert (ALS : aligned sp 16) by exact A16.
  - (* [comment removed for export] *)
    pose proof (vcmZ_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR2 & zR10 & zR15)).
    exists fx1, R1, M1. split. exact zMS. split. { intros x Hx. apply zKS. revert x Hx. kl KS_vcmZ. }
    split. exact zR2. split. exact zR10. exact zFR.
  - set (xk := L5W.nth_w wx k). set (yk := L5W.nth_w wy k).
    assert (Rxk : 0 <= xk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wx). assert (Ryk : 0 <= yk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wy).
    assert (Ux : L5.u64_at RSEGS M (xd + 8 * Z.of_nat (Datatypes.S k) - 8) xk). { replace (xd + 8 * Z.of_nat (Datatypes.S k) - 8) with (xd + 8 * Z.of_nat k) by (clear; lia). apply Lx. clear - Hkn Nx; lia. }
    assert (Uy : L5.u64_at RSEGS M (yd + 8 * Z.of_nat (Datatypes.S k) - 8) yk). { replace (yd + 8 * Z.of_nat (Datatypes.S k) - 8) with (yd + 8 * Z.of_nat k) by (clear; lia). apply Ly. clear - Hkn Ny; lia. }
    assert (ALX : aligned xd 8) by exact X8. assert (ALY : aligned yd 8) by exact Y8.
    assert (HVN : 1 <= Z.of_nat n <= 300) by (clear - Hn1 Hn2; lia). assert (HVK : 1 <= Z.of_nat (Datatypes.S k) <= 300) by (clear - Hkn Hn2; lia).
    assert (HVNK : 0 <= Z.of_nat n - Z.of_nat (Datatypes.S k) <= 299) by (clear - Hkn Hn2; lia).
    assert (HX1 : 0 <= xk <= 18446744073709551615) by (clear - Rxk; lia). assert (HY1 : 0 <= yk <= 18446744073709551615) by (clear - Ryk; lia).
    pose proof (vcmI_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => Z.of_nat n | 37%nat => xd | 38%nat => yd | 41%nat => Z.of_nat (Datatypes.S k) | 42%nat => xk | 43%nat => yk | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR5 & iR6 & iR15)).
    assert (K1 : forall j, In j (2 :: 10 :: 11 :: 12 :: 13 :: 14 :: 16 :: 17 :: KL)%nat -> getr R1 (reg j) = getr R (reg j)). { intros j Hj. apply iKS. revert j Hj. kl KS_vcmI. }
    assert (EM1 : M1 = M). { apply functional_extensionality. exact iFR. } subst M1.
    assert (C81 : L5.u64_at RSEGS M (sp - 8) (U R1 1)). { unfold U. rewrite (K1 1%nat) by inl. exact C8. }
    pose proof (br_913b4 fx1 R1 M) as MB1. rewrite iR5, iR6 in MB1.
    cbn [BigModel.compare_loop]. change (BigModel.nth_w wx k) with xk. change (BigModel.nth_w wy k) with yk.
    destruct (branch_taken BC_LTU (Z_to_bv 64 yk) (Z_to_bv 64 xk)) eqn:LT1.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = true). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by (clear - Rxk Ryk; lia). exact LT1. }
      rewrite LT1'.
      pose proof (vcmP_conc fx1 R1 M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
      destruct P as (fx2 & R2 & M2 & MG2 & pFR & pFZ & (pMS & pKS & pR2 & pR10)).
      exists fx2, R2, M2. split. { eapply msteps_trans. exact iMS. eapply msteps_trans. exact MB1. exact pMS. }
      split. { intros x Hx. rewrite (pKS x). apply K1. right. right. right. right. right. right. right. right. exact Hx. revert x Hx. kl KS_vcmP. }
      split. exact pR2. split. exact pR10. exact pFR.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = false). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by (clear - Rxk Ryk; lia). exact LT1. }
      rewrite LT1'.
      pose proof (vcmJ_conc fx1 R1 M (fun j => match j with 2%nat => sp | 37%nat => xd | 38%nat => yd | 41%nat => Z.of_nat (Datatypes.S k) | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
      destruct P as (fx2 & R2 & M2 & MG2 & jFR & jFZ & (jMS & jKS & jR11 & jR12 & jR16 & jR17)).
      assert (K2 : forall j, In j (2 :: 5 :: 6 :: 10 :: 13 :: 14 :: 15 :: KL)%nat -> getr R2 (reg j) = getr R1 (reg j)). { intros j Hj. apply jKS. revert j Hj. kl KS_vcmJ. }
      assert (EM2 : M2 = M). { apply functional_extensionality. exact jFR. } subst M2.
      pose proof (br_913c8 fx2 R2 M) as MB2. rewrite (K2 5%nat), (K2 6%nat), iR5, iR6 in MB2 by inl.
      destruct (branch_taken BC_GEU (Z_to_bv 64 xk) (Z_to_bv 64 yk)) eqn:GE2.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = false).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_true_iff in GE2. rewrite !BG.unsigned_lit in GE2 by (clear - Rxk Ryk; lia). exact GE2. }
        rewrite GE2'.
        assert (AT2: at_head R2 sp xd yd k).
        { unfold at_head. repeat split.
          - rewrite (K2 2%nat), (K1 2%nat) by inl. exact A2.
          - rewrite jR11. f_equal. clear; lia.
          - rewrite jR12. f_equal. clear; lia.
          - rewrite (K2 13%nat), (K1 13%nat) by inl. exact A13.
          - rewrite (K2 14%nat), (K1 14%nat) by inl. exact A14.
          - rewrite (K2 15%nat) by inl. rewrite iR15. f_equal. clear; lia.
          - rewrite jR16. f_equal. clear; lia.
          - rewrite jR17. f_equal. clear; lia. }
        assert (A10': getr R2 (reg 10) = Z_to_bv 64 MAXW). { rewrite (K2 10%nat), (K1 10%nat) by inl. exact A10. }
        assert (C82 : L5.u64_at RSEGS M (sp - 8) (U R2 1)). { unfold U. rewrite (K2 1%nat) by inl. exact C81. }
        destruct (IH fx2 R2 M sp xd yd n wx wy AT2 A10' ltac:(clear - Hkn; lia) Hn1 Hn2 LFM C82 Lx Ly Nx Ny Wx Wy) as (fx3 & R3 & M3 & MS3 & K3 & R32 & RES & MM3).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact iMS. eapply msteps_trans. exact MB1. eapply msteps_trans. exact jMS. eapply msteps_trans. exact MB2. exact MS3. }
        split. { intros x Hx. rewrite (K3 x Hx). rewrite (K2 x). apply K1. do 8 right. exact Hx. do 7 right. exact Hx. }
        split. exact R32. split. exact RES. exact MM3.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = true).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_false_iff in GE2. rewrite !BG.unsigned_lit in GE2 by (clear - Rxk Ryk; lia). exact GE2. }
        rewrite GE2'.
        assert (C82 : L5.u64_at RSEGS M (sp - 8) (U R2 1)). { unfold U. rewrite (K2 1%nat) by inl. exact C81. }
        pose proof (vcmN2_conc fx2 R2 M (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K2 _) by inl; rewrite (K1 _) by inl; sc)]).
        destruct P as (fx3 & R3 & M3 & MG3 & nFR & nFZ & (nMS & nKS & nR2)).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact iMS. eapply msteps_trans. exact MB1. eapply msteps_trans. exact jMS. eapply msteps_trans. exact MB2. exact nMS. }
        split. { intros x Hx. rewrite (nKS x). rewrite (K2 x). apply K1. do 8 right. exact Hx. do 7 right. exact Hx. revert x Hx. kl KS_vcmN2. }
        split. exact nR2.
        split. { rewrite (nKS 10%nat) by inl. rewrite (K2 10%nat), (K1 10%nat) by inl. exact A10. }
        exact nFR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KA : list nat := [1; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma cmA_run fx R M (sp xo yo : Z) (bx by_ : L5.bigobj) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo ->
  140735332487184 <= sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M (sp - 16) 16 ->
  L5.img_clear M 860160 880640 -> L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 ->
  cmp_objA M sp xo bx -> cmp_objA M sp yo by_ ->
  exists fx' R' M', msteps RSEGS (st fx R CMP M) (st fx' R' 0x91684 M')
    /\ (forall x, In x KA -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 2) = Z_to_bv 64 (sp - 16)
    /\ bv_unsigned (getr R' (reg 10)) = Z.lor (Z.of_nat (L5.bo_len by_)) (Z.of_nat (L5.bo_len bx))
    /\ getr R' (reg 11) = Z_to_bv 64 (Z.of_nat (L5.bo_len by_)) /\ getr R' (reg 12) = Z_to_bv 64 (L5.bo_data xo bx)
    /\ getr R' (reg 13) = Z_to_bv 64 SB /\ getr R' (reg 14) = Z_to_bv 64 (L5.bo_fb bx)
    /\ getr R' (reg 15) = Z_to_bv 64 (Z.of_nat (L5.bo_len bx)) /\ getr R' (reg 16) = Z_to_bv 64 (L5.bo_data yo by_)
    /\ getr R' (reg 17) = Z_to_bv 64 (L5.bo_fb by_)
    /\ L5.u64_at RSEGS M' (sp - 8) (U R 1)
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 SPR A16 W16 IMGC CSB CUAR OX OY. unfold CMP.
  destruct OX as (BX & SGX & LX1 & LX2 & X8 & XR & XBIG & XFR & XZ & XDR & XD8 & XDBIG & XDFR & XDZ).
  destruct OY as (BY & SGY & LY1 & LY2 & Y8 & YR & YBIG & YFR & YZ & YDR & YD8 & YDBIG & YDFR & YDZ).
  assert (ALS : aligned sp 16) by exact A16. assert (ALX : aligned xo 8) by exact X8. assert (ALY : aligned yo 8) by exact Y8.
  assert (HNX : 1 <= Z.of_nat (L5.bo_len bx) <= 300) by (clear - LX1 LX2; lia). assert (HNY : 1 <= Z.of_nat (L5.bo_len by_) <= 300) by (clear - LY1 LY2; lia).
  destruct BX as (XFB & XFBR & XLEN & XST). destruct BY as (YFB & YFBR & YLEN & YST).
  assert (XFBR' : 0 <= L5.bo_fb bx <= 255) by (clear - XFBR; lia). assert (YFBR' : 0 <= L5.bo_fb by_ <= 255) by (clear - YFBR; lia).
  destruct bx as [fbx nx [xv0 xv1|xcap xq]]; destruct by_ as [fby ny [yv0 yv1|ycap yq]]; cbn [L5.bo_st L5.bo_len L5.bo_fb L5.bo_data] in *.
  - destruct XST as (XB0 & _). destruct YST as (YB0 & _).
    pose proof (vcmAii_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAii. }
    repeat (split; [first [assumption | exact C8] |]). split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
  - destruct XST as (XB0 & _). destruct YST as (YB0 & _ & YQ & _).
    pose proof (vcmAid_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 38%nat => yq | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. assert (HVQ : 0 <= yq < 2 ^ 64) by (clear - YDR; lia). feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAid. }
    repeat (split; [first [assumption | exact C8] |]). split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
  - destruct XST as (XB0 & _ & XQ & _). destruct YST as (YB0 & _).
    pose proof (vcmAdi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 37%nat => xq | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. assert (HVQ : 0 <= xq < 2 ^ 64) by (clear - XDR; lia). feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAdi. }
    repeat (split; [first [assumption | exact C8] |]). split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
  - destruct XST as (XB0 & _ & XQ & _). destruct YST as (YB0 & _ & YQ & _).
    pose proof (vcmAdd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 37%nat => xq | 38%nat => yq | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. assert (HVQ : 0 <= xq < 2 ^ 64) by (clear - XDR; lia). assert (HVQ' : 0 <= yq < 2 ^ 64) by (clear - YDR; lia). feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAdd. }
    repeat (split; [first [assumption | exact C8] |]). split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kept_regs_preserved R R' : (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof. intros K. apply preserved_by_index. intros k Hk. apply K. revert k Hk. kl cmp_kept. Qed.
Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma lor_nz a b : 0 <= a -> 1 <= b -> Z.lor a b <> 0.
Proof. intros Ha Hb E. apply Z.lor_eq_0_iff in E. lia. Qed.
(* [comment removed for export] *)
Lemma limbs_off_frame M M' sp d ws : (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  4096 <= d -> d + 8 * Z.of_nat (length ws) <= 140737488355328 -> (sp <= d \/ d + 8 * Z.of_nat (length ws) <= sp - 16) ->
  L5.limbs_at RSEGS M d ws -> L5.limbs_at RSEGS M' d ws.
Proof.
  intros AG Dlo Dhi DFR LA i Hi. eapply L5C.u64_at_agree. 4: exact (LA i Hi). 2: clear - Dlo; lia. 2: clear - Dhi Hi; lia.
  intros j Hj. apply AG. clear - Hj Dlo Dhi Hi; lia. clear - Hj Hi DFR; lia.
Qed.

(* [comment removed for export] *)
Lemma obj_limbs_data M o b ws : L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
  L5.limbs_at RSEGS M (L5.bo_data o b) ws /\ length ws = L5.bo_len b /\ L5W.words_ok ws.
Proof.
  intros B (Ln & F & S). split; [|split; [exact Ln|exact F]]. unfold L5.big_at in B.
  destruct b as [fb n [v0 v1|cap q]]; cbn [L5.bo_st L5.bo_len L5.bo_data L5.bo_fb] in *.
  - destruct B as (_ & _ & _ & _ & U16 & U24 & Hn & _). subst ws.
    destruct n as [|[|[|n]]]; [apply (L5C.limbs_at_nil RSEGS)| | |exfalso; lia]; cbn [firstn]; intros i Hi; cbn [length] in Hi.
    + destruct i; [|exfalso; lia]. cbn [nth]. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. exact U16.
    + destruct i as [|[|i]]; [| |exfalso; lia]; cbn [nth].
      replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) by lia. exact U16.
      replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact U24.
  - exact S.
Qed.

Theorem cmp_runA (fx : FPState) R M (xo yo sp r : Z) (bx by_ : L5.bigobj) (wx wy : list Z) :
  getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R (reg 2) = Z_to_bv 64 sp -> 140735332487184 <= sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M (sp - 16) 16 ->
  L5.img_clear M 860160 880640 -> L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 ->
  cmp_objA M sp xo bx -> cmp_objA M sp yo by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M')
    /\ cmp_postA M M' R R' sp (L5.bo_len bx) (L5.bo_len by_) wx wy.
Proof.
  intros H10 H11 H1 RA H2 SPR A16 W16 IMGC CSB CUAR OX OY LMX LMY.
  destruct (cmA_run fx R M sp xo yo bx by_ H2 H10 H11 SPR A16 W16 IMGC CSB CUAR OX OY)
    as (fx1 & R1 & M1 & MS1 & K1 & A2 & A10 & A11 & A12 & A13 & A14 & A15 & A16' & A17 & C8 & FR1 & MG1).
  destruct OX as (BX & SGX & LX1 & LX2 & X8 & XR & XBIG & XFR & XZ & XDR & XD8 & XDBIG & XDFR & XDZ).
  destruct OY as (BY & SGY & LY1 & LY2 & Y8 & YR & YBIG & YFR & YZ & YDR & YD8 & YDBIG & YDFR & YDZ).
  destruct (obj_limbs_data M xo bx wx BX LMX) as (LAX & NX & WX). destruct (obj_limbs_data M yo by_ wy BY LMY) as (LAY & NY & WY).
  set (nx := L5.bo_len bx) in *. set (ny := L5.bo_len by_) in *. set (xd := L5.bo_data xo bx) in *. set (yd := L5.bo_data yo by_) in *.
  assert (XFBR : 0 <= L5.bo_fb bx <= 255) by (destruct BX as (_ & F & _); clear - F; lia).
  assert (YFBR : 0 <= L5.bo_fb by_ <= 255) by (destruct BY as (_ & F & _); clear - F; lia).
  assert (Hr : 0 <= r < 2 ^ 64) by (destruct RA; lia).
  assert (U1 : U R 1 = r). { unfold U. rewrite H1. apply L5.unsigned_lit. exact Hr. }
  (* [comment removed for export] *)
  pose proof (br_91330 fx1 R1 M1) as MB0.
  assert (NT0 : branch_taken BC_EQ (getr R1 (reg 10)) (getr R1 (reg 0)) = false).
  { unfold branch_taken. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite A10 in E.
    change (bv_unsigned (getr R1 (reg 0))) with 0 in E. revert E. apply lor_nz; clear - LX1; lia. }
  rewrite NT0 in MB0.
  (* [comment removed for export] *)
  pose proof (vcmB_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 39%nat => L5.bo_fb bx | 40%nat => L5.bo_fb by_ | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx2 & R2 & M2 & MG2 & bFR & bFZ & (bMS & bKS & bR10 & bR14 & bR17)).
  assert (EM2 : M2 = M1). { apply functional_extensionality. exact bFR. } subst M2.
  assert (K2 : forall j, In j (2 :: 11 :: 12 :: 13 :: 15 :: 16 :: KL)%nat -> getr R2 (reg j) = getr R1 (reg j)). { intros j Hj. apply bKS. revert j Hj. kl KS_vcmB. }
  assert (KL1 : forall j, In j KL -> getr R1 (reg j) = getr R (reg j)). { intros j Hj. apply K1. revert j Hj. kl KA. }
  assert (C82 : L5.u64_at RSEGS M1 (sp - 8) (U R2 1)). { unfold U. rewrite (K2 1%nat), (K1 1%nat) by inl. exact C8. }
  assert (W161 : L5.writable RSEGS M1 (sp - 16) 16) by exact (L5.writable_grows RSEGS M M1 _ _ MG1 W16).
  assert (ALS : aligned sp 16) by exact A16.
  (* [comment removed for export] *)
  assert (FIN : forall fx3 R3 M3 c, msteps RSEGS (st fx2 R2 0x916ac M1) (st fx3 R3 RET M3) ->
            (forall x, In x KL -> getr R3 (reg x) = getr R2 (reg x)) -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 10) = Z_to_bv 64 c ->
            (forall a, M3 a = M1 a) -> L5CMP.res_sized c nx ny -> (nx = ny -> c = L5CMP.cmp_val wx wy) ->
            exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M') /\ cmp_postA M M' R R' sp nx ny wx wy).
  { intros fx3 R3 M3 c MS3 K3 R32 R310 MM3 RS CV.
    assert (EM3 : M3 = M1). { apply functional_extensionality. exact MM3. } subst M3.
    assert (R31 : getr R3 (reg 1) = Z_to_bv 64 r). { rewrite (K3 1%nat), (K2 1%nat), (K1 1%nat) by inl. exact H1. }
    pose proof (ret_to fx3 R3 M1 0x91738 W_91738 r (fz _ _ 0x91738 _ F_91738 ltac:(apply bv_eq; reflexivity)) eq_refl D_91738 R31 (proj1 RA) (proj2 RA)) as RET'.
    exists fx3, R3, M1. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB0. eapply msteps_trans. exact bMS. eapply msteps_trans. exact MS3. exact RET'. }
    assert (KK : forall i, In i cmp_kept -> getr R3 (reg i) = getr R (reg i)).
    { intros i Hi. destruct (Nat.eq_dec i 2) as [->|NE]. rewrite R32. symmetry. exact H2.
      assert (Hi' : In i KL). { cbn in Hi. cbn. clear - Hi NE. repeat (destruct Hi as [<-|Hi]; [first [exfalso; apply NE; reflexivity | tauto] |]). destruct Hi. }
      rewrite (K3 i Hi'). rewrite (K2 i) by (do 6 right; exact Hi'). apply KL1. exact Hi'. }
    split. exact KK. split. apply kept_regs_preserved. exact KK. split. { exists c. split. exact R310. split. exact RS. exact CV. }
    split. exact FR1. exact MG1. }
  pose proof (br_91358 fx2 R2 M1) as MB1. rewrite (K2 15%nat), (K2 11%nat), A15, A11 in MB1 by inl.
  destruct (branch_taken BC_LTU (Z_to_bv 64 (Z.of_nat nx)) (Z_to_bv 64 (Z.of_nat ny))) eqn:LT1.
  - (* [comment removed for export] *)
    assert (LT1' : (nx < ny)%nat). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by (clear - LX2 LY2; lia). apply Z.ltb_lt in LT1. lia. }
    pose proof (vcmN_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K2 _) by inl; sc)]).
    destruct P as (fx3 & R3 & M3 & MG3 & nFR & nFZ & (nMS & nKS & nR2)).
    apply (FIN fx3 R3 M3 MAXW). { eapply msteps_trans. exact MB1. exact nMS. } { intros x Hx. apply nKS. revert x Hx. kl KS_vcmN. } exact nR2.
    { rewrite (nKS 10%nat) by inl. exact bR10. } exact nFR.
    { split. right; right; reflexivity. split. reflexivity. intros. exfalso. clear - LT1' H. lia. } { intros E. exfalso. clear - LT1' E. lia. }
  - assert (GE1 : (ny <= nx)%nat). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by (clear - LX2 LY2; lia). apply Z.ltb_ge in LT1. lia. }
    pose proof (br_9135c fx2 R2 M1) as MB2. rewrite (K2 15%nat), (K2 11%nat), A15, A11 in MB2 by inl.
    destruct (branch_taken BC_GEU (Z_to_bv 64 (Z.of_nat ny)) (Z_to_bv 64 (Z.of_nat nx))) eqn:GE2.
    + (* [comment removed for export] *)
      assert (EQN : nx = ny). { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_true_iff in GE2. rewrite !BG.unsigned_lit in GE2 by (clear - LX2 LY2; lia). apply Z.ltb_ge in GE2. lia. }
      pose proof (vcmE_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | 35%nat => Z.of_nat nx | 37%nat => xd | 38%nat => yd | _ => 0 end)) as P. cbn beta iota in P.
      assert (HNX : 1 <= Z.of_nat nx <= 300) by (clear - LX1 LX2; lia).
      assert (E11 : getr R2 (reg 11) = Z_to_bv 64 (Z.of_nat nx)). { rewrite (K2 11%nat) by inl. rewrite A11. rewrite EQN. reflexivity. }
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K2 _) by inl; sc)]).
      destruct P as (fx3 & R3 & M3 & MG3 & eFR & eFZ & (eMS & eKS & eR11 & eR12 & eR15 & eR16 & eR17)).
      assert (EM3 : M3 = M1). { apply functional_extensionality. exact eFR. } subst M3.
      assert (K3 : forall j, In j (2 :: 10 :: 13 :: 14 :: KL)%nat -> getr R3 (reg j) = getr R2 (reg j)). { intros j Hj. apply eKS. revert j Hj. kl KS_vcmE. }
      assert (AT : at_head R3 sp xd yd nx).
      { unfold at_head. repeat split.
        - rewrite (K3 2%nat), (K2 2%nat) by inl. exact A2.
        - rewrite eR11. f_equal. clear; lia.
        - rewrite eR12. f_equal. clear; lia.
        - rewrite (K3 13%nat), (K2 13%nat) by inl. exact A13.
        - rewrite (K3 14%nat) by inl. exact bR14.
        - rewrite eR15. reflexivity.
        - rewrite eR16. f_equal. clear; lia.
        - rewrite eR17. f_equal. clear; lia. }
      assert (LF1 : lfacts M1 sp xd yd nx).
      { constructor.
        - split; assumption.
        - exact W161.
        - split. { intros a Ha. rewrite FR1. apply IMGC. exact Ha. clear - Ha; lia. clear - Ha SPR; lia. }
          split. eapply L5C.u64_at_agree. 4: exact CSB. 2: clear; lia. 2: clear; lia. intros j Hj. apply FR1. clear - Hj; lia. clear - Hj SPR; lia.
          eapply u32_at_agree1. 4: exact CUAR. intros j Hj. apply FR1. clear - Hj; lia. clear - Hj SPR; lia. clear; lia. clear; lia.
        - split. clear - XDR; lia. split. exact XD8. exact XDBIG.
        - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          eapply L5KA.zeros_at_agree1. 2: exact XDZ. intros i Hi. apply FR1. clear - Hi XDR LX2; unfold SB in *; lia. clear - Hi XDR LX2 SPR; unfold SB in *; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        - split. clear - YDR; lia. split. exact YD8. rewrite EQN. exact YDBIG.
        - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          rewrite EQN. eapply L5KA.zeros_at_agree1. 2: exact YDZ. intros i Hi. apply FR1. clear - Hi YDR LY2; unfold SB in *; lia. clear - Hi YDR LY2 SPR; unfold SB in *; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      assert (C83 : L5.u64_at RSEGS M1 (sp - 8) (U R3 1)). { unfold U. rewrite (K3 1%nat) by inl. exact C82. }
      assert (LAX1 : L5.limbs_at RSEGS M1 xd wx). { eapply limbs_off_frame. exact FR1. clear - XDR; lia. rewrite NX. clear - XDR; lia. rewrite NX. exact XDFR. exact LAX. }
      assert (LAY1 : L5.limbs_at RSEGS M1 yd wy). { eapply limbs_off_frame. exact FR1. clear - YDR; lia. rewrite NY. clear - YDR; lia. rewrite NY. exact YDFR. exact LAY. }
      assert (A10' : getr R3 (reg 10) = Z_to_bv 64 MAXW). { rewrite (K3 10%nat) by inl. exact bR10. }
      destruct (wloop nx fx3 R3 M1 sp xd yd nx wx wy AT A10' ltac:(clear; lia) LX1 LX2 LF1 C83 LAX1 LAY1 NX ltac:(rewrite NY; symmetry; exact EQN) WX WY)
        as (fx4 & R4 & M4 & MS4 & K4 & R42 & RES & MM4).
      apply (FIN fx4 R4 M4 (L5CMP.cmp_val wx wy)).
      { eapply msteps_trans. exact MB1. eapply msteps_trans. exact MB2. eapply msteps_trans. exact eMS. exact MS4. }
      { intros x Hx. rewrite (K4 x Hx). apply K3. do 4 right. exact Hx. } exact R42.
      { rewrite RES. rewrite (L5CMP.enc_full wx wy nx NX ltac:(rewrite NY; symmetry; exact EQN) WX WY). reflexivity. } exact MM4.
      { split. apply L5CMP.cmp_val_cases. split; intros; exfalso; clear - EQN H; lia. } { intros _. reflexivity. }
    + (* [comment removed for export] *)
      assert (LT2 : (ny < nx)%nat). { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_false_iff in GE2. rewrite !BG.unsigned_lit in GE2 by (clear - LX2 LY2; lia). apply Z.ltb_lt in GE2. lia. }
      pose proof (vcmP_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K2 _) by inl; sc)]).
      destruct P as (fx3 & R3 & M3 & MG3 & pFR & pFZ & (pMS & pKS & pR2 & pR10)).
      apply (FIN fx3 R3 M3 1). { eapply msteps_trans. exact MB1. eapply msteps_trans. exact MB2. exact pMS. } { intros x Hx. apply pKS. revert x Hx. kl KS_vcmP. } exact pR2.
      exact pR10. exact pFR.
      { split. right; left; reflexivity. split. intros; exfalso; clear - LT2 H; lia. reflexivity. } { intros E. exfalso. clear - LT2 E. lia. }
Qed.

End SCFG_1.
End L5ACMP.
