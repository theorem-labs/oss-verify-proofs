(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun Bo0_code_91368_92368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5Cmp L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BLeafK L5BCmpP.
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

Definition CMP : Z := 0x91dd0.
Definition LHEAD : Z := 0x91f08.
Definition RET : Z := 0x91fe0.
Definition MAXW : Z := L5CMP.MAXW.

Definition cmp_kept : list nat := [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Definition cmp_objA (M : word -> option byte) (sp o : Z) (b : L5.bigobj) : Prop :=
  L5.big_at RSEGS M o b /\ Z.testbit (L5.bo_fb b) 1 = false /\ (1 <= L5.bo_len b)%nat /\ Z.of_nat (L5.bo_len b) <= 300 /\
  o mod 8 = 0 /\ 4096 <= o <= 140737488355296 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\
  (sp - 112 + 112 <= o \/ o + 32 <= sp - 112) /\ L5KA.zeros_at M (o / 8 + SB) 4 /\
  (4096 <= L5.bo_data o b /\ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 140737488355328) /\ L5.bo_data o b mod 8 = 0 /\
  (2147446784 + 17592186048512 <= L5.bo_data o b \/ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= 2147446784) /\
  (sp <= L5.bo_data o b \/ L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b) <= sp - 112) /\
  L5KA.zeros_at M (L5.bo_data o b / 8 + SB) (Z.of_nat (L5.bo_len b)).

Definition cmp_postA (M M' : word -> option byte) (R R' : bvmap 5 word) (sp : Z) (nx ny : nat) (wx wy : list Z) : Prop :=
  (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) /\ regs_preserved R R'
  /\ (exists c, getr R' (reg 10) = Z_to_bv 64 c /\ L5CMP.res_sized c nx ny /\ (nx = ny -> c = L5CMP.cmp_val wx wy))
  /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.

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
Lemma r10' : (10%bv : bv 5) = reg 10. Proof. bveq. Qed.
Lemma r11' : (11%bv : bv 5) = reg 11. Proof. bveq. Qed.
Lemma r18' : (18%bv : bv 5) = reg 18. Proof. bveq. Qed.
Lemma r22' : (22%bv : bv 5) = reg 22. Proof. bveq. Qed.
Lemma br_91b6c fx R M : msteps RSEGS (st fx R 0x91ec0 M) (st fx R (if branch_taken BC_EQ (getr R (reg 11)) (getr R (reg 0)) then 0x91ee4 else 0x91ec4) M).
Proof. rewrite <- r11', <- r0. apply (br_site fx R M 0x91ec0 0x91ee4 (0x91ec0%bv : word) _ BC_EQ 11 0 _ ltac:(bveq) F_91ec0 eq_refl D_91ec0); bveq. Qed.
Lemma br_91b98 fx R M : msteps RSEGS (st fx R 0x91eec M) (st fx R (if branch_taken BC_GEU (getr R (reg 18)) (getr R (reg 10)) then 0x91ef8 else 0x91ef0) M).
Proof. rewrite <- r18', <- r10'. apply (br_site fx R M 0x91eec 0x91ef8 (0x91eec%bv : word) _ BC_GEU 18 10 _ ltac:(bveq) F_91eec eq_refl D_91eec); bveq. Qed.
Lemma br_91ba8 fx R M : msteps RSEGS (st fx R 0x91efc M) (st fx R (if branch_taken BC_LTU (getr R (reg 10)) (getr R (reg 18)) then 0x91fa0 else 0x91f00) M).
Proof. rewrite <- r18', <- r10'. apply (br_site fx R M 0x91efc 0x91fa0 (0x91efc%bv : word) _ BC_LTU 10 18 _ ltac:(bveq) F_91efc eq_refl D_91efc); bveq. Qed.
Lemma br_91bf8 fx R M : msteps RSEGS (st fx R 0x91f4c M) (st fx R (if branch_taken BC_LTU (getr R (reg 10)) (getr R (reg 22)) then 0x91fa0 else 0x91f50) M).
Proof. rewrite <- r22', <- r10'. apply (br_site fx R M 0x91f4c 0x91fa0 (0x91f4c%bv : word) _ BC_LTU 10 22 _ ltac:(bveq) F_91f4c eq_refl D_91f4c); bveq. Qed.
Lemma br_91c40 fx R M : msteps RSEGS (st fx R 0x91f94 M) (st fx R (if branch_taken BC_GEU (getr R (reg 22)) (getr R (reg 10)) then 0x91f08 else 0x91f98) M).
Proof. rewrite <- r22', <- r10'. apply (br_site fx R M 0x91f94 0x91f08 (0x91f94%bv : word) _ BC_GEU 22 10 _ ltac:(bveq) F_91f94 eq_refl D_91f94); bveq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KX : list nat := [3; 4; 5; 6; 7; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Local Ltac kl KS := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; revert Hx; apply (L5K.incl_b _ KS); vm_compute; reflexivity.

Record xfacts (M : word -> option byte) (sp x fbx : Z) (R0 : bvmap 5 word) : Prop := XF {
  xf_sp : 140735332487280 <= sp <= 140737488355328 /\ sp mod 16 = 0;
  xf_w : L5.writable RSEGS M (sp - 112) 112;
  xf_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  xf_x : 4096 <= x <= 140737488355296 /\ x mod 8 = 0 /\ L5KA.zeros_at M (x / 8 + SB) 4 /\ L5.u8_at RSEGS M x fbx /\ 0 <= fbx <= 255 /\ Z.testbit fbx 1 = false;
  xf_sv : L5.u64_at RSEGS M (sp - 8) (U R0 1) /\ L5.u64_at RSEGS M (sp - 16) (U R0 8) /\ L5.u64_at RSEGS M (sp - 24) (U R0 9) /\ L5.u64_at RSEGS M (sp - 32) (U R0 18) /\ L5.u64_at RSEGS M (sp - 40) (U R0 19) /\ L5.u64_at RSEGS M (sp - 48) (U R0 20) /\ L5.u64_at RSEGS M (sp - 56) (U R0 21) /\ L5.u64_at RSEGS M (sp - 64) (U R0 22) }.
Definition at_out (R : bvmap 5 word) (sp x : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 96) /\ getr R (reg 8) = Z_to_bv 64 x /\ getr R (reg 19) = Z_to_bv 64 (x / 8 + 2147450880).

Lemma exit_P fx R M (sp x fbx : Z) (R0 : bvmap 5 word) :
  xfacts M sp x fbx R0 -> at_out R sp x ->
  exists fx' R' M', msteps RSEGS (st fx R 0x91fa0 M) (st fx' R' RET M')
    /\ (forall k, In k KX -> getr R' (reg k) = getr R (reg k)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = getr R (reg 9)
    /\ (getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\ getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\ getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22)) /\ (forall a, M' a = M a).
Proof.
  intros [[SPR A16] W112 [IMGC [CSB CUAR]] (XR & X8 & XZ & XFB & XFBR & XSG) (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22)] (A2 & A8 & A19).
  assert (ALS : aligned sp 16) by exact A16. assert (ALX : aligned x 8) by exact X8.
  assert (XSGp : 0 <= Z.land fbx 2 <= 0) by (rewrite (L5K.land2_bit1_false fbx ltac:(clear - XFBR; lia) XSG); clear; lia).
  pose proof (vcmP_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => x | 39%nat => fbx | 44%nat => U R0 1 | 45%nat => U R0 8 | 46%nat => U R0 9 | 47%nat => U R0 18 | 48%nat => U R0 19 | 49%nat => U R0 20 | 50%nat => U R0 21 | 51%nat => U R0 22 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR2 & zR8 & zR9 & zR10 & zR18 & zR19 & zR20 & zR21 & zR22)).
  exists fx1, R1, M1. split. exact zMS. split. { intros k Hk. apply zKS. revert k Hk. kl KS_vcmP. }
  split. exact zR2. split. exact zR10. split. { split. { rewrite zR1. symmetry. apply U_to. } split. { rewrite zR8. symmetry. apply U_to. } split. { rewrite zR9. symmetry. apply U_to. } split. { rewrite zR18. symmetry. apply U_to. } split. { rewrite zR19. symmetry. apply U_to. } split. { rewrite zR20. symmetry. apply U_to. } split. { rewrite zR21. symmetry. apply U_to. } { rewrite zR22. symmetry. apply U_to. } } exact zFR.
Qed.
Lemma exit_N fx R M (sp x fbx : Z) (R0 : bvmap 5 word) :
  xfacts M sp x fbx R0 -> at_out R sp x ->
  exists fx' R' M', msteps RSEGS (st fx R 0x91ef0 M) (st fx' R' RET M')
    /\ (forall k, In k KX -> getr R' (reg k) = getr R (reg k)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551615
    /\ (getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\ getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\ getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22)) /\ (forall a, M' a = M a).
Proof.
  intros [[SPR A16] W112 [IMGC [CSB CUAR]] (XR & X8 & XZ & XFB & XFBR & XSG) (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22)] (A2 & A8 & A19).
  assert (ALS : aligned sp 16) by exact A16. assert (ALX : aligned x 8) by exact X8.
  assert (XSGp : 0 <= Z.land fbx 2 <= 0) by (rewrite (L5K.land2_bit1_false fbx ltac:(clear - XFBR; lia) XSG); clear; lia).
  pose proof (vcmN_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => x | 39%nat => fbx | 44%nat => U R0 1 | 45%nat => U R0 8 | 46%nat => U R0 9 | 47%nat => U R0 18 | 48%nat => U R0 19 | 49%nat => U R0 20 | 50%nat => U R0 21 | 51%nat => U R0 22 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR2 & zR8 & zR9 & zR10 & zR18 & zR19 & zR20 & zR21 & zR22)).
  exists fx1, R1, M1. split. exact zMS. split. { intros k Hk. apply zKS. revert k Hk. kl KS_vcmN. }
  split. exact zR2. split. exact zR10. split. { split. { rewrite zR1. symmetry. apply U_to. } split. { rewrite zR8. symmetry. apply U_to. } split. { rewrite zR9. symmetry. apply U_to. } split. { rewrite zR18. symmetry. apply U_to. } split. { rewrite zR19. symmetry. apply U_to. } split. { rewrite zR20. symmetry. apply U_to. } split. { rewrite zR21. symmetry. apply U_to. } { rewrite zR22. symmetry. apply U_to. } } exact zFR.
Qed.
Lemma exit_N2 fx R M (sp x fbx : Z) (R0 : bvmap 5 word) :
  xfacts M sp x fbx R0 -> at_out R sp x ->
  exists fx' R' M', msteps RSEGS (st fx R 0x91f98 M) (st fx' R' RET M')
    /\ (forall k, In k KX -> getr R' (reg k) = getr R (reg k)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551615
    /\ (getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\ getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\ getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22)) /\ (forall a, M' a = M a).
Proof.
  intros [[SPR A16] W112 [IMGC [CSB CUAR]] (XR & X8 & XZ & XFB & XFBR & XSG) (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22)] (A2 & A8 & A19).
  assert (ALS : aligned sp 16) by exact A16. assert (ALX : aligned x 8) by exact X8.
  assert (XSGp : 0 <= Z.land fbx 2 <= 0) by (rewrite (L5K.land2_bit1_false fbx ltac:(clear - XFBR; lia) XSG); clear; lia).
  pose proof (vcmN2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => x | 39%nat => fbx | 44%nat => U R0 1 | 45%nat => U R0 8 | 46%nat => U R0 9 | 47%nat => U R0 18 | 48%nat => U R0 19 | 49%nat => U R0 20 | 50%nat => U R0 21 | 51%nat => U R0 22 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR2 & zR8 & zR9 & zR10 & zR18 & zR19 & zR20 & zR21 & zR22)).
  exists fx1, R1, M1. split. exact zMS. split. { intros k Hk. apply zKS. revert k Hk. kl KS_vcmN2. }
  split. exact zR2. split. exact zR10. split. { split. { rewrite zR1. symmetry. apply U_to. } split. { rewrite zR8. symmetry. apply U_to. } split. { rewrite zR9. symmetry. apply U_to. } split. { rewrite zR18. symmetry. apply U_to. } split. { rewrite zR19. symmetry. apply U_to. } split. { rewrite zR20. symmetry. apply U_to. } split. { rewrite zR21. symmetry. apply U_to. } { rewrite zR22. symmetry. apply U_to. } } exact zFR.
Qed.
Lemma exit_Z fx R M (sp x fbx : Z) (R0 : bvmap 5 word) :
  xfacts M sp x fbx R0 -> at_out R sp x -> getr R (reg 18) = Z_to_bv 64 18446744073709551615 -> getr R (reg 21) = Z_to_bv 64 18446744073709551615 ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall k, In k KX -> getr R' (reg k) = getr R (reg k)) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 10) = Z_to_bv 64 0
    /\ (getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\ getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\ getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22)) /\ (forall a, M' a = M a).
Proof.
  intros [[SPR A16] W112 [IMGC [CSB CUAR]] (XR & X8 & XZ & XFB & XFBR & XSG) (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22)] (A2 & A8 & A19) A18 A21.
  assert (ALS : aligned sp 16) by exact A16. assert (ALX : aligned x 8) by exact X8.
  assert (XSGp : 0 <= Z.land fbx 2 <= 0) by (rewrite (L5K.land2_bit1_false fbx ltac:(clear - XFBR; lia) XSG); clear; lia).
  pose proof (vcmZ_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => x | 39%nat => fbx | 44%nat => U R0 1 | 45%nat => U R0 8 | 46%nat => U R0 9 | 47%nat => U R0 18 | 48%nat => U R0 19 | 49%nat => U R0 20 | 50%nat => U R0 21 | 51%nat => U R0 22 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & zFR & zFZ & (zMS & zKS & zR1 & zR2 & zR8 & zR9 & zR10 & zR18 & zR19 & zR20 & zR21 & zR22)).
  exists fx1, R1, M1. split. exact zMS. split. { intros k Hk. apply zKS. revert k Hk. kl KS_vcmZ. }
  split. exact zR2. split. exact zR10. split. { split. { rewrite zR1. symmetry. apply U_to. } split. { rewrite zR8. symmetry. apply U_to. } split. { rewrite zR9. symmetry. apply U_to. } split. { rewrite zR18. symmetry. apply U_to. } split. { rewrite zR19. symmetry. apply U_to. } split. { rewrite zR20. symmetry. apply U_to. } split. { rewrite zR21. symmetry. apply U_to. } { rewrite zR22. symmetry. apply U_to. } } exact zFR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record lfacts (M : word -> option byte) (sp xd yd : Z) (n : nat) : Prop := LF {
  lf_x : 4096 <= xd <= 140737488355328 /\ xd mod 8 = 0 /\ 4104 <= xd + 8 * Z.of_nat n <= 140737488355328 /\ (2147446784 + 17592186048512 <= xd \/ xd + 8 * Z.of_nat n <= 2147446784)
         /\ (sp - 112 + 112 <= xd \/ xd + 8 * Z.of_nat n <= sp - 112);
  lf_xz : L5KA.zeros_at M (xd / 8 + SB) (Z.of_nat n);
  lf_y : 4096 <= yd <= 140737488355328 /\ yd mod 8 = 0 /\ 4104 <= yd + 8 * Z.of_nat n <= 140737488355328 /\ (2147446784 + 17592186048512 <= yd \/ yd + 8 * Z.of_nat n <= 2147446784)
         /\ (sp - 112 + 112 <= yd \/ yd + 8 * Z.of_nat n <= sp - 112);
  lf_yz : L5KA.zeros_at M (yd / 8 + SB) (Z.of_nat n);
  lf_v : L5.u64_at RSEGS M (sp - 80) xd /\ L5.u64_at RSEGS M (sp - 96) yd
         /\ L5KA.zeros_at M ((sp - 80) / 8 + SB) 1 /\ L5KA.zeros_at M ((sp - 96) / 8 + SB) 1 }.

(* [comment removed for export] *)
Definition at_head (R : bvmap 5 word) (sp x : Z) (k : nat) : Prop :=
  at_out R sp x /\ getr R (reg 9) = Z_to_bv 64 1 /\ getr R (reg 18) = Z_to_bv 64 (Z.of_nat k - 1) /\ getr R (reg 20) = Z_to_bv 64 2147450880 /\
  getr R (reg 21) = Z_to_bv 64 18446744073709551615.

Lemma m1_lit : Z_to_bv 64 (Z.of_nat 0 - 1) = Z_to_bv 64 18446744073709551615. Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma facts_keep M M' sp x fbx R0 xd yd n :
  xfacts M sp x fbx R0 -> lfacts M sp xd yd n -> mem_grows M M' -> (2147446784 + 17592186048512 <= x \/ x + 32 <= 2147446784) -> (sp - 112 + 112 <= x \/ x + 32 <= sp - 112) ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> xfacts M' sp x fbx R0 /\ lfacts M' sp xd yd n.
Proof.
  intros [[SPR A16] W112 [IMGC [CSB CUAR]] (XR & X8 & XZ & XFB & XFBR & XSG) (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22)]
         [(XDR & XD8 & XDC & XDBIG & XDFR) XDZ (YDR & YD8 & YDC & YDBIG & YDFR) YDZ (VX & VY & VXZ & VYZ)] G XBIG XFR K.
  assert (KC : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= sp - 104 \/ sp - 96 <= a) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb Hs Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: exact Ha. 2: exact Hb. intros j Hj. apply K. clear - Hj Ha Hb; lia. clear - Hj Hs; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (KZ : forall a g, 2147446784 <= a -> a + g <= 17594333495296 -> L5KA.zeros_at M a g -> L5KA.zeros_at M' a g).
  { intros a g Ha Hb Hz. eapply L5KA.zeros_at_agree1. 2: exact Hz. intros i Hi. apply K. clear - Hi Ha Hb; lia. clear - Hi Ha Hb SPR; lia. }
  split.
  - constructor. split; assumption. eapply L5.writable_grows; eauto.
    + split. { intros a Ha. rewrite K. apply IMGC. exact Ha. clear - Ha; lia. clear - Ha SPR; lia. }
      split. apply KC. clear; lia. clear; lia. clear - SPR; lia. exact CSB.
      eapply L5BLK.u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros i Hi. apply K. clear - Hi; lia. clear - Hi SPR; lia.
    + split. exact XR. split. exact X8. split. { apply KZ. clear - XR; unfold SB; lia. clear - XR; unfold SB; lia. exact XZ. }
      split. { eapply L5C.u8_at_agree. 4: exact XFB. 2: clear - XR; lia. 2: clear - XR; lia. intros j Hj. apply K. clear - Hj XR; lia. clear - Hj XFR; lia. }
      split. exact XFBR. exact XSG.
    + repeat split; apply KC; first [exact S1 | exact S8 | exact S9 | exact S18 | exact S19 | exact S20 | exact S21 | exact S22 | clear - SPR; lia].
  - constructor.
    + repeat split; first [assumption | clear - XDR; lia | clear - XDC; lia].
    + apply KZ. clear - XDR; unfold SB; lia. clear - XDR XDC; unfold SB; lia. exact XDZ.
    + repeat split; first [assumption | clear - YDR; lia | clear - YDC; lia].
    + apply KZ. clear - YDR; unfold SB; lia. clear - YDR YDC; unfold SB; lia. exact YDZ.
    + split. apply KC. clear - SPR; lia. clear - SPR; lia. clear; lia. exact VX. split. apply KC. clear - SPR; lia. clear - SPR; lia. clear; lia. exact VY.
      split. apply KZ. clear - SPR; unfold SB; lia. clear - SPR; unfold SB; lia. exact VXZ. apply KZ. clear - SPR; unfold SB; lia. clear - SPR; unfold SB; lia. exact VYZ.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma limbs_keep M M' sp d ws : (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  4096 <= d -> d + 8 * Z.of_nat (length ws) <= 140737488355328 -> (sp - 112 + 112 <= d \/ d + 8 * Z.of_nat (length ws) <= sp - 112) ->
  L5.limbs_at RSEGS M d ws -> L5.limbs_at RSEGS M' d ws.
Proof.
  intros AG Dlo Dhi DFR LA i Hi. eapply L5C.u64_at_agree. 4: exact (LA i Hi). 2: clear - Dlo; lia. 2: clear - Dhi Hi; lia.
  intros j Hj. apply AG. clear - Hj Dlo Dhi Hi; lia. clear - Hj Hi DFR; lia.
Qed.

Lemma wloop (k : nat) : forall fx R M (sp x fbx xd yd : Z) (R0 : bvmap 5 word) (n : nat) (wx wy : list Z),
  at_head R sp x k -> (k <= n)%nat -> (1 <= n)%nat -> Z.of_nat n <= 300 ->
  xfacts M sp x fbx R0 -> lfacts M sp xd yd n -> (2147446784 + 17592186048512 <= x \/ x + 32 <= 2147446784) -> (sp - 112 + 112 <= x \/ x + 32 <= sp - 112) ->
  L5.limbs_at RSEGS M xd wx -> L5.limbs_at RSEGS M yd wy -> length wx = n -> length wy = n -> L5W.words_ok wx -> L5W.words_ok wy ->
  exists fx' R' M', msteps RSEGS (st fx R LHEAD M) (st fx' R' RET M')
    /\ (forall j, In j KX -> getr R' (reg j) = getr R (reg j)) /\ getr R' (reg 2) = Z_to_bv 64 sp
    /\ getr R' (reg 10) = Z_to_bv 64 (L5CMP.enc (BigModel.compare_loop k wx wy))
    /\ (getr R' (reg 1) = getr R0 (reg 1) /\ getr R' (reg 8) = getr R0 (reg 8) /\ getr R' (reg 9) = getr R0 (reg 9) /\ getr R' (reg 18) = getr R0 (reg 18) /\ getr R' (reg 19) = getr R0 (reg 19) /\ getr R' (reg 20) = getr R0 (reg 20) /\ getr R' (reg 21) = getr R0 (reg 21) /\ getr R' (reg 22) = getr R0 (reg 22))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.
Proof.
  induction k as [|k IH]; intros fx R M sp x fbx xd yd R0 n wx wy AT Hkn Hn1 Hn2 XFM LFM XBIG XFR Lx Ly Nx Ny Wx Wy.
  all: destruct AT as (AO & A9 & A18 & A20 & A21).
  - (* [comment removed for export] *)
    rewrite m1_lit in A18.
    destruct (exit_Z fx R M sp x fbx R0 XFM AO A18 A21) as (fx1 & R1 & M1 & zMS & zK & zR2 & zR10 & zRS & zM).
    exists fx1, R1, M1. split. exact zMS. split. exact zK. split. exact zR2. split. exact zR10. split. exact zRS.
    split. { intros i _ _. apply zM. } intros a Ha. rewrite zM. exact Ha.
  - pose proof XFM as [[SPR A16] W112 [IMGC [CSB CUAR]] (XR & X8 & XZ & XFB & XFBR & XSG) SVS].
    pose proof LFM as [(XDR & XD8 & XDC & XDBIG & XDFR) XDZ (YDR & YD8 & YDC & YDBIG & YDFR) YDZ (VX & VY & VXZ & VYZ)].
    pose proof AO as (A2 & A8 & A19).
    replace (Z.of_nat (Datatypes.S k) - 1) with (Z.of_nat k) in A18 by (clear; lia).
    set (xk := L5W.nth_w wx k). set (yk := L5W.nth_w wy k).
    assert (Rxk : 0 <= xk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wx). assert (Ryk : 0 <= yk < 2 ^ 64) by (apply L5W.words_ok_nth; exact Wy).
    assert (Ux : L5.u64_at RSEGS M (xd + 8 * Z.of_nat k) xk). { apply Lx. clear - Hkn Nx; lia. }
    assert (Uy : L5.u64_at RSEGS M (yd + 8 * Z.of_nat k) yk). { apply Ly. clear - Hkn Ny; lia. }
    assert (ALS : aligned sp 16) by exact A16. assert (ALX : aligned xd 8) by exact XD8. assert (ALY : aligned yd 8) by exact YD8.
    assert (HVN : 1 <= Z.of_nat n <= 300) by (clear - Hn1 Hn2; lia). assert (HVK : 0 <= Z.of_nat k <= 299) by (clear - Hkn Hn2; lia).
    assert (HVNK : 1 <= Z.of_nat n - Z.of_nat k <= 300) by (clear - Hkn Hn2; lia).
    assert (HX1 : 0 <= xk <= 18446744073709551615) by (clear - Rxk; lia). assert (HY1 : 0 <= yk <= 18446744073709551615) by (clear - Ryk; lia).
    assert (VXZp : L5KA.zeros_at M ((sp - 80) / 8 + 2147450880) 1) by exact VXZ. assert (VYZp : L5KA.zeros_at M ((sp - 96) / 8 + 2147450880) 1) by exact VYZ.
    pose proof (vcmI_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => Z.of_nat n | 37%nat => xd | 38%nat => yd | 41%nat => Z.of_nat k | 42%nat => xk | 43%nat => yk | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG1 & iFR & iFZ & (iMS & iKS & iR1 & iR10 & iR11 & iR12 & iR13 & iR14 & iR22 & iCRA)).
    assert (K1 : forall j, In j (2 :: 8 :: 9 :: 18 :: 19 :: 20 :: 21 :: KX)%nat -> getr R1 (reg j) = getr R (reg j)). { intros j Hj. apply iKS. revert j Hj. kl KS_vcmI. }
    assert (FZ1 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn. apply iFZ. exact Hi. clear - Hn; lia. }
    destruct (facts_keep M M1 sp x fbx R0 xd yd n XFM LFM MG1 XBIG XFR FZ1) as [XF1 LF1].
    assert (AO1 : at_out R1 sp x). { unfold at_out. rewrite !(K1 _) by inl. exact AO. }
    pose proof (br_91bf8 fx1 R1 M1) as MB1. rewrite iR10, iR22 in MB1.
    cbn [BigModel.compare_loop]. change (BigModel.nth_w wx k) with xk. change (BigModel.nth_w wy k) with yk.
    destruct (branch_taken BC_LTU (Z_to_bv 64 yk) (Z_to_bv 64 xk)) eqn:LT1.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = true). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by (clear - Rxk Ryk; lia). exact LT1. }
      rewrite LT1'.
      destruct (exit_P fx1 R1 M1 sp x fbx R0 XF1 AO1) as (fx2 & R2 & M2 & pMS & pK & pR2 & pR10 & pRS & pM).
      exists fx2, R2, M2. split. { eapply msteps_trans. exact iMS. eapply msteps_trans. exact MB1. exact pMS. }
      split. { intros j Hj. rewrite (pK j Hj). apply K1. do 7 right. exact Hj. }
      split. exact pR2. split. { rewrite pR10, (K1 9%nat) by inl. exact A9. } split. exact pRS.
      split. { intros i Hi Hn. rewrite pM. apply FZ1. exact Hi. exact Hn. }
      intros a Ha. rewrite pM. apply MG1. exact Ha.
    + (* [comment removed for export] *)
      assert (LT1': (yk <? xk) = false). { unfold branch_taken, bv_ltu in LT1. rewrite !BG.unsigned_lit in LT1 by (clear - Rxk Ryk; lia). exact LT1. }
      rewrite LT1'.
      pose proof LF1 as [_ XDZ1 _ YDZ1 (VX1 & VY1 & VXZ1 & VYZ1)]. pose proof XF1 as [_ W112a [IMGC1 [CSB1 CUAR1]] _ _].
      assert (Ux1 : L5.u64_at RSEGS M1 (xd + 8 * Z.of_nat k) xk). { eapply L5C.u64_at_agree. 4: exact Ux. 2: clear - XDR; lia. 2: clear - XDC HVNK; lia. intros j Hj. apply FZ1. clear - Hj XDR XDC HVNK; lia. clear - Hj XDFR HVNK; lia. }
      assert (Uy1 : L5.u64_at RSEGS M1 (yd + 8 * Z.of_nat k) yk). { eapply L5C.u64_at_agree. 4: exact Uy. 2: clear - YDR; lia. 2: clear - YDC HVNK; lia. intros j Hj. apply FZ1. clear - Hj YDR YDC HVNK; lia. clear - Hj YDFR HVNK; lia. }
      assert (VXZ1p : L5KA.zeros_at M1 ((sp - 80) / 8 + 2147450880) 1) by exact VXZ1. assert (VYZ1p : L5KA.zeros_at M1 ((sp - 96) / 8 + 2147450880) 1) by exact VYZ1.
      pose proof (vcmJ_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 35%nat => Z.of_nat n | 37%nat => xd | 38%nat => yd | 41%nat => Z.of_nat k | 42%nat => xk | 43%nat => yk | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite (K1 _) by inl; sc)]).
      destruct P as (fx2 & R2 & M2 & MG2 & jFR & jFZ & (jMS & jKS & jR1 & jR10 & jR11 & jR12 & jR13 & jR14 & jR18 & jR22 & jCRA)).
      assert (K2 : forall j, In j (2 :: 8 :: 9 :: 19 :: 20 :: 21 :: KX)%nat -> getr R2 (reg j) = getr R1 (reg j)). { intros j Hj. apply jKS. revert j Hj. kl KS_vcmJ. }
      assert (FZ2 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)). { intros i Hi Hn. apply jFZ. exact Hi. clear - Hn; lia. }
      destruct (facts_keep M1 M2 sp x fbx R0 xd yd n XF1 LF1 MG2 XBIG XFR FZ2) as [XF2 LF2].
      assert (AO2 : at_out R2 sp x). { unfold at_out. rewrite !(K2 _) by inl. exact AO1. }
      assert (FZ02 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn. rewrite FZ2 by assumption. apply FZ1; assumption. }
      pose proof (br_91c40 fx2 R2 M2) as MB2. rewrite jR10, jR22 in MB2.
      destruct (branch_taken BC_GEU (Z_to_bv 64 xk) (Z_to_bv 64 yk)) eqn:GE2.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = false).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_true_iff in GE2. rewrite !BG.unsigned_lit in GE2 by (clear - Rxk Ryk; lia). exact GE2. }
        rewrite GE2'.
        assert (AT2: at_head R2 sp x k).
        { unfold at_head. split. exact AO2. split. { rewrite (K2 9%nat), (K1 9%nat) by inl. exact A9. } split. exact jR18.
          split. { rewrite (K2 20%nat), (K1 20%nat) by inl. exact A20. } rewrite (K2 21%nat), (K1 21%nat) by inl. exact A21. }
        assert (Lx2 : L5.limbs_at RSEGS M2 xd wx). { eapply limbs_keep. exact FZ02. clear - XDR; lia. rewrite Nx. clear - XDC; lia. rewrite Nx. exact XDFR. exact Lx. }
        assert (Ly2 : L5.limbs_at RSEGS M2 yd wy). { eapply limbs_keep. exact FZ02. clear - YDR; lia. rewrite Ny. clear - YDC; lia. rewrite Ny. exact YDFR. exact Ly. }
        destruct (IH fx2 R2 M2 sp x fbx xd yd R0 n wx wy AT2 ltac:(clear - Hkn; lia) Hn1 Hn2 XF2 LF2 XBIG XFR Lx2 Ly2 Nx Ny Wx Wy) as (fx3 & R3 & M3 & MS3 & K3 & R32 & RES & RS3 & FZ3 & MG3).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact iMS. eapply msteps_trans. exact MB1. eapply msteps_trans. exact jMS. eapply msteps_trans. exact MB2. exact MS3. }
        split. { intros j Hj. rewrite (K3 j Hj). rewrite (K2 j) by (do 6 right; exact Hj). apply K1. do 7 right. exact Hj. }
        split. exact R32. split. exact RES. split. exact RS3.
        split. { intros i Hi Hn. rewrite FZ3 by assumption. apply FZ02; assumption. }
        eapply mem_grows_trans. exact MG1. eapply mem_grows_trans. exact MG2. exact MG3.
      * (* [comment removed for export] *)
        assert (GE2': (xk <? yk) = true).
        { unfold branch_taken, bv_ltu in GE2. apply Bool.negb_false_iff in GE2. rewrite !BG.unsigned_lit in GE2 by (clear - Rxk Ryk; lia). exact GE2. }
        rewrite GE2'.
        destruct (exit_N2 fx2 R2 M2 sp x fbx R0 XF2 AO2) as (fx3 & R3 & M3 & nMS & nK & nR2 & nR10 & nRS & nM).
        exists fx3, R3, M3. split. { eapply msteps_trans. exact iMS. eapply msteps_trans. exact MB1. eapply msteps_trans. exact jMS. eapply msteps_trans. exact MB2. exact nMS. }
        split. { intros j Hj. rewrite (nK j Hj). rewrite (K2 j) by (do 6 right; exact Hj). apply K1. do 7 right. exact Hj. }
        split. exact nR2. split. exact nR10. split. exact nRS.
        split. { intros i Hi Hn. rewrite nM. apply FZ02; assumption. }
        intros a Ha. rewrite nM. apply MG2. apply MG1. exact Ha.
Qed.
Lemma kept_regs_preserved R R' : (forall i, In i cmp_kept -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof. intros K. apply preserved_by_index. intros k Hk. apply K. revert k Hk. kl cmp_kept. Qed.
Lemma lor_nz a b : 0 <= a -> 1 <= b -> Z.lor a b <> 0.
Proof. intros Ha Hb E. apply Z.lor_eq_0_iff in E. lia. Qed.
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


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cmA_run fx R M (sp xo yo : Z) (bx by_ : L5.bigobj) :
  getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo ->
  140735332487280 <= sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M (sp - 112) 112 ->
  L5.img_clear M 860160 884736 -> L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  cmp_objA M sp xo bx -> cmp_objA M sp yo by_ ->
  exists fx' R' M', msteps RSEGS (st fx R CMP M) (st fx' R' 0x91ec0 M')
    /\ (forall x, In x KX -> getr R' (reg x) = getr R (reg x)) /\ at_out R' sp xo
    /\ getr R' (reg 10) = Z_to_bv 64 (Z.of_nat (L5.bo_len by_))
    /\ bv_unsigned (getr R' (reg 11)) = Z.lor (Z.of_nat (L5.bo_len by_)) (Z.of_nat (L5.bo_len bx))
    /\ getr R' (reg 12) = Z_to_bv 64 (L5.bo_fb bx) /\ getr R' (reg 13) = Z_to_bv 64 (L5.bo_fb by_)
    /\ getr R' (reg 18) = Z_to_bv 64 (Z.of_nat (L5.bo_len bx)) /\ getr R' (reg 20) = Z_to_bv 64 2147450880
    /\ L5.u64_at RSEGS M' (sp - 80) (L5.bo_data xo bx) /\ L5.u64_at RSEGS M' (sp - 96) (L5.bo_data yo by_)
    /\ (L5.u64_at RSEGS M' (sp - 8) (U R 1) /\ L5.u64_at RSEGS M' (sp - 16) (U R 8) /\ L5.u64_at RSEGS M' (sp - 24) (U R 9) /\ L5.u64_at RSEGS M' (sp - 32) (U R 18) /\ L5.u64_at RSEGS M' (sp - 40) (U R 19) /\ L5.u64_at RSEGS M' (sp - 48) (U R 20) /\ L5.u64_at RSEGS M' (sp - 56) (U R 21) /\ L5.u64_at RSEGS M' (sp - 64) (U R 22))
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) /\ mem_grows M M'.
Proof.
  intros H2 H10 H11 SPR A16 W112 IMGC CSB CUAR OX OY. unfold CMP.
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
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & CYN & CYD & CXN & CXD & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAii. }
    split. { unfold at_out. repeat split; assumption. }
    split. exact A10. split. exact A11. split. exact A12. split. exact A13. split. exact A18. split. exact A20. split. exact CXD. split. exact CYD.
    split. { unfold U. repeat split; assumption. } split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
  - destruct XST as (XB0 & _). destruct YST as (YB0 & _ & YQ & _).
    assert (HVQ : 0 <= yq < 2 ^ 64) by (clear - YDR; lia). pose proof (vcmAid_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 38%nat => yq | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & CYN & CYD & CXN & CXD & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAid. }
    split. { unfold at_out. repeat split; assumption. }
    split. exact A10. split. exact A11. split. exact A12. split. exact A13. split. exact A18. split. exact A20. split. exact CXD. split. exact CYD.
    split. { unfold U. repeat split; assumption. } split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
  - destruct XST as (XB0 & _ & XQ & _). destruct YST as (YB0 & _).
    assert (HVQ : 0 <= xq < 2 ^ 64) by (clear - XDR; lia). pose proof (vcmAdi_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 37%nat => xq | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & CYN & CYD & CXN & CXD & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAdi. }
    split. { unfold at_out. repeat split; assumption. }
    split. exact A10. split. exact A11. split. exact A12. split. exact A13. split. exact A18. split. exact A20. split. exact CXD. split. exact CYD.
    split. { unfold U. repeat split; assumption. } split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
  - destruct XST as (XB0 & _ & XQ & _). destruct YST as (YB0 & _ & YQ & _).
    assert (HVQ : 0 <= xq < 2 ^ 64) by (clear - XDR; lia). assert (HVQ2 : 0 <= yq < 2 ^ 64) by (clear - YDR; lia). pose proof (vcmAdd_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => xo | 34%nat => yo | 35%nat => Z.of_nat nx | 36%nat => Z.of_nat ny | 37%nat => xq | 38%nat => yq | 39%nat => fbx | 40%nat => fby | _ => 0 end)) as P.
    cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A2 & A8 & A10 & A11 & A12 & A13 & A14 & A18 & A19 & A20 & CYN & CYD & CXN & CXD & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)).
    exists fx1, R1, M1. split. exact MS. split. { intros x Hx. apply KS. revert x Hx. kl KS_vcmAdd. }
    split. { unfold at_out. repeat split; assumption. }
    split. exact A10. split. exact A11. split. exact A12. split. exact A13. split. exact A18. split. exact A20. split. exact CXD. split. exact CYD.
    split. { unfold U. repeat split; assumption. } split. { intros i Hi Hn. apply FRZ. exact Hi. clear - Hn; lia. } exact MG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem cmp_runA (fx : FPState) R M (xo yo sp r : Z) (bx by_ : L5.bigobj) (wx wy : list Z) :
  getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 11) = Z_to_bv 64 yo -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R (reg 2) = Z_to_bv 64 sp -> 140735332487280 <= sp <= 140737488355328 -> sp mod 16 = 0 -> L5.writable RSEGS M (sp - 112) 112 ->
  L5KA.zeros_at M ((sp - 112) / 8 + SB) 14 ->
  L5.img_clear M 860160 884736 -> L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  cmp_objA M sp xo bx -> cmp_objA M sp yo by_ -> L5C.obj_limbs RSEGS M bx wx -> L5C.obj_limbs RSEGS M by_ wy ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M')
    /\ cmp_postA M M' R R' sp (L5.bo_len bx) (L5.bo_len by_) wx wy.
Proof.
  intros H10 H11 H1 RA H2 SPR A16 W112 SHZ IMGC CSB CUAR OX OY LMX LMY.
  destruct (cmA_run fx R M sp xo yo bx by_ H2 H10 H11 SPR A16 W112 IMGC CSB CUAR OX OY)
    as (fx1 & R1 & M1 & MS1 & K1 & AO1 & A10 & A11 & A12 & A13 & A18 & A20 & VX1 & VY1 & SV1 & FR1 & MG1).
  destruct OX as (BX & SGX & LX1 & LX2 & X8 & XR & XBIG & XFR & XZ & XDR & XD8 & XDBIG & XDFR & XDZ).
  destruct OY as (BY & SGY & LY1 & LY2 & Y8 & YR & YBIG & YFR & YZ & YDR & YD8 & YDBIG & YDFR & YDZ).
  destruct (obj_limbs_data M xo bx wx BX LMX) as (LAX & NX & WX). destruct (obj_limbs_data M yo by_ wy BY LMY) as (LAY & NY & WY).
  set (nx := L5.bo_len bx) in *. set (ny := L5.bo_len by_) in *. set (xd := L5.bo_data xo bx) in *. set (yd := L5.bo_data yo by_) in *.
  assert (XFBR : 0 <= L5.bo_fb bx <= 255) by (destruct BX as (_ & F & _); clear - F; lia).
  assert (YFBR : 0 <= L5.bo_fb by_ <= 255) by (destruct BY as (_ & F & _); clear - F; lia).
  assert (Hr : 0 <= r < 2 ^ 64) by (destruct RA; lia).
  (* [comment removed for export] *)
  assert (KC : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= sp - 96 \/ sp <= a) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb Hs Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: exact Ha. 2: exact Hb. intros j Hj. apply FR1. clear - Hj Ha Hb; lia. clear - Hj Hs; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (KZ : forall a g, 2147446784 <= a -> a + g <= 17594333495296 -> L5KA.zeros_at M a g -> L5KA.zeros_at M1 a g).
  { intros a g Ha Hb Hz. eapply L5KA.zeros_at_agree1. 2: exact Hz. intros i Hi. apply FR1. clear - Hi Ha Hb; lia. clear - Hi Ha Hb SPR; lia. }
  assert (XF1 : xfacts M1 sp xo (L5.bo_fb bx) R).
  { constructor. split; assumption. eapply L5.writable_grows; eauto.
    - split. { intros a Ha. rewrite FR1. apply IMGC. exact Ha. clear - Ha; lia. clear - Ha SPR; lia. }
      split. apply KC. clear; lia. clear; lia. clear - SPR; lia. exact CSB.
      eapply L5BLK.u32_at_agree1. 4: exact CUAR. 2: clear; lia. 2: clear; lia. intros i Hi. apply FR1. clear - Hi; lia. clear - Hi SPR; lia.
    - split. exact XR. split. exact X8. split. { apply KZ. clear - XR; unfold SB; lia. clear - XR; unfold SB; lia. exact XZ. }
      split. { destruct BX as (XFB & _). eapply L5C.u8_at_agree. 4: exact XFB. 2: clear - XR; lia. 2: clear - XR; lia. intros j Hj. apply FR1. clear - Hj XR; lia. clear - Hj XFR; lia. }
      split. exact XFBR. exact SGX.
    - exact SV1. }
  assert (VXZ1 : L5KA.zeros_at M1 ((sp - 80) / 8 + SB) 1).
  { apply KZ. clear - SPR; unfold SB; lia. clear - SPR; unfold SB; lia. eapply L5KA.zeros_at_sub. exact SHZ. clear - A16; lia. clear - A16; lia. }
  assert (VYZ1 : L5KA.zeros_at M1 ((sp - 96) / 8 + SB) 1).
  { apply KZ. clear - SPR; unfold SB; lia. clear - SPR; unfold SB; lia. eapply L5KA.zeros_at_sub. exact SHZ. clear - A16; lia. clear - A16; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (U1 : U R 1 = r). { unfold U. rewrite H1. apply L5.unsigned_lit. exact Hr. }
  (* [comment removed for export] *)
  pose proof (br_91b6c fx1 R1 M1) as MB0.
  assert (NT0 : branch_taken BC_EQ (getr R1 (reg 11)) (getr R1 (reg 0)) = false).
  { unfold branch_taken. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite A11 in E.
    change (bv_unsigned (getr R1 (reg 0))) with 0 in E. revert E. apply lor_nz; clear - LX1; lia. }
  rewrite NT0 in MB0.
  (* [comment removed for export] *)
  pose proof AO1 as (A2 & A8 & A19).
  pose proof (vcmB_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 39%nat => L5.bo_fb bx | 40%nat => L5.bo_fb by_ | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx2 & R2 & M2 & MG2 & bFR & bFZ & (bMS & bKS & bR11 & bR12 & bR13)).
  assert (EM2 : M2 = M1). { apply functional_extensionality. exact bFR. } subst M2.
  assert (K2 : forall j, In j (2 :: 8 :: 10 :: 18 :: 19 :: 20 :: KX)%nat -> getr R2 (reg j) = getr R1 (reg j)). { intros j Hj. apply bKS. revert j Hj. kl KS_vcmB. }
  assert (AO2 : at_out R2 sp xo). { unfold at_out. rewrite !(K2 _) by inl. exact AO1. }
  (* [comment removed for export] *)
  assert (FIN : forall fx3 R3 M3 c, msteps RSEGS (st fx2 R2 0x91eec M1) (st fx3 R3 RET M3) ->
            (forall x, In x KX -> getr R3 (reg x) = getr R2 (reg x)) -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 10) = Z_to_bv 64 c ->
            (getr R3 (reg 1) = getr R (reg 1) /\ getr R3 (reg 8) = getr R (reg 8) /\ getr R3 (reg 9) = getr R (reg 9) /\ getr R3 (reg 18) = getr R (reg 18) /\ getr R3 (reg 19) = getr R (reg 19) /\ getr R3 (reg 20) = getr R (reg 20) /\ getr R3 (reg 21) = getr R (reg 21) /\ getr R3 (reg 22) = getr R (reg 22)) ->
            (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 104 <= i < sp - 96) -> M3 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) -> mem_grows M1 M3 ->
            L5CMP.res_sized c nx ny -> (nx = ny -> c = L5CMP.cmp_val wx wy) ->
            exists (fx' : FPState) R' M', msteps RSEGS (st fx R CMP M) (st fx' R' r M') /\ cmp_postA M M' R R' sp nx ny wx wy).
  { intros fx3 R3 M3 c MS3 K3 R32 R310 (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22) FR3 MG3 RS CV.
    assert (R31 : getr R3 (reg 1) = Z_to_bv 64 r). { rewrite S1. exact H1. }
    pose proof (ret_to fx3 R3 M3 0x91fe0 W_91fe0 r (fz _ _ 0x91fe0 _ F_91fe0 ltac:(apply bv_eq; reflexivity)) eq_refl D_91fe0 R31 (proj1 RA) (proj2 RA)) as RET'.
    exists fx3, R3, M3. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MB0. eapply msteps_trans. exact bMS. eapply msteps_trans. exact MS3. exact RET'. }
    assert (KK : forall i, In i cmp_kept -> getr R3 (reg i) = getr R (reg i)).
    { intros i Hi. unfold cmp_kept in Hi. cbn [In] in Hi.
      assert (KXi : In i KX -> getr R3 (reg i) = getr R (reg i)). { intros Hx. rewrite (K3 i Hx). rewrite (K2 i) by (do 6 right; exact Hx). apply K1. exact Hx. }
      destruct Hi as [<-|Hi]. exact S1. destruct Hi as [<-|Hi]. { rewrite R32. symmetry. exact H2. }
      destruct Hi as [<-|Hi]. { apply KXi; inl. } destruct Hi as [<-|Hi]. { apply KXi; inl. } destruct Hi as [<-|Hi]. { apply KXi; inl. }
      destruct Hi as [<-|Hi]. exact S8. destruct Hi as [<-|Hi]. exact S9. destruct Hi as [<-|Hi]. exact S18. destruct Hi as [<-|Hi]. exact S19.
      destruct Hi as [<-|Hi]. exact S20. destruct Hi as [<-|Hi]. exact S21. destruct Hi as [<-|Hi]. exact S22.
      apply KXi. clear - Hi. unfold KX. cbn [In] in *. tauto. }
    split. exact KK. split. apply kept_regs_preserved. exact KK. split. { exists c. split. exact R310. split. exact RS. exact CV. }
    split. { intros i Hi Hn. rewrite FR3. apply FR1. exact Hi. clear - Hn; lia. exact Hi. clear - Hn; lia. }
    eapply mem_grows_trans. exact MG1. exact MG3. }
  assert (RSid : forall R3 : bvmap 5 word, (getr R3 (reg 1) = getr R (reg 1) /\ getr R3 (reg 8) = getr R (reg 8) /\ getr R3 (reg 9) = getr R (reg 9) /\ getr R3 (reg 18) = getr R (reg 18) /\ getr R3 (reg 19) = getr R (reg 19) /\ getr R3 (reg 20) = getr R (reg 20) /\ getr R3 (reg 21) = getr R (reg 21) /\ getr R3 (reg 22) = getr R (reg 22)) -> True) by (intros; exact I).
  pose proof (br_91b98 fx2 R2 M1) as MB1. rewrite (K2 18%nat), (K2 10%nat), A18, A10 in MB1 by inl.
  destruct (branch_taken BC_GEU (Z_to_bv 64 (Z.of_nat nx)) (Z_to_bv 64 (Z.of_nat ny))) eqn:GE1.
  2:{ (* [comment removed for export] *)
    assert (LT1' : (nx < ny)%nat). { unfold branch_taken, bv_ltu in GE1. apply Bool.negb_false_iff in GE1. rewrite !BG.unsigned_lit in GE1 by (clear - LX2 LY2; lia). apply Z.ltb_lt in GE1. lia. }
    destruct (exit_N fx2 R2 M1 sp xo (L5.bo_fb bx) R XF1 AO2) as (fx3 & R3 & M3 & nMS & nK & nR2 & nR10 & nRS & nM).
    apply (FIN fx3 R3 M3 MAXW). { eapply msteps_trans. exact MB1. exact nMS. } exact nK. exact nR2. exact nR10. exact nRS.
    { intros i _ _. apply nM. } { intros a Ha. rewrite nM. exact Ha. }
    { split. right; right; reflexivity. split. reflexivity. intros. exfalso. clear - LT1' H. lia. } { intros E. exfalso. clear - LT1' E. lia. } }
  assert (GE1' : (ny <= nx)%nat). { unfold branch_taken, bv_ltu in GE1. apply Bool.negb_true_iff in GE1. rewrite !BG.unsigned_lit in GE1 by (clear - LX2 LY2; lia). apply Z.ltb_ge in GE1. lia. }
  (* [comment removed for export] *)
  pose proof (vcmT_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx3 & R3 & M3 & MG3 & tFR & tFZ & (tMS & tKS & tR9)).
  assert (EM3 : M3 = M1). { apply functional_extensionality. exact tFR. } subst M3.
  assert (K3 : forall j, In j (2 :: 8 :: 10 :: 18 :: 19 :: 20 :: KX)%nat -> getr R3 (reg j) = getr R2 (reg j)). { intros j Hj. apply tKS. revert j Hj. kl KS_vcmT. }
  assert (AO3 : at_out R3 sp xo). { unfold at_out. rewrite !(K3 _) by inl. exact AO2. }
  pose proof (br_91ba8 fx3 R3 M1) as MB2. rewrite (K3 18%nat), (K3 10%nat), (K2 18%nat), (K2 10%nat), A18, A10 in MB2 by inl.
  destruct (branch_taken BC_LTU (Z_to_bv 64 (Z.of_nat ny)) (Z_to_bv 64 (Z.of_nat nx))) eqn:LT2.
  - (* [comment removed for export] *)
    assert (LT2' : (ny < nx)%nat). { unfold branch_taken, bv_ltu in LT2. rewrite !BG.unsigned_lit in LT2 by (clear - LX2 LY2; lia). apply Z.ltb_lt in LT2. lia. }
    destruct (exit_P fx3 R3 M1 sp xo (L5.bo_fb bx) R XF1 AO3) as (fx4 & R4 & M4 & pMS & pK & pR2 & pR10 & pRS & pM).
    apply (FIN fx4 R4 M4 1). { eapply msteps_trans. exact MB1. eapply msteps_trans. exact tMS. eapply msteps_trans. exact MB2. exact pMS. }
    { intros x Hx. rewrite (pK x Hx). apply K3. do 6 right. exact Hx. } exact pR2. { rewrite pR10. exact tR9. } exact pRS.
    { intros i _ _. apply pM. } { intros a Ha. rewrite pM. exact Ha. }
    { split. right; left; reflexivity. split. intros; exfalso; clear - LT2' H; lia. reflexivity. } { intros E. exfalso. clear - LT2' E. lia. }
  - (* [comment removed for export] *)
    assert (EQN : nx = ny). { unfold branch_taken, bv_ltu in LT2. rewrite !BG.unsigned_lit in LT2 by (clear - LX2 LY2; lia). apply Z.ltb_ge in LT2. lia. }
    assert (HNX : 1 <= Z.of_nat nx <= 300) by (clear - LX1 LX2; lia).
    pose proof (vcmE_conc fx3 R3 M1 (fun j => match j with 2%nat => sp | 35%nat => Z.of_nat nx | _ => 0 end)) as P. cbn beta iota in P.
    assert (E18 : getr R3 (reg 18) = Z_to_bv 64 (Z.of_nat nx)). { rewrite (K3 18%nat), (K2 18%nat) by inl. exact A18. }
    feed P ltac:(first [apply UR | apply U_to | sc]).
    destruct P as (fx4 & R4 & M4 & MG4 & eFR & eFZ & (eMS & eKS & eR18 & eR21)).
    assert (EM4 : M4 = M1). { apply functional_extensionality. exact eFR. } subst M4.
    assert (K4 : forall j, In j (2 :: 8 :: 9 :: 19 :: 20 :: KX)%nat -> getr R4 (reg j) = getr R3 (reg j)). { intros j Hj. apply eKS. revert j Hj. kl KS_vcmE. }
    assert (AT : at_head R4 sp xo nx).
    { unfold at_head. split. { unfold at_out. rewrite !(K4 _) by inl. exact AO3. } split. { rewrite (K4 9%nat) by inl. exact tR9. } split. exact eR18.
      split. { rewrite (K4 20%nat), (K3 20%nat), (K2 20%nat) by inl. exact A20. } exact eR21. }
    assert (LF1 : lfacts M1 sp xd yd nx).
    { constructor.
      - split. clear - XDR; lia. split. exact XD8. split. { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). clear - XDR HNX; lia. } split. exact XDBIG. clear - XDFR; lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        apply KZ. clear - XDR; unfold SB; lia. clear - XDR HNX; unfold SB; lia. exact XDZ.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        rewrite EQN. split. clear - YDR; lia. split. exact YD8. split. { clear - YDR LY1 LY2; lia. } split. exact YDBIG. clear - YDFR; lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite EQN. apply KZ. clear - YDR; unfold SB; lia. clear - YDR LY1 LY2; unfold SB; lia. exact YDZ.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split. exact VX1. split. exact VY1. split. exact VXZ1. exact VYZ1. }
    assert (LAX1 : L5.limbs_at RSEGS M1 xd wx). { intros i Hi. apply KC. clear - XDR; lia. rewrite NX in Hi. clear - XDR Hi; lia. rewrite NX in Hi. clear - XDFR Hi; lia. apply LAX. exact Hi. }
    assert (LAY1 : L5.limbs_at RSEGS M1 yd wy). { intros i Hi. apply KC. clear - YDR; lia. rewrite NY in Hi. clear - YDR Hi; lia. rewrite NY in Hi. clear - YDFR Hi; lia. apply LAY. exact Hi. }
    destruct (wloop nx fx4 R4 M1 sp xo (L5.bo_fb bx) xd yd R nx wx wy AT ltac:(clear; lia) LX1 LX2 XF1 LF1 XBIG ltac:(clear - XFR; lia) LAX1 LAY1 NX ltac:(rewrite NY; symmetry; exact EQN) WX WY)
      as (fx5 & R5 & M5 & MS5 & K5 & R52 & RES & RS5 & FZ5 & MG5).
    apply (FIN fx5 R5 M5 (L5CMP.cmp_val wx wy)).
    { eapply msteps_trans. exact MB1. eapply msteps_trans. exact tMS. eapply msteps_trans. exact MB2. eapply msteps_trans. exact eMS. exact MS5. }
    { intros x Hx. rewrite (K5 x Hx). rewrite (K4 x) by (do 5 right; exact Hx). apply K3. do 6 right. exact Hx. } exact R52.
    { rewrite RES. rewrite (L5CMP.enc_full wx wy nx NX ltac:(rewrite NY; symmetry; exact EQN) WX WY). reflexivity. } exact RS5. exact FZ5. exact MG5.
    { split. apply L5CMP.cmp_val_cases. split; intros; exfalso; clear - EQN H; lia. } { intros _. reflexivity. }
Qed.

End SCFG_1.
End L5ACMP.
