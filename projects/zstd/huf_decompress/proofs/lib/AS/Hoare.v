(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (31 recorded proofs replaced by written proofs (at_0, at_addi, at_btgt and 28 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Hoare () := "C47Corelib7Program6Basics4flipK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions4BvWfK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01C45stdpp9bitvector;definitions?bv_add_unsignedK47Corelib4Init5Logic4True01c59OSSVerify5KrLib2AS5Hoare4at_0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic3notC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare6regsetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib2AS5Hoare9mem_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare6memsetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes6option02C46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib2AS5Hoare7at_selfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses5mkrelc59OSSVerify5KrLib2AS5Hoare<u_succ_shiftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare>mem_agree_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib2AS5Hoare6tripleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare4assnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib2AS6CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib2AS5Hoare?regs_agree_monoC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib2AS5Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare>mem_agree_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare?mem_agree_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare9frameableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indK47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z3lorC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z=lor_ldiff_andC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z:ldiff_landc59OSSVerify5KrLib2AS5Hoare<land_m2_evenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare6ret_okC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib2AS5Hoare8ra_indepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare4procC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00c59OSSVerify5KrLib2AS5Hoare?triple_seq_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS5Hoare;triple_loopC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim8to_wexit00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim?msteps_to_wexitC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

Lemma at_0 : forall base, at_ base 0 = base.
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. intros. unfold btgt. apply at_addi. Qed.

(* [comment removed for export] *)
Lemma at_lit : forall (base : word) (d : Z) (a : word),
  Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. intros. assumption. Qed.

(* [comment removed for export] *)
Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

(* [comment removed for export] *)
Lemma u_succ_shift : forall (a : word) (i : Z),
  Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)).
Proof.
  intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. intros W m x _. reflexivity. Qed.

Lemma regs_agree_trans : forall C regs1 regs2 regs3,
  regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

Lemma mem_agree_trans : forall W m1 m2 m3,
  mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

Lemma regs_agree_mono : forall (C C' : regset) regs regs',
  (forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

Lemma mem_agree_mono : forall (W W' : memset) m m',
  (forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.

(* [comment removed for export] *)
Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
  C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

Lemma mem_agree_wbytes : forall (W : memset) m m' a bs,
  (forall i, (0 <= i < Z.of_nat (length bs))%Z -> W (Z_to_bv 64 (bv_unsigned a + i))) ->
  mem_agree W m m' -> mem_agree W m (wbytes m' a bs).
Proof.
  intros W m m' a bs. revert m' a.
  induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
  assert (Ha : W a).
  { specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
  apply IH.
  - intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
  - intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
    + exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
      subst x. exact Ha.
    + apply H, Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop :=
  forall regs mem rom, P regs mem rom ->
    exists regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      /\ Q regs' mem' rom
      /\ regs_agree C regs regs'
      /\ mem_agree W mem mem'.

(* [comment removed for export] *)
Lemma triple_intro : forall segs C W P a b Q,
  (forall regs mem rom, P regs mem rom ->
     exists regs' mem',
       msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
       /\ Q regs' mem' rom
       /\ regs_agree C regs regs'
       /\ mem_agree W mem mem') ->
  triple segs C W P a b Q.
Proof. intros; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof.
  intros segs C W P a regs mem rom HP.
  exists regs, mem. split; [apply mst_refl|].
  split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.

(* [comment removed for export] *)
Lemma triple_seq : forall segs C1 W1 C2 W2 P Q R a b c,
  triple segs C1 W1 P a b Q ->
  triple segs C2 W2 Q b c R ->
  triple segs (fun r => C1 r \/ C2 r) (fun x => W1 x \/ W2 x) P a c R.
Proof.
  intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|]. split.
  - eapply regs_agree_trans;
      [ eapply regs_agree_mono; [|exact Hr1]
      | eapply regs_agree_mono; [|exact Hr2] ]; auto.
  - eapply mem_agree_trans;
      [ eapply mem_agree_mono; [|exact Hm1]
      | eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.

(* [comment removed for export] *)
Lemma triple_conseq : forall segs C C' W W' P P' Q Q' a b,
  triple segs C W P a b Q ->
  (forall regs mem rom, P' regs mem rom -> P regs mem rom) ->
  (forall regs mem rom, Q regs mem rom -> Q' regs mem rom) ->
  (forall r, C r -> C' r) ->
  (forall x, W x -> W' x) ->
  triple segs C' W' P' a b Q'.
Proof.
  intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
  destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
  exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
  split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.

Lemma triple_seq_same : forall segs C W P Q R a b c,
  triple segs C W P a b Q ->
  triple segs C W Q b c R ->
  triple segs C W P a c R.
Proof.
  intros segs C W P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|].
  split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
  forall regs mem rom regs' mem',
    regs_agree C regs regs' -> mem_agree W mem mem' ->
    R regs mem rom -> R regs' mem' rom.

(* [comment removed for export] *)
Lemma triple_frame : forall segs C W P Q R a b,
  triple segs C W P a b Q ->
  frameable C W R ->
  triple segs C W (fun regs mem rom => P regs mem rom /\ R regs mem rom) a b
                  (fun regs mem rom => Q regs mem rom /\ R regs mem rom).
Proof.
  intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split; [exact Hst|].
  split; [split; [exact HQ | eapply HR; eassumption]|].
  split; assumption.
Qed.

(* [comment removed for export] *)
Lemma frameable_and : forall C W R1 R2,
  frameable C W R1 -> frameable C W R2 ->
  frameable C W (fun regs mem rom => R1 regs mem rom /\ R2 regs mem rom).
Proof. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.

Lemma frameable_reg : forall (C : regset) W (r : reg) (v : word),
  ~ C r -> frameable C W (fun regs _ _ => getr regs r = v).
Proof.
  intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
  rewrite (Hr r Hnc). exact Hv.
Qed.

(* [comment removed for export] *)
Lemma frameable_rdn : forall segs (C : regset) (W : memset) (a : word) (n : nat) bs,
  (forall i, (0 <= i < Z.of_nat n)%Z -> ~ W (Z_to_bv 64 (bv_unsigned a + i))) ->
  frameable C W (fun _ mem _ => rdn segs mem a n = Some bs).
Proof.
  intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
  rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
  induction n as [|n IH]; intros a Hdisj; [reflexivity|].
  assert (Ha : ~ W a).
  { specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
  cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
  intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop :=
  forall k : word, ret_ok k ->
    triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

(* [comment removed for export] *)
Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

(* [comment removed for export] *)
Lemma triple_call : forall segs C W P Q callsite entry ret,
  (forall regs mem rom,
     RiscvSemantics.step segs (mkst regs callsite mem rom)
       = MachineOk (mkst (regupd regs 1 ret) entry mem rom)) ->
  ret_ok ret ->
  ra_indep P ->
  proc segs C W P entry Q ->
  triple segs (fun r => C r \/ r = 1) W P callsite ret Q.
Proof.
  intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
  assert (Hpre : P (regupd regs 1 ret) mem rom
                 /\ getr (regupd regs 1 ret) 1 = ret).
  { split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
  destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
    as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split.
  - eapply mst_step; [reflexivity | apply Hjal | exact Hst].
  - split; [exact HQ|]. split; [|exact Hm].
    intros r Hr0.
    assert (HnC : ~ C r) by tauto.
    assert (Hne : r <> 1) by tauto.
    rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_loop : forall segs C W (I : nat -> assn) (hd out : word) (Q : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  forall n, triple segs C W (I n) hd out Q.
Proof.
  intros segs C W I hd out Q Hbody Hexit n.
  induction n as [|n IH]; [exact Hexit|].
  eapply triple_seq_same; [apply Hbody | exact IH].
Qed.

(* [comment removed for export] *)
Lemma triple_loop_measure :
  forall segs C W (I : nat -> assn) (hd out : word) (Q P : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  (forall regs mem rom, P regs mem rom -> exists n, I n regs mem rom) ->
  triple segs C W P hd out Q.
Proof.
  intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
  destruct (Hmeas _ _ _ HP) as (n & HI).
  exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma triple_msteps : forall segs C W P a b Q regs mem rom,
  triple segs C W P a b Q -> P regs mem rom ->
  exists regs' mem',
    msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) /\ Q regs' mem' rom.
Proof.
  intros segs C W P a b Q regs mem rom H HP.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  exists regs', mem'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma triple_wexit : forall segs C W P a b Q bufs code regs mem rom,
  triple segs C W P a b Q ->
  P regs mem rom ->
  (forall regs' mem', Q regs' mem' rom ->
     to_wexit segs (mkst regs' b mem' rom) bufs code) ->
  to_wexit segs (mkst regs a mem rom) bufs code.
Proof.
  intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End WithFP1.

