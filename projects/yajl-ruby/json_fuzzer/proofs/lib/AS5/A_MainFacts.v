(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import
  AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanPlanImages5 HS2Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require MState Mem Cells Step InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_IMG_LO : Z := 0x10000.
Definition A_IMG_HI : Z := 0x603000.

(* [comment removed for export] *)
Definition hs_fact (K : kentry) : bool :=
  existsb (kentry_eqb K) (kn HS_s2_00) && existsb (kentry_eqb K) (kn HS_s2_01)
  && existsb (kentry_eqb K) (kn HS_s2_10) && existsb (kentry_eqb K) (kn HS_s2_11).

(* [comment removed for export] *)
Lemma hs_regs : forall hs, HS_MAIN hs -> s_regs (a_ss hs) = s_regs (a_ss HS_s2_00).
Proof. intros hs [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. Qed.
Lemma hs_fd : forall hs, HS_MAIN hs -> a_fd hs = FdStd.
Proof. intros hs [-> | [-> | [-> | ->]]]; reflexivity. Qed.

Lemma existsb_exists' : forall {T} (f : T -> bool) l, existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  intros T f l. induction l as [|y l IH]; cbn; intros H; [discriminate|].
  apply orb_prop in H as [H|H]; [exists y; auto|]. destruct (IH H) as (x & Hin & Hx). exists x. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint wv_b (A : Z) (n : nat) : bool :=
  match n with O => true | S n' => match wview AImages.asegs (fun _ => None) (Mem.wa A) with Some _ => wv_b (A + 1) n' | None => false end end.
Lemma wv_b_sound : forall n A m, wv_b A n = true -> forall i, 0 <= i < Z.of_nat n -> wview AImages.asegs m (Mem.wa (A + i)) <> None.
Proof.
  induction n as [|n IH]; intros A m H i Hi; [lia|]. cbn [wv_b] in H.
  destruct (wview AImages.asegs (fun _ => None) (Mem.wa A)) as [b|] eqn:Hw; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.add_0_r. unfold wview in *. destruct (m (Mem.wa A)); [discriminate | exact ltac:(rewrite Hw; discriminate)].
  - replace (A + i) with (A + 1 + (i - 1)) by lia. apply (IH (A + 1) m H). lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB : forall m A bs, Mem.bytes_at AImages.asegs m A bs -> Mem.wr_at AImages.asegs m A (Z.of_nat (length bs)) ->
  Step.rw_cells AImages.asegs m A [Cells.CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split; [cbn; exact (conj eq_refl I)|]|]; cbn [Cells.cells_bytes Cells.cbytes Cells.cells_size Cells.csize].
  - rewrite app_nil_r. exact HB. - rewrite Nat.add_0_r. exact HW.
Qed.

Section MainFacts.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 LIM SINV argH fs E hs R FULL model.

  #[local] Notation MR := (Mr ASAN5 argH E hs model FULL).

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  (* [comment removed for export] *)
  Lemma fact_sound : forall K, hs_fact K = true -> kentry_ok ASEGS E MR K.
  Proof.
    intros K HK. unfold hs_fact in HK. apply andb_prop in HK as [HK HK4]. apply andb_prop in HK as [HK HK3]. apply andb_prop in HK as [HK1 HK2].
    assert (Hin : In K (kn hs)).
    { destruct Hhs as [-> | [-> | [-> | ->]]];
        [ apply existsb_exists' in HK1 as (K' & Hin & Heq) | apply existsb_exists' in HK2 as (K' & Hin & Heq)
        | apply existsb_exists' in HK3 as (K' & Hin & Heq) | apply existsb_exists' in HK4 as (K' & Hin & Heq)];
      apply kentry_eqb_eq in Heq; subst K'; exact Hin. }
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin).
  Qed.

  (* [comment removed for export] *)
  Lemma ev_init : forall n, (n < NX0)%nat -> ev E n = ev E0a n.
  Proof. intros n Hn. exact (proj1 (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) n Hn). Qed.

  (* [comment removed for export] *)
  Let Ez : env := Env (ev E) (eb E0a).
  Lemma Ez_agree : env_agree NX0 E0a Ez.
  Proof. split; [intros n Hn; symmetry; exact (ev_init n Hn) | reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma edenot_sp0 : edenot E e_sp0 = sp.
  Proof.
    change (edenot E e_sp0) with (edenot Ez e_sp0).
    rewrite <- (edenot_agree' NX0 E0a Ez e_sp0 Ez_agree (e_sp0_vars NX0 ltac:(unfold NX0; lia))). exact (edenot_e_sp0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
  Qed.
  Lemma uE_sp0 : uE E e_sp0 = usp.
  Proof. unfold uE. rewrite edenot_sp0. reflexivity. Qed.
  Lemma uE_envp : uE E e_envp = usp + 8 * argc + 16.
  Proof.
    change (uE E e_envp) with (uE Ez e_envp). unfold uE.
    rewrite <- (edenot_agree' NX0 E0a Ez e_envp Ez_agree eq_refl). exact (u_e_envp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
  Qed.
  Lemma uE_argc : uE E (EVar V_ARGC) = argc.
  Proof.
    unfold uE. cbn [edenot]. rewrite (ev_init V_ARGC ltac:(unfold V_ARGC, NX0; lia)).
    unfold E0. cbn [ev]. unfold vals0. cbn [nth V_ARGC]. pose proof (AsanInit.len_av APH sp rdraw argv envp uid hw Hva). rewrite u64_lit; unfold argc in *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma reg_is : forall r e, sr_get (s_regs (a_ss HS_s2_00)) r = e -> getr R r = edenot E e.
  Proof. intros r e He. rewrite <- He, <- (hs_regs hs Hhs). exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r). Qed.

  Lemma main_ra : getr R 1 = Z_to_bv 64 0x91610.   Proof. exact (reg_is 1 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_gp : getr R 3 = Z_to_bv 64 0x10800.   Proof. exact (reg_is 3 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_tp : getr R 4 = Z_to_bv 64 0x5e0b10.  Proof. exact (reg_is 4 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s2 : getr R 18 = Z_to_bv 64 0x81aa4.  Proof. exact (reg_is 18 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s4 : getr R 20 = Z_to_bv 64 0.  Proof. exact (reg_is 20 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s5 : getr R 21 = Z_to_bv 64 0.  Proof. exact (reg_is 21 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s6 : getr R 22 = Z_to_bv 64 0.  Proof. exact (reg_is 22 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s7 : getr R 23 = Z_to_bv 64 0.  Proof. exact (reg_is 23 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s8 : getr R 24 = Z_to_bv 64 0.  Proof. exact (reg_is 24 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s9 : getr R 25 = Z_to_bv 64 0.  Proof. exact (reg_is 25 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s10 : getr R 26 = Z_to_bv 64 0.  Proof. exact (reg_is 26 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_s11 : getr R 27 = Z_to_bv 64 0.  Proof. exact (reg_is 27 _ ltac:(vm_compute; reflexivity)). Qed.

  Lemma main_sp : getr R 2 = Z_to_bv 64 (usp + -48).
  Proof.
    rewrite (reg_is 2 (eaddz e_sp0 (-48)) ltac:(vm_compute; reflexivity)). unfold eaddz. rewrite mkAlu_denot. cbn [edenot].
    rewrite edenot_sp0. apply bv_eq. rewrite u_add64, !u_lit64a, Zplus_mod_idemp_r. f_equal.
  Qed.
  Lemma main_a0 : getr R 10 = Z_to_bv 64 argc.
  Proof. rewrite (reg_is 10 (EVar V_ARGC) ltac:(vm_compute; reflexivity)). apply bv_eq. fold (uE E (EVar V_ARGC)). rewrite uE_argc. pose proof (AsanInit.len_av APH sp rdraw argv envp uid hw Hva). rewrite u64_lit; unfold argc in *; lia. Qed.
  Lemma main_s1 : getr R 9 = Z_to_bv 64 argc.
  Proof. rewrite (reg_is 9 (EVar V_ARGC) ltac:(vm_compute; reflexivity)). rewrite <- main_a0. symmetry. exact (reg_is 10 (EVar V_ARGC) ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_a1 : getr R 11 = Z_to_bv 64 (usp + 8).
  Proof.
    rewrite (reg_is 11 (eaddz e_sp0 8) ltac:(vm_compute; reflexivity)). unfold eaddz. rewrite mkAlu_denot. cbn [edenot].
    rewrite edenot_sp0. apply bv_eq. rewrite u_add64, !u_lit64a, Zplus_mod_idemp_r. f_equal.
  Qed.
  Lemma main_s0 : getr R 8 = Z_to_bv 64 (usp + 8).
  Proof. rewrite <- main_a1, (reg_is 8 (eaddz e_sp0 8) ltac:(vm_compute; reflexivity)). symmetry. exact (reg_is 11 _ ltac:(vm_compute; reflexivity)). Qed.
  Lemma main_a2 : getr R 12 = Z_to_bv 64 (usp + 8 * argc + 16).
  Proof.
    rewrite (reg_is 12 e_envp ltac:(vm_compute; reflexivity)).
    pose proof uE_envp as U. unfold uE in U. rewrite <- U. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.
  Lemma main_s3 : getr R 19 = Z_to_bv 64 (usp + 8 * argc + 16).
  Proof. rewrite <- main_a2, (reg_is 19 e_envp ltac:(vm_compute; reflexivity)). symmetry. exact (reg_is 12 _ ltac:(vm_compute; reflexivity)). Qed.

  (* [comment removed for export] *)
  Lemma main_fs : m_fs model = fs.                          Proof. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma main_halted : m_halted model = None.               Proof. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma main_fds : m_fds model = fds_std.
  Proof. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as H. rewrite (hs_fd hs Hhs) in H. exact H. Qed.
  Lemma main_res : vm_reserved (m_vmmaps model) = segments_reserved ASEGS. Proof. exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma main_limit : vm_limit (m_vmmaps model) = LIM.     Proof. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

  (* [comment removed for export] *)
  Lemma Mr_hull : forall a : word, A_IMG_LO <= bv_unsigned a < A_IMG_HI -> MR a = FULL a.
  Proof.
    intros a Ha. unfold A_IMG_LO, A_IMG_HI in Ha. unfold Mr, mrestrict, hid.
    replace (argH E a) with false.
    2: { symmetry. destruct (argH E a) eqn:H; [|reflexivity]. exfalso.
         pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva E a H). unfold AP.CEIL, CEIL in *. lia. }
    unfold vis. replace (in_hull ASAN5 (bv_unsigned a)) with true by (symmetry; unfold in_hull; cbn [img_lo img_hi ASAN5]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    reflexivity.
  Qed.

  Lemma Mr_some0 : forall a b, MR a = Some b -> FULL a = Some b.
  Proof. intros a b H. unfold Mr, mrestrict in H. destruct (hid _ _ _ _ _ a); [discriminate H| exact H]. Qed.

  (* [comment removed for export] *)
  Lemma Mr_none_img : forall a b, MR a = None -> seg_rom ASEGS a = Some b -> FULL a = None.
  Proof.
    intros a b Hm Hs. pose proof (u64_range a).
    destruct (Z_lt_le_dec (bv_unsigned a) A_IMG_LO) as [L|L]; [| destruct (Z_lt_le_dec (bv_unsigned a) A_IMG_HI) as [L2|L2]].
    - exfalso. change ASEGS with AImages.asegs in Hs. rewrite AImageFacts.asan_seg_rom_none in Hs by (unfold A_IMG_LO in L; lia). discriminate Hs.
    - rewrite <- (Mr_hull a) by lia. exact Hm.
    - exfalso. change ASEGS with AImages.asegs in Hs. rewrite AImageFacts.asan_seg_rom_none in Hs by (unfold A_IMG_HI in L2; lia). discriminate Hs.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr : forall n (a : word) l, rdn ASEGS MR a n = Some l -> rdn ASEGS FULL a n = Some l.
  Proof.
    induction n as [|n IH]; intros a l H; [exact H|]. cbn [rdn] in H |- *.
    destruct (MR a) as [b|] eqn:Hm.
    - rewrite (Mr_some0 a b Hm). destruct (rdn ASEGS MR (a + 1) n) as [r|] eqn:Hr; [|discriminate H]. rewrite (IH _ _ Hr). exact H.
    - destruct (seg_rom ASEGS a) as [b|] eqn:Hs; [|discriminate H]. rewrite (Mr_none_img a b Hm Hs).
      destruct (rdn ASEGS MR (a + 1) n) as [r|] eqn:Hr; [|discriminate H]. rewrite (IH _ _ Hr). exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma lit_word : forall a (w : nat) v,
    hs_fact (KWord (SA (ELit 0) a) w (ELit v)) = true -> 0 <= a < 2 ^ 64 ->
    rdn ASEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
  Proof.
    intros a w v HK Ha. pose proof (fact_sound _ HK) as (Hw & _ & Hr). unfold adenot in Hr. cbn [edenot a_base a_off] in Hr.
    apply rdn_Mr. rewrite <- Hr. f_equal. all: apply bv_eq; rewrite ?u_add64, !u_lit64a, ?Zplus_mod_idemp_r; f_equal; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma lit_eword : forall a (w : nat) e,
    hs_fact (KWord (SA (ELit 0) a) w e) = true -> 0 <= a < 2 ^ 64 ->
    rdn ASEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E e)).
  Proof.
    intros a w e HK Ha. pose proof (fact_sound _ HK) as (Hw & _ & Hr). unfold adenot in Hr. cbn [edenot a_base a_off] in Hr.
    apply rdn_Mr. rewrite <- Hr. f_equal. all: apply bv_eq; rewrite ?u_add64, !u_lit64a, ?Zplus_mod_idemp_r; f_equal; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma range_fact : forall e lo hi, hs_fact (KRange e lo hi) = true -> lo <= bv_unsigned (edenot E e) <= hi.
  Proof. intros e lo hi HK. pose proof (fact_sound _ HK) as [H1 H2]. cbn [kentry_ok] in H1, H2. lia. Qed.

  Lemma lit_zero : forall a n,
    hs_fact (KZero (SA (ELit 0) a) (ELit n)) = true -> 0 < a -> a + n <= 2 ^ 64 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros a n HK Hlo Hhi i Hi. pose proof (fact_sound _ HK) as [_ Hz]. unfold estart, elenZ in Hz. cbn [edenot a_base a_off] in Hz.
    rewrite !u64_lit in Hz by lia. apply Mr_some0. replace (a + i) with (0 + a + i) by lia. apply Hz. lia.
  Qed.
  Lemma lit_fill : forall a n c,
    hs_fact (KFill (SA (ELit 0) a) (ELit n) c) = true -> 0 < a -> a + n <= 2 ^ 64 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 c).
  Proof.
    intros a n c HK Hlo Hhi i Hi. pose proof (fact_sound _ HK) as [_ Hz]. unfold estart, elenZ in Hz. cbn [edenot a_base a_off] in Hz.
    rewrite !u64_lit in Hz by lia. apply Mr_some0. replace (a + i) with (0 + a + i) by lia. apply Hz. lia.
  Qed.

  Lemma hull_word : forall a (w : nat) v,
    hs_fact (KWord (SA (ELit 0) a) w (ELit v)) = true ->
    A_IMG_LO <= a -> a + Z.of_nat w <= A_IMG_HI ->
    rdn ASEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
  Proof.
    intros a w v HK Hlo Hhi. unfold A_IMG_LO, A_IMG_HI in Hlo, Hhi.
    pose proof (fact_sound _ HK) as (Hw & _ & Hr). unfold adenot in Hr. cbn [edenot a_base a_off] in Hr.
    rewrite (rdn_ext ASEGS w FULL MR (Z_to_bv 64 a)); [| rewrite u64_lit; lia | intros x Hx; symmetry; apply Mr_hull; unfold A_IMG_LO, A_IMG_HI; rewrite u64_lit in Hx; lia].
    rewrite <- Hr. f_equal. all: apply bv_eq; rewrite ?u_add64, !u_lit64a, ?Zplus_mod_idemp_r; f_equal; lia.
  Qed.

  Lemma hull_zero : forall a n,
    hs_fact (KZero (SA (ELit 0) a) (ELit n)) = true ->
    A_IMG_LO <= a -> a + n <= A_IMG_HI ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros a n HK Hlo Hhi i Hi. unfold A_IMG_LO, A_IMG_HI in Hlo, Hhi.
    pose proof (fact_sound _ HK) as [_ Hz]. unfold estart, elenZ in Hz. cbn [edenot a_base a_off] in Hz.
    rewrite !u64_lit in Hz by lia. rewrite <- (Mr_hull (Z_to_bv 64 (a + i))) by (unfold A_IMG_LO, A_IMG_HI; rewrite u64_lit; lia).
    replace (a + i) with (0 + a + i) by lia. apply Hz. lia.
  Qed.

  Lemma hull_fill : forall a n c,
    hs_fact (KFill (SA (ELit 0) a) (ELit n) c) = true ->
    A_IMG_LO <= a -> a + n <= A_IMG_HI ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 c).
  Proof.
    intros a n c HK Hlo Hhi i Hi. unfold A_IMG_LO, A_IMG_HI in Hlo, Hhi.
    pose proof (fact_sound _ HK) as [_ Hz]. unfold estart, elenZ in Hz. cbn [edenot a_base a_off] in Hz.
    rewrite !u64_lit in Hz by lia. rewrite <- (Mr_hull (Z_to_bv 64 (a + i))) by (unfold A_IMG_LO, A_IMG_HI; rewrite u64_lit; lia).
    replace (a + i) with (0 + a + i) by lia. apply Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hull_img : forall lo hi,
    hs_fact (KImg lo hi) = true -> A_IMG_LO <= lo -> hi <= A_IMG_HI ->
    forall i, lo <= i < hi -> FULL (Z_to_bv 64 i) = None.
  Proof.
    intros lo hi HK Hlo Hhi i Hi. unfold A_IMG_LO, A_IMG_HI in Hlo, Hhi. pose proof (fact_sound _ HK) as (_ & _ & Hn).
    rewrite <- (Mr_hull (Z_to_bv 64 i)) by (unfold A_IMG_LO, A_IMG_HI; rewrite u64_lit; lia). apply Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_word : forall off (w : nat) v,
    hs_fact (KWord (SA e_sp0 off) w (ELit v)) = true ->
    rdn ASEGS MR (Z_to_bv 64 (usp + off)) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
  Proof.
    intros off w v HK. pose proof (fact_sound _ HK) as (Hw & _ & Hr). unfold adenot in Hr. cbn [edenot a_base a_off] in Hr.
    rewrite edenot_sp0 in Hr. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma high_mrd : forall x b, A_IMG_HI <= bv_unsigned x -> MR x = Some b ->
    Mem.mrd AImages.asegs FULL x = Some b /\ wview AImages.asegs FULL x <> None.
  Proof.
    intros x b Hx Hm. unfold A_IMG_HI in Hx. apply Mr_some0 in Hm. unfold Mem.mrd. rewrite Hm. split; [reflexivity|].
    rewrite (AImageFacts.asan_wview_overlay FULL x) by lia. rewrite Hm. discriminate.
  Qed.

  Lemma high_bytes_at : forall a bs, A_IMG_HI <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
    Mem.bytes_at AImages.asegs MR a bs -> Mem.bytes_at AImages.asegs FULL a bs /\ Mem.wr_at AImages.asegs FULL a (Z.of_nat (length bs)).
  Proof.
    intros a bs Ha Hb (B0 & B1 & B2). unfold A_IMG_HI in Ha.
    assert (P : forall i, (i < length bs)%nat -> exists b, MR (Mem.wa (a + Z.of_nat i)) = Some b /\ nth_error bs i = Some b).
    { intros i Hi. specialize (B2 i Hi). unfold Mem.mrd in B2.
      destruct (MR (Mem.wa (a + Z.of_nat i))) as [b|] eqn:Hm; [exists b; split; [reflexivity | symmetry; exact B2]|].
      exfalso. rewrite AImageFacts.asan_seg_rom_none in B2 by (unfold Mem.wa; rewrite u64_lit by lia; lia).
      symmetry in B2. apply nth_error_None in B2. lia. }
    split.
    - split; [exact B0|]. split; [exact B1|]. intros i Hi. destruct (P i Hi) as (b & Hm & Hn). rewrite Hn.
      apply (proj1 (high_mrd (Mem.wa (a + Z.of_nat i)) b ltac:(unfold A_IMG_HI, Mem.wa; rewrite u64_lit by lia; lia) Hm)).
    - split; [lia|]. split; [lia|]. intros i Hi. destruct (P (Z.to_nat i) ltac:(lia)) as (b & Hm & _).
      rewrite Z2Nat.id in Hm by lia. exact (proj2 (high_mrd (Mem.wa (a + i)) b ltac:(unfold A_IMG_HI, Mem.wa; rewrite u64_lit by lia; lia) Hm)).
  Qed.

End MainFacts.

(* [comment removed for export] *)
Module LibBridge.
#[local] Notation LSEGROM := (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.PropExec.seg_rom).
#[local] Notation LRDN := (OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.PropExec.rdn).

Lemma asegs_eq : AImages.asegs = ASEGS.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cfg_of_MS : forall R pc FULL model,
  cfg_of ASEGS R pc FULL model = mkCfg (MState.MS R bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None FULL (LSEGROM ASEGS)) model.
Proof. reflexivity. Qed.

Lemma rdn_lib : forall m a n, rdn ASEGS m a n = LRDN ASEGS m a n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_bytes_at : forall m bs a,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  LRDN ASEGS m (Mem.wa a) (length bs) = Some bs -> Mem.bytes_at ASEGS m a bs.
Proof.
  intros m bs. induction bs as [|b bs IH]; intros a Ha Hb Hr.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in Hb, Hr. rewrite Mem.rdn_unfold in Hr.
    destruct (Mem.mrd ASEGS m (Mem.wa a)) as [b'|] eqn:Hm; [|discriminate].
    destruct (LRDN ASEGS m (Mem.wa a + 1)%bv (length bs)) as [r|] eqn:Hr'; [|discriminate].
    injection Hr as <- <-.
    rewrite Mem.wa_succ in Hr'. specialize (IH (a + 1) ltac:(lia) ltac:(cbn [length] in *; lia) Hr') as (_ & _ & IHi).
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hm.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IHi. cbn [length] in Hi. lia.
Qed.

Section B.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 AsanInit.LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E hs R FULL model.

  (* [comment removed for export] *)
  Lemma hull_word_bytes_at : forall a (w : nat) v bs,
    hs_fact (KWord (SA (ELit 0) a) w (ELit v)) = true ->
    A_IMG_LO <= a -> a + Z.of_nat w <= A_IMG_HI ->
    word_to_le_bytes w (Z_to_bv 64 v) = bs ->
    Mem.bytes_at ASEGS FULL a bs.
  Proof.
    intros a w v bs HK Hlo Hhi Hbs.
    pose proof (hull_word sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC a w v HK Hlo Hhi) as Hr.
    rewrite Hbs, rdn_lib in Hr.
    assert (Hlen : length bs = w) by (rewrite <- Hbs; apply CatExec.length_N_to_le_bytes).
    subst w. unfold A_IMG_LO, A_IMG_HI in Hlo, Hhi. apply rdn_bytes_at; [lia | lia | exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma img_word_rw_cells : forall a (w : nat) v,
    hs_fact (KWord (SA (ELit 0) a) w (ELit v)) = true -> A_IMG_LO <= a -> a + Z.of_nat w <= A_IMG_HI -> wv_b a w = true ->
    Step.rw_cells AImages.asegs FULL a [Cells.CB w (word_to_le_bytes w (Z_to_bv 64 v))].
  Proof.
    intros a w v HK H1 H2 HW.
    pose proof (hull_word_bytes_at a w v _ HK H1 H2 eq_refl) as HB.
    pose proof (CatExec.length_N_to_le_bytes w (Z_to_bv 64 v)) as LEN. rewrite <- LEN at 1. apply rw_cells_CB; [exact HB|].
    rewrite LEN. unfold A_IMG_LO, A_IMG_HI in H1, H2. split; [lia|]. split; [lia|]. intros i Hi. apply (wv_b_sound w a FULL HW). exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma img_eword_rw_cells : forall a (w : nat) e,
    hs_fact (KWord (SA (ELit 0) a) w e) = true -> A_IMG_LO <= a -> a + Z.of_nat w <= A_IMG_HI -> wv_b a w = true ->
    Step.rw_cells AImages.asegs FULL a [Cells.CB w (word_to_le_bytes w (edenot E e))].
  Proof.
    intros a w e HK H1 H2 HW. unfold A_IMG_LO, A_IMG_HI in H1, H2.
    pose proof (lit_eword sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC a w e HK ltac:(lia)) as Hr. rewrite rdn_lib in Hr.
    pose proof (CatExec.length_N_to_le_bytes w (edenot E e)) as LEN.
    pose proof (rdn_bytes_at FULL (word_to_le_bytes w (edenot E e)) a ltac:(lia) ltac:(rewrite LEN; lia)) as HB. rewrite LEN in HB. specialize (HB Hr).
    rewrite <- LEN at 1. apply rw_cells_CB; [exact HB|].
    rewrite LEN. split; [lia|]. split; [lia|]. intros i Hi. apply (wv_b_sound w a FULL HW). exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma img_untouched_rw_cells : forall lo hi a bs,
    hs_fact (KImg lo hi) = true -> A_IMG_LO <= lo -> hi <= A_IMG_HI -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
    InitMem.rw_bytes_b AImages.asegs a bs = true ->
    Step.rw_cells AImages.asegs FULL a [Cells.CB (length bs) bs].
  Proof.
    intros lo hi a bs HK H1 H2 H3 H4 HB. unfold A_IMG_LO, A_IMG_HI in H1, H2. apply InitMem.rw_cells_image0; [| exact HB | lia | lia].
    intros x Hx. rewrite <- (MState.Z_to_bv_bv_unsigned x).
    apply (hull_img sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC lo hi HK); unfold A_IMG_LO, A_IMG_HI; lia.
  Qed.
End B.
End LibBridge.
