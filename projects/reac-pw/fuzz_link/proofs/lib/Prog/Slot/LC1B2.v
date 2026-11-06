(* Segment B2 of the op_write arm (fuzz_link.c:735-751, plain image): model_write's return at
   0x13ff8 through reac_link_alias_write (0x16290), check_socket (0x150e4), the refusal test
   (strlen, index_of, check_refused), check_write and check_requests, to the call of free(own) at
   0x1405c (pc 0x173d4, ra 0x14060). This file walks 0x13ff8-0x1400c and states the segment;
   LC1B2Test.v walks the refusal test and LC1B2Tail.v the rest. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem reac_link_alias_write_c check_socket_c strlen_c index_of_c check_refused_c
  check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LC1Defs LC1Call LC1B2Lib LC1B2Tab LC1B2Rc LC1B2St LC1B2Tail LC1B2Test.
Import ListNotations.
Local Open Scope Z_scope.

Section B2.
Hypothesis ALIAS_WRITE_OK : reac_link_alias_write_contract.
Hypothesis CHECK_SOCKET_OK : check_socket_contract.
Hypothesis STRLEN_OK : strlen_contract.
Hypothesis INDEX_OF_OK : index_of_contract_P.
Hypothesis CHECK_REFUSED_OK : check_refused_contract.
Hypothesis CHECK_WRITE_OK : check_write_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

(* the library's answer and the model's for this write, both over the kernel as it was *)
Lemma c1b2_model_is_norm : forall nb t kbs,
  w_rc (c1_wm nb t kbs) = norm_rc (w_rc (write_lib link_tab (sel_name nb) (Some t) [] (nk_kstate kbs))).
Proof. intros. reflexivity. Qed.

Lemma c1b2_model_reqs : forall nb t kbs,
  w_reqs (c1_wm nb t kbs) = w_reqs (write_lib link_tab (sel_name nb) (Some t) [] (nk_kstate kbs)).
Proof. intros. reflexivity. Qed.

(* 0x13ff8 -> 0x14010: s3 = model's code, the library's write, s6 = its code, check_socket *)
Lemma c1b2_from_mw : forall (E : lenv) (i : Z) (gp : word) (own : Z) (m0 : word -> option byte)
    (ms : machine_state),
  lenv_ok E -> c1_13ff8 E i gp own ms -> seg_fp (e_S E) (c1_hp E) m0 (ms_mem ms) ->
  evt rsegs (eqv_cl (c1b2_post E i gp own m0)) ms.
Proof.
  intros E i gp own m0 ms HE HC FP0.
  destruct HC as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & t3 & t4 & t5 & t6
                  & F & fc & m & P & N & kbs & mbs & gbs & nb & s & t & sl & -> & FRM & Hi & Hnb & HNn
                  & LH & HNS & HMR & HMN & CELLS & OWN & HOWN & AL & MI & TM & ST).
  cbn [ms_mem] in FP0.
  assert (SB : 0x960e0 + 65536 <= e_S E <= 2 ^ 47)
    by (unfold lenv_ok, SLOT_STACK_Z in HE; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (e_S E - SLOT_FRAME)) = e_S E - SLOT_FRAME)
    by (apply unsigned_lit; unfold SLOT_FRAME; lia).
  destruct (c1b2_lh_split E i P N kbs mbs gbs m LH) as [REST NL].
  assert (HGN : gnames_at m)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & X & _); exact X).
  assert (HOD : odd_at m)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & _ & X & _); exact X).
  assert (HIF : ifptrs_at m)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (HM : model_at m (e_md E) mbs)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (HMW : model_wf mbs)
    by (unfold c1b2_rest in REST; destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (HER : wr_at rsegs m A_ERRNO 4).
  { unfold c1b2_rest in REST.
    destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  unfold c1b2_nl in NL. destruct NL as (HK & HKW & HT & HOP0 & HMS0 & HOC & HOL).
  pose proof (c1b2_sel_str m nb Hnb HGN HOD) as HSA.
  pose proof (c1b2_sel_ptr_rng nb Hnb) as HSP.
  pose proof AL as ALc.
  destruct ALc as (AN0 & ABT & ANN & ALT & ASL & AD1 & AD2 & AD3 & AD4 & AD5).
  pose proof (bytes_at_bound rsegs m s (t ++ zb 0 :: sl) ABT) as ABB.
  rewrite length_app in ABB. cbn [length] in ABB.
  replace (t ++ zb 0 :: sl) with ((t ++ [zb 0]) ++ sl) in ABT by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in ABT. destruct ABT as [ABT1 ABT2].
  rewrite length_app in ABT2. cbn [length] in ABT2.
  replace (s + Z.of_nat (length t + 1)) with (s + Z.of_nat (length t) + 1) in ABT2 by lia.
  assert (HAL : str_arg m s (Some t)) by (split; [exact AN0 | split; [exact ABT1 | exact ANN]]).
  assert (KR := c1b2_kst_rng kbs HKW).
  assert (HRL : - 2 ^ 31 <= w_rc (write_lib link_tab (sel_name nb) (Some t) [] (nk_kstate kbs)) < 2 ^ 31).
  { unfold write_lib. destruct KR as (K1 & K2 & K3). apply c1b2_wrc_rng; assumption. }
  assert (HOR : 0 <= nk_opened kbs < 2 ^ 31) by (unfold nlk_wf in HKW; lia).
  unfold wz, C1_MW_RA.
  do 4 step.
  (* ---- reac_link_alias_write (name, alias) ---- *)
  eapply leaf_call_eqv.
  { exact ALIAS_WRITE_OK. }
  { exists kbs, link_tab, (sel_name nb), (Some t). cbv beta.
    unfold frame_apart_gnl, apart_frame.
    rewrite c1b2_spZ, USP, c1b2_errno, c1b2_arg0, c1b2_arg1.
    rewrite (unsigned_lit A_TP) by (unfold A_TP; lia).
    rewrite (unsigned_lit (sel_ptr nb)) by lia. rewrite (unsigned_lit s) by lia.
    split; [exact HK|].
    split; [unfold apart_gnl, A_G_NL, NK_SIZE, SLOT_FRAME; lia|].
    split; [exact HKW|].
    split; [exact HOP0|].
    split; [lia|].
    split; [lia|].
    split; [exact HT|].
    split; [exact HER|].
    split; [unfold A_TP, ERRNO_TP_OFF, SLOT_FRAME; lia|].
    split; [unfold apart_gnl, A_TP, ERRNO_TP_OFF, A_G_NL, NK_SIZE; lia|].
    split; [exact HSA|].
    split; [exact HAL|].
    split.
    { intros k n2 ix p HEk HUp.
      exact (c1b2_ptr_apart m kbs k n2 ix p (e_S E - SLOT_FRAME) 16928 HIF HT HEk HUp
               ltac:(unfold SLOT_FRAME; lia) ltac:(unfold SLOT_FRAME; lia)). }
    split.
    { intros s0 Hs0.
      exact (c1b2_sel_apart nb s0 (e_S E - SLOT_FRAME) 16928 Hnb Hs0
               ltac:(unfold SLOT_FRAME; lia) ltac:(unfold SLOT_FRAME; lia)). }
    split.
    { intros s0 Hs0. injection Hs0 as <-. unfold apart, apart_gnl in *.
      unfold SLOT_STACK_Z, SLOT_FRAME in *. split; lia. }
    { intros s0 Hs0. injection Hs0 as <-. exists sl. split; [exact ABT2 | lia]. } }
  { exact MI. }
  { rewrite USP. exact ST. }
  { rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia. }
  { rewrite USP. unfold SLOT_FRAME. lia. }
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 m1
         (regs1 & HR1 & HP1) MU1 WM1 MI1 ST1.
  specialize (HP1 kbs link_tab (sel_name nb) (Some t) HK HT).
  rewrite c1b2_arg0, c1b2_arg1 in HP1.
  rewrite (unsigned_lit (sel_ptr nb)), (unsigned_lit s) in HP1 by lia.
  specialize (HP1 HSA HAL). cbv zeta in HP1.
  rewrite (c1b2_sent_nil kbs HNS) in HP1.
  destruct HP1 as (HA0 & kbs1 & HK1 & HKW1 & _ & _ & _ & HT1 & _ & _ & _ & HSENT1 & HNSENT1
                   & HOP1 & HMS1 & HDIF1 & HRNG1 & HREF1).
  rewrite HR1, c1b2_g10 in HA0. subst a01.
  cbv beta in MU1. rewrite c1b2_errno, USP in MU1.
  rewrite (unsigned_lit A_TP) in MU1 by (unfold A_TP; lia).
  rewrite USP in ST1.
  assert (HMS1' : nk_misuse kbs1 = 0) by lia.
  assert (HOC1 : nk_opened kbs1 = nk_closed kbs1) by lia.
  assert (HOL1 : nk_opened kbs1 <= 64 * (i + 1)) by lia.
  assert (CAR1 : c1b2_car E i own s t sl P N kbs1 mbs gbs m0 m1).
  { match type of MU1 with munch ?W _ _ => assert (HWIN : c1b2_win E W) end.
    { intros x Hx. apply c1b2_inside3 in Hx. destruct Hx as [H|[H|H]].
      - left. unfold SLOT_STACK_Z, SLOT_FRAME in *. lia.
      - right. left. exact H.
      - right. right. unfold A_ERRNO. exact H. }
    exact (c1b2_car_alias E i own s t sl P N kbs1 mbs gbs m0 m m1 _ HE REST CELLS OWN AL TM FP0
             MU1 WM1 MI1 ST1 HWIN HK1 HKW1 HT1 HOP1 HMS1' HOC1 HOL1). }
  rewrite (ret_pc_even 81928 ltac:(lia) ltac:(reflexivity)).
  unfold wz.
  do 2 step.
  (* ---- check_socket ---- *)
  eapply leaf_call_eqv.
  { exact CHECK_SOCKET_OK. }
  { exists kbs1. split; [exact HK1|]. split; [exact HOP1|]. split; [lia | lia]. }
  { exact MI1. }
  { rewrite USP. exact ST1. }
  { rewrite USP. unfold SLOT_STACK_Z, SLOT_FRAME. lia. }
  { rewrite USP. unfold SLOT_FRAME. lia. }
  intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2
         (regs2 & HR2 & HP2) MU2 WM2 MI2 ST2.
  unfold unchanged in HP2. subst m2.
  rewrite (ret_pc_even 81936 ltac:(lia) ltac:(reflexivity)).
  (* ---- 0x14010: the refusal test ---- *)
  apply (c1b2_test STRLEN_OK INDEX_OF_OK CHECK_REFUSED_OK CHECK_WRITE_OK CHECK_REQUESTS_OK
           E i gp own nb (w_rc (c1_wm nb t kbs)) (nk_opened kbs) s
           (w_rc (write_lib link_tab (sel_name nb) (Some t) [] (nk_kstate kbs))) t sl m0); [exact HE|].
  unfold c1b2_s10. do 16 eexists. exists F, fc, m1, P, N, kbs1, mbs, gbs.
  split; [reflexivity|].
  split; [exact FRM|]. split; [exact Hi|]. split; [exact Hnb|]. split; [exact HNn|].
  split; [apply c1b2_model_is_norm|].
  split; [exact HRL|].
  split; [exact HOR|].
  split.
  { assert (HKL : Z.of_nat (length kbs1) = NK_SIZE) by (destruct HK1 as [_ X]; exact X).
    assert (HML : Z.of_nat (length mbs) = MD_SIZE) by (destruct HM as [_ X]; exact X).
    apply (c1b2_requests_are kbs1 mbs HKW1 HMW HKL HML).
    - rewrite HNSENT1, HMN, c1b2_model_reqs. reflexivity.
    - rewrite HSENT1, HMR, c1b2_model_reqs. reflexivity. }
  split.
  { intros HRF. apply HREF1. destruct HRF as [H|[H|[H|H]]].
    - left. exact H.
    - right. right. left. exact H.
    - right. right. right. left. intros s0 Hs0. injection Hs0 as <-. exact H.
    - right. right. right. right. exact H. }
  exact CAR1.
Qed.

Theorem c1_seg_B2 : forall (E : lenv) (i : Z) (gp : word) (own : Z) (ms : machine_state),
  lenv_ok E -> c1_13ff8 E i gp own ms ->
  evt rsegs (eqv_cl (fun ms' => c1_173d4 E i gp own ms' /\ seg_fp (e_S E) (c1_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp own ms HE HC.
  exact (c1b2_from_mw E i gp own (ms_mem ms) ms HE HC (seg_fp_refl (e_S E) (c1_hp E) (ms_mem ms))).
Qed.

End B2.
