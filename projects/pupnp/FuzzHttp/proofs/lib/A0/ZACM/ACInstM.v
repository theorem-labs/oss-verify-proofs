(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Tac Arr Bytes ZBridge Frame ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF Realize SafeReach Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ NodesLZSound NodesLZMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim LJ PEnv APrimSpec APrimSpec2 ASec AQuar AQuarM AHeap F_quar_E F_quar_P F_free_icpt F_free_null F_malloc_icpt F_realloc_icpt F_alloc_A F_alloc_P F_alloc_S1 F_sec_A AMallocP AMallocL8 AAllocL8 AMallocGL8 AReallocL8 AAllocSL8 ABudgetL8 ABudgetInst AUsedStatic AVaOfM AHeapPg ALinkSec ALinkAvoid AFsEnv
                        ALedger AHeap2 AHeapB AFreeL8 ALinkPg ALinkVm ALink ALinkPrim ALinkFree ALinkFreeIn AVaOf AHeapLaws AHeapInst.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS A0Prog SeamA0.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv) (FI : fs_if) (Bs : vmbase).
Hypothesis AO : alayout_ok AL.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis SP0S : alloc_ceiling + 2^23 + 184 <= 2^47.
Hypothesis BO : base_ok Bs.
Hypothesis SPACE_EQ : vb_space Bs = al_space AL.
Hypothesis SPACE_AL : al_space AL mod 65536 = 0.
Hypothesis SWIN_LO : 65536 <= SWIN (al_depot AL).

Hypothesis FSEI : forall m, thread_env (al_thread AL) m -> AFsEnv.fs_tls_env (at_thr (al_thread AL)) AFsEnv.A0_DTV AFsEnv.A0_TLSB (al_dtls AL) (al_fsb AL) m -> FSENV FI m.

Notation AIB := (AI_B AL E FI Bs AO FSBE SP0S FSEI).
Notation JB := (JA FI AIB).
Notation kept mo mo' := (m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).

#[using="Type"] Lemma mclean_of_seam : forall (H : word -> bool) (m : mem),
  (forall x, H x = true -> m x = None) -> H_off_segments asegs H -> mclean H m.
Proof. intros H m C O. split; assumption. Qed.

Definition malloc_room_prim : Prop := forall s LB (m : mem) c,
  RHEAP_B AL E s LB m -> 1 <= c <= 31 -> p_cnt (get_cls (bs_prim s) c) = 0 ->
  vroom Bs (va_of s) (D_gfa (get_cls (bs_prim s) c) c (max_count c / 2) + D_gfa (get_cls (bs_prim s) c) c (max_count c / 2) / 8 + 4 * page_size).

#[using="BO SPACE_EQ SPACE_AL SWIN_LO"] Lemma ac_malloc_prim : malloc_room_prim ->
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n lo : Z) (ras : list Z),
  RHEAP_B AL E s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top (al_thread AL) ->
  mem_inv asegs m ->
  fpchain m (at_top (al_thread AL)) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  0 <= n <= A0_MAXREQ -> budgetZ s LB n -> a0_need n <= 65536 ->
  AJ FI AIB JB (malloc_post_A FI AIB ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_malloc) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ROOM ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD NP.
  set (c := class_of (a0_need n)) in *. set (P := bs_prim s) in *.
  assert (CR : 1 <= c <= 31).
  { unfold c. rewrite class_of_a0. assert (1 <= a0_need n) by (unfold a0_need; assert (8 <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia);
      assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia); lia). pose proof (a0_class_of_range (a0_need n) ltac:(lia)). lia. }
  assert (LEN : length (pr_cls P) = 32%nat) by (destruct (rheap_pinv AL E s LB m HR) as (LEN & _); exact LEN).
  pose proof (budgetZ_prim s LB n ltac:(lia) NP BUD) as CAP. fold c in CAP.
  assert (AS0 : 0 <= ALLOC_STACK) by (vm_compute; discriminate). assert (AS1 : ALLOC_STACK <= 1888) by (vm_compute; discriminate).
  set (v := va_of s). set (v' := mkVA (va_prim v + D_calloc P c) (va_chunks v) (va_nsec v) (va_aux v)).
  cbn [AJ JA].
  eapply (AJA_of_implL FI AIB (mp_tree AL P n)
            (epostL (micpt_post (al_thread AL) gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra unit
                       (ma8_cpost AL E FI AIB unit (fun _ : unit => (fst (cache_alloc P c), bs_sec s)) 0 q s LB st n m) s0 s1 s2 s3 s4 s5 m))
            (fun mo r mo' => r = Ok tt /\ LINK Bs v' mo' /\ kept mo mo')).
  -
    intros CL HOFF. cbn [ms_mem] in CL.
    exact (malloc_walk AL E FI AIB AO FSBE unit (mp_tree AL P n) (fun _ : unit => (fst (cache_alloc P c), bs_sec s)) 0 ALLOC_STACK AS0 AS1
             gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m st n ras
             HR (mclean_of_seam _ _ CL HOFF) MI AE RF ST CLO LOQ Q16 QTOP CH TRIN NR
             (alloc_prim_L8 AL E FI AIB AO SWIN_LO FSBE (fun lo' hi' X => X) s LB st n (malloc_tr ra ras) q lo CLO TRIN NR NP CAP)).
  -
    intros mo LF VM. cbn [am_vm AI_B] in VM. pose proof (LINK_of_LINKvm Bs _ _ VM) as LK. fold v in LK.
    unfold mp_tree. fold P c. unfold v', D_calloc. destruct (p_cnt (get_cls P c) =? 0) eqn:EC.
    + apply (link_refill Bs AL BO SPACE_EQ SPACE_AL v _ c (get_cls P c)); [exact LK| exact CR| | | |].
      * exact (rheap_wf AL E s LB m HR c CR).
      * exact (rheap_refill_budget AL E s LB m HR c CR).
      * exact (ROOM s LB m c HR CR (proj1 (Z.eqb_eq _ _) EC)).
      * intros mo' LK' KP. split; [reflexivity|]. split; [exact LK'| exact KP].
    + unfold t_none. apply stwf_ret. split; [reflexivity|]. split; [| split; reflexivity].
      assert (EV : forall w : vabs, mkVA (va_prim w + 0) (va_chunks w) (va_nsec w) (va_aux w) = w) by (intros [wa wb wc wd]; cbn; f_equal; lia).
      rewrite EV. exact LK.
  - intros moE r moE' (_ & _ & K1 & K2). split; congruence.
  -
    intros r H' P' msr' moE moE' VM0 QW (-> & LK' & KP). cbn [epostL] in QW.
    destruct (malloc_conv AL E FI AIB unit (fun _ : unit => (fst (cache_alloc P c), bs_sec s)) 0 gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m st n tt H' msr' QW)
      as (s1' & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & A & junk & EMS & GH & EX & EQ & ENS & ELA & MI' & STK' & AE' & RF' & AP' & HR' & NB & NSH & WMo).
    exists (set_pages s1' P'), ((A, A, n) :: LB).
    split; [cbn [am_ghost AI_B]; rewrite set_pages_ghost; pose proof (f_equal fst GH) as GH1; unfold bs_ghost in GH1; cbn [fst] in GH1; rewrite GH1; reflexivity|].
    split.
    { cbn [am_vm AI_B]. rewrite set_pages_va. apply LINKvm_of_LINK.
      rewrite (malloc_prim_va_of s s1' c CR LEN EX ENS). exact LK'. }
    unfold malloc_post_A. exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', A, A, junk.
    split; [exact EMS|]. split.
    { unfold alloc_frame_A. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|].
      apply AP'. intros b Hb. destruct HR as (PLB & _). pose proof (Permutation_in _ PLB Hb) as Hb'.
      apply in_map_iff in Hb' as (r0 & <- & Hr). exists r0. split; [exact Hr|]. split; reflexivity. }
    split; [reflexivity|]. split; [exact (RHEAP_B_set_pages AL E s1' P' _ m' HR')|]. split; [exact NB|]. split; [exact NSH|]. split; [exact WMo|].
    cbn [am_nsec AI_B]. rewrite set_pages_nsec, ENS. rewrite (proj2 (Z.eqb_neq _ _) (a0_cls_prim_nz n ltac:(lia) NP)). reflexivity.
Qed.

Hypothesis REG_BASE : Forall (fun rg => exists e, In e (vb_maps Bs) /\ vlo e <= fst rg /\ fst rg + snd rg <= vhi e) (al_regions AL).

Definition sec_avoid (s : astB) (lo q : Z) : list (Z * Z) :=
  (lo, q) :: map (fun rg => (fst rg, fst rg + snd rg)) (al_regions AL) ++ map (fun c => (fst c, fst c + snd c)) (va_chunks (va_of s)).

Definition malloc_room_sec : Prop := forall s LB (m : mem) n,
  RHEAP_B AL E s LB m -> 0 <= n <= A0_MAXREQ -> 65536 < a0_need n -> budgetZ s LB n ->
  let nm := sec_msize (al_sneed n) in
  vroom Bs (va_of s) (nm + (nm / 8 + 2 * page_size) + 8192 + parr_step_cost) /\ gap_room Bs (va_of s) nm.

#[using="AL"] Lemma sec_msize_facts : forall n, 0 <= n <= A0_MAXREQ -> 65536 < a0_need n ->
  let nm := sec_msize (al_sneed n) in 69632 <= nm /\ nm < 2^64 /\ nm mod 4096 = 0 /\ lenZ nm = nm.
Proof.
  intros n NR NS. cbv zeta. destruct (al_sec_facts n NR NS) as (N1 & _ & ERZ & _ & _ & _ & (rk & NEED & RK & _)).
  assert (B : 69632 <= sec_msize (al_sneed n) < 2^64 /\ sec_msize (al_sneed n) mod 4096 = 0).
  { unfold sec_msize, rup4k, al_sneed. rewrite ERZ, NEED. unfold A0_MAXREQ in NR. clear - RK N1 NR. Z.div_mod_to_equations. lia. }
  destruct B as ((B1 & B2) & B3). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. apply lenZ_id; [lia| exact B3].
Qed.
Hypothesis PARR_BASE : exists e, In e (vb_maps Bs) /\ vlo e <= al_parr AL /\ al_parr AL + 2^23 <= vhi e.

#[using="BO SWIN_LO REG_BASE PARR_BASE"] Lemma ac_malloc_sec : malloc_room_sec ->
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n lo : Z) (ras : list Z),
  RHEAP_B AL E s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top (al_thread AL) ->
  mem_inv asegs m ->
  fpchain m (at_top (al_thread AL)) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  0 <= n <= A0_MAXREQ -> budgetZ s LB n -> 65536 < a0_need n ->
  AJ FI AIB JB (malloc_post_A FI AIB ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_malloc) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ROOM ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD NS.
  destruct (budgetZ_sec AL E s LB m n HR NS BUD) as (WMAX & BC & BB & BN).
  destruct (ROOM s LB m n HR NR NS BUD) as (VR & GR). cbv zeta in VR, GR.
  destruct (sec_msize_facts n NR NS) as (NM1 & NM2 & NM3 & NML). cbv zeta in NM1, NM2, NM3, NML.
  set (S := bs_sec s) in *. set (size := al_sneed n) in *. set (nm := sec_msize size) in *. set (v := va_of s) in *.
  set (avoid := sec_avoid s lo q).
  pose proof HR as (_ & _ & _ & INVB & _). destruct INVB as (_ & _ & RS & _). pose proof RS as ((W0a & W0m & W0b & _) & _). unfold bs_X in W0a, W0m, W0b. cbn [snd] in W0a, W0m, W0b. fold S in W0a, W0m, W0b.
  assert (AS0 : 0 <= ALLOC_STACK) by (vm_compute; discriminate). assert (AS1 : ALLOC_STACK <= 1888) by (vm_compute; discriminate).
  assert (AIN : In (lo, q) avoid) by (left; reflexivity).
  assert (AREG : Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL)).
  { apply Forall_forall. intros rg Hrg. right. apply in_or_app. left. exact (in_map (fun rg0 : Z * Z => (fst rg0, fst rg0 + snd rg0)) _ rg Hrg). }
  assert (ACH : Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks S)).
  { apply Forall_forall. intros c0 Hc0. right. apply in_or_app. right. apply in_map_iff. exists (cpair c0). split; [reflexivity|].
    unfold v, va_of. cbn [va_chunks]. apply in_map. exact Hc0. }
  cbn [AJ JA].
  eapply (AJA_of_implL FI AIB (sec_alloc_tree AL S size avoid)
            (epostL (micpt_post (al_thread AL) gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra Z
                       (ma8_cpost AL E FI AIB Z (fun a : Z => (bs_prim s, sec_alloc S a size)) 1 q s LB st n m) s0 s1 s2 s3 s4 s5 m))
            (fun mo r mo' => exists a, r = Ok a /\ LINK Bs (va_sec_alloc v S a nm) mo' /\ kept mo mo')).
  - intros CL HOFF. cbn [ms_mem] in CL.
    exact (malloc_walk AL E FI AIB AO FSBE Z (sec_alloc_tree AL S size avoid) (fun a : Z => (bs_prim s, sec_alloc S a size)) 1 ALLOC_STACK AS0 AS1
             gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m st n ras
             HR (mclean_of_seam _ _ CL HOFF) MI AE RF ST CLO LOQ Q16 QTOP CH TRIN NR
             (alloc_sec_L8 AL E FI AIB AO SWIN_LO FSBE (fun lo' hi' X => X) s LB st n (malloc_tr ra ras) q lo avoid lo q CLO TRIN NR NS AIN ltac:(lia) ltac:(lia)
                AREG ACH WMAX BC BB BN)).
  - intros mo LF VM. cbn [am_vm AI_B] in VM. pose proof (LINK_of_LINKvm Bs _ _ VM) as LK. fold v in LK.
    apply (link_sec_alloc Bs AL BO v _ S size avoid); [exact LK| cbv zeta; fold nm; rewrite NML; exact NM1| | | | |].
    + exact (link_avoid_ok Bs v _ lo q (al_regions AL) LK CLO REG_BASE).
    + cbv zeta. fold nm. rewrite NML. exact VR.
    + cbv zeta. fold nm. rewrite NML. exact GR.
    + intros EQN. destruct PARR_BASE as (e & EIN & E1 & E2).
      layout_facts AO 1%nat LP. destruct LP as ((PL1 & _) & PCE & _).
      pose proof (Z.div_mod (se_nres S) 16384 ltac:(lia)) as DM. rewrite W0m in DM.
      assert (STEP : 8 * se_nres S + 131072 <= 8388608) by (clear - EQN WMAX W0a DM; lia). change (2^23) with 8388608 in *.
      split; [exists e; split; [exact EIN| clear - E1 E2 STEP W0a; split; lia]|]. clear - PL1 PCE STEP W0a. repeat split; lia.
    + intros a mo' CS CE LK' KP. exists a. split; [reflexivity|]. cbv zeta in LK'. fold nm in LK'. rewrite NML in LK'. split; [exact LK'| exact KP].
  - intros moE r moE' (a & _ & _ & K1 & K2). split; congruence.
  - intros r H' P' msr' moE moE' VM0 QW (a & -> & LK' & KP). cbn [epostL] in QW.
    destruct (malloc_conv AL E FI AIB Z (fun a0 : Z => (bs_prim s, sec_alloc S a0 size)) 1 gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m st n a H' msr' QW)
      as (s1' & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & A & junk & EMS & GH & EX & EQ & ENS & ELA & MI' & STK' & AE' & RF' & AP' & HR' & NB & NSH & WMo).
    exists (set_pages s1' P'), ((A, A, n) :: LB).
    split; [cbn [am_ghost AI_B]; rewrite set_pages_ghost; pose proof (f_equal fst GH) as GH1; unfold bs_ghost in GH1; cbn [fst] in GH1; rewrite GH1; reflexivity|].
    split.
    { cbn [am_vm AI_B]. rewrite set_pages_va. apply LINKvm_of_LINK.
      destruct (malloc_sec_va_of s s1' a size W0m W0a EX ENS) as (VP & VC & VN & VA). cbv zeta in VP, VC, VN, VA. fold S nm v in VP, VC, VN, VA.
      pose proof (LINK_perm Bs _ _ _ LK' VC) as LK2. rewrite VP, VN, VA in LK2. exact LK2. }
    unfold malloc_post_A. exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', A, A, junk.
    split; [exact EMS|]. split.
    { unfold alloc_frame_A. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|].
      apply AP'. intros b Hb. destruct HR as (PLB & _). pose proof (Permutation_in _ PLB Hb) as Hb'.
      apply in_map_iff in Hb' as (r0 & <- & Hr). exists r0. split; [exact Hr|]. split; reflexivity. }
    split; [reflexivity|]. split; [exact (RHEAP_B_set_pages AL E s1' P' _ m' HR')|]. split; [exact NB|]. split; [exact NSH|]. split; [exact WMo|].
    cbn [am_nsec AI_B]. rewrite set_pages_nsec, ENS. rewrite (a0_cls_sec n NS). reflexivity.
Qed.

#[using="BO SPACE_EQ SPACE_AL SWIN_LO REG_BASE PARR_BASE"] Theorem ac_malloc_B : malloc_room_prim -> malloc_room_sec -> malloc_stmt_A FI AIB JB.
Proof.
  intros ROOMP ROOMS. unfold malloc_stmt_A.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN EA0 NR BUD. subst a0.
  change (RHEAP_A FI AIB s LB m) with (RHEAP_B AL E s LB m) in HR.
  change (am_stack_top FI AIB) with (at_top (al_thread AL)) in QTOP, CH.
  change (am_budget FI AIB s LB n) with (budgetZ s LB n) in BUD.
  unfold A0_RT_STACK in LOQ.
  destruct (Z_le_gt_dec (a0_need n) 65536) as [NP|NS].
  - exact (ac_malloc_prim ROOMP ra q gp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
             HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD NP).
  - exact (ac_malloc_sec ROOMS ra q gp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
             HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD ltac:(lia)).
Qed.

#[using="BO SPACE_EQ SPACE_AL SWIN_LO"] Lemma ac_rnull_prim : malloc_room_prim ->
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n lo : Z) (ras : list Z),
  RHEAP_B AL E s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top (al_thread AL) ->
  mem_inv asegs m ->
  fpchain m (at_top (al_thread AL)) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  0 <= n <= A0_MAXREQ -> budgetZ s LB n -> a0_need n <= 65536 ->
  AJ FI AIB JB (malloc_post_A FI AIB ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_realloc) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ROOM ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD NP.
  set (c := class_of (a0_need n)) in *. set (P := bs_prim s) in *.
  assert (CR : 1 <= c <= 31).
  { unfold c. rewrite class_of_a0. assert (1 <= a0_need n) by (unfold a0_need; assert (8 <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia);
      assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia); lia). pose proof (a0_class_of_range (a0_need n) ltac:(lia)). lia. }
  assert (LEN : length (pr_cls P) = 32%nat) by (destruct (rheap_pinv AL E s LB m HR) as (LEN & _); exact LEN).
  pose proof (budgetZ_prim s LB n ltac:(lia) NP BUD) as CAP. fold c in CAP.
  assert (AS0 : 0 <= ALLOC_STACK) by (vm_compute; discriminate). assert (AS1 : ALLOC_STACK <= 1888) by (vm_compute; discriminate).
  set (v := va_of s). set (v' := mkVA (va_prim v + D_calloc P c) (va_chunks v) (va_nsec v) (va_aux v)).
  cbn [AJ JA].
  eapply (AJA_of_implL FI AIB (mp_tree AL P n)
            (epostL (ricpt_post (al_thread AL) gp s7 s8 s9 s10 s11 F_ fc q lo 262144 ra unit
                       (rn8_cpost AL E FI AIB unit (fun _ : unit => (fst (cache_alloc P c), bs_sec s)) 0 q s LB st n m) s0 s1 s2 s3 s4 s5 s6 m))
            (fun mo r mo' => r = Ok tt /\ LINK Bs v' mo' /\ kept mo mo')).
  -
    intros CL HOFF. cbn [ms_mem] in CL.
    exact (realloc_null_walk AL E FI AIB AO FSBE unit (mp_tree AL P n) (fun _ : unit => (fst (cache_alloc P c), bs_sec s)) 0 ALLOC_STACK AS1
             gp s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 s LB m st n ras
             HR (mclean_of_seam _ _ CL HOFF) MI AE RF ST CLO LOQ Q16 QTOP CH TRIN NR
             (alloc_prim_L8 AL E FI AIB AO SWIN_LO FSBE (fun lo' hi' X => X) s LB st n (realloc_tr ra ras) q lo CLO TRIN NR NP CAP)).
  -
    intros mo LF VM. cbn [am_vm AI_B] in VM. pose proof (LINK_of_LINKvm Bs _ _ VM) as LK. fold v in LK.
    unfold mp_tree. fold P c. unfold v', D_calloc. destruct (p_cnt (get_cls P c) =? 0) eqn:EC.
    + apply (link_refill Bs AL BO SPACE_EQ SPACE_AL v _ c (get_cls P c)); [exact LK| exact CR| | | |].
      * exact (rheap_wf AL E s LB m HR c CR).
      * exact (rheap_refill_budget AL E s LB m HR c CR).
      * exact (ROOM s LB m c HR CR (proj1 (Z.eqb_eq _ _) EC)).
      * intros mo' LK' KP. split; [reflexivity|]. split; [exact LK'| exact KP].
    + unfold t_none. apply stwf_ret. split; [reflexivity|]. split; [| split; reflexivity].
      assert (EV : forall w : vabs, mkVA (va_prim w + 0) (va_chunks w) (va_nsec w) (va_aux w) = w) by (intros [wa wb wc wd]; cbn; f_equal; lia).
      rewrite EV. exact LK.
  - intros moE r moE' (_ & _ & K1 & K2). split; congruence.
  -
    intros r H' P' msr' moE moE' VM0 QW (-> & LK' & KP). cbn [epostL] in QW.
    destruct QW as (u0 & u1 & u2 & ua0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mW & m' & W & EMS & MUW & WMW & MU & ABV & STK' & CP).
    destruct CP as (s1' & A & junk & -> & GH & EX & EQ & ENS & ELA & MI' & AE' & RF' & AP' & HR' & NB & NSH & WMo).
    exists (set_pages s1' P'), ((A, A, n) :: LB).
    split; [cbn [am_ghost AI_B]; rewrite set_pages_ghost; pose proof (f_equal fst GH) as GH1; unfold bs_ghost in GH1; cbn [fst] in GH1; rewrite GH1; reflexivity|].
    split.
    { cbn [am_vm AI_B]. rewrite set_pages_va. apply LINKvm_of_LINK.
      rewrite (malloc_prim_va_of s s1' c CR LEN EX ENS). exact LK'. }
    unfold malloc_post_A. exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', A, A, junk.
    split; [exact EMS|]. split.
    { unfold alloc_frame_A. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|].
      apply AP'. intros b Hb. destruct HR as (PLB & _). pose proof (Permutation_in _ PLB Hb) as Hb'.
      apply in_map_iff in Hb' as (r0 & <- & Hr). exists r0. split; [exact Hr|]. split; reflexivity. }
    split; [reflexivity|]. split; [exact (RHEAP_B_set_pages AL E s1' P' _ m' HR')|]. split; [exact NB|]. split; [exact NSH|]. split; [exact WMo|].
    cbn [am_nsec AI_B]. rewrite set_pages_nsec, ENS. rewrite (proj2 (Z.eqb_neq _ _) (a0_cls_prim_nz n ltac:(lia) NP)). reflexivity.
Qed.

#[using="BO SWIN_LO REG_BASE PARR_BASE"] Lemma ac_rnull_sec : malloc_room_sec ->
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n lo : Z) (ras : list Z),
  RHEAP_B AL E s LB m -> asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top (al_thread AL) ->
  mem_inv asegs m ->
  fpchain m (at_top (al_thread AL)) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  0 <= n <= A0_MAXREQ -> budgetZ s LB n -> 65536 < a0_need n ->
  AJ FI AIB JB (malloc_post_A FI AIB ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_realloc) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros ROOM ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD NS.
  destruct (budgetZ_sec AL E s LB m n HR NS BUD) as (WMAX & BC & BB & BN).
  destruct (ROOM s LB m n HR NR NS BUD) as (VR & GR). cbv zeta in VR, GR.
  destruct (sec_msize_facts n NR NS) as (NM1 & NM2 & NM3 & NML). cbv zeta in NM1, NM2, NM3, NML.
  set (S := bs_sec s) in *. set (size := al_sneed n) in *. set (nm := sec_msize size) in *. set (v := va_of s) in *.
  set (avoid := sec_avoid s lo q).
  pose proof HR as (_ & _ & _ & INVB & _). destruct INVB as (_ & _ & RS & _). pose proof RS as ((W0a & W0m & W0b & _) & _). unfold bs_X in W0a, W0m, W0b. cbn [snd] in W0a, W0m, W0b. fold S in W0a, W0m, W0b.
  assert (AS0 : 0 <= ALLOC_STACK) by (vm_compute; discriminate). assert (AS1 : ALLOC_STACK <= 1888) by (vm_compute; discriminate).
  assert (AIN : In (lo, q) avoid) by (left; reflexivity).
  assert (AREG : Forall (fun rg : Z * Z => In (fst rg, fst rg + snd rg) avoid) (al_regions AL)).
  { apply Forall_forall. intros rg Hrg. right. apply in_or_app. left. exact (in_map (fun rg0 : Z * Z => (fst rg0, fst rg0 + snd rg0)) _ rg Hrg). }
  assert (ACH : Forall (fun c => In (sc_beg c, sc_beg c + sc_msize c) avoid) (se_chunks S)).
  { apply Forall_forall. intros c0 Hc0. right. apply in_or_app. right. apply in_map_iff. exists (cpair c0). split; [reflexivity|].
    unfold v, va_of. cbn [va_chunks]. apply in_map. exact Hc0. }
  cbn [AJ JA].
  eapply (AJA_of_implL FI AIB (sec_alloc_tree AL S size avoid)
            (epostL (ricpt_post (al_thread AL) gp s7 s8 s9 s10 s11 F_ fc q lo 262144 ra Z
                       (rn8_cpost AL E FI AIB Z (fun a : Z => (bs_prim s, sec_alloc S a size)) 1 q s LB st n m) s0 s1 s2 s3 s4 s5 s6 m))
            (fun mo r mo' => exists a, r = Ok a /\ LINK Bs (va_sec_alloc v S a nm) mo' /\ kept mo mo')).
  - intros CL HOFF. cbn [ms_mem] in CL.
    exact (realloc_null_walk AL E FI AIB AO FSBE Z (sec_alloc_tree AL S size avoid) (fun a : Z => (bs_prim s, sec_alloc S a size)) 1 ALLOC_STACK AS1
             gp s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 s LB m st n ras
             HR (mclean_of_seam _ _ CL HOFF) MI AE RF ST CLO LOQ Q16 QTOP CH TRIN NR
             (alloc_sec_L8 AL E FI AIB AO SWIN_LO FSBE (fun lo' hi' X => X) s LB st n (realloc_tr ra ras) q lo avoid lo q CLO TRIN NR NS AIN ltac:(lia) ltac:(lia)
                AREG ACH WMAX BC BB BN)).
  - intros mo LF VM. cbn [am_vm AI_B] in VM. pose proof (LINK_of_LINKvm Bs _ _ VM) as LK. fold v in LK.
    apply (link_sec_alloc Bs AL BO v _ S size avoid); [exact LK| cbv zeta; fold nm; rewrite NML; exact NM1| | | | |].
    + exact (link_avoid_ok Bs v _ lo q (al_regions AL) LK CLO REG_BASE).
    + cbv zeta. fold nm. rewrite NML. exact VR.
    + cbv zeta. fold nm. rewrite NML. exact GR.
    + intros EQN. destruct PARR_BASE as (e & EIN & E1 & E2).
      layout_facts AO 1%nat LP. destruct LP as ((PL1 & _) & PCE & _).
      pose proof (Z.div_mod (se_nres S) 16384 ltac:(lia)) as DM. rewrite W0m in DM.
      assert (STEP : 8 * se_nres S + 131072 <= 8388608) by (clear - EQN WMAX W0a DM; lia). change (2^23) with 8388608 in *.
      split; [exists e; split; [exact EIN| clear - E1 E2 STEP W0a; split; lia]|]. clear - PL1 PCE STEP W0a. repeat split; lia.
    + intros a mo' CS CE LK' KP. exists a. split; [reflexivity|]. cbv zeta in LK'. fold nm in LK'. rewrite NML in LK'. split; [exact LK'| exact KP].
  - intros moE r moE' (a & _ & _ & K1 & K2). split; congruence.
  - intros r H' P' msr' moE moE' VM0 QW (a & -> & LK' & KP). cbn [epostL] in QW.
    destruct QW as (u0 & u1 & u2 & ua0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mW & m' & W & EMS & MUW & WMW & MU & ABV & STK' & CP).
    destruct CP as (s1' & A & junk & -> & GH & EX & EQ & ENS & ELA & MI' & AE' & RF' & AP' & HR' & NB & NSH & WMo).
    exists (set_pages s1' P'), ((A, A, n) :: LB).
    split; [cbn [am_ghost AI_B]; rewrite set_pages_ghost; pose proof (f_equal fst GH) as GH1; unfold bs_ghost in GH1; cbn [fst] in GH1; rewrite GH1; reflexivity|].
    split.
    { cbn [am_vm AI_B]. rewrite set_pages_va. apply LINKvm_of_LINK.
      destruct (malloc_sec_va_of s s1' a size W0m W0a EX ENS) as (VP & VC & VN & VA). cbv zeta in VP, VC, VN, VA. fold S nm v in VP, VC, VN, VA.
      pose proof (LINK_perm Bs _ _ _ LK' VC) as LK2. rewrite VP, VN, VA in LK2. exact LK2. }
    unfold malloc_post_A. exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', A, A, junk.
    split; [exact EMS|]. split.
    { unfold alloc_frame_A. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|].
      apply AP'. intros b Hb. destruct HR as (PLB & _). pose proof (Permutation_in _ PLB Hb) as Hb'.
      apply in_map_iff in Hb' as (r0 & <- & Hr). exists r0. split; [exact Hr|]. split; reflexivity. }
    split; [reflexivity|]. split; [exact (RHEAP_B_set_pages AL E s1' P' _ m' HR')|]. split; [exact NB|]. split; [exact NSH|]. split; [exact WMo|].
    cbn [am_nsec AI_B]. rewrite set_pages_nsec, ENS. rewrite (a0_cls_sec n NS). reflexivity.
Qed.

#[using="BO SPACE_EQ SPACE_AL SWIN_LO REG_BASE PARR_BASE"] Theorem ac_realloc_null_B : malloc_room_prim -> malloc_room_sec -> realloc_null_stmt_A FI AIB JB.
Proof.
  intros ROOMP ROOMS. unfold realloc_null_stmt_A.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN EA0 EA1 NR BUD. subst a0 a1.
  change (RHEAP_A FI AIB s LB m) with (RHEAP_B AL E s LB m) in HR.
  change (am_stack_top FI AIB) with (at_top (al_thread AL)) in QTOP, CH.
  change (am_budget FI AIB s LB n) with (budgetZ s LB n) in BUD.
  unfold A0_RT_STACK in LOQ.
  destruct (Z_le_gt_dec (a0_need n) 65536) as [NP|NS].
  - exact (ac_rnull_prim ROOMP ra q gp t0 t1 t2 s0 s1 (wz 0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
             HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD NP).
  - exact (ac_rnull_sec ROOMS ra q gp t0 t1 t2 s0 s1 (wz 0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st n lo ras
             HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN NR BUD ltac:(lia)).
Qed.
End AC.
