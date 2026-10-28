(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_membuffer_assign H_membuffer_destroy H_obj HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition httpheader_free_entry := 0x14068%Z.
Ltac sstep := step; fix_lit_store.

Lemma hseg1 : forall (lo H : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m -> (0 <= H /\ H + 88 < 2^64)%Z -> (0 < H)%Z -> (H mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x14090) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz H) s1 (wz (H + 56)) (wz (H + 56)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz membuffer_destroy_entry) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -16) /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz httpheader_free_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI HR NZ AL. unfold httpheader_free_entry, membuffer_destroy_entry.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST. ub_null. ub_align. sstep. sstep. sstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact FR.
Qed.

Lemma hseg2 : forall (H : Z) ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  (0 <= H /\ H + 88 < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x14098) sp gp tp t0 t1 t2 (wz H) s1 (wz (H + 24)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_destroy_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz H) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x14090) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HR. unfold membuffer_destroy_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma hseg3 : forall (lo H : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -16) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> (0 <= H /\ H + 88 < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x17fb0) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz H) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x14098) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR HR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation lbrm k LB := (lb_remove (ai_K_eqb rsegs AI) k LB).
  Hypothesis LOK : layout_ok AI.
  Hypothesis FREEPC : al_free_pc L = 0x17fb0.
  Notation bsub := (bsub AI).
  Notation hdro := (hdro AI).
  Notation hblocks := (hblocks AI).

  Definition httpheader_free_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBK : list BLK) (lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L) [C4 errv'])
      /\ hpx AI [] LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ bsub LBK LB'.

  #[using="AC LOK FREEPC"] Theorem httpheader_free_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK : list BLK) (h : hdr AI) (lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 32 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    hdro m LB h -> bsub LBK LB -> NoDup (map blk_id (hblocks h ++ LBK)) ->
    a0 = wz (hA AI h) ->
    SREACH AI (httpheader_free_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK lo B m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz httpheader_free_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI HD KSUB ND ->.
    destruct h as [H kh id An nlen ncap kn Av vlen vcap kv]. unfold H_obj.hblocks in ND. unfold H_obj.hdro, H_obj.hdro_mem, H_obj.hdro_pure, H_obj.hblocks in HD. cbn in HD, ND |- .
    destruct HD as (([pad HC] & VC & [vbs [VBLK VN]] & NC & [nbs [NBLK NN]]) & (VL & VC5 & NL & NC5 & IDR) & HSUB).
    pose proof (HSUB _ (or_introl eq_refl)) as HIN. pose proof (HSUB _ (or_intror (or_introl eq_refl))) as VIN.
    pose proof (HSUB _ (or_intror (or_intror (or_introl eq_refl)))) as NIN.
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.

    cbn in ND. inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst. inversion ND2 as [|x l NI3 ND3]; subst.
    assert (NE12 : kh <> kv) by (intros E; apply NI1; rewrite E; left).
    assert (NE13 : kh <> kn) by (intros E; apply NI1; rewrite E; right; left).
    assert (NE23 : kv <> kn) by (intros E; apply NI2; rewrite E; left).
    assert (KK : forall b, In b LBK -> blk_id b <> kh /\ blk_id b <> kv /\ blk_id b <> kn).
    { intros b Hb. pose proof (in_map blk_id _ _ Hb) as Hi. apply base.list_elem_of_In in Hi.
      repeat split; intros E; rewrite E in Hi; [apply NI1; right; right; exact Hi| apply NI2; right; exact Hi| apply NI3; exact Hi]. }

    eapply sreach_evt. { eapply (hseg1 lo H); try eassumption; first [lia | (Z.div_mod_to_equations; lia)]. }
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ NC MU1 WM1 ltac:(cbn; lia)) as NC1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ VC MU1 WM1 ltac:(cbn; lia)) as VC1.
    destruct (ai_block_range rsegs AI s LB m _ HR VIN) as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ VBLK MU1 WM1 ltac:(cbn; lia)) as VBLK1.
    assert (HP1 : hpx AI [] LBK (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    clear MU1 WM1.

    eapply sreach_bind.
    { eapply (membuffer_destroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (A := An) (len := nlen) (cap := ncap) (LBrest := lbrm kn LB);
        try eassumption; try reflexivity; rewrite ?unsigned_lit by lia; try lia; try eassumption.
      - eapply (mbloc_block rsegs AI) with (b := (kh, H, 88)); [| cbn; lia| cbn; lia]. apply (in_lb_remove AI); [exact HIN| cbn; congruence].
      - right. exists kn. split; [exact NIN| reflexivity]. }
    intros sx2 LB2 ms2 P. unfold membuffer_destroy_post in P. destruct_exs P. destruct P as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HP2 & -> & HR2 & NC2).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HP2 by lia.
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    replace (ret_pc (Z_to_bv 64 0x14090)) with (Z_to_bv 64 0x14090) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (HIN2 : In (kh, H, 88) (lbrm kn LB)) by (apply (in_lb_remove AI); [exact HIN| cbn; congruence]).
    assert (VIN2 : In (kv, Av, vcap + 1) (lbrm kn LB)) by (apply (in_lb_remove AI); [exact VIN| cbn; congruence]).
    pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 FR1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FR2.
    pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 VC1 ltac:(eapply client_range_block; [exact HIN2| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as VC2.
    destruct (ai_blocks_disjoint rsegs AI s LB m _ _ HR HIN VIN ltac:(congruence)) as [DHV|DHV]; cbn in DHV.
    all: pose proof (rw_cells_bound rsegs _ _ _ VBLK1) as VBB; cbn [cells_size csize Nat.add] in VBB.
    all: assert (CRV : client_range AI (lbrm kn LB) (bv_unsigned sp + -16) Av (Z.of_nat (cells_size [CB (Z.to_nat (vcap + 1)) vbs])))
           by (eapply client_range_block; [exact VIN2| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]).
    all: assert (DJV : disjoint_from [(H + 56, H + 56 + 32)]%Z Av (Z.of_nat (cells_size [CB (Z.to_nat (vcap + 1)) vbs]))) by (cbn [disjoint_from cells_size csize Nat.add]; lia).
    all: pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP2 VBLK1 CRV DJV) as VBLK2.
    all: assert (KSUB2 : bsub LBK (lbrm kn LB)) by (intros b Hb; apply (in_lb_remove AI); [apply KSUB; exact Hb| apply KK; exact Hb]).
    all: assert (HP12 : hpx AI [] LBK (bv_unsigned sp) m m2).
    1,3: eapply (hpx_trans rsegs AI); [exact HP1|]; eapply (hpx_drop rsegs AI); [exact HP2| lia| exact KSUB2|];
         intros a Ha Hc; cbn; split; [| exact I]; intros Hr;
         eapply (fresh_block_not_client rsegs AI _ _ LBK (kh, H, 88) (bv_unsigned sp) m2 a LOK HR2 HIN2); [| lia| cbn; lia| exact Hc];
         intros b0 Hb0; split; [apply KSUB2; exact Hb0|]; intros ->; exact (proj1 (KK _ Hb0) eq_refl).
    all: clear HP1 HP2 FR1 VC1 VBLK1 NC1 ERR1 HE1 HR1 MI1 ST1.

    all: eapply sreach_evt; [eapply (hseg2 H); lia|]; intros ms' ->.
    all: eapply sreach_bind.
    1,3: eapply (membuffer_destroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (A := Av) (len := vlen) (cap := vcap) (LBrest := lbrm kv (lbrm kn LB));
        try eassumption; try reflexivity; rewrite ?unsigned_lit by lia; try lia; try eassumption;
        [ eapply (mbloc_block rsegs AI) with (b := (kh, H, 88)); [| cbn; lia| cbn; lia]; apply (in_lb_remove AI); [exact HIN2| cbn; congruence]
        | right; exists kv; split; [exact VIN2| reflexivity] ].
    all: intros sx3 LB3 ms3 P; unfold membuffer_destroy_post in P; destruct_exs P; destruct P as (-> & MI3 & ST3 & HE3 & [e3 ERR3] & HP3 & -> & HR3 & VC3).
    all: rewrite ?unsigned_lit in ST3 by lia; rewrite ?unsigned_lit in HP3 by lia.
    all: lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
    all: replace (ret_pc (Z_to_bv 64 0x14098)) with (Z_to_bv 64 0x14098) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    all: assert (HIN3 : In (kh, H, 88) (lbrm kv (lbrm kn LB))) by (apply (in_lb_remove AI); [exact HIN2| cbn; congruence]).
    all: pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HP3 FR2 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FR3.
    all: assert (KSUB3 : bsub LBK (lbrm kv (lbrm kn LB))) by (intros b Hb; apply (in_lb_remove AI); [apply KSUB2; exact Hb| apply KK; exact Hb]).
    all: assert (HP13 : hpx AI [] LBK (bv_unsigned sp) m m3).
    1,3: eapply (hpx_trans rsegs AI); [exact HP12|]; eapply (hpx_drop rsegs AI); [exact HP3| lia| exact KSUB3|];
         intros a Ha Hc; cbn; split; [| exact I]; intros Hr;
         eapply (fresh_block_not_client rsegs AI _ _ LBK (kh, H, 88) (bv_unsigned sp) m3 a LOK HR3 HIN3); [| lia| cbn; lia| exact Hc];
         intros b0 Hb0; split; [apply KSUB3; exact Hb0|]; intros ->; exact (proj1 (KK _ Hb0) eq_refl).

    all: eapply sreach_evt; [eapply (hseg3 lo H); try eassumption; lia|]; intros ms' [-> ST4].
    all: eapply sreach_mono.
    1,3: rewrite <- FREEPC; eapply (ac_free rsegs AI AC) with (lo := lo) (B := B); try eassumption; try reflexivity; try lia.
    all: intros sx4 LB4 ms4 P; unfold free_post in P; destruct_exs P; destruct P as (-> & AF & -> & HR4).
    all: destruct AF as (MI4 & ST5 & HE4 & [e4 ERR4] & HPF).
    all: unfold httpheader_free_post; repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|].
    all: split; [exact MI4|]; split; [exact ST5|]; split; [exact HE4|]; split; [eexists; exact ERR4|].
    all: assert (KSUB4 : bsub LBK (lbrm kh (lbrm kv (lbrm kn LB)))) by (intros b Hb; apply (in_lb_remove AI); [apply KSUB3; exact Hb| apply KK; exact Hb]).
    all: split; [| split; [exact HR4| exact KSUB4]].
    all: eapply (hpx_trans rsegs AI); [exact HP13|]; apply hpx_of_heap_pres; eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact KSUB4].
  Qed.
End W.
