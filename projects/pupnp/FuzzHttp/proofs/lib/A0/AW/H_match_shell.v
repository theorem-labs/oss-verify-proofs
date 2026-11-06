(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import FsEnvKit.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 300.

Definition match_entry := 0x87f94%Z.
Definition vfmatch_entry := 0x86a94%Z.

Definition match_q (sp : Z) : Z := sp - 128 - (sp - 128) mod 32.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.

Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

#[using="Type"] Lemma align_frame : forall m lo sp q junk junk2 (s4 s3 s2 s1 s0 ra : word),
  stk asegs m lo (sp + -128) -> lo + 16 <= sp + -128 ->
  rw_cells asegs m (sp + -128) [C8 (Z_to_bv 64 0); CB 24 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; CB 48 junk2] ->
  (q = sp + -128 \/ q = sp + -144) ->
  stk asegs m lo q /\ (exists jq, rw_cells asegs m q [CB 32 jq]) /\ stk asegs m (q + 32) (sp + -96)
  /\ rw_cells asegs m (sp + -96) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; CB 48 junk2].
Proof.
  intros until ra. intros ST LO FR Hq.
  pose proof (rw_cells_bound asegs _ _ _ FR) as B. cbn [cells_size csize Nat.add] in B.
  destruct Hq as [-> | ->].
  - split; [exact ST|].
    split_chunk FR 2%nat Q FRhi. replace (sp + -128 + 32) with (sp + -96) in FRhi by lia.
    split; [exact (rw_cells_forget asegs _ _ _ Q)|]. split; [| exact FRhi].
    replace (sp + -128 + 32) with (sp + -96) by lia. apply stk_empty. lia.
  - destruct (stk_carve asegs m lo (sp + -128) 16 ST ltac:(lia)) as [ST' [pj PAD]].
    replace (sp + -128 - Z.of_nat 16) with (sp + -144) in ST', PAD by lia.
    split; [exact ST'|].
    apply (rw_cells_split_CB asegs m (sp + -128) [C8 (Z_to_bv 64 0)] 24 junk _ [8%nat; 16%nat]) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    split_chunk FR 2%nat Qb R. split_chunk R 1%nat GAP FRhi.
    replace (sp + -128 + 16 + 16) with (sp + -96) in FRhi by lia.
    split; [| split; [| exact FRhi]].
    + lazymatch type of Qb with rw_cells _ _ _ ?cs => pose proof (proj2 (rw_cells_app asegs m (sp + -144) [CB 16 pj] cs)) as J end.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in J.
      try change (Z.of_nat 16) with 16%Z in J. replace (sp + -144 + 16) with (sp + -128) in J by lia. specialize (J (conj PAD Qb)). cbn [app] in J.
      exact (rw_cells_forget asegs _ _ _ J).
    + pose proof (stk_of_rw_cells asegs _ _ _ GAP) as G. cbn [cells_size csize Nat.add] in G. try change (Z.of_nat 16) with 16%Z in G.
      lazymatch type of G with stk _ _ ?a ?b => replace (sp + -144 + 32) with a by lia; replace (sp + -96) with b by lia end. exact G.
Qed.

Section SHELL.

  Variables (st : fsstate FI) (Wx : list ivl) (lo S fmt : Z) (X : mem -> Z -> Prop).
  Let F := fs_F FI st 0.  Let FL := fs_FL FI st 0.  Let st1 := fs_next FI st 0.

  Definition vf_post_A (q spv : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m1 : mem)
      : machine_state -> Prop :=
    fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 (st2 : fsstate FI),
      ms' = MS (mkR (wz 0x880a8) (wz q) gp tp t0 t1 t2 (wz (spv + -48)) (wz q) (wz r) a1 a2 a3 a4 a5 a6 a7
                   (wz F) (wz (sh F)) (wz F) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (ret_pc (wz 0x880a8)) fc None m2 (seg_rom asegs)
      /\ munch ((lo, q) :: FSIV Wx) m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2
      /\ fkeep FI Wx st1 m1 m2 /\ fs_live FI st2 = fs_live FI st1 /\ RFAKE FI st2 m2
      /\ stk asegs m2 lo q /\ asan_env asegs m2 /\ X m2 r.

  Definition vf_body_A (spv : Z) (m : mem) (gp tp : word) (va2 va3 va4 va5 va6 va7 : word) : Prop :=
    forall (m1 : mem), let q := match_q spv in
      munch ((lo, spv) :: FSIV []) m m1 -> wmono asegs m m1 -> fkeep FI [] st m m1 ->
      stk asegs m1 lo q -> mem_inv asegs m1 -> asan_env asegs m1 -> RFAKE FI st1 m1 -> fs_call_ok FI st1 tp 1 ->
      FSENV FI m1 ->
      fs_live FI st1 = fs_newff FI st 0 :: fs_live FI st ->
      forall t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc,
      rw_cells asegs m1 (spv + -48) [C8 va2; C8 va3; C8 va4; C8 va5; C8 va6; C8 va7] ->
      evt asegs (vf_post_A q spv gp tp s5 s6 s7 s8 s9 s10 s11 F_ fc m1)
        (MS (mkR (wz 0x880a8) (wz q) gp tp t0 t1 t2 (wz (spv + -48)) (wz q) (wz S) (wz fmt) (wz (spv + -48)) a3 a4 a5 a6 a7
                 (wz F) (wz (sh F)) (wz F) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz vfmatch_entry) fc None m1 (seg_rom asegs)).

  Definition match_post_A (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch ((lo, bv_unsigned sp) :: FSIV Wx) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ fkeep FI Wx st m m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ asan_env asegs m'
      /\ X m' r.

  Definition X_framed : Prop := forall m m' r, X m r -> munch [(F, F + 64); (sh F, sh F + 8); (FL, FL + 1)] m m' -> wmono asegs m m' -> X m' r.

  #[using="STACK_MALLOC_0"] Lemma match_shell_A : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc m,
    vf_body_A (bv_unsigned sp) m gp tp a2 a3 a4 a5 a6 a7 -> X_framed ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 4240 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m -> fs_call_ok FI st tp 2 ->
    FSENV FI m ->
    disjoint_from Wx (bv_unsigned sp + -144) 144 ->
    disjoint_from Wx F 64 -> disjoint_from Wx (sh F) 8 -> disjoint_from Wx FL 1 ->
    evt asegs (match_post_A ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz fmt) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros BODY XFR ST CLO LO AL16 MI AG RF FCO2 FE DJ DJF DJS DJL.
    pose proof (conj I FE) as FEh.
    pose proof (fs_call_ok_le FI _ _ _ 1%nat FCO2 ltac:(lia)) as FCO1. unfold match_entry, X_framed in *.
    pose proof (word_lt64 sp) as SPB. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.

    pose proof (fsb_ok FI) as (FSB1 & FSB2 & FSB3 & FSB4). unfold app_mem in FSB3.
    assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    unfold vf_body_A in BODY.
    pose (SF := sh F). assert (ESF1 : sh F = SF) by reflexivity. assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    change (sh F) with SF in BODY. clearbody SF.
    destruct (new_frame_facts FI st 0 m F SF FL RF ltac:(lia) eq_refl (eq_sym ESF1) eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    pose proof (new_frame_fk FI st 0 m F SF FL RF ltac:(lia) eq_refl (eq_sym ESF1) eq_refl) as NFK.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: FSIV Wx) m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: FSIV []) m) as MU1.

    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (fkeep_refl FI [] st m) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
    carve_frame 128%nat ST.
    step. sstep. sstep. sstep. sstep. sstep. sstep. sstep.
    step.
    step.
    rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. rewrite land_align32 by lia.

    remember (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32)%Z as q eqn:Eq0.
    assert (Hq : q = bv_unsigned sp + -128 \/ q = bv_unsigned sp + -144) by (subst q; clear -AL16 SPB; Z.div_mod_to_equations; lia).
    assert (EQ : match_q (bv_unsigned sp) = q) by (subst q; unfold match_q; clear -AL16 SPB; Z.div_mod_to_equations; lia).
    clear Eq0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (align_frame mm lo (bv_unsigned sp) q _ _ _ _ _ _ _ _ ST ltac:(lia) FR Hq) as (STq & (jq & Q) & GAP & FRhi) end.
    clear ST FR. rename STq into ST.
    step.
    step. step. step. step.
    sstep. sstep.
    step. step.
    sstep. sstep. sstep. sstep.
    step.   lit_branch.
    step. step. step.
    step.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    call (STACK_MALLOC_0 st lo q 64 F SF FL 64 24%nat 8%nat).
    all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
    match goal with A : asan_env asegs _ |- _ => clear AE; rename A into AE end.
    match goal with R : RFAKE FI _ _ |- _ => rename R into RF end.
    match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
    match goal with K : fkeep FI [] st _ _ |- _ => rename K into FKc end.
    match goal with P : rw_cells asegs _ F _ |- _ => rename P into FRF end.
    match goal with P : rw_cells asegs _ SF _ |- _ => rename P into SHF; shadow_cells_lit SHF end.
    match goal with P : rw_cells asegs _ FL _ |- _ => rename P into FLG end.
    pose proof (fs_call_ok_push FI st st1 tp 1%nat _ FCO2 LIVE1) as FCOB. clear FCO1 FCO2.
    fs_after_call FI FK FKc LSUB LIVE1 [(lo, bv_unsigned sp); (F, F + 64); (SF, SF + 8)]%Z.

    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 0)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 0)) with FL in LVL. rewrite ESF1 in LVS.
    step. step. step. step.
    step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
    sstep.
    step. step. step. step. step. step. step. step.

    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
      by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; lia).
    sstep. sstep. sstep.
    step.
    sstep.
    sstep. sstep. sstep.
    step.
    sstep. sstep. sstep. sstep.
    step.
    sstep.
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    split_chunk FRhi 6%nat FRlo VA.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (BODY mm MU1 WM FK) as B;
      assert (FEB : FSENV FI mm) by (exact (fsenv_FSIV FI [] lo _ m mm (proj2 FEh) MU1 CLO (Forall_nil _))) end.
    cbn zeta in B. rewrite EQ in B. clear BODY MU1.
    apply (fkeep_weaken FI [] Wx st st) in FK; [| sub_fp_solve| intros g Hg; exact Hg].
    call B.
    all: side (try (first [ eassumption | reflexivity | lia ])).
    clear B AE.
    match goal with K : fkeep FI Wx st1 _ _ |- _ => rename K into FKc end.
    match goal with E : fs_live FI _ = fs_live FI st1 |- _ => rename E into LIVE2 end.
    match goal with R : RFAKE FI _ _ |- _ => rename R into RF end.
    match goal with A : asan_env asegs _ |- _ => rename A into AE end.
    match goal with P : X _ _ |- _ => rename P into HX end.
    fs_after_call FI FK FKc LSUB LIVE2 [(lo, bv_unsigned sp); (F, F + 64); (SF, SF + 8)]%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(F, F + 64); (sh F, sh F + 8); (FL, FL + 1)]%Z mm) as MUX;
      pose proof (wmono_refl asegs mm) as WMX end.

    rewrite ESF1.
    step. sstep.
    step. step. sstep.
    step.   if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
    step.
    sstep. sstep. sstep. sstep. sstep. sstep. sstep. sstep.
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    sstep.
    env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.
    lazymatch type of RF with RFAKE _ ?st2 ?mb =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (LIVE2' : fs_live FI st2 = fs_newff FI st 0 :: fs_live FI st) by (rewrite LIVE2; exact LIVE1);
      assert (SHF' : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 0))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 0))))))
        by (change (ff_addr (fs_newff FI st 0)) with F; rewrite ESF1; unfold ff_shsize; rewrite FCLS; exact SHF);
      destruct (release FI st2 (fs_newff FI st 0) (fs_live FI st) mb mc _ RF LIVE2' MU0 WM0 FLG SHF' FRF
                  ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
    end end.
    clear RF MU0 WM0 SHF'.
    step.   step.
    step. step. step. step. step. step.
    step.   step.

    join_chunks FRlo VA FRhi.
    match goal with P : stk asegs _ lo q |- _ => release_frame Q P (q + 32)%Z end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with A : stk asegs mm lo (q + 32)%Z, B : stk asegs mm (q + 32)%Z _ |- _ =>
        pose proof (stk_merge asegs mm _ _ _ A B ltac:(lia)) as STm; clear A B end end.
    release_frame FRhi STm (bv_unsigned sp).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : X ?m2 ?r |- _ => assert (HX' : X mm r) by (eapply XFR; [exact H | exact MUX | exact WMX]) end end.
    finish.
    { rewrite LIVE3. reflexivity. }
    { exact RF3. }
  Qed.
End SHELL.
End W.
