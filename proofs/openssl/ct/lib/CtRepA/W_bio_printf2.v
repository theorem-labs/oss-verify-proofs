(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_ctrl W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition BIO_PRINTF_A : Z := 0x23ac0c.      (* [comment removed for export] *)
Definition BPRF_VPF_RA : Z := 0x23ad24.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_PRINTF_NULL_STACK : Z := BPRF_FRAME + BIO_VPRINTF_NULL_STACK.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition bio_printf_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (out pv nw n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_ex LB OW (bv_unsigned sp) [(out, out + BIO_SIZE)]%Z m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 3 <= rt_credit RT Σ'
    /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv (nw + n)).

Section WithPFC.
Hypothesis PFC : printf_contracts RT.

(* [comment removed for export] *)
Lemma BIO_printf_null_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pb : bptr) (out pv nw A : Z)
    (fmt : list Z) (args : list parg) (o : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BIO_PRINTF_NULL_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (length FR)) < FRAMES_MAX)%nat -> 3 <= rt_credit RT Σ ->
  In (pb, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  vfmtA_ok A fmt args o -> 0 < zlength o < 512 -> vargsA_ok OW LB m [a2; a3; a4; a5; a6; a7] args ->
  a0 = wz out -> a1 = wz A ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BIO_PRINTF_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (bio_printf_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB out pv nw (zlength o) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until o. intros HEAP ST CEIL LO SPT SP16 MI TP FLEN CRED HBIN HO NW0 VF OLEN VARGS -> ->.
  unfold BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK, BIO_PRINTF_A, BIO_SIZE, MallocRep.wz in *.
  remember (zlength o) as n eqn:En.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HO.
  (* [comment removed for export] *)
  change (Z_to_bv 64 2337804) with (Z_to_bv 64 BPRF_ENTRY).
  eapply (bprf_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold BPRF_FRAME, RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | exact MI | exact TP | clear - FLEN; lia | clear - CRED; lia |].
  intros Σ1 m3 f spa g jk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold BPRF_BODY, MallocRep.wz.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G5. unfold SEGTOP_A in G4.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  apply (rw_cells_agree _ _ _ _ _ AGF) in HO; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply (fun H => vargsA_ok_agree OW LB m m3 _ args H (agree_on_mono _ _ _ _ AGF ltac:(intros a Ha; right; right; exact Ha))) in VARGS.
  (* [comment removed for export] *)
  pose proof (rw_cells_skip m3 (bv_unsigned sp + -64) [C8 s0; C8 ra] [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] _ FRH eq_refl) as FRV.
  cbn [cells_size csize Nat.add app] in FRV. replace (bv_unsigned sp + -64 + Z.of_nat 16) with (bv_unsigned sp + -48) in FRV by (clear; lia).
  pose proof (munch_refl []%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step.
  apply evt_done. eapply cps_step_rt.
  { pose proof (@BIO_vprintf_null_cpsA (push AR f 0) PFC) as HP. cbn [ar_RT ar_PMc ar_FR push amb] in HP.
    eapply HP with (lo := lo) (OW := OW) (LB := LB) (pb := pb) (out := out) (pv := pv) (nw := nw) (A := A) (VA := bv_unsigned sp + -48)
                   (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (o := o); clear HP; rewrite ?ESPA;
      [exact HEAP3| exact ST3| exact CEIL| unfold BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BVPF_FRAME, BWI_FRAME, RT_STACK; clear - LO SPAL; lia
      | unfold USTACK_TOP; clear - SPT SPAH; lia| clear - SPA32; Z.div_mod_to_equations; lia| exact MI3| reflexivity| cbn [length]; exact FLEN
      | rewrite CR1; clear - CRED; lia| exact HBIN| exact HO| exact NW0| exact VF| rewrite <- En; exact OLEN| exact (proj2 (proj1 FRV))
      | clear - SPAH; lia| unfold USTACK_TOP, zlength in *; cbn [length]; clear - SPT; lia| exact VARGS| reflexivity| reflexivity| reflexivity]. }
  clear MU3 WM3. intros Σ2 mse PO EL2. cbv beta in PO.
  destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & Fe & fce & m4 & -> & MI4 & ST4 & APX4 & HEAP4 & EL4 & CR4 & HB4).
  unfold MallocRep.wz in *. rewrite (ret_pc_even 0x23ad24) by (clear; lia). rewrite ?ESPA in *. rewrite <- ?En in *.
  unfold apres_ex in APX4. cbn [outside fst snd] in APX4.
  assert (STW4 : forall a, spa <= a < 140737488355328 -> aclient_addr (OW ++ LB) spa a /\ (~ (out <= a < out + 128) /\ True)).
  { intros a Ha. split; [left; exact Ha|]. split; [clear - Ha BB3 D3 CEIL LO SPAL; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia| exact I]. }
  apply (rw_cells_agree _ _ _ _ _ APX4) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ APX4) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW4; clear - Ha SPT SPAH; lia].
  clear HO FRV FRF FRS.
  (* [comment removed for export] *)
  change (Z_to_bv 64 2338084) with (Z_to_bv 64 BPRF_EXIT).
  eapply (bprf_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]); rewrite ?ESPA;
    [exact HEAP4 | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST4 | exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | exact MI4 | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' x11' HEAP' CR' EL' ST' MI' AG'.
  apply (rw_cells_agree _ _ _ _ _ AG') in HB4; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL4, EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold bio_printf_null_post, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { unfold apres_ex. cbn [outside fst snd].
    assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact APX4|]; intros a [Ha Hx]; split; [eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia| exact Hx]|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL4, EL1; reflexivity|]. split; [rewrite CR'; clear - CR4 CR1; cbn [ar_RT push amb] in *; lia|].
  unfold bio_null_cells, bio_cells, MallocRep.wz. exact HB4.
Qed.
End WithPFC.

End WithRT.
