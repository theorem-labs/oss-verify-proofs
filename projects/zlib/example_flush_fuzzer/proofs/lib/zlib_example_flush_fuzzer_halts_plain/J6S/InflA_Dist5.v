(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6
     InflA_Match2 InflA_Distext2 InflA_Distext3.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import InflDec6 InflA_Dist1 InflA_Dist2 InflA_Dist3 InflA_Dist4.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Definition dist_after1 (s0 : inflate_state) (last : Z) : AM unit :=
  (do here <- (if Z.land (code_op last) 240 =? 0 then
                 let last' := last in
                 do here <- DECODE2 (is_distcode s0) last' ;
                 DROPBITS (code_bits last') ;; add_back ivar_ref (code_bits last') ;; aret here
               else aret last) ;
   DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
   if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
   else us (fun s => iset_extra (iset_offset s (code_val here)) (Z.land (code_op here) 15)) ;; set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am.

Lemma arm_DIST_dec1 : forall s c r,
  arm_DIST ivar_ref (mkW s c r)
  = match DECODE1 (is_distcode s) (is_distbits s) (mkW s c r) with
    | ARun last w1 => dist_after1 s last w1 | ALeave w1 => ALeave w1 | ARet rc w1 => ARet rc w1 end.
Proof. intros s c r. unfold arm_DIST. mstep1 (@gs_eq inflate_state). rewrite abind_run. reflexivity. Qed.

Lemma dist_after1_term : forall s last c r,
  (Z.land (code_op last) 240 =? 0) = false -> dist_after1 s last (mkW s c r) = dist_res last (is_back s) s c r.
Proof.
  intros s last c r E240. unfold dist_after1. rewrite E240. mstep1 (@aret_eq Z).
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv].
  unfold dist_res, rdrop. destruct (negb (Z.land (code_op last) 64 =? 0)).
  - rewrite go_bad_eq. irnorm. reflexivity.
  - mstep1 us_eq. mstep1 set_mode_eq. irnorm. reflexivity.
Qed.

Lemma dist_after1_link : forall s last c r here r2,
  (Z.land (code_op last) 240 =? 0) = true ->
  DECODE2 (is_distcode s) last (mkW s c r) = ARun here (mkW s c r2) ->
  dist_after1 s last (mkW s c r) = dist_res here (is_back s + code_bits last) s c (rdrop r2 (code_bits last)).
Proof.
  intros s last c r here r2 E240 HD2. unfold dist_after1. rewrite E240. rewrite abind_run. rewrite abind_run, HD2.
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv]. rewrite aret_eq.
  mstep1 DROPBITS_eq. rewrite abind_run, add_back_eq. cbn [iv_aux ivar_ref bkv is_back iset_back].
  unfold dist_res, rdrop. irnorm. rewrite iset_back_back, swrap32_add_l.
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  - rewrite go_bad_eq. cbn [is_back iset_back]. reflexivity.
  - mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma dist_after1_leave2 : forall s last c r w2,
  (Z.land (code_op last) 240 =? 0) = true ->
  DECODE2 (is_distcode s) last (mkW s c r) = ALeave w2 -> dist_after1 s last (mkW s c r) = ALeave w2.
Proof. intros s last c r w2 E240 HD2. unfold dist_after1. rewrite E240. rewrite abind_run. rewrite abind_run, HD2. reflexivity. Qed.


Definition ilDQ : cfg := ilSx [0x1e750; 0x1e724; 0x1e6c4] [].

Section DistQ.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dfacts HD :=
    destruct HD as (Hsane & Hlen & Hback & Hwh & Hwn & Hwl & Hws & Hwb & CI & (ext & TD & Hext) & Hofs).

  Definition qpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (11, EVar 35%nat); (22, EAdd (EVar 33%nat) (ELit 168));
     (31, ELit (-16180)); (29, ELit 30); (25, ELit 0x12510); (20, ELit 16209);
     (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat); (23, EVar 40%nat);
     (13, EVar 41%nat); (12, EVar 36%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat));
     (17, EVar 45%nat); (15, EVar 46%nat); (16, EVar 47%nat); (14, EVar 48%nat)].
  Definition qvb : list (nat * Z) :=
    [(45%nat, 2 ^ 15); (46%nat, 2 ^ 63); (47%nat, 2 ^ 63); (48%nat, 16); (49%nat, 256); (50%nat, 65536); (51%nat, 2 ^ 32); (52%nat, 256)].

  Lemma dist_Q_term : forall s c r R M b0 h0 n0,
    is_mode s = DIST -> dist_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    let last := dent1 s (ir_hold r) in
    code_bits last <= ir_bits r -> term_ok DISTS (is_distbits s) last = true -> 16 <= code_op last ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> DJE v s b0 h0 n0 r R ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1e66c) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (dist_res last (is_back s) s c r) R' M' pc'.
  Proof.
    intros s c r R M b0 h0 n0 Hmode HD RI last Hlb TM O16 HM HRC HX HJ. pose proof HD as HD0. open_dfacts HD.
    pose proof HJ as X. unfold DJE, DK in X.
    destruct X as ((HF & G18 & G1 & G23 & G9 & G26 & G17 & G15) & G22 & G12 & G27 & G13 & G16 & G14). open_fix HF.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. pose proof RI as RI0. open_rinv RI. pose proof CI as CI'. open_cinv CI. open_frame Mfr. unfold mapped in *.
    pose proof (tab_ok_root _ _ _ _ TD) as (Rt1 & Rt2 & Rt3).
    pose proof (ctab6_range v (is_distcode s) C Hofs) as [HA0 HA1].
    pose proof (ctab6_cells v s c r M (is_distcode s) C HM Hofs) as TAB.
    pose proof (ones_range15 (is_distbits s) Rt1) as Hones.
    pose proof (BITSv_bound (ir_hold r) (is_distbits s) ltac:(lia)) as HJ1.
    pose proof (code_bits_range last) as Hcb. pose proof (code_op_range last) as Hop. pose proof (code_val_range last) as Hval.
    pose proof (is6_back _ _ _ _ Msc) as C7148.
    assert (Hbm : 0 <= is_back s mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    destruct (term_ok_DISTS _ _ TM) as (Bh & _).
    arm_symexP (@nil (Z * expr)) ilDQ 12%nat [true]
      [RVal (EVar 49%nat); RVal (EVar 50%nat); RVal (EAdd (EVar 33%nat) (ELit 7160)); RVal (EVar 51%nat)] qpins qvb v r
      [Z.ones (is_distbits s); ctab6 v (is_distcode s); ctab6 v (is_distcode s) + 4 * BITSv (ir_hold r) (is_distbits s); code_bits last;
       code_op last; code_val last; is_back s mod 2 ^ 32] NoVals F0
      (mkst R (Z_to_bv 64 0x1e66c) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    1-2: subst last; unfold dent1; tab_read TAB (BITSv (ir_hold r) (is_distbits s)); clear - HJ1 Rt2 Hext; lia.
    symex_reg HR1 (15%bv : reg) as Q15. rewrite (szwrap32_of_mod32 (is_back s) Hback) in Q15.
    symex_reg HR1 (18%bv : reg) as Q9. symex_reg HR1 (6%bv : reg) as Q6. symex_reg HR1 (16%bv : reg) as Q16'.
    assert (HFR : FREG v s r last (is_back s) R1).
    { unfold FREG. split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|].
      regs_via Hfr1; first [exact Q15 | exact Q9 | exact Q6 | exact Q16' | match goal with |- ?G => idtac "FREG1 LEFT" G end]. }
    destruct (dist_fin v C s c r R1 M last (is_back s) (is_distbits s) Hmode HD0 RI0 TM Hlb HM HRC HX HFR) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; by_run Hms1 | exact HPOST].
  Qed.
End DistQ.
End FXG.
