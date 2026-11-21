(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import DrvAgree Keeps F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require Import AImg RtCells AProto AMalloc_iface AUri_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit MonadF Strnlen_iface F_printf_iface I_memcpy ADriver_iface AD_kit AD_emit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require AF_atexit_proof.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | disjoint_goal ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H;
              [ | eapply (munch_weaken W Wq m m');
                [ first [ fp_cover8
                        | unfold sub_fp; cbn [outside]; intros; Zify.zify; xlia zchecker
                        | unfold sub_fp; cbn [outside]; sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | unfold sub_fp; cbn [outside]; intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).

Lemma bad_test : forall r, -2^31 <= r < 2^31 ->
  negb (bv_ltu (Z_to_bv 64 (bv_swrap 32 (Z.land r 18446744073709551615 + -1))) (Z_to_bv 64 (-2))) = ((r =? 0) || (r =? -1))%bool.
Proof.
  intros r Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (4294967296 / 2)%Z with 2147483648%Z. change (2^64) with 18446744073709551616.
  destruct (Z.eqb_spec r 0) as [->|N0]; [vm_compute; reflexivity|].
  destruct (Z.eqb_spec r (-1)) as [->|N1]; [vm_compute; reflexivity|].
  cbn [orb]. apply Bool.negb_false_iff. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.

Section RUN.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Hypothesis ATEXIT : atexit_guard_specA_stmt.
  Let EMIT : emit_printf_stmtA := emit_printf_proofA HSTRN.

  Variables (L : alayout) (RNG00 : footprint) (rstk : region) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
            (LB : list ablock) (p : AsanCtrl.aptr) (A cap Lc : Z) (content : list Z) (lo : Z) (canary : word).
  Hypothesis INLB : In (HB p A cap) LB.
  Hypothesis HLBH : forall b, In b LB -> exists p' A' n', b = HB p' A' n'.
  Hypothesis FC : Forall (fun c => 0 <= c < 256) content.
  Hypothesis LC : zlength content <= cap.
  Hypothesis CAP : cap <= 2^26.
  Hypothesis L0 : 0 <= Lc.
  Hypothesis L6 : 6 + Lc <= zlength content.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPG : bv_unsigned sp + 128 = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis CEIL : ATOP <= lo.
  Hypothesis SPHI : bv_unsigned sp < 2^47.
  Hypothesis LO : lo <= bv_unsigned sp - ATARGET_RUN_STACK.
  Hypothesis RSlo : r_lo rstk <= lo.
  Hypothesis RShi : bv_unsigned sp <= r_hi rstk.
  Hypothesis RSceil : ATOP <= r_rlo rstk.
  Hypothesis HUL : HU L.
  Hypothesis UM1 : In [AMALLOC_PC; 0x803a8] (al_U L).
  Hypothesis UF1 : In [AFREE_PC; 0x8043c] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  Hypothesis HLB : forall b, In b LB -> 0x5f7000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.

  Notation usp := (bv_unsigned sp).
  Notation tpv := (Z_to_bv 64 ATP).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation M2 := (Z_to_bv 64 (-2)).

  Definition plen : Z := zlength content - 6 - Lc.
  Definition PAY : Z := A + 6 + Lc.
  Definition payload : list Z := skipn (Z.to_nat (6 + Lc)) content.
  Definition cfg : Z := if 0 <? Lc then znth content 2 else 0.
  Definition calls : Z := 1 + Z.land cfg 3.

  Definition LBT (own : option (AsanCtrl.aptr * Z)) : list ablock :=
    match own with None => LB | Some (q, D) => HB q D plen :: LB end.
  Definition dptr (own : option (AsanCtrl.aptr * Z)) : Z := match own with None => AEMPTY | Some (_, D) => D end.
  Definition oreg (own : option (AsanCtrl.aptr * Z)) : Z := match own with None => 0 | Some (_, D) => D end.
  Definition omodel (own : option (AsanCtrl.aptr * Z)) : option AsanCtrl.aptr := match own with None => None | Some (q, _) => Some q end.

  Definition FRAME (m : amem) : Prop :=
    exists j0 : list byte, rw_cells asegs m (usp + -80) [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition RNGS (RNG : footprint) : Prop :=
    rng RNG lo (usp + 128 - lo) /\ rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_fs L RNG
    /\ rrng RNG rstk /\ rrng RNG RFMT /\ rrng RNG RBstdout /\ fp_le RNG00 RNG.

  Lemma RNGS_mono : forall R R', fp_le R R' -> RNGS R -> RNGS R'.
  Proof.
    intros R R' LE (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). unfold RNGS, rrng in *.
    repeat match goal with |- _ /\ _ => split end; try (eapply rng_fp_le; [exact LE|]; assumption).
    - eapply rng_fs_mono; eauto.
    - eapply fp_le_trans; eauto.
  Qed.

  Definition BASE (c : Z) (st : APS) (m : amem) : Prop :=
    FRAME m /\ harness_invA m
    /\ rodata_sh0 m /\ rclean m rstk /\ rclean m RBstdout
    /\ mem_inv asegs m /\ stk asegs m lo (usp + -80)
    /\ stdout_file m (aps_so st) /\ aps_ok L st /\ rw_cells asegs m ssp_guard [C8 canary]
    /\ rw_cells asegs m AAEF_INCB [C1 (Z_to_bv 8 c)] /\ atx_cells2 m
    /\ adrv_pres AI LB usp m0 m.
  Definition INV0 (own : option (AsanCtrl.aptr * Z)) (st : APS) (m : amem) : Prop :=
    BASE 0 st m /\ bytes_at asegs m (dptr own) (zbytes payload).
  Definition INV (own : option (AsanCtrl.aptr * Z)) (RNG : footprint) (st : APS) (m : amem) : Prop :=
    AHEAP AI L RNG (aps_m st) (LBT own) m /\ RNGS RNG /\ INV0 own st m.

  Notation DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (wz plen) (wz (dptr own)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (oreg own)) rcw (wz AINIT_FLAG) (wz k) (wz b) M2 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition RUNST0 (own : option (AsanCtrl.aptr * Z)) (pc : Z) (k : Z) (rcw : word) (b : Z) (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
      ms = DST own pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 rcw k b t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ INV own RNG st m.
  Definition RUNST (own : option (AsanCtrl.aptr * Z)) (pc : Z) (k b : Z) (RNG : footprint) (st : APS) (ms : machine_state) : Prop :=
    (exists rcw, RUNST0 own pc k rcw b RNG st ms) /\ 0 <= b <= 1.

  Lemma facts : 0 <= plen /\ plen < 2^26 /\ zlength payload = plen /\ 0 <= cfg < 256 /\ 1 <= calls <= 4 /\ PAY = A + 6 + Lc.
  Proof.
    unfold calls, cfg, plen, payload, PAY. unfold zlength in *. rewrite length_skipn.
    assert (CF : 0 <= (if 0 <? Lc then znth content 2 else 0) < 256).
    { destruct (0 <? Lc); [|lia]. unfold znth. destruct (Z.ltb_spec 2 0); [lia|].
      assert (LT : (Z.to_nat 2 < length content)%nat) by lia.
      pose proof (proj1 (Forall_forall _ _) FC _ (nth_In content 0 LT)) as X. cbn beta in X. lia. }
    pose proof (land3_range (if 0 <? Lc then znth content 2 else 0) ltac:(lia)).
    repeat split; lia.
  Qed.

  Lemma LO' : lo <= usp - 80 - AHARNESS_STACK.
  Proof. unfold ATARGET_RUN_STACK in LO. lia. Qed.

  Lemma geo : 0x10007fff8000 <= lo /\ 0x7fff7f800000 <= lo /\ lo <= usp - 80 - 16384 /\ 0 <= usp < 2^47 /\ usp mod 16 = 0.
  Proof.
    pose proof LO' as L'. unfold AHARNESS_STACK in L'. pose proof CEIL as C. atop_facts.
    pose proof (bv_unsigned_in_range 64 sp). repeat split; try lia.
  Qed.

  Lemma trun_init : forall RNG (Q : machine_state -> Prop) (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk asegs m lo usp -> mem_inv asegs m -> atrun_cells0 m ->
    rw_cells asegs m AGOT_FUZZ_INIT [C8 (wz AFUZZ_INIT)] ->
    rng RNG lo (usp + 128 - lo) -> rng_aimg RNG ->
    (forall (m' : amem) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        FRAME m' -> stk asegs m' lo (usp + -80) ->
        munch [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (AATX, AATX + AATX_N)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
        rw_cells asegs m' AINIT_FLAG [C1 (Z_to_bv 8 1)] -> rw_cells asegs m' AAEF_INCB [C1 (Z_to_bv 8 0)] -> atx_cells2 m' ->
        evtF asegs RNG Q (MS (mkR x1 SPF gp tp x5 x6 x7 a3 a2 (wz 0) x11 x12 x13 x14 x15 x16 x17
                                   a1 a0 (wz AINIT_FLAG) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                             F (Z_to_bv 64 0x8038c) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 ATARGET_RUN) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST MI TR GFI RSTK RIMG K. pose proof geo as (G1 & G2 & G3 & G4 & G5).
    destruct TR as (PI & CB0 & (AX1 & F1 & A1) & (cdt & thr & sec & tm1 & LIBC)).
    unfold AINIT_FLAG, AGOT_FUZZ_INIT, AFUZZ_INIT, AAEF_INCB, ALIBC in *.
    pose proof (munch_refl [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (AATX, AATX + AATX_N)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1)] m) as MU1.
    unfold AINIT_FLAG, AATX, AATX_N in MU. unfold AINIT_FLAG in MU1.
    assert (EATX : AATX = 0x5f49e0) by reflexivity. assert (EATXN : AATX_N = 544) by reflexivity.
    unfold ATARGET_RUN. sort_lits.
    zstep. carve_frame 80%nat ST.
    do 9 zstep.
    do 8 zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
    do 5 zstep.
    lazymatch type of MU1 with munch _ _ ?mx =>
      pose proof (atx_cells1_agree _ m mx (magree_of_munch asegs _ _ _ MU1 WM) ltac:(intros a Ha; unfold atx_addrA in Ha; rewrite EATX, EATXN in Ha; cbn; lia) AX1) as AX1' end.
    clear MU1.
    call_sp (ATEXIT RNG);
      try first [ eassumption
                | unfold AAEF_GUARD; reflexivity
                | lia
                | eapply rng_sub'; [exact RSTK | lia] ].
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear; intros K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    do 3 zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; clear; intros K2; rewrite ?unsigned_lit in K2 by lia; lia]. clear K2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end.
    - lazymatch goal with H : rw_cells asegs _ (usp + -80) _ |- _ => eexists; exact H end.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.
  Section AfterCallee.
    Variables (LX : list ablock) (SP' : Z) (m m' : amem).
    Hypothesis HP : aheap_pres CI LX SP' m m'.
    Hypothesis HS : astk_shadow_pres SP' m m'.
    Hypothesis SPlo : lo <= SP'.
    Hypothesis SPhi : SP' <= usp + -80.
    Hypothesis SP8 : SP' mod 8 = 0.
    Hypothesis HL : forall b, In b LB -> In b LX.

    Let AG : magree asegs (dcli CI LX SP') m m' := magree_of_dpost CI LX SP' m m' HP HS.

    Lemma ci_drv : forall lo' hi' a, In (lo', hi') drv_img_ranges -> lo' <= a < hi' -> dcli CI LX SP' a.
    Proof. intros lo' hi' a Hin Ha. left. right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin| cbn; lia]. Qed.
    Lemma ci_drv_sh : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a < shad hi' -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> dcli CI LX SP' a.
    Proof.
      intros lo' hi' a Hin Ha H8' H8. left. right; right; right. exists (8 * (a - ASHOFF)). split.
      - right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
      - rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    Qed.
    Lemma stack_dcli : forall a, usp + -80 <= a < usp -> dcli CI LX SP' a.
    Proof. intros a Ha. pose proof geo. left. left. lia. Qed.
    Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LX SP' a.
    Proof.
      intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad SP')) as [LT|GE].
      - right. pose proof (shad_mono ATOP RLO H1). lia.
      - left. right; right; right. exists (8 * (a - ASHOFF)). split.
        + left. rewrite !shad_div in *. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
        + rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    Qed.

    Lemma BASE_after_dpost : forall c st st' RNG' LX',
      BASE c st m ->
      AHEAP AI L RNG' (aps_m st') LX' m' -> aps_rest st' = aps_rest st ->
      mem_inv asegs m' -> stk asegs m' lo (usp + -80) ->
      BASE c st' m'.
    Proof.
      intros c st st' RNG' LX' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & CB & AX2 & DP) AH' ESO MI' ST'.
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSceil as RSC. atop_facts.
      split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
      split.
      { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha.
        destruct (Z.lt_ge_cases a 0x7fffc52c);
          [ apply (ci_drv_sh 0x21060 0x22960); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
          | apply (ci_drv_sh 0x22960 0x22a00); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity] ]. }
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x20cc0); [unfold drv_img_ranges; cbn; tauto| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               apply (stack_sh_dcli (r_rlo rstk) (r_rhi rstk)); [atop_facts; lia| lia| exact Ha]. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x5f5080 0x5f54d0); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split; [exact MI'|]. split; [exact ST'|].
      split. { rewrite (aps_so_of_rest _ _ ESO). eapply stdout_file_magree; [exact AG| | exact SO]. intros a [Ha|Ha].
               - apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
               - apply (ci_drv 0x5f5080 0x5f54d0); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia]. }
      split. { eapply aps_ok_rest; [exact ESO| exact RK]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x5f49d0 0x5f49d8); [unfold drv_img_ranges; cbn; tauto|].
               unfold ssp_guard in Ha. cbn in Ha. lia. }
      split. { eapply rw_cells_magree; [exact AG| exact CB|]. intros a Ha. apply (ci_drv 0x5d4050 0x5d4070); [unfold drv_img_ranges; cbn; tauto|]. unfold AAEF_INCB in Ha. cbn in Ha. lia. }
      split. { eapply atx_cells2_agree; [exact AG| | exact AX2]. intros a Ha. apply (ci_drv 0x5f49e0 0x5f4c00); [unfold drv_img_ranges; cbn; tauto|]. unfold atx_addrA, AATX, AATX_N in Ha. lia. }
      eapply adrv_pres_trans; [exact DP|]. intros a Ha [Hc|Hs] Hx.
      - apply AG; [exact Ha|]. eapply dcli_weaken; [left; exact Hc| lia| lia| lia| exact HL].
      - apply AG; [exact Ha|]. eapply dcli_weaken; [right; exact Hs| lia| lia| lia| exact HL].
    Qed.

    Lemma bytes_after_dpost : forall D bs,
      bytes_at asegs m D bs ->
      ((exists q n, In (HB q D n) LX /\ Z.of_nat (length bs) <= n) \/ (exists lo' hi', In (lo', hi') drv_img_ranges /\ lo' <= D /\ D + Z.of_nat (length bs) <= hi')
       \/ (exists q B n, In (HB q B n) LX /\ B <= D /\ D + Z.of_nat (length bs) <= B + n)) ->
      bytes_at asegs m' D bs.
    Proof.
      intros D bs HBY HW. eapply bytes_at_magree; [exact AG| exact HBY|]. intros a Ha.
      destruct HW as [(q & n & Hin & Hn)|[(lo' & hi' & Hin & H1 & H2)|(q & B & n & Hin & H1 & H2)]].
      - left. right; right; left. exists (HB q D n). split; [exact Hin| cbn; lia].
      - apply (ci_drv lo' hi'); [exact Hin| lia].
      - left. right; right; left. exists (HB q B n). split; [exact Hin| cbn; lia].
    Qed.
  End AfterCallee.

  Lemma BASE_after_emit : forall cb st st' m m',
    BASE cb st m ->
    munch [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' lo (usp + -80) -> stdout_file m' (aps_so st') -> aps_resv st' = aps_resv st -> aps_atop st' = aps_atop st ->
    BASE cb st' m'
    /\ forall own, match own with None => plen = 0 | Some (_, D) => 0x5f7000 <= D /\ D + plen <= lo end ->
          bytes_at asegs m (dptr own) (zbytes payload) -> bytes_at asegs m' (dptr own) (zbytes payload).
  Proof.
    intros cb st st' m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & CB & AX2 & DP) MU WM MI' ST' SO' ERV EAT.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof facts as (PL0 & PLM & PLEN & _).
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    assert (AW : appW [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z).
    { unfold appW. repeat constructor; cbn; unfold KLOW, KHIGH; lia. }
    assert (OUT : forall a, (usp + -80 <= a \/ (0x5f7000 <= a < lo) \/ (a < 0x10007fff8000 /\ ~ (0x9de28 <= a < 0x9de28 + 232) /\ ~ (0x5f50a0 <= a < 0x5f50a0 + 1024)))
                            -> (fun a0 : Z => outside [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    split.
    2:{ intros own HD PB. eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
        destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold AEMPTY in Ha; lia]. }
    split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
    split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply OUT. lia. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact SO'|]. split; [destruct RK as [RK1 RK2]; split; [rewrite ERV; exact RK1| rewrite EAT; exact RK2]|].
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply OUT. unfold ssp_guard in Ha. cbn in Ha. lia. }
    split. { eapply rw_cells_magree; [exact AG| exact CB|]. intros a Ha. apply OUT. unfold AAEF_INCB in Ha. cbn in Ha. lia. }
    split. { eapply atx_cells2_agree; [exact AG| | exact AX2]. intros a Ha. apply OUT. unfold atx_addrA, AATX, AATX_N in Ha. lia. }
    eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT.
    unfold atrun_ivs, AINIT_FLAG in Hx. cbn in Hx. atop_facts.
    destruct Hc as [Hc|Hs].
    - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
      + left; lia.
      + right; right. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv (DRV_CI' iv Hiv)) as B1 || pose proof (AI_aci_img AI iv Hiv) as B1.
        pose proof (CI_WF iv Hiv) as B0. unfold AIMG_HI in B1. lia.
      + right; left. destruct (HLB b Hb) as (B1 & B2 & B3). lia.
      + right; right. rewrite shad_div. unfold ASHOFF.
        assert (R : 0 <= a' < 2^47).
        { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
          - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). unfold AIMG_HI in *. lia.
          - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. lia. }
        Z.div_mod_to_equations. lia.
    - right; right. rewrite !shad_div in Hs. unfold ASHOFF in Hs. pose proof geo. Z.div_mod_to_equations. lia.
  Qed.

  Lemma BASE_after_munch : forall cb st W m m',
    BASE cb st m -> munch W m m' -> wmono asegs m m' -> appW W ->
    (forall a, a < 0x5f7000 \/ 0x7fff7000 <= a < 0x10007fff8000 -> outside W a) ->
    (forall a, usp + -80 <= a -> outside W a) ->
    (forall b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a) ->
    mem_inv asegs m' -> stk asegs m' lo (usp + -80) ->
    BASE cb st m'.
  Proof.
    intros cb st W m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & CB & AX2 & DP) MU WM AW Wlow Wstk Wblk MI' ST'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    split. { unfold FRAME in *. destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply Wstk; cbn in Ha; lia]. }
    split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply Wlow. lia. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply stdout_file_magree; [exact AG| | exact SO]. intros a Ha. apply Wlow. lia. }
    split; [exact RK|].
    split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply Wlow. unfold ssp_guard in Ha. cbn in Ha. lia. }
    split. { eapply rw_cells_magree; [exact AG| exact CB|]. intros a Ha. apply Wlow. unfold AAEF_INCB in Ha. cbn in Ha. lia. }
    split. { eapply atx_cells2_agree; [exact AG| | exact AX2]. intros a Ha. apply Wlow. unfold atx_addrA, AATX, AATX_N in Ha. lia. }
    eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|].
    destruct Hc as [Hc|Hs].
    - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
      + apply Wstk. lia.
      + apply Wlow. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
      + apply (Wblk b a Hb R).
      + apply Wlow. rewrite shad_div. unfold ASHOFF.
        assert (R : 0 <= a' < 2^47).
        { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
          - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). destruct R as [R1 R2]. unfold AIMG_HI in *. lia.
          - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. atop_facts. lia. }
        right. Z.div_mod_to_equations. lia.
    - apply Wlow. rewrite !shad_div in Hs. unfold ASHOFF in Hs. right. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  Lemma AHEAP_after_emit : forall RNG st LX m m',
    AHEAP AI L RNG st LX m ->
    munch [(lo, usp + -80); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' -> wmono asegs m m' ->
    AHEAP AI L RNG st LX m'.
  Proof.
    intros RNG st LX m m' AH MU WM. pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
    eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
    constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
    - left. left. lia.
    - left. right; left. exists (RSTDOUT, RSTDOUT + 232)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
    - left. right; left. exists (0x5f5080, 0x5f54d0)%Z. split; [apply DRV_CI; cbn; tauto| cbn; lia].
  Qed.

  Lemma after_incb : forall c c' own RNG st m m',
    BASE c st m -> AHEAP AI L RNG (aps_m st) (LBT own) m -> bytes_at asegs m (dptr own) (zbytes payload) ->
    match own with None => plen = 0 | Some (_, D) => 0x5f7000 <= D end ->
    munch [(AAEF_INCB, AAEF_INCB + 1)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (usp + -80) ->
    rw_cells asegs m' AAEF_INCB [C1 (Z_to_bv 8 c')] ->
    BASE c' st m' /\ AHEAP AI L RNG (aps_m st) (LBT own) m' /\ bytes_at asegs m' (dptr own) (zbytes payload).
  Proof.
    intros c c' own RNG st m m' (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & CB & AX2 & DP) PX PB HD MU WM MI' ST' CB'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof facts as (PL0 & PLM & PLEN & _).
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, ~ (AAEF_INCB <= a < AAEF_INCB + 1) -> (fun a0 : Z => outside [(AAEF_INCB, AAEF_INCB + 1)] a0) a) by (intros a Ha; cbn; lia).
    assert (AW : appW [(AAEF_INCB, AAEF_INCB + 1)]%Z) by (unfold appW, AAEF_INCB; repeat constructor; cbn; unfold KLOW, KHIGH; lia).
    unfold AAEF_INCB in OUT.
    split; [| split].
    - split. { destruct FR as [j0 FR]. exists j0. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply OUT; cbn in Ha; lia]. }
      split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply OUT. lia. }
      split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply stdout_file_magree; [exact AG| | exact SO]. intros a Ha. apply OUT. rewrite ?RSTDOUT_eq, ?RSTDOUT_BUF_eq in Ha. cbn in Ha. lia. }
      split; [exact RK|].
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply OUT. unfold ssp_guard in Ha. cbn in Ha. lia. }
      split; [exact CB'|].
      split. { eapply atx_cells2_agree; [exact AG| | exact AX2]. intros a Ha. apply OUT. unfold atx_addrA, AATX, AATX_N in Ha. lia. }
      eapply adrv_pres_trans; [exact DP|]. intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT. intros E. apply Hx.
      unfold atrun_ivs, AINIT_FLAG. cbn [rin_ivs]. right; right; left. lia.
    - eapply (AI_frame AI); [exact PX| exact MU| exact WM|].
      constructor; [| constructor]. cbn [fst snd]. left. right; left. exists (0x5d4050, 0x5d4070)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; unfold AAEF_INCB; lia].
    - eapply bytes_at_magree; [exact AG| exact PB|]. intros a Ha. apply OUT. rewrite zbytes_length in Ha. unfold zlength in PLEN.
      destruct own as [[q D]|]; cbn [dptr] in Ha |- *; [lia| unfold AEMPTY in Ha; lia].
  Qed.

  Lemma call_body : forall own k (rcw : word) b RNG st ms {B} (K : Z -> @Monad.M APS B) (Q : B -> APS -> footprint -> machine_state -> Prop),
    1 <= k <= 4 -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => 0 < plen end -> RUNST0 own 0x803fc k rcw b RNG st ms ->
    (forall rc' RNG' st' ms', RUNST own (if k =? 1 then 0x80434 else 0x803fc) (k - 1) (bad_upd b rc') RNG' st' ms' -> implMA RNG' (K rc') st' Q ms') ->
    implMA RNG (rc' <- fuzz_oneA AAllocAsan payload ;; io_emit (ioA AAllocAsan) rc' ;;; K rc') st Q ms.
  Proof.
    intros own k rcw b RNG st ms B K Q HK HB01 OWNZ R HKONT.
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & (PX & RG & [BA PB])).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    assert (BOWN : match own with None => True | Some (_, D) => ablock_range D plen /\ 0x5f7000 <= D /\ D + plen <= ATOP end).
    { destruct own as [[q D]|]; [| exact I].
      pose proof (AI_block AI _ _ _ _ _ q D plen PX ltac:(left; reflexivity)) as (_ & BR & _).
      pose proof (AI_block_bounds AI _ _ _ _ _ (HB q D plen) PX ltac:(left; reflexivity)) as (B1 & B2 & B3). cbn in B1, B2, B3.
      unfold AIMG_HI in B1. split; [exact BR| lia]. }
    assert (HD : match own with None => plen = 0 | Some (_, D) => 0x5f7000 <= D end) by (destruct own as [[q D]|]; [exact (proj1 (proj2 BOWN))| exact OWNZ]).
    pose proof BA as (_ & _ & _ & _ & _ & MI & ST & _ & _ & _ & CB & _ & _).
    pose proof (munch_refl [(AAEF_INCB, AAEF_INCB + 1)] m) as MU0. pose proof (wmono_refl asegs m) as WM0. unfold AAEF_INCB in MU0, CB.
    pose proof (conj BA (conj PX PB)) as KEEP. clear BA PX PB.
    unfold AINIT_FLAG. apply implMA_from_evtF. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
    destruct KEEP as (BA & PX & PB).
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    lazymatch goal with H : rw_cells asegs mA 0x5d4054 _ |- _ => rename H into CBA end.
    lazymatch goal with H : mem_inv asegs mA |- _ => rename H into MIA end.
    lazymatch goal with H : stk asegs mA _ _ |- _ => rename H into STA end.
    destruct (after_incb 0 1 own RNG st m mA BA PX PB HD MU0 WM0 MIA STA CBA) as (BA1 & P & PB1).
    clear MU0 WM0 BA PX PB. try clear MI. try clear ST.
    pose proof BA1 as (FRa & HIa & RODa & RCSa & RCBa & _ & _ & SOa & RKa & GUa & CBa & AX2a & DPa).
    eapply implMA_bind.
    {
      eapply (FUZZ L RNG) with (lo := lo) (LB := LBT own) (D := dptr own) (payload := payload) (rstk := rstk);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact P.
      - intros b0 Hb. destruct own as [[q D]|]; cbn [LBT] in Hb; [destruct Hb as [<-|Hb]; [exists q, D, plen; reflexivity|]|]; exact (HLBH b0 Hb).
      - destruct own as [[q D]|]; cbn [dptr LBT].
        + left. exists q. rewrite PLEN. split; [left; reflexivity| lia].
        + right. split; [| reflexivity]. apply length_zero_iff_nil. unfold zlength in PLEN. lia.
      - exact PB1.
      - unfold payload. apply Forall_skipn'. exact FC.
      - destruct own as [[q D]|]; cbn [dptr]; [destruct BOWN as ((_ & _ & _ & X) & _); exact X| reflexivity].
      - lia.
      - exact HIa.
      - exact STA.
      - exact BOT.
      - pose proof LO'. lia.
      - lia.
      - clear -SP16 G4. Z.div_mod_to_equations. lia.
      - exact RCSa.
      - exact RSlo.
      - lia.
      - exact RSceil.
      - rewrite PLEN. reflexivity.
      - exact MIA.
      - exact FRM.
      - reflexivity.
      - reflexivity.
      - rewrite PLEN. reflexivity.
      - reflexivity.
      - exact HUL.
      - exact RGtop.
      - exact RGimg.
      - exact RGimsh.
      - exact RGfs.
      - exact RRS.
      - exact RKa. }
    cbv beta. intros r st1 RNG1 ms1 PO.
    destruct PO as (LE1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1
                    & -> & RR & MI1 & FRM1 & ST1 & HPR & HSP & P1 & HI1 & SOE).
    rewrite ?(unsigned_lit (usp + -80)) in ST1, HPR, HSP by lia.
    unfold ATRUN_RET. fix_ret.
    assert (RG1 : RNGS RNG1) by (eapply RNGS_mono; [exact LE1| exact RG]).
    pose proof RG1 as (RGstk1 & RGtop1 & RGimg1 & RGimsh1 & RGfs1 & RRS1 & RRF1 & RRB1 & LE01).
    assert (BA2 : BASE 1 st1 m1).
    { eapply (BASE_after_dpost (LBT own) (usp + -80) mA m1 HPR HSP); [lia| lia| clear -SP16 G4; Z.div_mod_to_equations; lia| | exact BA1| exact P1| exact SOE| exact MI1| exact ST1].
      intros bb Hb; destruct own as [[q D]|]; [right|]; exact Hb. }
    assert (PB2 : bytes_at asegs m1 (dptr own) (zbytes payload)).
    { eapply (bytes_after_dpost (LBT own) (usp + -80) mA m1 HPR HSP ltac:(lia) ltac:(lia)); [exact PB1|].
      rewrite zbytes_length. unfold zlength in PLEN. destruct own as [[q D]|]; cbn [dptr LBT].
      + left. exists q, plen. split; [left; reflexivity| lia].
      + right; left. exists 0x5d4050, 0x5d4070. split; [unfold drv_img_ranges; cbn; tauto|]. unfold AEMPTY. lia. }
    clear HPR HSP BA1 PB1 P FRa HIa RODa RCSa RCBa SOa RKa GUa CBa AX2a DPa MIA STA CBA.
    pose proof BA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CB & _ & _). unfold AAEF_INCB in CB.
    pose proof (munch_refl [(AAEF_INCB, AAEF_INCB + 1)] m1) as MU1. pose proof (wmono_refl asegs m1) as WM1. unfold AAEF_INCB in MU1.
    pose proof (conj BA2 (conj P1 PB2)) as KEEP. clear BA2 P1 PB2.
    apply implMA_from_evtF. zstep. zstep. zstep. zstep. apply evtF_done.
    destruct KEEP as (BA2 & P1 & PB2).
    lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    lazymatch goal with H : rw_cells asegs mB 0x5d4054 _ |- _ => rename H into CBB end.
    lazymatch goal with H : mem_inv asegs mB |- _ => rename H into MIB end.
    lazymatch goal with H : stk asegs mB _ _ |- _ => rename H into STB end.
    destruct (after_incb 1 0 own RNG1 st1 m1 mB BA2 P1 PB2 HD MU1 WM1 MIB STB CBB) as (BA3 & P3 & PB3).
    clear MU1 WM1 BA2 P1 PB2. try clear MI1. try clear ST1.
    pose proof BA3 as (FR & HI & ROD & RCS & RCB & _ & _ & SO & RK & GU & CB3 & AX2 & DP).
    eapply implMA_bind.
    { eapply implMA_keeps with (f := aps_mra); [| apply s_emit_aps_mra].
      unfold io_emit, ioA, io_S. cbn [a_so a_set_so AAllocAsan].
      destruct (drv_got_of_aheap AI _ _ _ _ _ P3) as (_ & _ & _ & GSSP).
      eapply (EMIT RNG1 rstk) with (lo := lo) (canary := canary) (v := r);
        rewrite ?(unsigned_lit (usp + -80)) by lia.
      - exact SO.
      - lia.
      - apply unsigned_wz_mod32.
      - exact STB.
      - pose proof LO'. unfold AEMIT_DEPTH, AHARNESS_STACK in *. lia.
      - unfold KHIGH. lia.
      - lia.
      - split; [exact GSSP | exact GU].
      - exact MIB.
      - exact FRM1.
      - exact (ASHENV _ _ _ _ _ P3).
      - exact RCS.
      - exact RSlo.
      - lia.
      - exact ROD.
      - exact RCB.
      - eapply rng_sub'; [eapply rng_fp_le; [exact LE1 | exact RGstk] | lia].
      - eapply rng_fp_le; [exact LE1 | exact RGimg].
      - unfold rrng. eapply rng_fp_le; [exact LE1 | exact RRS].
      - unfold rrng. eapply rng_fp_le; [exact LE1 | exact RRF].
      - unfold rrng. eapply rng_fp_le; [exact LE1 | exact RRB]. }
    cbv beta. intros [] st2 RNG2 ms2 [PO EH].
    destruct PO as (ER & v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SO2 & SSP2).
    subst RNG2.
    rewrite ?(unsigned_lit (usp + -80)) in MUc, ST2 by lia.
    fix_ret.
    unfold aps_mra in EH. pose proof (f_equal snd EH) as EAT. apply (f_equal fst) in EH. pose proof (f_equal snd EH) as ERV. apply (f_equal fst) in EH. cbn [fst snd] in EH, ERV, EAT.
    assert (P4 : AHEAP AI L RNG1 (aps_m st2) (LBT own) m2).
    { rewrite EH. eapply AHEAP_after_emit; [exact P3| exact MUc| exact WMc]. }
    assert (IV4 : INV0 own st2 m2).
    { destruct (BASE_after_emit 0 st1 st2 mB m2 BA3 MUc WMc MI2 ST2 SO2 ERV EAT) as [BA4 PBK]. split; [exact BA4|].
      apply PBK; [| exact PB3]. destruct own as [[q D]|]; [| exact OWNZ]. destruct BOWN as (_ & B1 & B2). lia. }
    clear MUc WMc.
    assert (HB' : 0 <= bad_upd b r <= 1) by (apply bad_upd_01; exact HB01).
    assert (TAIL : forall (x19 x22 : word), x22 = wz (bad_upd b r) ->
      evtF asegs RNG1 (fun ms' => RUNST own (if k =? 1 then 0x80434 else 0x803fc) (k - 1) (bad_upd b r) RNG1 st2 ms')
          (MS (mkR (Z_to_bv 64 0x80420) SPF gp tpv v0 v1 v2 (wz plen) (wz (dptr own)) c0 c1 c2 c3 c4 c5 c6 c7
                   (wz (oreg own)) x19 (wz AINIT_FLAG) (wz k) x22 M2 s8 s9 s10 s11 v3 v4 v5 v6)
              F2 (Z_to_bv 64 0x8042c) fc2 None m2 (seg_rom asegs))).
    { intros x19 x22 ->. unfold AINIT_FLAG.
      zstep. rewrite (swrap32_small (k + -1)) by lia. zstep. if_cases KK; zify_cond KK.
      - replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evtF_done. split; [| exact HB']. eexists. unfold RUNST0. do 16 eexists. exists F2, fc2, m2.
        split; [unfold AINIT_FLAG; reflexivity|]. split; [exact FRM2|]. split; [exact P4| split; [exact RG1| exact IV4]].
      - replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evtF_done. split; [| exact HB']. eexists. unfold RUNST0. do 16 eexists. exists F2, fc2, m2.
        split; [unfold AINIT_FLAG; reflexivity|]. split; [exact FRM2|]. split; [exact P4| split; [exact RG1| exact IV4]]. }
    eapply implMA_evtF; [| intros ms' H; exact (HKONT _ _ _ _ H)].
    unfold AINIT_FLAG in TAIL |- *.
    zstep. zstep. rewrite (bad_test r) by lia. if_cases KB.
    -
      eapply TAIL. unfold bad_upd. rewrite KB. reflexivity.
    - zstep. eapply TAIL. unfold bad_upd. rewrite KB. reflexivity.
  Qed.

  Lemma calls_loop : forall (n : nat) own b (rcw : word) RNG st ms,
    (1 <= n <= 4)%nat -> 0 <= b <= 1 -> match own with None => plen = 0 | Some _ => 0 < plen end ->
    RUNST0 own 0x803fc (Z.of_nat n) rcw b RNG st ms ->
    implMA RNG (run_calls (fuzz_oneA AAllocAsan) (io_emit (ioA AAllocAsan)) n payload b) st
           (fun b' st' RNG' ms' => RUNST own 0x80434 0 b' RNG' st' ms') ms.
  Proof.
    induction n as [|n IH]; intros own b rcw RNG st ms HN HB01 OWNZ R; [lia|].
    cbn [run_calls].
    eapply (call_body own (Z.of_nat (S n)) rcw b RNG st ms (fun rc' => run_calls (fuzz_oneA AAllocAsan) (io_emit (ioA AAllocAsan)) n payload (bad_upd b rc')));
      [lia| exact HB01| exact OWNZ| exact R|].
    intros rc' RNG' st' ms' R'. destruct n as [|n'].
    - cbn [run_calls]. replace (Z.of_nat 1 =? 1) with true in R' by reflexivity. apply implMA_ret. apply evtF_done.
      replace (Z.of_nat 1 - 1) with 0 in R' by lia. exact R'.
    - replace (Z.of_nat (S (S n')) =? 1) with false in R' by (symmetry; apply Z.eqb_neq; lia).
      destruct R' as [[rcw' R'] HB01'].
      apply (IH own (bad_upd b rc') rcw' RNG'); [lia| exact HB01'| exact OWNZ|]. replace (Z.of_nat (S n')) with (Z.of_nat (S (S n')) - 1) by lia. exact R'.
  Qed.

  Notation POST s RNG := (atarget_run_postA AI L RNG ra sp gp tpv s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo canary m0).

  Definition retv (b : Z) : Z := if b =? 0 then 0 else 78.

  Lemma run_tail : forall own b RNG st ms,
    RUNST own 0x80434 0 b RNG st ms ->
    implMA RNG ((match omodel own with Some q => afree_M q | None => mret tt end) ;;; mret (retv b)) st
           (POST st RNG00) ms.
  Proof.
    intros own b RNG st ms [[rcw R] HB01].
    destruct R as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & -> & FRM & (P & RG & [BA PB])).
    pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & CB & AX2 & DP).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    unfold FRAME in FR. destruct FR as [j0 FR].
    unfold AINIT_FLAG. apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind with (Q1 := fun _ st' RNG' ms' => fp_le RNG RNG' /\ exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : amem),
        ms' = MS (mkR x1' SPF gp tpv t0' t1' t2' (wz plen) (wz (dptr own)) a0' a1' a2' a3' a4' a5' a6' a7'
                      (wz (oreg own)) rcw (wz 0x5d4050) (wz 0) (wz b) M2 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x8043c) fc None m' (seg_rom asegs)
        /\ AHEAP AI L RNG' (aps_m st') LB m' /\ FRAME m'
        /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -80)
        /\ stdout_file m' (aps_so st') /\ aps_ok L st' /\ rw_cells asegs m' ssp_guard [C8 canary] /\ adrv_pres AI LB usp m0 m'
        /\ rw_cells asegs m' AAEF_INCB [C1 (Z_to_bv 8 0)] /\ atx_cells2 m').
    { destruct own as [[q D]|]; cbn [omodel oreg dptr LBT] in *.
      -
        eapply implMA_mono.
        { eapply (dfree_M AI DFREE L RNG) with (lo := lo) (p := q) (A := D) (n := plen); try reflexivity;
            rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | left; reflexivity | exact MI | exact ST | exact BOT | unfold AFREE_STACK; pose proof LO'; lia
                  | exact UF1 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | exact RK | idtac ]. all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
        cbv beta. intros [] st' RNG' ms' [SOE PO].
        destruct PO as (LE & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3, HPR3, HSP3 by lia.
        fix_ret. cbn [aps_m aset_m fst] in HEAP3.
        pose proof (AI_hb_ids AI _ _ _ _ _ P) as ND.
        rewrite (lb_remove_headA q D plen LB ND) in HPR3, HEAP3.
        destruct (BASE_after_dpost LB (usp + -80) m m3 HPR3 HSP3 ltac:(lia) ltac:(lia) ltac:(clear -SP16 G4; Z.div_mod_to_equations; lia)
                    ltac:(intros bb Hb; exact Hb) 0 st st' _ _ BA HEAP3 SOE MI3 ST3) as (FR3 & _ & _ & _ & _ & _ & _ & SO3 & RK3 & GU3 & CB3 & AX3 & DP3).
        split; [exact LE|]. do 16 eexists. exists m3.
        split; [reflexivity|]. split; [exact HEAP3|]. split; [exact FR3|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact SO3|]. split; [exact RK3|]. split; [exact GU3|]. split; [exact DP3|]. split; [exact CB3| exact AX3].
      -
        apply implMA_ret.
        eapply evtF_mono.
        { eapply (DFREEN L RNG) with (lo := lo); try reflexivity; rewrite ?(unsigned_lit (usp + -80)) by lia;
            first [ exact P | exact MI | exact ST | exact BOT | unfold AFREE_STACK; pose proof LO'; lia | exact UF1 | exact UF0 | exact RGtop | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
          all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
        cbv beta. intros ms' PO.
        destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
        rewrite ?(unsigned_lit (usp + -80)) in ST3, HPR3, HSP3 by lia. fix_ret.
        destruct (BASE_after_dpost LB (usp + -80) m m3 HPR3 HSP3 ltac:(lia) ltac:(lia) ltac:(clear -SP16 G4; Z.div_mod_to_equations; lia)
                    ltac:(intros bb Hb; exact Hb) 0 st st _ _ BA HEAP3 eq_refl MI3 ST3) as (FR3 & _ & _ & _ & _ & _ & _ & SO3 & RK3 & GU3 & CB3 & AX3 & DP3).
        split; [apply fp_le_refl|]. do 16 eexists. exists m3.
        split; [reflexivity|]. split; [exact HEAP3|]. split; [exact FR3|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact SO3|]. split; [exact RK3|]. split; [exact GU3|]. split; [exact DP3|]. split; [exact CB3| exact AX3]. }
    cbv beta. intros [] st' RNG' ms' (LE & x1' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & P' & [j0' FR'] & MI' & ST' & SO' & RK' & GU' & DP' & CB' & AX').
    apply implMA_ret.
    pose proof (RNGS_mono _ _ LE RG) as (RGstk' & _).
    zstep. zstep. zstep.
    match goal with |- context [Z_to_bv 64 (Z.land ?e 78)] =>
      replace (Z.land e 78) with (retv b)
        by (unfold retv; assert (Eb : b = 0 \/ b = 1) by lia; destruct Eb as [-> | ->]; vm_compute; reflexivity) end.
    do 9 zstep. release_frame FR' ST' (bv_unsigned sp). zstep. zstep.
    apply evtF_done. unfold atarget_run_postA. split; [eapply fp_le_trans; [exact LE00| exact LE]|].
    destruct (drv_got_of_aheap AI _ _ _ _ _ P') as (_ & _ & _ & GSSP').
    do 14 eexists. exists F, fc, m'.
    split; [reflexivity|].
    split; [unfold retv; destruct (b =? 0); lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split; [exact DP'|]. split; [exact P'|]. split; [exact SO'|]. split; [split; [exact GSSP'| exact GU']|]. split; [exact RK'|].
    split; [exact AX'| exact CB'].
  Qed.

  Lemma implMA_retb : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
    implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
  Proof. intros X Y RNG a f s Q ms H. exact H. Qed.

  Definition PRE1 (RNG : footprint) (s : APS) (m : amem) : Prop :=
    AHEAP AI L RNG (aps_m s) LB m /\ RNGS RNG /\ BASE 0 s m /\ bytes_at asegs m A (zbytes content).

  Notation EST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 SPF gp tpv t0 t1 t2 (Z_to_bv 64 plen) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 (Z_to_bv 64 AINIT_FLAG) (Z_to_bv 64 calls) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Lemma trun_empty : forall RNG s x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : amem),
    plen = 0 -> frm0 fc -> PRE1 RNG s m ->
    implMA RNG (runA AAllocAsan cfg payload) s (POST s RNG00) (EST 0x803ec x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & RG & BA & CT).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY).
    unfold runA, Adapter.target_run. rewrite PLEN. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMA_retb. cbv beta iota.
    unfold AINIT_FLAG. apply implMA_from_evtF. zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (calls_loop (Z.to_nat calls) None 0 x19 RNG); [lia| lia| exact PZ|].
      unfold RUNST0. do 16 eexists. exists F, fc, m. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold AEMPTY, AINIT_FLAG; reflexivity|].
      split; [exact FRM|]. split; [exact P|]. split; [exact RG|]. split; [exact BA|].
      assert (PE : payload = []). { apply length_zero_iff_nil. unfold zlength in PLEN. lia. }
      cbn [dptr]. rewrite PE. cbn [zbytes map]. apply bytes_at_nil. unfold AEMPTY. lia. }
    cbv beta. intros b st' RNG' ms' R. apply (run_tail None b RNG' st' ms' R).
  Qed.

  Lemma implMA_bind_assoc : forall {X Y W} RNG (ma : @Monad.M APS X) (g : X -> @Monad.M APS Y) (f : Y -> @Monad.M APS W) s Q ms,
    implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms -> implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms.
  Proof.
    intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  Lemma trun_copy : forall RNG s x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (m : amem),
    plen <> 0 -> frm0 fc -> PRE1 RNG s m ->
    implMA RNG (runA AAllocAsan cfg payload) s (POST s RNG00) (EST 0x803a0 x1 t0 t1 t2 (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 F fc m).
  Proof.
    intros until m. intros PZ FRM (P & RG & BA & CT). pose proof BA as (FR & HI & ROD & RCS & RCB & MI & ST & SO & RK & GU & CB & AX2 & DP).
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & LE00).
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    pose proof LC as LC'. pose proof L6 as L6'. unfold zlength in LC', L6'.
    pose proof (AI_block AI _ _ _ _ _ p A cap P INLB) as (_ & BR & RGA & RGAS & SHA & WRA & _ & (RLO & RHI & AR1 & AR2 & AR3 & AR4 & ARR & ARW)).
    pose proof BR as (BQ1 & BQ2 & BQ3 & BQ4). pose proof (ablk_lin _ _ BQ1) as (BK1 & BK2 & BK3 & BK4). unfold AIMG_HI in BK1.
    unfold runA, Adapter.target_run. rewrite !PLEN.
    replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; exact PZ).
    change (1 + Z.land cfg 3) with calls.
    apply implMA_bind_assoc.
    unfold FRAME in FR. destruct FR as [j0 FR].
    unfold AINIT_FLAG. apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (dmalloc_M AI DMALLOC L RNG) with (lo := lo); try reflexivity; rewrite ?(unsigned_lit (usp + -80)) by lia;
        first [ exact P | exact MI | exact ST | exact BOT | unfold AMALLOC_STACK; pose proof LO'; lia | unfold AREQMAX; lia
              | exact UM1 | exact UM0 | exact RGtop | exact RK | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AMALLOC_PC; lia. }
    cbv beta. intros r s1' RNG1 ms1 [SOE PO].
    destruct PO as (LE1 & u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MI1 & ST1 & HPR & HSP & RR).
    rewrite ?(unsigned_lit (usp + -80)) in ST1, HPR, HSP by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in RR.
    destruct r as [nb|]; [| destruct RR].
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & RGN & RGNS & _).
    pose proof BR' as (BN1 & BN2 & BN3 & BN4). pose proof (ablk_lin _ _ BN1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    assert (RG1 : RNGS RNG1) by (eapply RNGS_mono; [exact LE1| exact RG]).
    pose proof RG1 as (RGstk1 & RGtop1 & RGimg1 & RGimsh1 & RGfs1 & RRS1 & RRF1 & RRB1 & LE01).
    pose proof (magree_of_dpost _ _ _ _ _ HPR HSP) as AG1.
    assert (BA1 : BASE 0 s1' m1).
    { eapply (BASE_after_dpost LB (usp + -80) m m1 HPR HSP); [lia| lia| clear -SP16 G4; Z.div_mod_to_equations; lia| intros bb Hb; exact Hb| exact BA| exact HEAP1| exact SOE| exact MI1| exact ST1]. }
    pose proof BA1 as (FR1 & _). unfold FRAME in FR1. destruct FR1 as [j1 FR1].
    assert (CT1 : bytes_at asegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG1| exact CT|]. intros a Ha. left. right; right; left. exists (HB p A cap). split; [exact INLB|]. cbn. rewrite zbytes_length in Ha. lia. }
    pose proof (AI_hb_ids AI _ _ _ _ _ HEAP1) as ND.
    assert (DISJ : A' + plen <= A \/ A + cap <= A').
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' plen) (HB p A cap) HEAP1 ltac:(left; reflexivity) ltac:(right; exact INLB)) as D.
      cbn [ab_addr ab_size] in D. apply D. intros E. injection E. intros _ _ Eid.
      unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. rewrite Eid.
      apply in_flat_map. exists (HB p A cap). split; [exact INLB| left; reflexivity]. }
    assert (PB : bytes_at asegs m1 PAY (zbytes payload)).
    { rewrite <- (firstn_skipn (Z.to_nat (6 + Lc)) (zbytes content)) in CT1. apply bytes_at_app in CT1. destruct CT1 as [_ X].
      rewrite length_firstn, zbytes_length in X. unfold payload, zbytes. rewrite <- skipn_map. unfold zbytes in X.
      replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + Lc)) (length content))) with PAY in X by (rewrite EPAY; lia). exact X. }
    apply implMA_retb. cbv beta iota.
    apply implMA_from_evtF.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; atop_facts; lia|]. clear K1.
    zstep. zstep. zstep.
    zstep. zstep.
    assert (EPP : PAY + plen = A + zlength content) by (unfold PAY, plen; lia).
    pose proof (AI_block AI _ _ _ _ _ p A cap HEAP1 ltac:(right; exact INLB)) as (_ & _ & RGA1 & _ & SHA1 & _ & _ & (RLOa & RHIa & Aa1 & Aa2 & Aa3 & Aa4 & ARRa & ARWa)).
    pose proof (AI_block AI _ _ _ _ _ nb A' plen HEAP1 ltac:(left; reflexivity)) as (_ & _ & _ & _ & SHN1 & _ & _ & (RLOb & RHIb & Ab1 & Ab2 & Ab3 & Ab4 & ARRb & ARWb)).
    pose proof (block_hull RNG1 m1 PAY plen RLOa RHIa ltac:(lia) Aa1 Aa2 ltac:(lia) ltac:(lia) ltac:(lia) ARRa ARWa) as (HRa & HWa & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6).
    pose proof (block_hull RNG1 m1 A' plen RLOb RHIb ltac:(lia) Ab1 Ab2 ltac:(lia) ltac:(lia) ltac:(lia) ARRb ARWb) as (HRb & HWb & Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
    assert (UPa : unpoisoned m1 PAY (PAY + plen)).
    { eapply unpoisoned_sub; [apply (ablock_unpoisoned m1 A cap SHA1); first [lia | clear -BQ4; Z.div_mod_to_equations; lia] | lia | lia]. }
    assert (UPb : unpoisoned m1 A' (A' + plen)).
    { apply (ablock_unpoisoned m1 A' plen SHN1); first [lia | clear -BN4; Z.div_mod_to_equations; lia]. }
    pose proof (AI_rtcells AI _ _ _ _ _ HEAP1) as (_ & Rgot & Rric & Rmem & Rshb & _ & Rini & Rlay & _).
    pose proof (hull_props PAY plen ltac:(lia)) as (_ & _ & _ & _ & Pa5 & Pa6). pose proof (hull_props A' plen ltac:(lia)) as (_ & _ & _ & _ & Pb5 & Pb6).
    assert (EuP : bv_unsigned (Z_to_bv 64 PAY) = PAY) by (apply unsigned_lit; lia).
    assert (EuL : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; lia).
    assert (EuA : bv_unsigned (Z_to_bv 64 A') = A') by (apply unsigned_lit; lia).
    name_sp sp (-80)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evtF_cut; [eapply (memcpy_i_spec RNG1) with (RLO1 := hull_lo PAY) (RHI1 := hull_hi PAY plen) (RLO2 := hull_lo A') (RHI2 := hull_hi A' plen) | ] end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- _ => rewrite ?Hsp, ?EuP, ?EuL, ?EuA; rewrite ?unsigned_lit by lia
         end.
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- mem_inv _ _ => exact MI1
         | |- stk _ _ _ _ => exact ST1
         | |- bytes_at _ _ _ _ => exact PB
         | |- rw_cells _ _ _ [CB _ _] => exact NBLK
         | |- rw_cells _ _ _ _ => assumption
         | |- length _ = _ => rewrite zbytes_length; lia
         | |- app_blk _ _ => first [ eapply ablk_app_blk; [exact BN1| lia] | eapply ablk_app_blk; [eapply ablk_sub; [exact BQ1| unfold PAY; lia| lia]| lia] | unfold app_blk, KLOW, KHIGH, KEND in *; lia ]
         | |- unpoisoned _ _ _ => assumption
         | |- wr_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => assumption
         | |- rng _ lo _ => eapply rng_sub'; [exact RGstk1| lia]
         | |- rng _ PAY _ => eapply rng_sub'; [exact RGA1| lia]
         | |- rng _ _ _ => assumption
         | |- _ /\ _ => unfold KEND in *; repeat match goal with |- _ /\ _ => split end; lia
         | |- _ => unfold KHIGH in *; lia
         end.
    cbv beta. intros ms2 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & ST2 & NB2 & _).
    rewrite ?Hsp in MUc. rewrite ?Hsp in ST2. unname_sp.
    rewrite !(unsigned_lit A') in MUc, NB2 by lia. rewrite !(unsigned_lit plen) in MUc, NB2 by lia.
    replace (bv_unsigned sp + -64 - 2240) with (bv_unsigned sp + -2304) in MUc by lia.
    clear PB CT1 NBLK.
    transport_after_call asegs m1 m2 MUc WMc.
    fix_ret.
    assert (P2 : AHEAP AI L RNG1 (aps_m s1') (HB nb A' plen :: LB) m2).
    { eapply (AI_frame AI); [exact HEAP1| exact MUc| exact WMc|].
      pose proof (AI_layout AI _ _ _ _ _ HEAP1) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - right; left. exists (HB nb A' plen). split; [left; reflexivity| cbn; lia]. }
    assert (IV2 : INV0 (Some (nb, A')) s1' m2).
    { split.
      - eapply (BASE_after_munch 0 s1' _ m1 m2 BA1 MUc WMc); [| | | | exact MI2| exact ST2].
        + unfold appW. constructor; [cbn; unfold KLOW, KHIGH; lia|]. constructor; [cbn; pose proof BN1 as BN1'; unfold ablk, AIMG_HI, KLS in BN1'; unfold KLOW, KHIGH, KEND; first [clear - BN1' BN2 BN3; lia| lia]| constructor].
        + intros a Ha. cbn. pose proof BN1 as BN1'; unfold ablk, AIMG_HI, KLS in BN1'. first [clear - Ha BN1' BN3 CEIL G3; atop_facts; lia| lia].
        + intros a Ha. cbn. lia.
        + intros b a Hb R. cbn.
          pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' plen) b HEAP1 ltac:(left; reflexivity) ltac:(right; exact Hb)) as D.
          cbn [ab_addr ab_size] in D. destruct (HLB b Hb) as (B1 & B2 & B3). atop_facts.
          assert (NE : HB nb A' plen <> b).
          { intros E. unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
            subst b. apply in_flat_map. exists (HB nb A' plen). split; [exact Hb| left; reflexivity]. }
          specialize (D NE). first [clear - D R B3 CEIL G3; lia| lia].
      - cbn [dptr]. apply (rw_cells_bytes_at asegs) in NB2. cbn [cells_bytes cbytes app] in NB2. rewrite app_nil_r in NB2. exact NB2. }
    clear MUc WMc.
    zstep. zstep. zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (calls_loop (Z.to_nat calls) (Some (nb, A')) 0 x19 RNG1); [lia| lia| cbn; lia|].
      unfold RUNST0. do 16 eexists. exists F, fc, m2. rewrite Z2Nat.id by lia.
      split; [cbn [dptr oreg]; unfold AINIT_FLAG; reflexivity|].
      split; [exact FRM|]. split; [exact P2| split; [exact RG1| exact IV2]]. }
    cbv beta. intros b st' RNG' ms'' R. apply (run_tail (Some (nb, A')) b RNG' st' ms'' R).
  Qed.
  Lemma trun_main : forall (tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (s : APS),
    AHEAP AI L RNG00 (aps_m s) LB m0 -> bytes_at asegs m0 A (zbytes content) -> atrun_cells0 m0 -> harness_invA m0 ->
    stk asegs m0 lo usp -> mem_inv asegs m0 -> frm0 fc ->
    stdout_file m0 (aps_so s) -> ssp_cells m0 canary -> aps_ok L s ->
    rclean m0 rstk -> rodata_sh0 m0 -> rclean m0 RBstdout ->
    tp = tpv -> a0 = wz (A + 2) -> a1 = wz Lc -> a2 = wz PAY -> a3 = wz plen ->
    rng RNG00 lo (usp + 128 - lo) -> rng RNG00 lo (al_top L - lo) -> rng_aimg RNG00 -> rng_aimg_sh RNG00 -> rng_fs L RNG00 ->
    rrng RNG00 rstk -> rrng RNG00 RFMT -> rrng RNG00 RBstdout ->
    implMA RNG00 (runA AAllocAsan cfg payload) s (POST s RNG00)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATARGET_RUN) fc None m0 (seg_rom asegs)).
  Proof.
    intros until s. intros P0 CT TR0 HI0 ST0 MI0 FRM SO0 [GS0 GU0] RK RCS0 ROD0 RCB0 -> -> -> -> -> RGstk RGtop RGimg RGimsh RGfs RRS RRF RRB.
    pose proof facts as (PL0 & PLM & PLEN & CFG & CALLS & EPAY). pose proof geo as (G1 & G2 & G3 & G4 & G5).
    pose proof (bytes_at_bound _ _ _ _ CT) as CTB. rewrite zbytes_length in CTB.
    assert (PLEN' : Z.of_nat (length payload) = plen) by (unfold zlength in PLEN; exact PLEN).
    pose proof LC as LC'. pose proof L6 as L6'. unfold zlength in LC', L6'.
    destruct (HLB _ INLB) as (BA1 & BA2 & BA3). cbn [ab_addr ab_size] in BA1, BA2, BA3.
    destruct (drv_got_of_aheap AI _ _ _ _ _ P0) as (_ & _ & GFI0 & _).
    apply implMA_from_evtF.
    eapply trun_init; [exact ST0| exact MI0| exact TR0| exact GFI0| exact RGstk| exact RGimg|].
    intros m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST1 MU WM MI1 IF1 CB1 AX1.
    unfold AATX, AATX_N in MU.
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < usp - 128 /\ ~ (AINIT_FLAG <= a < AINIT_FLAG + 1) /\ ~ (0x5f49e0 <= a < 0x5f49e0 + 544)) \/ usp <= a ->
                            outside [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x5f49e0, 0x5f49e0 + 544)] a).
    { intros a Ha. unfold AINIT_FLAG in *. cbn. lia. }
    assert (AW : appW [(usp - 128, usp); (AINIT_FLAG, AINIT_FLAG + 1); (0x5f49e0, 0x5f49e0 + 544)]).
    { unfold appW, AINIT_FLAG. constructor; [cbn; unfold KLOW, KHIGH; lia|]. constructor; [cbn; unfold KLOW, KHIGH; lia|]. constructor; [cbn; unfold KLOW, KHIGH; lia| constructor]. }
    assert (P1 : AHEAP AI L RNG00 (aps_m s) LB m1).
    { eapply (AI_frame AI); [exact P0| exact MU| exact WM|].
      pose proof (AI_layout AI _ _ _ _ _ P0) as (Y1 & Y2 & Y3 & Y4 & _). atop_facts.
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - left. left. lia.
      - left. right; left. exists (0x5d4050, 0x5d4070). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn [fst snd]; unfold AINIT_FLAG; lia].
      - left. right; left. exists (0x5f49e0, 0x5f4c00). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn [fst snd]; lia]. }
    assert (CT1 : bytes_at asegs m1 A (zbytes content)).
    { eapply bytes_at_magree; [exact AG| exact CT|]. intros a Ha. apply OUT. left. rewrite zbytes_length in Ha. unfold AINIT_FLAG in *. lia. }
    assert (BA : BASE 0 s m1).
    { split; [exact FR|]. split.
      { eapply harness_invA_magree; [exact AG| | exact HI0]. intros a Ha. apply OUT. unfold AINIT_FLAG. lia. }
      split; [eapply rodata_sh0_frame; [exact ROD0| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCS0| exact MU| exact WM| exact AW]|].
      split; [eapply rclean_transport; [exact RCB0| exact MU| exact WM| exact AW]|].
      split; [exact MI1|]. split; [exact ST1|].
      split. { eapply stdout_file_magree; [exact AG| | exact SO0]. intros a Ha. apply OUT. left. rewrite ?RSTDOUT_eq, ?RSTDOUT_BUF_eq in Ha. unfold AINIT_FLAG. lia. }
      split; [exact RK|].
      split. { eapply rw_cells_magree; [exact AG| exact GU0|]. intros a Ha. apply OUT. left. unfold ssp_guard, AINIT_FLAG in *. cbn in Ha. lia. }
      split; [exact CB1|]. split; [exact AX1|].
      intros a Ha Hc Hx. apply AG; [exact Ha|]. apply OUT. unfold atrun_ivs in Hx. cbn [rin_ivs] in Hx. unfold AINIT_FLAG, AATX, AATX_N in *.
      destruct Hc as [Hc|Hs].
      - destruct Hc as [X|[X|[(b & Hb & R)|(a' & X & ->)]]].
        + right. lia.
        + left. destruct X as (iv & Hiv & R). pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
        + left. pose proof (HLB _ Hb) as (B1 & B2 & B3). atop_facts. lia.
        + left. rewrite shad_div. unfold ASHOFF.
          assert (R : 0 <= a' < 2^47).
          { destruct X as [X|[(iv & Hiv & R)|(c & FA & n & Hin & R)]]; [atop_facts; lia| |].
            - pose proof (AI_aci_img AI iv Hiv). pose proof (CI_WF iv Hiv). unfold AIMG_HI in *. lia.
            - destruct (HLB _ Hin) as (B1 & B2 & B3). cbn in B1, B2, B3. atop_facts. lia. }
          rewrite shad_div in Ha, Hx. unfold ASHOFF in Ha, Hx. Z.div_mod_to_equations. lia.
      - left. rewrite !shad_div in Hs. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
    assert (PRE : PRE1 RNG00 s m1).
    { split; [exact P1|]. split; [| split; [exact BA| exact CT1]].
      unfold RNGS, rrng in *. repeat match goal with |- _ /\ _ => split end; first [assumption | apply fp_le_refl]. }
    pose proof (AI_block AI _ _ _ _ _ p A cap P1 INLB) as (_ & _ & RGA & _).
    clear AG OUT MU WM CT SO0 P0 ST0 MI0 TR0 HI0 RCS0 ROD0 RCB0 GS0 GU0 GFI0 CB1 AX1.
    zstep. if_cases KL; zify_cond KL.
    -
      assert (EC : calls = 1) by (unfold calls, cfg; replace (0 <? Lc) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      zstep. zstep. if_cases KP; zify_cond KP.
      + apply evtF_done. rewrite <- EC.
        eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evtF_done. rewrite <- EC.
        eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
    -
      destruct (nth_error content 2) as [c2|] eqn:EC2; [| exfalso; apply nth_error_None in EC2; lia].
      pose proof (proj1 (Forall_forall _ _) FC c2 (nth_error_In _ _ EC2)) as C2R. cbn beta in C2R.
      pose proof (u8ro_read asegs m1 A (zbytes content) 2 (Z_to_bv 8 c2) (Z_to_bv 64 (A + 2)) CT1
                    ltac:(unfold zbytes; rewrite nth_error_map; try change (Z.to_nat 2) with 2%nat; rewrite EC2; reflexivity) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD.
      zstep. zstep.
      assert (EC : calls = Z.land c2 3 + 1).
      { unfold calls, cfg. replace (0 <? Lc) with true by (symmetry; apply Z.ltb_lt; lia). unfold znth.
        destruct (Z.ltb_spec 2 0); [lia|]. change (Z.to_nat 2) with 2%nat. rewrite (nth_error_nth _ _ _ EC2). lia. }
      replace (bv_unsigned (Z_to_bv 8 c2)) with c2
        by (rewrite Z_to_bv_unsigned; unfold bv_wrap; symmetry; apply Z.mod_small; unfold bv_modulus; cbn; lia).
      replace (Z.land c2 3 + 1) with calls by lia.
      zstep. if_cases KP; zify_cond KP.
      + apply evtF_done. eapply trun_empty; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
      + apply evtF_done. eapply trun_copy; [rewrite ?unsigned_lit in KP by lia; lia| exact FRM| exact PRE].
  Qed.
End RUN.

Theorem atarget_run_proofA (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop) :
  (forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
  (forall iv, In iv drv_img_ranges -> In iv (aci AI)) ->
  (forall iv, In iv (aci AI) -> 0 <= fst iv) ->
  dmalloc_stmt AI -> dfree_stmt AI -> dfree_null_stmt AI -> ashenv_law AI ->
  fuzz_oneA_stmt AI rng_fs -> strnlen_a_stmt ->
  atarget_run_stmtA AI rng_fs.
Proof.
  intros MONO DRV_CI CI_WF DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN.
  pose proof AF_atexit_proof.atexit_guard_proofA as ATEXIT.
  intros L RNG rstk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A cap Lc content lo canary.
  intros P0 INLB HLBH CT FC LC CAP L0 L6 TR0 HI0 ST0 BOT LO SPG SP16 SPHI MI0 FRM SO0 SSP RK RCS RSlo RShi RSceil ROD RCB -> -> -> -> -> HUL UM1 UF1 UM0 UF0
         RGstk RGtop RGimg RGimsh RGfs RRS RRF RRB.
  pose proof (AI_layout AI _ _ _ _ _ P0) as (Y1 & Y2 & Y3 & Y4 & _).
  eapply (trun_main AI rng_fs MONO DRV_CI DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN ATEXIT L RNG rstk ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            m LB p A cap Lc content lo canary INLB HLBH FC LC CAP L0 L6 SP16 SPG BOT ltac:(lia) SPHI LO RSlo RShi RSceil HUL UM1 UF1 UM0 UF0
            (fun b Hb => AI_block_bounds AI _ _ _ _ _ b P0 Hb) CI_WF);
    first [ exact P0 | exact CT | exact TR0 | exact HI0 | exact ST0 | exact MI0 | exact FRM | exact SO0 | exact SSP | exact RK
          | exact RCS | exact ROD | exact RCB | exact RGstk | exact RGtop | exact RGimg | exact RGimsh | exact RGfs
          | exact RRS | exact RRF | exact RRB | reflexivity ].
Qed.
End CANSEC1.
