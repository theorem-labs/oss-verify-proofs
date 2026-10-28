(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablXP1 LbB_TablXPr1 LbB_TablXPr2 LbB_TablXPr3 LbB_TablXPr4 LbB_TablXPr5.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablXPk1 LbB_TablXPk2 LbB_TablXPs LbB_TablXPs2 LbB_TablXPe LbB_TablXPx LbB_TablXPm1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac xwf := unfold xs_wf; cbn -[Z.pow Z.le Z.lt Z.mul Z.add];
  repeat match goal with |- _ /\ _ => split end;
  first [ left; reflexivity | right; reflexivity | reflexivity | lia | intros; reflexivity
        | intros; discriminate | intros; repeat split; lia | intros g; unfold XCS; repeat (apply Forall_cons; [cbn; tauto|]); apply Forall_nil ].
Lemma K1_wf : xs_wf K1. Proof. xwf. Qed.
Lemma K2_wf : xs_wf K2. Proof. xwf. Qed.
Lemma K3_wf : xs_wf K3. Proof. xwf. Qed.
Lemma K4_wf : xs_wf K4. Proof. xwf. Qed.
Lemma K5_wf : xs_wf K5. Proof. xwf. Qed.
Lemma L1_wf : xs_wf L1. Proof. xwf. Qed.
Lemma L2_wf : xs_wf L2. Proof. xwf. Qed.
Lemma L3_wf : xs_wf L3. Proof. xwf. Qed.
Lemma L4_wf : xs_wf L4. Proof. xwf. Qed.
Lemma L5_wf : xs_wf L5. Proof. xwf. Qed.
Lemma L6_wf : xs_wf L6. Proof. xwf. Qed.
Lemma L7_wf : xs_wf L7. Proof. xwf. Qed.

Section XP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition xp_epost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (t v b cap : Z) (xs : list Z) (pid : bptr)
      (lo B shi : Z) : machine_state -> Prop :=
    fun ms => exists ff fp R M errv',
      let e := XPEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp in
      ms = MS R F (Z_to_bv 64 (xp_disp_pc t)) fc None M (seg_rom asegs) /\ rfull R
      /\ getr R 3 = gp /\ getr R 4 = tp
      /\ RPl (xcommon (xg e b cap xs) ++ rinK (xg e b cap xs)) R /\ getr R 10 = Z_to_bv 64 0
      /\ fresh_frame H LF 2 ff fp
      /\ xmem H e xs None M s LB b cap pid errv'.

  Lemma xp_entry_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
      (t v b cap : Z) (xs : list Z) (pid : bptr) (lo B shi : Z) (errv : word),
    let SP := bv_unsigned sp in
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 v -> 0 <= t < 2 ^ 31 -> relro0 m ->
    vec32A LB m v b xs cap -> v mod 8 = 0 -> addressable m v 24 -> obj_win H LB LF SP lo v 24 ->
    ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
    wr_at asegs m v 24 -> lb_own LB m -> v4_oldblk LB b cap pid -> (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs))) ->
    (PrsGrammar.expand t <> None -> xbud LB cap (capmax (Zlen xs) cap 3) (as_AL H s)) ->
    as_RHEAP H s LB m -> 0 <= as_AL H s ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->
    as_rauxv_ok H m B -> SP <= B -> SP mod 16 = 0 -> SP <= 2 ^ 47 ->
    stk asegs m lo SP -> aceil <= lo -> lo <= SP - XP_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> stack0 m lo shi -> SP <= shi ->
    evt asegs (xp_epost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_EXPAND) fc None m (seg_rom asegs)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF
      t v b cap xs pid lo B shi errv SP Ha0 Ha1 TR RR VEC V8 ADV OBJ VB WV OWN OLD OSH BU
      RH AL0 TRO TRO2 RA SPB SP16 SP47 ST CE LO ER MI TP RA2 AC RF LFL S0 SHI.
    pose proof (rt_bp_base H HH) as HB. pose proof (rt_bp_ext H HH) as (_ & SM2 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (LO' : lo <= SP - 192 - 1024 - 2 * 4096 - 2 * 8304) by (unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    assert (Hsp : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    assert (SPE : bv_unsigned sp = SP) by reflexivity. clearbody SP.
    set (S1 := SP - 160 - (SP - 160) mod 32).
    assert (S1b : SP - 176 <= S1 <= SP - 160 /\ S1 mod 32 = 0) by (subst S1; clear - SP16; Z.div_mod_to_equations; lia).
    assert (S1E : SP - 160 - (SP - 160) mod 32 = S1) by reflexivity. clearbody S1.
    assert (V0 : 0 <= v /\ v + 24 <= 2 ^ 47) by (destruct VB; lia).

    eapply evt_cut.
    { eapply (xp_b1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t v lo);
        [exact Ha0 | lia | exact Ha1 | lia | rewrite SPE; exact SP16 | rewrite SPE; lia | rewrite SPE; exact ST | exact CE
        | rewrite SPE; lia | exact MI | exact AC]. }
    intros ms1 P1. destruct P1 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1
                                   & EQ1 & MU1 & WM1 & MI1 & ST1 & CS1).
    subst ms1. rewrite SPE in MU1, ST1, CS1 |- *. rewrite S1E in *.
    assert (X2 : as_FSB H + AFS_SIZE <= aceil) by (pose proof (ah_RFS_range H HB _ _ RF) as [(_ & X & _) _]; exact X).
    assert (X1 : aceil <= SP - 160) by (clear - CE LO'; lia).
    pose proof (stack_window_ok H LB LF (SP - 160) SP X1 X2) as (W1a & W1b & W1c).
    assert (RF1 : as_RFS H LF m1) by (eapply (ah_RFS_frame H HB); [exact RF | exact MU1 | exact WM1 | apply Forall_cons; [exact W1b | apply Forall_nil]]).
    assert (RH1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HB); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact W1c | apply Forall_nil]]).

    eapply evt_cut.
    { eapply (SM2 _ (Z_to_bv 64 S1)) with (LF := LF) (lo := lo);
        [exact RF1 | exact LFL | rewrite HLib.u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
        | exact CE | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact TP | exact AC1 | exact (ah_thr H HB _ _ _ RH1)]. }
    intros ms2 P2.
    destruct P2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & j1 & j2
                    & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & CF2 & SF2 & FP2 & AC2).
    subst ms2. rewrite HLib.u64_of_Z in MU2, ST2 by lia. unfold AFS_STACK in MU2.
    rewrite (ret_pc_even XP_SM_RET ltac:(unfold XP_SM_RET; lia) eq_refl).
    pose proof (fresh_of_RFS H HB LF 2 ff fp m2 RF2) as FFR.
    set (e := XPEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp).
    assert (P : xpre H e).
    { pose proof SP16 as SP16'. pose proof SP47 as SP47'. pose proof SPB as SPB'. pose proof SHI as SHI'. pose proof LO as LOs.
      pose proof OBJ as OBJ'.
      rewrite <- SPE in SP16', SP47', SPB', SHI', LOs, OBJ'.
      exact (xp_xpre_of H HB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp
                  FFR LFL RF SP16' SP47' SPB' SHI' CE LOs TP RA2 TR TRO2 V8 VB OBJ' OLD VEC RH BU TRO AL0). }
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & _ & _ & _ & _ & _ & F64 & FL & FH & Q1 & Q2 & Q3 & Q4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3
                   & FB & PB & _ & _ & VL & VF & VFL & VFP & SV1 & SV2 & _ & _).
    assert (PSPE : xSP e = SP) by exact SPE.
    assert (PS1E : xS1 e = S1) by (unfold xS1; rewrite PSPE; exact S1E).
    rewrite ?PSPE, ?PS1E in *. cbn [x_sp x_ff x_fp x_v x_lo x_t e] in *.
    change (fsz 2) with 256 in MU2, CF2. change (fshn 2) with 32 in MU2, SF2. change (Z.to_nat (256 - 40)) with 216%nat in CF2.
    pose proof FFR as FFR'. apply (x2frame_facts H) in FFR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).

    assert (ST2f : stk asegs m2 lo SP).
    { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 S1 SP)
        by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS, AFS_SIZE in *; clear - FS1 FS2 Q1 Q2 Q3 Q4 FL FH S1b LO' CE ACF1 ACF2 S45 SHF2; lia]).
      exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
    assert (WF2 : wr_at asegs m2 ff 256) by (eapply rw_cells_wr_at; [exact CF2 | cbn; lia]).
    assert (WS2 : wr_at asegs m2 (sh ff) 32).
    { destruct SF2 as (_ & _ & (_ & W)).
      assert (L : Z.of_nat (length (poison_bytes (Z.to_nat 32) 0)) = 32) by reflexivity. rewrite L in W. exact W. }
    assert (CFP2 : rw_cells asegs m2 (ff + 248) [C8 (Z_to_bv 64 fp)]).
    { apply (rw_cells_app asegs m2 ff [CB 24 j1; C8 (Z_to_bv 64 S1); CB 216 j2] [C8 (Z_to_bv 64 fp)]) in CF2 as [_ CFb].
      cbn [cells_size csize] in CFb. change (Z.of_nat (24 + (8 + (216 + 0)))) with 248 in CFb. exact CFb. }
    assert (WP2 : wr_at asegs m2 fp 1) by (eapply rw_cells_wr_at; [exact FP2 | cbn; lia]).
    assert (D2 : forall A n, A + n <= S1 - 1024 \/ S1 <= A -> A + n <= as_FSB H \/ as_FSB H + AFS_SIZE <= A ->
                 A + n <= sh ff \/ sh ff + 32 <= A -> disjoint_from [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32)] A n).
    { intros A n K1 K2 K3. cbn. unfold AFS_FLAGS, AFS_SIZE in *. clear - K1 K2 K3 Q1 Q2 Q3 Q4. lia. }
    assert (CS2 : rw_cells asegs m2 (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact CS1 | exact MU2 | exact WM2 |]. change (Z.of_nat (cells_size _)) with 104.
      pose proof (sh_lt_2_45 (ff + 256) ltac:(lia)) as SB.
      apply D2; [clear - S1b; lia | clear - X2 CE LO'; unfold AFS_SIZE in *; lia | clear - SHF0 SB S45 S1b; lia]. }
    assert (RR2 : relro0 m2).
    { intros i Hi. rewrite (MU2 (Z_to_bv 64 i)); [rewrite (MU1 (Z_to_bv 64 i)); [apply RR; exact Hi|]|].
      - rewrite u64_of_Z by lia. cbn [outside]. lia.
      - rewrite u64_of_Z by lia. cbn [outside]. unfold AFS_FLAGS, AFS_SIZE in *. lia. }

    remember (mkR (Z_to_bv 64 XP_SM_RET) (Z_to_bv 64 S1) gp tp u0 u1 u2 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff) b1 b2 b3 b4 b5 b6 b7
                 s2 (Z_to_bv 64 v) s4 (Z_to_bv 64 t) s6 s7 s8 s9 s10 (Z_to_bv 64 0x7fff8000) u3 u4 u5 u6) as R2 eqn:HR2.
    assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    destruct (xp_b2 R2 F fc m2 (seg_rom asegs) ff SP S1 v t lo ltac:(rewrite HR2; reflexivity) ltac:(rewrite HR2; reflexivity)
                ltac:(rewrite HR2; reflexivity) ltac:(rewrite HR2; reflexivity) ltac:(rewrite HR2; reflexivity) ltac:(rewrite HR2; reflexivity)
                ltac:(rewrite HR2; reflexivity) HF2 F64 ltac:(clear - FL; lia) ltac:(clear - FH ACF2; lia) FB TR ltac:(clear - V0; lia)
                ltac:(clear - S1b; lia) S45 ltac:(clear - S1b; lia) SP47 WF2 WS2 ST2f ltac:(clear - LO' S1b; lia) ltac:(clear - FH CE; lia) RR2 MI2)
      as (R3 & m3 & RUN3 & HF3 & KK3 & L2 & L8 & L9 & L10 & L11 & L18 & L19 & L20 & L21 & L25 & L26 & L27 & MU3 & WM3 & MI3 & SK3 & CL3 & KC3).

    destruct (xp_disp R3 F fc m3 (seg_rom asegs) t L21 L11 TR HF3) as (R4 & RUN4 & HF4 & KK4).
    eapply evt_of_msteps; [exact (CatSim.msteps_trans _ _ _ _ RUN3 RUN4)|].
    apply evt_done.
    exists ff, fp, R4, m3, errv. cbv zeta.
    split; [reflexivity|]. split; [exact HF4|].
    split; [rewrite (KK4 3%bv ltac:(inb)), (KK3 3%bv ltac:(inb)), HR2; reflexivity|].
    split; [rewrite (KK4 4%bv ltac:(inb)), (KK3 4%bv ltac:(inb)), HR2; reflexivity|].
    split.
    { unfold RPl, xcommon, rinK. cbv beta iota zeta delta [g_S1 g_SP g_ff g_v xg xSP xS1 x_sp x_ff x_v e]. rewrite SPE, S1E.
      repeat (apply Forall_cons; [cbn [fst snd]; rewrite (KK4 _ ltac:(inb)); assumption|]). apply Forall_nil. }
    split; [rewrite (KK4 10%bv ltac:(inb)); exact L10|].
    split; [exact FFR|].

    pose proof (sh_lt_2_45 (ff + 256) ltac:(lia)) as SB.
    assert (D3 : forall A n, A + n <= S1 + 48 \/ S1 + 56 <= A -> A + n <= ff \/ ff + 36 <= A -> A + n <= sh ff \/ sh ff + 20 <= A ->
                 disjoint_from [(S1 + 48, S1 + 56); (ff, ff + 24); (sh ff, sh ff + 20); (ff + 32, ff + 36)] A n).
    { intros A n Y1 Y2 Y3. cbn. clear - Y1 Y2 Y3 S1b. lia. }
    apply (xp_entry_xmem H HB e m3 errv P);
      cbv beta iota zeta delta [xsaved xS1 xSP xLF x_ra x_sp x_gp x_tp x_s0 x_s1 x_s2 x_s3 x_s4 x_s5
           x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_F x_fc x_m x_mo x_s x_LB x_LF x_t x_v x_b x_cap x_xs x_pid x_lo x_B x_shi x_ff x_fp e];
      rewrite ?SPE, ?S1E.
    - apply (munch_trans _ m m1 m3); [eapply munch_weaken; [|exact MU1]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO'; lia|].
      apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [|exact MU2]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO' S1b; lia|].
      eapply munch_weaken; [|exact MU3]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO' S1b SHF0 SB S45; lia.
    - exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM1 WM2) WM3).
    - exact MI3.
    - exact (SK3 _ _ ST2f).
    - exact AC.
    - exact ER.
    - exact RA.
    - exact S0.
    - eapply rw_cells_transport; [exact CS2 | exact MU3 | exact WM3 | change (Z.of_nat (cells_size _)) with 104; apply D3;
          [clear - S1b; lia | clear - FH CE LO' S1b; lia | clear - SHF0 SB S45 S1b; lia]].
    - exact CL3.
    - eapply rw_cells_transport; [exact CFP2 | exact MU3 | exact WM3 | change (Z.of_nat (cells_size _)) with 8; apply D3;
          [clear - FH CE LO' S1b; lia | clear; lia | clear - FB SHF1 SHF2; lia]].
    - exact (LbB_Own.wr_at_wmono m2 m3 ff 256 WF2 WM3).
    - exact (LbB_Own.wr_at_wmono m2 m3 _ 32 WS2 WM3).
    - exact (LbB_Own.wr_at_wmono m2 m3 _ 1 WP2 WM3).
    - exact (LbB_Own.wr_at_wmono m2 m3 (ff + 32) 4 ltac:(eapply os_wr_at_sub; [exact WF2 | lia | lia | lia]) WM3).
    - exact KC3.
    - assert (XA0 : aceil <= S1 + 48) by (clear - CE LO' S1b; lia).
      pose proof (stack_window_ok H LB ((2, ff, fp) :: LF) (S1 + 48) (S1 + 56) XA0 X2) as (_ & Wa & _).
      eapply (ah_RFS_frame H HB); [exact RF2 | exact MU3 | exact WM3 |].
      apply Forall_cons; [exact Wa|].
      apply Forall_cons; [right; exists (2, ff, fp); split; [left; reflexivity | cbn; change (fsz 2) with 256; clear; lia]|].
      apply Forall_cons; [left; cbn [fst snd]; split; [clear - SHF3; unfold AFS_SIZE in *; lia | right; clear - SHF1; unfold ATLS_PRIV_HI, ATP; lia]|].
      apply Forall_cons; [right; exists (2, ff, fp); split; [left; reflexivity | cbn; change (fsz 2) with 256; clear; lia] | apply Forall_nil].
    - exact VEC.
    - exact OSH.
    - exact ADV.
    - exact WV.
    - exact OWN.
  Qed.

  Lemma expand_none : forall t, t <> 106 -> t <> 52 -> t <> 53 -> t <> 54 -> t <> 55 -> PrsGrammar.expand t = None.
  Proof.
    intros t N1 N2 N3 N4 N5. unfold PrsGrammar.expand. cbv -[Z.eqb].
    rewrite (proj2 (Z.eqb_neq t 52) N2), (proj2 (Z.eqb_neq t 53) N3), (proj2 (Z.eqb_neq t 54) N4), (proj2 (Z.eqb_neq t 55) N5),
      (proj2 (Z.eqb_neq t 106) N1). reflexivity.
  Qed.

  Lemma xat_of_epost : forall (e : xpent H) pc R M errv' msF mo,
    as_VIS H (x_s e) msF = MS R (x_F e) (Z_to_bv 64 pc) (x_fc e) None M (seg_rom asegs) -> rfull R ->
    getr R 3 = x_gp e -> getr R 4 = x_tp e -> RPl (xcommon (xg e (x_b e) (x_cap e) (x_xs e)) ++ rinK (xg e (x_b e) (x_cap e) (x_xs e))) R ->
    as_AKREL H (x_s e) (mkCfg msF mo) -> as_MPRES H (x_mo e) mo ->
    xmem H e (x_xs e) None M (x_s e) (x_LB e) (x_b e) (x_cap e) (x_pid e) errv' ->
    xat H e pc rinK (x_xs e) None (mkCfg msF mo).
  Proof.
    intros e pc R M errv' msF mo VIS HF G3 G4 RP KR MP PM.
    exists R, M, (x_s e), (x_LB e), (x_b e), (x_cap e), (x_pid e), errv'. cbn [cfg_ms cfg_model].
    split; [exact VIS|]. split; [exact HF|]. split; [exact G3|]. split; [exact G4|]. split; [exact RP|].
    split; [exact KR|]. split; [exact MP|]. exact PM.
  Qed.

  Lemma xend_of_xat : forall (e : xpent H) ys sv cf,
    xat H e XP_ONE (fun g => routF g (g_e g)) ys sv cf -> ys = x_xs e ++ expandA (x_t e) -> x_end H e (x_xs e ++ expandA (x_t e)) true cf.
  Proof.
    intros e ys sv cf AT EQ. subst ys.
    destruct AT as (R & mL & sL & LBi & bi & capi & pidi & eL & VIS & HF & G3 & G4 & RP & KR & MP & PM).
    exists R, mL, sL, LBi, bi, capi, pidi, eL, sv.
    split; [exact VIS|]. split; [exact HF|]. split; [exact G3|]. split; [exact G4|].
    split; [exact RP|]. split; [intros X; discriminate X|].
    split; [exact KR|]. split; [exact MP|]. exact PM.
  Qed.

  Lemma xp_after_entry : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (t v b cap : Z) (xs : list Z)
      (pid : bptr) (lo B shi : Z) (msF' : machine_state) (mo' : Model),
    let SP := bv_unsigned sp in
    (length LF < AFS_MAXLIVE_BP)%nat -> as_RFS H LF m ->
    SP mod 16 = 0 -> SP <= 2 ^ 47 -> SP <= B -> SP <= shi -> aceil <= lo -> lo <= SP - XP_STACK ->
    tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    0 <= t < 2 ^ 31 -> trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] ->
    v mod 8 = 0 -> ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
    obj_win H LB LF SP lo v 24 -> v4_oldblk LB b cap pid -> vec32A LB m v b xs cap -> as_RHEAP H s LB m ->
    (PrsGrammar.expand t <> None -> xbud LB cap (capmax (Zlen xs) cap 3) (as_AL H s)) ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> 0 <= as_AL H s ->
    as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    xp_epost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi (as_VIS H s msF') ->
    as_SR H (pat_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap
                       (match PrsGrammar.expand t with Some _ => capmax (Zlen xs) cap 3 | None => cap end)
                       (xs ++ expandA t) pid lo B shi m mo (fun r0 => r0 = Z_to_bv 64 (xres t))) (mkCfg msF' mo').
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi msF' mo' SP
      LFL RF SP16 SPH SPB SPS CE LO TP RA TR TRO2 V8 VB OBJ OLD VEC RH BU TRO AL0 KR MP POST.
    pose proof (rt_bp_base H HH) as HB.
    destruct POST as (ff & fp & R & M & errv' & POST).
    set (e := XPEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp) in POST.
    cbv zeta in POST.
    destruct POST as (VIS & HF & G3 & G4 & RP & A0 & FF & PM).
    assert (P : xpre H e)
      by exact (xp_xpre_of H HB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi ff fp
                  FF LFL RF SP16 SPH SPB SPS CE LO TP RA TR TRO2 V8 VB OBJ OLD VEC RH BU TRO AL0).
    change (pat_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap
                     (match PrsGrammar.expand t with Some _ => capmax (Zlen xs) cap 3 | None => cap end)
                     (xs ++ expandA t) pid lo B shi m mo (fun r0 => r0 = Z_to_bv 64 (xres t))) with (xQ H e).
    pose proof (v4slow_fe724 H HB) as VSC. pose proof (v4slow_fa4fc H HB) as VSR.
    unfold xp_disp_pc in VIS.
    assert (ZL1 : forall x, Zlen (xs ++ [x]) = Zlen xs + 1) by (intros x; unfold Zlen; rewrite length_app; cbn [length]; lia).
    assert (ZL2 : forall x y, Zlen ((xs ++ [x]) ++ [y]) = Zlen xs + 2) by (intros x y; unfold Zlen; rewrite !length_app; cbn [length]; lia).
    Ltac xfin HH HB e P EX :=
      apply (xp_exit_step _ HB e true _ _ P);
      [ eapply (xend_of_xat e); [exact EX | cbv beta iota zeta delta [x_xs x_t e xs_lit K1 K2 K3 K4 K5 L4 L6]; unfold expandA, PrsGrammar.expand; cbv -[app]; rewrite <- ?app_assoc; reflexivity]
      | cbv beta iota zeta delta [x_t e]; unfold xres, PrsGrammar.expand; cbv; reflexivity ].
    destruct (Z.eqb_spec t 106) as [E1|N1].
    { subst t. cbn [xs_pc K1] in VIS.
      eapply (xstep H HH K1 e xs None msF' mo' (xQ H e) K1_wf K1_runs VSC P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros _; reflexivity | intros X; discriminate X | cbn [x_xs e]; lia | exact (xat_of_epost e _ R M errv' msF' mo' VIS HF G3 G4 RP KR MP PM) |].
      intros [msF2 mo2] AT2.
      eapply (xstep H HH L1 e (xs ++ [xs_lit K1]) (Some (xs_sv K1)) msF2 mo2 (xQ H e) L1_wf L1_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL1; lia | exact AT2 |].
      intros [msF3 mo3] AT3. xfin HH HB e P AT3. }
    destruct (Z.eqb_spec t 52) as [E2|N2].
    { subst t. cbn [xs_pc K5] in VIS.
      eapply (xstep H HH K5 e xs None msF' mo' (xQ H e) K5_wf K5_runs VSC P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros _; reflexivity | intros X; discriminate X | cbn [x_xs e]; lia | exact (xat_of_epost e _ R M errv' msF' mo' VIS HF G3 G4 RP KR MP PM) |].
      intros [msF2 mo2] AT2.
      eapply (xstep H HH L2 e (xs ++ [xs_lit K5]) (Some (xs_sv K5)) msF2 mo2 (xQ H e) L2_wf L2_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL1; lia | exact AT2 |].
      intros [msF3 mo3] AT3. xfin HH HB e P AT3. }
    destruct (Z.eqb_spec t 53) as [E3|N3].
    { subst t. cbn [xs_pc K2] in VIS.
      eapply (xstep H HH K2 e xs None msF' mo' (xQ H e) K2_wf K2_runs VSC P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros _; reflexivity | intros X; discriminate X | cbn [x_xs e]; lia | exact (xat_of_epost e _ R M errv' msF' mo' VIS HF G3 G4 RP KR MP PM) |].
      intros [msF2 mo2] AT2.
      eapply (xstep H HH L3 e (xs ++ [xs_lit K2]) (Some (xs_sv K2)) msF2 mo2 (xQ H e) L3_wf L3_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL1; lia | exact AT2 |].
      intros [msF3 mo3] AT3. xfin HH HB e P AT3. }
    destruct (Z.eqb_spec t 54) as [E4|N4].
    { subst t. cbn [xs_pc K3] in VIS.
      eapply (xstep H HH K3 e xs None msF' mo' (xQ H e) K3_wf K3_runs VSC P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros _; reflexivity | intros X; discriminate X | cbn [x_xs e]; lia | exact (xat_of_epost e _ R M errv' msF' mo' VIS HF G3 G4 RP KR MP PM) |].
      intros [msF2 mo2] AT2.
      eapply (xstep H HH L4 e (xs ++ [xs_lit K3]) (Some (xs_sv K3)) msF2 mo2 (xQ H e) L4_wf L4_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL1; lia | exact AT2 |].
      intros [msF3 mo3] AT3.
      eapply (xstep H HH L5 e ((xs ++ [xs_lit K3]) ++ [xs_lit L4]) (Some (xs_sv L4)) msF3 mo3 (xQ H e) L5_wf L5_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL2; lia | exact AT3 |].
      intros [msF4 mo4] AT4. xfin HH HB e P AT4. }
    destruct (Z.eqb_spec t 55) as [E5|N5].
    { subst t. cbn [xs_pc K4] in VIS.
      eapply (xstep H HH K4 e xs None msF' mo' (xQ H e) K4_wf K4_runs VSC P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros _; reflexivity | intros X; discriminate X | cbn [x_xs e]; lia | exact (xat_of_epost e _ R M errv' msF' mo' VIS HF G3 G4 RP KR MP PM) |].
      intros [msF2 mo2] AT2.
      eapply (xstep H HH L6 e (xs ++ [xs_lit K4]) (Some (xs_sv K4)) msF2 mo2 (xQ H e) L6_wf L6_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL1; lia | exact AT2 |].
      intros [msF3 mo3] AT3.
      eapply (xstep H HH L7 e ((xs ++ [xs_lit K4]) ++ [xs_lit L6]) (Some (xs_sv L6)) msF3 mo3 (xQ H e) L7_wf L7_runs VSR P ltac:(unfold XV; cbv; intros X; discriminate X));
        [intros X; discriminate X | intros _; reflexivity | cbn [x_xs e]; rewrite ZL2; lia | exact AT3 |].
      intros [msF4 mo4] AT4. xfin HH HB e P AT4. }

    pose proof (expand_none t N1 N2 N3 N4 N5) as EN.
    apply (xp_exit_step H HB e false msF' mo' P); [| cbn [x_t e]; unfold xres; rewrite EN; reflexivity].
    exists R, M, s, LB, b, cap, pid, errv', None. cbn [cfg_ms cfg_model x_xs x_t e]. unfold expandA. rewrite EN, app_nil_r.
    split; [exact VIS|]. split; [exact HF|]. split; [exact G3|]. split; [exact G4|].
    split; [apply RPl_app in RP as [RP' RK]; apply RPl_app; split; [exact RP'|]; unfold rinK in RK; apply RPl_cons in RK as [X _];
            apply RPl_cons; split; [exact X | exact (Forall_nil _)]|]. split; [intros _; exact A0|].
    split; [exact KR|]. split; [exact MP|]. exact PM.
  Qed.

  Theorem expand_okA : xp_stmtA H.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
      t v b cap xs pid lo B shi errv VIS Ha0 Ha1 TR RR PRE BU.
    pose proof (rt_bp_base H HH) as HB.
    destruct PRE as (VEC & V8 & ADV & OBJ & VB & WV & OWN & OLD & OSH & RH & KR & AL0 & TRO & TRO2
                     & RA & SPB & SP16 & SP47 & ST & CE & LO & ER & MI & TP & RA2 & AC & RF & LFL & S0 & SHI).
    eapply (ahh_evt_then H HB _ _ s msF _ mo KR VIS).
    { exact (xp_entry_evt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF
               t v b cap xs pid lo B shi errv Ha0 Ha1 TR RR VEC V8 ADV OBJ VB WV OWN OLD OSH BU
               RH AL0 TRO TRO2 RA SPB SP16 SP47 ST CE LO ER MI TP RA2 AC RF LFL S0 SHI). }
    intros msF' mo' KR' MP' POST.
    exact (xp_after_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF t v b cap xs pid lo B shi msF' mo'
             LFL RF SP16 SP47 SPB SHI CE LO TP RA2 TR TRO2 V8 VB OBJ OLD VEC RH BU TRO AL0 KR' MP' POST).
  Qed.
End XP.
