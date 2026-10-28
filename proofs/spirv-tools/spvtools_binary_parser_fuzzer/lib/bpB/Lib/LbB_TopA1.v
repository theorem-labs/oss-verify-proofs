(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RGb1 LbB_RG LbB_RG2 LbB_Ctx.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH1 LbB_TopH2 LbB_TopA.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopA1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition hA_post (e : hent H) : machine_state -> Prop :=
    fun ms' => exists (ff fp : Z) (XSc : list (Z * Z)) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 TOP_CTX_RA) (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e))
                    (Z_to_bv 64 (eS1 e)) (Z_to_bv 64 RG_ENV) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4))
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) (e_s8 e) (e_s9 e) (e_s10 e)
                    (Z_to_bv 64 (e_N e)) x28 x29 x30 x31) (e_F e) (Z_to_bv 64 CTX_CREATE) (e_fc e) None m' (seg_rom asegs)
      /\ hinv H e ff fp XSc (e_s e) (e_LB e) m'
       /\ rw_cells asegs m' (eS1 e + 88) [C8 (Z_to_bv 64 (e_D e))]
      /\ SHAD m' (ff + 32) (repeat (b8 0) 313)
      /\ wr_at asegs m' (sh ff + 334) 3
      /\ (exists jv, rw_cells asegs m' (ff + 2672) [CB 24 jv]).

  Definition hZ_post (e : hent H) : machine_state -> Prop :=
    fun ms' => exists (ff fp : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) (Z_to_bv 64 (eS1 e)) x10 x11 x12 x13
                    x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
                    (Z_to_bv 64 0x7fff8000) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (Z_to_bv 64 0) x28 x29 x30 x31) (e_F e) (Z_to_bv 64 TOP_RET6) (e_fc e) None m' (seg_rom asegs)
      /\ hinv H e ff fp [] (e_s e) (e_LB e) m'.

  Lemma tAz : forall (e : hent H) ms, hpre H e -> e_N e = 0 -> hF8_post H e ms -> evt asegs (hZ_post e) ms.
  Proof.
    intros e ms HP HN P. destruct P as (ff & fp & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m4
                                        & -> & HI4 & D4 & CB4 & W317 & WOBJ & CV).
    pose proof (rt_bp_base H HH) as HB.
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI4) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & _).
    pose proof aceil_facts as ACF.
    assert (DR : 0 <= e_D e < 2 ^ 64) by (exact (hpre_D H e HP)).
    rewrite HN.
    eapply evt_cut.
    { eapply (h3z (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) x28 x29 x30 x31
                  (e_F e) (e_fc e) m4 (eSP e) (eS1 e) ff (e_lo e)); try lia; [exact W317 | exact (hinv_stk H _ _ _ _ _ _ _ HI4) | exact (hinv_mi H _ _ _ _ _ _ _ HI4)]. }
    intros ms5 P5. destruct P5 as (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5).
    subst ms5. apply evt_done.
    exists ff, fp, y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m5. split; [reflexivity|].
    eapply (hinv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 |].
    unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; right. lia.
  Qed.
  Lemma tA1 : forall (e : hent H) ms, hpre H e -> 1 <= e_N e -> hF8_post H e ms -> evt asegs (hA_post e) ms.
  Proof.
    intros e ms HP HN P. destruct P as (ff & fp & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m4
                                        & -> & HI4 & D4 & CB4 & W317 & WOBJ & (jv & CV)).
    pose proof (rt_bp_base H HH) as HB.
    pose proof (rt_bp_ext H HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SS00 & _).
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI4) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (hpre_D H e HP) as DR.
    pose proof HP as (_ & BY & LEN & NR & _ & PD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ADD & _ & LFL & _).
    destruct (PD HN) as (pD & INd). specialize (ADD HN).
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.

    eapply evt_cut.
    { eapply (h3a (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) x28 x29 x30 x31
                  (e_F e) (e_fc e) m4 SP S1 ff (e_N e) lo); try lia; [exact W317 | exact (hinv_stk H _ _ _ _ _ _ _ HI4) | exact (hinv_mi H _ _ _ _ _ _ _ HI4)]. }
    intros ms5 P5. destruct P5 as (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5).
    subst ms5.
    assert (HI5 : hinv H e ff fp [] (e_s e) (e_LB e) m5).
    { eapply (hinv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 |].
      unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; right. lia. }

    assert (CB5 : rw_cells asegs m5 (sh ff + 4) [CB 313 (poison_bytes 313 0xf8)])
      by (eapply rw_cells_transport; [exact CB4 | exact MU5 | exact WM5 | cbn; lia]).
    assert (D5 : rw_cells asegs m5 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))])
      by (eapply rw_cells_transport; [exact D4 | exact MU5 | exact WM5 | cbn; lia]).
    eapply evt_cut.
    { eapply (SS00 (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1)) with (sa := sh ff + 4) (n := 313) (junk := poison_bytes 313 0xf8);
        [reflexivity | reflexivity | lia | exact CB5 | exact MI5 | exact (hinv_ac H _ _ _ _ _ _ _ HI5)]. }
    intros ms6 P6. destruct P6 as (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m6 & EQ6 & MU6 & WM6 & MI6 & CB6).
    subst ms6. rewrite (ret_pc_even TOP_00_RA ltac:(unfold TOP_00_RA; lia) eq_refl).
    assert (HI6 : hinv H e ff fp [] (e_s e) (e_LB e) m6).
    { eapply (hinv_munch H HB); [exact HP | exact HI5 | exact MU6 | exact WM6 | exact MI6 | |].
      - eapply stk_transport_disjoint; [exact ST5 | exact MU6 | exact WM6 | cbn; lia].
      - unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; right. lia. }
    assert (D6 : rw_cells asegs m6 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))])
      by (eapply rw_cells_transport; [exact D5 | exact MU6 | exact WM6 | cbn; lia]).
    assert (OSH6 : SHAD m6 (ff + 32) (repeat (b8 0) 313)).
    { split; [lia|]. split; [clear - F3; Z.div_mod_to_equations; lia|].
      replace (sh (ff + 32)) with (sh ff + 4) by (rewrite <- (sh_add8 ff 4); f_equal).
      exact (u8arr_of_rw_cells asegs m6 _ _ _ CB6). }

    eapply evt_cut.
    { exact (h4a (e_gp e) (e_tp e) z0 z1 z2 z10 z11 z12 z13 z14 z15 z16 z17 (e_s8 e) (e_s9 e) (e_s10 e) z28 z29 z30 z31
                 (e_F e) (e_fc e) m6 SP S1 ff (e_D e) (e_N e) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) D6). }
    intros ms7 (q13 & q14 & q15 & q16 & q17 & EQ7). subst ms7.
    assert (ACC6 : accessible m6 (e_D e) (e_N e)).
    { eapply (haccessible H HB e ff fp [] (e_s e) (e_LB e) m6 pD); [exact HP | exact HI6 | exact INd |].
      pose proof (ah_blocks H HB _ _ _ _ (hpre_RH0 H e HP) INd) as (_ & _ & _ & _ & BC & _). cbn in BC.
      eapply addressable_accessible; [exact ADD | lia | lia | unfold AAPP_HI; lia]. }
    assert (BY6 : bytes_at asegs m6 (e_D e) (e_ds e))
      by (eapply (hbytes H HB e ff fp [] (e_s e) (e_LB e) m6 pD (e_D e) (e_N e)); [exact HP | exact HI6 | exact INd | lia | lia | exact BY]).
    assert (WOBJ6 : wr_at asegs m6 (ff + 32) 2504) by (exact (wr_at_wmono _ _ _ _ (wr_at_wmono _ _ _ _ WOBJ WM5) WM6)).
    eapply evt_cut.
    { eapply (rg_ctor_evt H HB (Z_to_bv 64 TOP_RG_RA) (e_gp e) (e_tp e) z0 z1 z2 (Z_to_bv 64 SP) (Z_to_bv 64 S1) q13 q14 q15 q16 q17
                (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32))
                (e_s8 e) (e_s9 e) (e_s10 e) (Z_to_bv 64 (e_N e)) z28 z29 z30 z31 (e_F e) (e_fc e) m6 (e_s e) (e_LB e)
                ((6, ff, fp) :: e_LF e) pD (ff + 32) (e_D e) (e_N e) S1 lo (e_ds e));
        [exact S32 | lia | exact WOBJ6 | exact OSH6 | clear - F3; Z.div_mod_to_equations; lia
        | exists (6, ff, fp); split; [left; reflexivity | cbn; change (fsz 6) with 4096; lia]
        | lia | exact INd | exact ACC6 | exact BY6 | exact LEN
        | exact (proj1 (stk_split asegs m6 lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI6) ltac:(lia))) | exact CE | unfold RG_STACK, AFS_STACK; lia
        | exact (hinv_rf H _ _ _ _ _ _ _ HI6) | cbn [length]; unfold AFS_MAXLIVE_BP, AFS_MAXLIVE in *; lia | exact (hinv_rh H _ _ _ _ _ _ _ HI6)
        | exact MI6 | exact TP | exact (hinv_ac H _ _ _ _ _ _ _ HI6)]. }
    intros ms8 P8. destruct P8 as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m8 & XS & EQ8
                                   & FSX & MU8 & WM8 & MI8 & ST8 & RF8 & AC8 & RH8 & CO8).
    subst ms8. rewrite (ret_pc_even TOP_RG_RA ltac:(unfold TOP_RG_RA; lia) eq_refl).
    assert (CW8 : Forall (cwin H e ff XS) ([(ff + 32, ff + 32 + 2504); (S1 - RG_STACK, S1)] ++ XS)).
    { apply Forall_app. split.
      - unfold cwin, RG_STACK, AFS_STACK. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        + right; left. lia.
        + left. fold lo S1. lia.
      - apply Forall_forall. intros iv Hiv. right; right; right. exact Hiv. }
    assert (HI8 : hinv H e ff fp ([] ++ XS) (e_s e) (e_LB e) m8)
      by (eapply (hinv_callee H HB); [exact HP | exact HI6 | exact MU8 | exact WM8 | exact MI8 | exact ST8 | exact RF8 | exact AC8 | exact RH8 | exact FSX | exact CW8]).
    cbn [app] in HI8.

    assert (DJ8 : forall A n, ff <= A -> A + n <= ff + 4096 -> (A + n <= ff + 32 \/ ff + 2536 <= A) -> 0 <= n ->
                    disjoint_from ([(ff + 32, ff + 32 + 2504); (S1 - RG_STACK, S1)] ++ XS) A n).
    { intros A n X1 X2 X3 X4. apply disjoint_from_app. split; [cbn; unfold RG_STACK, AFS_STACK; lia|].
      clear - FSX X1 X2 RF8 FFR CE HB. induction XS as [|iv XS IH]; [exact I|]. inversion FSX as [|? ? FS1 FS2]; subst.
      destruct iv as [x y]. cbn. split; [| exact (IH FS2)].
      destruct (fsw_ok H HB e ff fp m8 (x, y) RF8 FFR CE FS1) as (_ & _ & _ & _ & D & _). cbn in D. lia. }
    assert (DJ8s : forall A n, sh ff <= A -> A + n <= sh ff + 512 -> 0 <= n ->
                    disjoint_from ([(ff + 32, ff + 32 + 2504); (S1 - RG_STACK, S1)] ++ XS) A n).
    { intros A n X1 X2 X4. apply disjoint_from_app. split; [cbn; unfold RG_STACK, AFS_STACK; destruct F16; lia|].
      clear - FSX X1 X2 RF8 FFR CE HB. induction XS as [|iv XS IH]; [exact I|]. inversion FSX as [|? ? FS1 FS2]; subst.
      destruct iv as [x y]. cbn. split; [| exact (IH FS2)].
      destruct (fsw_ok H HB e ff fp m8 (x, y) RF8 FFR CE FS1) as (_ & _ & _ & _ & _ & D & _). cbn in D. lia. }
    assert (D8 : rw_cells asegs m8 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))]).
    { eapply rw_cells_transport; [exact D6 | exact MU8 | exact WM8 |].
      apply disjoint_from_app. split; [cbn; unfold RG_STACK, AFS_STACK; lia|].
      clear - FSX RF8 FFR CE HB LOS1. induction XS as [|iv XS IH]; [exact I|]. inversion FSX as [|? ? FS1 FS2]; subst.
      destruct iv as [x y]. cbn. split; [| exact (IH FS2)].
      destruct (fsw_ok H HB e ff fp m8 (x, y) RF8 FFR CE FS1) as (_ & _ & _ & _ & _ & _ & D & _). cbn in D. fold lo in D. lia. }
    assert (OSH8 : SHAD m8 (ff + 32) (repeat (b8 0) 313)).
    { destruct OSH6 as (O1 & O2 & U). split; [exact O1|]. split; [exact O2|].
      eapply u8arr_transport; [exact U | exact MU8 | exact WM8 |]. rewrite repeat_length.
      replace (sh (ff + 32)) with (sh ff + 4) by (rewrite <- (sh_add8 ff 4); f_equal). apply DJ8s; cbn; lia. }
    assert (CV8 : rw_cells asegs m8 (ff + 2672) [CB 24 jv]).
    { assert (CV6 : rw_cells asegs m6 (ff + 2672) [CB 24 jv]).
      { eapply rw_cells_transport; [| exact MU6 | exact WM6 | cbn; lia].
        eapply rw_cells_transport; [exact CV | exact MU5 | exact WM5 | cbn; lia]. }
      eapply rw_cells_transport; [exact CV6 | exact MU8 | exact WM8 | apply DJ8; cbn; lia]. }
    assert (W334 : wr_at asegs m8 (sh ff + 334) 3).
    { destruct W317 as (X1 & X2 & X). split; [lia|]. split; [lia|]. intros i Hi.
      apply WM8. apply WM6. apply WM5. replace (sh ff + 334 + i) with (sh ff + 317 + (17 + i)) by lia. apply X. lia. }

    eapply evt_cut.
    { exact (h5a (e_gp e) (e_tp e) r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 (e_s8 e) (e_s9 e) (e_s10 e) r28 r29 r30 r31
                 (e_F e) (e_fc e) m8 SP S1 ff (e_N e) ltac:(lia)). }
    intros ms9 EQ9. hnf in EQ9. subst ms9.
    assert (OB : (0x6e8000 <= ff + 32 /\ ff + 32 + 2504 <= 0x7fff7000) \/ (0x10007fff8000 <= ff + 32 /\ ff + 32 + 2504 <= 2 ^ 47)).
    { pose proof (aapp_sub _ _ (ff + 32) 2504 F10 ltac:(lia) ltac:(lia)) as X. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in X. lia. }
    eapply evt_cut.
    { eapply (gte_evt (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) (e_gp e) (e_tp e) r5 r6 r7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                (Z_to_bv 64 (ff + 32)) (e_s8 e) (e_s9 e) (e_s10 e) (Z_to_bv 64 (e_N e)) r28 r29 r30 r31 (e_F e) (e_fc e) m8 (seg_rom asegs)
                (ff + 32) lo (e_shi e));
        rewrite ?HLib.u64_of_Z by lia;
        [exact CO8 | exact OSH8 | lia | clear - F3; Z.div_mod_to_equations; lia | lia | left; lia | exact ST8 | lia
        | exact (hinv_s0 H _ _ _ _ _ _ _ HI8) | lia | lia | lia | clear - S32; Z.div_mod_to_equations; lia | exact OB
        | exact AC8 | exact MI8]. }
    intros ms10 P10. destruct P10 as (g5 & g6 & g7 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & m10 & EQ10 & MU10 & WM10 & MI10 & ST10).
    subst ms10. rewrite HLib.u64_of_Z in MU10, ST10 by lia. rewrite (ret_pc_even TOP_GTE_RA ltac:(unfold TOP_GTE_RA; lia) eq_refl).
    assert (ST10f : stk asegs m10 lo SP).
    { destruct (stk_split asegs m8 lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI8) ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m10 S1 SP) by (eapply stk_transport_disjoint; [exact STu | exact MU10 | exact WM10 | cbn; lia]).
      exact (stk_merge asegs m10 lo S1 SP ST10 STu2 ltac:(lia)). }
    assert (HI10 : hinv H e ff fp XS (e_s e) (e_LB e) m10).
    { eapply (hinv_munch H HB); [exact HP | exact HI8 | exact MU10 | exact WM10 | exact MI10 | exact ST10f |].
      unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right; left. lia.
      - left. fold lo SP. lia. }

    assert (D10 : rw_cells asegs m10 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))])
      by (eapply rw_cells_transport; [exact D8 | exact MU10 | exact WM10 | cbn; lia]).
    eapply evt_cut.
    { exact (h6a (e_gp e) (e_tp e) g5 g6 g7 (Z_to_bv 64 RG_ENV) g11 g12 g13 g14 g15 g16 g17 (e_s8 e) (e_s9 e) (e_s10 e) g28 g29 g30 g31
                 (e_F e) (e_fc e) m10 SP S1 ff (e_N e)). }
    intros ms11 EQ11. hnf in EQ11. subst ms11. apply evt_done.
    exists ff, fp, XS, g5, g6, g7, g11, g12, g13, g14, g15, g16, g17, g28, g29, g30, g31, m10. split; [reflexivity|].
    split; [exact HI10|].
    split; [exact D10|].
    split.
    { destruct OSH8 as (O1 & O2 & U). split; [exact O1|]. split; [exact O2|].
      eapply u8arr_transport; [exact U | exact MU10 | exact WM10 |]. rewrite repeat_length.
      replace (sh (ff + 32)) with (sh ff + 4) by (rewrite <- (sh_add8 ff 4); f_equal). cbn. destruct F16; lia. }
    split; [exact (wr_at_wmono _ _ _ _ W334 WM10)|].
    exists jv. eapply rw_cells_transport; [exact CV8 | exact MU10 | exact WM10 | cbn; lia].
  Qed.
End TopA1.
