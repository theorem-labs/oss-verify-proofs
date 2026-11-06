(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim ATacA ACells APrimLem AFrame AFrameM AQuarS F_quar_Ep AQuarR F_ialloc F_unwind F_stacktrace F_free_icpt.
Import ListNotations.
Open Scope Z_scope.

Section FNULL.
  Context {HC : HasCeiling}.
  Variable L : athread.
  Notation THR := (at_thr L).
  Hypothesis TLO : thread_layout_ok L.
  Variables (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - FICPT_STACK.
  Hypothesis QTOP : q + 16 < at_top L.
  Hypothesis Q16 : q mod 16 = 0.
  Variables NM2 NM4 : Z.
  Hypothesis HNM2 : NM2 = 262144.
  Hypothesis HNM4 : NM4 = 262728.

  Notation WN := [(lo, q); (1327048, 1327048 + 4); (743232, 743232 + 8 + NM2); (1005440, 1271624 + 40); (THR + 3168, THR + 3169)].

  Definition fnull_post (ra s0 s1 s2 s3 s4 s5 : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch WN m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q
      /\ thread_env L m' /\ ia_cells NM2 NM4 true m'.

  #[using="HC TLO LOH CLO LOQ QTOP Q16 HNM2 HNM4"] Theorem free_null_icpt_spec : forall (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
        (m : mem) (ras : list Z) (inited : bool),
    stk asegs m lo q -> mem_inv asegs m -> thread_env L m -> trace_env m -> ia_cells NM2 NM4 inited m ->
    fpchain m (at_top L) q (bv_unsigned s0) ras -> (length ras <= 28)%nat -> Forall (fun r => r <> PC0_FREE) ras ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> PC0_FREE ->
    evt asegs (fnull_post ra s0 s1 s2 s3 s4 s5 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz free_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m ras inited ST MI0 TE TRE IA CH LRAS NPC RA4 RANE.
    unfold free_icpt_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ1 : lo <= q - 2128 - 512) by (unfold FICPT_STACK in LOQ; clear - LOQ; lia).
    assert (LQ3 : alloc_ceiling + 4096 <= q) by (unfold FICPT_STACK in LOQ; clear - LOQ CLO; lia).
    pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    pose proof (munch_refl [(q - 2128, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep.
    zstep. carve_frame 2128%nat ST.

    do 7 zstep.
    zstep.
    zstep.
    do 2 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -2128) with (q - 2128) in * by lia.
    assert (DJA : forall A k, A + k <= lo -> disjoint_from [(q - 2128, q)] A k) by (intros A k D1; cbn [disjoint_from]; clear - D1 LQ1; lia).
    assert (IAA : ia_cells NM2 NM4 inited mA).
    { destruct IA as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [eapply rw_cells_transport; [exact FL| exact MU| exact WM| apply DJA; unfold ia_flag; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j0; eapply rw_cells_transport; [exact C0| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j2; split; [| exact Z2]; eapply rw_cells_transport; [exact C2| exact MU| exact WM| apply DJA; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM2; lia); clear - LOH HNM2; lia]|].
      split; [exists j3; eapply rw_cells_transport; [exact C3| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j4; eapply rw_cells_transport; [exact C4'| exact MU| exact WM| apply DJA; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM4; lia); clear - LOH HNM4; lia]|].
      exists j1; eapply rw_cells_transport; [exact C1'| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]. }
    pose proof TE as TEc. te_split TEc.
    eapply (rw_cells_transport asegs _ m mA) in TE_gotpg; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ m mA) in TE_pg; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply evt_cut.
    { eapply (ialloc_spec NM2 NM4 HNM2 HNM4 _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 2128) mA lo inited).
      - exact ST.
      - exact CLO.
      - clear - LQ1; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact IAA.
      - exact TE_gotpg.
      - exact TE_pg.
      - assumption. }
    cbv beta. unfold ialloc_post. intros msI (i1 & i2 & i3 & i4 & i5 & i6 & mI & -> & MUi & WMi & MII & IAI & GPI & PGI & STI).

    replace (ret_pc (Z_to_bv 64 362068)) with (Z_to_bv 64 362068) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (HRD : ov_read_bytes asegs mI (wa 743240) 8 = Some (le8 (wz 0))).
    { destruct IAI as (_ & _ & (j2 & C2 & Z2) & _). specialize (Z2 eq_refl). subst j2. destruct C2 as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
      pose proof (bytes_at_read asegs mI 743240 _ 0 8 BY ltac:(clear; lia) ltac:(unfold zeros; rewrite repeat_length; clear - HNM2; lia)) as R.
      replace (743240 + 0) with 743240 in R by (clear; lia). rewrite R. f_equal. unfold zeros. rewrite skipn_repeat_firstn by (clear - HNM2; lia). reflexivity. }
    zstep.
    zstep. lit_branch.
    do 3 zstep.
    zstep.

    zstep.
    zstep. lit_branch.

    assert (DJI : forall A k, (q - 2128 <= A \/ A + k <= 741952 \/ (1327052 <= A /\ A + k <= lo)) -> disjoint_from [(q - 2128 - 48, q - 2128); (1327048, 1327048 + 4); (743232, 743232 + 8 + NM2); (1005440, 1271624 + 40)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 HNM2 LOH LQ1; lia).
    eapply (rw_cells_transport asegs _ mA mI) in FR; [| exact MUi| exact WMi| apply DJI; left; clear; lia].
    destruct TRE as (TR1 & TR2 & TR3).
    eapply (rw_cells_transport asegs _ m mA) in TR1; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mA mI) in TR1; [| exact MUi| exact WMi| apply DJI; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ m mA) in TR2; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mA mI) in TR2; [| exact MUi| exact WMi| apply DJI; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ m mA) in TR3; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mA mI) in TR3; [| exact MUi| exact WMi| apply DJI; right; right; cbn [cells_size csize Nat.add]; clear - LOH; lia].

    lazymatch type of FR with rw_cells _ _ _ (CB 2072 ?jj :: ?post) =>
      apply (rw_cells_split_CB asegs mI (q - 2128) [] 2072 jj post [8; 8; 240; 1800; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j1; CB 8 ?j2; CB 240 ?j3; CB 1800 ?j4; CB 8 ?j5; CB 8 ?j6; _; _; _; _; _; _; _] =>
      remember j1 as f1 eqn:Ef1; remember j2 as f2 eqn:Ef2; remember j3 as f3 eqn:Ef3; remember j4 as f4 eqn:Ef4; remember j5 as f5 eqn:Ef5; remember j6 as f6 eqn:Ef6 end.
    clear Ef1 Ef2 Ef3 Ef4 Ef5 Ef6.
    hide MU. hide WM. hide MUi. hide WMi.
    pose proof (munch_refl [(q - 2128, q)] mI) as MUf. pose proof (wmono_refl asegs mI) as WMf.
    do 5 zstep.

    replace (q + -81) with (q - 2128 + 2047) by (clear; lia). replace (q + -2128) with (q - 2128 + 0) by (clear; lia). replace (q + -2112) with (q - 2128 + 16) by (clear; lia).
    sstep.
    zstep.
    sstep.

    zstep.
    do 2 zstep.
    do 2 zstep.
    change (sx32 (Z_to_bv 64 30)) with (Z_to_bv 64 30).
    zstep.
    zstep. lit_branch.
    zstep.
    do 2 zstep.
    do 2 zstep.
    zstep.
    zstep.
    zstep.
    do 2 zstep. do 2 zstep.
    change (sx32 (Z_to_bv 64 30)) with (Z_to_bv 64 30).
    do 4 zstep.
    change (Z.b2z (30 <? 1) + -1) with (-1). change (-1 mod 18446744073709551616) with 18446744073709551615.
    replace (Z.land 18446744073709551615 q) with q
      by (symmetry; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; clear - QH ACR CLO LQ1; lia).
    zstep.
    zstep.
    zstep. lit_branch.
    do 2 zstep.
    do 4 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mU end.
    unhide MU. unhide WM. unhide MUi. unhide WMi.
    assert (TEU : thread_env L mU).
    { assert (TEA : thread_env L mA).
      { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
      assert (TEI : thread_env L mI).
      { eapply thread_env_frame_q; [exact TEA| exact MUi| exact WMi|]. unfold thread_clear_q, img_out_q, iastat.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [| clear - LOH LQ1 CLO T1 T2 T3 T4 HNM2; lia]).
        - right; left. clear - LOH LQ1. lia.
        - right; right; right; right; right. clear. lia.
        - right; right; right; right; left. clear - HNM2. lia.
        - right; right; right; right; left. clear. lia. }
      eapply thread_env_frame; [exact TEI| exact MUf| exact WMf|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }

    destruct (proj1 (rw_cells_app asegs mU (q - 2128) [C8 (wz (q - 2128 + 16))] _) FR) as [F0 FRa]. cbn [cells_size csize Nat.add] in FRa. replace (q - 2128 + Z.of_nat 8) with (q - 2128 + 8) in FRa by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 8) [C8 (wz 0)] _) FRa) as [F8 FRb]. cbn [cells_size csize Nat.add] in FRb. replace (q - 2128 + 8 + Z.of_nat 8) with (q - 2128 + 16) in FRb by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 16) [CB 240 f3] _) FRb) as [F16 FRc]. cbn [cells_size csize Nat.add] in FRc. replace (q - 2128 + 16 + Z.of_nat 240) with (q - 2128 + 256) in FRc by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 256) [CB 1800 f4] _) FRc) as [F256 FRd]. cbn [cells_size csize Nat.add] in FRd. replace (q - 2128 + 256 + Z.of_nat 1800) with (q - 2128 + 2056) in FRd by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 2056) [C8 (wz q)] _) FRd) as [F2056 FRe]. cbn [cells_size csize Nat.add] in FRe. replace (q - 2128 + 2056 + Z.of_nat 8) with (q - 64) in FRe by (clear; lia).
    clear FR FRa FRb FRc FRd.
    apply (rw_cells_C8_C4C4 mU (q - 2128 + 8) [] 0 [] ltac:(lia)) in F8. cbn [app] in F8.
    destruct (u64arr_of_CB mU (q - 2128 + 16) 30 f3 F16) as (ws & LWS & BUF).

    destruct (rw_cells_take3 asegs mU (q - 64) [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0] [C8 ra] FRe) as (_ & GS0 & GRA).
    cbn [cells_size csize Nat.add] in GS0, GRA. replace (q - 64 + Z.of_nat 48) with (q - 16) in GS0, GRA by (clear; lia). replace (q - 16 + Z.of_nat 8) with (q - 8) in GRA by (clear; lia).
    pose proof (rd64_of_C8 mU (q - 8) ra GRA) as RDRA. pose proof (rd64_of_C8 mU (q - 16) s0 GS0) as RDS0.

    assert (CHU : fpchain mU (at_top L) q (bv_unsigned s0) ras).
    { eapply fpchain_frame; [| exact MUf| exact WMf| constructor; [cbn [fst snd]; clear; lia| constructor]].
      eapply fpchain_frame; [| exact MUi| exact WMi| repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LOH LQ1 HNM2; lia].
      eapply fpchain_frame; [exact CH| exact MU| exact WM| constructor; [cbn [fst snd]; clear; lia| constructor]]. }
    replace (q + -2128) with (q - 2128) by (clear; lia).
    eapply evt_cut.
    { eapply (ui_entry L _ gp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ _ F_ fc (q - 2128) (q - 2128) 362328 mU
                ltac:(clear - QTOP; lia) ltac:(clear; lia) TLO lo q (bv_unsigned ra) (bv_unsigned s0) ras ws (wz 0) (wz 0) (wz q)).
      - exact STI.
      - exact CLO.
      - clear - LQ1; lia.
      - exact LQ3.
      - exact TEU.
      - exact F8.
      - exact BUF.
      - exact LWS.
      - exact F2056.
      - clear; lia.
      - clear - QTOP; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear; lia.
      - exact RDRA.
      - exact RA4.
      - exact RANE.
      - exact RDS0.
      - exact CHU.
      - exact NPC.
      - exact LRAS.
      - exact MII. }
    cbv beta. unfold ui_post.
    intros msW (w0 & w1 & w2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & mW & ws' & tgw & -> & MUw & WMw & MIW & STW & TEW & SZW & BUFW & LWS' & TRW & TFW).

    replace (ret_pc (Z_to_bv 64 362420)) with (Z_to_bv 64 362420) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (DJW : forall A k, ((q - 2128 <= A /\ A + k <= q - 2128 + 8) \/ (q - 2128 + 256 <= A /\ A + k <= q - 2128 + 2056) \/ q - 2128 + 2064 <= A) ->
              disjoint_from [(lo, q - 2128); (q - 2128 + 8, q - 2128 + 12); (q - 2128 + 16, q - 2128 + 256); (q - 2128 + 2056, q - 2128 + 2064); (THR + 3168, THR + 3169)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 T4 CLO LQ1; lia).
    eapply (rw_cells_transport asegs _ mU mW) in F0; [| exact MUw| exact WMw| apply DJW; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in F256; [| exact MUw| exact WMw| apply DJW; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in FRe; [| exact MUw| exact WMw| apply DJW; right; right; clear; lia].
    pose proof (CB_of_u64arr mW (q - 2128 + 16) ws' BUFW) as CBW. rewrite LWS' in CBW. change (8 * 30)%nat with 240%nat in CBW.
    assert (J4 : rw_cells asegs mW (q - 2128 + 2056) ([C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs mW (q - 2128 + 2056) [C8 (wz q)] _)). split; [exact TFW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 2056 + Z.of_nat 8) with (q - 64) by (clear; lia). exact FRe. }
    assert (J3 : rw_cells asegs mW (q - 2128 + 256) ([CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs mW (q - 2128 + 256) [CB 1800 f4] _)). split; [exact F256|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 256 + Z.of_nat 1800) with (q - 2128 + 2056) by (clear; lia). exact J4. }
    assert (J2 : rw_cells asegs mW (q - 2128 + 16) ([CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs mW (q - 2128 + 16) [CB 240 (u64s ws')] _)). split; [exact CBW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 16 + Z.of_nat 240) with (q - 2128 + 256) by (clear; lia). exact J3. }
    assert (J1 : rw_cells asegs mW (q - 2128 + 8) ([C4 (wz (Z.of_nat (length ([362328; bv_unsigned ra] ++ ras)))); C4 tgw] ++ [CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs mW (q - 2128 + 8) [C4 (wz (Z.of_nat (length ([362328; bv_unsigned ra] ++ ras)))); C4 tgw] _)). split; [exact SZW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 8 + Z.of_nat 8) with (q - 2128 + 16) by (clear; lia). exact J2. }
    assert (FRJ : rw_cells asegs mW (q - 2128) ([C8 (wz (q - 2128 + 16))] ++ [C4 (wz (Z.of_nat (length ([362328; bv_unsigned ra] ++ ras)))); C4 tgw] ++ [CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs mW (q - 2128) [C8 (wz (q - 2128 + 16))] _)). split; [exact F0|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + Z.of_nat 8) with (q - 2128 + 8) by (clear; lia). exact J1. }
    cbn [app] in FRJ. clear J1 J2 J3 J4 F0 F256 TFW FRe CBW SZW.

    assert (MUT : munch WN m mW).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_trans; [eapply munch_weaken; [| exact MUi]| eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_weaken; [| exact MUw]]]];
        unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & O3 & O4 & O5 & _); repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
    pose proof (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMi (wmono_trans asegs _ _ _ WMf WMw))) as WMT.
    hide MU. hide WM. hide MUi. hide WMi. hide MUf. hide WMf. hide MUw. hide WMw.
    pose proof (munch_refl [(q - 2192, q - 2128)] mW) as MUd. pose proof (wmono_refl asegs mW) as WMd.

    do 2 zstep.
    do 2 zstep.
    zstep.
    do 2 zstep.
    do 2 zstep.
    do 5 zstep.
    zstep.
    zstep. carve_frame 64%nat STW.
    replace (q + -2128 + -64) with (q + -2192) in * by (clear; lia).
    do 8 sstep.
    zstep. lit_branch.
    do 8 zstep.
    zstep.

    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mD end.
    release_frame FR STW (q - 2128).
    replace (ret_pc (Z_to_bv 64 362440)) with (Z_to_bv 64 362440) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    replace (q + -2128) with (q - 2128) in * by (clear; lia).
    zstep.
    do 7 zstep.
    zstep. replace (q - 2128 + 2128) with q by (clear; lia). zstep.
    release_frame FRJ STW q.
    assert (TED : thread_env L mD).
    { eapply thread_env_frame; [exact TEW| exact MUd| exact WMd|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
    assert (IAD : ia_cells NM2 NM4 true mD).
    { unhide MUf. unhide WMf. unhide MUw. unhide WMw.
      assert (MUID : munch [(lo, q); (THR + 3168, THR + 3169)] mI mD).
      { eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_trans; [eapply munch_weaken; [| exact MUw]| eapply munch_weaken; [| exact MUd]]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _);
          repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
      assert (TRC : forall A cs, rw_cells asegs mI A cs -> 743232 <= A -> A + Z.of_nat (cells_size cs) <= 1327052 -> rw_cells asegs mD A cs).
      { intros A cs C H1 H2. eapply rw_cells_transport_m; [exact C| exact MUID|]. cbn [disjoint_from]. clear - H1 H2 LOH T3. lia. }
      destruct IAI as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM2; lia); clear - HNM2; lia]|].
      split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM4; lia); clear - HNM4; lia]|].
      exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
    apply evt_done. unfold fnull_post. do 15 eexists. exists mD.
    split; [reflexivity|]. split; [exact MUT|]. split; [exact WMT|]. split; [assumption|]. split; [exact STW|]. split; [exact TED| exact IAD].
  Qed.

End FNULL.

