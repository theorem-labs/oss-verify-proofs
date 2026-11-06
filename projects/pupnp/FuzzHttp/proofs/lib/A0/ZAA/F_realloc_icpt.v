(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim ATacA ACells LJ LJU APrimLem AFrame AFrameM AQuarS F_quar_Ep AQuarR ATacFix F_ialloc F_unwind F_stacktrace F_free_icpt.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition realloc_icpt_entry : Z := 0x58634.
Definition asan_realloc_entry : Z := 0x33fe0.

Section RICPT.
  Context {HC : HasCeiling}.
  Variable L : athread.
  Notation THR := (at_thr L).
  Hypothesis TLO : thread_layout_ok L.
  Variables (gp s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - 4096.
  Hypothesis QTOP : q + 16 < at_top L.
  Hypothesis Q16 : q mod 16 = 0.
  Variables NM2 NM4 : Z.
  Hypothesis HNM2 : NM2 = 262144.
  Hypothesis HNM4 : NM4 = 262728.

  Notation WN := [(lo, q); (1323912, 1323912 + 4); (740096, 740096 + 8 + NM2); (1002304, 1268488 + 40); (THR + 3168, THR + 3169)].
  Notation T := (q - 2136).

  Definition realloc_tr (ra : word) (ras : list Z) : list Z := PC0_REALLOC :: bv_unsigned ra :: ras.

  Variables (ra : word) (ras : list Z).

  Variable RT : Type.
  Variable TREE : itree nodeL (exc RT).
  Variable H : word -> bool.
  Variables (p size : Z).
  Variable CPRE : mem -> Prop.
  Variable CPOST : mem -> RT -> (word -> bool) -> word -> mem -> Prop.

  Definition rcallee_post (ra' s0 s1 s2 s3 s4 s5 s6 : word) (mW : mem) : RT -> (word -> bool) -> machine_state -> Prop :=
    fun r H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 W,
      ms' = MS (mkR ra' (wz (q - 2144)) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra') fc None m2 (seg_rom asegs)
      /\ munch W mW m2 /\ (forall A k, q - 2144 <= A -> disjoint_from W A k) /\ stk asegs m2 lo (q - 2144)
      /\ CPOST mW r H' a0 m2.

  Hypothesis CALLEE : forall (ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) (mW : mem) (ws : list word),
    mclean H mW -> stk asegs mW lo (q - 2144) ->
    rw_cells asegs mW T [C8 (wz (T + 16)); C8 (wz (Z.of_nat (length (realloc_tr ra ras))))] -> u64arr asegs mW (T + 16) ws -> length ws = 30%nat ->
    firstn (length (realloc_tr ra ras)) ws = map wz (realloc_tr ra ras) ->
    CPRE mW ->
    implA H TREE (rcallee_post ra' s0 s1 s2 s3 s4 s5 s6 mW)
      (MS (mkR ra' (wz (q - 2144)) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz p) (wz size) (wz T) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz asan_realloc_entry) fc None mW (seg_rom asegs)).

  Definition ricpt_post (s0 s1 s2 s3 s4 s5 s6 : word) (m : mem) : RT -> (word -> bool) -> machine_state -> Prop :=
    fun r H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mW m' W,
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch WN m mW /\ wmono asegs m mW /\ munch W mW m' /\ (forall A k, q - 2144 <= A -> disjoint_from W A k)
      /\ stk asegs m' lo q /\ CPOST mW r H' a0 m'.

  #[using="HC TLO LOH CLO LOQ QTOP Q16 HNM2 HNM4 CALLEE"] Theorem realloc_icpt_spec : forall (t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word)
        (m : mem) (inited : bool),
    mclean H m -> stk asegs m lo q -> mem_inv asegs m -> thread_env L m -> trace_env m -> ia_cells NM2 NM4 inited m ->
    fpchain m (at_top L) q (bv_unsigned s0) ras -> (length ras <= 28)%nat -> Forall (fun r => r <> PC0_REALLOC) ras ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> PC0_REALLOC ->
    (p = 0 \/ 6328320 <= p < 2^47) ->
    (forall mW, munch WN m mW -> wmono asegs m mW -> mem_inv asegs mW -> thread_env L mW -> ia_cells NM2 NM4 true mW -> CPRE mW) ->
    implA H TREE (ricpt_post s0 s1 s2 s3 s4 s5 s6 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz p) (wz size) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz realloc_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m inited MC ST MI0 TE TRE IA CH LRAS NPC RA4 RANE PR CPREF.
    unfold realloc_icpt_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ1 : lo <= q - 2144 - 512) by (clear - LOQ; lia).
    assert (LQ3 : alloc_ceiling + 4096 <= q) by (clear - LOQ CLO; lia).
    pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    pose proof (munch_refl [(q - 2160, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep.
    zstep. carve_frame 2144%nat ST.

    do 8 zstep.
    zstep.
    zstep.
    do 3 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -2144) with (q - 2144) in * by lia.
    assert (DJA : forall A k, A + k <= lo -> disjoint_from [(q - 2160, q)] A k) by (intros A k D1; cbn [disjoint_from]; clear - D1 LQ1; lia).
    pose proof TE as TEc. te_split TEc.
    eapply (rw_cells_transport asegs _ m mA) in TE_inited; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].

    zstep. carve_frame 16%nat ST.
    replace (q + -2144 + -16) with (q + -2160) in * by (clear; lia).
    do 2 sstep.
    do 2 zstep.
    zstep.
    do 2 zstep.
    zstep. lit_branch.
    do 2 zstep.
    zstep.
    zstep.

    release_frame FR0 ST (q + -2144).
    replace (ret_pc (Z_to_bv 64 363116)) with (Z_to_bv 64 363116) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. lit_branch.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    replace (q + -2144) with (q - 2144) in * by lia.
    assert (IAA : ia_cells NM2 NM4 inited mB).
    { destruct IA as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [eapply rw_cells_transport; [exact FL| exact MU| exact WM| apply DJA; unfold ia_flag; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j0; eapply rw_cells_transport; [exact C0| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j2; split; [| exact Z2]; eapply rw_cells_transport; [exact C2| exact MU| exact WM| apply DJA; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM2; lia); clear - LOH HNM2; lia]|].
      split; [exists j3; eapply rw_cells_transport; [exact C3| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j4; eapply rw_cells_transport; [exact C4'| exact MU| exact WM| apply DJA; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM4; lia); clear - LOH HNM4; lia]|].
      exists j1; eapply rw_cells_transport; [exact C1'| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]. }
    eapply (rw_cells_transport asegs _ m mB) in TE_gotpg; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ m mB) in TE_pg; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply evt_cut.
    { eapply (ialloc_spec NM2 NM4 HNM2 HNM4 _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 2144) mB lo inited).
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

    replace (ret_pc (Z_to_bv 64 363124)) with (Z_to_bv 64 363124) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (AR : 0 <= p < 2^47) by (clear - PR; lia).
    zstep.
    replace (Z.shiftr p 47) with 0 by (symmetry; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; clear - AR; lia).
    zstep. lit_branch.
    do 3 zstep.
    set (i32 := Z.shiftr p 32) in *.
    assert (I32 : 0 <= i32 < 32768) by (unfold i32; rewrite Z.shiftr_div_pow2 by lia; clear - AR; change (2^32) with 4294967296; change (2^47) with 140737488355328 in AR; Z.div_mod_to_equations; lia).
    assert (HRD : ov_read_bytes asegs mI (wa (740104 + 8 * i32)) 8 = Some (le8 (wz 0))).
    { destruct IAI as (_ & _ & (j2 & C2 & Z2) & _). specialize (Z2 eq_refl). subst j2. destruct C2 as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
      pose proof (bytes_at_read asegs mI 740104 _ (8 * i32) 8 BY ltac:(clear - I32; lia)
                    ltac:(unfold zeros; rewrite repeat_length; clear - I32 HNM2; lia)) as R.
      rewrite R. f_equal. unfold zeros. rewrite skipn_repeat_firstn by (clear - I32 HNM2; lia). reflexivity. }
    replace (740096 + Z.shiftl i32 3) with (740104 + 8 * i32 + -8) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; clear; lia).
    zstep.
    zstep.
    zstep. lit_branch.

    assert (DJI : forall A k, (q - 2144 <= A \/ A + k <= 738816 \/ (1323916 <= A /\ A + k <= lo)) -> disjoint_from [(q - 2144 - 48, q - 2144); (1323912, 1323912 + 4); (740096, 740096 + 8 + NM2); (1002304, 1268488 + 40)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 HNM2 LOH LQ1; lia).
    eapply (rw_cells_transport asegs _ mB mI) in FR; [| exact MUi| exact WMi| apply DJI; left; clear; lia].
    destruct TRE as (TR1 & TR2 & TR3).
    eapply (rw_cells_transport asegs _ m mB) in TR1; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mB mI) in TR1; [| exact MUi| exact WMi| apply DJI; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ m mB) in TR2; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mB mI) in TR2; [| exact MUi| exact WMi| apply DJI; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ m mB) in TR3; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mB mI) in TR3; [| exact MUi| exact WMi| apply DJI; right; right; cbn [cells_size csize Nat.add]; clear - LOH; lia].

    lazymatch type of FR with rw_cells _ _ _ (CB 2080 ?jj :: ?post) =>
      apply (rw_cells_split_CB asegs mI (q - 2144) [] 2080 jj post [8; 8; 8; 240; 1800; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j0; CB 8 ?j1; CB 8 ?j2; CB 240 ?j3; CB 1800 ?j4; CB 8 ?j5; CB 8 ?j6; _; _; _; _; _; _; _; _] =>
      remember j0 as f0 eqn:Ef0; remember j1 as f1 eqn:Ef1; remember j2 as f2 eqn:Ef2; remember j3 as f3 eqn:Ef3; remember j4 as f4 eqn:Ef4; remember j5 as f5 eqn:Ef5; remember j6 as f6 eqn:Ef6 end.
    clear Ef0 Ef1 Ef2 Ef3 Ef4 Ef5 Ef6.
    hide MU. hide WM. hide MUi. hide WMi.
    pose proof (munch_refl [(q - 2144, q)] mI) as MUf. pose proof (wmono_refl asegs mI) as WMf.
    do 7 zstep.

    replace (q + -89) with (q - 2144 + 2055) by (clear; lia). replace (q + -2136) with (q - 2144 + 8) by (clear; lia). replace (q + -2120) with (q - 2144 + 24) by (clear; lia).
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
    { assert (TEA : thread_env L mB).
      { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
      assert (TEI : thread_env L mI).
      { eapply thread_env_frame_q; [exact TEA| exact MUi| exact WMi|]. unfold thread_clear_q, img_out_q, iastat.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [| clear - LOH LQ1 CLO T1 T2 T3 T4 HNM2; lia]).
        - right; left. clear - LOH LQ1. lia.
        - right; right; right; right; right. clear. lia.
        - right; right; right; right; left. clear - HNM2. lia.
        - right; right; right; right; left. clear. lia. }
      eapply thread_env_frame; [exact TEI| exact MUf| exact WMf|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }

    destruct (proj1 (rw_cells_app asegs mU (q - 2144) [CB 8 f0] _) FR) as [FJ FRz]. cbn [cells_size csize Nat.add] in FRz. replace (q - 2144 + Z.of_nat 8) with (q - 2136) in FRz by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2136) [C8 (wz (q - 2144 + 24))] _) FRz) as [F0 FRa]. cbn [cells_size csize Nat.add] in FRa. replace (q - 2136 + Z.of_nat 8) with (q - 2136 + 8) in FRa by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2136 + 8) [C8 (wz 0)] _) FRa) as [F8 FRb]. cbn [cells_size csize Nat.add] in FRb. replace (q - 2136 + 8 + Z.of_nat 8) with (q - 2136 + 16) in FRb by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2136 + 16) [CB 240 f3] _) FRb) as [F16 FRc]. cbn [cells_size csize Nat.add] in FRc. replace (q - 2136 + 16 + Z.of_nat 240) with (q - 2136 + 256) in FRc by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2136 + 256) [CB 1800 f4] _) FRc) as [F256 FRd]. cbn [cells_size csize Nat.add] in FRd. replace (q - 2136 + 256 + Z.of_nat 1800) with (q - 2136 + 2056) in FRd by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2136 + 2056) [C8 (wz q)] _) FRd) as [F2056 FRe]. cbn [cells_size csize Nat.add] in FRe. replace (q - 2136 + 2056 + Z.of_nat 8) with (q - 72) in FRe by (clear; lia).
    clear FR FRz FRa FRb FRc FRd.
    apply (rw_cells_C8_C4C4 mU (q - 2136 + 8) [] 0 [] ltac:(lia)) in F8. cbn [app] in F8.
    destruct (u64arr_of_CB mU (q - 2136 + 16) 30 f3 F16) as (ws & LWS & BUF).

    destruct (rw_cells_take3 asegs mU (q - 72) [CB 8 f6; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0] [C8 ra] FRe) as (_ & GS0 & GRA).
    cbn [cells_size csize Nat.add] in GS0, GRA. replace (q - 72 + Z.of_nat 56) with (q - 16) in GS0, GRA by (clear; lia). replace (q - 16 + Z.of_nat 8) with (q - 8) in GRA by (clear; lia).
    pose proof (rd64_of_C8 mU (q - 8) ra GRA) as RDRA. pose proof (rd64_of_C8 mU (q - 16) s0 GS0) as RDS0.

    assert (CHU : fpchain mU (at_top L) q (bv_unsigned s0) ras).
    { eapply fpchain_frame; [| exact MUf| exact WMf| constructor; [cbn [fst snd]; clear; lia| constructor]].
      eapply fpchain_frame; [| exact MUi| exact WMi| repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LOH LQ1 HNM2; lia].
      eapply fpchain_frame; [exact CH| exact MU| exact WM| constructor; [cbn [fst snd]; clear; lia| constructor]]. }
    replace (q + -2144) with (q - 2144) by (clear; lia).
    eapply evt_cut.
    { eapply (ui_entry L _ gp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ _ F_ fc (q - 2144) (q - 2136) 363372 mU
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

    replace (ret_pc (Z_to_bv 64 363464)) with (Z_to_bv 64 363464) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    destruct (proj1 (rw_cells_app asegs mU (q - 2136 + 8) [C4 (wz 0)] [C4 (wz 0)]) F8) as [_ TAG].
    cbn [cells_size csize Nat.add] in TAG. replace (q - 2136 + 8 + Z.of_nat 4) with (q - 2136 + 12) in TAG by (clear; lia).
    assert (DJW : forall A k, ((q - 2144 <= A /\ A + k <= q - 2136 + 8) \/ (q - 2136 + 12 <= A /\ A + k <= q - 2136 + 16) \/ (q - 2136 + 256 <= A /\ A + k <= q - 2136 + 2056) \/ q - 2136 + 2064 <= A) ->
              disjoint_from [(lo, q - 2144); (q - 2136 + 8, q - 2136 + 12); (q - 2136 + 16, q - 2136 + 256); (q - 2136 + 2056, q - 2136 + 2064); (THR + 3168, THR + 3169)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 T4 CLO LQ1; lia).
    eapply (rw_cells_transport asegs _ mU mW) in FJ; [| exact MUw| exact WMw| apply DJW; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in F0; [| exact MUw| exact WMw| apply DJW; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in TAG; [| exact MUw| exact WMw| apply DJW; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in F256; [| exact MUw| exact WMw| apply DJW; right; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in FRe; [| exact MUw| exact WMw| apply DJW; right; right; right; clear; lia].
    set (tr := realloc_tr ra ras).
    assert (ETR : [363372; bv_unsigned ra] ++ ras = tr) by reflexivity. rewrite ETR in SZW, TRW.
    destruct (proj1 (rw_cells_app asegs mW (q - 2136 + 8) [C4 (wz (Z.of_nat (length tr)))] [C4 tgw]) SZW) as [SZ1 _].
    assert (TAG' : rw_cells asegs mW (q - 2136 + 8 + Z.of_nat (cells_size [C4 (wz (Z.of_nat (length tr)))])) [C4 (wz 0)]).
    { cbn [cells_size csize Nat.add]. replace (q - 2136 + 8 + Z.of_nat 4) with (q - 2136 + 12) by (clear; lia). exact TAG. }
    pose proof (proj2 (rw_cells_app asegs mW (q - 2136 + 8) [C4 (wz (Z.of_nat (length tr)))] [C4 (wz 0)]) (conj SZ1 TAG')) as SZ8.
    cbn [app] in SZ8.
    assert (LTR : (1 <= length tr <= 30)%nat) by (unfold tr, realloc_tr; cbn [length]; clear - LRAS; lia).
    apply (rw_cells_C4C4_C8 mW (q - 2136 + 8) [] (Z.of_nat (length tr)) [] ltac:(clear - LTR; lia)) in SZ8. cbn [app] in SZ8.
    replace (q - 2144 + 24) with (q - 2136 + 16) in F0 by (clear; lia).
    assert (SZ8' : rw_cells asegs mW (q - 2136 + Z.of_nat (cells_size [C8 (wz (q - 2136 + 16))])) [C8 (wz (Z.of_nat (length tr)))]).
    { cbn [cells_size csize Nat.add]. replace (q - 2136 + Z.of_nat 8) with (q - 2136 + 8) by (clear; lia). exact SZ8. }
    pose proof (proj2 (rw_cells_app asegs mW (q - 2136) [C8 (wz (q - 2136 + 16))] [C8 (wz (Z.of_nat (length tr)))]) (conj F0 SZ8')) as SOBJ.
    cbn [app] in SOBJ.

    assert (MUT : munch WN m mW).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_trans; [eapply munch_weaken; [| exact MUi]| eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_weaken; [| exact MUw]]]];
        unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & O3 & O4 & O5 & _); repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
    pose proof (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMi (wmono_trans asegs _ _ _ WMf WMw))) as WMT.
    assert (IAW : ia_cells NM2 NM4 true mW).
    { assert (MUID : munch [(lo, q); (THR + 3168, THR + 3169)] mI mW).
      { eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_weaken; [| exact MUw]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _);
          repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
      assert (TRC : forall A cs, rw_cells asegs mI A cs -> 740096 <= A -> A + Z.of_nat (cells_size cs) <= 1323916 -> rw_cells asegs mW A cs).
      { intros A cs C H1 H2. eapply rw_cells_transport_m; [exact C| exact MUID|]. cbn [disjoint_from]. clear - H1 H2 LOH T3. lia. }
      destruct IAI as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM2; lia); clear - HNM2; lia]|].
      split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM4; lia); clear - HNM4; lia]|].
      exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
    pose proof (CPREF mW MUT WMT MIW TEW IAW) as CPW.
    hide MU. hide WM. hide MUi. hide WMi. hide MUf. hide WMf. hide MUw. hide WMw.

    do 2 zstep.
    replace (q + -2136) with (q - 2136) by (clear; lia).
    do 2 zstep.
    zstep.
    lz_here.
    rewrite <- (ebind_ret_r TREE).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (CALLEE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mW ws'); [ assumption | exact STW | exact SOBJ | exact BUFW | exact LWS' | exact TRW | exact CPW ]. }
    intros r2 H2 ms2 [PO MC2]. unfold rcallee_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & W2 & -> & MU2 & DJ2 & ST2 & CP2).
    clean_ms_mem MC2.

    eapply (rw_cells_transport_m _ mW m2) in FJ; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in SOBJ; [| exact MU2| apply DJ2; clear; lia].
    eapply (u64arr_transport_m _ mW m2) in BUFW; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in F256; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in TFW; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in FRe; [| exact MU2| apply DJ2; clear; lia].
    pose proof (CB_of_u64arr m2 (q - 2136 + 16) ws' BUFW) as CBW. rewrite LWS' in CBW. change (8 * 30)%nat with 240%nat in CBW.
    assert (J4 : rw_cells asegs m2 (q - 2136 + 2056) ([C8 (wz q)] ++ [CB 8 f6; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2136 + 2056) [C8 (wz q)] _)). split; [exact TFW|].
      cbn [cells_size csize Nat.add]. replace (q - 2136 + 2056 + Z.of_nat 8) with (q - 72) by (clear; lia). exact FRe. }
    assert (J3 : rw_cells asegs m2 (q - 2136 + 256) ([CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2136 + 256) [CB 1800 f4] _)). split; [exact F256|].
      cbn [cells_size csize Nat.add]. replace (q - 2136 + 256 + Z.of_nat 1800) with (q - 2136 + 2056) by (clear; lia). exact J4. }
    assert (J2 : rw_cells asegs m2 (q - 2136 + 16) ([CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2136 + 16) [CB 240 (u64s ws')] _)). split; [exact CBW|].
      cbn [cells_size csize Nat.add]. replace (q - 2136 + 16 + Z.of_nat 240) with (q - 2136 + 256) by (clear; lia). exact J3. }
    assert (J1 : rw_cells asegs m2 (q - 2136) ([C8 (wz (q - 2136 + 16)); C8 (wz (Z.of_nat (length tr)))] ++ [CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2136) [C8 (wz (q - 2136 + 16)); C8 (wz (Z.of_nat (length tr)))] _)). split; [exact SOBJ|].
      cbn [cells_size csize Nat.add]. replace (q - 2136 + Z.of_nat 16) with (q - 2136 + 16) by (clear; lia). exact J2. }
    assert (FRJ : rw_cells asegs m2 (q - 2144) ([CB 8 f0] ++ [C8 (wz (q - 2136 + 16)); C8 (wz (Z.of_nat (length tr)))] ++ [CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2144) [CB 8 f0] _)). split; [exact FJ|].
      cbn [cells_size csize Nat.add]. replace (q - 2144 + Z.of_nat 8) with (q - 2136) by (clear; lia). exact J1. }
    cbn [app] in FRJ. clear J1 J2 J3 J4 SOBJ F256 TFW FRe CBW FJ.
    lz_go.
    replace (ret_pc (Z_to_bv 64 363484)) with (Z_to_bv 64 363484) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    do 8 zstep.
    zstep. replace (q - 2144 + 2144) with q by (clear; lia). zstep.
    release_frame FRJ ST2 q.
    lz_ret. apply evt_done. unfold ricpt_post.
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, mW, m2, W2.
    split; [reflexivity|]. split; [exact MUT|]. split; [exact WMT|]. split; [exact MU2|]. split; [exact DJ2|]. split; [exact ST2| exact CP2].
  Qed.

End RICPT.

