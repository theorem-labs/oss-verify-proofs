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

Definition malloc_icpt_entry : Z := 0x58630.
Definition asan_malloc_entry : Z := 0x335fc.

Section MICPT.
  Context {HC : HasCeiling}.
  Variable L : athread.
  Notation THR := (at_thr L).
  Hypothesis TLO : thread_layout_ok L.
  Variables (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - 4096.
  Hypothesis QTOP : q + 16 < at_top L.
  Hypothesis Q16 : q mod 16 = 0.

  Notation WM_ := [(lo, q); (THR + 3168, THR + 3169)].
  Notation T := (q - 2128).

  Definition malloc_tr (ra : word) (ras : list Z) : list Z := PC0_MALLOC :: bv_unsigned ra :: ras.

  Variables (ra : word) (ras : list Z).

  Variable RT : Type.
  Variable TREE : itree nodeL (exc RT).
  Variable H : word -> bool.
  Variable size : Z.
  Variable CPRE : mem -> Prop.
  Variable CPOST : mem -> RT -> (word -> bool) -> word -> mem -> Prop.

  Definition mcallee_post (ra' s0 s1 s2 s3 s4 s5 : word) (mW : mem) : RT -> (word -> bool) -> machine_state -> Prop :=
    fun r H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 W,
      ms' = MS (mkR ra' (wz (q - 2128)) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra') fc None m2 (seg_rom asegs)
      /\ munch W mW m2 /\ (forall A k, q - 2128 <= A -> disjoint_from W A k) /\ stk asegs m2 lo (q - 2128)
      /\ CPOST mW r H' a0 m2.

  Hypothesis CALLEE : forall (ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (mW : mem) (ws : list word),
    mclean H mW -> stk asegs mW lo (q - 2128) ->
    rw_cells asegs mW T [C8 (wz (T + 16)); C8 (wz (Z.of_nat (length (malloc_tr ra ras))))] -> u64arr asegs mW (T + 16) ws -> length ws = 30%nat ->
    firstn (length (malloc_tr ra ras)) ws = map wz (malloc_tr ra ras) ->
    CPRE mW ->
    implA H TREE (mcallee_post ra' s0 s1 s2 s3 s4 s5 mW)
      (MS (mkR ra' (wz (q - 2128)) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz size) (wz T) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz asan_malloc_entry) fc None mW (seg_rom asegs)).

  Definition micpt_post (s0 s1 s2 s3 s4 s5 : word) (m : mem) : RT -> (word -> bool) -> machine_state -> Prop :=
    fun r H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mW m' W,
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch WM_ m mW /\ wmono asegs m mW /\ munch W mW m' /\ (forall A k, q - 2128 <= A -> disjoint_from W A k)
      /\ stk asegs m' lo q /\ CPOST mW r H' a0 m'.

  #[using="HC TLO LOH CLO LOQ QTOP Q16 CALLEE"] Theorem malloc_icpt_spec : forall (t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
        (m : mem),
    mclean H m -> stk asegs m lo q -> mem_inv asegs m -> thread_env L m -> trace_env m ->
    fpchain m (at_top L) q (bv_unsigned s0) ras -> (length ras <= 28)%nat -> Forall (fun r => r <> PC0_MALLOC) ras ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> PC0_MALLOC ->
    (forall mW, munch WM_ m mW -> wmono asegs m mW -> mem_inv asegs mW -> thread_env L mW -> CPRE mW) ->
    implA H TREE (micpt_post s0 s1 s2 s3 s4 s5 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz size) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz malloc_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m MC ST MI0 TE TRE CH LRAS NPC RA4 RANE CPREF.
    unfold malloc_icpt_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ1 : lo <= q - 2128 - 512) by (clear - LOQ; lia).
    assert (LQ3 : alloc_ceiling + 4096 <= q) by (clear - LOQ CLO; lia).
    pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    pose proof (munch_refl [(q - 2144, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep.
    zstep. carve_frame 2128%nat ST.

    do 7 zstep.
    zstep.
    zstep.
    do 2 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -2128) with (q - 2128) in * by lia.
    assert (DJA : forall A k, A + k <= lo -> disjoint_from [(q - 2144, q)] A k) by (intros A k D1; cbn [disjoint_from]; clear - D1 LQ1; lia).
    pose proof TE as TEc. te_split TEc.
    eapply (rw_cells_transport asegs _ m mA) in TE_inited; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].

    zstep. carve_frame 16%nat ST.
    replace (q + -2128 + -16) with (q + -2144) in * by (clear; lia).
    do 2 sstep.
    do 2 zstep.
    zstep.
    do 2 zstep.
    zstep. lit_branch.
    do 2 zstep.
    zstep.
    zstep.
    release_frame FR0 ST (q + -2128).
    replace (ret_pc (Z_to_bv 64 362556)) with (Z_to_bv 64 362556) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. lit_branch.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    replace (q + -2128) with (q - 2128) in * by lia.

    destruct TRE as (TR1 & TR2 & TR3).
    eapply (rw_cells_transport asegs _ m mB) in TR1; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ m mB) in TR2; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ m mB) in TR3; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].

    lazymatch type of FR with rw_cells _ _ _ (CB 2072 ?jj :: ?post) =>
      apply (rw_cells_split_CB asegs mB (q - 2128) [] 2072 jj post [8; 8; 240; 1800; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j1; CB 8 ?j2; CB 240 ?j3; CB 1800 ?j4; CB 8 ?j5; CB 8 ?j6; _; _; _; _; _; _; _] =>
      remember j1 as f1 eqn:Ef1; remember j2 as f2 eqn:Ef2; remember j3 as f3 eqn:Ef3; remember j4 as f4 eqn:Ef4; remember j5 as f5 eqn:Ef5; remember j6 as f6 eqn:Ef6 end.
    clear Ef1 Ef2 Ef3 Ef4 Ef5 Ef6.
    hide MU. hide WM.
    pose proof (munch_refl [(q - 2128, q)] mB) as MUf. pose proof (wmono_refl asegs mB) as WMf.
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
    unhide MU. unhide WM.
    assert (TEU : thread_env L mU).
    { assert (TEA : thread_env L mB).
      { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
      eapply thread_env_frame; [exact TEA| exact MUf| exact WMf|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
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
      eapply fpchain_frame; [exact CH| exact MU| exact WM| constructor; [cbn [fst snd]; clear; lia| constructor]]. }
    replace (q + -2128) with (q - 2128) by (clear; lia).
    eapply evt_cut.
    { eapply (ui_entry L _ gp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ _ F_ fc (q - 2128) (q - 2128) 362704 mU
                ltac:(clear - QTOP; lia) ltac:(clear; lia) TLO lo q (bv_unsigned ra) (bv_unsigned s0) ras ws (wz 0) (wz 0) (wz q)).
      - exact ST.
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
      - assumption. }
    cbv beta. unfold ui_post.
    intros msW (w0 & w1 & w2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & mW & ws' & tgw & -> & MUw & WMw & MIW & STW & TEW & SZW & BUFW & LWS' & TRW & TFW).
    replace (ret_pc (Z_to_bv 64 362796)) with (Z_to_bv 64 362796) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 8) [C4 (wz 0)] [C4 (wz 0)]) F8) as [_ TAG].
    cbn [cells_size csize Nat.add] in TAG. replace (q - 2128 + 8 + Z.of_nat 4) with (q - 2128 + 12) in TAG by (clear; lia).
    assert (DJW : forall A k, ((q - 2128 <= A /\ A + k <= q - 2128 + 8) \/ (q - 2128 + 12 <= A /\ A + k <= q - 2128 + 16) \/ (q - 2128 + 256 <= A /\ A + k <= q - 2128 + 2056) \/ q - 2128 + 2064 <= A) ->
              disjoint_from [(lo, q - 2128); (q - 2128 + 8, q - 2128 + 12); (q - 2128 + 16, q - 2128 + 256); (q - 2128 + 2056, q - 2128 + 2064); (THR + 3168, THR + 3169)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 T4 CLO LQ1; lia).
    eapply (rw_cells_transport asegs _ mU mW) in F0; [| exact MUw| exact WMw| apply DJW; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in TAG; [| exact MUw| exact WMw| apply DJW; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in F256; [| exact MUw| exact WMw| apply DJW; right; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in FRe; [| exact MUw| exact WMw| apply DJW; right; right; right; clear; lia].
    set (tr := malloc_tr ra ras).
    assert (ETR : [362704; bv_unsigned ra] ++ ras = tr) by reflexivity. rewrite ETR in SZW, TRW.
    destruct (proj1 (rw_cells_app asegs mW (q - 2128 + 8) [C4 (wz (Z.of_nat (length tr)))] [C4 tgw]) SZW) as [SZ1 _].
    assert (TAG' : rw_cells asegs mW (q - 2128 + 8 + Z.of_nat (cells_size [C4 (wz (Z.of_nat (length tr)))])) [C4 (wz 0)]).
    { cbn [cells_size csize Nat.add]. replace (q - 2128 + 8 + Z.of_nat 4) with (q - 2128 + 12) by (clear; lia). exact TAG. }
    pose proof (proj2 (rw_cells_app asegs mW (q - 2128 + 8) [C4 (wz (Z.of_nat (length tr)))] [C4 (wz 0)]) (conj SZ1 TAG')) as SZ8.
    cbn [app] in SZ8.
    assert (LTR : (1 <= length tr <= 30)%nat) by (unfold tr, malloc_tr; cbn [length]; clear - LRAS; lia).
    apply (rw_cells_C4C4_C8 mW (q - 2128 + 8) [] (Z.of_nat (length tr)) [] ltac:(clear - LTR; lia)) in SZ8. cbn [app] in SZ8.
    assert (SZ8' : rw_cells asegs mW (q - 2128 + Z.of_nat (cells_size [C8 (wz (q - 2128 + 16))])) [C8 (wz (Z.of_nat (length tr)))]).
    { cbn [cells_size csize Nat.add]. replace (q - 2128 + Z.of_nat 8) with (q - 2128 + 8) by (clear; lia). exact SZ8. }
    pose proof (proj2 (rw_cells_app asegs mW (q - 2128) [C8 (wz (q - 2128 + 16))] [C8 (wz (Z.of_nat (length tr)))]) (conj F0 SZ8')) as SOBJ.
    cbn [app] in SOBJ.
    assert (MUT : munch WM_ m mW).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_weaken; [| exact MUw]]];
        unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _); repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
    pose proof (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMf WMw)) as WMT.
    pose proof (CPREF mW MUT WMT MIW TEW) as CPW.
    hide MU. hide WM. hide MUf. hide WMf. hide MUw. hide WMw.

    do 2 zstep.
    replace (q + -2128) with (q - 2128) by (clear; lia).
    zstep.
    zstep.
    lz_here.
    rewrite <- (ebind_ret_r TREE).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (CALLEE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mW ws'); [ assumption | exact STW | exact SOBJ | exact BUFW | exact LWS' | exact TRW | exact CPW ]. }
    intros r2 H2 ms2 [PO MC2]. unfold mcallee_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & W2 & -> & MU2 & DJ2 & ST2 & CP2).
    clean_ms_mem MC2.

    eapply (rw_cells_transport_m _ mW m2) in SOBJ; [| exact MU2| apply DJ2; clear; lia].
    eapply (u64arr_transport_m _ mW m2) in BUFW; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in F256; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in TFW; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in FRe; [| exact MU2| apply DJ2; clear; lia].
    pose proof (CB_of_u64arr m2 (q - 2128 + 16) ws' BUFW) as CBW. rewrite LWS' in CBW. change (8 * 30)%nat with 240%nat in CBW.
    assert (J4 : rw_cells asegs m2 (q - 2128 + 2056) ([C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128 + 2056) [C8 (wz q)] _)). split; [exact TFW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 2056 + Z.of_nat 8) with (q - 64) by (clear; lia). exact FRe. }
    assert (J3 : rw_cells asegs m2 (q - 2128 + 256) ([CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128 + 256) [CB 1800 f4] _)). split; [exact F256|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 256 + Z.of_nat 1800) with (q - 2128 + 2056) by (clear; lia). exact J4. }
    assert (J2 : rw_cells asegs m2 (q - 2128 + 16) ([CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128 + 16) [CB 240 (u64s ws')] _)). split; [exact CBW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 16 + Z.of_nat 240) with (q - 2128 + 256) by (clear; lia). exact J3. }
    assert (FRJ : rw_cells asegs m2 (q - 2128) ([C8 (wz (q - 2128 + 16)); C8 (wz (Z.of_nat (length tr)))] ++ [CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128) [C8 (wz (q - 2128 + 16)); C8 (wz (Z.of_nat (length tr)))] _)). split; [exact SOBJ|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + Z.of_nat 16) with (q - 2128 + 16) by (clear; lia). exact J2. }
    cbn [app] in FRJ. clear J2 J3 J4 SOBJ F256 TFW FRe CBW.
    lz_go.
    replace (ret_pc (Z_to_bv 64 362812)) with (Z_to_bv 64 362812) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    do 7 zstep.
    zstep. replace (q - 2128 + 2128) with q by (clear; lia). zstep.
    release_frame FRJ ST2 q.
    lz_ret. apply evt_done. unfold micpt_post.
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, mW, m2, W2.
    split; [reflexivity|]. split; [exact MUT|]. split; [exact WMT|]. split; [exact MU2|]. split; [exact DJ2|]. split; [exact ST2| exact CP2].
  Qed.

End MICPT.

