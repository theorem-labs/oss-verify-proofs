(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv F_unwind.
Import ListNotations.
Open Scope Z_scope.

Definition unwind_entry := 0x79504%Z.

Section S.
Context {HC : HasCeiling}.
  Variables (ra0 gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t2 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q T top pc0 : Z) (m0 : mem).
  Hypothesis QT : 64 <= q + -64 /\ q <= T + 8 /\ T + 16 + 240 <= top /\ top <= 2^47.
  Hypothesis PC0 : 0 <= pc0 < 2^64.
  Notation W := [(q + -64, q); (T + 8, T + 12); (T + 16, T + 256)].
  Notation W2 := [(q + -64, q); (T + 8, T + 12); (T + 16, T + 256); (T + 2056, T + 2064)].

  Definition uw_post (tr rest : list Z) (lo bp : Z) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2' a0 a1 a2 a3 a4 a5 a6 a7 t3' t4' t5' t6' m' (ws' : list word) (tg : word),
      ms' = MS (mkR ra0 (wz q) gp tp t0 t1 t2' s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F_ (ret_pc ra0) fc None m' (seg_rom asegs)
      /\ munch W2 m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (T + 8) [C4 (wz (Z.of_nat (length (tr ++ rest)))); C4 tg]
      /\ u64arr asegs m' (T + 16) ws' /\ length ws' = 30%nat /\ firstn (length (tr ++ rest)) ws' = map wz (tr ++ rest)
      /\ (exists junk, rw_cells asegs m' (q + -64) [CB 64 junk]) /\ stk asegs m' lo (q + -64)
      /\ rw_cells asegs m' (T + 2056) [C8 (wz bp)].

  #[using="QT PC0"] Lemma uw_entry : forall (lo bp bottom ra1 a1' : Z) (ras : list Z) (ws : list word) (szj tg tfj : word) t0 t1,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q + -64 ->
    rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    rw_cells asegs m0 (T + 8) [C4 szj; C4 tg] -> u64arr asegs m0 (T + 16) ws -> length ws = 30%nat ->
    rw_cells asegs m0 (T + 2056) [C8 tfj] ->
    bottom < bp -> bp < top - 16 -> bp mod 8 = 0 -> bottom < top -> 4096 <= top ->
    T + 2064 + 16 <= bp ->
    rd64 m0 (bp - 8) ra1 -> 4096 <= ra1 -> ra1 <> pc0 ->
    rd64 m0 (bp - 16) a1' -> fpchain m0 top bp a1' ras -> Forall (fun r => r <> pc0) ras -> (length ras <= 28)%nat ->
    0 <= bottom ->
    mem_inv asegs m0 ->
    evt asegs (uw_post [pc0; ra1] ras lo bp)
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0v s1v (wz T) (wz 30) (wz pc0) (wz bp) (wz 0) (wz top) (wz bottom) (wz 1)
                s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz unwind_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo bp bottom ra1 a1' ras ws szj tg tfj t0 t1 ST CLO LO GP PG SZ BUF LWS TF V1 V2 V3 BT TP LOA R1 R1P R1N R2 CH NP LR B0 MI.
    unfold unwind_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl W2 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB. rewrite LWS in BB.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 64%nat ST. rewrite !E in *.
    destruct R1 as [R1B R1R]. destruct R2 as [R2B R2R].
    do 8 sstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z.land ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) bp) with bp.
    2:{ change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
        rewrite Z.land_comm, Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
    sstep.
    zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso; lia. }
    zstep. zstep. zstep. zstep. zstep.
    do 7 zstep.
    zstep. replace (q + -64 + 64) with q by lia.
    zstep.
    release_frame FR ST q.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (fpchain_frame ras _ mm top bp a1' _ CH MU WM ltac:(repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil)) as CH1 end.
    clear CH.
    call (uf_entry ra0 gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 _ _ t2 t3 t4 t5 t6 F_ fc q T top pc0 _ QT PC0
             lo bp bottom ra1 a1' ras ws szj tg).
    all: side (try (first [ eassumption | lia | (split; [assumption| lia]) ])).
    apply evt_done. unfold uw_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  #[using="QT PC0"] Lemma uw_entry_top : forall (lo bp bottom : Z) (ws : list word) (szj tg tfj : word) t0 t1,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q + -64 ->
    rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    rw_cells asegs m0 (T + 8) [C4 szj; C4 tg] -> u64arr asegs m0 (T + 16) ws -> length ws = 30%nat ->
    rw_cells asegs m0 (T + 2056) [C8 tfj] ->
    bottom < bp -> top - 16 <= bp -> bp <= 2^47 -> bottom < top -> 4096 <= top ->
    0 <= bottom ->
    mem_inv asegs m0 ->
    evt asegs (uw_post [pc0] [] lo bp)
      (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0v s1v (wz T) (wz 30) (wz pc0) (wz bp) (wz 0) (wz top) (wz bottom) (wz 1)
                s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (wz unwind_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo bp bottom ws szj tg tfj t0 t1 ST CLO LO GP PG SZ BUF LWS TF V1 V2 BPH BT TP B0 MI.
    unfold unwind_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl W2 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB. rewrite LWS in BB.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 64%nat ST. rewrite !E in *.
    do 8 sstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z.land ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) bp) with bp.
    2:{ change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
        rewrite Z.land_comm, Z.land_ones by lia. symmetry. apply Z.mod_small. change (2^47) with 140737488355328 in BPH. lia. }
    sstep.
    zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso; lia. }
    zstep. zstep. zstep. zstep. zstep.
    do 7 zstep.
    zstep. replace (q + -64 + 64) with q by lia.
    zstep.
    release_frame FR ST q.
    call (uf_entry_top ra0 gp tp s0v s1v s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 _ _ t2 t3 t4 t5 t6 F_ fc q T top pc0 _ QT PC0
             lo bp bottom ws szj tg).
    all: side (try (first [ eassumption | lia | (split; [assumption| lia]) | (change (2^47) with 140737488355328 in BPH; change (2^64) with 18446744073709551616; lia) ])).
    apply evt_done. unfold uw_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End S.

Definition unwind_impl_entry := 0x603b4%Z.

Lemma land_sel_true : forall c t, c = true -> 0 <= t < 2^64 -> Z.land ((0 - Z.b2z c) mod 18446744073709551616) t = t.
Proof.
  intros c t -> Ht. change ((0 - Z.b2z true) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section UI.
Context {HC : HasCeiling}.
  Variable L : athread.
  Variables (ra0 gp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9 s10 s11 t2 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q T pc0 : Z) (m0 : mem).

  Hypothesis QT : q <= T /\ T + 2064 + 16 <= at_top L.
  Hypothesis PC0 : 0 <= pc0 < 2^64.
  Hypothesis TL : thread_layout_ok L.
  Notation top := (at_top L). Notation bottom := (at_bottom L). Notation thr := (at_thr L).
  Notation W3 lo := [(lo, q); (T + 8, T + 12); (T + 16, T + 256); (T + 2056, T + 2064); (at_thr L + 3168, at_thr L + 3169)].

  Definition ui_post (lo bp : Z) (tr rest : list Z) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2' a0 a1 a2 a3 a4 a5 a6 a7 t3' t4' t5' t6' m' (ws' : list word) (tg : word),
      ms' = MS (mkR ra0 (wz q) gp (wz A0_TP) t0 t1 t2' s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9 s10 s11 t3' t4' t5' t6')
               F_ (ret_pc ra0) fc None m' (seg_rom asegs)
      /\ munch (W3 lo) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ thread_env L m'
      /\ rw_cells asegs m' (T + 8) [C4 (wz (Z.of_nat (length (tr ++ rest)))); C4 tg]
      /\ u64arr asegs m' (T + 16) ws' /\ length ws' = 30%nat /\ firstn (length (tr ++ rest)) ws' = map wz (tr ++ rest)
      /\ rw_cells asegs m' (T + 2056) [C8 (wz bp)].

  #[using="QT PC0 TL"] Lemma ui_entry : forall (lo bp ra1 a1' : Z) (ras : list Z) (ws : list word) (szj tg tfj : word) t0 t1 a6 a7,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo + 512 <= q -> alloc_ceiling + 4096 <= bp ->
    thread_env L m0 ->
    rw_cells asegs m0 (T + 8) [C4 szj; C4 tg] -> u64arr asegs m0 (T + 16) ws -> length ws = 30%nat ->
    rw_cells asegs m0 (T + 2056) [C8 tfj] ->
    q <= bp -> bp < top - 16 -> bp mod 8 = 0 -> T + 2064 + 16 <= bp ->
    rd64 m0 (bp - 8) ra1 -> 4096 <= ra1 -> ra1 <> pc0 ->
    rd64 m0 (bp - 16) a1' -> fpchain m0 top bp a1' ras -> Forall (fun r => r <> pc0) ras -> (length ras <= 28)%nat ->
    mem_inv asegs m0 ->
    evt asegs (ui_post lo bp [pc0; ra1] ras)
      (MS (mkR ra0 (wz q) gp (wz A0_TP) t0 t1 t2 s0v s1v (wz T) (wz pc0) (wz bp) (wz 0) (wz 1) (wz 30) a6 a7
                s2v s3v s4v s5v s6v s7v s8v s9 s10 s11 t3 t4 t5 t6) F_ (wz unwind_impl_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo bp ra1 a1' ras ws szj tg tfj t0 t1 a6 a7 ST CLO LO QHI TE SZ BUF LWS TF V1 V2 V3 LOA R1 R1P R1N R2 CH NP LR MI.
    unfold unwind_impl_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold thread_layout_ok in TL.
    pose proof (munch_refl (W3 lo) m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB. rewrite LWS in BB.
    te_split TE.
    destruct R1 as [R1B R1R]. destruct R2 as [R2B R2R].
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 80%nat ST. rewrite !E in *.
    do 11 sstep.
    do 6 zstep.
    sstep.

    zstep. zstep. zstep.
    change (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1).
    zstep. zstep. zstep. zstep.
    zstep. if_cases KI; zify_cond KI. { exfalso. revert KI. clear. intros KI. lia. }

    zstep.
    carve_frame 16%nat ST.
    zstep. sstep.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. clear. intros KT. lia. }
    zstep. zstep.
    zstep.   zstep.
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. zstep. zstep.
    zstep.   zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso; lia. }
    zstep.   zstep. zstep.
    replace (q + -80 + -16 + 16) with (q + -80) by lia.
    zstep.
    release_frame FR0 ST (q + -80).
    zstep. if_cases KTH; zify_cond KTH. { exfalso; lia. }
    zstep.
    zstep.
    zstep.
    sstep.
    zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. clear. intros KU. lia. }
    zstep.

    zstep. zstep.
    change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    zstep. zstep. if_cases KS; zify_cond KS. 2:{ exfalso. revert KS. clear. intros KS. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (land_sel_true (bottom <? top) top) by (first [apply Z.ltb_lt; lia | lia]).
    zstep.   zstep. zstep.

    zstep. zstep.
    change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    zstep. zstep. if_cases KS2; zify_cond KS2. 2:{ exfalso. revert KS2. clear. intros KS2. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (land_sel_true (bottom <? top) bottom) by (first [apply Z.ltb_lt; lia | lia]).
    zstep.   zstep.
    zstep. if_cases KF; zify_cond KF. { exfalso. revert KF. clear. intros KF. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (fpchain_frame ras _ mm top bp a1' _ CH MU WM ltac:(repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil)) as CH1 end.
    clear CH.
    call (uw_entry _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ s9 s10 s11 _ _ _ _ _ F_ fc (q + -80) T top pc0 _ ltac:(lia) PC0
             lo bp bottom ra1 a1' ras ws _ tg tfj).
    all: side (try (first [ eassumption | lia | (split; [assumption| lia]) ])).
    match goal with J : ex _ |- _ => match type of J with context [CB 64] => destruct J as [jk JK] end end.

    sstep.
    do 10 zstep. zstep. replace (q + -80 + 80) with q by lia. zstep.

    match goal with P : stk asegs _ lo (q + -80 + -64) |- _ => release_frame JK P (q + -80) end.
    match goal with P : stk asegs _ lo (q + -80) |- _ => release_frame FR P q end.
    apply evt_done. unfold ui_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    all: repeat match goal with |- _ /\ _ => split end; try eassumption.
    all: unfold thread_env; repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  #[using="PC0 TL"] Lemma ui_entry_top : forall (lo bp : Z) (ws : list word) (szj tg tfj : word) t0 t1 a6 a7,
    q <= T -> T + 16 + 240 <= top ->
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo + 512 <= q -> alloc_ceiling + 4096 <= bp ->
    thread_env L m0 ->
    rw_cells asegs m0 (T + 8) [C4 szj; C4 tg] -> u64arr asegs m0 (T + 16) ws -> length ws = 30%nat ->
    rw_cells asegs m0 (T + 2056) [C8 tfj] ->
    q <= bp -> top - 16 <= bp -> bp <= 2^47 -> T + 2064 + 16 <= bp ->
    mem_inv asegs m0 ->
    evt asegs (ui_post lo bp [pc0] [])
      (MS (mkR ra0 (wz q) gp (wz A0_TP) t0 t1 t2 s0v s1v (wz T) (wz pc0) (wz bp) (wz 0) (wz 1) (wz 30) a6 a7
                s2v s3v s4v s5v s6v s7v s8v s9 s10 s11 t3 t4 t5 t6) F_ (wz unwind_impl_entry) fc None m0 (seg_rom asegs)).
  Proof.
    clear QT. intros lo bp ws szj tg tfj t0 t1 a6 a7 QT1 QT2 ST CLO LO QHI TE SZ BUF LWS TF V1 V2 BPH LOA MI.
    unfold unwind_impl_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold thread_layout_ok in TL.
    pose proof (munch_refl (W3 lo) m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB. rewrite LWS in BB.
    te_split TE.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 80%nat ST. rewrite !E in *.
    do 11 sstep.
    do 6 zstep.
    sstep.

    zstep. zstep. zstep.
    change (sxb (Z_to_bv 8 1)) with (Z_to_bv 64 1).
    zstep. zstep. zstep. zstep.
    zstep. if_cases KI; zify_cond KI. { exfalso. revert KI. clear. intros KI. lia. }

    zstep.
    carve_frame 16%nat ST.
    zstep. sstep.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. clear. intros KT. lia. }
    zstep. zstep.
    zstep.   zstep.
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. zstep. zstep.
    zstep.   zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso; lia. }
    zstep.   zstep. zstep.
    replace (q + -80 + -16 + 16) with (q + -80) by lia.
    zstep.
    release_frame FR0 ST (q + -80).
    zstep. if_cases KTH; zify_cond KTH. { exfalso; lia. }
    zstep.
    zstep.
    zstep.
    sstep.
    zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. clear. intros KU. lia. }
    zstep.

    zstep. zstep.
    change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    zstep. zstep. if_cases KS; zify_cond KS. 2:{ exfalso. revert KS. clear. intros KS. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (land_sel_true (bottom <? top) top) by (first [apply Z.ltb_lt; lia | lia]).
    zstep.   zstep. zstep.

    zstep. zstep.
    change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    zstep. zstep. if_cases KS2; zify_cond KS2. 2:{ exfalso. revert KS2. clear. intros KS2. lia. }
    zstep. zstep. zstep. zstep. zstep.
    rewrite (land_sel_true (bottom <? top) bottom) by (first [apply Z.ltb_lt; lia | lia]).
    zstep.   zstep.
    zstep. if_cases KF; zify_cond KF. { exfalso. revert KF. clear. intros KF. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    call (uw_entry_top _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ s9 s10 s11 _ _ _ _ _ F_ fc (q + -80) T top pc0 _ ltac:(lia) PC0
             lo bp bottom ws _ tg tfj).
    all: side (try (first [ eassumption | lia | (split; [assumption| lia]) ])).
    match goal with J : ex _ |- _ => match type of J with context [CB 64] => destruct J as [jk JK] end end.

    sstep.
    do 10 zstep. zstep. replace (q + -80 + 80) with q by lia. zstep.

    match goal with P : stk asegs _ lo (q + -80 + -64) |- _ => release_frame JK P (q + -80) end.
    match goal with P : stk asegs _ lo (q + -80) |- _ => release_frame FR P q end.
    apply evt_done. unfold ui_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    all: repeat match goal with |- _ /\ _ => split end; try eassumption.
    all: unfold thread_env; repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End UI.
