(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import R_small R_m2s R_thread R_cache_defs R_prim_defs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import R_leaves I_ikit R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_allocate1 R_prim_kit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import R_asan_malloc R_setshadow R_allocate1C R_allocate3 F_memset.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import I_lkit R_asan_calloc RT_caltail RT_calcore_stmt RT_malloc.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Exec RzCPS MState.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface D_defs D_kit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import R_glue_defs R_poison R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_maltail RT_freelift RT_malcore_stmt.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require RT_traces G4_chain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_gaps_iface RT_g4_unwind RT_calloc_fn RT_calloc.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Ed_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition calloc_B_sec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (UB n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma calloc_B_sec_spec : forall ra sp gp tp t0 t1 t2 s1' a1 a2 a3 a4 a5 a6 a7 s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6
    ra0 s0 s1 s2 s3 s4 s5 s6 v1 v2 v3 (F : bvmap 5 word) fc (m : mem) (UB n SB lo : Z) (ws : list word) (w : word)
    (jp jq j1 : list byte),
  (0 < UB < 2^64)%Z -> (1 <= n <= 2^31)%Z -> (0 <= SB)%Z -> (SB + 2^37 < 2^64)%Z -> (UB + n <= SB \/ SB + 2^37 <= UB)%Z ->
  stk asegs m lo (bv_unsigned sp + -2192) -> (lo <= bv_unsigned sp + -2192)%Z -> (0x73a000 <= lo)%Z ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jp] ->
  rw_cells asegs m (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))] ->
  u64arr asegs m (bv_unsigned sp + -2120) ws -> length ws = 255%nat ->
  rw_cells asegs m (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w] ->
  rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jq] ->
  rw_cells asegs m (bv_unsigned sp + -2192) [CB 8 j1; C8 v3; C8 v2; C8 v1; C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0xb8d44)] ->
  rw_cells asegs m i_spacebeg [C8 (Z_to_bv 64 SB)] ->
  mem_inv asegs m ->
  evt asegs (calloc_B_sec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc UB n lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 n) s1' (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 INST) (Z_to_bv 64 1) s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x91f90) fc None m (seg_rom asegs)).
Proof.
  intros until j1. intros HUB Hn HSB0 HSB1 HSB ST HLO HIMG FRs FRp FRt TB HTB FRb FRq FRa SBC MI.
  unfold i_spacebeg, INST, g_instance in *.
  change (1971416 + 32)%Z with 1971448%Z in SBC.
  move SBC at bottom.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 2192, SP)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply u64arr_rw_ma in TB. rewrite HTB in TB.
  zhide.
  zstep. ifF.
  zstep.
  destruct HSB as [HSBlo|HSBhi].
  - (* [comment removed for export] *)
    zstep. ifT.
    do 7 zstep.
    do 10 zstep.
    release_frame FRa ST (SP + -2144)%Z. release_frame FRq ST (SP + -2136)%Z. release_frame FRb ST (SP + -2120)%Z.
    release_frame TB ST (SP + -80)%Z. release_frame FRt ST (SP + -72)%Z. release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
    zstep.
    finish.
    all: rewrite ?(unsigned_lit SP) by lia; try assumption.
  - (* [comment removed for export] *)
    zstep. ifF.
    zstep. zstep.
    zstep. ifT.
    do 7 zstep.
    do 10 zstep.
    release_frame FRa ST (SP + -2144)%Z. release_frame FRq ST (SP + -2136)%Z. release_frame FRb ST (SP + -2120)%Z.
    release_frame TB ST (SP + -80)%Z. release_frame FRt ST (SP + -72)%Z. release_frame FRp ST (SP + -64)%Z. release_frame FRs ST SP.
    zstep.
    finish.
    all: rewrite ?(unsigned_lit SP) by lia; try assumption.
Qed.

Open Scope Z_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Back0S.
Variables (Σ : rtsA) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem) (nm sz lo : Z)
          (tb : list word) (w : word) (jp jq j1 : list byte).
Hypothesis MST : mat_stable PMc.
Hypothesis Hn1 : 64512 < nm * sz <= CALLOC_SEC_MAX.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0xF000 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis MU1 : munch [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (bv_unsigned sp - 2336, bv_unsigned sp)] m m1.
Hypothesis WM1 : wmono asegs m m1.
Hypothesis IC1 : rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells asegs m1 (bv_unsigned sp + -72) [CB 8 jp].
Hypothesis IC3 : rw_cells asegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr asegs m1 (bv_unsigned sp + -2120) tb.
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells asegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 w].
Hypothesis ICq : rw_cells asegs m1 (bv_unsigned sp + -2144) [CB 8 jq].
Hypothesis IC5 : rw_cells asegs m1 (bv_unsigned sp + -2192)
                   [CB 8 j1; C8 (Z_to_bv 64 0xb8cd4); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0xb8d44)].
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation n := (nm * sz).

(* [comment removed for export] *)
Definition calloc_post0S : config -> Prop :=
  fun c => exists (Σ' : rtsA) (p : Z),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_st ra sp gp (Z_to_bv 64 0x717eb8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RTA Σ' usp lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) usp m m'
         /\ wr_at asegs m' p n /\ acc asegs m' p n) c
       /\ rt_live RTA Σ' = (p, n) :: rt_live RTA Σ /\ rt_frames RTA Σ' = rt_frames RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Theorem back_cps0S : cps asegs (core_post0 Σ PMc (usp + -2176) gp (Z_to_bv 64 n) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1)
                                          (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1)
                              calloc_post0S.
Proof using MST Hn1 HA LOW LOR SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 ICq IC5.
  intros TT c2 Hc2 Hk. destruct Hc2 as (Σ' & p & HAST & HL & HF & HS & HCR & Hp0 & Hp16 & HpU).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by (unfold RT_STACK in LOR; lia).
  assert (LO8 : 0x7fff7f800000 <= lo) by (pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN in *; lia).
  unfold CALLOC_SEC_MAX in Hn1.
  assert (W2 : forall ms, (exists m', ret_st (Z_to_bv 64 0x91f90) (Z_to_bv 64 (usp + -2176 + -16)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 n)
                                      (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136))
                                      (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
                            /\ ART_A Σ' m' /\ mem_inv asegs m' /\ wmono asegs m1 m' /\ stk asegs m' lo (usp + -2176 + -16)
                            /\ rt_pres (live Σ) (frames Σ) (usp + -2176 + -16) m1 m' /\ wr_at asegs m' p n /\ acc asegs m' p n) ->
             evt asegs (fun ms => exists m'', ret_st ra sp gp (Z_to_bv 64 0x717eb8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m'' ms
                  /\ rt_after RTA Σ' usp lo m m'' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) usp m m''
                  /\ wr_at asegs m'' p n /\ acc asegs m'' p n) ms).
  { intros ms (m' & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F' & fc' & ->) & ART' & MI' & WM' & ST' & PR' & WR' & AC').
    replace (usp + -2176 + -16) with (usp + -2192) in * by lia.
    rewrite (ret_pc_even 0x91f90) by (lia || reflexivity).
    assert (AG : forall a k, usp + -2192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m')
      by (intros a k H1 H2; exact (bk_agree0 Σ sp m1 tb HTB m' a k PR' H1 H2)).
    assert (TB' : u64arr asegs m' (usp + -2120) (ma_dec64 255 (u64s tb))).
    { pose proof (u64arr_rw_ma m1 _ _ TB1) as X. rewrite HTB in X.
      apply ma_rw_cells_u64arr. apply (rw_cells_agree asegs m1 m' _ _ X); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM']. }
    (* [comment removed for export] *)
    assert (HIN : In (p, n) (live Σ')) by (cbn [rt_live RTA] in HL; unfold rtA_live in HL; rewrite HL; left; reflexivity).
    pose proof (rta_live_range Σ' m' p n ART' HIN) as (LR1 & LR2 & LR3).
    pose proof (ART_consts Σ' m' ART') as ((SBC0 & _) & _ & _ & _ & (_ & _ & (S1 & S2) & _ & _) & _).
    assert (SBC : rw_cells asegs m' i_spacebeg [C8 (Z_to_bv 64 (l_SB (lay Σ')))]) by exact (rw_cells_app_l m' _ [C8 (Z_to_bv 64 (l_SB (lay Σ')))] _ SBC0).
    assert (SEC : 0 <= l_SB (lay Σ') /\ l_SB (lay Σ') + 2 ^ 37 < 2 ^ 64
                  /\ (p + n <= l_SB (lay Σ') \/ l_SB (lay Σ') + 2 ^ 37 <= p)
                  /\ (p + n <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi + 16 <= p)).
    { pose proof (geo_prb Σ' m' ART') as (P1 & P2 & _).
      pose proof (geo_grant Σ' m' ART' (l_PRB (lay Σ')) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (Q1 & _ & Q3 & Q4 & _).
      destruct (geo_live Σ' m' ART' p n HIN) as [(c & i & Hc & Hnth & Ep & G1 & G2 & G3 & G4 & G5)|(s & Hs & Hq & Hsn & Ep & Hroom & _)].
      - exfalso. pose proof (ClassSize_range c Hc) as (CR & _). unfold p_ubeg in Ep. rewrite (rz_size_big n) in Ep by lia. lia.
      - pose proof (ART_wf Σ' m' ART') as (_ & _ & _ & (_ & _ & _ & SF & _) & _).
        pose proof (proj1 (Forall_forall _ _) SF s Hs) as (X1 & X2 & X3 & _). rewrite Hsn in *. unfold s_ubeg in Ep.
        unfold apart, grant_ok in *. unfold rb, kUserCap, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
        change (2 ^ 37) with 137438953472 in *. change (2 ^ 64) with 18446744073709551616 in *.
        pose proof (rta_sp0_range Σ' m' ART') as (_ & R2). unfold l_ACEIL, rtA_sp0, USTACK_TOP, STACK_WIN in *. lia. }
    destruct SEC as (PR0 & PR1 & PR2 & PR3).
    eapply evt_mono.
    { apply (calloc_B_sec_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (usp + -2136)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1)
               (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 0x91f90) s0 s1 s2 s3 s4 s5 s6 (Z_to_bv 64 sz) (Z_to_bv 64 nm) (Z_to_bv 64 0xb8cd4) F' (frm_clear fc') m' p n (l_SB (lay Σ')) lo
               (ma_dec64 255 (u64s tb)) w jp jq j1).
      - unfold USTACK_TOP in HpU. lia.
      - lia.
      - exact PR0.
      - exact PR1.
      - exact PR2.
      - exact ST'.
      - unfold RT_STACK in LOR. lia.
      - lia.
      - apply (rw_cells_agree asegs m1 m' _ _ IC1); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC2); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC3); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact TB'.
      - apply ma_dec64_length.
      - apply (rw_cells_agree asegs m1 m' _ _ IC4); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ ICq); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - apply (rw_cells_agree asegs m1 m' _ _ IC5); [apply AG; cbn [cells_size csize Nat.add]; lia | exact WM'].
      - exact SBC.
      - exact MI'. }
    intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> & MU'' & WM'' & MI'' & ST'').
    exists m''. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc'; reflexivity|].
    assert (MUC : munch (W_client Σ' (usp + -2192)) m' m'').
    { eapply (munch_weaken _ _ m' m''); [|exact MU'']. intros x Hx. cbn [outside]. split; [|exact I].
      unfold W_client in Hx. cbn [app outside] in Hx. destruct Hx as (X1 & _). lia. }
    assert (Hsp' : rtA_sp0 Σ' - STACK_WIN <= usp + -2192) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
    split.
    { split; [exact (ART_transport _ Σ' m' m'' ART' MUC WM'' (art_avoid_client Σ' m' (usp + -2192) ART' Hsp'))|].
      split; [exact MI''|]. split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM' WM''))|]. exact ST''. }
    split.
    { intros a Ha. cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha.
      pose proof (fn_client Σ m usp HA Hsp0 (bv_unsigned a) Ha) as Ho. unfold W_fn in Ho. cbn [outside] in Ho.
      destruct Ho as (O1 & _ & _ & O4 & _).
      rewrite (MU'' a ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (PR' a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])).
      exact (MU1 a ltac:(cbn [outside]; split; [exact O1|]; split; [exact O4 | exact I])). }
    split; [exact (wr_at_transport asegs m' m'' p n WR' WM'')|].
    apply (acc_transport _ m' m'' _ _ AC' MU''); [lia|].
    assert (Hsh : shad (p + n - 1) + 1 <= 2 ^ 44 + SHB + 1) by (unfold shad; assert ((p + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold USTACK_TOP in HpU; lia); lia).
    cbn [disjoint_from]. unfold SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
    split; [left; unfold RT_STACK in LOR; lia | exact I]. }
  apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ') _ _ _ (fl_ASTA_mat_stable Σ' PMc MST) W2) HAST).
  intros c3 Hc3. apply Hk. exists Σ', p. split; [exact Hc3|].
  cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit.
  split; [exact HL|]. split; [exact HF|]. split; [exact HS|].
  split; [exact HCR|].
  split; [exact Hp0|]. split; [exact Hp16 | exact HpU].
Qed.
End Back0S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem rta_calloc_sec : core_stmt_sec0 -> calloc_contract_sec RTA.
Proof.
  intros CP Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nm sz lo
    FDO MST Hnm Hsz Hn Ha0 Ha1 Htp Hlen Hcr ART0 MI0 CALL UWOK. subst a0 a1 tp. unfold CALLOC_MAX, CALLOC_SEC_MAX in Hn.
  intros TT cf Hc Hk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0.
  unfold rtA_live in Hlen. unfold rtA_credit in Hcr.
  assert (Hn1 : 64512 < nm * sz <= CALLOC_SEC_MAX) by (unfold CALLOC_SEC_MAX; lia).
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _).
  assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
  destruct (unwindC_trace [(l_T (lay Σ) + 3168, l_T (lay Σ) + 3169); (bv_unsigned sp - 2336, bv_unsigned sp)] calloc_pc m ra s0 sp
              (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) UWOK ltac:(vm_compute; tauto) ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; cbn [disjoint_from]; clear - Ha HTl LOR; unfold RT_STACK in LOR; lia)) as (ch & tr & CHC & HTR & Htr & Htrl & _).
  assert (W1 : evt asegs (calloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (frm_clear fc) nm sz (l_T (lay Σ)) lo tr m)
                 (entry_st ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 nm) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6 F fc e_calloc m)).
  { unfold entry_st, e_calloc.
    exact (calloc_A_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F (frm_clear fc) m nm sz
             (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo tr ch
             Hnm Hsz ltac:(lia) ST ltac:(unfold RT_STACK in LOR; lia) HLOH ltac:(unfold USTACK_TOP in SPT; lia) ltac:(lia) ltac:(lia) HTR CHC
             G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl GT1 HT HTl HTT SC UB MI0). }
  assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 nm) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                                   s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_calloc m) ms ->
                  evt asegs (calloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (frm_clear fc) nm sz (l_T (lay Σ)) lo tr m) ms)
    by (intros ms <-; exact W1).
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. unfold calloc_A_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
  apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
  apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
  apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (j1 & Hc1).
  apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
  destruct Hc1 as (HM & HPm & HPM & HZ).
  destruct HPm as (Hms & MU1 & WM1 & MI1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & ICq & IC5 & AFr & J0 & UB1 & ST1).
  assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  pose proof (front_ART0 Σ m (bv_unsigned sp) ART0 Hsp0 m1 MU1 WM1 UB1) as ART1.
  set (usp := bv_unsigned sp) in *.
  assert (Hc2 : ASTA RTA Σ PMc (eq (core_entry0 Σ (usp + -2176) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc (nm * sz) m1)) c1).
  { split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold core_entry0.
    replace (usp + -2176 + -144) with (usp + -2320) by lia. replace (usp + -2176 + 40) with (usp + -2136) by lia. reflexivity. }
  assert (ST1' : stk asegs m1 lo (usp + -2176 + -144)) by (replace (usp + -2176 + -144) with (usp + -2320) by lia; exact ST1).
  assert (TRC : RT_caltail.trc_cells (usp + -2176) tr m1 tb).
  { unfold RT_caltail.trc_cells. replace (usp + -2176 + 40 + 16) with (usp + -2120) by lia. replace (usp + -2176 + 40) with (usp + -2136) by lia.
    split; [exact IC4|]. split; [exact TB1 | exact HTB]. }
  assert (AFC : RT_caltail.af_cells (usp + -2176) (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
  { split; replace (usp + -2176 + -144) with (usp + -2320) by lia; [exact AFr | exact J0]. }
  assert (LOR' : lo + 0x1000 <= usp + -2176 + -144) by (unfold RT_STACK in LOR; lia).
  assert (SPT' : usp + -2176 + 2144 <= USTACK_TOP) by lia.
  assert (SPA' : (usp + -2176) mod 16 = 0).
  { pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q - 136). lia. }
  assert (K : forall c2, core_post0 Σ PMc (usp + -2176) gp (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1)
                           (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 (nm * sz) lo m1 c2 -> realizes asegs c2 TT).
  { intros c2 Hc2'. exact (back_cps0S Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 nm sz lo (wr_trace tr tb) (Z_to_bv 64 (Z.of_nat (length tr))) jp jq j1
                             MST Hn1 ART0 LOW' ltac:(unfold RT_STACK in LOR; lia) SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 ltac:(rewrite wr_trace_length by lia; exact HTB) IC4 ICq IC5 TT c2 Hc2' Hk). }
  exact (CP Σ PMc m1 (usp + -2176) gp (Z_to_bv 64 (nm * sz)) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 INST) (Z_to_bv 64 1) (Z_to_bv 64 1)
           (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc (nm * sz) lo tr tb j0
           FDO MST ltac:(cbv beta; lia) ltac:(lia) Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.
