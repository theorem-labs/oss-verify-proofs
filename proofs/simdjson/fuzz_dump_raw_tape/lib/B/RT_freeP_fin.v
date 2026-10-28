(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_qput R_sec_defs R_mmapordie RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA2 RT_freeF RT_freeH RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_loop RT_drain_istmt RT_drain_itemp RT_dsec_defs RT_dsec_nw RT_dsec_art2 RT_freeP_defs RT_freeP_cli RT_freeP_run RT_freeP_ret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma icpt_frame_agree : forall (m m' : mem) usp ra s0 s1 s2 s3 s4 s5, icpt_frame m usp ra s0 s1 s2 s3 s4 s5 ->
  (forall a : word, usp - 2128 <= bv_unsigned a < usp -> m' a = m a) -> icpt_frame m' usp ra s0 s1 s2 s3 s4 s5.
Proof.
  intros m m' usp ra s0 s1 s2 s3 s4 s5 (FRs & (jp & FRp) & FRt & (wsb & TB & HTB) & (w & FRb)) AG.
  split; [exact (D_kit.rw_cells_agree_nw bsegs m m' _ _ FRs ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia))|].
  split; [exists jp; exact (D_kit.rw_cells_agree_nw bsegs m m' _ _ FRp ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia))|].
  split; [exact (D_kit.rw_cells_agree_nw bsegs m m' _ _ FRt ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia))|].
  split; [exists wsb; split; [|exact HTB];
          exact (D_kit.u64arr_agree_nw bsegs m m' _ _ TB ltac:(intros a Ha; apply AG; rewrite HTB in Ha; cbn in Ha; lia))|].
  exists w. exact (D_kit.rw_cells_agree_nw bsegs m m' _ _ FRb ltac:(intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia)).
Qed.

Section RetP.
Variables (Σk : rtsA) (k : nat) (s : secst) (lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (live0 : list (Z * Z)) (m : mem).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation C := (bv_unsigned sp - 2096).
Hypothesis HG : geo_ok Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis HW2 : rt_wf (recs Σk k).
Hypothesis HLO : l_ACEIL (lay Σk) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= usp.
Hypothesis Husp : usp + 16 <= USTACK_TOP.
Hypothesis Hdep : depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)).
Hypothesis HQB : Forall (fun b0 => exists j0, nth_error (r_st (pr Σk 24)) j0 = Some CkBatch /\ fst b0 = p_abeg (l_SB (lay Σk)) 24 j0) (ql Σk ++ qg Σk).
Hypothesis Hlive : liveP Σk s live0.
Hypothesis ICF : icpt_frame m usp ra s0 s1 s2 s3 s4 s5.
#[local] Notation L := (lay Σk).
#[local] Notation T := (l_T (lay Σk)).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).

Definition mun_effP : SyscallEffect := mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 (s_mb s), Z_to_bv 64 (smsz (s_n s)))] [] [].

Definition pp_post : machine_state -> Prop :=
  fun ms' => exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ ART_A (recs Σk k) m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rt_pres live0 (frames Σk) usp m m'.

Lemma pp_ret : forall ms0,
  svc_munP Σk k s usp lo gp s7 s8 s9 s10 s11 F fc live0 m (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x80bd4)
    (Z_to_bv 64 usp) (Z_to_bv 64 (MB + 6128 + 16)) (Z_to_bv 64 0x80b64) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
    (Z_to_bv 64 (usp + -81)) s6 ms0 ->
  evt bsegs pp_post (nretA ms0 mun_effP).
Proof using HG Hk HW2 HLO HLO2 Husp Hdep HQB Hlive ICF.
  intros ms0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & HA' & MI' & UF' & ST' & RP' & FR').
  pose proof (pp_nums Σk usp lo HG HLO HLO2 Husp) as (N4 & N5 & N6).
  pose proof HLO as HLk.
  pose proof (an_map Σk k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
  assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
  pose proof (dg_consts L m' (proj1 HA')) as (_ & MMG' & _).
  eapply evt_cut.
  { unfold mun_effP.
    apply (uod_B_spec (Z_to_bv 64 0x5daa4) (Z_to_bv 64 (C - 112)) gp (Z_to_bv 64 tpA) t0' t1' t2' a2' a3' a4' a5' a6'
             (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) (Z_to_bv 64 0x100000) s7 s8 s9
             s10 s11 t3' t4' t5' t6' F fc m' (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 0x80b64)
             MB MSZ lo); rewrite ?RSP.
    - exact M1. - exact M7. - clear - M2 HLk; lia.
    - unfold hide, img_hull_lo, img_hull_hi. clear - M4; unfold SEGTOP_A in *; lia.
    - exact UF'. - exact MMG'. - exact ST'.
    - clear - HLk G1 G8 G4. unfold kHighShadowEnd, K_HIGH_SHADOW_hi, SHB in *. lia.
    - clear - N5; lia. - clear - N6; lia. - exact MI'. }
  intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m'' & -> & MU & WB & MI'' & ST'' & _).
  rewrite RSP in MU, ST''.

  assert (CLI : forall z a, l_ACEIL L <= z -> C - 112 <= z -> aclient live0 (frames Σk) z a -> outside [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a).
  { intros z a Hz1 Hz2 Ha. destruct (ds_client_mapP Σk k s z a live0 HG Hlive Hk Hz1 Ha) as (X1 & X2).
    cbn [outside]. split; [exact X1|]. split; [|exact I]. clear - X2 HLk N5 Hz2. lia. }
  assert (STA : forall a n0, C - 112 <= a -> 0 <= n0 -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a n0).
  { intros a n0 H1 H2. cbn [disjoint_from]. clear - H1 H2 M2 HLk N5. split; [lia | split; [lia | exact I]]. }

  pose proof (ds_art_nw Σk k s lo (C - 112) HG Hk HLk ltac:(clear - N5; lia) ltac:(clear - N6; lia) Hdep HQB m' m'' HA' MU ST'') as ART''.
  assert (FR'' : qput_frame m'' (usp + -2208) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x80bd4)
                   (Z_to_bv 64 usp) (Z_to_bv 64 (MB + 6128 + 16)) (Z_to_bv 64 0x80b64) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
                   (Z_to_bv 64 (usp + -81)) s6).
  { unfold qput_frame in *. replace (usp + -2208) with (C - 112) by (clear; lia).
    apply (rwc_nw _ m' m'' _ _ FR' MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia. }
  assert (AG : forall a : word, usp - 2128 <= bv_unsigned a < usp -> m'' a = m a).
  { intros a Ha. rewrite (MU a); [apply RP'; left; clear - Ha Husp; unfold USTACK_TOP in *; lia|].
    apply (disjoint_outside _ (bv_unsigned a) 1); [apply STA; clear - Ha; lia | clear; lia]. }
  pose proof (icpt_frame_agree m m'' usp ra s0 s1 s2 s3 s4 s5 ICF AG) as ICF''.
  destruct (rt_wfx_of_wf _ HW2) as (HWX & HC).
  assert (HBY : RT_state.qbytes (ql (recs Σk k)) <= 0x100000)
    by (destruct HW2 as (_ & _ & _ & _ & (Q1 & _) & _); unfold QMAX_L in Q1; exact Q1).
  rewrite (ret_pc_even 0x5daa4) by (first [reflexivity | lia]).
  replace (Z_to_bv 64 (C - 112)) with (Z_to_bv 64 (usp + -2208)) by (f_equal; clear; lia).
  replace (C - 112) with (usp + -2208) in ST'' by (clear; lia).
  eapply evt_mono.
  { exact (ret_tailP (recs Σk k) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x5daa4) y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10
             (Z_to_bv 64 0x80b64) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) y11 y12 y13 y14
             (Z_to_bv 64 usp) (Z_to_bv 64 (MB + 6128 + 16)) (Z_to_bv 64 0x80b64) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
             (Z_to_bv 64 (usp + -81)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (usp + -2128)) F fc m'' lo
             (geo_of_wf _ HW2) ART'' HWX HC HBY MI'' ST'' HLk HLO2 Husp ICF'' FR''). }
  intros ms' (v & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m7 & -> & ART7 & MI7 & WM7 & ST7 & MU7).
  unfold pp_post. exists v, z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, m7. split; [reflexivity|].
  split; [exact ART7|]. split; [exact MI7|]. split; [exact ST7|].
  intros a Ha.
  assert (HO : outside [(l_ACEIL L, usp)] (bv_unsigned a)).
  { apply (aclient_split Σk live0 usp _ HG ltac:(clear - HLk HLO2; lia)); [|exact Ha].
    intros p0 n0 Hin. destruct (Hlive p0 n0 Hin) as [X|(t & Ht & _ & Htq & Htn & ->)]; [left; exact X|].
    right. destruct (In_nth_error _ _ Ht) as (kt & Hkt). exists kt, t. split; [exact Hkt | split; [exact Htq | split; [exact Htn | reflexivity]]]. }
  rewrite (MU7 a) by (cbn [outside] in HO |- *; clear - HO HLk HLO2; split; [lia | exact I]).
  rewrite (MU a) by (apply (CLI usp); [clear - HLk HLO2; lia | clear; lia | exact Ha]).
  apply RP'. destruct Ha as [Ha|Ha]; [left; clear - Ha; lia | right; exact Ha].
Qed.

End RetP.

End GWIN.
