(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread R_m2s RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts RT_release R_fs_ok RT_stackmalloc R_fs6 R_fs6free.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sf_mid (m m' : mem) (fl : Z) : mem := fun a => if bv_eqb a (wa fl) then m a else m' a.

Lemma sf_mid_at : forall (m m' : mem) fl, sf_mid m m' fl (wa fl) = m (wa fl).
Proof. intros m m' fl. unfold sf_mid. rewrite (proj2 (bv_eqb_eq (wa fl) (wa fl)) eq_refl). reflexivity. Qed.

Lemma sf_mid_off : forall (m m' : mem) fl (a : word), 0 <= fl < 2 ^ 64 -> bv_unsigned a <> fl -> sf_mid m m' fl a = m' a.
Proof.
  intros m m' fl a Hfl Hne. unfold sf_mid. destruct (bv_eqb a (wa fl)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst a. rewrite wa_unsigned in Hne by lia. contradiction.
Qed.

Lemma wview_ext : forall (m1 m2 : mem) (a : word), m1 a = m2 a -> wview bsegs m1 a = wview bsegs m2 a.
Proof. intros m1 m2 a E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SF.
Variables (Σ : rtsA) (m m' : mem) (f : Z) (fr : list (Z * nat)) (p usp lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HF : frames Σ = (f, 6%nat) :: fr.
Hypothesis Hp : 0 <= p < 256.
Hypothesis Hf : f = frame_addr (l_FSB (lay Σ)) 6 p.
Hypothesis Hb : nth (Z.to_nat p) (fss_flags (fs_of Σ 6)) 0 = 1.
Hypothesis Hlo : l_ACEIL (lay Σ) <= lo.
Hypothesis Husp : lo + 16 <= usp.
Hypothesis Husp2 : usp <= USTACK_TOP.
Hypothesis MU : munch (sf_W (l_FSB (lay Σ)) p usp) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis P_flags : fs_flags (l_FSB (lay Σ)) 6 m' (upd (fss_flags (fs_of Σ 6)) (Z.to_nat p) 0).
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation fl := (fl_base (l_FSB (lay Σ)) 6 + p).
#[local] Notation m1 := (sf_mid m m' (fl_base (l_FSB (lay Σ)) 6 + p)).
#[local] Notation Σ' := (fs_release Σ 6 p fr).

(* [comment removed for export] *)
Lemma sf_geo : 0 < FSB /\ FSB mod 4096 = 0 /\ FSB + 0xb09000 <= l_ACEIL L
  /\ (FSB + 0xb09000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= FSB)
  /\ FSB + 0x1000 <= fl /\ fl + 1 <= FSB + 0x9000
  /\ FSB + 0x9000 <= f /\ f + 4096 <= FSB + 0xb09000 /\ f mod 4096 = 0
  /\ shad (f + 4096) = shad f + 512.
Proof using HA Hp Hf.
  clear - HA Hp Hf.
  pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & _).
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  unfold fl_base, flags_off. change (2 ^ (15 - 6)) with 512.
  split; [lia|]. split; [lia|].
  rewrite Hf. unfold frame_addr, fsz. change (2 ^ 20) with 1048576. change (64 * 2 ^ 6) with 4096.
  split; [lia|]. split; [lia|].
  assert (M : (FSB + 36864 + 6 * 1048576 + p * 4096) mod 4096 = 0).
  { apply Z.mod_divide in G2; [|lia]. destruct G2 as [q Hq]. apply Z.mod_divide; [lia|]. exists (q + 9 + 1536 + p). lia. }
  split; [exact M|].
  unfold shad. apply Z.mod_divide in M; [|lia]. destruct M as [q Hq]. rewrite Hq.
  replace (q * 4096 + 4096) with ((q * 512 + 512) * 8) by lia. replace (q * 4096) with ((q * 512) * 8) by lia.
  rewrite !Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sf_art1 : ART_A Σ m1.
Proof using HA HF Hp Hf Hlo Husp Husp2 MU WM.
  pose proof sf_geo as (G1 & G2 & G3 & G4 & F1 & F2 & A1 & A2 & A3 & A4).
  pose proof (rta_sp0_range Σ m HA) as Hr.
  assert (Hfl : 0 <= fl < 2 ^ 64) by (unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  apply (ART_client_frame Σ m m1 (usp - 16) HA); [unfold l_ACEIL, rtA_sp0 in *; lia | |].
  - intros a Hnc. destruct (Z.eq_dec (bv_unsigned a) fl) as [E|NE].
    + assert (Ea : a = wa fl) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ea. apply sf_mid_at.
    + rewrite (sf_mid_off m m' fl a Hfl NE). apply MU. unfold sf_W. cbn [outside].
      split; [lia|]. split; [|split; [|exact I]].
      * intros Hx. apply Hnc. right; right; right; right. exists f, 6%nat. split; [rewrite HF; left; reflexivity|].
        change (fs_size 6) with 4096. rewrite A4. rewrite <- Hf in Hx. exact Hx.
      * intros Hx. apply Hnc. left. lia.
  - intros a Ha. destruct (Z.eq_dec (bv_unsigned a) fl) as [E|NE].
    + assert (Ea : a = wa fl) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
      rewrite (wview_ext m1 m a) by (rewrite Ea; apply sf_mid_at). exact Ha.
    + rewrite (wview_ext m1 m' a) by (apply sf_mid_off; assumption). exact (WM a Ha).
Qed.

(* [comment removed for export] *)
Lemma sf_mu2 : munch [(fl, fl + 1)] m1 m'.
Proof using HA Hp Hf.
  pose proof sf_geo as (G1 & G2 & G3 & G4 & F1 & F2 & _).
  pose proof (rta_sp0_range Σ m HA) as Hr.
  assert (Hfl : 0 <= fl < 2 ^ 64) by (unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  intros a Ha. cbn [outside] in Ha. symmetry. apply sf_mid_off; [exact Hfl | lia].
Qed.

Lemma sf_wm2 : wmono bsegs m1 m'.
Proof using HA Hp Hf WM.
  pose proof sf_geo as (G1 & G2 & G3 & G4 & F1 & F2 & _).
  pose proof (rta_sp0_range Σ m HA) as Hr.
  assert (Hfl : 0 <= fl < 2 ^ 64) by (unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia).
  intros a Ha. destruct (Z.eq_dec (bv_unsigned a) fl) as [E|NE].
  - assert (Ea : a = wa fl) by (rewrite <- E; unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
    rewrite (wview_ext m1 m a) in Ha by (rewrite Ea; apply sf_mid_at). exact (WM a Ha).
  - rewrite (wview_ext m1 m' a) in Ha by (apply sf_mid_off; assumption). exact Ha.
Qed.

Lemma sf_flag0 : rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)].
Proof using HA Hp P_flags.
  clear - HA Hp P_flags.
  pose proof (rel_flags_ok Σ m HA 6%nat ltac:(right; right; reflexivity)) as (Hlen & _). change (Z.of_nat 6) with 6 in Hlen. change (NF 6) with 256 in Hlen.
  assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ 6)))%nat) by (apply Nat2Z.inj_lt; rewrite Hlen, Z2Nat.id by lia; lia).
  unfold fs_flags in P_flags. rewrite map_upd in P_flags.
  assert (Hn : nth_error (upd (map b8 (fss_flags (fs_of Σ 6))) (Z.to_nat p) (b8 0)) (Z.to_nat p) = Some (Z_to_bv 8 0)).
  { rewrite nth_error_upd_same by (rewrite length_map; exact Hpl). reflexivity. }
  pose proof (u8arr_byte m' _ _ _ _ P_flags Hn) as X. rewrite Z2Nat.id in X by lia. exact X.
Qed.

Theorem sf_art : ART_A Σ' m'.
Proof using HA HF Hp Hf Hb Hlo Husp Husp2 MU WM P_flags.
  pose proof (rta_frame_release_at Σ m1 f 6%nat fr sf_art1 HF p ltac:(right; right; reflexivity) ltac:(change (NF (Z.of_nat 6)) with 256; exact Hp)
                ltac:(change (Z.of_nat 6) with 6; exact Hf) Hb) as (_ & _ & _ & _ & _ & R).
  change (Z.of_nat 6) with 6 in R.
  exact (proj1 (R m' sf_mu2 sf_wm2 sf_flag0)).
Qed.

(* [comment removed for export] *)
Lemma sf_pres : rt_pres (live Σ) fr usp m m'.
Proof using HA HF Hp Hf Hb Hlo Husp Husp2 MU.
  pose proof sf_geo as (G1 & G2 & G3 & G4 & F1 & F2 & A1 & A2 & A3 & A4).
  pose proof (rta_sp0_range Σ m HA) as Hr. pose proof (rta_sp0_win Σ m HA) as Hw.
  destruct (rta_frame_release_at Σ m f 6%nat fr HA HF p ltac:(right; right; reflexivity) ltac:(change (NF (Z.of_nat 6)) with 256; exact Hp)
              ltac:(change (Z.of_nat 6) with 6; exact Hf) Hb) as (_ & NC & _).
  change (Z.of_nat 6) with 6 in NC.
  assert (INC : forall x, aclient (live Σ) fr usp x -> x < usp -> aclient (live Σ) (frames Σ) USTACK_TOP x).
  { intros x [H|[H|[H|[H|H]]]] Hx; [lia | right; left; exact H | right; right; left; exact H | |].
    - right; right; right; left. destruct H as (f2 & k2 & Hin & H2). exists f2, k2. split; [rewrite HF; right; exact Hin | exact H2].
    - right; right; right; right. destruct H as (f2 & k2 & Hin & H2). exists f2, k2. split; [rewrite HF; right; exact Hin | exact H2]. }
  intros a Ha. apply MU. unfold sf_W. cbn [outside].
  assert (Hsh : shad f + 512 <= 0x10007fff8000).
  { rewrite <- A4. unfold shad, SHB. assert ((f + 4096) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
  split; [|split; [|split; [|exact I]]].
  - intros Hx. apply NC. replace fl with (bv_unsigned a) by lia. apply INC; [exact Ha|]. unfold l_ACEIL in *. lia.
  - (* [comment removed for export] *)
    rewrite <- Hf. intros Hx. destruct Ha as [H|[H|[H|[H|H]]]].
    + unfold l_ACEIL, rtA_sp0, STACK_WIN in *. lia.
    + destruct H as ((lo0 & hi0 & Hin & Hr0) & _). unfold CLIENT_STATIC in Hin.
      assert (SHB <= shad f) by (unfold shad; pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); lia). unfold SHB in *.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    + destruct H as (q & n & Hin & Hq).
      destruct (rta_fshadow_apart Σ m HA f 6%nat ltac:(rewrite HF; left; reflexivity)) as (AP & _).
      specialize (AP q n Hin). change (fs_size 6) with 4096 in AP. rewrite A4 in AP. lia.
    + destruct H as (f2 & k2 & Hin & H2).
      destruct (rta_fshadow_apart Σ m HA f 6%nat ltac:(rewrite HF; left; reflexivity)) as (_ & AP).
      specialize (AP f2 k2 ltac:(rewrite HF; right; exact Hin)). change (fs_size 6) with 4096 in AP. rewrite A4 in AP. lia.
    + destruct H as (f2 & k2 & Hin & H2).
      pose proof (rta_frames_disj Σ m HA f 6%nat f2 k2 [] fr ltac:(rewrite HF; reflexivity) ltac:(exact Hin)) as D.
      change (fs_size 6) with 4096 in D.
      destruct (rta_frames_align Σ m HA f2 k2 ltac:(rewrite HF; right; exact Hin)) as (M2 & _).
      destruct (rta_frames_range Σ m HA f2 k2 ltac:(rewrite HF; right; exact Hin)) as (P2 & _).
      assert (Hs2 : 0 < fs_size k2 /\ fs_size k2 mod 8 = 0).
      { destruct (rta_frame_in Σ m f2 k2 HA ltac:(rewrite HF; right; exact Hin)) as ([-> | [-> | ->]] & _); split; reflexivity. }
      unfold shad in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - (* [comment removed for export] *)
    intros Hx. destruct Ha as [H|[H|[H|[H|H]]]].
    + lia.
    + destruct H as ((lo0 & hi0 & Hin & Hr0) & _). unfold CLIENT_STATIC in Hin. unfold l_ACEIL, rtA_sp0, STACK_WIN, SEGTOP_A in *.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    + destruct H as (q & n & Hin & Hq). pose proof (rta_live_range Σ m q n HA Hin) as (_ & L2 & _). unfold l_ACEIL, rtA_sp0 in *. lia.
    + destruct H as (f2 & k2 & Hin & H2).
      destruct (rta_frames_range Σ m HA f2 k2 ltac:(rewrite HF; right; exact Hin)) as (_ & R2 & _). unfold l_ACEIL, rtA_sp0 in *. lia.
    + destruct H as (f2 & k2 & Hin & H2).
      destruct (rta_frames_range Σ m HA f2 k2 ltac:(rewrite HF; right; exact Hin)) as (P2 & R2 & _).
      assert (shad (f2 + fs_size k2) <= 0x10007fff8000).
      { unfold shad, SHB. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
      unfold l_ACEIL, rtA_sp0, STACK_WIN in *. lia.
Qed.

End SF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sf_pre : forall Σ m f fr p, ART_A Σ m -> frames Σ = (f, 6%nat) :: fr -> 0 <= p < 256 -> f = frame_addr (l_FSB (lay Σ)) 6 p ->
  fs_flags (l_FSB (lay Σ)) 6 m (fss_flags (fs_of Σ 6)) /\ flags_ok 6 (fss_flags (fs_of Σ 6))
  /\ rw_cells bsegs m (frame_addr (l_FSB (lay Σ)) 6 p + 4088) [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) 6 + p))]
  /\ exists junkS, rw_cells bsegs m (shad (frame_addr (l_FSB (lay Σ)) 6 p)) [CB 512 junkS].
Proof.
  intros Σ m f fr p HA HF Hp Hf.
  pose proof (fs_rep_cls Σ m 6%nat (ART_fs Σ m HA) ltac:(right; right; reflexivity)) as (_ & CF & _). change (Z.of_nat 6) with 6 in CF.
  pose proof (rel_flags_ok Σ m HA 6%nat ltac:(right; right; reflexivity)) as OK. change (Z.of_nat 6) with 6 in OK.
  split; [exact CF|]. split; [exact OK|].
  destruct (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB. apply Forall_cons_iff in FB as [FB0 _].
  destruct FB0 as (p' & Hf' & _ & Ws & Cw). cbn [fst snd] in *. change (Z.of_nat 6) with 6 in *. change (fs_size 6) with 4096 in *.
  rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ ltac:(right; right; reflexivity)) in Hf'. subst p'. rewrite Hf in Cw, Ws.
  split; [replace (frame_addr (l_FSB (lay Σ)) 6 p + 4088) with (frame_addr (l_FSB (lay Σ)) 6 p + 4096 - 8) by lia; exact Cw|].
  change (4096 / 8) with 512 in Ws.
  pose proof (wr_at_stk m _ _ Ws ltac:(lia)) as St.
  destruct (stk_bytes bsegs m _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs.
  split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hbs]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact Ws.
Qed.

Theorem rta_stack_free_6 : stack_free_contract RTA 6.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo
    FDO MST _ -> HF ART0 MI0 CALL.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (rel_slot Σ m f 6%nat fr ART0 HF) as (_ & p & Hp & Hf & Hb).
  change (Z.of_nat 6) with 6 in Hp, Hf. change (NF 6) with 256 in Hp.
  destruct (sf_pre Σ m f fr p ART0 HF Hp Hf) as (FL & OK & LW & (junkS & SHC)).
  destruct (sm_pre Σ m 6%nat lo ART0 ltac:(right; right; reflexivity) ltac:(lia) LOW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2S & FSOK & HLO & FSL & _).
  assert (W1 : evt bsegs (sf6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p (fss_flags (fs_of Σ 6)) lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_free 6) m)).
  { unfold entry_st.
    exact (stack_free_6_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (l_FSB (lay Σ)) p (fss_flags (fs_of Σ 6)) lo junkS ltac:(rewrite Hf; reflexivity) Hp FL OK LW SHC M2S FSOK HLO FSL ST
             ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sf6_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
  apply AST_exI in Hc1 as (a0' & Hc1).
  exists (fs_release Σ 6 p fr), a0'.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity | reflexivity]]]].
  unfold ASTA. change (rt_allow RTA (fs_release Σ 6 p fr)) with (rtA_allow Σ).
  eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
  intros ms (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PF & _).
  assert (Hlo : l_ACEIL (lay Σ) <= lo) by (cbn [rt_sp0 RTA] in LOW; unfold rtA_sp0 in LOW; unfold l_ACEIL; lia).
  assert (Husp : lo + 16 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
  assert (Husp2 : bv_unsigned sp <= USTACK_TOP) by lia.
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split.
  - split; [exact (sf_art Σ m m' f fr p (bv_unsigned sp) lo ART0 HF Hp Hf Hb Hlo Husp Husp2 MU WM PF)|].
    split; [exact MI|]. split; [exact WM | exact ST'].
  - exact (sf_pres Σ m m' f fr p (bv_unsigned sp) lo ART0 HF Hp Hf Hb Hlo Husp Husp2 MU).
Qed.
