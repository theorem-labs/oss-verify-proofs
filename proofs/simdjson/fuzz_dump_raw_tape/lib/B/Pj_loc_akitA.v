(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma loc_cs : forall a,
  (0x6aa628 <= a < 0x6ab4d8 \/ 0x6cbe28 <= a < 0x6cbe30 \/ 0x6cc07b <= a < 0x6cc07c \/ 0x6cc158 <= a < 0x6cc15c) -> client_static a.
Proof.
  intros a Ha. split.
  - exists 0x6aa210, 0x6cd7d8. split; [unfold CLIENT_STATIC; cbn; auto| lia].
  - intros (lo & hi & Hin & Hr). unfold RT_STATIC in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]). exact Hin.
Qed.

Definition NCL (sp : Z) : list (Z * Z) :=
  [(0, 0x6aa628); (0x6ab4d8, 0x6cbe28); (0x6cbe30, 0x6cc07b); (0x6cc07c, 0x6cc158); (0x6cc15c, sp); (USTACK_TOP, 2^65)].

Lemma outside_app_iff : forall (W1 W2 : list (Z * Z)) a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Lemma outside_dec : forall (W : list (Z * Z)) a, outside W a \/ ~ outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a; cbn; [left; exact I|].
  destruct (IH a) as [H|H]; [| right; tauto].
  destruct (Z_lt_dec a lo) as [L|L]; [left; split; [lia| exact H]|].
  destruct (Z_lt_dec a hi) as [R|R]; [right; intros [X _]; lia| left; split; [lia| exact H]].
Qed.

Lemma not_outside_in : forall (W : list (Z * Z)) a, ~ outside W a -> exists lo hi, In (lo, hi) W /\ lo <= a < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z_lt_dec a lo) as [L|L]; [| destruct (Z_lt_dec a hi) as [R|R]; [exists lo, hi; split; [left; reflexivity| lia]|]].
  - destruct (IH a) as (l & h & Hin & X); [intros Ho; apply H; split; [lia| exact Ho]|]. exists l, h. split; [right; exact Hin| exact X].
  - destruct (IH a) as (l & h & Hin & X); [intros Ho; apply H; split; [lia| exact Ho]|]. exists l, h. split; [right; exact Hin| exact X].
Qed.

Lemma ncl_aclient : forall live frames sp a, 0 <= a < 2^64 -> outside (NCL sp) a -> aclient live frames sp a.
Proof.
  intros live frames sp a Ha Ho. unfold NCL in Ho. cbn [outside] in Ho. unfold USTACK_TOP in *.
  destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _).
  destruct (Z_lt_dec a 0x6cc15c) as [L|L].
  - right; left. apply loc_cs. lia.
  - left. unfold USTACK_TOP. lia.
Qed.

Lemma munch_of_pres : forall live frames sp W (m m' : mem), rt_pres_fp live frames sp W m m' -> munch (W ++ NCL sp) m m'.
Proof.
  intros live frames sp W m m' H a Ho. apply outside_app_iff in Ho as [H1 H2].
  pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. cbn in R.
  apply H; [apply ncl_aclient; [lia| exact H2]| exact H1].
Qed.

Lemma munch_of_pres_ex : forall live frames sp d n (m m' : mem), rt_pres_ex live frames sp d n m m' -> munch ((d, d + n) :: NCL sp) m m'.
Proof.
  intros live frames sp d n m m' H a (H1 & H2).
  pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. cbn in R.
  apply H; [apply ncl_aclient; [lia| exact H2]| exact H1].
Qed.

Lemma stk_hi_eq : forall (m : mem) lo a b, stk bsegs m lo a -> a = b -> stk bsegs m lo b.
Proof. intros m lo a b H <-. exact H. Qed.
Lemma mod16_off : forall s k, s mod 16 = 0 -> k mod 16 = 0 -> (s + k) mod 16 = 0.
Proof. intros s k Hs Hk. rewrite Z.add_mod, Hs, Hk by lia. reflexivity. Qed.

Section AKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma pres_fp_fold_munch : forall Σ (mX m0 m m' : mem) (q lo : Z) Wmu Wout,
  ART RT Σ mX -> rt_sp0 RT Σ - STACK_WIN <= lo ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q Wout m0 m -> munch Wmu m m' ->
  (forall a, q <= a \/ a < lo -> outside Wout a -> outside Wmu a) ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q Wout m0 m'.
Proof using AF.
  intros Σ mX m0 m m' q lo Wmu Wout HA Hlo ACC MU SUB a Ha Ho. rewrite <- (ACC a Ha Ho). apply MU.
  apply SUB; [| exact Ho]. destruct (aclient_split_c RT AF Σ mX q (bv_unsigned a) HA Ha); lia.
Qed.

Lemma pres_fp_after_call : forall Σ (mX m0 m m' : mem) (q lo sp_c : Z) Wc Wout,
  ART RT Σ mX -> rt_sp0 RT Σ - STACK_WIN <= lo -> sp_c <= q ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q Wout m0 m -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp_c Wc m m' ->
  (forall a, q <= a \/ a < lo -> outside Wout a -> outside Wc a) ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q Wout m0 m'.
Proof using AF.
  intros Σ mX m0 m m' q lo sp_c Wc Wout HA Hlo Hq ACC PR SUB a Ha Ho. rewrite <- (ACC a Ha Ho). apply PR.
  - eapply aclient_mono; [exact Ha| auto| auto| exact Hq].
  - apply SUB; [| exact Ho]. destruct (aclient_split_c RT AF Σ mX q (bv_unsigned a) HA Ha); lia.
Qed.

Lemma aclient_bounds : forall Σ (m : mem) q a, ART RT Σ m -> 0 <= q -> aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> 0 <= a < USTACK_TOP.
Proof using AF.
  intros Σ m q a HA Hq H. pose proof (af_sp0_range RT AF Σ m HA) as SPR. pose proof (af_sp0_win RT AF Σ m HA) as SPW.
  destruct H as [X|[X|[X|[X|X]]]].
  - ul.
  - pose proof (client_static_range _ X). ul.
  - destruct X as (p' & n' & Hin & Hp). pose proof (af_live_range RT AF Σ m p' n' HA Hin). ul.
  - destruct X as (f' & k' & Hin & Hf). pose proof (af_frames_range RT AF Σ m f' k' HA Hin) as (R0 & R & _). ul.
  - destruct X as (f' & k' & Hin & Hf). pose proof (af_frames_range RT AF Σ m f' k' HA Hin) as (R0 & R & _).
    assert (0 <= fs_size k')%Z by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    assert (shad (f' + fs_size k') <= 17592186044416 + SHB)%Z.
    { unfold shad. assert ((f' + fs_size k') / 8 <= 17592186044416)%Z by (apply Z.div_le_upper_bound; unfold SHB in *; ul). lia. }
    assert (SHB <= shad f')%Z by (unfold shad; assert (0 <= f' / 8)%Z by (apply Z.div_pos; lia); lia).
    unfold SHB in *. ul.
Qed.

Lemma pres_fp_W_weaken : forall Σ q W W' (m m' : mem),
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W m m' -> (forall a, outside W' a -> outside W a) -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W' m m'.
Proof. intros Σ q W W' m m' H SUB a Ha Ho. exact (H a Ha (SUB _ Ho)). Qed.

Lemma rw_cells_revive : forall Σ q W (m0 m : mem) A cs,
  rw_cells bsegs m0 A cs -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W m0 m -> wmono bsegs m0 m ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ outside W a) ->
  rw_cells bsegs m A cs.
Proof.
  intros Σ q W m0 m A cs H ACC WM SIDE. apply (rw_cells_agree bsegs m0 m A cs H); [| exact WM].
  intros a Ha. destruct (SIDE _ Ha) as [X Y]. exact (ACC a X Y).
Qed.

Lemma pres_fp_refl' : forall Σ q W (m : mem), rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W m m.
Proof. intros Σ q W m a _ _. reflexivity. Qed.

Lemma art_after_munch : forall Σ (sp' : Z) Wmu (m m' : mem),
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp' -> munch Wmu m m' -> wmono bsegs m m' ->
  (forall a lo hi, In (lo, hi) Wmu -> lo <= a < hi -> 0 <= a < 2^64 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' a) ->
  ART RT Σ m'.
Proof using AF.
  intros Σ sp' Wmu m m' HA Hsp MU WM H. apply (art_client_write RT AF Σ m m' sp' HA Hsp); [| exact WM].
  intros a Hna. apply MU. destruct (outside_dec Wmu (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. exfalso. apply Hna.
  destruct (not_outside_in Wmu (bv_unsigned a) Ho) as (lo & hi & Hin & Hr).
  pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. cbn in R.
  exact (H (bv_unsigned a) lo hi Hin Hr ltac:(lia)).
Qed.

Definition got_ssp (m : mem) : Prop := ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)].
Lemma gotl : forall Σ m, ART RT Σ m -> got_ssp m.
Proof using AF. intros Σ m H. exact (proj1 (af_got_lib RT AF Σ m H)). Qed.

Lemma cloc_acc : forall Σ m, ART RT Σ m -> acc bsegs m 0x33380 48.
Proof using AF.
  intros Σ m H. apply (acc_lit RT AF Σ m 0x33380 48 H). unfold ACC_LITS. cbn [In]. repeat (first [left; reflexivity | right]).
Qed.

Definition icpt_postA (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0v : word) (fc : bv 32) (lo : Z) (W : list (Z * Z))
    (REST : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ ART RT Σ m'
    /\ (stk bsegs m' lo (bv_unsigned sp) /\ REST m').

Lemma memsetA_spec : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (D C N : Z) (junk : list byte) (lo : Z),
  rw_cells bsegs m D [CB (Z.to_nat N) junk] -> 0 <= D -> D + N <= 2^47 -> 0 <= N < 2^40 -> 0 <= C < 256 ->
  (0 < N -> acc bsegs m D N /\ rng_class RT Σ D N) -> (forall i, 0 <= i < N -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (D + i)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall ms', icpt_postA Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz D) fc lo [(D, D + N)]
                 (fun m' => rw_cells bsegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))]) m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz C) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz e_memset) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros DST HD HDN HN HC CHK CL ART0 MI0 COK HK.
  eapply (mci_icall RT PMc).
  - apply (rc_memset RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz C) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m D N (Z_to_bv 8 C) lo FDO MST eq_refl); [| reflexivity| lia| lia| | exact ART0| exact MI0| exact COK].
    + f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
    + split; [exact CHK| split; [exact CL|]]. exact (rw_cells_wr_at bsegs m D _ N DST ltac:(cbn; lia)).
  - intros c HQ. unfold icpt_postF in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & (RA & RMI & RWM & RST) & PR & BY).
    apply (mci_retF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. apply HK. unfold icpt_postA.
    exists q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, F', m'. split; [reflexivity|].
    split; [intros a Ha (Ho & _); exact (PR a Ha Ho)|]. split; [exact RWM|]. split; [exact RMI|]. split; [exact RA|]. split; [exact RST|].
    replace (C mod 256) with C by (rewrite Z.mod_small; lia).
    assert (WR : wr_at bsegs m' D (Z.of_nat (length (repeat (Z_to_bv 8 C) (Z.to_nat N))))).
    { rewrite repeat_length, Z2Nat.id by lia. exact (wr_at_transport bsegs m m' D _ (rw_cells_wr_at bsegs m D _ N DST ltac:(cbn; lia)) RWM). }
    pose proof (rw_cells_CB_intro m' D _ BY WR) as X. rewrite repeat_length in X. exact X.
Qed.
End AKit.

Section MKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma memcmpA_spec : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  a0 = wz p -> a1 = wz q -> a2 = wz (Z.of_nat (length bp)) -> length bq = length bp ->
  0 < p -> p + Z.of_nat (length bp) <= 2^47 -> 0 < q -> q + Z.of_nat (length bp) <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^40 ->
  bytes_at bsegs m p bp -> bytes_at bsegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (forall r : word, (r = Z_to_bv 64 0 <-> bp = bq) ->
   forall ms', icpt_postA RT Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r fc lo [] (fun _ => True) m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz PJ_MEMCMP_STUB_A) fc None m (seg_rom bsegs)).
Proof using MCI FDO MST.
  intros until lo. intros E0 E1 E2 LEN P0 PH Q0 QH NZ LS BP BQ CP CQ ART0 MI0 COK HK.
  eapply (aevt_memcmpI RT PMc MCI FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p q bp bq lo);
    [exact E0| exact E1| exact E2| exact LEN| lia| lia| exact NZ| exact LS| exact BP| exact BQ| exact CP| exact CQ| exact ART0| exact MI0| exact COK|].
  intros r q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' HR (RA & RMI & RWM & RST) PR.
  apply (HK r HR). unfold icpt_postA.
  exists q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, F', m'. split; [reflexivity|].
  split; [intros a Ha _; apply (PR a Ha); lia|]. split; [exact RWM|]. split; [exact RMI|]. split; [exact RA|]. split; [exact RST| exact I].
Qed.
End MKit.

Ltac a_ul := unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia.
Ltac a_unz := rewrite ?unsigned_lit by (unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia).
Ltac a_outside_sub := cbn [outside app]; intros; lia.

Ltac a_in_client :=
  let a := fresh "a" in let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros a lo hi Hin; cbn [In app] in Hin;
  repeat (destruct Hin as [Hin|Hin];
          [injection Hin; clear Hin; intros; subst;
           first [ right; left; apply loc_cs; lia
                 | left; unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia
                 | match goal with H : forall i : Z, _ -> aclient _ _ _ _ |- aclient _ _ _ ?x =>
                     lazymatch type of H with forall i, _ -> aclient _ _ _ (?P + i)%Z =>
                       replace x with (P + (x - P))%Z by lia; eapply aclient_mono; [apply H; lia| auto| auto| lia] end end ]
          |]);
  destruct Hin.

Ltac a_chk :=
  intros _; split;
  [ lazymatch goal with ARTX : ART ?RT ?Σ ?m, AF : art_facts _ |- acc _ _ _ _ =>
      apply (af_acc_static RT AF Σ m _ _ ARTX); [lia | intros i Hi; split; [apply loc_cs; lia | lia]] end
  | right; right; right; unfold SEGTOP_A; lia ].
Ltac a_cl := intros i Hi; right; left; apply loc_cs; lia.

Ltac a_len_lits :=
  repeat match goal with |- context [Z.of_nat (@length byte ?X)] =>
    let n := eval vm_compute in (Z.of_nat (@length byte X)) in change (Z.of_nat (@length byte X)) with n end.
Ltac a_nl := a_len_lits; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]; unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia.
Ltac a_cks_prep := unfold checked_src; a_len_lits; try a_unz.
Ltac a_cks_stack :=
  a_cks_prep;
  split; [ intros _; split; [ lazymatch goal with ARTX : ART ?RT ?Σ ?m, AF : art_facts _ |- acc _ _ _ _ => apply (af_acc_stack RT AF Σ m _ _ ARTX); a_ul end
                            | right; right; left; a_ul ]
         | right; a_ul ].
Ltac a_cks_lit ACCQ :=
  a_cks_prep;
  split; [ intros _; split; [ lazymatch goal with ARTX : ART ?RT ?Σ ?m |- acc _ _ _ _ => apply (ACCQ Σ m ARTX) end
                            | right; right; right; unfold SEGTOP_A; lia ]
         | left; a_ul ].
Ltac a_mod16 :=
  try match goal with H : bv_unsigned ?s1 = (bv_unsigned ?s + ?k)%Z |- context [bv_unsigned ?s1 mod 16] => rewrite H end;
  first [ assumption | apply mod16_off; [assumption | reflexivity] ].
Ltac a_call_ok :=
  unfold call_ok; try a_unz;
  split; [ first [ assumption | lazymatch goal with ST : stk bsegs ?mm ?lo ?a |- stk bsegs _ _ ?b => exact (stk_hi_eq mm lo a b ST ltac:(lia)) end ]
         | split; [ assumption | split; [ a_ul | split; [ a_ul | a_mod16 ]]]].

Ltac astart q Wout :=
  lazymatch goal with
  | ART0 : ART ?RT ?Σ ?m, AF : art_facts _ |- _ =>
      pose proof (pres_fp_refl' RT Σ q Wout m) as ACC; pose proof ART0 as ARTX; pose proof (wmono_refl bsegs m) as WMS;
      pose proof (af_sp0_range RT AF Σ m ART0) as SP0R; pose proof (af_sp0_win RT AF Σ m ART0) as SP0W;
      unfold RT_STACK in *;
      lazymatch goal with LOR : (rt_sp0 RT Σ - STACK_WIN <= ?lo)%Z |- _ =>
        assert (LOLO : (0x6ce000 <= lo)%Z) by a_ul end
  end.

Ltac a_fold :=
  lazymatch goal with
  | ACC : rt_pres_fp _ _ ?q ?Wout ?m0 ?ms, MU : munch ?Wmu _ ?mc, ARTX : ART ?RT ?Σ _, AF : art_facts _ |- _ =>
    lazymatch goal with
    | WMS : wmono bsegs ms mc, LOR : (rt_sp0 RT Σ - STACK_WIN <= ?lo)%Z |- _ =>
      let flo := lazymatch Wmu with cons (pair ?f _) _ => f end in
      let ARTC := fresh "ARTC" in
      assert (ARTC : ART RT Σ mc) by (apply (art_after_munch RT AF Σ flo Wmu ms mc ARTX); [a_ul | exact MU | exact WMS | a_in_client]);
      let ACC2 := fresh "ACC" in
      pose proof (pres_fp_fold_munch RT AF Σ mc m0 ms mc q lo Wmu Wout ARTC LOR ACC MU ltac:(a_outside_sub)) as ACC2;
      pose (MUW := Wmu);
      clear ACC MU WMS ARTX; rename ACC2 into ACC; rename ARTC into ARTX
    end
  end.

Tactic Notation "acall" uconstr(SPEC) := a_fold; apply evt_done; eapply SPEC.
Tactic Notation "acall_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; a_fold; apply evt_done; eapply SPEC; unname_sp
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; a_fold; apply evt_done; eapply SPEC; unname_sp
  | _ => a_fold; apply evt_done; eapply SPEC
  end.

Ltac apost_call :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let PRc := fresh "PRc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in let ARTc := fresh "ARTN" in
  destruct PO as [E [PRc [WMc [MIc [ARTc PO]]]]]; subst ms';
  try (rewrite ?unsigned_lit in PRc by (unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia));
  try (rewrite ?unsigned_lit in PO by (unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia));
  lazymatch type of PRc with rt_pres_fp _ _ ?spc ?Wc ?m1 ?m2 =>
    let MUN := fresh "MUN" in
    pose proof (munch_of_pres _ _ spc Wc m1 m2 PRc) as MUN; unfold NCL in MUN; cbv [app] in MUN;
    transport_after_call bsegs m1 m2 MUN WMc;
    clear MUN WMc;
    try match goal with H : mem_inv bsegs m1 |- _ => clear H end;
    lazymatch goal with
    | ACC : rt_pres_fp _ _ ?q ?Wout ?m0 m1, ARTX0 : ART ?RT ?Σ m1, LOR : (rt_sp0 _ _ - STACK_WIN <= ?lo)%Z, AF : art_facts _ |- _ =>
        let ACC2 := fresh "ACC" in
        pose proof (pres_fp_after_call RT AF Σ m1 m0 m1 m2 q lo spc Wc Wout ARTX0 LOR ltac:(a_ul) ACC PRc ltac:(a_outside_sub)) as ACC2;
        clear ACC PRc ARTX0; rename ACC2 into ACC
    end;
    rename ARTc into ARTX;
    try clear m1
  end;
  lazymatch goal with AF : art_facts ?RT, ARTX : ART _ ?Σ ?m2 |- _ =>
    first [ match goal with H : ro_cells bsegs m2 0x16f508 _ |- _ => idtac end
          | pose proof (gotl RT AF Σ m2 ARTX : ro_cells bsegs m2 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)]) as GOT ] end;
  try destruct_ands PO;
  lazymatch goal with
  | MUW := ?W |- aevt _ _ _ _ (MS _ _ _ _ _ ?m2 _) => pose proof (munch_refl W m2) as MU; pose proof (wmono_refl bsegs m2) as WMS; clear MUW
  end;
  lazymatch goal with AF : art_facts ?RT, MST : mat_stable ?PMc |- aevt _ _ _ _ _ => apply (aevt_evt RT AF PMc MST) end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      lazymatch eval vm_compute in (andb (Z.leb 0 n) (Z.ltb n 18446744073709551616)) with
      | true => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
      | false => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end
  end).

Tactic Notation "acallc" uconstr(SPEC) "clearing" tactic3(clr) "by" tactic3(side) :=
  a_fold; apply evt_done; eapply SPEC; [ side .. | clr; apost_call ].

Ltac afinish_with tac :=
  a_fold;
  apply evt_done;
  lazymatch goal with HK : forall ms', _ -> aevt _ _ _ _ ms' |- _ => apply HK end;
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  tac;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [lazymatch goal with ACC : rt_pres_fp _ _ _ _ _ _ |- _ => exact ACC end|];
  split; [assumption|];
  split; [assumption|];
  split; [lazymatch goal with ARTX : ART _ _ _ |- _ => exact ARTX end|];
  repeat match goal with |- _ /\ _ => split end; try (first [assumption | eassumption]).
Ltac afinish := afinish_with ltac:(idtac).

Ltac a_widen W' :=
  lazymatch goal with ACC : rt_pres_fp _ _ ?q ?W ?m0 ?m, ARTX : ART ?RT ?Σ _ |- _ =>
    let ACC2 := fresh "ACC" in
    pose proof (pres_fp_W_weaken RT Σ q W W' m0 m ACC ltac:(a_outside_sub)) as ACC2; clear ACC; rename ACC2 into ACC end.

Definition a_kept (P : Prop) : Prop := P.
Ltac a_hide H := lazymatch type of H with ?T => change (a_kept T) in H end.
Ltac a_revive H :=
  unfold a_kept in H;
  lazymatch goal with ACC : rt_pres_fp _ _ ?q ?W ?m0 ?m, ARTX : ART ?RT ?Σ _ |- _ =>
    lazymatch goal with WM : wmono bsegs m0 m |- _ =>
    lazymatch type of H with rw_cells bsegs _ ?A ?cs =>
      let H2 := fresh "RV" in
      assert (H2 : rw_cells bsegs m A cs);
      [ apply (rw_cells_revive RT Σ q W m0 m A cs H ACC WM); intros a Ha; cbn [cells_size csize Nat.add] in Ha; split;
        [ first [ right; left; apply loc_cs; lia
                | left; unfold USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia
                | match goal with HA : forall i : Z, _ -> aclient _ _ _ _ |- aclient _ _ _ ?x =>
                    lazymatch type of HA with forall i, _ -> aclient _ _ _ (?P + i)%Z =>
                      replace x with (P + (x - P))%Z by lia; eapply aclient_mono; [apply HA; lia| auto| auto| lia] end end ]
        | cbn [outside app]; lia ]
      | clear H; rename H2 into H ] end end end.
