(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.


Lemma ASTA_switch (RT : rt_sig) (Σ Σ' : rts RT) PMc Pm c : ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
  (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
  intros H HA HM. unfold ASTA in *. rewrite HA.
  eapply AST_conseq; [exact H | auto |]. intros mo [H1 H2]. split; [apply HM; exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pow2_geN (fs : Z) (d : nat) : fsz fs -> fs <= 8 * 2 ^ Z.of_nat d -> fs + 8 <= 8 * 2 ^ Z.of_nat d /\ (fs / 8) mod 2 ^ Z.of_nat d = fs / 8 /\ fs / 8 < 2 ^ Z.of_nat d.
Proof.
  intros Hf H. pose proof (fsz_facts fs Hf) as (F1 & F2 & F3 & F4).
  assert (G : 64 <= 2 ^ Z.of_nat d \/ 2 ^ Z.of_nat d = 1 \/ 2 ^ Z.of_nat d = 2 \/ 2 ^ Z.of_nat d = 4 \/ 2 ^ Z.of_nat d = 8 \/ 2 ^ Z.of_nat d = 16 \/ 2 ^ Z.of_nat d = 32).
  { destruct d as [|[|[|[|[|[|d]]]]]]; [right; cbn; lia .. | left].
    replace (Z.of_nat (S (S (S (S (S (S d))))))) with (6 + Z.of_nat d) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64.
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat d) ltac:(lia) ltac:(lia)). nia. }
  assert (Hq : fs + 8 <= 8 * 2 ^ Z.of_nat d) by (destruct Hf as [-> |[-> | ->]]; lia).
  split; [exact Hq|]. split; [apply Z.mod_small; Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma region_ok_frameN (rho : valuation) (t fl : int) (rg : region) (m : word -> option byte) (flA : Z) :
  region_ok ctasegs rho t rg m -> rg_abs rg = None -> fsz (to_Z (rg_size rg)) ->
  rho fl = flA -> 0 <= flA < 2 ^ 64 -> rho t + to_Z (rg_size rg) + 8 < two63 ->
  bytes_at ctasegs m (rho t + to_Z (rg_size rg)) (le8 (Z_to_bv 64 flA)) ->
  region_ok ctasegs rho t (RG None (rg_size rg + 8)%uint63 (rg_al rg) false (rg_dflt rg) (rg_d rg) (iset (rg_d rg) (rg_cells rg) (rg_size rg >> 3)%uint63 (CP fl w_zero))) m.
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & Hby) Eabs Hfs Efl HflA Htop Hb.
  set (fs := to_Z (rg_size rg)) in *. pose proof (fsz_facts fs Hfs) as (F1 & F2 & F3 & F4).
  unfold rbase in *. rewrite Eabs in *. destruct (pow2_geN fs (rg_d rg) Hfs H3) as (HdN & Hdm & Hdl).
  assert (Esz8 : to_Z (rg_size rg + 8)%uint63 = fs + 8).
  { rewrite add_spec. change (to_Z 8%uint63) with 8. fold fs. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  assert (Ek7 : to_Z (rg_size rg >> 3)%uint63 = fs / 8) by (rewrite phi_shr3; reflexivity).
  unfold region_ok, rbase. cbn [rg_abs rg_size rg_al rg_wr rg_d]. rewrite Esz8.
  split; [exact H0|]. split; [lia|]. split; [lia|]. split; [exact HdN|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  intros i Hi. destruct (Z_lt_le_dec i fs) as [L|L].
  - destruct (Hby i ltac:(lia)) as (b & Eb & Kb & _). exists b. split; [exact Eb|]. split; [|discriminate].
    unfold rg_kb, rd_cell in *. cbn [rg_d rg_cells rg_dflt]. rewrite iget_iset.
    assert (Ek : to_Z (of_Z (i / 8)) = i / 8) by (apply of_Z_small; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hk7 : i / 8 < fs / 8) by (Z.div_mod_to_equations; lia). assert (Hk0 : 0 <= i / 8) by (apply Z.div_pos; lia).
    rewrite Ek7, Hdm, Ek.
    assert (Hm : (i / 8) mod 2 ^ Z.of_nat (rg_d rg) = i / 8) by (apply Z.mod_small; lia). rewrite Hm.
    destruct (Z.eqb_spec (fs / 8) (i / 8)) as [E|E]; [lia | exact Kb].
  - pose proof (bytes_at_mrd m (rho t + fs) _ (i - fs) Hb ltac:(rewrite length_le8; lia)) as Eb.
    replace (rho t + fs + (i - fs)) with (rho t + i) in Eb by lia.
    unfold le8, word_to_le_bytes in Eb. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 flA)) as Hw.
    rewrite (nth_Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 flA)) (Z.to_nat (i - fs)) ltac:(lia) ltac:(lia)) in Eb.
    rewrite Z2Nat.id in Eb by lia.
    exists (byte_of (bv_unsigned (Z_to_bv 64 flA)) (i - fs)). split; [exact Eb|]. split; [|discriminate].
    unfold rg_kb, rd_cell. cbn [rg_d rg_cells rg_dflt]. rewrite iget_iset.
    assert (Ek8 : i / 8 = fs / 8) by (Z.div_mod_to_equations; lia).
    assert (Ek : to_Z (of_Z (i / 8)) = fs / 8) by (rewrite Ek8; apply of_Z_small; lia).
    rewrite Ek7, Hdm, Ek, Hdm, Z.eqb_refl. cbn [cell_kb kb_ok].
    assert (Em : i mod 8 = i - fs) by (Z.div_mod_to_equations; lia). rewrite Em.
    rewrite byte_of_unsigned. unfold pword. rewrite Efl. change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_ok_flag (rho : valuation) (fl : int) (m : word -> option byte) (flA : Z) :
  rho fl = flA -> 0 < flA -> flA + 1 < two63 -> rw_cells ctasegs m flA [C1 (Z_to_bv 8 1)] ->
  region_ok ctasegs rho fl (RG None 1 0 true DUnk 0 (iset 0 IEmpty 0 (CW w_one 1))) m.
Proof.
  intros Efl H0 Htop [[_ Hb] (_ & _ & Hw)]. unfold region_ok, rbase. cbn [rg_abs rg_size rg_al rg_wr rg_d]. rewrite Efl.
  change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0.
  split; [split; [lia | left; exact H0]|]. split; [exact Htop|]. split; [lia|]. split; [cbn; lia|]. split; [cbn; lia|]. split; [lia|]. split; [apply Z.mod_1_r|].
  intros i Hi. assert (i = 0) by lia. subst i. exists (Z_to_bv 8 1). split.
  - pose proof (bytes_at_mrd m flA _ 0 Hb ltac:(cbn; lia)) as E. exact E.
  - split; [|intros _; apply (Hw 0); cbn; lia].
    unfold rg_kb, rd_cell. cbn [rg_d rg_cells rg_dflt]. change (of_Z (0 / 8)) with 0%uint63. rewrite iget_iset_same. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma flag_zero_cells (rho : valuation) (fl : int) (rgf : region) (m : word -> option byte) (flA : Z) :
  region_ok ctasegs rho fl rgf m -> rg_abs rgf = None -> to_Z (rg_size rgf) = 1 -> rg_wr rgf = true -> rho fl = flA ->
  flag_known_zero ctasegs rgf = true -> rw_cells ctasegs m flA [C1 (Z_to_bv 8 0)].
Proof.
  intros (H0 & H1 & _ & _ & _ & _ & _ & Hby) Eabs Esz Ewr Efl Hz. unfold rbase in *. rewrite Eabs, Efl in *. rewrite Esz in *. unfold two63 in H1.
  destruct (Hby 0 ltac:(lia)) as (b & Eb & Kb & Wb). rewrite Z.add_0_r in Eb, Wb.
  unfold flag_known_zero in Hz. unfold rg_kb in Kb. change (of_Z (0 / 8)) with 0%uint63 in Kb. change (0 mod 8) with 0 in Kb.
  destruct (rd_cell ctasegs rgf 0) as [w km| |]; [|discriminate|discriminate]. apply andb_prop in Hz as [Hz1 Hz2].
  apply Uint63.eqb_spec in Hz1, Hz2. cbn [cell_kb] in Kb.
  assert (Hbit : Z.testbit (to_Z km) 0 = true).
  { pose proof (f_equal to_Z Hz1) as E. rewrite land_spec' in E. change (to_Z 1%uint63) with 1 in E.
    pose proof (f_equal (fun z => Z.testbit z 0) E) as X. cbv beta in X. rewrite Z.land_spec in X.
    change (Z.testbit 1 0) with true in X. rewrite andb_true_r in X. exact X. }
  rewrite Hbit in Kb. cbn [kb_ok] in Kb.
  assert (Hb0 : byteZ (wZ w) 0 = 0).
  { pose proof (f_equal to_Z Hz2) as E. rewrite land_spec' in E. change (to_Z 255%uint63) with (Z.ones 8) in E. rewrite Z.land_ones in E by lia.
    change (to_Z 0%uint63) with 0 in E. unfold byteZ. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. rewrite wZ_split.
    change (2 ^ 8) with 256 in E. replace (Z.b2z (wh w) * two63 + to_Z (wl w)) with (to_Z (wl w) + (Z.b2z (wh w) * 36028797018963968) * 256) by (unfold two63; lia).
    rewrite Z.mod_add by lia. exact E. }
  rewrite Hb0 in Kb. assert (Ebz : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Kb; reflexivity). subst b.
  split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r. exact (Wb Ewr).
Qed.

Notation dead_rg := (RG (Some 0%uint63) 0 0 false DUnk 0 IEmpty).

(* [comment removed for export] *)
Lemma mget_kill_region (M : HxMem.mem) (t x : int) (rg : region) : to_Z t < to_Z TAGLIM ->
  mget (kill_region M t rg) x = if (to_Z t =? to_Z x) then Some dead_rg else mget M x.
Proof. intros Ht. rewrite kill_region_eq. exact (mget_mset M t x _ Ht). Qed.

Lemma mget_kill_cases (M : HxMem.mem) (t x : int) (rg rgx : region) : to_Z t < to_Z TAGLIM ->
  mget (kill_region M t rg) x = Some rgx -> (x = t /\ rgx = dead_rg) \/ (x <> t /\ mget M x = Some rgx).
Proof. intros Ht G. rewrite kill_region_eq in G. exact (mget_mset_cases M t x _ rgx Ht G). Qed.

Lemma mget_empty (t : int) : mget IEmpty t = None.
Proof. unfold mget. destruct (_ <? _)%uint63; [apply iget_empty | reflexivity]. Qed.

Section HkRelease.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis PMc_fdfs : fdfs_only PMc.
Hypothesis PMc_mat : mat_stable PMc.
Variable T : TSet.
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.
Hypothesis XP_stk : stk_okx (xp_stk xp).

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv ctasegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok ctasegs SHBW (ghost RT) JA FInvA).

(* [comment removed for export] *)
Lemma kind_apart_flag (Σ : rts RT) (m : word -> option byte) (b s : Z) (wr : bool) (flA : Z) :
  rkind RT sp0 r xp Σ b s wr -> ART RT Σ m -> loc_bounds RT lo sp0 r xp Σ ->
  ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP flA -> 0 < flA -> flA + 1 <= rt_sp0 RT Σ - STACK_WIN ->
  (flA + 1 <= 0x10000 \/ SEGTOP_A <= flA) -> (flA + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= flA) ->
  flA + 1 <= b \/ b + s <= flA.
Proof.
  intros K HART HB Hnc H0 Htop Himg Hsh. pose proof HB as (L1 & L2 & L3 & L4).
  destruct K as [-> -> | K1 K2 | a0 n0 K -> -> _ | -> -> | Hin H0' | k Hin -> | f k Hin -> ->].
  - right. lia.
  - destruct Himg; [left; lia | right; lia].
  - destruct (skind_shadow RT AF lo sp0 r xp H_r XP_stk Σ m a0 n0 HART HB K) as (Q1 & Q2 & _). unfold SH_LO, SH_HI in *. destruct Hsh; [left; lia | right; lia].
  - left. lia.
  - assert (X : ~ (b <= flA < b + s)) by (intros X; apply Hnc; right; right; left; exists b, s; auto). lia.
  - assert (X : ~ (b <= flA < b + fs_size k - 8)).
    { intros X. apply Hnc. right; right; right; left. exists b, k. split; [exact Hin | lia]. }
    lia.
  - destruct (af_frames_range RT AF _ _ _ _ HART Hin) as (F1 & F2 & _). pose proof (fs_size_facts k) as (G1 & G2 & G3 & G4).
    pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r.
    pose proof (shad_range f ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as R1.
    pose proof (shad_range (f + fs_size k) ltac:(unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia)) as R2.
    rewrite (shad_end f (fs_size k)) in R2 by (Z.div_mod_to_equations; lia). unfold SH_LO, SH_HI in *. destruct Hsh; [left; lia | right; lia].
Qed.

(* [comment removed for export] *)
Lemma release_view (rho : valuation) (S : sstate) (ms : machine_state) (Me : HxMem.mem) (t fl : int) (rg : region) (flA : Z) :
  (forall x, mget Me x = None) ->
  Rn ctasegs rho S ms -> mget (s_mem S) t = Some rg -> rg_abs rg = None -> fsz (to_Z (rg_size rg)) ->
  to_Z t < to_Z (s_next S) -> to_Z (s_next S) <= to_Z fl -> to_Z fl < 999990 -> tag_even t = true -> tag_even fl = true ->
  rho t + to_Z (rg_size rg) + 8 < 2 ^ 47 -> 0 < flA -> flA + 1 < 2 ^ 47 -> (flA + 1 <= rho t \/ rho t + to_Z (rg_size rg) + 8 <= flA) ->
  rw_cells ctasegs (ms_mem ms) flA [C1 (Z_to_bv 8 1)] -> bytes_at ctasegs (ms_mem ms) (rho t + to_Z (rg_size rg)) (le8 (Z_to_bv 64 flA)) ->
  RSn ctasegs SHBW (fun x : int => if (x =? fl)%uint63 then flA else rho x)
    (SS (s_pc S) (s_regs S) (s_resv S)
        (mset (mset Me t (RG None (rg_size rg + 8)%uint63 (rg_al rg) false (rg_dflt rg) (rg_d rg) (iset (rg_d rg) (rg_cells rg) (rg_size rg >> 3)%uint63 (CP fl w_zero))))
              fl (RG None 1 0 true DUnk 0 (iset 0 IEmpty 0 (CW w_one 1))))
        (s_abs S) (fl + 2)%uint63) ms.
Proof.
  intros Hemp HRn Eg Eabs Hfs Tt2 Tr Ec2 Ttev Tev Hftop R3 Hfltop R3b R1 R4b.
  pose proof (fsz_facts _ Hfs) as (F1 & F2 & F3 & F4).
  assert (Esz8 : to_Z (rg_size rg + 8)%uint63 = to_Z (rg_size rg) + 8).
  { rewrite add_spec. change (to_Z 8%uint63) with 8. apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  (* [comment removed for export] *)
  remember (mset (mset Me t (RG None (rg_size rg + 8)%uint63 (rg_al rg) false (rg_dflt rg) (rg_d rg) (iset (rg_d rg) (rg_cells rg) (rg_size rg >> 3)%uint63 (CP fl w_zero))))
                 fl (RG None 1 0 true DUnk 0 (iset 0 IEmpty 0 (CW w_one 1)))) as Mt eqn:EMt.
  set (rho_t := fun x : int => if (x =? fl)%uint63 then flA else rho x).
  assert (Hag_t : agree_below (s_next S) rho rho_t).
  { intros x Hx. unfold rho_t. destruct (eqbP x fl) as [E|E]; [rewrite E in Hx; lia | reflexivity]. }
  assert (Erfl : rho_t fl = flA) by (unfold rho_t; rewrite Uint63.eqb_refl; reflexivity).
  assert (Efl2 : to_Z (fl + 2)%uint63 = to_Z fl + 2) by (apply add2_Z; lia).
  assert (Hfl20 : to_Z fl < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Ht20 : to_Z t < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  split.
  - intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below (s_next S) rho rho2).
    { intros x Hx. rewrite (Hag2 x) by lia. apply Hag_t. exact Hx. }
    assert (E2fl : rho2 fl = flA) by (rewrite (Hag2 fl) by lia; exact Erfl).
    assert (E2t : rho2 t = rho t) by (apply Hag02; lia).
    destruct (HRn rho2 Hag02) as (Hsvc & Hpc & HRg2 & Hrv2 & HRm2).
    split; [exact Hsvc|]. split; [exact Hpc|]. split; [exact HRg2|]. split; [exact Hrv2|]. cbn [s_mem]. rewrite EMt.
    split.
    + intros t3 rg3 G3. destruct (mget_mset_cases _ fl t3 _ rg3 Hfl20 G3) as [[-> ->]|[N1 G3']].
      * apply (region_ok_flag rho2 fl (ms_mem ms) flA E2fl R3); [unfold two63; lia | exact R1].
      * destruct (mget_mset_cases Me t t3 _ rg3 Ht20 G3') as [[-> ->]|[N2 G3'']]; [|rewrite Hemp in G3''; discriminate].
        apply (region_ok_frameN rho2 t fl rg (ms_mem ms) flA (proj1 HRm2 t rg Eg) Eabs Hfs E2fl); [lia | rewrite E2t; unfold two63; lia | rewrite E2t; exact R4b].
    + apply (regions_sep_new rho2 _ fl).
      * apply (regions_sep_new rho2 Me t); [| apply Hemp | exact Ht20 |].
        -- intros t1 t2 r1 r2 G1. rewrite Hemp in G1. discriminate.
        -- intros t2 rg2 G2. rewrite Hemp in G2. discriminate.
      * rewrite (mget_mset Me t fl _ Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z fl)) as [E|E]; [lia | apply Hemp].
      * exact Hfl20.
      * intros t2 rg2 G2. destruct (mget_mset_cases Me t t2 _ rg2 Ht20 G2) as [[-> ->]|[N2 G2']]; [|rewrite Hemp in G2'; discriminate].
        unfold rbase. cbn [rg_abs rg_size]. rewrite E2fl, E2t, Esz8. change (to_Z 1%uint63) with 1. lia.
  - cbn [s_mem]. rewrite EMt. intros rho2 Hag2 s rgx Gx Eax Hodd.
    destruct (mget_mset_cases _ fl s _ rgx Hfl20 Gx) as [[-> ->]|[N1 Gx']]; [congruence|].
    destruct (mget_mset_cases Me t s _ rgx Ht20 Gx') as [[-> ->]|[N2 Gx'']]; [congruence | rewrite Hemp in Gx''; discriminate].
Time Qed.

Lemma hkA_release_ok : xhook_okA hkA_release.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_release, hkx_release in Hh.
  destruct (x_frames cd) as [|t fr] eqn:Efl; [discriminate|].
  destruct (mget (s_mem S) t) as [rg|] eqn:Eg; [|discriminate]. destruct (mget (s_mem S) (sh_tag t)) as [rgs|] eqn:Egs; [|discriminate].
  destruct (((rg_size rg =? 56) || (rg_size rg =? 120) || (rg_size rg =? 248))%uint63 && (even_up (s_next S) <? 999990)%uint63) eqn:Eck; [|discriminate].
  apply andb_prop in Eck as [Ec1 Ec2]. apply ltb_spec in Ec2. change (to_Z 999990%uint63) with 999990 in Ec2.
  assert (Hfs : fsz (to_Z (rg_size rg))).
  { unfold fsz. apply orb_prop in Ec1 as [Ec1|Ec1]; [apply orb_prop in Ec1 as [Ec1|Ec1]|]; apply Uint63.eqb_spec in Ec1; rewrite Ec1;
      [left | right; left | right; right]; reflexivity. }
  clear Ec1. pose proof (fsz_facts _ Hfs) as (FZ1 & FZ2 & FZ3 & FZ4). set (fs := to_Z (rg_size rg)) in *.
  cbv zeta in Hh. set (fl := even_up (s_next S)) in *.
  set (rg64 := RG None (rg_size rg + 8)%uint63 (rg_al rg) false (rg_dflt rg) (rg_d rg) (iset (rg_d rg) (rg_cells rg) (rg_size rg >> 3)%uint63 (CP fl w_zero))) in *.
  set (rgf := RG None 1 0 true DUnk 0 (iset 0 IEmpty 0 (CW w_one 1))) in *.
  remember (mset (mset IEmpty t rg64) fl rgf) as Mt eqn:EMt.
  (* [comment removed for export] *)
  remember (SS (s_pc S) (s_regs S) (s_resv S) Mt (s_abs S) (fl + 2)%uint63) as St eqn:ESt.
  destruct (hxs_step SHBW ctasegs IEmpty St) as [ic1 [S1|c1 S1]] eqn:Es1; [|discriminate].
  destruct (hxs_step SHBW ctasegs IEmpty S1) as [ic2 [S2|c2 S2]] eqn:Es2; [|discriminate].
  destruct (mget (s_mem S2) fl) as [rgf2|] eqn:Egf2; [|discriminate].
  destruct (flag_known_zero ctasegs rgf2 && w_eqb (s_pc S2) (w_add (s_pc S) (W false 8))) eqn:Eck2; [|discriminate].
  apply andb_prop in Eck2 as [Ez Epc2]. injection Hh as <- <-.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr).
  rewrite Efl in *. change (to_Z NEXT0) with 32 in *.
  set (m := ms_mem ms) in *.
  (* [comment removed for export] *)
  destruct (even_up_spec (s_next S) Hnx) as [Tev Tr]. fold fl in Tev, Tr.
  assert (Efl2 : to_Z (fl + 2)%uint63 = to_Z fl + 2) by (apply add2_Z; lia).
  assert (Hfl20 : to_Z fl < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Hint : In t (x_blocks cd ++ t :: fr)) by (apply in_or_app; right; left; reflexivity).
  destruct (Htl t Hint) as (Ttev & Tt1 & Tt2).
  assert (Ht20 : to_Z t < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  assert (Est : to_Z (sh_tag t) = to_Z t + 1) by (apply sh_tag_Z; lia).
  (* [comment removed for export] *)
  destruct (proj2 Hlink t ltac:(left; reflexivity)) as (rg' & Eg' & Eabs & Ewr & _). rewrite Eg in Eg'. injection Eg' as <-.
  set (f := rho t) in *. set (k := fcls fs).
  assert (Ersz : rsize (s_mem S) t = fs) by (unfold rsize; rewrite Eg; reflexivity).
  assert (Efk : fs_size k = fs + 8) by (unfold k; apply fcls_size; exact Hfs).
  assert (Hfr' : rt_frames RT (g_S RT g) = (f, k) :: frm_list rho (s_mem S) fr) by (rewrite Hfr; unfold frm_list; cbn [map]; rewrite Ersz; reflexivity).
  assert (HinF : In (f, k) (rt_frames RT (g_S RT g))) by (rewrite Hfr'; left; reflexivity).
  destruct (af_frames_range RT AF _ _ _ _ HART HinF) as (F1 & F2 & F3 & F4). rewrite Efk in *.
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r.
  destruct (af_frame_release RT AF (g_S RT g) m f k (frm_list rho (s_mem S) fr) HART Hfr') as (Σ' & flA & R1 & R2 & R3 & R3b & R3c & R3d & R3e & R4 & R5).
  rewrite Efk in *. replace (f + (fs + 8) - 8) with (f + fs) in R4 by ring.
  assert (R4b : bytes_at ctasegs m (f + fs) (le8 (Z_to_bv 64 flA))).
  { destruct R4 as [_ Hb]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  (* [comment removed for export] *)
  set (rho_t := fun x : int => if (x =? fl)%uint63 then flA else rho x).
  assert (Hag_t : agree_below (s_next S) rho rho_t).
  { intros x Hx. unfold rho_t. destruct (eqbP x fl) as [E|E]; [rewrite E in Hx; lia | reflexivity]. }
  assert (Erfl : rho_t fl = flA) by (unfold rho_t; rewrite Uint63.eqb_refl; reflexivity).
  (* [comment removed for export] *)
  assert (HRSt : RSn ctasegs SHBW rho_t St ms).
  { unfold rho_t. rewrite ESt, EMt.
    apply (release_view rho S ms IEmpty t fl rg flA mget_empty HRn Eg Eabs Hfs); try assumption; fold fs; try lia;
      unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia. }
  (* [comment removed for export] *)
  destruct (hxs_step_RSn ctasegs SHBW rho_t IEmpty ic1 St S1 ms (ic_ok_empty ctasegs) HRSt Es1) as (_ & ms1 & Hst1 & HRS1 & Hf1 & Hfc1 & Ho1 & Hm1 & Hrs1).
  destruct (hxs_step_RSn ctasegs SHBW rho_t IEmpty ic2 S1 S2 ms1 (ic_ok_empty ctasegs) HRS1 Es2) as (_ & ms2 & Hst2 & HRS2 & Hf2 & Hfc2 & Ho2 & Hm2 & Hrs2).
  destruct (hxs_step_next ctasegs SHBW IEmpty ic1 St S1 Es1) as [Enx1 Eabs1]. destruct (hxs_step_next ctasegs SHBW IEmpty ic2 S1 S2 Es2) as [Enx2 Eabs2].
  pose proof (hxs_step_dirs ctasegs SHBW IEmpty ic1 St S1 Es1) as Hd1. pose proof (hxs_step_dirs ctasegs SHBW IEmpty ic2 S1 S2 Es2) as Hd2.
  assert (EsmT : s_mem St = Mt) by (rewrite ESt; reflexivity). assert (EnxT : s_next St = (fl + 2)%uint63) by (rewrite ESt; reflexivity).
  rewrite EsmT in Hd1, Hm1. rewrite EnxT in Enx1.
  (* [comment removed for export] *)
  assert (HwrT : forall t' rg', mget Mt t' = Some rg' -> rg_wr rg' = true -> t' = fl /\ rg_abs rg' = None /\ to_Z (rg_size rg') = 1).
  { rewrite EMt. intros t' rg' G' W'. destruct (mget_mset_cases _ fl t' _ rg' Hfl20 G') as [[-> ->]|[N1 G'']]; [auto|].
    destruct (mget_mset_cases IEmpty t t' _ rg' Ht20 G'') as [[-> ->]|[N2 G3]]; [discriminate W' | rewrite mget_empty in G3; discriminate]. }
  assert (Hwr1 : forall t' rg', mget (s_mem S1) t' = Some rg' -> rg_wr rg' = true -> t' = fl /\ rg_abs rg' = None /\ to_Z (rg_size rg') = 1).
  { intros t' rg' G' W'.
    specialize (Hd1 t').
    rewrite G' in Hd1.
    destruct (mget Mt t') as [rg0|] eqn:G0; [|contradiction].
    destruct Hd1 as (Ea & Es & _ & Ew & _).
    rewrite Ea, Es.
    apply (HwrT t' rg0 G0).
    rewrite <- Ew. exact W'. }
  assert (Hwr2 : forall rg', mget (s_mem S2) fl = Some rg' -> rg_abs rg' = None /\ to_Z (rg_size rg') = 1 /\ rg_wr rg' = true).
  { assert (GetFl : mget Mt fl = Some rgf) by (rewrite EMt, (mget_mset _ fl fl rgf Hfl20), Z.eqb_refl; reflexivity).
    intros rg' G'. pose proof (Hd2 fl) as X2. rewrite G' in X2. destruct (mget (s_mem S1) fl) as [rg1|] eqn:G1; [|contradiction].
    pose proof (Hd1 fl) as X1. rewrite G1, GetFl in X1.
    destruct X1 as (Ea1 & Es1' & _ & Ew1 & _). destruct X2 as (Ea2 & Es2' & _ & Ew2 & _).
    rewrite Ea2, Ea1, Es2', Es1', Ew2, Ew1. auto. }
  (* [comment removed for export] *)
  assert (Hstep : forall (M : HxMem.mem) (ma mb : word -> option byte),
            (forall t' rg', mget M t' = Some rg' -> rg_wr rg' = true -> t' = fl /\ rg_abs rg' = None /\ to_Z (rg_size rg') = 1) ->
            mem_step rho_t M ma mb -> wr_at ctasegs ma flA 1 -> mem_inv ctasegs ma ->
            munch [(flA, flA + 1)] ma mb /\ wmono ctasegs ma mb /\ mem_inv ctasegs mb).
  { intros M ma mb HW [->|(t' & rg' & off & bs & G' & W' & Em & Hoff)] Hwa Hia; [split; [apply munch_refl | split; [apply wmono_refl | exact Hia]]|].
    destruct (HW t' rg' G' W') as (-> & Ea' & Es'). unfold rbase in Em. rewrite Ea', Erfl in Em. rewrite Es' in Hoff.
    pose proof (to_Z_bounded off) as Bo. subst mb.
    split; [apply munch_write; [apply munch_refl | lia | unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia | cbn [inside]; left; lia]|].
    split; [apply wmono_write, wmono_refl|].
    apply mem_inv_store; [exact Hia|]. exact (wr_at_store_ok ctasegs ma flA 1 (to_Z off) (length bs) Hwa ltac:(lia) ltac:(lia)). }
  assert (Hwa0 : wr_at ctasegs m flA 1) by (destruct R1 as [_ X]; exact X).
  destruct (Hstep Mt m (ms_mem ms1) HwrT Hm1 Hwa0 Hmi) as (MU1 & WM1 & MI1).
  assert (Hwa1 : wr_at ctasegs (ms_mem ms1) flA 1).
  { destruct Hwa0 as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. intros i Hi. apply WM1, X3, Hi. }
  destruct (Hstep (s_mem S1) (ms_mem ms1) (ms_mem ms2) Hwr1 Hm2 Hwa1 MI1) as (MU2 & WM2 & MI2).
  set (m2 := ms_mem ms2) in *.
  assert (MU : munch [(flA, flA + 1)] m m2) by (exact (munch_trans _ _ _ _ MU1 MU2)).
  assert (WM : wmono ctasegs m m2) by (exact (wmono_trans ctasegs _ _ _ WM1 WM2)).
  (* [comment removed for export] *)
  destruct (Hwr2 rgf2 Egf2) as (Eaf2 & Esf2 & Ewf2).
  pose proof (Rn_R ctasegs rho_t S2 ms2 (proj1 HRS2)) as (_ & _ & _ & _ & [HRg_2 _]).
  pose proof (flag_zero_cells rho_t fl rgf2 m2 flA (HRg_2 fl rgf2 Egf2) Eaf2 Esf2 Ewf2 Erfl Ez) as Hz.
  destruct (R5 m2 MU WM Hz) as (HART' & Efr' & El' & Es' & Ecr' & Eal' & HM').
  (* [comment removed for export] *)
  apply (J_evt RT AF PMc PMc_mat T g ms). exists ms2. split; [eapply msteps_trans; [apply msteps_one; exact Hst1 | apply msteps_one; exact Hst2]|].
  intros c Hc. apply (K (GH RT Σ') rho_t ms2 Hag_t); [|exact (ASTA_switch RT (g_S RT g) Σ' PMc _ c Hc Eal' HM')].
  (* [comment removed for export] *)
  assert (Hst20 : to_Z (sh_tag t) < to_Z TAGLIM) by (change (to_Z TAGLIM) with 1048576; lia).
  remember (kill_region (kill_region (s_mem S) t rg) (sh_tag t) rgs) as M3 eqn:EM3.
  assert (Cases3 : forall x rgx, mget M3 x = Some rgx ->
            (x = sh_tag t /\ rgx = dead_rg) \/ (x = t /\ rgx = dead_rg) \/ (x <> sh_tag t /\ x <> t /\ mget (s_mem S) x = Some rgx)).
  { rewrite EM3. intros x rgx G. destruct (mget_kill_cases _ (sh_tag t) x _ rgx Hst20 G) as [[-> ->]|[N1 G']]; [left; auto|].
    destruct (mget_kill_cases _ t x _ rgx Ht20 G') as [[-> ->]|[N2 G'']]; [right; left; auto | right; right; auto]. }
  assert (GetOld3 : forall x, x <> t -> x <> sh_tag t -> mget M3 x = mget (s_mem S) x).
  { intros x N1 N2. rewrite EM3, (mget_kill_region _ (sh_tag t) x rgs Hst20).
    destruct (Z.eqb_spec (to_Z (sh_tag t)) (to_Z x)) as [E|E]; [apply to_Z_inj in E; exfalso; apply N2; symmetry; exact E|].
    rewrite (mget_kill_region _ t x rg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z x)) as [E'|E']; [apply to_Z_inj in E'; exfalso; apply N1; symmetry; exact E' | reflexivity]. }
  destruct (FMem_loc_bounds RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m HF) as [HB _].
  assert (Hfa : forall rho2, agree_below (s_next S) rho rho2 -> forall x rgx, mget (s_mem S) x = Some rgx ->
            flA + 1 <= rbase rho2 x rgx \/ rbase rho2 x rgx + to_Z (rg_size rgx) <= flA).
  { intros rho2 Hag x rgx G.
    exact (kind_apart_flag (g_S RT g) m _ _ _ flA (region_loc RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho rho2 cd (s_mem S) (s_next S) m x rgx HF Hag G)
             HART HB R2 R3 R3b R3d R3e). }
  assert (Hkept : forall a, 0 <= a < 2 ^ 64 -> a <> flA -> m2 (wa a) = m (wa a)).
  { intros a Ha Hne. apply MU. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I]. }
  (* [comment removed for export] *)
  assert (Hnt : forall x, In x (x_blocks cd ++ fr) -> x <> t /\ x <> sh_tag t /\ In x (x_blocks cd ++ t :: fr)).
  { intros x Hin. assert (Hin' : In x (x_blocks cd ++ t :: fr)) by (apply in_app_or in Hin; apply in_or_app; destruct Hin; [left | right; right]; assumption).
    split; [|split; [|exact Hin']].
    - intros ->. exact (NoDup_remove_2 _ _ _ Hnd Hin).
    - intros ->. destruct (Htl _ Hin') as (X & _). destruct (sh_tag_odd t Ttev Ht20) as [Y _]. rewrite Y in X. discriminate X. }
  assert (HF' : FMemA (GH RT Σ') rho_t (XCD (x_blocks cd) fr (x_calls cd + 1) (x_nb cd)) M3 (fl + 2)%uint63 m2).
  { apply (FMem_update RT CL lo sp0 r m0 cr0 anc xp g rho rho_t cd (s_mem S) M3 (s_next S) _ m m2 Σ' sp0 _ _ _ _ HF Hag_t); try assumption; try lia.
    - (* [comment removed for export] *)
      destruct Hstk as (S1' & S2' & S3'). split; [exact S1'|]. split; [exact S2'|]. intros a Ha. destruct (S3' a Ha) as [Hw (b & Hb)].
      assert (Ea : m2 (wa a) = m (wa a)) by (apply Hkept; unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia).
      destruct (same_byte_kept m m2 _ Ea) as [E1 E2]. split; [exact (E2 Hw) | exists b; rewrite E1; exact Hb].
    - unfold B0. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). destruct H_r; lia.
    - intros a Hcm. assert (Hne : bv_unsigned a <> flA).
      { intros E. apply R2. rewrite <- E. destruct Hcm as [[Hcm|[Hcm|[(p & n & Hin & Hr)|[(f0 & k0 & [] & _)|(f0 & k0 & [] & _)]]]] _].
        - exfalso. rewrite E in Hcm. unfold B0 in *. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1). destruct H_r; lia.
        - right; left. exact Hcm.
        - right; right; left. exists p, n. split; [rewrite Hlive; apply in_or_app; right; exact Hin | exact Hr]. }
      pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      pose proof (Hkept (bv_unsigned a) Hr Hne) as X. unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. exact X.
    - rewrite El', Hlive. unfold blk_list. f_equal. apply map_ext_in. intros b Hb.
      destruct (Hnt b (in_or_app _ _ _ (or_introl Hb))) as (N1 & N2 & Hin'). destruct (Htl b Hin') as (_ & Tb1 & Tb2).
      rewrite (Hag_t b) by lia. f_equal. unfold rsize. rewrite (GetOld3 b N1 N2). reflexivity.
    - rewrite Efr'. unfold frm_list. apply map_ext_in. intros f0 Hf. destruct (Hnt f0 (in_or_app _ _ _ (or_intror Hf))) as (N1 & N2 & Hin').
      destruct (Htl f0 Hin') as (_ & Tb1 & Tb2). rewrite (Hag_t f0) by lia. f_equal. f_equal. unfold rsize. rewrite (GetOld3 f0 N1 N2). reflexivity.
    - exact (NoDup_remove_1 _ _ _ Hnd).
    - intros x Hin. destruct (Hnt x Hin) as (_ & _ & Hin'). destruct (Htl x Hin') as (X1 & X2 & X3). split; [exact X1|]. change (to_Z NEXT0) with 32. lia.
    - intros x rgx G. destruct (Cases3 x rgx G) as [[-> _]|[[-> _]|(_ & _ & G')]]; [lia | lia | pose proof (Htags _ _ G'); lia].
    - intros x rgx G. destruct (Cases3 x rgx G) as [[-> ->]|[[-> ->]|(N1 & N2 & G')]].
      + cbn [rg_abs rg_size rg_wr]. left. repeat split; reflexivity.
      + cbn [rg_abs rg_size rg_wr]. left. repeat split; reflexivity.
      + pose proof (Hcls x rgx G') as C. destruct (rg_abs rgx); [exact C|].
        destruct C as [C|[C|[C|[(b & Hin & Eb & Es3 & Ew3)|[(Hin & C)|[(f0 & Hin & Ef0 & C)|C]]]]]].
        * left. exact C.
        * right; left. exact C.
        * right; right; left. exact C.
        * right; right; right; left. exists b. split; [exact Hin|]. split; [exact Eb|]. split; [|exact Ew3]. rewrite Es3. f_equal.
          destruct (Hnt b (in_or_app _ _ _ (or_introl Hin))) as (Nb1 & Nb2 & _). unfold rsize. rewrite (GetOld3 b Nb1 Nb2). reflexivity.
        * right; right; right; right; left. split; [|exact C]. destruct Hin as [E|Hin]; [exfalso; apply N2; symmetry; exact E | exact Hin].
        * right; right; right; right; right; left. exists f0. assert (Hin2 : In f0 fr) by (destruct Hin as [E|Hin]; [subst f0; exfalso; apply N1; exact Ef0 | exact Hin]).
          split; [exact Hin2|]. split; [exact Ef0|]. destruct C as [Es3 Ew3]. split; [|exact Ew3]. rewrite Es3. f_equal. f_equal.
          destruct (Hnt f0 (in_or_app _ _ _ (or_intror Hin2))) as (Nb1 & Nb2 & _). unfold rsize. rewrite (GetOld3 f0 Nb1 Nb2). reflexivity.
        * right; right; right; right; right; right. exact C.
    - destruct Hlink as [LL1 LL2]. split.
      + intros b Hb. destruct (LL1 b Hb) as (rgb & Gb & X). exists rgb. split; [|exact X].
        destruct (Hnt b (in_or_app _ _ _ (or_introl Hb))) as (Nb1 & Nb2 & _). rewrite (GetOld3 b Nb1 Nb2). exact Gb.
      + intros f0 Hf. destruct (LL2 f0 (or_intror Hf)) as (rgf0 & Gf & X). exists rgf0. split; [|exact X].
        destruct (Hnt f0 (in_or_app _ _ _ (or_intror Hf))) as (Nb1 & Nb2 & _). rewrite (GetOld3 f0 Nb1 Nb2). exact Gf.
    - intros x Hin. destruct (Hnt x Hin) as (_ & _ & Hin'). destruct (Htl x Hin') as (_ & X2 & X3).
      rewrite (Hag_t (sh_tag x)) by (rewrite sh_tag_Z by lia; lia). rewrite (Hag_t x) by lia. exact (Hrsh x Hin'). }
  split; [split|split; [exact HF' | split; [|]]].
  - (* [comment removed for export] *)
    intros rho2 Hag2. cbn [s_next] in Hag2.
    assert (Hag02 : agree_below (s_next S) rho rho2).
    { intros x Hx. rewrite (Hag2 x) by lia. apply Hag_t. exact Hx. }
    destruct (proj1 HRS2 rho2 ltac:(rewrite Enx2, Enx1; exact Hag2)) as (Hsvc & Hpc & HRg2 & Hrv2 & _).
    split; [exact Hsvc|]. split; [exact Hpc|]. split; [exact HRg2|]. split; [exact Hrv2|]. cbn [s_mem]. fold m2.
    destruct (HRn rho2 Hag02) as (_ & _ & _ & _ & HRm2). fold m in HRm2.
    assert (HRm3 : Rmem ctasegs rho2 (s_mem S) m2).
    { apply (Rmem_frame ctasegs rho2 (s_mem S) m m2 HRm2). intros x rgx G i Hi.
      destruct (proj1 HRm2 x rgx G) as (Bx0 & Bx1 & _). unfold two63 in Bx1.
      apply same_byte_kept. apply Hkept; [lia|]. destruct (Hfa rho2 Hag02 x rgx G); lia. }
    rewrite EM3. apply (Rmem_kill_region ctasegs rho2 _ (sh_tag t) rgs m2); [exact (Rmem_kill_region ctasegs rho2 _ t rg m2 HRm3 Eg)|].
    rewrite (mget_kill_region _ t (sh_tag t) rg Ht20). destruct (Z.eqb_spec (to_Z t) (to_Z (sh_tag t))) as [E|E]; [lia | exact Egs].
  - intros rho2 Hag2. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp (GH RT Σ') rho_t rho2 _ _ _ m2 HF' Hag2).
  - rewrite Ho2, Ho1. exact Hro.
  - exact (regs_nf_step _ _ (regs_nf_step _ _ Hnf Hrs1) Hrs2).
Time Qed.

End HkRelease.
