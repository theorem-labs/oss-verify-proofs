(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StepTac MemSplit.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout RefMemcpyLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbStartupDefs UbStartup UDrvData.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SP0 := lvar 1. Definition ARGC := lvar 2. Definition P0 := lvar 3. Definition P1 := lvar 4.
Definition C := lvar 5. Definition T := lvar 6. Definition X0 := lvar 7. Definition X1 := lvar 8.

Fixpoint rpat (base : positive) (k : nat) (acc : tree lin) : tree lin :=
  match k with O => acc | S k' => rpat base k' (tset (Pos.of_succ_nat k) (lvar (base + Pos.of_nat k)) acc) end.
Definition KNOWN_P : list (nat * lin) :=
  [(1%nat, lconst 0x5265c); (2%nat, laddc SP0 (-48)); (3%nat, lconst 0x10800); (4%nat, lconst 0x77990);
   (10%nat, ARGC); (11%nat, laddc SP0 8)].
Definition R_main : tree lin :=
  Eval vm_compute in fold_left (fun t '(j, l) => tset (Pos.of_succ_nat j) l t) KNOWN_P (rpat 100 31 TEmpty).
Lemma R_main_ok : rpat_ok R_main KNOWN_P 100 = true.
Proof. vm_compute. reflexivity. Qed.

Definition RG_img : list region :=
  [ RGz (lconst 0x65a18) 344 RO TEmpty;                              (* [comment removed for export] *)
    RGz (lconst 0x659a8) 32 RO TEmpty;                               (* [comment removed for export] *)
    RGz (lconst 0x66bd8) 232 RI TEmpty;                              (* [comment removed for export] *)
    RGz (lconst 0x66cc8) 232 RI TEmpty;                              (* [comment removed for export] *)
    RGz (lconst 0x778e8) 8 RI (put_bytes TEmpty 0 (bvs_of T 4));     (* [comment removed for export] *)
    RGz (lconst 0x97c00) 8 RW (put_bytes TEmpty 0 (bvs_of C 8));     (* [comment removed for export] *)
    RGz (lconst 0x76e20) 24 RI TEmpty;                               (* [comment removed for export] *)
    RGz (lconst 0x98060) 1032 RI TEmpty;                             (* [comment removed for export] *)
    RGz (lconst 0x10481) 24 RO TEmpty; RGz (lconst 0x10bd5) 32 RO TEmpty; RGz (lconst 0x10f35) 56 RO TEmpty;
    RGz (lconst 0x11bc5) 40 RO TEmpty; RGz (lconst 0x1287e) 8 RO TEmpty; RGz (lconst 0x125ce) 64 RO TEmpty;
    RGz (lconst 0x12bd6) 40 RO TEmpty; RGz (lconst 0x12f2e) 8 RO TEmpty; RGz (lconst 0x13020) 16 RO TEmpty;
    RGz (lconst 0x18330) 528 RO TEmpty;                             (* [comment removed for export] *)
    RGz (lconst 0x979d8) 296 RI TEmpty ].                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition IMG_RO_P : list (Z * nat) := [(0x65a18, 344%nat); (0x659a8, 32%nat); (0x10481, 24%nat); (0x10bd5, 32%nat); (0x10f35, 56%nat);
  (0x11bc5, 40%nat); (0x1287e, 8%nat); (0x125ce, 64%nat); (0x12bd6, 40%nat); (0x12f2e, 8%nat); (0x13020, 16%nat); (0x18330, 528%nat)].
Definition IMG_RI_P : list (Z * nat) := [(0x66bd8, 232%nat); (0x66cc8, 232%nat); (0x778e8, 8%nat); (0x76e20, 24%nat); (0x98060, 1032%nat); (0x979d8, 296%nat)].
Time Lemma img_checks_P : forallb (fun '(lo, n) => img_ro_ok PSEGS lo n) IMG_RO_P = true /\ forallb (fun '(lo, n) => img_rw_ok PSEGS lo n) (IMG_RI_P ++ [(0x97c00, 8%nat)]) = true.
Proof. split; vm_compute; reflexivity. Time Qed.

(* [comment removed for export] *)
Definition DM_WRITES : list (Z * Z) := [(0x778c0,8); (0x97c28,8); (0x97c88,8); (0x97c50,8); (0x97c18,8); (0x97c10,8);
  (0x979b8,8); (0x979c8,8); (0x979c0,8); (0x97c38,8); (0x97c40,8); (0x779a0,8); (0x77988,8); (0x778c8,8); (0x97c20,1); (0x778f0,4);
  (0x778e8,4); (0x77960,8); (0x77940,8); (0x778d0,8); (0x778d8,8); (0x778e0,8);
  (0x97c00,4); (0x97c04,4); (0x97c01,1); (0x77980,8); (0x66dd0,1)].

Lemma u_const : forall c, 0 <= c < 2^64 -> bv_unsigned (Z_to_bv 64 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Time Lemma dmain_miss : forall sp0 av ev hw rdraw tid x,
  Forall (fun an : Z * Z => bv_unsigned x < fst an \/ fst an + snd an <= bv_unsigned x) DM_WRITES ->
  D_main sp0 av ev hw rdraw tid x = None.
Proof.
  intros sp0 av ev hw rdraw tid x H. unfold DM_WRITES in H.
  repeat (apply Forall_cons_iff in H as [?H H]). cbn [fst snd] in *.
  unfold D_main, D_fd, D_ssp, D_pre_ios, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite wbytes_outside;
          [ | cbn [length Z_to_le_bytes word_to_le_bytes]; rewrite u_const by lia; lia
            | cbn [length Z_to_le_bytes word_to_le_bytes]; rewrite u_const by lia; lia ]).
  reflexivity.
Time Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RG_hi1 : list region :=
  [ RGz (laddc SP0 (-65536)) 65536 RW TEmpty;
    RGz (laddc SP0 8) 16 RW (put_bytes TEmpty 0 (bvs_of P0 8 ++ bvs_of P1 8));
    RGz (ladd P0 X0) 1 RW (put_bytes TEmpty 0 [BK 0]) ].
Definition RG_main1 : list region := RG_hi1 ++ RG_img.
Definition F_main1 : list fact :=
  [FRange SP0 0x7fff80000000 0x800000000000; FMod SP0 4 0; FRange ARGC 1 1024; FCond BC_NE ARGC (lconst 2) true;
   FRange P0 0x7fff80000000 0x800010000000; FRange X0 0 131071; FRange T 1 4194304].
Definition P_main1 : sst := SST 0x228cc R_main RG_main1 F_main1 200 RNone.
Lemma P_main1_wf : state_wf P_main1 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition E_main (sp0 : word) (av ev : list (list byte)) (tid c : word) (regs : bvmap 5 word) : valu :=
  fun x =>
    if Pos.eqb x 1 then sp0
    else if Pos.eqb x 2 then argcN av
    else if Pos.eqb x 3 then cat_argv_ptr sp0 av ev 0
    else if Pos.eqb x 4 then (if Nat.ltb 1 (length av) then cat_argv_ptr sp0 av ev 1 else Z_to_bv 64 0)
    else if Pos.eqb x 5 then c
    else if Pos.eqb x 6 then tid
    else if Pos.eqb x 7 then Z_to_bv 64 (Z.of_nat (length (nth 0 av [])))
    else if Pos.eqb x 8 then Z_to_bv 64 (Z.of_nat (length (nth 1 av [])))
    else if (Pos.ltb 100 x && Pos.leb x 131)%bool then getr regs (Z_to_bv 5 (Zpos x - 100)) else Z_to_bv 64 0.

Lemma rk_find_in : forall known j l, rk_find known j = Some l -> In (j, l) known.
Proof.
  intros known j l H. unfold rk_find in H. destruct (List.find _ known) as [[k l']|] eqn:Hf; [|discriminate].
  injection H as <-. destruct (find_some _ _ Hf) as [Hin Hk]. cbn [fst] in Hk. apply Nat.eqb_eq in Hk. subst k. exact Hin.
Qed.

(* [comment removed for export] *)
Definition miss_ok (lo : Z) (n : nat) : bool :=
  forallb (fun an : Z * Z => Z.leb (lo + Z.of_nat n) (fst an) || Z.leb (fst an + snd an) lo)%bool DM_WRITES.
Lemma img_miss_ok : forallb (fun '(lo, n) => miss_ok lo n)
    (IMG_RO_P ++ [(0x66bd8, 232%nat); (0x66cc8, 232%nat); (0x778ec, 4%nat); (0x76e20, 24%nat); (0x98060, 1032%nat); (0x979d8, 296%nat)]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma miss_ok_byte : forall lo n i, miss_ok lo n = true -> 0 <= i < Z.of_nat n ->
  Forall (fun an : Z * Z => lo + i < fst an \/ fst an + snd an <= lo + i) DM_WRITES.
Proof.
  intros lo n i H Hi. unfold miss_ok in H. rewrite forallb_forall in H. apply Forall_forall. intros [a k] Hak.
  specialize (H (a, k) Hak). cbn [fst snd] in *. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma PSEGS_top : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) 0xa0000) PSEGS = true.
Proof. vm_compute. reflexivity. Qed.

Section Handoff.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.

Let E := E_main sp0 av ev tid (canary rdraw) regs.

#[using="Hsp"] Lemma sp0_lo : 0x7fff80000000 <= bv_unsigned sp0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). destruct Hsp as [H _]. exact H. Qed.
#[using="Hsp"] Lemma sp0_hi : bv_unsigned sp0 <= 0x800000000000. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). destruct Hsp as [_ [H _]]. exact H. Qed.
#[using="Hsp"] Lemma sp0_al : bv_unsigned sp0 mod 16 = 0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). destruct Hsp as [_ [_ H]]. exact H. Qed.

#[using="uid hw mem ME"] Lemma E_regs : regs_ok E R_main regs.
Proof. LiaFast.lf_pins (fun (uid hw mem ME : LiaFast.U) => LiaFast.u0).
  apply (regs_ok_pat E R_main regs KNOWN_P 100 R_main_ok).
  - intros j Hj Hf. unfold E, E_main.
    repeat (rewrite (proj2 (Pos.eqb_neq _ _)) by lia).
    rewrite (proj2 (Pos.ltb_lt _ _)) by lia. rewrite (proj2 (Pos.leb_le _ _)) by lia. cbn [andb].
    f_equal. f_equal. lia.
  - intros j l Hj Hf. apply rk_find_in in Hf. unfold KNOWN_P in Hf.
    repeat destruct Hf as [Hf|Hf]; try (injection Hf as <- <-); try (destruct Hf).
    + etransitivity; [exact (me_ra _ _ _ _ _ _ _ _ _ ME)|]. reflexivity.
    + etransitivity; [exact (me_sp _ _ _ _ _ _ _ _ _ ME)|]. unfold SP0. rewrite lden_laddc, lden_lvar. reflexivity.
    + etransitivity; [exact (me_gp _ _ _ _ _ _ _ _ _ ME)|]. reflexivity.
    + etransitivity; [exact (me_tp _ _ _ _ _ _ _ _ _ ME)|]. reflexivity.
    + etransitivity; [exact (me_a0 _ _ _ _ _ _ _ _ _ ME)|]. unfold ARGC. rewrite lden_lvar. reflexivity.
    + etransitivity; [exact (me_a1 _ _ _ _ _ _ _ _ _ ME)|]. unfold SP0. rewrite lden_laddc, lden_lvar. reflexivity.
Qed.

#[using="Type"] Lemma E_SP0 : lden E SP0 = sp0. Proof. LiaFast.lf_pins LiaFast.u0. unfold SP0. rewrite lden_lvar. reflexivity. Qed.

#[using="uid hw Hsp ME"] Lemma rg0_ok : rg_ok PSEGS E mem (RGz (laddc SP0 (-65536)) 65536 RW TEmpty).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H.
  assert (HA : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc, E_SP0. apply u_small64. unfold two64; lia. }
  apply rg_rw_empty_ok; rewrite ?HA; [lia | unfold two64; lia |].
  intros i Hi. apply (main_entry_win_mapped sp0 av ev uid tid hw rdraw regs mem ME).
  rewrite u_small64 by (unfold two64; lia). unfold stack_max_size. lia.
Qed.

#[using="Hsp"] Lemma u_sp0_plus : forall k, 0 <= k <= 2^40 -> bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + k)) = bv_unsigned sp0 + k.
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). intros k Hk. pose proof sp0_hi. pose proof sp0_lo. apply u_small64. unfold two64; lia. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME"] Lemma argv_slots : rdn PSEGS mem (Z_to_bv 64 (bv_unsigned sp0 + 8)) 16
  = Some (word_le8 (cat_argv_ptr sp0 av ev 0) ++ word_le8 (E 4%positive)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof (valid_argv_len av Hva) as Hlen. pose proof (valid_argv_nonempty av Hva) as Hne.
  change 16%nat with (8 + 8)%nat. apply rdn_app_some; [lia | unfold two64; lia | |].
  - rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_sp0_plus by lia; lia).
    pose proof (read_argv_ptr_w PSEGS RPH sp0 av ev uid hw rdraw Hva Hve L H 0 ltac:(lia)) as R.
    rewrite word_add_nat in R. exact R.
  - replace (bv_unsigned sp0 + 8 + Z.of_nat 8) with (bv_unsigned sp0 + 16) by lia.
    rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_sp0_plus by lia; lia).
    unfold E, E_main. cbn [Pos.eqb]. destruct (Nat.ltb 1 (length av)) eqn:Hl.
    + apply Nat.ltb_lt in Hl.
      pose proof (read_argv_ptr_w PSEGS RPH sp0 av ev uid hw rdraw Hva Hve L H 1 ltac:(lia)) as R.
      rewrite word_add_nat in R. replace (bv_unsigned sp0 + 16) with (bv_unsigned sp0 + Z.of_nat (8 + 8 * 1)) by lia.
      exact R.
    + apply Nat.ltb_ge in Hl. assert (Hl1 : length av = 1%nat) by lia.
      change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
      rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by (rewrite u_sp0_plus by lia; lia).
      pose proof (read_argv_null PSEGS RPH sp0 rdraw av ev uid hw Hva Hve H) as R.
      rewrite word_add_nat, Hl1 in R. replace (bv_unsigned sp0 + 16) with (bv_unsigned sp0 + Z.of_nat (8 + 8 * 1)) by lia.
      exact R.
Qed.

#[using="uid hw Hsp Hva Hve ME"] Lemma rg1_ok : rg_ok PSEGS E mem (RGz (laddc SP0 8) 16 RW (put_bytes TEmpty 0 (bvs_of P0 8 ++ bvs_of P1 8))).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H.
  change (RGz (laddc SP0 8) 16 RW (put_bytes TEmpty 0 (bvs_of P0 8 ++ bvs_of P1 8)))
    with (track (RGz (laddc SP0 8) 16 RW TEmpty) 0 (bvs_of P0 8 ++ bvs_of P1 8)).
  assert (HA : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc, E_SP0. apply u_sp0_plus. lia. }
  apply rg_track_rdn; [ | lia | rsz_simpl; cbn; lia | ].
  - apply rg_rw_empty_ok; rewrite ?HA; [lia | unfold two64; lia |].
    intros i Hi. rewrite (rdn_overlay PSEGS 0xa0000 mem (bv_unsigned sp0 + 8) 16 _ PSEGS_top ltac:(lia) ltac:(unfold two64; lia) argv_slots i ltac:(lia)).
    destruct (nth_error _ (Z.to_nat i)) eqn:Hn; [discriminate|]. apply nth_error_None in Hn.
    rewrite length_app, !length_n_to_le_8 in Hn. lia.
  - cbn [RGz rg_base track RGz]. rewrite HA, Z.add_0_r. change (length (bvs_of P0 8 ++ bvs_of P1 8)) with 16%nat. rewrite argv_slots. f_equal.
    rewrite map_app. unfold P0, P1. rewrite !bvs_of_den by lia. rewrite !n_to_le_8_spec. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma mem_miss : forall lo n i, 0 <= lo -> lo + Z.of_nat n <= 0xa0000 -> miss_ok lo n = true -> 0 <= i < Z.of_nat n ->
  mem (Z_to_bv 64 (lo + i)) = None.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo n i Hlo Hn Hm Hi. pose proof sp0_lo as L.
  rewrite (main_entry_mem_data sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  apply dmain_miss. pose proof (miss_ok_byte lo n i Hm Hi) as H.
  rewrite Forall_forall in H |- *. intros an Han. specialize (H an Han). rewrite u_small64 by (unfold two64; lia). exact H.
Qed.

#[using="uid hw Hsp ME"] Lemma rg_ro_ok : forall lo n, 0 <= lo -> lo + Z.of_nat n <= 0xa0000 -> miss_ok lo n = true -> img_ro_ok PSEGS lo n = true ->
  rg_ok PSEGS E mem (RGz (lconst lo) (Z.of_nat n) RO TEmpty).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo n Hlo Hn Hm Hc. apply rg_img_ro; [unfold two64; lia | unfold two64; lia | exact Hc |].
  intros i Hi. exact (mem_miss lo n i Hlo Hn Hm Hi).
Qed.

#[using="uid hw Hsp ME"] Lemma rg_ri_empty_ok : forall lo n, 0 <= lo -> lo + Z.of_nat n <= 0xa0000 -> miss_ok lo n = true -> img_rw_ok PSEGS lo n = true ->
  rg_ok PSEGS E mem (RGz (lconst lo) (Z.of_nat n) RI TEmpty).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo n Hlo Hn Hm Hc. apply rg_img_ri; [unfold two64; lia | unfold two64; lia | exact Hc | | | ].
  - intros i Hi _. exact (mem_miss lo n i Hlo Hn Hm Hi).
  - intros i Hi. right. exact (mem_miss lo n i Hlo Hn Hm Hi).
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma E_T : E 6%positive = tid. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma E_C : E 5%positive = canary rdraw. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="sp0 av ev uid hw rdraw regs Hsp ME"] Lemma rdn_tid : rdn PSEGS mem (Z_to_bv 64 0x778e8) 4 = Some (word_to_le_bytes 4 tid).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L.
  rewrite (main_entry_rdn_data sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  reflexivity.
Qed.

#[using="sp0 av ev uid tid hw regs Hsp ME"] Lemma rdn_guard : rdn PSEGS mem (Z_to_bv 64 0x97c00) 8 = Some (canary_bytes rdraw).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L.
  rewrite (main_entry_rdn_data sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_small64 by (unfold two64; lia); unfold stack_max_size; lia).
  reflexivity.
Qed.

#[using="uid hw Hsp ME"] Lemma rg6_ok : rg_ok PSEGS E mem (RGz (lconst 0x778e8) 8 RI (put_bytes TEmpty 0 (bvs_of T 4))).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  change 8 with (Z.of_nat 8). apply rg_img_ri; [unfold two64; lia | unfold two64; lia | | | | ].
  - destruct img_checks_P as [_ H]. vm_compute in H. vm_compute. reflexivity.
  - intros i Hi Hu. rewrite put_bytes_spec in Hu by lia. rewrite okey_pos in Hu by lia.
    destruct (Z.leb 0 i && Z.ltb i (0 + Z.of_nat (length (bvs_of T 4))))%bool eqn:Hin.
    + apply andb_prop in Hin as [_ Hin]. apply Z.ltb_lt in Hin. cbn in Hin.
      destruct (nth_error (bvs_of T 4) (Z.to_nat (i - 0))) eqn:Hx; [discriminate|]. apply nth_error_None in Hx. cbn in Hx. lia.
    + apply andb_false_iff in Hin as [Hin|Hin]; [apply Z.leb_gt in Hin; lia|]. apply Z.ltb_ge in Hin. cbn in Hin.
      replace (0x778e8 + i) with (0x778ec + (i - 4)) by lia.
      apply (mem_miss 0x778ec 4 (i - 4)); [lia | lia | vm_compute; reflexivity | lia].
  - intros i _. destruct (mem (Z_to_bv 64 (0x778e8 + i))); [left; discriminate | right; reflexivity].
  - intros p v Hp. rewrite put_bytes_spec in Hp by lia. rewrite tget_empty in Hp.
    destruct (Z.leb 0 (Zpos p - 1) && Z.ltb (Zpos p - 1) (0 + Z.of_nat (length (bvs_of T 4))))%bool eqn:Hin; [|discriminate].
    apply andb_prop in Hin as [_ Hin]. apply Z.ltb_lt in Hin. cbn in Hin. split; [lia|].
    rewrite Z.sub_0_r in Hp. unfold T in Hp.
    pose proof (rdn_rd1 PSEGS mem 0x778e8 4 _ ltac:(lia) ltac:(unfold two64; lia) rdn_tid (Z.to_nat (Zpos p - 1))) as H.
    rewrite Z2Nat.id in H by lia. apply H.
    unfold word_to_le_bytes. rewrite <- E_T. rewrite <- (bvs_of_den E 6 4) by lia. rewrite nth_error_map, Hp. reflexivity.
Qed.

#[using="uid hw Hsp ME"] Lemma rg7_ok : rg_ok PSEGS E mem (RGz (lconst 0x97c00) 8 RW (put_bytes TEmpty 0 (bvs_of C 8))).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  change (RGz (lconst 0x97c00) 8 RW (put_bytes TEmpty 0 (bvs_of C 8))) with (track (RGz (lconst 0x97c00) (Z.of_nat 8) RW TEmpty) 0 (bvs_of C 8)).
  apply rg_track_rdn; [ | lia | rsz_simpl; cbn; lia | ].
  - apply rg_rw_img; [unfold two64; lia | unfold two64; lia |].
    destruct img_checks_P as [_ H]. vm_compute in H. vm_compute. reflexivity.
  - cbn [RGz rg_base track RGz]. replace (bv_unsigned (lden E (lconst 0x97c00)) + 0) with 0x97c00 by (vm_compute; reflexivity).
    change (length (bvs_of C 8)) with 8%nat. rewrite rdn_guard. f_equal.
    unfold C. rewrite bvs_of_den by lia. rewrite E_C. rewrite <- (canary_val rdraw).
    assert (HL : length (canary_bytes rdraw) = 8%nat) by reflexivity.
    rewrite <- HL at 1. symmetry. apply Z_to_le_bytes_lez.
Qed.

#[using="Type"] Lemma E_P0 : E 3%positive = cat_argv_ptr sp0 av ev 0. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma E_X0 : E 7%positive = Z_to_bv 64 (Z.of_nat (length (nth 0 av []))). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="uid hw rdraw Hsp Hva Hve"] Lemma p0_bounds : bv_unsigned sp0 + 192 <= bv_unsigned (cat_argv_ptr sp0 av ev 0) /\
  bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av [])) + 1 < 2^64 /\
  bv_unsigned (cat_argv_ptr sp0 av ev 0) <= bv_unsigned sp0 + 2^28.
Proof. LiaFast.lf_pins (fun (uid hw rdraw Hsp Hva Hve : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof (valid_argv_nonempty av Hva) as Hne.
  pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve L H 0 ltac:(lia)) as U.
  pose proof (argv_ptr_bounds_at sp0 av ev Hva Hve H 0 ltac:(lia)) as [_ B].
  rewrite U in B |- *. unfold cat_struct_size, auxv_size in *. cbn [firstn total_arg_bytes_nat] in *.
  pose proof (valid_argv_len av Hva). destruct Hve as [Hev _].
  replace (total_arg_bytes_nat (firstn 0 av)) with 0%nat in * by reflexivity.
  split; [|split]; lia.
Qed.

#[using="uid hw Hsp Hva Hve"] Lemma u_P0X0 : bv_unsigned (lden E (ladd P0 X0)) = bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av [])).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve : LiaFast.U) => LiaFast.u0).
  pose proof p0_bounds as (B1 & B2 & B3). pose proof sp0_lo.
  rewrite lden_ladd. unfold P0, X0. rewrite !lden_lvar, E_P0, E_X0.
  rewrite bv_add_unsigned, Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (Z.of_nat _)) by (unfold bv_modulus; lia).
  apply bv_wrap_small. unfold bv_modulus. pose proof (bv_unsigned_in_range _ (cat_argv_ptr sp0 av ev 0)). lia.
Qed.

#[using="uid tid hw rdraw regs Hsp Hva Hve ME"] Lemma rdn_nul0 : rdn PSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av [])))) 1 = Some [Z_to_bv 8 0].
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve ME : LiaFast.U) => LiaFast.u0).
  pose proof p0_bounds as (B1 & B2 & B3). pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof (valid_argv_nonempty av Hva) as Hne.
  rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME) by (rewrite u_small64 by (unfold two64; lia); lia).
  change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
  rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by (rewrite u_small64 by (unfold two64; lia); lia).
  pose proof (read_argv_byte_k RPH PSEGS sp0 av ev 0 (length (nth 0 av [])) uid hw rdraw ltac:(lia) ltac:(lia)
                (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve H)) as R.
  rewrite word_add_nat in R. rewrite R. f_equal. f_equal.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

#[using="uid hw Hsp Hva Hve ME"] Lemma rg20_ok : rg_ok PSEGS E mem (RGz (ladd P0 X0) 1 RW (put_bytes TEmpty 0 [BK 0])).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME : LiaFast.U) => LiaFast.u0).
  pose proof p0_bounds as (B1 & B2 & B3). pose proof sp0_lo as L.
  change (RGz (ladd P0 X0) 1 RW (put_bytes TEmpty 0 [BK 0])) with (track (RGz (ladd P0 X0) 1 RW TEmpty) 0 [BK 0]).
  apply rg_track_rdn; [ | lia | rsz_simpl; cbn; lia | ].
  - apply rg_rw_empty_ok; rewrite ?u_P0X0; [lia | unfold two64; lia |].
    intros i Hi.
    pose proof (rdn_overlay PSEGS 0xa0000 mem (bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av []))) 1 [Z_to_bv 8 0] PSEGS_top) as HO.
    rewrite HO; [| lia | unfold two64; lia | exact rdn_nul0 | exact Hi]. replace i with 0 by lia. discriminate.
  - cbn [RGz rg_base track RGz length]. rewrite u_P0X0, Z.add_0_r, rdn_nul0. reflexivity.
Qed.

#[using="uid hw Hsp ME"] Lemma rg_ro_okZ : forall lo sz, 0 <= lo -> 0 <= sz -> lo + sz <= 0xa0000 -> miss_ok lo (Z.to_nat sz) = true ->
  img_ro_ok PSEGS lo (Z.to_nat sz) = true -> rg_ok PSEGS E mem (RGz (lconst lo) sz RO TEmpty).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo sz H1 H2 H3 H4 H5. replace sz with (Z.of_nat (Z.to_nat sz)) at 1 by lia.
  apply rg_ro_ok; [lia | lia | exact H4 | exact H5].
Qed.
#[using="uid hw Hsp ME"] Lemma rg_ri_empty_okZ : forall lo sz, 0 <= lo -> 0 <= sz -> lo + sz <= 0xa0000 -> miss_ok lo (Z.to_nat sz) = true ->
  img_rw_ok PSEGS lo (Z.to_nat sz) = true -> rg_ok PSEGS E mem (RGz (lconst lo) sz RI TEmpty).
Proof. LiaFast.lf_pins (fun (uid hw Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo sz H1 H2 H3 H4 H5. replace sz with (Z.of_nat (Z.to_nat sz)) at 1 by lia.
  apply rg_ri_empty_ok; [lia | lia | exact H4 | exact H5].
Qed.

#[using="uid hw Hsp Hva Hve ME"] Lemma rgs_main1_ok : Forall (rg_ok PSEGS E mem) RG_main1.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME : LiaFast.U) => LiaFast.u0).
  unfold RG_main1, RG_hi1, RG_img. cbn [app].
  repeat (apply Forall_cons;
    [ first [ exact rg0_ok | exact rg1_ok | exact rg20_ok | exact rg6_ok | exact rg7_ok
            | (apply rg_ro_okZ; [lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity])
            | (apply rg_ri_empty_okZ; [lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]) ] | ]).
  apply Forall_nil.
Qed.

#[using="uid hw Hsp Hva Hve"] Lemma rgs_main1_disj : rgs_disj E RG_main1.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof p0_bounds as (B1 & B2 & B3).
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc, E_SP0. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc, E_SP0. apply u_sp0_plus. lia. }
  pose proof u_P0X0 as HA2.
  apply (rgs_disj_app_sep E RG_hi1 RG_img 0xa0000).
  - cbn [RG_hi1 rgs_disj].
    repeat match goal with
           | |- _ /\ _ => split
           | |- Forall _ (_ :: _) => apply Forall_cons
           | |- Forall _ [] => apply Forall_nil
           | |- True => exact I
           | |- rg_disj _ _ _ => unfold rg_disj; rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2; lia
           end.
  - apply cdisj_sound; [vm_compute; reflexivity|].
    unfold RG_img. repeat (apply Forall_cons; [eexists; split; [reflexivity | rewrite w64_mod; unfold two64; lia] |]). apply Forall_nil.
  - unfold RG_hi1. repeat (apply Forall_cons; [cbn [RGz rg_base]; rewrite ?HA0, ?HA1, ?HA2; lia|]). apply Forall_nil.
  - unfold RG_img. repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; unfold lconst, lden, lz; cbn [l_c l_t tsum]; rewrite Z.add_0_r, w64_mod;
                                                  rewrite u_small64 by (unfold two64; lia); unfold two64; lia|]).
    apply Forall_nil.
Qed.

Hypothesis Hargc : length av <> 2%nat.

#[using="uid hw Hsp Hva Hve Htid Hargc"] Lemma facts_main1 : Forall (fact_ok E) F_main1.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid Hargc : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof sp0_al as Al. pose proof p0_bounds as (B1 & B2 & B3).
  pose proof (valid_argv_len av Hva). pose proof (valid_argv_nonempty av Hva).
  pose proof (u_argcN av Hva) as UA.
  pose proof (valid_argv_str_len av 0 Hva ltac:(lia)) as SL.
  unfold F_main1. repeat apply Forall_cons; try apply Forall_nil; cbn [fact_ok]; unfold SP0, ARGC, P0, X0, T; rewrite ?lden_lvar.
  - change (E 1%positive) with sp0. lia.
  - change (E 1%positive) with sp0. exact Al.
  - change (E 2%positive) with (argcN av). lia.
  - cbn [branch_taken]. change (E 2%positive) with (argcN av).
    destruct (bv_eqb (argcN av) (lden E (lconst 2))) eqn:Heq; [|reflexivity]. exfalso.
    apply bv_eqb_eq in Heq. apply (f_equal bv_unsigned) in Heq. rewrite UA in Heq.
    replace (bv_unsigned (lden E (lconst 2))) with 2 in Heq by reflexivity. lia.
  - rewrite E_P0. lia.
  - rewrite E_X0. rewrite u_small64 by (unfold two64; lia). lia.
  - rewrite E_T. lia.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc"] Theorem handoff1 : sden PSEGS E P_main1 (mkst (fx := fx0) regs (Z_to_bv 64 0x228cc) mem (seg_rom PSEGS)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc : LiaFast.U) => LiaFast.u0).
  apply sden0_sden; [exact P_main1_wf|].
  refine (conj eq_refl (conj eq_refl (conj eq_refl (conj E_regs (conj rgs_main1_ok (conj rgs_main1_disj (conj facts_main1 _))))))).
  vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="av Hargc"] Lemma rdn_stack_to_mem : forall segs (base : word) (img : list byte) (a : Z) n,
  bv_unsigned base <= a -> a - bv_unsigned base + Z.of_nat n <= Z.of_nat (length img) -> a + Z.of_nat n <= 2^64 ->
  rdn segs (stack_to_mem base img) (Z_to_bv 64 a) n = Some (firstn n (skipn (Z.to_nat (a - bv_unsigned base)) img)).
Proof. LiaFast.lf_pins (fun (av Hargc : LiaFast.U) => LiaFast.u0).
  intros segs base img a n. revert a. induction n as [|n IH]; intros a H1 H2 H3; [reflexivity|].
  cbn [rdn]. pose proof (bv_unsigned_in_range _ base) as RB. unfold bv_modulus in RB.
  assert (Hs : stack_to_mem base img (Z_to_bv 64 a) = nth_error img (Z.to_nat (a - bv_unsigned base))).
  { unfold stack_to_mem. rewrite u_small64 by (unfold two64; lia).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hs. destruct (nth_error img (Z.to_nat (a - bv_unsigned base))) as [b|] eqn:Hb;
    [| apply nth_error_None in Hb; lia].
  rewrite zbv_add1. rewrite (IH (a + 1)) by lia.
  f_equal. replace (Z.to_nat (a + 1 - bv_unsigned base)) with (S (Z.to_nat (a - bv_unsigned base))) by lia.
  clear -Hb. revert Hb. generalize (Z.to_nat (a - bv_unsigned base)) as k. intros k Hb.
  revert k Hb. induction img as [|x img IHi]; intros [|k] Hb; cbn in *; try discriminate.
  - injection Hb as <-. destruct n; reflexivity.
  - apply IHi. exact Hb.
Qed.

Definition K0 : nat := length (nth 0 av []).

#[using="uid tid hw rdraw regs Hsp Hva Hve ME Hargc"] Lemma argv0_window : exists buf,
  rdn PSEGS mem (cat_argv_ptr sp0 av ev 0) (length buf) = Some buf /\
  firstn (S K0) buf = nth 0 av [] ++ [Z_to_bv 8 0] /\
  (bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat K0) / 8 * 8 + 8 <= bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length buf) /\
  bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length buf) <= 0x800010000000.
Proof. LiaFast.lf_pins (fun (uid tid hw rdraw regs Hsp Hva Hve ME Hargc : LiaFast.U) => LiaFast.u0).
  pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof sp0_al as Al. pose proof (valid_argv_nonempty av Hva) as Hne.
  pose proof p0_bounds as (B1 & B2 & B3).
  destruct (bsb_byte_k RPH sp0 av ev 0 uid hw rdraw ltac:(lia)) as (pre & post & Hbsb & Hpre).
  pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve L H 0 ltac:(lia)) as U.
  set (p0 := cat_argv_ptr sp0 av ev 0) in *.
  set (img := entry_stack_image RPH sp0 av ev uid hw rdraw).
  set (blk := build_stack_bytes RPH sp0 av ev uid hw rdraw) in *.
  assert (Himg : img = blk ++ entry_slack sp0 blk (ed_slack rdraw)) by reflexivity.
  assert (Hlimg : bv_unsigned sp0 + Z.of_nat (length img) = entry_page_top sp0 blk).
  { rewrite Himg, length_app, length_entry_slack. unfold entry_slack_len.
    pose proof (entry_page_top_ge sp0 blk) as G. unfold entry_block_top in *. lia. }
  assert (Hpt : entry_page_top sp0 blk mod 8 = 0).
  { unfold entry_page_top, page_round_up_Z, page_size. rewrite Z.mul_comm. rewrite <- Z.mul_mod_idemp_l by lia.
    change (4096 mod 8) with 0. reflexivity. }
  assert (Hlblk : bv_unsigned p0 + Z.of_nat K0 + 1 <= bv_unsigned sp0 + Z.of_nat (length blk)).
  { rewrite Hbsb, !length_app. rewrite U, Hpre. unfold K0. cbn [length]. lia. }
  pose proof (entry_page_top_ge sp0 blk) as G. unfold entry_block_top in G.
  pose proof (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve H) as NW.
  pose proof (bsb_bound RPH sp0 av ev uid hw rdraw Hva Hve) as BB. fold blk in BB, NW.
  assert (PT : entry_page_top sp0 blk <= entry_block_top sp0 blk + 4096).
  { unfold entry_page_top, page_round_up_Z, page_size. pose proof (Z.div_mod (entry_block_top sp0 blk + 4096 - 1) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (entry_block_top sp0 blk + 4096 - 1) 4096 ltac:(lia)). lia. }
  unfold entry_block_top in PT.
  set (n := Z.to_nat ((bv_unsigned p0 + Z.of_nat K0) / 8 * 8 + 8 - bv_unsigned p0)).
  assert (Hn : Z.of_nat n = (bv_unsigned p0 + Z.of_nat K0) / 8 * 8 + 8 - bv_unsigned p0).
  { unfold n. rewrite Z2Nat.id; [reflexivity|]. pose proof (Z.mod_pos_bound (bv_unsigned p0 + Z.of_nat K0) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned p0 + Z.of_nat K0) 8 ltac:(lia)). lia. }
  assert (Hwin : (bv_unsigned p0 + Z.of_nat K0) / 8 * 8 + 8 <= entry_page_top sp0 blk).
  { pose proof (Z.div_mod (bv_unsigned p0 + Z.of_nat K0) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned p0 + Z.of_nat K0) 8 ltac:(lia)).
    pose proof (Z.div_mod (entry_page_top sp0 blk) 8 ltac:(lia)). rewrite Hpt in *.
    assert ((bv_unsigned p0 + Z.of_nat K0) / 8 < entry_page_top sp0 blk / 8) by lia. lia. }
  exists (firstn n (skipn (Z.to_nat (bv_unsigned p0 - bv_unsigned sp0)) img)).
  assert (Hlen : length (firstn n (skipn (Z.to_nat (bv_unsigned p0 - bv_unsigned sp0)) img)) = n).
  { rewrite length_firstn, length_skipn. lia. }
  rewrite Hlen. refine (conj _ (conj _ (conj _ _))).
  - rewrite (main_entry_rdn_above sp0 av ev uid tid hw rdraw regs mem ME); [ | lia | lia].
    change (wrap_mem RPH sp0 av ev uid hw rdraw) with (wmem RPH sp0 av ev uid hw rdraw).
    rewrite (rdn_wmem_stack PSEGS RPH sp0 av ev uid hw rdraw) by lia.
    pose proof (rdn_stack_to_mem PSEGS sp0 img (bv_unsigned p0) n) as R. rewrite Z_to_bv_bv_unsigned in R. apply R; lia.
  - rewrite firstn_firstn. rewrite Nat.min_l by lia.
    replace (Z.to_nat (bv_unsigned p0 - bv_unsigned sp0)) with (length pre) by (rewrite U, Hpre; lia).
    rewrite Himg, Hbsb, <- !app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. cbn [app].
    rewrite firstn_app. unfold K0. replace (S (length (nth 0 av [])) - length (nth 0 av []))%nat with 1%nat by lia.
    rewrite firstn_all2 by lia. reflexivity.
  - lia.
  - lia.
Qed.

#[using="sp0 av ev uid tid hw rdraw regs Hsp ME Hargc"] Lemma rodata_clear_main : forall i, 0x12fa8 <= i < 0x12fc8 -> mem (Z_to_bv 64 i) = None.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME Hargc : LiaFast.U) => LiaFast.u0).
  intros i Hi. replace i with (0x12fa8 + (i - 0x12fa8)) by lia.
  apply (mem_miss 0x12fa8 32 (i - 0x12fa8)); [lia | lia | vm_compute; reflexivity | lia].
Qed.
(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Hargc"] Lemma outside_main1_hi : forall x, bv_unsigned sp0 + 24 <= bv_unsigned x < 2^48 ->
  bv_unsigned x <> bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av [])) -> outside E (s_rgs P_main1) x.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hargc : LiaFast.U) => LiaFast.u0).
  intros x Hx Hn. pose proof sp0_lo. pose proof sp0_hi.
  pose proof u_P0X0 as HA2.
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  unfold outside. cbn [s_rgs P_main1 RG_main1 RG_hi1 RG_img app].
  repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2, ?u_lconst by lia; lia|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Hargc"] Lemma outside_main1_rodata : forall x, 0x12fa8 <= bv_unsigned x < 0x12fc8 -> outside E (s_rgs P_main1) x.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hargc : LiaFast.U) => LiaFast.u0).
  intros x Hx. pose proof sp0_lo. pose proof sp0_hi.
  pose proof p0_bounds as (B1 & B2 & B3).
  pose proof u_P0X0 as HA2.
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  unfold outside. cbn [s_rgs P_main1 RG_main1 RG_hi1 RG_img app].
  repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2, ?u_lconst by lia; lia|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
#[using="uid hw rdraw Hsp Hva Hve Hargc"] Lemma argv0_top : entry_stack_fits sp0 av ev ->
  bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av [])) + 1 <= TASK_SIZE.
Proof. LiaFast.lf_pins (fun (uid hw rdraw Hsp Hva Hve Hargc : LiaFast.U) => LiaFast.u0).
  intros Hf. pose proof sp0_lo as L. pose proof sp0_hi as H. pose proof (valid_argv_nonempty av Hva) as Hne.
  destruct (bsb_byte_k RPH sp0 av ev 0 uid hw rdraw ltac:(lia)) as (pre & post & Hbsb & Hpre).
  pose proof (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve L H 0 ltac:(lia)) as U.
  pose proof (build_stack_bytes_within_span RPH sp0 av ev uid hw rdraw) as WS.
  unfold entry_stack_fits in Hf. unfold TASK_SIZE, sp_window_hi in *.
  assert (Hl : Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) >= Z.of_nat (length pre) + Z.of_nat (length (nth 0 av [])) + 1).
  { rewrite Hbsb, !length_app. cbn [length]. lia. }
  rewrite U, <- Hpre. lia.
Qed.

(* [comment removed for export] *)
Definition exit_glob (m : word -> option byte) : Prop :=
  rdn PSEGS m (Z_to_bv 64 0x97bf8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) /\
  rdn PSEGS m (Z_to_bv 64 0x628d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2283c)) /\
  rdn PSEGS m (Z_to_bv 64 0x66e18) 1%nat = Some [Z_to_bv 8 0] /\
  rdn PSEGS m (Z_to_bv 64 0x97c23) 1%nat = Some [Z_to_bv 8 0] /\
  rdn PSEGS m (Z_to_bv 64 0x98050) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn PSEGS m (Z_to_bv 64 0x98040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn PSEGS m (Z_to_bv 64 0x66db0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66cc8)) /\
  rdn PSEGS m (Z_to_bv 64 0x66cc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66bd8)).

#[using="Type"] Lemma exit_glob_pristine : exit_glob (fun _ => None).
Proof. LiaFast.lf_pins LiaFast.u0.
  unfold exit_glob. repeat split; vm_compute; try reflexivity;
    f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity.
Qed.

Definition EXG_RANGES : list (Z * nat) := [(0x97bf8, 4%nat); (0x628d0, 8%nat); (0x66e18, 1%nat); (0x97c23, 1%nat); (0x98050, 8%nat); (0x98040, 8%nat); (0x66db0, 8%nat); (0x66cc0, 8%nat)].

#[using="Type"] Lemma exg_miss : forallb (fun '(lo, n) => miss_ok lo n) EXG_RANGES = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Hargc"] Lemma exg_outside : forall lo n i, In (lo, n) EXG_RANGES -> 0 <= i < Z.of_nat n -> outside E (s_rgs P_main1) (Z_to_bv 64 (lo + i)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hargc : LiaFast.U) => LiaFast.u0).
  intros lo n i Hin Hi. pose proof sp0_lo. pose proof sp0_hi. pose proof p0_bounds as (B1 & B2 & B3).
  pose proof u_P0X0 as HA2.
  assert (HA0 : bv_unsigned (lden E (laddc SP0 (-65536))) = bv_unsigned sp0 - 65536).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  assert (HA1 : bv_unsigned (lden E (laddc SP0 8)) = bv_unsigned sp0 + 8).
  { rewrite lden_laddc. unfold SP0. rewrite lden_lvar. apply u_small64. unfold two64; lia. }
  unfold EXG_RANGES in Hin. unfold outside. cbn [s_rgs P_main1 RG_main1 RG_hi1 RG_img app].
  repeat (destruct Hin as [Hin|Hin];
    [injection Hin as <- <-; cbn in Hi; rewrite u_small64 by (unfold two64; lia);
     repeat (apply Forall_cons; [rsz_simpl; cbn [RGz rg_base rg_size]; rewrite ?HA0, ?HA1, ?HA2, ?u_lconst by lia; lia|]); apply Forall_nil |]).
  destruct Hin.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc"] Lemma exit_glob_of_MF : forall m', (forall x, outside E (s_rgs P_main1) x -> m' x = mem x) -> exit_glob m'.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc : LiaFast.U) => LiaFast.u0).
  intros m' Hmf. pose proof sp0_lo as L.
  assert (Hm : forall lo n, In (lo, n) EXG_RANGES -> rdn PSEGS m' (Z_to_bv 64 lo) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 lo) n).
  { intros lo n Hin. pose proof exg_miss as HM. rewrite forallb_forall in HM. pose proof (HM _ Hin) as Hmo. cbv beta in Hmo.
    assert (Hb : 0 <= lo /\ lo + Z.of_nat n <= 0xa0000).
    { unfold EXG_RANGES in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; lia|]). destruct Hin. }
    apply rdn_ext_rd1; [lia | unfold two64; lia |].
    intros i Hi. unfold rd1. rewrite (Hmf _ (exg_outside lo n i Hin Hi)). rewrite (mem_miss lo n i) by (lia || exact Hmo). reflexivity. }
  pose proof exit_glob_pristine as P. unfold exit_glob in *.
  rewrite (Hm 0x97bf8 4%nat), (Hm 0x628d0 8%nat), (Hm 0x66e18 1%nat), (Hm 0x97c23 1%nat), (Hm 0x98050 8%nat), (Hm 0x98040 8%nat),
    (Hm 0x66db0 8%nat), (Hm 0x66cc0 8%nat) by (unfold EXG_RANGES; cbn; tauto). exact P.
Qed.
End Handoff.
