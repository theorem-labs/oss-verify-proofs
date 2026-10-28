(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitR ARep ARepKit ARepFrame RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_agetfrom F_arefill F_amaybe F_areturn F_acdrain.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Definition cdealloc_entry : Z := 0x35f58.
End CANSEC1.
Notation CDEALLOC_STACK := 688 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma initcache_loop2_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a1 a2 a3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv bsegs m -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  rng RNG (al_t L) 4096 ->
  evtF bsegs RNG (fun ms' => exists a4' a5' a6' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 a4' a5' a6' (Z_to_bv 64 15)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4' t5' t6') F (Z_to_bv 64 0x360dc) fc None m' (seg_rom bsegs)
      /\ munch (ic_W L i d) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6)
        F (Z_to_bv 64 0x36088) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT; [lia|]. band_lin.   (* [comment removed for export] *)
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t6x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells bsegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv bsegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono bsegs m mm ->
    evtF bsegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t6x)
          F (Z_to_bv 64 0x36064) fc None mm (seg_rom bsegs)))
  end.
  { intros q t6x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.                         (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.                                                (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).   (* [comment removed for export] *)
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1; lia. }
      cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.                            (* [comment removed for export] *)
    step. step. step.                                          (* [comment removed for export] *)
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 30 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.                                              (* [comment removed for export] *)
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  - (* [comment removed for export] *)
    do 7 zstep.                                                (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    destruct (mc_big i ltac:(clear -I K17 K31; lia)) as (MC & SB & Q1).
    step.                                                      (* [comment removed for export] *)
    setreg 30 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cdmain_post (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sta' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
              (al_t L + 2784, al_t L + 2792)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (acache_addr L c) [C4 (Z_to_bv 64 (k0 + 1)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr bsegs m' (acache_addr L c + 16) (upd chunks (Z.to_nat k0) (Z_to_bv 64 ((P - aregion L c) / 16)))
    /\ rw_cells bsegs m' (al_t L + 2784) [C8 sta'].

Lemma cd_main_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (sta : word),
  stk bsegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 (al_space_beg L))] ->
  rw_cells bsegs m (acache_addr L c) [C4 (Z_to_bv 64 k0); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr bsegs m (acache_addr L c + 16) chunks -> length chunks = 16%nat ->
  rw_cells bsegs m (al_t L + 2784) [C8 sta] ->
  1 <= c < K_NUM_CLASSES -> 0 <= k0 < 16 -> 0 <= mc < 2^31 -> 0 <= csz < 2^63 ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_t L) 4096 ->
  evtF bsegs RNG (cdmain_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc L c k0 mc csz P lo chunks m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1x
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 k0) a5 a6 a7
             s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35f9c) fc None m (seg_rom bsegs)).
Proof.
  intros until sta. intros ST CEIL LO MI FR ISB CR CH LCH STA HC K0 MC CSZ P0 P1 SP1 SP2 T0 T1 TAL TI RIMG RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
                          (al_t L + 2784, al_t L + 2792)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (acache_addr L c + 4 * k0)) ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); rewrite Z.mod_small by (clear -K0; lia); f_equal;
      change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by (clear; lia); clear; lia).
  setreg 13 (Z_to_bv 64 ((P - aregion L c) / 16))
    ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); change (2^4) with 16; change (2^32) with 4294967296; f_equal; f_equal;
          rewrite RBE; rewrite (Z.mod_small (c * 4294967296)) by (clear -HC; lia);
          rewrite (Z.mod_small (P - c * 4294967296)) by (clear -HC P0 P1 SP1 SP2 RBE; lia);
          rewrite Z.mod_small by (clear -HC P0 P1 SP1 SP2 RBE; lia); clear; lia).
  box CH. box STA. box ISB.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  step.                                                        (* [comment removed for export] *)
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STA MUc WMc ltac:(rewrite CAE; clear -HC; lia).
  carry ISB MUc WMc ltac:(rewrite CAE; clear -HC TI; lia).   (* [comment removed for export] *)
  clear MUc WMc.
  pose proof (u32arr_store_ok bsegs _ (acache_addr L c + 16) _ k0 (wa (acache_addr L c + 16 + 4 * k0)) CH ltac:(rewrite LCH; clear -K0; lia) eq_refl) as SOK.
  box CR. box STA. box ISB. box FR.
  snapshot [(acache_addr L c + 16, acache_addr L c + 80)]%Z MUa WMa.
  step.                                                        (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a (le4 ?v)) _) =>
    pose proof (u32arr_write bsegs mm (acache_addr L c + 16) _ k0 v CH ltac:(rewrite LCH; clear -K0; lia)) as CH2
  end.
  clear CH. store_done. try clear SOK.
  carry CR MUa WMa ltac:(clear; lia). carry STA MUa WMa ltac:(rewrite CAE; clear -HC; lia). carry ISB MUa WMa ltac:(rewrite CAE; clear -HC TI; lia).
  carry FR MUa WMa ltac:(rewrite CAE; clear -HC T1 SPR CEIL LO; lia). clear MUa WMa.
  zstep.                                                       (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2784)) = true) by (pose proof atop_range as AR; apply amo_alignedD_intro; [clear -TI T1 AR; lia| clear -TAL; Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
  box CH2. box CR. box ISB.
  snapshot [(al_t L + 2784, al_t L + 2792)]%Z MUb WMb.
  amo_stepA AMO.                                               (* [comment removed for export] *)
  carry CH2 MUb WMb ltac:(rewrite ?upd_length, LCH, CAE; clear -HC; lia). carry CR MUb WMb ltac:(rewrite CAE; clear -HC; lia). carry ISB MUb WMb ltac:(clear -TI; lia).
  clear MUb WMb.
  do 8 step.                                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold cdmain_post. finish.
  all: try eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma a_cinit_init_cache : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite a_cinit_init_cache. reflexivity. Qed.
Lemma put_cls_put_cls : forall c x y st, put_cls c x (put_cls c y st) = put_cls c x st.
Proof. intros c x y st. unfold put_cls, set_cls. cbn. f_equal. rewrite insert_insert. destruct (decide (c = c)) as [|NE]; [reflexivity| exfalso; apply NE; reflexivity]. Qed.
Lemma get_cls_put_cls_same : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. apply get_cls_put_cls_eq. Qed.

(* [comment removed for export] *)
Definition cd_W (L : alayout) (sp : Z) (c nf mfa mfa' : Z) : list (Z * Z) :=
  let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  ([(sp - 688, sp)] ++ ic_W L 1 31 ++
   [(CA, CA + 4); (CA + 16, CA + 80); (al_t L + 2784, al_t L + 2792); (al_t L + 2800, al_t L + 3168);
    (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
    (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)])%Z.

(* [comment removed for export] *)
Definition cdealloc_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c P lo : Z) (chunks : list word) (m : amem)
    (stX : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let mc := max_cached c in let half := mc / 2 in let cnt := c_count r in
  fp_le RNG RNG' /\
  exists (drained : bool) mfa' sj' (sta' : word),
  let nf' := if drained then nf + half else nf in
  let cnt' := if drained then cnt - half + 1 else cnt + 1 in
     (* [comment removed for export] *)
     drained = (a_cinit st && (cnt =? mc))%bool
  /\ get_cls stX c = mkAClass (c_mapped_user r) (c_allocated_user r) nf' mfa' cnt'
  /\ stX = put_cls c (get_cls stX c) (init_cache st)
  /\ (   mfa' = mfa
      \/ (drained = true /\ mfa < 4 * (nf + half) /\ mfa' = rup (4 * (nf + half)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf' <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
     (* [comment removed for export] *)
  /\ munch (cd_W L (bv_unsigned sp) c nf mfa mfa') m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (c_count (get_cls st j)) (max_cached j) (size_of_class j))
  /\ arec_hdr L m' c cnt' (max_cached c) (size_of_class c)
  /\ u32arr bsegs m' (CA + 16) (upd chunks (Z.to_nat (cnt' - 1)) (Z_to_bv 64 ((P - aregion L c) / 16)))
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf'); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2784) [C8 sta']
  /\ (drained = true -> u32arr bsegs m' (FA + 4 * nf) (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)))
  /\ junk_at m' (FA + 4 * nf') (mfa' - 4 * nf')
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma cdealloc_spec : forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr bsegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells bsegs m (al_t L + 2784) [C8 sta] ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until sta. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC RECS CH LCH CH31 STA MTX REG J72 STATS LSJ FJ AZF SBE HC CNTS NF MFA MFAM NFN P0 P1
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(pose proof atop_range as AR; clear -T1 AR; lia)) as (kT0 & T0k).   (* [comment removed for export] *)
  pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdealloc_entry in *.
  change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  word_range sp SPR.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCEV].
  pose proof (CNTS c ltac:(clear -HC; lia)) as CNTc. fold nf in CNTc.
  pose proof (RECS c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  box TCX. box SCX. box TSP.
  pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  box MTX. box REG. box STA. box CH. box STATS. clear CR.
  do 7 step.                                                   (* [comment removed for export] *)
  carry STATS MUN WM ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
  carry MTX MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry REG MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STA MUN WM ltac:(clear -SPR CEIL LO T0 T1; lia).
  carry CH MUN WM ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RECS0 : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
    [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MUN | exact WM |];
      cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -Hj SPR CEIL LO T0 T1; lia |]
  end.
  clear RECS.
  eapply junk_frame in J72; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia].
  eapply junk_frame in FJ; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite FAE; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF0 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC SPR CEIL LO MFA NF; Z.div_mod_to_equations; lia |];
    assert (MC0 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MUN | exact WM |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC SPR CEIL LO; lia |]; apply Forall_nil |]
  end.
  clear AZF MC.
  pose proof (RECS0 c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (clear -HC; lia); clear -KZ HC; lia|].   (* [comment removed for export] *)
  step. step. if_cases K32; zify_cond K32; [exfalso; rewrite ?unsigned_lit in K32 by (clear -HC; lia); clear -K32 HC; lia|].   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (acache_addr L c)) ltac:(rewrite CAE; f_equal; clear; lia).
  step.                                                        (* [comment removed for export] *)
  unfold max_count in *.
  destruct (a_cinit st) eqn:CI.
  - (* [comment removed for export] *)
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step. if_cases KM; zify_cond KM; [exfalso; rewrite ?unsigned_lit in KM by (clear -MCR; lia); clear -KM MCR; lia|].   (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit (c_count (get_cls st c))) by (clear -CNTc MCR; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -CNTc MCR; lia).   (* [comment removed for export] *)
    + (* [comment removed for export] *)
      do 7 step.                                               (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      apply evtF_done.
      unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with true by (symmetry; apply Z.eqb_eq; exact KD).
      name_sp sp (-48).
      eapply cdrain_spec with (lo := lo) (L := L) (sj := sj) (chunks := chunks) (cnt := c_count (get_cls st c)) (mc := max_cached c) (csz := size_of_class c);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC0
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZF0
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              clear KONT; fold nf mfa; first [assumption | clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNTc KD MCR; lia]).
      (* [comment removed for export] *)
      intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DR.
      unfold cdrain_ret in DR. cbv zeta in DR. destruct DR as (md & MU01 & WM01 & RR & CR2 & CH2 & ST2).
      pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
      destruct RR0 as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & GC2 & ST2E & MU2 & WM2 & MI2 & _ & MTX2 & REG2 & J722 & STATS2 & LSJ2 & SRC2 & JR2 & AZF2 & MC2).
      rewrite Hsp in *. unname_sp.
      rewrite ?unsigned_lit in MU2 by (clear -SPR CEIL LO; lia).
      rewrite ?unsigned_lit in ST2 by (clear -SPR CEIL LO; lia).
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
      assert (SHF : shad (afreearr L c + mfa) + shlen (new - mfa) <= 0x10007fff8000).
      { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE MCR. Z.div_mod_to_equations. lia. }
      assert (SHB2 : 2148256256 <= shad (afreearr L c + mfa)) by (rewrite shad_div, FAE; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      xport FR MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T1 HC; lia).
      xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      xport STA MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      xport STA MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      pose proof MC2 as MC2'. destruct MC2' as (_ & _ & _ & _ & _ & _ & _ & ISB2 & _).
      replace (ret_pc (Z_to_bv 64 221448)) with (Z_to_bv 64 221448 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      iprefix.
      step. step. step. step.                                  (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      rewrite (sx32_lit (c_count (get_cls st c) - max_cached c / 2)) by (clear -CNTc MCR KD; lia).
      step.                                                    (* [comment removed for export] *)
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 837304 _ => exact ISB2
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH2
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. cbv beta. eapply KONT.
      (* [comment removed for export] *)
      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa.
      split; [exact FPLE|].
      exists true, new, sj', sta'. cbn [andb].
      rewrite CI. cbn [andb].
      split; [symmetry; apply Z.eqb_eq; exact KD|].
      assert (GCX : get_cls (put_cls c (cls_set_count (c_count (get_cls st2 c) - max_cached c / 2 + 1)
                        (cls_set_num_freed (c_num_freed (get_cls st2 c) + max_cached c / 2) (get_cls st2 c))) st2) c
                    = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) (nf + max_cached c / 2) new (c_count (get_cls st c) - max_cached c / 2 + 1)).
      { rewrite get_cls_put_cls_eq, GC2. reflexivity. }
      split; [exact GCX|].
      split. { rewrite GCX. unfold init_cache. rewrite CI. rewrite GC2. cbn [cls_set_count cls_set_num_freed c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count].
               destruct ST2E as [E|E]; rewrite E; [reflexivity|]. rewrite GC2, put_cls_put_cls. reflexivity. }
      split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
               split; [reflexivity|]. split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
               eapply fill_frame; [exact FILL | exact MU3 | exact WM3 |]. intros _. cbn [disjoint_from].
               clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF CAE. lia. }
      split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app].
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU01]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU2]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia). }
      split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2| exact WM3]]]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr.
               eapply cells_frame; [| exact MU3 | exact WM3 |].
               { eapply cells_frame; [| exact MU2 | exact WM2 |].
                 { eapply cells_frame; [exact (RECS0 j Hj) | exact MU01 | exact WM01 |].
                   cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
                 cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. ub TSP; clear -Hj NE SPR CEIL LO T0 T0k SHB2 T1 HC SP1 SP2 RIE FAE NF MFA NEWB SHF Y; lia. }
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) - max_cached c / 2 + 1 - 1) with (c_count (get_cls st c) - max_cached c / 2) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J722 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS2 | exact MU3 | exact WM3 | rewrite LSJ2; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ2|]. split; [exact STA3|].
      split. { intros _. eapply u32arr_frame; [exact SRC2 | exact MU3 | exact WM3 |]. rewrite length_firstn, length_skipn, LCH. cbn [disjoint_from]. rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR CNTc NFN; lia. }
      split; [eapply junk_frame; [exact JR2 | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR NEWB; lia]|].
      assert (SHF3 : 2148256256 <= shad (afreearr L c + new) /\ shad (afreearr L c + new) + shlen (536870912 - new) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF NEWB MCR AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
    + (* [comment removed for export] *)
      pose proof MC0 as MC0'. destruct MC0' as (_ & _ & _ & _ & _ & _ & _ & ISB0 & _).
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 837304 _ => exact ISB0
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with false by (symmetry; apply Z.eqb_neq; exact KD).
      eapply KONT.
      (* [comment removed for export] *)
      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI. cbn [andb].
      split; [apply fp_le_refl|].
      exists false, mfa, sj, sta'.
      split; [symmetry; apply Z.eqb_neq; exact KD|].
      split; [rewrite get_cls_put_cls_eq; reflexivity|].
      split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
      split; [left; reflexivity|].
      split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app].
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
      split; [eapply wmono_trans; [exact WM| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS0 j Hj) | exact MU3 | exact WM3 |].
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) + 1 - 1) with (c_count (get_cls st c)) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ|]. split; [exact STA3|].
      split; [intros; discriminate|].
      split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
      assert (SHF3 : 2148256256 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      split; [eapply azero_frame; [exact AZF0 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC0 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
  - (* [comment removed for export] *)
    replace (if false then max_cached c else 0) with 0 by reflexivity. rewrite (sx32_lit 0) by (clear; lia).
    assert (CNT0 : c_count (get_cls st c) = 0) by (clear -CNTc; lia).
    step. if_cases KM; zify_cond KM; [| exfalso; rewrite ?unsigned_lit in KM by (clear; lia); clear -KM; lia].   (* [comment removed for export] *)
    do 9 step.                                                 (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * 1)) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (1 - 16)) ltac:(f_equal; clear; lia).
    box FR. box STA. box CH. box MTX. box REG.
    eapply evtF_cut.
    { eapply (initcache_loop2_spec RNG 31 1 L (fun j => c_count (get_cls st j))); try reflexivity.
      - clear; lia.
      - intros j Hj. pose proof (RECS0 j Hj) as Rj. cbn in Rj. exact Rj.
      - assumption.
      - exact T0.
      - atop_facts; exact T1.
      - exact RT. }
    cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & RECS3).
    carry FR MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia]).
    carry STA MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    carry CH MU2 WM2 ltac:(rewrite LCH; apply ic_W_disjoint_chunks).
    carry MTX MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    carry REG MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    pose proof (stk_transport_disjoint bsegs _ _ m2 _ _ ST MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia])) as ST2.
    eapply junk_frame in J72; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]].
    eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite FAE; unfold acache_addr; clear -SP1 SP2 HC Y NF MFA; lia| clear; cbn; lia| clear; lia]].
    xport STATS MU2 WM2 ltac:(rewrite LSJ; apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    assert (AZF2 : azero m2 (shad (afreearr L c + mfa)) (shlen (536870912 - mfa))).
    { eapply azero_frame; [exact AZF0 | exact MU2 | exact WM2 |]. intros _. assert (SHF3 : 2148256256 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      apply ic_W_disjoint_gen; [unfold acache_addr; clear -SHF3 T0k; lia| clear; cbn; lia| clear; lia]. }   (* [comment removed for export] *)
    assert (MC2 : m3_cells L m2).
    { eapply m3_cells_frame; [exact MC0 | exact MU2 | exact WM2 |]. unfold AIMG_HI, AIMG_LO. ub TCX. cbn [ic_W]. unfold acache_addr.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC T0 T1 Y; lia |]). apply Forall_nil. }
    clear ST MI AZF0 MC0.
    pose proof (RECS3 c ltac:(clear -HC; lia)) as CR2. unfold arec_hdr in CR2. rewrite CNT0 in CR2.
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step.                                                      (* [comment removed for export] *)
    rewrite (sx32_lit 0) by (clear; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -MCR; lia); [| exfalso; clear -KD MCR; lia].   (* [comment removed for export] *)
    pose proof MC2 as MC2'. destruct MC2' as (_ & _ & _ & _ & _ & _ & _ & ISB2 & _).
    pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
    eapply evtF_cut.
    { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks) (k0 := 0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ 837304 _ => exact ISB2
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => exact LCH
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (al_t _) _ => exact RT
       | |- iclr _ _ => exact TIC                              (* [comment removed for export] *)
       end;
      unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
      first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
    cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
    apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. cbn [a_cinit set_cinit].
    change (get_cls (set_cinit true st) c) with (get_cls st c). fold nf. rewrite CNT0.
    replace (0 =? max_cached c) with false by (symmetry; apply Z.eqb_neq; clear -MCR; lia).
    eapply KONT.
    (* [comment removed for export] *)
    unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI, CNT0. cbn [andb].
    split; [apply fp_le_refl|].
    exists false, mfa, sj, sta'.
    split; [reflexivity|].
    split; [rewrite get_cls_put_cls_eq; reflexivity|].
    split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
    split; [left; reflexivity|].
    split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    split. { unfold cd_W. cbv zeta. cbn [ic_W app].
             eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]; cbn [ic_W]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
    split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM2| exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS3 j Hj) | exact MU3 | exact WM3 |].
             cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
    split; [exact CR3|].
    split; [eapply u32arr_addr_eq; [exact CH3| reflexivity]|].
    split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
    split; [exact LSJ|]. split; [exact STA3|].
    split; [intros; discriminate|].
    split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
    assert (SHF3 : 2148256256 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
    eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
Qed.
End CANSEC2.
