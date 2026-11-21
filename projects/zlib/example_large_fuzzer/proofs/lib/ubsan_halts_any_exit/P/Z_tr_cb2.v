(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition cb_site3_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (dist : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t6 w wbb m',
    ms' = MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) t6) F (wz 0x1c818) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16 /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma cb_S3 : forall (L : dlay) (s : deflate_state) (LT DT sx lc dist code V l : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  code = arr_get length_code_a lc -> V = lc - arr_get base_length_a code -> l = arr_get extra_lbits_a code ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L -> 0 <= lc < 256 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site3_post L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) dist
                           ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp (wz (code * 4)) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) (wz lc)) F (wz 0x1c77c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ecode EV El EMH HBB HW MI LAY Rlc RBV RPD ROOM. unfold cbR.
  pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
  pose proof (extra_lbits_facts code Rcode) as (Rex & Rbase & _). rewrite <- El in Rex.
  pose proof (length_base_le lc Rlc) as RVlo. rewrite <- Ecode in RVlo.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  pose proof (u32ro_read m Z_BASE_LENGTH (av32 base_length_a 29) code _ (wa (Z_BASE_LENGTH + 4 * code)) (rod_base_length m MI)
                (av32_nth base_length_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDb.
  pose proof (u32ro_read m Z_EXTRA_LBITS (av32 extra_lbits_a 29) code _ (wa (Z_EXTRA_LBITS + 4 * code)) (rod_extra_lbits m MI)
                (av32_nth extra_lbits_a 29 code ltac:(lia)) ltac:(lia) eq_refl) as RDe. rewrite <- El in RDe.
  unfold Z_BASE_LENGTH, Z_EXTRA_LBITS in *.
  do 6 zs2. zs2. zs2. zs2. rewrite <- EV. zs2. zs2.
  assert (RV : 0 <= V < 256) by lia. clear Ecode EV El. zstep. br_cases K.
  -
    zs2. sb_or w1 LO BB ltac:(exact HW). zs2. zs2. zs2. reg_as (l + BV) (BV + l).
    apply evt_done. unfold cb_site3_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend|]. split; exact LO.
  -
    zs2. zs2. zs2. sb_or w1 LO BB ltac:(exact HW).
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_site3_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend|]. split; apply lo16_unsigned_wz.
Qed.

Definition cb_site4_post (X : Z -> Prop) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (vs0 vt6 : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s2 s3 s4 s5 t5 w wbb pcx m',
    ms' = MS (cbR L LT DT sx ra sp gp tp (wz vs0) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) w t5 (wz vt6)) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16 /\ bv_unsigned w mod 2^16 = BB mod 2^16 /\ X pcx.

Ltac cb_fin4 MU WM GA GD Gpend LOc LOr side EXT :=
  apply evt_done; unfold cb_site4_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV;
  rewrite ?(proj2 (Z.ltb_ge _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; do 10 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LOc|]; split; [LOr|]; side; (split; [reflexivity| EXT]).

Lemma cb_S4 : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist dcode V l : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = arr_get dfc dcode -> l = arr_get ddl dcode ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  0 <= V < 65536 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site4_post (fun pcx => (pcx = 0x1c60c /\ dcode < 4) \/ (pcx = 0x1c8c4 /\ 4 <= dcode))
                           L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (dcode * 4) (dist - 1)
                           ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz dist) w (wz BV) t6) F (wz 0x1c818) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Edc EV El EMH HBB HW MI LAY RDL Rdist RDT1 RDT2 RV Rl RBV RPD ROOM. unfold cbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & _). rewrite <- Edc in Rdc.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI dcode ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  set (didx := if dist - 1 <? 256 then dist - 1 else 256 + Z.shiftr (dist - 1) 7).
  assert (Edi : dcode = arr_get dist_code_a didx) by (rewrite Edc; unfold d_code, didx; destruct (dist - 1 <? 256); reflexivity).
  assert (Rdi : 0 <= didx < 512).
  { unfold didx. destruct (Z.ltb_spec (dist - 1) 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
    pose proof (Z.div_pos (dist - 1) 128 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (dist - 1) 128 256 ltac:(lia) ltac:(lia)). lia. }
  eapply (evt_cut psegs (fun ms' => ms' = MS (mkR ra sp gp tp (wz 65535) (wz Z_LENGTH_CODE) (wz 4) (wz didx) s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) (wz sx)
       (wz 16) (wz (-20)) (wz 257) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz Z_DIST_CODE) w (wz BV) (wz (dist - 1))) F (wz 0x1c834) fc None m (seg_rom psegs))).
  { do 3 zs2. br_cases K.
    - do 2 zs2. apply evt_done.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_lt _ _)) by lia; lia).
    - zs2. rewrite srliw7 by lia. do 3 zs2. apply evt_done.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_ge _ _)) by lia; try replace (dist + -1) with (dist - 1) by lia; lia). }
  intros ms' ->. clearbody didx.
  pose proof (u8ro_read psegs m Z_DIST_CODE (av8 dist_code_a 512) didx _ (wa (Z_DIST_CODE + didx)) (rod_dist_code m MI)
                (av8_nth dist_code_a 512 didx ltac:(lia)) ltac:(lia) eq_refl) as RDdc. rewrite <- Edi in RDdc.
  unfold Z_DIST_CODE in *.
  zs2. zsb. rewrite (bv8_small dcode) by lia.
  zs2. shl_norm. zs2.
  zs2. rewrite (zx16_small l) by lia. zs2. rewrite (zx16_small V) by lia.
  clear Edc EV El Edi.
  zs2. zs2. zs2.
  sb_or w1 LO BB (exact HW).
  zs2. zstep. br_cases K.
  -
    zs2. zs2. zstep. br_cases K4.
    + cb_fin4 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(left) ltac:(lia).
    + cb_fin4 MU WM GA GD Gpend ltac:(exact LO) ltac:(exact LO) ltac:(right) ltac:(lia).
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zstep. reg_as (l + BV + -16) (BV + l - 16). br_cases K4.
    + cb_fin4 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
    + zstep. cb_fin4 MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
Qed.

Lemma cb_S5 : forall (L : dlay) (s : deflate_state) (LT DT sx dist dcode V l : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = dist - 1 - arr_get base_dist_a dcode -> l = arr_get extra_dbits_a dcode ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv psegs m -> dlay_ok L -> 1 <= dist <= 32768 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt psegs (cb_site_post 0x1c60c L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l)
                          ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp (wz (dcode * 4)) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV) w t5 (wz (dist - 1))) F (wz 0x1c8c4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Edc EV El EMH HBB HW MI LAY Rdist RBV RPD ROOM. unfold cbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & _). rewrite <- El in Rex.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  pose proof (u32ro_read m Z_BASE_DIST (av32 base_dist_a 30) dcode _ (wa (Z_BASE_DIST + 4 * dcode)) (rod_base_dist m MI)
                (av32_nth base_dist_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDb.
  pose proof (u32ro_read m Z_EXTRA_DBITS (av32 extra_dbits_a 30) dcode _ (wa (Z_EXTRA_DBITS + 4 * dcode)) (rod_extra_dbits m MI)
                (av32_nth extra_dbits_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDe. rewrite <- El in RDe.
  unfold Z_BASE_DIST, Z_EXTRA_DBITS in *.
  do 6 zs2. zs2. zs2. zs2. rewrite <- EV. zs2. zs2.
  assert (RV : 0 <= V < 32768) by lia. clear Edc EV El. zstep. br_cases K.
  -
    zs2. sb_or w1 LO BB (exact HW). zs2. zs2. zs2. zs2. reg_as (l + BV) (BV + l).
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    zs2. zs2. zs2. sb_or w1 LO BB (exact HW).
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_site_post, cbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
