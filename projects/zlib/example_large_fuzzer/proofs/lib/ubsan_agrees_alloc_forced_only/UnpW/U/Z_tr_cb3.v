(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cb_S4_post (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV BV0 : Z) (dist dcode : Z)
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s5 s7 s8 s9 s10 w m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp (wz (dcode * 4)) s1 (wz (dist - 1)) (wz BV) (wz dcode) s5 w s7 s8 s9 s10 s11) F (wz 0x1df08) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

(* [comment removed for export] *)
Lemma cb_S4 : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist dcode V l : Z) (PB : arr) (PD BB BV : Z) (w : word)
    (ra sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = arr_get dfc dcode -> l = arr_get ddl dcode ->
  EM m L s PB PD w (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 -> DT mod 2 = 0 ->
  0 <= V < 32768 -> 0 <= l <= 16 ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (cb_S4_post L s LT DT sx (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) BV dist dcode
                ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) w s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1ddc0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Edc EV El EMH HW MI LAY RDL Rdist RDT1 RDT2 ADT RV Rl RBV RPD ROOM. unfold ucbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & _). rewrite <- Edc in Rdc.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDL m (munch_refl _ _) (wmono_refl _ _) MI dcode ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  set (didx := if dist - 1 <? 256 then dist - 1 else Z.shiftr (dist - 1) 7 + 256).
  assert (Edi : dcode = arr_get dist_code_a didx).
  { rewrite Edc; unfold d_code, didx; destruct (dist - 1 <? 256); [reflexivity|]. f_equal. lia. }
  assert (Rdi : 0 <= didx < 512).
  { unfold didx. destruct (Z.ltb_spec (dist - 1) 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
    pose proof (Z.div_pos (dist - 1) 128 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (dist - 1) 128 256 ltac:(lia) ltac:(lia)). lia. }
  assert (RSH7 : 0 <= Z.shiftr (dist + -1) 7 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  (* [comment removed for export] *)
  zs2. zs2. zs2.
  eapply (evt_cut usegs (fun ms' => exists s5', ms' = MS (ucbR L LT DT sx ra sp gp tp (wz didx) w (wz (dist - 1)) (wz BV) (wz Z_DIST_CODE) s5' s6 s7 s8 s9 s10 s11)
                                                  F (wz 0x1ddf4) fc None m (seg_rom usegs))).
  { unfold ucbR, Z_DIST_CODE. zstep. br_cases K.
    - (* [comment removed for export] *) ustep CB_TRAP. zs2. rewrite srliw7 by lia. zs2. zs2. ustep CB_TRAP. apply evt_done. eexists.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_ge _ _)) by lia; try replace (dist + -1) with (dist - 1) by lia; lia).
    - (* [comment removed for export] *) zs2. zs2. zstep. br_true. apply evt_done. eexists.
      state_eq ltac:(unfold didx; rewrite ?(proj2 (Z.ltb_lt _ _)) by lia; lia). }
  intros ms' (s5' & ->). clearbody didx. unfold ucbR.
  pose proof (u8ro_read usegs m Z_DIST_CODE (av8 dist_code_a 512) didx _ (wa (Z_DIST_CODE + didx)) (rod_dist_code m MI)
                (av8_nth dist_code_a 512 didx ltac:(lia)) ltac:(lia) eq_refl) as RDdc. rewrite <- Edi in RDdc.
  unfold Z_DIST_CODE in *.
  zs2. zsb. rewrite (bv8_small dcode) by lia.
  zs2. shl_norm.
  uwalk 0x1de24 CB_TRAP. at_pc 0x1de24.
  zs. rewrite (zx16_small V) by lia. zs. rewrite (zx16_small l) by lia.
  clear Edc EV El Edi.
  do 5 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    ustep CB_TRAP. zs2. zs2.
    sb_or w1 LO BB ltac:(exact HW).
    zstep. zs2.
    reg_as (BV + l) (BV + l).
    apply evt_done. unfold cb_S4_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  - (* [comment removed for export] *)
    ustep CB_TRAP. zs. zs. zs. zs.
    sb_or w1 LO BB ltac:(exact HW).
    zs. zs. zstep. zs.
    uwalk 0x1de88 CB_TRAP. at_pc 0x1de88.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1debc CB_TRAP. at_pc 0x1debc.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1ded8 CB_TRAP. at_pc 0x1ded8.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16).
    apply evt_done. unfold cb_S4_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

(* [comment removed for export] *)
Lemma cb_S5 : forall (L : dlay) (s : deflate_state) (LT DT sx dist dcode V l : Z) (X : bool) (PB : arr) (PD BB BV BV0 : Z) (w : word)
    (ra sp gp tp s1 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dcode = d_code (dist - 1) -> V = dist - 1 - arr_get base_dist_a dcode -> l = arr_get extra_dbits_a dcode -> X = (4 <=? dcode) ->
  EM m L s PB PD w (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L -> 1 <= dist <= 32768 -> 0 <= BV0 < 2^32 ->
  0 <= BV <= 16 -> 0 <= PD -> (X = true -> 16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ucb_post 0x1d9f4 L s LT DT sx (if X then sbF_PB PB PD BB BV V l else PB) (if X then sbF_PD PD BV l else PD)
                (if X then sbF_BB BB BV V l else BB) (if X then sbF_BV BV l else BV) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz (dcode * 4)) s1 (wz (dist - 1)) (wz BV) (wz dcode) s5 w s7 s8 s9 s10 s11) F (wz 0x1df08) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Edc EV El EX EMH HW MI LAY Rdist RBV0 RBV RPD ROOM. unfold ucbR.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & EXD). rewrite <- El in Rex.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zstep.
  lazymatch goal with H : mem_inv usegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u32ro_read mc Z_BASE_DIST (av32 base_dist_a 30) dcode _ (wa (Z_BASE_DIST + 4 * dcode)) (rod_base_dist mc H)
                (av32_nth base_dist_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDb;
    pose proof (u32ro_read mc Z_EXTRA_DBITS (av32 extra_dbits_a 30) dcode _ (wa (Z_EXTRA_DBITS + 4 * dcode)) (rod_extra_dbits mc H)
                (av32_nth extra_dbits_a 30 dcode ltac:(lia)) ltac:(lia) eq_refl) as RDe end.
  rewrite <- El in RDe. unfold Z_BASE_DIST, Z_EXTRA_DBITS in *.
  ustep CB_TRAP. zstep. br_cases K.
  - (* [comment removed for export] *)
    replace X with false by (rewrite EX; symmetry; apply Z.leb_gt; lia).
    apply evt_done. unfold ucb_post, ucbR. do 13 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact HW].
  - (* [comment removed for export] *)
    replace X with true by (rewrite EX; symmetry; apply Z.leb_le; lia).
    assert (ROOM' : 16 - l < BV -> PD + 2 <= 65536) by (intros; apply ROOM; [rewrite EX; apply Z.leb_le; lia| assumption]).
    uwalk 0x1df34 CB_TRAP. at_pc 0x1df34.
    zs2. zs2. zs2. ustep CB_TRAP. zs2. zs2.
    zs2. zs2. zs2. zs2.
    rewrite <- EV. assert (RV : 0 <= V < 32768) by lia.
    zs2. rewrite (land16_small V) by lia.
    zs2. zs2. shl_g0. zs2. zs2. shl_g1.
    clear Edc EV El.
    zstep. br_cases K2.
    + (* [comment removed for export] *)
      ustep CB_TRAP. zs2. zs2. zs2.
      sb_or w1 LO BB ltac:(exact HW).
      zs2. zstep.
      zstep. br_true. zstep.
      reg_as (BV + l) (BV + l).
      apply evt_done. unfold ucb_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 13 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| exact LO].
    + (* [comment removed for export] *)
      ustep CB_TRAP. zs. zs. zs. zs.
      sb_or w1 LO BB ltac:(exact HW).
      zs. zs. zstep. zs.
      uwalk 0x1dfb0 CB_TRAP. at_pc 0x1dfb0.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
      zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
      uwalk 0x1dfe4 CB_TRAP. at_pc 0x1dfe4.
      pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
      uwalk 0x1e000 CB_TRAP. at_pc 0x1e000.
      zs2. rewrite srlw_val16 by lia.
      pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
      zs2. zstep. ustep CB_TRAP. zs2. zs2. rewrite swrap32_add_mod64, ?wz_add_mod64. strip32.
      zstep. br_true. zstep.
      reg_as (BV + (l + -16)) (BV + l - 16).
      apply evt_done. unfold ucb_post, ucbR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 13 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
