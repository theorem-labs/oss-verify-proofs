(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition stR (L : dlay) (T mc1 n nextlen : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) :=
  mkR ra sp gp tp (wz (dl_As L + 2748)) (wz 16) (wz 4) s0 s1 (wz (dl_As L)) (wz T) (wz mc1) (wz (dl_As L + 2047)) (wz nextlen) (wz n) (wz (dl_As L + 5936)) (wz 65535)
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 9) (wz 14) (wz 10) (wz 15).

(* [comment removed for export] *)
Definition st_rep_post (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen k : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s3 s5 s6 s7 s8 wbb pcx m',
    ms' = MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz (k - 1)) s3 (wz BV) s5 s6 s7 s8 s9 s10 s11) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1cb2c /\ k - 1 <> 0) \/ (pcx = 0x1cb5c /\ k - 1 = 0)).

Lemma st_rep_iter : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen k V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc curlen -> l = arr_get bdl curlen ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= curlen < 39 ->
  0 <= V < 65536 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) -> 1 <= k < 2^31 ->
  evt psegs (st_rep_post L s T mc1 n nextlen curlen k (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) ra sp gp tp s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz k) s3 (wz BV) s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cb2c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB Rcl RV Rl RBV RPD ROOM Rk. unfold stR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI curlen Rcl) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  replace (dl_As L + 2748 + 4 * curlen) with (dl_As L + 2748 + curlen * 4) in RDc, RDl by lia.
  clear EV El.
  zs2. rewrite (zx16_small l) by lia. zs2. rewrite (zx16_small V) by lia.
  zs2. zs2. zs2. zs2.
  sb_or w LO BB (rewrite lo16_sx16; exact HBB).
  zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (l + BV + -16) (BV + l - 16). reg_as (k + -1) (k - 1).
    zstep. br_cases K2.
    + apply evt_done. unfold st_rep_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [apply lo16_unsigned_wz|]. right. split; [reflexivity| lia].
    + apply evt_done. unfold st_rep_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [apply lo16_unsigned_wz|]. left. split; [reflexivity| lia].
  - (* [comment removed for export] *)
    zs2. zs2. zs2. reg_as (k + -1) (k - 1).
    zstep. br_cases K2.
    + apply evt_done. unfold st_rep_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [exact LO|]. left. split; [reflexivity| lia].
    + apply evt_done. unfold st_rep_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [close_EM GA GD Gpend|]. split; [exact LO|]. right. split; [reflexivity| lia].
Qed.
