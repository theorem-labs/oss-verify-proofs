(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st1 Z_tr_st4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition st_tail_post (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s1 s4 s5 s6 s7 wbb pcx m',
    ms' = MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) s1 (wz 0) (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1cb64 /\ nextlen <> 0) \/ (pcx = 0x1cf38 /\ nextlen = 0)).

(* [comment removed for export] *)
Lemma st_x36_keep : forall (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen V V' : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s1 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  V' mod 2^16 = V mod 2^16 -> 0 <= BV <= 14 -> 0 <= PD -> 0 <= nextlen < 65536 ->
  evt psegs (st_tail_post L s T mc1 n nextlen curlen (sbF_PB PB PD BB BV V 2) (sbF_PD PD BV 2) (sbF_BB BB BV V 2) (sbF_BV BV 2) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) s1 w (wz BV) (wz (bv_swrap 32 (Z.shiftl V' (BV mod 32)))) s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cdb4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY EQV RBV RPD Rnl. unfold stR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV V V' EQV) in LO.
  zs2. zs2. zs2. zs2. zstep. br_cases K.
  - apply evt_done. unfold st_tail_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend|]. split; [exact LO|].
    left. split; [reflexivity| lia].
  - zstep.
    apply evt_done. unfold st_tail_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend|]. split; [exact LO|].
    right. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma st_x36_flush : forall (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen V V' : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra sp gp tp s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  V' mod 2^16 = V mod 2^16 -> 0 <= V' < 2^32 -> 15 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= nextlen < 65536 ->
  evt psegs (st_tail_post L s T mc1 n nextlen curlen (sbF_PB PB PD BB BV V 2) (sbF_PD PD BV 2) (sbF_BB BB BV V 2) (sbF_BV BV 2) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz V') w s3 (wz (bv_swrap 32 (Z.shiftl V' (BV mod 32)))) s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cde8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY EQV RV' RBV RPD ROOM Rnl. unfold stR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV V V' EQV) in LO.
  sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
  sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
  zs2. zs2. zs2. zs2. rewrite srlw_val by lia. rewrite (wrap16_eqm16 V V' EQV).
  zs2. zs2. zs2. zs2. reg_as (BV + -14) (BV + 2 - 16).
  zstep. br_cases K.
  - apply evt_done. unfold st_tail_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend|]. split; [apply lo16_unsigned_wz|].
    left. split; [reflexivity| lia].
  - zstep.
    apply evt_done. unfold st_tail_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend|]. split; [apply lo16_unsigned_wz|].
    right. split; [reflexivity| lia].
Qed.
