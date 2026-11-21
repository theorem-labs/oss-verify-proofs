(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition ust_siteB_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen : Z) (PB : arr) (PD BB BV : Z)
    (x1 x24 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x18 x19 x26 x27 wbb m',
    ms' = MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) x24 (wz BV) x26 x27 sp gp tp) F (wz 0x1ec98) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma st_siteB : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x24 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc curlen -> l = arr_get bdl curlen ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= curlen < 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ust_siteB_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) x1 x24 sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) x24 x25 x26 x27 sp gp tp) F (wz 0x1e9ec) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB Rcl RV Rl RBV RPD ROOM. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI curlen Rcl) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  replace (dl_As L + 2748 + 4 * curlen) with (dl_As L + 2748 + curlen * 4) in RDc, RDl by lia.
  clear EV El.
  ustep ST_TRAP. ustep ST_TRAP. zs2. shl_norm. zs2. ustep ST_TRAP.
  zs. rewrite (zx16_small l) by lia. zs2. zs2.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    ustep ST_TRAP. ustep ST_TRAP. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep ST_TRAP.
    zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zstep.
    apply evt_done. unfold ust_siteB_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| exact LO].
  - (* [comment removed for export] *)
    ustep ST_TRAP. ustep ST_TRAP. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep ST_TRAP.
    zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1ea64 ST_TRAP. at_pc 0x1ea64.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1ea98 ST_TRAP. at_pc 0x1ea98.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1eab4 ST_TRAP. at_pc 0x1eab4.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep.
    zstep. br_true.
    reg_as (l + BV + -16) (BV + l - 16). zstep.
    apply evt_done. unfold ust_siteB_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
