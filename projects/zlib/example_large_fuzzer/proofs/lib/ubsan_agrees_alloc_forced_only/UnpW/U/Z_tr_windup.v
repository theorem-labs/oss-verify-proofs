(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_BI_WINDUP : Z := 0x1bfd0.
Definition wuF_PB (PB : arr) (PD BB BV : Z) : arr :=
  if 8 <? BV then arr_set (arr_set PB PD (wrap8 (Z.land BB 255))) (PD + 1) (wrap8 (Z.shiftr (wrap16 BB) 8))
  else if 0 <? BV then arr_set PB PD (wrap8 BB) else PB.
Definition wuF_PD (PD BV : Z) : Z := if 8 <? BV then PD + 1 + 1 else if 0 <? BV then PD + 1 else PD.
Lemma bi_windup_wuF : forall s PB PD BB BV, bi_windup (upd4 s PB PD BB BV) = upd4 s (wuF_PB PB PD BB BV) (wuF_PD PD BV) 0 0.
Proof.
  intros. unfold wuF_PB, wuF_PD. destruct (Z.ltb_spec 8 BV) as [C|C].
  - rewrite bi_windup_eq2 by (rewrite upd4_bi_valid; exact C). rewrite !upd4_pending_buf, !upd4_pending, !upd4_bi_buf. apply upd4_upd4.
  - destruct (Z.ltb_spec 0 BV) as [C0|C0].
    + rewrite bi_windup_eq1 by (rewrite upd4_bi_valid; lia). rewrite !upd4_pending_buf, !upd4_pending, !upd4_bi_buf. apply upd4_upd4.
    + rewrite bi_windup_eq0 by (rewrite upd4_bi_valid; lia). rewrite !upd4_pending_buf, !upd4_pending. apply upd4_upd4.
Qed.
Definition bi_windup_post (L : dlay) (s : deflate_state) (PB : arr) (PD : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD (wz 0) (wz 0).
Lemma bi_windup_spec : forall (L : dlay) (s : deflate_state) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> mem_inv usegs m -> dlay_ok L ->
  bv_unsigned wbb mod 2^16 = BB mod 2^16 ->
  0 <= BV <= 16 -> 0 <= PD -> wuF_PD PD BV <= 65536 ->
  a0 = wz (dl_As L) ->
  evt usegs (bi_windup_post L s (wuF_PB PB PD BB BV) (wuF_PD PD BV)
                ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_BI_WINDUP) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH MI LAY LO RBV RPD ROOM ->. unfold Z_BI_WINDUP.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. unfold wuF_PD in ROOM.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  zs2. al8 (dl_As L). gF.
  do 3 zstep. zs2. zstep.
  zstep. br_cases K.
  -
    zstep. br_cases K0.
    +
      zs2. zs2. gF. zs2. zs2. zs2. zs2. zs2. zstep.
      apply evt_done. unfold bi_windup_post, wuF_PB, wuF_PD. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
    +
      rewrite (proj2 (Z.ltb_ge 8 BV)), (proj2 (Z.ltb_lt 0 BV)) in ROOM by lia.
      do 6 zstep.
          gF. zs2. zs2. zs2. gX. gF.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 BB) ltac:(apply lo8_wrap8; rewrite lo16_zx16; exact LO).
      zs2. zs2. gF. zs2. zs2. zs2. zs2. zs2. zstep.
      apply evt_done. unfold bi_windup_post, wuF_PB, wuF_PD. rewrite (proj2 (Z.ltb_ge 8 BV)), (proj2 (Z.ltb_lt 0 BV)) by lia. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
  -
    rewrite (proj2 (Z.ltb_lt 8 BV)) in ROOM by lia.
    do 6 zstep.
      gF. zs2. zs2. zs2. gX. gF.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land BB 255)) ltac:(apply lo8_wrap8_land; rewrite lo16_zx16; exact LO).
    zstep. zstep. rd_c2 GD 55%nat 1. zsb. zs2. zs2. zstep.
      gF. zs2. zs2. zs2. rewrite xor_guard by lia. gT.
    gF.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land BB 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 BB) 8)) ltac:(apply hi8_lo16; exact LO).
    zs2. zs2. gF. zs2. zs2. zs2. zs2. zs2. zstep.
    apply evt_done. unfold bi_windup_post, wuF_PB, wuF_PD. rewrite (proj2 (Z.ltb_lt 8 BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
Qed.
