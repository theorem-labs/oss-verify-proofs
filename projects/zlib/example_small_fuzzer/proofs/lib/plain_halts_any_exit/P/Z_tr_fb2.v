(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.

Module Z_tr_init.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit.Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require FillWinModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_INIT_BLOCK : Z := 0x1aa30.

Definition ib_loop_post (L : dlay) (fcA dl : arr) (i : Z) (n : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1aa54) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 212, dl_As L + 2504)] m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u16arr psegs m' (dl_As L + 212) (avct (arr_fill_nat fcA i n 0) dl 573).

Lemma ib_loop : forall (n : nat) (L : dlay) (fcA dl : arr) (i : Z) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem),
  u16arr psegs m (dl_As L + 212) (avct fcA dl 573) -> arr_len fcA = 573 ->
  0 < dl_As L /\ dl_As L + 5968 < 2^62 ->
  0 <= i -> i + Z.of_nat n = 286 -> (1 <= n)%nat ->
  munch [(dl_As L + 212, dl_As L + 2504)] m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
  a3 = wz (dl_As L + 212 + 2 * (2 * i)) -> a4 = wz (dl_As L + 1356) ->
  evt psegs (ib_loop_post L fcA dl i n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1aa48) fc None m (seg_rom psegs)).
Proof.
  induction n as [|n IH]; intros until m; intros ARR LEN RS Hi Hn H1 MU WM MI -> ->; [lia|].
  unfold u16arr in ARR. pose proof (avct_zlength fcA dl 573 ltac:(lia)) as LCT.
  ct_store_fc ARR fcA dl 573 (dl_As L + 212) i 0 ltac:(reflexivity).
  do 2 zstep.
  destruct n as [|n].
  -
    if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|].
    apply evt_done. unfold ib_loop_post. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    cbn [arr_fill_nat]. exact ARR.
  - if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [|exfalso; lia].
    replace (wz (dl_As L + 212 + 2 * (2 * i) + 4)) with (wz (dl_As L + 212 + 2 * (2 * (i + 1)))) by (f_equal; lia).
    cbn [arr_fill_nat].
    eapply IH; try eassumption; try reflexivity; try lia.
Qed.


Definition ib_ph_post (EXIT : Z) (W : list ivl)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (P : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz EXIT) fc None m' (seg_rom psegs)
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ P m'.

Lemma ib_dt : forall (L : dlay) (fcA dl : arr)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem),
  u16arr psegs m (dl_As L + 2504) (avct fcA dl 61) -> arr_len fcA = 61 ->
  0 < dl_As L /\ dl_As L + 5968 < 2^62 -> mem_inv psegs m ->
  a2 = wz (dl_As L + 2047) ->
  evt psegs (ib_ph_post 0x1aacc [(dl_As L + 2504, dl_As L + 2748)] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
               (fun m' => u16arr psegs m' (dl_As L + 2504) (avct (arr_fill fcA 0 30 0) dl 61)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1aa54) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LEN RS MI ->.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  apply u16arr_to_cells in ARR. unfold avct in ARR. change (2 * 61) with 122 in ARR. rewrite zseq_122 in ARR. cbn [map c2s] in ARR.
  do 30 zstep.
  apply evt_done. unfold ib_ph_post. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  rewrite avct_fill by lia. change (2 * 61) with 122. rewrite zseq_122. apply u16arr_of_cells. exact ARR.
Qed.

Lemma ib_bt : forall (L : dlay) (fcA dl : arr)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem),
  u16arr psegs m (dl_As L + 2748) (avct fcA dl 39) -> arr_len fcA = 39 ->
  0 < dl_As L /\ dl_As L + 5968 < 2^62 -> mem_inv psegs m ->
  a2 = wz (dl_As L + 2047) ->
  evt psegs (ib_ph_post 0x1ab18 [(dl_As L + 2748, dl_As L + 2904)] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
               (fun m' => u16arr psegs m' (dl_As L + 2748) (avct (arr_fill fcA 0 19 0) dl 39)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1aacc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LEN RS MI ->.
  pose proof (munch_refl [(dl_As L + 2748, dl_As L + 2904)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  apply u16arr_to_cells in ARR. unfold avct in ARR. change (2 * 39) with 78 in ARR. rewrite zseq_78 in ARR. cbn [map c2s] in ARR.
  do 19 zstep.
  apply evt_done. unfold ib_ph_post. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  rewrite avct_fill by lia. change (2 * 39) with 78. rewrite zseq_78. apply u16arr_of_cells. exact ARR.
Qed.

Definition init_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : mem -> dlay -> deflate_state -> Prop) (L : dlay) (s : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + DS_SIZE)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ DSTx B m' L (init_block s).

Lemma init_block_gen : forall (B : mem -> dlay -> deflate_state -> Prop) (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  (forall W ma mb, B ma L s -> munch W ma mb -> wmono psegs ma mb -> disjoint_from W (dl_As L + 2904) 72 -> B mb L s) ->
  (forall ma, B ma L s -> B ma L (init_block s)) ->
  DSTx B m L s -> mem_inv psegs m ->
  a0 = wz (dl_As L) ->
  evt psegs (init_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_INIT_BLOCK) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HBm HBs ST MI ->. unfold Z_INIT_BLOCK.
  pose proof (munch_refl [(dl_As L, dl_As L + DS_SIZE)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2904); (dl_As L + 5881, dl_As L + 5968)] m) as MUf.
  open_DST ST. lay_open LAY.
  pose proof (ln_ltf _ LENS) as LNlt. pose proof (ln_dtf _ LENS) as LNdt. pose proof (ln_btf _ LENS) as LNbt.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504)] m) as MU1.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2748)] m) as MU2.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2904)] m) as MU3.
  unfold dlt in Glt.
  do 6 zstep.
  call (ib_loop (Z.to_nat L_CODES) L (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 0 m).
  1:{ exact Glt. } 1:{ exact LNlt. } 1:{ exact Rs. } 1:{ lia. } 1:{ unfold L_CODES. lia. } 1:{ unfold L_CODES. lia. }
  1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact MI. } 1:{ f_equal. lia. } 1:{ reflexivity. }
  clear Glt. rename POST into Glt. rewrite arr_fill_unfold in Glt.
  unfold u16arr in Glt. pose proof (avct_zlength (arr_fill (ds_dyn_ltree_fc s) 0 L_CODES 0) (ds_dyn_ltree_dl s) 573 ltac:(lia)) as LCTl.
  mv_group ddt_munch Gdt MU1 WM. clear MU1. unfold ddt in Gdt.
  call (ib_dt L (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s)).
  1:{ exact Gdt. } 1:{ exact LNdt. } 1:{ exact Rs. } 1:{ eassumption. } 1:{ reflexivity. }
  clear Gdt. rename POST into Gdt.
  unfold u16arr in Gdt. pose proof (avct_zlength (arr_fill (ds_dyn_dtree_fc s) 0 30 0) (ds_dyn_dtree_dl s) 61 ltac:(lia)) as LCTd.
  mv_group dbt_munch Gbt MU2 WM. clear MU2. unfold dbt in Gbt.
  call (ib_bt L (ds_bl_tree_fc s) (ds_bl_tree_dl s)).
  1:{ exact Gbt. } 1:{ exact LNbt. } 1:{ exact Rs. } 1:{ eassumption. } 1:{ reflexivity. }
  clear Gbt. rename POST into Gbt.
  unfold u16arr in Gbt. pose proof (avct_zlength (arr_fill (ds_bl_tree_fc s) 0 19 0) (ds_bl_tree_dl s) 39 ltac:(lia)) as LCTb.
  mv_group dsD_munch GD MU3 WM. clear MU3. open_D GD.
  do 3 zstep.
  pose proof (arr_len_fill (ds_dyn_ltree_fc s) 0 L_CODES 0) as LNf.
  ct_store_fc Glt (arr_fill (ds_dyn_ltree_fc s) 0 L_CODES 0) (ds_dyn_ltree_dl s) 573 (dl_As L + 212) 256 (wrap16 1) ltac:(reflexivity).
  do 2 zstep. step. fix_lit_store. step. fix_lit_store. do 2 zstep.
  apply evt_done. unfold init_block_post. do 15 eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  tr_groups MUf WM.
  apply (HBm [(dl_As L + 212, dl_As L + 2904); (dl_As L + 5881, dl_As L + 5968)] m m0) in GB; [| exact MUf| exact WM| cbn [disjoint_from]; slia].
  apply HBs in GB.
  constructor; [exact GA| exact GB| exact GC
               | exists hD0, hD1, hD2, hD3, hD4; unfold dsD_cells, init_block, set_Freq, set_tree_fc, tree_fc; dsred; close_cells GD
               | unfold dlt, u16arr, init_block, set_Freq, set_tree_fc, tree_fc; dsred; change END_BLOCK with 256; exact Glt
               | unfold ddt, u16arr, init_block, set_Freq, set_tree_fc, tree_fc; dsred; exact Gdt
               | unfold dbt, u16arr, init_block, set_Freq, set_tree_fc, tree_fc; dsred; exact Gbt
               | exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend
               | close_lens_with LENS ltac:(unfold init_block, set_Freq, set_tree_fc, tree_fc) | exact LAY].
Qed.

Lemma init_block_spec : forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  a0 = wz (dl_As L) ->
  evt psegs (init_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dsB L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_INIT_BLOCK) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST MI E. apply init_block_gen; [| | exact ST| exact MI| exact E].
  - intros W ma mb H MU WM D. exact (dsB_munch ma mb L s W H MU WM D).
  - intros ma H. exact H.
Qed.

Lemma tr_init_spec : tr_init_stmt.
Proof.
  unfold tr_init_stmt. intros until m. intros ST MI ->. unfold Z_TR_INIT.
  pose proof (munch_refl [(dl_As L, dl_As L + DS_SIZE)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(dl_As L + 2904, dl_As L + 2976); (dl_As L + 5881, dl_As L + 5968)] m) as MUf.
  open_DST ST. lay_open LAY.
  destruct GB as (d1 & d2 & d3 & d4 & d5 & d6 & hB1 & hB2 & hB3 & GB). unfold dsBi_cells in GB.
  open_D GD.
  do 10 zstep.
  zstep. step. fix_lit_store. zstep. step. fix_lit_store.
  do 3 zstep.
  zstep. step. fix_lit_store.
  do 4 zstep. (* 1.4: + sw zero, 8(a1) = bi_used *)
  tr_groups MUf WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (ST1 : DST mc L (set_bi_valid (set_bi_buf s 0) 0)) end.
  { constructor; [exact GA| exists hB1, hB2, hB3; unfold dsB_cells, Z_SL_DESC, Z_SD_DESC, Z_SBL_DESC; dsred; close_cells GB| exact GC
                 | do 5 eexists; unfold dsD_cells; dsred; close_cells GD
                 | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend
                 | close_lens LENS| exact LAY]. }
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf.
  call (init_block_spec L (set_bi_valid (set_bi_buf s 0) 0)).
  1:{ exact ST1. } 1:{ eassumption. } 1:{ reflexivity. }
  apply evt_done. unfold tr_init_post. do 15 eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  exact POST.
Qed.
End Z_tr_init.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_cb3.

Module Z_tr_cb4.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_cb3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_cb3.Z_tr_cb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_cb3.Z_tr_cb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel RefCompressBlk1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.CompressModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefCompressBlk1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition cb_iter_post (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 t4 t5 t6 wbb PB' PD' BB' BV' pcx m',
    ms' = MS (cbR L LT DT (sx + 1 + 1 + 1) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV') t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ sbs_run (upd4 s PB PD BB BV) (sym_calls (upd4 s PB PD BB BV) lfc ldl dfc ddl sx) = upd4 s PB' PD' BB' BV'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'
    /\ ((pcx = 0x1c5e4 /\ ds_sym_next s <= sx + 3) \/ (pcx = 0x1c298 /\ sx + 3 < ds_sym_next s)).

Lemma cb_iter : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> ct_readable (Wem L) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  (forall i, 0 <= i < 286 -> 0 <= arr_get lfc i < 65536) -> (forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> 0 <= ds_sym_next s -> ds_sym_next s + 3 < 2^31 -> sx < ds_sym_next s ->
  sym_ok 65536 (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt psegs (cb_iter_post L s lfc ldl dfc ddl LT DT sx PB PD BB BV ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c298) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL RDD RLT1 RLT2 RDT1 RDT2 RLf RDf RBV RPD BYT Rlb Rsn1 Rsn2 Hsx SOK.
  pose proof SOK as (Hsx0 & _).
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  call (cb_body L s lfc ldl dfc ddl LT DT sx PB PD BB BV wbb).
  1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDL. } 1:{ exact RDD. } 1:{ exact RLT1. } 1:{ exact RLT2. }
  1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact BYT. } 1:{ exact Rlb. } 1:{ lia. } 1:{ exact SOK. }
  match goal with H : EM _ _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of H with EM mm _ _ _ _ _ _ => pose proof H as EMo end end.
  open_EM EMo. unfold cbR. zs2. zs2. zstep. reg_as (sx + 3) (sx + 1 + 1 + 1).
  br_cases K.
  - apply evt_done. unfold cb_iter_post, cbR. do 16 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    left. split; [reflexivity| lia].
  - apply evt_done. unfold cb_iter_post, cbR. do 16 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    right. split; [reflexivity| lia].
Qed.

Definition cb_loop_post (L : dlay) (s : deflate_state) (LT DT : Z) (R : deflate_state)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 a4 t4 t5 t6 wbb PB' PD' BB' BV' m',
    ms' = MS (mkR ra sp gp tp (wz 65535) (wz Z_LENGTH_CODE) (wz 4) s0 s1 (wz (dl_As L)) (wz LT) (wz DT) (wz (dl_As L + 5888)) a4
                  (wz 16) (wz (-20)) (wz 257) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz BV') t4 t5 t6) F (wz 0x1c5e4) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'.

Lemma cb_loop : forall (f : nat) (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV sx : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 LT lfc ldl 286 -> ct_readable (Wem L) m0 DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  (forall i, 0 <= i < 286 -> 0 <= arr_get lfc i < 65536) -> (forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> 0 <= ds_sym_next s -> ds_sym_next s + 3 < 2^31 ->
  sx < ds_sym_next s -> ds_sym_next s - sx <= 3 * Z.of_nat (S f) ->
  cb_ok 65536 (S f) (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  R = compress_block_loop (S f) (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt psegs (cb_loop_post L s LT DT R ra sp gp tp s6 s7 s8 s9 s10 s11 F fc m0)
      (MS (cbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c298) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros EMH HBB MI LAY MU WM RDL RDD RLT1 RLT2 RDT1 RDT2 RLf RDf RBV RPD BYT Rlb Rsn1 Rsn2 Hsx SNF CBOK ER.
  - cbn [cb_ok] in CBOK. destruct CBOK as [SOK NEXT]. pose proof SOK as (Hsx0 & _). rewrite cb_loop_S in ER. cbv zeta in ER.
    call (cb_iter L s lfc ldl dfc ddl LT DT sx PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| apply sub_fp_refl]. } 1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact BYT. }
    1:{ exact Rlb. } 1:{ exact Rsn1. } 1:{ exact Rsn2. } 1:{ exact Hsx. } 1:{ exact SOK. }
    match goal with E : sbs_run _ _ = _ |- _ => rewrite E in ER; rewrite upd4_sym_next in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    rewrite (proj2 (Z.ltb_ge _ _)) in ER by lia.
    apply evt_done. unfold cb_loop_post, cbR. do 16 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [exact ER|]. split; [assumption|]. split; assumption.
  - cbn [cb_ok] in CBOK. destruct CBOK as [SOK NEXT]. pose proof SOK as (Hsx0 & _). rewrite cb_loop_S in ER. cbv zeta in ER, NEXT.
    call (cb_iter L s lfc ldl dfc ddl LT DT sx PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| apply sub_fp_refl]. } 1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact BYT. }
    1:{ exact Rlb. } 1:{ exact Rsn1. } 1:{ exact Rsn2. } 1:{ exact Hsx. } 1:{ exact SOK. }
    match goal with E : sbs_run _ _ = _ |- _ => rewrite E in ER, NEXT; rewrite upd4_sym_next in ER, NEXT end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
    + rewrite (proj2 (Z.ltb_ge _ _)) in ER by lia.
      apply evt_done. unfold cb_loop_post, cbR. do 16 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|]. split; [assumption|]. split; assumption.
    + rewrite (proj2 (Z.ltb_lt _ _)) in ER, NEXT by lia.
      eapply (IH L s lfc ldl dfc ddl LT DT R m0); try eassumption; try lia.
Qed.

Ltac close_lens_sbF LENS :=
  let l1 := fresh in let l2 := fresh in let l3 := fresh in let l4 := fresh in let l5 := fresh in let l6 := fresh in let l7 := fresh in
  let l8 := fresh in let l9 := fresh in let l10 := fresh in let l11 := fresh in let l12 := fresh in let l13 := fresh in
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
  constructor; unfold upd4; dsred; first [assumption | rewrite ?sbF_PB_len; assumption].
Ltac cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY :=
  constructor; [exact HA| exact GB| exact GC| exact HD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
               | exact Gwin| exact Gprev| exact Ghead| exact HP| | exact LAY].

Definition Z_COMPRESS_BLOCK : Z := 0x1c22c.

Notation cbW L lo sp := [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] (only parsing).

Definition compress_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch (cbW L lo sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L (compress_block s lfc ldl dfc ddl).

Lemma compress_block_spec : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> dlay_below L lo (bv_unsigned sp) ->
  ct_readable (cbW L lo sp) m LT lfc ldl 286 -> ct_readable (cbW L lo sp) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 ->
  (forall i, 0 <= i < 286 -> 0 <= arr_get lfc i < 65536) -> (forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 65536) ->
  compress_block_ok 65536 s lfc ldl dfc ddl -> 0 <= ds_lit_bufsize s -> 0 <= ds_sym_next s -> ds_sym_next s + 3 < 2^31 ->
  a0 = wz (dl_As L) -> a1 = wz LT -> a2 = wz DT ->
  evt psegs (compress_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s lfc ldl dfc ddl lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_COMPRESS_BLOCK) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST MI STK LO BEL RDL RDD RLT1 RLT2 RDT1 RDT2 RLf RDf (BI & PB0 & CBOK & ENDOK) Rlb Rsn1 Rsn2 -> -> ->. unfold Z_COMPRESS_BLOCK.
  pose proof BI as (RBV & RBB & RPD).
  pose proof (munch_refl (cbW L lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  carve_frame 48%nat STK.
  do 7 zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  assert (HBB : bv_unsigned (wz (ds_bi_buf s)) mod 2^16 = ds_bi_buf s mod 2^16) by apply lo16_unsigned_wz.
  assert (BYT : byt (ds_pending_buf s)) by exact PB0.
  assert (EX0 : upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) = s) by apply upd4_self.
  pose proof EMH as EMo. open_EM EMo.
  do 3 zs2. zs2. clear GA GD Gpend LPB LNP0.
  zstep. br_cases K.
  -
    pose proof EMH as EMo. open_EM EMo. zs2. clear GA GD Gpend LPB LNP0.
    assert (EQF : compress_block s lfc ldl dfc ddl
                  = upd4 s (sbF_PB (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) (arr_get lfc 256) (arr_get ldl 256))
                           (sbF_PD (ds_pending s) (ds_bi_valid s) (arr_get ldl 256)) (sbF_BB (ds_bi_buf s) (ds_bi_valid s) (arr_get lfc 256) (arr_get ldl 256))
                           (sbF_BV (ds_bi_valid s) (arr_get ldl 256))).
    { unfold compress_block. rewrite (proj2 (Z.eqb_eq _ _) K). cbn [negb]. unfold send_code, END_BLOCK. rewrite <- send_bits_sbF, EX0. reflexivity. }
    cbv zeta in ENDOK. rewrite (proj2 (Z.eqb_eq _ _) K) in ENDOK. cbn [negb] in ENDOK. unfold END_BLOCK in ENDOK. rewrite <- EX0 in ENDOK.
    apply sbs_ok_cons_flat in ENDOK. destruct ENDOK as (Rl & ROOM & _).
    call (cb_S6 L s lfc ldl LT (arr_get lfc 256) (arr_get ldl 256) (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) (wz (ds_bi_buf s))).
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ lia. } 1:{ exact ROOM. }
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    do 8 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold compress_block_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
  -
    do 10 zs2.
    destruct (Z.to_nat (ds_sym_next s)) as [|f] eqn:En; [lia|].
    remember (compress_block_loop (S f) s lfc ldl dfc ddl 0) as R eqn:ER.
    specialize (CBOK K).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      call (cb_loop f L s lfc ldl dfc ddl LT DT R mc (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact RBV. } 1:{ lia. } 1:{ exact BYT. }
    1:{ exact Rlb. } 1:{ exact Rsn1. } 1:{ exact Rsn2. } 1:{ lia. } 1:{ lia. } 1:{ rewrite EX0. exact CBOK. } 1:{ rewrite EX0. exact ER. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : compress_block s lfc ldl dfc ddl
                    = upd4 s (sbF_PB pb pd bb bv (arr_get lfc 256) (arr_get ldl 256)) (sbF_PD pd bv (arr_get ldl 256))
                             (sbF_BB bb bv (arr_get lfc 256) (arr_get ldl 256)) (sbF_BV bv (arr_get ldl 256)));
      [ unfold compress_block; rewrite (proj2 (Z.eqb_neq _ _) K); cbn [negb]; rewrite ?En; rewrite <- ER, E; unfold send_code, END_BLOCK; apply send_bits_sbF |]
    end.
    cbv zeta in ENDOK. rewrite (proj2 (Z.eqb_neq _ _) K) in ENDOK. cbn [negb] in ENDOK. rewrite ?En in ENDOK.
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ => rewrite E in ENDOK end.
    unfold END_BLOCK in ENDOK. apply sbs_ok_cons_flat in ENDOK. destruct ENDOK as (Rl & ROOM & _).
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ => call (cb_S6 L s lfc ldl LT (arr_get lfc 256) (arr_get ldl 256) pb pd bb bv) end.
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDL| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact RLT1. } 1:{ exact RLT2. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ assumption. } 1:{ assumption. } 1:{ exact ROOM. }
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    do 8 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold compress_block_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
Qed.
End Z_tr_cb4.


Module Z_tr_fbtail.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

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

Definition tfb_windup_post (L : dlay) (s : deflate_state) (PB : arr) (PD : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b868) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD (wz 0) (wz 0).

Lemma tfb_windup : forall (L : dlay) (s : deflate_state) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD (wz BB) (wz BV) -> mem_inv psegs m -> dlay_ok L ->
  0 <= BV <= 16 -> 0 <= BB < 2^16 -> 0 <= PD -> wuF_PD PD BV <= 65536 ->
  evt psegs (tfb_windup_post L s (wuF_PB PB PD BB BV) (wuF_PD PD BV)
                ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1 a4 a5 a6 a7 s2 s3 s4 (wz (dl_As L + 5912)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (dl_As L + 5912)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b7f4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH MI LAY RBV RBB RPD ROOM.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH. unfold wuF_PD in ROOM.
  zs2. zs2. zstep. br_cases K.
  -
    zstep. br_cases K0.
    +
      zs2. zs2. zs2. zs2. zs2. zs2. zs2. (* 1.4 bi_windup: lw, sh, add, and, add, sw, sw bi_used *)
      apply evt_done. unfold tfb_windup_post, wuF_PB, wuF_PD. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 5 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
    +
      rewrite (proj2 (Z.ltb_ge 8 BV)), (proj2 (Z.ltb_lt 0 BV)) in ROOM by lia.
      zs2. zs2. rd_c2 GD 55%nat 0. zsb. zs2. zs2. zs2.
      pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 BB) ltac:(apply b0_val_w; lia).
      zs2. zs2. zs2. zs2. zs2. zs2. zs2. (* 1.4 bi_windup: lw, sh, add, and, add, sw, sw bi_used *)
      apply evt_done. unfold tfb_windup_post, wuF_PB, wuF_PD. rewrite (proj2 (Z.ltb_ge 8 BV)), (proj2 (Z.ltb_lt 0 BV)) by lia. do 5 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
  -
    rewrite (proj2 (Z.ltb_lt 8 BV)) in ROOM by lia.
    zs2. zs2. rd_c2 GD 55%nat 0. zsb. zs2. zs2. zs2.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land BB 255)) ltac:(apply b0_val_land; lia).
    zs2. zs2. rd_c2 GD 55%nat 1. zsb. zs2. zs2. zs2. zs2.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land BB 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 BB) 8)) ltac:(apply b1_val; lia).
    zs2. zs2. zs2. zs2. zs2. zs2. zs2. (* 1.4 bi_windup: lw, sh, add, and, add, sw, sw bi_used *)
    apply evt_done. unfold tfb_windup_post, wuF_PB, wuF_PD. rewrite (proj2 (Z.ltb_lt 8 BV)) by lia. do 5 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. close_EM GA GD Gpend.
Qed.
End Z_tr_fbtail.


Module Z_tr_fb1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_tr_emit Z_tr_cb3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_fb2.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_fb2.Z_tr_fbtail.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac name_mem id := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => is_var mm; rename mm into id end.

Notation tfW L lo sp := [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] (only parsing).

Notation tfWz L lo sp := [(lo, bv_unsigned sp); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] (only parsing).

Definition tfb_post_gen (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (Rfin : deflate_state) (lo : Z) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch (tfW L lo sp) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DREP m' L Rfin.

Lemma tfb_post_gen_eq : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m,
  tr_flush_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m
  = tfb_post_gen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (tr_flush_block s buf len last) lo m.
Proof. reflexivity. Qed.

Definition tfR (L : dlay) (sp : word) (last len bufp : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (dl_As L)) (wz last) a0 a1 a2 a3 a4 a5 a6 a7
      (wz len) (wz bufp) (wz (dl_As L + 2047)) (wz (dl_As L + 5912)) (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition tf_frame (ra0 s0o s1o s2o s3o s4o s5o s6o : word) : list cell := [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0].

Lemma bi_windup_flat : forall Z0, bi_windup Z0 = upd4 Z0 (wuF_PB (ds_pending_buf Z0) (ds_pending Z0) (ds_bi_buf Z0) (ds_bi_valid Z0)) (wuF_PD (ds_pending Z0) (ds_bi_valid Z0)) 0 0.
Proof. intros Z0. rewrite <- (upd4_self Z0) at 1. apply bi_windup_wuF. Qed.

Lemma wuF_PB_len : forall PB PD BB BV, arr_len (wuF_PB PB PD BB BV) = arr_len PB.
Proof. intros. unfold wuF_PB. destruct (8 <? BV); [|destruct (0 <? BV)]; rewrite ?arr_len_set; reflexivity. Qed.

Lemma tfb_finish : forall (L : dlay) (Z0 Rfin : deflate_state) (c : cstrm) (last lo pcx : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L Z0 -> dzs m L c -> ds_strm Z0 = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 Z0 -> (last <> 0 -> ds_pending (bi_windup Z0) <= 65536) ->
  Rfin = (if negb (last =? 0) then bi_windup Z0 else Z0) ->
  ((pcx = 0x1b7f4 /\ last <> 0) \/ (pcx = 0x1b868 /\ last = 0)) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (dl_As L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (dl_As L + 5912)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pcx) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI ROOM ER [[-> NZ]|[-> ZE]]; unfold tf_frame in *.
  -
    rewrite (proj2 (Z.eqb_neq _ _) NZ) in ER. cbn [negb] in ER. specialize (ROOM NZ). rewrite bi_windup_flat in ER, ROOM.
    rewrite upd4_pending in ROOM. destruct BI as (RBV & RBB & RPD).
    pose proof (munch_refl (Wem L) m) as MUw. pose proof (wmono_refl psegs m) as WMw.
    open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
    pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH.
    call (tfb_windup L Z0 (ds_pending_buf Z0) (ds_pending Z0) (ds_bi_buf Z0) (ds_bi_valid Z0)).
    1:{ exact EMH. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RBV. } 1:{ exact RBB. } 1:{ lia. } 1:{ exact ROOM. }
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end.
    destruct (EM_to_groups _ _ _ _ _ _ _ 0 0 EMf eq_refl eq_refl) as (HA & HD & HP).
    clear GA GD Gpend EMH. tr_groups MUw WMw.
    do 10 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold tfb_post_gen. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite ER. split.
    + match goal with |- dzs ?mm _ _ => change (dzs mm L (ds_strm Z0)) end. rewrite ESTRM. exact DZ.
    + cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY.
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; unfold upd4; dsred; rewrite ?wuF_PB_len; assumption.
  -
    rewrite (proj2 (Z.eqb_eq _ _) ZE) in ER. cbn [negb] in ER.
    below_open BEL.
    do 10 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold tfb_post_gen. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite ER. split; [rewrite ESTRM; exact DZ| exact ST].
Qed.
End Z_tr_fb1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_fb2.Z_tr_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_fb2.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_fb2.Z_tr_fbtail OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tfb_ssite_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 wbb m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b544) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma tfb_ssite : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= last <= 1 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_ssite_post L s sp last len bufp (sbF_PB PB PD BB BV (2 + last) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (2 + last) 3) (sbF_BV BV 3)
                ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 (wz BV) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b444) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY Rl RBV RPD ROOM. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. reg_as (last + 2) (2 + last). zstep. br_cases K.
  -
    zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    zs2. zs2. zs2.
    apply evt_done. unfold tfb_ssite_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| exact LO].
  -
    zs2. zs2. zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    sbf_b0 L Gpend PB PD (nbv BB BV (2 + last)) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV (2 + last)) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite (Z.mod_small (2 + last) 65536) by lia.
    zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (BV + -13) (BV + 3 - 16).
    apply evt_done. unfold tfb_ssite_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 7 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Lemma send_bits_flat : forall X V l, send_bits X V l = upd4 X (sbF_PB (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) V l) (sbF_PD (ds_pending X) (ds_bi_valid X) l)
                                                        (sbF_BB (ds_bi_buf X) (ds_bi_valid X) V l) (sbF_BV (ds_bi_valid X) l).
Proof. intros. rewrite <- (upd4_self X) at 1. apply send_bits_sbF. Qed.

Lemma BINV_init_block : forall P Y, BINV P Y -> BINV P (init_block Y).
Proof. intros P Y H. eapply BINV_bits4; [|exact H]. apply (k_init_block _ _ _ keeps_bits4 eq_refl). Qed.
Lemma strm_init_block : forall Y, ds_strm (init_block Y) = ds_strm Y.
Proof. intros. apply (k_init_block _ _ _ keeps_strm eq_refl). Qed.

Lemma tfb_arm_static : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (last len bufp lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> RefFlushBlk13.stat_ok 65536 last X ->
  RefFlushBlk13.post_ok 65536 last (compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) ->
  0 <= last <= 1 ->
  Rfin = tfb_fin last (compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 (wz (ds_bi_valid X)) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b444) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI (ROOM & CBOK & Rsn & Rlb) (BIY & ROOMY) Rl ER.
  unfold Z_TRFB_STACK in LO. pose proof BI as (RBV & RBB & RPD).
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  pose proof (munch_refl (Wem L) m) as MUw. pose proof (wmono_refl psegs m) as WMw.
  open_DST ST. pose proof (ln_pend _ LENS) as LNP.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH.
  unfold sb_room, Buf_size in ROOM.
  call (tfb_ssite L X sp last len bufp (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) (wz (ds_bi_buf X))).
  1:{ exact EMH. } 1:{ apply lo16_unsigned_wz. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ lia. } 1:{ intros; apply ROOM; lia. }
  match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end.
  match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
    destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
  clear GA GD Gpend EMH. tr_groups MUw WMw. clear MUw WMw.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ST1 : DST mm L (send_bits X (2 + last) 3)) by
      (rewrite send_bits_flat; cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY; close_lens_sbF LENS) end.
  clear HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead EMf.
  unfold tfR. do 6 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl psegs m1) as WMz.
  call (compress_block_spec L (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl Z_STATIC_LTREE Z_STATIC_DTREE lo).
  1:{ exact ST1. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ eapply ct_readable_ro; [apply rod_static_ltree| lia]. } 1:{ eapply ct_readable_ro; [apply rod_static_dtree| lia]. }
  1:{ unfold Z_STATIC_LTREE; lia. } 1:{ unfold Z_STATIC_LTREE; lia. } 1:{ unfold Z_STATIC_DTREE; lia. } 1:{ unfold Z_STATIC_DTREE; lia. }
  1:{ intros i _. pose proof (TreesTab.static_ltree_fc_bound i). lia. } 1:{ intros i _. pose proof (TreesTab.static_dtree_fc_bound i). lia. }
  1:{ exact CBOK. } 1:{ rewrite send_bits_flat, upd4_lit_bufsize. lia. } 1:{ rewrite send_bits_flat, upd4_sym_next. lia. } 1:{ rewrite send_bits_flat, upd4_sym_next. lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST1. name_mem m2.
  remember (compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl) as Y eqn:EY.
  assert (ESY : ds_strm Y = c).
  { rewrite EY, (k_compress_block _ _ _ keeps_strm eq_refl), (k_send_bits _ _ _ keeps_strm eq_refl). exact ESTRM. }
  zs2. zs2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep.
  name_mem m3.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b7f4 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - zs2. eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b868 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
