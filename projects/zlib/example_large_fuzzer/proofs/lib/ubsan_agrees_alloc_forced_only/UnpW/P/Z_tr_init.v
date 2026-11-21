(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_INIT_BLOCK : Z := 0x1adb0.

Definition ib_loop_post (L : dlay) (fcA dl : arr) (i : Z) (n : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1add4) fc None m' (seg_rom psegs)
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
          F (wz 0x1adc8) fc None m (seg_rom psegs)).
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
  evt psegs (ib_ph_post 0x1ae4c [(dl_As L + 2504, dl_As L + 2748)] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
               (fun m' => u16arr psegs m' (dl_As L + 2504) (avct (arr_fill fcA 0 30 0) dl 61)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1add4) fc None m (seg_rom psegs)).
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
  evt psegs (ib_ph_post 0x1ae98 [(dl_As L + 2748, dl_As L + 2904)] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
               (fun m' => u16arr psegs m' (dl_As L + 2748) (avct (arr_fill fcA 0 19 0) dl 39)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1ae4c) fc None m (seg_rom psegs)).
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
