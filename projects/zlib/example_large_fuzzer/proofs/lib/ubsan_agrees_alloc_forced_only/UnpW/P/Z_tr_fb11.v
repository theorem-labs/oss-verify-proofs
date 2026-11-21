(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_stored Z_tr_fb1 Z_tr_fb8 Z_tr_fb10.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel GenBitlenModel FlushBlockModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk12 RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Lemma tfb_pre_hi : forall s buf len last, 0 < ds_level s ->
  exists X0 X1 X2 X3 X4 X5 X6 mb d,
    X0 = tfb_X0 s /\ X1 = build_tree X0 TL /\ X2 = build_tree X1 TD /\ X3 = scan_tree X2 TL (ds_l_max_code X2) /\ X4 = scan_tree X3 TD (ds_d_max_code X3)
    /\ X5 = build_tree X4 TB /\ mb = tfb_mb X5 /\ X6 = tfb_X6 X5 mb /\ d = tfb_branch X6 buf len
    /\ tfb_pre s buf len last = tfb_emit d X6 mb buf len last
    /\ (RefFlushBlk13.hi_ok 65536 s buf len last -> hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last)
    /\ bits4 X6 = bits4 s.
Proof.
  intros s buf len last Hl. do 9 eexists.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split].
  - unfold tfb_pre. rewrite (proj2 (Z.ltb_lt _ _) Hl). reflexivity.
  - intros H. exact H.
  - exact (RefFlushBlk13.bits4_X6' s).
Qed.

Section WithBuildTree.
Hypothesis BT : build_tree_stmt.

Lemma tr_flush_block_spec : tr_flush_block_stmt.
Proof.
  unfold tr_flush_block_stmt. intros until m. intros DR MI RC STK LO AL BEL BI FBS BOK Rlen Rl -> -> -> ->.
  rewrite tfb_post_gen_eq, tr_flush_block_eq.
  destruct DR as [DZ ST]. unfold Z_TR_FLUSH_BLOCK.
  pose proof BEL as BEL0. below_open BEL0.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
  unfold RefFlushBlk13.fb_safe in FBS. cbv zeta in FBS. rewrite (ln_pend _ LENS) in FBS. destruct FBS as (Rlev & Rdt & _ & RF & POK & HILO).
  pose proof (munch_refl (tfW L lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl psegs m) as WMs.
  pose proof (dlay_ranges _ LAY) as (Rs & _).
  assert (LO' : lo <= bv_unsigned sp - 512) by exact LO.
  carve_frame 64%nat STK.
  do 9 zstep.
  tr_groups MUs WMs. clear MUs WMs. name_mem m1.
  pose proof GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA'). unfold dsA_cells in GA'.
  do 10 zs2. clear GA'.
  assert (ST : DST m1 L s) by (constructor; assumption).
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge _ _)) in HILO by lia. unfold tfb_pre in POK |- *. rewrite (proj2 (Z.ltb_ge 0 (ds_level s))) in POK |- * by lia.
    do 4 zs2.
    replace (wz (len + 5)) with (wz (wrap64 (len + 5))) by (apply Z_to_bv_eqm; rewrite wrap64_mod, Z.mod_mod by lia; reflexivity).
    eapply (tfb_emit_all L s _ (ds_strm s) buf last len 0 (wrap64 (len + 5)) (wrap64 (len + 5))
              (if (wrap64 (len + 4) <=? wrap64 (len + 5)) && is_some buf then 2 else 0) lo m);
      [exact ST| exact DZ| reflexivity| eassumption| exact MU| exact WM| exact FR| exact STK| exact LO| exact BEL| exact BI| exact BOK| exact Rlen| exact Rl| lia
      | apply wrap64_range| apply wrap64_range| rewrite Z.eqb_refl; reflexivity| | exact POK| reflexivity].
    unfold RefFlushBlk13.lo_ok in HILO. destruct buf as [off|]; cbn [is_some].
    + destruct BOK as [Ro1 Ro2]. rewrite !wrap64_id by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb]. exact HILO.
    + rewrite Bool.andb_false_r. exact HILO.
  - (* [comment removed for export] *)
    assert (Hlev : 0 < ds_level s) by lia.
    rewrite (proj2 (Z.ltb_lt _ _) Hlev) in HILO.
    destruct (tfb_pre_hi s buf len last Hlev) as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & mb & d & E0 & E1 & E2 & E3 & E4 & E5 & Emb & E6 & Ed & EPRE & HIB & B6).
    rewrite EPRE in POK |- *.
    eapply (tfb_hi1 BT L s X0 X1 X2 X3 X4 X5 X6 _ buf last len mb d lo m);
      [exact ST| exact DZ| eassumption| exact RC| exact MU| exact WM| exact FR| exact STK| exact LO| exact AL| exact BEL| exact Hlev| exact Rdt| exact RF
      | exact E0| exact E1| exact E2| exact E3| exact E4| exact E5| exact Emb| exact E6| exact Ed| apply HIB; exact HILO| eapply BINV_bits4; [exact B6| exact BI]
      | exact POK| exact BOK| exact Rlen| exact Rl| reflexivity].
Qed.

End WithBuildTree.
