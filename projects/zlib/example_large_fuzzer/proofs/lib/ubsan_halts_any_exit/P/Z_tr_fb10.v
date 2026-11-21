(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_stored Z_tr_scan3 Z_tr_fbmid Z_tr_fbpure Z_tr_fb1 Z_tr_fb8 Z_tr_fb9.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel ScanModel GenBitlenModel FlushBlockModel RefFlushBlk12 RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_SL_range : forall X, 0 <= tfb_SL X < 2^64.
Proof.
  intros X. unfold tfb_SL. pose proof (wrap64_range (ds_static_len X + 3 + 7)) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma tfb_OL_range : forall X, 0 <= tfb_OL X < 2^64.
Proof.
  intros X. unfold tfb_OL. cbv zeta. destruct (_ || _); [apply tfb_SL_range|].
  pose proof (wrap64_range (ds_opt_len X + 3 + 7)) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma tfb_branch_eq : forall X6 buf len,
  tfb_branch X6 buf len = (if (wrap64 (len + 4) <=? tfb_OL X6) && is_some buf then 2 else if tfb_SL X6 =? tfb_OL X6 then 0 else 1).
Proof. intros. reflexivity. Qed.

Lemma relro_tfW : forall L lo (sp : word) m0 m, relro_clean m0 -> munch (tfW L lo sp) m0 m -> dlay_ok L -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> relro_clean m.
Proof.
  intros L lo sp m0 m RC MU LAY BEL LE. eapply relro_clean_munch; [exact RC| exact MU|].
  pose proof (lo_s _ LAY) as Bs. pose proof (lo_b _ LAY) as Bb. unfold blk_ok in Bs, Bb. unfold dlay_below in BEL. unfold RELRO_LO, RELRO_HI.
  cbn [disjoint_from]. lia.
Qed.

Lemma DST_scanL : forall m L X mc X',
  X' = scan_tree X TL mc ->
  dsA m L X -> dsB m L X -> dsC m L X -> dsD m L X -> ddt m L X -> dblc m L X -> dheap m L X -> ddep m L X ->
  dwin m L X -> dprev m L X -> dhead m L X -> dpend m L X -> dlens X -> dlay_ok L ->
  dlt m L X' -> dbt m L X' -> DST m L X'.
Proof.
  intros m L X mc X' E GA GB GC GD Gdt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY Glt Gbt.
  destruct (scan_tree_flat X TL mc) as (b' & EF & Lb). rewrite <- E in EF. clear E.
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
  constructor; [rewrite EF; exact GA| rewrite EF; exact GB| rewrite EF; exact GC| rewrite EF; exact GD| exact Glt| rewrite EF; exact Gdt| exact Gbt| rewrite EF; exact Gblc
    | rewrite EF; exact Gheap| rewrite EF; exact Gdep| rewrite EF; exact Gwin| rewrite EF; exact Gprev| rewrite EF; exact Ghead| rewrite EF; exact Gpend| | exact LAY].
  rewrite EF; constructor; unfold set_Len, set_Dad, set_tree_dl, tree_dl; dsred; rewrite ?arr_len_set; first [assumption | lia].
Qed.
Lemma DST_scanD : forall m L X mc X',
  X' = scan_tree X TD mc ->
  dsA m L X -> dsB m L X -> dsC m L X -> dsD m L X -> dlt m L X -> dblc m L X -> dheap m L X -> ddep m L X ->
  dwin m L X -> dprev m L X -> dhead m L X -> dpend m L X -> dlens X -> dlay_ok L ->
  ddt m L X' -> dbt m L X' -> DST m L X'.
Proof.
  intros m L X mc X' E GA GB GC GD Glt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY Gdt Gbt.
  destruct (scan_tree_flat X TD mc) as (b' & EF & Lb). rewrite <- E in EF. clear E.
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
  constructor; [rewrite EF; exact GA| rewrite EF; exact GB| rewrite EF; exact GC| rewrite EF; exact GD| rewrite EF; exact Glt| exact Gdt| exact Gbt| rewrite EF; exact Gblc
    | rewrite EF; exact Gheap| rewrite EF; exact Gdep| rewrite EF; exact Gwin| rewrite EF; exact Gprev| rewrite EF; exact Ghead| rewrite EF; exact Gpend| | exact LAY].
  rewrite EF; constructor; unfold set_Len, set_Dad, set_tree_dl, tree_dl; dsred; rewrite ?arr_len_set; first [assumption | lia].
Qed.

Definition hi_body (PBL : Z) (X0 X1 X2 X3 X4 X5 X6 : deflate_state) (mb d : Z) (buf : option Z) (len last : Z) : Prop :=
  bt_safe X0 TL /\ bt_safe X1 TD
  /\ (0 <= ds_l_max_code X2 /\ ds_l_max_code X2 + 1 < 573) /\ (forall i, 0 <= i <= ds_l_max_code X2 -> 0 <= Len X2 TL i <= 15)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536)
  /\ (0 <= ds_d_max_code X3 /\ ds_d_max_code X3 + 1 < 61) /\ (forall i, 0 <= i <= ds_d_max_code X3 -> 0 <= Len X3 TD i <= 15)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536)
  /\ bt_safe X4 TB
  /\ ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 16)
      /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536))
  /\ 0 <= ds_opt_len X5 < 2 ^ 63 /\ 0 <= ds_static_len X5 < 2 ^ 63 /\ 0 <= ds_strategy X5 <= 4
  /\ match d with
     | 0 => RefFlushBlk13.stat_ok PBL last X6
     | 1 => RefFlushBlk12.dyn_ok PBL last X6 mb
     | _ => RefFlushBlk13.sto_ok PBL X6 buf len last
     end.

Section WithBuildTree.
Hypothesis BT : build_tree_stmt.

Lemma tfb_hi2 : forall (L : dlay) (X4 X5 X6 Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X4 -> dzs m L c -> ds_strm X4 = c -> mem_inv psegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe X4 TB -> X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536) ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 ->
  BINV 65536 X6 ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X6 | 1 => RefFlushBlk12.dyn_ok 65536 last X6 mb | _ => RefFlushBlk13.sto_ok 65536 X6 buf len last end ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b644) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI RC MU WM FR STK LO AL BEL BTS E5 Emb E6 Ed RBd Rol Rsl Rst BI6 SAFE POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  assert (Rmb : 0 <= mb <= 18) by (rewrite Emb; unfold tfb_mb; pose proof (build_bl_tree_loop_range 17 X5 18 ltac:(lia)); lia).
  unfold tfR. do 3 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl psegs m1) as WMz.
  call (BT L X4 TB lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ eapply relro_tfW; try eassumption; lia. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_BT_STACK. lia. }
  1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. } 1:{ exact BTS. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. rewrite <- E5 in *. rewrite ESP in *. name_mem m2.
  match goal with H : DST m2 L X5 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof Gbt as Gbt'. unfold dbt, u16arr in Gbt'.
  pose proof (munch_refl [] m2) as MUm. pose proof (wmono_refl psegs m2) as WMm.
  call (tfb_mbsearch L X5).
  1:{ exact Gbt'. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RBd. }
  rewrite <- Emb. clear Gbt'. tr_groups MUm WMm. clear MUm WMm. name_mem m3.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m3) as MUo. pose proof (wmono_refl psegs m3) as WMo.
  call (tfb_optlen L X5 sp last len (buf_ptr L buf) mb).
  1:{ exact GA. } 1:{ exact GD. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact Rol. } 1:{ exact Rsl. } 1:{ exact Rst. } 1:{ exact Rmb. }
  clear GD. tr_groups MUo WMo. clear MUo WMo. rewrite <- E6 in *. name_mem m4.
  assert (ST6 : DST m4 L X6).
  { rewrite E6 in *. constructor; [exact GA| exact GB| exact GC| assumption| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; assumption. }
  clear GA GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  eapply (tfb_emit_all L X6 Rfin c buf last len mb (tfb_SL X6) (tfb_OL X6) d lo m0);
    [exact ST6| exact DZ| | eassumption| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact BEL| exact BI6| exact BOK| exact Rlen| exact Rl| exact Rmb
    | apply tfb_SL_range| apply tfb_OL_range| rewrite Ed; apply tfb_branch_eq| exact SAFE| exact POK| exact ER].
  rewrite E6, E5. change (ds_strm (tfb_X6 (build_tree X4 TB) mb)) with (ds_strm (build_tree X4 TB)). rewrite (k_build_tree _ _ _ keeps_strm). exact ESTRM.
Qed.

Lemma tfb_hi1 : forall (L : dlay) (s X0 X1 X2 X3 X4 X5 X6 Rfin : deflate_state) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> dzs m L (ds_strm s) -> mem_inv psegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  X0 = tfb_X0 s -> X1 = build_tree X0 TL -> X2 = build_tree X1 TD -> X3 = scan_tree X2 TL (ds_l_max_code X2) -> X4 = scan_tree X3 TD (ds_d_max_code X3) ->
  X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last -> BINV 65536 X6 ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b2ec) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ MI RC MU WM FR STK LO AL BEL Hlev Rdt RF E0 E1 E2 E3 E4 E5 Emb E6 Ed HI BI6 POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO. unfold tf_frame in FR. pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  destruct HI as (BTS0 & BTS1 & (Rlm0 & Rlm1) & RLl & RLn & _ & (Rdm0 & Rdm1) & RDl & RDn & _ & BTS4 & (_ & RBd) & Rol & Rsl & Rst & SAFE).
  assert (ES4 : ds_strm X4 = ds_strm X0).
  { rewrite E4, (k_scan_tree _ _ _ keeps_strm), E3, (k_scan_tree _ _ _ keeps_strm), E2, (k_build_tree _ _ _ keeps_strm), E1, (k_build_tree _ _ _ keeps_strm). reflexivity. }
  pose proof (lo_Ss _ LAY) as SEPSs. unfold apart in SEPSs. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & RS).
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MUd. pose proof (wmono_refl psegs m) as WMd.
  pose proof ST as ST'. destruct ST' as [GA _ _ _ Glt _ _ _ _ _ _ _ _ _ _ _].
  assert (RDT : ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573)
    by (eapply ct_readable_rw; [exact Glt| lia| lia| cbn [disjoint_from]; lia]).
  call (tfb_detect L s sp last len (buf_ptr L buf)).
  1:{ exact GA. } 1:{ exact DZ. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Hlev. } 1:{ exact Rdt. } 1:{ exact RDT. } 1:{ exact RF. }
  clear GA Glt RDT DZ. rewrite <- E0 in *. name_mem m1.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _].
  tr_groups MUd WMd. clear MUd WMd.
  assert (ST0 : DST m1 L X0).
  { rewrite E0. unfold tfb_X0. destruct (_ && _);
      (constructor; [exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY]);
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]; constructor; assumption. }
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS.
  unfold tfR. do 3 zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (BT L X0 TL lo).
  1:{ exact ST0. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS0. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST0. rewrite <- E1 in *. rewrite ESP in *. name_mem m3.
  do 3 zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl psegs m4) as WMz.
  call (BT L X1 TD lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. eassumption. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS1. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E2 in *. rewrite ESP in *. name_mem m5.
  match goal with H : DST m5 L X2 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 2748, dl_As L + 2904)] m5) as MUs. pose proof (wmono_refl psegs m5) as WMs.
  pose proof GB as (hB1 & hB2 & hB3 & GBr).
  call (tfb_scan1 L X2 hB1 hB2 hB3).
  1:{ exact Glt. } 1:{ exact Gbt. } 1:{ exact GBr. } 1:{ apply (ln_ltd _ LENS). } 1:{ apply (ln_btf _ LENS). } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact Rlm0. } 1:{ exact Rlm1. } 1:{ exact RLn. } 1:{ exact RLl. }
  clear Glt Gbt GBr. tr_groups MUs WMs. clear MUs WMs. rewrite <- E3 in *. name_mem m6.
  match goal with HL : dlt m6 L X3, HB : dbt m6 L X3 |- _ =>
    pose proof (DST_scanL m6 L X2 (ds_l_max_code X2) X3 E3 GA GB GC GD Gdt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY HL HB) as ST3; clear HL HB end.
  clear GA GB GC GD Gdt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS.
  match goal with H : DST m6 L X3 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748); (dl_As L + 2748, dl_As L + 2904)] m6) as MUs. pose proof (wmono_refl psegs m6) as WMs.
  pose proof GB as (hC1 & hC2 & hC3 & GBr).
  unfold Z_tr_scan1.scR.
  call (tfb_scan2 L X3 hC1 hC2 hC3).
  1:{ exact Gdt. } 1:{ exact Gbt. } 1:{ exact GBr. } 1:{ apply (ln_dtd _ LENS). } 1:{ apply (ln_btf _ LENS). } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact Rdm0. } 1:{ exact Rdm1. } 1:{ exact RDn. } 1:{ exact RDl. }
  clear Gdt Gbt GBr. tr_groups MUs WMs. clear MUs WMs. rewrite <- E4 in *. name_mem m7.
  match goal with HD : ddt m7 L X4, HB : dbt m7 L X4 |- _ =>
    pose proof (DST_scanD m7 L X3 (ds_d_max_code X3) X4 E4 GA GB GC GD Glt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY HD HB) as ST4; clear HD HB end.
  clear GA GB GC GD Glt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS.
  unfold Z_tr_scan2.scR2.
  match goal with HZ : dzs m7 L (ds_strm X0) |- _ =>
    eapply (tfb_hi2 L X4 X5 X6 Rfin (ds_strm X0) buf last len mb d lo m0);
    [exact ST4| exact HZ| exact ES4| eassumption| exact RC| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact AL| exact BEL
    | exact BTS4| exact E5| exact Emb| exact E6| exact Ed| exact RBd| exact Rol| exact Rsl| exact Rst| exact BI6| exact SAFE| exact POK| exact BOK| exact Rlen| exact Rl| exact ER] end.
Qed.

End WithBuildTree.
