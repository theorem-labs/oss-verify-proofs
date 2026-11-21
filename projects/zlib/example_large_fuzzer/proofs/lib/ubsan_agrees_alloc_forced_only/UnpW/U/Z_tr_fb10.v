(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_cb5 Z_tr_st4 Z_tr_fb1 Z_tr_fb2 Z_tr_stored Z_tr_fb3 Z_tr_fb7 Z_tr_fb8 Z_tr_fb9 Z_tr_fbmid Z_tr_scan1 Z_tr_scan2 Z_tr_bt_iface Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab TreeModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefSendTree4 RefFlushBlk12 RefFlushBlk13. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma relro_tfW : forall L lo (sp : word) m0 m, relro_clean m0 -> munch (tfW L lo sp) m0 m -> dlay_ok L -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> relro_clean m.
Proof.
  intros L lo sp m0 m RC MU LAY BEL LE. eapply relro_clean_munch; [exact RC| exact MU|].
  pose proof (lo_s _ LAY) as Bs. pose proof (lo_b _ LAY) as Bb. unfold blk_ok in Bs, Bb. unfold dlay_below in BEL. unfold RELRO_LO, RELRO_HI.
  cbn [disjoint_from]. lia.
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

(* [comment removed for export] *)
Lemma tfb_hi2 : forall (L : dlay) (X4 X5 X6 Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X4 -> dzs m L c -> ds_strm X4 = c -> mem_inv usegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe X4 TB -> X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536) ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 ->
  BINV 65536 X6 ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X6 | 1 => RefFlushBlk12.dyn_ok 65536 last X6 mb | _ => RefFlushBlk13.sto_ok 65536 X6 buf len last end ->
  (d = 1 -> ubsan_dyn X6 mb) ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c4b8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI RC MU WM FR STK LO AL BEL BTS E5 Emb E6 Ed RBd Rol Rsl Rst BI6 SAFE UB POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption). pose proof LAY as LAY'. lay_open LAY'.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  assert (Rmb : 0 <= mb <= 18) by (rewrite Emb; unfold tfb_mb; pose proof (build_bl_tree_loop_range 17 X5 18 ltac:(lia)); lia).
  unfold utfR. zs2. zs2. zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl usegs m1) as WMz.
  call (BT L X4 TB lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ eapply relro_tfW; try eassumption; lia. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_BT_STACK. lia. }
  1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. } 1:{ exact BTS. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. rewrite <- E5 in *. rewrite ESP in *. name_mem m2.
  match goal with H : DST m2 L X5 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof Gbt as Gbt'. unfold dbt, u16arr in Gbt'.
  pose proof (munch_refl [] m2) as MUm. pose proof (wmono_refl usegs m2) as WMm.
  call (tfb_mbsearch L X5 sp last len (buf_ptr L buf)).
  1:{ exact Gbt'. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RBd. }
  rewrite <- Emb. clear Gbt'. tr_groups MUm WMm. clear MUm WMm. name_mem m3.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m3) as MUo. pose proof (wmono_refl usegs m3) as WMo.
  unfold utfR.
  call (tfb_optlen L X5 sp last len (buf_ptr L buf) mb).
  1:{ exact GA. } 1:{ exact GD. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact Rol. } 1:{ exact Rsl. } 1:{ exact Rst. } 1:{ exact Rmb. }
  clear GD. tr_groups MUo WMo. clear MUo WMo. rewrite <- E6 in *. name_mem m4.
  assert (ST6 : DST m4 L X6).
  { rewrite E6 in *. constructor; [exact GA| exact GB| exact GC| assumption| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; assumption. }
  clear GA GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold utfR.
  eapply (tfb_emit_all L X6 Rfin c buf last len mb (tfb_SL X6) (tfb_OL X6) d lo m0);
    [exact ST6| exact DZ| | eassumption| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact BEL| exact BI6| exact BOK| exact Rlen| exact Rl| exact Rmb
    | apply tfb_SL_range| apply tfb_OL_range| rewrite Ed; apply tfb_branch_eq| exact SAFE| exact UB| exact POK| exact ER].
  rewrite E6, E5. change (ds_strm (tfb_X6 (build_tree X4 TB) mb)) with (ds_strm (build_tree X4 TB)). rewrite (k_build_tree _ _ _ keeps_strm). exact ESTRM.
Qed.

(* [comment removed for export] *)
Lemma tfb_hi1 : forall (L : dlay) (s X0 X1 X2 X3 X4 X5 X6 Rfin : deflate_state) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> dzs m L (ds_strm s) -> mem_inv usegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  X0 = tfb_X0 s -> X1 = build_tree X0 TL -> X2 = build_tree X1 TD -> X3 = scan_tree X2 TL (ds_l_max_code X2) -> X4 = scan_tree X3 TD (ds_d_max_code X3) ->
  X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last -> (d = 1 -> ubsan_dyn X6 mb) -> BINV 65536 X6 ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c3d4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ MI RC MU WM FR STK LO AL BEL Hlev Rdt RF E0 E1 E2 E3 E4 E5 Emb E6 Ed HI UB BI6 POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO. unfold tf_frame in FR. pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  destruct HI as (BTS0 & BTS1 & (Rlm0 & Rlm1) & RLl & RLn & _ & (Rdm0 & Rdm1) & RDl & RDn & _ & BTS4 & (_ & RBd) & Rol & Rsl & Rst & SAFE).
  assert (ES4 : ds_strm X4 = ds_strm X0).
  { rewrite E4, (k_scan_tree _ _ _ keeps_strm), E3, (k_scan_tree _ _ _ keeps_strm), E2, (k_build_tree _ _ _ keeps_strm), E1, (k_build_tree _ _ _ keeps_strm). reflexivity. }
  (* [comment removed for export] *)
  pose proof (lo_Ss _ LAY) as SEPSs. unfold apart in SEPSs. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & RS).
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MUd. pose proof (wmono_refl usegs m) as WMd.
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
  (* [comment removed for export] *)
  unfold utfR. zs2. zs2. zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl usegs m2) as WMz.
  call (BT L X0 TL lo).
  1:{ exact ST0. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS0. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST0. rewrite <- E1 in *. rewrite ESP in *. name_mem m3.
  unfold utfR. zs2. zs2. zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl usegs m4) as WMz.
  call (BT L X1 TD lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. eassumption. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS1. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E2 in *. rewrite ESP in *. name_mem m5.
  (* [comment removed for export] *)
  match goal with H : DST m5 L X2 |- _ => pose proof H as ST2; destruct H as [_ GB _ _ _ _ _ _ _ _ _ _ _ _ _ _] end.
  pose proof GB as (hB1 & hB2 & hB3 & GBr). unfold dsB_cells in GBr.
  unfold utfR. zs2. clear GB GBr. zs2. zs2. zs2. name_mem m6.
  pose proof (munch_refl (tfWz L lo sp) m6) as MUz. pose proof (wmono_refl usegs m6) as WMz.
  call (scan_tree_spec L X2 TL (ds_l_max_code X2) lo).
  1:{ exact ST2. } 1:{ eassumption. } 1:{ rewrite ESP. eassumption. } 1:{ rewrite ESP. unfold Z_SC_STACK. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ left; reflexivity. } 1:{ exact Rlm0. } 1:{ cbn [tsize]. exact Rlm1. } 1:{ cbn [tsize]. exact RLn. } 1:{ exact RLl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST2. rewrite <- E3 in *. rewrite ESP in *. name_mem m7.
  match goal with H : DST m7 L X3 |- _ => pose proof H as ST3; destruct H as [_ GB _ _ _ _ _ _ _ _ _ _ _ _ _ _] end.
  pose proof GB as (hC1 & hC2 & hC3 & GBr). unfold dsB_cells in GBr.
  unfold utfR. zs2. clear GB GBr. zs2. zs2. zs2. name_mem m8.
  pose proof (munch_refl (tfWz L lo sp) m8) as MUz. pose proof (wmono_refl usegs m8) as WMz.
  call (scan_tree_spec L X3 TD (ds_d_max_code X3) lo).
  1:{ exact ST3. } 1:{ eassumption. } 1:{ rewrite ESP. eassumption. } 1:{ rewrite ESP. unfold Z_SC_STACK. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ right; reflexivity. } 1:{ exact Rdm0. } 1:{ cbn [tsize]. exact Rdm1. } 1:{ cbn [tsize]. exact RDn. } 1:{ exact RDl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST3. rewrite <- E4 in *. rewrite ESP in *. name_mem m9.
  unfold utfR.
  match goal with HZ : dzs m9 L (ds_strm X0) |- _ =>
    eapply (tfb_hi2 L X4 X5 X6 Rfin (ds_strm X0) buf last len mb d lo m0);
    [eassumption| exact HZ| exact ES4| eassumption| exact RC| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact AL| exact BEL
    | exact BTS4| exact E5| exact Emb| exact E6| exact Ed| exact RBd| exact Rol| exact Rsl| exact Rst| exact BI6| exact SAFE| exact UB| exact POK| exact BOK| exact Rlen| exact Rl| exact ER] end.
Qed.

End WithBuildTree.
