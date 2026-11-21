(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_init Z_tr_cb3 Z_tr_cb4 Z_tr_st14 Z_tr_fbtail Z_tr_fbpure Z_tr_fb1 Z_tr_fb2 Z_tr_fb5 Z_tr_fb6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel FlushBlockModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefSendTree4 RefFlushBlk12 RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma ct_readable_weaken : forall W m T fc dl n n', ct_readable W m T fc dl n -> n' <= n -> ct_readable W m T fc dl n'.
Proof. intros W m T fc dl n n' H Hn m' MU WM MI i Hi. apply H; [exact MU| exact WM| exact MI| lia]. Qed.

(* [comment removed for export] *)
Lemma tfb_arm_dyn : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len bufp mb lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  RefFlushBlk12.dyn_ok 65536 last X mb -> RefFlushBlk13.post_ok 65536 last (tfb_emit 1 X mb buf len last) ->
  0 <= last <= 1 -> 0 <= mb <= 18 ->
  Rfin = tfb_fin last (tfb_emit 1 X mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz (ds_bi_valid X)) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b838) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL DOK (BIY & ROOMY) Rl Rmb ER.
  unfold Z_TRFB_STACK in LO. rewrite (RefFlushBlk13.tfb_emit_1 buf len last X mb Rmb) in ER, BIY, ROOMY. cbv zeta in ER, BIY, ROOMY.
  unfold RefFlushBlk12.dyn_ok in DOK. cbv zeta in DOK.
  destruct DOK as (BI & HOK & (Rlm0 & Rlm1) & (Rdm0 & Rdm1) & (_ & RBd) & RBf & RLl & RLn & RDl & RDn & SAFE1 & SAFE2 & CBOK & RLf & RDf & _ & Rsn & Rlb).
  pose proof BI as (RBV & RBB & RPD).
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  remember (sbs_run X (hd_calls last X mb)) as X11 eqn:E11.
  assert (T11 : trees8 X11 = trees8 X) by (rewrite E11; apply trees8_sbs_run).
  assert (BI11 : BINV 65536 X11) by (rewrite E11; apply sbs_BINV; assumption).
  remember (send_tree X11 TL (ds_l_max_code X)) as X12 eqn:E12.
  assert (T12 : trees8 X12 = trees8 X) by (rewrite E12, trees8_send_tree; exact T11).
  assert (BI12 : BINV 65536 X12) by (rewrite E12; apply send_tree_BINV; assumption).
  remember (send_tree X12 TD (ds_d_max_code X)) as X13 eqn:E13.
  assert (T13 : trees8 X13 = trees8 X) by (rewrite E13, trees8_send_tree; exact T12).
  assert (ESN : ds_sym_next X13 = ds_sym_next X).
  { rewrite E13, (k_send_tree _ _ _ keeps_sym_next eq_refl), E12, (k_send_tree _ _ _ keeps_sym_next eq_refl), E11. apply (k_sbs_run _ _ _ keeps_sym_next eq_refl). }
  assert (ELB : ds_lit_bufsize X13 = ds_lit_bufsize X).
  { rewrite E13, (k_send_tree _ _ _ keeps_lit_bufsize eq_refl), E12, (k_send_tree _ _ _ keeps_lit_bufsize eq_refl), E11. apply (k_sbs_run _ _ _ keeps_lit_bufsize eq_refl). }
  assert (ES13 : ds_strm X13 = c).
  { rewrite E13, (k_send_tree _ _ _ keeps_strm eq_refl), E12, (k_send_tree _ _ _ keeps_strm eq_refl), E11, (k_sbs_run _ _ _ keeps_strm eq_refl). exact ESTRM. }
  destruct (RefFlushBlk12.trees8_facts _ _ T11) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  destruct (RefFlushBlk12.trees8_facts _ _ T12) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  destruct (RefFlushBlk12.trees8_facts _ _ T13) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  (* [comment removed for export] *)
  pose proof (munch_refl (Wem L) m) as MUw. pose proof (wmono_refl psegs m) as WMw.
  open_DST ST. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. lay_open LAY.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH.
  destruct GB as (hB1 & hB2 & hB3 & GB). unfold dsB_cells in GB.
  assert (RDB : ct_readable (Wem L) m (dl_As L + 2748) (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39)
    by (eapply ct_readable_rw; [exact Gbt| lia| lia| cbn [disjoint_from]; lia]).
  call (tfb_dyn_hdr L X (ds_bl_tree_fc X) (ds_bl_tree_dl X) sp last len bufp mb X11 (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) (wz (ds_bi_buf X)) hB1 hB2 hB3).
  1:{ reflexivity. } 1:{ exact EMH. } 1:{ apply lo16_unsigned_wz. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact GB. } 1:{ exact RDB. }
  1:{ exact Rl. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmb. } 1:{ exact RBd. } 1:{ exact RBV. } 1:{ lia. }
  1:{ rewrite upd4_self. exact HOK. } 1:{ rewrite upd4_self. exact E11. }
  name_mem m1.
  match goal with H : EM m1 _ _ _ _ _ _ |- _ => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
  match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
    destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
  clear GA GD Gpend EMH. tr_groups MUw WMw. clear MUw WMw.
  assert (ST11 : DST m1 L X11).
  { match goal with E : X11 = upd4 _ _ _ _ _ |- _ => rewrite E end.
    constructor; [exact HA| exists hB1, hB2, hB3; exact GB| exact GC| exact HD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact HP| | exact LAY].
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; unfold upd4; dsred; assumption. }
  clear HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead EMf.
  (* [comment removed for export] *)
  unfold blR, tfR. do 4 zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (send_tree_spec L X11 TL (ds_l_max_code X) lo).
  1:{ exact ST11. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ lia. } 1:{ cbn [tsz]. lia. } 1:{ rewrite A5. exact RBf. }
  1:{ cbn [tree_dl]. rewrite A2. exact RLl. } 1:{ cbn [tree_dl tsz]. rewrite A2. exact RLn. }
  1:{ exact BI11. } 1:{ exact SAFE1. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST11. rewrite <- E12 in *. name_mem m3.
  (* [comment removed for export] *)
  do 5 zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl psegs m4) as WMz.
  call (send_tree_spec L X12 TD (ds_d_max_code X) lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ lia. } 1:{ cbn [tsz]. lia. } 1:{ rewrite B5. exact RBf. }
  1:{ cbn [tree_dl]. rewrite B4. exact RDl. } 1:{ cbn [tree_dl tsz]. rewrite B4. exact RDn. }
  1:{ exact BI12. } 1:{ exact SAFE2. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E13 in *. name_mem m5.
  (* [comment removed for export] *)
  do 4 zs2. name_mem m6.
  match goal with H : DST m6 L X13 |- _ => pose proof H as ST13; destruct H as [_ _ _ _ Glt Gdt Gbt _ _ _ _ _ _ _ _ _] end.
  assert (DISJ : disjoint_from (cbW L lo (wz (bv_unsigned sp + -64))) (dl_As L + 212) 2692) by (cbn [disjoint_from]; lia).
  pose proof (tree_readable _ m6 L X13 TL Glt Gdt Gbt DISJ) as RDL. cbn [toff tree_fc tree_dl tsz] in RDL. rewrite C1, C2 in RDL.
  pose proof (tree_readable _ m6 L X13 TD Glt Gdt Gbt DISJ) as RDD. cbn [toff tree_fc tree_dl tsz] in RDD. rewrite C3, C4 in RDD.
  clear Glt Gdt Gbt DISJ.
  pose proof (munch_refl (tfWz L lo sp) m6) as MUz. pose proof (wmono_refl psegs m6) as WMz.
  call (compress_block_spec L X13 (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) (ds_dyn_dtree_fc X) (ds_dyn_dtree_dl X) (dl_As L + 212) (dl_As L + 2504) lo).
  1:{ exact ST13. } 1:{ eassumption. } 1:{ eassumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ eapply ct_readable_weaken; [exact RDL| lia]. } 1:{ eapply ct_readable_weaken; [exact RDD| lia]. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact CBOK. }
  1:{ rewrite ELB. lia. } 1:{ rewrite ESN. lia. } 1:{ rewrite ESN. lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST13. name_mem m7.
  rewrite C1, C2, C3, C4 in ER, BIY, ROOMY.
  remember (compress_block X13 (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) (ds_dyn_dtree_fc X) (ds_dyn_dtree_dl X)) as Y eqn:EY.
  assert (ESY : ds_strm Y = c) by (rewrite EY, (k_compress_block _ _ _ keeps_strm eq_refl); exact ES13).
  zs2. zs2. name_mem m8.
  pose proof (munch_refl (tfWz L lo sp) m8) as MUz. pose proof (wmono_refl psegs m8) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep. name_mem m9.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1bbe8 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1bb74 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
