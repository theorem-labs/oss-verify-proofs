(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_cb4 Z_tr_fbtail.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Ltac name_mem id := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => is_var mm; rename mm into id end.

(* [comment removed for export] *)
Notation tfW L lo sp := [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] (only parsing).

(* [comment removed for export] *)
Notation tfWz L lo sp := [(lo, bv_unsigned sp); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] (only parsing).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition tfR (L : dlay) (sp : word) (last len bufp : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (dl_As L)) (wz last) a0 a1 a2 a3 a4 a5 a6 a7
      (wz len) (wz bufp) (wz (dl_As L + 2047)) (wz (dl_As L + 5912)) (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
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
  ((pcx = 0x1bb74 /\ last <> 0) \/ (pcx = 0x1bbe8 /\ last = 0)) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (dl_As L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (dl_As L + 5912)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pcx) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI ROOM ER [[-> NZ]|[-> ZE]]; unfold tf_frame in *.
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) ZE) in ER. cbn [negb] in ER.
    below_open BEL.
    do 10 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold tfb_post_gen. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite ER. split; [rewrite ESTRM; exact DZ| exact ST].
Qed.
