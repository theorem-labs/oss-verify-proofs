(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model Z_slow_kit Z_fw_model Z_fw_kit Z_fw_slide Z_ukit Zl_defl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition ZL_SH1 : Z := 0x1849c.
Definition ZL_SH1X : Z := 0x184c8.
Definition ZL_SH2 : Z := 0x184f4.
Definition ZL_SH2X : Z := 0x18520.     (* 1.4: the loop-2 exit, before the slid store *)
Definition ZL_SH_TRAP : Z := 0x18534.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shpost1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (a' : arr) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x16 x17 m',
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz 32768) (wz 0) (wz A) (wz 0) (wz 3) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz ZL_SH1X) fc None m' (seg_rom usegs)
    /\ munch [(A, A + 65536)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A (u16s (av16 a' 32768)).

Definition shpost2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (a' : arr) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x16 x17 m',
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz 32768) (wz A) (wz 0) (wz 3) (wz 0) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz ZL_SH2X) fc None m' (seg_rom usegs)
    /\ munch [(A, A + 65536)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A (u16s (av16 a' 32768)).

(* a worker's plain 1.4 P/Zl_slidehash lemma, on usegs: split a cell list's footprint (the slid store's tail) *)
Lemma rw_cells_app_loc : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) <-> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Section LOOPS.

Lemma zl_shloop_h : forall (n : nat) (k : Z) (a : arr) (A : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  k = Z.of_nat (S n) -> k <= 32768 ->
  u8arr usegs m A (u16s (av16 a 32768)) -> arr_len a = 32768 -> (forall i, 0 <= i < 32768 -> 0 <= arr_get a i < 65536) ->
  mem_inv usegs m -> 2 <= A -> A + 65536 < 2^62 ->
  evt usegs (shpost1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc A
                    (slide_hash_loop (Z.to_nat k) a k 32768) m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz 32768) (wz k) (wz (A + 2 * k)) (wz 0) (wz 3) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz ZL_SH1) fc None m (seg_rom usegs)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros until m. intros Hk Kle ARR LEN RNG MI A2 AH. unfold ZL_SH1.
  assert (K1 : 1 <= k) by lia.
  pose proof (av16_zlength a 32768 ltac:(lia)) as L16.
  pose proof (RNG (k - 1) ltac:(lia)) as Rv.
  pose proof (munch_refl [(A, A + 65536)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  gF. gF. zstep.
  replace (wz (A + 2 * k + -2)) with (wz (A + 2 * (k - 1))) by (f_equal; lia).
  ld16 ARR a 32768 A (k - 1) ltac:(exact Rv).
  zs. zstep. zstep. zstep. rewrite (shm_mach (arr_get a (k - 1))) by exact Rv.
  pose proof (shm_range 32768 (arr_get a (k - 1))) as Rs.
  zs.
  st16u ARR a 32768 A (k - 1) (shm 32768 (arr_get a (k - 1))) ltac:(reflexivity).
  rewrite (slide_hash_loop_step k a 32768) by exact K1. cbv zeta.
  name_mem m1.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (k - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (wz (k + -1)) with (wz (k - 1)) by (f_equal; lia).
    eapply evt_mono.
    + eapply (IH (n - 1)%nat ltac:(lia) (k - 1) _ A); [lia| lia| exact ARR| rewrite arr_len_set; exact LEN| | assumption| lia| lia].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Rs| apply RNG; exact Hi].
    + intros ms' (x16' & x17' & m2 & -> & MU2 & WM2 & MI2 & ARR2). exists x16', x17', m2.
      split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
      split; [exact MI2| exact ARR2].
  - (* [comment removed for export] *)
    replace (k - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (wz (A + 2 * (k - 1))) with (wz A) by (f_equal; lia).
    replace (wz (k + -1)) with (wz 0) by (f_equal; lia).
    apply evt_done. unfold shpost1, ZL_SH1X. eexists _, _, m1.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption| exact ARR].
Qed.

Lemma zl_shloop_p : forall (n : nat) (k : Z) (a : arr) (A : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  k = Z.of_nat (S n) -> k <= 32768 ->
  u8arr usegs m A (u16s (av16 a 32768)) -> arr_len a = 32768 -> (forall i, 0 <= i < 32768 -> 0 <= arr_get a i < 65536) ->
  mem_inv usegs m -> 2 <= A -> A + 65536 < 2^62 ->
  evt usegs (shpost2 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc A
                    (slide_hash_loop (Z.to_nat k) a k 32768) m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz 32768) (wz (A + 2 * k)) (wz 0) (wz 3) (wz k) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz ZL_SH2) fc None m (seg_rom usegs)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros until m. intros Hk Kle ARR LEN RNG MI A2 AH. unfold ZL_SH2.
  assert (K1 : 1 <= k) by lia.
  pose proof (av16_zlength a 32768 ltac:(lia)) as L16.
  pose proof (RNG (k - 1) ltac:(lia)) as Rv.
  pose proof (munch_refl [(A, A + 65536)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  gF. gF. zstep.
  replace (wz (A + 2 * k + -2)) with (wz (A + 2 * (k - 1))) by (f_equal; lia).
  ld16 ARR a 32768 A (k - 1) ltac:(exact Rv).
  zs. zstep. zstep. zstep. rewrite (shm_mach (arr_get a (k - 1))) by exact Rv.
  pose proof (shm_range 32768 (arr_get a (k - 1))) as Rs.
  zs.
  st16u ARR a 32768 A (k - 1) (shm 32768 (arr_get a (k - 1))) ltac:(reflexivity).
  rewrite (slide_hash_loop_step k a 32768) by exact K1. cbv zeta.
  name_mem m1.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (k - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (wz (k + -1)) with (wz (k - 1)) by (f_equal; lia).
    eapply evt_mono.
    + eapply (IH (n - 1)%nat ltac:(lia) (k - 1) _ A); [lia| lia| exact ARR| rewrite arr_len_set; exact LEN| | assumption| lia| lia].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Rs| apply RNG; exact Hi].
    + intros ms' (x16' & x17' & m2 & -> & MU2 & WM2 & MI2 & ARR2). exists x16', x17', m2.
      split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
      split; [exact MI2| exact ARR2].
  - (* [comment removed for export] *)
    replace (k - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (wz (A + 2 * (k - 1))) with (wz A) by (f_equal; lia).
    replace (wz (k + -1)) with (wz 0) by (f_equal; lia).
    apply evt_done. unfold shpost2, ZL_SH2X. eexists _, _, m1.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption| exact ARR].
Qed.
End LOOPS.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma slide_hash_spec : slide_hash_stmt.
Proof.
  unfold slide_hash_stmt. intros until m. intros ST MI WS HS RH RP ->. unfold ZL_SLIDE_HASH.
  pose proof (munch_refl [(dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  open_DST ST. lay_open LAY. open_A GA.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof (ln_head _ LENS) as Whl. pose proof (ln_prev _ LENS) as Wpl.
  assert (AH2 : 2 <= dl_Ah L /\ dl_Ah L mod 2 = 0) by (pose proof (lo_h _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
  assert (AP2 : 2 <= dl_Ap L /\ dl_Ap L mod 2 = 0) by (pose proof (lo_p _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  zstep. al8 (dl_As L). gF.
  zs. zs. rewrite HS. zstep. zstep. gF. zstep. zstep. zstep. gX.
  zs. rewrite WS. zstep. rewrite (land1_mod2 (dl_Ah L) (proj2 AH2)). zstep.
  replace (wz (65536 + dl_Ah L)) with (wz (dl_Ah L + 2 * 32768)) by (f_equal; lia).
  open_u16 Ghead. open_u16 Gprev.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (zl_shloop_h (Z.to_nat 32767) 32768 (ds_head d) (dl_Ah L)); [lia| lia| exact Ghead| exact Whl| exact RH| assumption| lia| lia]
                    | clear Ghead; post_call segs mm ] end.
  name_mem mA. rename POST into HEAD. remember (slide_hash_loop (Z.to_nat 32768) (ds_head d) 32768 32768) as hd eqn:Ehd.
  assert (LNH : arr_len hd = 32768) by (rewrite Ehd, slide_hash_loop_len; exact Whl).
  pose proof (av16_zlength hd 32768 ltac:(lia)) as L16h.
  apply box in Ehd.
  (* [comment removed for export] *)
  zs. zstep. zstep. gF. zstep. zstep. zstep. gX. zstep. rewrite (land1_mod2 (dl_Ap L) (proj2 AP2)). zstep. zstep.
  replace (wz (65536 + dl_Ap L)) with (wz (dl_Ap L + 2 * 32768)) by (f_equal; lia).
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (zl_shloop_p (Z.to_nat 32767) 32768 (ds_prev d) (dl_Ap L)); [lia| lia| exact Gprev| exact Wpl| exact RP| assumption| lia| lia]
                    | clear Gprev; post_call segs mm ] end.
  name_mem mB. rename POST into PREV. remember (slide_hash_loop (Z.to_nat 32768) (ds_prev d) 32768 32768) as pv eqn:Epv.
  assert (LNP : arr_len pv = 32768) by (rewrite Epv, slide_hash_loop_len; exact Wpl).
  pose proof (av16_zlength pv 32768 ltac:(lia)) as L16p.
  apply box in Epv.
  (* [comment removed for export] *)
  zstep. zstep. zstep. tr_groups MUf WMf.
  assert (KEEP : munch [(dl_Ap L, dl_Ap L + 2 * 32768); (dl_Ah L, dl_Ah L + 2 * 32768); (dl_As L + 5960, dl_As L + 5964)] m mB /\ True)
    by (split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia | exact I]).
  tr_groups MU WM.
  clear MU.
  assert (SOK4 : store_ok usegs mB (wz (dl_As L + 5960)) 4 = true)
    by (destruct GD as (h0 & h1 & h2 & h3 & h4 & RCD); unfold dsD_cells in RCD; destruct RCD as [_ WR]; replace (dl_As L + 5960) with ((dl_As L + 5881) + 79) by lia; eapply wr_at_store_ok; [exact WR| (cbn [cells_size csize]; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn; lia)| (cbn [cells_size csize]; rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn; lia)]).
  destruct GD as (h0 & h1 & h2 & h3 & h4 & RCD). unfold dsD_cells in RCD.
  change (rw_cells usegs mB (dl_As L + 5881) ([CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize d)); C4 (wz (ds_lit_bufsize d)); C4 (wz (ds_sym_next d)); C4 (wz (ds_sym_end d)); CB 4 h1; C8 (wz (ds_opt_len d)); C8 (wz (ds_static_len d)); C4 (wz (ds_matches d)); C4 (wz (ds_insert d)); C2 (wz (ds_bi_buf d)); CB 2 h2; C4 (wz (ds_bi_valid d)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water d))] ++ [CB 4 h4; C4 (wz 0)])) in RCD.
  apply rw_cells_app_loc in RCD. destruct RCD as [RC1 RC2].
  assert (RC2n : rw_cells usegs mB (dl_As L + 5960) [CB 4 h4; C4 (wz 0)]).
  { replace (dl_As L + 5960) with (dl_As L + 5881 + Z.of_nat (cells_size [CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize d)); C4 (wz (ds_lit_bufsize d)); C4 (wz (ds_sym_next d)); C4 (wz (ds_sym_end d)); CB 4 h1; C8 (wz (ds_opt_len d)); C8 (wz (ds_static_len d)); C4 (wz (ds_matches d)); C4 (wz (ds_insert d)); C2 (wz (ds_bi_buf d)); CB 2 h2; C4 (wz (ds_bi_valid d)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water d))])) by (cbn [cells_size csize]; lia). exact RC2. }
  repeat match goal with H : munch _ _ mB |- _ => clear H end.
  destruct KEEP as [MU3 _].
  pose proof (munch_refl [(dl_As L + 5960, dl_As L + 5964)] mB) as MSB.
  pose proof (wmono_refl usegs mB) as WMB.
  zs. zstep.
  pose proof (agree_on_of_munch _ _ _ (dl_As L) 212 MSB WMB ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; slia)) as AGA.
  pose proof (agree_on_of_munch _ _ _ (dl_Ap L) 65536 MSB WMB ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; slia)) as AGP.
  pose proof (agree_on_of_munch _ _ _ (dl_Ah L) 65536 MSB WMB ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; slia)) as AGH.
  pose proof (agree_on_of_munch _ _ _ (dl_As L + 5881) 79 MSB WMB ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; slia)) as AGD.
  assert (DF : rw_cells usegs m0 (dl_As L + 5881) ([CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize d)); C4 (wz (ds_lit_bufsize d)); C4 (wz (ds_sym_next d)); C4 (wz (ds_sym_end d)); CB 4 h1; C8 (wz (ds_opt_len d)); C8 (wz (ds_static_len d)); C4 (wz (ds_matches d)); C4 (wz (ds_insert d)); C2 (wz (ds_bi_buf d)); CB 2 h2; C4 (wz (ds_bi_valid d)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water d))] ++ [CB 4 (le4 (wz 1)); C4 (wz 0)])).
  { apply rw_cells_app_loc. split.
    - exact RC1.
    - replace (dl_As L + 5881 + Z.of_nat (cells_size [CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize d)); C4 (wz (ds_lit_bufsize d)); C4 (wz (ds_sym_next d)); C4 (wz (ds_sym_end d)); CB 4 h1; C8 (wz (ds_opt_len d)); C8 (wz (ds_static_len d)); C4 (wz (ds_matches d)); C4 (wz (ds_insert d)); C2 (wz (ds_bi_buf d)); CB 2 h2; C4 (wz (ds_bi_valid d)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water d))])) with (dl_As L + 5960) by (cbn [cells_size csize]; lia).
      eapply rw_cells_sim; [exact RC2n| cells_sim_tac]. }
  try replace (dl_As L + 5960 + 4) with (dl_As L + 5964) in MU3 by lia.
  apply evt_done. unfold slide_hash_post. do 15 eexists. eexists.
  split; [reflexivity|]. split; [exact MU3|]. split; [exact WM|].
  split; [first [assumption | exact (mem_inv_wmono usegs mB _ MI WMB) | exact (mem_inv_wmono usegs mB _ MI WM)]|].
  apply unbox in Ehd. apply unbox in Epv.
  unfold slide_hash. cbv zeta. rewrite HS, WS, <- Ehd. dsred. rewrite <- Epv.
  constructor.
  + exists hA1, hA2, hA3, hA4, hA5. unfold dsA_cells. dsred.
    exact GA.
  + eapply dsB_munch; [exact GB| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply dsC_munch; [exact GC| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + do 5 eexists; exact DF.
  + eapply dlt_munch; [exact Glt| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply ddt_munch; [exact Gdt| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply dbt_munch; [exact Gbt| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply dblc_munch; [exact Gblc| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply dheap_munch; [exact Gheap| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply ddep_munch; [exact Gdep| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + eapply dwin_munch; [exact Gwin| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + unfold dprev, u16arr. dsred. exact PREV.
  + unfold dhead, u16arr. dsred. exact HEAD.
  + eapply dpend_munch; [exact Gpend| exact MSB| exact WMB| cbn [disjoint_from]; slia].
  + destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
    constructor; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact LNP|exact LNH|exact l13].
  + exact LAY.
Qed.
