(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the piece "the cell write" of the walk of LLVMFuzzerTestOneInput (0x80c40),
   lib/AU/HPgSegM.v hqu_piece_M3e_cell_stmt (CELL 0x836e4 -> LATCH 0x836b4 / RC 0x83850). Proves no function (kind:
   segment lemma).

   THE WALK. lib/AU/HPgBM3eCellBlk.v bc_blk runs the code from CELL: with n = x->n = |cs| it either leaves at the
   cap test to RC (cap <= n) writing nothing, or stores the cell (channel, param, value) at x->cell[n] through three
   instrumented checks (x's shadow bytes are 0 while x is in scope) and x->n := n + 1, and jumps to LATCH. The model
   moves the same way: one step of Pod/Headamp.v ha_fold over the pair (k, v) whose expect_cell is the cell either
   stops at the cap (the answer is (cs, keys + 1, rf), which x holds) or appends the cell; x's bytes become
   hqu_x_open (cs ++ [cell]) (keys + 1) rf (bce_open_old / bce_open_snoc split both into the same five parts,
   bce_x_write puts the new one together from the old bytes and the four stores).

   SECTION HYPOTHESES: MTL : ameter_laws MT and errno_low : api_env rsegs B (as lib/AU/HPgBM3eBase.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YK1e.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgBM3eBase HPgBM3eRc HPgBM3eCellBlk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= x's bytes, before and after the write ======================================= *)
Definition bce_z0 : byte := Z_to_bv 8 0.

Lemma bce_open_old : forall cs keys rf, (length cs < X_CELLS)%nat ->
hqu_x_open cs keys rf =
  (repeat bce_z0 4 ++ x_cells_bytes cs) ++ (repeat bce_z0 12 ++
  (repeat bce_z0 (12 * (X_CELLS - length cs - 1)) ++
  (Mem.le4 (Z_to_bv 64 (Z.of_nat (length cs))) ++ (Mem.le4 (Z_to_bv 64 keys) ++ Mem.le4 (Z_to_bv 64 rf))))).
Proof.
intros cs keys rf Hl. unfold hqu_x_open, ha_res_bytes, bce_z0.
replace (12 * (X_CELLS - length cs))%nat with (12 + 12 * (X_CELLS - length cs - 1))%nat by (unfold X_CELLS in *; lia).
rewrite repeat_app. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bce_open_snoc : forall cs c keys rf, (length cs < X_CELLS)%nat ->
hqu_x_open (cs ++ [c]) keys rf =
  (repeat bce_z0 4 ++ x_cells_bytes cs) ++ (x_cell_bytes c ++
  (repeat bce_z0 (12 * (X_CELLS - length cs - 1)) ++
  (Mem.le4 (Z_to_bv 64 (Z.of_nat (length cs) + 1)) ++ (Mem.le4 (Z_to_bv 64 keys) ++ Mem.le4 (Z_to_bv 64 rf))))).
Proof.
intros cs c keys rf Hl. unfold hqu_x_open, ha_res_bytes, bce_z0, x_cells_bytes.
rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r, length_app. cbn [length].
replace (X_CELLS - (length cs + 1))%nat with (X_CELLS - length cs - 1)%nat by lia.
replace (Z.of_nat (length cs + 1)) with (Z.of_nat (length cs) + 1) by lia.
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bce_len_pre : forall cs, length (repeat bce_z0 4 ++ x_cells_bytes cs) = (4 + 12 * length cs)%nat.
Proof. intros cs. rewrite length_app, repeat_length, length_x_cells_bytes. reflexivity. Qed.

Lemma bce_small32 : forall z, 0 <= z < 2 ^ 32 -> bv_unsigned (Z_to_bv 64 z) mod 2 ^ 32 = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

Section w. Context {fx : YK11.FPState}.
(* a 4-byte store, read back as the little-endian bytes of the stored value *)
Lemma bce_le4_of_val : forall H mem a z,
val_mem rsegs (mrestrict H mem) a 4 (bv_unsigned (Z_to_bv 64 z) mod 2 ^ 32) ->
hm_bytes rsegs H mem a (Mem.le4 (Z_to_bv 64 z)).
Proof.
intros H mem a z V. apply hm_bytes_of_val in V. unfold Mem.le4.
change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in V. rewrite YK1e.Z_to_le_bytes_mod in V. exact V.
Qed.

(* x's 136 bytes after the cell write, from the bytes before it and the four stores *)
Lemma bce_x_write : forall H mem H' mem' xa cs keys rf ch p val,
(length cs < X_CELLS)%nat -> 0 <= xa -> xa + 136 < 2 ^ 64 ->
hm_bytes rsegs H mem xa (hqu_x_open cs keys rf) ->
val_mem rsegs (mrestrict H' mem') (xa + 4 + 12 * Z.of_nat (length cs)) 4 (bv_unsigned (Z_to_bv 64 ch) mod 2 ^ 32) ->
val_mem rsegs (mrestrict H' mem') (xa + 8 + 12 * Z.of_nat (length cs)) 4 (bv_unsigned (Z_to_bv 64 p) mod 2 ^ 32) ->
val_mem rsegs (mrestrict H' mem') (xa + 12 + 12 * Z.of_nat (length cs)) 4 (bv_unsigned (Z_to_bv 64 val) mod 2 ^ 32) ->
val_mem rsegs (mrestrict H' mem') (xa + 0x7c) 4 (Z.of_nat (length cs) + 1) ->
(forall a, 0 <= a < 2 ^ 64 ->
 ~ (xa + 4 + 12 * Z.of_nat (length cs) <= a < xa + 16 + 12 * Z.of_nat (length cs) \/ xa + 0x7c <= a < xa + 0x80) ->
 aview rsegs H' mem' a = aview rsegs H mem a) ->
hm_bytes rsegs H' mem' xa (hqu_x_open (cs ++ [(ch, p, val)]) keys rf).
Proof.
intros H mem H' mem' xa cs keys rf ch p val Hl Hx0 Hx1 Hold V1 V2 V3 V4 Hkeep.
unfold X_CELLS in Hl.
rewrite bce_open_old in Hold by (unfold X_CELLS; lia). rewrite bce_open_snoc by (unfold X_CELLS; lia).
apply (proj1 (hm_bytes_app rsegs _ _ _ _ _)) in Hold as [HP0 Hold]. rewrite bce_len_pre in Hold.
apply (proj1 (hm_bytes_app rsegs _ _ _ _ _)) in Hold as [_ Hold]. rewrite repeat_length in Hold.
apply (proj1 (hm_bytes_app rsegs _ _ _ _ _)) in Hold as [HZ Hold]. rewrite repeat_length in Hold.
apply (proj1 (hm_bytes_app rsegs _ _ _ _ _)) in Hold as [_ HKR]. rewrite Mem.length_le4 in HKR.
unfold X_CELLS in HZ, HKR |- *.
apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split.
{ apply (hm_bytes_kept rsegs _ _ _ _ _ _ HP0). intros y Hy. rewrite bce_len_pre in Hy. apply Hkeep; lia. }
rewrite bce_len_pre. apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split.
{ cbn [x_cell_bytes]. apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split.
  { replace (xa + Z.of_nat (4 + 12 * length cs)) with (xa + 4 + 12 * Z.of_nat (length cs)) by lia.
    exact (bce_le4_of_val _ _ _ _ V1). }
  rewrite Mem.length_le4. apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split.
  { replace (xa + Z.of_nat (4 + 12 * length cs) + Z.of_nat 4) with (xa + 8 + 12 * Z.of_nat (length cs)) by lia.
    exact (bce_le4_of_val _ _ _ _ V2). }
  rewrite Mem.length_le4.
  replace (xa + Z.of_nat (4 + 12 * length cs) + Z.of_nat 4 + Z.of_nat 4) with (xa + 12 + 12 * Z.of_nat (length cs)) by lia.
  exact (bce_le4_of_val _ _ _ _ V3). }
assert (Hm : length (x_cell_bytes (ch, p, val)) = 12%nat)
  by (cbn [x_cell_bytes]; rewrite !length_app, !Mem.length_le4; reflexivity).
rewrite Hm. apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split.
{ apply (hm_bytes_kept rsegs _ _ _ _ _ _ HZ). intros y Hy. rewrite repeat_length in Hy. apply Hkeep; lia. }
rewrite repeat_length. apply (proj2 (hm_bytes_app rsegs _ _ _ _ _)). split.
{ replace (xa + Z.of_nat (4 + 12 * length cs) + Z.of_nat 12 + Z.of_nat (12 * (10 - length cs - 1))) with (xa + 0x7c) by lia.
  apply bce_le4_of_val. rewrite bce_small32 by lia. exact V4. }
rewrite Mem.length_le4.
apply (hm_bytes_kept rsegs _ _ _ _ _ _ HKR). intros y Hy. rewrite length_app, !Mem.length_le4 in Hy. apply Hkeep; lia.
Qed.
End w.

(* ======================================= the piece ======================================= *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.

(* x's shadow bytes are 0 while x is in scope (the cut pattern hqu_shX) *)
Lemma bce_xsh : forall cx r ev (W2 : world rsegs) mem2, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
hsu_fsh_at rsegs cx W2 mem2 hqu_shX ->
forall a, e_F (x_e rsegs cx) + HQU_XO <= a < e_F (x_e rsegs cx) + HQU_XO + 136 ->
aview rsegs (w_H W2) mem2 (shadow_of_addr SHADOW_OFF a) = Some 0.
Proof.
intros cx r ev W2 mem2 HS Hfsh a Ha.
destruct (br_start B cx r ev HS) as (_ & _ & _ & _ & H32 & H4k & _).
unfold hsu_fsh_at, hd_fsh in Hfsh. unfold HQU_XO in Ha.
assert (HF8 : e_F (x_e rsegs cx) mod 8 = 0).
{ pose proof (Z.div_mod (e_F (x_e rsegs cx)) 32 ltac:(lia)) as Hd.
  symmetry. apply (Z.mod_unique _ 8 (4 * (e_F (x_e rsegs cx) / 32)) 0); [left; lia | lia]. }
assert (Hd8 : e_F (x_e rsegs cx) = 8 * (e_F (x_e rsegs cx) / 8)) by (pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)); lia).
assert (Ha8 : 8 * (a / 8) <= a < 8 * (a / 8) + 8)
  by (pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia).
assert (Hi1 : 88 <= a / 8 - e_F (x_e rsegs cx) / 8 < 105) by lia.
assert (Hsh : shadow_of_addr SHADOW_OFF a = shadow_addr (e_F (x_e rsegs cx)) + (a / 8 - e_F (x_e rsegs cx) / 8))
  by (unfold shadow_of_addr, shadow_addr; lia).
rewrite Hsh. rewrite (Hfsh (a / 8 - e_F (x_e rsegs cx) / 8)
  ltac:(rewrite hqu_shX_len; change (Z.of_nat 116) with 116; lia)).
f_equal. apply hqu_shX_x. lia.
Qed.

Theorem hbe_piece_M3e_cell : @hqu_piece_M3e_cell_stmt fx rc SK rsegs B MT.
Proof.
unfold hqu_piece_M3e_cell_stmt. intros cx POST r ev at0 m HS HL HRC.
unfold hqu_from_CELL. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf HC.
destruct (br_start B cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
destruct (hbe_start_R B cx r ev HS) as (HR0 & HR220 & HR32).
destruct (hbe_seg B cx _ HP) as (_ & _ & _ & _ & _ & _ & HFapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
destruct HC as (Hb & Hat & Hf9 & Hf18 & Hf19 & Hlive & Ham & Hec & Hcv & Hpi & Hkle & Hxat).
pose proof Hb as (Hcore & Hfxk & Hfsh & _).
pose proof Hcore as (HJ & _).
pose proof Hlive as (Hn0 & Hcor & Hprops & Hpst).
pose proof Hpi as (Hv & Hpref & Hsm & Hfold).
pose proof Hxat as (Hxb & Hl10 & Hlcap & Hlk & Hk & Hrf).
pose proof (br_x_geo B cx r ev HS) as (Hx0 & Hx1 & Hx2 & Hx4).
pose proof (br_frame_at B cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
unfold hsu_at_cx, hsu_at in Hat.
pose proof (hbe_at_get _ _ _ _ _ 9 (e_R (x_e rsegs cx)) Hat ltac:(hbe_in)) as R9.
pose proof (hbe_at_get _ _ _ _ _ 20 (e_cap (x_e rsegs cx)) Hat ltac:(hbe_in)) as R20.
pose proof (hbe_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(hbe_in)) as R27.
pose proof (hbe_at_get _ _ _ _ _ 21 ch Hat ltac:(hbe_in)) as R21.
pose proof (hbe_at_get _ _ _ _ _ 16 p Hat ltac:(hbe_in)) as R16.
pose proof (hbe_at_get _ _ _ _ _ 18 val Hat ltac:(hbe_in)) as R18.
pose proof (hbe_at_cell _ _ _ _ _ XR 0x138 (e_F (x_e rsegs cx) + HQU_XO) Hat ltac:(hbe_in)) as C138.
pose proof (hbe_at_cell _ _ _ _ _ XR 0xc0 (hqu_not (e_F (x_e rsegs cx) + HQU_XO + HQU_X_CELL0)) Hat ltac:(hbe_in)) as Cc0.
pose proof (hbe_at_cell _ _ _ _ _ XR 0xc8 (e_F (x_e rsegs cx) + HQU_XO + HQU_X_CELL0) Hat ltac:(hbe_in)) as Cc8.
cbn [hd_xv] in C138, Cc0, Cc8.
rewrite Z.mod_small in C138 by (unfold HQU_XO, T_SEG_STK, ASTACK in *; lia).
rewrite Z.mod_small in Cc8 by (unfold HQU_XO, HQU_X_CELL0, T_SEG_STK, ASTACK in *; lia).
pose proof (br_x_n (w_H W2) mem2 (e_F (x_e rsegs cx) + HQU_XO) cs (keys + 1) rf Hl10 Hxb) as Vn.
pose proof (bce_xsh cx r ev W2 mem2 HS Hfsh) as Hxs.
unfold X_CELLS in Hl10.
eapply SRr_bind.
{ apply (@bc_blk fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 (x_k rsegs cx) regs2 (x_pos rsegs cx)
    (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx) + HQU_XO) (e_cap (x_e rsegs cx)) (Z.of_nat (length cs)) HJ Hown);
  [ rewrite <- HFa; unfold HQU_XO in *; lia
  | rewrite <- HFa; unfold HQU_XO in *; lia
  | unfold HQU_XO in *; pose proof (Z.div_mod (e_F (x_e rsegs cx)) 32 ltac:(lia));
    symmetry; apply (Z.mod_unique _ 8 (4 * (e_F (x_e rsegs cx) / 32) + 0x58) 0); [left; lia | lia]
  | exact R9 | exact R20 | exact R27
  | unfold HQU_XO in *; lia | unfold T_SEG_STK, ASTACK in *; lia | lia | exact Hcap | lia
  | exact C138 | exact Cc0 | exact Cc8 | exact Vn | exact Hxs ]. }
intros W3 c3 _ [(Hge & ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr & Hfr & Hperm & Hio & Hmo & Hkeep & _)
               |(Hlt & ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr & Hfr & Hperm & Hio & Hmo & Hkeep & (V1 & V2 & V3 & V4))].
- (* the cap is reached: RC, nothing written; the fold stops at this pair *)
  cbn [ha_fold] in Hfold. rewrite Hpref, Hec in Hfold. cbn [negb] in Hfold.
  rewrite (proj2 (Z.leb_le _ _) Hge) in Hfold. unfold hqu_fin in Hfold. injection Hfold as E1 E2 E3.
  assert (Hkeep' : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha; apply Hkeep; [exact Ha | intros []]).
  assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (hbe_core_blk B MT MTL cx (hqu_E3 rsegs B cx) (fun _ => False) [10]%bv
      ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr);
    [ intros q Hq; destruct Hq as [->|[->| ->]]; (apply br_not_in_bv; [lia | reflexivity])
    | exact Hfr | exact Hperm | exact Hio | exact Hmo | exact Hkeep | intros a [] ]. }
  apply (HRC fx2 ly3 S3 W3 regs3 mem3 md3).
  split.
  { apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX hqu_shX ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
      HS Hb Hcore3 (fun a Ha _ => Hkeep' a Ha)); [|exact Hfxk].
    unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
    intros i Hi. rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi. apply Hkeep'. lia. }
  split.
  { unfold hsu_at_cx, hsu_at.
    assert (Hat3 : Forall (fun f => hd_at rsegs (w_H W3) mem3 regs3 (x_e rsegs cx) (fst f) (snd f))
      (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx)).
    { assert (Hat0 : Forall (fun f => hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (fst f) (snd f))
        (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx)) by hbe_sub Hat.
      apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat0).
      unfold T_SEG_STK, ASTACK in *.
      intros f Hf. unfold hqu_L_seg, hqu_L_frame, hqu_L_loopc in Hf. cbv zeta in Hf. cbn [app In] in Hf.
      repeat (destruct Hf as [<-|Hf];
        [ cbn [hm_keeps fst hd_xv];
          first [ apply (br_reg_kept _ _ _ _ Hkr); [lia | reflexivity]
                | intros i Hi; apply Hkeep'; lia ] |]).
      destruct Hf. }
    hbe_sub Hat3. }
  split; [exact Hcor|].
  split; [exact (hbe_exp_rc cx r Hlive)|].
  rewrite <- E1, <- E2, <- E3.
  split; [|exact (conj Hl10 (conj Hlcap (conj Hlk (conj Hk Hrf))))].
  apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
  apply (hm_bytes_kept rsegs _ _ _ _ _ _ (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hxb)).
  intros y Hy. apply Hkeep'. rewrite hqu_x_open_len in Hy by (unfold X_CELLS; lia). unfold HQU_XO in *. lia.
- (* the cell is written: LATCH (S (S m)) with the cell appended *)
  cbn [ha_fold] in Hfold. rewrite Hpref, Hec in Hfold. cbn [negb] in Hfold.
  rewrite (proj2 (Z.leb_gt _ _) Hlt) in Hfold.
  assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
  { apply (hbe_core_blk B MT MTL cx (hqu_E3 rsegs B cx)
      (fun a => e_F (x_e rsegs cx) + HQU_XO + 4 + 12 * Z.of_nat (length cs) <= a <
                e_F (x_e rsegs cx) + HQU_XO + 16 + 12 * Z.of_nat (length cs) \/
                e_F (x_e rsegs cx) + HQU_XO + 0x7c <= a < e_F (x_e rsegs cx) + HQU_XO + 0x80) [10; 11; 12; 13]%bv
      ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr);
    [ intros q Hq; destruct Hq as [->|[->| ->]]; (apply br_not_in_bv; [lia | reflexivity])
    | exact Hfr | exact Hperm | exact Hio | exact Hmo | exact Hkeep
    | intros a Ha; apply (hbe_wz_E3 B cx a); left; unfold HQU_XO in *; lia ]. }
  apply (HL fx2 ly3 S3 W3 regs3 mem3 md3 (cs ++ [(ch, p, val)]) (keys + 1) rf).
  split.
  { apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX hqu_shX ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
      HS Hb Hcore3); [| |exact Hfxk].
    - intros a Ha Hw. apply Hkeep; [exact Ha|]. intros Hwr. apply Hw. right. left. unfold HQU_XO in *. lia.
    - unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
      intros i Hi. rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi. apply Hkeep; [lia|].
      unfold HQU_XO in *. lia. }
  split.
  { unfold hsu_at_cx, hsu_at.
    replace (Z.of_nat (S (S m))) with (Z.of_nat m + 2) by lia.
    assert (Hat0 : Forall (fun f => hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (fst f) (snd f))
      (hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2)))
      by hbe_sub Hat.
    apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat0).
    unfold T_SEG_STK, ASTACK in *.
    intros f Hf. unfold hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_t56, hqu_L_body in Hf. cbv zeta in Hf.
    cbn [app In] in Hf.
    repeat (destruct Hf as [<-|Hf];
      [ cbn [hm_keeps fst hd_xv];
        first [ apply (br_reg_kept _ _ _ _ Hkr); [lia | reflexivity]
              | intros i Hi; apply Hkeep; unfold HQU_XO in *; lia ] |]).
    destruct Hf. }
  split; [exact Hf9|]. split; [exact Hf18|]. split; [exact Hf19|]. split; [exact Hlive|].
  split; [unfold hqu_nent; lia|]. split; [lia|].
  split; [|exact Hfold].
  split.
  { apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
    assert (E21 : bv_unsigned (getr regs2 21) = bv_unsigned (Z_to_bv 64 ch)) by (f_equal; exact R21).
    assert (E16 : bv_unsigned (getr regs2 16) = bv_unsigned (Z_to_bv 64 p)) by (f_equal; exact R16).
    assert (E18 : bv_unsigned (getr regs2 18) = bv_unsigned (Z_to_bv 64 val)) by (f_equal; exact R18).
    rewrite E21 in V1. rewrite E16 in V2. rewrite E18 in V3.
    apply (bce_x_write (w_H W2) mem2 (w_H W3) mem3 (e_F (x_e rsegs cx) + HQU_XO) cs (keys + 1) rf ch p val
      ltac:(unfold X_CELLS; lia) ltac:(unfold HQU_XO in *; lia) ltac:(unfold HQU_XO in *; lia)
      (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hxb) V1 V2 V3 V4 Hkeep). }
  rewrite length_app. cbn [length]. unfold X_CELLS.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hk | exact Hrf].
Qed.
Print Assumptions hbe_piece_M3e_cell.
End d.
End c.
Print Assumptions hbe_piece_M3e_cell.
