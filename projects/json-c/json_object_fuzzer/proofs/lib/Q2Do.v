(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QRUw QnCn Q7UD Qhd4 Qwm6 QlKV QsKa Q30W Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlAdd.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo a arr size d : Z) (ps : list Z) (T : TSet).

Definition array_list_add_A_entry : Z := 0xa0834.
Definition al_add_costB : Z := 256 * size + 512.

Definition array_list_add_A_post (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (arr' size' : Z) (B' : bud),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bD B0 <= bD B' /\
HEAPAx A' ((a, AL_SZ) :: (arr', 8 * size') :: LB) LM FRS B' m' md' /\
( (r = 2^64 - 1 /\ arr' = arr /\ size' = size /\ size <= Z.of_nat (length ps) + 1 /\ bB B0 - al_add_costB <= bB B' /\ alist asegs A4F m' [(a, AL_SZ); (arr, 8 * size)] a ps)
\/ (r = 0 /\ alist asegs A4F m' [(a, AL_SZ); (arr', 8 * size')] a (ps ++ [d])
/\ ((size' = size /\ arr' = arr /\ Z.of_nat (length ps) + 1 < size /\ bB B0 <= bB B')
\/ (size' = 2 * size /\ size <= Z.of_nat (length ps) + 1 /\ bB B0 - al_add_costB <= bB B'))) ).

Definition add_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma al_add_storeA :
forall (x1 t0 t1 t2 x9 a2 a3 a4 a5 a6 a7 x19 x23 x25 x26 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (r size' : Z) (junk : list byte) (errv : word),
HEAPAx A ((a, AL_SZ) :: (r, 8 * size') :: LB) LM FRS B m md ->
al_hdr asegs A4F m a r (Z.of_nat (length ps)) size' ->
u64arr asegs m r (wl ps) ->
al_tail asegs m r size' (length ps) junk ->
Z.of_nat (length ps) + 1 <= size' -> (1 <= size' /\ 8 * size' < 2^64) ->
((size' = size /\ r = arr /\ Z.of_nat (length ps) + 1 < size /\ bB B0 <= bB B) \/ (size' = 2 * size /\ size <= Z.of_nat (length ps) + 1 /\ bB B0 - al_add_costB <= bB B)) ->
0 <= d < 2^64 ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -96 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
add_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bD B0 <= bD B ->
(forall ms' md' A', array_list_add_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (a + 8)) x9 (Z_to_bv 64 a) (Z_to_bv 64 d) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 16)) x19 (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (Z.of_nat (length ps))) x23
(Z_to_bv 64 (a / 8 + 2147450882)) x25 x26 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0924) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP HDR ARR JK ROOM Hsz CASES Hd ST LO LOS SPA HT FR ERR RA VM0 HPR BD K.
unfold al_hdr in HDR. unfold al_tail in JK. unfold add_frameA in FR.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP r (8 * size') Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 r (8 * size') HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 r (8 * size') HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0r.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 r (8 * size') HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP3r.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r (8 * size') HP ltac:(right; left; reflexivity)) as SHr. unfold shad in SHr.
a4l.
pose proof (u64arr_bound asegs m r (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
assert (LJ : length junk = Z.to_nat (8 * (size' - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).

apply (rw_cells_CB_cut asegs m _ _ junk 8) in JK; [|lia]. destruct JK as [J1 J2]. clear LJ.

pose proof (ov_read1_of_ro asegs _ _ _ (shadow_granule0 asegs m (r / 8 + 2147450880) (8 * size') (Z.of_nat (length ps)) ltac:(lia) ltac:(lia) SHr)) as HR.
clear SHr.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (a, a + 32); (r, r + 8 * size')] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step.
step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step.
step. step. sh_norm.
replace ((r + Z.of_nat (length ps) * 8) / 8 + 2147450880) with (r / 8 + 2147450880 + Z.of_nat (length ps)) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR. step. if_false.
assert (SOK : store_ok asegs m (wa (r + Z.of_nat (length ps) * 8)) 8 = true).
{ destruct J1 as [_ W]. cbn [cells_size csize Nat.add] in W.
replace (r + Z.of_nat (length ps) * 8) with (r + 8 * Z.of_nat (length ps) + 0) by lia.
eapply wr_at_store_ok; [exact W | lia | cbn; lia]. }
step.
pose proof (rw_cells_write asegs m _ _ 0 _ (C8 (Z_to_bv 64 d)) J1 eq_refl eq_refl I) as J1'.
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub cbytes] in J1'.
replace (r + 8 * Z.of_nat (length ps) + Z.of_nat 0) with (r + 8 * Z.of_nat (length ps)) in J1' by lia.
clear J1.
change (Z_to_bv 64 (r + Z.of_nat (length ps) * 8)) with (wa (r + Z.of_nat (length ps) * 8)).
replace (wa (r + Z.of_nat (length ps) * 8)) with (wa (r + 8 * Z.of_nat (length ps))) by (unfold wa; f_equal; lia).
store_done.
step. rewrite ?zxb_zero. step. if_false.
step.
step. step. step.
do 15 step.
evt_done5. apply K. unfold array_list_add_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 0, errv, r, size', B end.
split; [| split; [exact VM0 | split; [| split; [ | split; [ eassumption | split; [exact BD | split; [ | right]]]]]]].
- apply ret_statew_same.
- release_frame FR ST (bv_unsigned sp). exact ST.
- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP].
- eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
- split; [reflexivity|]. split; [| exact CASES].
eapply alist_close. split; [| split; [| split; [| split; [rewrite length_app; cbn [length]; lia | exact Hsz]]]].
+ unfold al_hdr. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
replace (Z.of_nat (length ps) + Z.pos (Pos.of_succ_nat 0)) with (Z.of_nat (length ps) + 1) by lia. eassumption.
+ eapply u64arr_snoc; [eassumption|]. eassumption.
+ unfold al_tail. rewrite length_app. cbn [length].
replace (r + 8 * Z.of_nat (length ps + 1)) with (r + 8 * Z.of_nat (length ps) + Z.of_nat 8) by lia.
replace (Z.to_nat (8 * (size' - Z.of_nat (length ps + 1)))) with (Z.to_nat (8 * (size' - Z.of_nat (length ps))) - 8)%nat by lia.
exact J2.
Qed.

Lemma al_add_growA :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (junk : list byte) (errv : word),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m md ->
al_hdr asegs A4F m a arr (Z.of_nat (length ps)) size ->
u64arr asegs m arr (wl ps) ->
al_tail asegs m arr size (length ps) junk ->
Z.of_nat (length ps) <= size -> (1 <= size /\ 8 * size < 2^64) -> size <= Z.of_nat (length ps) + 1 -> Z.of_nat (length ps) + 1 < 2^28 ->
0 <= d < 2^64 ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
add_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
al_add_costB <= bB B0 -> 0 <= bD B0 ->
(forall ms' md' A', array_list_add_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (a + 8)) (Z_to_bv 64 (-1)) (Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 size) a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 16)) s3 (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (Z.of_nat (length ps))) (Z_to_bv 64 (Z.of_nat (length ps) + 1))
(Z_to_bv 64 (a / 8 + 2147450882)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa08b4) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP HDR ARR JK Hlen Hsz GROWS Hlen28 Hd ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD K.
unfold al_hdr in HDR. unfold add_frameA in FR.
unfold_consts. unfold al_add_costB in BB. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> arr).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 arr (8 * size) HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
a4l.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
assert (LJ' : Z.of_nat (length junk) = 8 * (size - Z.of_nat (length ps))) by (rewrite LJ; lia).
pose proof (al_arr_join asegs m arr size ps junk ARR JK Hlen) as COMB. clear LJ.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (a, a + 32)] m) as MU.
stash COMB.
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite (unsigned_lit size) by lia. rewrite (Z.shiftl_mul_pow2 size 1) by lia. change (2^1) with 2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut with (P := eq (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6434400) t0 t1 t2
(Z_to_bv 64 (a + 8)) (Z_to_bv 64 (-1)) (Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 size) (Z_to_bv 64 (size * 2)) a4 a5 a6 a7
(Z_to_bv 64 (a + 16)) s3 (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.of_nat (length ps))) (Z_to_bv 64 (Z.of_nat (length ps) + 1))
(Z_to_bv 64 (a / 8 + 2147450882)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa08c0) fc None mc (seg_rom asegs)))
end.
{ destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) (size * 2)) as [LT|GE].
- step. if_truex. apply evt_done. reflexivity.
- step. if_falsex. step. apply evt_done. replace (size * 2) with (Z.of_nat (length ps) + 1) by lia. reflexivity. }
intros ms' <-.
step. step. step. if_falsex. step.
step. rewrite (unsigned_lit (size * 2)) by lia. rewrite (Z.shiftr_div_pow2 (size * 2) 61) by lia.
rewrite (Z.div_small (size * 2) (2^61)) by lia.
step. if_false.
step.
asan_chk0.
step. step.
step. rewrite (unsigned_lit (size * 2)) by lia. rewrite (Z.shiftl_mul_pow2 (size * 2) 3) by lia. change (2^3) with 8.
step.

unstash COMB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in COMB; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
clear SHa.
alloc_callA (hiA_realloc A4L HIx) blk arr uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (right; left; reflexivity).
all: try exact COMB.
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [left; lia | unfold a4_straces; repeat first [left; reflexivity | right] | lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 ERR2 OUT2. open_ret RS. a4l.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & _ & HPR2 & HP2) | (Hr & HPR2 & [junk' BLK] & HP2)].
-
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in COMB; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
a4l.
destruct (al_arr_split asegs m2 arr size size ps junk [] COMB ltac:(apply Nat2Z.inj; rewrite LJ', Z2Nat.id by lia; reflexivity) ltac:(lia)) as [ARR2 JK2].
clear MU WM MI ST COMB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold array_list_add_A_post.
exists m2, (2^64 - 1), e2, arr, size, (charge B0 (16 * (size * 2 * 8) + 512) (uw_cost UWptr)).
split; [| split; [eapply model_vm_only_trans; [exact VM0 | exact VM2] | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [exact HP2| left]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ cbn [bD charge uw_cost]. lia.
+ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact GROWS|]. split; [unfold al_add_costB; cbn [bB charge]; lia|].
rewrite app_nil_r in JK2. eapply alist_close. split; [exact HDR | split; [exact ARR2 | split; [exact JK2 | lia]]].
-
assert (LO8 : length (u64s (wl ps) ++ junk) = Z.to_nat (8 * size)).
{ rewrite length_app, u64s_length, wl_length. lia. }
rewrite LO8, Z.min_r, firstn_all2 in BLK by (rewrite ?LO8; lia). clear LO8.
replace (size * 2 * 8) with (8 * (2 * size)) in BLK, HP2 by lia.
destruct (al_arr_split asegs m2 r size (2 * size) ps junk junk' BLK ltac:(apply Nat2Z.inj; rewrite LJ', Z2Nat.id by lia; reflexivity) ltac:(lia)) as [ARR2 JK2]. clear BLK. unfold al_tail in JK2.
assert (HP2' : HEAPAx A2 ((a, 32) :: (r, 8 * (2 * size)) :: LB) LM FRS (charge B0 (16 * (8 * (2 * size)) + 512) (uw_cost UWptr)) m2 md2).
{ exact (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP2 (perm_swap (a, 32) (r, 8 * (2 * size)) LB) (Permutation_refl LM) (Permutation_refl FRS)). }
clear HP2.
blk_factsA A4L HIx HP2' r (8 * (2 * size)) Hqal Hqlo Hqhi Hqimg.
assert (Hne2 : a <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2') as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 r (8 * (2 * size)) HP2' ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne2) as Hrdj.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM MI ST COMB.
shadow_nowA A4L HIx HP2' a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0'.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3'.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2') as MI. a4l.
pose proof (wl_length ps) as WL.
pose proof (munch_refl [(a, a + 32)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2'.
step. if_falsex.
step.
step. rewrite ?zxb_zero. step. if_false.
step.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.
replace (size * 2) with (2 * size) in * by lia.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
evt_done5.
eapply (al_add_storeA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 md2 A2 _ r (2 * size) (junk ++ junk') e2);
first [exact ST2 | exact SPA | exact HT | exact RA | exact K | idtac].
all: lazymatch goal with
| |- HEAPA _ _ _ _ _ _ _ _ _ =>
eapply (heapA_client_frame A4L HIx); [exact HP2' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2' MU); solve_frameW_withA HP2' | exact WM | exact MI]
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; assumption
| |- u64arr _ _ _ _ => exact ARR2
| |- al_tail _ _ _ _ _ _ => unfold al_tail; exact JK2
| |- add_frameA _ => unfold add_frameA; assumption
| |- rw_cells _ _ _ _ => assumption
| |- model_vm_only (cfg_model _) (cfg_model _) => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP2' | intros bb Hbb0; right; right; exact Hbb0 | clia | solve_clientWA A4L HIx HP2']
| |- _ \/ _ => right; split; [reflexivity | split; [lia | unfold al_add_costB; cbn [bB charge]; lia]]
| |- bD _ <= _ => cbn [bD charge uw_cost]; lia
| |- _ => clia
end.
Qed.

Lemma array_list_add_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m0 md0 ->
alist asegs A4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps -> Z.of_nat (length ps) + 1 < 2^28 ->
0 <= d < 2^64 ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 d ->
(size <= Z.of_nat (length ps) + 1 -> al_add_costB <= bB B0) -> 0 <= bD B0 ->
(forall ms' md' A', array_list_add_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_add_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP AL Hlen28 Hd ST LO LOS SPA HT ERR RA A0 A1 BB BD K.
destruct (alist_openx asegs A4F m0 a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR.
unfold_consts. unfold A_SB, A_TP, A_ERRNO, array_list_add_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
shadow_nowA A4L HIx HP a 32 SHa.
a4l.
pose proof (u64arr_bound asegs m0 arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m0) as MU.
apply slots_of_u64arr in ARR. stash ARR. stash JK.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1.
carve_frame 96%nat ST.
do 13 step.
step. step. step.
step.
asan_chkA.
step. step. step.
step. if_falsex.
step.
asan_chkA.
step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LB) LM FRS B0 m1 md0) by heap_nowA A4L HIx HP MU WM MI.
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP]. }
unstash ARR. unstash JK.
eapply (rw_cells_transport asegs _ m0 m1) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia].
eapply (rw_cells_transport asegs _ m0 m1) in JK; [| exact MU | exact WM | unfold al_tail; cbn [disjoint_from]; simpl_sizes; lia].
apply u64arr_of_slots in ARR.
step.
destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) size) as [LT|GE].
-
if_truex.
evt_done5.
eapply (al_add_storeA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A B0 arr size junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; assumption
| |- add_frameA _ => unfold add_frameA; assumption
| |- rw_cells _ _ _ _ => assumption
| |- _ \/ _ => left; split; [reflexivity | split; [reflexivity | split; [lia | lia]]]
| |- bD _ <= _ => lia
| |- _ => clia
end.
-
specialize (BB GE).
if_falsex.
evt_done5.
eapply (al_add_growA _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; assumption
| |- add_frameA _ => unfold add_frameA; assumption
| |- rw_cells _ _ _ _ => assumption
| |- _ <= bB _ => exact BB
| |- _ <= bD _ => exact BD
| |- _ => clia
end.
Qed.
End AAlAdd.
End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition array_list_set_idx_A_entry : Z := 0xa07ac.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition array_list_set_idx_A_post (a arr size : Z) (ps : list Z) (idx d : Z) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (a1 a3 a4 a5 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if idx <? Z.of_nat (length ps) then 0 else 2^64 - 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(arr, arr + 8 * size); (bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ alist asegs A4F m' [(a, AL_SZ); (arr, 8 * size)] a (if idx <? Z.of_nat (length ps) then upd ps (Z.to_nat idx) d else ps)
/\ stk asegs m' lo (bv_unsigned sp).

Lemma array_list_set_idx_A : forall (a0 a1 a3 a4 a5 : word) (m : word -> option byte) (lo sbcell a arr size : Z) (ps : list Z) (idx d : Z),
small_pre sp m lo sbcell ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 d -> 0 <= idx < 2^64 ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (array_list_set_idx_A_post a arr size ps idx d m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_set_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until d. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) AL SEP A0 A1 A2 Hi (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa SHr.
destruct (alist_openx asegs A4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz). unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (u64arr_bound asegs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
unfold array_list_set_idx_A_entry, array_list_set_idx_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0 a1 a2.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply slots_of_u64arr in ARR. stash SHr. stash ARR.
carve_frame 16%nat ST.
step. step.
step. step. step.
step.
asan_chkA.
step.
step.
destruct (Z.ltb_spec idx (Z.of_nat (length ps))) as [LT|GE].
- if_falsex.
asan_chk0.
step.
step. step.
rewrite (unsigned_lit idx) by lia. rewrite (Z.shiftl_mul_pow2 idx 3) by lia. change (2^3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (Z_to_bv 64 (arr / 8 + 2147450880 + idx)) 1 = Some [Z_to_bv 8 0])
by (unstash SHr; apply ov_read1_of_ro; eapply (ro_cells_transport asegs _ m mc); [| exact MU | cbn; lia];
apply (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) idx); [lia | lia | exact SHr])
end.
step. step. sh_norm.
replace ((arr + idx * 8) / 8 + 2147450880) with (arr / 8 + 2147450880 + idx) by (Z.div_mod_to_equations; lia).
step. rewrite ?zxb_zero. clear HR.
step. if_false.
unstash ARR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
apply u64arr_of_slots in ARR;
pose proof (u64arr_store_ok asegs mc arr (wl ps) idx (wa (arr + idx * 8)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;

assert (MU2 : munch [(arr, arr + 8 * size); (bv_unsigned sp - 16, bv_unsigned sp)] m mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia)
end.
clear MU. rename MU2 into MU.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc arr (wl ps) idx (Z_to_bv 64 d) ARR ltac:(lia)) as ARR' end.
replace (8 * idx) with (idx * 8) in ARR' by lia. rewrite <- wl_upd in ARR'.
clear ARR. store_done.
step.
step.
step. step. step.
apply evt_done. eexists _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split.
+ eapply alist_close. split; [| split; [exact ARR' | split; [| split; [rewrite upd_length; exact Hlen | exact Hsz]]]].
* unfold al_hdr. rewrite upd_length. assumption.
* unfold al_tail. rewrite upd_length. exact JK.
+ release_frame FR ST (bv_unsigned sp). exact ST.
- if_truex.
step.
step.
step. step. step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
unstash ARR.
apply evt_done. eexists _, _, _, _, _. split; [reflexivity|]. split; [| split; [exact WM|]].
{ eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [assumption|].
split.
+ lazymatch goal with |- alist _ _ ?mf _ _ _ =>
eapply (rw_cells_transport asegs _ m mf) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia] end.
eapply alist_close. split; [| split; [apply u64arr_of_slots; exact ARR | split; [exact JK | split; [exact Hlen | exact Hsz]]]].
unfold al_hdr. assumption.
+ release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTKj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import QnCn.Mq0. Import QTKj.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlShrink.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo a arr size : Z) (ps : list Z) (T : TSet).

Definition array_list_shrink_A_entry : Z := 0xa064c.
Definition al_shrink_costB : Z := 16 * (8 * Z.max (Z.of_nat (length ps)) 1) + 512.

Definition array_list_shrink_A_post (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (arr' size' : Z) (B' : bud),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B0 - (if Z.of_nat (length ps) =? size then 0 else al_shrink_costB) <= bB B' /\ bD B0 <= bD B' /\
HEAPAx A' ((a, AL_SZ) :: (arr', 8 * size') :: LB) LM FRS B' m' md' /\
alist asegs A4F m' [(a, AL_SZ); (arr', 8 * size')] a ps /\
( (r = 2^64 - 1 /\ arr' = arr /\ size' = size)
\/ (r = 0 /\ size' = Z.max (Z.of_nat (length ps)) 1) ).

Lemma array_list_shrink_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m0 md0 ->
alist asegs A4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps -> Z.of_nat (length ps) < 2^28 ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 0 ->
(Z.of_nat (length ps) <> size -> al_shrink_costB <= bB B0) -> 0 <= bD B0 ->
(forall ms' md' A', array_list_shrink_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_shrink_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP AL Hlen28 ST LO LOS SPA HT ERR RA A0 A1 BB BD K.
destruct (alist_openx asegs A4F m0 a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR.
unfold_consts. unfold al_shrink_costB in BB. unfold A_SB, A_TP, A_ERRNO, array_list_shrink_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> arr).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 arr (8 * size) HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
a4l.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
assert (LJ' : Z.of_nat (length junk) = 8 * (size - Z.of_nat (length ps))) by (rewrite LJ; lia).
pose proof (al_arr_join asegs m0 arr size ps junk ARR JK Hlen) as COMB.
assert (ALk : forall mx, rw_cells asegs mx a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 (Z.of_nat (length ps))); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free A4F))] ->
rw_cells asegs mx arr [CB (Z.to_nat (8 * size)) ((u64s (wl ps) ++ junk) ++ [])] ->
alist asegs A4F mx [(a, AL_SZ); (arr, 8 * size)] a ps).
{ intros mx H1 H2. destruct (al_arr_split asegs mx arr size size ps junk [] H2 LJ ltac:(lia)) as [X Y].
rewrite app_nil_r in Y. eapply alist_close. split; [exact H1 | split; [exact X | split; [exact Y | lia]]]. }
clear ARR JK AL LJ.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (a, a + 32)] m0) as MU.
stash COMB.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1.
carve_frame 48%nat ST.
do 7 step.
step. step. step.
step.
asan_chkA.
step.
step. step. step.
step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. if_falsex.
step.
asan_chkA.
step.
step. replace (Z.of_nat (length ps) + 0) with (Z.of_nat (length ps)) by lia.
step.
destruct (Z.eq_dec (Z.of_nat (length ps)) size) as [EQ|NE].
-
rewrite <- EQ in *. if_falsex. step. step.
do 9 step.
unstash COMB.
evt_done5. apply K. unfold array_list_shrink_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 0, errv, arr, (Z.of_nat (length ps)), B0 end.
split; [| split; [apply model_vm_only_refl | split; [| split; [ | split; [ assumption | split; [match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y); lia end | split; [lia | split; [ | split; [| right; split; [reflexivity | lia]]]]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST (bv_unsigned sp). exact ST.
+ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ apply ALk; [assumption|].
lazymatch goal with |- rw_cells _ ?mf _ _ => eapply (rw_cells_transport asegs _ m0 mf); [exact COMB | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
-
specialize (BB NE).
if_truex. step. if_truex.
asan_chk0.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut with (P := eq (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0 t1 t2
(Z_to_bv 64 (a + 16)) (Z_to_bv 64 2147450880)
(Z_to_bv 64 arr) (v_sltiu (Z_to_bv 64 (Z.of_nat (length ps))) 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 size) a4 a5 a6 a7
(Z_to_bv 64 (a / 8 + 2147450882)) (Z_to_bv 64 (Z.max (Z.of_nat (length ps)) 1)) (Z_to_bv 64 a) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0728) fc None mc (seg_rom asegs)))
end.
{ destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [Z0|NZ].
- rewrite !Z0. cbn [Z.max Z.compare Pos.compare]. step. step. apply evt_done. reflexivity.
- step. step. rewrite v_sltiu1_pos by lia. rewrite (unsigned_lit 0) by lia.
apply evt_done. rewrite Z.max_l by lia.
replace (Z.of_nat (length ps) + 0) with (Z.of_nat (length ps)) by lia. reflexivity. }
intros ms' <-.
step. rewrite (unsigned_lit (Z.max (Z.of_nat (length ps)) 1)) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.max (Z.of_nat (length ps)) 1) 3) by lia. change (2^3) with 8.
step.

unstash COMB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m0 mc) in COMB; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
clear SHa GOT CELL.
alloc_callA (hiA_realloc A4L HIx) blk arr uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (right; left; reflexivity).
all: try exact COMB.
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [left; lia | unfold a4_straces; repeat first [left; reflexivity | right] | lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 ERR2 OUT2. open_ret RS. a4l.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & _ & HPR2 & HP2) | (Hr & HPR2 & [junk' BLK] & HP2)].
+
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in COMB; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM MI ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_true.
do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold array_list_shrink_A_post.
exists m2, (2^64 - 1), e2, arr, size, (charge B0 (16 * (Z.max (Z.of_nat (length ps)) 1 * 8) + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| split; [exact HP2| split; [apply ALk; assumption | left; repeat split; reflexivity]]]]]]]]].
* apply ret_statew_same.
* release_frame FR ST2 (bv_unsigned sp). exact ST2.
* rewrite (proj2 (Z.eqb_neq _ _) NE). unfold al_shrink_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
+
set (ns := Z.max (Z.of_nat (length ps)) 1) in *.
assert (Hns : Z.of_nat (length ps) <= ns /\ 1 <= ns /\ ns <= size) by (subst ns; lia).
assert (Ens : ns = Z.max (Z.of_nat (length ps)) 1) by reflexivity. clearbody ns.
assert (LO8 : length (u64s (wl ps) ++ junk) = Z.to_nat (8 * size)).
{ rewrite length_app, u64s_length, wl_length. lia. }
rewrite LO8, Z.min_l in BLK by lia. clear LO8.
rewrite firstn_app, u64s_length, wl_length, firstn_all2 in BLK by (rewrite u64s_length, wl_length; lia).
replace (ns * 8) with (8 * ns) in BLK, HP2 by lia.
destruct (al_arr_split asegs m2 r ns ns ps (firstn (Z.to_nat (8 * ns) - 8 * length ps) junk) junk' BLK
ltac:(rewrite length_firstn; lia) ltac:(lia)) as [ARR JK]. clear BLK. unfold al_tail in JK.
assert (HP2' : HEAPAx A2 ((a, 32) :: (r, 8 * ns) :: LB) LM FRS (charge B0 (16 * (8 * ns) + 512) (uw_cost UWptr)) m2 md2).
{ exact (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP2 (perm_swap (a, 32) (r, 8 * ns) LB) (Permutation_refl LM) (Permutation_refl FRS)). }
clear HP2.
blk_factsA A4L HIx HP2' r (8 * ns) Hqal Hqlo Hqhi Hqimg.
assert (Hne2 : a <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2') as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 r (8 * ns) HP2' ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne2) as Hrdj.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM MI ST COMB.
shadow_nowA A4L HIx HP2' a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0'.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3'.
a4l.
pose proof (wl_length ps) as WL.
pose proof (u64arr_bound asegs m2 r (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2') as MI. a4l.
pose proof (munch_refl [(a, a + 32); (bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
apply slots_of_u64arr in ARR. stash ARR. stash JK.
reenterA asegs A4L HIx asegs_wx HP2'.
step. step. if_falsex.
step.
asan_chk0.
step.
step. rewrite ?zxb_zero. step. if_false.
step. step.
do 9 step.
unstash ARR. unstash JK.
evt_done5. apply K. unfold array_list_shrink_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 0, e2, r, ns, (charge B0 (16 * (8 * ns) + 512) (uw_cost UWptr)) end.
split; [| split; [| split; [| split; [ | split; [ assumption | split; [ | split; [| split; [| split; [| right; split; [reflexivity | exact Ens]]]]]]]]]].
* apply ret_statew_same.
* exact VM2.
* release_frame FR ST2 (bv_unsigned sp). exact ST2.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2' | intros bb Hbb0; right; right; exact Hbb0 | clia | solve_clientWA A4L HIx HP2'].
* rewrite (proj2 (Z.eqb_neq _ _) NE). unfold al_shrink_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
* eapply (heapA_client_frame A4L HIx); [exact HP2' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2' MU); solve_frameW_withA HP2' | exact WM | assumption].
* lazymatch goal with |- alist _ _ ?mf _ _ _ =>
eapply (rw_cells_transport asegs _ m2 mf) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
eapply (rw_cells_transport asegs _ m2 mf) in JK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
eapply alist_close. split; [| split; [apply u64arr_of_slots; exact ARR | split; [exact JK | lia]]]. unfold al_hdr. assumption.
Qed.
End AAlShrink.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition jo_array_length_A_entry : Z := 0x9ecb8.
Definition jo_array_get_idx_A_entry : Z := 0x9ed30.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Lemma jo_array_length_A : forall (a1 a2 a3 a4 : word) (m : word -> option byte) (lo sbcell p rc tojs pb udel ud a arr size : Z) (ps : list Z),
small_pre sp m lo sbcell ->
rw_cells asegs m p (jhdr_cells JT_ARRAY rc tojs pb udel ud ++ [C8 (Z_to_bv 64 a)]) -> 0 < p -> p + 48 <= alloc_ceiling -> p mod 8 = 0 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p / 8 + A_SB + 6 <= alloc_ceiling ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
evt asegs (array_list_length_A_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a3 a4 ps m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 jo_array_length_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ps. intros PRE HDR Hp Hph Hal SH HSH AL ALB SHa.
pose proof PRE as (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8).
unfold jhdr_cells, JT_ARRAY in HDR. cbn [app] in HDR. unfold jo_array_length_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash AL. stash SHa.
carve_frame 16%nat ST.
step. step.
step. step. step.
step.
asan_chkA.
step.
step.
step.
release_frame FR ST (bv_unsigned sp).
step.
unstash AL. unstash SHa.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (ALc : alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps);
[ | assert (SHc : ro_cells asegs mc (a / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]);
[ | ] ] end end.
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply (alist_agree asegs A4F [(a, AL_SZ); (arr, 8 * size)]); [exact AL | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros b n Hb. cbn [disjoint_from].
destruct Hb as [E | [E | []]]; injection E as <- <-; split; try exact I; lia. }
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply ro_cells_transport; [exact SHa | exact MU |]. cbn [disjoint_from]. simpl_sizes. split; [| exact I]. Z.div_mod_to_equations. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_mono; [eapply (array_list_length_A ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ _ _ a3 a4 mc lo sbcell a arr size ps) |] end.
1: unfold small_pre, A_GOT_SB, A_SB, alloc_ceiling, sp_window_lo, stack_max_size; split; [exact MI | split; [exact ST | split; [lia | split; [lia | split; [exact GOT | split; [exact CELL | split; [exact Hc0 | lia]]]]]]].
1: exact ALc.
1: reflexivity.
1: exact ALB.
1: exact SHc.
intros ms' (x1 & x2 & m' & -> & MU' & WM' & MI' & ST'). exists x1, x2, m'. split; [reflexivity|].
split; [eapply munch_trans; [| exact MU']; replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU |].
split; [eapply wmono_trans; eassumption |]. split; [exact MI' | exact ST'].
Qed.

Lemma jo_array_get_idx_A : forall (a2 a3 a4 : word) (m : word -> option byte) (lo sbcell p rc tojs pb udel ud a arr size : Z) (ps : list Z) (i : Z),
small_pre sp m lo sbcell ->
rw_cells asegs m p (jhdr_cells JT_ARRAY rc tojs pb udel ud ++ [C8 (Z_to_bv 64 a)]) -> 0 < p -> p + 48 <= alloc_ceiling -> p mod 8 = 0 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p / 8 + A_SB + 6 <= alloc_ceiling ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps -> 0 <= i < 2^64 ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) -> 0 <= size -> arr / 8 + A_SB + size <= alloc_ceiling ->
evt asegs (array_list_get_idx_A_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ps i m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 jo_array_get_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until i. intros PRE HDR Hp Hph Hal SH HSH AL Hi ALB SHa SHr Hsz HSr.
pose proof PRE as (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8).
unfold jhdr_cells, JT_ARRAY in HDR. cbn [app] in HDR. unfold jo_array_get_idx_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH, HSr. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash AL. stash SHa. stash SHr.
carve_frame 16%nat ST.
step. step.
step. step. step.
step.
asan_chkA.
step.
step. step.
release_frame FR ST (bv_unsigned sp).
step.
unstash AL. unstash SHa. unstash SHr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (ALc : alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps);
[ | assert (SHc : ro_cells asegs mc (a / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]);
[ | assert (SHrc : bytes_at asegs mc (arr / 8 + 2147450880) (shadow_bytes (8 * size))); [ | ] ] ] end end.
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply (alist_agree asegs A4F [(a, AL_SZ); (arr, 8 * size)]); [exact AL | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros b n Hb. cbn [disjoint_from].
destruct Hb as [E | [E | []]]; injection E as <- <-; split; try exact I; lia. }
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply ro_cells_transport; [exact SHa | exact MU |]. cbn [disjoint_from]. simpl_sizes. split; [| exact I]. Z.div_mod_to_equations. lia. }
{ eapply bytes_at_transport; [exact SHr | exact MU |]. cbn [disjoint_from]. rewrite shadow_bytes_length8 by lia. split; [| exact I]. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_mono; [eapply (array_list_get_idx_A ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ _ _ _ _ mc lo sbcell a arr size ps i) |] end.
1: unfold small_pre, A_GOT_SB, A_SB, alloc_ceiling, sp_window_lo, stack_max_size; split; [exact MI | split; [exact ST | split; [lia | split; [lia | split; [exact GOT | split; [exact CELL | split; [exact Hc0 | lia]]]]]]].
1: exact ALc.
1: reflexivity.
1: reflexivity.
1: exact Hi.
1: exact ALB.
1: exact SHc.
1: exact SHrc.
intros ms' (x1 & x2 & x3 & x4 & m' & -> & MU' & WM' & MI' & ST'). exists x1, x2, x3, x4, m'. split; [reflexivity|].
split; [eapply munch_trans; [| exact MU']; replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU |].
split; [eapply wmono_trans; eassumption |]. split; [exact MI' | exact ST'].
Qed.
End Regs.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlAdd.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo a arr size d : Z) (ps : list Z) (T : TSet).

Definition array_list_add_A_entry : Z := 0xa27dc.
Definition al_add_costB : Z := 256 * size + 512.

Definition array_list_add_A_post (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (arr' size' : Z) (B' : bud),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bD B0 <= bD B' /\
HEAPAx A' ((a, AL_SZ) :: (arr', 8 * size') :: LB) LM FRS B' m' md' /\
( (r = 2^64 - 1 /\ arr' = arr /\ size' = size /\ size <= Z.of_nat (length ps) + 1 /\ bB B0 - al_add_costB <= bB B' /\ alist asegs A4F m' [(a, AL_SZ); (arr, 8 * size)] a ps)
\/ (r = 0 /\ alist asegs A4F m' [(a, AL_SZ); (arr', 8 * size')] a (ps ++ [d])
/\ ((size' = size /\ arr' = arr /\ Z.of_nat (length ps) + 1 < size /\ bB B0 <= bB B')
\/ (size' = 2 * size /\ size <= Z.of_nat (length ps) + 1 /\ bB B0 - al_add_costB <= bB B'))) ).

Definition add_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma al_add_storeA :
forall (x1 t0 t1 t2 x9 a2 a3 a4 a5 a6 a7 x19 x23 x25 x26 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (r size' : Z) (junk : list byte) (errv : word),
HEAPAx A ((a, AL_SZ) :: (r, 8 * size') :: LB) LM FRS B m md ->
al_hdr asegs A4F m a r (Z.of_nat (length ps)) size' ->
u64arr asegs m r (wl ps) ->
al_tail asegs m r size' (length ps) junk ->
Z.of_nat (length ps) + 1 <= size' -> (1 <= size' /\ 8 * size' < 2^64) ->
((size' = size /\ r = arr /\ Z.of_nat (length ps) + 1 < size /\ bB B0 <= bB B) \/ (size' = 2 * size /\ size <= Z.of_nat (length ps) + 1 /\ bB B0 - al_add_costB <= bB B)) ->
0 <= d < 2^64 ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -96 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
add_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bD B0 <= bD B ->
(forall ms' md' A', array_list_add_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (a + 8)) x9 (Z_to_bv 64 a) (Z_to_bv 64 d) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 16)) x19 (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (Z.of_nat (length ps))) x23
(Z_to_bv 64 (a / 8 + 2147450882)) x25 x26 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa28d8) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP HDR ARR JK ROOM Hsz CASES Hd ST LO LOS SPA HT FR ERR RA VM0 HPR BD K.
unfold al_hdr in HDR. unfold al_tail in JK. unfold add_frameA in FR.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP r (8 * size') Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 r (8 * size') HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 r (8 * size') HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0r.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 r (8 * size') HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP3r.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r (8 * size') HP ltac:(right; left; reflexivity)) as SHr. unfold shad in SHr.
a4l.
pose proof (u64arr_bound asegs m r (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
assert (LJ : length junk = Z.to_nat (8 * (size' - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).

apply (rw_cells_CB_cut asegs m _ _ junk 8) in JK; [|lia]. destruct JK as [J1 J2]. clear LJ.

pose proof (ov_read1_of_ro asegs _ _ _ (shadow_granule0 asegs m (r / 8 + 2147450880) (8 * size') (Z.of_nat (length ps)) ltac:(lia) ltac:(lia) SHr)) as HR.
clear SHr.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (a, a + 32); (r, r + 8 * size')] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep.
bstep. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
bstep.
bstep. bstep. sh_norm.
replace ((r + Z.of_nat (length ps) * 8) / 8 + 2147450880) with (r / 8 + 2147450880 + Z.of_nat (length ps)) by (Z.div_mod_to_equations; lia).
bstep. rewrite ?zxb_zero. clear HR. bstep. if_false.
assert (SOK : store_ok asegs m (wa (r + Z.of_nat (length ps) * 8)) 8 = true).
{ destruct J1 as [_ W]. cbn [cells_size csize Nat.add] in W.
replace (r + Z.of_nat (length ps) * 8) with (r + 8 * Z.of_nat (length ps) + 0) by lia.
eapply wr_at_store_ok; [exact W | lia | cbn; lia]. }
bstep.
pose proof (rw_cells_write asegs m _ _ 0 _ (C8 (Z_to_bv 64 d)) J1 eq_refl eq_refl I) as J1'.
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub cbytes] in J1'.
replace (r + 8 * Z.of_nat (length ps) + Z.of_nat 0) with (r + 8 * Z.of_nat (length ps)) in J1' by lia.
clear J1.
change (Z_to_bv 64 (r + Z.of_nat (length ps) * 8)) with (wa (r + Z.of_nat (length ps) * 8)).
replace (wa (r + Z.of_nat (length ps) * 8)) with (wa (r + 8 * Z.of_nat (length ps))) by (unfold wa; f_equal; lia).
store_done.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep.
bstep. bstep. bstep.
do 15 bstep.
evt_done5. apply K. unfold array_list_add_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 0, errv, r, size', B end.
split; [| split; [exact VM0 | split; [| split; [ | split; [ eassumption | split; [exact BD | split; [ | right]]]]]]].
- apply ret_statew_same.
- release_frame FR ST (bv_unsigned sp). exact ST.
- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP].
- eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
- split; [reflexivity|]. split; [| exact CASES].
eapply alist_close. split; [| split; [| split; [| split; [rewrite length_app; cbn [length]; lia | exact Hsz]]]].
+ unfold al_hdr. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
replace (Z.of_nat (length ps) + Z.pos (Pos.of_succ_nat 0)) with (Z.of_nat (length ps) + 1) by lia. eassumption.
+ eapply u64arr_snoc; [eassumption|]. eassumption.
+ unfold al_tail. rewrite length_app. cbn [length].
replace (r + 8 * Z.of_nat (length ps + 1)) with (r + 8 * Z.of_nat (length ps) + Z.of_nat 8) by lia.
replace (Z.to_nat (8 * (size' - Z.of_nat (length ps + 1)))) with (Z.to_nat (8 * (size' - Z.of_nat (length ps))) - 8)%nat by lia.
exact J2.
Qed.

Lemma al_add_growA :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (junk : list byte) (errv : word),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m md ->
al_hdr asegs A4F m a arr (Z.of_nat (length ps)) size ->
u64arr asegs m arr (wl ps) ->
al_tail asegs m arr size (length ps) junk ->
Z.of_nat (length ps) <= size -> (1 <= size /\ 8 * size < 2^64) -> size <= Z.of_nat (length ps) + 1 -> Z.of_nat (length ps) + 1 < 2^28 ->
0 <= d < 2^64 ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
add_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
al_add_costB <= bB B0 -> 0 <= bD B0 ->
(forall ms' md' A', array_list_add_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (a + 8)) (Z_to_bv 64 (-1)) (Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 size) a3 a4 a5 a6 a7
(Z_to_bv 64 (a + 16)) s3 (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (Z.of_nat (length ps))) (Z_to_bv 64 (Z.of_nat (length ps) + 1))
(Z_to_bv 64 (a / 8 + 2147450882)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2868) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP HDR ARR JK Hlen Hsz GROWS Hlen28 Hd ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD K.
unfold al_hdr in HDR. unfold add_frameA in FR.
unfold_consts. unfold al_add_costB in BB. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> arr).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 arr (8 * size) HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
a4l.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
assert (LJ' : Z.of_nat (length junk) = 8 * (size - Z.of_nat (length ps))) by (rewrite LJ; lia).
pose proof (al_arr_join asegs m arr size ps junk ARR JK Hlen) as COMB. clear LJ.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (a, a + 32)] m) as MU.
stash COMB.
reenterA asegs A4L HIx asegs_wx HP.
bstep. rewrite (unsigned_lit size) by lia. rewrite (Z.shiftl_mul_pow2 size 1) by lia. change (2^1) with 2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut with (P := eq (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6444320) t0 t1 t2
(Z_to_bv 64 (a + 8)) (Z_to_bv 64 (-1)) (Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 size) (Z_to_bv 64 (size * 2)) a4 a5 a6 a7
(Z_to_bv 64 (a + 16)) s3 (Z_to_bv 64 (a / 8 + 2147450881)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.of_nat (length ps))) (Z_to_bv 64 (Z.of_nat (length ps) + 1))
(Z_to_bv 64 (a / 8 + 2147450882)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2874) fc None mc (seg_rom asegs)))
end.
{ destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) (size * 2)) as [LT|GE].
- bstep. if_truex. apply evt_done. reflexivity.
- bstep. if_falsex. bstep. apply evt_done. replace (size * 2) with (Z.of_nat (length ps) + 1) by lia. reflexivity. }
intros ms' <-.
bstep. bstep. bstep. if_falsex. bstep.
bstep. rewrite (unsigned_lit (size * 2)) by lia. rewrite (Z.shiftr_div_pow2 (size * 2) 61) by lia.
rewrite (Z.div_small (size * 2) (2^61)) by lia.
bstep. if_false.
bstep.
asan_chk0.
bstep. bstep.
bstep. rewrite (unsigned_lit (size * 2)) by lia. rewrite (Z.shiftl_mul_pow2 (size * 2) 3) by lia. change (2^3) with 8.
bstep.

unstash COMB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in COMB; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
clear SHa.
alloc_callA (hiA_realloc A4L HIx) blk arr uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (right; left; reflexivity).
all: try exact COMB.
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [left; lia | unfold a4_straces; repeat first [left; reflexivity | right] | lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 ERR2 OUT2. open_ret RS. a4l.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & _ & HPR2 & HP2) | (Hr & HPR2 & [junk' BLK] & HP2)].
-
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in COMB; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
a4l.
destruct (al_arr_split asegs m2 arr size size ps junk [] COMB ltac:(apply Nat2Z.inj; rewrite LJ', Z2Nat.id by lia; reflexivity) ltac:(lia)) as [ARR2 JK2].
clear MU WM MI ST COMB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true.
do 15 bstep.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold array_list_add_A_post.
exists m2, (2^64 - 1), e2, arr, size, (charge B0 (16 * (size * 2 * 8) + 512) (uw_cost UWptr)).
split; [| split; [eapply model_vm_only_trans; [exact VM0 | exact VM2] | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [exact HP2| left]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ cbn [bD charge uw_cost]. lia.
+ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact GROWS|]. split; [unfold al_add_costB; cbn [bB charge]; lia|].
rewrite app_nil_r in JK2. eapply alist_close. split; [exact HDR | split; [exact ARR2 | split; [exact JK2 | lia]]].
-
assert (LO8 : length (u64s (wl ps) ++ junk) = Z.to_nat (8 * size)).
{ rewrite length_app, u64s_length, wl_length. lia. }
rewrite LO8, Z.min_r, firstn_all2 in BLK by (rewrite ?LO8; lia). clear LO8.
replace (size * 2 * 8) with (8 * (2 * size)) in BLK, HP2 by lia.
destruct (al_arr_split asegs m2 r size (2 * size) ps junk junk' BLK ltac:(apply Nat2Z.inj; rewrite LJ', Z2Nat.id by lia; reflexivity) ltac:(lia)) as [ARR2 JK2]. clear BLK. unfold al_tail in JK2.
assert (HP2' : HEAPAx A2 ((a, 32) :: (r, 8 * (2 * size)) :: LB) LM FRS (charge B0 (16 * (8 * (2 * size)) + 512) (uw_cost UWptr)) m2 md2).
{ exact (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP2 (perm_swap (a, 32) (r, 8 * (2 * size)) LB) (Permutation_refl LM) (Permutation_refl FRS)). }
clear HP2.
blk_factsA A4L HIx HP2' r (8 * (2 * size)) Hqal Hqlo Hqhi Hqimg.
assert (Hne2 : a <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2') as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 r (8 * (2 * size)) HP2' ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne2) as Hrdj.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM MI ST COMB.
shadow_nowA A4L HIx HP2' a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0'.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3'.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2') as MI. a4l.
pose proof (wl_length ps) as WL.
pose proof (munch_refl [(a, a + 32)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2'.
bstep. if_falsex.
bstep.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep.
replace (size * 2) with (2 * size) in * by lia.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
evt_done5.
eapply (al_add_storeA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 md2 A2 _ r (2 * size) (junk ++ junk') e2);
first [exact ST2 | exact SPA | exact HT | exact RA | exact K | idtac].
all: lazymatch goal with
| |- HEAPA _ _ _ _ _ _ _ _ _ =>
eapply (heapA_client_frame A4L HIx); [exact HP2' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2' MU); solve_frameW_withA HP2' | exact WM | exact MI]
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; assumption
| |- u64arr _ _ _ _ => exact ARR2
| |- al_tail _ _ _ _ _ _ => unfold al_tail; exact JK2
| |- add_frameA _ => unfold add_frameA; assumption
| |- rw_cells _ _ _ _ => assumption
| |- model_vm_only (cfg_model _) (cfg_model _) => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP2' | intros bb Hbb0; right; right; exact Hbb0 | clia | solve_clientWA A4L HIx HP2']
| |- _ \/ _ => right; split; [reflexivity | split; [lia | unfold al_add_costB; cbn [bB charge]; lia]]
| |- bD _ <= _ => cbn [bD charge uw_cost]; lia
| |- _ => clia
end.
Qed.

Lemma array_list_add_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m0 md0 ->
alist asegs A4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps -> Z.of_nat (length ps) + 1 < 2^28 ->
0 <= d < 2^64 ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 d ->
(size <= Z.of_nat (length ps) + 1 -> al_add_costB <= bB B0) -> 0 <= bD B0 ->
(forall ms' md' A', array_list_add_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_add_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP AL Hlen28 Hd ST LO LOS SPA HT ERR RA A0 A1 BB BD K.
destruct (alist_openx asegs A4F m0 a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR.
unfold_consts. unfold A_SB, A_TP, A_ERRNO, array_list_add_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
shadow_nowA A4L HIx HP a 32 SHa.
a4l.
pose proof (u64arr_bound asegs m0 arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m0) as MU.
apply slots_of_u64arr in ARR. stash ARR. stash JK.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1.
carve_frame 96%nat ST.
do 13 bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep. bstep. bstep.
bstep. if_falsex.
bstep.
asan_chkA.
bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LB) LM FRS B0 m1 md0) by heap_nowA A4L HIx HP MU WM MI.
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP]. }
unstash ARR. unstash JK.
eapply (rw_cells_transport asegs _ m0 m1) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia].
eapply (rw_cells_transport asegs _ m0 m1) in JK; [| exact MU | exact WM | unfold al_tail; cbn [disjoint_from]; simpl_sizes; lia].
apply u64arr_of_slots in ARR.
bstep.
destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) size) as [LT|GE].
-
if_truex.
evt_done5.
eapply (al_add_storeA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A B0 arr size junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; assumption
| |- add_frameA _ => unfold add_frameA; assumption
| |- rw_cells _ _ _ _ => assumption
| |- _ \/ _ => left; split; [reflexivity | split; [reflexivity | split; [lia | lia]]]
| |- bD _ <= _ => lia
| |- _ => clia
end.
-
specialize (BB GE).
if_falsex.
evt_done5.
eapply (al_add_growA _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; assumption
| |- add_frameA _ => unfold add_frameA; assumption
| |- rw_cells _ _ _ _ => assumption
| |- _ <= bB _ => exact BB
| |- _ <= bD _ => exact BD
| |- _ => clia
end.
Qed.
End AAlAdd.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import QnCn.Mq0. Import QTKj.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlShrink.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo a arr size : Z) (ps : list Z) (T : TSet).

Definition array_list_shrink_A_entry : Z := 0xa25a4.
Definition al_shrink_costB : Z := 16 * (8 * Z.max (Z.of_nat (length ps)) 1) + 512.

Definition array_list_shrink_A_post (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (arr' size' : Z) (B' : bud),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B0 - (if Z.of_nat (length ps) =? size then 0 else al_shrink_costB) <= bB B' /\ bD B0 <= bD B' /\
HEAPAx A' ((a, AL_SZ) :: (arr', 8 * size') :: LB) LM FRS B' m' md' /\
alist asegs A4F m' [(a, AL_SZ); (arr', 8 * size')] a ps /\
( (r = 2^64 - 1 /\ arr' = arr /\ size' = size)
\/ (r = 0 /\ size' = Z.max (Z.of_nat (length ps)) 1) ).

Lemma array_list_shrink_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) LM FRS B0 m0 md0 ->
alist asegs A4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps -> Z.of_nat (length ps) < 2^28 ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 0 ->
(Z.of_nat (length ps) <> size -> al_shrink_costB <= bB B0) -> 0 <= bD B0 ->
(forall ms' md' A', array_list_shrink_A_post ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_shrink_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP AL Hlen28 ST LO LOS SPA HT ERR RA A0 A1 BB BD K.
destruct (alist_openx asegs A4F m0 a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR.
unfold_consts. unfold al_shrink_costB in BB. unfold A_SB, A_TP, A_ERRNO, array_list_shrink_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP a 32 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Hrimg.
assert (Hne : a <> arr).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 arr (8 * size) HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
shadow_nowA A4L HIx HP a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
a4l.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
assert (LJ' : Z.of_nat (length junk) = 8 * (size - Z.of_nat (length ps))) by (rewrite LJ; lia).
pose proof (al_arr_join asegs m0 arr size ps junk ARR JK Hlen) as COMB.
assert (ALk : forall mx, rw_cells asegs mx a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 (Z.of_nat (length ps))); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free A4F))] ->
rw_cells asegs mx arr [CB (Z.to_nat (8 * size)) ((u64s (wl ps) ++ junk) ++ [])] ->
alist asegs A4F mx [(a, AL_SZ); (arr, 8 * size)] a ps).
{ intros mx H1 H2. destruct (al_arr_split asegs mx arr size size ps junk [] H2 LJ ltac:(lia)) as [X Y].
rewrite app_nil_r in Y. eapply alist_close. split; [exact H1 | split; [exact X | split; [exact Y | lia]]]. }
clear ARR JK AL LJ.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (a, a + 32)] m0) as MU.
stash COMB.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1.
carve_frame 48%nat ST.
do 7 bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep. bstep. bstep.
bstep. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. if_falsex.
bstep.
asan_chkA.
bstep.
bstep. replace (Z.of_nat (length ps) + 0) with (Z.of_nat (length ps)) by lia.
bstep.
destruct (Z.eq_dec (Z.of_nat (length ps)) size) as [EQ|NE].
-
rewrite <- EQ in *. if_falsex. bstep. bstep.
do 9 bstep.
unstash COMB.
evt_done5. apply K. unfold array_list_shrink_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 0, errv, arr, (Z.of_nat (length ps)), B0 end.
split; [| split; [apply model_vm_only_refl | split; [| split; [ | split; [ assumption | split; [match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y); lia end | split; [lia | split; [ | split; [| right; split; [reflexivity | lia]]]]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST (bv_unsigned sp). exact ST.
+ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ apply ALk; [assumption|].
lazymatch goal with |- rw_cells _ ?mf _ _ => eapply (rw_cells_transport asegs _ m0 mf); [exact COMB | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
-
specialize (BB NE).
if_truex. bstep. if_truex.
asan_chk0.
bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut with (P := eq (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6444320) t0 t1 t2
(Z_to_bv 64 (a + 16)) (Z_to_bv 64 2147450880)
(Z_to_bv 64 arr) (v_sltiu (Z_to_bv 64 (Z.of_nat (length ps))) 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 size) a4 a5 a6 a7
(Z_to_bv 64 (a / 8 + 2147450882)) (Z_to_bv 64 (Z.max (Z.of_nat (length ps)) 1)) (Z_to_bv 64 a) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa268c) fc None mc (seg_rom asegs)))
end.
{ destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [Z0|NZ].
- rewrite !Z0. cbn [Z.max Z.compare Pos.compare]. bstep. bstep. apply evt_done. reflexivity.
- bstep. bstep. rewrite v_sltiu1_pos by lia. rewrite (unsigned_lit 0) by lia.
apply evt_done. rewrite Z.max_l by lia.
replace (Z.of_nat (length ps) + 0) with (Z.of_nat (length ps)) by lia. reflexivity. }
intros ms' <-.
bstep. rewrite (unsigned_lit (Z.max (Z.of_nat (length ps)) 1)) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.max (Z.of_nat (length ps)) 1) 3) by lia. change (2^3) with 8.
bstep.

unstash COMB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m0 mc) in COMB; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
clear SHa GOT CELL.
alloc_callA (hiA_realloc A4L HIx) blk arr uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (right; left; reflexivity).
all: try exact COMB.
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [left; lia | unfold a4_straces; repeat first [left; reflexivity | right] | lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 ERR2 OUT2. open_ret RS. a4l.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & _ & HPR2 & HP2) | (Hr & HPR2 & [junk' BLK] & HP2)].
+
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in COMB; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM MI ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. bstep. if_true.
do 9 bstep.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold array_list_shrink_A_post.
exists m2, (2^64 - 1), e2, arr, size, (charge B0 (16 * (Z.max (Z.of_nat (length ps)) 1 * 8) + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| split; [exact HP2| split; [apply ALk; assumption | left; repeat split; reflexivity]]]]]]]]].
* apply ret_statew_same.
* release_frame FR ST2 (bv_unsigned sp). exact ST2.
* rewrite (proj2 (Z.eqb_neq _ _) NE). unfold al_shrink_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
+
set (ns := Z.max (Z.of_nat (length ps)) 1) in *.
assert (Hns : Z.of_nat (length ps) <= ns /\ 1 <= ns /\ ns <= size) by (subst ns; lia).
assert (Ens : ns = Z.max (Z.of_nat (length ps)) 1) by reflexivity. clearbody ns.
assert (LO8 : length (u64s (wl ps) ++ junk) = Z.to_nat (8 * size)).
{ rewrite length_app, u64s_length, wl_length. lia. }
rewrite LO8, Z.min_l in BLK by lia. clear LO8.
rewrite firstn_app, u64s_length, wl_length, firstn_all2 in BLK by (rewrite u64s_length, wl_length; lia).
replace (ns * 8) with (8 * ns) in BLK, HP2 by lia.
destruct (al_arr_split asegs m2 r ns ns ps (firstn (Z.to_nat (8 * ns) - 8 * length ps) junk) junk' BLK
ltac:(rewrite length_firstn; lia) ltac:(lia)) as [ARR JK]. clear BLK. unfold al_tail in JK.
assert (HP2' : HEAPAx A2 ((a, 32) :: (r, 8 * ns) :: LB) LM FRS (charge B0 (16 * (8 * ns) + 512) (uw_cost UWptr)) m2 md2).
{ exact (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP2 (perm_swap (a, 32) (r, 8 * ns) LB) (Permutation_refl LM) (Permutation_refl FRS)). }
clear HP2.
blk_factsA A4L HIx HP2' r (8 * ns) Hqal Hqlo Hqhi Hqimg.
assert (Hne2 : a <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2') as ND. cbn in ND. inversion ND as [|x l Hni Hnd]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a 32 r (8 * ns) HP2' ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne2) as Hrdj.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM MI ST COMB.
shadow_nowA A4L HIx HP2' a 32 SHa.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 0 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0'.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ a 32 3 a 32 HP2' ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3'.
a4l.
pose proof (wl_length ps) as WL.
pose proof (u64arr_bound asegs m2 r (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2') as MI. a4l.
pose proof (munch_refl [(a, a + 32); (bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
apply slots_of_u64arr in ARR. stash ARR. stash JK.
reenterA asegs A4L HIx asegs_wx HP2'.
bstep. bstep. if_falsex.
bstep.
asan_chk0.
bstep.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep.
do 9 bstep.
unstash ARR. unstash JK.
evt_done5. apply K. unfold array_list_shrink_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 0, e2, r, ns, (charge B0 (16 * (8 * ns) + 512) (uw_cost UWptr)) end.
split; [| split; [| split; [| split; [ | split; [ assumption | split; [ | split; [| split; [| split; [| right; split; [reflexivity | exact Ens]]]]]]]]]].
* apply ret_statew_same.
* exact VM2.
* release_frame FR ST2 (bv_unsigned sp). exact ST2.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2' | intros bb Hbb0; right; right; exact Hbb0 | clia | solve_clientWA A4L HIx HP2'].
* rewrite (proj2 (Z.eqb_neq _ _) NE). unfold al_shrink_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
* eapply (heapA_client_frame A4L HIx); [exact HP2' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2' MU); solve_frameW_withA HP2' | exact WM | assumption].
* lazymatch goal with |- alist _ _ ?mf _ _ _ =>
eapply (rw_cells_transport asegs _ m2 mf) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
eapply (rw_cells_transport asegs _ m2 mf) in JK; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end.
eapply alist_close. split; [| split; [apply u64arr_of_slots; exact ARR | split; [exact JK | lia]]]. unfold al_hdr. assumption.
Qed.
End AAlShrink.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QRUw.
Import QnCn.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition jo_array_length_A_entry : Z := 0xa0930.
Definition jo_array_get_idx_A_entry : Z := 0xa09c8.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Lemma jo_array_length_A : forall (a1 a2 a3 a4 : word) (m : word -> option byte) (lo sbcell p rc tojs pb udel ud a arr size : Z) (ps : list Z),
small_pre sp m lo sbcell ->
rw_cells asegs m p (jhdr_cells JT_ARRAY rc tojs pb udel ud ++ [C8 (Z_to_bv 64 a)]) -> 0 < p -> p + 48 <= alloc_ceiling -> p mod 8 = 0 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p / 8 + A_SB + 6 <= alloc_ceiling ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
evt asegs (array_list_length_A_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a3 a4 ps m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 jo_array_length_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ps. intros PRE HDR Hp Hph Hal SH HSH AL ALB SHa.
pose proof PRE as (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8).
unfold jhdr_cells, JT_ARRAY in HDR. cbn [app] in HDR. unfold jo_array_length_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash AL. stash SHa.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep.
bstep.
release_frame FR ST (bv_unsigned sp).
bstep.
unstash AL. unstash SHa.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (ALc : alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps);
[ | assert (SHc : ro_cells asegs mc (a / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]);
[ | ] ] end end.
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply (alist_agree asegs A4F [(a, AL_SZ); (arr, 8 * size)]); [exact AL | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros b n Hb. cbn [disjoint_from].
destruct Hb as [E | [E | []]]; injection E as <- <-; split; try exact I; lia. }
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply ro_cells_transport; [exact SHa | exact MU |]. cbn [disjoint_from]. simpl_sizes. split; [| exact I]. Z.div_mod_to_equations. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_mono; [eapply (array_list_length_A ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ _ _ a3 a4 mc lo sbcell a arr size ps) |] end.
1: unfold small_pre, A_GOT_SB, A_SB, alloc_ceiling, sp_window_lo, stack_max_size; split; [exact MI | split; [exact ST | split; [lia | split; [lia | split; [exact GOT | split; [exact CELL | split; [exact Hc0 | lia]]]]]]].
1: exact ALc.
1: reflexivity.
1: exact ALB.
1: exact SHc.
intros ms' (x1 & x2 & m' & -> & MU' & WM' & MI' & ST'). exists x1, x2, m'. split; [reflexivity|].
split; [eapply munch_trans; [| exact MU']; replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU |].
split; [eapply wmono_trans; eassumption |]. split; [exact MI' | exact ST'].
Qed.

Lemma jo_array_get_idx_A : forall (a2 a3 a4 : word) (m : word -> option byte) (lo sbcell p rc tojs pb udel ud a arr size : Z) (ps : list Z) (i : Z),
small_pre sp m lo sbcell ->
rw_cells asegs m p (jhdr_cells JT_ARRAY rc tojs pb udel ud ++ [C8 (Z_to_bv 64 a)]) -> 0 < p -> p + 48 <= alloc_ceiling -> p mod 8 = 0 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p / 8 + A_SB + 6 <= alloc_ceiling ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps -> 0 <= i < 2^64 ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) -> 0 <= size -> arr / 8 + A_SB + size <= alloc_ceiling ->
evt asegs (array_list_get_idx_A_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ps i m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 jo_array_get_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until i. intros PRE HDR Hp Hph Hal SH HSH AL Hi ALB SHa SHr Hsz HSr.
pose proof PRE as (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8).
unfold jhdr_cells, JT_ARRAY in HDR. cbn [app] in HDR. unfold jo_array_get_idx_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH, HSr. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash AL. stash SHa. stash SHr.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep. bstep.
release_frame FR ST (bv_unsigned sp).
bstep.
unstash AL. unstash SHa. unstash SHr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (ALc : alist asegs A4F mc [(a, AL_SZ); (arr, 8 * size)] a ps);
[ | assert (SHc : ro_cells asegs mc (a / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]);
[ | assert (SHrc : bytes_at asegs mc (arr / 8 + 2147450880) (shadow_bytes (8 * size))); [ | ] ] ] end end.
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply (alist_agree asegs A4F [(a, AL_SZ); (arr, 8 * size)]); [exact AL | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros b n Hb. cbn [disjoint_from].
destruct Hb as [E | [E | []]]; injection E as <- <-; split; try exact I; lia. }
{ destruct ALB as (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hah, Hrh.
eapply ro_cells_transport; [exact SHa | exact MU |]. cbn [disjoint_from]. simpl_sizes. split; [| exact I]. Z.div_mod_to_equations. lia. }
{ eapply bytes_at_transport; [exact SHr | exact MU |]. cbn [disjoint_from]. rewrite shadow_bytes_length8 by lia. split; [| exact I]. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_mono; [eapply (array_list_get_idx_A ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ _ _ _ _ mc lo sbcell a arr size ps i) |] end.
1: unfold small_pre, A_GOT_SB, A_SB, alloc_ceiling, sp_window_lo, stack_max_size; split; [exact MI | split; [exact ST | split; [lia | split; [lia | split; [exact GOT | split; [exact CELL | split; [exact Hc0 | lia]]]]]]].
1: exact ALc.
1: reflexivity.
1: reflexivity.
1: exact Hi.
1: exact ALB.
1: exact SHc.
1: exact SHrc.
intros ms' (x1 & x2 & x3 & x4 & x5 & m' & -> & MU' & WM' & MI' & ST'). exists x1, x2, x3, x4, x5, m'. split; [reflexivity|].
split; [eapply munch_trans; [| exact MU']; replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU |].
split; [eapply wmono_trans; eassumption |]. split; [exact MI' | exact ST'].
Qed.
End Regs.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition array_list_set_idx_A_entry : Z := 0xa2714.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition array_list_set_idx_A_post (a arr size : Z) (ps : list Z) (idx d : Z) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (a1 a3 a4 a5 a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if idx <? Z.of_nat (length ps) then 0 else 2^64 - 1)) a1 a2 a3 a4 a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(arr, arr + 8 * size); (bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ alist asegs A4F m' [(a, AL_SZ); (arr, 8 * size)] a (if idx <? Z.of_nat (length ps) then upd ps (Z.to_nat idx) d else ps)
/\ stk asegs m' lo (bv_unsigned sp).

Lemma array_list_set_idx_A : forall (a0 a1 a3 a4 a5 : word) (m : word -> option byte) (lo sbcell a arr size : Z) (ps : list Z) (idx d : Z),
small_pre sp m lo sbcell ->
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 d -> 0 <= idx < 2^64 ->
al_blkA a arr size ->
ro_cells asegs m (a / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
bytes_at asegs m (arr / 8 + A_SB) (shadow_bytes (8 * size)) ->
evt asegs (array_list_set_idx_A_post a arr size ps idx d m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_set_idx_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until d. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) AL SEP A0 A1 A2 Hi (Ha0 & Ha8 & Hah & Hr0 & Hr8 & Hrh) SHa SHr.
destruct (alist_openx asegs A4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz). unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (u64arr_bound asegs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
unfold array_list_set_idx_A_entry, array_list_set_idx_A_post, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8, Hah, Hrh. word_range sp SPR. subst a0 a1 a2.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply slots_of_u64arr in ARR. stash SHr. stash ARR.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep.
destruct (Z.ltb_spec idx (Z.of_nat (length ps))) as [LT|GE].
- if_falsex.
asan_chk0.
bstep.
bstep. bstep.
rewrite (unsigned_lit idx) by lia. rewrite (Z.shiftl_mul_pow2 idx 3) by lia. change (2^3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HR : ov_read_bytes asegs mc (Z_to_bv 64 (arr / 8 + 2147450880 + idx)) 1 = Some [Z_to_bv 8 0])
by (unstash SHr; apply ov_read1_of_ro; eapply (ro_cells_transport asegs _ m mc); [| exact MU | cbn; lia];
apply (shadow_granule0 asegs m (arr / 8 + 2147450880) (8 * size) idx); [lia | lia | exact SHr])
end.
bstep. bstep. sh_norm.
replace ((arr + idx * 8) / 8 + 2147450880) with (arr / 8 + 2147450880 + idx) by (Z.div_mod_to_equations; lia).
bstep. rewrite ?zxb_zero. clear HR.
bstep. if_false.
unstash ARR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (rw_cells_transport asegs _ m mc) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia];
apply u64arr_of_slots in ARR;
pose proof (u64arr_store_ok asegs mc arr (wl ps) idx (wa (arr + idx * 8)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;

assert (MU2 : munch [(arr, arr + 8 * size); (bv_unsigned sp - 16, bv_unsigned sp)] m mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia)
end.
clear MU. rename MU2 into MU.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc arr (wl ps) idx (Z_to_bv 64 d) ARR ltac:(lia)) as ARR' end.
replace (8 * idx) with (idx * 8) in ARR' by lia. rewrite <- wl_upd in ARR'.
clear ARR. store_done.
bstep.
bstep.
bstep. bstep. bstep.
apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split.
+ eapply alist_close. split; [| split; [exact ARR' | split; [| split; [rewrite upd_length; exact Hlen | exact Hsz]]]].
* unfold al_hdr. rewrite upd_length. assumption.
* unfold al_tail. rewrite upd_length. exact JK.
+ release_frame FR ST (bv_unsigned sp). exact ST.
- if_truex.
bstep.
bstep.
bstep. bstep. bstep.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
unstash ARR.
apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [| split; [exact WM|]].
{ eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [assumption|].
split.
+ lazymatch goal with |- alist _ _ ?mf _ _ _ =>
eapply (rw_cells_transport asegs _ m mf) in ARR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite slots_size; lia] end.
eapply alist_close. split; [| split; [apply u64arr_of_slots; exact ARR | split; [exact JK | split; [exact Hlen | exact Hsz]]]].
unfold al_hdr. assumption.
+ release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End Regs.
End RC__1.
