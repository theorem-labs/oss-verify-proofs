(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj QSL3 QeL5 Q7UD Qhd4 Qwm6 QlKV QsKa Q30W Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3. Import QeL5.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 Q30W.Mq3 QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition lh_entry_free_A_entry : Z := 0x9bd40.
Definition lh_table_free_A_entry : Z := 0xa2700.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhFree.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition lh_entry_free_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
HEAPAx A' LB LM FRS (charge B 512 0) m' md'.

Lemma lh_entry_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (p k kn pad nx pv lo : Z) (errv : word),
HEAPAx A ((k, kn) :: LB) LM FRS B m md ->
rw_cells asegs m p [C8 (Z_to_bv 64 k); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pad); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 pv)] ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p mod 8 = 0 -> p + 40 <= alloc_ceiling -> (p + 40 <= 0x10000 \/ 0x645000 <= p) -> p / 8 + A_SB + 3 <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
512 <= bB B -> 0 <= bD B ->
(forall ms' md' A', lh_entry_free_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_entry_free_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ENT SHp Pal Php Pimg Psh ST LO LOS SPA HT ERR TP RA A0 BB BD K.
unfold_consts. word_range sp SPR.
pose proof (rw_cells_bound asegs m p _ ENT) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP k kn Hkal Hklo Hkhi Himg_k.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst a0 tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold lh_entry_free_A_entry, A_ERRNO in *. a4l.
carve_frame 16%nat ST.
do 3 step.
do 3 step.
step. asan_chkA.
step. step. step. sh_norm. rewrite (div8_add p 8) by lia. change (8 / 8) with 1.
step. rewrite ?sxb_zero, ?zxb_zero.
step.
step. if_false.
step. norm_sx32.
step. if_true.
asan_chkA.
step. step.

alloc_callA (hiA_free A4L HIx) blk k uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists kn. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec k 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_head in HPR2, HP2.
replace (if k =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (k =? 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST ENT SHp GOT CELL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_false.
do 4 step.
evt_done5. apply K. unfold lh_entry_free_A_post.
exists m2, r2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | exact HP2]]]]].
- unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists; reflexivity.
- release_frame FR ST2 (bv_unsigned sp). exact ST2.
Qed.

Variables (sp gp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (lo t tbl size : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (s0c s1c s2c s3c s4c rac : word).

Variable u : uwd.
Hypothesis UW : uw_at (hiA_top A4L HIx) m0 (bv_unsigned sp) (bv_unsigned s0c) u.
Hypothesis UWK : uw_ok A4L (hl_free A4H) rac u.

Definition free_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -48) [C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Notation hdr_cellsA hsz hcnt hhd htl :=
[C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free A4F)); C8 (Z_to_bv 64 (fn_lh_char_hash A4F)); C8 (Z_to_bv 64 (fn_lh_char_equal A4F))].

Definition free_exitA (errv : word) (K0 : machine_state -> config -> ASA A4L HIx -> Prop) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(hsz hcnt hhd htl : Z),
HEAPAx A ((t, 56) :: (tbl, 40 * size) :: LB) LM FRS B m md ->
rw_cells asegs m t (hdr_cellsA hsz hcnt hhd htl) ->
stk asegs m lo (bv_unsigned sp + -48) ->
free_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - Z.of_nat (length es) * 512 <= bB B -> bD B0 <= bD B ->
K0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 t) x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_SB) x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2790) fc None m (seg_rom asegs)) md A.

Lemma lh_free_loopA :
forall (k j : nat) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (errv : word) (hsz hcnt hhd htl : Z),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPAx A (map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * size) :: LB) LM FRS B m md ->
lh_slots asegs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = size ->
(forall e, In e es -> le_v e = 0) ->
rw_cells asegs m t (hdr_cellsA hsz hcnt hhd htl) ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
free_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
(Z.of_nat (length es) + 2) * 512 <= bB B0 -> uw_cost u <= bD B0 ->
bB B0 - Z.of_nat j * 512 <= bB B -> bD B0 <= bD B ->
free_exitA errv (fun ms md A => AJ5 A4L HIx A T md ms) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (t + 32)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ent_addr tbl (le_ix e))) (Z_to_bv 64 A_SB) (Z_to_bv 64 (t / 8 + 4 + A_SB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2764) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until htl; intros Hk Hj HP SL LINK Hlen VZ HDR ST LO LOS SPA HT FR ERR VM0 HPR BB0 BD0 BB BD KX.
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
assert (NX : nx_of tbl es j = 0).
{ unfold nx_of. destruct (nth_error es (S j)) eqn:E2; [|reflexivity].
pose proof (proj1 (nth_error_Some es (S j)) ltac:(rewrite E2; discriminate)). lia. }
rewrite NX in C.
unfold free_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
replace (skipn j es) with [e] in HP.
2:{ symmetry. rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
destruct (skipn j es) as [|e' tl] eqn:ES; [discriminate|]. cbn in Hj. injection Hj as ->.
apply (f_equal (@length lent)) in ES. rewrite length_skipn in ES. cbn in ES. destruct tl; [reflexivity | cbn in ES; lia]. }
cbn [map app kblk] in HP.
blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP tbl (40 * size) Hbal Hblo Hbhi Himg_b.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
shadow_nowA A4L HIx HP t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPt4.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP ltac:(right; right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 0 tbl (40 * size) HP ltac:(right; right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEPe0.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP ltac:(right; right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEPe3.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.

cbn [fn_lh_entry_free A4F]. replace (ret_pc (Z_to_bv 64 0x9bd40)) with (Z_to_bv 64 0x9bd40) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
eapply (lh_entry_free_A_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A ((t, 56) :: (tbl, 40 * size) :: LB) LM FRS B
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) 0 (pv_of tbl es j) lo errv);
[ heap_nowA A4L HIx HP MU WM MI | exact C | exact SHe | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
{ unfold ent_addr. Z.div_mod_to_equations. lia. }
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Himg_b; [left; nia | right; lia]. }
{ clia. }
{ rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
{ lia. }
{ lia. }
{ destruct u; cbn [uw_cost] in *; lia. }
intros ms2 md2 A2 (m2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). a4l.
rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. a4l.
assert (HPR' : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; in_tailA Hb]. }
clear MU WM MI ST SHt SHe SEPt4 SEPe0 SEPe3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
shadow_nowA A4L HIx HP2 t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt4.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP2 ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP2 ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPe3.
a4l.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
pose proof (rw_cells_bound asegs _ _ _ C) as EB. cbn [cells_size csize Nat.add] in EB.
assert (EA8 : ent_addr tbl (le_ix e) mod 8 = 0) by (unfold ent_addr; Z.div_mod_to_equations; lia).
step. step. step. sh_norm. rewrite (div8_add (ent_addr tbl (le_ix e)) 24) by lia. change (24 / 8) with 3.
step. rewrite ?zxb_zero. step. if_true.
step. step. if_true.
evt_done5. eapply KX; [exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | eapply model_vm_only_trans; eassumption | exact HPR'
| cbn [bB charge]; lia | cbn [bD charge]; lia].
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
destruct (nth_error es (S j)) as [e'|] eqn:E2.
2:{ exfalso. apply nth_error_None in E2. lia. }
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
unfold free_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (SK : skipn j es = e :: skipn (S j) es).
{ rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
remember (skipn j es) as sk eqn:ES. destruct sk as [|e0 tl]; [discriminate|]. cbn in Hj. injection Hj as ->.
f_equal. change tl with (skipn 1 (e :: tl)). rewrite ES, skipn_skipn. reflexivity. }
rewrite SK in HP. cbn [map app] in HP. unfold kblk at 1 in HP.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
assert (Hint : In (t, 56) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (Hinb : In (tbl, 40 * size) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
assert (Hint' : In (t, 56) (((le_k e, le_kn e) :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) ++ LM)) by (apply in_or_app; left; right; exact Hint).
assert (Hinb' : In (tbl, 40 * size) (((le_k e, le_kn e) :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) ++ LM)) by (apply in_or_app; left; right; exact Hinb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hint') as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hint') as Himg_t.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hinb') as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hinb') as Himg_b.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(right; exact Hint)) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP ltac:(right; exact Hint) ltac:(cbn; lia) Hint') as SEPt4.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP ltac:(right; exact Hinb) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 0 tbl (40 * size) HP ltac:(right; exact Hinb) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hinb') as SEPe0.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP ltac:(right; exact Hinb) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hinb') as SEPe3.
clear Hint Hinb Hint' Hinb'.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.

cbn [fn_lh_entry_free A4F]. replace (ret_pc (Z_to_bv 64 0x9bd40)) with (Z_to_bv 64 0x9bd40) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
eapply (lh_entry_free_A_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) LM FRS B
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) (ent_addr tbl (le_ix e')) (pv_of tbl es j) lo errv);
[ heap_nowA A4L HIx HP MU WM MI | exact C | exact SHe | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
{ unfold ent_addr. Z.div_mod_to_equations. lia. }
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Himg_b; [left; nia | right; lia]. }
{ clia. }
{ rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
{ lia. }
{ lia. }
{ destruct u; cbn [uw_cost] in *; lia. }
intros ms2 md2 A2 (m2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). a4l.
rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. a4l.
assert (HPR' : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; right; exact Hb | right; exact Hb]. }
clear MU WM MI ST SHt SHe SEPt4 SEPe0 SEPe3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
assert (Hinb : In (tbl, 40 * size) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
assert (Hinb' : In (tbl, 40 * size) ((map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) ++ LM)) by (apply in_or_app; left; exact Hinb).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP2 Hinb ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP2 Hinb ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hinb') as SEPe3.
clear Hinb Hinb'.
a4l.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
pose proof (rw_cells_bound asegs _ _ _ C) as EB. cbn [cells_size csize Nat.add] in EB.
assert (EA8 : ent_addr tbl (le_ix e) mod 8 = 0) by (unfold ent_addr; Z.div_mod_to_equations; lia).
step. step. step. sh_norm. rewrite (div8_add (ent_addr tbl (le_ix e)) 24) by lia. change (24 / 8) with 3.
step. rewrite ?zxb_zero. step. if_true.
step. step. unfold ent_addr. if_falsex.
evt_done5.
replace (Z_to_bv 64 (t / 8 + 2147450884)) with (Z_to_bv 64 (t / 8 + 4 + 2147450880)) by (f_equal; lia).
eapply (IH (S j) e'); first [exact E2 | exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | exact HPR' | exact KX | exact BB0 | exact BD0 | idtac].
+ lia.
+ eapply (lh_slots_pres A4H); [exact HPR2 | apply in_or_app; left; apply in_or_app; right; right; left; reflexivity | exact Hlen | exact SL].
+ split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]].
+ exact Hlen.
+ exact VZ.
+ clia.
+ lia.
+ exact SPA.
+ exact HT.
+ eapply model_vm_only_trans; eassumption.
+ cbn [bB charge]. lia.
+ cbn [bD charge]. lia.
Qed.

Definition lh_table_free_A_post (errv : word) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H rac sp gp (Z_to_bv 64 A_TP) s0c s1c s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B0 - (Z.of_nat (length es) + 2) * 512 <= bB B' /\ bD B0 - uw_cost u <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma lh_free_exit_okA : forall errv,
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
bv_unsigned rac mod 2 = 0 -> 0 <= size ->
(Z.of_nat (length es) + 2) * 512 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', lh_table_free_A_post errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
free_exitA errv (fun ms md A => AJ5 A4L HIx A T md ms).
Proof.
intros errv LO LOS SPA HT RA Hsz BB0 BD0 K. unfold free_exitA. intros until htl. intros HP HDR ST FR ERR VM0 HPR BB BD.
unfold free_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01A HIx _ _ _ _ _ _ _ _ _ _ _ HP) as Hne.
shadow_nowA A4L HIx HP t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 3 t 56 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt3.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step.

alloc_callA (hiA_free A4L HIx) blk tbl uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists (40 * size). right; left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec tbl 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
replace (if tbl =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (tbl =? 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST HDR SHt SEPt3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
do 8 step.
release_frame FR ST2 (bv_unsigned sp).
step.

alloc_callA (hiA_free A4L HIx) blk t uw u A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 56. left. reflexivity. }
all: try (solve [eapply uw_at_pre0; [eapply uw_at_heap_pres; [exact UW | exact HPR | lia] | lia]]).
all: try (solve [exact UWK]).
all: try (destruct (Z.eqb_spec t 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite lb_remove_head in HP3, HPR3.
replace (if t =? 0 then 0 else uw_cost u) with (uw_cost u) in HP3 by (destruct (Z.eqb_spec t 0); [lia | reflexivity]).
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply K. unfold lh_table_free_A_post.
exists m3, r3, (charge (charge B 512 0) 512 (uw_cost u)).
split; [apply ret_statew_same|]. split; [eapply model_vm_only_trans; [| exact VM3]; eapply model_vm_only_trans; eassumption|].
split; [exact ST3|]. split; [exact HPR|]. split; [exact ERR3|].
split; [cbn [bB charge]; lia|]. split; [cbn [bD charge]; destruct u; cbn [uw_cost] in *; lia|]. exact HP3.
Qed.

Lemma lh_table_free_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B0 m0 md0 ->
lh_open asegs A4F m0 t tbl size es svs ->
(forall e, In e es -> le_v e = 0) ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned rac mod 2 = 0 ->
a0 = Z_to_bv 64 t ->
(Z.of_nat (length es) + 2) * 512 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', lh_table_free_A_post errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR rac sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0c s1c a0 a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_table_free_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP OPEN VZ ST LO LOS SPA HT ERR RA A0 BB0 BD0 K.
destruct OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. unfold lh_blocks in HP. cbn [app] in HP.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
shadow_nowA A4L HIx HP t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 1 t 56 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt4.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m0) as MU.
subst a0. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold lh_table_free_A_entry, A_ERRNO in *. a4l.
carve_frame 48%nat ST.
do 7 step.
do 3 step.
step. step. asan_chkA.
step. cbn [fn_lh_entry_free A4F]. step. if_false.
step. asan_chkA.
step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) LM FRS B0 m1 md0) by heap_nowA A4L HIx HP MU WM MI.
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb | clia | solve_clientWA A4L HIx HP].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
pose proof (lh_free_exit_okA errv ltac:(clia) ltac:(lia) SPA HT RA ltac:(lia) BB0 BD0 K) as EXIT.
assert (SL1 : lh_slots asegs m1 tbl svs).
{ eapply (lh_slots_frame asegs m0 m1 tbl svs _ SL MU WM). intros i Hi. apply Forall_cons; [|apply Forall_nil].
cbn. unfold ent_addr. left. lia. }
rewrite hd_of_nth in *.
destruct (nth_error es 0) as [e0|] eqn:E0.
2:{
step. if_true.
evt_done5.
assert (ES : es = []) by (destruct es; [reflexivity | discriminate]). rewrite ES in HP1. cbn [map app] in HP1.
eapply EXIT; [exact HP1 | exact HDR | exact ST | exact FR | exact ERR | apply model_vm_only_refl | exact HPR1 | cbn; lia | cbn; lia]. }
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 0%nat e0 E0) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some es 0) ltac:(rewrite E0; discriminate)) as Hes0.
step. unfold ent_addr. if_falsex.
evt_done5.
replace (Z_to_bv 64 (t / 8 + 2147450884)) with (Z_to_bv 64 (t / 8 + 4 + 2147450880)) by (f_equal; lia).
eapply (lh_free_loopA (length es - 1) 0 e0);
first [ exact HDR | exact ST | exact FR | exact ERR | exact HPR1 | exact EXIT | exact SL1 | exact Hlen | exact VZ | exact SPA | exact HT | exact BB0 | exact BD0
| apply model_vm_only_refl | exact E0 | idtac ].
all: lazymatch goal with
| |- HEAPA _ _ _ _ _ _ _ _ _ =>
cbn [skipn]; eapply (heapA_perm A4L HIx); [exact HP1| | apply Permutation_refl | apply Permutation_refl];
change ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) with ([(t, 56); (tbl, 40 * size)] ++ (map kblk es ++ LB));
change (map kblk es ++ (t, 56) :: (tbl, 40 * size) :: LB) with (map kblk es ++ [(t, 56); (tbl, 40 * size)] ++ LB);
apply Permutation_app_swap_app
| |- lh_link _ _ _ => split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]]
| |- _ => first [clia | lia]
end.
Qed.
End ALhFree.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH QmZZ QTEu QRUw QKQo QnCn Q6WR QnP9 QJZd QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0 QnP9.Mq0 QJZd.Mq4 QW22.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac post_callA segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callA" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callA segs m ]
end.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF3.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Lemma mf_arrA : forall (kids : list (option jshape))
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (junk8 : list byte),
s = Sarr kids ->
HEAPAx A (BS ++ LB) LM FRS B m md ->
jval asegs A4F s m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 m junk8 ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_SB) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9ac74) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst s.
destruct (jval_arr_open asegs A4F kids m BS x 0 J) as (pb & PBS & a & ABS & ps & KBS & EBS & OPB & HDR & AL & OK). clear J.
pose proof AL as (arr & size & ajunk & EABS & Hlen & Hsz & _). subst ABS.
rewrite EBS, <- app_assoc in HP. cbn [app] in HP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HP x 48 SHx.
shadow_nowA A4L HIx HP a 32 SHa.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp + -48)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2].
rewrite EBS in BB. cbn [concat app] in BB. rewrite ?length_app in BB. cbn [length] in BB. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add in BB.
stash OPB. stash OK. stash HDR0.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32. step. step. if_falsex. step. step. if_truex.
step. if_true.
step.
asan_chkA.
step. step.

callA (array_list_length_A _ (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 x) x9 a5 a6 a7 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1
(Z_to_bv 64 a) _ _ _ _ m lo _ a arr size ps).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|]; lia).
all: try (unfold al_blkA; lia).
all: try first [exact AL | exact SHa | reflexivity].
step.
destruct kids as [|k0 kids1].
- destruct ps as [|p0 ps1]; [| cbn in L1; discriminate]. destruct KBS as [|bs KBS1]; [| cbn in L2; discriminate].
cbn [length Z.of_nat]. if_false.
step.
step.
asan_chkA.
step. step.
cbn [concat app] in HP.
unstash OPB. unstash OK. unstash HDR0.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (array_list_free_A_cps HIx _ _ gp (Z_to_bv 64 x) x9 (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F1 fc1 mc md
((x, 48) :: PBS ++ LB) LM FRS B lo a T)
with (BS := [(a, 32); (arr, 8 * size)]) (ps := []) (u := UWptr)
end.
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (lazymatch goal with Hmi : mem_inv asegs ?mc |- HEAPA _ _ _ _ _ _ _ ?mc _ =>
eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM Hmi | perm | apply Permutation_refl | apply Permutation_refl] end).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try (eapply (alist_agree asegs A4F); [exact AL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia).
all: try apply Forall_nil.
all: try (replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR4 by lia.
lazymatch type of MU with munch _ m ?mc =>
assert (HPRc : heap_pres A4H (((x, 48) :: PBS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -48) m mc)
by (eapply (heap_pres_of_munch A4H _ (bv_unsigned sp + -48)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; right; exact Hb] | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]);
pose proof (heap_pres_trans _ _ _ _ _ _ HPRc HPR4) as HPR4m
end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia].
first [ apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]
| apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4m) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]] ].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR4m | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR4m | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
clear MU WM.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. a4l.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
step.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sarr []) BS x rc T);
[ exact HP4 | lia | exact HDR0 | exact OPB4 | exact FR | exact ST4 | clia | clia | exact SPA | exact HT
| exact ERR4 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM4] | exact HPRb
| eapply fsaved_trans; [exact FS | exact FS4] | intros Hf; exact (FRM4 (FRM Hf)) | exact Hrc
| cbn [bD charge uw_cost] in *; lia
| clear - EBS BB BB0 BB4 HB00; subst BS; cbn [concat app length] in *; rewrite ?length_app in *; cbn [length] in *; lia
| clear - BB BB4 HB00; cbn [concat app length] in BB; rewrite ?Nat2Z.inj_succ in BB; lia | exact K ].
- pose proof AL as AL0. cbn [length] in L1.
rewrite L1. if_truex.
step. step.
do 6 step. lazymatch goal with STx : stk asegs _ lo (bv_unsigned sp + -48) |- _ => release_frame FR STx (bv_unsigned sp) end. step.
unstash OPB. unstash OK. unstash HDR0.
evt_done5. apply K. unfold mf_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 2, B end.
lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
assert (AG : agree_on asegs BS m mf)
by (eapply (agree_of_munch asegs); [exact MUx | exact WMx |]; intros b k Hb; cbn;
rewrite EBS in Hb;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b k HP ltac:(in_sub Hb)) as (Hk & _ & Hblo & Hbhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi; lia)
end.
split; [apply ret_statew_intro; [exact FS | exact FRM] |].
split; [exact VM0|]. split; [assumption|].
split.
{ eapply heap_pres_trans; [exact HPR |]. lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx | exact WMx |] end.
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; in_sub Hb | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]. }
split; [assumption|]. split; [lia|].
right; right. split; [reflexivity|]. split; [exact Hrc|]. split; [| split; [lia|]].
+ split; [discriminate|]. exists a, arr, size. exists pb, PBS, KBS, ps.
split; [rewrite EBS; reflexivity|]. split; [eapply opt_pbuf_agree; [exact OPB | exact AG | rewrite EBS; intros b Hb; in_sub Hb]|].
split; [assumption|].
split; [cbn [repeat]; rewrite app_nil_r; eapply (alist_agree asegs A4F); [exact AL0 | exact AG | rewrite EBS; intros b Hb; in_sub Hb]
| eapply okids_agree; [exact OK | exact AG | rewrite EBS; intros b Hb; in_sub Hb]].
+ rewrite EBS, <- app_assoc in *. cbn [app] in *.
eapply (heapA_client_frame A4L HIx); [exact HP | | assumption | assumption].
lazymatch goal with MUx : munch _ m ?mf |- _ => eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUx); apply Forall_cons; [cbn; left; lia | apply Forall_nil] end.
Qed.
End MF3.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt QugP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QugP.Mq0 QsKa.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition jo_new_array_A3 (HIx : heap_iface_A A4L) :=
jo_new_container_A_stmt HIx (fun _ => True) 0x9eb2c (32 + 32 + 4096) new_array_costA 0 0x9eb50 (Sarr []) (fun BS => arr_capA BS = 32 /\ length BS = 3%nat).

Section AJoNewArray3.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma json_object_new_array_A3_cps : jo_new_array_A3 HIx.
Proof.
unfold jo_new_array_A3, jo_new_container_A_stmt. intros until u. intros PRE _ UW UWK BB BD K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
unfold_consts. unfold new_array_costA in BB. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
subst tp. a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 32%nat ST.
do 4 step.
step. step. step.
step. step.

alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 mA md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mA) as MU.
pose proof (wmono_refl asegs mA) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex.
step. step.
do 5 step.
evt_done5. eapply (K _ md2 mA 0 A2 (charge B (16 * 48 + 512) (uw_cost u))).
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [exact VM2|]. split; [| split; [exact HPR | exists e2; exact ERR2]].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold new_array_costA. cbn [bB charge]. lia.
+ cbn [bD charge]. lia.
+ left. split; [reflexivity | exact HP2].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2) as [GOT CELL].
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 32)] mA) as MU.
pose proof (wmono_refl asegs mA) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs |- _ =>
split_for_access BLKc asegs mc r cs 16%nat 24%nat;
lazymatch type of BLKc with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
change [c1; c2; c3; c4; c5] with ([c1; c2; c3] ++ ([c4] ++ [c5])) in BLKc end;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia
end;
assert (HPc : HEAPAx A2 ((r, 48) :: LB) LM FRS (charge B (16 * 48 + 512) (uw_cost u)) mc md2) by heap_nowA A4L HIx HP2 MU WM MI
end.
clear SHr.
eapply (amemset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r 48 (r + 16) 0 24 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DST
| exact ST2 | lia | lia | replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9ebb8)) with (Z_to_bv 64 0x9ebb8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step. step. step.

evt_done5.
eapply (array_list_new2_A_cps HIx) with (LB := (r, 48) :: LB) (isz := 32) (lo := lo);
[ heap_nowA A4L HIx HP2 MU WM MI4 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact ST4 | reflexivity | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (unfold al_new2_costB; cbn [bB bD charge]; lia).
all: try match goal with H : rw_cells asegs ?mx (6434400 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms3 md3 A3 (mB & r2 & e3 & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & BB3 & BD3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR3 by lia.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
lazymatch goal with H1 : rw_cells asegs _ r _, H2 : rw_cells asegs _ (r + 16) _, H3 : rw_cells asegs _ (r + 40) _ |- _ =>
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in H1; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]];
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in H2; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]];
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in H3; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]
end.
a4l. clear MU WM MI4. try clear MI.
destruct OUT3 as [(-> & HP3) | (Hr2 & arr & AL3 & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step.
asan_chkA.
stepz.
step. if_false.
step. step.

clear SHr.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); destruct u; unfold al_new2_costB in *; cbn [bB bD charge uw_cost] in *; lia).
all: try match goal with H : rw_cells asegs ?mx (6434400 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms4 mC md4 A4 r4 RS4 VM4 ST4' HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP4 by (destruct (Z.eqb_spec r 0); reflexivity).
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4' by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl asegs mC) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
step. step.
do 5 step.
evt_done5. eapply (K _ md4 mC 0 A4 (charge B3 512 0)).
* unfold jo_post_frameA.
split; [| split; [| split; [| split; [exact HPR | exists e3; exact ERR4]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM4].
-- release_frame FR ST4' (bv_unsigned sp). exact ST4'.
* unfold new_array_costA, al_new2_costB in *. cbn [bB charge] in *. lia.
* cbn [bD charge uw_cost] in *. lia.
* left. split; [reflexivity | exact HP4].
+
pose proof AL3 as (arr_ & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR).
assert (Esz : size = 32 /\ arr_ = arr) by (injection EBS; intros; lia). destruct Esz as [Esz ->]. subst size. cbn [app] in HP3.
pose proof (rw_cells_bound asegs mB r2 _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 r2 32 Hr2al Hr2lo Hr2hi Himg_r2.
blk_factsA A4L HIx HP3 arr (8 * 32) Haal Halo Hahi Himg_arr.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Harr : arr <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]. inversion Hnd as [|x' l' Hni' Hnd']. apply Hni'. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r2 32 r 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * 32) r 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harr) as Hdj2.
shadow_nowA A4L HIx HP3 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEP5'.
a4l. clear AHDR AARR.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step.
asan_chkA.
step.
step. if_truex.
step.
do 5 step.
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) => eapply (K _ md3 mf r A3 B3) end.
* unfold jo_post_frameA.
split; [| split; [| split; [| split; [ | exists e3; assumption]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- release_frame FR ST3 (bv_unsigned sp). exact ST3.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; right; right; right; exact Hb | clia | solve_clientWA A4L HIx HP3].
* unfold new_array_costA, al_new2_costB in *. cbn [bB charge] in *. lia.
* cbn [bD charge uw_cost] in *. lia.
* right. split; [exact Hr|]. exists [(r, 48); (r2, 32); (arr, 8 * 32)]. split; [| split].
-- lazymatch goal with BLKh : rw_cells asegs ?mf r _ |- jval _ _ _ ?mf _ _ _ =>
cbn [jval]; exists 0, [], [(r, 48); (r2, 32); (arr, 8 * 32)]; split; [reflexivity|]; split; [left; split; reflexivity|];
exists r2, [(r2, 32); (arr, 8 * 32)], [], []; split; [reflexivity|]; split; [| split; [| split; [reflexivity | split; [reflexivity | exact I]]]]
end.
++ unfold jhdr_cells. cbn [fn_arr_to_json_string A4F app].
lazymatch goal with H1 : rw_cells asegs ?mf r _, H2 : rw_cells asegs ?mf (r + 16) _, H3 : rw_cells asegs ?mf (r + 40) _ |- rw_cells _ ?mf r ?cs =>
lazymatch cs with [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] => change cs with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7])) end;
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add]; split; [exact H1|];
replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
replace (r + 16 + Z.of_nat 24) with (r + 40) by lia; split; [| exact H3];
eapply rw_cells_recast; [exact H2 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]
end.
++ eapply (alist_agree asegs A4F); [exact AL3 | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- split; [unfold arr_capA; cbn; reflexivity | reflexivity].
-- cbn [app].
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP3
(Permutation_sym (Permutation_middle [(r2, 32); (arr, 8 * 32)] LB (r, 48))) (Permutation_refl LM) (Permutation_refl FRS)) as HP3'.
cbn [app] in HP3'.
eapply (heapA_client_frame A4L HIx); [exact HP3' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3' MU); solve_frameW_withA HP3' | exact WM | assumption].
Qed.
End AJoNewArray3.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw Q2Do Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Qvbw.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 Q2Do.Mq2 Q2Do.Mq0 QsKa.Mq4 QlKV.Mq2 QsKa Q9O6.Mq1 QW22.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Stmts2J.
Variable HIx : heap_iface_A A4L.
Definition jo_array_add_A2J_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v : Z)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (ABS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> jopt asegs A4F vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
Z.of_nat (length kids) + 1 < 2^28 ->
arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bD B <= bD B' ->
((r = 0 /\ exists ABS', jval asegs A4F (Sarr (kids ++ [vs])) m' ABS' p 1 /\ length ABS' = (length ABS + length VBS)%nat /\
arr_grownA (arr_capA ABS) (Z.of_nat (length kids)) (arr_capA ABS') /\
bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md' /\
(forall w wv, jtx (Sarr kids) ABS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sarr (kids ++ [vs])) ABS' = Some (w + (2 + wv), []))) \/
(r = 2^64 - 1 /\ bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
jval asegs A4F (Sarr kids) m' ABS p 1 /\ jopt asegs A4F vs m' VBS v /\
HEAPA A4L HIx A' (ABS ++ VBS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End Stmts2J.
Definition jo_array_add_A2J (HIx : heap_iface_A A4L) := jo_array_add_A2J_stmt HIx 0x9ecf4 (16 + 96 + 4096).

Section Stmts2Js.
Variable HIx : heap_iface_A A4L.
Definition jo_array_shrink_A2J_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_preA HIx A (ABS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
Z.of_nat (length kids) < 2^28 ->
arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
(exists ABS', jval asegs A4F (Sarr kids) m' ABS' p 1 /\ length ABS' = length ABS /\
(arr_capA ABS' = arr_capA ABS \/ (r = 0 /\ arr_capA ABS' = Z.max (Z.of_nat (length kids)) 1)) /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md' /\
(forall w, jtx (Sarr kids) ABS = Some (w, []) -> jtx (Sarr kids) ABS' = Some (w, []))) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End Stmts2Js.
Definition jo_array_shrink_A2J (HIx : heap_iface_A A4L) := jo_array_shrink_A2J_stmt HIx 0x9ed6c (16 + 48 + 4096).

Section AJoArrShrink2J.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma json_object_array_shrink_A2J_cps : jo_array_shrink_A2J HIx.
Proof.
unfold jo_array_shrink_A2J, jo_array_shrink_A2J_stmt. intros until errv. intros PRE J A0 A1 Hlen28 BB K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
destruct (sarr_open asegs A4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & ajunk & EAL & Hlen & Hsz & _). subst AL.
assert (Esize : size = arr_capA ABS /\ a_ = a /\ arr_ = arr) by (rewrite EABS in EBS; cbn [app] in EBS; injection EBS; intros; lia).
destruct Esize as (Esize & -> & ->). rewrite <- Esize in *. clear EABS rest_ Hcap1 Hcap2 Hcap3. subst ABS.

assert (HPa : HEAPAx A ((a, 32) :: (arr, 8 * size) :: ((p, 48) :: concat KBS ++ PBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
set (LBR := (p, 48) :: concat KBS ++ PBS ++ LB) in HPa.
assert (INp : In (p, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBS) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HPa p 48 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HPa a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HPa arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HPa p 48 SHp.
a4l. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash OPB. stash KIDS. stash HAL. clear J.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1 tp.
carve_frame 16%nat ST.
step. step.
step. if_false.
step. step. step.
step.
asan_chkA.
step.
step. step.
release_frame FR ST (bv_unsigned sp).
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LBR) LM FRS B m1 md) by heap_nowA A4L HIx HPa MU WM MI.
assert (HPR1 : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPa | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HPa]. }
assert (AG1 : agree_on asegs LBR m m1) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
unstash OPB. unstash KIDS. unstash HAL.
step.
evt_done5.
eapply (array_list_shrink_A_cps HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 md LBR LM FRS B lo a arr size ps T);
[ exact HP1
| eapply (alist_agree asegs A4F); [exact HAL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia
| rewrite L1; lia
| exact ST | clia | lia | exact SPA | exact HT | eassumption | exact RA | reflexivity | reflexivity
| intros Hne; unfold al_shrink_costB, arr_shrink_costA in *; rewrite ?L1 in Hne |- *; destruct (Z.eqb_spec (Z.of_nat (length kids)) size); lia
| exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms' md' A' (m' & r & errv' & arr' & size' & B' & RS & VM & ST' & HPR' & ERR' & BB' & BD' & HP' & AL' & OUT).
assert (HPR'' : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m') by (eapply heap_pres_trans; [exact HPR1 | exact HPR']).
assert (AG : agree_on asegs LBR m m') by (eapply (agree_of_heap_pres asegs A4H); [exact HPR'' | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K ms' md' m' r A' B').
- unfold jo_post_frameA. split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [| exists errv'; exact ERR'].
eapply heap_pres_weaken; [exact HPR'' | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply HiL; exact Hb | right; exact Hb]].
- unfold al_shrink_costB, arr_shrink_costA in *. rewrite L1 in BB'. exact BB'.
- exact BD'.
- exists (((p, 48) :: [(a, 32); (arr', 8 * size')] ++ concat KBS) ++ PBS). split; [| split; [rewrite !length_app; reflexivity | split; [| split]]].
+ eapply (sarr_close asegs A4F); try reflexivity.
* eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
* unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR'); [exact HDR | eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
* exact AL'.
* exact L1.
* exact L2.
* eapply akids_agree; [exact KIDS | exact AG | exact HiK].
+ destruct OUT as [(-> & -> & ->) | (-> & ->)]; unfold arr_capA; cbn [app nth snd];
[left | right; split; [reflexivity|]]; rewrite ?L1; Z.div_mod_to_equations; lia.
+ eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl].
+ intros w Hw. cbn [app] in Hw |- *. rewrite jtx_arr_eq in Hw |- *. exact Hw.
Qed.
End AJoArrShrink2J.

Section AJoArrAdd2J.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma jopt_valAJ : forall A LBall LM FRS B m md s bs v,
HEAPAx A LBall LM FRS B m md -> incl bs LBall -> jopt asegs A4F s m bs v -> 0 <= v /\ v + 1 <= alloc_ceiling.
Proof.
intros A LBall LM FRS B m md [s'|] bs v HP Hi J; cbn in J.
- destruct J as [Hv J]. destruct (jval_root_in asegs A4F _ _ _ _ _ J) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; exact (Hi _ Hin))) as (_ & _ & Hlo & Hhi & _). lia.
- destruct J as [-> _]. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
Qed.

Lemma json_object_array_add_A2J_cps : jo_array_add_A2J HIx.
Proof.
unfold jo_array_add_A2J, jo_array_add_A2J_stmt. intros until errv. intros PRE J JOB A0 A1 Hlen28 BB K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
destruct (sarr_open asegs A4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & ajunk & EAL & Hlen & Hsz & _). subst AL.
assert (Esize : size = arr_capA ABS /\ a_ = a /\ arr_ = arr) by (rewrite EABS in EBS; cbn [app] in EBS; injection EBS; intros; lia).
destruct Esize as (Esize & -> & ->). rewrite <- Esize in *. clear EABS rest_ Hcap1 Hcap2 Hcap3. subst ABS.

assert (HPa : HEAPAx A ((a, 32) :: (arr, 8 * size) :: ((p, 48) :: concat KBS ++ PBS ++ VBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
set (LBR := (p, 48) :: concat KBS ++ PBS ++ VBS ++ LB) in HPa.
assert (INp : In (p, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBS) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
pose proof (jopt_valAJ _ _ _ _ _ _ _ vs VBS v HPa ltac:(intros b Hb; right; right; apply HiV; exact Hb) JOB) as Hv.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hv.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HPa p 48 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HPa a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HPa arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HPa p 48 SHp.
a4l. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash OPB. stash KIDS. stash HAL. stash JOB. clear J.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1 tp.
carve_frame 16%nat ST.
step. step.
step. step. step.
step.
asan_chkA.
step.
step. step.
release_frame FR ST (bv_unsigned sp).
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LBR) LM FRS B m1 md) by heap_nowA A4L HIx HPa MU WM MI.
assert (HPR1 : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPa | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HPa]. }
assert (AG1 : agree_on asegs LBR m m1) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
unstash OPB. unstash KIDS. unstash HAL. unstash JOB.
step.
evt_done5.
eapply (array_list_add_A_cps HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 md LBR LM FRS B lo a arr size v ps T);
[ exact HP1
| eapply (alist_agree asegs A4F); [exact HAL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia
| rewrite L1; lia | lia
| exact ST | clia | lia | exact SPA | exact HT | eassumption | exact RA | reflexivity | reflexivity
| intros Hge; unfold al_add_costB, arr_add_costA in *; rewrite ?L1 in Hge |- *; destruct (Z.ltb_spec (Z.of_nat (length kids) + 1) size); lia
| exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms' md' A' (m' & r & errv' & arr' & size' & B' & RS & VM & ST' & HPR' & ERR' & BD' & HP' & OUT).
assert (HPR'' : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m') by (eapply heap_pres_trans; [exact HPR1 | exact HPR']).
assert (AG : agree_on asegs LBR m m') by (eapply (agree_of_heap_pres asegs A4H); [exact HPR'' | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K ms' md' m' r A' B').
- unfold jo_post_frameA. split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [| exists errv'; exact ERR'].
eapply heap_pres_weaken; [exact HPR'' | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply HiL; exact Hb | right; exact Hb]].
- exact BD'.
- destruct OUT as [(-> & -> & -> & Hgr & BBf & AL') | (-> & AL' & CASES)].
+ right. split; [reflexivity|]. split; [unfold al_add_costB, arr_add_costA in *; rewrite <- ?L1 in Hgr; destruct (Z.ltb_spec (Z.of_nat (length kids) + 1) size); lia|].
split; [| split].
* eapply (sarr_close asegs A4F) with (AL := [(a, 32); (arr, 8 * size)]) (KBS := KBS) (PBS := PBS) (pb := pb); try eassumption; try reflexivity.
-- eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
-- unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR'); [exact HDR | eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
-- eapply akids_agree; [exact KIDS | exact AG | exact HiK].
* eapply jopt_agree; [exact JOB | exact AG | exact HiV].
* eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl].
+ left. split; [reflexivity|]. exists (((p, 48) :: [(a, 32); (arr', 8 * size')] ++ concat (KBS ++ [VBS])) ++ PBS). split; [| split; [rewrite concat_app; cbn [concat]; rewrite !length_app; cbn [length]; rewrite ?app_nil_r, ?length_app; cbn [length Nat.add]; do 3 f_equal; rewrite <- !Nat.add_assoc; f_equal; apply Nat.add_comm | split; [| split; [| split]]]].
* eapply (sarr_close asegs A4F) with (ps := ps ++ [v]); try reflexivity.
-- eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
-- unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR'); [exact HDR | eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
-- exact AL'.
-- rewrite !length_app. cbn [length]. lia.
-- rewrite !length_app. cbn [length]. lia.
-- apply akids_app; [eapply akids_agree; [exact KIDS | exact AG | exact HiK] | apply akids_one; eapply jopt_agree; [exact JOB | exact AG | exact HiV]].
* unfold arr_grownA, arr_capA. cbn [app nth snd]. rewrite ?L1 in CASES.
destruct CASES as [(-> & -> & Hlt & _) | (-> & Hge & _)]; [left | right]; Z.div_mod_to_equations; lia.
* unfold al_add_costB, arr_add_costA in *. rewrite ?L1 in CASES. rewrite ?L1.
destruct (Z.ltb_spec (Z.of_nat (length kids) + 1) size); destruct CASES as [(_ & _ & Hlt & BBx) | (_ & Hge & BBx)]; lia.
* rewrite concat_app. cbn [concat]. rewrite app_nil_r.
eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl].
* intros w wv Hw Hwv. exact (arr_add_jtx asegs A4F m kids ps KBS PBS (p, 48) (a, 32) (arr, 8 * size) (arr', 8 * size') vs VBS w wv KIDS Hw Hwv).
Qed.
End AJoArrAdd2J.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4 QnP9 QJZd.Mqd QW22.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac post_callA segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callA" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callA segs m ]
end.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF3.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Lemma mf_arrA : forall (kids : list (option jshape))
(x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud),
s = Sarr kids ->
HEAPAx A (BS ++ LB) LM FRS B m md ->
jval asegs A4F s m BS x 0 ->
mf_frameA ra sp s0 s1 s2 s3 s4 s5 s6 m ->
stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 <= bB B -> 512 * Z.of_nat (length BS) <= bB B ->
KPOSTA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc T ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c30c) fc1 None m (seg_rom asegs)).
Proof.
intros until B. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB0 BB K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst s.
destruct (jval_arr_open asegs A4F kids m BS x 0 J) as (pb & PBS & a & ABS & ps & KBS & EBS & OPB & HDR & AL & OK). clear J.
pose proof AL as (arr & size & ajunk & EABS & Hlen & Hsz & _). subst ABS.
rewrite EBS, <- app_assoc in HP. cbn [app] in HP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB00 HD00].
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HP arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HP x 48 SHx.
shadow_nowA A4L HIx HP a 32 SHa.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp + -64)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2].
rewrite EBS in BB. cbn [concat app] in BB. rewrite ?length_app in BB. cbn [length] in BB. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add in BB.
stash OPB. stash OK. stash HDR0.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32. bstep. bstep. if_falsex. bstep. bstep. if_truex.
bstep. if_true.
bstep.
asan_chkA.
bstep. bstep.

callA (array_list_length_A _ (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 x) x9 a5 a6 a7 x18 (Z_to_bv 64 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1
(Z_to_bv 64 a) _ _ _ _ m lo _ a arr size ps).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|]; lia).
all: try (unfold al_blkA; lia).
all: try first [exact AL | exact SHa | reflexivity].
bstep.
destruct kids as [|k0 kids1].
- destruct ps as [|p0 ps1]; [| cbn in L1; discriminate]. destruct KBS as [|bs KBS1]; [| cbn in L2; discriminate].
cbn [length Z.of_nat]. if_false.
bstep.
bstep.
asan_chkA.
bstep. bstep.
cbn [concat app] in HP.
unstash OPB. unstash OK. unstash HDR0.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (array_list_free_A_cps HIx _ _ gp (Z_to_bv 64 x) x9 x18 (Z_to_bv 64 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 F1 fc1 mc md
((x, 48) :: PBS ++ LB) LM FRS B lo a T)
with (BS := [(a, 32); (arr, 8 * size)]) (ps := []) (u := UWptr)
end.
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (lazymatch goal with Hmi : mem_inv asegs ?mc |- HEAPA _ _ _ _ _ _ _ ?mc _ =>
eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM Hmi | perm | apply Permutation_refl | apply Permutation_refl] end).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try (eapply (alist_agree asegs A4F); [exact AL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia).
all: try apply Forall_nil.
all: try (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR4 by lia.
lazymatch type of MU with munch _ m ?mc =>
assert (HPRc : heap_pres A4H (((x, 48) :: PBS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -64) m mc)
by (eapply (heap_pres_of_munch A4H _ (bv_unsigned sp + -64)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; right; exact Hb] | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]);
pose proof (heap_pres_trans _ _ _ _ _ _ HPRc HPR4) as HPR4m
end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia].
first [ apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]
| apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4m) in HDR0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]] ].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR4m | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_weaken; [exact HPR4m | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]]. }
clear MU WM.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. a4l.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
bstep.
evt_done5.
eapply (mf_genA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv (Sarr []) BS x rc T);
[ exact HP4 | lia | exact HDR0 | exact OPB4 | exact FR | exact ST4 | clia | clia | exact SPA | exact HT
| exact ERR4 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM4] | exact HPRb
| eapply fsaved_trans; [exact FS | exact FS4] | intros Hf; exact (FRM4 (FRM Hf)) | exact Hrc
| cbn [bD charge uw_cost] in *; lia
| clear - EBS BB BB0 BB4 HB00; subst BS; cbn [concat app length] in *; rewrite ?length_app in *; cbn [length] in *; lia
| clear - BB BB4 HB00; cbn [concat app length] in BB; rewrite ?Nat2Z.inj_succ in BB; lia | exact K ].
- pose proof AL as AL0. cbn [length] in L1.
rewrite L1. if_truex.
bstep. bstep.
do 9 bstep. lazymatch goal with STx : stk asegs _ lo (bv_unsigned sp + -64) |- _ => release_frame FR STx (bv_unsigned sp) end. bstep.
unstash OPB. unstash OK. unstash HDR0.
evt_done5. apply K. unfold mf_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, 2, B end.
lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
assert (AG : agree_on asegs BS m mf)
by (eapply (agree_of_munch asegs); [exact MUx | exact WMx |]; intros b k Hb; cbn;
rewrite EBS in Hb;
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b k HP ltac:(in_sub Hb)) as (Hk & _ & Hblo & Hbhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi; lia)
end.
split; [apply ret_statew_intro; [exact FS | exact FRM] |].
split; [exact VM0|]. split; [assumption|].
split.
{ eapply heap_pres_trans; [exact HPR |]. lazymatch goal with MUx : munch _ m ?mf, WMx : wmono asegs m ?mf |- _ =>
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx | exact WMx |] end.
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; in_sub Hb | clia | apply Forall_cons; [cbn; left; lia | apply Forall_nil]]. }
split; [assumption|]. split; [lia|].
right; right. split; [reflexivity|]. split; [exact Hrc|]. split; [| split; [lia|]].
+ split; [discriminate|]. exists a, arr, size. exists pb, PBS, KBS, ps.
split; [rewrite EBS; reflexivity|]. split; [eapply opt_pbuf_agree; [exact OPB | exact AG | rewrite EBS; intros b Hb; in_sub Hb]|].
split; [assumption|].
split; [cbn [repeat]; rewrite app_nil_r; eapply (alist_agree asegs A4F); [exact AL0 | exact AG | rewrite EBS; intros b Hb; in_sub Hb]
| eapply okids_agree; [exact OK | exact AG | rewrite EBS; intros b Hb; in_sub Hb]].
+ rewrite EBS, <- app_assoc in *. cbn [app] in *.
eapply (heapA_client_frame A4L HIx); [exact HP | | assumption | assumption].
lazymatch goal with MUx : munch _ m ?mf |- _ => eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUx); apply Forall_cons; [cbn; left; lia | apply Forall_nil] end.
Qed.
End MF3.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QpNt.Mq8 QugP.Mq2 QsKa.Mqd.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition jo_new_array_A3 (HIx : heap_iface_A A4L) :=
jo_new_container_A_stmt HIx (fun _ => True) 0xa074c (32 + 32 + 4096) new_array_costA 0 0xa0770 (Sarr []) (fun BS => arr_capA BS = 32 /\ length BS = 3%nat).

Section AJoNewArray3.
Variable HIx : heap_iface_A A4L.

Lemma json_object_new_array_A3_cps : jo_new_array_A3 HIx.
Proof.
unfold jo_new_array_A3, jo_new_container_A_stmt. intros until u. intros PRE _ UW UWK BB BD K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
unfold_consts. unfold new_array_costA in BB. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
subst tp. a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 32%nat ST.
do 4 bstep.
bstep. bstep. bstep.
bstep. bstep.

alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 mA md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mA) as MU.
pose proof (wmono_refl asegs mA) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_truex.
bstep. bstep.
do 5 bstep.
evt_done5. eapply (K _ md2 mA 0 A2 (charge B (16 * 48 + 512) (uw_cost u))).
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [exact VM2|]. split; [| split; [exact HPR | exists e2; exact ERR2]].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold new_array_costA. cbn [bB charge]. lia.
+ cbn [bD charge]. lia.
+ left. split; [reflexivity | exact HP2].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2) as [GOT CELL].
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 32)] mA) as MU.
pose proof (wmono_refl asegs mA) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex.
bstep.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstep. bstepz.
asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
clear SHr.
bstep. bstep. bstep. bstep.

evt_done5.
eapply (array_list_new2_A_cps HIx) with (LB := (r, 48) :: LB) (isz := 32) (lo := lo);
[ heap_nowA A4L HIx HP2 MU WM MI | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact ST2 | reflexivity | lia
| replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (unfold al_new2_costB; cbn [bB bD charge]; lia).
all: try match goal with H : rw_cells asegs ?mx (6444320 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms3 md3 A3 (mB & r2 & e3 & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & BB3 & BD3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR3 by lia.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
lazymatch goal with H1 : rw_cells asegs _ r _ |- _ =>
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in H1; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]
end.
a4l. clear MU WM. try clear MI.
destruct OUT3 as [(-> & HP3) | (Hr2 & arr & AL3 & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep.
asan_chkA.
bstepz.
bstep. if_false.
bstep. bstep.

clear SHr.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); destruct u; unfold al_new2_costB in *; cbn [bB bD charge uw_cost] in *; lia).
all: try match goal with H : rw_cells asegs ?mx (6444320 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms4 mC md4 A4 r4 RS4 VM4 ST4' HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP4 by (destruct (Z.eqb_spec r 0); reflexivity).
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4' by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl asegs mC) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
bstep. bstep.
do 5 bstep.
evt_done5. eapply (K _ md4 mC 0 A4 (charge B3 512 0)).
* unfold jo_post_frameA.
split; [| split; [| split; [| split; [exact HPR | exists e3; exact ERR4]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM4].
-- release_frame FR ST4' (bv_unsigned sp). exact ST4'.
* unfold new_array_costA, al_new2_costB in *. cbn [bB charge] in *. lia.
* cbn [bD charge uw_cost] in *. lia.
* left. split; [reflexivity | exact HP4].
+
pose proof AL3 as (arr_ & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR).
assert (Esz : size = 32 /\ arr_ = arr) by (injection EBS; intros; lia). destruct Esz as [Esz ->]. subst size. cbn [app] in HP3.
pose proof (rw_cells_bound asegs mB r2 _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 r2 32 Hr2al Hr2lo Hr2hi Himg_r2.
blk_factsA A4L HIx HP3 arr (8 * 32) Haal Halo Hahi Himg_arr.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Harr : arr <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]. inversion Hnd as [|x' l' Hni' Hnd']. apply Hni'. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r2 32 r 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * 32) r 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harr) as Hdj2.
shadow_nowA A4L HIx HP3 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEP5'.
a4l. clear AHDR AARR.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep.
asan_chkA.
bstep.
bstep. if_truex.
bstep.
do 5 bstep.
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) => eapply (K _ md3 mf r A3 B3) end.
* unfold jo_post_frameA.
split; [| split; [| split; [| split; [ | exists e3; assumption]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- release_frame FR ST3 (bv_unsigned sp). exact ST3.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; right; right; right; exact Hb | clia | solve_clientWA A4L HIx HP3].
* unfold new_array_costA, al_new2_costB in *. cbn [bB charge] in *. lia.
* cbn [bD charge uw_cost] in *. lia.
* right. split; [exact Hr|]. exists [(r, 48); (r2, 32); (arr, 8 * 32)]. split; [| split].
-- lazymatch goal with BLKh : rw_cells asegs ?mf r _ |- jval _ _ _ ?mf _ _ _ =>
cbn [jval]; exists 0, [], [(r, 48); (r2, 32); (arr, 8 * 32)]; split; [reflexivity|]; split; [left; split; reflexivity|];
exists r2, [(r2, 32); (arr, 8 * 32)], [], []; split; [reflexivity|]; split; [| split; [| split; [reflexivity | split; [reflexivity | exact I]]]]
end.
++ unfold jhdr_cells. cbn [fn_arr_to_json_string A4F app].

lazymatch goal with BLKc : rw_cells asegs ?mf r _ |- rw_cells _ ?mf r _ => exact BLKc end.
++ eapply (alist_agree asegs A4F); [exact AL3 | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- split; [unfold arr_capA; cbn; reflexivity | reflexivity].
-- cbn [app].
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP3
(Permutation_sym (Permutation_middle [(r2, 32); (arr, 8 * 32)] LB (r, 48))) (Permutation_refl LM) (Permutation_refl FRS)) as HP3'.
cbn [app] in HP3'.
eapply (heapA_client_frame A4L HIx); [exact HP3' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3' MU); solve_frameW_withA HP3' | exact WM | assumption].
Qed.
End AJoNewArray3.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Qvbw.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg Q2Do.Mq5 Q2Do.Mq4 QsKa.Mqd. Import QlKV.Mq2 QsKa Q9O6.Mq1. Import QW22.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Stmts2J.
Variable HIx : heap_iface_A A4L.
Definition jo_array_add_A2J_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v : Z)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (ABS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> jopt asegs A4F vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
Z.of_nat (length kids) + 1 < 2^28 ->
arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bD B <= bD B' ->
((r = 0 /\ exists ABS', jval asegs A4F (Sarr (kids ++ [vs])) m' ABS' p 1 /\ length ABS' = (length ABS + length VBS)%nat /\
arr_grownA (arr_capA ABS) (Z.of_nat (length kids)) (arr_capA ABS') /\
bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md' /\
(forall w wv, jtx (Sarr kids) ABS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sarr (kids ++ [vs])) ABS' = Some (w + (2 + wv), []))) \/
(r = 2^64 - 1 /\ bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
jval asegs A4F (Sarr kids) m' ABS p 1 /\ jopt asegs A4F vs m' VBS v /\
HEAPA A4L HIx A' (ABS ++ VBS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End Stmts2J.
Definition jo_array_add_A2J (HIx : heap_iface_A A4L) := jo_array_add_A2J_stmt HIx 0xa097c (16 + 96 + 4096).

Section Stmts2Js.
Variable HIx : heap_iface_A A4L.
Definition jo_array_shrink_A2J_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_preA HIx A (ABS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
Z.of_nat (length kids) < 2^28 ->
arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
(exists ABS', jval asegs A4F (Sarr kids) m' ABS' p 1 /\ length ABS' = length ABS /\
(arr_capA ABS' = arr_capA ABS \/ (r = 0 /\ arr_capA ABS' = Z.max (Z.of_nat (length kids)) 1)) /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md' /\
(forall w, jtx (Sarr kids) ABS = Some (w, []) -> jtx (Sarr kids) ABS' = Some (w, []))) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End Stmts2Js.
Definition jo_array_shrink_A2J (HIx : heap_iface_A A4L) := jo_array_shrink_A2J_stmt HIx 0xa0a14 (16 + 48 + 4096).

Section AJoArrShrink2J.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma json_object_array_shrink_A2J_cps : jo_array_shrink_A2J HIx.
Proof.
unfold jo_array_shrink_A2J, jo_array_shrink_A2J_stmt. intros until errv. intros PRE J A0 A1 Hlen28 BB K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
destruct (sarr_open asegs A4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & ajunk & EAL & Hlen & Hsz & _). subst AL.
assert (Esize : size = arr_capA ABS /\ a_ = a /\ arr_ = arr) by (rewrite EABS in EBS; cbn [app] in EBS; injection EBS; intros; lia).
destruct Esize as (Esize & -> & ->). rewrite <- Esize in *. clear EABS rest_ Hcap1 Hcap2 Hcap3. subst ABS.

assert (HPa : HEAPAx A ((a, 32) :: (arr, 8 * size) :: ((p, 48) :: concat KBS ++ PBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
set (LBR := (p, 48) :: concat KBS ++ PBS ++ LB) in HPa.
assert (INp : In (p, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBS) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HPa p 48 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HPa a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HPa arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HPa p 48 SHp.
a4l. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash OPB. stash KIDS. stash HAL. clear J.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1 tp.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_false.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep. bstep.
release_frame FR ST (bv_unsigned sp).
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LBR) LM FRS B m1 md) by heap_nowA A4L HIx HPa MU WM MI.
assert (HPR1 : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPa | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HPa]. }
assert (AG1 : agree_on asegs LBR m m1) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
unstash OPB. unstash KIDS. unstash HAL.
bstep.
evt_done5.
eapply (array_list_shrink_A_cps HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 md LBR LM FRS B lo a arr size ps T);
[ exact HP1
| eapply (alist_agree asegs A4F); [exact HAL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia
| rewrite L1; lia
| exact ST | clia | lia | exact SPA | exact HT | eassumption | exact RA | reflexivity | reflexivity
| intros Hne; unfold al_shrink_costB, arr_shrink_costA in *; rewrite ?L1 in Hne |- *; destruct (Z.eqb_spec (Z.of_nat (length kids)) size); lia
| exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms' md' A' (m' & r & errv' & arr' & size' & B' & RS & VM & ST' & HPR' & ERR' & BB' & BD' & HP' & AL' & OUT).
assert (HPR'' : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m') by (eapply heap_pres_trans; [exact HPR1 | exact HPR']).
assert (AG : agree_on asegs LBR m m') by (eapply (agree_of_heap_pres asegs A4H); [exact HPR'' | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K ms' md' m' r A' B').
- unfold jo_post_frameA. split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [| exists errv'; exact ERR'].
eapply heap_pres_weaken; [exact HPR'' | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply HiL; exact Hb | right; exact Hb]].
- unfold al_shrink_costB, arr_shrink_costA in *. rewrite L1 in BB'. exact BB'.
- exact BD'.
- exists (((p, 48) :: [(a, 32); (arr', 8 * size')] ++ concat KBS) ++ PBS). split; [| split; [rewrite !length_app; reflexivity | split; [| split]]].
+ eapply (sarr_close asegs A4F); try reflexivity.
* eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
* unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR'); [exact HDR | eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
* exact AL'.
* exact L1.
* exact L2.
* eapply akids_agree; [exact KIDS | exact AG | exact HiK].
+ destruct OUT as [(-> & -> & ->) | (-> & ->)]; unfold arr_capA; cbn [app nth snd];
[left | right; split; [reflexivity|]]; rewrite ?L1; Z.div_mod_to_equations; lia.
+ eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl].
+ intros w Hw. cbn [app] in Hw |- *. rewrite jtx_arr_eq in Hw |- *. exact Hw.
Qed.
End AJoArrShrink2J.

Section AJoArrAdd2J.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma jopt_valAJ : forall A LBall LM FRS B m md s bs v,
HEAPAx A LBall LM FRS B m md -> incl bs LBall -> jopt asegs A4F s m bs v -> 0 <= v /\ v + 1 <= alloc_ceiling.
Proof.
intros A LBall LM FRS B m md [s'|] bs v HP Hi J; cbn in J.
- destruct J as [Hv J]. destruct (jval_root_in asegs A4F _ _ _ _ _ J) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; exact (Hi _ Hin))) as (_ & _ & Hlo & Hhi & _). lia.
- destruct J as [-> _]. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
Qed.

Lemma json_object_array_add_A2J_cps : jo_array_add_A2J HIx.
Proof.
unfold jo_array_add_A2J, jo_array_add_A2J_stmt. intros until errv. intros PRE J JOB A0 A1 Hlen28 BB K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (arr_capA_jval _ _ _ _ _ J) as (a_ & arr_ & rest_ & EABS & Hcap1 & Hcap2 & Hcap3).
destruct (sarr_open asegs A4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & ajunk & EAL & Hlen & Hsz & _). subst AL.
assert (Esize : size = arr_capA ABS /\ a_ = a /\ arr_ = arr) by (rewrite EABS in EBS; cbn [app] in EBS; injection EBS; intros; lia).
destruct Esize as (Esize & -> & ->). rewrite <- Esize in *. clear EABS rest_ Hcap1 Hcap2 Hcap3. subst ABS.

assert (HPa : HEAPAx A ((a, 32) :: (arr, 8 * size) :: ((p, 48) :: concat KBS ++ PBS ++ VBS ++ LB)) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
set (LBR := (p, 48) :: concat KBS ++ PBS ++ VBS ++ LB) in HPa.
assert (INp : In (p, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBS) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
pose proof (jopt_valAJ _ _ _ _ _ _ _ vs VBS v HPa ltac:(intros b Hb; right; right; apply HiV; exact Hb) JOB) as Hv.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hv.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HPa p 48 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HPa a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HPa arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HPa p 48 SHp.
a4l. unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
stash OPB. stash KIDS. stash HAL. stash JOB. clear J.
reenterA asegs A4L HIx asegs_wx HP. subst a0 a1 tp.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
bstep.
asan_chkA.
bstep.
bstep. bstep.
release_frame FR ST (bv_unsigned sp).
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A ((a, 32) :: (arr, 8 * size) :: LBR) LM FRS B m1 md) by heap_nowA A4L HIx HPa MU WM MI.
assert (HPR1 : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPa | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HPa]. }
assert (AG1 : agree_on asegs LBR m m1) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR1 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
unstash OPB. unstash KIDS. unstash HAL. unstash JOB.
bstep.
evt_done5.
eapply (array_list_add_A_cps HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 md LBR LM FRS B lo a arr size v ps T);
[ exact HP1
| eapply (alist_agree asegs A4F); [exact HAL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl];
intros b k Hb; cbn in Hb; cbn; destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia
| rewrite L1; lia | lia
| exact ST | clia | lia | exact SPA | exact HT | eassumption | exact RA | reflexivity | reflexivity
| intros Hge; unfold al_add_costB, arr_add_costA in *; rewrite ?L1 in Hge |- *; destruct (Z.ltb_spec (Z.of_nat (length kids) + 1) size); lia
| exact (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms' md' A' (m' & r & errv' & arr' & size' & B' & RS & VM & ST' & HPR' & ERR' & BD' & HP' & OUT).
assert (HPR'' : heap_pres A4H (LBR ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m') by (eapply heap_pres_trans; [exact HPR1 | exact HPR']).
assert (AG : agree_on asegs LBR m m') by (eapply (agree_of_heap_pres asegs A4H); [exact HPR'' | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
eapply (K ms' md' m' r A' B').
- unfold jo_post_frameA. split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [| exists errv'; exact ERR'].
eapply heap_pres_weaken; [exact HPR'' | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply HiL; exact Hb | right; exact Hb]].
- exact BD'.
- destruct OUT as [(-> & -> & -> & Hgr & BBf & AL') | (-> & AL' & CASES)].
+ right. split; [reflexivity|]. split; [unfold al_add_costB, arr_add_costA in *; rewrite <- ?L1 in Hgr; destruct (Z.ltb_spec (Z.of_nat (length kids) + 1) size); lia|].
split; [| split].
* eapply (sarr_close asegs A4F) with (AL := [(a, 32); (arr, 8 * size)]) (KBS := KBS) (PBS := PBS) (pb := pb); try eassumption; try reflexivity.
-- eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
-- unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR'); [exact HDR | eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
-- eapply akids_agree; [exact KIDS | exact AG | exact HiK].
* eapply jopt_agree; [exact JOB | exact AG | exact HiV].
* eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl].
+ left. split; [reflexivity|]. exists (((p, 48) :: [(a, 32); (arr', 8 * size')] ++ concat (KBS ++ [VBS])) ++ PBS). split; [| split; [rewrite concat_app; cbn [concat]; rewrite !length_app; cbn [length]; rewrite ?app_nil_r, ?length_app; cbn [length Nat.add]; do 3 f_equal; rewrite <- !Nat.add_assoc; f_equal; apply Nat.add_comm | split; [| split; [| split]]]].
* eapply (sarr_close asegs A4F) with (ps := ps ++ [v]); try reflexivity.
-- eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
-- unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR'); [exact HDR | eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]].
-- exact AL'.
-- rewrite !length_app. cbn [length]. lia.
-- rewrite !length_app. cbn [length]. lia.
-- apply akids_app; [eapply akids_agree; [exact KIDS | exact AG | exact HiK] | apply akids_one; eapply jopt_agree; [exact JOB | exact AG | exact HiV]].
* unfold arr_grownA, arr_capA. cbn [app nth snd]. rewrite ?L1 in CASES.
destruct CASES as [(-> & -> & Hlt & _) | (-> & Hge & _)]; [left | right]; Z.div_mod_to_equations; lia.
* unfold al_add_costB, arr_add_costA in *. rewrite ?L1 in CASES. rewrite ?L1.
destruct (Z.ltb_spec (Z.of_nat (length kids) + 1) size); destruct CASES as [(_ & _ & Hlt & BBx) | (_ & Hge & BBx)]; lia.
* rewrite concat_app. cbn [concat]. rewrite app_nil_r.
eapply (heapA_perm A4L HIx); [exact HP' | unfold LBR; perm | apply Permutation_refl | apply Permutation_refl].
* intros w wv Hw Hwv. exact (arr_add_jtx asegs A4F m kids ps KBS PBS (p, 48) (a, 32) (arr, 8 * size) (arr', 8 * size') vs VBS w wv KIDS Hw Hwv).
Qed.
End AJoArrAdd2J.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeL5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeL5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition lh_entry_free_A_entry : Z := 0x9d528.
Definition lh_table_free_A_entry : Z := 0xa4ba8.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhFree.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition lh_entry_free_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
HEAPAx A' LB LM FRS (charge B 512 0) m' md'.

Lemma lh_entry_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (p k kn pad nx pv lo : Z) (errv : word),
HEAPAx A ((k, kn) :: LB) LM FRS B m md ->
rw_cells asegs m p [C8 (Z_to_bv 64 k); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pad); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 pv)] ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p mod 8 = 0 -> 0 < p ->
p + 40 <= alloc_ceiling -> (p + 40 <= 0x10000 \/ 0x647000 <= p) -> p / 8 + A_SB + 3 <= alloc_ceiling ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
512 <= bB B -> 0 <= bD B ->
(forall ms' md' A', lh_entry_free_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo errv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_entry_free_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ENT SHp Pal Pnz Php Pimg Psh ST LO LOS SPA HT ERR TP RA A0 BB BD K.
unfold_consts. word_range sp SPR.
pose proof (rw_cells_bound asegs m p _ ENT) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP k kn Hkal Hklo Hkhi Himg_k.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst a0 tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold lh_entry_free_A_entry, A_ERRNO in *. a4l.
carve_frame 16%nat ST.
do 3 bstep.
do 3 bstep.
bstep. asan_chkA.
bstep. bstep. bstep. sh_norm. rewrite (div8_add p 8) by lia. change (8 / 8) with 1.
bstep. rewrite ?sxb_zero, ?zxb_zero.
bstep.
bstep. if_false.
bstep. norm_sx32.
bstep. if_true.
asan_chkA.
bstep. bstep.

alloc_callA (hiA_free A4L HIx) blk k uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists kn. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec k 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_head in HPR2, HP2.
replace (if k =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (k =? 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST ENT SHp GOT CELL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_false.
do 4 bstep.
evt_done5. apply K. unfold lh_entry_free_A_post.
exists m2, r2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | exact HP2]]]]].
- unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists; reflexivity.
- release_frame FR ST2 (bv_unsigned sp). exact ST2.
Qed.

Variables (sp gp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (lo t tbl size : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (s0c s1c s2c s3c s4c rac : word).

Variable u : uwd.
Hypothesis UW : uw_at (hiA_top A4L HIx) m0 (bv_unsigned sp) (bv_unsigned s0c) u.
Hypothesis UWK : uw_ok A4L (hl_free A4H) rac u.

Ltac ub_align_true :=
repeat match goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) _] => rewrite (unsigned_lit x) by lia end;
match goal with |- context [Z.land ?e 7] => rewrite (ub_land7 e) by ub_mod_solve end; if_true.

Definition free_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -48) [C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Notation hdr_cellsA hsz hcnt hhd htl :=
[C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free A4F)); C8 (Z_to_bv 64 (fn_lh_char_hash A4F)); C8 (Z_to_bv 64 (fn_lh_char_equal A4F))].

Definition free_exitA (errv : word) (K0 : machine_state -> config -> ASA A4L HIx -> Prop) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(hsz hcnt hhd htl : Z),
HEAPAx A ((t, 56) :: (tbl, 40 * size) :: LB) LM FRS B m md ->
rw_cells asegs m t (hdr_cellsA hsz hcnt hhd htl) ->
stk asegs m lo (bv_unsigned sp + -48) ->
free_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - Z.of_nat (length es) * 512 <= bB B -> bD B0 <= bD B ->
K0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 t) x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_SB) x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa4c3c) fc None m (seg_rom asegs)) md A.

Lemma lh_free_loopA :
forall (k j : nat) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (errv : word) (hsz hcnt hhd htl : Z),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPAx A (map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * size) :: LB) LM FRS B m md ->
lh_slots asegs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = size ->
(forall e, In e es -> le_v e = 0) ->
rw_cells asegs m t (hdr_cellsA hsz hcnt hhd htl) ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
free_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
(Z.of_nat (length es) + 2) * 512 <= bB B0 -> uw_cost u <= bD B0 ->
bB B0 - Z.of_nat j * 512 <= bB B -> bD B0 <= bD B ->
free_exitA errv (fun ms md A => AJ5 A4L HIx A T md ms) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (t + 32)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ent_addr tbl (le_ix e))) (Z_to_bv 64 A_SB) (Z_to_bv 64 (t / 8 + 4 + A_SB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa4c18) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until htl; intros Hk Hj HP SL LINK Hlen VZ HDR ST LO LOS SPA HT FR ERR VM0 HPR BB0 BD0 BB BD KX.
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
assert (NX : nx_of tbl es j = 0).
{ unfold nx_of. destruct (nth_error es (S j)) eqn:E2; [|reflexivity].
pose proof (proj1 (nth_error_Some es (S j)) ltac:(rewrite E2; discriminate)). lia. }
rewrite NX in C.
unfold free_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
replace (skipn j es) with [e] in HP.
2:{ symmetry. rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
destruct (skipn j es) as [|e' tl] eqn:ES; [discriminate|]. cbn in Hj. injection Hj as ->.
apply (f_equal (@length lent)) in ES. rewrite length_skipn in ES. cbn in ES. destruct tl; [reflexivity | cbn in ES; lia]. }
cbn [map app kblk] in HP.
blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP tbl (40 * size) Hbal Hblo Hbhi Himg_b.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
shadow_nowA A4L HIx HP t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPt4.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP ltac:(right; right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 0 tbl (40 * size) HP ltac:(right; right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEPe0.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP ltac:(right; right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEPe3.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep.

cbn [fn_lh_entry_free A4F]. replace (ret_pc (Z_to_bv 64 0x9d528)) with (Z_to_bv 64 0x9d528) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
eapply (lh_entry_free_A_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A ((t, 56) :: (tbl, 40 * size) :: LB) LM FRS B
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) 0 (pv_of tbl es j) lo errv);
[ heap_nowA A4L HIx HP MU WM MI | exact C | exact SHe | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
{ unfold ent_addr. Z.div_mod_to_equations. lia. }
{ unfold ent_addr in *. lia. }
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Himg_b; [left; nia | right; lia]. }
{ clia. }
{ rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
{ lia. }
{ lia. }
{ destruct u; cbn [uw_cost] in *; lia. }
intros ms2 md2 A2 (m2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). a4l.
rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. a4l.
assert (HPR' : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; in_tailA Hb]. }
clear MU WM MI ST SHt SHe SEPt4 SEPe0 SEPe3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
shadow_nowA A4L HIx HP2 t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt4.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP2 ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP2 ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPe3.
a4l.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
pose proof (rw_cells_bound asegs _ _ _ C) as EB. cbn [cells_size csize Nat.add] in EB.
assert (EA8 : ent_addr tbl (le_ix e) mod 8 = 0) by (unfold ent_addr; Z.div_mod_to_equations; lia).
bstep. bstep.
bstep. ub_align_true.
bstep. bstep. sh_norm. rewrite (div8_add (ent_addr tbl (le_ix e)) 24) by lia. change (24 / 8) with 3.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. if_true.
evt_done5. eapply KX; [exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | eapply model_vm_only_trans; eassumption | exact HPR'
| cbn [bB charge]; lia | cbn [bD charge]; lia].
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
destruct (nth_error es (S j)) as [e'|] eqn:E2.
2:{ exfalso. apply nth_error_None in E2. lia. }
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
unfold free_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (SK : skipn j es = e :: skipn (S j) es).
{ rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
remember (skipn j es) as sk eqn:ES. destruct sk as [|e0 tl]; [discriminate|]. cbn in Hj. injection Hj as ->.
f_equal. change tl with (skipn 1 (e :: tl)). rewrite ES, skipn_skipn. reflexivity. }
rewrite SK in HP. cbn [map app] in HP. unfold kblk at 1 in HP.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
assert (Hint : In (t, 56) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (Hinb : In (tbl, 40 * size) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
assert (Hint' : In (t, 56) (((le_k e, le_kn e) :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) ++ LM)) by (apply in_or_app; left; right; exact Hint).
assert (Hinb' : In (tbl, 40 * size) (((le_k e, le_kn e) :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) ++ LM)) by (apply in_or_app; left; right; exact Hinb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hint') as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hint') as Himg_t.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hinb') as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hinb') as Himg_b.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(right; exact Hint)) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP ltac:(right; exact Hint) ltac:(cbn; lia) Hint') as SEPt4.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP ltac:(right; exact Hinb) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 0 tbl (40 * size) HP ltac:(right; exact Hinb) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hinb') as SEPe0.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP ltac:(right; exact Hinb) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hinb') as SEPe3.
clear Hint Hinb Hint' Hinb'.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. bstep.

cbn [fn_lh_entry_free A4F]. replace (ret_pc (Z_to_bv 64 0x9d528)) with (Z_to_bv 64 0x9d528) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
eapply (lh_entry_free_A_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) LM FRS B
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) (ent_addr tbl (le_ix e')) (pv_of tbl es j) lo errv);
[ heap_nowA A4L HIx HP MU WM MI | exact C | exact SHe | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
{ unfold ent_addr. Z.div_mod_to_equations. lia. }
{ unfold ent_addr in *. lia. }
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Himg_b; [left; nia | right; lia]. }
{ clia. }
{ rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
{ lia. }
{ lia. }
{ destruct u; cbn [uw_cost] in *; lia. }
intros ms2 md2 A2 (m2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). a4l.
rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. a4l.
assert (HPR' : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia |].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; right; exact Hb | right; exact Hb]. }
clear MU WM MI ST SHt SHe SEPt4 SEPe0 SEPe3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
assert (Hinb : In (tbl, 40 * size) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
assert (Hinb' : In (tbl, 40 * size) ((map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB) ++ LM)) by (apply in_or_app; left; exact Hinb).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP2 Hinb ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (le_ix e) 3 tbl (40 * size) HP2 Hinb ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) Hinb') as SEPe3.
clear Hinb Hinb'.
a4l.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
pose proof (rw_cells_bound asegs _ _ _ C) as EB. cbn [cells_size csize Nat.add] in EB.
assert (EA8 : ent_addr tbl (le_ix e) mod 8 = 0) by (unfold ent_addr; Z.div_mod_to_equations; lia).
bstep. bstep.
bstep. ub_align_true.
bstep. bstep. sh_norm. rewrite (div8_add (ent_addr tbl (le_ix e)) 24) by lia. change (24 / 8) with 3.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep. unfold ent_addr. if_falsex.
evt_done5.
replace (Z_to_bv 64 (t / 8 + 2147450884)) with (Z_to_bv 64 (t / 8 + 4 + 2147450880)) by (f_equal; lia).
eapply (IH (S j) e'); first [exact E2 | exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | exact HPR' | exact KX | exact BB0 | exact BD0 | idtac].
+ lia.
+ eapply (lh_slots_pres A4H); [exact HPR2 | apply in_or_app; left; apply in_or_app; right; right; left; reflexivity | exact Hlen | exact SL].
+ split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]].
+ exact Hlen.
+ exact VZ.
+ clia.
+ lia.
+ exact SPA.
+ exact HT.
+ eapply model_vm_only_trans; eassumption.
+ cbn [bB charge]. lia.
+ cbn [bD charge]. lia.
Qed.

Definition lh_table_free_A_post (errv : word) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H rac sp gp (Z_to_bv 64 A_TP) s0c s1c s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md0) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B0 - (Z.of_nat (length es) + 2) * 512 <= bB B' /\ bD B0 - uw_cost u <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma lh_free_exit_okA : forall errv,
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
bv_unsigned rac mod 2 = 0 -> 0 <= size ->
(Z.of_nat (length es) + 2) * 512 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', lh_table_free_A_post errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
free_exitA errv (fun ms md A => AJ5 A4L HIx A T md ms).
Proof.
intros errv LO LOS SPA HT RA Hsz BB0 BD0 K. unfold free_exitA. intros until htl. intros HP HDR ST FR ERR VM0 HPR BB BD.
unfold free_frameA in FR. unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01A HIx _ _ _ _ _ _ _ _ _ _ _ HP) as Hne.
shadow_nowA A4L HIx HP t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 3 t 56 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt3.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
bstep. asan_chkA.
bstep. bstep.

alloc_callA (hiA_free A4L HIx) blk tbl uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists (40 * size). right; left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec tbl 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
replace (if tbl =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (tbl =? 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST HDR SHt SEPt3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
do 8 bstep.
release_frame FR ST2 (bv_unsigned sp).
bstep.

alloc_callA (hiA_free A4L HIx) blk t uw u A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 56. left. reflexivity. }
all: try (solve [eapply uw_at_pre0; [eapply uw_at_heap_pres; [exact UW | exact HPR | lia] | lia]]).
all: try (solve [exact UWK]).
all: try (destruct (Z.eqb_spec t 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite lb_remove_head in HP3, HPR3.
replace (if t =? 0 then 0 else uw_cost u) with (uw_cost u) in HP3 by (destruct (Z.eqb_spec t 0); [lia | reflexivity]).
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply K. unfold lh_table_free_A_post.
exists m3, r3, (charge (charge B 512 0) 512 (uw_cost u)).
split; [apply ret_statew_same|]. split; [eapply model_vm_only_trans; [| exact VM3]; eapply model_vm_only_trans; eassumption|].
split; [exact ST3|]. split; [exact HPR|]. split; [exact ERR3|].
split; [cbn [bB charge]; lia|]. split; [cbn [bD charge]; destruct u; cbn [uw_cost] in *; lia|]. exact HP3.
Qed.

Lemma lh_table_free_A_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B0 m0 md0 ->
lh_open asegs A4F m0 t tbl size es svs ->
(forall e, In e es -> le_v e = 0) ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
bv_unsigned rac mod 2 = 0 ->
a0 = Z_to_bv 64 t ->
(Z.of_nat (length es) + 2) * 512 <= bB B0 -> uw_cost u <= bD B0 ->
(forall ms' md' A', lh_table_free_A_post errv ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR rac sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0c s1c a0 a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_table_free_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP OPEN VZ ST LO LOS SPA HT ERR RA A0 BB0 BD0 K.
destruct OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. unfold lh_blocks in HP. cbn [app] in HP.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
shadow_nowA A4L HIx HP t 56 SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 1 t 56 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 4 t 56 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPt4.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m0) as MU.
subst a0. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold lh_table_free_A_entry, A_ERRNO in *. a4l.
carve_frame 48%nat ST.
do 7 bstep.
do 3 bstep.
bstep. asan_chkA.
bstep. cbn [fn_lh_entry_free A4F]. bstep. if_false.
bstep. asan_chkA.
bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPAx A ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) LM FRS B0 m1 md0) by heap_nowA A4L HIx HP MU WM MI.
assert (HPR1 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb | clia | solve_clientWA A4L HIx HP].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb]. }
pose proof (lh_free_exit_okA errv ltac:(clia) ltac:(lia) SPA HT RA ltac:(lia) BB0 BD0 K) as EXIT.
assert (SL1 : lh_slots asegs m1 tbl svs).
{ eapply (lh_slots_frame asegs m0 m1 tbl svs _ SL MU WM). intros i Hi. apply Forall_cons; [|apply Forall_nil].
cbn. unfold ent_addr. left. lia. }
rewrite hd_of_nth in *.
destruct (nth_error es 0) as [e0|] eqn:E0.
2:{
bstep. if_true.
evt_done5.
assert (ES : es = []) by (destruct es; [reflexivity | discriminate]). rewrite ES in HP1. cbn [map app] in HP1.
eapply EXIT; [exact HP1 | exact HDR | exact ST | exact FR | exact ERR | apply model_vm_only_refl | exact HPR1 | cbn; lia | cbn; lia]. }
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 0%nat e0 E0) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some es 0) ltac:(rewrite E0; discriminate)) as Hes0.
bstep. unfold ent_addr. if_falsex.
evt_done5.
replace (Z_to_bv 64 (t / 8 + 2147450884)) with (Z_to_bv 64 (t / 8 + 4 + 2147450880)) by (f_equal; lia).
eapply (lh_free_loopA (length es - 1) 0 e0);
first [ exact HDR | exact ST | exact FR | exact ERR | exact HPR1 | exact EXIT | exact SL1 | exact Hlen | exact VZ | exact SPA | exact HT | exact BB0 | exact BD0
| apply model_vm_only_refl | exact E0 | idtac ].
all: lazymatch goal with
| |- HEAPA _ _ _ _ _ _ _ _ _ =>
cbn [skipn]; eapply (heapA_perm A4L HIx); [exact HP1| | apply Permutation_refl | apply Permutation_refl];
change ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) with ([(t, 56); (tbl, 40 * size)] ++ (map kblk es ++ LB));
change (map kblk es ++ (t, 56) :: (tbl, 40 * size) :: LB) with (map kblk es ++ [(t, 56); (tbl, 40 * size)] ++ LB);
apply Permutation_app_swap_app
| |- lh_link _ _ _ => split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]]
| |- _ => first [clia | lia]
end.
Qed.
End ALhFree.
End RC__1.
