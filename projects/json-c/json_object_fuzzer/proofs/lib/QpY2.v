(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u Qc6I QJFf QCiC Qpj5 QvDJ Q67d Q6sh QKTr QJBH QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QZbm QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QZbm.
Import QlES.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section Laws.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma RFake_releaseK : forall c0 FS0 m f (flag : word),
(forall f', In f' FS0 -> fframe_rangeA RE (ff_cls f') (ff_addr f')) ->
RFake FS0 RE X m -> In (c0, f) FS0 ->
bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
RFake (ffs_remove f FS0) RE X (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None
/\ fp_RFake FS0 RE X (bv_unsigned flag).
Proof.
intros c0 FS0 m f flag _ RF Hin Hrd. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL c0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.

assert (Eflag : flag = wz (fs_flag FS c0 pos)).
{ destruct SLOT as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
apply le8_inj. eapply bytes_at_det; [exact Hrd| exact BA| rewrite !length_le8; reflexivity]. }
subst flag.
pose proof (fs_flag_range FS c0 pos Hc0 Hp) as FR. pose proof (fs_foff_range c0 Hc0) as FO.
pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
assert (UF : bv_unsigned (wz (fs_flag FS c0 pos)) = fs_flag FS c0 pos) by (apply unsigned_lit; lia).
assert (EA : wz (fs_flag FS c0 pos) = wa (fs_flag FS c0 0 + pos)) by (unfold wa, fs_flag; f_equal; lia).
pose proof (fs_N_pos c0 Hc0) as N0.
split; [| split].
-
pose proof (wmono_write asegs m m (wz (fs_flag FS c0 pos)) [b8 0] (wmono_refl asegs m)) as WM.
rewrite EA in WM |- *.
assert (FRc : forall A cs, rw_cells asegs m A cs ->
A + Z.of_nat (cells_size cs) <= fs_flag FS c0 0 + pos \/ fs_flag FS c0 0 + pos + 1 <= A ->
rw_cells asegs (write_to_mem m (wa (fs_flag FS c0 0 + pos)) [b8 0]) A cs).
{ intros A cs H D. apply rw_cells_frame; [exact H| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia| cbn; lia]. }
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [apply fs_shape_remove; exact SHP|].
split. { apply ro_cells_frame; [exact SSL| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia]. }
split. { apply FRc; [exact GC| cbn; unfold fs_flag in *; lia]. }
split. { intros c Hc. destruct (HI c Hc) as [h H]. exists h. apply FRc; [exact H| cbn; unfold fs_hint, fs_flag, kFsClasses in *; lia]. }
split. { intros c Hc. destruct (Z.eq_dec c c0) as [->|Nc].
- rewrite (flags_of_clear_same RE FS0 c0 pos f SHP Hc0 Hp Ef). apply u8arr_write; [apply FL; exact Hc0| rewrite flags_of_length; lia].
- rewrite (flags_of_clear_other RE FS0 c0 f c SHP Hin ltac:(lia)). apply u8arr_frame; [apply FL; exact Hc| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia|].
rewrite flags_of_length. cbn [length]. pose proof (fs_N_pos c Hc).
destruct (Z.lt_ge_cases c c0).
+ pose proof (fs_foff_mono c c0 ltac:(lia) ltac:(lia) ltac:(exact (proj2 Hc0))). unfold fs_flag in *. lia.
+ pose proof (fs_foff_mono c0 c ltac:(lia) ltac:(lia) ltac:(exact (proj2 Hc))). unfold fs_flag in *. lia. }
split. { intros c p Hcp Hpp. apply ffs_remove_In in Hcp as [Hcp Hne]. cbn [ff_addr snd] in Hne.
pose proof (SL c p Hcp Hpp) as H. destruct (SHf _ Hcp) as (Hcc & _). cbn [ff_cls fst] in Hcc.
pose proof (fs_frame_in_area FS c p Hcc Hpp) as [A1 A2]. unfold fs_area_lo in A1.
assert (64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
apply FRc; [exact H| cbn; unfold fs_flag in *; lia]. }
split; (eapply hjunk_wmono; [| exact WM]); assumption.
-
destruct (FL c0 Hc0) as [_ WR]. rewrite flags_of_length in WR.
replace (wz (fs_flag FS c0 pos)) with (wa (fs_flag FS c0 0 + pos)) by (unfold wa, fs_flag; f_equal; lia).
apply WR. lia.
- rewrite UF. apply (fp_meta RE X FS0 _ SHP). lia.
Qed.

Lemma RFake_flagK : forall c0 FS0 m f, RFake FS0 RE X m -> In (c0, f) FS0 ->
exists flag : word, ro_cells asegs m (f + ff_size c0 - 8) [C8 flag] /\ FS + 0x1000 <= bv_unsigned flag < FS + 0x9000.
Proof.
intros c0 FS0 m f RF Hin. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL c0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.
pose proof (fs_flag_range FS c0 pos Hc0 Hp) as FR. pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
exists (wz (fs_flag FS c0 pos)). split; [exact (proj1 SLOT)|]. rewrite unsigned_lit by lia. exact FR.
Qed.

Lemma RFake_alignK : forall c0 FS0 m f, RFake FS0 RE X m -> In (c0, f) FS0 -> c0 <= 6 -> f mod ff_size c0 = 0.
Proof.
intros c0 FS0 m f RF Hin H6. pose proof RF as (AL & _ & _ & SHP & _).
destruct SHP as [SHf _]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
subst f. unfold fs_frame, ff_size.
assert (E : c0 = 0 \/ c0 = 1 \/ c0 = 2 \/ c0 = 3 \/ c0 = 4 \/ c0 = 5 \/ c0 = 6) by lia.
destruct E as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn; Z.div_mod_to_equations; lia.
Qed.

Lemma RFake_releaseK_range : forall c0 FS0 m f (flag : word),
RFake FS0 RE X m -> In (c0, f) FS0 ->
bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
FS + 0x1000 <= bv_unsigned flag < FS + 0x9000 /\ bv_unsigned flag + 1 <= band_lo.
Proof.
intros c0 FS0 m f flag RF Hin Hrd. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL c0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.
assert (Eflag : flag = wz (fs_flag FS c0 pos)).
{ destruct SLOT as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
apply le8_inj. eapply bytes_at_det; [exact Hrd| exact BA| rewrite !length_le8; reflexivity]. }
subst flag. pose proof (fs_flag_range FS c0 pos Hc0 Hp) as FR. pose proof (fs_foff_range c0 Hc0) as FO.
pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
rewrite unsigned_lit by (unfold fs_flag in *; lia). unfold fs_flag in *. idtac. lia.
Qed.

End Laws.

Section GconsFacts.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Local Notation FS := (ae_fs_base RE).

Lemma RFake_releaseK_pres : forall c0 m f (flag : word),
RFake FS0 RE X m -> In (c0, f) FS0 -> bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
aheap_presA asegs a_alayout LB0 FS0 band_lo m (write_to_mem m flag [Z_to_bv 8 0]).
Proof.
intros c0 m f flag RF Hin Hrd.
pose proof (RFake_releaseK_range RE X c0 FS0 m f flag RF Hin Hrd) as [FR CE].
pose proof RF as (AL & K1 & K2 & SHP & _). pose proof K1 as K1'. unfold A_FS_MAP_SIZE in K1'.
unfold aheap_presA.
assert (Ew : flag = wa (bv_unsigned flag)).
{ unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
rewrite Ew at 1. pose proof (bv_unsigned_in_range 64 flag) as FLR. change (bv_modulus 64) with (2^64) in FLR.
apply agree_on_write; [lia| cbn; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. intros x Hx.
assert (Ex : x = bv_unsigned flag) by lia. subst x. clear Hx.
intros [C|[C|[C|[C|[C|[C|C]]]]]].
- lia.
- cbn [ala_client_data a_alayout] in C. unfold a_client_data in C. lia.
- eapply (live_user_not_fs _ _ _ _ _ _ GC (bv_unsigned flag)); [exact C| unfold A_FS_MAP_SIZE; lia].
- pose proof (body_ge RE FS0 (bv_unsigned flag) SHP C). lia.
- destruct C as (g & Hg & Hs). destruct SHP as [SHf _]. destruct (SHf _ Hg) as (Hc & pos & Hp & Eg).
pose proof (fs_frame_in_area FS (ff_cls g) pos Hc Hp) as [B1 B2]. rewrite <- Eg in B1, B2.
unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2. idtac.
assert (SZ : 0 <= ff_size (ff_cls g)) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 (ff_cls g)); lia).
rewrite !SH_eq in Hs. Z.div_mod_to_equations. lia.
- rewrite SH_247, ?KHI_eq in C. pose proof SH_band. lia.
- rewrite !SH_eq in C. cbn [ala_img_lo a_alayout] in C. lia.
Qed.

End GconsFacts.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRF : ac_RFake C = RFake.

Lemma ARUN_fframe_releaseK0 : forall c0 s LB FS RE m f (flag : word),
ARUN C s LB FS RE m -> In (c0, f) FS ->
bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
ARUN C s LB (ffs_remove f FS) RE (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None.
Proof.
intros c0 s LB FS RE m f flag AR Hf HB. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof R8 as R8r. rewrite HRF in R8r.
destruct (RFake_releaseK RE X c0 FS0 m f flag (gc_ff_range _ _ _ _ _ _ GC) R8r Hf0 HB) as (R8' & WV & FPF).
split; [|exact WV].
apply (ARUN_close C s LB (ffs_remove f FS) RE _ X G LB0 (ffs_remove f FS0)); [exact PB| apply Permutation_filter; exact PF|].
assert (GC' : gcons (ps_a s) LB0 (ffs_remove f FS0) G RE X).
{ eapply gcons_ff_sub; [exact GC|]. intros f' Hin. unfold ffs_remove in Hin.
apply (proj2 (list_elem_of_In _ _)) in Hin. apply (proj1 (list_elem_of_filter _ _ _)) in Hin.
destruct Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin. exact Hin. }

pose proof (bv_unsigned_in_range 64 flag) as FR. unfold bv_modulus in FR. change (2 ^ Z.of_N 64) with (2^64) in FR.
assert (AG : forall P : Z -> Prop, (forall x, P x -> czone LB0 RE x -> False) ->
agree_on asegs P m (write_to_mem m flag [Z_to_bv 8 0])).
{ intros P HP. rewrite <- (Z_to_bv_bv_unsigned flag); change (Z_to_bv 64 (bv_unsigned flag)) with (wa (bv_unsigned flag)). apply agree_on_write; cbn [length]; change (Z.of_nat 1) with 1; [lia| lia|].
intros x Hx Px. assert (x = bv_unsigned flag) as -> by lia.
apply (fp_RFake_zone RE X) in FPF.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CE & _); cbn [fst snd] in AL, K, CE.
apply (HP _ Px). unfold czone. destruct FPF as [FPF|FPF]; [do 3 right; left; exact FPF| do 4 right; left; exact FPF]. }
assert (WM : wmono asegs m (write_to_mem m flag [Z_to_bv 8 0])) by (apply wmono_write; apply wmono_refl).
split; [exact GC'|].
split; [eapply (ac_RTconst_frame C); [exact R1| exact WM| apply AG; intros x; apply (fp_RTconst_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RStats_frame C); [exact R2| exact WM| apply AG; intros x; apply (fp_RStats_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| apply AG; intros x; apply (fp_RPrim_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| apply AG; intros x; apply (fp_RChunks_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AG; intros x; apply (fp_RSec_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; intros x; apply (fp_RQuar_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| apply AG; intros x; apply (fp_RDepot_cz _ _ _ _ _ _ GC)]|].
rewrite HRF. exact R8'.
Qed.

Lemma ARUN_fframe_releaseK : forall c0 s LB FS RE m f (flag : word),
ARUN C s LB FS RE m -> In (c0, f) FS -> bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
ARUN C s LB (ffs_remove f FS) RE (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None
/\ bv_unsigned flag + 1 <= band_lo
/\ aheap_presA asegs a_alayout LB FS band_lo m (write_to_mem m flag [Z_to_bv 8 0]).
Proof.
intros c0 s LB FS RE m f flag AR Hf HB.
destruct (ARUN_fframe_releaseK0 c0 s LB FS RE m f flag AR Hf HB) as [AR' WV]. split; [exact AR'|]. split; [exact WV|].
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
split; [exact (proj2 (RFake_releaseK_range RE X c0 FS0 m f flag R8 Hf0 HB))|].
pose proof (RFake_releaseK_pres (ps_a s) LB0 FS0 G RE X GC c0 m f flag R8 Hf0 HB) as AP.
unfold aheap_presA in *. eapply agree_on_mono; [exact AP|]. intros x. unfold aclient_addrA, in_ablock, in_fframe_body, in_fframe_shadow.
intros [H|[H|[H|[H|[H|[H|H]]]]]]; [left; exact H| right; left; exact H| | | | do 5 right; left; exact H| do 6 right; exact H].
- do 2 right; left. destruct H as (b & Hb & R). exists b. split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- do 3 right; left. destruct H as (ff & Hff & R). exists ff. split; [eapply Permutation_in; [exact PF| exact Hff]| exact R].
- do 4 right; left. destruct H as (ff & Hff & R). exists ff. split; [eapply Permutation_in; [exact PF| exact Hff]| exact R].
Qed.

Lemma ARUN_fframe_flagK : forall c0 s LB FS RE m f, ARUN C s LB FS RE m -> In (c0, f) FS ->
exists flag : word, ro_cells asegs m (f + ff_size c0 - 8) [C8 flag] /\ ae_fs_base RE + 0x1000 <= bv_unsigned flag < ae_fs_base RE + 0x9000.
Proof.
intros c0 s LB FS RE m f AR Hf. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
exact (RFake_flagK RE X c0 FS0 m f R8 Hf0).
Qed.

Lemma ARUN_fframe_align : forall c0 s LB FS RE m f, ARUN C s LB FS RE m -> In (c0, f) FS -> c0 <= 6 -> f mod ff_size c0 = 0.
Proof.
intros c0 s LB FS RE m f AR Hf H6. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
exact (RFake_alignK RE X c0 FS0 m f R8 Hf0 H6).
Qed.

Lemma ARUN_fs_block_disjoint : forall s LB FS RE m b, ARUN C s LB FS RE m -> In b LB ->
ablk_addr b + ablk_size b <= ae_fs_base RE \/ ae_fs_base RE + 0xb09000 <= ablk_addr b.
Proof.
intros s LB FS RE m [[p A] n] AR Hb. cbn [ablk_addr ablk_size fst snd]. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _). assert (Hb0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact Hb]).
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (_ & K & CE & DP & _). cbn [fst snd] in K, CE. unfold iv_disjoint in DP. cbn [fst snd] in DP.
destruct (live_block_geom _ _ _ _ _ _ GC p A n Hb0) as (Hn & AL & [(c & i & Ht & Hc & Hp & HA & CT)|(e & He & Hp & Hr & HA & CT)]); unfold blk_container in CT.
- pose proof (slot_prim _ _ _ _ _ _ GC c i _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in *. change (2 ^ 37) with 137438953472 in *. unfold A_FS_MAP_SIZE in *. lia.
- destruct (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & _ & _ & _ & _ & _ & F).
pose proof (proj1 (List.Forall_forall _ _) F _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D. unfold kPage, A_FS_MAP_SIZE in *. lia.
Qed.
End S.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig QQwg QUxU QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Definition fp_cls (RE : aentry) (X : rlay) (c : Z) (z : Z) : Prop :=
(ri_addr RE c <= z < ri_addr RE c + 128)
\/ (pc_addr X c <= z < pc_addr X c + 80)
\/ (fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize)
\/ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) z
\/ (reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset)
\/ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z.

Section Geom.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Hypothesis RL : rlay_ok RE X.

Lemma reg_geom : forall c, 0 <= c < 32 ->
reg_beg (ae_L RE) c = prim_lo RE + c * 4294967296 /\ fa_beg (ae_L RE) c = prim_lo RE + c * 4294967296 + 3758096384
/\ prim_lo RE mod 65536 = 0 /\ 17594333495296 <= prim_lo RE /\ prim_hi RE <= band_lo /\ prim_hi RE = prim_lo RE + 137438957568
/\ region_info RE = prim_lo RE + 137438953472.
Proof.
intros c Hc. pose proof (rlay_prim_facts RE X RL) as (P0 & P1 & P2 & _).
idtac. rewrite ?KHI_eq in P1.
unfold fa_beg, reg_beg, prim_lo, prim_hi, region_info in *. pose proof kconsts as (KR & KO & _). rewrite KR, KO.
change (2^32) with 4294967296. change (2^37) with 137438953472 in *.
repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma fp_cls_lt_ceil : forall c z, 0 <= c < 32 -> fp_cls RE X c z -> z < band_lo.
Proof.
intros c z Hc F. pose proof (reg_geom c Hc) as (RB & FB & AL & PK & PC & PH & RI).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & TB & _). cbn [fst snd] in TB.
pose proof kconsts as (KR & KO & KS & _).
rewrite ?KHI_eq in *. unfold fp_cls, ri_addr, pc_addr, in_sh in F. cbn [fst snd] in F. rewrite ?RB, ?FB, ?RI, ?KO, ?KS in F.
unfold SH in F.
destruct F as [F|[F|[F|[F|[F|F]]]]]; try lia.
all: unfold A_SHADOW_OFS in F; Z.div_mod_to_equations; lia.
Qed.

Lemma fp_cls_not_stats : forall c z, 0 <= c < 32 -> fp_cls RE X c z -> ~ (rl_T X + 2768 <= z < rl_T X + 3168).
Proof.
intros c z Hc F. pose proof (reg_geom c Hc) as (RB & FB & AL & PK & PC & PH & RI).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof kconsts as (KR & KO & KS & _).
rewrite ?KHI_eq in *. unfold fp_cls, ri_addr, pc_addr, in_sh in F. cbn [fst snd] in F. rewrite ?RB, ?FB, ?RI, ?KO, ?KS in F.
unfold SH, A_SHADOW_OFS in F. unfold prim_lo in *.
destruct F as [F|[F|[F|[F|[F|F]]]]]; Z.div_mod_to_equations; (first [ clear - H q TD TK PK AL r F Hc z c X RE BAND H9 q1 H5 H4 r0 H0 PH PC r1 q0; lia | lia ]).
Qed.

Lemma fp_cls_sep : forall c c' z, 0 <= c < 32 -> 0 <= c' < 32 -> c <> c' -> fp_cls RE X c z -> fp_cls RE X c' z -> False.
Proof.
intros c c' z Hc Hc' NE F F'.
pose proof (reg_geom c Hc) as (RB & FB & AL & PK & PC & PH & RI). pose proof (reg_geom c' Hc') as (RB' & FB' & _).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof kconsts as (KR & KO & KS & _).
rewrite ?KHI_eq in *. unfold fp_cls, ri_addr, pc_addr, in_sh in F, F'. cbn [fst snd] in F, F'.
rewrite ?RB, ?FB, ?RI, ?KO, ?KS in F. rewrite ?RB', ?FB', ?RI, ?KO, ?KS in F'.
unfold SH, A_SHADOW_OFS in F, F'. unfold prim_lo in *.
assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia;
destruct F as [F|[F|[F|[F|[F|F]]]]]; destruct F' as [F'|[F'|[F'|[F'|[F'|F']]]]]; Z.div_mod_to_equations; (first [ clear - H q D TK PK AL r F' F NE z c' c X RE BAND TD Hc' Hc H9 q1 H5 H4 r0 H0 r1 q0 PH PC H14 q2 H10 r2 H19 q3 H15 r3; nia | nia ]).
Qed.
End Geom.

Lemma crep_slot_geom : forall a G RE X m c K i t,
class_rep a G RE X m c K -> 1 <= c <= 31 -> tag_at G c i = Some t ->
0 <= i /\ (i + 1) * class_size c <= c_alloc_user (cls a c)
/\ 32 <= class_size c /\ class_size c mod 32 = 0
/\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c
/\ c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset
/\ exists k, 0 <= k /\ i * class_size c = 8 * k /\ class_size c = 8 * (class_size c / 8).
Proof.
intros a G RE X m c K i t (_ & PU & _) Hc Ht. pose proof (tag_at_lt G c i t Ht) as [I1 I2].
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5).
pose proof (class_size_facts c Hc) as [S1 S2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; lia).
split; [lia|]. split; [(first [ clear - E8 S2 S1 I2 I1 G5 G3 G2 G1 i c G a; nia | nia ])|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
exists (i * (class_size c / 8)). split; [(first [ clear - E8 S2 S1 I2 I1 G5 G3 G2 G1 i c G a; nia | nia ])|]. split; [(first [ clear - E8 S1 i c G a; nia | nia ])| exact E8].
Qed.

Section ClassFrame.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).

Lemma class_rep_agree : forall m m' c K,
class_rep a G RE X m c K -> 0 <= c < 32 -> agree_on asegs (fp_cls RE X c) m m' -> class_rep a G RE X m' c K.
Proof.
intros m m' c K HC Hc AG. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _). rewrite KM in G5.
split; [split; [|split]|split].
- exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. left. cbn [ri_cells cells_size csize Nat.add] in Hz. lia.
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. right; left. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [|split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. right; left. rewrite LCH in Hz. cbn in Hz. lia.
- exact PU.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HCL : 1 <= c <= 31) by lia. pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize -> fp_cls RE X c z) by (intros z Hz; do 2 right; left; exact Hz).
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 -> fp_cls RE X c z).
{ intros z Hz. do 3 right; left. split; cbn [fst snd]; lia. }
assert (INU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset -> fp_cls RE X c z) by (intros z Hz; do 4 right; left; exact Hz).
assert (INUS : forall z, SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8 -> fp_cls RE X c z).
{ intros z Hz. do 5 right. split; cbn [fst snd]; lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KO8 SZ1 G3 G2 G1 LCH CH K c G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H31 H30 H24 q4 H19 q3 H5 H4 r0 H0 H r KO8 q0 SZ2 r3 SZ1 G5 r4 G4 G3 G2 G1 P14 r5 q LCH CH K c G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H36 H35 H29 q5 H0 H r q G5 r5 P14 r6 LCH CH K c G a; lia | lia ])).
destruct MU8 as (qm & QM).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
+ eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite map_length in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+ intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (crep_slot_geom a G RE X m c K i t HC HCL Ht) as (I1 & IL & _ & _ & SB & B1 & B2 & _). rewrite SB in Hz.
apply INU. clear - Hz I1 IL B1 B2 SZ1. nia.
+ eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply INU. lia.
+ intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (crep_slot_geom a G RE X m c K i t HC HCL Ht) as (I1 & IL & _ & _ & SB & B1 & B2 & k & K0 & K1 & K2).
rewrite SB, K1, SH_plus8 in Hz. apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia.
clear - Hz I1 IL B1 B2 SZ1 K0 K1 K2 KO8. nia.
+ eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
+ eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G2 G3 G4 KO8 QA QA0; lia.
+ eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma class_rep_ext : forall a' G' m c K,
class_rep a G RE X m c K -> cls a' c = cls a c -> as_cache_inited a' = as_cache_inited a -> G' c = G c ->
class_rep a' G' RE X m c K.
Proof.
intros a' G' m c K HC EC EI EG.
assert (TG : forall i, tag_at G' c i = tag_at G c i) by (intros i; unfold tag_at; rewrite EG; reflexivity).
unfold class_rep, cr_cells, cr_pure, cr_region in *. rewrite EC, EI, EG. setoid_rewrite TG. exact HC.
Qed.
End ClassFrame.

Lemma RPrim_open : forall a G RE X m, RPrim a G RE X m ->
exists K : Z -> pcls, hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ forall c, 0 <= c < kNumClasses -> class_rep a G RE X m c (K c).
Proof. intros a G RE X m H. exact H. Qed.

Definition wc_ok {BAND : Band} (RE : aentry) (X : rlay) (c : Z) (iv : Z * Z) : Prop :=
let '(lo, hi) := iv in
band_lo <= lo
\/ (rl_T X + 2768 <= lo /\ hi <= rl_T X + 3168)
\/ (forall z, lo <= z < hi -> fp_cls RE X c z).

Lemma agree_other_classes {BAND : Band} : forall RE X c W m m',
rlay_ok RE X -> 0 <= c < 32 -> munch W m m' -> wmono asegs m m' -> Forall (wc_ok RE X c) W ->
forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m'.
Proof.
intros RE X c W m m' RL Hc MU WM FW c0 Hc0 NE. pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hc0.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as WC. cbn [wc_ok] in WC.
destruct WC as [WC|[WC|WC]].
- pose proof (fp_cls_lt_ceil RE X RL c0 x Hc0 Fx). lia.
- pose proof (fp_cls_not_stats RE X RL c0 x Hc0 Fx). lia.
- exact (fp_cls_sep RE X RL c0 c x Hc0 Hc (fun E => NE E) Fx (WC x (conj H1 H2))).
Qed.

Definition cr_user (a : AState) (G : ghost) (RE : aentry) (m : mem) (c : Z) : Prop :=
let x := cls a c in let sz := class_size c in let rb := reg_beg (ae_L RE) c in
(forall i t, tag_at G c i = Some t -> tag_prim t = true -> hjunk m (slot_beg RE c i) (slot_beg RE c i + sz))
/\ hjunk m (rb + c_alloc_user x) (rb + c_mapped_user x)
/\ (forall i t, tag_at G c i = Some t -> tag_prim t = true ->
rw_cells asegs m (SH (slot_beg RE c i)) [CB (Z.to_nat (sz / 8)) (repeat fa_byte (Z.to_nat (sz / 8)))])
/\ rw_cells asegs m (SH (rb + c_alloc_user x))
[CB (Z.to_nat ((c_mapped_user x - c_alloc_user x) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user x - c_alloc_user x) / 8)))]
/\ hjunk m (SH (rb + c_mapped_user x)) (SH (rb + kFreeArrayOffset)).

Definition uzone (RE : aentry) (c : Z) (z : Z) : Prop :=
(reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset) \/ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z.

Lemma class_rep_split : forall a G RE X m c K,
class_rep a G RE X m c K <->
cr_cells a RE X m c K /\ cr_pure a G c K /\
(1 <= c -> u32arr asegs m (fa_beg (ae_L RE) c) (map (fun i => Z_to_bv 64 (coff c i)) (pk_fl K))
/\ hjunk m (fa_beg (ae_L RE) c + 4 * c_num_freed (cls a c)) (fa_beg (ae_L RE) c + c_mapped_fa (cls a c))
/\ cr_user a G RE m c
/\ hjunk m (SH (fa_beg (ae_L RE) c)) (SH (fa_beg (ae_L RE) c + kFreeArraySize))).
Proof.
intros a G RE X m c K. unfold class_rep, cr_region, cr_user. split.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
Qed.

Lemma cr_user_agree : forall a G RE m m' c K,
cr_pure a G c K -> cr_user a G RE m c -> 1 <= c <= 31 -> agree_on asegs (uzone RE c) m m' -> cr_user a G RE m' c.
Proof.
intros a G RE m m' c K PU HU HCL AG. unfold cr_user in HU. destruct HU as (SL & UT & SS & US & UJ). pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _). rewrite KM in G5.
pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (INU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset -> uzone RE c z) by (intros z Hz; left; exact Hz).
assert (INUS : forall z, SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8 -> uzone RE c z).
{ intros z Hz. right. split; cbn [fst snd]; lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KO8 SZ1 G3 G2 G1 K c G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H26 H25 H19 q3 H14 q2 H5 H4 r0 H0 H r KO8 q0 SZ2 r2 SZ1 G5 r3 G4 G3 G2 G1 P14 r4 q K c G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H31 H30 H24 q4 H0 H r q G5 r4 P14 r5 K c G a; lia | lia ])).
destruct MU8 as (qm & QM).
assert (GEOM : forall i t, tag_at G c i = Some t ->
0 <= i /\ (i + 1) * class_size c <= c_alloc_user (cls a c)
/\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c
/\ exists k, 0 <= k /\ i * class_size c = 8 * k /\ class_size c = 8 * (class_size c / 8)).
{ intros i t Ht. pose proof (tag_at_lt G c i t Ht) as [I1 I2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; (first [ clear - H26 H25 H14 q2 H0 H r SZ2 r2 P14 r4 q K c G; lia | lia ])).
split; [lia|]. split; [(first [ clear - E8 I2 i QM qm KO8 SZ2 SZ1 G5 G4 G3 G2 G1 P14 P12 P1 K c G a; nia | nia ])|]. split; [reflexivity|]. exists (i * (class_size c / 8)). split; [(first [ clear - E8 I1 i QM qm KO8 SZ2 SZ1 G5 G4 G3 G2 G1 P14 K c G a; nia | nia ])|]. split; [(first [ clear - E8 i SZ1 G3 K c G a; nia | nia ])| exact E8]. }
split; [|split; [|split; [|split]]].
- intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (GEOM i t Ht) as (I1 & IL & SB & _). rewrite SB in Hz. apply INU. clear - Hz I1 IL G3 G4 SZ1. nia.
- eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply INU. lia.
- intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (GEOM i t Ht) as (I1 & IL & SB & k & K0 & K1 & K2).
rewrite SB, K1, SH_plus8 in Hz. apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia.
clear - Hz I1 IL G3 G4 SZ1 K0 K1 K2 KO8. nia.
- eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
- eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G2 G3 G4 KO8 QA QA0; lia.
Qed.

Lemma cr_user_ext : forall a a' G RE m c,
cr_user a G RE m c -> c_alloc_user (cls a' c) = c_alloc_user (cls a c) -> c_mapped_user (cls a' c) = c_mapped_user (cls a c) ->
cr_user a' G RE m c.
Proof. intros a a' G RE m c H E1 E2. unfold cr_user in *. rewrite E1, E2. exact H. Qed.

Lemma uzone_bounds {BAND : Band} : forall RE X c z, rlay_ok RE X -> 0 <= c < 32 -> uzone RE c z ->
(reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + 3758096384)
\/ (SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + 469762048).
Proof.
intros RE X c z RL Hc U. pose proof kconsts as (KR & KO & _). unfold uzone, in_sh in U. cbn [fst snd] in U. rewrite KO in U.
change (3758096384 / 8) with 469762048 in U. exact U.
Qed.

Lemma fp_RPrim_lt_ceil {BAND : Band} : forall G RE X x, rlay_ok RE X -> fp_RPrim G RE X x -> x < band_lo.
Proof.
intros G RE X x RL F. pose proof (rlay_prim_facts RE X RL) as (P0 & P1 & P2 & _).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof kconsts as (KR & KO & KS & K32 & _).
rewrite ?KHI_eq in *. unfold prim_lo, prim_hi, region_info in *.
destruct F as [F|[F|[F|[F|[[F _]|[F _]]]]]].
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. unfold region_info in *. lia.
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. lia.
- destruct F as (c & Hc & F1 & F2). unfold fa_beg, reg_beg in *. rewrite KR, KO, KS, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold fa_beg, reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, KS, K32 in *.
Z.div_mod_to_equations. nia.
- destruct F as (c & Hc & F1 & F2). unfold reg_beg in *. rewrite KR, KO, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, K32 in *.
Z.div_mod_to_equations. nia.
Qed.

Lemma RPrim_stack {BAND : Band} : forall a G RE X m m' W,
RPrim a G RE X m -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> RPrim a G RE X m'.
Proof.
intros a G RE X m m' W RP RL MU WM FW. eapply RPrim_frame; [exact RP| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. cbn [fst] in C.
pose proof (fp_RPrim_lt_ceil G RE X x RL Fx). lia.
Qed.

Lemma rw_cells_CB_app : forall m A n1 l1 n2 l2,
rw_cells asegs m A [CB n1 l1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 l2] ->
rw_cells asegs m A [CB (n1 + n2) (l1 ++ l2)].
Proof.
intros m A n1 l1 n2 l2 H1 H2.
assert (H : rw_cells asegs m A ([CB n1 l1] ++ [CB n2 l2])).
{ apply (proj2 (rw_cells_app asegs m A [CB n1 l1] [CB n2 l2])). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; assumption. }
destruct H1 as [[[L1 _] _] _]. destruct H2 as [[[L2 _] _] _]. cbn in L1, L2.
eapply rw_cells_recast'; [exact H| cbn; rewrite length_app; lia| cbn; rewrite !app_nil_r; reflexivity].
Qed.

Lemma rw_cells_CB_split : forall m A n1 n2 l,
rw_cells asegs m A [CB (n1 + n2) l] ->
rw_cells asegs m A [CB n1 (firstn n1 l)] /\ rw_cells asegs m (A + Z.of_nat n1) [CB n2 (skipn n1 l)].
Proof.
intros m A n1 n2 l H. assert (L : length l = (n1 + n2)%nat) by (destruct H as [[[L _] _] _]; cbn in L; lia).
assert (H' : rw_cells asegs m A ([CB n1 (firstn n1 l)] ++ [CB n2 (skipn n1 l)])).
{ eapply rw_cells_recast'; [exact H| cbn; rewrite length_take, length_drop; lia| cbn; rewrite !app_nil_r; apply firstn_skipn]. }
apply (proj1 (rw_cells_app asegs m A _ _)) in H'. cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QDw3 QNwL QYnC QSsj QNQk.Mq1.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma st_avoid_offhull : forall lo hi, (hi <= 0x10000 \/ 0x645000 <= lo) -> st_avoid (lo, hi).
Proof. intros lo hi H x [Hx1 Hx2] K; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.

Lemma st_avoid_T {BAND : Band} : forall RE X lo hi, rlay_ok RE X -> rl_T X <= lo -> hi <= rl_T X + 0x1000 -> st_avoid (lo, hi).
Proof.
intros RE X lo hi RL H1 H2. apply st_avoid_offhull.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & [_ TH] & _). cbn [fst snd] in TH. lia.
Qed.

Ltac st_avoid_solve :=
lazymatch goal with
| |- st_avoid (?lo, _) =>
lazymatch lo with
| context [rl_T _] => eapply st_avoid_T; [eassumption| cbn [fst snd]; lia| cbn [fst snd]; lia]
| _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; unfold prim_lo, prim_hi in *; lia
end
| |- _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; unfold prim_lo, prim_hi in *; lia
end.

Definition zsel (P : bool) : Z := Z.b2z P.
Arguments zsel : simpl never.
Lemma or_le_lia : forall a b c d, a <= b \/ c <= d -> a - b <= 2^66 -> c - d <= 2^66 ->
0 <= zsel (a <=? b) <= 1 /\ a <= b + (1 - zsel (a <=? b)) * 2^66 /\ c <= d + zsel (a <=? b) * 2^66.
Proof.
intros a b c d H B1 B2. unfold zsel. destruct (Z.leb_spec a b) as [L|L]; cbn [Z.b2z]; lia.
Qed.
Ltac encode_or H := apply or_le_lia in H; [| lia| lia].
End Mq2.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition run_free_hooks_entry : Z := 0x71c84.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma run_free_hooks_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 32 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz run_free_hooks_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. idtac. rtc RT 41%nat K41. unfold run_free_hooks_entry.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
do 5 step.
step. step. step.
step. if_lit.
step. step. step.
step. step. step.
step. if_lit.
do 5 step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; idtac; lia| constructor].
Qed.
End S.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition mem_to_shadow_entry : Z := 0x4ac30.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma mem_to_shadow_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
RTconst RE X m -> mem_inv asegs m -> (0 <= p <= 0x7fff7fff \/ KHI <= p < 2^47) ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz mem_to_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros RT MI HP. rewrite ?KHI_eq in HP. unfold mem_to_shadow_entry.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1.
destruct HP as [HP|HP].
-
step_until 0. if_true_u. step_until 0.
apply evt_done; unfold leaf_post; do 15 eexists; split; [reflexivity|]. f_equal. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. change (2 ^ 3) with 8. lia.
- step_until 0. if_false_u. step_until 0. if_true_u. step_until 0. if_false_u. step_until 0. if_false_u. step_until 0.
apply evt_done; unfold leaf_post; do 15 eexists; split; [reflexivity|]. f_equal. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. change (2 ^ 3) with 8. lia.
Qed.
End Walk.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition m2s_entry : Z := 0x64d20.
Definition miz_entry : Z := 0x754a0.
Definition rip_entry : Z := 0x651ac.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma m2s_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
RTconst RE X m -> rlay_ok RE X -> KHI <= p -> p < 2^47 ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz m2s_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros RT RL K1p K2p. rewrite ?KHI_eq in K1p. idtac. unfold m2s_entry.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
step. step. step. step. step. step.
stp. step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia.
Qed.

Lemma m2s_spec_low : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
RTconst RE X m -> rlay_ok RE X -> 0 <= p -> p <= 0x7fff7fff ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz m2s_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros RT RL K1p K2p. rewrite ?KHI_eq in K1p. idtac. unfold m2s_entry.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia.
Qed.

Definition zrd (m : mem) (A n : Z) : Prop := forall i, 0 <= i < n -> bytes_at asegs m (A + i) [b8 0].

Lemma zrd_ro1 : forall m A n a, zrd m A n -> A <= a -> a + 1 <= A + n -> ro_cells asegs m a [C1 (b8 0)].
Proof.
intros m A n a ZR H1 H2. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
replace a with (A + (a - A)) by lia. apply ZR. lia.
Qed.

Lemma zrd_bytes : forall m A n k j, zrd m A n -> A <= j -> j + Z.of_nat k <= A + n -> (0 < k)%nat ->
bytes_at asegs m j (repeat (b8 0) k).
Proof.
intros m A n k. induction k as [|k IH]; intros j ZR Hj Hk Hp; [lia|].
cbn [repeat]. change (b8 0 :: repeat (b8 0) k) with ([b8 0] ++ repeat (b8 0) k). apply (proj2 (bytes_at_app _ _ _ _ _)).
split; [replace j with (A + (j - A)) by lia; apply ZR; lia|].
replace (j + Z.of_nat (length [b8 0])) with (j + 1) by (cbn; lia).
destruct k as [|k'].
-
pose proof (ZR (j - A) ltac:(lia)) as (B1 & B2 & _). cbn in B2. replace (A + (j - A)) with j in * by lia.
split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
- apply IH; [exact ZR| lia| lia| lia].
Qed.

Lemma zrd_ro8 : forall m A n a, zrd m A n -> A <= a -> a + 8 <= A + n -> ro_cells asegs m a [C8 (wz 0)].
Proof.
intros m A n a ZR H1 H2. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
change (le8 (wz 0)) with (repeat (b8 0) 8). eapply zrd_bytes; [exact ZR| lia| cbn; lia| lia].
Qed.

Lemma zrd_munch : forall m m' A n W, zrd m A n -> munch W m m' -> wmono asegs m m' ->
(forall x, A <= x < A + n -> outside W x) -> zrd m' A n.
Proof.
intros m m' A n W ZR MU WM HO i Hi. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM|]| apply ZR; exact Hi|].
- intros x Hx _. exact (HO x Hx).
- intros a Ha. cbn in Ha |- *. lia.
Qed.

Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma miz_bloop : forall k (c : Z) ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n ab ae e : Z) P,
zrd m A n -> e = A + n -> 0 <= A -> A + 1 <= c -> c <= ab -> c <= e -> ab <= e + 8 -> e <= KHI -> k = Z.to_nat (e - c) ->
(forall a3' a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) a3' (wz e) (wz ab) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x754f8) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) (wz c) (wz e) (wz ab) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x754e0) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR He A0 C1 C2 C3 C4 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A n (c + -1) ZR ltac:(lia) ltac:(lia)) as B.
step. step. stp.
step. destruct (Z_le_gt_dec ab c) as [X1|X1].
{ ifz. apply K. }
ifz. stp. step. destruct (Z_lt_le_dec c e) as [X2|X2].
- ifz. eapply (IH (Z.to_nat (e - (c + 1)))); [lia| exact ZR| lia| lia| lia| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. apply K.
Qed.

Lemma miz_wloop : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n ae e : Z) P,
zrd m A n -> e = A + n -> 0 <= A -> A <= p -> p + 8 <= ae -> ae <= e -> p mod 8 = 0 -> ae mod 8 = 0 -> e <= KHI ->
k = Z.to_nat (ae - p) ->
(forall a3' a5', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) a3' (wz e) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7550c) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) a3 (wz e) (wz p) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x754fc) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR He A0 C1 C2 C3 P8 E8 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro8 m A n p ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. step. destruct (Z_lt_le_dec (p + 8) ae) as [X1|X1].
- ifz. eapply (IH (Z.to_nat (ae - (p + 8)))); [lia| exact ZR| lia| lia| lia| Z.div_mod_to_equations; lia| lia| Z.div_mod_to_equations; lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. apply K.
Qed.

Lemma miz_eloop : forall k (q : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n e : Z) P,
zrd m A n -> e = A + n -> 0 <= A -> A <= q -> q < e -> e <= KHI -> k = Z.to_nat (e - q) ->
(forall a0' a2' a4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz 0) a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7552c) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) (wz q) a3 (wz (e - q)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75518) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR He A0 C1 C2 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A n q ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. stp. step. destruct (Z_lt_le_dec (q + 1) e) as [X1|X1].
- ifz. replace (e - q + -1) with (e - (q + 1)) by lia.
eapply (IH (Z.to_nat (e - (q + 1)))); [lia| exact ZR| lia| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. apply K.
Qed.

Lemma miz_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n lo : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
zrd m A n -> 0 < n -> n <= 2^40 -> 0x645000 <= A -> A + n + 8 <= KHI ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' _ => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz miz_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST CEIL LO ZR N0 N40 ALO AHI.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AHI.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold miz_entry.
carve_frame 16%nat ST.
istep. istep.
step. step. step. step. step. ifz.
step. step. step. stp. stp.
rewrite (unsigned_lit (A + 7)), (unsigned_lit (A + n)) by lia. rewrite !land_m8 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ZR' : zrd mc A n) by (eapply zrd_munch; [exact ZR| exact MU| exact WM| intros x Hx; cbn; lia]) end.
set (ab := A + 7 - (A + 7) mod 8). set (ae := A + n - (A + n) mod 8).
assert (AB : A <= ab < A + 8 /\ ab mod 8 = 0) by (subst ab; Z.div_mod_to_equations; lia).
assert (AE : A + n - 8 < ae <= A + n /\ ae mod 8 = 0) by (subst ae; Z.div_mod_to_equations; lia).
clearbody ab ae.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a6' : word, ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 16 a6' R)) FF (wz 0x754f8) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ab A) as [X1|X1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. step. ifz. step. stp.
eapply (miz_bloop (Z.to_nat (A + n - (A + 1))) (A + 1)); [exact ZR'| reflexivity| lia| lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3' a6'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a6' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a3'' a5' : word, ms2 = MS (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 15 a5' R)) FF (wz 0x7550c) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ae ab) as [X2|X2].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. eapply (miz_wloop (Z.to_nat (ae - ab)) ab); [exact ZR'| reflexivity| lia| lia| Z.div_mod_to_equations; lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3'' a5'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a3'' & a5' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall a0' a2' a4',
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m (fun a0'' _ => a0'' = wz 1))
(MS (mkR ra (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0' (wz 0) a2' a3'' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7552c) fc None mc (seg_rom asegs)))
end.
{ intros a0' a2' a4'. stp. step. step.
release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity. }
step. destruct (Z_lt_le_dec ae A) as [X3|X3].
{ ifz. apply TAIL. }
ifz. step. destruct (Z_le_gt_dec (A + n) ae) as [X4|X4].
{ ifz. apply TAIL. }
ifz. stp. rewrite (unsigned_lit ae) by lia. replace (A + n + - ae) with (A + n - ae) by lia.
eapply (miz_eloop (Z.to_nat (A + n - ae)) ae); [exact ZR'| reflexivity| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a0' a2' a4'. apply TAIL.
Qed.

Definition shadow_ok (m : mem) (dst n : Z) : Prop :=
forall k, 0 <= k -> dst / 8 * 8 + 8 * k < dst + n ->
exists v, bytes_at asegs m (SH (dst / 8 * 8) + k) [b8 v] /\
(v = 0 \/ (0 < v < 8 /\ dst + n <= dst / 8 * 8 + 8 * k + v)).

Lemma shadow_ok_munch : forall m m' dst n W, shadow_ok m dst n -> munch W m m' -> wmono asegs m m' ->
(forall x, SH dst <= x <= SH (dst + n - 1) -> outside W x) -> 0 < n -> shadow_ok m' dst n.
Proof.
intros m m' dst n W SO MU WM HO N0 k Hk Hkn. destruct (SO k Hk Hkn) as (v & B & C). exists v. split; [| exact C].
eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM|]| exact B|].
- intros x Hx _. exact (HO x Hx).
- intros a Ha. cbn in Ha |- *. rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_first : forall m dst n, shadow_ok m dst n -> 0 < n ->
exists v, ro_cells asegs m (SH dst) [C1 (b8 v)] /\ 0 <= v < 8 /\ (v = 0 \/ dst mod 8 < v).
Proof.
intros m dst n SO N0. destruct (SO 0 ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
exists v. split; [| Z.div_mod_to_equations; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
replace (SH dst) with (SH (dst / 8 * 8) + 0); [exact B|]. rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_last : forall m dst n, shadow_ok m dst n -> 0 < n ->
exists v, ro_cells asegs m (SH (dst + n - 1)) [C1 (b8 v)] /\ 0 <= v < 8 /\ (v = 0 \/ (dst + n - 1) mod 8 < v).
Proof.
intros m dst n SO N0.
destruct (SO ((dst + n - 1) / 8 - dst / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
exists v. split; [| Z.div_mod_to_equations; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
replace (SH (dst + n - 1)) with (SH (dst / 8 * 8) + ((dst + n - 1) / 8 - dst / 8)); [exact B|]. rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_zrd : forall m dst n, shadow_ok m dst n -> 0 < n ->
zrd m (SH ((dst + 7) / 8 * 8)) (SH ((dst + n) / 8 * 8) - SH ((dst + 7) / 8 * 8)).
Proof.
intros m dst n SO N0 i Hi. rewrite !SH_eq in Hi.
destruct (SO (((dst + 7) / 8 * 8 - dst / 8 * 8) / 8 + i) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
assert (v = 0) as -> by (Z.div_mod_to_equations; lia).
match type of B with bytes_at _ _ ?a _ => replace (SH ((dst + 7) / 8 * 8) + i) with a; [exact B|] end.
rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma signed_small : forall e, 0 <= e < 2^63 -> bv_signed (wz e) = e.
Proof. intros e He. rewrite zb_signed, (unsigned_lit e) by lia. destruct (Z.ltb_spec0 e (2^63)); lia. Qed.
Lemma land7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac rip_tail RT RL FR ST usp :=
do 10 step; release_frame FR ST usp;
step; apply evt_done; unfold rpost; do 16 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|]; split; [reflexivity| rt_solve RT RL].

Lemma rip_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> KHI <= dst -> dst + n <= band_lo ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO SO [N0 N43] K1d K2d.
pose proof CEIL as CEIL'. idtac. pose proof K1d as K1d'. pose proof K2d as K2d'.
rewrite ?KHI_eq in K1d. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold rip_entry.
carve_frame 64%nat ST.
do 8 istep.
step. ifz.
step. step. rt_now RT RL 19%nat K19. rt_now RT RL 5%nat K5. rt_now RT RL 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp.
step. ifz.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
step. ifz.
stp. stp. stp.
rewrite (unsigned_lit (dst + 7)), (unsigned_lit (n + dst)) by lia. rewrite !land_m8 by lia.
set (ab8 := dst + 7 - (dst + 7) mod 8). set (ae8 := n + dst - (n + dst) mod 8).
assert (AB : dst <= ab8 < dst + 8 /\ ab8 mod 8 = 0 /\ ab8 = (dst + 7) / 8 * 8) by (subst ab8; Z.div_mod_to_equations; lia).
assert (AE : dst + n - 8 < ae8 <= dst + n /\ ae8 mod 8 = 0 /\ ae8 = (dst + n) / 8 * 8) by (subst ae8; Z.div_mod_to_equations; lia).
clearbody ab8 ae8.
step. call0 m2s_spec; [rt_solve RT RL| exact RL| lia| idtac; lia|]. subst_words.
step. step. step. call0 m2s_spec; [rt_solve RT RL| exact RL| rewrite ?KHI_eq; clear - AE K1d N0; Z.div_mod_to_equations; lia| idtac; lia|]. subst_words.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | exact N0]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (shadow_ok_first _ dst n SO' N0) as (v0 & B0 & R0 & C0).
destruct (shadow_ok_last _ dst n SO' N0) as (v1 & B1 & R1 & C1).

step. stp. stp. rewrite (unsigned_lit dst) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
step.
rewrite (sxb_b8 v0) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' : word, ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' R)) FF (wz 0x652bc) fcc rv mm ro))
end.
{ step. destruct C0 as [->|C0].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit dst), land7 by lia. step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a2' & a3' & ->). simp_regs.

stp. stp. stp. rewrite (unsigned_lit (n + dst + -1)) by lia.
replace (2147450880 + (n + dst + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
step. rewrite (sxb_b8 v1) by lia.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' a2'' : word, ms2 = MS (@bvmap_set 5 word 11 a1' (@bvmap_set 5 word 12 a2'' R)) FF (wz 0x65310) fcc rv mm ro))
end.
{ step. destruct C1 as [->|C1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit (n + dst + -1)), land7 by lia. replace ((n + dst + -1) mod 8) with ((dst + n - 1) mod 8) by (f_equal; lia).
step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a1' & a2'' & ->). simp_regs.

pose proof (shadow_ok_zrd _ dst n SO' N0) as ZR. destruct AB as (AB1 & AB2 & AB3). destruct AE as (AE1 & AE2 & AE3).
rewrite <- AB3, <- AE3 in ZR.
assert (SHB : 0x2008fff7000 <= SH ab8 /\ SH ae8 + 8 <= 0x10007fff8000 /\ 8 * (SH ae8 - SH ab8) = ae8 - ab8).
{ rewrite !SH_eq. clear - AB1 AB2 AE1 AE2 K1d K2d N0. Z.div_mod_to_equations. lia. }
step. destruct (Z_le_gt_dec (SH ae8) (SH ab8)) as [X5|X5].
{ ifz. rip_tail RT RL FR ST (bv_unsigned sp). }
ifz. stp. rewrite ?(unsigned_lit (SH ae8)), ?(unsigned_lit (SH ab8)) by lia. replace (SH ae8 + - SH ab8) with (SH ae8 - SH ab8) by lia.
step. step.
call_u miz_spec.
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ZR. } { lia. } { clear - SHB AB1 AE1 N43; Z.div_mod_to_equations; lia. } { lia. } { rewrite ?KHI_eq. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
step. ifz. rip_tail RT RL FR ST' (bv_unsigned sp).
Qed.

Lemma rip_spec_low : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> 0 <= dst -> dst + n <= 0x7fff7800 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO SO [N0 N43] K1d K2d.
pose proof CEIL as CEIL'. idtac. pose proof K1d as K1d'. pose proof K2d as K2d'.
rewrite ?KHI_eq in K1d. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold rip_entry.
carve_frame 64%nat ST.
do 8 istep.
step. ifz.
step. step. rt_now RT RL 19%nat K19. rt_now RT RL 5%nat K5. rt_now RT RL 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
stp.
step. ifz.
step. ifz.
stp. stp. stp.
rewrite (unsigned_lit (dst + 7)), (unsigned_lit (n + dst)) by lia. rewrite !land_m8 by lia.
set (ab8 := dst + 7 - (dst + 7) mod 8). set (ae8 := n + dst - (n + dst) mod 8).
assert (AB : dst <= ab8 < dst + 8 /\ ab8 mod 8 = 0 /\ ab8 = (dst + 7) / 8 * 8) by (subst ab8; Z.div_mod_to_equations; lia).
assert (AE : dst + n - 8 < ae8 <= dst + n /\ ae8 mod 8 = 0 /\ ae8 = (dst + n) / 8 * 8) by (subst ae8; Z.div_mod_to_equations; lia).
clearbody ab8 ae8.
step. call0 m2s_spec_low; [rt_solve RT RL| exact RL| lia| idtac; lia|]. subst_words.
step. step. step. call0 m2s_spec_low; [rt_solve RT RL| exact RL| rewrite ?KHI_eq; clear - AE K1d N0; Z.div_mod_to_equations; lia| idtac; lia|]. subst_words.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | exact N0]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (shadow_ok_first _ dst n SO' N0) as (v0 & B0 & R0 & C0).
destruct (shadow_ok_last _ dst n SO' N0) as (v1 & B1 & R1 & C1).

step. stp. stp. rewrite (unsigned_lit dst) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
step.
rewrite (sxb_b8 v0) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' : word, ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' R)) FF (wz 0x652bc) fcc rv mm ro))
end.
{ step. destruct C0 as [->|C0].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit dst), land7 by lia. step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a2' & a3' & ->). simp_regs.

stp. stp. stp. rewrite (unsigned_lit (n + dst + -1)) by lia.
replace (2147450880 + (n + dst + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
step. rewrite (sxb_b8 v1) by lia.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' a2'' : word, ms2 = MS (@bvmap_set 5 word 11 a1' (@bvmap_set 5 word 12 a2'' R)) FF (wz 0x65310) fcc rv mm ro))
end.
{ step. destruct C1 as [->|C1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit (n + dst + -1)), land7 by lia. replace ((n + dst + -1) mod 8) with ((dst + n - 1) mod 8) by (f_equal; lia).
step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a1' & a2'' & ->). simp_regs.

pose proof (shadow_ok_zrd _ dst n SO' N0) as ZR. destruct AB as (AB1 & AB2 & AB3). destruct AE as (AE1 & AE2 & AE3).
rewrite <- AB3, <- AE3 in ZR.
assert (SHB : 0x7fff8000 <= SH ab8 /\ SH ae8 <= 0x8fff7000 /\ 8 * (SH ae8 - SH ab8) = ae8 - ab8).
{ rewrite !SH_eq. clear - AB1 AB2 AE1 AE2 K1d K2d N0. Z.div_mod_to_equations. lia. }
step. destruct (Z_le_gt_dec (SH ae8) (SH ab8)) as [X5|X5].
{ ifz. rip_tail RT RL FR ST (bv_unsigned sp). }
ifz. stp. rewrite ?(unsigned_lit (SH ae8)), ?(unsigned_lit (SH ab8)) by lia. replace (SH ae8 + - SH ab8) with (SH ae8 - SH ab8) by lia.
step. step.
call_u miz_spec.
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ZR. } { lia. } { clear - SHB AB1 AE1 N43; Z.div_mod_to_equations; lia. } { lia. } { rewrite ?KHI_eq. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
step. ifz. rip_tail RT RL FR ST' (bv_unsigned sp).
Qed.

Lemma rip_spec_lh : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> ((KHI <= dst /\ dst + n <= band_lo) \/ (0 <= dst /\ dst + n <= 0x7fff7800)) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO SO NR [[K1d K2d]|[K1d K2d]].
- eapply rip_spec; eassumption.
- eapply rip_spec_low; eassumption.
Qed.

End S.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QDM6.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj QNQk.Mq4.
Import Qu1d.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition rz_size2log_entry : Z := 0x44768.

Definition rz_log_of (v : Z) : Z := if v =? 16 then 0 else 7.

Lemma rz_size2log_spec {BAND : Band} : forall v ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
(v = 16 \/ v = 2048) ->
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (rz_log_of v)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rz_size2log_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros HV MI ST CEIL LO. idtac. unfold rz_size2log_entry.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
destruct HV as [-> | ->]; cbn [rz_log_of Z.eqb Pos.eqb].
- repeat (stp; try if_lit).
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity.
- repeat (stp; try if_lit).
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity.
Qed.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QUnM QZbm.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma shword_eq : forall x, 8 * (SH x / 8) = SH (64 * (x / 64)).
Proof. intros x. rewrite !SH_eq. Z.div_mod_to_equations. lia. Qed.

Lemma shword_pt : forall x z, 8 * (SH x / 8) <= z < 8 * (SH x / 8) + 8 ->
exists y, y mod 8 = 0 /\ 64 * (x / 64) <= y < 64 * (x / 64) + 64 /\ SH y = z.
Proof.
intros x z Hz. rewrite shword_eq, SH_eq in Hz. exists (8 * (z - 0x7fff8000)). rewrite SH_eq.
Z.div_mod_to_equations. lia.
Qed.

Lemma sh_in : forall lo hi y, lo mod 8 = 0 -> hi mod 8 = 0 -> lo <= y < hi -> y mod 8 = 0 -> SH lo <= SH y < SH hi.
Proof. intros lo hi y AL AH Hy Y8. rewrite !SH_eq. Z.div_mod_to_equations. lia. Qed.

Section S.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Hypothesis RP : RPrim a G RE X m.
Hypothesis RCH : RChunks a LB0 G RE X m.
Hypothesis RQ : RQuar a LB0 G RE X m.
Hypothesis RF : RFake FS0 RE X m.
Local Notation L := (ae_L RE).

Definition shsome (lo hi : Z) : Prop :=
forall y, lo <= y < hi -> y mod 8 = 0 -> exists b, m (wa (SH y)) = Some b.

Lemma shsome_of_hjunk : forall lo hi, lo mod 8 = 0 -> hi mod 8 = 0 -> hjunk m (SH lo) (SH hi) -> shsome lo hi.
Proof. intros lo hi AL AH (_ & _ & J) y Hy Y8. apply J. apply sh_in; assumption. Qed.

Lemma shword_hjunk : forall lo hi x, lo mod 64 = 0 -> hi mod 64 = 0 -> 0 <= lo -> hi <= band_lo -> lo <= x < hi ->
shsome lo hi -> hjunk m (8 * (SH x / 8)) (8 * (SH x / 8) + 8).
Proof.
intros lo hi x AL AH K CE Hx SS. pose proof (shword_eq x) as E. rewrite ?KHI_eq in K. idtac.
split; [rewrite E, SH_eq; Z.div_mod_to_equations; lia|].
split; [rewrite E, SH_eq; Z.div_mod_to_equations; lia|].
intros z Hz. destruct (shword_pt x z Hz) as (y & Y8 & Hy & <-). apply SS; [| exact Y8].
Z.div_mod_to_equations. nia.
Qed.

Lemma cells_hjunk_sh : forall lo cs, rw_cells asegs m (SH lo) cs -> KHI <= lo -> hjunk m (SH lo) (SH lo + Z.of_nat (cells_size cs)).
Proof. intros lo cs H K. apply cells_hjunk; [exact H|]. rewrite SH_eq, ?KHI_eq in *. Z.div_mod_to_equations. lia. Qed.

Lemma cells_hjunk_sh0 : forall lo cs, rw_cells asegs m (SH lo) cs -> 0 <= lo -> hjunk m (SH lo) (SH lo + Z.of_nat (cells_size cs)).
Proof. intros lo cs H K. apply cells_hjunk; [exact H|]. rewrite SH_eq in *. Z.div_mod_to_equations. lia. Qed.

Lemma batches_shadow : forall QA bs J j, batches_mem RE m QA bs J -> In j J ->
rw_cells asegs m (SH (slot_beg RE 24 j)) [CB 1024%nat (fas 1024)].
Proof.
intros QA bs. induction bs as [|b bs IH]; intros J j H Hin; destruct J as [|j' J]; cbn in H, Hin; try contradiction.
destruct H as [HB H]. destruct Hin as [<-|Hin].
- destruct HB as (_ & _ & _ & S). exact S.
- eapply IH; [exact H| exact Hin].
Qed.

Lemma chunk_mem_shadow : forall lo hi A n, chunk_mem m lo hi A n -> hjunk m (SH lo) (SH lo + (hi - lo) / 8).
Proof.
intros lo hi A n CM. pose proof CM as (_ & _ & _ & _ & S & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(unfold used_size; lia)) as (U1 & U2 & U3).
pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
pose proof (cells_hjunk_sh0 lo _ S ltac:(clear - M8; lia)) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J.
match type of J with hjunk _ _ ?e => replace (SH lo + (hi - lo) / 8) with e; [exact J|] end.
Z.div_mod_to_equations. nia.
Qed.

Lemma qchunk_mem_shadow : forall lo hi A n, qchunk_mem m lo hi A n -> hjunk m (SH lo) (SH lo + (hi - lo) / 8).
Proof.
intros lo hi A n CM. pose proof CM as (_ & _ & _ & (sj & S) & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (qchunk_geom m lo hi A n CM) as (_ & _ & _ & _ & _ & _ & _ & _ & q & g & r & Q1 & Q2 & G1 & G2 & G3 & R1 & R2 & T).
pose proof (cells_hjunk_sh0 lo _ S ltac:(clear - M8; lia)) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J.
match type of J with hjunk _ _ ?e => replace (SH lo + (hi - lo) / 8) with e; [exact J|] end.
rewrite G2 in *. Z.div_mod_to_equations. nia.
Qed.

Lemma slot_shadow : forall c i t, tag_at G c i = Some t ->
hjunk m (SH (slot_beg RE c i)) (SH (slot_beg RE c i) + class_size c / 8).
Proof.
intros c i t Ht.
pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & P8 & P16 & Hc & R1 & R2 & S32 & SM).
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & KP & _).
assert (KS : KHI <= slot_beg RE c i) by lia.
destruct t as [| |p|p|].
-
destruct RP as (K & _ & _ & CR). destruct (CR c ltac:(unfold kNumClasses; lia)) as (_ & _ & REG).
destruct (REG ltac:(lia)) as (_ & _ & _ & _ & FS & _). specialize (FS i TFree Ht eq_refl).
pose proof (cells_hjunk_sh _ _ FS KS) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia. exact J.
-
destruct RP as (K & _ & _ & CR). destruct (CR c ltac:(unfold kNumClasses; lia)) as (_ & _ & REG).
destruct (REG ltac:(lia)) as (_ & _ & _ & _ & FS & _). specialize (FS i TCached Ht eq_refl).
pose proof (cells_hjunk_sh _ _ FS KS) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia. exact J.
-
destruct (gc_live_tags' a LB0 FS0 G RE X GC c i p Ht) as (id & n & A & -> & Hin & Hcl).
pose proof (proj1 RCH _ _ _ Hin) as CR. cbn [chunk_rep] in CR. destruct CR as (_ & i' & Ht' & HA & CM).
rewrite Hcl in Ht', HA, CM.
assert (i' = i) as ->.
{ symmetry. eapply proj2. eapply (gc_unique a LB0 FS0 G RE X GC c i c i' (APrim id n)); [exact Ht| exact Ht'| |]; cbn; rewrite N.eqb_refl, Z.eqb_refl; reflexivity. }
pose proof (chunk_mem_shadow _ _ _ _ CM) as J.
replace (slot_beg RE c i + class_size c - slot_beg RE c i) with (class_size c) in J by lia. exact J.
-
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & BND).
destruct (TQP c i p Ht) as [HinP Hcl]. pose proof (REP p HinP) as QR.
destruct (gc_quar_tags a LB0 FS0 G RE X GC c i p Ht) as [_ FP].
destruct p as [id n|mb n]; cbn [qptr_rep] in QR.
+ destruct QR as (i' & Ht' & _ & HQA & CM). unfold aptr_cls in Hcl. cbn [aptr_req] in Hcl. rewrite Hcl in Ht', HQA, CM.
assert (i' = i) as ->.
{ symmetry. eapply proj2. eapply (gc_unique a LB0 FS0 G RE X GC c i c i' (APrim id n)); [exact Ht| exact Ht'| |]; cbn; rewrite N.eqb_refl, Z.eqb_refl; reflexivity. }
pose proof (qchunk_mem_shadow _ _ _ _ CM) as J.
replace (slot_beg RE c i + class_size c - slot_beg RE c i) with (class_size c) in J by lia. exact J.
+ destruct QR as (_ & _ & FP' & _). cbn [aptr_req] in FP. rewrite FP in FP'. discriminate.
-
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & BND).
pose proof (C24 c i Ht) as ->. specialize (TQO i Ht). apply in_app_or in TQO.
assert (S : rw_cells asegs m (SH (slot_beg RE 24 i)) [CB 1024%nat (fas 1024)]).
{ destruct TQO as [Hin|Hin].
- destruct HT as (_ & BM & _). eapply batches_shadow; [exact BM| exact Hin].
- destruct HG as (_ & BM & _). eapply batches_shadow; [exact BM| exact Hin]. }
pose proof (cells_hjunk_sh _ _ S KS) as J. cbn [cells_size csize Nat.add] in J.
change (class_size 24 / 8) with 1024. exact J.
Qed.

Lemma region_shadow : forall c, 1 <= c <= 31 -> shsome (reg_beg L c) (reg_beg L c + kFreeArrayOffset).
Proof.
intros c Hc y Hy Y8.
destruct RP as (K & _ & _ & CR). destruct (CR c ltac:(unfold kNumClasses; lia)) as (_ & PU & REG).
destruct (REG ltac:(lia)) as (_ & _ & _ & _ & _ & TAIL & JU & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEN & AU0 & AUM & MUF & MUM).
pose proof (class_size_facts c Hc) as [S1 S2].
pose proof (rl_prim a LB0 FS0 G RE X GC) as (AL16 & KP & _).
pose proof (region_in_prim RE c Hc) as (R1 & _ & _ & R4).
pose proof (reg_beg_align RE X c (gc_rlay a LB0 FS0 G RE X GC)) as (RB8 & _).
pose proof kconsts as (_ & KO & _ & _ & _ & _ & KU & _).
set (rb := reg_beg L c) in *. set (sz := class_size c) in *.
set (au := c_alloc_user (cls a c)) in *. set (mu := c_mapped_user (cls a c)) in *.
assert (SZ8 : sz mod 8 = 0) by (clear - S2; Z.div_mod_to_equations; lia).
assert (AU8 : exists k, au = 8 * k).
{ exists (Z.of_nat (length (G c)) * (sz / 8)). rewrite <- LEN.
transitivity (Z.of_nat (length (G c)) * (8 * (sz / 8))); [f_equal; clear - SZ8; Z.div_mod_to_equations; lia| ring]. }
assert (MU8 : exists k, mu = 8 * k).
{ exists (mu / 8). rewrite KU in MUM. clear - MUM. Z.div_mod_to_equations. lia. }
destruct AU8 as (ka & Hka). destruct MU8 as (km & Hkm).
destruct (Z_lt_le_dec y (rb + au)) as [LT|GE].
-
set (i := (y - rb) / sz).
assert (Hi : 0 <= i /\ rb + i * sz <= y < rb + i * sz + sz) by (subst i; clear - Hy S1; Z.div_mod_to_equations; nia).
assert (IL : i < Z.of_nat (length (G c))) by (subst i; clear - Hy LT S1 LEN; Z.div_mod_to_equations; nia).
destruct (nth_error (G c) (Z.to_nat i)) as [t|] eqn:E; [| apply nth_error_None in E; lia].
assert (Ht : tag_at G c i = Some t) by (unfold tag_at; destruct (Z.ltb_spec i 0); [lia| exact E]).
pose proof (slot_shadow c i t Ht) as (_ & _ & J). unfold slot_beg in J. fold rb sz in J.
assert (P8 : exists k, i * sz = 8 * k).
{ exists (i * (sz / 8)). transitivity (i * (8 * (sz / 8))); [f_equal; clear - SZ8; Z.div_mod_to_equations; lia| ring]. }
destruct P8 as (k & Pk). rewrite Pk in J, Hi.
apply J. rewrite !SH_eq. clear - Hi Y8 RB8 S1 S2 Pk. Z.div_mod_to_equations. lia.
- destruct (Z_lt_le_dec y (rb + mu)) as [LT2|GE2].
+
assert (KS : KHI <= rb + au) by lia.
pose proof (cells_hjunk_sh _ _ TAIL KS) as (_ & _ & J). cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia.
apply J. rewrite !SH_eq. rewrite Hka, Hkm in *. clear - LT2 GE Y8 RB8. Z.div_mod_to_equations. lia.
+
destruct JU as (_ & _ & J). apply J. rewrite !SH_eq. rewrite Hkm, KO in *. clear - GE2 Hy Y8 RB8. Z.div_mod_to_equations. lia.
Qed.

Lemma block_byte_nbhd : forall p A n0 x, In (p, A, n0) LB0 -> A <= x < A + n0 ->
hjunk m (8 * (SH x / 8)) (8 * (SH x / 8) + 8).
Proof.
intros p A n0 x Hin Hx.
pose proof (rl_prim a LB0 FS0 G RE X GC) as (AL16 & KP & _). pose proof kconsts as (_ & KO & _ & _ & KPG & _ & KU & _).
destruct (live_block_geom a LB0 FS0 G RE X GC p A n0 Hin) as (Hn & A16 & [(c & i & Ht & Hc & Hp & HA & CT)|(e & He & Hp & Hr & HA & CT)]);
unfold blk_container in CT.
- pose proof (slot_prim a LB0 FS0 G RE X GC c i _ Ht) as (P1 & P2 & P8 & P16 & Hcc & R1 & R2 & S32 & SM).
pose proof (region_in_prim RE c Hcc) as (Q1 & _ & _ & Q4).
eapply (shword_hjunk (reg_beg L c) (reg_beg L c + kFreeArrayOffset)).
+ rewrite Q4. rewrite ?KHI_eq in KP. Z.div_mod_to_equations. lia.
+ rewrite Q4, KO. Z.div_mod_to_equations. lia.
+ rewrite ?KHI_eq in KP. lia.
+ pose proof (region_in_prim RE c Hcc) as (_ & Q2 & Q3 & _). pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & _ & PH & _).
unfold prim_hi in PH. unfold prim_lo in *. pose proof kconsts as (_ & _ & KS & _). lia.
+ lia.
+ apply region_shadow. exact Hcc.
- pose proof (sec_entry_facts a LB0 FS0 G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M2.
pose proof (proj1 RCH _ _ _ Hin) as CR. rewrite Hp in CR. cbn [chunk_rep] in CR. destruct CR as (_ & Hin2 & _ & CM).
rewrite <- Hr, <- E4 in CM.
eapply (shword_hjunk (se_beg e + kPage) (se_beg e + se_size e)).
+ rewrite KPG. Z.div_mod_to_equations. lia.
+ Z.div_mod_to_equations. lia.
+ rewrite KPG. lia.
+ lia.
+ lia.
+ apply shsome_of_hjunk; [rewrite KPG; Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia|].
pose proof (chunk_mem_shadow _ _ _ _ CM) as J.
replace (SH (se_beg e + kPage) + (se_beg e + se_size e - (se_beg e + kPage)) / 8) with (SH (se_beg e + se_size e)) in J; [exact J|].
rewrite !SH_eq, KPG. Z.div_mod_to_equations. lia.
Qed.

Lemma frame_byte_nbhd : forall c f x, In (c, f) FS0 -> f <= x < f + ff_size c ->
hjunk m (8 * (SH x / 8)) (8 * (SH x / 8) + 8).
Proof.
intros c f x Hin Hx.
destruct RF as (AL & K1 & K2 & SHP & _ & _ & _ & _ & _ & _ & J).
destruct SHP as [SHf _]. destruct (SHf _ Hin) as (Hc & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc, Hp, Ef.
pose proof (fs_frame_in_area (ae_fs_base RE) c pos Hc Hp) as [F1 F2]. rewrite <- Ef in F1, F2.
unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in *.
eapply (shword_hjunk (ae_fs_base RE + 0x9000) (ae_fs_base RE + 0xb09000)).
- Z.div_mod_to_equations. lia.
- Z.div_mod_to_equations. lia.
- lia.
- lia.
- lia.
- apply shsome_of_hjunk; [Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| exact J].
Qed.

Lemma amemset_nbhd : forall dst n, amemset_whereA LB0 FS0 dst n -> 0 < n ->
hjunk m (8 * (SH dst / 8)) (8 * (SH dst / 8) + 8)
/\ hjunk m (8 * (SH (dst + n - 1) / 8)) (8 * (SH (dst + n - 1) / 8) + 8).
Proof.
intros dst n [(p & A & n0 & Hin & H1 & H2)|(c & f & Hin & H1 & H2)] Hn.
- split; eapply (block_byte_nbhd p A n0); try exact Hin; lia.
- split; eapply (frame_byte_nbhd c f); try exact Hin; lia.
Qed.

End S.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QDM6.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QUxU QNwL QYnC QSsj QNQk.Mq4.
Import Qu1d.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition get_current_thread_entry : Z := 0x6d2e0.
Definition get_thread_stats_entry : Z := 0x6c4ac.

Section Thread.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma get_current_thread_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (rl_T X) /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_current_thread_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
rtc RT 3%nat K3. rtc RT 4%nat K4. rtc RT 28%nat K28. rtc RT 29%nat K29. pose proof (RT_ctx_thread _ _ _ RT) as CT.
pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & CLO & CHI & _). cbn [fst snd] in CLO, CHI. idtac. rewrite ?KHI_eq in CLO.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TLO & THI & _). cbn [fst snd] in TLO, THI. idtac. rewrite ?KHI_eq in TLO.
unfold get_current_thread_entry, A_TP, A_TLS_TSD, A_TSD_MAIN in *.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. step. stp. step. if_lit.
stp. step.
step. step. step. step. step. step. step.
step. unfold_cond. rewrite (unsigned_lit (rl_ctx X)) by lia. if_lit.
step.
step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor].
Qed.

Lemma get_thread_stats_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 32 ->
evt asegs (leafw_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (rl_T X + 2800) /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_thread_stats_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TLO & THI & _). cbn [fst snd] in TLO, THI. idtac. rewrite ?KHI_eq in TLO.
unfold get_thread_stats_entry.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
call_sp (get_current_thread_spec _ _); try eassumption.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
{ lia. }
subst. rename x14 into m1.
step. unfold_cond. rewrite (unsigned_lit (rl_T X)) by lia. if_lit.
step. step.
step. step. step.
release_frame FR PC (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [reflexivity|]. exact POST.
Qed.
End Thread.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj QNQk.Mq2.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition tls_fs_entry : Z := 0x553c0.
Definition tls_fs_stack : Z := 176.
Definition A_FS_TLSDESC : Z := 0x0e6bd8.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma tls_fs_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 176 ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 176, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz A_TP /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_FS_TLSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz tls_fs_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
unfold tls_fs_entry, tls_fs_stack, A_FS_TLSDESC, A_TP in *.
obj_facts RL.
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 176%nat ST.

step_until 0x553d8.

rt_now RT RL 0%nat K0. step_until 0. if_false. clear K0. step_until 0x553dc.

rt_now RT RL 36%nat K36. rt_now RT RL 34%nat K34. rt_now RT RL 38%nat K38. rt_now RT RL 39%nat K39.
step_until 0x553f0. clear K36 K34 K38 K39.
replace (wz (2 ^ 64 - 2048 + 6436448)) with (wz 6434400) by (apply bv_eq; vm_compute; reflexivity).
step_until 0. if_false.

rt_now RT RL 3%nat K3. step_until 0. if_false. clear K3.
rt_now RT RL 4%nat K4. rt_now RT RL 28%nat K28. unfold A_TSD_MAIN in K28. rt_now RT RL 29%nat K29.
step_until 0x6d2ec. clear K4 K28 K29. istep. if_false_u.
rt_ctx_now RT RL CT. step_until 0. clear CT. if_false_u.

rt_T_now RT RL TT. step_until 0x7ab08. clear TT.

step_until 0x7ab44.
rt_now RT RL 19%nat K19. step_until 0x7ab4c. clear K19.
rt_now RT RL 37%nat K37. step_until 0. clear K37. if_false_u.
rt_now RT RL 20%nat K20. step_until 0x7ab60. clear K20.
rt_now RT RL 34%nat K34. step_until 0x7ab64. clear K34.
rt_now RT RL 9%nat K9. step_until 0x7ab6c. clear K9.
rt_now RT RL 35%nat K35. step_until 0. clear K35. if_false_u.
rt_now RT RL 31%nat K31. step_until 0. clear K31. if_false_u.
istep. if_true_u. istep. if_false_u.
step_until 0. if_true_u.
rt_dtls_now RT RL DT. step_until 0. clear DT. if_false_u.

step_until 0x55420. step_until 0.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor].
Qed.

End Walk.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QsJM.
Import QlES.
Import ListNotations. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section Laws.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma RFake_releaseK : forall c0 FS0 m f (flag : word),
(forall f', In f' FS0 -> fframe_rangeA RE (ff_cls f') (ff_addr f')) ->
RFake FS0 RE X m -> In (c0, f) FS0 ->
bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
RFake (ffs_remove f FS0) RE X (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None
/\ fp_RFake FS0 RE X (bv_unsigned flag).
Proof.
intros c0 FS0 m f flag _ RF Hin Hrd. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL c0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.

assert (Eflag : flag = wz (fs_flag FS c0 pos)).
{ destruct SLOT as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
apply le8_inj. eapply bytes_at_det; [exact Hrd| exact BA| rewrite !length_le8; reflexivity]. }
subst flag.
pose proof (fs_flag_range FS c0 pos Hc0 Hp) as FR. pose proof (fs_foff_range c0 Hc0) as FO.
pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
assert (UF : bv_unsigned (wz (fs_flag FS c0 pos)) = fs_flag FS c0 pos) by (apply unsigned_lit; lia).
assert (EA : wz (fs_flag FS c0 pos) = wa (fs_flag FS c0 0 + pos)) by (unfold wa, fs_flag; f_equal; lia).
pose proof (fs_N_pos c0 Hc0) as N0.
split; [| split].
-
pose proof (wmono_write asegs m m (wz (fs_flag FS c0 pos)) [b8 0] (wmono_refl asegs m)) as WM.
rewrite EA in WM |- *.
assert (FRc : forall A cs, rw_cells asegs m A cs ->
A + Z.of_nat (cells_size cs) <= fs_flag FS c0 0 + pos \/ fs_flag FS c0 0 + pos + 1 <= A ->
rw_cells asegs (write_to_mem m (wa (fs_flag FS c0 0 + pos)) [b8 0]) A cs).
{ intros A cs H D. apply rw_cells_frame; [exact H| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia| cbn; lia]. }
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [apply fs_shape_remove; exact SHP|].
split. { apply ro_cells_frame; [exact SSL| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia]. }
split. { apply FRc; [exact GC| cbn; unfold fs_flag in *; lia]. }
split. { intros c Hc. destruct (HI c Hc) as [h H]. exists h. apply FRc; [exact H| cbn; unfold fs_hint, fs_flag, kFsClasses in *; lia]. }
split. { intros c Hc. destruct (Z.eq_dec c c0) as [->|Nc].
- rewrite (flags_of_clear_same RE FS0 c0 pos f SHP Hc0 Hp Ef). apply u8arr_write; [apply FL; exact Hc0| rewrite flags_of_length; lia].
- rewrite (flags_of_clear_other RE FS0 c0 f c SHP Hin ltac:(lia)). apply u8arr_frame; [apply FL; exact Hc| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia|].
rewrite flags_of_length. cbn [length]. pose proof (fs_N_pos c Hc).
destruct (Z.lt_ge_cases c c0).
+ pose proof (fs_foff_mono c c0 ltac:(lia) ltac:(lia) ltac:(exact (proj2 Hc0))). unfold fs_flag in *. lia.
+ pose proof (fs_foff_mono c0 c ltac:(lia) ltac:(lia) ltac:(exact (proj2 Hc))). unfold fs_flag in *. lia. }
split. { intros c p Hcp Hpp. apply ffs_remove_In in Hcp as [Hcp Hne]. cbn [ff_addr snd] in Hne.
pose proof (SL c p Hcp Hpp) as H. destruct (SHf _ Hcp) as (Hcc & _). cbn [ff_cls fst] in Hcc.
pose proof (fs_frame_in_area FS c p Hcc Hpp) as [A1 A2]. unfold fs_area_lo in A1.
assert (64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
apply FRc; [exact H| cbn; unfold fs_flag in *; lia]. }
split; (eapply hjunk_wmono; [| exact WM]); assumption.
-
destruct (FL c0 Hc0) as [_ WR]. rewrite flags_of_length in WR.
replace (wz (fs_flag FS c0 pos)) with (wa (fs_flag FS c0 0 + pos)) by (unfold wa, fs_flag; f_equal; lia).
apply WR. lia.
- rewrite UF. apply (fp_meta RE X FS0 _ SHP). lia.
Qed.

Lemma RFake_flagK : forall c0 FS0 m f, RFake FS0 RE X m -> In (c0, f) FS0 ->
exists flag : word, ro_cells asegs m (f + ff_size c0 - 8) [C8 flag] /\ FS + 0x1000 <= bv_unsigned flag < FS + 0x9000.
Proof.
intros c0 FS0 m f RF Hin. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL c0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.
pose proof (fs_flag_range FS c0 pos Hc0 Hp) as FR. pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
exists (wz (fs_flag FS c0 pos)). split; [exact (proj1 SLOT)|]. rewrite unsigned_lit by lia. exact FR.
Qed.

Lemma RFake_alignK : forall c0 FS0 m f, RFake FS0 RE X m -> In (c0, f) FS0 -> c0 <= 6 -> f mod ff_size c0 = 0.
Proof.
intros c0 FS0 m f RF Hin H6. pose proof RF as (AL & _ & _ & SHP & _).
destruct SHP as [SHf _]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
subst f. unfold fs_frame, ff_size.
assert (E : c0 = 0 \/ c0 = 1 \/ c0 = 2 \/ c0 = 3 \/ c0 = 4 \/ c0 = 5 \/ c0 = 6) by lia.
destruct E as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn; Z.div_mod_to_equations; lia.
Qed.

Lemma RFake_releaseK_range : forall c0 FS0 m f (flag : word),
RFake FS0 RE X m -> In (c0, f) FS0 ->
bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
FS + 0x1000 <= bv_unsigned flag < FS + 0x9000 /\ bv_unsigned flag + 1 <= band_lo.
Proof.
intros c0 FS0 m f flag RF Hin Hrd. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL c0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.
assert (Eflag : flag = wz (fs_flag FS c0 pos)).
{ destruct SLOT as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
apply le8_inj. eapply bytes_at_det; [exact Hrd| exact BA| rewrite !length_le8; reflexivity]. }
subst flag. pose proof (fs_flag_range FS c0 pos Hc0 Hp) as FR. pose proof (fs_foff_range c0 Hc0) as FO.
pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
rewrite unsigned_lit by (unfold fs_flag in *; lia). unfold fs_flag in *. idtac. lia.
Qed.

End Laws.

Section GconsFacts.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Local Notation FS := (ae_fs_base RE).

Lemma RFake_releaseK_pres : forall c0 m f (flag : word),
RFake FS0 RE X m -> In (c0, f) FS0 -> bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
aheap_presA asegs a_alayout LB0 FS0 band_lo m (write_to_mem m flag [Z_to_bv 8 0]).
Proof.
intros c0 m f flag RF Hin Hrd.
pose proof (RFake_releaseK_range RE X c0 FS0 m f flag RF Hin Hrd) as [FR CE].
pose proof RF as (AL & K1 & K2 & SHP & _). pose proof K1 as K1'. unfold A_FS_MAP_SIZE in K1'.
unfold aheap_presA.
assert (Ew : flag = wa (bv_unsigned flag)).
{ unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
rewrite Ew at 1. pose proof (bv_unsigned_in_range 64 flag) as FLR. change (bv_modulus 64) with (2^64) in FLR.
apply agree_on_write; [lia| cbn; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. intros x Hx.
assert (Ex : x = bv_unsigned flag) by lia. subst x. clear Hx.
intros [C|[C|[C|[C|[C|[C|C]]]]]].
- lia.
- cbn [ala_client_data a_alayout] in C. unfold a_client_data in C. lia.
- eapply (live_user_not_fs _ _ _ _ _ _ GC (bv_unsigned flag)); [exact C| unfold A_FS_MAP_SIZE; lia].
- pose proof (body_ge RE FS0 (bv_unsigned flag) SHP C). lia.
- destruct C as (g & Hg & Hs). destruct SHP as [SHf _]. destruct (SHf _ Hg) as (Hc & pos & Hp & Eg).
pose proof (fs_frame_in_area FS (ff_cls g) pos Hc Hp) as [B1 B2]. rewrite <- Eg in B1, B2.
unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2. idtac.
assert (SZ : 0 <= ff_size (ff_cls g)) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 (ff_cls g)); lia).
rewrite !SH_eq in Hs. Z.div_mod_to_equations. lia.
- rewrite SH_247, ?KHI_eq in C. pose proof SH_band. lia.
- rewrite !SH_eq in C. cbn [ala_img_lo a_alayout] in C. lia.
Qed.

End GconsFacts.

Section S.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRF : ac_RFake C = RFake.

Lemma ARUN_fframe_releaseK0 : forall c0 s LB FS RE m f (flag : word),
ARUN C s LB FS RE m -> In (c0, f) FS ->
bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
ARUN C s LB (ffs_remove f FS) RE (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None.
Proof.
intros c0 s LB FS RE m f flag AR Hf HB. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof R8 as R8r. rewrite HRF in R8r.
destruct (RFake_releaseK RE X c0 FS0 m f flag (gc_ff_range _ _ _ _ _ _ GC) R8r Hf0 HB) as (R8' & WV & FPF).
split; [|exact WV].
apply (ARUN_close C s LB (ffs_remove f FS) RE _ X G LB0 (ffs_remove f FS0)); [exact PB| apply Permutation_filter; exact PF|].
assert (GC' : gcons (ps_a s) LB0 (ffs_remove f FS0) G RE X).
{ eapply gcons_ff_sub; [exact GC|]. intros f' Hin. unfold ffs_remove in Hin.
apply (proj2 (list_elem_of_In _ _)) in Hin. apply (proj1 (list_elem_of_filter _ _ _)) in Hin.
destruct Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin. exact Hin. }

pose proof (bv_unsigned_in_range 64 flag) as FR. unfold bv_modulus in FR. change (2 ^ Z.of_N 64) with (2^64) in FR.
assert (AG : forall P : Z -> Prop, (forall x, P x -> czone LB0 RE x -> False) ->
agree_on asegs P m (write_to_mem m flag [Z_to_bv 8 0])).
{ intros P HP. rewrite <- (Z_to_bv_bv_unsigned flag); change (Z_to_bv 64 (bv_unsigned flag)) with (wa (bv_unsigned flag)). apply agree_on_write; cbn [length]; change (Z.of_nat 1) with 1; [lia| lia|].
intros x Hx Px. assert (x = bv_unsigned flag) as -> by lia.
apply (fp_RFake_zone RE X) in FPF.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CE & _); cbn [fst snd] in AL, K, CE.
apply (HP _ Px). unfold czone. destruct FPF as [FPF|FPF]; [do 3 right; left; exact FPF| do 4 right; left; exact FPF]. }
assert (WM : wmono asegs m (write_to_mem m flag [Z_to_bv 8 0])) by (apply wmono_write; apply wmono_refl).
split; [exact GC'|].
split; [eapply (ac_RTconst_frame C); [exact R1| exact WM| apply AG; intros x; apply (fp_RTconst_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RStats_frame C); [exact R2| exact WM| apply AG; intros x; apply (fp_RStats_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| apply AG; intros x; apply (fp_RPrim_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| apply AG; intros x; apply (fp_RChunks_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AG; intros x; apply (fp_RSec_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| apply AG; intros x; apply (fp_RQuar_cz _ _ _ _ _ _ GC)]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| apply AG; intros x; apply (fp_RDepot_cz _ _ _ _ _ _ GC)]|].
rewrite HRF. exact R8'.
Qed.

Lemma ARUN_fframe_releaseK : forall c0 s LB FS RE m f (flag : word),
ARUN C s LB FS RE m -> In (c0, f) FS -> bytes_at asegs m (f + ff_size c0 - 8) (le8 flag) ->
ARUN C s LB (ffs_remove f FS) RE (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None
/\ bv_unsigned flag + 1 <= band_lo
/\ aheap_presA asegs a_alayout LB FS band_lo m (write_to_mem m flag [Z_to_bv 8 0]).
Proof.
intros c0 s LB FS RE m f flag AR Hf HB.
destruct (ARUN_fframe_releaseK0 c0 s LB FS RE m f flag AR Hf HB) as [AR' WV]. split; [exact AR'|]. split; [exact WV|].
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
split; [exact (proj2 (RFake_releaseK_range RE X c0 FS0 m f flag R8 Hf0 HB))|].
pose proof (RFake_releaseK_pres (ps_a s) LB0 FS0 G RE X GC c0 m f flag R8 Hf0 HB) as AP.
unfold aheap_presA in *. eapply agree_on_mono; [exact AP|]. intros x. unfold aclient_addrA, in_ablock, in_fframe_body, in_fframe_shadow.
intros [H|[H|[H|[H|[H|[H|H]]]]]]; [left; exact H| right; left; exact H| | | | do 5 right; left; exact H| do 6 right; exact H].
- do 2 right; left. destruct H as (b & Hb & R). exists b. split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- do 3 right; left. destruct H as (ff & Hff & R). exists ff. split; [eapply Permutation_in; [exact PF| exact Hff]| exact R].
- do 4 right; left. destruct H as (ff & Hff & R). exists ff. split; [eapply Permutation_in; [exact PF| exact Hff]| exact R].
Qed.

Lemma ARUN_fframe_flagK : forall c0 s LB FS RE m f, ARUN C s LB FS RE m -> In (c0, f) FS ->
exists flag : word, ro_cells asegs m (f + ff_size c0 - 8) [C8 flag] /\ ae_fs_base RE + 0x1000 <= bv_unsigned flag < ae_fs_base RE + 0x9000.
Proof.
intros c0 s LB FS RE m f AR Hf. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
exact (RFake_flagK RE X c0 FS0 m f R8 Hf0).
Qed.

Lemma ARUN_fframe_align : forall c0 s LB FS RE m f, ARUN C s LB FS RE m -> In (c0, f) FS -> c0 <= 6 -> f mod ff_size c0 = 0.
Proof.
intros c0 s LB FS RE m f AR Hf H6. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & _ & _ & _ & _ & R8). rewrite HRF in R8.
assert (Hf0 : In (c0, f) FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
exact (RFake_alignK RE X c0 FS0 m f R8 Hf0 H6).
Qed.

Lemma ARUN_fs_block_disjoint : forall s LB FS RE m b, ARUN C s LB FS RE m -> In b LB ->
ablk_addr b + ablk_size b <= ae_fs_base RE \/ ae_fs_base RE + 0xb09000 <= ablk_addr b.
Proof.
intros s LB FS RE m [[p A] n] AR Hb. cbn [ablk_addr ablk_size fst snd]. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _). assert (Hb0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact Hb]).
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (_ & K & CE & DP & _). cbn [fst snd] in K, CE. unfold iv_disjoint in DP. cbn [fst snd] in DP.
destruct (live_block_geom _ _ _ _ _ _ GC p A n Hb0) as (Hn & AL & [(c & i & Ht & Hc & Hp & HA & CT)|(e & He & Hp & Hr & HA & CT)]); unfold blk_container in CT.
- pose proof (slot_prim _ _ _ _ _ _ GC c i _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in *. change (2 ^ 37) with 137438953472 in *. unfold A_FS_MAP_SIZE in *. lia.
- destruct (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & _ & _ & _ & _ & _ & F).
pose proof (proj1 (List.Forall_forall _ _) F _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D. unfold kPage, A_FS_MAP_SIZE in *. lia.
Qed.
End S.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Definition fp_cls (RE : aentry) (X : rlay) (c : Z) (z : Z) : Prop :=
(ri_addr RE c <= z < ri_addr RE c + 128)
\/ (pc_addr X c <= z < pc_addr X c + 80)
\/ (fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize)
\/ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) z
\/ (reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset)
\/ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z.

Section Geom.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Hypothesis RL : rlay_ok RE X.

Lemma reg_geom : forall c, 0 <= c < 32 ->
reg_beg (ae_L RE) c = prim_lo RE + c * 4294967296 /\ fa_beg (ae_L RE) c = prim_lo RE + c * 4294967296 + 3758096384
/\ prim_lo RE mod 65536 = 0 /\ 17594333495296 <= prim_lo RE /\ prim_hi RE <= band_lo /\ prim_hi RE = prim_lo RE + 137438957568
/\ region_info RE = prim_lo RE + 137438953472.
Proof.
intros c Hc. pose proof (rlay_prim_facts RE X RL) as (P0 & P1 & P2 & _).
idtac. rewrite ?KHI_eq in P1.
unfold fa_beg, reg_beg, prim_lo, prim_hi, region_info in *. pose proof kconsts as (KR & KO & _). rewrite KR, KO.
change (2^32) with 4294967296. change (2^37) with 137438953472 in *.
repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma fp_cls_lt_ceil : forall c z, 0 <= c < 32 -> fp_cls RE X c z -> z < band_lo.
Proof.
intros c z Hc F. pose proof (reg_geom c Hc) as (RB & FB & AL & PK & PC & PH & RI).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & _ & TB & _). cbn [fst snd] in TB.
pose proof kconsts as (KR & KO & KS & _).
rewrite ?KHI_eq in *. unfold fp_cls, ri_addr, pc_addr, in_sh in F. cbn [fst snd] in F. rewrite ?RB, ?FB, ?RI, ?KO, ?KS in F.
unfold SH in F.
destruct F as [F|[F|[F|[F|[F|F]]]]]; try lia.
all: unfold A_SHADOW_OFS in F; Z.div_mod_to_equations; lia.
Qed.

Lemma fp_cls_not_stats : forall c z, 0 <= c < 32 -> fp_cls RE X c z -> ~ (rl_T X + 2768 <= z < rl_T X + 3168).
Proof.
intros c z Hc F. pose proof (reg_geom c Hc) as (RB & FB & AL & PK & PC & PH & RI).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof kconsts as (KR & KO & KS & _).
rewrite ?KHI_eq in *. unfold fp_cls, ri_addr, pc_addr, in_sh in F. cbn [fst snd] in F. rewrite ?RB, ?FB, ?RI, ?KO, ?KS in F.
unfold SH, A_SHADOW_OFS in F. unfold prim_lo in *.
destruct F as [F|[F|[F|[F|[F|F]]]]]; Z.div_mod_to_equations; (first [ clear - H q TD TK PK AL r F Hc z c X RE BAND H9 q1 H5 H4 r0 H0 PH PC r1 q0; lia | lia ]).
Qed.

Lemma fp_cls_sep : forall c c' z, 0 <= c < 32 -> 0 <= c' < 32 -> c <> c' -> fp_cls RE X c z -> fp_cls RE X c' z -> False.
Proof.
intros c c' z Hc Hc' NE F F'.
pose proof (reg_geom c Hc) as (RB & FB & AL & PK & PC & PH & RI). pose proof (reg_geom c' Hc') as (RB' & FB' & _).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD; cbn [fst snd] in TD.
pose proof kconsts as (KR & KO & KS & _).
rewrite ?KHI_eq in *. unfold fp_cls, ri_addr, pc_addr, in_sh in F, F'. cbn [fst snd] in F, F'.
rewrite ?RB, ?FB, ?RI, ?KO, ?KS in F. rewrite ?RB', ?FB', ?RI, ?KO, ?KS in F'.
unfold SH, A_SHADOW_OFS in F, F'. unfold prim_lo in *.
assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia;
destruct F as [F|[F|[F|[F|[F|F]]]]]; destruct F' as [F'|[F'|[F'|[F'|[F'|F']]]]]; Z.div_mod_to_equations; (first [ clear - H q D TK PK AL r F' F NE z c' c X RE BAND TD Hc' Hc H9 q1 H5 H4 r0 H0 r1 q0 PH PC H14 q2 H10 r2 H19 q3 H15 r3; nia | nia ]).
Qed.
End Geom.

Lemma crep_slot_geom : forall a G RE X m c K i t,
class_rep a G RE X m c K -> 1 <= c <= 31 -> tag_at G c i = Some t ->
0 <= i /\ (i + 1) * class_size c <= c_alloc_user (cls a c)
/\ 32 <= class_size c /\ class_size c mod 32 = 0
/\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c
/\ c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset
/\ exists k, 0 <= k /\ i * class_size c = 8 * k /\ class_size c = 8 * (class_size c / 8).
Proof.
intros a G RE X m c K i t (_ & PU & _) Hc Ht. pose proof (tag_at_lt G c i t Ht) as [I1 I2].
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5).
pose proof (class_size_facts c Hc) as [S1 S2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; lia).
split; [lia|]. split; [(first [ clear - E8 S2 S1 I2 I1 G5 G3 G2 G1 i c G a; nia | nia ])|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
exists (i * (class_size c / 8)). split; [(first [ clear - E8 S2 S1 I2 I1 G5 G3 G2 G1 i c G a; nia | nia ])|]. split; [(first [ clear - E8 S1 i c G a; nia | nia ])| exact E8].
Qed.

Section ClassFrame.
Variables (a : AState) (G : ghost) (RE : aentry) (X : rlay).

Lemma class_rep_agree : forall m m' c K,
class_rep a G RE X m c K -> 0 <= c < 32 -> agree_on asegs (fp_cls RE X c) m m' -> class_rep a G RE X m' c K.
Proof.
intros m m' c K HC Hc AG. pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof HC as (((j1 & j2 & j3 & j4 & RI) & PC & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _). rewrite KM in G5.
split; [split; [|split]|split].
- exists j1, j2, j3, j4. eapply rw_cells_agree; [exact AG| exact RI|]. intros z Hz. left. cbn [ri_cells cells_size csize Nat.add] in Hz. lia.
- eapply rw_cells_agree; [exact AG| exact PC|]. intros z Hz. right; left. cbn [pc_cells cells_size csize Nat.add] in Hz. lia.
- exists CH. split; [|split; [exact LCH| exact HCH]]. eapply u32arr_agree; [exact AG| exact ACH|]. intros z Hz. right; left. rewrite LCH in Hz. cbn in Hz. lia.
- exact PU.
- intros Hc1. specialize (REG Hc1). destruct REG as (FA & FJ & SL & UT & SS & US & UJ & FS).
assert (HCL : 1 <= c <= 31) by lia. pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (INFA : forall z, fa_beg (ae_L RE) c <= z < fa_beg (ae_L RE) c + kFreeArraySize -> fp_cls RE X c z) by (intros z Hz; do 2 right; left; exact Hz).
assert (INFS : forall z, SH (fa_beg (ae_L RE) c) <= z < SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8 -> fp_cls RE X c z).
{ intros z Hz. do 3 right; left. split; cbn [fst snd]; lia. }
assert (INU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset -> fp_cls RE X c z) by (intros z Hz; do 4 right; left; exact Hz).
assert (INUS : forall z, SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8 -> fp_cls RE X c z).
{ intros z Hz. do 5 right. split; cbn [fst snd]; lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (KS8 : kFreeArraySize = 8 * 67108864) by (rewrite KS; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KO8 SZ1 G3 G2 G1 LCH CH K c G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H31 H30 H24 q4 H19 q3 H5 H4 r0 H0 H r KO8 q0 SZ2 r3 SZ1 G5 r4 G4 G3 G2 G1 P14 r5 q LCH CH K c G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H36 H35 H29 q5 H0 H r q G5 r5 P14 r6 LCH CH K c G a; lia | lia ])).
destruct MU8 as (qm & QM).
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
+ eapply u32arr_agree; [exact AG| exact FA|]. intros z Hz. rewrite map_length in Hz. apply INFA. lia.
+ eapply hjunk_agree; [exact AG| exact FJ|]. intros z Hz. apply INFA. lia.
+ intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (crep_slot_geom a G RE X m c K i t HC HCL Ht) as (I1 & IL & _ & _ & SB & B1 & B2 & _). rewrite SB in Hz.
apply INU. clear - Hz I1 IL B1 B2 SZ1. nia.
+ eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply INU. lia.
+ intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (crep_slot_geom a G RE X m c K i t HC HCL Ht) as (I1 & IL & _ & _ & SB & B1 & B2 & k & K0 & K1 & K2).
rewrite SB, K1, SH_plus8 in Hz. apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia.
clear - Hz I1 IL B1 B2 SZ1 K0 K1 K2 KO8. nia.
+ eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
+ eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G2 G3 G4 KO8 QA QA0; lia.
+ eapply hjunk_agree; [exact AG| exact FS|]. intros z Hz. rewrite KS8, SH_plus8 in Hz. apply INFS. rewrite KS8, Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma class_rep_ext : forall a' G' m c K,
class_rep a G RE X m c K -> cls a' c = cls a c -> as_cache_inited a' = as_cache_inited a -> G' c = G c ->
class_rep a' G' RE X m c K.
Proof.
intros a' G' m c K HC EC EI EG.
assert (TG : forall i, tag_at G' c i = tag_at G c i) by (intros i; unfold tag_at; rewrite EG; reflexivity).
unfold class_rep, cr_cells, cr_pure, cr_region in *. rewrite EC, EI, EG. setoid_rewrite TG. exact HC.
Qed.
End ClassFrame.

Lemma RPrim_open : forall a G RE X m, RPrim a G RE X m ->
exists K : Z -> pcls, hjunk m (rl_T X + 2768) (rl_T X + 2800)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses)
/\ forall c, 0 <= c < kNumClasses -> class_rep a G RE X m c (K c).
Proof. intros a G RE X m H. exact H. Qed.

Definition wc_ok {BAND : Band} (RE : aentry) (X : rlay) (c : Z) (iv : Z * Z) : Prop :=
let '(lo, hi) := iv in
band_lo <= lo
\/ (rl_T X + 2768 <= lo /\ hi <= rl_T X + 3168)
\/ (forall z, lo <= z < hi -> fp_cls RE X c z).

Lemma agree_other_classes {BAND : Band} : forall RE X c W m m',
rlay_ok RE X -> 0 <= c < 32 -> munch W m m' -> wmono asegs m m' -> Forall (wc_ok RE X c) W ->
forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m'.
Proof.
intros RE X c W m m' RL Hc MU WM FW c0 Hc0 NE. pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hc0.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as WC. cbn [wc_ok] in WC.
destruct WC as [WC|[WC|WC]].
- pose proof (fp_cls_lt_ceil RE X RL c0 x Hc0 Fx). lia.
- pose proof (fp_cls_not_stats RE X RL c0 x Hc0 Fx). lia.
- exact (fp_cls_sep RE X RL c0 c x Hc0 Hc (fun E => NE E) Fx (WC x (conj H1 H2))).
Qed.

Definition cr_user (a : AState) (G : ghost) (RE : aentry) (m : mem) (c : Z) : Prop :=
let x := cls a c in let sz := class_size c in let rb := reg_beg (ae_L RE) c in
(forall i t, tag_at G c i = Some t -> tag_prim t = true -> hjunk m (slot_beg RE c i) (slot_beg RE c i + sz))
/\ hjunk m (rb + c_alloc_user x) (rb + c_mapped_user x)
/\ (forall i t, tag_at G c i = Some t -> tag_prim t = true ->
rw_cells asegs m (SH (slot_beg RE c i)) [CB (Z.to_nat (sz / 8)) (repeat fa_byte (Z.to_nat (sz / 8)))])
/\ rw_cells asegs m (SH (rb + c_alloc_user x))
[CB (Z.to_nat ((c_mapped_user x - c_alloc_user x) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user x - c_alloc_user x) / 8)))]
/\ hjunk m (SH (rb + c_mapped_user x)) (SH (rb + kFreeArrayOffset)).

Definition uzone (RE : aentry) (c : Z) (z : Z) : Prop :=
(reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset) \/ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) z.

Lemma class_rep_split : forall a G RE X m c K,
class_rep a G RE X m c K <->
cr_cells a RE X m c K /\ cr_pure a G c K /\
(1 <= c -> u32arr asegs m (fa_beg (ae_L RE) c) (map (fun i => Z_to_bv 64 (coff c i)) (pk_fl K))
/\ hjunk m (fa_beg (ae_L RE) c + 4 * c_num_freed (cls a c)) (fa_beg (ae_L RE) c + c_mapped_fa (cls a c))
/\ cr_user a G RE m c
/\ hjunk m (SH (fa_beg (ae_L RE) c)) (SH (fa_beg (ae_L RE) c + kFreeArraySize))).
Proof.
intros a G RE X m c K. unfold class_rep, cr_region, cr_user. split.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
- intros (A & B & C). split; [exact A|]. split; [exact B|]. intros Hc. specialize (C Hc). tauto.
Qed.

Lemma cr_user_agree : forall a G RE m m' c K,
cr_pure a G c K -> cr_user a G RE m c -> 1 <= c <= 31 -> agree_on asegs (uzone RE c) m m' -> cr_user a G RE m' c.
Proof.
intros a G RE m m' c K PU HU HCL AG. unfold cr_user in HU. destruct HU as (SL & UT & SS & US & UJ). pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _). rewrite KM in G5.
pose proof (class_size_facts c HCL) as [SZ1 SZ2].
assert (INU : forall z, reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + kFreeArrayOffset -> uzone RE c z) by (intros z Hz; left; exact Hz).
assert (INUS : forall z, SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8 -> uzone RE c z).
{ intros z Hz. right. split; cbn [fst snd]; lia. }
assert (KO8 : kFreeArrayOffset = 8 * 469762048) by (rewrite KO; reflexivity).
assert (AU8 : exists q, 0 <= q /\ c_alloc_user (cls a c) = 8 * q).
{ exists (Z.of_nat (length (G c)) * (class_size c / 8)). split; [(first [ clear - KO8 SZ1 G3 G2 G1 K c G a; nia | nia ])|]. rewrite <- G1. Z.div_mod_to_equations. (first [ clear - H26 H25 H19 q3 H14 q2 H5 H4 r0 H0 H r KO8 q0 SZ2 r2 SZ1 G5 r3 G4 G3 G2 G1 P14 r4 q K c G a; nia | nia ]). }
destruct AU8 as (qa & QA0 & QA).
assert (MU8 : exists q, c_mapped_user (cls a c) = 8 * q) by (exists (c_mapped_user (cls a c) / 8); Z.div_mod_to_equations; (first [ clear - H31 H30 H24 q4 H0 H r q G5 r4 P14 r5 K c G a; lia | lia ])).
destruct MU8 as (qm & QM).
assert (GEOM : forall i t, tag_at G c i = Some t ->
0 <= i /\ (i + 1) * class_size c <= c_alloc_user (cls a c)
/\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c
/\ exists k, 0 <= k /\ i * class_size c = 8 * k /\ class_size c = 8 * (class_size c / 8)).
{ intros i t Ht. pose proof (tag_at_lt G c i t Ht) as [I1 I2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; (first [ clear - H26 H25 H14 q2 H0 H r SZ2 r2 P14 r4 q K c G; lia | lia ])).
split; [lia|]. split; [(first [ clear - E8 I2 i QM qm KO8 SZ2 SZ1 G5 G4 G3 G2 G1 P14 P12 P1 K c G a; nia | nia ])|]. split; [reflexivity|]. exists (i * (class_size c / 8)). split; [(first [ clear - E8 I1 i QM qm KO8 SZ2 SZ1 G5 G4 G3 G2 G1 P14 K c G a; nia | nia ])|]. split; [(first [ clear - E8 i SZ1 G3 K c G a; nia | nia ])| exact E8]. }
split; [|split; [|split; [|split]]].
- intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (GEOM i t Ht) as (I1 & IL & SB & _). rewrite SB in Hz. apply INU. clear - Hz I1 IL G3 G4 SZ1. nia.
- eapply hjunk_agree; [exact AG| exact UT|]. intros z Hz. apply INU. lia.
- intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (GEOM i t Ht) as (I1 & IL & SB & k & K0 & K1 & K2).
rewrite SB, K1, SH_plus8 in Hz. apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia.
clear - Hz I1 IL G3 G4 SZ1 K0 K1 K2 KO8. nia.
- eapply rw_cells_agree; [exact AG| exact US|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (Z.div_mod_to_equations; lia).
rewrite QA, QM in Hz. replace (8 * qm - 8 * qa) with (8 * (qm - qa)) in Hz by lia.
rewrite SH_plus8 in Hz. rewrite (Z.mul_comm 8 (qm - qa)), Z.div_mul in Hz by lia.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QA0 QA QM G3 G4 KO8; lia.
- eapply hjunk_agree; [exact AG| exact UJ|]. intros z Hz. rewrite QM, KO8, !SH_plus8 in Hz.
apply INUS. rewrite KO8, Z.mul_comm, Z.div_mul by lia. clear - Hz QM G2 G3 G4 KO8 QA QA0; lia.
Qed.

Lemma cr_user_ext : forall a a' G RE m c,
cr_user a G RE m c -> c_alloc_user (cls a' c) = c_alloc_user (cls a c) -> c_mapped_user (cls a' c) = c_mapped_user (cls a c) ->
cr_user a' G RE m c.
Proof. intros a a' G RE m c H E1 E2. unfold cr_user in *. rewrite E1, E2. exact H. Qed.

Lemma uzone_bounds {BAND : Band} : forall RE X c z, rlay_ok RE X -> 0 <= c < 32 -> uzone RE c z ->
(reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + 3758096384)
\/ (SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + 469762048).
Proof.
intros RE X c z RL Hc U. pose proof kconsts as (KR & KO & _). unfold uzone, in_sh in U. cbn [fst snd] in U. rewrite KO in U.
change (3758096384 / 8) with 469762048 in U. exact U.
Qed.

Lemma fp_RPrim_lt_ceil {BAND : Band} : forall G RE X x, rlay_ok RE X -> fp_RPrim G RE X x -> x < band_lo.
Proof.
intros G RE X x RL F. pose proof (rlay_prim_facts RE X RL) as (P0 & P1 & P2 & _).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof kconsts as (KR & KO & KS & K32 & _).
rewrite ?KHI_eq in *. unfold prim_lo, prim_hi, region_info in *.
destruct F as [F|[F|[F|[F|[[F _]|[F _]]]]]].
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. unfold region_info in *. lia.
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. lia.
- destruct F as (c & Hc & F1 & F2). unfold fa_beg, reg_beg in *. rewrite KR, KO, KS, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold fa_beg, reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, KS, K32 in *.
Z.div_mod_to_equations. nia.
- destruct F as (c & Hc & F1 & F2). unfold reg_beg in *. rewrite KR, KO, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, K32 in *.
Z.div_mod_to_equations. nia.
Qed.

Lemma RPrim_stack {BAND : Band} : forall a G RE X m m' W,
RPrim a G RE X m -> rlay_ok RE X -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> RPrim a G RE X m'.
Proof.
intros a G RE X m m' W RP RL MU WM FW. eapply RPrim_frame; [exact RP| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx Hx. apply outside_intro.
intros lo hi Hin [H1 H2]. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as C. cbn [fst] in C.
pose proof (fp_RPrim_lt_ceil G RE X x RL Fx). lia.
Qed.

Lemma rw_cells_CB_app : forall m A n1 l1 n2 l2,
rw_cells asegs m A [CB n1 l1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 l2] ->
rw_cells asegs m A [CB (n1 + n2) (l1 ++ l2)].
Proof.
intros m A n1 l1 n2 l2 H1 H2.
assert (H : rw_cells asegs m A ([CB n1 l1] ++ [CB n2 l2])).
{ apply (proj2 (rw_cells_app asegs m A [CB n1 l1] [CB n2 l2])). cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; assumption. }
destruct H1 as [[[L1 _] _] _]. destruct H2 as [[[L2 _] _] _]. cbn in L1, L2.
eapply rw_cells_recast'; [exact H| cbn; rewrite length_app; lia| cbn; rewrite !app_nil_r; reflexivity].
Qed.

Lemma rw_cells_CB_split : forall m A n1 n2 l,
rw_cells asegs m A [CB (n1 + n2) l] ->
rw_cells asegs m A [CB n1 (firstn n1 l)] /\ rw_cells asegs m (A + Z.of_nat n1) [CB n2 (skipn n1 l)].
Proof.
intros m A n1 n2 l H. assert (L : length l = (n1 + n2)%nat) by (destruct H as [[[L _] _] _]; cbn in L; lia).
assert (H' : rw_cells asegs m A ([CB n1 (firstn n1 l)] ++ [CB n2 (skipn n1 l)])).
{ eapply rw_cells_recast'; [exact H| cbn; rewrite length_take, length_drop; lia| cbn; rewrite !app_nil_r; apply firstn_skipn]. }
apply (proj1 (rw_cells_app asegs m A _ _)) in H'. cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QWRO QFQR QmP7 QKBN QNQk.Mq6.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma st_avoid_offhull : forall lo hi, (hi <= 0x10000 \/ 0x647000 <= lo) -> st_avoid (lo, hi).
Proof. intros lo hi H x [Hx1 Hx2] K; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.

Lemma st_avoid_T {BAND : Band} : forall RE X lo hi, rlay_ok RE X -> rl_T X <= lo -> hi <= rl_T X + 0x1000 -> st_avoid (lo, hi).
Proof.
intros RE X lo hi RL H1 H2. apply st_avoid_offhull.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & [_ TH] & _). cbn [fst snd] in TH. lia.
Qed.

Ltac st_avoid_solve :=
lazymatch goal with
| |- st_avoid (?lo, _) =>
lazymatch lo with
| context [rl_T _] => eapply st_avoid_T; [eassumption| cbn [fst snd]; lia| cbn [fst snd]; lia]
| _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; unfold prim_lo, prim_hi in *; lia
end
| |- _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; unfold prim_lo, prim_hi in *; lia
end.

Definition zsel (P : bool) : Z := Z.b2z P.
Arguments zsel : simpl never.
Lemma or_le_lia : forall a b c d, a <= b \/ c <= d -> a - b <= 2^66 -> c - d <= 2^66 ->
0 <= zsel (a <=? b) <= 1 /\ a <= b + (1 - zsel (a <=? b)) * 2^66 /\ c <= d + zsel (a <=? b) * 2^66.
Proof.
intros a b c d H B1 B2. unfold zsel. destruct (Z.leb_spec a b) as [L|L]; cbn [Z.b2z]; lia.
Qed.
Ltac encode_or H := apply or_le_lia in H; [| lia| lia].
End Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1 QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8.
Import QlES. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition run_free_hooks_entry : Z := 0x7205c.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma run_free_hooks_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 32 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz run_free_hooks_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. idtac. rtc RT 41%nat K41. unfold run_free_hooks_entry.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
do 5 step.
step. step. step.
step. if_lit.
step. step. step.
step. step. step.
step. if_lit.
do 5 step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; idtac; lia| constructor].
Qed.
End S.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition mem_to_shadow_entry : Z := 0x4b008.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma mem_to_shadow_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
RTconst RE X m -> mem_inv asegs m -> (0 <= p <= 0x7fff7fff \/ KHI <= p < 2^47) ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz mem_to_shadow_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros RT MI HP. rewrite ?KHI_eq in HP. unfold mem_to_shadow_entry.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1.
destruct HP as [HP|HP].
-
step_until 0. if_true_u. step_until 0.
apply evt_done; unfold leaf_post; do 15 eexists; split; [reflexivity|]. f_equal. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. change (2 ^ 3) with 8. lia.
- step_until 0. if_false_u. step_until 0. if_true_u. step_until 0. if_false_u. step_until 0. if_false_u. step_until 0.
apply evt_done; unfold leaf_post; do 15 eexists; split; [reflexivity|]. f_equal. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. change (2 ^ 3) with 8. lia.
Qed.
End Walk.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition m2s_entry : Z := 0x650f8.
Definition miz_entry : Z := 0x75878.
Definition rip_entry : Z := 0x65584.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma m2s_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
RTconst RE X m -> rlay_ok RE X -> KHI <= p -> p < 2^47 ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz m2s_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros RT RL K1p K2p. rewrite ?KHI_eq in K1p. idtac. unfold m2s_entry.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
step. step. step. step. step. step.
stp. step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia.
Qed.

Lemma m2s_spec_low : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
RTconst RE X m -> rlay_ok RE X -> 0 <= p -> p <= 0x7fff7fff ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz m2s_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros RT RL K1p K2p. rewrite ?KHI_eq in K1p. idtac. unfold m2s_entry.
rtc RT 19%nat K19. rtc RT 5%nat K5. rtc RT 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia.
Qed.

Definition zrd (m : mem) (A n : Z) : Prop := forall i, 0 <= i < n -> bytes_at asegs m (A + i) [b8 0].

Lemma zrd_ro1 : forall m A n a, zrd m A n -> A <= a -> a + 1 <= A + n -> ro_cells asegs m a [C1 (b8 0)].
Proof.
intros m A n a ZR H1 H2. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
replace a with (A + (a - A)) by lia. apply ZR. lia.
Qed.

Lemma zrd_bytes : forall m A n k j, zrd m A n -> A <= j -> j + Z.of_nat k <= A + n -> (0 < k)%nat ->
bytes_at asegs m j (repeat (b8 0) k).
Proof.
intros m A n k. induction k as [|k IH]; intros j ZR Hj Hk Hp; [lia|].
cbn [repeat]. change (b8 0 :: repeat (b8 0) k) with ([b8 0] ++ repeat (b8 0) k). apply (proj2 (bytes_at_app _ _ _ _ _)).
split; [replace j with (A + (j - A)) by lia; apply ZR; lia|].
replace (j + Z.of_nat (length [b8 0])) with (j + 1) by (cbn; lia).
destruct k as [|k'].
-
pose proof (ZR (j - A) ltac:(lia)) as (B1 & B2 & _). cbn in B2. replace (A + (j - A)) with j in * by lia.
split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
- apply IH; [exact ZR| lia| lia| lia].
Qed.

Lemma zrd_ro8 : forall m A n a, zrd m A n -> A <= a -> a + 8 <= A + n -> ro_cells asegs m a [C8 (wz 0)].
Proof.
intros m A n a ZR H1 H2. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
change (le8 (wz 0)) with (repeat (b8 0) 8). eapply zrd_bytes; [exact ZR| lia| cbn; lia| lia].
Qed.

Lemma zrd_munch : forall m m' A n W, zrd m A n -> munch W m m' -> wmono asegs m m' ->
(forall x, A <= x < A + n -> outside W x) -> zrd m' A n.
Proof.
intros m m' A n W ZR MU WM HO i Hi. eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM|]| apply ZR; exact Hi|].
- intros x Hx _. exact (HO x Hx).
- intros a Ha. cbn in Ha |- *. lia.
Qed.

Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma miz_bloop : forall k (c : Z) ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n ab ae e : Z) P,
zrd m A n -> e = A + n -> 0 <= A -> A + 1 <= c -> c <= ab -> c <= e -> ab <= e + 8 -> e <= KHI -> k = Z.to_nat (e - c) ->
(forall a3' a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) a3' (wz e) (wz ab) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x758d0) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) (wz c) (wz e) (wz ab) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x758b8) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR He A0 C1 C2 C3 C4 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A n (c + -1) ZR ltac:(lia) ltac:(lia)) as B.
step. step. stp.
step. destruct (Z_le_gt_dec ab c) as [X1|X1].
{ ifz. apply K. }
ifz. stp. step. destruct (Z_lt_le_dec c e) as [X2|X2].
- ifz. eapply (IH (Z.to_nat (e - (c + 1)))); [lia| exact ZR| lia| lia| lia| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. apply K.
Qed.

Lemma miz_wloop : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n ae e : Z) P,
zrd m A n -> e = A + n -> 0 <= A -> A <= p -> p + 8 <= ae -> ae <= e -> p mod 8 = 0 -> ae mod 8 = 0 -> e <= KHI ->
k = Z.to_nat (ae - p) ->
(forall a3' a5', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) a3' (wz e) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x758e4) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz 0) (wz ae) a3 (wz e) (wz p) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x758d4) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR He A0 C1 C2 C3 P8 E8 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro8 m A n p ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. step. destruct (Z_lt_le_dec (p + 8) ae) as [X1|X1].
- ifz. eapply (IH (Z.to_nat (ae - (p + 8)))); [lia| exact ZR| lia| lia| lia| Z.div_mod_to_equations; lia| lia| Z.div_mod_to_equations; lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. apply K.
Qed.

Lemma miz_eloop : forall k (q : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n e : Z) P,
zrd m A n -> e = A + n -> 0 <= A -> A <= q -> q < e -> e <= KHI -> k = Z.to_nat (e - q) ->
(forall a0' a2' a4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz 0) a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75904) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) (wz q) a3 (wz (e - q)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x758f0) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR He A0 C1 C2 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A n q ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. stp. step. destruct (Z_lt_le_dec (q + 1) e) as [X1|X1].
- ifz. replace (e - q + -1) with (e - (q + 1)) by lia.
eapply (IH (Z.to_nat (e - (q + 1)))); [lia| exact ZR| lia| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. apply K.
Qed.

Lemma miz_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n lo : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
zrd m A n -> 0 < n -> n <= 2^40 -> 0x647000 <= A -> A + n + 8 <= KHI ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' _ => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz miz_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST CEIL LO ZR N0 N40 ALO AHI.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AHI.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold miz_entry.
carve_frame 16%nat ST.
istep. istep.
step. step. step. step. step. ifz.
step. step. step. stp. stp.
rewrite (unsigned_lit (A + 7)), (unsigned_lit (A + n)) by lia. rewrite !land_m8 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ZR' : zrd mc A n) by (eapply zrd_munch; [exact ZR| exact MU| exact WM| intros x Hx; cbn; lia]) end.
set (ab := A + 7 - (A + 7) mod 8). set (ae := A + n - (A + n) mod 8).
assert (AB : A <= ab < A + 8 /\ ab mod 8 = 0) by (subst ab; Z.div_mod_to_equations; lia).
assert (AE : A + n - 8 < ae <= A + n /\ ae mod 8 = 0) by (subst ae; Z.div_mod_to_equations; lia).
clearbody ab ae.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a6' : word, ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 16 a6' R)) FF (wz 0x758d0) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ab A) as [X1|X1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. step. ifz. step. stp.
eapply (miz_bloop (Z.to_nat (A + n - (A + 1))) (A + 1)); [exact ZR'| reflexivity| lia| lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3' a6'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a6' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a3'' a5' : word, ms2 = MS (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 15 a5' R)) FF (wz 0x758e4) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ae ab) as [X2|X2].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. eapply (miz_wloop (Z.to_nat (ae - ab)) ab); [exact ZR'| reflexivity| lia| lia| Z.div_mod_to_equations; lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3'' a5'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a3'' & a5' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall a0' a2' a4',
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m (fun a0'' _ => a0'' = wz 1))
(MS (mkR ra (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0' (wz 0) a2' a3'' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75904) fc None mc (seg_rom asegs)))
end.
{ intros a0' a2' a4'. stp. step. step.
release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity. }
step. destruct (Z_lt_le_dec ae A) as [X3|X3].
{ ifz. apply TAIL. }
ifz. step. destruct (Z_le_gt_dec (A + n) ae) as [X4|X4].
{ ifz. apply TAIL. }
ifz. stp. rewrite (unsigned_lit ae) by lia. replace (A + n + - ae) with (A + n - ae) by lia.
eapply (miz_eloop (Z.to_nat (A + n - ae)) ae); [exact ZR'| reflexivity| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a0' a2' a4'. apply TAIL.
Qed.

Definition shadow_ok (m : mem) (dst n : Z) : Prop :=
forall k, 0 <= k -> dst / 8 * 8 + 8 * k < dst + n ->
exists v, bytes_at asegs m (SH (dst / 8 * 8) + k) [b8 v] /\
(v = 0 \/ (0 < v < 8 /\ dst + n <= dst / 8 * 8 + 8 * k + v)).

Lemma shadow_ok_munch : forall m m' dst n W, shadow_ok m dst n -> munch W m m' -> wmono asegs m m' ->
(forall x, SH dst <= x <= SH (dst + n - 1) -> outside W x) -> 0 < n -> shadow_ok m' dst n.
Proof.
intros m m' dst n W SO MU WM HO N0 k Hk Hkn. destruct (SO k Hk Hkn) as (v & B & C). exists v. split; [| exact C].
eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM|]| exact B|].
- intros x Hx _. exact (HO x Hx).
- intros a Ha. cbn in Ha |- *. rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_first : forall m dst n, shadow_ok m dst n -> 0 < n ->
exists v, ro_cells asegs m (SH dst) [C1 (b8 v)] /\ 0 <= v < 8 /\ (v = 0 \/ dst mod 8 < v).
Proof.
intros m dst n SO N0. destruct (SO 0 ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
exists v. split; [| Z.div_mod_to_equations; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
replace (SH dst) with (SH (dst / 8 * 8) + 0); [exact B|]. rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_last : forall m dst n, shadow_ok m dst n -> 0 < n ->
exists v, ro_cells asegs m (SH (dst + n - 1)) [C1 (b8 v)] /\ 0 <= v < 8 /\ (v = 0 \/ (dst + n - 1) mod 8 < v).
Proof.
intros m dst n SO N0.
destruct (SO ((dst + n - 1) / 8 - dst / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
exists v. split; [| Z.div_mod_to_equations; lia]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app].
replace (SH (dst + n - 1)) with (SH (dst / 8 * 8) + ((dst + n - 1) / 8 - dst / 8)); [exact B|]. rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_zrd : forall m dst n, shadow_ok m dst n -> 0 < n ->
zrd m (SH ((dst + 7) / 8 * 8)) (SH ((dst + n) / 8 * 8) - SH ((dst + 7) / 8 * 8)).
Proof.
intros m dst n SO N0 i Hi. rewrite !SH_eq in Hi.
destruct (SO (((dst + 7) / 8 * 8 - dst / 8 * 8) / 8 + i) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
assert (v = 0) as -> by (Z.div_mod_to_equations; lia).
match type of B with bytes_at _ _ ?a _ => replace (SH ((dst + 7) / 8 * 8) + i) with a; [exact B|] end.
rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma signed_small : forall e, 0 <= e < 2^63 -> bv_signed (wz e) = e.
Proof. intros e He. rewrite zb_signed, (unsigned_lit e) by lia. destruct (Z.ltb_spec0 e (2^63)); lia. Qed.
Lemma land7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac rip_tail RT RL FR ST usp :=
do 10 step; release_frame FR ST usp;
step; apply evt_done; unfold rpost; do 16 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|]; split; [reflexivity| rt_solve RT RL].

Lemma rip_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> KHI <= dst -> dst + n <= band_lo ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO SO [N0 N43] K1d K2d.
pose proof CEIL as CEIL'. idtac. pose proof K1d as K1d'. pose proof K2d as K2d'.
rewrite ?KHI_eq in K1d. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold rip_entry.
carve_frame 64%nat ST.
do 8 istep.
step. ifz.
step. step. rt_now RT RL 19%nat K19. rt_now RT RL 5%nat K5. rt_now RT RL 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp.
step. ifz.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
step. ifz.
stp. stp. stp.
rewrite (unsigned_lit (dst + 7)), (unsigned_lit (n + dst)) by lia. rewrite !land_m8 by lia.
set (ab8 := dst + 7 - (dst + 7) mod 8). set (ae8 := n + dst - (n + dst) mod 8).
assert (AB : dst <= ab8 < dst + 8 /\ ab8 mod 8 = 0 /\ ab8 = (dst + 7) / 8 * 8) by (subst ab8; Z.div_mod_to_equations; lia).
assert (AE : dst + n - 8 < ae8 <= dst + n /\ ae8 mod 8 = 0 /\ ae8 = (dst + n) / 8 * 8) by (subst ae8; Z.div_mod_to_equations; lia).
clearbody ab8 ae8.
step. call0 m2s_spec; [rt_solve RT RL| exact RL| lia| idtac; lia|]. subst_words.
step. step. step. call0 m2s_spec; [rt_solve RT RL| exact RL| rewrite ?KHI_eq; clear - AE K1d N0; Z.div_mod_to_equations; lia| idtac; lia|]. subst_words.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | exact N0]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (shadow_ok_first _ dst n SO' N0) as (v0 & B0 & R0 & C0).
destruct (shadow_ok_last _ dst n SO' N0) as (v1 & B1 & R1 & C1).

step. stp. stp. rewrite (unsigned_lit dst) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
step.
rewrite (sxb_b8 v0) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' : word, ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' R)) FF (wz 0x65694) fcc rv mm ro))
end.
{ step. destruct C0 as [->|C0].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit dst), land7 by lia. step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a2' & a3' & ->). simp_regs.

stp. stp. stp. rewrite (unsigned_lit (n + dst + -1)) by lia.
replace (2147450880 + (n + dst + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
step. rewrite (sxb_b8 v1) by lia.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' a2'' : word, ms2 = MS (@bvmap_set 5 word 11 a1' (@bvmap_set 5 word 12 a2'' R)) FF (wz 0x656e8) fcc rv mm ro))
end.
{ step. destruct C1 as [->|C1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit (n + dst + -1)), land7 by lia. replace ((n + dst + -1) mod 8) with ((dst + n - 1) mod 8) by (f_equal; lia).
step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a1' & a2'' & ->). simp_regs.

pose proof (shadow_ok_zrd _ dst n SO' N0) as ZR. destruct AB as (AB1 & AB2 & AB3). destruct AE as (AE1 & AE2 & AE3).
rewrite <- AB3, <- AE3 in ZR.
assert (SHB : 0x2008fff7000 <= SH ab8 /\ SH ae8 + 8 <= 0x10007fff8000 /\ 8 * (SH ae8 - SH ab8) = ae8 - ab8).
{ rewrite !SH_eq. clear - AB1 AB2 AE1 AE2 K1d K2d N0. Z.div_mod_to_equations. lia. }
step. destruct (Z_le_gt_dec (SH ae8) (SH ab8)) as [X5|X5].
{ ifz. rip_tail RT RL FR ST (bv_unsigned sp). }
ifz. stp. rewrite ?(unsigned_lit (SH ae8)), ?(unsigned_lit (SH ab8)) by lia. replace (SH ae8 + - SH ab8) with (SH ae8 - SH ab8) by lia.
step. step.
call_u miz_spec.
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ZR. } { lia. } { clear - SHB AB1 AE1 N43; Z.div_mod_to_equations; lia. } { lia. } { rewrite ?KHI_eq. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
step. ifz. rip_tail RT RL FR ST' (bv_unsigned sp).
Qed.

Lemma rip_spec_low : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> 0 <= dst -> dst + n <= 0x7fff7800 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO SO [N0 N43] K1d K2d.
pose proof CEIL as CEIL'. idtac. pose proof K1d as K1d'. pose proof K2d as K2d'.
rewrite ?KHI_eq in K1d. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold rip_entry.
carve_frame 64%nat ST.
do 8 istep.
step. ifz.
step. step. rt_now RT RL 19%nat K19. rt_now RT RL 5%nat K5. rt_now RT RL 1%nat K1.
step. stp. stp.
step. stp. stp. stp.
step. ifz.
stp.
step. ifz.
step. ifz.
stp. stp. stp.
rewrite (unsigned_lit (dst + 7)), (unsigned_lit (n + dst)) by lia. rewrite !land_m8 by lia.
set (ab8 := dst + 7 - (dst + 7) mod 8). set (ae8 := n + dst - (n + dst) mod 8).
assert (AB : dst <= ab8 < dst + 8 /\ ab8 mod 8 = 0 /\ ab8 = (dst + 7) / 8 * 8) by (subst ab8; Z.div_mod_to_equations; lia).
assert (AE : dst + n - 8 < ae8 <= dst + n /\ ae8 mod 8 = 0 /\ ae8 = (dst + n) / 8 * 8) by (subst ae8; Z.div_mod_to_equations; lia).
clearbody ab8 ae8.
step. call0 m2s_spec_low; [rt_solve RT RL| exact RL| lia| idtac; lia|]. subst_words.
step. step. step. call0 m2s_spec_low; [rt_solve RT RL| exact RL| rewrite ?KHI_eq; clear - AE K1d N0; Z.div_mod_to_equations; lia| idtac; lia|]. subst_words.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | exact N0]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (shadow_ok_first _ dst n SO' N0) as (v0 & B0 & R0 & C0).
destruct (shadow_ok_last _ dst n SO' N0) as (v1 & B1 & R1 & C1).

step. stp. stp. rewrite (unsigned_lit dst) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
step.
rewrite (sxb_b8 v0) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' : word, ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' R)) FF (wz 0x65694) fcc rv mm ro))
end.
{ step. destruct C0 as [->|C0].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit dst), land7 by lia. step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a2' & a3' & ->). simp_regs.

stp. stp. stp. rewrite (unsigned_lit (n + dst + -1)) by lia.
replace (2147450880 + (n + dst + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
step. rewrite (sxb_b8 v1) by lia.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' a2'' : word, ms2 = MS (@bvmap_set 5 word 11 a1' (@bvmap_set 5 word 12 a2'' R)) FF (wz 0x656e8) fcc rv mm ro))
end.
{ step. destruct C1 as [->|C1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit (n + dst + -1)), land7 by lia. replace ((n + dst + -1) mod 8) with ((dst + n - 1) mod 8) by (f_equal; lia).
step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a1' & a2'' & ->). simp_regs.

pose proof (shadow_ok_zrd _ dst n SO' N0) as ZR. destruct AB as (AB1 & AB2 & AB3). destruct AE as (AE1 & AE2 & AE3).
rewrite <- AB3, <- AE3 in ZR.
assert (SHB : 0x7fff8000 <= SH ab8 /\ SH ae8 <= 0x8fff7000 /\ 8 * (SH ae8 - SH ab8) = ae8 - ab8).
{ rewrite !SH_eq. clear - AB1 AB2 AE1 AE2 K1d K2d N0. Z.div_mod_to_equations. lia. }
step. destruct (Z_le_gt_dec (SH ae8) (SH ab8)) as [X5|X5].
{ ifz. rip_tail RT RL FR ST (bv_unsigned sp). }
ifz. stp. rewrite ?(unsigned_lit (SH ae8)), ?(unsigned_lit (SH ab8)) by lia. replace (SH ae8 + - SH ab8) with (SH ae8 - SH ab8) by lia.
step. step.
call_u miz_spec.
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ZR. } { lia. } { clear - SHB AB1 AE1 N43; Z.div_mod_to_equations; lia. } { lia. } { rewrite ?KHI_eq. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
step. ifz. rip_tail RT RL FR ST' (bv_unsigned sp).
Qed.

Lemma rip_spec_lh : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> ((KHI <= dst /\ dst + n <= band_lo) \/ (0 <= dst /\ dst + n <= 0x7fff7800)) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ RTconst RE X m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO SO NR [[K1d K2d]|[K1d K2d]].
- eapply rip_spec; eassumption.
- eapply rip_spec_low; eassumption.
Qed.

End S.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QDM6.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO QFQR QmP7 QKBN QNQk.Mq8.
Import QN4c.
Import QlES. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition rz_size2log_entry : Z := 0x44994.

Definition rz_log_of (v : Z) : Z := if v =? 16 then 0 else 7.

Lemma rz_size2log_spec {BAND : Band} : forall v ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
(v = 16 \/ v = 2048) ->
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (rz_log_of v)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rz_size2log_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros HV MI ST CEIL LO. idtac. unfold rz_size2log_entry.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
destruct HV as [-> | ->]; cbn [rz_log_of Z.eqb Pos.eqb].
- repeat (stp; try if_lit).
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity.
- repeat (stp; try if_lit).
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity.
Qed.
End Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QXcn QsJM.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma shword_eq : forall x, 8 * (SH x / 8) = SH (64 * (x / 64)).
Proof. intros x. rewrite !SH_eq. Z.div_mod_to_equations. lia. Qed.

Lemma shword_pt : forall x z, 8 * (SH x / 8) <= z < 8 * (SH x / 8) + 8 ->
exists y, y mod 8 = 0 /\ 64 * (x / 64) <= y < 64 * (x / 64) + 64 /\ SH y = z.
Proof.
intros x z Hz. rewrite shword_eq, SH_eq in Hz. exists (8 * (z - 0x7fff8000)). rewrite SH_eq.
Z.div_mod_to_equations. lia.
Qed.

Lemma sh_in : forall lo hi y, lo mod 8 = 0 -> hi mod 8 = 0 -> lo <= y < hi -> y mod 8 = 0 -> SH lo <= SH y < SH hi.
Proof. intros lo hi y AL AH Hy Y8. rewrite !SH_eq. Z.div_mod_to_equations. lia. Qed.

Section S.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Hypothesis RP : RPrim a G RE X m.
Hypothesis RCH : RChunks a LB0 G RE X m.
Hypothesis RQ : RQuar a LB0 G RE X m.
Hypothesis RF : RFake FS0 RE X m.
Local Notation L := (ae_L RE).

Definition shsome (lo hi : Z) : Prop :=
forall y, lo <= y < hi -> y mod 8 = 0 -> exists b, m (wa (SH y)) = Some b.

Lemma shsome_of_hjunk : forall lo hi, lo mod 8 = 0 -> hi mod 8 = 0 -> hjunk m (SH lo) (SH hi) -> shsome lo hi.
Proof. intros lo hi AL AH (_ & _ & J) y Hy Y8. apply J. apply sh_in; assumption. Qed.

Lemma shword_hjunk : forall lo hi x, lo mod 64 = 0 -> hi mod 64 = 0 -> 0 <= lo -> hi <= band_lo -> lo <= x < hi ->
shsome lo hi -> hjunk m (8 * (SH x / 8)) (8 * (SH x / 8) + 8).
Proof.
intros lo hi x AL AH K CE Hx SS. pose proof (shword_eq x) as E. rewrite ?KHI_eq in K. idtac.
split; [rewrite E, SH_eq; Z.div_mod_to_equations; lia|].
split; [rewrite E, SH_eq; Z.div_mod_to_equations; lia|].
intros z Hz. destruct (shword_pt x z Hz) as (y & Y8 & Hy & <-). apply SS; [| exact Y8].
Z.div_mod_to_equations. nia.
Qed.

Lemma cells_hjunk_sh : forall lo cs, rw_cells asegs m (SH lo) cs -> KHI <= lo -> hjunk m (SH lo) (SH lo + Z.of_nat (cells_size cs)).
Proof. intros lo cs H K. apply cells_hjunk; [exact H|]. rewrite SH_eq, ?KHI_eq in *. Z.div_mod_to_equations. lia. Qed.

Lemma cells_hjunk_sh0 : forall lo cs, rw_cells asegs m (SH lo) cs -> 0 <= lo -> hjunk m (SH lo) (SH lo + Z.of_nat (cells_size cs)).
Proof. intros lo cs H K. apply cells_hjunk; [exact H|]. rewrite SH_eq in *. Z.div_mod_to_equations. lia. Qed.

Lemma batches_shadow : forall QA bs J j, batches_mem RE m QA bs J -> In j J ->
rw_cells asegs m (SH (slot_beg RE 24 j)) [CB 1024%nat (fas 1024)].
Proof.
intros QA bs. induction bs as [|b bs IH]; intros J j H Hin; destruct J as [|j' J]; cbn in H, Hin; try contradiction.
destruct H as [HB H]. destruct Hin as [<-|Hin].
- destruct HB as (_ & _ & _ & S). exact S.
- eapply IH; [exact H| exact Hin].
Qed.

Lemma chunk_mem_shadow : forall lo hi A n, chunk_mem m lo hi A n -> hjunk m (SH lo) (SH lo + (hi - lo) / 8).
Proof.
intros lo hi A n CM. pose proof CM as (_ & _ & _ & _ & S & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (round_up_ge (used_size n) 8 ltac:(unfold used_size; lia)) as (U1 & U2 & U3).
pose proof (ngran_eq (used_size n) ltac:(unfold used_size; lia)) as (N1 & N2 & N3).
pose proof (cells_hjunk_sh0 lo _ S ltac:(clear - M8; lia)) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J.
match type of J with hjunk _ _ ?e => replace (SH lo + (hi - lo) / 8) with e; [exact J|] end.
Z.div_mod_to_equations. nia.
Qed.

Lemma qchunk_mem_shadow : forall lo hi A n, qchunk_mem m lo hi A n -> hjunk m (SH lo) (SH lo + (hi - lo) / 8).
Proof.
intros lo hi A n CM. pose proof CM as (_ & _ & _ & (sj & S) & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (qchunk_geom m lo hi A n CM) as (_ & _ & _ & _ & _ & _ & _ & _ & q & g & r & Q1 & Q2 & G1 & G2 & G3 & R1 & R2 & T).
pose proof (cells_hjunk_sh0 lo _ S ltac:(clear - M8; lia)) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J.
match type of J with hjunk _ _ ?e => replace (SH lo + (hi - lo) / 8) with e; [exact J|] end.
rewrite G2 in *. Z.div_mod_to_equations. nia.
Qed.

Lemma slot_shadow : forall c i t, tag_at G c i = Some t ->
hjunk m (SH (slot_beg RE c i)) (SH (slot_beg RE c i) + class_size c / 8).
Proof.
intros c i t Ht.
pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & P8 & P16 & Hc & R1 & R2 & S32 & SM).
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & KP & _).
assert (KS : KHI <= slot_beg RE c i) by lia.
destruct t as [| |p|p|].
-
destruct RP as (K & _ & _ & CR). destruct (CR c ltac:(unfold kNumClasses; lia)) as (_ & _ & REG).
destruct (REG ltac:(lia)) as (_ & _ & _ & _ & FS & _). specialize (FS i TFree Ht eq_refl).
pose proof (cells_hjunk_sh _ _ FS KS) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia. exact J.
-
destruct RP as (K & _ & _ & CR). destruct (CR c ltac:(unfold kNumClasses; lia)) as (_ & _ & REG).
destruct (REG ltac:(lia)) as (_ & _ & _ & _ & FS & _). specialize (FS i TCached Ht eq_refl).
pose proof (cells_hjunk_sh _ _ FS KS) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia. exact J.
-
destruct (gc_live_tags' a LB0 FS0 G RE X GC c i p Ht) as (id & n & A & -> & Hin & Hcl).
pose proof (proj1 RCH _ _ _ Hin) as CR. cbn [chunk_rep] in CR. destruct CR as (_ & i' & Ht' & HA & CM).
rewrite Hcl in Ht', HA, CM.
assert (i' = i) as ->.
{ symmetry. eapply proj2. eapply (gc_unique a LB0 FS0 G RE X GC c i c i' (APrim id n)); [exact Ht| exact Ht'| |]; cbn; rewrite N.eqb_refl, Z.eqb_refl; reflexivity. }
pose proof (chunk_mem_shadow _ _ _ _ CM) as J.
replace (slot_beg RE c i + class_size c - slot_beg RE c i) with (class_size c) in J by lia. exact J.
-
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & BND).
destruct (TQP c i p Ht) as [HinP Hcl]. pose proof (REP p HinP) as QR.
destruct (gc_quar_tags a LB0 FS0 G RE X GC c i p Ht) as [_ FP].
destruct p as [id n|mb n]; cbn [qptr_rep] in QR.
+ destruct QR as (i' & Ht' & _ & HQA & CM). unfold aptr_cls in Hcl. cbn [aptr_req] in Hcl. rewrite Hcl in Ht', HQA, CM.
assert (i' = i) as ->.
{ symmetry. eapply proj2. eapply (gc_unique a LB0 FS0 G RE X GC c i c i' (APrim id n)); [exact Ht| exact Ht'| |]; cbn; rewrite N.eqb_refl, Z.eqb_refl; reflexivity. }
pose proof (qchunk_mem_shadow _ _ _ _ CM) as J.
replace (slot_beg RE c i + class_size c - slot_beg RE c i) with (class_size c) in J by lia. exact J.
+ destruct QR as (_ & _ & FP' & _). cbn [aptr_req] in FP. rewrite FP in FP'. discriminate.
-
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & BND).
pose proof (C24 c i Ht) as ->. specialize (TQO i Ht). apply in_app_or in TQO.
assert (S : rw_cells asegs m (SH (slot_beg RE 24 i)) [CB 1024%nat (fas 1024)]).
{ destruct TQO as [Hin|Hin].
- destruct HT as (_ & BM & _). eapply batches_shadow; [exact BM| exact Hin].
- destruct HG as (_ & BM & _). eapply batches_shadow; [exact BM| exact Hin]. }
pose proof (cells_hjunk_sh _ _ S KS) as J. cbn [cells_size csize Nat.add] in J.
change (class_size 24 / 8) with 1024. exact J.
Qed.

Lemma region_shadow : forall c, 1 <= c <= 31 -> shsome (reg_beg L c) (reg_beg L c + kFreeArrayOffset).
Proof.
intros c Hc y Hy Y8.
destruct RP as (K & _ & _ & CR). destruct (CR c ltac:(unfold kNumClasses; lia)) as (_ & PU & REG).
destruct (REG ltac:(lia)) as (_ & _ & _ & _ & _ & TAIL & JU & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEN & AU0 & AUM & MUF & MUM).
pose proof (class_size_facts c Hc) as [S1 S2].
pose proof (rl_prim a LB0 FS0 G RE X GC) as (AL16 & KP & _).
pose proof (region_in_prim RE c Hc) as (R1 & _ & _ & R4).
pose proof (reg_beg_align RE X c (gc_rlay a LB0 FS0 G RE X GC)) as (RB8 & _).
pose proof kconsts as (_ & KO & _ & _ & _ & _ & KU & _).
set (rb := reg_beg L c) in *. set (sz := class_size c) in *.
set (au := c_alloc_user (cls a c)) in *. set (mu := c_mapped_user (cls a c)) in *.
assert (SZ8 : sz mod 8 = 0) by (clear - S2; Z.div_mod_to_equations; lia).
assert (AU8 : exists k, au = 8 * k).
{ exists (Z.of_nat (length (G c)) * (sz / 8)). rewrite <- LEN.
transitivity (Z.of_nat (length (G c)) * (8 * (sz / 8))); [f_equal; clear - SZ8; Z.div_mod_to_equations; lia| ring]. }
assert (MU8 : exists k, mu = 8 * k).
{ exists (mu / 8). rewrite KU in MUM. clear - MUM. Z.div_mod_to_equations. lia. }
destruct AU8 as (ka & Hka). destruct MU8 as (km & Hkm).
destruct (Z_lt_le_dec y (rb + au)) as [LT|GE].
-
set (i := (y - rb) / sz).
assert (Hi : 0 <= i /\ rb + i * sz <= y < rb + i * sz + sz) by (subst i; clear - Hy S1; Z.div_mod_to_equations; nia).
assert (IL : i < Z.of_nat (length (G c))) by (subst i; clear - Hy LT S1 LEN; Z.div_mod_to_equations; nia).
destruct (nth_error (G c) (Z.to_nat i)) as [t|] eqn:E; [| apply nth_error_None in E; lia].
assert (Ht : tag_at G c i = Some t) by (unfold tag_at; destruct (Z.ltb_spec i 0); [lia| exact E]).
pose proof (slot_shadow c i t Ht) as (_ & _ & J). unfold slot_beg in J. fold rb sz in J.
assert (P8 : exists k, i * sz = 8 * k).
{ exists (i * (sz / 8)). transitivity (i * (8 * (sz / 8))); [f_equal; clear - SZ8; Z.div_mod_to_equations; lia| ring]. }
destruct P8 as (k & Pk). rewrite Pk in J, Hi.
apply J. rewrite !SH_eq. clear - Hi Y8 RB8 S1 S2 Pk. Z.div_mod_to_equations. lia.
- destruct (Z_lt_le_dec y (rb + mu)) as [LT2|GE2].
+
assert (KS : KHI <= rb + au) by lia.
pose proof (cells_hjunk_sh _ _ TAIL KS) as (_ & _ & J). cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia.
apply J. rewrite !SH_eq. rewrite Hka, Hkm in *. clear - LT2 GE Y8 RB8. Z.div_mod_to_equations. lia.
+
destruct JU as (_ & _ & J). apply J. rewrite !SH_eq. rewrite Hkm, KO in *. clear - GE2 Hy Y8 RB8. Z.div_mod_to_equations. lia.
Qed.

Lemma block_byte_nbhd : forall p A n0 x, In (p, A, n0) LB0 -> A <= x < A + n0 ->
hjunk m (8 * (SH x / 8)) (8 * (SH x / 8) + 8).
Proof.
intros p A n0 x Hin Hx.
pose proof (rl_prim a LB0 FS0 G RE X GC) as (AL16 & KP & _). pose proof kconsts as (_ & KO & _ & _ & KPG & _ & KU & _).
destruct (live_block_geom a LB0 FS0 G RE X GC p A n0 Hin) as (Hn & A16 & [(c & i & Ht & Hc & Hp & HA & CT)|(e & He & Hp & Hr & HA & CT)]);
unfold blk_container in CT.
- pose proof (slot_prim a LB0 FS0 G RE X GC c i _ Ht) as (P1 & P2 & P8 & P16 & Hcc & R1 & R2 & S32 & SM).
pose proof (region_in_prim RE c Hcc) as (Q1 & _ & _ & Q4).
eapply (shword_hjunk (reg_beg L c) (reg_beg L c + kFreeArrayOffset)).
+ rewrite Q4. rewrite ?KHI_eq in KP. Z.div_mod_to_equations. lia.
+ rewrite Q4, KO. Z.div_mod_to_equations. lia.
+ rewrite ?KHI_eq in KP. lia.
+ pose proof (region_in_prim RE c Hcc) as (_ & Q2 & Q3 & _). pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & _ & PH & _).
unfold prim_hi in PH. unfold prim_lo in *. pose proof kconsts as (_ & _ & KS & _). lia.
+ lia.
+ apply region_shadow. exact Hcc.
- pose proof (sec_entry_facts a LB0 FS0 G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M2.
pose proof (proj1 RCH _ _ _ Hin) as CR. rewrite Hp in CR. cbn [chunk_rep] in CR. destruct CR as (_ & Hin2 & _ & CM).
rewrite <- Hr, <- E4 in CM.
eapply (shword_hjunk (se_beg e + kPage) (se_beg e + se_size e)).
+ rewrite KPG. Z.div_mod_to_equations. lia.
+ Z.div_mod_to_equations. lia.
+ rewrite KPG. lia.
+ lia.
+ lia.
+ apply shsome_of_hjunk; [rewrite KPG; Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia|].
pose proof (chunk_mem_shadow _ _ _ _ CM) as J.
replace (SH (se_beg e + kPage) + (se_beg e + se_size e - (se_beg e + kPage)) / 8) with (SH (se_beg e + se_size e)) in J; [exact J|].
rewrite !SH_eq, KPG. Z.div_mod_to_equations. lia.
Qed.

Lemma frame_byte_nbhd : forall c f x, In (c, f) FS0 -> f <= x < f + ff_size c ->
hjunk m (8 * (SH x / 8)) (8 * (SH x / 8) + 8).
Proof.
intros c f x Hin Hx.
destruct RF as (AL & K1 & K2 & SHP & _ & _ & _ & _ & _ & _ & J).
destruct SHP as [SHf _]. destruct (SHf _ Hin) as (Hc & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc, Hp, Ef.
pose proof (fs_frame_in_area (ae_fs_base RE) c pos Hc Hp) as [F1 F2]. rewrite <- Ef in F1, F2.
unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in *.
eapply (shword_hjunk (ae_fs_base RE + 0x9000) (ae_fs_base RE + 0xb09000)).
- Z.div_mod_to_equations. lia.
- Z.div_mod_to_equations. lia.
- lia.
- lia.
- lia.
- apply shsome_of_hjunk; [Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| exact J].
Qed.

Lemma amemset_nbhd : forall dst n, amemset_whereA LB0 FS0 dst n -> 0 < n ->
hjunk m (8 * (SH dst / 8)) (8 * (SH dst / 8) + 8)
/\ hjunk m (8 * (SH (dst + n - 1) / 8)) (8 * (SH (dst + n - 1) / 8) + 8).
Proof.
intros dst n [(p & A & n0 & Hin & H1 & H2)|(c & f & Hin & H1 & H2)] Hn.
- split; eapply (block_byte_nbhd p A n0); try exact Hin; lia.
- split; eapply (frame_byte_nbhd c f); try exact Hin; lia.
Qed.

End S.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QDM6.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq8.
Import QN4c.
Import QlES. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition get_current_thread_entry : Z := 0x6d6b8.
Definition get_thread_stats_entry : Z := 0x6c884.

Section Thread.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma get_current_thread_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (leafw_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (rl_T X) /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_current_thread_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
rtc RT 3%nat K3. rtc RT 4%nat K4. rtc RT 28%nat K28. rtc RT 29%nat K29. pose proof (RT_ctx_thread _ _ _ RT) as CT.
pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & CLO & CHI & _). cbn [fst snd] in CLO, CHI. idtac. rewrite ?KHI_eq in CLO.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TLO & THI & _). cbn [fst snd] in TLO, THI. idtac. rewrite ?KHI_eq in TLO.
unfold get_current_thread_entry, A_TP, A_TLS_TSD, A_TSD_MAIN in *.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. step. stp. step. if_lit.
stp. step.
step. step. step. step. step. step. step.
step. unfold_cond. rewrite (unsigned_lit (rl_ctx X)) by lia. if_lit.
step.
step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor].
Qed.

Lemma get_thread_stats_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 32 ->
evt asegs (leafw_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 32, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz (rl_T X + 2800) /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz get_thread_stats_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TLO & THI & _). cbn [fst snd] in TLO, THI. idtac. rewrite ?KHI_eq in TLO.
unfold get_thread_stats_entry.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
call_sp (get_current_thread_spec _ _); try eassumption.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
{ lia. }
subst. rename x14 into m1.
step. unfold_cond. rewrite (unsigned_lit (rl_T X)) by lia. if_lit.
step. step.
step. step. step.
release_frame FR PC (bv_unsigned sp).
apply evt_done. unfold leafw_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact PC|]. split; [reflexivity|]. exact POST.
Qed.
End Thread.
End Mqi.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition tls_fs_entry : Z := 0x55798.
Definition tls_fs_stack : Z := 176.
Definition A_FS_TLSDESC : Z := 0x0e8fe8.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma tls_fs_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 176 ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(bv_unsigned sp - 176, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz A_TP /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_FS_TLSDESC) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz tls_fs_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL MI ST CEIL LO. pose proof CEIL as CEIL'. idtac.
unfold tls_fs_entry, tls_fs_stack, A_FS_TLSDESC, A_TP in *.
obj_facts RL.
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 176%nat ST.

step_until 0x557b0.

rt_now RT RL 0%nat K0. step_until 0. if_false. clear K0. step_until 0x557b4.

rt_now RT RL 36%nat K36. rt_now RT RL 34%nat K34. rt_now RT RL 38%nat K38. rt_now RT RL 39%nat K39.
step_until 0x557c8. clear K36 K34 K38 K39.
replace (wz (2 ^ 64 - 2048 + 6446368)) with (wz 6444320) by (apply bv_eq; vm_compute; reflexivity).
step_until 0. if_false.

rt_now RT RL 3%nat K3. step_until 0. if_false. clear K3.
rt_now RT RL 4%nat K4. rt_now RT RL 28%nat K28. unfold A_TSD_MAIN in K28. rt_now RT RL 29%nat K29.
step_until 0x6d6c4. clear K4 K28 K29. istep. if_false_u.
rt_ctx_now RT RL CT. step_until 0. clear CT. if_false_u.

rt_T_now RT RL TT. step_until 0x7aee0. clear TT.

step_until 0x7af1c.
rt_now RT RL 19%nat K19. step_until 0x7af24. clear K19.
rt_now RT RL 37%nat K37. step_until 0. clear K37. if_false_u.
rt_now RT RL 20%nat K20. step_until 0x7af38. clear K20.
rt_now RT RL 34%nat K34. step_until 0x7af3c. clear K34.
rt_now RT RL 9%nat K9. step_until 0x7af44. clear K9.
rt_now RT RL 35%nat K35. step_until 0. clear K35. if_false_u.
rt_now RT RL 31%nat K31. step_until 0. clear K31. if_false_u.
istep. if_true_u. istep. if_false_u.
step_until 0. if_true_u.
rt_dtls_now RT RL DT. step_until 0. clear DT. if_false_u.

step_until 0x557f8. step_until 0.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [reflexivity|].
eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor].
Qed.

End Walk.
