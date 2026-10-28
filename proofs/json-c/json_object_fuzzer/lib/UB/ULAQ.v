(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgLo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgLo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7b.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac sepcache_on ::= fail.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_seed_addr : Z := 0x66a40.

#[using="Type"] Lemma mod16_mod4 : forall k, k mod 16 = 0 -> k mod 4 = 0.
Proof.
intros k H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (4 * q). lia.
Qed.

#[using="Type"] Lemma hash_core :
forall (kp : Z) (ks slack : list byte) (m : word -> option byte)
(x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (SP : Z) (rac s0c s1c s2c hf seed : word) (j8 : list byte),
bytes_at rsegs m kp (ks ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) ks ->
(- (kp + Z.of_nat (length ks) + 1)) mod 8 <= Z.of_nat (length slack) ->
mem_inv rsegs m -> kp mod 4 = 0 -> 0 < kp ->
rw_cells rsegs m SP [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2c; C8 s1c; C8 s0c; C8 rac] ->
rw_cells rsegs m GHASH4 [C8 hf; C4 seed] ->
bv_unsigned rac mod 2 = 0 ->
evt rsegs (fun ms' => exists (u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word) (h : Z) m',
ms' = MS (mkR rac (Z_to_bv 64 (SP + 96)) gp tp u0 u1 u2 s0c s1c (Z_to_bv 64 h) v1 v2 v3 v4 v5 v6 v7 s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (ret_pc rac) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ 0 <= h < 2^64)
(MS (mkR x1 (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 kp) (Z_to_bv 64 lh_seed_addr) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x278a8) fc None m (seg_rom rsegs)).
Proof.
intros until j8. intros STR NONUL PAD MI AL KP0 FR G RA.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (rw_cells_bound rsegs m SP _ FR) as SB. cbn [cells_size csize Nat.add] in SB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold lh_seed_addr, GHASH4 in *.
step. step.

call (strlen_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 kp)); [rewrite unsigned_lit by lia; exact STR | exact NONUL | rewrite unsigned_lit by lia; exact PAD | exact MI |].
do 7 (hstep (Z_to_bv 64 SP)).
rewrite (unsigned_lit kp) by lia. replace (Z.land kp 3) with 0 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; lia).
if_true.
step. step.
match goal with H : bytes_at rsegs ?mx kp _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into STR2; rename mx into m2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
destruct (Z.lt_ge_cases (Z.of_nat (length ks)) 13) as [LT | GE].
- if_truex. step. step.
replace (Z_to_bv 64 kp) with (Z_to_bv 64 (kp + 0)) by (f_equal; lia).
replace (Z_to_bv 64 (Z.of_nat (length ks))) with (Z_to_bv 64 (Z.of_nat (length ks) - 0)) by (f_equal; lia).
eapply evt_cut; [eapply (hash_tail kp ks slack m2 STR2 MI2 AL KP0 0); lia|].
cbv beta. intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->).
do 13 step.
word_range v0 VR; replace v0 with (Z_to_bv 64 (bv_unsigned v0)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
apply evt_done. do 14 eexists. eexists. eexists. split; [reflexivity|]. repeat split; try assumption; lia.
- if_falsex. do 6 step.
replace (Z_to_bv 64 kp) with (Z_to_bv 64 (kp + 0)) by (f_equal; lia).
replace (Z_to_bv 64 (Z.of_nat (length ks))) with (Z_to_bv 64 (Z.of_nat (length ks) - 0)) by (f_equal; lia).
eapply evt_cut; [eapply (hash_loop kp ks slack m2 STR2 AL KP0 (Z.to_nat (Z.of_nat (length ks) - 0)) 0); lia|].
cbv beta. intros ms' (j' & t0' & t1' & t2' & a1' & a2' & a3' & t3' & Hj' & Hr' & Hal' & ->).
eapply evt_cut; [eapply (hash_tail kp ks slack m2 STR2 MI2 AL KP0 j'); lia|].
cbv beta. intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->).
do 13 step.
word_range v0 VR; replace v0 with (Z_to_bv 64 (bv_unsigned v0)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
apply evt_done. do 14 eexists. eexists. eexists. split; [reflexivity|]. repeat split; try assumption; lia.
Qed.
End RC__1.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Umd7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtfO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtfO.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section LhHash.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).
Variable MREL : Model -> Model -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.

Definition seed_settle_post (sp gp : word) (s0v : word) (s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (ms' : machine_state) (md' : Model) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (A' : AS S4L HIx) (errv' : word),
ms' = MS (mkR x1 sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0v (Z_to_bv 64 lh_seed_addr) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x278a8) fc None m' (seg_rom rsegs) /\
md' = md /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\ lh_glob4 m' /\ HEAPx A' LB m' md.

Definition seed_settle_stmt (SD : Z) : Prop :=
forall (x1 sp gp t0 t1 t2 s0v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv seedv : word),
HEAPx A LB m md -> lh_glob4 m ->
rw_cells rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C4 seedv] -> sx32 seedv = Z_to_bv 64 (-1) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
(forall ms' md', seed_settle_post sp gp s0v s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0v (Z_to_bv 64 lh_seed_addr) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2788c) fc None m (seg_rom rsegs)) md) T.

Variable SD : Z.
Hypothesis SD_ge : 16 <= SD.
Hypothesis SEED : seed_settle_stmt SD.

#[using="Type"] Lemma key_string : forall A LB m md kp kn ks,
HEAPx A LB m md -> In (kp, kn) LB -> cstr rsegs m kp kn ks ->
exists slack, bytes_at rsegs m kp (ks ++ Z_to_bv 8 0 :: slack) /\
(- (kp + Z.of_nat (length ks) + 1)) mod 8 <= Z.of_nat (length slack) /\
~ In (Z_to_bv 8 0) ks /\ kp mod 16 = 0 /\ Z.of_nat (length ks) + 1 <= kn /\ 0 < kp /\ kp + kn <= alloc_ceiling /\
kp + Z.of_nat (length ks) + 1 + Z.of_nat (length slack) <= kp + kn + 16.
Proof.
intros A LB m md kp kn ks HP Hin (CL & CNZ & junk & CB).
pose proof (heap_blk S4L HIx _ _ _ _ kp kn HP Hin) as (Hn0 & Hal & Hlo & Hhi & _).
assert (NN : ~ In (Z_to_bv 8 0) ks).
{ intros X. rewrite Forall_forall in CNZ. apply (CNZ _ X). reflexivity. }
destruct (str_slack S4L HIx _ _ _ _ kp kn (ks ++ [Z_to_bv 8 0] ++ junk) kp ks HP Hin) as (slack & B & P & E).
{ split; [exact CB|]. split; [lia|]. split; [lia|]. split; [| exact NN].
rewrite Z.sub_diag. change (Z.to_nat 0) with 0%nat. rewrite skipn_O. rewrite app_assoc, firstn_app, firstn_all2 by (rewrite length_app; cbn; lia).
rewrite length_app. cbn [length]. replace (length ks + 1 - (length ks + 1))%nat with 0%nat by lia. cbn. rewrite app_nil_r. reflexivity. }
exists slack. split; [exact B|]. split; [exact P|]. split; [exact NN|]. split; [exact Hal|]. split; [exact CL | split; [exact Hlo | split; [exact Hhi | exact E]]].
Qed.

#[using="MREL_refl SD_ge SEED"] Lemma lh_char_hash_cps : forall HD, 96 + SD <= HD -> lh_char_hash_stmt HIx MREL HD.
Proof.
intros HD HHD. unfold lh_char_hash_stmt. intros until ks. intros HP INK CS G ST LO LOS SPA HT ERR TP RA FRM A0 K.
unfold_consts. word_range sp SPR.
destruct (key_string _ _ _ _ _ _ _ HP INK CS) as (slack & STR & PAD & NN & KAL & KL & KPOS & KHI & KSL). unfold alloc_ceiling, sp_window_lo, stack_max_size in KHI.
assert (LF : Z.of_nat (length (ks ++ Z_to_bv 8 0 :: slack)) = Z.of_nat (length ks) + 1 + Z.of_nat (length slack)) by (rewrite length_app; cbn; lia).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof G as ([seed G1] & G2 & (vf & G3 & VF)). unfold GHASH4 in G1. unfold GGOT4 in G2. unfold GVDSO4 in G3.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold lh_char_hash_entry. subst a0 tp.
carve_frame 96%nat ST.
do 12 step.
step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (G1' : lh_glob4 m1).
{ eapply (lh_glob_frame rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4 m m1); [exact G | exact MU | exact WM |].
apply Forall_cons; [cbn; unfold GHASH4, GGOT4, GVDSO4; lia | apply Forall_nil]. }
assert (HP1 : HEAPx A LB m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (HPR1 : heap_presx S4L s4_volatile LB (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch S4L s4_volatile LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; exact Hb | clia |]. solve_clientW S4L HIx HP. }
destruct (bv_eqb (sx32 seed) (Z_to_bv 64 (-1))) eqn:ESEED; [change (negb true) with false | change (negb false) with true]; cbv iota.
-
apply evt_RZ_done.
eapply (SEED _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md T A LB lo errv seed);
[exact HP1 | exact G1' | exact G1 | apply (proj1 (Fs.bv_eqb_eq _ _)); exact ESEED | ..]; try alloc_side.
intros ms2 md2 (y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & A2 & errv2 & -> & -> & ST2 & HPR2 & ERR2 & GL2 & HP2).
cbn [hl_segs S4L] in *. rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST2, HPR2 by lia.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (HPR12 : heap_presx S4L s4_volatile LB (bv_unsigned sp) m m2).
{ eapply heap_presx_trans; [exact HPR1|]. eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; exact Hb | intros a' Ha'; exact Ha']. }
assert (CS2 : cstr rsegs m2 kp kn ks).
{ destruct CS as (CL' & CNZ & junk2 & CB). split; [exact CL'|]. split; [exact CNZ|]. exists junk2.
eapply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR12); [exact CB|]. eapply client_rangex_block; [exact INK | lia | cbn; lia]. }
clear STR PAD LF KSL slack.
destruct (key_string _ _ _ _ _ _ _ HP2 INK CS2) as (slack & STR & PAD & _ & _ & _ & _ & _ & KSL2).
assert (LF2 : Z.of_nat (length (ks ++ Z_to_bv 8 0 :: slack)) = Z.of_nat (length ks) + 1 + Z.of_nat (length slack)) by (rewrite length_app; cbn; lia).
pose proof GL2 as ([seed2 G21] & G22 & (vf2 & G23 & VF2)). unfold GHASH4 in G21. unfold GGOT4 in G22. unfold GVDSO4 in G23.
clear MU WM MI1.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m2) as MU.
reenter MOK2.
call (hash_core kp ks slack m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc (bv_unsigned sp + -96) ra s0 s1 s2 (Z_to_bv 64 (fn_lh_char_hash S4F)) seed2 _);
[exact STR | exact NN | exact PAD | exact MI | apply mod16_mod4; exact KAL | exact KPOS | exact FR | exact G21 | exact RA |].
replace (Z_to_bv 64 (bv_unsigned sp + -96 + 96)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
match goal with H : mem_inv rsegs mF |- _ => rename H into MIF end.
apply evt_RZ_done. apply K. unfold lh_hash_post.
eexists. exists A2. eexists. exists errv2.
split; [unfold ret_statew; do 16 eexists; split; [reflexivity | split; [apply QCcH.fsaved_refl | intros H0; exact H0]] |].
split; [lia|]. split; [apply MREL_refl|].
split; [release_frame FR ST2 (bv_unsigned sp); exact ST2 |].
split; [| split; [eassumption | split]].
+ eapply heap_presx_trans; [exact HPR12|]. eapply (heap_presx_of_munch S4L s4_volatile LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; exact Hb | clia |]. solve_clientW S4L HIx HP2.
+ eapply (lh_glob_frame rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4 m2 mF); [exact GL2 | exact MU | exact WM |].
apply Forall_cons; [cbn; unfold GHASH4, GGOT4, GVDSO4; lia | apply Forall_nil].
+ heap_now S4L HIx HP2 MU WM MIF.
-
call (hash_core kp ks slack m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc (bv_unsigned sp + -96) ra s0 s1 s2 (Z_to_bv 64 (fn_lh_char_hash S4F)) seed _);
[exact STR | exact NN | exact PAD | exact MI1 | apply mod16_mod4; exact KAL | exact KPOS | exact FR | exact G1 | exact RA |].
replace (Z_to_bv 64 (bv_unsigned sp + -96 + 96)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
match goal with H : mem_inv rsegs mF |- _ => rename H into MIF end.
apply evt_RZ_done. apply K. unfold lh_hash_post.
eexists. exists A. eexists. exists errv.
split; [unfold ret_statew; do 16 eexists; split; [reflexivity | split; [apply QCcH.fsaved_refl | intros H0; exact H0]] |].
split; [lia|]. split; [apply MREL_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST |].
split; [| split; [eassumption | split]].
+ eapply (heap_presx_of_munch S4L s4_volatile LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; exact Hb | clia |]. solve_clientW S4L HIx HP.
+ eapply (lh_glob_frame rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4 m mF); [exact G | exact MU | exact WM |].
apply Forall_cons; [cbn; unfold GHASH4, GGOT4, GVDSO4; lia | apply Forall_nil].
+ heap_now S4L HIx HP MU WM MIF.
Qed.
End LhHash.

End RC__2.
