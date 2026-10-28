(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uihm.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.


Local Ltac if_lit0 := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoNewDoubleS.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis STRDUP : strdup_stmt HIx.

#[using="Type"] Lemma fsaved_restore : forall (F F' : bvmap 5 word) (k1 k2 k3 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> bv_unsigned k1 = bv_unsigned k3 ->
fsaved (bvmap_set k1 v F) F' -> fsaved F (bvmap_set k2 (Sem.reg_get F k3) F').
Proof.
intros F F' k1 k2 k3 v E12 E13 FS j Hj.
replace k2 with k1 by (apply bv_eq; exact E12). replace k3 with k1 by (apply bv_eq; exact E13).
destruct (Z.eq_dec (bv_unsigned k1) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other by (intros E; apply NE; rewrite E; reflexivity).
rewrite (FS j Hj). apply QEpW.reg_get_set_other. intros E; apply NE; rewrite E; reflexivity.
Qed.

#[using="Type"] Lemma le8_read : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
intros segs m a v H.
pose proof (bytes_at_read segs m a (le8 v) 0 8 H ltac:(lia) ltac:(pose proof (length_le8 v); cbn; lia)) as R.
rewrite Z.add_0_r in R. cbn [skipn Z.to_nat] in R.
replace (firstn 8 (le8 v)) with (le8 v) in R. 2:{ symmetry. apply firstn_all2. rewrite length_le8. lia. }
pose proof (bytes_at_bound _ _ _ _ H) as B. unfold wa in R. exact R.
Qed.

Definition json_object_new_double_s_entry : Z := 0x26058.
Definition GOT_free_userdata : Z := 0x658c0.

Definition new_dbls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (ds lo : Z) (str : list byte)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
bytes_at rsegs m' ds (str ++ [b0]) /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, jval rsegs S4F (Sdouble true) m' BS r 1 /\ HEAPx A' (BS ++ LB) m' md') ).


#[using="STRDUP"] Lemma json_object_new_double_s_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (ds lo b n : Z) (str bytes : list byte) (errv : word),
HEAPx A LB m md ->
In (b, n) LB -> str_in_block S4L m b n bytes ds str ->
Z.of_nat (length str) + 1 <= 2^31 ->
bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 ds ->
(forall ms' md', new_dbls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB ds lo str ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_s_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP Hin SIB LEN32 GOT ST LO LOS SPA HT ERR TP RA A0 K.
destruct SIB as (BLKB & Hbds & Hdse & Hfst & NONUL). cbn [hl_segs S4L] in BLKB.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
pose proof (heap_blk S4L HIx _ _ _ _ b n HP Hin) as (Hn0 & Hbal & Hb0 & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ b n HP Hin) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (LENB : length bytes = Z.to_nat n) by (destruct BLKB as [[[Hwf _] _] _]; exact Hwf).
subst a0 tp.
assert (SRC1 : bytes_at rsegs m ds (str ++ [b0])).
{ pose proof (bytes_at_sub S4L m b bytes (Z.to_nat (ds - b)) (length str + 1) (rw_cells_bytes_at S4L _ _ _ _ BLKB) ltac:(lia)) as X.
rewrite Hfst in X. replace (b + Z.of_nat (Z.to_nat (ds - b))) with ds in X by lia. exact X. }
assert (CR : client_range S4L LB (bv_unsigned sp) ds (Z.of_nat (length str) + 1)).
{ eapply client_range_block; [exact Hin | lia | lia]. }
assert (SRCm : forall mx, heap_pres S4L LB (bv_unsigned sp) m mx -> bytes_at rsegs mx ds (str ++ [b0])).
{ intros mx HPRx. eapply (heap_pres_bytes_at S4L); [exact HPRx | exact SRC1 |]. rewrite length_app. cbn [length].
replace (Z.of_nat (length str + 1)) with (Z.of_nat (length str) + 1) by lia. exact CR. }
assert (GOTm : forall mx, heap_pres S4L LB (bv_unsigned sp) m mx -> bytes_at rsegs mx GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F)))).
{ intros mx HPRx. eapply (heap_pres_bytes_at S4L); [exact HPRx | exact GOT |]. right; left. intros a Ha.
rewrite length_le8 in Ha. cbn. unfold GOT_free_userdata in Ha. unfold s4_client_static. lia. }
clear SRC1.
assert (GOTk : True -> bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F)))) by (intros _; exact GOT). clear GOT.
apply rz_evt; [exact MOK|]. unfold json_object_new_double_s_entry.
carve_frame 32%nat ST.
do 9 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_truex. do 9 step.
apply evt_RZ_done. apply K. unfold new_dbls_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [|left; auto]]]]]].
+ apply ret_statew_intro; [apply fsaved_set_self'; reflexivity | intros Hf; exact Hf].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ exact (SRCm _ HPR).
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
assert (Hrb : r <> b) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ n HP2 Hin)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r 48 b n HP2 ltac:(left; reflexivity) ltac:(right; exact Hin) Hrb) as Hdisjrb.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in BLKB; [| eapply client_range_block; [exact Hin | lia | cbn [cells_size csize]; lia]]. cbn [hl_segs S4L] in BLKB.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_falsex.
step. step. step. ubsan_align Hal. do 5 step. stepz. stepz. stepz. stepz. stepz. stepz. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (HP3 : HEAPx A2 ((r, 48) :: LB) mcur md2) by
(eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); solve_frameW_with HP2)
end.
destruct (str_slack S4L HIx _ _ _ _ b n bytes ds str HP3 ltac:(right; exact Hin) (conj BLKB (conj Hbds (conj Hdse (conj Hfst NONUL))))) as [slack [SRC3 [PAD3 SLK3]]]. cbn [hl_segs S4L] in SRC3.
pose proof (bytes_at_bound _ _ _ _ SRC3) as Hbb3. rewrite length_app in Hbb3. cbn [length] in Hbb3.
apply evt_RZ_done. eapply STRDUP; [exact HP3 | rewrite unsigned_lit by lia; exact SRC3 | exact NONUL | rewrite unsigned_lit by lia; exact PAD3
| rewrite !unsigned_lit by lia; eapply client_range_block; [right; exact Hin | lia | lia]
| rewrite !unsigned_lit by lia; left; unfold_consts; lia | lia | .. ]; try alloc_side.
intros ms4 md4 POST4. destruct POST4 as (m4 & A4 & r2 & e4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & STR4 & OUT4). open_ret RS4. cbn [hl_segs S4L] in *.
rewrite (unsigned_lit ds) in STR4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.

assert (HPRa : heap_pres S4L LB (bv_unsigned sp) m m4).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; right; exact Hbb | clia |]. solve_clientW S4L HIx HP2.
- eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; right; exact Hbb]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI ST2 SRC3 PAD3 SLK3 Hbb3 BLKB HP3.
destruct OUT4 as [(-> & HP4) | (Hr2 & SBLK & HP4)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
reenter MOK4.
step. if_truex. step. step.

apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (LB := (r, 48) :: LB) (BS := []) (p := 0) (lo := lo);
[ cbn [app]; eapply (heap_frame S4L HIx); [exact HP4 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP4 MU); solve_frameW_with HP4
| left; split; reflexivity | .. ]; try alloc_side.
intros ms5 md5 (m5 & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP5).
destruct RS5 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR5 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m m5).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_weaken; [exact HPR5 | lia | intros bb Hbb; right; exact Hbb]. }
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU. pose proof (wmono_refl rsegs m5) as WM.
reenter MOK5.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms6 m6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR6, HP6.
extend_pres S4L HIx HPRb MU WM HP5 HPR6.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6.
pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI. cbn [hl_segs S4L] in MI.
lazymatch type of ERR6 with rw_cells _ _ _ [C4 ?e] => assert (ERR6x : rw_cells rsegs m6 490332 [C4 e]) by exact ERR6 end. clear ERR6. rename ERR6x into ERR6.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (490332, 490336)] m6) as MU. pose proof (wmono_refl rsegs m6) as WM.
reenter MOK6.
do 4 step. step. if_lit0. step. step. if_lit0. step. step. stepz. step.
do 6 step.
apply evt_RZ_done. apply K. unfold new_dbls_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A6, 0 end. eexists.
split; [| split; [| split; [| split; [ | split; [eassumption | split; [| left; split; [reflexivity|]]]]]]].
* apply ret_statew_intro; [| intros Hf; apply FRM5; exact Hf].
eapply fsaved_restore; [reflexivity | reflexivity | exact FS5].
* eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM4|]. eapply model_vm_only_trans; [exact VM5| exact VM6].
* release_frame FR ST6 (bv_unsigned sp). exact ST6.
* eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |]. solve_clientW S4L HIx HP6.
* apply SRCm. eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |]. solve_clientW S4L HIx HP6.
* eapply (heap_frame S4L HIx); [exact HP6 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP6 MU). solve_frameW_with HP6.
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as Himg_r2. cbn [hl_img_lo hl_img_hi S4L] in Himg_r2.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP4 ltac:(left; reflexivity))).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 _ r 48 HP4 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hr2r) as Hdisj2.
pose proof (GOTm _ HPRa) as GOT4. cbn [fn_free_userdata S4F] in GOT4.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
reenter MOK4.
step. if_falsex. step. step. step. if_true.
step. pose proof (le8_read rsegs _ _ _ GOT4) as RD1. step. clear RD1. step. step. stepz. stepz. stepz. step. step.
do 6 step.
apply evt_RZ_done. apply K. unfold new_dbls_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A4, r, e4 end.
split; [| split; [| split; [| split; [ | split; [exact ERR4 | split; [| right]]]]]].
* apply ret_statew_intro; [apply fsaved_set_self'; reflexivity | intros Hf; exact Hf].
* eapply model_vm_only_trans; [exact VM2| exact VM4].
* release_frame FR ST4 (bv_unsigned sp). exact ST4.
* eapply heap_pres_trans; [exact HPRa|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP4 | intros bb Hbb; right; right; exact Hbb | clia |]. solve_clientW S4L HIx HP4.
* first [exact STR4 | eapply (bytes_at_transport rsegs); [exact STR4 | exact MU |]; cbn; rewrite length_app; cbn [length]; unfold_consts; lia].
* split; [exact Hr|]. exists [(r, 48); (r2, Z.of_nat (length str) + 1)]. split.
-- jhdr_split BLK.
cbn [jval]. exists 0, [], [(r, 48); (r2, Z.of_nat (length str) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Sem.reg_get F (Z_to_bv 5 10)), r2, (Z.of_nat (length str) + 1), str. split; [reflexivity|]. split; [lia|]. split.
++ unfold jhdr_cells. cbn [fn_ud_to_json_string fn_free_userdata S4F app]. exact BLK.
++ unfold cstr. split; [lia|]. split.
** apply Forall_forall. intros x Hx E0. apply NONUL. apply bv8_zero_iff in E0. subst x. exact Hx.
** exists []. rewrite app_nil_r. unfold b0 in SBLK. exact SBLK.
-- eapply (heap_frame S4L HIx); [ eapply heap_perm; [exact HP4 | apply perm_swap] | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ (heap_perm _ _ _ _ _ _ _ HP4 (perm_swap _ _ _)) MU). solve_frameW_with HP4.
Qed.
End JoNewDoubleS.

End RC__1.
