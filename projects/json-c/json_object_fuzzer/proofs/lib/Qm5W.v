(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKdB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKdB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmd7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg1M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.  From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvPk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvPk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoObjAdd.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.

Definition INSERT := lh_insert_A_full HIx LF OBL_AMEMSET (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) (fun a => model_vm_only_refl (cfg_model a)) (fun a b c => model_vm_only_trans (cfg_model a) (cfg_model b) (cfg_model c)) (fun a b H => H) HD HD_ge HASH.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB VBS PBS LM : list blk) (FRS : list frame) (B0 : bud) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (80 + 96 + 4096 + 144 + HD).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis INK : In (k, kn) LB.
Hypothesis KN : kn <= 2^31.
Hypothesis FRM : frm0 fc.
Hypothesis FRN : Z.of_nat (length FRS) < 4096.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.

Hypothesis BB0 : oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B0.
Hypothesis BR0 : 512 * (3 + Z.of_nat (length es) + Z.of_nat (length (concat KBS)) + Z.of_nat (length PBS)) <= bB B0.
Hypothesis BD0 : 0 <= bD B0.

Definition OBS : list blk := ((p, 48) :: lh_blocks t tbl size es ++ concat KBS) ++ PBS.

Definition OHDR : list cell :=
[C4 (Z_to_bv 64 JT_OBJECT); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (fn_obj_to_json_string A4F)); C8 (Z_to_bv 64 pb); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 t)].
Definition oadd_frameA (junk0 : list byte) (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation SB0 := 2147450880.

Hypothesis Kont : forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B0 <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( ( Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA size (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ ( Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B0 - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = size
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms'.

Lemma oadd_factsX : forall A B m md LIST REST,
HEAPAx A LIST LM FRS B m md -> Permutation LIST (lh_blocks t tbl size es ++ (p, 48) :: REST) ->
(p mod 16 = 0 /\ 0 < p /\ p + 48 <= alloc_ceiling /\ (p + 48 <= 0x10000 \/ 0x647000 <= p)) /\
(t mod 16 = 0 /\ 0 < t /\ t + 56 <= alloc_ceiling /\ (t + 56 <= 0x10000 \/ 0x647000 <= t)) /\
(tbl mod 16 = 0 /\ 0 < tbl /\ tbl + 40 * size <= alloc_ceiling /\ (tbl + 40 * size <= 0x10000 \/ 0x647000 <= tbl)) /\
(t + 56 <= tbl \/ tbl + 40 * size <= t) /\ (p + 48 <= t \/ t + 56 <= p) /\ (p + 48 <= tbl \/ tbl + 40 * size <= p) /\
(forall e, In e es -> 0 <= le_kn e /\ 0 < le_k e /\ le_k e + le_kn e <= alloc_ceiling /\
(t + 56 <= le_k e \/ le_k e + le_kn e <= t) /\ (tbl + 40 * size <= le_k e \/ le_k e + le_kn e <= tbl)).
Proof.
clear Kont LO LOS SPA HT RA INK KN FRM LK1 LK2 BB0 BR0 BD0. intros A B m md LIST REST HP0 PERM.
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP0 PERM (Permutation_refl _) (Permutation_refl _)) as HP. clear HP0 PERM.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg.
unfold lh_blocks in HP. cbn [app] in HP.
assert (INp : In (p, 48) (((t, 56) :: (tbl, 40 * size) :: map (fun e => (le_k e, le_kn e)) es ++ (p, 48) :: REST) ++ LM))
by (apply in_or_app; left; right; right; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p 48 HP INp) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_r in ND.
cbn in ND. rewrite map_app in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst.
assert (Hpt : p <> t) by (intros E; apply Hni; right; apply in_or_app; right; left; exact E).
assert (Hpb : p <> tbl) by (intros E; apply Hni'; apply in_or_app; right; left; exact E).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 t 56 HP INp ltac:(apply in_or_app; left; left; reflexivity) Hpt) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 tbl (40 * size) HP INp ltac:(apply in_or_app; left; right; left; reflexivity) Hpb) as D2.
split; [repeat split; assumption|]. split; [repeat split; assumption|]. split; [repeat split; assumption|].
split; [exact SEP|]. split; [exact D1|]. split; [exact D2|].
intros e He. destruct (KF e He) as (K0 & K1 & K2 & _ & K4 & K5). repeat (split; [assumption|]). exact K5.
Qed.

Lemma oadd_pvX : forall A B m md LIST REST,
HEAPAx A LIST LM FRS B m md -> Permutation LIST ((p, 48) :: VBS ++ REST) -> jopt asegs A4F vs m VBS v ->
p <> v /\ 0 <= v /\ v + 1 <= alloc_ceiling.
Proof.
clear Kont LO LOS SPA HT RA INK KN FRM LK1 LK2 BB0 BR0 BD0. intros A B m md LIST REST HP0 PERM JOB.
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP0 PERM (Permutation_refl _) (Permutation_refl _)) as HP. clear HP0 PERM.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Hplo & Hphi & _).
destruct vs as [s'|]; cbn in JOB.
- destruct JOB as [Hv J]. destruct (jval_root_in asegs A4F _ _ _ _ _ J) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & Hvlo & Hvhi & _).
split; [| lia]. intros E. subst v.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_r in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_or_app; left. exact (in_map blk_addr _ _ Hin).
- destruct JOB as [-> _]. pose proof alloc_ceiling_ge. lia.
Qed.

Lemma oadd_keyX : forall A B LBX m md, HEAPAx A LBX LM FRS B m md -> In (k, kn) LBX -> cstr asegs m k kn ks ->
bytes_at asegs m k (ks ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) ks /\ Z.of_nat (length ks) + 1 <= kn /\ 0 < k /\ k + kn <= alloc_ceiling /\ k mod 16 = 0.
Proof.
clear Kont LO LOS SPA HT RA INK FRM LK1 LK2 BB0 BR0 BD0. intros A B LBX m md HP Hin (CL & CNZ & junk & CB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ k kn HP ltac:(apply in_or_app; left; exact Hin)) as (Hn0 & Hal & Hlo & Hhi & _).
assert (NN : ~ In (Z_to_bv 8 0) ks) by (intros X; rewrite Forall_forall in CNZ; apply (CNZ _ X); reflexivity).
assert (BB : bytes_at asegs m k ((ks ++ [Z_to_bv 8 0]) ++ junk)).
{ destruct CB as [[[_ _] HB] _]. cbn in HB. rewrite app_nil_r in HB. rewrite <- app_assoc. exact HB. }
apply bytes_at_app in BB as [BB _].
split; [exact BB|]. split; [exact NN|]. split; [exact CL|]. split; [exact Hlo|]. split; [exact Hhi| exact Hal].
Qed.

Lemma oadd_len_new : forall tbl' size' es' (e : lent),
length es' = length es ->
Z.of_nat (length (((p, 48) :: lh_blocks t tbl' size' (es' ++ [e]) ++ concat (KBS ++ [VBS])) ++ PBS))
= Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1.
Proof.
clear. intros tbl' size' es' e LEN'. unfold OBS, lh_blocks. cbn [app length].
rewrite !length_app. cbn [length].
rewrite !length_map, length_app, concat_app, length_app. cbn [length concat]. rewrite app_nil_r, LEN'. lia.
Qed.
Lemma obj_capA_lh : forall tbl' size' es'' rest, 0 <= size' -> obj_capA (((p, 48) :: lh_blocks t tbl' size' es'' ++ rest) ++ PBS) = size'.
Proof. clear. intros. unfold obj_capA, lh_blocks. cbn [app nth snd]. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
Lemma obj_grownA_of : forall size' cap',
16 <= size -> cap' = size' -> size' = (if lf_thr size <=? Z.of_nat (length es) then lh_ns size else size) ->
obj_grownA size (Z.of_nat (length kids)) cap'.
Proof.
clear - LK1. intros size' cap' Hs -> E. unfold obj_grownA. rewrite LK1 in E.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length kids))); [right | left]; split; lia.
Qed.

Lemma oadd_insA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : config) (A2 : ASA A4L HIx) (h : Z) (errc : word) (svs : list slotv) (junk0 : list byte),
HEAPAx A2 (OBS ++ VBS ++ LB) LM FRS B0 mc mdc ->
rw_cells asegs mc p OHDR ->
lh_open asegs A4F mc t tbl size es svs ->
okids asegs A4F mc kids (map kv es) KBS -> opt_pbuf asegs mc PBS pb -> jopt asegs A4F vs mc VBS v ->
cstr asegs mc k kn ks -> lh_globA mc ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
stk asegs mc lo (bv_unsigned sp + -80) ->
oadd_frameA junk0 mc ->
model_vm_only (cfg_model md0) (cfg_model mdc) -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc ->
fsaved F F2 -> frm0 fc2 -> 0 <= h < 2^64 ->
AJ5 A4L HIx A2 T mdc
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 v) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 k) (Z_to_bv 64 (p + 40)) (Z_to_bv 64 p) (Z_to_bv 64 h) (Z_to_bv 64 (p / 8 + 5 + SB0)) (Z_to_bv 64 SB0) s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x9d760) fc2 None mc (seg_rom asegs)).
Proof.
intros until junk0. intros HP HDR OPEN KIDS OPB JOB CS G ERR ST FR VMa HPRa FSa FRMa Hh.
unfold oadd_frameA in FR. unfold OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG.
destruct (oadd_factsX _ _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold OBS; perm)) as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvX _ _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold OBS; perm) JOB) as (Hpv & V0 & V1).
assert (INK' : In (k, kn) (OBS ++ VBS ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact INK).
destruct (oadd_keyX _ _ _ _ _ HP INK' CS) as (STR & NN & KL & KPOS & KHI & KAL).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ k kn HP ltac:(apply in_or_app; left; exact INK')) as Hkimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg.
pose proof (bytes_at_bound _ _ _ _ STR) as KB. rewrite length_app in KB. cbn [length] in KB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
assert (INp : In (p, 48) (OBS ++ VBS ++ LB)) by (unfold OBS; cbn; left; reflexivity).
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen). pose proof (lf_size_range size Hsz) as HSR.
assert (INSNN : 0 <= ins_costB size (Z.of_nat (length kids))).
{ clear - HSR. unfold ins_costB, resize_costB, lh_ns. destruct (lf_thr size <=? Z.of_nat (length kids)); [destruct (size <=? 2 ^ 29); lia | lia]. }
assert (BBs : strdup_costB (Z.of_nat (length ks)) <= bB B0) by (unfold oadd_costB in BB0; lia).
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash KF. stash SEP. stash D1. stash D2.
reenterA asegs A4L HIx asegs_wx HP.
step. step. if_false.
step. step.

evt_done5.
eapply (hiA_strdup A4L HIx) with (LB := OBS ++ VBS ++ LB) (ab := k) (nb := kn) (src := k) (str := ks) (lo := lo) (u := UWptr);
[ heap_nowA A4L HIx HP MU WM MI | exact INK' | lia | lia | exact STR | exact NN | lia | .. ];
a4l_goal; rewrite ?unsigned_lit by lia;
first [ exact ST | exact LO | exact ERR | exact BBs | reflexivity | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; lia]
| solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat (first [left; reflexivity | right])]
| solve [cbn [uw_cost]; lia] | lia | idtac ].
intros ms4 m4 md4 A4 r2 e4 RS4 VM4 ST4 HPR4 ERR4 OUT4. open_ret RS4. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST4, HPR4 by lia.
unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash CS.
assert (AG4 : agree_on asegs (OBS ++ VBS ++ LB) mc m4).
{ eapply (agree_of_heap_pres asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_pres_weaken; [exact HPR4 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m4).
{ eapply heap_presx_trans; [exact HPRa|]. apply heap_pres_presx.
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; exact Hb | right; exact Hb]]. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
apply (rw_cells_agree asegs _ _ _ _ _ HDR) in AG4 as HDR4; [| exists p, 48; split; [exact INp | cbn; lia]].
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN AG4 ltac:(unfold OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN4.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDS AG4 ltac:(unfold OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS4.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AG4 ltac:(unfold OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB4.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AG4 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB4.
pose proof (lh_globA_client _ _ _ _ HPR4 G) as G4.
clear MU WM MI HDR OPEN KIDS OPB JOB G ST STR.
destruct OUT4 as [(-> & He4 & HP4) | (Hr2 & NEWK & HP4)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [] m4) as MU.
stash OPEN4. stash KIDS4. stash OPB4. stash JOB4.
reenterA asegs A4L HIx asegs_wx HP4.
step. step. if_true. step. do 9 step. step.
release_frame FR ST4 (bv_unsigned sp). step.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
unstash OPEN4. unstash KIDS4. unstash OPB4. unstash JOB4.
lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?Bx _ _ => apply (Kont _ md4 m4 (2^64 - 1) A4 Bx) end.
+ unfold jo_post_framexA. a4l_goal.
split; [apply ret_statew_intro; [exact FSa | intros _; exact FRMa] |].
split; [eapply model_vm_only_trans; [exact VMa | exact VM4] |].
split; [exact ST4 |].
split; [exact HPRb | exists e4; exact ERR4].
+ exact G4.
+ cbn [bD charge uw_cost]. lia.
+ right. split; [reflexivity|]. exists [].
split; [| split; [exact JOB4 | split; [cbn [app]; exact HP4 | cbn [bB charge]; unfold oadd_costB, strdup_costB; lia]]].
eapply (sobj_close asegs A4F) with (TBS := lh_blocks t tbl size es) (kvs := map kv es);
[ reflexivity | exact OPB4 | unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR4
| exists tbl, size, es, svs; split; [reflexivity | split; [reflexivity | exact OPEN4]]
| rewrite length_map; exact LK1 | exact LK2 | exact KIDS4 ].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r2 _ HP4 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & Hr2wr).
cbn [hl_segs hla_base A4L A4H] in Hr2wr.
assert (INp4 : In (p, 48) ((r2, Z.of_nat (length ks) + 1) :: OBS ++ VBS ++ LB)) by (right; exact INp).
shadow_inA A4L HIx HP4 INp4 SHp. a4l.
pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [] m4) as MU.
stash OPEN4. stash KIDS4. stash OPB4. stash JOB4. stash NEWK.
reenterA asegs A4L HIx asegs_wx HP4.
step. step. if_falsex.
step. rewrite ?zxb_zero. step. if_false.
step.
step. step. step. step.
do 9 step. step.
unstash OPEN4. unstash KIDS4. unstash OPB4. unstash JOB4. unstash NEWK.
release_frame FR ST4 (bv_unsigned sp).
step.
assert (CS4 : cstr asegs m4 r2 (Z.of_nat (length ks) + 1) ks).
{ split; [lia|]. split; [exact (proj1 (proj2 CS))|]. exists []. rewrite app_nil_r.
pose proof (bytes_at_bound _ _ _ _ NEWK) as NB. rewrite length_app in NB. cbn [length] in NB.
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; exact NEWK] |].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (Z.of_nat (length ks) + 1) + 0)) with (Z.of_nat (length ks) + 1) by lia. exact Hr2wr. }
lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?Bx _ _ => assert (BBi : ins_costB size (Z.of_nat (length es)) <= bB Bx) end.
{ cbn [bB charge]. unfold oadd_costB, strdup_costB in BB0. rewrite LK1. lia. }
evt_done5.
eapply INSERT with (LB := (p, 48) :: concat KBS ++ PBS ++ VBS ++ LB) (t := t) (tbl := tbl) (size := size) (es := es) (svs := svs)
(k := r2) (kn := Z.of_nat (length ks) + 1) (ks := ks) (v := v) (h := h) (lo := lo) (errv := e4);
a4l_goal; rewrite ?unsigned_lit by lia;
first [ eapply (heapA_perm A4L HIx); [exact HP4 | unfold OBS; perm | apply Permutation_refl | apply Permutation_refl]
| exact OPEN4 | exact G4 | exact CS4 | exact ST4 | exact ERR4 | exact RA | exact FRMa | exact BBi | reflexivity | lia
| solve [cbn [bD charge uw_cost]; lia] | idtac ].
intros ms5 md5 A5 (mF & r5 & e5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & G5 & BB5 & BD5 & OUT5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
set (LBI := (p, 48) :: concat KBS ++ PBS ++ VBS ++ LB) in *.
assert (AG5 : agree_on asegs LBI m4 mF).
{ eapply (agree_of_heap_presx asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_presx_weaken; [exact HPR5 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb | intros a' Ha'; exact Ha']. }
assert (HiK : incl (concat KBS) LBI) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
apply (rw_cells_agree asegs _ _ _ _ _ HDR4) in AG5 as HDR5; [| exists p, 48; split; [left; reflexivity | cbn; lia]].
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDS4 AG5 HiK) as KIDS5.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB4 AG5 HiP) as OPB5.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB4 AG5 HiV) as JOB5.
apply (Kont _ md5 mF r5 A5 B5).
+ unfold jo_post_framexA. a4l_goal.
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FSa | exact FS5] | intros _; apply FRM5; exact FRMa] |].
split; [eapply model_vm_only_trans; [exact VMa | eapply model_vm_only_trans; [exact VM4 | exact VM5]] |].
split; [exact ST5|].
split; [| exists e5; exact ERR5].
eapply heap_presx_trans; [exact HPRb|]. eapply heap_presx_weaken; [exact HPR5 | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply HiL; exact Hb | right; exact Hb].
+ exact G5.
+ cbn [bD charge uw_cost] in BD5. lia.
+ destruct OUT5 as [(-> & OPEN5 & CS5 & HP5) | (-> & tbl' & size' & es' & svs' & g & STRIP & OPEN5 & HP5 & SZ')].
*
right. split; [reflexivity|]. exists [(r2, Z.of_nat (length ks) + 1)]. split; [| split; [exact JOB5 | split]].
-- eapply (sobj_close asegs A4F) with (TBS := lh_blocks t tbl size es) (kvs := map kv es);
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR5
| exists tbl, size, es, svs; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map; exact LK1 | exact LK2 | exact KIDS5 ].
-- eapply (heapA_perm A4L HIx); [exact HP5 | unfold LBI, OBS; perm | apply Permutation_refl | apply Permutation_refl].
-- cbn [bB charge] in BB5. unfold oadd_costB, strdup_costB. rewrite LK1 in BB5. lia.
*
left. split; [reflexivity|].
exists (((p, 48) :: lh_blocks t tbl' size' (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks v]) ++ concat (KBS ++ [VBS])) ++ PBS), (kids ++ [vs]).
assert (LEN' : length es' = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
split; [| split; [| split; [| split]]].
-- eapply (sobj_close asegs A4F) with (kvs := map kv (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks v]));
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR5
| exists tbl', size', (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks v]), svs'; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map, !length_app, (strip_length _ _ STRIP); cbn [length]; lia
| rewrite !length_app; cbn [length]; lia
| rewrite map_app, (strip_kv _ _ STRIP); cbn [map]; apply okids_app; [exact KIDS5 | apply okids_one; unfold kv; cbn [le_v]; exact JOB5] ].
-- rewrite concat_app. cbn [concat]. rewrite app_nil_r. eapply (heapA_perm A4L HIx); [exact HP5 | unfold LBI; perm | apply Permutation_refl | apply Permutation_refl].
-- rewrite length_app. cbn [length]. lia.
-- rewrite okmax_app, okmax_single. pose proof (okmax_nonneg kids). pose proof (odep_nonneg vs). lia.
-- left. split; [rewrite length_app; cbn [length]; lia|]. split; [cbn [bB charge] in BB5; unfold oadd_costB, strdup_costB; rewrite LK1 in BB5; lia|].
split; [apply oadd_len_new; exact LEN'|].
pose proof OPEN5 as (_ & _ & _ & _ & Hsz5 & _). pose proof (lf_size_range size' Hsz5).
split; [eapply obj_grownA_of; [lia | apply obj_capA_lh; lia | exact SZ'] |].

intros w wv Hw Hwv. unfold OBS, lh_blocks in Hw. unfold lh_blocks. rewrite map_app. cbn [map le_k le_kn].
assert (EKEYS : map (fun e0 : lent => (le_k e0, le_kn e0)) es' = map (fun e0 : lent => (le_k e0, le_kn e0)) es).
{ pose proof (f_equal (map (fun x : Z * Z * list byte * Z => (fst (fst (fst x)), snd (fst (fst x))))) STRIP) as E. rewrite !map_map in E. exact E. }
rewrite EKEYS.
exact (obj_add_jtx asegs A4F mF kids (map kv es) KBS PBS (p, 48) (t, 56) (tbl, 40 * size) (tbl', 40 * size') (r2, Z.of_nat (length ks) + 1)
(map (fun e0 : lent => (le_k e0, le_kn e0)) es) vs VBS w wv KIDS5 ltac:(rewrite length_map; exact LK1) Hw Hwv).
Qed.
End AJoObjAdd.
End RC__1.
