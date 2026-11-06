(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKY2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXDj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXDj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q25t. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNDM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7DP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7DP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHqi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHqi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi08.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6w1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6w1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWwJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWwJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4I1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4I1.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac inl := first [solve [cbn; repeat first [left; reflexivity | right]; reflexivity] | cbn; tauto].
Import QWRO(aentry, mkAE, ae_sp0, ae_stack_top, ae_fs_base, ae_L, ae_stack_bottom, ff_size)
QFQR(rlay, mkRL, rl_T, rl_ctx, rl_dn, rl_ssb, rl_dtls, A_FS_MAP_SIZE)
QKBN(hjunk)
QsJM(RFake, fs_shape, kFsClasses, fs_N, fs_foff, fs_flag, fs_frame, fs_hint, fs_area_lo, fs_area_hi, flags_of, live_b, fs_N_pos, fs_foff_range, flags_of_length)
QV3O(RDepot, SS_BASE, DP_TAB, DP_MAP1, bkt, zseq, lastb).
Import QWRO(DP_N, DEPOT_CAP).
Set Default Proof Using "All".
Local Ltac inw := (apply OBJS_common; first [solve [cbn; repeat first [left; reflexivity | right]] | cbn; tauto]).

Local Notation wz := (Z_to_bv 64).

Definition E_PG (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).
Definition E_SHPG (v : nat) : expr := EMd Instr.M_MUL (ELit 512) (EVar v).

Definition FAKE_FACTS : list kentry :=
[ KWord (SA (E_PG 406) 88) 8 (ELit 20); KZero (SA (E_PG 406) 96) (ELit 11571104); KZero (SA (E_PG 406) 0) (ELit 88);
KWr (SA (E_PG 406) 0) (ELit 11571200);
KZero (SA (E_SHPG 406) 0x7fff8000) (ELit 1446400); KRange (EVar 406) 1 34359733495 ].
Definition fake_checks (k : list kentry) : bool := kn_has_all FAKE_FACTS k.
Lemma FAKE_CHECKS : forall w ch, HSCLASS_S w ch -> fake_checks (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section DepotFacts.
Variables (tf h0 : Z).
Let cell : Z := DP_TAB + 4 * bkt h0.

Definition DEPOT_FACTS : list kentry :=
[ KWord (SA (ELit 0) 0x5d40a8) 8 (E_PG 478); KWord (SA (ELit 0) 0x1c4098) 8 (E_PG 479);
KWord (SA (E_PG 478) 16) 8 (ELit h0); KWord (SA (E_PG 478) 24) 4 (ELit 0); KWord (SA (E_PG 478) 28) 4 (ELit 1);
KZero (SA (E_PG 478) 32) (ELit 1048544); KWr (SA (E_PG 478) 0) (ELit 1048576);
KWr (SA (E_PG 479) 0) (ELit 8388608);
KWord (SA (E_PG 237) 3168) 1 (ELit 0); KWr (SA (E_PG 237) 0) (ELit 4096);
KImg 0x1c40a8 cell; KImg (cell + 4) 0x5d4098;
KRange (EVar 237) 1 34359736319; KRange (EVar 478) 1 34359736064; KRange (EVar 479) 1 34359734272 ].

Definition depot_checks (k : list kentry) : bool :=
kn_has_all DEPOT_FACTS k
&& kn_rw_cells k SS_BASE [C8 (wz tf); C8 (wz 0x800000)] && img_wn 0x1c4098 8 && kn_rw_cells k 0x1c40a0 [C4 (wz tf)]
&& kn_rw_cells k cell [C4 (wz 1)] && kn_rw_cells k DP_N [C4 (wz 1)] && img_wn 0x5d40a8 8
&& img_zero DP_TAB (4 * bkt h0) && img_zero (cell + 4) (0x5d4098 - cell - 4)
&& (0 <=? tf) && (tf <=? 6) && (0 <=? h0) && (h0 <? 2^64).
End DepotFacts.

Lemma DEPOT_CHECKS : forall w ch, HSCLASS_S w ch -> exists tf h0, depot_checks tf h0 (kn_view ch) = true.
Proof.
intros [|] ch [-> | ->].
- exists 3, 0x60133795861b14d8. vm_compute. reflexivity.
- exists 2, 0x2b43f9992ae5842b. vm_compute. reflexivity.
- exists 3, 0x60133795861b14d8. vm_compute. reflexivity.
- exists 2, 0x2b43f9992ae5842b. vm_compute. reflexivity.
Qed.

Lemma flags_of_nil_zero : forall FS c, forallb zbyteb (flags_of [] FS c) = true.
Proof.
intros FS c. unfold flags_of. apply forallb_forall. intros x Hx. apply in_map_iff in Hx as (i & <- & _). reflexivity.
Qed.

Lemma zcells_CB : forall bs, forallb zbyteb bs = true -> zcells [CB (length bs) bs] = true.
Proof. intros bs H. cbn [zcells zcell]. rewrite Nat.eqb_refl, H. reflexivity. Qed.

Lemma u8arr_of_rw_CB : forall m a bs, rw_cells asegs m a [CB (length bs) bs] -> u8arr asegs m a bs.
Proof.
intros m a bs [[WF BA] WR]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
split; [exact BA| exact WR].
Qed.

Lemma zero_range_C4 : forall m a n b, wr_at asegs m a n -> (forall i, 0 <= i < n -> bytes_at asegs m (a + i) [Z_to_bv 8 0]) ->
a <= b -> b + 4 <= a + n -> rw_cells asegs m b [C4 (Z_to_bv 64 0)].
Proof.
intros m a n b (W1 & W2 & W) BY H1 H2. split; [split; [inl|]|].
- cbn [cells_bytes cbytes app le4]. change (le4 (Z_to_bv 64 0) ++ []) with [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
destruct (BY (b - a + Z.of_nat i) ltac:(lia)) as (_ & _ & B0). specialize (B0 0%nat ltac:(cbn; lia)). cbn [nth_error] in B0. change (Z.of_nat 0) with 0 in B0.
replace (a + (b - a + Z.of_nat i) + 0) with (b + Z.of_nat i) in B0 by lia. rewrite B0.
destruct i as [|[|[|[|i]]]]; try reflexivity. lia.
- split; [lia|]. split; [cbn [cells_size csize Nat.add]; lia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
replace (b + i) with (a + (b - a + i)) by lia. apply W. lia.
Qed.

Lemma ro_rw : forall m a cs, ro_cells asegs m a cs -> wr_at asegs m a (Z.of_nat (cells_size cs)) -> rw_cells asegs m a cs.
Proof. intros m a cs RO WR. split; [exact RO| exact WR]. Qed.

Section D.
Context {BAND : Band}.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Hypothesis HB : band_lo = atopE E.
#[local] Notation m := (view (LV_J E) mo FULL).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB) (only parsing).

Let KO : know_ok asegs E m (kn_view ch) := MV4 main_know_view.

Lemma objf : forall v len, In (v, len) (OBJS_W w) ->
pg E v mod 4096 = 0 /\ 0 < pg E v /\ appr (pg E v) len /\ pg E v + len <= band_lo.
Proof.
intros v len Ho. pose proof ((LA obj_facts) (v, len) Ho) as (F1 & F2 & F3 & F4 & F5 & F6). cbn [fst snd] in *.
unfold pg. rewrite HB. split; [exact F1|]. split; [exact F2|]. split; [split; [|exact F5]|exact F6].
destruct F4 as [F4|F4]; [left; lia| right; exact F4].
Qed.

Theorem RFake_main : RFake [] (RE_main sp w E) (X_main E) m.
Proof.
pose proof (FAKE_CHECKS w ch HCL) as CK.
assert (ffact : forall K, kn_has K FAKE_FACTS = true -> kn_has K (kn_view ch) = true).
{ intros K HK. unfold fake_checks, kn_has_all in CK. rewrite forallb_forall in CK. apply CK. apply kn_has_In. exact HK. }
pose proof (kn_range_var E m (kn_view ch) KO 406 _ _ (ffact (KRange (EVar 406) 1 34359733495) eq_refl)) as B.
pose proof (objf 406%nat 11571200 ltac:(inw)) as (O1 & O2 & O3 & O4). destruct O3 as [LH OH].
assert (HI : 0x647000 <= pg E 406) by (unfold pg in *; lia).
unfold RFake. change (ae_fs_base (RE_main sp w E)) with (pg E 406). cbv zeta.
set (FS := pg E 406) in *.
pose proof (kn_zero_rw E m (kn_view ch) KO (E_PG 406) 0 88 FS (ffact (KZero (SA (E_PG 406) 0) (ELit 88)) eq_refl) eq_refl ltac:(lia) ltac:(lia)) as Z88.
pose proof (kn_zero_rw E m (kn_view ch) KO (E_PG 406) 96 11571104 FS (ffact (KZero (SA (E_PG 406) 96) (ELit 11571104)) eq_refl) eq_refl ltac:(lia) ltac:(lia)) as ZB.
pose proof (kn_zero_some E m (kn_view ch) KO (E_PG 406) 96 11571104 FS (ffact (KZero (SA (E_PG 406) 96) (ELit 11571104)) eq_refl) eq_refl ltac:(lia) ltac:(lia)) as ZS.
pose proof (kn_zero_some E m (kn_view ch) KO (E_SHPG 406) 0x7fff8000 1446400 (512 * bv_unsigned (ev E 406)) (ffact (KZero (SA (E_SHPG 406) 0x7fff8000) (ELit 1446400)) eq_refl) eq_refl ltac:(lia) ltac:(lia)) as ZSH.
pose proof (kn_word E m (kn_view ch) (E_PG 406) 88 8 (ELit 20) FS 20 KO (ffact (KWord (SA (E_PG 406) 88) 8 (ELit 20)) eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as K88.
cbn [wcell] in K88.
unfold A_FS_MAP_SIZE, kFsClasses in *.
split; [exact O1|]. split; [split; [exact LH| exact OH]|]. split; [exact O4|].
split; [split; [intros f []| constructor]|].
split; [exact K88|].
split; [apply ZB; [reflexivity| lia| lia| cbn; lia]|].
split. { intros c Hc. exists (wz 0). unfold fs_hint. apply Z88; [reflexivity| cbn [cells_size csize Nat.add]; lia| lia| cbn [cells_size csize Nat.add]; lia]. }
split. { intros c Hc. pose proof (fs_foff_range c Hc) as FR. pose proof (fs_N_pos c Hc) as NP. change (2^15) with 32768 in FR. unfold fs_flag.
apply u8arr_of_rw_CB. apply ZB; [apply zcells_CB; apply flags_of_nil_zero| cbn [cells_size csize Nat.add]; rewrite flags_of_length; lia| lia|].
cbn [cells_size csize Nat.add]. rewrite flags_of_length. lia. }
split; [intros c pos [] _|].
unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE. split.
- split; [lia|]. split; [lia|]. intros a Ha. apply ZS. lia.
- unfold SH, A_SHADOW_OFS. split; [right; Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
intros a Ha. apply ZSH. unfold FS, pg in Ha. Z.div_mod_to_equations. lia.
Qed.

Theorem RDepot_main : RDepot (RE_main sp w E) (X_main E) m.
Proof.
destruct (DEPOT_CHECKS w ch HCL) as (tf & h0 & CK).
assert (dfact : forall i K, nth_error (DEPOT_FACTS h0) i = Some K -> kn_has K (kn_view ch) = true).
{ intros i K HK. pose proof CK as C. unfold depot_checks in C. do 12 (apply andb_prop in C as [C _]).
unfold kn_has_all in C. rewrite forallb_forall in C. apply C. eapply nth_error_In. exact HK. }
pose proof CK as C. unfold depot_checks in C.
apply andb_prop in C as [C H4]. apply andb_prop in C as [C H3]. apply andb_prop in C as [C H2]. apply andb_prop in C as [C H1].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
apply andb_prop in C as [C IZ2]. apply andb_prop in C as [C IZ1]. apply andb_prop in C as [C W58]. apply andb_prop in C as [C CN].
apply andb_prop in C as [C CBK]. apply andb_prop in C as [C C60]. apply andb_prop in C as [C W48]. apply andb_prop in C as [_ C38].
pose proof (kn_range_var E m (kn_view ch) KO 237 _ _ (dfact 12%nat _ eq_refl)) as B240.
pose proof (kn_range_var E m (kn_view ch) KO 478 _ _ (dfact 13%nat _ eq_refl)) as B486.
pose proof (kn_range_var E m (kn_view ch) KO 479 _ _ (dfact 14%nat _ eq_refl)) as B487.
pose proof (objf 478%nat 1048576 ltac:(inw)) as (D1 & D2 & D3 & D4).
pose proof (objf 479%nat 8388608 ltac:(inw)) as (S1 & S2 & S3 & S4).
pose proof (objf 237%nat 4096 ltac:(inw)) as (T1 & T2 & T3 & T4).
unfold RDepot.
change (rl_dn (X_main E)) with (pg E 478). change (rl_ssb (X_main E)) with (pg E 479). change (rl_T (X_main E)) with (pg E 237).
assert (AD : appr_lia (pg E 478) 1048576) by (apply appr_to_lia; [lia| unfold pg in *; lia| exact D3]).
assert (AS' : appr_lia (pg E 479) 8388608) by (apply appr_to_lia; [lia| unfold pg in *; lia| exact S3]).
assert (AT : appr_lia (pg E 237) 4096) by (apply appr_to_lia; [lia| unfold pg in *; lia| exact T3]).
assert (HDN : 0x647000 <= pg E 478) by (destruct D3 as [_ [X|X]]; unfold pg in *; lia).
assert (HSS : 0x647000 <= pg E 479) by (destruct S3 as [_ [X|X]]; unfold pg in *; lia).
set (DN := pg E 478) in *. set (SSB := pg E 479) in *. set (T := pg E 237) in *.
exists 1, tf, tf, h0, 0x800000, (fun _ => h0), (fun _ => 1).
split; [lia|]. split; [lia|]. split; [lia|].
split; [intros i Hi; split; [unfold DEPOT_CAP; lia| lia]|].
split; [cbn; constructor; [intros []| constructor]|].
split; [unfold DN, pg; rewrite Z.mul_comm; change 4096 with (256 * 16); rewrite Z.mul_assoc; apply Z.mod_mul; lia|]. split; [exact AD|]. split; [lia|].
split; [unfold SSB, pg; rewrite Z.mul_comm; change 4096 with (512 * 8); rewrite Z.mul_assoc; apply Z.mod_mul; lia|]. split; [exact AS'|]. split; [lia|].
split; [exact AT|]. split; [lia|].
split.
{
apply (proj2 (rw_cells_app asegs m SS_BASE [C8 (wz tf); C8 (wz 8388608)] _)). split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C38)|].
cbn [cells_size csize Nat.add]. unfold SS_BASE.
pose proof (kn_word E m (kn_view ch) (ELit 0) 0x1c4098 8 (E_PG 479) 0 SSB KO (dfact 1%nat _ eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as K58.
cbn [wcell Z.add] in K58.
apply (proj2 (rw_cells_app asegs m _ [C8 (wz SSB)] _)). split.
- apply ro_rw; [exact K58|]. apply img_wn_wr_at; [exact W48| lia| cbn; lia].
- cbn [cells_size csize Nat.add]. exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C60). }
split.
{
intros b Hb. change (lastb (fun _ => h0) b (Z.to_nat 1)) with (if bkt h0 =? b then 1 else 0).
assert (BK : 0 <= bkt h0 < 2^20) by (unfold bkt; change 1048575 with (Z.ones 20); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound h0 (2^20) ltac:(lia)); lia).
destruct (Z.eqb_spec (bkt h0) b) as [<-|NE]; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO CBK)|].
destruct (Z.lt_ge_cases b (bkt h0)).
- destruct (kimg_zero_bytes E m (kn_view ch) KO 0x1c40a8 (DP_TAB + 4 * bkt h0) DP_TAB (4 * bkt h0) (dfact 10%nat _ eq_refl) ltac:(unfold DP_TAB; lia) ltac:(lia) IZ1) as [WR BY].
apply (zero_range_C4 m DP_TAB (4 * bkt h0)); [exact WR| exact BY| lia| lia].
- destruct (kimg_zero_bytes E m (kn_view ch) KO (DP_TAB + 4 * bkt h0 + 4) 0x5d4098 (DP_TAB + 4 * bkt h0 + 4) (0x5d4098 - (DP_TAB + 4 * bkt h0) - 4)
(dfact 11%nat _ eq_refl) ltac:(lia) ltac:(lia) IZ2) as [WR BY].
apply (zero_range_C4 m (DP_TAB + 4 * bkt h0 + 4) (0x5d4098 - (DP_TAB + 4 * bkt h0) - 4)); [exact WR| exact BY| lia| unfold DP_TAB in *; lia]. }
split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO CN)|].
split.
{
pose proof (kn_word E m (kn_view ch) (ELit 0) 0x5d40a8 8 (E_PG 478) 0 DN KO (dfact 0%nat _ eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as K58.
cbn [wcell Z.add] in K58. apply ro_rw; [exact K58|]. apply img_wn_wr_at; [exact W58| unfold DP_MAP1; lia| unfold DP_MAP1; cbn; lia]. }
split.
{
intros i Hi. replace i with 1 by lia. change (lastb (fun _ => h0) (bkt h0) (Z.to_nat (1 - 1))) with 0.
pose proof (kn_word E m (kn_view ch) (E_PG 478) 16 8 (ELit h0) DN h0 KO (dfact 2%nat _ eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as N1.
pose proof (kn_word E m (kn_view ch) (E_PG 478) 24 4 (ELit 0) DN 0 KO (dfact 3%nat _ eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as N2.
pose proof (kn_word E m (kn_view ch) (E_PG 478) 28 4 (ELit 1) DN 1 KO (dfact 4%nat _ eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as N3.
cbn [wcell] in N1, N2, N3.
apply ro_rw.
- apply (proj2 (ro_cells_app asegs m _ [C8 (wz h0)] _)). split; [exact N1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
apply (proj2 (ro_cells_app asegs m _ [C4 (wz 0)] _)). split; [replace (DN + 16 * 1 + 8) with (DN + 24) by lia; exact N2|].
cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4. replace (DN + 16 * 1 + 8 + 4) with (DN + 28) by lia. exact N3.
- cbn [cells_size csize Nat.add].
apply (kn_wr_at E m (kn_view ch) KO (E_PG 478) 0 1048576 DN (dfact 6%nat _ eq_refl) eq_refl); lia. }
split.
{
split; [right; lia|]. split; [lia|]. intros a Ha.
apply (kn_zero_some E m (kn_view ch) KO (E_PG 478) 32 1048544 DN (dfact 5%nat _ eq_refl) eq_refl); lia. }
split.
{
split; [right; lia|]. split; [lia|]. intros a Ha.
apply (kn_wr_some E m (kn_view ch) KO (E_PG 479) 0 8388608 SSB (dfact 7%nat _ eq_refl) eq_refl); lia. }

pose proof (kn_word E m (kn_view ch) (E_PG 237) 3168 1 (ELit 0) T 0 KO (dfact 8%nat _ eq_refl) eq_refl ltac:(lia) eq_refl ltac:(inl)) as U.
cbn [wcell] in U. apply ro_rw; [exact U|]. cbn [cells_size csize Nat.add].
apply (kn_wr_at E m (kn_view ch) KO (E_PG 237) 0 4096 T (dfact 9%nat _ eq_refl) eq_refl); lia.
Qed.
End D.

Definition depot_main {BAND : Band} (sp : word) (w : bool) (E : env) (m : word -> option byte) : Prop :=
RDepot (RE_main sp w E) (X_main E) m /\ RFake [] (RE_main sp w E) (X_main E) m.

Theorem depot_at_main : at_main_stmt (fun BAND sp w E m => @depot_main BAND sp w E m).
Proof.
intros sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BAND HB HG.
split; [exact (RDepot_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB)|].
exact (RFake_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB).
Qed.
