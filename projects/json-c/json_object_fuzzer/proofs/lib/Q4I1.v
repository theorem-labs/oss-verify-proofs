(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6w1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6w1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWwJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWwJ.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac inl := first [solve [cbn; repeat first [left; reflexivity | right]] | cbn; tauto].
Import QWRO(aentry, mkAE, ae_sp0, ae_stack_top, ae_fs_base, ae_L, ae_stack_bottom, fframe_rangeA)
QFQR(rlay, mkRL, rl_T, rl_ctx, rl_dn, rl_ssb, rl_dtls, ghost, tag_at, rlay_objs, prim_lo, prim_hi, region_info, ptrarr_lo, ptrarr_hi,
iv_disjoint, pairwise_disjoint, avoid_covers, rlay_ok, gcons, live_prim, live_sec, sec_ok, holds, ncarved, A_FS_MAP_SIZE).
Set Default Proof Using "All".

Definition E_R : expr :=
EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 10))) (ELit 3935).
Definition LAYOUT_FACTS : list kentry :=
[ KRange (EVar 10) 0 8; KRange E_R 0 4095; KRange (EVar 6) 0 2047 ].
Lemma LAYOUT_FACTS_in : forall w ch, HSCLASS_S w ch -> kn_has_all LAYOUT_FACTS (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Definition OBJS_C : list (nat * Z) :=
[(2113%nat, 4096); (496%nat, 4096); (479%nat, 8388608); (478%nat, 1048576); (406%nat, 11571200); (330%nat, 4096); (265%nat, 4096); (238%nat, 65536);
(237%nat, 4096); (236%nat, 8388608); (208%nat, 137439023104); (207%nat, 3727360); (78%nat, 65536)].
Lemma OBJS_common : forall w o, In o OBJS_C -> In o (OBJS_W w).
Proof. intros [|] o Ho; cbn in Ho |- *; tauto. Qed.

Section L.
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
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation LV := (LV_J E).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation EI := (E0 JOB6PH sp rdraw brk0 argv envp uid hw).

Let KO : know_ok QZzg.asegs E (view LV mo FULL) (kn_view ch) := MV4 main_know_view.

Lemma lfb : forall K, In K LAYOUT_FACTS -> kn_has K (kn_view ch) = true.
Proof. intros K HK. exact (kn_has_all_In _ _ _ (LAYOUT_FACTS_in w ch HCL) HK). Qed.

Lemma usp_eq : usp = 32768 * bv_unsigned (ev E 0) + 16 * bv_unsigned (ev E 6).
Proof.
pose proof (proj1 (P co_sinv)) as EV.
rewrite (EV 0%nat ltac:(cbv; lia)), (EV 6%nat ltac:(cbv; lia)).
change (ev EI 0) with (Z_to_bv 64 (usp / 32768)).
change (ev EI 6) with (Z_to_bv 64 ((usp mod 32768) / 16)).
pose proof (u64_range sp) as RS. destruct Hsp as (H1 & H2 & AL). unfold sp_window_lo, sp_window_hi in *.
assert (M16 : (usp mod 32768) mod 16 = 0) by (rewrite <- (Znumtheory.Zmod_div_mod 16 32768 usp) by (try lia; exists 2048; lia); exact AL).
pose proof (Z.div_mod usp 32768 ltac:(lia)) as D1. pose proof (Z.div_mod (usp mod 32768) 16 ltac:(lia)) as D2. rewrite M16 in D2.
pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)) as B1.
assert (B2 : 0 <= usp / 32768 < 2^49) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (B3 : 0 <= usp mod 32768 / 16 < 2^11) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite !u64_lit by lia. lia.
Qed.

Lemma st_main_facts : usp - 0xa0 <= st_main E < usp + 0x8000 /\ st_main E mod 4096 = 0
/\ 0x7fff80000000 <= usp <= 2^47 /\ usp mod 16 = 0.
Proof.
pose proof usp_eq as U. pose proof Hsp as (LO & HI & AL). unfold sp_window_lo, sp_window_hi in LO, HI.
pose proof (kn_range_var E _ (kn_view ch) KO 10 0 8 (lfb (KRange (EVar 10) 0 8) ltac:(inl))) as B10.
pose proof (kn_range_var E _ (kn_view ch) KO 6 0 2047 (lfb (KRange (EVar 6) 0 2047) ltac:(inl))) as B6.
pose proof (kn_range_small E _ (kn_view ch) KO E_R 0 4095 (16 * bv_unsigned (ev E 6) + (-4096) * bv_unsigned (ev E 10) + 3935)
(lfb (KRange E_R 0 4095) ltac:(inl)) eq_refl ltac:(lia) ltac:(lia)) as BR.
unfold st_main. split; [lia|]. split; [|lia].
replace (32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10)) with ((8 * bv_unsigned (ev E 0) + bv_unsigned (ev E 10)) * 4096) by lia.
apply Z.mod_mul. lia.
Qed.

Lemma band_usp : band_lo + 0x800000 = usp.
Proof. rewrite HB. unfold atopE. rewrite (MA main_sp0). lia. Qed.

Lemma obj_disj : forall o1 o2, In o1 (OBJS_W w) -> In o2 (OBJS_W w) -> o1 <> o2 ->
4096 * bv_unsigned (ev E (fst o1)) + snd o1 <= 4096 * bv_unsigned (ev E (fst o2))
\/ 4096 * bv_unsigned (ev E (fst o2)) + snd o2 <= 4096 * bv_unsigned (ev E (fst o1)).
Proof.
intros o1 o2 H1 H2 Hne.
assert (Hne' : obj_e E o1 <> obj_e E o2) by (intros Heq; exact (Hne ((MA obj_e_inj) o1 o2 H1 H2 Heq))).
pose proof ((MA maps_disj) _ _ ((MA in_maps_obj) o1 H1) ((MA in_maps_obj) o2 H2) Hne') as D. unfold Q1LT.APS.iv_disjoint in D.
rewrite !(MA u_obj_base) in D by assumption. rewrite !(MA u_obj_len) in D by assumption. exact D.
Qed.

Lemma obj_facts : forall o, In o (OBJS_W w) ->
(4096 * bv_unsigned (ev E (fst o))) mod 4096 = 0 /\ 0 < 4096 * bv_unsigned (ev E (fst o)) /\ 0 < snd o
/\ (4096 * bv_unsigned (ev E (fst o)) + snd o <= 0x7fff7000 \/ 0x10007fff8000 <= 4096 * bv_unsigned (ev E (fst o)))
/\ (4096 * bv_unsigned (ev E (fst o)) + snd o <= 0x10000 \/ 0x647000 <= 4096 * bv_unsigned (ev E (fst o)))
/\ 4096 * bv_unsigned (ev E (fst o)) + snd o <= atopE E.
Proof.
intros o Ho. pose proof ((MA pv_bound) o Ho) as PB. pose proof ((MA obj_lowhigh) o Ho) as LH.
pose proof ((MA u_obj_base) o Ho) as UB. pose proof ((MA u_obj_len) o Ho) as UL.
pose proof ((MA entry_top) _ ((MA in_maps_obj) o Ho)) as T. rewrite <- (MA main_atop) in T.
pose proof (P co_bounds) as BD. rewrite Forall_forall in BD.
pose proof (BD _ ((MA in_maps_obj) o Ho)) as (_ & _ & _ & OH & _). cbn [img_lo img_hi BJO6] in OH.
rewrite UB, UL in LH, T, OH. unfold QzgH.kLowEnd, Qqcs.Mq0.kHighMemBeg in LH.
pose proof ((MA obj_len_bound) o Ho) as L0.
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [lia|]. split; [lia|]. split; [exact LH|]. split; [exact OH| exact T].
Qed.

Lemma sb_facts : SB E mod 65536 = 0 /\ PRES E <= SB E /\ SB E <= PRES E + 0x10000
/\ 0x10007fff8000 <= PRES E /\ PRES E + 0x2000011000 <= atopE E
/\ PARR E mod 4096 = 0 /\ PARR E + 0x800000 <= atopE E
/\ ((0 < PARR E /\ PARR E + 0x800000 <= 0x7fff7000) \/ 0x10007fff8000 <= PARR E)
/\ (PARR E + 0x800000 <= 0x10000 \/ 0x647000 <= PARR E)
/\ (PRES E + 0x2000011000 <= PARR E \/ PARR E + 0x800000 <= PRES E).
Proof.
destruct (MA sb_layout) as (S1 & S2 & S3).
pose proof (PRES_O_in w) as Hp. pose proof (PARR_O_in w) as Hq.
pose proof (obj_facts _ Hp) as (_ & _ & _ & LP & _ & T1). pose proof (obj_facts _ Hq) as (A2 & P2 & _ & LQ & OQ & T2).
pose proof (obj_disj _ _ Hp Hq ltac:(discriminate)) as D. cbn [fst snd] in *.
pose proof (u64_range (ev E 209)). pose proof (u64_range (ev E 208)). pose proof (u64_range (ev E 236)).
unfold SB, PRES, PARR in *. repeat split; try lia.
Qed.

Lemma RE_main_unfold :
ae_sp0 (RE_main sp w E) = usp /\ ae_stack_top (RE_main sp w E) = st_main E /\ ae_fs_base (RE_main sp w E) = pg E 406
/\ prim_lo (RE_main sp w E) = SB E /\ ptrarr_lo (RE_main sp w E) = PARR E
/\ Q6sh.al_avoid (ae_L (RE_main sp w E)) = Qi08.avoid_J (PRES E) (PARR E) (objs_of w E) (atopE E)
/\ rlay_objs (RE_main sp w E) (X_main E)
= [(pg E 237, 0x1000); (pg E 238, 0x10000); (pg E 478, 0x100000); (pg E 479, 0x800000); (pg E 330, 0x1000); (pg E 406, 0xb09000)].
Proof. repeat split; reflexivity. Qed.

Lemma robj_facts : forall v len, In (v, len) (OBJS_W w) -> v <> 208%nat -> v <> 236%nat ->
pg E v mod 4096 = 0 /\ (((0 < pg E v /\ pg E v + len <= 0x7fff7000) \/ 0x10007fff8000 <= pg E v)
/\ (pg E v + len <= 0x10000 \/ 0x647000 <= pg E v))
/\ pg E v + len <= band_lo
/\ iv_disjoint (pg E v, len) (SB E, 2^37 + 0x1000) /\ iv_disjoint (pg E v, len) (PARR E, 0x800000).
Proof.
intros v len Ho N1 N2. pose proof (PRES_O_in w) as Hp. pose proof (PARR_O_in w) as Hq.
pose proof (obj_facts _ Ho) as (F1 & F2 & F3 & F4 & F5 & F6). cbn [fst snd] in *.
pose proof (obj_disj _ _ Ho Hp ltac:(intros X; injection X; lia)) as D1. pose proof (obj_disj _ _ Ho Hq ltac:(intros X; injection X; lia)) as D2.
cbn [fst snd] in D1, D2. pose proof sb_facts as (S1 & S2 & S3 & _).
unfold pg, iv_disjoint, SB, PRES, PARR in *. cbn [fst snd]. rewrite HB. repeat split; try lia.
Qed.

Lemma OBJ_in_W : forall o, In o [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)] -> In o (OBJS_W w).
Proof. intros o Ho. destruct w; cbn in Ho |- *; tauto. Qed.
Lemma OBJ_in_K : forall o, In o [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)] -> In o (OBJS_K w).
Proof. intros o Ho. destruct w; cbn in Ho |- *; tauto. Qed.

Theorem rlay_main : rlay_ok (RE_main sp w E) (X_main E).
Proof.
pose proof st_main_facts as (T1 & T2 & T3 & T4). pose proof band_usp as BU.
pose proof sb_facts as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
destruct RE_main_unfold as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
unfold rlay_ok, avoid_covers, prim_hi, ptrarr_hi. rewrite U7. rewrite ?U4, ?U5, ?U6, ?U1, ?U2, ?U3.
change (Q6sh.al_space_beg (ae_L (RE_main sp w E))) with (SB E). change (Q6sh.al_ptrarr (ae_L (RE_main sp w E))) with (PARR E).
split; [exact T1|]. split; [exact T2|]. split; [lia|]. split; [lia|]. split; [exact T4|].
split; [exact S1|]. split; [unfold QZzg.KHI; lia|]. split; [rewrite HB; lia|].
split; [exact S6|]. split; [split; [exact S8| exact S9]|]. split; [rewrite HB; lia|].
split; [| split].
-  split.
{ unfold iv_disjoint. cbn [fst snd]. lia. }
intros o Ho. unfold Qi08.avoid_J, Q7z8.kPrimResLen, Q7z8.kPtrArrLen.
assert (OBJ : forall v len, In (v, len) (OBJS_K w) -> exists iv, In iv ([(PRES E, PRES E + 137439023104); (PARR E, PARR E + 8388608)] ++ objs_of w E
++ [(0x10000, 0x647000); (0x7fff7000, 0x10007fff8000); (atopE E, 2^64)]) /\ fst iv <= pg E v /\ pg E v + len <= snd iv).
{ intros v len Hin. exists (wiv2z (obj_e E (v, len))). split.
- apply in_app_iff. right. apply in_app_iff. left. unfold objs_of. exact (in_map (fun o => wiv2z (obj_e E o)) _ _ Hin).
- pose proof (OBJS_K_sub _ _ Hin) as Hin'. unfold wiv2z. rewrite ((MA u_obj_base) _ Hin'), ((MA u_obj_len) _ Hin'). cbn [fst snd]. unfold pg. lia. }
cbn [In app] in Ho.
destruct Ho as [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [ <- | [] ] ] ] ] ] ] ] ] ] ] ]; cbn [fst snd].
+ exists (0x10000, 0x647000). split; [apply in_cons, in_cons, in_or_app; right; left; reflexivity| cbn [fst snd]; lia].
+ exists (0x7fff7000, 0x10007fff8000). split; [apply in_cons, in_cons, in_or_app; right; right; left; reflexivity| cbn [fst snd]; unfold QZzg.KHI; lia].
+ exists (atopE E, 2^64). split; [apply in_cons, in_cons, in_or_app; right; right; right; left; reflexivity| cbn [fst snd]; rewrite HB; lia].
+ exists (PRES E, PRES E + 137439023104). split; [left; reflexivity| cbn [fst snd]; lia].
+ exists (PARR E, PARR E + 8388608). split; [right; left; reflexivity| cbn [fst snd]; lia].
+ apply (OBJ 237%nat 4096). apply OBJ_in_K. inl.
+ apply (OBJ 238%nat 65536). apply OBJ_in_K. inl.
+ apply (OBJ 478%nat 1048576). apply OBJ_in_K. inl.
+ apply (OBJ 479%nat 8388608). apply OBJ_in_K. inl.
+ apply (OBJ 330%nat 4096). apply OBJ_in_K. inl.
+ unfold A_FS_MAP_SIZE. apply (OBJ 406%nat 11571200). apply OBJ_in_K. inl.
-
unfold A_FS_MAP_SIZE.
apply Forall_cons; [cbn [fst snd]; exact (robj_facts 237%nat 4096 ltac:(apply OBJ_in_W; inl) ltac:(discriminate) ltac:(discriminate))|].
apply Forall_cons; [cbn [fst snd]; exact (robj_facts 238%nat 65536 ltac:(apply OBJ_in_W; inl) ltac:(discriminate) ltac:(discriminate))|].
apply Forall_cons; [cbn [fst snd]; exact (robj_facts 478%nat 1048576 ltac:(apply OBJ_in_W; inl) ltac:(discriminate) ltac:(discriminate))|].
apply Forall_cons; [cbn [fst snd]; exact (robj_facts 479%nat 8388608 ltac:(apply OBJ_in_W; inl) ltac:(discriminate) ltac:(discriminate))|].
apply Forall_cons; [cbn [fst snd]; exact (robj_facts 330%nat 4096 ltac:(apply OBJ_in_W; inl) ltac:(discriminate) ltac:(discriminate))|].
apply Forall_cons; [cbn [fst snd]; exact (robj_facts 406%nat 11571200 ltac:(apply OBJ_in_W; inl) ltac:(discriminate) ltac:(discriminate))|].
apply Forall_nil.
-
assert (PW : forall v1 n1 v2 n2, In (v1, n1) [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)] ->
In (v2, n2) [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)] ->
(v1, n1) <> (v2, n2) -> iv_disjoint (pg E v1, n1) (pg E v2, n2)).
{ intros v1 n1 v2 n2 H1 H2 Hne. pose proof (obj_disj _ _ (OBJ_in_W _ H1) (OBJ_in_W _ H2) Hne) as D. cbn [fst snd] in D. unfold iv_disjoint, pg. cbn [fst snd]. lia. }
unfold A_FS_MAP_SIZE. cbn [pairwise_disjoint].
repeat match goal with
| |- _ /\ _ => split
| |- True => exact I
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons
| |- iv_disjoint (pg E ?v1, ?n1) (pg E ?v2, ?n2) =>
apply (PW v1 n1 v2 n2); [inl | inl | discriminate]
end.
Qed.

Theorem gcons_main : gcons Q6sh.astate0 [] [] G_main (RE_main sp w E) (X_main E).
Proof.
unfold gcons. split; [exact rlay_main|].
split; [intros p A n [] |]. split; [constructor|].
split; [intros c i p H; rewrite G_main_tag in H; discriminate|].
split; [intros c i p H; rewrite G_main_tag in H; discriminate|].
split; [intros c H; exfalso; apply H; reflexivity|].
split.
{ intros c Hc. rewrite QQwg.cls_astate0. cbn [Q6sh.c_alloc_user Q6sh.c_mapped_user Q6sh.cst0].
unfold Q6sh.kFreeArrayOffset, Q6sh.kUserMapSize. repeat split; try lia; reflexivity. }
split; [intros c i c' i' p t t' H; rewrite G_main_tag in H; discriminate|].
split; [intros c i t id n H; rewrite G_main_tag in H; discriminate|].
cbn [Q6sh.as_reg Q6sh.astate0 map pairwise_disjoint].
split; [constructor|]. split; [exact I|]. split; [constructor|].
split; [intros f []|]. intros f1 f2 [].
Qed.
End L.

Theorem gcons_at_main : at_main_stmt (fun BAND sp w E m => @gcons BAND Q6sh.astate0 [] [] G_main (RE_main sp w E) (X_main E)).
Proof. intros sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BAND HB HG. exact (gcons_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB). Qed.
