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

Local Ltac inl := first [solve [cbn; repeat first [left; reflexivity | right]] | cbn; tauto].
Import QWRO(aentry, mkAE, ae_sp0, ae_stack_top, ae_fs_base, ae_L, ae_stack_bottom)
QFQR(rlay, mkRL, rl_T, rl_ctx, rl_dn, rl_ssb, rl_dtls, prim_lo, region_info, ptrarr_lo, tag_at, tag_prim, count_tag, stag_eqb, TFree, TCached,
A_TP, A_INSTANCE, A_ERRNO, slot_beg)
QKBN(RPrim, RStats, RChunks, class_rep, cr_cells, cr_pure, cr_region, ri_cells, pc_cells, ri_addr, pc_addr, coff, pcls, mkPK, pk_fl, pk_ca,
hjunk, fa_byte, bsize, bmax, SH_le).
Set Default Proof Using "All".
Local Ltac inw := (apply OBJS_common; first [solve [cbn; repeat first [left; reflexivity | right]] | cbn; tauto]).

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition E_PG (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).

Definition E_RIB : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209)).

Definition PRIM_FACTS : list kentry :=
[ KZero (SA (E_PG 237) 80) (ELit 3088); KWr (SA (E_PG 237) 0) (ELit 4096);
KZero (SA E_RIB 0x2000010000) (ELit 4096);
KRange (EVar 237) 1 34359736319; KRange (EVar 208) 4295491576 34326181871; KRange (EVar 209) 0 15 ].

Definition prim_checks (k : list kentry) : bool :=
kn_has_all PRIM_FACTS k && img_wn A_ERRNO 4 && img_wn 0x174420 1.
Lemma PRIM_CHECKS : forall w ch, HSCLASS_S w ch -> prim_checks (kn_view ch) = true.  Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Lemma rw_cells_CB0 : forall m a k (bs : list byte), k = 0%nat -> bs = [] -> 0 <= a <= 2^64 -> rw_cells asegs m a [CB k bs].
Proof.
intros m a k bs -> -> Ha. split; [split; [cbn; split; [reflexivity| exact I]|]|].
- split; [lia|]. split; [cbn [cells_bytes cbytes app length Z.of_nat]; lia|]. intros i Hi. cbn [cells_bytes cbytes app length] in Hi. lia.
- split; [lia|]. split; [cbn [cells_size csize Nat.add Z.of_nat]; lia|]. intros i Hi. cbn [cells_size csize Nat.add Z.of_nat] in Hi. lia.
Qed.

Lemma max_count_nonneg : forall c, 0 <= Q6sh.max_count c.
Proof. intros c. unfold Q6sh.max_count. destruct (Q6sh.class_size c =? 0); lia. Qed.

Lemma SH_div_le : forall a b, a <= b -> a / 8 <= b / 8.
Proof. intros a b H. apply Z.div_le_mono; lia. Qed.

Section P.
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
#[local] Notation LV := (LV_J E).
#[local] Notation m := (view (LV_J E) mo FULL).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB) (only parsing).

Let KO : know_ok asegs E m (kn_view ch) := MV4 main_know_view.

Lemma pfact : forall K, kn_has K PRIM_FACTS = true -> kn_has K (kn_view ch) = true.
Proof.
intros K HK. pose proof (PRIM_CHECKS w ch HCL) as CK. unfold prim_checks in CK. apply andb_prop in CK as [H _]. apply andb_prop in H as [H _].
unfold kn_has_all in H. rewrite forallb_forall in H. apply H. apply kn_has_In. exact HK.
Qed.

Let T : Z := 4096 * bv_unsigned (ev E 237).
Let RIB : Z := 4096 * bv_unsigned (ev E 208) + (-4096) * bv_unsigned (ev E 209).

Lemma B240 : 1 <= bv_unsigned (ev E 237) <= 34359736319.
Proof. exact (kn_range_var E m (kn_view ch) KO 237 _ _ (pfact (KRange (EVar 237) 1 34359736319) eq_refl)). Qed.
Lemma B221 : 4295491576 <= bv_unsigned (ev E 208) <= 34326181871.
Proof. exact (kn_range_var E m (kn_view ch) KO 208 _ _ (pfact (KRange (EVar 208) 4295491576 34326181871) eq_refl)). Qed.
Lemma B222 : 0 <= bv_unsigned (ev E 209) <= 15.
Proof. exact (kn_range_var E m (kn_view ch) KO 209 _ _ (pfact (KRange (EVar 209) 0 15) eq_refl)). Qed.

Lemma T_oh : T + 4096 <= 0x10000 \/ 0x647000 <= T.
Proof.
pose proof ((LA obj_facts) (237%nat, 4096) ltac:(inw)) as (_ & _ & _ & _ & OH & _). cbn [fst snd] in OH. unfold T. lia.
Qed.

Lemma T_zero_rw : forall a cs, zcells cs = true -> T + 80 <= a -> a + Z.of_nat (cells_size cs) <= T + 3168 -> rw_cells asegs m a cs.
Proof.
intros a cs Z1 H1 H2. pose proof B240 as B. pose proof T_oh as OH. unfold T in *.
apply (kn_zero_rw E m (kn_view ch) KO (E_PG 237) 80 3088 (4096 * bv_unsigned (ev E 237)) (pfact (KZero (SA (E_PG 237) 80) (ELit 3088)) eq_refl)
eq_refl ltac:(lia) ltac:(lia) a cs Z1); lia.
Qed.
Lemma T_zero_some : forall a, T + 80 <= a < T + 3168 -> exists b, m (wa a) = Some b.
Proof.
intros a Ha. pose proof B240 as B. unfold T in *.
apply (kn_zero_some E m (kn_view ch) KO (E_PG 237) 80 3088 (4096 * bv_unsigned (ev E 237)) (pfact (KZero (SA (E_PG 237) 80) (ELit 3088)) eq_refl)
eq_refl ltac:(lia) ltac:(lia) a). lia.
Qed.
Lemma T_hjunk : forall lo hi, T + 80 <= lo -> lo <= hi -> hi <= T + 3168 -> hjunk m lo hi.
Proof.
intros lo hi H1 H2 H3. pose proof B240 as B. pose proof T_oh as OH. unfold T in *. split; [lia|]. split; [lia|].
intros a Ha. apply T_zero_some. unfold T. lia.
Qed.

Lemma RI_zero_rw : forall a cs, zcells cs = true -> RIB + 0x2000010000 <= a -> a + Z.of_nat (cells_size cs) <= RIB + 0x2000010000 + 4096 ->
rw_cells asegs m a cs.
Proof.
intros a cs Z1 H1 H2. pose proof B221 as B1. pose proof B222 as B2. unfold RIB in *.
apply (kn_zero_rw E m (kn_view ch) KO E_RIB 0x2000010000 4096 (4096 * bv_unsigned (ev E 208) + (-4096) * bv_unsigned (ev E 209))
(pfact (KZero (SA E_RIB 0x2000010000) (ELit 4096)) eq_refl) eq_refl ltac:(lia) ltac:(lia) a cs Z1); lia.
Qed.

Theorem RStats_main : RStats (RE_main sp w E) (X_main E) m.
Proof.
pose proof B240 as B. pose proof (PRIM_CHECKS w ch HCL) as CK0. unfold prim_checks in CK0. apply andb_prop in CK0 as [CK' W2]. apply andb_prop in CK' as [_ W1].
unfold RStats. change (rl_T (X_main E)) with T. split; [apply T_hjunk; unfold T; lia|].

split.
- destruct (img_wn_junk E m (kn_view ch) 0 0 A_ERRNO 4 KO (or_intror I) W1 ltac:(unfold A_ERRNO; lia) ltac:(unfold A_ERRNO; cbn; lia)) as [bs RW].
pose proof RW as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
destruct bs as [|x0 [|x1 [|x2 [|x3 [|? ?]]]]]; try discriminate.
exists (wz (bytes_le_to_Z [x0; x1; x2; x3])).
eapply rw_cells_recast'; [exact RW| inl|]. cbn [cells_bytes cbytes app]. rewrite le4_of_bytes by reflexivity. reflexivity.
- destruct (img_wn_junk E m (kn_view ch) 0 0 0x174420 1 KO (or_intror I) W2 ltac:(lia) ltac:(cbn; lia)) as [bs RW].
pose proof RW as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
destruct bs as [|x0 [|? ?]]; try discriminate.
exists x0. eapply rw_cells_recast'; [exact RW| inl| reflexivity].
Qed.

Theorem RChunks_main : RChunks Q6sh.astate0 [] G_main (RE_main sp w E) (X_main E) m.
Proof. split; [intros p A n []| intros p A n p' A' n' z []]. Qed.

Lemma sbf : SB E mod 65536 = 0 /\ PRES E <= SB E /\ SB E <= PRES E + 0x10000
/\ 0x10007fff8000 <= PRES E /\ PRES E + 0x2000011000 <= atopE E /\ SB E + 2^37 <= PRES E + 0x2000011000.
Proof.
pose proof (LA sb_facts) as (S1 & S2 & S3 & S4 & S5 & _).
destruct (MA sb_layout) as (_ & _ & S6). repeat split; assumption.
Qed.

Lemma existsb_false_of : forall {X} (f : X -> bool) l, (forall p, In p l -> f p = false) -> existsb f l = false.
Proof. intros X f l H. induction l as [|a l IH]; [reflexivity|]. cbn [existsb]. rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros p Hp. apply H. right. exact Hp. Qed.

Lemma vis_apart : forall x, SH (SB E + 2^32) <= x < SH (SB E + 2^37) -> in_allow BJO6 E ch x = false.
Proof.
intros x Hx. pose proof sbf as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (MA main_atop_bounds) as AB.
change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
unfold SH, A_SHADOW_OFS in Hx.
assert (X1 : 0x2008fff7000 <= x < 0x10007fff8000).
{ pose proof (SH_div_le (0x10007fff8000) (SB E + 4294967296) ltac:(lia)). pose proof (SH_div_le (SB E + 137438953472) 0x7fffff800000 ltac:(lia)). lia. }

assert (OBJ : forall o d len, In o (OBJS_W w) -> o <> (208%nat, 137439023104) -> 0 <= d -> 0 <= len -> d + len <= snd o ->
forall lo n, lo = 4096 * bv_unsigned (ev E (fst o)) + d -> n = len ->
((lo <=? x) && (x <? lo + n))%bool = false
/\ ((shadow_off BJO6 + lo / 8 <=? x) && (x <? shadow_off BJO6 + (lo + n) / 8))%bool = false).
{ intros o d len Ho Hne D0 L0' DL lo n -> ->. pose proof (PRES_O_in w) as Hp.
pose proof ((LA obj_facts) o Ho) as (_ & _ & L0 & LH & _ & _). pose proof ((LA obj_disj) o _ Ho Hp Hne) as D.
cbn [shadow_off BJO6]. cbn [fst snd] in D. unfold PRES in S1, S2, S3, S4, S5, S6.
set (ob := 4096 * bv_unsigned (ev E (fst o))) in *. set (pr := 4096 * bv_unsigned (ev E 208)) in *.
split.
- apply andb_false_iff. destruct (Z.lt_ge_cases x (ob + d)) as [LT|GE]; [left; apply Z.leb_gt; exact LT| right; apply Z.ltb_ge].
destruct LH as [LH|LH]; lia.
- apply andb_false_iff. destruct D as [D|D].
+ right. apply Z.ltb_ge. pose proof (SH_div_le (ob + d + len) (SB E + 4294967296) ltac:(lia)). lia.
+ left. apply Z.leb_gt. pose proof (SH_div_le (SB E + 137438953472) (ob + d) ltac:(lia)). lia. }
assert (OV : forall o, In o (OBJS_W w) -> o <> (208%nat, 137439023104) ->
((uE E (fst (ov o)) <=? x) && (x <? uE E (fst (ov o)) + uE E (snd (ov o))))%bool = false
/\ ((sh_lo BJO6 E (ov o) <=? x) && (x <? sh_hi BJO6 E (ov o)))%bool = false).
{ intros o Ho Hne. pose proof ((LA obj_facts) o Ho) as (_ & _ & L0 & _).
unfold sh_lo, sh_hi.
change (uE E (fst (ov o))) with (bv_unsigned (fst (obj_e E o))). change (uE E (snd (ov o))) with (bv_unsigned (snd (obj_e E o))).
rewrite ((MA u_obj_base) o Ho), ((MA u_obj_len) o Ho).
exact (OBJ o 0 (snd o) Ho Hne ltac:(lia) ltac:(lia) ltac:(lia) (4096 * bv_unsigned (ev E (fst o))) (snd o) ltac:(lia) eq_refl). }

pose proof B221 as B1. pose proof B222 as B2.
assert (RI : uE E (fst PRES_PAGE_J) = SB E + 137438953472).
{ unfold PRES_PAGE_J, uE, SB, PRES. cbn [fst edenot]. rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite !u_lit64a. lia. }
assert (RL : uE E (snd PRES_PAGE_J) = 4096) by (unfold PRES_PAGE_J, uE; cbn [snd edenot]; rewrite u64_lit by lia; reflexivity).
assert (HL1 : uE E (ELit 65536) = 65536) by (unfold uE; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
assert (HL2 : uE E (ELit 6516736) = 6516736) by (unfold uE; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
destruct (MA u_stack) as [US1 US2]. pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (_ & TP2 & _ & TP4). pose proof (MV4 atop_val) as AV.
unfold in_allow, in_vis, in_sh. rewrite (MA VIS_eq).
assert (ALL : forall p, In p (VIS_W w) ->
((uE E (fst p) <=? x) && (x <? uE E (fst p) + uE E (snd p)))%bool = false /\ ((sh_lo BJO6 E p <=? x) && (x <? sh_hi BJO6 E p))%bool = false).
{ intros p Hp.
assert (C : (exists o, In o (OBJS_W w) /\ o <> (208%nat, 137439023104) /\ p = ov o) \/ p = PRES_PAGE_J \/ p = HULL_J \/ (w = false /\ p = PAGE2_B) \/ p = (e_stacklo, e_stacklen)).
{ destruct w; cbn [VIS_W app In] in Hp;
repeat (destruct Hp as [<-|Hp];
[ first [ left; eexists (_, _); split; [ | split; [ | reflexivity ] ]; [cbn; tauto | discriminate]
| right; left; reflexivity | right; right; left; reflexivity
| right; right; right; left; split; reflexivity | right; right; right; right; reflexivity ] | ]);
destruct Hp. }
destruct C as [(o & Ho & Hne & ->) | [-> | [-> | [[Hw ->] | ->]]]].
- exact (OV o Ho Hne).
- unfold sh_lo, sh_hi. cbn [shadow_off BJO6]. rewrite RI, RL.
split; apply andb_false_iff; left; apply Z.leb_gt; [lia|]. pose proof (SH_div_le (SB E + 137438953472) (SB E + 137438953472) ltac:(lia)). lia.
- unfold sh_lo, sh_hi, HULL_J. cbn [shadow_off BJO6 fst snd]. rewrite HL1, HL2.
split; apply andb_false_iff; right; apply Z.ltb_ge; lia.
-
assert (Ho : In (423%nat, 8192) (OBJS_W w)) by (rewrite Hw; cbn; tauto).
pose proof ((MA pv_bound) _ Ho) as PB. cbn [fst] in PB.
assert (U1 : uE E (fst PAGE2_B) = 4096 * bv_unsigned (ev E 423) + 4096).
{ unfold PAGE2_B, uE. cbn [fst edenot]. rewrite u_add64, u_mul64, !u64_lit by lia. rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity. }
assert (U2 : uE E (snd PAGE2_B) = 4096) by (unfold PAGE2_B, uE; cbn [snd edenot]; rewrite u64_lit by lia; reflexivity).
unfold sh_lo, sh_hi. rewrite U1, U2.
exact (OBJ (423%nat, 8192) 4096 4096 Ho ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(cbn; lia) _ _ eq_refl eq_refl).
- unfold sh_lo, sh_hi. cbn [shadow_off BJO6 fst snd]. rewrite US1, US2.
split; apply andb_false_iff; left; apply Z.leb_gt; [lia|].
pose proof (SH_div_le (SB E + 137438953472) (TOPP (bv_unsigned sp) - 8388608) ltac:(lia)). lia. }
rewrite (existsb_false_of _ _ (fun p Hp => proj1 (ALL p Hp))), (existsb_false_of _ _ (fun p Hp => proj2 (ALL p Hp))). reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Theorem prim_shadow_main : forall x, SH (SB E + 2^32) <= x < SH (SB E + 2^37) -> m (wa x) = Some (b8 0).
Proof.
intros x Hx. pose proof sbf as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (MA main_atop_bounds) as AB.
change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (X1 : 0x2008fff7000 <= x < 0x10007fff8000).
{ unfold SH, A_SHADOW_OFS in Hx.
pose proof (SH_div_le (0x10007fff8000) (SB E + 4294967296) ltac:(lia)). pose proof (SH_div_le (SB E + 137438953472) 0x7fffff800000 ltac:(lia)). lia. }
assert (WX : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).

pose proof (PRES_O_in w) as HPO.
assert (Hvis : hidden LV mo (wa x) = false).
{ unfold hidden. apply negb_false_iff. rewrite WX.
apply (MA inside_allowed (ov (208%nat, 137439023104)) x (MA obj_inside (208%nat, 137439023104) HPO)).
apply orb_true_iff. right. unfold sh_lo, sh_hi. cbn [shadow_off BJO6].
change (uE E (fst (ov (208%nat, 137439023104)))) with (bv_unsigned (fst (obj_e E (208%nat, 137439023104)))).
change (uE E (snd (ov (208%nat, 137439023104)))) with (bv_unsigned (snd (obj_e E (208%nat, 137439023104)))).
rewrite ((MA u_obj_base) (208%nat, 137439023104) HPO), ((MA u_obj_len) (208%nat, 137439023104) HPO). cbn [fst snd].
unfold PRES in *. unfold SH, A_SHADOW_OFS in Hx.
pose proof (SH_div_le (4096 * bv_unsigned (ev E 208)) (SB E + 4294967296) ltac:(lia)).
pose proof (SH_div_le (SB E + 137438953472) (4096 * bv_unsigned (ev E 208) + 137439023104) ltac:(lia)).
apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
rewrite (view_visible LV mo FULL (wa x) Hvis).

assert (Hb : in_bands LV (wa x) = true).
{ unfold in_bands, LV_J, L_main_job6, in_zivs, zin. cbn [lv_bands existsb fst snd]. rewrite WX.
apply orb_true_iff. right. apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
destruct ((MA band_kinds) (wa x) Hb) as (Hm & Hna & Hlz & Hbz).
assert (Hal : in_allow BJO6 E ch (bv_unsigned (wa x)) = false) by (rewrite WX; exact (vis_apart x Hx)).
assert (Hh : hid BJO6 (bv_unsigned sp) (argH0 JOB6PH sp rdraw argv envp uid hw) E ch mo (wa x) = true).
{ unfold hid. apply orb_true_iff. right. apply negb_true_iff. unfold vis. rewrite Hm, Hna, Hlz, Hal. cbn [negb andb orb].
unfold in_hull. cbn [img_lo img_hi BJO6]. rewrite WX.
replace ((65536 <=? x) && (x <? 6582272))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
unfold ATOP, STACK_MAX. pose proof (MV4 atop_val) as AV.
replace (bv_unsigned sp - 8388608 <=? x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
assert (Hg : in_ghost BJO6 E ch (bv_unsigned (wa x)) = false).
{ unfold in_ghost. replace (in_shwin BJO6 (bv_unsigned (wa x))) with true; [apply andb_false_r|].
symmetry. unfold in_shwin. cbn [shadow_off BJO6]. rewrite WX. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
exact (P co_zero (wa x) Hh Hm Hna Hlz Hg).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma lay : Q6sh.al_space_beg (ae_L (RE_main sp w E)) = SB E /\ region_info (RE_main sp w E) = RIB + 0x2000010000.
Proof.
split; [reflexivity|]. unfold region_info. change (Q6sh.al_space_beg (ae_L (RE_main sp w E))) with (SB E).
unfold RIB, SB, PRES. change (2^37) with 137438953472. lia.
Qed.

Theorem RPrim_main : RPrim Q6sh.astate0 G_main (RE_main sp w E) (X_main E) m.
Proof.
pose proof B240 as BT. pose proof B221 as B1. pose proof B222 as B2. pose proof lay as (LSB & LRI). pose proof T_oh as OH.
pose proof sbf as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (MA main_atop_bounds) as AB.
exists (fun _ => mkPK [] []).
split; [change (rl_T (X_main E)) with T; apply T_hjunk; unfold T; lia|].
split; [intros c H; exfalso; apply H; reflexivity|].
intros c Hc. unfold Q6sh.kNumClasses in Hc.
unfold class_rep, cr_cells, cr_pure, cr_region. rewrite !QQwg.cls_astate0. cbn [pk_fl pk_ca].
split; [| split].
-
split; [| split].
+ exists (repeat (b8 0) 8), (repeat (b8 0) 4), (repeat (b8 0) 3), (repeat (b8 0) 56).
unfold ri_addr. rewrite LRI. apply RI_zero_rw; [reflexivity| unfold RIB; lia| cbn [cells_size csize ri_cells Nat.add]; unfold RIB; lia].
+ unfold pc_addr. change (rl_T (X_main E)) with T. cbn [Q6sh.as_cache_inited Q6sh.astate0 pc_cells Q6sh.c_count Q6sh.cst0].
apply T_zero_rw; [reflexivity| unfold T; lia| cbn [cells_size csize pc_cells Nat.add]; unfold T; lia].
+ exists (repeat (wz 0) 16). unfold pc_addr. change (rl_T (X_main E)) with T. split; [| split; [apply repeat_length| intros j Hj; cbn in Hj; lia]].
unfold T in *.
apply (kn_zero_u32arr E m (kn_view ch) KO (E_PG 237) 80 3088 (4096 * bv_unsigned (ev E 237)) (pfact (KZero (SA (E_PG 237) 80) (ELit 3088)) eq_refl) eq_refl
ltac:(lia) ltac:(lia)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
-
cbn [Q6sh.c_num_freed Q6sh.c_count Q6sh.c_mapped_fa Q6sh.c_alloc_user Q6sh.c_mapped_user Q6sh.cst0 length Z.of_nat G_main count_tag filter].
pose proof (max_count_nonneg c). unfold Q6sh.kFreeArraySize, Q6sh.kFreeArrayMapSize, Q6sh.kFreeArrayOffset, Q6sh.kUserMapSize.
repeat split; try lia; try constructor; try (intros i []); try reflexivity; try (intros _; reflexivity).
-
intros Hc1. cbn [Q6sh.c_num_freed Q6sh.c_mapped_fa Q6sh.c_alloc_user Q6sh.c_mapped_user Q6sh.cst0 map].
rewrite ?Z.mul_0_r, ?Z.add_0_r, ?Z.sub_0_r.
unfold Q6sh.fa_beg, Q6sh.reg_beg. rewrite LSB.
unfold Q6sh.kRegionSize, Q6sh.kFreeArrayOffset, Q6sh.kFreeArraySize in *.
change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
assert (CR : 4294967296 <= c * 4294967296 <= 31 * 4294967296) by nia.
remember (SB E + c * 4294967296) as rb eqn:Erb.
assert (SHB : forall x y, x <= y -> SH x <= SH y) by (intros; apply SH_le; assumption).
pose proof (SHB (SB E + 4294967296) rb ltac:(lia)) as M1.
pose proof (SHB (rb + 3758096384 + 536870912) (SB E + 137438953472) ltac:(lia)) as M2.
pose proof (SHB rb (rb + 3758096384) ltac:(lia)) as M3. pose proof (SHB (rb + 3758096384) (rb + 3758096384 + 536870912) ltac:(lia)) as M4.
assert (SLO' : 0x647000 <= SH (SB E + 4294967296)) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
assert (SHI' : SH (SB E + 137438953472) <= 2^64) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
assert (PSH : forall x, SH (SB E + 4294967296) <= x < SH (SB E + 137438953472) -> exists b, m (wa x) = Some b).
{ intros x Hx. exists (b8 0). apply prim_shadow_main. change (2^32) with 4294967296. change (2^37) with 137438953472. exact Hx. }
split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
+
split; [split; [lia| split; [cbn [length u32s map concat Z.of_nat app]; lia| intros i Hi; cbn [length u32s map concat app] in Hi; lia]]
| split; [lia| split; [cbn [length Z.of_nat]; lia| intros i Hi; cbn [length Z.of_nat] in Hi; lia]]].
+ split; [lia|]. split; [lia|]. intros a Ha. lia.
+ intros i t Ht. rewrite G_main_tag in Ht. discriminate.
+ split; [lia|]. split; [lia|]. intros a Ha. lia.
+ intros i t Ht. rewrite G_main_tag in Ht. discriminate.
+ apply rw_cells_CB0; [reflexivity| reflexivity| lia].
+ split; [lia|]. split; [lia|]. intros a Ha. apply PSH. lia.
+ split; [lia|]. split; [lia|]. intros a Ha. apply PSH. lia.
Qed.
End P.

Definition prim_main {BAND : Band} (sp : word) (w : bool) (E : env) (m : word -> option byte) : Prop :=
RStats (RE_main sp w E) (X_main E) m
/\ RPrim Q6sh.astate0 G_main (RE_main sp w E) (X_main E) m
/\ RChunks Q6sh.astate0 [] G_main (RE_main sp w E) (X_main E) m.

Theorem prim_at_main : at_main_stmt (fun BAND sp w E m => @prim_main BAND sp w E m).
Proof.
intros sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BAND HB HG.
split; [exact (RStats_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB)|].
split; [exact (RPrim_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB)|].
exact (RChunks_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB).
Qed.
