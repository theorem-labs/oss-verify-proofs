(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh QQwg QKTr QJBH QvG1 QDw3 QUxU QNwL QYnC QmP7 Q9Ho QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QDw3 QUxU QNwL QYnC QmP7.Mq0 Q9Ho.Mq1.
Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Ltac gc_split GC :=
destruct GC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A8b & A9 & A10 & A11 & A12 & A13).

Lemma gcons_ext {BAND : Band} : forall a a' LB FS G RE X,
gcons a LB FS G RE X ->
(forall c, c_alloc_user (cls a' c) = c_alloc_user (cls a c)) ->
(forall c, c_mapped_user (cls a' c) = c_mapped_user (cls a c)) ->
as_reg a' = as_reg a -> (as_next a <= as_next a')%N ->
gcons a' LB FS G RE X.
Proof.
intros a a' LB FS G RE X GC EA EM ER EN. gc_split GC.
split; [exact A1|]. split.
{ intros p A n H. destruct (A2 p A n H) as [[H1|H1] H2]; split; [left; exact H1| exact H2| | exact H2].
right. destruct H1 as (mb & E & H3 & H4 & H5 & H6). exists mb. rewrite ER. repeat split; assumption. }
split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split.
{ intros c Hc. destruct (A6 c Hc) as [X1 X2]. split; [exact X1|]. rewrite EA. exact X2. }
split. { intros c Hc. rewrite EA, EM. apply A7. exact Hc. }
split; [exact A8|]. split. { intros c i t id n Ht Hh. pose proof (A8b c i t id n Ht Hh). lia. }
rewrite ER. repeat (split; [assumption|]). exact A13.
Qed.

Section Retag.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Variables (c0 i0 : Z) (t0 t1 : stag).
Hypothesis GC : gcons a LB FS G RE X.
Hypothesis HT0 : tag_at G c0 i0 = Some t0.
Let G' := set_tag c0 i0 t1 G.

Lemma retag_at : forall c i, tag_at G' c i = if (c =? c0) && (i =? i0) then Some t1 else tag_at G c i.
Proof.
intros c i. pose proof (tag_at_Some_lt _ _ _ _ HT0) as [I0 _].
destruct (Z.eqb_spec c c0) as [->|NC]; [destruct (Z.eqb_spec i i0) as [->|NI]|]; cbn [andb].
- exact (tag_at_set_tag_eq G c0 i0 t1 t0 HT0).
- apply tag_at_set_tag_ne; lia.
- apply tag_at_set_tag_ne; lia.
Qed.
End Retag.

Lemma gcons_free_prim {BAND : Band} : forall a LB FS G RE X p A n c i id,
gcons a LB FS G RE X -> In (p, A, n) LB -> p = APrim id n -> tag_at G c i = Some (TLive p) ->
gcons a (alb_remove p LB) FS (set_tag c i (TQuar p) G) RE X.
Proof.
intros a LB FS G RE X p A n c i id GC Hin Ep Ht. pose proof GC as GC0. gc_split GC.
pose proof (retag_at G c i (TLive p) (TQuar p) Ht) as RT.
assert (PC : aptr_cls p = c /\ from_primary (aptr_req p) = true).
{ destruct (A4 c i p Ht) as (id0 & n0 & A0 & E0 & HinA & Hc0). rewrite Ep in E0. inversion E0. subst id0 n0.
split; [subst p; exact Hc0|].
destruct (A2 p A n Hin) as [[(id' & i1 & E & Hn & HP & _)|(mb & E & _ & HP & _)] _]; subst p; [exact HP| discriminate]. }
destruct PC as (PCc & PCp).
split; [exact A1|]. split.
{ intros q Aq nq Hq. apply In_alb_remove in Hq as [Hq NE]. cbn [ablk_id fst] in NE.
destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| right; exact H1| exact H2].
left. destruct H1 as (id' & i' & E & Hn & HP & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [| split; [exact Hi'| exact HA]]. rewrite RT.
destruct (Z.eqb_spec (class_of nq) c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb]; try exact Ht'.
exfalso. rewrite EC, EI, Ht in Ht'. inversion Ht'. apply NE. symmetry. assumption. }
split.
{ unfold alb_remove. clear - A3. induction LB as [|b LB IH]; cbn; [constructor|].
inversion A3; subst. destruct (decide _); cbn; [constructor; [| apply IH; assumption]| apply IH; assumption].
intros Hm. apply H1. apply in_map_iff in Hm as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E|].
apply list_elem_of_In. apply list_elem_of_In in Hb'. apply list_elem_of_filter in Hb'. tauto. }
split.
{ intros c' i' q Hq. rewrite RT in Hq.
destruct (Z.eqb_spec c' c) as [->|NC]; [destruct (Z.eqb_spec i' i) as [->|NI]|]; cbn [andb] in Hq; [discriminate| |].
- destruct (A4 c i' q Hq) as (idq & nq & Aq & Eq & HinA & Hc). exists idq, nq, Aq. split; [exact Eq|]. split; [| exact Hc]. apply In_alb_remove. split; [exact HinA|].
cbn [ablk_id fst]. intros ->. pose proof (A8 c i' c i p _ _ Hq Ht) as [_ E]; [cbn; apply aptr_eqb_refl'| cbn; apply aptr_eqb_refl'| lia].
- destruct (A4 c' i' q Hq) as (idq & nq & Aq & Eq & HinA & Hc). exists idq, nq, Aq. split; [exact Eq|]. split; [| exact Hc]. apply In_alb_remove. split; [exact HinA|].
cbn [ablk_id fst]. intros ->. pose proof (A8 c' i' c i p _ _ Hq Ht) as [E _]; [cbn; apply aptr_eqb_refl'| cbn; apply aptr_eqb_refl'| lia]. }
split.
{ intros c' i' q Hq. rewrite RT in Hq.
destruct (Z.eqb_spec c' c) as [->|NC]; [destruct (Z.eqb_spec i' i) as [->|NI]|]; cbn [andb] in Hq.
- inversion Hq; subst q. split; [exact PCc| exact PCp].
- exact (A5 _ _ _ Hq).
- exact (A5 _ _ _ Hq). }
split.
{ intros c' NE. rewrite ncarved_set_tag. apply A6. intros E. apply NE.
destruct (Z.eq_dec c' c) as [->|NC]; [rewrite set_tag_class, E; reflexivity| rewrite set_tag_other_class by exact NC; exact E]. }
split; [exact A7|]. split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2. rewrite RT in H1, H2.
assert (HH : forall cc ii u, (if (cc =? c) && (ii =? i) then Some (TQuar p) else tag_at G cc ii) = Some u -> holds q u = true ->
exists u', tag_at G cc ii = Some u' /\ holds q u' = true).
{ intros cc ii u Hu Ku. destruct ((cc =? c) && (ii =? i)) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst cc ii. inversion Hu; subst u.
exists (TLive p). split; [exact Ht| exact Ku].
- exists u. auto. }
destruct (HH _ _ _ H1 K1) as (u1' & H1' & K1'). destruct (HH _ _ _ H2 K2) as (u2' & H2' & K2').
exact (A8 _ _ _ _ q _ _ H1' H2' K1' K2'). }
split.
{ intros c1 i1 t id1 n1 H1 K1. rewrite RT in H1. destruct ((c1 =? c) && (i1 =? i)) eqn:E.
- inversion H1; subst t. eapply (A8b c i (TLive p) id1 n1 Ht). exact K1.
- eapply A8b; eassumption. }
repeat (split; [assumption|]). exact A13.
Qed.

Lemma gcons_free_sec {BAND : Band} : forall a LB FS G RE X p A n mb,
gcons a LB FS G RE X -> In (p, A, n) LB -> p = ASec mb n ->
gcons a (alb_remove p LB) FS G RE X.
Proof.
intros a LB FS G RE X p A n mb GC Hin Ep. gc_split GC.
split; [exact A1|]. split.
{ intros q Aq nq Hq. apply In_alb_remove in Hq as [Hq _]. exact (A2 q Aq nq Hq). }
split.
{ unfold alb_remove. clear - A3. induction LB as [|b LB IH]; cbn; [constructor|].
inversion A3; subst. destruct (decide _); cbn; [constructor; [| apply IH; assumption]| apply IH; assumption].
intros Hm. apply H1. apply in_map_iff in Hm as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E|].
apply list_elem_of_In. apply list_elem_of_In in Hb'. apply list_elem_of_filter in Hb'. tauto. }
split.
{ intros c' i' q Hq. destruct (A4 c' i' q Hq) as (idq & nq & Aq & Eq & HinA & Hc). exists idq, nq, Aq. split; [exact Eq|]. split; [| exact Hc].
apply In_alb_remove. split; [exact HinA|]. cbn [ablk_id fst]. intros ->. subst p. discriminate. }
repeat (split; [assumption|]). exact A13.
Qed.

End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf QvDJ QyW2 Qp4j QsGW QSsj Qu1d QNQk QpY2 QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf.
Import Q6sh QKTr QvDJ.Mq3.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq2.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition memchr_stub : Z := 0x4f974.
Definition memchr_icpt_entry : Z := 0x52220.
Definition MEMCHR_ICPT_STACK : Z := 2224.

Definition memchr_len (c n : Z) (buf : list byte) : Z :=
match find_byte c (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i + 1 | None => n end.

Definition memchr_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A c n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (memchr_res A c n buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ bytes_at asegs m' A buf.

Lemma find_byte_lt : forall c l i, find_byte c l = Some i -> (i < length l)%nat.
Proof.
intros c l. induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
destruct (bv_unsigned b =? c); [inversion H; cbn; lia|].
destruct (find_byte c l) as [j|]; [| discriminate]. inversion H; subst. specialize (IH j eq_refl). cbn. lia.
Qed.

Lemma memchr_len_bound : forall c n buf, 0 <= n -> 0 <= memchr_len c n buf <= n /\ (memchr_len c n buf <= Z.of_nat (length buf) \/ memchr_len c n buf = n).
Proof.
intros c n buf Hn. unfold memchr_len. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [| lia].
apply find_byte_lt in E. rewrite length_firstn in E. lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c n lo : Z) (buf : list byte) (cw : word).
Let L := memchr_len c n buf.
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - MEMCHR_ICPT_STACK.
Hypothesis A0 : 0 < A.
Hypothesis N0 : 0 <= n < 2^64.
Hypothesis CW : bv_unsigned cw mod 256 = c.
Hypothesis OK : memchr_ok A c n buf.
Hypothesis BSTK : A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A.
Hypothesis RNG : rng_ok m A L.
Let usp := bv_unsigned sp.
Let POST := memchr_icpt_post ra sp gp tp.

Lemma memchr_icpt_tail : forall mf (res rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v s3v s4v s5v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
res = wz (memchr_res A c n buf) ->
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2128) -> stk asegs mf (usp + -2128) (usp + -56) ->
rw_cells asegs mf (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
(MS (mkR rav (wz (usp + -2128)) gp tp t0 t1 t2 sp s1v res a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x522dc) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros -> MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
set (BAh := bytes_at) in BUF.
do 8 istep.
pose proof (stk_merge asegs _ _ _ _ ST1 ST2 ltac:(lia)) as ST. clear ST1 ST2.
release_frame FR ST (bv_unsigned sp).
step. step.
apply evt_done. unfold POST, memchr_icpt_post. do 15 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact BUF.
Qed.

Lemma memchr_icpt_check : forall mf (len : Z) (res rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
len = L -> res = wz (memchr_res A c n buf) ->
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2128) -> stk asegs mf (usp + -2128) (usp + -56) ->
rw_cells asegs mf (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
(MS (mkR rav (wz (usp + -2128)) gp tp t0 t1 t2 sp (wz len) res a1 a2 a3 a4 a5 a6 a7 (wz A) s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x52294) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros -> ER MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (memchr_len_bound c n buf ltac:(lia)) as [LB _]. fold L in LB.
pose proof RNG as (RA0 & RA47 & SOK & BIG & NB).
assert (RNG' : rng_ok mf A L).
{ eapply rng_ok_munch; [exact RNG| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. cbn. rewrite !SH_eq, ?KHI_eq in *. left. Z.div_mod_to_equations. lia. }
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SB2.
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RC2.

step. step. step.
destruct (Z.eq_dec L 0) as [Lz|Lz].
{
if_cases K1; zify_cond K1; rewrite ?Lz, ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Lz; cbn in K1; lia].
step. rewrite Lz. ifz. step.
eapply memchr_icpt_tail; [exact ER| exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF]. }
destruct (Z_le_gt_dec L 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct RNG' as (_ & _ & SOK' & _ & NB'). destruct (NB' ltac:(lia)) as [[w1 W1] [w2 W2]]. pose proof (SOK' ltac:(lia)) as SO2.
destruct SB2 as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. step. step. step. stp. stp.
rewrite (unsigned_lit A), (unsigned_lit (A + L + -1)) by lia.
replace (2147450880 + A ≫ 3) with (SH A) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (A + L + -1) ≫ 3) with (SH (A + L - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH A /\ SH A <= SH (A + L - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH A)), (unsigned_lit (SH (A + L - 1))) by lia. rewrite !land_m8 by lia.
replace (SH A - SH A mod 8) with (8 * (SH A / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (A + L - 1) - SH (A + L - 1) mod 8) with (8 * (SH (A + L - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ A L SO2 ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ A L SO2 ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1'' a3'' a4'' a5'' : word,
ms1 = MS (@bvmap_set 5 word 11 a1'' (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 14 a4'' (@bvmap_set 5 word 15 a5'' R)))) FF (wz 0x522dc) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (A + L + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (A + L - 1)) (SH A)) as [X1|X1].
+ ifz. replace (SH A) with (SH (A + L - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_a1 0x523ec ltac:(right; left; reflexivity) (Z.to_nat (SH (A + L - 1) - SH A)) (SH A)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4x. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1'' & a3'' & a4'' & a5'' & ->). simp_regs.
eapply memchr_icpt_tail; [exact ER| exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF].
-
destruct RNG' as (_ & _ & SOK' & BIG' & _). destruct (BIG' ltac:(lia)) as [KA L43]. pose proof (SOK' ltac:(lia)) as SO2.
ifz. step. ifz. step. step. step.
pose proof (rt_mem_cells_of _ SB2 RC2) as RTM.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia| exact SO2| lia| lia| lia| exact KA|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST5 end.
step. step. step. ifz.
eapply memchr_icpt_tail; [first [exact ER| reflexivity]| exact MU| exact WM| assumption| exact ST5| eassumption| eassumption| eassumption].
Qed.

Lemma memchr_icpt_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
stk asegs m lo usp -> bytes_at asegs m A buf -> mem_inv asegs m ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) cw (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memchr_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros ST BUF MI.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
pose proof (memchr_len_bound c n buf ltac:(lia)) as [LB LB2]. fold L in LB, LB2.
pose proof RNG as (RA0 & RA47 & _ & _ & _).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
set (BAh := bytes_at) in BUF.
unfold memchr_stub. step.
carve_frame 56%nat ST.
do 8 istep.
step. step. step. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_159b60 _ RCc) as K14. pose proof (rt_161720 _ RCc) as K18. clear RCc.

step. call0 asaninited_spec7; [exact K18|]. subst_words. step. ifz.

step. call_u tryinit_spec7; [exact K18| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => rename H into ST1' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
step. stp. step. step. step. step. clear K14 K18.
assert (BUF1 : bytes_at asegs m1 A buf).
{ eapply bytes_at_transport; [exact BUF| exact MUs|]. cbn. lia. }
clear BUF.

step. call_u (memchr_spec _ _ _ _ _ _ _ _ _ (wz A) cw (wz n));
[rewrite unsigned_lit by lia; exact BUF1| rewrite !unsigned_lit, CW by lia; exact OK| assumption|].
rewrite ?(unsigned_lit A), ?(unsigned_lit n), ?CW in * by lia.
match goal with H : stk asegs ?mc' (bv_unsigned sp + -2128) _, H2 : rw_cells asegs ?mc' (bv_unsigned sp + -56) _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
rename H into ST2'; rename H2 into FR' end.
match goal with H : bytes_at asegs ?mc' A buf |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into BUF2 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.

step. ifz. step.
unfold memchr_res.
destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
-
pose proof (find_byte_lt _ _ _ FB) as IL. rewrite length_firstn in IL.
assert (EL : L = Z.of_nat i + 1) by (subst L; unfold memchr_len; rewrite FB; reflexivity).
unfold_cond. rewrite (unsigned_lit (A + Z.of_nat i)) by lia. if_lit.
stp. rewrite (unsigned_lit A) by lia.
stp. step. step. step.
replace (A + Z.of_nat i + - A + 1) with L by lia.
step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply memchr_icpt_check; [reflexivity| unfold memchr_res; rewrite FB; reflexivity| exact MUs| exact WM| assumption| exact ST1'| exact ST2'| exact FR'| exact BUF2].
-
assert (EL : L = n) by (subst L; unfold memchr_len; rewrite FB; reflexivity).
ifz. step. step. step. step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply memchr_icpt_check; [symmetry; exact EL| unfold memchr_res; rewrite FB; reflexivity| exact MUs| exact WM| assumption| exact ST1'| exact ST2'| exact FR'| exact BUF2].
Qed.
End S.

Theorem memchr_icpt_spec {BAND : Band} :
forall (A n lo : Z) (buf : list byte) (cw : word),
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
bytes_at asegs m A buf -> memchr_ok A (bv_unsigned cw mod 256) n buf -> mem_inv asegs m ->
0 < A -> 0 <= n < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MEMCHR_ICPT_STACK ->
A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m A (memchr_len (bv_unsigned cw mod 256) n buf) ->
evt asegs (memchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (bv_unsigned cw mod 256) n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) cw (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memchr_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros BUF OK MI A0 N0 ST CEIL LO BSTK SB RC RNG.
eapply memchr_icpt_main; try eassumption. reflexivity.
Qed.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq1.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition memcpy_stub : Z := 0x61740.
Definition memcpy_icpt_entry : Z := 0x62940.
Definition MEMCPY_ICPT_STACK : Z := 2240.

Definition memcpy_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.

Lemma qslow_loop_at : forall (pc : Z), (pc = 0x62cc0 \/ pc = 0x62dc0) ->
forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz e) (wz e) (wz 0) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (pc + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz p) (wz e) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom asegs)).
Proof.
intros pc [-> | ->];
(induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ]).
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (dst srcA n lo : Z) (src junk : list byte).
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - MEMCPY_ICPT_STACK.
Hypothesis N0 : 0 <= n.
Hypothesis SRC : bytes_at asegs m srcA src.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis DST : rw_cells asegs m dst [CB (Z.to_nat n) junk].
Hypothesis SEP : srcA + n <= dst \/ dst + n <= srcA.
Hypothesis SST : srcA + n <= lo \/ bv_unsigned sp <= srcA.
Hypothesis DSTK : dst + n <= lo \/ bv_unsigned sp <= dst.
Hypothesis RS : rng_ok m srcA n.
Hypothesis RD : rng_ok m dst n.
Let usp := bv_unsigned sp.
Let POST := memcpy_icpt_post ra sp gp tp.

Definition frame_cells (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) : list cell :=
[C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma memcpy_icpt_tail : forall mc (rav t0 t1 t2 a3 a4 a5 a6 a7 s1v s2v s3v s4v s5v s6v s7v s8v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -2160) -> stk asegs mc (usp + -2160) (usp + -80) ->
rw_cells asegs mc (usp + -80) (frame_cells s8 s7 s6 s5 s4 s3 s2 s1 s0) ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR rav (wz (usp + -2160)) gp tp t0 t1 t2 sp s1v (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62a34) fc None mc (seg_rom asegs)).
Proof.
intros until s11; intros MUs WM MI ST ST2 FR. unfold frame_cells in FR.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. unfold MEMCPY_ICPT_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_15a5f8 _ RCc) as KR. clear RCc.

step. stp. step. clear KR.
assert (SRCc : bytes_at asegs mc srcA src).
{ eapply bytes_at_transport; [exact SRC| exact MUs|]. cbn. rewrite LEN, Z2Nat.id by lia. lia. }
assert (DSTc : rw_cells asegs mc dst [CB (Z.to_nat n) junk]).
{ eapply rw_cells_transport; [exact DST| exact MUs| exact WM|]. cbn. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }

assert (MU : munch [(dst, dst + n); (lo, bv_unsigned sp)] m mc)
by (eapply munch_weaken; [| exact MUs]; unfold sub_fp; cbn; intros x Hx; lia).
clear MUs.

(call_u (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc src junk);
[rewrite unsigned_lit by lia; exact SRCc| rewrite unsigned_lit by lia; exact LEN| rewrite !unsigned_lit by lia; exact DSTc
| rewrite !unsigned_lit by lia; exact SEP| exact MI|]).
all: replace (ret_pc (wz 0x62a40)) with (wz 0x62a40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
all: do 12 istep.
all: match goal with ST1 : stk asegs ?mc lo _, ST2x : stk asegs ?mc (bv_unsigned sp + -2160) _ |- _ =>
pose proof (stk_merge asegs _ _ _ _ ST1 ST2x ltac:(lia)) as STm; clear ST1 ST2x end.
all: match goal with FRx : rw_cells asegs ?mc (bv_unsigned sp + -80) _, STx : stk asegs ?mc lo _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
all: step.
all: apply evt_done; unfold POST, memcpy_icpt_post; do 15 eexists; split; [reflexivity|].
all: rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit srcA) by lia.
all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

Local Ltac at_mc MUs WM :=
lazymatch type of MUs with munch _ m ?mc =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SBc;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc
end.

Lemma memcpy_icpt_to : forall mc (rav t0 t1 t2 a3 a4 a5 a6 a7 s1v s2v s3v s5v s7v s8v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -2160) -> stk asegs mc (usp + -2160) (usp + -80) ->
rw_cells asegs mc (usp + -80) (frame_cells s8 s7 s6 s5 s4 s3 s2 s1 s0) ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR rav (wz (usp + -2160)) gp tp t0 t1 t2 sp s1v (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2v s3v (wz (dst + n)) s5v (wz (n + -65)) s7v s8v s9 s10 s11 t3 t4 t5 t6)
F (wz 0x629ec) fc None mc (seg_rom asegs)).
Proof.
intros until s11; intros MUs WM MI ST ST2 FR. unfold frame_cells in FR.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. unfold MEMCPY_ICPT_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.

step. step. rewrite (unsigned_lit dst), zb_lxor_ones by lia. ifz.

step. step.
destruct (Z.eq_dec n 0) as [Nz|Nz].
{
if_cases K1; zify_cond K1; rewrite ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Nz; Z.div_mod_to_equations; lia].
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia; [exfalso; lia|]. step.
eapply memcpy_icpt_tail; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR]. }
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct RD as (_ & _ & SOK & _ & NB). destruct (NB ltac:(lia)) as [[w3 W3] [w4 W4]]. pose proof (SOK ltac:(lia)) as SOd.
pose proof (rw_cells_below m mc _ _ _ W3 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W3c.
pose proof (rw_cells_below m mc _ _ _ W4 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W4c.
clear W3 W4.
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SOd| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. destruct SBc as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. stp. step. stp. stp.
rewrite (unsigned_lit dst), (unsigned_lit (dst + n + -1)) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (dst + n + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH dst /\ SH dst <= SH (dst + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH dst)), (unsigned_lit (SH (dst + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH dst - SH dst mod 8) with (8 * (SH dst / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (dst + n - 1) - SH (dst + n - 1) mod 8) with (8 * (SH (dst + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.

destruct (shadow_ok_last _ dst n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ dst n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x62a34) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (dst + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (dst + n - 1)) (SH dst)) as [X1|X1].
+ ifz. replace (SH dst) with (SH (dst + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_at 0x62dc0 (or_intror eq_refl) (Z.to_nat (SH (dst + n - 1) - SH dst)) (SH dst)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.
eapply memcpy_icpt_tail; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR].
-
destruct RD as (_ & _ & SOK & BIG & _). destruct (BIG ltac:(lia)) as (KD & N43). pose proof (SOK ltac:(lia)) as SOd.
ifz. step. ifz.
step. step. step. step.
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SOd| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. pose proof (rt_mem_cells_of _ SBc RCc) as RTM. clear SBc RCc.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia| exact SO'| lia| lia| lia| exact KD|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST' end.
step. step. step. step. step. ifz.
eapply memcpy_icpt_tail; [eassumption| eassumption| eassumption| exact ST'| eassumption| eassumption].
Qed.

Lemma memcpy_icpt_from : forall mc (rav t0 t1 t2 a3 a4 a5 a6 a7 s1v s2v s5v s6v s7v s8v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -2160) -> stk asegs mc (usp + -2160) (usp + -80) ->
rw_cells asegs mc (usp + -80) (frame_cells s8 s7 s6 s5 s4 s3 s2 s1 s0) ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR rav (wz (usp + -2160)) gp tp t0 t1 t2 sp s1v (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2v (wz (srcA + n)) (wz (dst + n)) s5v s6v s7v s8v s9 s10 s11 t3 t4 t5 t6)
F (wz 0x629a0) fc None mc (seg_rom asegs)).
Proof.
intros until s11; intros MUs WM MI ST ST2 FR.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCPY_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.

step. step. rewrite (unsigned_lit srcA), zb_lxor_ones by lia. ifz.

step. step. step.
destruct (Z.eq_dec n 0) as [Nz|Nz].
{
if_cases K1; zify_cond K1; rewrite ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Nz; Z.div_mod_to_equations; lia].
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia; [exfalso; lia|]. step.
eapply memcpy_icpt_to; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR]. }
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct RS as (_ & _ & SOK & _ & NB). destruct (NB ltac:(lia)) as [[w1 W1] [w2 W2]]. pose proof (SOK ltac:(lia)) as SOs.
pose proof (rw_cells_below m mc _ _ _ W1 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W1c.
pose proof (rw_cells_below m mc _ _ _ W2 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W2c.
clear W1 W2.
assert (SO' : shadow_ok mc srcA n)
by (eapply shadow_ok_munch; [exact SOs| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. destruct SBc as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. stp. step. stp. stp.
rewrite (unsigned_lit srcA), (unsigned_lit (srcA + n + -1)) by lia.
replace (2147450880 + srcA ≫ 3) with (SH srcA) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (srcA + n + -1) ≫ 3) with (SH (srcA + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH srcA /\ SH srcA <= SH (srcA + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH srcA)), (unsigned_lit (SH (srcA + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH srcA - SH srcA mod 8) with (8 * (SH srcA / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (srcA + n - 1) - SH (srcA + n - 1) mod 8) with (8 * (SH (srcA + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.

destruct (shadow_ok_last _ srcA n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ srcA n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x629ec) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (srcA + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (srcA + n - 1)) (SH srcA)) as [X1|X1].
+ ifz. replace (SH srcA) with (SH (srcA + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_at 0x62cc0 (or_introl eq_refl) (Z.to_nat (SH (srcA + n - 1) - SH srcA)) (SH srcA)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.
replace (srcA + n + -1) with (srcA + n - 1) by lia.
eapply memcpy_icpt_to; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR].
-
destruct RS as (_ & _ & SOK & BIG & _). destruct (BIG ltac:(lia)) as (KS & N43). pose proof (SOK ltac:(lia)) as SOs.
ifz. step. ifz.
step. step. step. step. step.
assert (SO' : shadow_ok mc srcA n)
by (eapply shadow_ok_munch; [exact SOs| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. pose proof (rt_mem_cells_of _ SBc RCc) as RTM. clear SBc RCc.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia| exact SO'| lia| lia| lia| exact KS|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST' end.
step. step. step. step. step. ifz.
eapply memcpy_icpt_to; [eassumption| eassumption| eassumption| exact ST'| eassumption| eassumption].
Qed.

Lemma memcpy_icpt_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
mem_inv asegs m -> stk asegs m lo usp ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memcpy_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros MI ST.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCPY_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.

set (BAh := bytes_at) in SRC. set (RWh := rw_cells) in DST.
unfold memcpy_stub. step.
carve_frame 80%nat ST.
do 11 istep.
step. step.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_1588c8 _ RCc) as K10. pose proof (rt_161720 _ RCc) as K18. clear RCc.
step. stp. stp. clear K10 K18.
step. ifz.
stp. stp. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2160) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2160) _ ST ltac:(lia))) as ST2. clear ST.

step. if_cases K1; [eapply memcpy_icpt_from; [exact MUs| exact WM| exact MI| exact ST1| exact ST2| exact FR]|].
step. if_cases K2; [eapply memcpy_icpt_from; [exact MUs| exact WM| exact MI| exact ST1| exact ST2| exact FR]|].
zify_cond K2. rewrite ?(unsigned_lit srcA), ?(unsigned_lit (dst + n)) in K2 by lia.
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit dst), ?(unsigned_lit (srcA + n)) in K3 by lia; [exfalso; lia|].
eapply memcpy_icpt_from; [exact MUs| exact WM| exact MI| exact ST1| exact ST2| exact FR].
Qed.
End S.

Theorem memcpy_icpt_spec {BAND : Band} :
forall (dst srcA n lo : Z) (src junk : list byte),
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),

bytes_at asegs m srcA src -> length src = Z.to_nat n -> rw_cells asegs m dst [CB (Z.to_nat n) junk] ->
srcA + n <= dst \/ dst + n <= srcA -> mem_inv asegs m -> 0 <= n ->

stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MEMCPY_ICPT_STACK ->
srcA + n <= lo \/ bv_unsigned sp <= srcA -> dst + n <= lo \/ bv_unsigned sp <= dst ->

shadow_base asegs m -> rt_consts_at asegs m ->

rng_ok m srcA n -> rng_ok m dst n ->
evt asegs (memcpy_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memcpy_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros SRC LEN DST SEP MI N0 ST CEIL LO SST DSTK SB RC RS RD.
eapply memcpy_icpt_main; eassumption.
Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig QDM6.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QNQk.Mq1 Q9Ho.Mq2 Q9Ho.Mq1. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma hjunk_C8x5 : forall m a, hjunk m a (a + 40) -> exists q0 q1 q2 q3 q4 : word, rw_cells asegs m a [C8 q0; C8 q1; C8 q2; C8 q3; C8 q4].
Proof.
intros m a J. destruct (hjunk_split m a (a + 16) (a + 40) J ltac:(lia)) as [J1 J2].
destruct (hjunk_C8x2 m a J1) as (q0 & q1 & H1).
destruct (hjunk_split m (a + 16) (a + 16 + 16) (a + 40) J2 ltac:(lia)) as [J3 J4].
destruct (hjunk_C8x2 m (a + 16) J3) as (q2 & q3 & H2).
replace (a + 40) with (a + 16 + 16 + 8) in J4 by lia. destruct (hjunk_C8 m (a + 16 + 16) J4) as (q4 & H3).
exists q0, q1, q2, q3, q4.
apply (proj2 (rw_cells_app asegs m a [C8 q0; C8 q1] [C8 q2; C8 q3; C8 q4])). split; [exact H1|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m (a + 16) [C8 q2; C8 q3] [C8 q4])). split; [exact H2|]. cbn [cells_size csize Nat.add]. exact H3.
Qed.

Lemma unw_readable_prologue : forall RE W m m' (bp : Z) (s0v rav : word),
munch W m m' -> (forall x, bp <= x -> outside W x) ->
rw_cells asegs m' (bp - 16) [C8 s0v; C8 rav] ->
unw_readable asegs RE m bp -> unw_readable asegs RE m' (bp - 16).
Proof.
intros RE W m m' bp s0v rav MU OUT FR UR x Hx XR.
destruct (Z.lt_ge_cases x bp) as [LOW|HIGH].
- pose proof (rw_cells_bytes_at asegs m' (bp - 16) _ FR) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
destruct B as (_ & _ & B). specialize (B (Z.to_nat (x - (bp - 16)))).
replace (bp - 16 + Z.of_nat (Z.to_nat (x - (bp - 16)))) with x in B by lia.
assert (LL : (Z.to_nat (x - (bp - 16)) < length (le8 s0v ++ le8 rav))%nat) by (rewrite length_app, !length_le8; lia).
rewrite (B LL). destruct (nth_error (le8 s0v ++ le8 rav) (Z.to_nat (x - (bp - 16)))) as [b|] eqn:E; [exists b; reflexivity|].
apply nth_error_None in E. lia.
- destruct (UR x ltac:(lia) XR) as (b & E). exists b. unfold mrd in *. rewrite (MU (wa x)); [exact E|].
rewrite wa_unsigned by lia. apply OUT. lia.
Qed.

Lemma alb_remove_perm : forall p LB LB', Permutation LB LB' -> Permutation (alb_remove p LB) (alb_remove p LB').
Proof.
intros p LB LB' P. unfold alb_remove. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
- constructor.
- destruct (negb (aptr_eqb (ablk_id x) p)); [apply perm_skip; exact IH| exact IH].
- destruct (negb (aptr_eqb (ablk_id y) p)), (negb (aptr_eqb (ablk_id x) p)); try apply perm_swap; try apply Permutation_refl; apply perm_skip; apply Permutation_refl.
- eapply perm_trans; eassumption.
Qed.

Lemma alb_remove_sub : forall p LB b, In b (alb_remove p LB) -> In b LB.
Proof. intros p LB b H. apply In_alb_remove in H as [H _]. exact H. Qed.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 QmP7.Mq0 Q9Ho.Mq1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Lemma cr_pure_div8 : forall a G c K, cr_pure a G c K -> 1 <= c <= 31 ->
(exists qa, 0 <= qa /\ c_alloc_user (cls a c) = 8 * qa /\ qa = ncarved G c * (class_size c / 8))
/\ (exists qm, 0 <= qm /\ c_mapped_user (cls a c) = 8 * qm)
/\ class_size c = 8 * (class_size c / 8).
Proof.
intros a G c K PU Hc. pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5). rewrite KM in G5.
pose proof (class_size_facts c Hc) as [S1 S2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; lia).
split; [| split; [| exact E8]].
- exists (ncarved G c * (class_size c / 8)). unfold ncarved. split; [nia|]. split; [| reflexivity]. rewrite <- G1. nia.
- exists (c_mapped_user (cls a c) / 8). Z.div_mod_to_equations. lia.
Qed.

Definition cr_slots (a : AState) (G : ghost) (RE : aentry) (m : mem) (c : Z) : Prop :=
(forall i t, tag_at G c i = Some t -> tag_prim t = true -> hjunk m (slot_beg RE c i) (slot_beg RE c i + class_size c))
/\ (forall i t, tag_at G c i = Some t -> tag_prim t = true ->
rw_cells asegs m (SH (slot_beg RE c i)) [CB (Z.to_nat (class_size c / 8)) (repeat fa_byte (Z.to_nat (class_size c / 8)))]).

Lemma cr_user_split : forall a G RE m c,
cr_user a G RE m c <->
cr_slots a G RE m c
/\ hjunk m (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) (reg_beg (ae_L RE) c + c_mapped_user (cls a c))
/\ rw_cells asegs m (SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)))
[CB (Z.to_nat ((c_mapped_user (cls a c) - c_alloc_user (cls a c)) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user (cls a c) - c_alloc_user (cls a c)) / 8)))]
/\ hjunk m (SH (reg_beg (ae_L RE) c + c_mapped_user (cls a c))) (SH (reg_beg (ae_L RE) c + kFreeArrayOffset)).
Proof. intros. unfold cr_user, cr_slots. tauto. Qed.

Definition szone (RE : aentry) (c au : Z) (z : Z) : Prop :=
(reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + au) \/ (SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + au / 8).

Lemma cr_slots_agree : forall a G RE m m' c K,
cr_pure a G c K -> cr_slots a G RE m c -> 1 <= c <= 31 ->
agree_on asegs (szone RE c (c_alloc_user (cls a c))) m m' -> cr_slots a G RE m' c.
Proof.
intros a G RE m m' c K PU [SL SS] Hc AG.
pose proof (cr_pure_div8 a G c K PU Hc) as ((qa & QA0 & QA & QAE) & _ & E8).
pose proof (class_size_facts c Hc) as [S1 S2].
assert (GEOM : forall i t, tag_at G c i = Some t ->
0 <= i /\ (i + 1) * class_size c <= c_alloc_user (cls a c) /\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c).
{ intros i t Ht. pose proof (tag_at_Some_lt _ _ _ _ Ht) as [I1 I2]. rewrite QA, QAE. split; [lia|]. split; [nia| reflexivity]. }
split.
- intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (GEOM i t Ht) as (I1 & IL & SB). rewrite SB in Hz. left. clear - Hz I1 IL S1. nia.
- intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (GEOM i t Ht) as (I1 & IL & SB). rewrite SB in Hz.
replace (i * class_size c) with (8 * (i * (class_size c / 8))) in Hz by nia. rewrite SH_plus8 in Hz.
right. rewrite QA, Z.mul_comm, Z.div_mul by lia. clear - Hz I1 IL S1 E8 QA QA0. nia.
Qed.

Lemma cr_slots_ext : forall a a' G RE m c, cr_slots a G RE m c -> cr_slots a' G RE m c.
Proof. intros. exact H. Qed.

Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
wr_at asegs m a n1 -> wr_at asegs m (a + n1) n2 -> wr_at asegs m a (n1 + n2).
Proof.
intros m a n1 n2 H1 H2 (A1 & B1 & W1) (A2 & B2 & W2). split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i n1).
- apply W1. lia.
- replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Lemma u32arr_nil : forall m A, 0 <= A <= 2^64 -> u32arr asegs m A [].
Proof. intros m A H. split; [apply bytes_at_nil; exact H|]. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.

Lemma u32arr_cons : forall m A (v : word) ws,
rw_cells asegs m A [C4 v] -> u32arr asegs m (A + 4) ws -> u32arr asegs m A (v :: ws).
Proof.
intros m A v ws [[_ HB] HW] [AB AW]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in HB, HW. rewrite app_nil_r in HB.
split.
- cbn [u32s]. apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite length_le4. split; [exact HB| exact AB].
- cbn [length]. replace (4 * Z.of_nat (S (length ws))) with (4 + 4 * Z.of_nat (length ws)) by lia.
apply wr_at_app; [lia| lia| exact HW| exact AW].
Qed.

Lemma u32arr_app : forall m A ws1 ws2,
u32arr asegs m A ws1 -> u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr asegs m A (ws1 ++ ws2).
Proof.
intros m A ws1 ws2 [B1 W1] [B2 W2]. split.
- rewrite u32s_app. apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite u32s_length.
split; [exact B1|]. replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) by lia. exact B2.
- rewrite length_app. replace (4 * Z.of_nat (length ws1 + length ws2)) with (4 * Z.of_nat (length ws1) + 4 * Z.of_nat (length ws2)) by lia.
apply wr_at_app; [lia| lia| exact W1| exact W2].
Qed.

Lemma u32arr_hjunk : forall m A ws, u32arr asegs m A ws -> 0x645000 <= A -> hjunk m A (A + 4 * Z.of_nat (length ws)).
Proof.
intros m A ws [B W] HA. destruct W as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros a Ha.
specialize (W2 (a - A) ltac:(lia)). replace (A + (a - A)) with a in W2 by lia.
rewrite a_wview_overlay in W2 by (rewrite wa_unsigned by lia; lia). unfold wa in W2.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b| exfalso; apply W2; reflexivity].
rewrite <- E. reflexivity.
Qed.

End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC Qpj5 Q67d QUnM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 Q9Ho.Mq1.
Import QUnM.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Definition quar_img : list (Z * Z) :=
[ (A_INSTANCE + 728, 64); (A_INSTANCE + 816, 2800); (0x0f0d00, 0x81038); (0x17f588, 4) ].

Lemma quar_img_ok : forall x, in_ivs quar_img x ->
~ in_ivs rtconst_img x /\ ~ (A_INSTANCE + 104 <= x < A_INSTANCE + 728) /\ x <> 0x171d60 /\ ~ (A_ERRNO <= x < A_ERRNO + 4)
/\ ~ (0x1c19c8 <= x < 0x1c19c8 + 0x450028) /\ x < 0x645000 /\ 0x10000 <= x.
Proof.
intros x (iv & Hin & [H1 H2]).
assert (F : forallb (fun iv => forallb (fun jv => (fst iv + snd iv <=? fst jv) || (fst jv + snd jv <=? fst iv))
(rtconst_img ++ [(A_INSTANCE + 104, 624); (0x171d60, 1); (A_ERRNO, 4); (0x1c19c8, 0x450028)])
&& (fst iv + snd iv <=? 0x645000) && (0x10000 <=? fst iv)) quar_img = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in F. specialize (F iv Hin). apply andb_prop in F as [F F7]. apply Z.leb_le in F7. apply andb_prop in F as [F F6]. apply Z.leb_le in F6.
rewrite forallb_forall in F.
assert (D : forall jv, In jv (rtconst_img ++ [(A_INSTANCE + 104, 624); (0x171d60, 1); (A_ERRNO, 4); (0x1c19c8, 0x450028)]) ->
~ (fst jv <= x < fst jv + snd jv)).
{ intros jv Hjv Hx. specialize (F jv Hjv). apply orb_prop in F as [F|F]; apply Z.leb_le in F; lia. }
split; [| split; [| split; [| split; [| split; [| split; lia]]]]].
- intros (jv & Hjv & [J1 J2]). apply (D jv); [apply in_app_iff; left; exact Hjv| lia].
- intros Hx. apply (D (A_INSTANCE + 104, 624)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
- intros ->. apply (D (0x171d60, 1)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
- intros Hx. apply (D (A_ERRNO, 4)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
- intros Hx. apply (D (0x1c19c8, 0x450028)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
Qed.

Section Excl.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.

Let RL : rlay_ok RE X := gc_rlay a LB0 FS0 G RE X GC.

Inductive qloc (x : Z) : Prop :=
| QL_T    : rl_T X + 80 <= x < rl_T X + 208 -> qloc x
| QL_img  : in_ivs quar_img x -> qloc x
| QL_slot : forall c i t, tag_at G c i = Some t -> tag_quar t = true -> in_iv (slot_beg RE c i, class_size c) x -> qloc x
| QL_slsh : forall c i t, tag_at G c i = Some t -> tag_quar t = true -> in_sh (slot_beg RE c i, class_size c) x -> qloc x
| QL_sec  : forall e, In e (as_reg a) -> ~ sec_live LB0 e -> se_beg e + kPage <= x < se_beg e + se_size e -> qloc x
| QL_sesh : forall e, In e (as_reg a) -> ~ sec_live LB0 e -> in_sh (se_beg e + kPage, se_size e - kPage) x -> qloc x.

Lemma fp_RQuar_loc : forall x, fp_RQuar a LB0 G RE X x -> qloc x.
Proof.
intros x [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- apply QL_T. destruct H; cbn [fst snd] in *; lia.
- apply QL_img. exists (A_INSTANCE + 728, 64). split; [cbn; tauto| exact H].
- apply QL_img. exists (A_INSTANCE + 816, 2800). split; [cbn; tauto| exact H].
- apply QL_img. exists (0x0f0d00, 0x81038). split; [cbn; tauto| exact H].
- apply QL_img. exists (0x17f588, 4). split; [cbn; tauto| exact H].
- destruct H as (c & i & t & Ht & Hq & Hx). eapply QL_slot; eauto.
- destruct H as (c & i & t & Ht & Hq & Hx). eapply QL_slsh; eauto.
- destruct H as (e & He & NL & Hx). eapply QL_sec; eauto.
- destruct H as (e & He & NL & Hx). eapply QL_sesh; eauto.
Qed.

Local Ltac zfacts :=
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & TC & TP & TA); cbn [fst snd] in TK, TC, TP, TA;
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _ & AK & AC & PA);
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _);
unfold iv_disjoint, prim_hi, ptrarr_hi in TP, TA, PA, PC, AC; cbn [fst snd] in TP, TA, PA;
pose proof SH_band as SHB0;
rewrite ?KHI_eq in *.

Local Ltac lit := rewrite ?KHI_eq in *.

Local Ltac shband H :=
lazymatch type of H with in_sh (?lo, ?len) ?x =>
let B := fresh "SB" in
assert (B : kLowEnd <= x < KHI)
by (apply (in_sh_band lo len x);
[first [assumption| Z.div_mod_to_equations; lia]| lia| rewrite ?KHI_eq in *; lia| idtac; unfold prim_hi in *; lia| exact H]);
unfold kLowEnd, KHI in B
end.

Lemma qslot_facts : forall c i t, tag_at G c i = Some t ->
prim_lo RE <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= prim_hi RE /\ slot_beg RE c i mod 8 = 0
/\ 1 <= c <= 31 /\ reg_beg (ae_L RE) c <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= reg_beg (ae_L RE) c + kFreeArrayOffset
/\ 32 <= class_size c /\ reg_beg (ae_L RE) c = prim_lo RE + c * 2^32 /\ fa_beg (ae_L RE) c = reg_beg (ae_L RE) c + kFreeArrayOffset.
Proof.
intros c i t Ht. pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & P3 & _ & C1 & R1 & R2 & S1 & _).
pose proof (region_in_prim RE c C1) as (Q1 & Q2 & Q3 & Q4). repeat split; try assumption; lia.
Qed.

Lemma qsec_facts : forall e, In e (as_reg a) ->
se_beg e mod 4096 = 0 /\ appr_lia (se_beg e) (se_size e) /\ se_beg e + se_size e <= band_lo /\ kPage + 16 <= se_size e
/\ iv_disjoint (se_beg e, se_size e) (prim_lo RE, 2^37 + 0x1000)
/\ iv_disjoint (se_beg e, se_size e) (ptrarr_lo RE, 0x800000)
/\ Forall (iv_disjoint (se_beg e, se_size e)) (rlay_objs RE X).
Proof.
intros e He. pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
pose proof kconsts as (_ & _ & _ & _ & KP & _). rewrite KP in *. split; [exact E1|]. split; [apply appr_to_lia; [lia| lia| exact E2]|]. repeat split; try assumption. lia.
Qed.

Lemma obj_vs_T : forall o x, In o (rlay_objs RE X) -> o <> (rl_T X, 0x1000) -> in_iv o x -> rl_T X <= x < rl_T X + 0x1000 -> False.
Proof.
intros o x Ho NE [O1 O2] Hx.
pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (T_obj RE X) NE) as D. unfold iv_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma obj_vs_sec : forall o e x, In o (rlay_objs RE X) -> In e (as_reg a) -> in_iv o x -> se_beg e <= x < se_beg e + se_size e -> False.
Proof.
intros o e x Ho He [O1 O2] Hx. pose proof (qsec_facts e He) as (_ & _ & _ & _ & _ & _ & F). lit.
pose proof (proj1 (List.Forall_forall _ _) F o Ho) as D. unfold iv_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma fpQ_RTconst : forall x, fp_RQuar a LB0 G RE X x -> fp_RTconst RE X x -> False.
Proof.
intros x FQ FT. zfacts. destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- exact (rt_avoid_Thigh RE X (rl_T X + 80) (rl_T X + 208) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT).
- pose proof (quar_img_ok x H) as (NI & _ & _ & _ & _ & LT & GT).
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & HO)].
2:{ pose proof (rl_objs_lia a LB0 FS0 G RE X GC o Ho) as (_ & K & _). destruct HO as [O1 O2]. rewrite ?KHI_eq in K. lia. }
destruct FT as [F|[F|[F|F]]]; [exact (NI F)| destruct F; cbn [fst snd] in *; lia| |].
+ pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ctx_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
+ pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dtls_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H; cbn [fst snd] in *.
exact (rt_avoid_prim RE X RL (slot_beg RE c i) (slot_beg RE c i + class_size c) P1 P2 x ltac:(split; cbn [fst snd]; lia) FT).
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & HO)]; [lia|]. eapply obj_vs_sec; [exact Ho| exact He| exact HO| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H.
exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
Qed.

Lemma fpQ_RStats : forall x, fp_RQuar a LB0 G RE X x -> fp_RStats RE X x -> False.
Proof.
intros x FQ FS. zfacts. unfold fp_RStats, A_ERRNO in FS. cbn [in_iv fst snd] in FS. unfold in_iv in FS. cbn [fst snd] in FS.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- lia.
- pose proof (quar_img_ok x H) as (_ & _ & N1 & N2 & _ & LT). unfold A_ERRNO in N2. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H; cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 H0 H i c KO PA AK PK TA TP FS x X RE BAND; lia | lia ]).
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H. (first [ clear - SB P3 P1 i c PA AK PK TA TP TK FS x X RE BAND; lia | lia ]).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct FS as [F|[F|F]]; [| lia| lia]. eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H. (first [ clear - SB E2 e PA AK PK TA TP TK FS x X RE BAND; lia | lia ]).
Qed.

Lemma fas_band : forall c y, 1 <= c <= 31 -> in_sh (fa_beg (ae_L RE) c, kFreeArraySize) y -> 0x2008fff7000 <= y < SH band_lo.
Proof.
intros c y Hc F. zfacts. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL).
apply (in_sh_heap _ kFreeArraySize y FAL); [lia| rewrite ?KHI_eq; lia| idtac; unfold prim_lo in *; lia| exact F].
Qed.
Lemma reg_band : forall c y, 1 <= c <= 31 -> in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) y -> 0x2008fff7000 <= y < SH band_lo.
Proof.
intros c y Hc F. zfacts. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (RAL & _).
apply (in_sh_heap _ kFreeArrayOffset y RAL); [lia| rewrite ?KHI_eq; lia| idtac; unfold prim_lo in *; lia| exact F].
Qed.
Lemma slot_band : forall c i t y, tag_at G c i = Some t -> in_sh (slot_beg RE c i, class_size c) y -> 0x2008fff7000 <= y < SH band_lo.
Proof.
intros c i t y Ht F. zfacts. pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB).
apply (in_sh_heap _ (class_size c) y P3); [lia| rewrite ?KHI_eq; lia| idtac; unfold prim_hi in *; lia| exact F].
Qed.
Lemma sec_band : forall e y, In e (as_reg a) -> in_sh (se_beg e + kPage, se_size e - kPage) y -> 0x7fff7000 <= y < 0x10007fff8000.
Proof.
intros e y He F. zfacts. pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _).
pose proof (in_sh_band (se_beg e + kPage) (se_size e - kPage) y ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(rewrite KP in *; lia) ltac:(lia) F) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.
Lemma hdr_band : forall e y, In e (as_reg a) -> in_sh (se_beg e, kPage) y -> 0x7fff7000 <= y < 0x10007fff8000.
Proof.
intros e y He F. zfacts. pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _).
pose proof (in_sh_band (se_beg e) kPage y ltac:(Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(rewrite KP in *; lia) ltac:(lia) F) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.
Lemma fs_band : forall y, in_sh (ae_fs_base RE, A_FS_MAP_SIZE) y -> 0x7fff7000 <= y < 0x10007fff8000.
Proof.
intros y F. pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE y ltac:(Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; lia) FC F) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.

Lemma fpQ_RPrim : forall x, fp_RQuar a LB0 G RE X x -> fp_RPrim G RE X x -> False.
Proof.
intros x FQ FP. zfacts.

assert (PW : (prim_lo RE <= x < prim_hi RE /\ ~ in_slots (fun t => negb (tag_prim t)) RE G x)
\/ rl_T X + 208 <= x < rl_T X + 2800
\/ (0x2008fff7000 <= x < SH band_lo
/\ ((exists c, 1 <= c <= 31 /\ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) x)
\/ ((exists c, 1 <= c <= 31 /\ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) x) /\ ~ in_slots_sh (fun t => negb (tag_prim t)) RE G x)))).
{ destruct FP as [F|[F|[F|[F|[[F NS]|[F NS]]]]]].
- left. destruct F as [F1 F2]; cbn [fst snd] in F1, F2. split; [unfold region_info, prim_hi, prim_lo in *; lia|].
intros (c & i & t & Ht & _ & [S1 S2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & Sz & RB & FB). cbn [fst snd] in S1, S2.
unfold region_info, prim_hi, prim_lo in *. rewrite KO in *. lia.
- right; left. destruct F; cbn [fst snd] in *. lia.
- left. destruct F as (c & Hc & F). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). split; [unfold prim_hi, prim_lo in *; lia|].
intros (c' & i & t & Ht & _ & [S1 S2]). pose proof (qslot_facts c' i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & Sz & RB & FB). cbn [fst snd] in S1, S2.
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
- right; right. destruct F as (c & Hc & F). rewrite K32 in Hc. split; [exact (fas_band c x ltac:(lia) F)|]. left. exists c. split; [lia| exact F].
- left. destruct F as (c & Hc & F). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). unfold prim_hi, prim_lo in *. split; [lia| exact NS].
- right; right. destruct F as (c & Hc & F). rewrite K32 in Hc. split; [exact (reg_band c x ltac:(lia) F)|]. right. split; [| exact NS]. exists c. split; [lia| exact F]. }
clear FP.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
-  unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[PW _]]]; lia.
-  pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[PW _]]]; lia.
-  pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
unfold prim_hi, prim_lo in *. destruct PW as [[PW NS]|[PW|[PW _]]]; [| (first [ clear - R2 R1 P3 P2 P1 H2 H1 i c PW KO PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
apply NS. exists c, i, t. split; [exact Ht|]. split; [destruct t; cbn in Hq |- *; congruence|]. split; cbn [fst snd]; lia.
-  pose proof (slot_band c i t x Ht H) as SB. pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[_ [(c' & Hc' & F)|[(c' & Hc' & F) NS]]]]]; [lia| lia| |].
+ pose proof (region_in_prim RE c' Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c' RL) as (_ & _ & FAL).
eapply (in_sh_disjoint (slot_beg RE c i) (class_size c) (fa_beg (ae_L RE) c') kFreeArraySize x P3 FAL ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
+ apply NS. exists c, i, t. split; [exact Ht|]. split; [destruct t; cbn in Hq |- *; congruence| exact H].
-  pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[PW _]]]; [(first [ clear - D2 D1 E4 E2 H e PW KP PA AK PK TA TP x X RE BAND; lia | lia ])| | lia].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
-  pose proof (sec_band e x He H) as SB. pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[_ [(c' & Hc' & F)|[(c' & Hc' & F) NS]]]]]; [lia| lia| |].
+ pose proof (region_in_prim RE c' Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c' RL) as (_ & _ & FAL).
eapply (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (fa_beg (ae_L RE) c') kFreeArraySize x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) FAL ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - FAL Q3 Q2 Q1 D2 D1 E4 E2 E1 e c' KP KS KO PA AK PK TA TP X RE BAND; lia | lia ]).
+ pose proof (region_in_prim RE c' Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c' RL) as (RAL & _).
eapply (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (reg_beg (ae_L RE) c') kFreeArrayOffset x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) RAL ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - RAL Q4 Q3 Q2 Q1 D2 D1 E4 E2 E1 e Hc' c' KP KS KO PA AK PK TA TP X RE BAND; lia | lia ]).
Qed.

Lemma fpQ_RChunks : forall x, fp_RQuar a LB0 G RE X x -> fp_RChunks a LB0 G RE X x -> False.
Proof.
intros x FQ FC. zfacts.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 H KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband F. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT).
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband F. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & Hl & [F1 F2]). cbn [fst snd] in F1, F2.
assert (NE : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [->|]; [right; intros ->; rewrite Ht in Ht'; inversion Ht'; subst; destruct t'; discriminate| left; assumption]).
pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' t' Ht Ht' NE). (first [ clear - H P3 P1 H2 H1 i c PA AK PK TA TP F2 F1 i' c' x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1. (first [ clear - D1 E2 RB R2 R1 C1 P3 P1 H2 H1 i c KP KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (qslot_facts c' i' t' Ht') as (P1' & P2' & P3' & C1' & R1' & R2' & S1' & RB' & FB'). lit. shband F. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1' & P2' & P3' & C1' & R1' & R2' & S1' & RB' & FB'). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c' & i' & t' & Ht' & Hl & F). pose proof (qslot_facts c' i' t' Ht') as (P1' & P2' & P3' & C1' & R1' & R2' & S1' & RB' & FB'). lit.
assert (NE : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [->|]; [right; intros ->; rewrite Ht in Ht'; inversion Ht'; subst; destruct t'; discriminate| left; assumption]).
pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' t' Ht Ht' NE) as D.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (slot_beg RE c' i') (class_size c') x P3 P3' ltac:(lia) ltac:(lia) D H F).
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (se_beg e + kPage) (se_size e - kPage) x P3 ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E2 RB R2 R1 C1 P3 P1 i c KP KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 D2 D1 E4 E2 H e KP KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & HL & F). assert (e' = e) as -> by (apply (sec_same a LB0 FS0 G RE X GC e' e x He' He); lia). exact (NL HL).
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband F. lia.
+ destruct F as (e' & He' & _ & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. shband F. lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2. shband H.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e' & He' & _ & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. lia.
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (slot_beg RE c i) (class_size c) x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) P3 ltac:(lia) ltac:(lia) ltac:((first [ clear - RB R2 R1 C1 P3 P1 D2 D1 E4 E2 e KP KO PA AK PK TA TP i c X RE BAND; lia | lia ])) H F).
+ destruct F as (e' & He' & HL & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
assert (DD : se_beg e + se_size e <= se_beg e' \/ se_beg e' + se_size e' <= se_beg e).
{ destruct (decide (se_beg e = se_beg e')) as [EQ|NEb].
- exfalso. pose proof (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' EQ) as <-. exact (NL HL).
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e' (gc_sec_disj a LB0 FS0 G RE X GC) He He'
ltac:(intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd] in D. lia. }
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (se_beg e' + kPage) (se_size e' - kPage) x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1' r0 D2 D1 E4 e KP PA AK PK TA TP e' X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - DD E2' D2 D1 E4 E2 e KP PA AK PK TA TP e' X RE BAND; lia | lia ])) H F).
Qed.

Lemma fpQ_RSec : forall x, fp_RQuar a LB0 G RE X x -> fp_RSec a RE X x -> False.
Proof.
intros x FQ FS. zfacts.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| pose proof (qsec_facts e He) as (_ & _ & _ & E4 & _); lia].
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (quar_img_ok x H) as (_ & NS & _ & _ & _ & LT).
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. apply NS. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1. (first [ clear - D1 E4 E2 RB R2 R1 C1 P3 P1 H2 H1 i c KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (se_beg e) kPage x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 RB R2 R1 C1 P3 P1 i c KP KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. (first [ clear - D2 D1 E4 E2 H e KP PA AK PK TA TP H1 H0 x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & F). assert (e' = e) as -> by (apply (sec_same a LB0 FS0 G RE X GC e' e x He' He); [| lia]; pose proof (qsec_facts e' He') as (_ & _ & _ & E4' & _); lia). lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. shband F. lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2. shband H.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. (first [ clear - SB D2 D1 E4 E2 e KP PA AK PK TA TP H1 H0 x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
assert (DD : se_beg e + se_size e <= se_beg e' \/ se_beg e' + kPage <= se_beg e + kPage).
{ destruct (decide (se_beg e = se_beg e')) as [EQ|NEb].
- pose proof (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' EQ) as <-. right; lia.
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e' (gc_sec_disj a LB0 FS0 G RE X GC) He He'
ltac:(intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd] in D. (first [ clear - D NEb E4' E2' E1' D2 D1 E4 E2 E1 e KP PA AK PK TA TP e' X RE BAND; lia | lia ]). }
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (se_beg e') kPage x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1' r0 D2 D1 E4 e KP PA AK PK TA TP e' X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:(lia) H F).
Qed.

Lemma fpQ_RDepot : forall x, fp_RQuar a LB0 G RE X x -> fp_RDepot RE X x -> False.
Proof.
intros x FQ FD. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & NC & NP & _). cbn [fst snd] in NK, NC, NP. unfold iv_disjoint in NP; cbn [fst snd] in NP.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & BC & BP & _). cbn [fst snd] in BK, BC, BP. unfold iv_disjoint in BP; cbn [fst snd] in BP.
rewrite ?KHI_eq in *.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- destruct FD as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. lia.
+ eapply (obj_vs_T _ x (dn_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ eapply (obj_vs_T _ x (ssb_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & ND & LT).
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| lia].
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c NP KO PA AK PK TA TP H0 H x X RE BAND; lia | lia ])| destruct F; cbn [fst snd] in *; (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c BP KO PA AK PK TA TP H0 H x X RE BAND; lia | lia ])| (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c KO PA AK PK TA TP F x X RE BAND; lia | lia ])].
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct FD as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. lia.
+ eapply (obj_vs_sec _ e x (dn_obj RE X) He F). lia.
+ eapply (obj_vs_sec _ e x (ssb_obj RE X) He F). lia.
+ eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H.
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| lia].
Qed.

Lemma fpQ_RFake : forall x, fp_RQuar a LB0 G RE X x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x FQ FF. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & FP & _). cbn [fst snd] in FAL, FK, FC, FP. unfold iv_disjoint in FP; cbn [fst snd] in FP.
rewrite ?KHI_eq in *.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H]; destruct FF as [[F _]|[F _]].
- eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
- pose proof (fs_band x F). lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). destruct F; cbn [fst snd] in *. lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). pose proof (fs_band x F). lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; destruct F; cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c FP FK KO PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (fs_band x F). lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H. destruct F; cbn [fst snd] in *. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (ae_fs_base RE) A_FS_MAP_SIZE x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - RB R2 R1 C1 P3 P1 i c FP FK FAL KO PA AK PK TA TP X RE BAND; lia | lia ])) H F).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. eapply (obj_vs_sec _ e x (fs_obj RE X) He F). lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (fs_band x F). lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H. destruct F; cbn [fst snd] in *. lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 e PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - D E2 E1 e FK FAL KP PA AK PK TA TP X RE BAND; lia | lia ])) H F).
Qed.

Inductive ploc (x : Z) : Prop :=
| PL_ri    : region_info RE <= x < region_info RE + 0x1000 -> ploc x
| PL_T     : rl_T X + 208 <= x < rl_T X + 2800 -> ploc x
| PL_fas   : forall c, 1 <= c <= 31 -> fa_beg (ae_L RE) c <= x < fa_beg (ae_L RE) c + kFreeArraySize -> ploc x
| PL_fassh : forall c, 1 <= c <= 31 -> in_sh (fa_beg (ae_L RE) c, kFreeArraySize) x -> ploc x
| PL_reg   : forall c, 1 <= c <= 31 -> reg_beg (ae_L RE) c <= x < reg_beg (ae_L RE) c + kFreeArrayOffset ->
~ in_slots (fun t => negb (tag_prim t)) RE G x -> ploc x
| PL_regsh : forall c, 1 <= c <= 31 -> in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) x ->
~ in_slots_sh (fun t => negb (tag_prim t)) RE G x -> ploc x.

Lemma fp_RPrim_loc : forall x, fp_RPrim G RE X x -> ploc x.
Proof.
intros x [F|[F|[F|[F|[[F NS]|[F NS]]]]]]; pose proof kconsts as (_ & _ & _ & K32 & _).
- apply PL_ri. destruct F; cbn [fst snd] in *; lia.
- apply PL_T. destruct F; cbn [fst snd] in *; lia.
- destruct F as (c & Hc & F). apply (PL_fas x c); [rewrite K32 in Hc; lia| exact F].
- destruct F as (c & Hc & F). apply (PL_fassh x c); [rewrite K32 in Hc; lia| exact F].
- destruct F as (c & Hc & F). apply (PL_reg x c); [rewrite K32 in Hc; lia| exact F| exact NS].
- destruct F as (c & Hc & F). apply (PL_regsh x c); [rewrite K32 in Hc; lia| exact F| exact NS].
Qed.

Lemma fpP_RChunks : forall x, fp_RPrim G RE X x -> fp_RChunks a LB0 G RE X x -> False.
Proof.
intros x FP FC. zfacts.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS].
- unfold region_info, prim_lo in *. destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. unfold prim_lo in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. lia.
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F). lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). lia.
- destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. unfold prim_hi, prim_lo in *. (first [ clear - R2 R1 P3 P2 P1 H KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F). lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). lia.
- pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *.
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. unfold prim_lo in *. (first [ clear - D1 E2 Q3 Q2 Q1 H c KP KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_band c' i' t' x Ht' F). unfold prim_lo in *. lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). unfold prim_lo in *. lia.
- pose proof (fas_band c x Hc H) as SB. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL).
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
eapply (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (slot_beg RE c' i') (class_size c') x FAL P3 ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
eapply (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (se_beg e + kPage) (se_size e - kPage) x FAL ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - D1 E2 E1 FAL Q3 Q2 Q1 c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ]).
- pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & Hl & F). apply NS. exists c', i', t'. split; [exact Ht'|]. split; [destruct t'; try discriminate; reflexivity| exact F].
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. unfold prim_lo in *. lia.
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_band c' i' t' x Ht' F). unfold prim_lo in *. lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). unfold prim_lo in *. lia.
- pose proof (reg_band c x Hc H) as SB. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (RAL & _).
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c' & i' & t' & Ht' & Hl & F). apply NS. exists c', i', t'. split; [exact Ht'|]. split; [destruct t'; try discriminate; reflexivity| exact F].
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
eapply (in_sh_disjoint (reg_beg (ae_L RE) c) kFreeArrayOffset (se_beg e + kPage) (se_size e - kPage) x RAL ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - D1 E2 E1 RAL Q4 Q3 Q2 Q1 Hc c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ]).
Qed.

Lemma fpP_RSec : forall x, fp_RPrim G RE X x -> fp_RSec a RE X x -> False.
Proof.
intros x FP FS. zfacts.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL)
| pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (reg_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (RAL & _) ];
unfold prim_lo in *;
(destruct FS as [F|[F|[F|F]]];
[ destruct F; cbn [fst snd] in *; unfold A_INSTANCE in *; lia
| destruct F; cbn [fst snd] in *; (first [ clear - H PA AK PK TA TP H1 H0 x X RE BAND Q3 Q2 Q1 c KO FAL SB SHB0 KS RAL; lia | lia ])
| destruct F as (e & He & F); pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3); lit; unfold iv_disjoint in D1; cbn [fst snd] in D1
| destruct F as (e & He & F); pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3); lit; unfold iv_disjoint in D1; cbn [fst snd] in D1 ]).
all: unfold prim_hi, prim_lo in *; try (first [ clear - D1 E4 E2 H PA AK PK TA TP F e x X RE BAND Q3 Q2 Q1 c KO SB SHB0 KS; lia | lia ]).
all: try (pose proof (hdr_band e x He F); lia).
- eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
- exact (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (se_beg e) kPage x FAL ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 FAL Q3 Q2 Q1 c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
- exact (in_sh_disjoint (reg_beg (ae_L RE) c) kFreeArrayOffset (se_beg e) kPage x RAL ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 RAL Q3 Q2 Q1 c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
Qed.

Lemma fpP_RDepot : forall x, fp_RPrim G RE X x -> fp_RDepot RE X x -> False.
Proof.
intros x FP FD. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & NC & NP & _). cbn [fst snd] in NK, NC, NP. unfold iv_disjoint in NP; cbn [fst snd] in NP.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & BC & BP & _). cbn [fst snd] in BK, BC, BP. unfold iv_disjoint in BP; cbn [fst snd] in BP.
rewrite ?KHI_eq in *.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4) | pose proof (reg_band c x Hc H) as SB ];
unfold prim_lo in *; destruct FD as [F|[F|[F|F]]].
all: try (destruct F as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - H PK F2 x RE BAND NP PA AK TA TP F1 X BP TK Q2 Q1 c KO Q3 SB NK SHB0 BK Q4 Hc KS; lia | lia ])).
all: try (first [ clear - H PA AK PK TA TP F x X RE BAND Q3 Q2 Q1 c KO SB SHB0 TK KS; lia | lia ]).
- eapply (obj_vs_T _ x (dn_obj RE X)); [intros E; injection E; lia| exact F| lia].
- eapply (obj_vs_T _ x (ssb_obj RE X)); [intros E; injection E; lia| exact F| lia].
Qed.

Lemma fpP_RFake : forall x, fp_RPrim G RE X x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x FP FF. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & FP' & _). cbn [fst snd] in FAL, FK, FC, FP'. unfold iv_disjoint in FP'; cbn [fst snd] in FP'.
rewrite ?KHI_eq in *.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL2)
| pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (reg_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (RAL & _) ];
unfold prim_lo in *; destruct FF as [[F _]|[F _]]; try (destruct F; cbn [fst snd] in *; (first [ clear - H FP' FK PA AK PK TA TP H1 H0 x X RE BAND Q3 Q2 Q1 c KO SB SHB0 Q4 Hc KS; lia | lia ])); try (pose proof (fs_band x F); lia).
- eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
- exact (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (ae_fs_base RE) A_FS_MAP_SIZE x FAL2 ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - FAL2 Q3 Q2 Q1 c FP' FK FAL KS KO PA AK PK TA TP X RE BAND; lia | lia ])) H F).
- exact (in_sh_disjoint (reg_beg (ae_L RE) c) kFreeArrayOffset (ae_fs_base RE) A_FS_MAP_SIZE x RAL ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - RAL Q3 Q2 Q1 c FP' FK FAL KS KO PA AK PK TA TP X RE BAND; lia | lia ])) H F).
Qed.

Lemma fpP_RStats : forall x, fp_RPrim G RE X x -> fp_RStats RE X x -> False.
Proof.
intros x FP FS. zfacts. unfold fp_RStats, A_ERRNO, in_iv in FS. cbn [fst snd] in FS.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info, prim_lo in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4) | pose proof (reg_band c x Hc H) as SB ];
unfold prim_lo in *; (first [ clear - H PA AK PK TA TP FS x X RE BAND TK Q3 Q2 Q1 c KO SB SHB0 KS; lia | lia ]).
Qed.

Lemma fpS_excl : forall x, fp_RStats RE X x ->
(fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x \/ fp_RDepot RE X x \/ fp_RFake FS0 RE X x \/ fp_RTconst RE X x) -> False.
Proof.
intros x FS F. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & _). cbn [fst snd] in NK.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & _). cbn [fst snd] in BK.
rewrite ?KHI_eq in *.
assert (ST : (rl_T X + 2800 <= x < rl_T X + 3168) \/ (x < 0x645000 /\ (A_ERRNO <= x < A_ERRNO + 4 \/ x = 0x171d60))).
{ unfold fp_RStats, in_iv in FS. cbn [fst snd] in FS. unfold A_ERRNO in *. (first [ clear - FK PA AK PK TA TP FS x X RE BAND; lia | lia ]). }
clear FS. unfold A_ERRNO in ST.
destruct F as [FC'|[FSe|[FD|[FF|FT]]]].
- destruct FC' as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. unfold prim_hi, prim_lo in *. (first [ clear - R2 R1 P3 P2 P1 ST FK KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. destruct ST as [ST|ST]; [| (first [ clear - E2 E1 ST FK KP PA AK PK TA TP F e x X RE BAND; lia | lia ])].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F). lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). lia.
- destruct FSe as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. (first [ clear - ST FK PA AK PK TA TP TK H0 H x X RE BAND; lia | lia ]).
+ destruct F; cbn [fst snd] in *. (first [ clear - ST FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. destruct ST as [ST|ST]; [| (first [ clear - E4 E2 E1 ST FK KP PA AK PK TA TP F e x X RE BAND; lia | lia ])].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (e & He & F). pose proof (hdr_band e x He F). lia.
- destruct FD as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. lia.
+ destruct ST as [ST|ST]; [| destruct F; cbn [fst snd] in *; (first [ clear - ST NK FK PA AK PK TA TP H x X RE BAND; lia | lia ])]. eapply (obj_vs_T _ x (dn_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ destruct ST as [ST|ST]; [| destruct F; cbn [fst snd] in *; (first [ clear - ST BK FK PA AK PK TA TP H x X RE BAND; lia | lia ])]. eapply (obj_vs_T _ x (ssb_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ (first [ clear - ST FK PA AK PK TA TP TK F x X RE BAND; lia | lia ]).
- destruct FF as [[F _]|[F _]].
+ destruct ST as [ST|ST]; [| destruct F; cbn [fst snd] in *; (first [ clear - ST FK FAL PA AK PK TA TP H0 H x X RE BAND; lia | lia ])]. eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
+ pose proof (fs_band x F). (first [ clear - H ST FK PA AK PK TA TP TK x X RE BAND; lia | lia ]).
- destruct ST as [ST|[LT ST]].
+ exact (rt_avoid_Thigh RE X (rl_T X + 2800) (rl_T X + 3168) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT).
+ destruct (fp_RTconst_where RE X x FT) as [_|(o & Ho & HO)].
2:{ pose proof (rl_objs_lia a LB0 FS0 G RE X GC o Ho) as (_ & K & _). destruct HO as [O1 O2]. rewrite ?KHI_eq in K. (first [ clear - K O2 O1 o ST FK PA AK PK TA TP x X RE BAND; lia | lia ]). }
destruct FT as [FI|[FT|[FT|FT]]].
* destruct FI as (iv & Hin & [I1 I2]).
assert (CK : forallb (fun iv => ((fst iv + snd iv <=? 6434236) || (6434240 <=? fst iv)) && ((fst iv + snd iv <=? 0x171d60) || (0x171d61 <=? fst iv))) rtconst_img = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in CK. specialize (CK iv Hin). apply andb_prop in CK as [C1 C2].
apply orb_prop in C1 as [C1|C1]; apply Z.leb_le in C1; apply orb_prop in C2 as [C2|C2]; apply Z.leb_le in C2; (first [ clear - C2 ST FK PA AK PK TA TP I2 iv x X RE BAND C1 I1; lia | lia ]).
* destruct FT; cbn [fst snd] in *. (first [ clear - ST FK AK PK TK H0 H x X RE BAND; lia | lia ]).
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ctx_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; lia.
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dtls_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; (first [ clear - K ST FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
Qed.

Lemma depot_img_ok : forall x, 0x1c19c8 <= x < 0x1c19c8 + 0x450028 ->
~ in_ivs rtconst_img x /\ ~ (A_INSTANCE + 104 <= x < A_INSTANCE + 728) /\ x < 0x645000.
Proof.
intros x Hx.
assert (F : forallb (fun jv => (fst jv + snd jv <=? 0x1c19c8) || (0x1c19c8 + 0x450028 <=? fst jv)) (rtconst_img ++ [(A_INSTANCE + 104, 624)]) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in F.
split; [| split; [| lia]].
- intros (jv & Hjv & [J1 J2]). specialize (F jv ltac:(apply in_app_iff; left; exact Hjv)). apply orb_prop in F as [F|F]; apply Z.leb_le in F; lia.
- intros H. specialize (F (A_INSTANCE + 104, 624) ltac:(apply in_app_iff; right; left; reflexivity)). cbn [fst snd] in F.
apply orb_prop in F as [F|F]; apply Z.leb_le in F; lia.
Qed.

Lemma fpD_excl : forall x, fp_RDepot RE X x ->
(fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x \/ fp_RFake FS0 RE X x \/ fp_RTconst RE X x) -> False.
Proof.
intros x FD F. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & FP' & FA'). cbn [fst snd] in FAL, FK, FC, FP', FA'.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & NC & NP & NA). cbn [fst snd] in NK, NC, NP, NA.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & BC & BP & BA). cbn [fst snd] in BK, BC, BP, BA.
unfold iv_disjoint, prim_lo in FP', FA', NP, NA, BP, BA; cbn [fst snd] in FP', FA', NP, NA, BP, BA. unfold prim_lo in *.
rewrite ?KHI_eq in *.

assert (DW : (0x1c19c8 <= x < 0x1c19c8 + 0x450028)
\/ (exists o, In o (rlay_objs RE X) /\ in_iv o x /\ o <> (ae_fs_base RE, A_FS_MAP_SIZE) /\ o <> (rl_ctx X, 0x10000)
/\ (o = (rl_dn X, 0x100000) \/ o = (rl_ssb X, 0x800000)))
\/ x = rl_T X + 3168).
{ destruct FD as [H|[H|[H|H]]].
- left. destruct H; cbn [fst snd] in *; lia.
- right; left. exists (rl_dn X, 0x100000). split; [apply dn_obj|]. split; [exact H|].
split; [intros E; injection E; unfold A_FS_MAP_SIZE; lia|]. split; [intros E; injection E; lia| left; reflexivity].
- right; left. exists (rl_ssb X, 0x800000). split; [apply ssb_obj|]. split; [exact H|].
split; [intros E; injection E; unfold A_FS_MAP_SIZE; lia|]. split; [intros E; injection E; lia| right; reflexivity].
- right; right. exact H. }
clear FD.
assert (OBJK : forall o, In o (rlay_objs RE X) -> in_iv o x -> appr_lia (fst o) (snd o) /\ fst o <= x < fst o + snd o /\ x < band_lo
/\ (x < al_space_beg (ae_L RE) \/ al_space_beg (ae_L RE) + (2^37 + 4096) <= x)
/\ (x < ptrarr_lo RE \/ ptrarr_lo RE + 8388608 <= x)).
{ intros o Ho [O1 O2]. pose proof (rl_objs_lia a LB0 FS0 G RE X GC o Ho) as (_ & K & Ce & Dp & Da).
unfold iv_disjoint, prim_lo in Dp, Da. cbn [fst snd] in Dp, Da. split; [exact K|]. clear - O1 O2 Ce Dp Da. lia. }
clear FP' FA' NP NA BP BA.
destruct F as [FC'|[FSe|[FF|FT]]].
- destruct FC' as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. cbn [fst snd] in *.
destruct DW as [D|[(o & Ho & HO & _ & _ & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H R2 R1 P3 P2 P1 o FK KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ])| (first [ clear - R2 R1 P3 P2 P1 D FK KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ])].
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| exact (obj_vs_sec o e x Ho He HO ltac:(lia))|].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK SHB0 PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
- destruct FSe as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & NS & _); unfold A_INSTANCE in NS; lia| pose proof (OBJK o Ho HO); (first [ clear - H1 o FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ])| lia].
+ destruct F; cbn [fst snd] in *.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); (first [ clear - D FK AK PK H x RE BAND; lia | lia ])| pose proof (OBJK o Ho HO); lia| (first [ clear - D FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ])].
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| exact (obj_vs_sec o e x Ho He HO ltac:(lia))|].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (e & He & F). pose proof (hdr_band e x He F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
- destruct FF as [[F _]|[F _]].
+ destruct DW as [D|[(o & Ho & HO & NEF & _ & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); destruct F; cbn [fst snd] in *; lia| |].
* pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (fs_obj RE X) NEF) as D. unfold iv_disjoint in D. destruct HO, F; cbn [fst snd] in *. lia.
* eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
+ pose proof (fs_band x F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
- destruct DW as [D|[(o & Ho & HO & NEF & NEC & EO)|D]].
+ pose proof (depot_img_ok x D) as (NI & _ & LT).
destruct (fp_RTconst_where RE X x FT) as [_|(o & Ho & HO)]; [| pose proof (OBJK o Ho HO); (first [ clear - H o D FK PA AK PK TA TP x X RE BAND; lia | lia ])].
destruct FT as [FI|[FT|[FT|FT]]]; [exact (NI FI)| destruct FT; cbn [fst snd] in *; lia| |].
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ctx_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; lia.
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dtls_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; lia.
+ pose proof (OBJK o Ho HO) as (XB & XI & _).
destruct (fp_RTconst_where RE X x FT) as [LT|(o' & Ho' & HO')]; [lia|].
destruct (decide (o = o')) as [<-|NE].
*
destruct FT as [FI|[FT|[FT|FT]]].
-- pose proof (proj1 (rtconst_img_ok x FI)). lia.
-- assert (NE : o <> (rl_T X, 0x1000)) by (destruct EO as [-> | ->]; intros E; injection E; lia).
apply (obj_vs_T o x Ho NE HO). destruct FT; cbn [fst snd] in *; lia.
-- pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (ctx_obj RE X) NEC) as D. unfold iv_disjoint in D. destruct HO, FT; cbn [fst snd] in *. (first [ clear - D XI o FK PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
-- assert (NED : o <> (rl_dtls X, 0x1000)) by (destruct EO as [-> | ->]; intros E; injection E; lia).
pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (dtls_obj RE X) NED) as D. unfold iv_disjoint in D. destruct HO, FT; cbn [fst snd] in *. (first [ clear - D XI o FK PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
* pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho Ho' NE) as D. unfold iv_disjoint in D. destruct HO, HO'; (first [ clear - D H2 H1 o' XI o FK PA AK PK TA TP x X RE BAND; lia | lia ]).
+ exact (rt_avoid_Thigh RE X (rl_T X + 3168) (rl_T X + 3169) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT).
Qed.

Lemma fpC_excl : forall x, fp_RChunks a LB0 G RE X x -> (fp_RTconst RE X x \/ fp_RSec a RE X x \/ fp_RFake FS0 RE X x) -> False.
Proof.
intros x FC F. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC' & FP' & FA'). cbn [fst snd] in FAL, FK, FC', FP', FA'.
unfold iv_disjoint, prim_lo in FP'; cbn [fst snd] in FP'. unfold prim_lo in *. rewrite ?KHI_eq in *.

assert (CW : (exists c i t, tag_at G c i = Some t /\ in_iv (slot_beg RE c i, class_size c) x)
\/ (exists e, In e (as_reg a) /\ se_beg e + kPage <= x < se_beg e + se_size e)
\/ (exists c i t, tag_at G c i = Some t /\ in_sh (slot_beg RE c i, class_size c) x)
\/ (exists e, In e (as_reg a) /\ in_sh (se_beg e + kPage, se_size e - kPage) x)).
{ destruct FC as [[[H|H] _]|[H|H]].
- left. destruct H as (c & i & t & Ht & _ & Hx). exists c, i, t. auto.
- right; left. destruct H as (e & He & _ & Hx). exists e. auto.
- right; right; left. destruct H as (c & i & t & Ht & _ & Hx). exists c, i, t. auto.
- right; right; right. destruct H as (e & He & _ & Hx). exists e. auto. }
clear FC. destruct F as [FT|[FSe|FF]].
- destruct CW as [(c & i & t & Ht & Hx)|[(e & He & Hx)|[(c & i & t & Ht & Hx)|(e & He & Hx)]]].
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct Hx; cbn [fst snd] in *.
exact (rt_avoid_prim RE X RL (slot_beg RE c i) (slot_beg RE c i + class_size c) P1 P2 x ltac:(split; cbn [fst snd]; lia) FT).
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & HO)]; [lia|]. eapply obj_vs_sec; [exact Ho| exact He| exact HO| lia].
+ pose proof (slot_band c i t x Ht Hx). exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
+ pose proof (sec_band e x He Hx). exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
- destruct CW as [(c & i & t & Ht & Hx)|[(e & He & Hx)|[(c & i & t & Ht & Hx)|(e & He & Hx)]]];
destruct FSe as [F|[F|[F|F]]].
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. destruct Hx, F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. destruct Hx, F; cbn [fst snd] in *. (first [ clear - R2 R1 P3 P2 P1 H0 H i c FK KO PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_hi, prim_lo in *; cbn [fst snd] in D1. destruct Hx; cbn [fst snd] in *. (first [ clear - D1 E4 E2 R2 R1 P3 P2 P1 H0 H i c FK KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *.
pose proof (hdr_band e x He F). destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & _). lit. unfold iv_disjoint in D2; cbn [fst snd] in D2. destruct F; cbn [fst snd] in *. (first [ clear - D2 E2 Hx e FK KP PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
pose proof (sec_same a LB0 FS0 G RE X GC e' e x He' He ltac:(lia) ltac:(lia)) as ->. lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (hdr_band e' x He' F). lia.
+ pose proof (slot_band c i t x Ht Hx). destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (slot_band c i t x Ht Hx). destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (slot_band c i t x Ht Hx). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (e & He & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_hi, prim_lo in *; cbn [fst snd] in D1.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (se_beg e) kPage x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 R2 R1 P3 P2 P1 i c FK KP KO PA AK PK TA TP e X RE BAND; lia | lia ])) Hx F).
+ pose proof (sec_band e x He Hx). destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (sec_band e x He Hx). destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e' & He' & F). pose proof (sec_band e x He Hx). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
assert (DD : se_beg e + se_size e <= se_beg e' \/ se_beg e' + kPage <= se_beg e + kPage).
{ destruct (decide (se_beg e = se_beg e')) as [EQ|NEb].
- pose proof (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' EQ) as <-. right; lia.
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e' (gc_sec_disj a LB0 FS0 G RE X GC) He He'
ltac:(intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd] in D. (first [ clear - D NEb E4' E2' E1' E2 E1 e FK KP PA AK PK TA TP e' X RE BAND; lia | lia ]). }
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (se_beg e') kPage x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H9 q1 H0 H r q E1 r1 e PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1' r0 PA AK PK TA TP e' X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - DD e AK e' RE BAND; lia | lia ])) Hx F).
- destruct CW as [(c & i & t & Ht & Hx)|[(e & He & Hx)|[(c & i & t & Ht & Hx)|(e & He & Hx)]]]; destruct FF as [[F _]|[F _]].
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. destruct Hx, F; cbn [fst snd] in *. (first [ clear - R2 R1 P3 P2 P1 H0 H i c FP' FK KO PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. pose proof (fs_band x F). destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). eapply (obj_vs_sec _ e x (fs_obj RE X) He F). lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (fs_band x F). lia.
+ pose proof (slot_band c i t x Ht Hx). destruct F; cbn [fst snd] in *. lia.
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (ae_fs_base RE) A_FS_MAP_SIZE x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H9 q1 H0 H r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - R2 R1 P3 P2 P1 i c FP' FK FAL KO PA AK PK TA TP X RE BAND; lia | lia ])) Hx F).
+ pose proof (sec_band e x He Hx). destruct F; cbn [fst snd] in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 e PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H9 q1 H0 H r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - D E2 E1 e FK FAL KP PA AK PK TA TP X RE BAND; lia | lia ])) Hx F).
Qed.

Lemma fp_lt_ceil : forall x,
(fp_RTconst RE X x \/ fp_RStats RE X x \/ fp_RPrim G RE X x \/ fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x
\/ fp_RDepot RE X x \/ fp_RFake FS0 RE X x) -> x < band_lo.
Proof.
intros x F. destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso].
assert (CZ : czone LB0 RE x) by (left; exact GE).
destruct F as [F|[F|[F|[F|[F|[F|F]]]]]].
- exact (fp_RTconst_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RStats_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RPrim_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RChunks_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RSec_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RDepot_cz a LB0 FS0 G RE X GC x F CZ).
- pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
destruct (fp_RFake_zone RE X FS0 x F) as [[H1 H2]|H]; cbn [fst snd] in *; [lia|].
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; lia) FC H). unfold kLowEnd, KHI in *. lia.
Qed.
End Excl.

Section Bundle.
Context {BAND : Band}.
Variable C : arun_components.

Definition QOTH (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RTconst RE X m /\ RStats RE X m /\ RPrim a G RE X m /\ RChunks a LB0 G RE X m
/\ ac_RSec C a LB0 RE X m /\ ac_RDepot C RE X m /\ ac_RFake C FS0 RE X m.

Definition QRUN (rb bt bg : Z) (pend : list (aptr * Z))
(a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
gcons a LB0 FS0 G RE X /\ QOTH a LB0 FS0 G RE X m /\ RQuarM rb bt bg pend a LB0 G RE X m.

Definition qzone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ band_lo <= x.

Lemma QOTH_frame : forall a LB0 FS0 G RE X m m',
gcons a LB0 FS0 G RE X -> QOTH a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => ~ qzone a LB0 G RE X x) m m' -> QOTH a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' GC (R1 & R2 & R3 & R4 & R5 & R6 & R7) WM AG.
assert (AGX : forall P : Z -> Prop, (forall x, P x -> fp_RQuar a LB0 G RE X x -> False) -> (forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2. eapply agree_on_mono; [exact AG|]. intros x Px [Q|Q]; [exact (H1 x Px Q)| pose proof (H2 x Px); lia]. }
split; [eapply RTconst_frame; [exact R1| exact WM| apply AGX; [intros x P Q; exact (fpQ_RTconst _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ _ _ _ _ GC); tauto]]|].
split; [eapply RStats_frame; [exact R2| exact WM| apply AGX; [intros x P Q; exact (fpQ_RStats _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ _ _ _ _ GC); tauto]]|].
split; [eapply RPrim_frame; [exact R3| exact WM| apply AGX; [intros x P Q; exact (fpQ_RPrim _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ _ _ _ _ GC); tauto]]|].
split; [eapply RChunks_frame; [exact R4| exact WM| apply AGX; [intros x P Q; exact (fpQ_RChunks _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ FS0 _ _ _ GC); tauto]]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AGX; [intros x P Q; exact (fpQ_RSec _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ FS0 G _ _ GC); tauto]]|].
split; [eapply (ac_RDepot_frame C); [exact R6| exact WM| apply AGX; [intros x P Q; exact (fpQ_RDepot _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto]]|].
eapply (ac_RFake_frame C); [exact R7| exact WM| apply AGX; [intros x P Q; exact (fpQ_RFake _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto]].
Qed.

Definition QREST (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RChunks a LB0 G RE X m /\ ac_RSec C a LB0 RE X m /\ ac_RDepot C RE X m /\ ac_RFake C FS0 RE X m.

Lemma QOTH_split : forall a LB0 FS0 G RE X m,
QOTH a LB0 FS0 G RE X m <-> RTconst RE X m /\ RStats RE X m /\ RPrim a G RE X m /\ QREST a LB0 FS0 G RE X m.
Proof. intros. unfold QOTH, QREST. tauto. Qed.

Definition pzone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ band_lo <= x.

Lemma QREST_frame : forall a LB0 FS0 G RE X m m',
gcons a LB0 FS0 G RE X -> QREST a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => ~ pzone a LB0 G RE X x) m m' -> QREST a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' GC (R4 & R5 & R6 & R7) WM AG.
assert (AGX : forall P : Z -> Prop,
(forall x, P x -> fp_RQuar a LB0 G RE X x -> False) -> (forall x, P x -> fp_RPrim G RE X x -> False) ->
(forall x, P x -> fp_RStats RE X x -> False) -> (forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2 H3 H4. eapply agree_on_mono; [exact AG|]. intros x Px [Q|[Q|[Q|Q]]]; [exact (H1 x Px Q)| exact (H2 x Px Q)| exact (H3 x Px Q)| pose proof (H4 x Px); lia]. }
split; [| split; [| split]].
- eapply RChunks_frame; [exact R4| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 _ _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 _ _ _ GC); tauto.
- eapply (ac_RSec_frame C); [exact R5| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 G _ _ GC); tauto.
- eapply (ac_RDepot_frame C); [exact R6| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RDepot _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RDepot _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto.
- eapply (ac_RFake_frame C); [exact R7| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto.
Qed.

Lemma QREST_munch : forall a LB0 FS0 G RE X m m' W,
gcons a LB0 FS0 G RE X -> QREST a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> pzone a LB0 G RE X x) ->
QREST a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC Q MU WM HW. eapply QREST_frame; [exact GC| exact Q| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx. exact (NZ (HW lo hi x Hin Hx)).
Qed.

Lemma QREST_ext : forall a a' LB0 FS0 G G' RE X m,
QREST a LB0 FS0 G RE X m -> as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
same_tags is_live G G' -> QREST a' LB0 FS0 G' RE X m.
Proof.
intros a a' LB0 FS0 G G' RE X m (R4 & R5 & R6 & R7) ER EN ES SLV.
split; [eapply RChunks_ext; [exact R4| intros e He; rewrite ER; exact He| exact SLV]|].
split; [eapply (ac_RSec_ext C); [exact R5| exact ER| exact EN| exact ES]|].
split; [exact R6| exact R7].
Qed.

Lemma QOTH_munch : forall a LB0 FS0 G RE X m m' W,
gcons a LB0 FS0 G RE X -> QOTH a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> qzone a LB0 G RE X x) ->
QOTH a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC Q MU WM HW. eapply QOTH_frame; [exact GC| exact Q| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx. exact (NZ (HW lo hi x Hin Hx)).
Qed.

Lemma QOTH_ext : forall a a' LB0 FS0 G G' RE X m,
QOTH a LB0 FS0 G RE X m ->
(forall c, cls a' c = cls a c) -> as_cache_inited a' = as_cache_inited a ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
same_len G G' -> same_tags tag_prim G G' -> same_tags is_live G G' ->
QOTH a' LB0 FS0 G' RE X m.
Proof.
intros a a' LB0 FS0 G G' RE X m (R1 & R2 & R3 & R4 & R5 & R6 & R7) EC EI ER EN ES SL SP SLV.
split; [exact R1|]. split; [exact R2|].
split; [eapply RPrim_ext; [exact R3| exact EC| exact EI| exact SL| exact SP]|].
split; [eapply RChunks_ext; [exact R4| intros e He; rewrite ER; exact He| exact SLV]|].
split; [eapply (ac_RSec_ext C); [exact R5| exact ER| exact EN| exact ES]|].
split; [exact R6| exact R7].
Qed.

Section Concrete.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.

Lemma QRUN_of_ARUNX : forall a LB0 FS0 G RE X m, ARUNX C a LB0 FS0 G RE X m -> QRUN 0 QB QB [] a LB0 FS0 G RE X m.
Proof.
intros a LB0 FS0 G RE X m (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRQ in R6.
split; [exact GC|]. split; [| exact R6]. repeat (split; [assumption|]). exact R8.
Qed.

Lemma ARUNX_of_QRUN : forall a LB0 FS0 G RE X m, QRUN 0 QB QB [] a LB0 FS0 G RE X m -> ARUNX C a LB0 FS0 G RE X m.
Proof.
intros a LB0 FS0 G RE X m (GC & (R1 & R2 & R3 & R4 & R5 & R7 & R8) & R6).
split; [exact GC|]. rewrite HRT, HRS, HRP, HRC, HRQ. repeat (split; [assumption|]). exact R8.
Qed.

Lemma QRUN_of_ARUN : forall s LB FS RE m, ARUN C s LB FS RE m ->
exists X G LB0 FS0, Permutation LB LB0 /\ Permutation FS FS0 /\ QRUN 0 QB QB [] (ps_a s) LB0 FS0 G RE X m.
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
exists X, G, LB0, FS0. split; [exact PB|]. split; [exact PF|]. apply QRUN_of_ARUNX. exact AX.
Qed.

Lemma ARUN_of_QRUN : forall s LB FS RE m X G LB0 FS0,
Permutation LB LB0 -> Permutation FS FS0 -> QRUN 0 QB QB [] (ps_a s) LB0 FS0 G RE X m -> ARUN C s LB FS RE m.
Proof. intros s LB FS RE m X G LB0 FS0 PB PF Q. eapply ARUN_close; [exact PB| exact PF| apply ARUNX_of_QRUN; exact Q]. Qed.
End Concrete.

Lemma qzone_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RQuar a LB0 G RE X x \/ (band_lo <= x < SP) -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
assert (QC : fp_RQuar a LB0 G RE X x -> czone LB0 RE x -> False) by (intros Q CZ; exact (fp_RQuar_cz a LB0 FS0 G RE X GC x Q CZ)).
assert (QL : fp_RQuar a LB0 G RE X x -> x < band_lo).
{ intros Q. destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply (QC Q); left; exact GE]. }
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
-  destruct Z as [Q|Q]; [pose proof (QL Q); lia| lia].
-  cbn [ala_client_data a_alayout] in C1. destruct Z as [Q|Q]; [apply (QC Q); right; left; exact C1|].
unfold a_client_data in C1. idtac. lia.
-  assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
destruct Z as [Q|Q]; [apply (QC Q); do 2 right; left; exact LU|].
pose proof (live_user_heap a LB0 FS0 G RE X GC x LU). lia.
-  assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
destruct Z as [Q|Q]; [apply (QC Q); do 3 right; left; split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia| lia].
-  assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
pose proof (frame_shadow_where a LB0 FS0 G RE X GC x SHD) as FS'.
destruct Z as [Q|Q]; [apply (QC Q); do 4 right; left; exact FS'|].
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; lia) FC FS'). unfold kLowEnd, KHI in *. lia.
-  destruct Z as [Q|Q]; [apply (QC Q); do 5 right; left; rewrite SH_247 in C1; exact C1|].
rewrite SH_247, ?KHI_eq in *. lia.
-  cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (925696 / 8) with 115712 in C1. change (65536 / 8) with 8192 in C1.
destruct Z as [Q|Q]; [| idtac; lia].
destruct (fp_RQuar_loc a LB0 G RE X x Q) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
+ pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK. rewrite ?KHI_eq in TK. lia.
+ pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT).
destruct H as (iv & Hin & [I1 I2]). cbn in Hin. unfold A_INSTANCE in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in I1, I2; lia.
+ pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & _). pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & _).
destruct H as [H1 _]; cbn [fst] in H1. rewrite ?KHI_eq in PK. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC c i t x Ht H). lia.
+ pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (_ & E2 & _). rewrite ?KHI_eq in E2. pose proof kconsts as (_ & _ & _ & _ & KP & _). lia.
+
pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & [_ E2] & E3 & E4 & E5 & E6 & _). pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
apply in_sh_bounds in H; [| rewrite KP; clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia].
rewrite !SH_eq in H. rewrite KP in H. clear - H C1 E1 E2 M1. destruct E2 as [E2|E2]; Z.div_mod_to_equations; lia.
Qed.

Lemma pzone_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RPrim G RE X x \/ fp_RStats RE X x -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK.
assert (QC : czone LB0 RE x -> False).
{ intros CZ. destruct Z as [Q|Q]; [exact (fp_RPrim_cz a LB0 FS0 G RE X GC x Q CZ)| exact (fp_RStats_cz a LB0 FS0 G RE X GC x Q CZ)]. }
assert (QL : x < band_lo).
{ destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply QC; left; exact GE]. }
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
- lia.
- apply QC. right; left. exact C1.
- apply QC. do 2 right; left. destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
apply QC. do 3 right; left; split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
apply QC. do 4 right; left. exact (frame_shadow_where a LB0 FS0 G RE X GC x SHD).
- apply QC. do 5 right; left. rewrite SH_247 in C1. exact C1.
- cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (925696 / 8) with 115712 in C1. change (65536 / 8) with 8192 in C1.
rewrite ?KHI_eq in TK. pose proof kconsts as (_ & _ & _ & K32 & _).
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & _). rewrite ?KHI_eq in PK.
destruct Z as [Q|Q].
+ destruct (fp_RPrim_loc G RE X x Q) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS].
* unfold region_info, prim_lo in *. lia.
* lia.
* pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof kconsts as (_ & KO & _). unfold prim_lo in *. lia.
* pose proof (fas_band a LB0 FS0 G RE X GC c x Hc H). lia.
* pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). unfold prim_lo in *. lia.
* pose proof (reg_band a LB0 FS0 G RE X GC c x Hc H). lia.
+ unfold fp_RStats, in_iv, A_ERRNO in Q. cbn [fst snd] in Q. lia.
Qed.

Definition wzone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (SP x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ (band_lo <= x < SP).

Lemma wzone_pzone : forall a LB0 G RE X SP x, wzone a LB0 G RE X SP x -> pzone a LB0 G RE X x.
Proof. intros a LB0 G RE X SP x [H|[H|[H|H]]]; unfold pzone; [tauto| tauto| tauto| lia]. Qed.

Lemma aheap_presA_of_munch_w : forall a LB0 FS0 G RE X LB FS SP m m' W,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> wzone a LB0 G RE X SP x) ->
aheap_presA asegs a_alayout LB FS SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FS SP m m' W GC PB PF CSP MU WM HW. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|Z]]].
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
Qed.

Lemma aheap_presA_of_munch : forall a LB0 FS0 G RE X LB FS SP m m' W,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> fp_RQuar a LB0 G RE X x \/ (band_lo <= x < SP)) ->
aheap_presA asegs a_alayout LB FS SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FS SP m m' W GC PB PF CSP MU WM HW. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. apply outside_intro. intros lo hi Hin Hx.
exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (HW lo hi x Hin Hx)).
Qed.
End Bundle.

Section Depot.
Context {BAND : Band}.
Variable C : arun_components.

Definition azone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (SP x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ (band_lo <= x < SP).

Lemma depot_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RDepot RE X x -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Q.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & _). cbn [fst] in NK.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & _). cbn [fst] in BK.
assert (QC : czone LB0 RE x -> False) by (intros CZ; exact (fp_RDepot_cz a LB0 FS0 G RE X GC x Q CZ)).
assert (QL : x < band_lo).
{ destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply QC; left; exact GE]. }
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
- lia.
- apply QC. right; left. exact C1.
- apply QC. do 2 right; left. destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
apply QC. do 3 right; left; split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
apply QC. do 4 right; left. exact (frame_shadow_where a LB0 FS0 G RE X GC x SHD).
- apply QC. do 5 right; left. rewrite SH_247 in C1. exact C1.
- cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (925696 / 8) with 115712 in C1. change (65536 / 8) with 8192 in C1.
rewrite ?KHI_eq in TK, NK, BK. destruct Q as [H|[H|[H|H]]]; [destruct H; cbn [fst snd] in *; lia| destruct H; cbn [fst snd] in *; lia| destruct H; cbn [fst snd] in *; lia| lia].
Qed.

Lemma aheap_presA_of_munch_a : forall a LB0 FS0 G RE X LB FS SP m m' W,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> azone a LB0 G RE X SP x) ->
aheap_presA asegs a_alayout LB FS SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FS SP m m' W GC PB PF CSP MU WM HW. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|[Z|Z]]]].
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z).
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
Qed.

Definition QR3 (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RChunks a LB0 G RE X m /\ ac_RSec C a LB0 RE X m /\ ac_RFake C FS0 RE X m.

Lemma QREST_split : forall a LB0 FS0 G RE X m,
QREST C a LB0 FS0 G RE X m <-> QR3 a LB0 FS0 G RE X m /\ ac_RDepot C RE X m.
Proof. intros. unfold QREST, QR3. tauto. Qed.

Lemma QR3_frame : forall a LB0 FS0 G RE X m m',
gcons a LB0 FS0 G RE X -> QR3 a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => ~ (fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ band_lo <= x)) m m' ->
QR3 a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' GC (R4 & R5 & R7) WM AG.
assert (AGX : forall P : Z -> Prop,
(forall x, P x -> fp_RQuar a LB0 G RE X x -> False) -> (forall x, P x -> fp_RPrim G RE X x -> False) ->
(forall x, P x -> fp_RStats RE X x -> False) -> (forall x, P x -> fp_RDepot RE X x -> False) ->
(forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2 H3 H4 H5. eapply agree_on_mono; [exact AG|]. intros x Px [Q|[Q|[Q|[Q|Q]]]];
[exact (H1 x Px Q)| exact (H2 x Px Q)| exact (H3 x Px Q)| exact (H4 x Px Q)| pose proof (H5 x Px); lia]. }
split; [| split].
- eapply RChunks_frame; [exact R4| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 _ _ _ GC x Q); tauto.
+ intros x P Q; apply (fpD_excl _ _ FS0 _ _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 _ _ _ GC); tauto.
- eapply (ac_RSec_frame C); [exact R5| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 G _ _ GC x Q); tauto.
+ intros x P Q; apply (fpD_excl _ _ FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 G _ _ GC); tauto.
- eapply (ac_RFake_frame C); [exact R7| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P Q; apply (fpD_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto.
Qed.

Lemma QR3_munch : forall a LB0 FS0 G RE X m m' W SP,
gcons a LB0 FS0 G RE X -> QR3 a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> azone a LB0 G RE X SP x) ->
QR3 a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W SP GC Q MU WM HW. eapply QR3_frame; [exact GC| exact Q| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx.
apply NZ. destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto| do 4 right; lia].
Qed.

Lemma QR3_ext : forall a a' LB0 FS0 G G' RE X m,
QR3 a LB0 FS0 G RE X m -> as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
same_tags is_live G G' -> QR3 a' LB0 FS0 G' RE X m.
Proof.
intros a a' LB0 FS0 G G' RE X m (R4 & R5 & R7) ER EN ES SLV.
split; [eapply RChunks_ext; [exact R4| intros e He; rewrite ER; exact He| exact SLV]|].
split; [eapply (ac_RSec_ext C); [exact R5| exact ER| exact EN| exact ES]| exact R7].
Qed.

End Depot.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUvT QZbm QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QUvT QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QZbm QpY2.Mq9 QpY2.Mq4 QpME.Mq3.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc1_entry : Z := 0x4a904.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma land_8191 : forall x, Z.land x 8191 = x mod 8192.
Proof. intros x. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod8192_of_64 : forall x, (x mod 2^64) mod 8192 = x mod 8192.
Proof. intros x. apply Z.mod_mod_divide. exists (2^51); reflexivity. Qed.

Lemma fs1_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 20480) fl -> fl = flags_of FS0 FS 1 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 1) FS0)) < fs_N 1 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (8192 - i) -> 0 <= i < 8192 ->
bv_unsigned cur mod 8192 = (u + i) mod 8192 ->
(forall j, 0 <= j < i -> live_b FS0 1 (fs_frame FS 1 ((u + j) mod 8192)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 (wz FS) (wz (8192 - i')) (wz (FS + 4096)) cur' (wz (FS + 20480)) (wz 8191)
(wz (FS + 20480 + pos)) a6 (wz pos) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4aa10) fc None mc (seg_rom asegs)
/\ 0 <= pos < 8192 /\ live_b FS0 1 (fs_frame FS 1 pos) = false /\ 0 <= i' < 8192)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (8192 - i)) (wz (FS + 4096)) cur (wz (FS + 20480)) (wz 8191) a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4a998) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 8191).
assert (Hpos : pos = (u + i) mod 8192) by (subst pos; rewrite land_8191; exact Hcur).
assert (PR : 0 <= pos < 8192) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 1 (fs_frame FS 1 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 20480) fl pos (b8 1) (wa (FS + 20480 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 8192) as [LT|GE].
+ if_true_u. replace (8192 - i + -1) with (8192 - (i + 1)) by lia.
eapply (IH (Z.to_nat (8192 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod8192_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 1 -> live_b FS0 1 (fs_frame FS 1 p) = true).
{ apply (scan_exhausts FS0 FS 1 u (i + 1)); try change (fs_N 1) with 8192; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 1 ltac:(lia) ALL) as CNT. change (fs_N 1) with 8192 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 20480) fl pos (b8 0) (wa (FS + 20480 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 8191), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc1_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 1) FS0)) < fs_N 1 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 1 pos /\ 0 <= pos < fs_N 1 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 1 f
/\ RTconst RE X m' /\ RFake ((1, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 1 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0); C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 8, FS + 8 + 8); (fs_flag FS 1 pos, fs_flag FS 1 pos + 1);
(f, f + ff_size 1); (SH f, SH f + ff_size 1 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc1_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc1_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 1 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. change (8 * 1) with 8 in HINT.
pose proof (FL 1 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 1) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 8192) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 1 0) with (FS + 20480) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x553c0.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4a998.

eapply evt_cut.
{ eapply (fs1_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 8, FS + 8 + 8); (FS + 20480 + pos, FS + 20480 + pos + 1);
(FS + 1085440 + pos * 128, FS + 1085440 + pos * 128 + 128); (SH (FS + 1085440 + pos * 128), SH (FS + 1085440 + pos * 128) + 16)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 4 istep. rewrite (unsigned_lit pos), Z.shiftl_mul_pow2 by lia. change (2 ^ 7) with 128.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 20480) fl pos (wa (FS + 20480 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 20480) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 5 istep.
replace (FS + 36864 + (1048576 + pos * 128)) with (FS + 1085440 + pos * 128) by lia.
remember (FS + 1085440 + pos * 128) as f eqn:Ef in *.
assert (FB : FS + 1085440 <= f /\ f + 128 <= FS + 1085440 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 128) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 128 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 128) = SH f + 16) by (rewrite !SH_eq; replace (f + 128) with (f + 16 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 128) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 16) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).
pose proof (fun Hm => hjunk_split _ (SH f) (SH f + 8) _ J2f Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2a J2b].
destruct (hjunk_cells _ (SH f) 8 J2a) as [junks SHC].
replace (SH f + Z.of_nat 16) with (SH f + 8 + Z.of_nat 8) in J2b by (cbn; lia).
destruct (hjunk_cells _ (SH f + 8) 8 J2b) as [junks2 SHC2]. clear J2c J2r J2f J2a J2b.
istep. istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 88 (take 88 (drop 32 junkf))] [C8 (wz (FS + 20480 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 120 (take 24 junkf ++ le8 sp ++ take 88 (drop 32 junkf))] [C8 (wz (FS + 20480 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 1 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 1 pos = FS + 20480 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 1 0 = FS + 20480) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 1 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 1) with 8192; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 1) with 128 in NT. change (128 / 8) with 16 in NT. change (8 * 1) with 8 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. change (8 * 1) with 8. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 1 - 8) with (f + 120) by (change (ff_size 1) with 128; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 88 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 1) with 8192; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 1) with 128. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split.
{ apply (proj2 (rw_cells_app asegs _ (SH f) [C8 (wz 0)] [C8 (wz 0)])). split; [exact SHC| exact SHC2]. }
rewrite FLG. change (ff_size 1) with 128. change (128 / 8) with 16.
eapply munch_weaken; [| exact MU2]. intros y Hy. cbn [outside fst snd] in Hy |- *. lia.
Qed.
End Walk.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QUvT QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QZbm QpY2.Mq9 QpY2.Mq4 QpME.Mq3.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc2_entry : Z := 0x4aa94.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod4096_of_64 : forall x, (x mod 2^64) mod 4096 = x mod 4096.
Proof. intros x. apply Z.mod_mod_divide. exists (2^52); reflexivity. Qed.

Lemma fs2_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 28672) fl -> fl = flags_of FS0 FS 2 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 2) FS0)) < fs_N 2 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (4096 - i) -> 0 <= i < 4096 ->
bv_unsigned cur mod 4096 = (u + i) mod 4096 ->
(forall j, 0 <= j < i -> live_b FS0 2 (fs_frame FS 2 ((u + j) mod 4096)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 (wz FS) (wz (4096 - i')) (wz (FS + 4096)) cur' (wz (FS + 28672)) (wz 4095)
(wz (FS + 28672 + pos)) a6 (wz pos) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4aba0) fc None mc (seg_rom asegs)
/\ 0 <= pos < 4096 /\ live_b FS0 2 (fs_frame FS 2 pos) = false /\ 0 <= i' < 4096)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (4096 - i)) (wz (FS + 4096)) cur (wz (FS + 28672)) (wz 4095) a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4ab28) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 4095).
assert (Hpos : pos = (u + i) mod 4096) by (subst pos; rewrite land_4095; exact Hcur).
assert (PR : 0 <= pos < 4096) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 2 (fs_frame FS 2 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 28672) fl pos (b8 1) (wa (FS + 28672 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 4096) as [LT|GE].
+ if_true_u. replace (4096 - i + -1) with (4096 - (i + 1)) by lia.
eapply (IH (Z.to_nat (4096 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod4096_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 2 -> live_b FS0 2 (fs_frame FS 2 p) = true).
{ apply (scan_exhausts FS0 FS 2 u (i + 1)); try change (fs_N 2) with 4096; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 2 ltac:(lia) ALL) as CNT. change (fs_N 2) with 4096 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 28672) fl pos (b8 0) (wa (FS + 28672 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 4095), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc2_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 2) FS0)) < fs_N 2 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 2 pos /\ 0 <= pos < fs_N 2 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 2 f
/\ RTconst RE X m' /\ RFake ((2, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 2 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 16, FS + 16 + 8); (fs_flag FS 2 pos, fs_flag FS 2 pos + 1);
(f, f + ff_size 2); (SH f, SH f + ff_size 2 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc2_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc2_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 2 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. change (8 * 2) with 16 in HINT.
pose proof (FL 2 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 2) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 4096) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 2 0) with (FS + 28672) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x553c0.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4ab28.

eapply evt_cut.
{ eapply (fs2_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 16, FS + 16 + 8); (FS + 28672 + pos, FS + 28672 + pos + 1);
(FS + 2134016 + pos * 256, FS + 2134016 + pos * 256 + 256); (SH (FS + 2134016 + pos * 256), SH (FS + 2134016 + pos * 256) + 32)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 3 istep.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 28672) fl pos (wa (FS + 28672 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 28672) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 7 istep. rewrite ?(unsigned_lit pos), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
replace (FS + 36864 + (2097152 + pos * 256)) with (FS + 2134016 + pos * 256) by lia.
remember (FS + 2134016 + pos * 256) as f eqn:Ef in *.
assert (FB : FS + 2134016 <= f /\ f + 256 <= FS + 2134016 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 256) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 256 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 256) = SH f + 32) by (rewrite !SH_eq; replace (f + 256) with (f + 32 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 256) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 32) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).
pose proof (fun Hm => hjunk_split _ (SH f) (SH f + 8) _ J2f Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2a J2b].
pose proof (fun Hm => hjunk_split _ (SH f + 8) (SH f + 16) _ J2b Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2b1 J2c'].
pose proof (fun Hm => hjunk_split _ (SH f + 16) (SH f + 24) _ J2c' Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2c1 J2d].
destruct (hjunk_cells _ (SH f) 8 J2a) as [junks SHC].
replace (SH f + 16) with (SH f + 8 + Z.of_nat 8) in J2b1 by (cbn; lia).
destruct (hjunk_cells _ (SH f + 8) 8 J2b1) as [junks2 SHC2].
replace (SH f + 24) with (SH f + 16 + Z.of_nat 8) in J2c1 by (cbn; lia).
destruct (hjunk_cells _ (SH f + 16) 8 J2c1) as [junks3 SHC3].
replace (SH f + Z.of_nat 32) with (SH f + 24 + Z.of_nat 8) in J2d by (cbn; lia).
destruct (hjunk_cells _ (SH f + 24) 8 J2d) as [junks4 SHC4]. clear J2c J2r J2f J2a J2b J2b1 J2c' J2c1 J2d.
istep. istep. istep. istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 216 (take 216 (drop 32 junkf))] [C8 (wz (FS + 28672 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 248 (take 24 junkf ++ le8 sp ++ take 216 (drop 32 junkf))] [C8 (wz (FS + 28672 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 2 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 2 pos = FS + 28672 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 2 0 = FS + 28672) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 2 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 2) with 4096; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 2) with 256 in NT. change (256 / 8) with 32 in NT. change (8 * 2) with 16 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. change (8 * 2) with 16. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 2 - 8) with (f + 248) by (change (ff_size 2) with 256; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 216 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 2) with 4096; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 2) with 256. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split.
{ apply (proj2 (rw_cells_app asegs _ (SH f) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
apply (proj2 (rw_cells_app asegs _ (SH f + 8) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0)])). split; [exact SHC2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 8 + 8) with (SH f + 16) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 16) [C8 (wz 0)] [C8 (wz 0)])). split; [exact SHC3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 16 + 8) with (SH f + 24) by lia. exact SHC4. }
rewrite FLG. change (ff_size 2) with 256. change (256 / 8) with 32.
eapply munch_weaken; [| exact MU2]. intros y Hy. cbn [outside fst snd] in Hy |- *. lia.
Qed.
End Walk.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QWRO Qu4g QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QWRO Qu4g QFQR QmP7 QmP7.Mq1 Q9Ho.Mq3.
Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Ltac gc_split GC :=
destruct GC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A8b & A9 & A10 & A11 & A12 & A13).

Lemma gcons_ext {BAND : Band} : forall a a' LB FS G RE X,
gcons a LB FS G RE X ->
(forall c, c_alloc_user (cls a' c) = c_alloc_user (cls a c)) ->
(forall c, c_mapped_user (cls a' c) = c_mapped_user (cls a c)) ->
as_reg a' = as_reg a -> (as_next a <= as_next a')%N ->
gcons a' LB FS G RE X.
Proof.
intros a a' LB FS G RE X GC EA EM ER EN. gc_split GC.
split; [exact A1|]. split.
{ intros p A n H. destruct (A2 p A n H) as [[H1|H1] H2]; split; [left; exact H1| exact H2| | exact H2].
right. destruct H1 as (mb & E & H3 & H4 & H5 & H6). exists mb. rewrite ER. repeat split; assumption. }
split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split.
{ intros c Hc. destruct (A6 c Hc) as [X1 X2]. split; [exact X1|]. rewrite EA. exact X2. }
split. { intros c Hc. rewrite EA, EM. apply A7. exact Hc. }
split; [exact A8|]. split. { intros c i t id n Ht Hh. pose proof (A8b c i t id n Ht Hh). lia. }
rewrite ER. repeat (split; [assumption|]). exact A13.
Qed.

Section Retag.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Variables (c0 i0 : Z) (t0 t1 : stag).
Hypothesis GC : gcons a LB FS G RE X.
Hypothesis HT0 : tag_at G c0 i0 = Some t0.
Let G' := set_tag c0 i0 t1 G.

Lemma retag_at : forall c i, tag_at G' c i = if (c =? c0) && (i =? i0) then Some t1 else tag_at G c i.
Proof.
intros c i. pose proof (tag_at_Some_lt _ _ _ _ HT0) as [I0 _].
destruct (Z.eqb_spec c c0) as [->|NC]; [destruct (Z.eqb_spec i i0) as [->|NI]|]; cbn [andb].
- exact (tag_at_set_tag_eq G c0 i0 t1 t0 HT0).
- apply tag_at_set_tag_ne; lia.
- apply tag_at_set_tag_ne; lia.
Qed.
End Retag.

Lemma gcons_free_prim {BAND : Band} : forall a LB FS G RE X p A n c i id,
gcons a LB FS G RE X -> In (p, A, n) LB -> p = APrim id n -> tag_at G c i = Some (TLive p) ->
gcons a (alb_remove p LB) FS (set_tag c i (TQuar p) G) RE X.
Proof.
intros a LB FS G RE X p A n c i id GC Hin Ep Ht. pose proof GC as GC0. gc_split GC.
pose proof (retag_at G c i (TLive p) (TQuar p) Ht) as RT.
assert (PC : aptr_cls p = c /\ from_primary (aptr_req p) = true).
{ destruct (A4 c i p Ht) as (id0 & n0 & A0 & E0 & HinA & Hc0). rewrite Ep in E0. inversion E0. subst id0 n0.
split; [subst p; exact Hc0|].
destruct (A2 p A n Hin) as [[(id' & i1 & E & Hn & HP & _)|(mb & E & _ & HP & _)] _]; subst p; [exact HP| discriminate]. }
destruct PC as (PCc & PCp).
split; [exact A1|]. split.
{ intros q Aq nq Hq. apply In_alb_remove in Hq as [Hq NE]. cbn [ablk_id fst] in NE.
destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| right; exact H1| exact H2].
left. destruct H1 as (id' & i' & E & Hn & HP & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [| split; [exact Hi'| exact HA]]. rewrite RT.
destruct (Z.eqb_spec (class_of nq) c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb]; try exact Ht'.
exfalso. rewrite EC, EI, Ht in Ht'. inversion Ht'. apply NE. symmetry. assumption. }
split.
{ unfold alb_remove. clear - A3. induction LB as [|b LB IH]; cbn; [constructor|].
inversion A3; subst. destruct (decide _); cbn; [constructor; [| apply IH; assumption]| apply IH; assumption].
intros Hm. apply H1. apply in_map_iff in Hm as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E|].
apply list_elem_of_In. apply list_elem_of_In in Hb'. apply list_elem_of_filter in Hb'. tauto. }
split.
{ intros c' i' q Hq. rewrite RT in Hq.
destruct (Z.eqb_spec c' c) as [->|NC]; [destruct (Z.eqb_spec i' i) as [->|NI]|]; cbn [andb] in Hq; [discriminate| |].
- destruct (A4 c i' q Hq) as (idq & nq & Aq & Eq & HinA & Hc). exists idq, nq, Aq. split; [exact Eq|]. split; [| exact Hc]. apply In_alb_remove. split; [exact HinA|].
cbn [ablk_id fst]. intros ->. pose proof (A8 c i' c i p _ _ Hq Ht) as [_ E]; [cbn; apply aptr_eqb_refl'| cbn; apply aptr_eqb_refl'| lia].
- destruct (A4 c' i' q Hq) as (idq & nq & Aq & Eq & HinA & Hc). exists idq, nq, Aq. split; [exact Eq|]. split; [| exact Hc]. apply In_alb_remove. split; [exact HinA|].
cbn [ablk_id fst]. intros ->. pose proof (A8 c' i' c i p _ _ Hq Ht) as [E _]; [cbn; apply aptr_eqb_refl'| cbn; apply aptr_eqb_refl'| lia]. }
split.
{ intros c' i' q Hq. rewrite RT in Hq.
destruct (Z.eqb_spec c' c) as [->|NC]; [destruct (Z.eqb_spec i' i) as [->|NI]|]; cbn [andb] in Hq.
- inversion Hq; subst q. split; [exact PCc| exact PCp].
- exact (A5 _ _ _ Hq).
- exact (A5 _ _ _ Hq). }
split.
{ intros c' NE. rewrite ncarved_set_tag. apply A6. intros E. apply NE.
destruct (Z.eq_dec c' c) as [->|NC]; [rewrite set_tag_class, E; reflexivity| rewrite set_tag_other_class by exact NC; exact E]. }
split; [exact A7|]. split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2. rewrite RT in H1, H2.
assert (HH : forall cc ii u, (if (cc =? c) && (ii =? i) then Some (TQuar p) else tag_at G cc ii) = Some u -> holds q u = true ->
exists u', tag_at G cc ii = Some u' /\ holds q u' = true).
{ intros cc ii u Hu Ku. destruct ((cc =? c) && (ii =? i)) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst cc ii. inversion Hu; subst u.
exists (TLive p). split; [exact Ht| exact Ku].
- exists u. auto. }
destruct (HH _ _ _ H1 K1) as (u1' & H1' & K1'). destruct (HH _ _ _ H2 K2) as (u2' & H2' & K2').
exact (A8 _ _ _ _ q _ _ H1' H2' K1' K2'). }
split.
{ intros c1 i1 t id1 n1 H1 K1. rewrite RT in H1. destruct ((c1 =? c) && (i1 =? i)) eqn:E.
- inversion H1; subst t. eapply (A8b c i (TLive p) id1 n1 Ht). exact K1.
- eapply A8b; eassumption. }
repeat (split; [assumption|]). exact A13.
Qed.

Lemma gcons_free_sec {BAND : Band} : forall a LB FS G RE X p A n mb,
gcons a LB FS G RE X -> In (p, A, n) LB -> p = ASec mb n ->
gcons a (alb_remove p LB) FS G RE X.
Proof.
intros a LB FS G RE X p A n mb GC Hin Ep. gc_split GC.
split; [exact A1|]. split.
{ intros q Aq nq Hq. apply In_alb_remove in Hq as [Hq _]. exact (A2 q Aq nq Hq). }
split.
{ unfold alb_remove. clear - A3. induction LB as [|b LB IH]; cbn; [constructor|].
inversion A3; subst. destruct (decide _); cbn; [constructor; [| apply IH; assumption]| apply IH; assumption].
intros Hm. apply H1. apply in_map_iff in Hm as (b' & E & Hb'). apply in_map_iff. exists b'. split; [exact E|].
apply list_elem_of_In. apply list_elem_of_In in Hb'. apply list_elem_of_filter in Hb'. tauto. }
split.
{ intros c' i' q Hq. destruct (A4 c' i' q Hq) as (idq & nq & Aq & Eq & HinA & Hc). exists idq, nq, Aq. split; [exact Eq|]. split; [| exact Hc].
apply In_alb_remove. split; [exact HinA|]. cbn [ablk_id fst]. intros ->. subst p. discriminate. }
repeat (split; [assumption|]). exact A13.
Qed.

End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C QbcP_c1 QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import Qu3b.Mq5.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition memcpy_stub : Z := 0x61b18.
Definition memcpy_icpt_entry : Z := 0x62d18.
Definition MEMCPY_ICPT_STACK : Z := 2240.

Definition memcpy_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at asegs m' (bv_unsigned a1) src.

Lemma qslow_loop_at : forall (pc : Z), (pc = 0x63098 \/ pc = 0x63198) ->
forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz e) (wz e) (wz 0) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (pc + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz p) (wz e) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom asegs)).
Proof.
intros pc [-> | ->];
(induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ]).
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (dst srcA n lo : Z) (src junk : list byte).
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - MEMCPY_ICPT_STACK.
Hypothesis N0 : 0 <= n.
Hypothesis SRC : bytes_at asegs m srcA src.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis DST : rw_cells asegs m dst [CB (Z.to_nat n) junk].
Hypothesis SEP : srcA + n <= dst \/ dst + n <= srcA.
Hypothesis SST : srcA + n <= lo \/ bv_unsigned sp <= srcA.
Hypothesis DSTK : dst + n <= lo \/ bv_unsigned sp <= dst.
Hypothesis RS : rng_ok m srcA n.
Hypothesis RD : rng_ok m dst n.
Let usp := bv_unsigned sp.
Let POST := memcpy_icpt_post ra sp gp tp.

Definition frame_cells (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) : list cell :=
[C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma memcpy_icpt_tail : forall mc (rav t0 t1 t2 a3 a4 a5 a6 a7 s1v s2v s3v s4v s5v s6v s7v s8v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -2160) -> stk asegs mc (usp + -2160) (usp + -80) ->
rw_cells asegs mc (usp + -80) (frame_cells s8 s7 s6 s5 s4 s3 s2 s1 s0) ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR rav (wz (usp + -2160)) gp tp t0 t1 t2 sp s1v (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62e0c) fc None mc (seg_rom asegs)).
Proof.
intros until s11; intros MUs WM MI ST ST2 FR. unfold frame_cells in FR.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. unfold MEMCPY_ICPT_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_15a5f8 _ RCc) as KR. clear RCc.

step. stp. step. clear KR.
assert (SRCc : bytes_at asegs mc srcA src).
{ eapply bytes_at_transport; [exact SRC| exact MUs|]. cbn. rewrite LEN, Z2Nat.id by lia. lia. }
assert (DSTc : rw_cells asegs mc dst [CB (Z.to_nat n) junk]).
{ eapply rw_cells_transport; [exact DST| exact MUs| exact WM|]. cbn. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }

assert (MU : munch [(dst, dst + n); (lo, bv_unsigned sp)] m mc)
by (eapply munch_weaken; [| exact MUs]; unfold sub_fp; cbn; intros x Hx; lia).
clear MUs.

(call_u (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc src junk);
[rewrite unsigned_lit by lia; exact SRCc| rewrite unsigned_lit by lia; exact LEN| rewrite !unsigned_lit by lia; exact DSTc
| rewrite !unsigned_lit by lia; exact SEP| exact MI|]).
all: replace (ret_pc (wz 0x62e18)) with (wz 0x62e18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
all: do 12 istep.
all: match goal with ST1 : stk asegs ?mc lo _, ST2x : stk asegs ?mc (bv_unsigned sp + -2160) _ |- _ =>
pose proof (stk_merge asegs _ _ _ _ ST1 ST2x ltac:(lia)) as STm; clear ST1 ST2x end.
all: match goal with FRx : rw_cells asegs ?mc (bv_unsigned sp + -80) _, STx : stk asegs ?mc lo _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
all: step.
all: apply evt_done; unfold POST, memcpy_icpt_post; do 15 eexists; split; [reflexivity|].
all: rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit srcA) by lia.
all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

Local Ltac at_mc MUs WM :=
lazymatch type of MUs with munch _ m ?mc =>
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SBc;
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc
end.

Lemma memcpy_icpt_to : forall mc (rav t0 t1 t2 a3 a4 a5 a6 a7 s1v s2v s3v s5v s7v s8v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -2160) -> stk asegs mc (usp + -2160) (usp + -80) ->
rw_cells asegs mc (usp + -80) (frame_cells s8 s7 s6 s5 s4 s3 s2 s1 s0) ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR rav (wz (usp + -2160)) gp tp t0 t1 t2 sp s1v (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2v s3v (wz (dst + n)) s5v (wz (n + -65)) s7v s8v s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62dc4) fc None mc (seg_rom asegs)).
Proof.
intros until s11; intros MUs WM MI ST ST2 FR. unfold frame_cells in FR.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. unfold MEMCPY_ICPT_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.

step. step. rewrite (unsigned_lit dst), zb_lxor_ones by lia. ifz.

step. step.
destruct (Z.eq_dec n 0) as [Nz|Nz].
{
if_cases K1; zify_cond K1; rewrite ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Nz; Z.div_mod_to_equations; lia].
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia; [exfalso; lia|]. step.
eapply memcpy_icpt_tail; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR]. }
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct RD as (_ & _ & SOK & _ & NB). destruct (NB ltac:(lia)) as [[w3 W3] [w4 W4]]. pose proof (SOK ltac:(lia)) as SOd.
pose proof (rw_cells_below m mc _ _ _ W3 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W3c.
pose proof (rw_cells_below m mc _ _ _ W4 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W4c.
clear W3 W4.
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SOd| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. destruct SBc as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. stp. step. stp. stp.
rewrite (unsigned_lit dst), (unsigned_lit (dst + n + -1)) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (dst + n + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH dst /\ SH dst <= SH (dst + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH dst)), (unsigned_lit (SH (dst + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH dst - SH dst mod 8) with (8 * (SH dst / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (dst + n - 1) - SH (dst + n - 1) mod 8) with (8 * (SH (dst + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.

destruct (shadow_ok_last _ dst n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ dst n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x62e0c) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (dst + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (dst + n - 1)) (SH dst)) as [X1|X1].
+ ifz. replace (SH dst) with (SH (dst + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_at 0x63198 (or_intror eq_refl) (Z.to_nat (SH (dst + n - 1) - SH dst)) (SH dst)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.
eapply memcpy_icpt_tail; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR].
-
destruct RD as (_ & _ & SOK & BIG & _). destruct (BIG ltac:(lia)) as (KD & N43). pose proof (SOK ltac:(lia)) as SOd.
ifz. step. ifz.
step. step. step. step.
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SOd| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. pose proof (rt_mem_cells_of _ SBc RCc) as RTM. clear SBc RCc.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia| exact SO'| lia| lia| lia| exact KD|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST' end.
step. step. step. step. step. ifz.
eapply memcpy_icpt_tail; [eassumption| eassumption| eassumption| exact ST'| eassumption| eassumption].
Qed.

Lemma memcpy_icpt_from : forall mc (rav t0 t1 t2 a3 a4 a5 a6 a7 s1v s2v s5v s6v s7v s8v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -2160) -> stk asegs mc (usp + -2160) (usp + -80) ->
rw_cells asegs mc (usp + -80) (frame_cells s8 s7 s6 s5 s4 s3 s2 s1 s0) ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR rav (wz (usp + -2160)) gp tp t0 t1 t2 sp s1v (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2v (wz (srcA + n)) (wz (dst + n)) s5v s6v s7v s8v s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62d78) fc None mc (seg_rom asegs)).
Proof.
intros until s11; intros MUs WM MI ST ST2 FR.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCPY_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.

step. step. rewrite (unsigned_lit srcA), zb_lxor_ones by lia. ifz.

step. step. step.
destruct (Z.eq_dec n 0) as [Nz|Nz].
{
if_cases K1; zify_cond K1; rewrite ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Nz; Z.div_mod_to_equations; lia].
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia; [exfalso; lia|]. step.
eapply memcpy_icpt_to; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR]. }
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct RS as (_ & _ & SOK & _ & NB). destruct (NB ltac:(lia)) as [[w1 W1] [w2 W2]]. pose proof (SOK ltac:(lia)) as SOs.
pose proof (rw_cells_below m mc _ _ _ W1 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W1c.
pose proof (rw_cells_below m mc _ _ _ W2 MUs WM ltac:(constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor])) as W2c.
clear W1 W2.
assert (SO' : shadow_ok mc srcA n)
by (eapply shadow_ok_munch; [exact SOs| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. destruct SBc as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. stp. step. stp. stp.
rewrite (unsigned_lit srcA), (unsigned_lit (srcA + n + -1)) by lia.
replace (2147450880 + srcA ≫ 3) with (SH srcA) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (srcA + n + -1) ≫ 3) with (SH (srcA + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH srcA /\ SH srcA <= SH (srcA + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH srcA)), (unsigned_lit (SH (srcA + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH srcA - SH srcA mod 8) with (8 * (SH srcA / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (srcA + n - 1) - SH (srcA + n - 1) mod 8) with (8 * (SH (srcA + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.

destruct (shadow_ok_last _ srcA n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ srcA n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x62dc4) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (srcA + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (srcA + n - 1)) (SH srcA)) as [X1|X1].
+ ifz. replace (SH srcA) with (SH (srcA + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_at 0x63098 (or_introl eq_refl) (Z.to_nat (SH (srcA + n - 1) - SH srcA)) (SH srcA)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.
replace (srcA + n + -1) with (srcA + n - 1) by lia.
eapply memcpy_icpt_to; [exact MUs| exact WM| exact MI| exact ST| exact ST2| exact FR].
-
destruct RS as (_ & _ & SOK & BIG & _). destruct (BIG ltac:(lia)) as (KS & N43). pose proof (SOK ltac:(lia)) as SOs.
ifz. step. ifz.
step. step. step. step. step.
assert (SO' : shadow_ok mc srcA n)
by (eapply shadow_ok_munch; [exact SOs| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia).
at_mc MUs WM. pose proof (rt_mem_cells_of _ SBc RCc) as RTM. clear SBc RCc.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia| exact SO'| lia| lia| lia| exact KS|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST' end.
step. step. step. step. step. ifz.
eapply memcpy_icpt_to; [eassumption| eassumption| eassumption| exact ST'| eassumption| eassumption].
Qed.

Lemma memcpy_icpt_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
mem_inv asegs m -> stk asegs m lo usp ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memcpy_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros MI ST.
pose proof (proj1 RS) as S0. pose proof (proj1 (proj2 RS)) as S1. pose proof (proj1 RD) as D0. pose proof (proj1 (proj2 RD)) as D1.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCPY_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.

set (BAh := bytes_at) in SRC. set (RWh := rw_cells) in DST.
unfold memcpy_stub. step.
carve_frame 80%nat ST.
do 11 istep.
step. step.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_1588c8 _ RCc) as K10. pose proof (rt_161720 _ RCc) as K18. clear RCc.
step. stp. stp. clear K10 K18.
step. ifz.
stp. stp. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2160) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2160) _ ST ltac:(lia))) as ST2. clear ST.

step. if_cases K1; [eapply memcpy_icpt_from; [exact MUs| exact WM| exact MI| exact ST1| exact ST2| exact FR]|].
step. if_cases K2; [eapply memcpy_icpt_from; [exact MUs| exact WM| exact MI| exact ST1| exact ST2| exact FR]|].
zify_cond K2. rewrite ?(unsigned_lit srcA), ?(unsigned_lit (dst + n)) in K2 by lia.
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit dst), ?(unsigned_lit (srcA + n)) in K3 by lia; [exfalso; lia|].
eapply memcpy_icpt_from; [exact MUs| exact WM| exact MI| exact ST1| exact ST2| exact FR].
Qed.
End S.

Theorem memcpy_icpt_spec {BAND : Band} :
forall (dst srcA n lo : Z) (src junk : list byte),
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),

bytes_at asegs m srcA src -> length src = Z.to_nat n -> rw_cells asegs m dst [CB (Z.to_nat n) junk] ->
srcA + n <= dst \/ dst + n <= srcA -> mem_inv asegs m -> 0 <= n ->

stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MEMCPY_ICPT_STACK ->
srcA + n <= lo \/ bv_unsigned sp <= srcA -> dst + n <= lo \/ bv_unsigned sp <= dst ->

shadow_base asegs m -> rt_consts_at asegs m ->

rng_ok m srcA n -> rng_ok m dst n ->
evt asegs (memcpy_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (wz dst) (wz srcA) (wz n) src lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz srcA) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memcpy_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros SRC LEN DST SEP MI N0 ST CEIL LO SST DSTK SB RC RS RD.
eapply memcpy_icpt_main; eassumption.
Qed.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig QDM6.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QNQk.Mq6 Q9Ho.Mq4 Q9Ho.Mq3. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma hjunk_C8x5 : forall m a, hjunk m a (a + 40) -> exists q0 q1 q2 q3 q4 : word, rw_cells asegs m a [C8 q0; C8 q1; C8 q2; C8 q3; C8 q4].
Proof.
intros m a J. destruct (hjunk_split m a (a + 16) (a + 40) J ltac:(lia)) as [J1 J2].
destruct (hjunk_C8x2 m a J1) as (q0 & q1 & H1).
destruct (hjunk_split m (a + 16) (a + 16 + 16) (a + 40) J2 ltac:(lia)) as [J3 J4].
destruct (hjunk_C8x2 m (a + 16) J3) as (q2 & q3 & H2).
replace (a + 40) with (a + 16 + 16 + 8) in J4 by lia. destruct (hjunk_C8 m (a + 16 + 16) J4) as (q4 & H3).
exists q0, q1, q2, q3, q4.
apply (proj2 (rw_cells_app asegs m a [C8 q0; C8 q1] [C8 q2; C8 q3; C8 q4])). split; [exact H1|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m (a + 16) [C8 q2; C8 q3] [C8 q4])). split; [exact H2|]. cbn [cells_size csize Nat.add]. exact H3.
Qed.

Lemma unw_readable_prologue : forall RE W m m' (bp : Z) (s0v rav : word),
munch W m m' -> (forall x, bp <= x -> outside W x) ->
rw_cells asegs m' (bp - 16) [C8 s0v; C8 rav] ->
unw_readable asegs RE m bp -> unw_readable asegs RE m' (bp - 16).
Proof.
intros RE W m m' bp s0v rav MU OUT FR UR x Hx XR.
destruct (Z.lt_ge_cases x bp) as [LOW|HIGH].
- pose proof (rw_cells_bytes_at asegs m' (bp - 16) _ FR) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
destruct B as (_ & _ & B). specialize (B (Z.to_nat (x - (bp - 16)))).
replace (bp - 16 + Z.of_nat (Z.to_nat (x - (bp - 16)))) with x in B by lia.
assert (LL : (Z.to_nat (x - (bp - 16)) < length (le8 s0v ++ le8 rav))%nat) by (rewrite length_app, !length_le8; lia).
rewrite (B LL). destruct (nth_error (le8 s0v ++ le8 rav) (Z.to_nat (x - (bp - 16)))) as [b|] eqn:E; [exists b; reflexivity|].
apply nth_error_None in E. lia.
- destruct (UR x ltac:(lia) XR) as (b & E). exists b. unfold mrd in *. rewrite (MU (wa x)); [exact E|].
rewrite wa_unsigned by lia. apply OUT. lia.
Qed.

Lemma alb_remove_perm : forall p LB LB', Permutation LB LB' -> Permutation (alb_remove p LB) (alb_remove p LB').
Proof.
intros p LB LB' P. unfold alb_remove. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
- constructor.
- destruct (negb (aptr_eqb (ablk_id x) p)); [apply perm_skip; exact IH| exact IH].
- destruct (negb (aptr_eqb (ablk_id y) p)), (negb (aptr_eqb (ablk_id x) p)); try apply perm_swap; try apply Permutation_refl; apply perm_skip; apply Permutation_refl.
- eapply perm_trans; eassumption.
Qed.

Lemma alb_remove_sub : forall p LB b, In b (alb_remove p LB) -> In b LB.
Proof. intros p LB b H. apply In_alb_remove in H as [H _]. exact H. Qed.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb QmP7.Mq1 Q9Ho.Mq3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Lemma cr_pure_div8 : forall a G c K, cr_pure a G c K -> 1 <= c <= 31 ->
(exists qa, 0 <= qa /\ c_alloc_user (cls a c) = 8 * qa /\ qa = ncarved G c * (class_size c / 8))
/\ (exists qm, 0 <= qm /\ c_mapped_user (cls a c) = 8 * qm)
/\ class_size c = 8 * (class_size c / 8).
Proof.
intros a G c K PU Hc. pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5). rewrite KM in G5.
pose proof (class_size_facts c Hc) as [S1 S2].
assert (E8 : class_size c = 8 * (class_size c / 8)) by (Z.div_mod_to_equations; lia).
split; [| split; [| exact E8]].
- exists (ncarved G c * (class_size c / 8)). unfold ncarved. split; [nia|]. split; [| reflexivity]. rewrite <- G1. nia.
- exists (c_mapped_user (cls a c) / 8). Z.div_mod_to_equations. lia.
Qed.

Definition cr_slots (a : AState) (G : ghost) (RE : aentry) (m : mem) (c : Z) : Prop :=
(forall i t, tag_at G c i = Some t -> tag_prim t = true -> hjunk m (slot_beg RE c i) (slot_beg RE c i + class_size c))
/\ (forall i t, tag_at G c i = Some t -> tag_prim t = true ->
rw_cells asegs m (SH (slot_beg RE c i)) [CB (Z.to_nat (class_size c / 8)) (repeat fa_byte (Z.to_nat (class_size c / 8)))]).

Lemma cr_user_split : forall a G RE m c,
cr_user a G RE m c <->
cr_slots a G RE m c
/\ hjunk m (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) (reg_beg (ae_L RE) c + c_mapped_user (cls a c))
/\ rw_cells asegs m (SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)))
[CB (Z.to_nat ((c_mapped_user (cls a c) - c_alloc_user (cls a c)) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user (cls a c) - c_alloc_user (cls a c)) / 8)))]
/\ hjunk m (SH (reg_beg (ae_L RE) c + c_mapped_user (cls a c))) (SH (reg_beg (ae_L RE) c + kFreeArrayOffset)).
Proof. intros. unfold cr_user, cr_slots. tauto. Qed.

Definition szone (RE : aentry) (c au : Z) (z : Z) : Prop :=
(reg_beg (ae_L RE) c <= z < reg_beg (ae_L RE) c + au) \/ (SH (reg_beg (ae_L RE) c) <= z < SH (reg_beg (ae_L RE) c) + au / 8).

Lemma cr_slots_agree : forall a G RE m m' c K,
cr_pure a G c K -> cr_slots a G RE m c -> 1 <= c <= 31 ->
agree_on asegs (szone RE c (c_alloc_user (cls a c))) m m' -> cr_slots a G RE m' c.
Proof.
intros a G RE m m' c K PU [SL SS] Hc AG.
pose proof (cr_pure_div8 a G c K PU Hc) as ((qa & QA0 & QA & QAE) & _ & E8).
pose proof (class_size_facts c Hc) as [S1 S2].
assert (GEOM : forall i t, tag_at G c i = Some t ->
0 <= i /\ (i + 1) * class_size c <= c_alloc_user (cls a c) /\ slot_beg RE c i = reg_beg (ae_L RE) c + i * class_size c).
{ intros i t Ht. pose proof (tag_at_Some_lt _ _ _ _ Ht) as [I1 I2]. rewrite QA, QAE. split; [lia|]. split; [nia| reflexivity]. }
split.
- intros i t Ht Hp. eapply hjunk_agree; [exact AG| exact (SL i t Ht Hp)|]. intros z Hz.
pose proof (GEOM i t Ht) as (I1 & IL & SB). rewrite SB in Hz. left. clear - Hz I1 IL S1. nia.
- intros i t Ht Hp. eapply rw_cells_agree; [exact AG| exact (SS i t Ht Hp)|]. intros z Hz.
cbn [cells_size csize] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by lia.
pose proof (GEOM i t Ht) as (I1 & IL & SB). rewrite SB in Hz.
replace (i * class_size c) with (8 * (i * (class_size c / 8))) in Hz by nia. rewrite SH_plus8 in Hz.
right. rewrite QA, Z.mul_comm, Z.div_mul by lia. clear - Hz I1 IL S1 E8 QA QA0. nia.
Qed.

Lemma cr_slots_ext : forall a a' G RE m c, cr_slots a G RE m c -> cr_slots a' G RE m c.
Proof. intros. exact H. Qed.

Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
wr_at asegs m a n1 -> wr_at asegs m (a + n1) n2 -> wr_at asegs m a (n1 + n2).
Proof.
intros m a n1 n2 H1 H2 (A1 & B1 & W1) (A2 & B2 & W2). split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i n1).
- apply W1. lia.
- replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Lemma u32arr_nil : forall m A, 0 <= A <= 2^64 -> u32arr asegs m A [].
Proof. intros m A H. split; [apply bytes_at_nil; exact H|]. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.

Lemma u32arr_cons : forall m A (v : word) ws,
rw_cells asegs m A [C4 v] -> u32arr asegs m (A + 4) ws -> u32arr asegs m A (v :: ws).
Proof.
intros m A v ws [[_ HB] HW] [AB AW]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in HB, HW. rewrite app_nil_r in HB.
split.
- cbn [u32s]. apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite length_le4. split; [exact HB| exact AB].
- cbn [length]. replace (4 * Z.of_nat (S (length ws))) with (4 + 4 * Z.of_nat (length ws)) by lia.
apply wr_at_app; [lia| lia| exact HW| exact AW].
Qed.

Lemma u32arr_app : forall m A ws1 ws2,
u32arr asegs m A ws1 -> u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr asegs m A (ws1 ++ ws2).
Proof.
intros m A ws1 ws2 [B1 W1] [B2 W2]. split.
- rewrite u32s_app. apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite u32s_length.
split; [exact B1|]. replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) by lia. exact B2.
- rewrite length_app. replace (4 * Z.of_nat (length ws1 + length ws2)) with (4 * Z.of_nat (length ws1) + 4 * Z.of_nat (length ws2)) by lia.
apply wr_at_app; [lia| lia| exact W1| exact W2].
Qed.

Lemma u32arr_hjunk : forall m A ws, u32arr asegs m A ws -> 0x647000 <= A -> hjunk m A (A + 4 * Z.of_nat (length ws)).
Proof.
intros m A ws [B W] HA. destruct W as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros a Ha.
specialize (W2 (a - A) ltac:(lia)). replace (A + (a - A)) with a in W2 by lia.
rewrite a_wview_overlay in W2 by (rewrite wa_unsigned by lia; lia). unfold wa in W2.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b| exfalso; apply W2; reflexivity].
rewrite <- E. reflexivity.
Qed.

End Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig Qc6I QJFf.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb Q9Ho.Mq3.
Import QXcn.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Definition quar_img : list (Z * Z) :=
[ (A_INSTANCE + 728, 64); (A_INSTANCE + 816, 2800); (0x0f33c0, 0x81038); (0x181c48, 4) ].

Lemma quar_img_ok : forall x, in_ivs quar_img x ->
~ in_ivs rtconst_img x /\ ~ (A_INSTANCE + 104 <= x < A_INSTANCE + 728) /\ x <> 0x174420 /\ ~ (A_ERRNO <= x < A_ERRNO + 4)
/\ ~ (0x1c4088 <= x < 0x1c4088 + 0x450028) /\ x < 0x647000 /\ 0x10000 <= x.
Proof.
intros x (iv & Hin & [H1 H2]).
assert (F : forallb (fun iv => forallb (fun jv => (fst iv + snd iv <=? fst jv) || (fst jv + snd jv <=? fst iv))
(rtconst_img ++ [(A_INSTANCE + 104, 624); (0x174420, 1); (A_ERRNO, 4); (0x1c4088, 0x450028)])
&& (fst iv + snd iv <=? 0x647000) && (0x10000 <=? fst iv)) quar_img = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in F. specialize (F iv Hin). apply andb_prop in F as [F F7]. apply Z.leb_le in F7. apply andb_prop in F as [F F6]. apply Z.leb_le in F6.
rewrite forallb_forall in F.
assert (D : forall jv, In jv (rtconst_img ++ [(A_INSTANCE + 104, 624); (0x174420, 1); (A_ERRNO, 4); (0x1c4088, 0x450028)]) ->
~ (fst jv <= x < fst jv + snd jv)).
{ intros jv Hjv Hx. specialize (F jv Hjv). apply orb_prop in F as [F|F]; apply Z.leb_le in F; lia. }
split; [| split; [| split; [| split; [| split; [| split; lia]]]]].
- intros (jv & Hjv & [J1 J2]). apply (D jv); [apply in_app_iff; left; exact Hjv| lia].
- intros Hx. apply (D (A_INSTANCE + 104, 624)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
- intros ->. apply (D (0x174420, 1)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
- intros Hx. apply (D (A_ERRNO, 4)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
- intros Hx. apply (D (0x1c4088, 0x450028)); [apply in_app_iff; right; cbn; tauto| cbn [fst snd]; lia].
Qed.

Section Excl.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.

Let RL : rlay_ok RE X := gc_rlay a LB0 FS0 G RE X GC.

Inductive qloc (x : Z) : Prop :=
| QL_T    : rl_T X + 80 <= x < rl_T X + 208 -> qloc x
| QL_img  : in_ivs quar_img x -> qloc x
| QL_slot : forall c i t, tag_at G c i = Some t -> tag_quar t = true -> in_iv (slot_beg RE c i, class_size c) x -> qloc x
| QL_slsh : forall c i t, tag_at G c i = Some t -> tag_quar t = true -> in_sh (slot_beg RE c i, class_size c) x -> qloc x
| QL_sec  : forall e, In e (as_reg a) -> ~ sec_live LB0 e -> se_beg e + kPage <= x < se_beg e + se_size e -> qloc x
| QL_sesh : forall e, In e (as_reg a) -> ~ sec_live LB0 e -> in_sh (se_beg e + kPage, se_size e - kPage) x -> qloc x.

Lemma fp_RQuar_loc : forall x, fp_RQuar a LB0 G RE X x -> qloc x.
Proof.
intros x [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- apply QL_T. destruct H; cbn [fst snd] in *; lia.
- apply QL_img. exists (A_INSTANCE + 728, 64). split; [cbn; tauto| exact H].
- apply QL_img. exists (A_INSTANCE + 816, 2800). split; [cbn; tauto| exact H].
- apply QL_img. exists (0x0f33c0, 0x81038). split; [cbn; tauto| exact H].
- apply QL_img. exists (0x181c48, 4). split; [cbn; tauto| exact H].
- destruct H as (c & i & t & Ht & Hq & Hx). eapply QL_slot; eauto.
- destruct H as (c & i & t & Ht & Hq & Hx). eapply QL_slsh; eauto.
- destruct H as (e & He & NL & Hx). eapply QL_sec; eauto.
- destruct H as (e & He & NL & Hx). eapply QL_sesh; eauto.
Qed.

Local Ltac zfacts :=
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & TC & TP & TA); cbn [fst snd] in TK, TC, TP, TA;
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & PC & _ & AK & AC & PA);
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _);
unfold iv_disjoint, prim_hi, ptrarr_hi in TP, TA, PA, PC, AC; cbn [fst snd] in TP, TA, PA;
pose proof SH_band as SHB0;
rewrite ?KHI_eq in *.

Local Ltac lit := rewrite ?KHI_eq in *.

Local Ltac shband H :=
lazymatch type of H with in_sh (?lo, ?len) ?x =>
let B := fresh "SB" in
assert (B : kLowEnd <= x < KHI)
by (apply (in_sh_band lo len x);
[first [assumption| Z.div_mod_to_equations; lia]| lia| rewrite ?KHI_eq in *; lia| idtac; unfold prim_hi in *; lia| exact H]);
unfold kLowEnd, KHI in B
end.

Lemma qslot_facts : forall c i t, tag_at G c i = Some t ->
prim_lo RE <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= prim_hi RE /\ slot_beg RE c i mod 8 = 0
/\ 1 <= c <= 31 /\ reg_beg (ae_L RE) c <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= reg_beg (ae_L RE) c + kFreeArrayOffset
/\ 32 <= class_size c /\ reg_beg (ae_L RE) c = prim_lo RE + c * 2^32 /\ fa_beg (ae_L RE) c = reg_beg (ae_L RE) c + kFreeArrayOffset.
Proof.
intros c i t Ht. pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & P2 & P3 & _ & C1 & R1 & R2 & S1 & _).
pose proof (region_in_prim RE c C1) as (Q1 & Q2 & Q3 & Q4). repeat split; try assumption; lia.
Qed.

Lemma qsec_facts : forall e, In e (as_reg a) ->
se_beg e mod 4096 = 0 /\ appr_lia (se_beg e) (se_size e) /\ se_beg e + se_size e <= band_lo /\ kPage + 16 <= se_size e
/\ iv_disjoint (se_beg e, se_size e) (prim_lo RE, 2^37 + 0x1000)
/\ iv_disjoint (se_beg e, se_size e) (ptrarr_lo RE, 0x800000)
/\ Forall (iv_disjoint (se_beg e, se_size e)) (rlay_objs RE X).
Proof.
intros e He. pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & D1 & D2 & D3).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
pose proof kconsts as (_ & _ & _ & _ & KP & _). rewrite KP in *. split; [exact E1|]. split; [apply appr_to_lia; [lia| lia| exact E2]|]. repeat split; try assumption. lia.
Qed.

Lemma obj_vs_T : forall o x, In o (rlay_objs RE X) -> o <> (rl_T X, 0x1000) -> in_iv o x -> rl_T X <= x < rl_T X + 0x1000 -> False.
Proof.
intros o x Ho NE [O1 O2] Hx.
pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (T_obj RE X) NE) as D. unfold iv_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma obj_vs_sec : forall o e x, In o (rlay_objs RE X) -> In e (as_reg a) -> in_iv o x -> se_beg e <= x < se_beg e + se_size e -> False.
Proof.
intros o e x Ho He [O1 O2] Hx. pose proof (qsec_facts e He) as (_ & _ & _ & _ & _ & _ & F). lit.
pose proof (proj1 (List.Forall_forall _ _) F o Ho) as D. unfold iv_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma fpQ_RTconst : forall x, fp_RQuar a LB0 G RE X x -> fp_RTconst RE X x -> False.
Proof.
intros x FQ FT. zfacts. destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- exact (rt_avoid_Thigh RE X (rl_T X + 80) (rl_T X + 208) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT).
- pose proof (quar_img_ok x H) as (NI & _ & _ & _ & _ & LT & GT).
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & HO)].
2:{ pose proof (rl_objs_lia a LB0 FS0 G RE X GC o Ho) as (_ & K & _). destruct HO as [O1 O2]. rewrite ?KHI_eq in K. lia. }
destruct FT as [F|[F|[F|F]]]; [exact (NI F)| destruct F; cbn [fst snd] in *; lia| |].
+ pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ctx_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
+ pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dtls_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H; cbn [fst snd] in *.
exact (rt_avoid_prim RE X RL (slot_beg RE c i) (slot_beg RE c i + class_size c) P1 P2 x ltac:(split; cbn [fst snd]; lia) FT).
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & HO)]; [lia|]. eapply obj_vs_sec; [exact Ho| exact He| exact HO| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H.
exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
Qed.

Lemma fpQ_RStats : forall x, fp_RQuar a LB0 G RE X x -> fp_RStats RE X x -> False.
Proof.
intros x FQ FS. zfacts. unfold fp_RStats, A_ERRNO in FS. cbn [in_iv fst snd] in FS. unfold in_iv in FS. cbn [fst snd] in FS.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- lia.
- pose proof (quar_img_ok x H) as (_ & _ & N1 & N2 & _ & LT). unfold A_ERRNO in N2. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H; cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 H0 H i c KO PA AK PK TA TP FS x X RE BAND; lia | lia ]).
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H. (first [ clear - SB P3 P1 i c PA AK PK TA TP TK FS x X RE BAND; lia | lia ]).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct FS as [F|[F|F]]; [| lia| lia]. eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H. (first [ clear - SB E2 e PA AK PK TA TP TK FS x X RE BAND; lia | lia ]).
Qed.

Lemma fas_band : forall c y, 1 <= c <= 31 -> in_sh (fa_beg (ae_L RE) c, kFreeArraySize) y -> 0x2008fff7000 <= y < SH band_lo.
Proof.
intros c y Hc F. zfacts. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL).
apply (in_sh_heap _ kFreeArraySize y FAL); [lia| rewrite ?KHI_eq; lia| idtac; unfold prim_lo in *; lia| exact F].
Qed.
Lemma reg_band : forall c y, 1 <= c <= 31 -> in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) y -> 0x2008fff7000 <= y < SH band_lo.
Proof.
intros c y Hc F. zfacts. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (RAL & _).
apply (in_sh_heap _ kFreeArrayOffset y RAL); [lia| rewrite ?KHI_eq; lia| idtac; unfold prim_lo in *; lia| exact F].
Qed.
Lemma slot_band : forall c i t y, tag_at G c i = Some t -> in_sh (slot_beg RE c i, class_size c) y -> 0x2008fff7000 <= y < SH band_lo.
Proof.
intros c i t y Ht F. zfacts. pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB).
apply (in_sh_heap _ (class_size c) y P3); [lia| rewrite ?KHI_eq; lia| idtac; unfold prim_hi in *; lia| exact F].
Qed.
Lemma sec_band : forall e y, In e (as_reg a) -> in_sh (se_beg e + kPage, se_size e - kPage) y -> 0x7fff7000 <= y < 0x10007fff8000.
Proof.
intros e y He F. zfacts. pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _).
pose proof (in_sh_band (se_beg e + kPage) (se_size e - kPage) y ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(rewrite KP in *; lia) ltac:(lia) F) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.
Lemma hdr_band : forall e y, In e (as_reg a) -> in_sh (se_beg e, kPage) y -> 0x7fff7000 <= y < 0x10007fff8000.
Proof.
intros e y He F. zfacts. pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _).
pose proof (in_sh_band (se_beg e) kPage y ltac:(Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(rewrite KP in *; lia) ltac:(lia) F) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.
Lemma fs_band : forall y, in_sh (ae_fs_base RE, A_FS_MAP_SIZE) y -> 0x7fff7000 <= y < 0x10007fff8000.
Proof.
intros y F. pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE y ltac:(Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; lia) FC F) as B.
unfold kLowEnd, KHI in B. exact B.
Qed.

Lemma fpQ_RPrim : forall x, fp_RQuar a LB0 G RE X x -> fp_RPrim G RE X x -> False.
Proof.
intros x FQ FP. zfacts.

assert (PW : (prim_lo RE <= x < prim_hi RE /\ ~ in_slots (fun t => negb (tag_prim t)) RE G x)
\/ rl_T X + 208 <= x < rl_T X + 2800
\/ (0x2008fff7000 <= x < SH band_lo
/\ ((exists c, 1 <= c <= 31 /\ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) x)
\/ ((exists c, 1 <= c <= 31 /\ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) x) /\ ~ in_slots_sh (fun t => negb (tag_prim t)) RE G x)))).
{ destruct FP as [F|[F|[F|[F|[[F NS]|[F NS]]]]]].
- left. destruct F as [F1 F2]; cbn [fst snd] in F1, F2. split; [unfold region_info, prim_hi, prim_lo in *; lia|].
intros (c & i & t & Ht & _ & [S1 S2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & Sz & RB & FB). cbn [fst snd] in S1, S2.
unfold region_info, prim_hi, prim_lo in *. rewrite KO in *. lia.
- right; left. destruct F; cbn [fst snd] in *. lia.
- left. destruct F as (c & Hc & F). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). split; [unfold prim_hi, prim_lo in *; lia|].
intros (c' & i & t & Ht & _ & [S1 S2]). pose proof (qslot_facts c' i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & Sz & RB & FB). cbn [fst snd] in S1, S2.
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
- right; right. destruct F as (c & Hc & F). rewrite K32 in Hc. split; [exact (fas_band c x ltac:(lia) F)|]. left. exists c. split; [lia| exact F].
- left. destruct F as (c & Hc & F). rewrite K32 in Hc. pose proof (region_in_prim RE c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). unfold prim_hi, prim_lo in *. split; [lia| exact NS].
- right; right. destruct F as (c & Hc & F). rewrite K32 in Hc. split; [exact (reg_band c x ltac:(lia) F)|]. right. split; [| exact NS]. exists c. split; [lia| exact F]. }
clear FP.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
-  unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[PW _]]]; lia.
-  pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[PW _]]]; lia.
-  pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
unfold prim_hi, prim_lo in *. destruct PW as [[PW NS]|[PW|[PW _]]]; [| (first [ clear - R2 R1 P3 P2 P1 H2 H1 i c PW KO PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
apply NS. exists c, i, t. split; [exact Ht|]. split; [destruct t; cbn in Hq |- *; congruence|]. split; cbn [fst snd]; lia.
-  pose proof (slot_band c i t x Ht H) as SB. pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[_ [(c' & Hc' & F)|[(c' & Hc' & F) NS]]]]]; [lia| lia| |].
+ pose proof (region_in_prim RE c' Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c' RL) as (_ & _ & FAL).
eapply (in_sh_disjoint (slot_beg RE c i) (class_size c) (fa_beg (ae_L RE) c') kFreeArraySize x P3 FAL ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
+ apply NS. exists c, i, t. split; [exact Ht|]. split; [destruct t; cbn in Hq |- *; congruence| exact H].
-  pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[PW _]]]; [(first [ clear - D2 D1 E4 E2 H e PW KP PA AK PK TA TP x X RE BAND; lia | lia ])| | lia].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
-  pose proof (sec_band e x He H) as SB. pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
unfold prim_hi, prim_lo in *. destruct PW as [[PW _]|[PW|[_ [(c' & Hc' & F)|[(c' & Hc' & F) NS]]]]]; [lia| lia| |].
+ pose proof (region_in_prim RE c' Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c' RL) as (_ & _ & FAL).
eapply (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (fa_beg (ae_L RE) c') kFreeArraySize x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) FAL ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - FAL Q3 Q2 Q1 D2 D1 E4 E2 E1 e c' KP KS KO PA AK PK TA TP X RE BAND; lia | lia ]).
+ pose proof (region_in_prim RE c' Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c' RL) as (RAL & _).
eapply (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (reg_beg (ae_L RE) c') kFreeArrayOffset x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) RAL ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - RAL Q4 Q3 Q2 Q1 D2 D1 E4 E2 E1 e Hc' c' KP KS KO PA AK PK TA TP X RE BAND; lia | lia ]).
Qed.

Lemma fpQ_RChunks : forall x, fp_RQuar a LB0 G RE X x -> fp_RChunks a LB0 G RE X x -> False.
Proof.
intros x FQ FC. zfacts.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 H KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband F. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT).
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband F. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & Hl & [F1 F2]). cbn [fst snd] in F1, F2.
assert (NE : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [->|]; [right; intros ->; rewrite Ht in Ht'; inversion Ht'; subst; destruct t'; discriminate| left; assumption]).
pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' t' Ht Ht' NE). (first [ clear - H P3 P1 H2 H1 i c PA AK PK TA TP F2 F1 i' c' x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1. (first [ clear - D1 E2 RB R2 R1 C1 P3 P1 H2 H1 i c KP KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (qslot_facts c' i' t' Ht') as (P1' & P2' & P3' & C1' & R1' & R2' & S1' & RB' & FB'). lit. shband F. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1' & P2' & P3' & C1' & R1' & R2' & S1' & RB' & FB'). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c' & i' & t' & Ht' & Hl & F). pose proof (qslot_facts c' i' t' Ht') as (P1' & P2' & P3' & C1' & R1' & R2' & S1' & RB' & FB'). lit.
assert (NE : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [->|]; [right; intros ->; rewrite Ht in Ht'; inversion Ht'; subst; destruct t'; discriminate| left; assumption]).
pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' t' Ht Ht' NE) as D.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (slot_beg RE c' i') (class_size c') x P3 P3' ltac:(lia) ltac:(lia) D H F).
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (se_beg e + kPage) (se_size e - kPage) x P3 ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E2 RB R2 R1 C1 P3 P1 i c KP KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 D2 D1 E4 E2 H e KP KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & HL & F). assert (e' = e) as -> by (apply (sec_same a LB0 FS0 G RE X GC e' e x He' He); lia). exact (NL HL).
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband F. lia.
+ destruct F as (e' & He' & _ & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. shband F. lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2. shband H.
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e' & He' & _ & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. lia.
+ destruct F as (c & i & t & Ht & _ & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (slot_beg RE c i) (class_size c) x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) P3 ltac:(lia) ltac:(lia) ltac:((first [ clear - RB R2 R1 C1 P3 P1 D2 D1 E4 E2 e KP KO PA AK PK TA TP i c X RE BAND; lia | lia ])) H F).
+ destruct F as (e' & He' & HL & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
assert (DD : se_beg e + se_size e <= se_beg e' \/ se_beg e' + se_size e' <= se_beg e).
{ destruct (decide (se_beg e = se_beg e')) as [EQ|NEb].
- exfalso. pose proof (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' EQ) as <-. exact (NL HL).
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e' (gc_sec_disj a LB0 FS0 G RE X GC) He He'
ltac:(intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd] in D. lia. }
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (se_beg e' + kPage) (se_size e' - kPage) x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1' r0 D2 D1 E4 e KP PA AK PK TA TP e' X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - DD E2' D2 D1 E4 E2 e KP PA AK PK TA TP e' X RE BAND; lia | lia ])) H F).
Qed.

Lemma fpQ_RSec : forall x, fp_RQuar a LB0 G RE X x -> fp_RSec a RE X x -> False.
Proof.
intros x FQ FS. zfacts.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| pose proof (qsec_facts e He) as (_ & _ & _ & E4 & _); lia].
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (quar_img_ok x H) as (_ & NS & _ & _ & _ & LT).
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. apply NS. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1. (first [ clear - D1 E4 E2 RB R2 R1 C1 P3 P1 H2 H1 i c KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband F. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint in D1; cbn [fst snd] in D1.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (se_beg e) kPage x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 RB R2 R1 C1 P3 P1 i c KP KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. (first [ clear - D2 D1 E4 E2 H e KP PA AK PK TA TP H1 H0 x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & F). assert (e' = e) as -> by (apply (sec_same a LB0 FS0 G RE X GC e' e x He' He); [| lia]; pose proof (qsec_facts e' He') as (_ & _ & _ & E4' & _); lia). lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. shband F. lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. unfold iv_disjoint in D1, D2; cbn [fst snd] in D1, D2. shband H.
destruct FS as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ destruct F; cbn [fst snd] in *. (first [ clear - SB D2 D1 E4 E2 e KP PA AK PK TA TP H1 H0 x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
assert (DD : se_beg e + se_size e <= se_beg e' \/ se_beg e' + kPage <= se_beg e + kPage).
{ destruct (decide (se_beg e = se_beg e')) as [EQ|NEb].
- pose proof (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' EQ) as <-. right; lia.
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e' (gc_sec_disj a LB0 FS0 G RE X GC) He He'
ltac:(intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd] in D. (first [ clear - D NEb E4' E2' E1' D2 D1 E4 E2 E1 e KP PA AK PK TA TP e' X RE BAND; lia | lia ]). }
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (se_beg e') kPage x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q D2 D1 E4 E1 r1 e KP PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1' r0 D2 D1 E4 e KP PA AK PK TA TP e' X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:(lia) H F).
Qed.

Lemma fpQ_RDepot : forall x, fp_RQuar a LB0 G RE X x -> fp_RDepot RE X x -> False.
Proof.
intros x FQ FD. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & NC & NP & _). cbn [fst snd] in NK, NC, NP. unfold iv_disjoint in NP; cbn [fst snd] in NP.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & BC & BP & _). cbn [fst snd] in BK, BC, BP. unfold iv_disjoint in BP; cbn [fst snd] in BP.
rewrite ?KHI_eq in *.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
- destruct FD as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. lia.
+ eapply (obj_vs_T _ x (dn_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ eapply (obj_vs_T _ x (ssb_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & ND & LT).
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| lia].
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2.
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c NP KO PA AK PK TA TP H0 H x X RE BAND; lia | lia ])| destruct F; cbn [fst snd] in *; (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c BP KO PA AK PK TA TP H0 H x X RE BAND; lia | lia ])| (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c KO PA AK PK TA TP F x X RE BAND; lia | lia ])].
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H.
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct FD as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. lia.
+ eapply (obj_vs_sec _ e x (dn_obj RE X) He F). lia.
+ eapply (obj_vs_sec _ e x (ssb_obj RE X) He F). lia.
+ eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H.
destruct FD as [F|[F|[F|F]]]; [destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| destruct F; cbn [fst snd] in *; lia| lia].
Qed.

Lemma fpQ_RFake : forall x, fp_RQuar a LB0 G RE X x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x FQ FF. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & FP & _). cbn [fst snd] in FAL, FK, FC, FP. unfold iv_disjoint in FP; cbn [fst snd] in FP.
rewrite ?KHI_eq in *.
destruct (fp_RQuar_loc x FQ) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H]; destruct FF as [[F _]|[F _]].
- eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
- pose proof (fs_band x F). lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). destruct F; cbn [fst snd] in *. lia.
- pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT). pose proof (fs_band x F). lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; destruct F; cbn [fst snd] in *. (first [ clear - RB R2 R1 C1 P3 P1 H2 H1 i c FP FK KO PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct H as [H1 H2]; cbn [fst snd] in H1, H2. pose proof (fs_band x F). lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. shband H. destruct F; cbn [fst snd] in *. lia.
- pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (ae_fs_base RE) A_FS_MAP_SIZE x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - RB R2 R1 C1 P3 P1 i c FP FK FAL KO PA AK PK TA TP X RE BAND; lia | lia ])) H F).
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. eapply (obj_vs_sec _ e x (fs_obj RE X) He F). lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (fs_band x F). lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. shband H. destruct F; cbn [fst snd] in *. lia.
- pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 e PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - D E2 E1 e FK FAL KP PA AK PK TA TP X RE BAND; lia | lia ])) H F).
Qed.

Inductive ploc (x : Z) : Prop :=
| PL_ri    : region_info RE <= x < region_info RE + 0x1000 -> ploc x
| PL_T     : rl_T X + 208 <= x < rl_T X + 2800 -> ploc x
| PL_fas   : forall c, 1 <= c <= 31 -> fa_beg (ae_L RE) c <= x < fa_beg (ae_L RE) c + kFreeArraySize -> ploc x
| PL_fassh : forall c, 1 <= c <= 31 -> in_sh (fa_beg (ae_L RE) c, kFreeArraySize) x -> ploc x
| PL_reg   : forall c, 1 <= c <= 31 -> reg_beg (ae_L RE) c <= x < reg_beg (ae_L RE) c + kFreeArrayOffset ->
~ in_slots (fun t => negb (tag_prim t)) RE G x -> ploc x
| PL_regsh : forall c, 1 <= c <= 31 -> in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) x ->
~ in_slots_sh (fun t => negb (tag_prim t)) RE G x -> ploc x.

Lemma fp_RPrim_loc : forall x, fp_RPrim G RE X x -> ploc x.
Proof.
intros x [F|[F|[F|[F|[[F NS]|[F NS]]]]]]; pose proof kconsts as (_ & _ & _ & K32 & _).
- apply PL_ri. destruct F; cbn [fst snd] in *; lia.
- apply PL_T. destruct F; cbn [fst snd] in *; lia.
- destruct F as (c & Hc & F). apply (PL_fas x c); [rewrite K32 in Hc; lia| exact F].
- destruct F as (c & Hc & F). apply (PL_fassh x c); [rewrite K32 in Hc; lia| exact F].
- destruct F as (c & Hc & F). apply (PL_reg x c); [rewrite K32 in Hc; lia| exact F| exact NS].
- destruct F as (c & Hc & F). apply (PL_regsh x c); [rewrite K32 in Hc; lia| exact F| exact NS].
Qed.

Lemma fpP_RChunks : forall x, fp_RPrim G RE X x -> fp_RChunks a LB0 G RE X x -> False.
Proof.
intros x FP FC. zfacts.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS].
- unfold region_info, prim_lo in *. destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. unfold prim_lo in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. lia.
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F). lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). lia.
- destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. unfold prim_hi, prim_lo in *. (first [ clear - R2 R1 P3 P2 P1 H KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F). lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). lia.
- pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *.
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. unfold prim_lo in *. (first [ clear - D1 E2 Q3 Q2 Q1 H c KP KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_band c' i' t' x Ht' F). unfold prim_lo in *. lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). unfold prim_lo in *. lia.
- pose proof (fas_band c x Hc H) as SB. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL).
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
eapply (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (slot_beg RE c' i') (class_size c') x FAL P3 ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_hi, prim_lo in *. rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
eapply (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (se_beg e + kPage) (se_size e - kPage) x FAL ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - D1 E2 E1 FAL Q3 Q2 Q1 c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ]).
- pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & Hl & F). apply NS. exists c', i', t'. split; [exact Ht'|]. split; [destruct t'; try discriminate; reflexivity| exact F].
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. unfold prim_lo in *. lia.
+ destruct F as (c' & i' & t' & Ht' & _ & F). pose proof (slot_band c' i' t' x Ht' F). unfold prim_lo in *. lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). unfold prim_lo in *. lia.
- pose proof (reg_band c x Hc H) as SB. pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X c RL) as (RAL & _).
destruct FC as [[[F|F] _]|[F|F]].
+ destruct F as (c' & i' & t' & Ht' & _ & [F1 F2]). pose proof (qslot_facts c' i' t' Ht') as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. lia.
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (c' & i' & t' & Ht' & Hl & F). apply NS. exists c', i', t'. split; [exact Ht'|]. split; [destruct t'; try discriminate; reflexivity| exact F].
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1.
eapply (in_sh_disjoint (reg_beg (ae_L RE) c) kFreeArrayOffset (se_beg e + kPage) (se_size e - kPage) x RAL ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia)); [| exact H| exact F].
unfold prim_lo in *. (first [ clear - D1 E2 E1 RAL Q4 Q3 Q2 Q1 Hc c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ]).
Qed.

Lemma fpP_RSec : forall x, fp_RPrim G RE X x -> fp_RSec a RE X x -> False.
Proof.
intros x FP FS. zfacts.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL)
| pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (reg_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (RAL & _) ];
unfold prim_lo in *;
(destruct FS as [F|[F|[F|F]]];
[ destruct F; cbn [fst snd] in *; unfold A_INSTANCE in *; lia
| destruct F; cbn [fst snd] in *; (first [ clear - H PA AK PK TA TP H1 H0 x X RE BAND Q3 Q2 Q1 c KO FAL SB SHB0 KS RAL; lia | lia ])
| destruct F as (e & He & F); pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3); lit; unfold iv_disjoint in D1; cbn [fst snd] in D1
| destruct F as (e & He & F); pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3); lit; unfold iv_disjoint in D1; cbn [fst snd] in D1 ]).
all: unfold prim_hi, prim_lo in *; try (first [ clear - D1 E4 E2 H PA AK PK TA TP F e x X RE BAND Q3 Q2 Q1 c KO SB SHB0 KS; lia | lia ]).
all: try (pose proof (hdr_band e x He F); lia).
- eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
- exact (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (se_beg e) kPage x FAL ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 FAL Q3 Q2 Q1 c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
- exact (in_sh_disjoint (reg_beg (ae_L RE) c) kFreeArrayOffset (se_beg e) kPage x RAL ltac:(Z.div_mod_to_equations; (first [ clear - H5 q0 H1 H0 r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 RAL Q3 Q2 Q1 c KP KS KO PA AK PK TA TP e X RE BAND; lia | lia ])) H F).
Qed.

Lemma fpP_RDepot : forall x, fp_RPrim G RE X x -> fp_RDepot RE X x -> False.
Proof.
intros x FP FD. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & NC & NP & _). cbn [fst snd] in NK, NC, NP. unfold iv_disjoint in NP; cbn [fst snd] in NP.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & BC & BP & _). cbn [fst snd] in BK, BC, BP. unfold iv_disjoint in BP; cbn [fst snd] in BP.
rewrite ?KHI_eq in *.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4) | pose proof (reg_band c x Hc H) as SB ];
unfold prim_lo in *; destruct FD as [F|[F|[F|F]]].
all: try (destruct F as [F1 F2]; cbn [fst snd] in F1, F2; (first [ clear - H PK F2 x RE BAND NP PA AK TA TP F1 X BP TK Q2 Q1 c KO Q3 SB NK SHB0 BK Q4 Hc KS; lia | lia ])).
all: try (first [ clear - H PA AK PK TA TP F x X RE BAND Q3 Q2 Q1 c KO SB SHB0 TK KS; lia | lia ]).
- eapply (obj_vs_T _ x (dn_obj RE X)); [intros E; injection E; lia| exact F| lia].
- eapply (obj_vs_T _ x (ssb_obj RE X)); [intros E; injection E; lia| exact F| lia].
Qed.

Lemma fpP_RFake : forall x, fp_RPrim G RE X x -> fp_RFake FS0 RE X x -> False.
Proof.
intros x FP FF. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & FP' & _). cbn [fst snd] in FAL, FK, FC, FP'. unfold iv_disjoint in FP'; cbn [fst snd] in FP'.
rewrite ?KHI_eq in *.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (_ & _ & FAL2)
| pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (reg_band c x Hc H) as SB; pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4); pose proof (reg_beg_align RE X c RL) as (RAL & _) ];
unfold prim_lo in *; destruct FF as [[F _]|[F _]]; try (destruct F; cbn [fst snd] in *; (first [ clear - H FP' FK PA AK PK TA TP H1 H0 x X RE BAND Q3 Q2 Q1 c KO SB SHB0 Q4 Hc KS; lia | lia ])); try (pose proof (fs_band x F); lia).
- eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
- exact (in_sh_disjoint (fa_beg (ae_L RE) c) kFreeArraySize (ae_fs_base RE) A_FS_MAP_SIZE x FAL2 ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - FAL2 Q3 Q2 Q1 c FP' FK FAL KS KO PA AK PK TA TP X RE BAND; lia | lia ])) H F).
- exact (in_sh_disjoint (reg_beg (ae_L RE) c) kFreeArrayOffset (ae_fs_base RE) A_FS_MAP_SIZE x RAL ltac:(Z.div_mod_to_equations; (first [ clear - H10 q1 H1 H0 r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - RAL Q3 Q2 Q1 c FP' FK FAL KS KO PA AK PK TA TP X RE BAND; lia | lia ])) H F).
Qed.

Lemma fpP_RStats : forall x, fp_RPrim G RE X x -> fp_RStats RE X x -> False.
Proof.
intros x FP FS. zfacts. unfold fp_RStats, A_ERRNO, in_iv in FS. cbn [fst snd] in FS.
destruct (fp_RPrim_loc x FP) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS];
[ unfold region_info, prim_lo in H | | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4)
| pose proof (fas_band c x Hc H) as SB | pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4) | pose proof (reg_band c x Hc H) as SB ];
unfold prim_lo in *; (first [ clear - H PA AK PK TA TP FS x X RE BAND TK Q3 Q2 Q1 c KO SB SHB0 KS; lia | lia ]).
Qed.

Lemma fpS_excl : forall x, fp_RStats RE X x ->
(fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x \/ fp_RDepot RE X x \/ fp_RFake FS0 RE X x \/ fp_RTconst RE X x) -> False.
Proof.
intros x FS F. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & _). cbn [fst snd] in NK.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & _). cbn [fst snd] in BK.
rewrite ?KHI_eq in *.
assert (ST : (rl_T X + 2800 <= x < rl_T X + 3168) \/ (x < 0x647000 /\ (A_ERRNO <= x < A_ERRNO + 4 \/ x = 0x174420))).
{ unfold fp_RStats, in_iv in FS. cbn [fst snd] in FS. unfold A_ERRNO in *. (first [ clear - FK PA AK PK TA TP FS x X RE BAND; lia | lia ]). }
clear FS. unfold A_ERRNO in ST.
destruct F as [FC'|[FSe|[FD|[FF|FT]]]].
- destruct FC' as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. cbn [fst snd] in *. unfold prim_hi, prim_lo in *. (first [ clear - R2 R1 P3 P2 P1 ST FK KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ]).
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. destruct ST as [ST|ST]; [| (first [ clear - E2 E1 ST FK KP PA AK PK TA TP F e x X RE BAND; lia | lia ])].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F). lia.
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F). lia.
- destruct FSe as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. (first [ clear - ST FK PA AK PK TA TP TK H0 H x X RE BAND; lia | lia ]).
+ destruct F; cbn [fst snd] in *. (first [ clear - ST FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. destruct ST as [ST|ST]; [| (first [ clear - E4 E2 E1 ST FK KP PA AK PK TA TP F e x X RE BAND; lia | lia ])].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (e & He & F). pose proof (hdr_band e x He F). lia.
- destruct FD as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. lia.
+ destruct ST as [ST|ST]; [| destruct F; cbn [fst snd] in *; (first [ clear - ST NK FK PA AK PK TA TP H x X RE BAND; lia | lia ])]. eapply (obj_vs_T _ x (dn_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ destruct ST as [ST|ST]; [| destruct F; cbn [fst snd] in *; (first [ clear - ST BK FK PA AK PK TA TP H x X RE BAND; lia | lia ])]. eapply (obj_vs_T _ x (ssb_obj RE X)); [intros E; injection E; lia| exact F| lia].
+ (first [ clear - ST FK PA AK PK TA TP TK F x X RE BAND; lia | lia ]).
- destruct FF as [[F _]|[F _]].
+ destruct ST as [ST|ST]; [| destruct F; cbn [fst snd] in *; (first [ clear - ST FK FAL PA AK PK TA TP H0 H x X RE BAND; lia | lia ])]. eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
+ pose proof (fs_band x F). (first [ clear - H ST FK PA AK PK TA TP TK x X RE BAND; lia | lia ]).
- destruct ST as [ST|[LT ST]].
+ exact (rt_avoid_Thigh RE X (rl_T X + 2800) (rl_T X + 3168) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT).
+ destruct (fp_RTconst_where RE X x FT) as [_|(o & Ho & HO)].
2:{ pose proof (rl_objs_lia a LB0 FS0 G RE X GC o Ho) as (_ & K & _). destruct HO as [O1 O2]. rewrite ?KHI_eq in K. (first [ clear - K O2 O1 o ST FK PA AK PK TA TP x X RE BAND; lia | lia ]). }
destruct FT as [FI|[FT|[FT|FT]]].
* destruct FI as (iv & Hin & [I1 I2]).
assert (CK : forallb (fun iv => ((fst iv + snd iv <=? 6444156) || (6444160 <=? fst iv)) && ((fst iv + snd iv <=? 0x174420) || (0x174421 <=? fst iv))) rtconst_img = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in CK. specialize (CK iv Hin). apply andb_prop in CK as [C1 C2].
apply orb_prop in C1 as [C1|C1]; apply Z.leb_le in C1; apply orb_prop in C2 as [C2|C2]; apply Z.leb_le in C2; (first [ clear - C2 ST FK PA AK PK TA TP I2 iv x X RE BAND C1 I1; lia | lia ]).
* destruct FT; cbn [fst snd] in *. (first [ clear - ST FK AK PK TK H0 H x X RE BAND; lia | lia ]).
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ctx_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; lia.
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dtls_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; (first [ clear - K ST FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
Qed.

Lemma depot_img_ok : forall x, 0x1c4088 <= x < 0x1c4088 + 0x450028 ->
~ in_ivs rtconst_img x /\ ~ (A_INSTANCE + 104 <= x < A_INSTANCE + 728) /\ x < 0x647000.
Proof.
intros x Hx.
assert (F : forallb (fun jv => (fst jv + snd jv <=? 0x1c4088) || (0x1c4088 + 0x450028 <=? fst jv)) (rtconst_img ++ [(A_INSTANCE + 104, 624)]) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in F.
split; [| split; [| lia]].
- intros (jv & Hjv & [J1 J2]). specialize (F jv ltac:(apply in_app_iff; left; exact Hjv)). apply orb_prop in F as [F|F]; apply Z.leb_le in F; lia.
- intros H. specialize (F (A_INSTANCE + 104, 624) ltac:(apply in_app_iff; right; left; reflexivity)). cbn [fst snd] in F.
apply orb_prop in F as [F|F]; apply Z.leb_le in F; lia.
Qed.

Lemma fpD_excl : forall x, fp_RDepot RE X x ->
(fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x \/ fp_RFake FS0 RE X x \/ fp_RTconst RE X x) -> False.
Proof.
intros x FD F. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & FP' & FA'). cbn [fst snd] in FAL, FK, FC, FP', FA'.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & NC & NP & NA). cbn [fst snd] in NK, NC, NP, NA.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & BC & BP & BA). cbn [fst snd] in BK, BC, BP, BA.
unfold iv_disjoint, prim_lo in FP', FA', NP, NA, BP, BA; cbn [fst snd] in FP', FA', NP, NA, BP, BA. unfold prim_lo in *.
rewrite ?KHI_eq in *.

assert (DW : (0x1c4088 <= x < 0x1c4088 + 0x450028)
\/ (exists o, In o (rlay_objs RE X) /\ in_iv o x /\ o <> (ae_fs_base RE, A_FS_MAP_SIZE) /\ o <> (rl_ctx X, 0x10000)
/\ (o = (rl_dn X, 0x100000) \/ o = (rl_ssb X, 0x800000)))
\/ x = rl_T X + 3168).
{ destruct FD as [H|[H|[H|H]]].
- left. destruct H; cbn [fst snd] in *; lia.
- right; left. exists (rl_dn X, 0x100000). split; [apply dn_obj|]. split; [exact H|].
split; [intros E; injection E; unfold A_FS_MAP_SIZE; lia|]. split; [intros E; injection E; lia| left; reflexivity].
- right; left. exists (rl_ssb X, 0x800000). split; [apply ssb_obj|]. split; [exact H|].
split; [intros E; injection E; unfold A_FS_MAP_SIZE; lia|]. split; [intros E; injection E; lia| right; reflexivity].
- right; right. exact H. }
clear FD.
assert (OBJK : forall o, In o (rlay_objs RE X) -> in_iv o x -> appr_lia (fst o) (snd o) /\ fst o <= x < fst o + snd o /\ x < band_lo
/\ (x < al_space_beg (ae_L RE) \/ al_space_beg (ae_L RE) + (2^37 + 4096) <= x)
/\ (x < ptrarr_lo RE \/ ptrarr_lo RE + 8388608 <= x)).
{ intros o Ho [O1 O2]. pose proof (rl_objs_lia a LB0 FS0 G RE X GC o Ho) as (_ & K & Ce & Dp & Da).
unfold iv_disjoint, prim_lo in Dp, Da. cbn [fst snd] in Dp, Da. split; [exact K|]. clear - O1 O2 Ce Dp Da. lia. }
clear FP' FA' NP NA BP BA.
destruct F as [FC'|[FSe|[FF|FT]]].
- destruct FC' as [[[F|F] _]|[F|F]].
+ destruct F as (c & i & t & Ht & _ & [F1 F2]). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. cbn [fst snd] in *.
destruct DW as [D|[(o & Ho & HO & _ & _ & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H R2 R1 P3 P2 P1 o FK KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ])| (first [ clear - R2 R1 P3 P2 P1 D FK KO PA AK PK TA TP F2 F1 i c x X RE BAND; lia | lia ])].
+ destruct F as (e & He & _ & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| exact (obj_vs_sec o e x Ho He HO ltac:(lia))|].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (c & i & t & Ht & _ & F). pose proof (slot_band c i t x Ht F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK SHB0 PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
+ destruct F as (e & He & _ & F). pose proof (sec_band e x He F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
- destruct FSe as [F|[F|[F|F]]].
+ destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & NS & _); unfold A_INSTANCE in NS; lia| pose proof (OBJK o Ho HO); (first [ clear - H1 o FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ])| lia].
+ destruct F; cbn [fst snd] in *.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); (first [ clear - D FK AK PK H x RE BAND; lia | lia ])| pose proof (OBJK o Ho HO); lia| (first [ clear - D FK PA AK PK TA TP H0 H x X RE BAND; lia | lia ])].
+ destruct F as (e & He & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| exact (obj_vs_sec o e x Ho He HO ltac:(lia))|].
eapply (obj_vs_sec _ e x (T_obj RE X) He); [split; cbn [fst snd]; lia| lia].
+ destruct F as (e & He & F). pose proof (hdr_band e x He F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
- destruct FF as [[F _]|[F _]].
+ destruct DW as [D|[(o & Ho & HO & NEF & _ & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); destruct F; cbn [fst snd] in *; lia| |].
* pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (fs_obj RE X) NEF) as D. unfold iv_disjoint in D. destruct HO, F; cbn [fst snd] in *. lia.
* eapply (obj_vs_T _ x (fs_obj RE X)); [intros E; injection E; unfold A_FS_MAP_SIZE; lia| exact F| lia].
+ pose proof (fs_band x F).
destruct DW as [D|[(o & Ho & HO & _)|D]]; [pose proof (depot_img_ok x D) as (_ & _ & LT); lia| pose proof (OBJK o Ho HO); (first [ clear - H0 H o FK PA AK PK TA TP x X RE BAND; lia | lia ])| lia].
- destruct DW as [D|[(o & Ho & HO & NEF & NEC & EO)|D]].
+ pose proof (depot_img_ok x D) as (NI & _ & LT).
destruct (fp_RTconst_where RE X x FT) as [_|(o & Ho & HO)]; [| pose proof (OBJK o Ho HO); (first [ clear - H o D FK PA AK PK TA TP x X RE BAND; lia | lia ])].
destruct FT as [FI|[FT|[FT|FT]]]; [exact (NI FI)| destruct FT; cbn [fst snd] in *; lia| |].
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ctx_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; lia.
* pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dtls_obj RE X)) as (_ & K & _). rewrite ?KHI_eq in K. destruct FT; cbn [fst snd] in *; lia.
+ pose proof (OBJK o Ho HO) as (XB & XI & _).
destruct (fp_RTconst_where RE X x FT) as [LT|(o' & Ho' & HO')]; [lia|].
destruct (decide (o = o')) as [<-|NE].
*
destruct FT as [FI|[FT|[FT|FT]]].
-- pose proof (proj1 (rtconst_img_ok x FI)). lia.
-- assert (NE : o <> (rl_T X, 0x1000)) by (destruct EO as [-> | ->]; intros E; injection E; lia).
apply (obj_vs_T o x Ho NE HO). destruct FT; cbn [fst snd] in *; lia.
-- pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (ctx_obj RE X) NEC) as D. unfold iv_disjoint in D. destruct HO, FT; cbn [fst snd] in *. (first [ clear - D XI o FK PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
-- assert (NED : o <> (rl_dtls X, 0x1000)) by (destruct EO as [-> | ->]; intros E; injection E; lia).
pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho (dtls_obj RE X) NED) as D. unfold iv_disjoint in D. destruct HO, FT; cbn [fst snd] in *. (first [ clear - D XI o FK PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
* pose proof (rl_objs_disj a LB0 FS0 G RE X GC _ _ Ho Ho' NE) as D. unfold iv_disjoint in D. destruct HO, HO'; (first [ clear - D H2 H1 o' XI o FK PA AK PK TA TP x X RE BAND; lia | lia ]).
+ exact (rt_avoid_Thigh RE X (rl_T X + 3168) (rl_T X + 3169) RL ltac:(lia) ltac:(lia) x ltac:(split; cbn [fst snd]; lia) FT).
Qed.

Lemma fpC_excl : forall x, fp_RChunks a LB0 G RE X x -> (fp_RTconst RE X x \/ fp_RSec a RE X x \/ fp_RFake FS0 RE X x) -> False.
Proof.
intros x FC F. zfacts.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC' & FP' & FA'). cbn [fst snd] in FAL, FK, FC', FP', FA'.
unfold iv_disjoint, prim_lo in FP'; cbn [fst snd] in FP'. unfold prim_lo in *. rewrite ?KHI_eq in *.

assert (CW : (exists c i t, tag_at G c i = Some t /\ in_iv (slot_beg RE c i, class_size c) x)
\/ (exists e, In e (as_reg a) /\ se_beg e + kPage <= x < se_beg e + se_size e)
\/ (exists c i t, tag_at G c i = Some t /\ in_sh (slot_beg RE c i, class_size c) x)
\/ (exists e, In e (as_reg a) /\ in_sh (se_beg e + kPage, se_size e - kPage) x)).
{ destruct FC as [[[H|H] _]|[H|H]].
- left. destruct H as (c & i & t & Ht & _ & Hx). exists c, i, t. auto.
- right; left. destruct H as (e & He & _ & Hx). exists e. auto.
- right; right; left. destruct H as (c & i & t & Ht & _ & Hx). exists c, i, t. auto.
- right; right; right. destruct H as (e & He & _ & Hx). exists e. auto. }
clear FC. destruct F as [FT|[FSe|FF]].
- destruct CW as [(c & i & t & Ht & Hx)|[(e & He & Hx)|[(c & i & t & Ht & Hx)|(e & He & Hx)]]].
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. destruct Hx; cbn [fst snd] in *.
exact (rt_avoid_prim RE X RL (slot_beg RE c i) (slot_beg RE c i + class_size c) P1 P2 x ltac:(split; cbn [fst snd]; lia) FT).
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit.
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & HO)]; [lia|]. eapply obj_vs_sec; [exact Ho| exact He| exact HO| lia].
+ pose proof (slot_band c i t x Ht Hx). exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
+ pose proof (sec_band e x He Hx). exact (rt_avoid_gap RE X RL 0x7fff7000 0x10007fff8000 ltac:(unfold kLowEnd; lia) ltac:(rewrite ?KHI_eq; lia) x ltac:(split; cbn [fst snd]; lia) FT).
- destruct CW as [(c & i & t & Ht & Hx)|[(e & He & Hx)|[(c & i & t & Ht & Hx)|(e & He & Hx)]]];
destruct FSe as [F|[F|[F|F]]].
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. destruct Hx, F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. destruct Hx, F; cbn [fst snd] in *. (first [ clear - R2 R1 P3 P2 P1 H0 H i c FK KO PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_hi, prim_lo in *; cbn [fst snd] in D1. destruct Hx; cbn [fst snd] in *. (first [ clear - D1 E4 E2 R2 R1 P3 P2 P1 H0 H i c FK KO PA AK PK TA TP F e x X RE BAND; lia | lia ]).
+ destruct F as (e & He & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *.
pose proof (hdr_band e x He F). destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & _). lit. unfold iv_disjoint in D2; cbn [fst snd] in D2. destruct F; cbn [fst snd] in *. (first [ clear - D2 E2 Hx e FK KP PA AK PK TA TP H0 H x X RE BAND; lia | lia ]).
+ destruct F as (e' & He' & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
pose proof (sec_same a LB0 FS0 G RE X GC e' e x He' He ltac:(lia) ltac:(lia)) as ->. lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (hdr_band e' x He' F). lia.
+ pose proof (slot_band c i t x Ht Hx). destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (slot_band c i t x Ht Hx). destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e & He & F). pose proof (slot_band c i t x Ht Hx). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. lia.
+ destruct F as (e & He & F). pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit.
pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & _). lit. unfold iv_disjoint, prim_hi, prim_lo in *; cbn [fst snd] in D1.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (se_beg e) kPage x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 PA AK PK TA TP e X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - D1 E4 E2 E1 R2 R1 P3 P2 P1 i c FK KP KO PA AK PK TA TP e X RE BAND; lia | lia ])) Hx F).
+ pose proof (sec_band e x He Hx). destruct F; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
+ pose proof (sec_band e x He Hx). destruct F; cbn [fst snd] in *. lia.
+ destruct F as (e' & He' & F). pose proof (sec_band e x He Hx). pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit. lia.
+ destruct F as (e' & He' & F). pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & D1 & D2 & D3). lit. pose proof (qsec_facts e' He') as (E1' & E2' & E3' & E4' & _). lit.
assert (DD : se_beg e + se_size e <= se_beg e' \/ se_beg e' + kPage <= se_beg e + kPage).
{ destruct (decide (se_beg e = se_beg e')) as [EQ|NEb].
- pose proof (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' EQ) as <-. right; lia.
- pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e' (gc_sec_disj a LB0 FS0 G RE X GC) He He'
ltac:(intros EQ; apply NEb; exact (f_equal fst EQ))) as D. unfold iv_disjoint in D. cbn [fst snd] in D. (first [ clear - D NEb E4' E2' E1' E2 E1 e FK KP PA AK PK TA TP e' X RE BAND; lia | lia ]). }
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (se_beg e') kPage x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H9 q1 H0 H r q E1 r1 e PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1' r0 PA AK PK TA TP e' X RE BAND; lia | lia ])) ltac:(lia) ltac:(lia) ltac:((first [ clear - DD e AK e' RE BAND; lia | lia ])) Hx F).
- destruct CW as [(c & i & t & Ht & Hx)|[(e & He & Hx)|[(c & i & t & Ht & Hx)|(e & He & Hx)]]]; destruct FF as [[F _]|[F _]].
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. destruct Hx, F; cbn [fst snd] in *. (first [ clear - R2 R1 P3 P2 P1 H0 H i c FP' FK KO PA AK PK TA TP H2 H1 x X RE BAND; lia | lia ]).
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *. pose proof (fs_band x F). destruct Hx; cbn [fst snd] in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). eapply (obj_vs_sec _ e x (fs_obj RE X) He F). lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _). lit. pose proof (fs_band x F). lia.
+ pose proof (slot_band c i t x Ht Hx). destruct F; cbn [fst snd] in *. lia.
+ pose proof (qslot_facts c i t Ht) as (P1 & P2 & P3 & C1 & R1 & R2 & S1 & RB & FB). lit. unfold prim_hi, prim_lo in *.
exact (in_sh_disjoint (slot_beg RE c i) (class_size c) (ae_fs_base RE) A_FS_MAP_SIZE x P3 ltac:(Z.div_mod_to_equations; (first [ clear - H9 q1 H0 H r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - R2 R1 P3 P2 P1 i c FP' FK FAL KO PA AK PK TA TP X RE BAND; lia | lia ])) Hx F).
+ pose proof (sec_band e x He Hx). destruct F; cbn [fst snd] in *. lia.
+ pose proof (qsec_facts e He) as (E1 & E2 & E3 & E4 & _ & _ & D3). lit.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
exact (in_sh_disjoint (se_beg e + kPage) (se_size e - kPage) (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(rewrite KP; Z.div_mod_to_equations; (first [ clear - H4 q0 H0 H r q E1 r0 e PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(Z.div_mod_to_equations; (first [ clear - H9 q1 H0 H r q FAL r1 PA AK PK TA TP X RE BAND; lia | lia ])) ltac:(lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; (first [ clear - D E2 E1 e FK FAL KP PA AK PK TA TP X RE BAND; lia | lia ])) Hx F).
Qed.

Lemma fp_lt_ceil : forall x,
(fp_RTconst RE X x \/ fp_RStats RE X x \/ fp_RPrim G RE X x \/ fp_RChunks a LB0 G RE X x \/ fp_RSec a RE X x
\/ fp_RDepot RE X x \/ fp_RFake FS0 RE X x) -> x < band_lo.
Proof.
intros x F. destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso].
assert (CZ : czone LB0 RE x) by (left; exact GE).
destruct F as [F|[F|[F|[F|[F|[F|F]]]]]].
- exact (fp_RTconst_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RStats_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RPrim_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RChunks_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RSec_cz a LB0 FS0 G RE X GC x F CZ).
- exact (fp_RDepot_cz a LB0 FS0 G RE X GC x F CZ).
- pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
destruct (fp_RFake_zone RE X FS0 x F) as [[H1 H2]|H]; cbn [fst snd] in *; [lia|].
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; lia) FC H). unfold kLowEnd, KHI in *. lia.
Qed.
End Excl.

Section Bundle.
Context {BAND : Band}.
Variable C : arun_components.

Definition QOTH (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RTconst RE X m /\ RStats RE X m /\ RPrim a G RE X m /\ RChunks a LB0 G RE X m
/\ ac_RSec C a LB0 RE X m /\ ac_RDepot C RE X m /\ ac_RFake C FS0 RE X m.

Definition QRUN (rb bt bg : Z) (pend : list (aptr * Z))
(a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
gcons a LB0 FS0 G RE X /\ QOTH a LB0 FS0 G RE X m /\ RQuarM rb bt bg pend a LB0 G RE X m.

Definition qzone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ band_lo <= x.

Lemma QOTH_frame : forall a LB0 FS0 G RE X m m',
gcons a LB0 FS0 G RE X -> QOTH a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => ~ qzone a LB0 G RE X x) m m' -> QOTH a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' GC (R1 & R2 & R3 & R4 & R5 & R6 & R7) WM AG.
assert (AGX : forall P : Z -> Prop, (forall x, P x -> fp_RQuar a LB0 G RE X x -> False) -> (forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2. eapply agree_on_mono; [exact AG|]. intros x Px [Q|Q]; [exact (H1 x Px Q)| pose proof (H2 x Px); lia]. }
split; [eapply RTconst_frame; [exact R1| exact WM| apply AGX; [intros x P Q; exact (fpQ_RTconst _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ _ _ _ _ GC); tauto]]|].
split; [eapply RStats_frame; [exact R2| exact WM| apply AGX; [intros x P Q; exact (fpQ_RStats _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ _ _ _ _ GC); tauto]]|].
split; [eapply RPrim_frame; [exact R3| exact WM| apply AGX; [intros x P Q; exact (fpQ_RPrim _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ _ _ _ _ GC); tauto]]|].
split; [eapply RChunks_frame; [exact R4| exact WM| apply AGX; [intros x P Q; exact (fpQ_RChunks _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ FS0 _ _ _ GC); tauto]]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| apply AGX; [intros x P Q; exact (fpQ_RSec _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil _ _ FS0 G _ _ GC); tauto]]|].
split; [eapply (ac_RDepot_frame C); [exact R6| exact WM| apply AGX; [intros x P Q; exact (fpQ_RDepot _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto]]|].
eapply (ac_RFake_frame C); [exact R7| exact WM| apply AGX; [intros x P Q; exact (fpQ_RFake _ _ _ _ _ _ GC x Q P)| intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto]].
Qed.

Definition QREST (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RChunks a LB0 G RE X m /\ ac_RSec C a LB0 RE X m /\ ac_RDepot C RE X m /\ ac_RFake C FS0 RE X m.

Lemma QOTH_split : forall a LB0 FS0 G RE X m,
QOTH a LB0 FS0 G RE X m <-> RTconst RE X m /\ RStats RE X m /\ RPrim a G RE X m /\ QREST a LB0 FS0 G RE X m.
Proof. intros. unfold QOTH, QREST. tauto. Qed.

Definition pzone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ band_lo <= x.

Lemma QREST_frame : forall a LB0 FS0 G RE X m m',
gcons a LB0 FS0 G RE X -> QREST a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => ~ pzone a LB0 G RE X x) m m' -> QREST a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' GC (R4 & R5 & R6 & R7) WM AG.
assert (AGX : forall P : Z -> Prop,
(forall x, P x -> fp_RQuar a LB0 G RE X x -> False) -> (forall x, P x -> fp_RPrim G RE X x -> False) ->
(forall x, P x -> fp_RStats RE X x -> False) -> (forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2 H3 H4. eapply agree_on_mono; [exact AG|]. intros x Px [Q|[Q|[Q|Q]]]; [exact (H1 x Px Q)| exact (H2 x Px Q)| exact (H3 x Px Q)| pose proof (H4 x Px); lia]. }
split; [| split; [| split]].
- eapply RChunks_frame; [exact R4| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 _ _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 _ _ _ GC); tauto.
- eapply (ac_RSec_frame C); [exact R5| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 G _ _ GC); tauto.
- eapply (ac_RDepot_frame C); [exact R6| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RDepot _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RDepot _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto.
- eapply (ac_RFake_frame C); [exact R7| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto.
Qed.

Lemma QREST_munch : forall a LB0 FS0 G RE X m m' W,
gcons a LB0 FS0 G RE X -> QREST a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> pzone a LB0 G RE X x) ->
QREST a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC Q MU WM HW. eapply QREST_frame; [exact GC| exact Q| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx. exact (NZ (HW lo hi x Hin Hx)).
Qed.

Lemma QREST_ext : forall a a' LB0 FS0 G G' RE X m,
QREST a LB0 FS0 G RE X m -> as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
same_tags is_live G G' -> QREST a' LB0 FS0 G' RE X m.
Proof.
intros a a' LB0 FS0 G G' RE X m (R4 & R5 & R6 & R7) ER EN ES SLV.
split; [eapply RChunks_ext; [exact R4| intros e He; rewrite ER; exact He| exact SLV]|].
split; [eapply (ac_RSec_ext C); [exact R5| exact ER| exact EN| exact ES]|].
split; [exact R6| exact R7].
Qed.

Lemma QOTH_munch : forall a LB0 FS0 G RE X m m' W,
gcons a LB0 FS0 G RE X -> QOTH a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> qzone a LB0 G RE X x) ->
QOTH a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W GC Q MU WM HW. eapply QOTH_frame; [exact GC| exact Q| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx. exact (NZ (HW lo hi x Hin Hx)).
Qed.

Lemma QOTH_ext : forall a a' LB0 FS0 G G' RE X m,
QOTH a LB0 FS0 G RE X m ->
(forall c, cls a' c = cls a c) -> as_cache_inited a' = as_cache_inited a ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
same_len G G' -> same_tags tag_prim G G' -> same_tags is_live G G' ->
QOTH a' LB0 FS0 G' RE X m.
Proof.
intros a a' LB0 FS0 G G' RE X m (R1 & R2 & R3 & R4 & R5 & R6 & R7) EC EI ER EN ES SL SP SLV.
split; [exact R1|]. split; [exact R2|].
split; [eapply RPrim_ext; [exact R3| exact EC| exact EI| exact SL| exact SP]|].
split; [eapply RChunks_ext; [exact R4| intros e He; rewrite ER; exact He| exact SLV]|].
split; [eapply (ac_RSec_ext C); [exact R5| exact ER| exact EN| exact ES]|].
split; [exact R6| exact R7].
Qed.

Section Concrete.
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.

Lemma QRUN_of_ARUNX : forall a LB0 FS0 G RE X m, ARUNX C a LB0 FS0 G RE X m -> QRUN 0 QB QB [] a LB0 FS0 G RE X m.
Proof.
intros a LB0 FS0 G RE X m (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRQ in R6.
split; [exact GC|]. split; [| exact R6]. repeat (split; [assumption|]). exact R8.
Qed.

Lemma ARUNX_of_QRUN : forall a LB0 FS0 G RE X m, QRUN 0 QB QB [] a LB0 FS0 G RE X m -> ARUNX C a LB0 FS0 G RE X m.
Proof.
intros a LB0 FS0 G RE X m (GC & (R1 & R2 & R3 & R4 & R5 & R7 & R8) & R6).
split; [exact GC|]. rewrite HRT, HRS, HRP, HRC, HRQ. repeat (split; [assumption|]). exact R8.
Qed.

Lemma QRUN_of_ARUN : forall s LB FS RE m, ARUN C s LB FS RE m ->
exists X G LB0 FS0, Permutation LB LB0 /\ Permutation FS FS0 /\ QRUN 0 QB QB [] (ps_a s) LB0 FS0 G RE X m.
Proof.
intros s LB FS RE m AR. destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
exists X, G, LB0, FS0. split; [exact PB|]. split; [exact PF|]. apply QRUN_of_ARUNX. exact AX.
Qed.

Lemma ARUN_of_QRUN : forall s LB FS RE m X G LB0 FS0,
Permutation LB LB0 -> Permutation FS FS0 -> QRUN 0 QB QB [] (ps_a s) LB0 FS0 G RE X m -> ARUN C s LB FS RE m.
Proof. intros s LB FS RE m X G LB0 FS0 PB PF Q. eapply ARUN_close; [exact PB| exact PF| apply ARUNX_of_QRUN; exact Q]. Qed.
End Concrete.

Lemma qzone_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RQuar a LB0 G RE X x \/ (band_lo <= x < SP) -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
assert (QC : fp_RQuar a LB0 G RE X x -> czone LB0 RE x -> False) by (intros Q CZ; exact (fp_RQuar_cz a LB0 FS0 G RE X GC x Q CZ)).
assert (QL : fp_RQuar a LB0 G RE X x -> x < band_lo).
{ intros Q. destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply (QC Q); left; exact GE]. }
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
-  destruct Z as [Q|Q]; [pose proof (QL Q); lia| lia].
-  cbn [ala_client_data a_alayout] in C1. destruct Z as [Q|Q]; [apply (QC Q); right; left; exact C1|].
unfold a_client_data in C1. idtac. lia.
-  assert (LU : in_live_user LB0 x) by (destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R]).
destruct Z as [Q|Q]; [apply (QC Q); do 2 right; left; exact LU|].
pose proof (live_user_heap a LB0 FS0 G RE X GC x LU). lia.
-  assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
destruct Z as [Q|Q]; [apply (QC Q); do 3 right; left; split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia| lia].
-  assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
pose proof (frame_shadow_where a LB0 FS0 G RE X GC x SHD) as FS'.
destruct Z as [Q|Q]; [apply (QC Q); do 4 right; left; exact FS'|].
pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) ltac:(unfold A_FS_MAP_SIZE in *; lia) FC FS'). unfold kLowEnd, KHI in *. lia.
-  destruct Z as [Q|Q]; [apply (QC Q); do 5 right; left; rewrite SH_247 in C1; exact C1|].
rewrite SH_247, ?KHI_eq in *. lia.
-  cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (933888 / 8) with 116736 in C1. change (65536 / 8) with 8192 in C1.
destruct Z as [Q|Q]; [| idtac; lia].
destruct (fp_RQuar_loc a LB0 G RE X x Q) as [H|H|c i t Ht Hq H|c i t Ht Hq H|e He NL H|e He NL H].
+ pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK. rewrite ?KHI_eq in TK. lia.
+ pose proof (quar_img_ok x H) as (_ & _ & _ & _ & _ & LT).
destruct H as (iv & Hin & [I1 I2]). cbn in Hin. unfold A_INSTANCE in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in I1, I2; lia.
+ pose proof (slot_prim a LB0 FS0 G RE X GC c i t Ht) as (P1 & _). pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & _).
destruct H as [H1 _]; cbn [fst] in H1. rewrite ?KHI_eq in PK. lia.
+ pose proof (slot_band a LB0 FS0 G RE X GC c i t x Ht H). lia.
+ pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (_ & E2 & _). rewrite ?KHI_eq in E2. pose proof kconsts as (_ & _ & _ & _ & KP & _). lia.
+
pose proof (sec_facts a LB0 FS0 G RE X GC e He) as (E1 & [_ E2] & E3 & E4 & E5 & E6 & _). pose proof kconsts as (_ & _ & _ & _ & KP & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1.
apply in_sh_bounds in H; [| rewrite KP; clear - E1; Z.div_mod_to_equations; lia| rewrite KP; lia].
rewrite !SH_eq in H. rewrite KP in H. clear - H C1 E1 E2 M1. destruct E2 as [E2|E2]; Z.div_mod_to_equations; lia.
Qed.

Lemma pzone_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RPrim G RE X x \/ fp_RStats RE X x -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK.
assert (QC : czone LB0 RE x -> False).
{ intros CZ. destruct Z as [Q|Q]; [exact (fp_RPrim_cz a LB0 FS0 G RE X GC x Q CZ)| exact (fp_RStats_cz a LB0 FS0 G RE X GC x Q CZ)]. }
assert (QL : x < band_lo).
{ destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply QC; left; exact GE]. }
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
- lia.
- apply QC. right; left. exact C1.
- apply QC. do 2 right; left. destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
apply QC. do 3 right; left; split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
apply QC. do 4 right; left. exact (frame_shadow_where a LB0 FS0 G RE X GC x SHD).
- apply QC. do 5 right; left. rewrite SH_247 in C1. exact C1.
- cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (933888 / 8) with 116736 in C1. change (65536 / 8) with 8192 in C1.
rewrite ?KHI_eq in TK. pose proof kconsts as (_ & _ & _ & K32 & _).
pose proof (rl_prim a LB0 FS0 G RE X GC) as (_ & PK & _). rewrite ?KHI_eq in PK.
destruct Z as [Q|Q].
+ destruct (fp_RPrim_loc G RE X x Q) as [H|H|c Hc H|c Hc H|c Hc H NS|c Hc H NS].
* unfold region_info, prim_lo in *. lia.
* lia.
* pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof kconsts as (_ & KO & _). unfold prim_lo in *. lia.
* pose proof (fas_band a LB0 FS0 G RE X GC c x Hc H). lia.
* pose proof (region_in_prim RE c Hc) as (Q1 & Q2 & Q3 & Q4). unfold prim_lo in *. lia.
* pose proof (reg_band a LB0 FS0 G RE X GC c x Hc H). lia.
+ unfold fp_RStats, in_iv, A_ERRNO in Q. cbn [fst snd] in Q. lia.
Qed.

Definition wzone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (SP x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ (band_lo <= x < SP).

Lemma wzone_pzone : forall a LB0 G RE X SP x, wzone a LB0 G RE X SP x -> pzone a LB0 G RE X x.
Proof. intros a LB0 G RE X SP x [H|[H|[H|H]]]; unfold pzone; [tauto| tauto| tauto| lia]. Qed.

Lemma aheap_presA_of_munch_w : forall a LB0 FS0 G RE X LB FS SP m m' W,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> wzone a LB0 G RE X SP x) ->
aheap_presA asegs a_alayout LB FS SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FS SP m m' W GC PB PF CSP MU WM HW. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|Z]]].
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
Qed.

Lemma aheap_presA_of_munch : forall a LB0 FS0 G RE X LB FS SP m m' W,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> fp_RQuar a LB0 G RE X x \/ (band_lo <= x < SP)) ->
aheap_presA asegs a_alayout LB FS SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FS SP m m' W GC PB PF CSP MU WM HW. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. apply outside_intro. intros lo hi Hin Hx.
exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (HW lo hi x Hin Hx)).
Qed.
End Bundle.

Section Depot.
Context {BAND : Band}.
Variable C : arun_components.

Definition azone (a : AState) (LB0 : list ablock) (G : ghost) (RE : aentry) (X : rlay) (SP x : Z) : Prop :=
fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ (band_lo <= x < SP).

Lemma depot_client : forall a LB0 FS0 G RE X LB FS SP x,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
aclient_addrA a_alayout LB FS SP x -> fp_RDepot RE X x -> False.
Proof.
intros a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Q.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (fs_obj RE X)) as (FAL & FK & FC & _). cbn [fst snd] in FAL, FK, FC.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (T_obj RE X)) as (_ & TK & _). cbn [fst snd] in TK.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (dn_obj RE X)) as (_ & NK & _). cbn [fst] in NK.
pose proof (rl_objs_lia a LB0 FS0 G RE X GC _ (ssb_obj RE X)) as (_ & BK & _). cbn [fst] in BK.
assert (QC : czone LB0 RE x -> False) by (intros CZ; exact (fp_RDepot_cz a LB0 FS0 G RE X GC x Q CZ)).
assert (QL : x < band_lo).
{ destruct (Z.lt_ge_cases x band_lo) as [L|GE]; [exact L| exfalso; apply QC; left; exact GE]. }
destruct CA as [C1|[C1|[C1|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1|C1]]]]]].
- lia.
- apply QC. right; left. exact C1.
- apply QC. do 2 right; left. destruct C1 as (b & Hb & R); exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| exact R].
- assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5).
apply QC. do 3 right; left; split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| split; assumption]).
apply QC. do 4 right; left. exact (frame_shadow_where a LB0 FS0 G RE X GC x SHD).
- apply QC. do 5 right; left. rewrite SH_247 in C1. exact C1.
- cbn [ala_img_lo a_alayout] in C1. rewrite !SH_eq in C1. change (933888 / 8) with 116736 in C1. change (65536 / 8) with 8192 in C1.
rewrite ?KHI_eq in TK, NK, BK. destruct Q as [H|[H|[H|H]]]; [destruct H; cbn [fst snd] in *; lia| destruct H; cbn [fst snd] in *; lia| destruct H; cbn [fst snd] in *; lia| lia].
Qed.

Lemma aheap_presA_of_munch_a : forall a LB0 FS0 G RE X LB FS SP m m' W,
gcons a LB0 FS0 G RE X -> Permutation LB LB0 -> Permutation FS FS0 -> band_lo <= SP ->
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> azone a LB0 G RE X SP x) ->
aheap_presA asegs a_alayout LB FS SP m m'.
Proof.
intros a LB0 FS0 G RE X LB FS SP m m' W GC PB PF CSP MU WM HW. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|[Z|Z]]]].
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_introl Z)).
- exact (pzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
- exact (depot_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA Z).
- exact (qzone_client a LB0 FS0 G RE X LB FS SP x GC PB PF CSP CA (or_intror Z)).
Qed.

Definition QR3 (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RChunks a LB0 G RE X m /\ ac_RSec C a LB0 RE X m /\ ac_RFake C FS0 RE X m.

Lemma QREST_split : forall a LB0 FS0 G RE X m,
QREST C a LB0 FS0 G RE X m <-> QR3 a LB0 FS0 G RE X m /\ ac_RDepot C RE X m.
Proof. intros. unfold QREST, QR3. tauto. Qed.

Lemma QR3_frame : forall a LB0 FS0 G RE X m m',
gcons a LB0 FS0 G RE X -> QR3 a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fun x => ~ (fp_RQuar a LB0 G RE X x \/ fp_RPrim G RE X x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ band_lo <= x)) m m' ->
QR3 a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' GC (R4 & R5 & R7) WM AG.
assert (AGX : forall P : Z -> Prop,
(forall x, P x -> fp_RQuar a LB0 G RE X x -> False) -> (forall x, P x -> fp_RPrim G RE X x -> False) ->
(forall x, P x -> fp_RStats RE X x -> False) -> (forall x, P x -> fp_RDepot RE X x -> False) ->
(forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2 H3 H4 H5. eapply agree_on_mono; [exact AG|]. intros x Px [Q|[Q|[Q|[Q|Q]]]];
[exact (H1 x Px Q)| exact (H2 x Px Q)| exact (H3 x Px Q)| exact (H4 x Px Q)| pose proof (H5 x Px); lia]. }
split; [| split].
- eapply RChunks_frame; [exact R4| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RChunks _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 _ _ _ GC x Q); tauto.
+ intros x P Q; apply (fpD_excl _ _ FS0 _ _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 _ _ _ GC); tauto.
- eapply (ac_RSec_frame C); [exact R5| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RSec _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl _ _ FS0 G _ _ GC x Q); tauto.
+ intros x P Q; apply (fpD_excl _ _ FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil _ _ FS0 G _ _ GC); tauto.
- eapply (ac_RFake_frame C); [exact R7| exact WM| apply AGX].
+ intros x P Q; exact (fpQ_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; exact (fpP_RFake _ _ _ _ _ _ GC x Q P).
+ intros x P Q; apply (fpS_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P Q; apply (fpD_excl a LB0 FS0 G _ _ GC x Q); tauto.
+ intros x P; apply (fp_lt_ceil a LB0 FS0 G _ _ GC); tauto.
Qed.

Lemma QR3_munch : forall a LB0 FS0 G RE X m m' W SP,
gcons a LB0 FS0 G RE X -> QR3 a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> azone a LB0 G RE X SP x) ->
QR3 a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W SP GC Q MU WM HW. eapply QR3_frame; [exact GC| exact Q| exact WM|].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x NZ _. apply outside_intro. intros lo hi Hin Hx.
apply NZ. destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto| do 4 right; lia].
Qed.

Lemma QR3_ext : forall a a' LB0 FS0 G G' RE X m,
QR3 a LB0 FS0 G RE X m -> as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
same_tags is_live G G' -> QR3 a' LB0 FS0 G' RE X m.
Proof.
intros a a' LB0 FS0 G G' RE X m (R4 & R5 & R7) ER EN ES SLV.
split; [eapply RChunks_ext; [exact R4| intros e He; rewrite ER; exact He| exact SLV]|].
split; [eapply (ac_RSec_ext C); [exact R5| exact ER| exact EN| exact ES]| exact R7].
Qed.

End Depot.
End Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QUvT.Mq0 QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QsJM QpY2 QpY2.Mqe QpME.Mqa.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc1_entry : Z := 0x4ab30.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma land_8191 : forall x, Z.land x 8191 = x mod 8192.
Proof. intros x. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod8192_of_64 : forall x, (x mod 2^64) mod 8192 = x mod 8192.
Proof. intros x. apply Z.mod_mod_divide. exists (2^51); reflexivity. Qed.

Lemma fs1_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 20480) fl -> fl = flags_of FS0 FS 1 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 1) FS0)) < fs_N 1 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (8192 - i) -> 0 <= i < 8192 ->
bv_unsigned cur mod 8192 = (u + i) mod 8192 ->
(forall j, 0 <= j < i -> live_b FS0 1 (fs_frame FS 1 ((u + j) mod 8192)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 (wz FS) (wz (8192 - i')) (wz (FS + 4096)) cur' (wz (FS + 20480)) (wz 8191)
(wz (FS + 20480 + pos)) a6 (wz pos) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4ac3c) fc None mc (seg_rom asegs)
/\ 0 <= pos < 8192 /\ live_b FS0 1 (fs_frame FS 1 pos) = false /\ 0 <= i' < 8192)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (8192 - i)) (wz (FS + 4096)) cur (wz (FS + 20480)) (wz 8191) a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4abc4) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 8191).
assert (Hpos : pos = (u + i) mod 8192) by (subst pos; rewrite land_8191; exact Hcur).
assert (PR : 0 <= pos < 8192) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 1 (fs_frame FS 1 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 20480) fl pos (b8 1) (wa (FS + 20480 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 8192) as [LT|GE].
+ if_true_u. replace (8192 - i + -1) with (8192 - (i + 1)) by lia.
eapply (IH (Z.to_nat (8192 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod8192_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 1 -> live_b FS0 1 (fs_frame FS 1 p) = true).
{ apply (scan_exhausts FS0 FS 1 u (i + 1)); try change (fs_N 1) with 8192; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 1 ltac:(lia) ALL) as CNT. change (fs_N 1) with 8192 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 20480) fl pos (b8 0) (wa (FS + 20480 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 8191), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc1_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 1) FS0)) < fs_N 1 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 1 pos /\ 0 <= pos < fs_N 1 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 1 f
/\ RTconst RE X m' /\ RFake ((1, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 1 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0); C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 8, FS + 8 + 8); (fs_flag FS 1 pos, fs_flag FS 1 pos + 1);
(f, f + ff_size 1); (SH f, SH f + ff_size 1 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc1_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc1_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 1 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. change (8 * 1) with 8 in HINT.
pose proof (FL 1 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 1) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 8192) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 1 0) with (FS + 20480) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x55798.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4abc4.

eapply evt_cut.
{ eapply (fs1_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 8, FS + 8 + 8); (FS + 20480 + pos, FS + 20480 + pos + 1);
(FS + 1085440 + pos * 128, FS + 1085440 + pos * 128 + 128); (SH (FS + 1085440 + pos * 128), SH (FS + 1085440 + pos * 128) + 16)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 4 istep. rewrite (unsigned_lit pos), Z.shiftl_mul_pow2 by lia. change (2 ^ 7) with 128.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 20480) fl pos (wa (FS + 20480 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 20480) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 5 istep.
replace (FS + 36864 + (1048576 + pos * 128)) with (FS + 1085440 + pos * 128) by lia.
remember (FS + 1085440 + pos * 128) as f eqn:Ef in *.
assert (FB : FS + 1085440 <= f /\ f + 128 <= FS + 1085440 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 128) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 128 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 128) = SH f + 16) by (rewrite !SH_eq; replace (f + 128) with (f + 16 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 128) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 16) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).
pose proof (fun Hm => hjunk_split _ (SH f) (SH f + 8) _ J2f Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2a J2b].
destruct (hjunk_cells _ (SH f) 8 J2a) as [junks SHC].
replace (SH f + Z.of_nat 16) with (SH f + 8 + Z.of_nat 8) in J2b by (cbn; lia).
destruct (hjunk_cells _ (SH f + 8) 8 J2b) as [junks2 SHC2]. clear J2c J2r J2f J2a J2b.
istep. istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 88 (take 88 (drop 32 junkf))] [C8 (wz (FS + 20480 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 120 (take 24 junkf ++ le8 sp ++ take 88 (drop 32 junkf))] [C8 (wz (FS + 20480 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 1 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 1 pos = FS + 20480 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 1 0 = FS + 20480) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 1 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 1) with 8192; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 1) with 128 in NT. change (128 / 8) with 16 in NT. change (8 * 1) with 8 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. change (8 * 1) with 8. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 1 - 8) with (f + 120) by (change (ff_size 1) with 128; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 88 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 1) with 8192; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 1) with 128. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split.
{ apply (proj2 (rw_cells_app asegs _ (SH f) [C8 (wz 0)] [C8 (wz 0)])). split; [exact SHC| exact SHC2]. }
rewrite FLG. change (ff_size 1) with 128. change (128 / 8) with 16.
eapply munch_weaken; [| exact MU2]. intros y Hy. cbn [outside fst snd] in Hy |- *. lia.
Qed.
End Walk.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QUvT.Mq0 QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QsJM QpY2 QpY2.Mqe QpME.Mqa.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc2_entry : Z := 0x4acc0.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod4096_of_64 : forall x, (x mod 2^64) mod 4096 = x mod 4096.
Proof. intros x. apply Z.mod_mod_divide. exists (2^52); reflexivity. Qed.

Lemma fs2_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 28672) fl -> fl = flags_of FS0 FS 2 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 2) FS0)) < fs_N 2 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (4096 - i) -> 0 <= i < 4096 ->
bv_unsigned cur mod 4096 = (u + i) mod 4096 ->
(forall j, 0 <= j < i -> live_b FS0 2 (fs_frame FS 2 ((u + j) mod 4096)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp (wz 0) t1 t2 s0 (wz FS) (wz (4096 - i')) (wz (FS + 4096)) cur' (wz (FS + 28672)) (wz 4095)
(wz (FS + 28672 + pos)) a6 (wz pos) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4adcc) fc None mc (seg_rom asegs)
/\ 0 <= pos < 4096 /\ live_b FS0 2 (fs_frame FS 2 pos) = false /\ 0 <= i' < 4096)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (4096 - i)) (wz (FS + 4096)) cur (wz (FS + 28672)) (wz 4095) a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4ad54) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 4095).
assert (Hpos : pos = (u + i) mod 4096) by (subst pos; rewrite land_4095; exact Hcur).
assert (PR : 0 <= pos < 4096) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 2 (fs_frame FS 2 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 28672) fl pos (b8 1) (wa (FS + 28672 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 4096) as [LT|GE].
+ if_true_u. replace (4096 - i + -1) with (4096 - (i + 1)) by lia.
eapply (IH (Z.to_nat (4096 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod4096_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 2 -> live_b FS0 2 (fs_frame FS 2 p) = true).
{ apply (scan_exhausts FS0 FS 2 u (i + 1)); try change (fs_N 2) with 4096; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 2 ltac:(lia) ALL) as CNT. change (fs_N 2) with 4096 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 28672) fl pos (b8 0) (wa (FS + 28672 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 4095), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc2_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 2) FS0)) < fs_N 2 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 2 pos /\ 0 <= pos < fs_N 2 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 2 f
/\ RTconst RE X m' /\ RFake ((2, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 2 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 16, FS + 16 + 8); (fs_flag FS 2 pos, fs_flag FS 2 pos + 1);
(f, f + ff_size 2); (SH f, SH f + ff_size 2 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc2_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc2_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 2 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. change (8 * 2) with 16 in HINT.
pose proof (FL 2 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 2) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 4096) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 2 0) with (FS + 28672) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x55798.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4ad54.

eapply evt_cut.
{ eapply (fs2_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS + 16, FS + 16 + 8); (FS + 28672 + pos, FS + 28672 + pos + 1);
(FS + 2134016 + pos * 256, FS + 2134016 + pos * 256 + 256); (SH (FS + 2134016 + pos * 256), SH (FS + 2134016 + pos * 256) + 32)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 3 istep.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 28672) fl pos (wa (FS + 28672 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 28672) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 7 istep. rewrite ?(unsigned_lit pos), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
replace (FS + 36864 + (2097152 + pos * 256)) with (FS + 2134016 + pos * 256) by lia.
remember (FS + 2134016 + pos * 256) as f eqn:Ef in *.
assert (FB : FS + 2134016 <= f /\ f + 256 <= FS + 2134016 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 256) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 256 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 256) = SH f + 32) by (rewrite !SH_eq; replace (f + 256) with (f + 32 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 256) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 32) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).
pose proof (fun Hm => hjunk_split _ (SH f) (SH f + 8) _ J2f Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2a J2b].
pose proof (fun Hm => hjunk_split _ (SH f + 8) (SH f + 16) _ J2b Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2b1 J2c'].
pose proof (fun Hm => hjunk_split _ (SH f + 16) (SH f + 24) _ J2c' Hm) as J2s. specialize (J2s ltac:(cbn; lia)). destruct J2s as [J2c1 J2d].
destruct (hjunk_cells _ (SH f) 8 J2a) as [junks SHC].
replace (SH f + 16) with (SH f + 8 + Z.of_nat 8) in J2b1 by (cbn; lia).
destruct (hjunk_cells _ (SH f + 8) 8 J2b1) as [junks2 SHC2].
replace (SH f + 24) with (SH f + 16 + Z.of_nat 8) in J2c1 by (cbn; lia).
destruct (hjunk_cells _ (SH f + 16) 8 J2c1) as [junks3 SHC3].
replace (SH f + Z.of_nat 32) with (SH f + 24 + Z.of_nat 8) in J2d by (cbn; lia).
destruct (hjunk_cells _ (SH f + 24) 8 J2d) as [junks4 SHC4]. clear J2c J2r J2f J2a J2b J2b1 J2c' J2c1 J2d.
istep. istep. istep. istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 216 (take 216 (drop 32 junkf))] [C8 (wz (FS + 28672 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 248 (take 24 junkf ++ le8 sp ++ take 216 (drop 32 junkf))] [C8 (wz (FS + 28672 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 2 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 2 pos = FS + 28672 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 2 0 = FS + 28672) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 2 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 2) with 4096; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 2) with 256 in NT. change (256 / 8) with 32 in NT. change (8 * 2) with 16 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. change (8 * 2) with 16. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 2 - 8) with (f + 248) by (change (ff_size 2) with 256; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 216 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 2) with 4096; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 2) with 256. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split.
{ apply (proj2 (rw_cells_app asegs _ (SH f) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0); C8 (wz 0)])). split; [exact SHC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
apply (proj2 (rw_cells_app asegs _ (SH f + 8) [C8 (wz 0)] [C8 (wz 0); C8 (wz 0)])). split; [exact SHC2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 8 + 8) with (SH f + 16) by lia.
apply (proj2 (rw_cells_app asegs _ (SH f + 16) [C8 (wz 0)] [C8 (wz 0)])). split; [exact SHC3|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
replace (SH f + 16 + 8) with (SH f + 24) by lia. exact SHC4. }
rewrite FLG. change (ff_size 2) with 256. change (256 / 8) with 32.
eapply munch_weaken; [| exact MU2]. intros y Hy. cbn [outside fst snd] in Hy |- *. lia.
Qed.
End Walk.
End Mqe.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition memchr_stub : Z := 0x4fd4c.
Definition memchr_icpt_entry : Z := 0x525f8.
Definition MEMCHR_ICPT_STACK : Z := 2224.

Definition memchr_len (c n : Z) (buf : list byte) : Z :=
match find_byte c (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i + 1 | None => n end.

Definition memchr_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A c n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (memchr_res A c n buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ bytes_at asegs m' A buf.

Lemma find_byte_lt : forall c l i, find_byte c l = Some i -> (i < length l)%nat.
Proof.
intros c l. induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
destruct (bv_unsigned b =? c); [inversion H; cbn; lia|].
destruct (find_byte c l) as [j|]; [| discriminate]. inversion H; subst. specialize (IH j eq_refl). cbn. lia.
Qed.

Lemma memchr_len_bound : forall c n buf, 0 <= n -> 0 <= memchr_len c n buf <= n /\ (memchr_len c n buf <= Z.of_nat (length buf) \/ memchr_len c n buf = n).
Proof.
intros c n buf Hn. unfold memchr_len. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [| lia].
apply find_byte_lt in E. rewrite length_firstn in E. lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c n lo : Z) (buf : list byte) (cw : word).
Let L := memchr_len c n buf.
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - MEMCHR_ICPT_STACK.
Hypothesis A0 : 0 < A.
Hypothesis N0 : 0 <= n < 2^64.
Hypothesis CW : bv_unsigned cw mod 256 = c.
Hypothesis OK : memchr_ok A c n buf.
Hypothesis BSTK : A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A.
Hypothesis RNG : rng_ok m A L.
Let usp := bv_unsigned sp.
Let POST := memchr_icpt_post ra sp gp tp.

Lemma memchr_icpt_tail : forall mf (res rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v s3v s4v s5v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
res = wz (memchr_res A c n buf) ->
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2128) -> stk asegs mf (usp + -2128) (usp + -56) ->
rw_cells asegs mf (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
(MS (mkR rav (wz (usp + -2128)) gp tp t0 t1 t2 sp s1v res a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x526b4) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros -> MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
set (BAh := bytes_at) in BUF.
do 8 istep.
pose proof (stk_merge asegs _ _ _ _ ST1 ST2 ltac:(lia)) as ST. clear ST1 ST2.
release_frame FR ST (bv_unsigned sp).
step. step.
apply evt_done. unfold POST, memchr_icpt_post. do 15 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact BUF.
Qed.

Lemma memchr_icpt_check : forall mf (len : Z) (res rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
len = L -> res = wz (memchr_res A c n buf) ->
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2128) -> stk asegs mf (usp + -2128) (usp + -56) ->
rw_cells asegs mf (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
(MS (mkR rav (wz (usp + -2128)) gp tp t0 t1 t2 sp (wz len) res a1 a2 a3 a4 a5 a6 a7 (wz A) s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x5266c) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros -> ER MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (memchr_len_bound c n buf ltac:(lia)) as [LB _]. fold L in LB.
pose proof RNG as (RA0 & RA47 & SOK & BIG & NB).
assert (RNG' : rng_ok mf A L).
{ eapply rng_ok_munch; [exact RNG| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. cbn. rewrite !SH_eq, ?KHI_eq in *. left. Z.div_mod_to_equations. lia. }
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SB2.
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RC2.

step. step. step.
destruct (Z.eq_dec L 0) as [Lz|Lz].
{
if_cases K1; zify_cond K1; rewrite ?Lz, ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Lz; cbn in K1; lia].
step. rewrite Lz. ifz. step.
eapply memchr_icpt_tail; [exact ER| exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF]. }
destruct (Z_le_gt_dec L 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct RNG' as (_ & _ & SOK' & _ & NB'). destruct (NB' ltac:(lia)) as [[w1 W1] [w2 W2]]. pose proof (SOK' ltac:(lia)) as SO2.
destruct SB2 as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. step. step. step. stp. stp.
rewrite (unsigned_lit A), (unsigned_lit (A + L + -1)) by lia.
replace (2147450880 + A ≫ 3) with (SH A) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (A + L + -1) ≫ 3) with (SH (A + L - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH A /\ SH A <= SH (A + L - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH A)), (unsigned_lit (SH (A + L - 1))) by lia. rewrite !land_m8 by lia.
replace (SH A - SH A mod 8) with (8 * (SH A / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (A + L - 1) - SH (A + L - 1) mod 8) with (8 * (SH (A + L - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ A L SO2 ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ A L SO2 ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1'' a3'' a4'' a5'' : word,
ms1 = MS (@bvmap_set 5 word 11 a1'' (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 14 a4'' (@bvmap_set 5 word 15 a5'' R)))) FF (wz 0x526b4) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (A + L + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (A + L - 1)) (SH A)) as [X1|X1].
+ ifz. replace (SH A) with (SH (A + L - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_a1 0x527c4 ltac:(right; left; reflexivity) (Z.to_nat (SH (A + L - 1) - SH A)) (SH A)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4x. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1'' & a3'' & a4'' & a5'' & ->). simp_regs.
eapply memchr_icpt_tail; [exact ER| exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF].
-
destruct RNG' as (_ & _ & SOK' & BIG' & _). destruct (BIG' ltac:(lia)) as [KA L43]. pose proof (SOK' ltac:(lia)) as SO2.
ifz. step. ifz. step. step. step.
pose proof (rt_mem_cells_of _ SB2 RC2) as RTM.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia| exact SO2| lia| lia| lia| exact KA|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST5 end.
step. step. step. ifz.
eapply memchr_icpt_tail; [first [exact ER| reflexivity]| exact MU| exact WM| assumption| exact ST5| eassumption| eassumption| eassumption].
Qed.

Lemma memchr_icpt_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
stk asegs m lo usp -> bytes_at asegs m A buf -> mem_inv asegs m ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) cw (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memchr_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros ST BUF MI.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
pose proof (memchr_len_bound c n buf ltac:(lia)) as [LB LB2]. fold L in LB, LB2.
pose proof RNG as (RA0 & RA47 & _ & _ & _).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
set (BAh := bytes_at) in BUF.
unfold memchr_stub. step.
carve_frame 56%nat ST.
do 8 istep.
step. step. step. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2128) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (rt_159b60 _ RCc) as K14. pose proof (rt_161720 _ RCc) as K18. clear RCc.

step. call0 asaninited_spec7; [exact K18|]. subst_words. step. ifz.

step. call_u tryinit_spec7; [exact K18| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => rename H into ST1' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
step. stp. step. step. step. step. clear K14 K18.
assert (BUF1 : bytes_at asegs m1 A buf).
{ eapply bytes_at_transport; [exact BUF| exact MUs|]. cbn. lia. }
clear BUF.

step. call_u (memchr_spec _ _ _ _ _ _ _ _ _ (wz A) cw (wz n));
[rewrite unsigned_lit by lia; exact BUF1| rewrite !unsigned_lit, CW by lia; exact OK| assumption|].
rewrite ?(unsigned_lit A), ?(unsigned_lit n), ?CW in * by lia.
match goal with H : stk asegs ?mc' (bv_unsigned sp + -2128) _, H2 : rw_cells asegs ?mc' (bv_unsigned sp + -56) _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
rename H into ST2'; rename H2 into FR' end.
match goal with H : bytes_at asegs ?mc' A buf |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into BUF2 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.

step. ifz. step.
unfold memchr_res.
destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
-
pose proof (find_byte_lt _ _ _ FB) as IL. rewrite length_firstn in IL.
assert (EL : L = Z.of_nat i + 1) by (subst L; unfold memchr_len; rewrite FB; reflexivity).
unfold_cond. rewrite (unsigned_lit (A + Z.of_nat i)) by lia. if_lit.
stp. rewrite (unsigned_lit A) by lia.
stp. step. step. step.
replace (A + Z.of_nat i + - A + 1) with L by lia.
step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply memchr_icpt_check; [reflexivity| unfold memchr_res; rewrite FB; reflexivity| exact MUs| exact WM| assumption| exact ST1'| exact ST2'| exact FR'| exact BUF2].
-
assert (EL : L = n) by (subst L; unfold memchr_len; rewrite FB; reflexivity).
ifz. step. step. step. step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply memchr_icpt_check; [symmetry; exact EL| unfold memchr_res; rewrite FB; reflexivity| exact MUs| exact WM| assumption| exact ST1'| exact ST2'| exact FR'| exact BUF2].
Qed.
End S.

Theorem memchr_icpt_spec {BAND : Band} :
forall (A n lo : Z) (buf : list byte) (cw : word),
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
bytes_at asegs m A buf -> memchr_ok A (bv_unsigned cw mod 256) n buf -> mem_inv asegs m ->
0 < A -> 0 <= n < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MEMCHR_ICPT_STACK ->
A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m A (memchr_len (bv_unsigned cw mod 256) n buf) ->
evt asegs (memchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (bv_unsigned cw mod 256) n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) cw (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memchr_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros BUF OK MI A0 N0 ST CEIL LO BSTK SB RC RNG.
eapply memchr_icpt_main; try eassumption. reflexivity.
Qed.
