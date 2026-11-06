(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh QQwg QKTr QJBH QvG1 QDw3 QUxU QNwL QYnC QmP7 Q9Ho QYyZ QnRU QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QDw3 QUxU QNwL QYnC QmP7.Mq0 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0.
Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma gcons_alloc_prim {BAND : Band} : forall a LB FS G RE X c i n,
gcons a LB FS G RE X -> tag_at G c i = Some TCached -> c = class_of n -> 0 <= n <= 2^26 -> from_primary n = true ->
gcons (set_next (N.succ (as_next a)) a) ((APrim (as_next a) n, slot_beg RE c i + rz_size n, n) :: LB) FS
(set_tag c i (TLive (APrim (as_next a) n)) G) RE X.
Proof.
intros a LB FS G RE X c i n GC Ht Ec Hn HP. pose proof GC as GC0. gc_split GC.
set (p := APrim (as_next a) n).
pose proof (retag_at G c i TCached (TLive p) Ht) as RT.
pose proof (tag_at_Some_lt _ _ _ _ Ht) as [I0 _].

assert (FRESH : forall c' i' t, tag_at G c' i' = Some t -> holds p t = false).
{ intros c' i' t Ht' . destruct (holds p t) eqn:E; [| reflexivity]. exfalso.
pose proof (A8b c' i' t (as_next a) n Ht' E). lia. }
assert (NOTIN : ~ In p (map ablk_id LB)).
{ intros Hin. apply in_map_iff in Hin. destruct Hin as ([[q A'] n'] & Eq & Hin). cbn in Eq. subst q.
destruct (A2 p A' n' Hin) as [[(id' & i1 & E & _ & _ & Ht1 & _)|(mb & E & _)] _]; [| discriminate].
pose proof (FRESH _ _ _ Ht1) as F. unfold holds in F. rewrite aptr_eqb_refl' in F. discriminate. }
split; [exact A1|]. split.
{ intros q Aq nq Hq. destruct Hq as [Hq|Hq].
- inversion Hq. subst q Aq nq. split; [| lia]. left. exists (as_next a), i. split; [reflexivity|]. split; [lia|]. split; [exact HP|].
split; [rewrite <- Ec, RT, !Z.eqb_refl; reflexivity|]. split; [exact I0|]. rewrite <- Ec. reflexivity.
- destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| right; exact H1| exact H2].
left. destruct H1 as (id' & i' & E & Hn' & HP' & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [| split; [exact Hi'| exact HA]]. rewrite RT.
destruct (Z.eqb_spec (class_of nq) c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb]; try exact Ht'.
exfalso. rewrite EC, EI, Ht in Ht'. discriminate. }
split. { cbn [map ablk_id fst]. constructor; [exact NOTIN| exact A3]. }
split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct (Z.eqb_spec c' c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb] in Hq.
- inversion Hq. subst q. exists (as_next a), n, (slot_beg RE c i + rz_size n). split; [reflexivity|]. split; [left; reflexivity| subst c'; symmetry; exact Ec].
- destruct (A4 _ _ _ Hq) as (id' & n' & A' & E & Hin & Hc'). exists id', n', A'. split; [exact E|]. split; [right; exact Hin| exact Hc'].
- destruct (A4 _ _ _ Hq) as (id' & n' & A' & E & Hin & Hc'). exists id', n', A'. split; [exact E|]. split; [right; exact Hin| exact Hc']. }
split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? c) && (i' =? i)) eqn:E; [inversion Hq| exact (A5 _ _ _ Hq)]. }
split.
{ intros c' NE. rewrite ncarved_set_tag. cbn [cls set_next as_cls]. apply A6. intros E. apply NE.
destruct (Z.eq_dec c' c) as [->|NC]; [rewrite set_tag_class, E; reflexivity| rewrite set_tag_other_class by exact NC; exact E]. }
split; [exact A7|]. split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2. rewrite RT in H1, H2.
destruct (aptr_eqb q p) eqn:EQ.
- apply aptr_eqb_true in EQ. subst q.
destruct ((c1 =? c) && (i1 =? i)) eqn:E1.
+ destruct ((c2 =? c) && (i2 =? i)) eqn:E2.
* apply andb_prop in E1 as [E1a E1b]. apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E1a. apply Z.eqb_eq in E1b. apply Z.eqb_eq in E2a. apply Z.eqb_eq in E2b. lia.
* exfalso. rewrite (FRESH _ _ _ H2) in K2. discriminate.
+ exfalso. rewrite (FRESH _ _ _ H1) in K1. discriminate.
- assert (NP1 : forall u, Some u = Some (TLive p) -> holds q u = true -> False).
{ intros u E K. inversion E. subst u. unfold holds in K. rewrite K in EQ. discriminate. }
destruct ((c1 =? c) && (i1 =? i)) eqn:E1; [exfalso; exact (NP1 _ (eq_sym H1) K1)|].
destruct ((c2 =? c) && (i2 =? i)) eqn:E2; [exfalso; exact (NP1 _ (eq_sym H2) K2)|].
exact (A8 _ _ _ _ q _ _ H1 H2 K1 K2). }
split.
{ intros c1 i1 t id1 n1 H1 K1. cbn [as_next set_next]. rewrite RT in H1.
destruct ((c1 =? c) && (i1 =? i)) eqn:E.
- inversion H1. subst t. unfold holds in K1. apply aptr_eqb_true in K1. inversion K1. lia.
- pose proof (A8b _ _ _ _ _ H1 K1). lia. }
cbn [as_reg set_next]. repeat (split; [assumption|]). exact A13.
Qed.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QCiC QCNF QoNr Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u.
Import QCiC.Mq1. Import QCNF.Mq1 QoNr.
Import Qu3b.Mq3.
Import QnRU.Mq3 QnRU.Mq4.

Import QvG1. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Open Scope bv_scope.

Import ListNotations.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac zstep0 := zs.

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
intros f Hf. rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed.

Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia. reflexivity. Qed.

Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.

Ltac mlia := Z.div_mod_to_equations; lia.

Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
split. { apply Z.lor_nonneg. lia. }
pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
rewrite Z.shiftl_mul_pow2 in * by lia.
replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
pose proof (bytes_le_to_Z_range bs) as HR.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec0 i 8).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
u8arr segs m A bs -> length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
intros segs m A bs k [Hb Hw] HL.
assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
{ clear. induction k as [|k IH]; intros bs HL.
- exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
- destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
- rewrite Hu. exact Hb.
- rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).

Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
intros ws i v Hi Hl. unfold wval, wnth.
pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.

Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
intros ws i j v Hi Hj Hij. unfold wval, wnth.
destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
- pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
- rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.

Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. lia. Qed.

Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
change (2^9)%Z with 512%Z.
set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody y. clear x Hx.
Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
split; intros H; Z.div_mod_to_equations; lia.
Qed.

Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
(0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
apply Z.div_lt_upper_bound; [lia|].
assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed.

End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 QHig QwAs Q0Do Qc6I QJFf QvDJ QyW2 Qp4j QsGW QSsj Qu1d QNQk QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf.
Import Q6sh QKTr QvDJ.Mq3.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq2 QYyZ.Mq1 QnRU.Mq5.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition strnlen_stub : Z := 0x4f954.
Definition strnlen_icpt_entry : Z := 0x4fca0.
Definition STRNLEN_ICPT_STACK : Z := 2144 + STRNLEN_STACK.

Lemma strnlen_res_bound : forall n buf, 0 <= n -> 0 <= strnlen_res n buf <= n
/\ memchr_len 0 n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
intros n buf Hn. unfold strnlen_res, memchr_len. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [| lia].
apply find_byte_lt in E. rewrite length_firstn in E. lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n lo : Z) (buf : list byte).
Let L := memchr_len 0 n buf.
Let R := strnlen_res n buf.
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - STRNLEN_ICPT_STACK.
Hypothesis A0 : 0 < A.
Hypothesis N0 : 0 <= n < 2^64.
Hypothesis OK : memchr_ok A 0 n buf.
Hypothesis BSTK : A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A.
Hypothesis RNG : rng_ok m A L.
Let usp := bv_unsigned sp.
Let POST := strnlen_post ra sp gp tp.

Lemma strnlen_icpt_tail : forall mf (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v s3v s4v s5v s6v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2144) -> stk asegs mf (usp + -2144) (usp + -64) ->
rw_cells asegs mf (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR rav (wz (usp + -2144)) gp tp t0 t1 t2 sp s1v (wz R) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4fd64) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
set (BAh := bytes_at) in BUF.
do 9 istep.
pose proof (stk_merge asegs _ _ _ _ ST1 ST2 ltac:(lia)) as ST. clear ST1 ST2.
release_frame FR ST (bv_unsigned sp).
step. step.
apply evt_done. unfold POST, strnlen_post. do 15 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact BUF.
Qed.

Lemma strnlen_icpt_check : forall mf (len : Z) (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v s6v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
len = L ->
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2144) -> stk asegs mf (usp + -2144) (usp + -64) ->
rw_cells asegs mf (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR rav (wz (usp + -2144)) gp tp t0 t1 t2 sp (wz len) (wz R) a1 a2 a3 a4 a5 a6 a7 (wz A) s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4fd1c) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros -> MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (memchr_len_bound 0 n buf ltac:(lia)) as [LB _]. fold L in LB.
pose proof RNG as (RA0 & RA47 & SOK & BIG & NB).
assert (RNG' : rng_ok mf A L).
{ eapply rng_ok_munch; [exact RNG| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. cbn. rewrite !SH_eq, ?KHI_eq in *. left. Z.div_mod_to_equations. lia. }
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SB2.
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RC2.

step. step. step.
destruct (Z.eq_dec L 0) as [Lz|Lz].
{ if_cases K1; zify_cond K1; rewrite ?Lz, ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Lz; cbn in K1; lia].
step. rewrite Lz. ifz. step.
eapply strnlen_icpt_tail; [exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF]. }
destruct (Z_le_gt_dec L 64) as [N64|N65].
- unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
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
ms1 = MS (@bvmap_set 5 word 11 a1'' (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 14 a4'' (@bvmap_set 5 word 15 a5'' R)))) FF (wz 0x4fd64) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (A + L + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (A + L - 1)) (SH A)) as [X1|X1].
+ ifz. replace (SH A) with (SH (A + L - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_a1 0x4fe38 ltac:(right; right; left; reflexivity) (Z.to_nat (SH (A + L - 1) - SH A)) (SH A)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4x. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1'' & a3'' & a4'' & a5'' & ->). simp_regs.
eapply strnlen_icpt_tail; [exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF].
- destruct RNG' as (_ & _ & SOK' & BIG' & _). destruct (BIG' ltac:(lia)) as [KA L43]. pose proof (SOK' ltac:(lia)) as SO2.
ifz. step. ifz. step. step. step.
pose proof (rt_mem_cells_of _ SB2 RC2) as RTM.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia| exact SO2| lia| lia| lia| exact KA|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST5 end.
step. step. step. ifz.
eapply strnlen_icpt_tail; [exact MU| exact WM| assumption| exact ST5| eassumption| eassumption| eassumption].
Qed.

Lemma strnlen_icpt_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
stk asegs m lo usp -> bytes_at asegs m A buf -> mem_inv asegs m ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strnlen_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros ST BUF MI.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
pose proof (strnlen_res_bound n buf ltac:(lia)) as [RB LR]. fold R L in RB, LR. fold R in LR.
pose proof (memchr_len_bound 0 n buf ltac:(lia)) as [LB _]. fold L in LB.
pose proof RNG as (RA0 & RA47 & _ & _ & _).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold strnlen_stub. step.
carve_frame 64%nat ST.
do 9 istep.
step. step. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof RCc as RCc'. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_15a5a8 _ RCc) as K11. pose proof (rt_161720 _ RCc) as K18. pose proof (rt_1f2663 _ RCc) as K23. clear RCc.

step. call_u tryinit_spec7; [exact K18| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs _ lo (bv_unsigned sp + -2144) |- _ => rename H into ST1' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
step. stp. step. step. step. clear K11 K18.
first [ assert (BUF1 : bytes_at asegs mA A buf) by exact BUF
| assert (BUF1 : bytes_at asegs mA A buf) by (eapply bytes_at_transport; [exact BUF| exact MUs|]; cbn; lia) ].
clear BUF.
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1.
clear RCc'. pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1.
assert (RNG1 : rng_ok mA A L).
{ eapply rng_ok_munch; [exact RNG| exact MUs| exact WM|]. apply Forall_cons; [| apply Forall_nil]. cbn. rewrite !SH_eq, ?KHI_eq in *. left. Z.div_mod_to_equations. lia. }

step. call_u (strnlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mA A n buf lo);
[ unsigned_lits; exact ST1'| exact BUF1| exact OK| assumption| exact CEIL| unsigned_lits; unfold STRNLEN_STACK, MEMCHR_ICPT_STACK; lia
| unsigned_lits; lia| lia| lia| exact SB1| exact RC1| exact RNG1|].
match goal with H : stk asegs ?mc' lo (bv_unsigned sp + -2144), H2 : rw_cells asegs ?mc' (bv_unsigned sp + -64) _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
rename H into ST1x; rename H2 into FR' end.
match goal with H : stk asegs ?mc' (bv_unsigned sp + -2144) _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST2' end.
match goal with H : bytes_at asegs ?mc' A buf |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into BUF2 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mB end.
fold R.

step. ifz. step. stp. stp. clear K7 K23. step. ifz.

stp. step.
destruct (Z_lt_le_dec (R + 1) n) as [X1|X1].
-
ifz. step. step. step. step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply strnlen_icpt_check; [lia| exact MUs| exact WM| assumption| exact ST1x| exact ST2'| exact FR'| exact BUF2].
-
ifz. step. step. step. step. step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply strnlen_icpt_check; [lia| exact MUs| exact WM| assumption| exact ST1x| exact ST2'| exact FR'| exact BUF2].
Qed.
End S.

Theorem strnlen_icpt_spec {BAND : Band} :
forall (A n lo : Z) (buf : list byte),
forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
stk asegs m lo (bv_unsigned sp) -> bytes_at asegs m A buf -> memchr_ok A 0 n buf -> mem_inv asegs m ->
band_lo <= lo -> lo <= bv_unsigned sp - STRNLEN_ICPT_STACK ->
A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A ->
0 < A -> 0 <= n < 2^64 ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m A (memchr_len 0 n buf) ->
evt asegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strnlen_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros ST BUF OK MI CEIL LO SEP A0 N0 SB RC RNG.
eapply strnlen_icpt_main; eassumption.
Qed.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Q0Do.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QYyZ.Mq5 QqLk QkfD.
Import QnRU.Mq9.
Import QlES. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Z.
Context {BAND : Band}.
Variables (a a1 : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Variables (mb msz n : Z).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Hypothesis GC1 : gcons a1 LB0 FS0 G RE X.
Hypothesis ER : as_reg a1 = as_reg a ++ [mkSec mb msz n].
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis MSZ : 4096 <= msz.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Hypothesis AVQ : mb + msz <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= mb.
Hypothesis AVR : forall e, In e (as_reg a) -> mb + msz <= se_beg e \/ se_beg e + se_size e <= mb.
Set Default Proof Using "GC GC1 ER MBP MBK MBC MSZ AVO AVP AVQ AVR".

Definition nbody (x : Z) : Prop := mb + 4096 <= x < mb + msz \/ in_sh (mb + 4096, msz - 4096) x.

Lemma nbody_nmap : forall x, nbody x -> nmap mb msz x.
Proof.
intros x [H|H]; [left; lia| right].
exact (in_sh_sub mb msz (mb + 4096) (msz - 4096) x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) H).
Qed.

Lemma nbody_RSec1 : forall x, nbody x -> fp_RSec a1 RE X x -> False.
Proof.
intros x NB F. pose proof (nbody_nmap x NB) as NM. pose proof kconsts as (_ & _ & _ & _ & KP & _).
destruct F as [H|[H|[H|H]]].
- exact (nmap_RSec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x NM ltac:(left; exact H)).
- exact (nmap_RSec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x NM ltac:(right; left; exact H)).
- destruct H as (e & He & Hx). rewrite ER in He. apply in_app_iff in He. destruct He as [He|[<-|[]]].
+ pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _). pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1.
exact (nmap_sec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR e x He ltac:(left; lia) NM).
+ cbn [se_beg] in Hx. destruct NB as [B|B]; [lia|].
pose proof (@in_sh_band BAND (mb + 4096) (msz - 4096) x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(clear - MBK MSZ; lia) ltac:(lia) B) as SB.
unfold kLowEnd, KHI in SB. rewrite KP in Hx. clear - MBK MSZ Hx SB. lia.
- destruct H as (e & He & Hx). rewrite ER in He. apply in_app_iff in He. destruct He as [He|[<-|[]]].
+ exact (nmap_sec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR e x He ltac:(right; left; exact Hx) NM).
+ cbn [se_beg] in Hx. destruct NB as [B|B].
* pose proof (@in_sh_band BAND mb kPage x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(rewrite KP; lia) ltac:(rewrite KP; clear - MBK MSZ; lia) ltac:(rewrite KP; lia) Hx) as SB.
unfold kLowEnd, KHI in SB. clear - MBK MSZ B SB. lia.
* exact (in_sh_disjoint mb kPage (mb + 4096) (msz - 4096) x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(clear - MBP; Z.div_mod_to_equations; lia)
ltac:(rewrite KP; lia) ltac:(lia) ltac:(rewrite KP; lia) Hx B).
Qed.

Definition szone (x : Z) : Prop := nbody x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ band_lo <= x.

Lemma szone_frame : forall m m' W,
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> szone x) ->
((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RStats RE X x) -> RStats RE X m -> RStats RE X m')
/\ ((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RDepot RE X x) -> RDepot RE X m -> RDepot RE X m')
/\ (RSec a1 LB0 RE X m -> RSec a1 LB0 RE X m').
Proof.
intros m m' W MU WM HW.
assert (AG : forall P : Z -> Prop, (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> P x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx. exact (HP lo hi x Hin Hx Px). }
split; [| split].
- intros NS RS. eapply RStats_frame; [exact RS| exact WM| apply AG]. intros lo hi x Hin Hx Px. exact (NS lo hi x Hin Hx Px).
- intros ND RD. eapply RDepot_frame; [exact RD| exact WM| apply AG]. intros lo hi x Hin Hx Px. exact (ND lo hi x Hin Hx Px).
- intros RSE. eapply RSec_frame; [exact RSE| exact WM| apply AG]. intros lo hi x Hin Hx Px.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|Z]]].
+ exact (nbody_RSec1 x Z Px).
+ exact (fpS_excl _ _ _ _ _ _ GC1 x Z ltac:(right; left; exact Px)).
+ exact (fpD_excl _ _ _ _ _ _ GC1 x Z ltac:(right; left; exact Px)).
+ pose proof (fp_lt_ceil _ _ _ _ _ _ GC1 x ltac:(do 4 right; left; exact Px)). lia.
Qed.

Lemma RSec_hdr_last : forall LB m, RSec a1 LB RE X m ->
rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 (sec_size n)); C8 (Z_to_bv 64 (Z.of_nat (length (as_reg a))))].
Proof.
intros LB m RS. destruct RS as (_ & _ & _ & _ & _ & _ & H7 & _).
specialize (H7 (length (as_reg a)) (mkSec mb msz n)). rewrite ER in H7. rewrite nth_error_app2, Nat.sub_diag in H7 by lia.
destruct (H7 eq_refl) as (H & _ & _). cbn [se_beg se_size se_req] in H. exact H.
Qed.

Lemma nbody_RStats : forall x, nbody x -> fp_RStats RE X x -> False.
Proof. intros x NB F. exact (nmap_RStats a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x (nbody_nmap x NB) F). Qed.
Lemma nbody_RDepot : forall x, nbody x -> fp_RDepot RE X x -> False.
Proof. intros x NB F. exact (nmap_RDepot a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x (nbody_nmap x NB) F). Qed.
End Z.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6 Qpj5 Q67d QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QnRU.Mq7 QOJv.Mq5 Qu3b.Mq2 QTVW.Mq0.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac lia_ar := lazymatch goal with
| |- @eq Z _ _ => lia | |- @eq nat _ _ => lia | |- Z.le _ _ => lia | |- Z.lt _ _ => lia | |- Z.ge _ _ => lia | |- Z.gt _ _ => lia
| |- le _ _ => lia | |- lt _ _ => lia | |- ge _ _ => lia | |- gt _ _ => lia | |- ~ _ => lia | |- _ \/ _ => lia | |- False => lia | |- _ -> _ => lia
end.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation TT := (fun (_ : evA) (_ : ansA) => True).

Definition prel (c : Z) (a a' : AState) : Prop :=
(forall c', c' <> c -> cls a' c' = cls a c') /\ as_cache_inited a' = as_cache_inited a
/\ as_reg a' = as_reg a /\ as_next a' = as_next a /\ c_count (cls a' c) = c_count (cls a c).

Lemma prel_refl : forall c a, prel c a a.
Proof. intros. repeat split; reflexivity. Qed.
Lemma prel_trans : forall c a1 a2 a3, prel c a1 a2 -> prel c a2 a3 -> prel c a1 a3.
Proof. intros c a1 a2 a3 (A & B & C & D & E) (A' & B' & C' & D' & E'). repeat split; try congruence. intros c' H. rewrite A' by exact H. apply A. exact H. Qed.
Lemma prel_set_cls : forall c a x, c_count x = c_count (cls a c) -> prel c a (set_cls c x a).
Proof. intros c a x E. repeat split; try reflexivity. { intros c' H. apply cls_set_cls_ne. exact H. } rewrite cls_set_cls_eq. exact E. Qed.

Section Model.
Variable L : ALay.
Ltac tret_ok := apply tall_ret; cbn.

Lemma ensure_fa_prel a c nf : tall TT (okrel (fun r => prel c a (snd r))) (ensure_fa L a c nf).
Proof.
unfold ensure_fa. destruct (_ <=? _); [tret_ok; apply prel_refl|]. destruct (_ <? _); [exact I|].
apply tall_vis. intros x _. destruct (fixed_ok x); tret_ok; [apply prel_set_cls; reflexivity| apply prel_refl].
Qed.

Lemma populate_prel a c req : tall TT (okrel (fun r => prel c a (snd r))) (populate L a c req).
Proof.
unfold populate. eapply tall_bind_ok with (P1 := fun r => prel c a (snd r)).
{ destruct (_ <? _); [| tret_ok; apply prel_refl]. destruct (_ <? _); [exact I|].
apply tall_vis. intros x _. destruct (fixed_ok x); tret_ok; [apply prel_set_cls; reflexivity| apply prel_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
eapply tall_bind_ok with (P1 := fun r => prel c a (snd r)).
{ eapply tall_mono; [apply ensure_fa_prel|]. intros [[b s2]| |w]; cbn; [| exact (fun x => x)| exact (fun x => x)]. intros H2. eapply prel_trans; eauto. }
intros [ok2 s2] H2. cbn in H2. destruct ok2; cbn [negb]; tret_ok; [| exact H2]. eapply prel_trans; [exact H2| apply prel_set_cls; reflexivity].
Qed.

Lemma get_from_allocator_prel a c k : tall TT (okrel (fun r => prel c a (snd r))) (get_from_allocator L a c k).
Proof.
unfold get_from_allocator. eapply tall_bind_ok with (P1 := fun r => prel c a (snd r)).
{ destruct (_ <? _); [apply populate_prel| tret_ok; apply prel_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
destruct (_ <? _); [exact I|]. tret_ok. eapply prel_trans; [exact H1| apply prel_set_cls; reflexivity].
Qed.
End Model.

Fixpoint retag_list (c : Z) (l : list Z) (t : stag) (G : ghost) : ghost :=
match l with [] => G | i :: l' => set_tag c i t (retag_list c l' t G) end.

Lemma retag_list_other_class : forall c l t G c', c' <> c -> retag_list c l t G c' = G c'.
Proof. intros c l t G c' NE. induction l as [|i l IH]; cbn; [reflexivity|]. rewrite set_tag_other_class by exact NE. exact IH. Qed.

Lemma ncarved_retag_list : forall c l t G c', ncarved (retag_list c l t G) c' = ncarved G c'.
Proof. intros c l t G c'. induction l as [|i l IH]; cbn; [reflexivity|]. rewrite ncarved_set_tag. exact IH. Qed.

Lemma tag_at_retag_list_out : forall c l t G c' i', (c' <> c \/ ~ In i' l) -> Forall (fun i => 0 <= i) l ->
tag_at (retag_list c l t G) c' i' = tag_at G c' i'.
Proof.
intros c l t G c' i' H NN. induction l as [|i l IH]; cbn; [reflexivity|]. inversion NN; subst.
rewrite tag_at_set_tag_ne; [apply IH; [| assumption]| assumption|].
- destruct H as [H|H]; [left; exact H| right; intros K; apply H; right; exact K].
- destruct H as [H|H]; [left; exact H| right; intros ->; apply H; left; reflexivity].
Qed.

Lemma tag_at_retag_list_in : forall c l t G i, In i l -> Forall (fun i => 0 <= i) l ->
(forall j, In j l -> exists t0, tag_at G c j = Some t0) ->
tag_at (retag_list c l t G) c i = Some t.
Proof.
intros c l t G i Hin NN OLD. induction l as [|i0 l IH]; [destruct Hin|]. cbn. inversion NN; subst.
assert (OLD' : forall j, In j l -> exists t0, tag_at G c j = Some t0) by (intros j Hj; apply OLD; right; exact Hj).
destruct (Z.eq_dec i i0) as [->|NE].
-
assert (E : exists t0, tag_at (retag_list c l t G) c i0 = Some t0).
{ destruct (in_dec Z.eq_dec i0 l) as [Hl|Hl].
- exists t. apply IH; assumption.
- rewrite tag_at_retag_list_out; [apply OLD; left; reflexivity| right; exact Hl| assumption]. }
destruct E as [t0 Ht0]. exact (tag_at_set_tag_eq _ c i0 t t0 Ht0).
- destruct Hin as [->|Hin]; [congruence|]. rewrite tag_at_set_tag_ne; [apply IH; assumption| assumption| right; exact NE].
Qed.

Lemma same_tags_retag_list : forall f c l t G,
f t = false -> Forall (fun i => 0 <= i) l -> (forall j, In j l -> exists t0, tag_at G c j = Some t0 /\ f t0 = false) ->
same_tags f G (retag_list c l t G).
Proof.
intros f c l t G Hf NN OLD c' i' u Hu. destruct (Z.eq_dec c' c) as [->|NE].
- destruct (in_dec Z.eq_dec i' l) as [Hin|Hout].
+ rewrite (tag_at_retag_list_in c l t G i' Hin NN ltac:(intros j Hj; destruct (OLD j Hj) as [t0 [H _]]; exists t0; exact H)).
destruct (OLD i' Hin) as [t0 [H0 F0]]. rewrite H0. split; intros E; inversion E; subst; congruence.
+ rewrite tag_at_retag_list_out; [tauto| right; exact Hout| exact NN].
- rewrite tag_at_retag_list_out; [tauto| left; exact NE| exact NN].
Qed.

Lemma gcons_retag_list {BAND : Band} : forall a LB FS G RE X c l t,
gcons a LB FS G RE X -> Forall (fun i => 0 <= i) l ->
(forall j, In j l -> exists t0, tag_at G c j = Some t0 /\ is_live t0 = false) ->
(forall q, holds q t = false) -> is_live t = false ->
gcons a LB FS (retag_list c l t G) RE X.
Proof.
intros a LB FS G RE X c l t GC NN OLD NH NL. induction l as [|i l IH]; cbn; [exact GC|]. inversion NN; subst.
assert (OLD' : forall j, In j l -> exists t0, tag_at G c j = Some t0 /\ is_live t0 = false) by (intros j Hj; apply OLD; right; exact Hj).
specialize (IH ltac:(assumption) OLD').
assert (E : exists t0, tag_at (retag_list c l t G) c i = Some t0 /\ is_live t0 = false).
{ destruct (in_dec Z.eq_dec i l) as [Hl|Hl].
- exists t. split; [| exact NL]. apply tag_at_retag_list_in; [exact Hl| assumption| intros j Hj; destruct (OLD' j Hj) as [t0 [H _]]; exists t0; exact H].
- rewrite tag_at_retag_list_out; [apply OLD; left; reflexivity| right; exact Hl| assumption]. }
destruct E as [t0 [Ht0 NL0]]. eapply gcons_retag_nonlive; [exact IH| exact Ht0| exact NL0| exact NH| exact NL].
Qed.

Lemma gstep_retag_cached {BAND : Band} : forall RE X a G c l,
Forall (fun i => 0 <= i) l -> (forall j, In j l -> tag_at G c j = Some TFree) ->
gstep RE X a a G (retag_list c l TCached G).
Proof.
intros RE X a G c l NN OLD. split; [| split; [| split]].
- apply same_tags_retag_list; [reflexivity| exact NN| intros j Hj; exists TFree; split; [apply OLD; exact Hj| reflexivity]].
- apply same_tags_retag_list; [reflexivity| exact NN| intros j Hj; exists TFree; split; [apply OLD; exact Hj| reflexivity]].
- intros c' i' t Ht. destruct (Z.eq_dec c' c) as [->|NE]; [destruct (in_dec Z.eq_dec i' l) as [Hin|Hout]|].
+ exists TCached. apply tag_at_retag_list_in; [exact Hin| exact NN| intros j Hj; exists TFree; apply OLD; exact Hj].
+ exists t. rewrite tag_at_retag_list_out; [exact Ht| right; exact Hout| exact NN].
+ exists t. rewrite tag_at_retag_list_out; [exact Ht| left; exact NE| exact NN].
- intros LB FS GC. apply gcons_retag_list; [exact GC| exact NN| intros j Hj; exists TFree; split; [apply OLD; exact Hj| reflexivity]| intros q; reflexivity| reflexivity].
Qed.

Lemma gstep_ext {BAND : Band} : forall RE X a a' G,
(forall c, c_alloc_user (cls a' c) = c_alloc_user (cls a c)) -> (forall c, c_mapped_user (cls a' c) = c_mapped_user (cls a c)) ->
as_reg a' = as_reg a -> as_next a' = as_next a -> gstep RE X a a' G G.
Proof. intros RE X a a' G EA EM ER EN. apply gstep_state. intros LB FS GC. eapply gcons_ext; [exact GC| exact EA| exact EM| exact ER| rewrite EN; reflexivity]. Qed.

Lemma gstep_populate {BAND : Band} : forall RE X a a' G c K K' k,
1 <= c < kNumClasses -> prel c a a' ->
cr_pure a G c K -> cr_pure a' (gappend c (repeat TFree k) G) c K' ->
gstep RE X a a' G (gappend c (repeat TFree k) G).
Proof.
intros RE X a a' G c K K' k Hc (EO & EI & ER & EN & _) PU PU'.
pose proof kconsts as (_ & _ & _ & K32 & _ & _ & KM & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5).
destruct PU' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & H4 & H5).
rewrite gappend_class, length_app, repeat_length in H1.
assert (NL : Forall (fun t => is_live t = false /\ forall q, holds q t = false) (repeat TFree k)).
{ apply Forall_forall. intros t Ht. apply repeat_spec in Ht. subst t. split; [reflexivity| intros q; reflexivity]. }
split; [| split; [| split]].
- apply same_tags_gappend. apply Forall_forall. intros t Ht. apply repeat_spec in Ht. subst t. reflexivity.
- apply same_tags_gappend. apply Forall_forall. intros t Ht. apply repeat_spec in Ht. subst t. reflexivity.
- intros c' i' t Ht. exists t. apply tag_at_gappend_Some_old. exact Ht.
- intros LB FS GC. eapply gcons_gappend; [exact GC| exact Hc| exact NL| exact EO| unfold ncarved; exact G1| rewrite repeat_length; lia| lia| lia| exact H4| exact H5| exact ER| exact EN].
Qed.

Lemma In_skipn_In {A} : forall n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right; exact H. Qed.
Lemma In_firstn_In {A} : forall n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left; exact H. Qed.
Lemma NoDup_firstn {A} : forall n (l : list A), List.NoDup l -> List.NoDup (firstn n l).
Proof. intros n l H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_r _ _ H). Qed.
Lemma NoDup_skipn {A} : forall n (l : list A), List.NoDup l -> List.NoDup (skipn n l).
Proof. intros n l H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_l _ _ H). Qed.
Lemma NoDup_firstn_skipn {A} : forall n (l : list A) x, List.NoDup l -> In x (firstn n l) -> In x (skipn n l) -> False.
Proof.
intros n l x H H1 H2. rewrite <- (firstn_skipn n l) in H. induction (firstn n l) as [|y f IH]; [destruct H1|].
cbn in H. apply List.NoDup_cons_iff in H as [Hy Hf]. destruct H1 as [->|H1]; [apply Hy; apply in_or_app; right; exact H2| exact (IH Hf H1)].
Qed.

Lemma count_tag_retag_list : forall f c l t t0 G,
List.NoDup l -> Forall (fun i => 0 <= i) l -> (forall j, In j l -> tag_at G c j = Some t0) ->
count_tag f (retag_list c l t G c) = count_tag f (G c) - (if f t0 then Z.of_nat (length l) else 0) + (if f t then Z.of_nat (length l) else 0).
Proof.
intros f c l t t0 G ND NN OLD. induction l as [|i l IH]; cbn -[Z.of_nat]; [destruct (f t), (f t0); lia|].
inversion ND; subst. inversion NN; subst.
assert (OLD' : forall j, In j l -> tag_at G c j = Some t0) by (intros j Hj; apply OLD; right; exact Hj).
specialize (IH ltac:(assumption) ltac:(assumption) OLD').
pose proof (OLD i ltac:(left; reflexivity)) as Ht0.
assert (Hi : tag_at (retag_list c l t G) c i = Some t0) by (rewrite tag_at_retag_list_out; [exact Ht0| right; assumption| assumption]).
rewrite set_tag_class.
rewrite (count_tag_list_set f (retag_list c l t G c) (Z.to_nat i) t t0).
- rewrite IH. destruct (f t), (f t0); cbn [length]; lia.
- unfold tag_at in Hi. destruct (Z.ltb_spec i 0); [discriminate|]. exact Hi.
Qed.

Lemma cr_pure_move : forall a G c K k a',
cr_pure a G c K -> 1 <= c <= 31 -> 0 <= k <= c_num_freed (cls a c) -> k <= max_count c -> c_count (cls a c) = 0 ->
as_cache_inited a' = true ->
cls a' c = set_count k (set_num_freed (c_num_freed (cls a c) - k) (cls a c)) ->
let FL := pk_fl K in let nfk := Z.to_nat (c_num_freed (cls a c) - k) in
cr_pure a' (retag_list c (skipn nfk FL) TCached G) c (mkPK (firstn nfk FL) (skipn nfk FL)).
Proof.
intros a G c K k a' PU Hc Hk Hkm CNT EI Ea FL nfk.
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _).
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
fold FL in P1, P3, P5.
assert (NNF : Forall (fun i => 0 <= i) FL).
{ apply Forall_forall. intros i Hi. exact (proj1 (tag_at_Some_lt _ _ _ _ (P5 i Hi))). }
assert (NN : Forall (fun i => 0 <= i) (skipn nfk FL)).
{ apply Forall_forall. intros i Hi. exact (proj1 (List.Forall_forall _ _) NNF i (In_skipn_In _ _ _ Hi)). }
assert (OLD : forall j, In j (skipn nfk FL) -> tag_at G c j = Some TFree) by (intros j Hj; apply P5; exact (In_skipn_In _ _ _ Hj)).
assert (LF : length (firstn nfk FL) = nfk) by (rewrite length_firstn; lia).
assert (LS : Z.of_nat (length (skipn nfk FL)) = k) by (rewrite length_skipn; lia).
unfold cr_pure. rewrite Ea, EI. cbn [pk_fl pk_ca set_count set_num_freed c_num_freed c_count c_mapped_fa c_alloc_user c_mapped_user].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia_ar.
- apply NoDup_firstn. exact P3.
- apply NoDup_skipn. exact P3.
- intros i Hi. rewrite tag_at_retag_list_out; [apply P5; exact (In_firstn_In _ _ _ Hi)| | exact NN].
right. intros Hi'. exact (NoDup_firstn_skipn _ _ _ P3 Hi Hi').
- intros i Hi. apply tag_at_retag_list_in; [exact Hi| exact NN| intros j Hj; exists TFree; apply OLD; exact Hj].
- rewrite (count_tag_retag_list _ c _ TCached TFree G (NoDup_skipn _ _ P3) NN OLD). cbn. rewrite P7. lia.
- rewrite (count_tag_retag_list _ c _ TCached TFree G (NoDup_skipn _ _ P3) NN OLD). cbn. rewrite P8, CNT. lia.
- pose proof (ncarved_retag_list c (skipn nfk FL) TCached G c) as NC. unfold ncarved in NC. rewrite NC. exact G1.
Qed.

Lemma u32arr_split : forall m A ws1 ws2,
u32arr asegs m A (ws1 ++ ws2) -> u32arr asegs m A ws1 /\ u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
intros m A ws1 ws2 [B W]. rewrite u32s_app in B. apply (proj1 (bytes_at_app _ _ _ _ _)) in B as [B1 B2].
rewrite u32s_length in B2. destruct W as (W0 & W1 & W2). rewrite length_app in W1, W2.
replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) in B2 by lia.
split; split; [exact B1| | exact B2|]; (split; [lia|]; split; [lia|]); intros i Hi.
- apply W2. lia.
- replace (A + 4 * Z.of_nat (length ws1) + i) with (A + (4 * Z.of_nat (length ws1) + i)) by lia. apply W2. lia.
Qed.

Lemma cr_user_retag : forall a a' G G' RE m c,
cr_user a G RE m c ->
(forall i t', tag_at G' c i = Some t' -> tag_prim t' = true -> exists t, tag_at G c i = Some t /\ tag_prim t = true) ->
c_alloc_user (cls a' c) = c_alloc_user (cls a c) -> c_mapped_user (cls a' c) = c_mapped_user (cls a c) ->
cr_user a' G' RE m c.
Proof.
intros a a' G G' RE m c (SL & UT & SS & US & UJ) TG EA EM. unfold cr_user. rewrite EA, EM.
split; [| split; [exact UT| split; [| split; [exact US| exact UJ]]]].
- intros i t' Ht' Hp'. destruct (TG i t' Ht' Hp') as (t & Ht & Hp). exact (SL i t Ht Hp).
- intros i t' Ht' Hp'. destruct (TG i t' Ht' Hp') as (t & Ht & Hp). exact (SS i t Ht Hp).
Qed.

Lemma retag_cached_prim : forall c l G i t', Forall (fun i => 0 <= i) l -> (forall j, In j l -> tag_at G c j = Some TFree) ->
tag_at (retag_list c l TCached G) c i = Some t' -> tag_prim t' = true ->
exists t, tag_at G c i = Some t /\ tag_prim t = true.
Proof.
intros c l G i t' NN OLD Ht' Hp'. destruct (in_dec Z.eq_dec i l) as [Hin|Hout].
- exists TFree. split; [apply OLD; exact Hin| reflexivity].
- exists t'. rewrite tag_at_retag_list_out in Ht'; [| right; exact Hout| exact NN]. split; [exact Ht'| exact Hp'].
Qed.

Lemma gfa_close {BAND : Band} : forall (aX a'' : AState) (GX : ghost) RE X (m m'' : mem) c k (K : Z -> pcls) j1 j2 j3 j4 CH',
let x := cls aX c in let nf := c_num_freed x in let FL := pk_fl (K c) in let nfk := Z.to_nat (nf - k) in
let G' := retag_list c (skipn nfk FL) TCached GX in
let fb := fa_beg (ae_L RE) c in
rlay_ok RE X -> 1 <= c <= 30 -> 1 <= k <= nf -> k <= max_count c -> c_count x = 0 -> as_cache_inited aX = true ->
cls a'' c = set_count k (set_num_freed (nf - k) x) -> (forall c0, c0 <> c -> cls a'' c0 = cls aX c0) -> as_cache_inited a'' = true ->
hjunk m (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, GX c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep aX GX RE X m c0 (K c0)) ->
cr_pure aX GX c (K c) ->
wmono asegs m m'' ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m'') ->
agree_on asegs (uzone RE c) m m'' ->
rw_cells asegs m'' (ri_addr RE c)
[C8 (wz 0); CB 8 j1; C8 (wz (nf - k)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0); C8 (wz (c_mapped_user x));
C8 (wz 0); CB 4 j2; C1 (Z_to_bv 8 0); CB 3 j3; CB 56 j4] ->
rw_cells asegs m'' (pc_addr X c) [C4 (wz k); C4 (wz (bmax c)); C8 (wz (bsize c))] ->
u32arr asegs m'' (pc_addr X c + 16) CH' -> length CH' = 16%nat ->
(forall j, (j < Z.to_nat k)%nat -> nth_error CH' j = nth_error (map (fun i => wz (coff c i)) FL) (nfk + j)%nat) ->
u32arr asegs m'' fb (map (fun i => wz (coff c i)) FL) ->
hjunk m (fb + 4 * nf) (fb + c_mapped_fa x) ->
cr_user aX GX RE m c ->
hjunk m (SH fb) (SH fb + 67108864) ->
RPrim a'' G' RE X m''.
Proof.
intros until CH'; intros x nf FL nfk G' fb RL Hc Hk Hkm CNT EI Ea EO EI'' HJS GNE HCall PU WM OTH AGU RI PC ACH LCH PR FA FJ HU FS.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & _). fold FL in P1, P3, P5.
assert (NNF : Forall (fun i => 0 <= i) FL).
{ apply Forall_forall. intros i Hi. exact (proj1 (tag_at_Some_lt _ _ _ _ (P5 i Hi))). }
assert (NN : Forall (fun i => 0 <= i) (skipn nfk FL)).
{ apply Forall_forall. intros i Hi. exact (proj1 (List.Forall_forall _ _) NNF i (In_skipn_In _ _ _ Hi)). }
assert (OLD : forall j, In j (skipn nfk FL) -> tag_at GX c j = Some TFree) by (intros j Hj; apply P5; exact (In_skipn_In _ _ _ Hj)).
assert (EG : forall c0, c0 <> c -> G' c0 = GX c0) by (intros c0 NE; apply retag_list_other_class; exact NE).
assert (LK : (length FL = nfk + Z.to_nat k)%nat) by (subst nfk nf x; lia).
assert (NFK : Z.of_nat nfk = nf - k) by (subst nfk nf x; lia).
exists (fun c0 => if c0 =? c then mkPK (firstn nfk FL) (skipn nfk FL) else K c0).
split; [eapply hjunk_wmono; [exact HJS| exact WM]|]. split.
{ intros c0 NE0. apply GNE. destruct (Z.eq_dec c0 c) as [->|NE]; [| rewrite <- (EG c0 NE); exact NE0].
intros E. apply NE0. apply length_zero_iff_nil. pose proof (ncarved_retag_list c (skipn nfk FL) TCached GX c) as NC.
unfold ncarved in NC. unfold G'. rewrite <- Nat2Z.inj_iff. rewrite NC, E. reflexivity. }
intros c0 Hc0. destruct (Z.eqb_spec c0 c) as [->|NE].
2:{ eapply class_rep_ext; [| apply EO; exact NE| rewrite EI, EI''; reflexivity| apply EG; exact NE].
eapply class_rep_agree; [apply HCall; [exact Hc0| exact NE]| rewrite K32 in Hc0; exact Hc0| apply OTH; [exact Hc0| exact NE]]. }
apply class_rep_split. split; [| split].
-
unfold cr_cells. rewrite Ea, EI''. cbn [pk_ca set_count set_num_freed c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
split; [exists j1, j2, j3, j4; exact RI|]. split; [exact PC|].
exists CH'. split; [exact ACH|]. split; [exact LCH|].
intros j Hj. rewrite length_skipn in Hj. rewrite PR by lia.
rewrite nth_error_map. rewrite <- (firstn_skipn nfk FL) at 1. rewrite nth_error_app2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (nfk + j - Nat.min nfk (length FL))%nat with j by lia.
destruct (nth_error (skipn nfk FL) j) as [v|] eqn:E; cbn [option_map].
+ rewrite (nth_error_nth _ _ _ E). reflexivity.
+ exfalso. apply nth_error_None in E. rewrite length_skipn in E. lia.
-
apply (cr_pure_move aX GX c (K c) k a''); [exact PU| lia| lia| exact Hkm| exact CNT| exact EI''| exact Ea].
-
intros _. rewrite Ea. cbn [pk_fl set_count set_num_freed c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
assert (SPL := u32arr_split m'' fb (map (fun i => wz (coff c i)) (firstn nfk FL)) (map (fun i => wz (coff c i)) (skipn nfk FL))
ltac:(rewrite <- map_app, firstn_skipn; exact FA)).
destruct SPL as [FA1 FA2]. rewrite length_map, length_firstn in FA2.
split; [exact FA1|]. split.
{ eapply hjunk_merge; [| eapply hjunk_wmono; [exact FJ| exact WM]].
pose proof (u32arr_hjunk m'' _ _ FA2) as J. rewrite length_map, length_skipn in J.
replace (fb + 4 * Z.of_nat (Nat.min nfk (length FL))) with (fb + 4 * (nf - k)) in J by lia.
replace (fb + 4 * (nf - k) + 4 * Z.of_nat (length FL - nfk)) with (fb + 4 * nf) in J by lia.
apply J. pose proof (rlay_prim_facts RE X RL) as (_ & PK1 & _). rewrite ?KHI_eq in PK1. unfold fb, fa_beg, reg_beg. rewrite KR, KO. unfold prim_lo in PK1. nia. }
split; [| rewrite KS; replace 536870912 with (8 * 67108864) by reflexivity; rewrite SH_plus8; eapply hjunk_wmono; [exact FS| exact WM]].
eapply (cr_user_retag aX a'' GX G'); [| intros i t' Ht' Hp'; exact (retag_cached_prim c _ GX i t' NN OLD Ht' Hp')| rewrite Ea; reflexivity| rewrite Ea; reflexivity].
eapply cr_user_agree; [exact PU| exact HU| lia| exact AGU].
Qed.

Lemma ri_stat_recast : forall m A c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 (w : word) j4t,
rw_cells asegs m A [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; C8 w; CB 48 j4t] ->
rw_cells asegs m A [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; CB 56 (le8 w ++ j4t)].
Proof.
intros until j4t; intros H. pose proof H as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
eapply rw_cells_recast'; [exact H| |].
- cbn [cells_wf cell_wf]. rewrite length_app, length_le8. repeat split; try tauto. lia.
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma RPrimL_set_mutex_stk {BAND : Band} : forall a G RE X m m' cl v w lo1 hi1,
RPrimL a G RE X m cl v -> rlay_ok RE X -> band_lo <= lo1 ->
munch [(lo1, hi1); (ri_addr RE cl, ri_addr RE cl + 8)] m m' -> wmono asegs m m' ->
rw_cells asegs m' (ri_addr RE cl) [C8 (Z_to_bv 64 w)] ->
RPrimL a G RE X m' cl w.
Proof.
intros a G RE X m m' cl v w lo1 hi1 RP RL CE MU WM HEAD. pose proof RP as (K & HJ & GNE & HC & Hcl & HCL).
pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hcl.
assert (FWc : Forall (wc_ok RE X cl) [(lo1, hi1); (ri_addr RE cl, ri_addr RE cl + 8)]).
{ constructor; [cbn; left; exact CE|]. constructor; [| constructor]. cbn -[fp_cls]. do 2 right. intros z Hz. left. lia. }
eapply (RPrimL_reclose a a G G RE X m m' cl K (K cl) w RL HJ GNE HC ltac:(rewrite K32; exact Hcl));
[intros; reflexivity| reflexivity| intros; reflexivity| intros NE; exact (proj1 (GNE cl NE))| exact WM
| eapply agree_other_classes; [exact RL| exact Hcl| exact MU| exact WM| exact FWc] |].
eapply class_repL_agree_but_mutex; [exact RL| exact HCL| exact Hcl| | exact HEAD].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x [FX NX] Hx. cbn. split; [| split; [exact NX| exact I]].
pose proof (fp_cls_lt_ceil RE X RL cl x Hcl FX). lia.
Qed.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp QVsB Qsn5 QpME QmvA QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QKTr Q6sh.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QpME.Mq0 QkfD.
Import QQwg.
Import QmP7.Mq0 QYyZ.Mq0 QYyZ.Mq5.
Import QmvA.Mq1.
Import QFd5.Mq3.
Import QlES.
Import ListNotations. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma sec_size_facts : forall n, 0 <= n <= 2^26 -> from_primary n = false ->
65536 < sec_size n /\ sec_size n <= 2^26 + 4104 /\ sec_size n mod 8 = 0
/\ sec_map_size n = sec_size n + 4095 - (sec_size n + 4095) mod 4096 + 4096
/\ sec_map_size n mod 4096 = 0 /\ sec_size n + 4096 <= sec_map_size n < sec_size n + 8192.
Proof.
intros n Hn HP. unfold from_primary in HP. apply Z.leb_gt in HP. unfold sec_size, sec_map_size, needed, kMaxSize in *.
unfold round_up, kPage in *.
assert (R1 : rz_size n <= 2048 /\ (n <= 64512 -> rz_size n <= 1024) /\ (64512 < n -> rz_size n = 2048)).
{ unfold rz_size. repeat match goal with |- context [n <=? ?c] => destruct (Z.leb_spec0 n c) end; lia. }
destruct (Z.le_gt_cases n 64512) as [LE|GT].
{ exfalso. destruct R1 as (_ & R & _). specialize (R LE). Z.div_mod_to_equations. lia. }
destruct R1 as (_ & _ & R). rewrite (R GT) in *. replace (Z.max n 8) with n in * by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma avoids_In : forall b n avoid iv, avoids b n avoid = true -> In iv avoid -> b + n <= fst iv \/ snd iv <= b.
Proof.
intros b n avoid iv H Hin. unfold avoids in H. rewrite forallb_forall in H. specialize (H iv Hin).
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma avoid_facts : forall a b n, avoid_covers RE X -> 0 < n -> (0 < b /\ b + n <= 2^64) -> avoids b n (avoid_of (ae_L RE) a) = true ->
(appr b n /\ b + n <= band_lo) /\ (forall o, In o (rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b)
/\ (b + n <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= b) /\ (b + n <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= b)
/\ (forall e, In e (as_reg a) -> b + n <= se_beg e \/ se_beg e + se_size e <= b).
Proof.
intros a b n AVC Hn Hb AV.
assert (COV : forall o, In o (a_hull :: (0x7fff7000, KHI - 0x7fff7000) :: (band_lo, 2^64 - band_lo)
:: (prim_lo RE, 2^37 + 0x1000) :: (ptrarr_lo RE, 0x800000) :: rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b).
{ intros o Ho. destruct (AVC o Ho) as (iv & Hiv & I1 & I2).
destruct (avoids_In b n _ iv AV ltac:(unfold avoid_of; apply in_or_app; left; exact Hiv)); lia. }
split; [| split; [| split; [| split]]].
- pose proof (COV _ ltac:(left; reflexivity)) as H1. pose proof (COV _ ltac:(right; left; reflexivity)) as H2.
pose proof (COV _ ltac:(do 2 right; left; reflexivity)) as H3. cbn [fst snd] in H1, H2, H3. unfold KHI in *. lia.
- intros o Ho. apply COV. do 5 right. exact Ho.
- pose proof (COV _ ltac:(do 3 right; left; reflexivity)) as C. cbn [fst snd] in C. exact C.
- pose proof (COV _ ltac:(do 4 right; left; reflexivity)) as C. cbn [fst snd] in C. exact C.
- intros e He. destruct (avoids_In b n _ (sec_iv e) AV ltac:(unfold avoid_of; apply in_or_app; right; apply in_map; exact He)); unfold sec_iv in *; cbn [fst snd] in *; lia.
Qed.

Lemma fp_RSec_lt_ceil : forall a LB FS G x, gcons a LB FS G RE X -> fp_RSec a RE X x -> x < band_lo.
Proof.
intros a LB FS G x GC Fx. pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (_ & _ & _ & _ & KP & _).
idtac. destruct Fx as [H|[H|[H|H]]].
- destruct H as [H1 H2]; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
- destruct H as [H1 H2]; cbn [fst snd] in *. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & _ & PH & _). unfold ptrarr_hi, ptrarr_lo in *. idtac. lia.
- destruct H as (e & He & H). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _). idtac.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1. lia.
- destruct H as (e & He & H). pose proof (hdr_band _ _ _ _ _ _ GC e x He H). lia.
Qed.

Definition ltail_W (sp parr nch mb : Z) : list (Z * Z) :=
[(sp - 96, sp); (967944, 968560); (parr + 8 * nch, parr + 8 * nch + 8); (mb, mb + 32)].

Definition ltail_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo parr nch nres mb msz sz : Z) (reg : list secent) (m : mem) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (pj' : list byte),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (mb + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (ltail_W (bv_unsigned sp) parr nch mb) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' 967944 [C8 (wz nres); C8 (wz (nch + 1))]
/\ wjunk m' 967960 69
/\ rw_cells asegs m' 968512 [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)]
/\ wjunk m' 968520 5
/\ u64arr asegs m' parr (map (fun e => wz (se_beg e)) reg ++ [wz mb])
/\ rw_cells asegs m' (parr + 8 * (nch + 1)) [CB (Z.to_nat (8 * (nres - nch - 1))) pj']
/\ rw_cells asegs m' mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz nch)].

Lemma largealloc_tail : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(rax t0 t1 t2 a1 a2 a4 a5 a6 a7 s4x s6x s7x s8x s9x t3 t4 t5 t6 : word) (m : mem)
(lo parr nch nres mb msz sz E : Z) (reg : list secent) (junk8 pj : list byte),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -96) -> lo <= bv_unsigned sp - 96 ->
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
ro_cells asegs m 967896 [C8 (wz 4096); C8 (wz parr)] ->
rw_cells asegs m 967944 [C8 (wz nres); C8 (wz nch)] ->
wjunk m 967960 69 ->
rw_cells asegs m 968512 [C4 (wz 1); C4 (wz 0)] ->
wjunk m 968520 5 ->
u64arr asegs m parr (map (fun e => wz (se_beg e)) reg) -> nch = Z.of_nat (length reg) ->
rw_cells asegs m (parr + 8 * nch) [CB (Z.to_nat (8 * (nres - nch))) pj] -> nch < nres -> nres <= 2^20 ->
0x645000 <= parr -> parr + 8388608 <= lo ->
rw_cells asegs m mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz 0)] ->
0x645000 <= mb -> mb + msz <= lo -> 4096 <= msz -> (mb + msz <= parr \/ parr + 8388608 <= mb) ->
0 <= E < 2^64 -> 16 <= Z.lxor E 63 <= 26 ->
evt asegs (ltail_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo parr nch nres mb msz sz reg m)
(MS (mkR rax (wz (bv_unsigned sp + -96)) gp (wz A_TP) t0 t1 t2 (wz 968520) (wz 967896)
(wz (mb + 4096)) a1 a2 (wz nch) a4 a5 a6 a7 (wz msz) (wz E) s4x (wz mb) s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F (wz 0x43ddc) fc None m (seg_rom asegs)).
Proof.
intros until pj; intros MI ST LO FR K43 I1 I2 I3 I4 P1 NCH P2 NLT NMX PK PH ZBh MK MH MSZ MPD HE HIDX.
assert (LM : Z.of_nat (length (map (fun e => wz (se_beg e)) reg)) = nch) by (rewrite length_map; lia).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (stk_bound _ _ _ _ ST) as SB0 || idtac.
destruct (wjunk69_open m _ I2) as (w0 & w1 & w2 & w3 & w4 & bsl & J1 & BSL & LBSL). clear I2. change (967960 + 40) with 968000 in BSL.
destruct (wjunk5_open m _ I4) as (g0 & g1 & g2 & g3 & g4 & GS). clear I4.
set (idx := Z.lxor E 63) in HIDX.
pose proof (munch_refl (ltail_W (bv_unsigned sp) parr nch mb) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold ltail_W in MU.

replace (Z.to_nat (8 * (nres - nch))) with (8 + Z.to_nat (8 * (nres - nch - 1)))%nat in P2 by lia.
destruct (rw_cells_CB_split m _ _ _ _ P2) as [P2a P2b]. clear P2. change (Z.of_nat 8) with 8 in P2b.
step.
step.
rewrite (unsigned_lit E) by lia. fold idx.
step.
step. step.
rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
replace (parr + nch * 8) with (parr + 8 * nch) by lia.
remember (parr + 8 * nch) as Q eqn:EQ.
step.
step. step. step. step.
step. step.
step.
stp.
step. step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' : word, ms1 = MS (@bvmap_set 5 word 12 a2' R) FF (wz 0x43e24) fcc rv mm ro))
end.
{ step. if_cases Hc.
- apply evt_done. eexists. simp_regs. reflexivity.
- step. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a2' ->]. simp_regs.
step. step.
rewrite (unsigned_lit idx), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.

destruct (nth_error bsl (Z.to_nat (5 + idx - 5))) as [bw|] eqn:BW; [| apply nth_error_None in BW; lia].
with_mem ltac:(fun mm => pose proof (u64arr_read asegs mm _ bsl (5 + idx - 5) bw (wa (967896 + idx * 8 + 104)) BSL BW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as HR).
step.
clear HR. step.
step.
with_mem ltac:(fun mm => pose proof (u64arr_store_ok asegs mm _ bsl (5 + idx - 5) (wa (967896 + idx * 8 + 104)) BSL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK).
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc _ bsl (5 + idx - 5) (wz (bv_unsigned bw + 1)) BSL ltac:(lia)) as BSL';
replace (wa (968000 + 8 * (5 + idx - 5))) with (wa (967896 + idx * 8 + 104)) in BSL' by (unfold wa; f_equal; lia) end.
clear BSL. store_done. try clear SOK. rename BSL' into BSL.

step.
amo_step (amo_aligned_intro8 968536 ltac:(lia) ltac:(reflexivity)).
step.
amo_step (amo_aligned_intro8 968544 ltac:(lia) ltac:(reflexivity)).
step.

recast I3 [C1 (b8 1); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)].
stp.

do 11 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ltail_post. do 15 eexists. exists (drop 8 pj).
split; [reflexivity|].
subst Q. split; [unfold ltail_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact I1|].
split; [eapply (wjunk69_close _ _ [C1 (b8 (bv_unsigned (wz 0))); CB 7 (drop 1 (le8 w0))]); [exact J1| reflexivity| exact BSL| rewrite upd_length; exact LBSL]|].
change (bv_unsigned (wz 0)) with 0 in I3. split; [exact I3|].
split; [eapply wjunk5_close; exact GS|].
split; [eapply u64arr_snoc; [exact P1| rewrite length_map, <- NCH; exact P2a]|].
split; [replace (parr + 8 * (nch + 1)) with (parr + 8 * nch + 8) by lia; exact P2b|].
exact ZBh.
Qed.

Lemma largealloc_finish : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (s : PStateA) (a a1 : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z)
(rax t0 t1 t2 a1r a2 a4 a5 a6 a7 s4x s6x s7x s8x s9x t3 t4 t5 t6 : word) (m1 : mem)
(mb E nres1 : Z) (junk8 pj shu : list byte) (w0 w1 w2 w3 w4 g0 g1 g2 g3 g4 : word) (bsl : list word),
let msz := sec_map_size n in let sz := sec_size n in let reg := as_reg a in let nch := Z.of_nat (length reg) in let parr := ptrarr_lo RE in
gcons a LB FS G RE X -> avoid_covers RE X -> RTconst RE X m -> RStats RE X m -> RSec a LB RE X m ->
band_lo <= lo -> lo <= bv_unsigned sp - LARGE_STACK -> 0 <= n <= 2^26 -> from_primary n = false ->
mb mod kPage = 0 -> appr mb msz -> mb + msz <= band_lo -> zavoids mb msz (avoid_of (ae_L RE) a) = true ->
munch [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888);
(967936, 968560); (parr, parr + 0x800000)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -96) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m1 967944 [C8 (wz nres1); C8 (wz nch)] ->
rw_cells asegs m1 967960 [CB 8 (le8 w0); C8 w1; C8 w2; C8 w3; C8 w4] -> u64arr asegs m1 968000 bsl -> length bsl = 64%nat ->
rw_cells asegs m1 968512 [C4 (wz 1); C4 (wz 0)] ->
rw_cells asegs m1 968520 [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4] ->
u64arr asegs m1 parr (map (fun e => wz (se_beg e)) reg) ->
rw_cells asegs m1 (parr + 8 * nch) [CB (Z.to_nat (8 * (nres1 - nch))) pj] ->
nch < nres1 -> nres1 <= 2^20 -> nres1 mod kPtrArrBlock = 0 -> (nres1 = as_nres a \/ nres1 = as_nres a + kPtrArrBlock) ->
rw_cells asegs m1 mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz 0)] ->
rw_cells asegs m1 (mb + 32) [CB 4064 (repeat (b8 0) 4064)] ->
rw_cells asegs m1 (mb + 4096) [CB (Z.to_nat (msz - 4096)) (repeat (b8 0) (Z.to_nat (msz - 4096)))] ->
rw_cells asegs m1 (SH mb) [CB (Z.to_nat 512) (repeat (b8 250) (Z.to_nat 512))] ->
rw_cells asegs m1 (SH (mb + 4096)) [CB (Z.to_nat (sz / 8)) shu] ->
rw_cells asegs m1 (SH (mb + 4096 + sz)) [CB (Z.to_nat ((msz - 4096 - sz) / 8)) (repeat (b8 250) (Z.to_nat ((msz - 4096 - sz) / 8)))] ->
0 <= E < 2^64 -> 16 <= Z.lxor E 63 <= 26 ->
as_reg a1 = as_reg a ++ [mkSec mb msz n] -> as_nres a1 = nres1 -> as_tq a1 = as_tq a -> as_gq a1 = as_gq a ->
(forall c, cls a1 c = cls a c) -> as_cache_inited a1 = as_cache_inited a -> as_next a1 = as_next a -> as_spent a1 = as_spent a + sec_cost msz ->
evt asegs (large_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m (Some mb, a1) s)
(MS (mkR rax (wz (bv_unsigned sp + -96)) gp (wz A_TP) t0 t1 t2 (wz 968520) (wz 967896)
(wz (mb + 4096)) a1r a2 (wz nch) a4 a5 a6 a7 (wz msz) (wz E) s4x (wz mb) s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F (wz 0x43ddc) fc None m1 (seg_rom asegs)).
Proof.
intros until bsl; intros msz sz reg nch parr GC AVC RT RS RSE CEIL LO Hn HP MAL MK MC AVm MU WM MI1 ST1 RT1 FR I1 J1 BSL LBSL I3 GS P1 P2 NLT NMX NMOD NRES
ZBh ZBp ZBb SFh SBu SFs HE HIDX R1 R2 R3 R4 R5 R6 R7 R8.
pose proof CEIL as CEIL'. idtac. unfold LARGE_STACK in LO.
pose proof MC as MC'. idtac. pose proof MK as MK'. apply appr_to_lia in MK; [| unfold msz; pose proof (sec_map_size_ge n ltac:(lia) HP) as [SM _]; lia| lia].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _). rewrite KP in MAL. unfold kPtrArrBlock in NMOD, NRES.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & QH & _). unfold ptrarr_hi in QH. change (al_ptrarr (ae_L RE)) with parr in QH. fold parr in QK. rewrite ?KHI_eq in QK. idtac.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _ & TQD). cbn [fst snd] in TK, TB, TQD. unfold iv_disjoint in TQD; cbn [fst snd] in TQD. fold parr in TQD.
idtac. rewrite ?KHI_eq in TK. apply appr_to_lia in QK; [| lia| unfold ptrarr_hi in *; lia].
pose proof (sec_size_facts n Hn HP) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). fold sz msz in Z1, Z2, Z3, Z4, Z5, Z6.
pose proof (avoid_facts a mb msz AVC ltac:(lia) ltac:(lia) AVm) as (_ & AVO & AVP & AVQ & AVR). fold parr in AVQ.
pose proof (AVO _ (T_obj RE X)) as TMB. cbn [fst snd] in TMB.
assert (SHB : 0x7fff8000 <= SH mb /\ SH (mb + msz) = SH mb + msz / 8 /\ SH mb + msz / 8 <= 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; (first [ clear - H39 q7 H30 H24 q4 H19 H10 H9 r1 H5 H4 r0 q0 H0 H r q TMB AVQ Z5 r4 Z4 r5 Z3 r3 Z1 TQD TK QK MK' MC' R7 q3 LBSL q1 MK MAL r7 parr reg sz msz bsl mb n a1 a X RE BAND; lia | lia ])).
destruct SHB as (SHB1 & SHB2 & SHB3).
assert (SHE1 : SH (mb + 4096) = SH mb + 512) by (rewrite !SH_eq; (first [ clear - Z5 Z4 Z3 Z1 R7 NMOD NLT LBSL MK MAL nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])).
assert (SHE2 : SH (mb + 4096 + sz) = SH mb + 512 + sz / 8) by (rewrite !SH_eq; (first [ clear - Z5 Z4 Z3 Z1 R7 NMOD NLT LBSL MK MAL nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])).
destruct RSE as (_ & _ & _ & _ & _ & _ & HD & NLE & NMX0 & NMOD0). fold reg nch in HD, NLE.
rtc RT1 25%nat K25. fold parr in K25. unfold A_INSTANCE in K25.

eapply evt_cut.
{ eapply (largealloc_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rax t0 t1 t2 a1r a2 a4 a5 a6 a7 s4x s6x s7x s8x s9x t3 t4 t5 t6 m1
lo parr nch nres1 mb msz sz E reg junk8 pj);
[exact MI1| exact ST1| lia| exact FR| exact K25| exact I1| | exact I3| | exact P1| reflexivity| exact P2| lia| lia| (first [ clear - Z6 Z1 QK R7 NLT LBSL MK NLE parr nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])| (first [ clear - Z6 Z1 QH CEIL' R7 NLT LBSL MK NLE parr nch reg sz msz bsl nres1 mb lo n a1 a RE BAND; lia | lia ])| exact ZBh| (first [ clear - Z6 Z1 R7 NLT LBSL MK NLE nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])| (first [ clear - Z6 Z1 MC' CEIL' R7 LBSL MK reg sz msz bsl nres1 mb lo n a1 a RE BAND; lia | lia ])| (first [ clear - Z6 Z1 R7 LBSL MK reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])| exact AVQ| exact HE| exact HIDX].
- eapply (wjunk69_close _ _ [CB 8 (le8 w0)]); [exact J1| reflexivity| exact BSL| exact LBSL].
- eapply wjunk5_close; exact GS. }
cbv beta. intros ms' PO.
destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & pj' & -> & MUt & WMt & MI' & ST' & I1' & J' & I3' & G' & P1' & P2' & ZBh').
unfold ltail_W in MUt.
assert (PSH : parr + 8388608 <= SH mb \/ SH mb + msz / 8 <= parr) by (clear - QK SHB1 SHB3; lia).
assert (PSM : mb + msz <= SH mb \/ SH mb + msz / 8 <= mb) by (clear - MK MC SHB1 SHB3; lia).
assert (MBL : 0x645000 <= mb) by (clear - MK Z1 Z6; lia).
hide MK; hide QK; hide MK'; hide TK; hide SHB1; hide SHB3; hide NRES; hide TQD; hide AVP; hide AVQ; hide TMB; hide MAL; hide NMOD; hide NMOD0;
hide Z3; hide Z4; hide Z5; hide HIDX.
pose proof (munch_chain' _ _ m' _ m MUt MU ltac:(sub_fp_solve)) as MU'.
unhide MK'; unhide TK; unhide SHB1; unhide SHB3; unhide NRES; unhide TQD; unhide AVP; unhide AVQ; unhide TMB; unhide MAL; unhide NMOD; unhide NMOD0;
unhide Z3; unhide Z4; unhide Z5; unhide HIDX.
pose proof (wmono_trans asegs _ _ _ WM WMt) as WM'.
clear ZBh P2 GS I3 J1 I1 FR P1 BSL MU WM ST1 K25 RT1 MI1.
hide Z3; hide Z4; hide Z5; hide MAL; hide NMOD; hide NMOD0; hide HIDX; hide NRES; hide HE; hide Hn; hide NLE; hide NMX0;
hide TK; hide TB; hide TQD; hide TMB; hide AVP; hide KR; hide KO; hide KS; hide K32; hide KU; hide CEIL'; hide MC'; hide MK'; hide NRES.

hide PSH; hide PSM.
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (mb + 32) _) in ZBp;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r;
clear - MBL MC CEIL LO SPR AVQ NLT NMX Z1 Z6; unfold nch in *; split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (SH mb) _) in SFh;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; unhide PSH; unhide PSM;
clear - SHB1 SHB2 SHB3 MBL MC CEIL LO SPR PSH PSM NLT NMX Z1 Z6; pose proof SH_band; unfold nch in *;
split; [Z.div_mod_to_equations; lia| split; [lia| split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (mb + 4096) _) in ZBb;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; rewrite ?Z2Nat.id by lia;
clear - MBL MC CEIL LO SPR AVQ NLT NMX Z1 Z6; unfold nch in *; split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (SH (mb + 4096)) _) in SBu;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; rewrite ?Z2Nat.id by (clear - Z1; Z.div_mod_to_equations; lia); unhide PSH; unhide PSM;
rewrite SHE1; clear - SHB1 SHB2 SHB3 MBL MC CEIL LO SPR PSH PSM NLT NMX Z1 Z6; pose proof SH_band; unfold nch in *;
split; [Z.div_mod_to_equations; lia| split; [lia| split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (SH (mb + 4096 + sz)) _) in SFs;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; rewrite ?Z2Nat.id by (clear - Z1 Z6; Z.div_mod_to_equations; lia); unhide PSH; unhide PSM;
rewrite SHE2; clear - SHB1 SHB2 SHB3 MBL MC CEIL LO SPR PSH PSM NLT NMX Z1 Z6; pose proof SH_band; unfold nch in *;
split; [Z.div_mod_to_equations; lia| split; [lia| split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]]]].
transport_after_call asegs m1 m' MUt WMt.
unhide NRES.
unhide Z3; unhide Z4; unhide Z5; unhide MAL; unhide NMOD; unhide NMOD0; unhide HIDX; unhide NRES; unhide HE; unhide Hn; unhide NLE; unhide NMX0;
unhide TK; unhide TB; unhide TQD; unhide TMB; unhide AVP; unhide KR; unhide KO; unhide KS; unhide K32; unhide KU; unhide CEIL'; unhide MC'; unhide MK'; unhide MK; unhide QK.
clear MUt WMt.

assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (967936, 968560); (parr, parr + 8388608)]).
{ clear - RL MK' MK AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| subst parr; lia| subst parr; unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
assert (FWst : Forall st_avoid [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (967936, 968560); (parr, parr + 8388608)]).
{ clear - MK MBL SHB1 CEIL LO SPR TK QK.
repeat apply Forall_cons; try apply Forall_nil;
first [apply st_avoid_above; cbn [fst]; unfold A_ERRNO; lia| apply st_avoid_low; cbn [snd]; lia
| destruct (Z_lt_le_dec (rl_T X) 0x645000); [apply st_avoid_low; cbn [snd]; lia| apply st_avoid_above; cbn [fst]; unfold A_ERRNO; lia]]. }
assert (MUf : munch (W_large (bv_unsigned sp) RE X ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m').
{ clear - MU' SHB2. unfold W_large, LARGE_STACK, A_INSTANCE. cbn [app]. rewrite SHB2. change (ptrarr_lo RE) with parr.
change (967832 + 104) with 967936. change (967832 + 728) with 968560.
refine (munch_weaken _ _ _ _ _ MU'). sub_fp_solve. }

assert (HD' : forall i e, nth_error reg i = Some e -> sec_hdr_mem m' i e).
{ intros i e Hi. pose proof (HD i e Hi) as (A1 & A2 & A3). pose proof (nth_error_In _ _ Hi) as He.
pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
rewrite ?KHI_eq in E2. idtac.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [G1 _]. rewrite <- E4 in G1.
unfold iv_disjoint in E8; cbn [fst snd] in E8. change (ptrarr_lo RE) with parr in E8.
pose proof (proj1 (List.Forall_forall _ _) E9 _ (T_obj RE X)) as ET. unfold iv_disjoint in ET; cbn [fst snd] in ET.
pose proof (AVR e He) as EM.
assert (SE : SH (se_beg e) + 512 = SH (se_beg e + 4096) /\ 0x80000000 <= SH (se_beg e) /\ SH (se_beg e + 4096) <= 0x10007fff8000
/\ (SH (se_beg e + 4096) <= SH mb \/ SH mb + msz / 8 <= SH (se_beg e))).
{ pose proof (sec_req_facts (se_req e) ltac:(lia) E5) as [_ GE].
clear - SHB2 E1 E2 E3 EM MAL MK MC G1 E6 Z6 Z1 GE. rewrite <- SHB2. rewrite !SH_eq. Z.div_mod_to_equations. lia. }
destruct SE as (SE1 & SE2 & SE3 & SE4).
assert (AG : agree_on asegs (fun x => (se_beg e <= x < se_beg e + 4096) \/ (SH (se_beg e) <= x < SH (se_beg e) + 512)) m m').
{ eapply agree_on_of_munch; [exact MU'| exact WM'|]. intros x Hx _. cbn [outside].
clear - Hx EM E2 E3 G1 E6 E8 ET SE1 SE2 SE3 SE4 CEIL LO SPR MK MC SHB1 SHB3 QK QH TK TB Z6 Z1. (first [ clear - Hx x SE4 SE3 SE2 SE1 EM ET G1 E8 E6 E3 E2 e SHB3 SHB1 Z6 Z1 TB TK QH QK MC MK LO CEIL parr sz msz mb lo n sp X RE BAND; lia | lia ]). }
split; [| split].
- eapply rw_cells_agree; [exact AG| exact A1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. left. lia.
- eapply hjunk_wmono; [exact A2| exact WM'].
- eapply rw_cells_agree; [exact AG| exact A3|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. right. clear - Hz. lia. }
apply evt_done. unfold large_post. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact WM'|].
split; [eapply RTconst_munch; [exact RT| exact MU'| exact WM'| exact FWrt]|].
split; [eapply RStats_munch; [exact RS| exact MU'| exact WM'| exact FWst]|].
cbv beta iota zeta. fold msz sz.
split; [rewrite KP; reflexivity|].
split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact R7|].
split; [rewrite R2; unfold kPtrArrBlock; clear - NRES; lia|].
split; [exact R8|].
split; [rewrite KP; exact MAL|]. split; [exact MK'|]. split; [exact MC'|]. split; [exact AVm|].
split; [exact MUf|].
split.
{
unfold RSec, RSec_mem. rewrite R1, R2. change (ptrarr_lo RE) with parr. fold reg. rewrite length_app. cbn [length].
replace (Z.of_nat (length reg + 1)) with (nch + 1) by (clear; lia).
unfold SEC_NRES, SEC_JUNK, SEC_MUT, SEC_GST, A_INSTANCE.
change (967832 + 112) with 967944. change (967832 + 128) with 967960. change (967832 + 680) with 968512. change (967832 + 688) with 968520.
split; [exact I1'|]. split; [exact J'|]. split; [exact I3'|]. split; [exact G'|].
split; [rewrite map_app; cbn [map]; exact P1'|].
split; [replace (parr + 8 * nres1) with (parr + 8 * (nch + 1) + Z.of_nat (cells_size [CB (Z.to_nat (8 * (nres1 - nch - 1))) pj'])) by (cbn [cells_size csize]; clear - NLT; lia);
apply cells_hjunk; [exact P2'| clear - QK; lia]|].
split.
- intros i e Hi. destruct (Nat.lt_ge_cases i (length reg)) as [LT|GE].
+ rewrite nth_error_app1 in Hi by exact LT. exact (HD' i e Hi).
+ rewrite nth_error_app2 in Hi by exact GE.
destruct (i - length reg)%nat as [|k] eqn:EK; [| cbn in Hi; destruct k; discriminate].
cbn in Hi. injection Hi as <-. unfold sec_hdr_mem. cbn [se_beg se_size se_req]. fold sz.
replace (Z.of_nat i) with nch by (clear - GE EK; lia).
split; [exact ZBh'|]. split.
* rewrite KP. replace (mb + 4096) with (mb + 32 + Z.of_nat (cells_size [CB 4064 (repeat (b8 0) 4064)])) by (cbn; clear; lia).
apply cells_hjunk; [exact ZBp| clear - MBL; lia].
* unfold fas, fa_byte. exact SFh.
- unfold kMaxNumChunks, kPtrArrBlock. clear - NLT NMX NMOD. lia. }
rewrite KP. split; [exact ZBb|]. split.
{ replace (SH (mb + 4096 + sz)) with (SH (mb + 4096) + Z.of_nat (cells_size [CB (Z.to_nat (sz / 8)) shu])) by (cbn [cells_size csize]; clear - SHE1 SHE2 Z1; lia).
apply cells_hjunk; [exact SBu| clear - SHE1 SHB1; lia]. }
unfold fas, fa_byte. exact SFs.
Qed.
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 Q9Ho.Mq2 QnRU.Mqa.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).

Lemma unw_obj_head : forall m obj sz q rest bp, rw_cells asegs m obj (unw_obj obj sz q rest bp) -> length q = 5%nat -> 0 <= sz < 2^32 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz sz)] /\ exists q30 : list word, u64arr asegs m (obj + 16) q30 /\ Z.of_nat (length q30) = 30.
Proof.
intros m obj sz q rest bp H LQ SZ.
destruct (unw_obj_open m obj sz q rest bp LQ H) as (qs & rest2 & LQS & H1 & Q & _). split.
- eapply rw_cells_recast'; [exact H1| cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite (le8_split32 sz) by lia. rewrite <- !app_assoc. reflexivity.
- exists qs. split; [exact Q| exact LQS].
Qed.

End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QmP7.Mq0 QTVW.Mq0 QnRU.Mq7.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition populate_entry : Z := 0x443f8.
Definition POPULATE_STACK : Z := 512.

Lemma class_size_lo : forall c, 1 <= c <= 16 -> class_size c = 32 * c.
Proof. intros c Hc. unfold class_size. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Ltac popA_finish :=
apply evt_done; do 3 eexists;
split; [ cbv delta [mkR];
repeat match goal with |- context [wz (if ?cnd then _ else _)] =>
first [ replace cnd with true by (symmetry; apply Z.ltb_lt; lia) | replace cnd with false by (symmetry; apply Z.ltb_ge; lia) ] end;
reflexivity |];
split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [ match goal with H : stk asegs _ _ _ |- _ => exact H end | match goal with H : rw_cells asegs _ (bv_unsigned _ + -64) _ |- _ => exact H end ].

Lemma populate_A : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (a : AState) (c req lo v : Z) j1 j2 j3 j4,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp + -64 ->
1 <= c <= 30 -> 0 <= req <= 8 ->
rw_cells asegs m (ri_addr RE c) (ri_cellsL v (cls a c) j1 j2 j3 j4) ->
0 <= c_alloc_user (cls a c) <= c_mapped_user (cls a c) -> c_mapped_user (cls a c) <= kFreeArrayOffset ->
evt asegs (fun ms1 => exists (a5' a6' : word) m1,
ms1 = MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (ri_addr RE c)) (wz (rl_T X + 2768))
(wz A_INSTANCE) (wz (c * 4294967296)) (wz c) (wz (c_alloc_user (cls a c))) (wz req) a5' a6' a7
(wz (reg_beg (ae_L RE) c)) (wz (c_alloc_user (cls a c) + class_size c * req)) (wz (c_mapped_user (cls a c))) (wz (class_size c))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (if c_mapped_user (cls a c) <? c_alloc_user (cls a c) + class_size c * req then 0x44498 else 0x4456c)) fc None m1 (seg_rom asegs)
/\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (bv_unsigned sp + -64)
/\ rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 2768)) (wz c) (wz (ri_addr RE c)) (wz req) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz populate_entry) fc None m (seg_rom asegs)).
Proof.
intros until j4; intros RT RL MI ST CEIL LO Hc Hreq RI AU MU0.
pose proof CEIL as CEIL'. idtac.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX). rewrite KO in MU0.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2. hide PAL.
assert (SR : 0 <= class_size c * req <= 1033280) by (first [ clear - SZ1 TB TK PK RB SPR CEIL' Hreq LO CEIL lo req c sp X RE BAND; nia | nia ]).
cbv beta delta [ri_cellsL] in RI. unfold ri_addr in *. rtc RT 24%nat K24. unfold A_INSTANCE in *.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold populate_entry.
carve_frame 64%nat ST.
do 9 step.
step. step.
step.
step. stp.
step. ifz.
step. step.
destruct (Z.leb_spec c 16) as [CLO|CHI].
- ifz. stp.
step. step. step. step. step.
rewrite !(unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^5) with 32. change (2^32) with 4294967296.
replace (c * 32) with (class_size c) by (rewrite class_size_lo by lia; lia).
rewrite (unsigned_lit (class_size c)), (unsigned_lit req) by lia.
replace (al_space_beg (ae_L RE) + c * 4294967296) with (reg_beg (ae_L RE) c) by (rewrite RB; reflexivity).
step.
destruct (Z.ltb_spec (c_mapped_user (cls a c)) (c_alloc_user (cls a c) + class_size c * req)) as [LT|GE]; ifz; [|step]; popA_finish.
- ifz.
stp. step. stp. stp. step. stp. step. stp. step.
get_reg 21%Z ltac:(fun v => replace v with (wz (class_size c)) by (clear - CHI Hc; enum_cases c 17 30; vm_compute; reflexivity)).
step. step. step. step. step.
rewrite !(unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^32) with 4294967296.
rewrite (unsigned_lit (class_size c)), (unsigned_lit req) by lia.
replace (al_space_beg (ae_L RE) + c * 4294967296) with (reg_beg (ae_L RE) c) by (rewrite RB; reflexivity).
step.
destruct (Z.ltb_spec (c_mapped_user (cls a c)) (c_alloc_user (cls a c) + class_size c * req)) as [LT|GE]; ifz; popA_finish.
Qed.
End S.

Section S2.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Definition pop_W (sp c au : Z) : list (Z * Z) :=
[ (sp - POPULATE_STACK, sp); (rl_T X + 2768, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition pop_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (G : ghost) (c au lo : Z) (m : word -> option byte) (v : Z)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (k : nat),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (pop_W (bv_unsigned sp) c au) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrimL (snd r) (gappend c (repeat TFree k) G) RE X m' c v
/\ a0 = wz (if fst r then 1 else 0).

Definition pop_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s1' : AState) (G : ghost) (c au lo : Z) (m : word -> option byte) (v : Z) (ms' : machine_state) : Prop :=
exists x1 t0 t1 t2 x9 a1 a2 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 m',
ms' = MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (ri_addr RE c)) x9 (wz A_INSTANCE) a1 a2 (wz (c_alloc_user (cls s1' c))) a4 a5 a6 a7
(wz (reg_beg (ae_L RE) c)) x19
(wz (c_mapped_user (cls s1' c))) (wz (class_size c)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4456c) fc None m' (seg_rom asegs)
/\ munch (pop_W (bv_unsigned sp) c au) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrimL s1' G RE X m' c v.
End S2.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 Q9Ho.Mq1 QnRU.Mq7.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).

Definition carved (nc : Z) (k : nat) : list Z := map (fun j => nc + Z.of_nat j) (seq 0 k).
Definition coffw (c : Z) (j : Z) : word := Z_to_bv 64 (coff c j).

Lemma carved_length : forall nc k, length (carved nc k) = k.
Proof. intros. unfold carved. rewrite length_map, length_seq. reflexivity. Qed.
Lemma carved_S : forall nc k, carved nc (S k) = carved nc k ++ [nc + Z.of_nat k].
Proof. intros. unfold carved. rewrite seq_S, map_app. reflexivity. Qed.
Lemma in_carved : forall nc k i, In i (carved nc k) <-> nc <= i < nc + Z.of_nat k.
Proof.
intros nc k i. unfold carved. rewrite in_map_iff. split.
- intros (j & <- & Hj). apply in_seq in Hj. lia.
- intros Hi. exists (Z.to_nat (i - nc)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma NoDup_carved : forall nc k, List.NoDup (carved nc k).
Proof.
intros nc k. unfold carved. apply (NoDup_map_NoDup_ForallPairs (fun j => nc + Z.of_nat j)); [| apply seq_NoDup].
intros x y _ _ E. lia.
Qed.

Lemma skipn_repeat' {A} : forall (b : A) o n, skipn o (repeat b n) = repeat b (n - o).
Proof. intros b o. induction o as [|o IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat' {A} : forall (b : A) k n, (k <= n)%nat -> firstn k (repeat b n) = repeat b k.
Proof. intros b k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

Lemma rw_cells_CB_repeat_sub : forall m A n b o len,
rw_cells asegs m A [CB n (repeat b n)] -> (o + len <= n)%nat ->
rw_cells asegs m (A + Z.of_nat o) [CB len (repeat b len)].
Proof.
intros m A n b o len H LE.
replace n with (o + (n - o))%nat in H by lia.
apply rw_cells_CB_split in H. destruct H as [_ H]. rewrite skipn_repeat' in H.
replace (o + (n - o) - o)%nat with (len + (n - o - len))%nat in H by lia. replace (n - o)%nat with (len + (n - o - len))%nat in H by lia.
apply rw_cells_CB_split in H. destruct H as [H _]. rewrite firstn_repeat' in H by lia. exact H.
Qed.

Lemma cr_pure_carve : forall a G c K newc a',
cr_pure a G c K -> 1 <= c <= 31 -> 0 <= newc ->
c_alloc_user (cls a c) + newc * class_size c <= c_mapped_user (cls a c) ->
4 * (c_num_freed (cls a c) + newc) <= c_mapped_fa (cls a c) ->
cls a' c = set_alloc_user (c_alloc_user (cls a c) + newc * class_size c) (set_num_freed (c_num_freed (cls a c) + newc) (cls a c)) ->
as_cache_inited a' = as_cache_inited a ->
cr_pure a' (gappend c (repeat TFree (Z.to_nat newc)) G) c (mkPK (pk_fl K ++ rev (carved (ncarved G c) (Z.to_nat newc))) (pk_ca K)).
Proof.
intros a G c K newc a' PU Hc Hn LEu LEf Ea Ei.
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _).
pose proof (cr_pure_div8 a G c K PU Hc) as ((qa & QA0 & QA & QAE) & _ & E8).
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
unfold cr_pure. rewrite Ea, Ei. cbn [pk_fl pk_ca c_num_freed c_count c_mapped_fa c_alloc_user c_mapped_user set_alloc_user set_num_freed].
rewrite gappend_class.
assert (OLD : forall i t, tag_at G c i = Some t -> 0 <= i < ncarved G c) by (intros i t Ht; exact (tag_at_Some_lt _ _ _ _ Ht)).
assert (TG : forall i, In i (pk_fl K ++ rev (carved (ncarved G c) (Z.to_nat newc))) ->
tag_at (gappend c (repeat TFree (Z.to_nat newc)) G) c i = Some TFree).
{ intros i Hi. apply in_app_or in Hi. destruct Hi as [Hi|Hi].
- apply tag_at_gappend_Some_old. exact (P5 i Hi).
- rewrite <- in_rev in Hi. apply in_carved in Hi. rewrite tag_at_gappend_new by lia.
apply nth_error_repeat. lia. }
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
- rewrite length_app, length_rev, carved_length. lia.
- apply NoDup_app; [exact P3| apply NoDup_rev; apply NoDup_carved|].
intros i Hi Hi'. rewrite <- in_rev in Hi'. apply in_carved in Hi'. pose proof (OLD i _ (P5 i Hi)). lia.
- intros i Hi. apply tag_at_gappend_Some_old. exact (P6 i Hi).
- rewrite count_tag_app, count_tag_repeat, P7. cbn. lia.
- rewrite count_tag_app, count_tag_repeat, P8. cbn. lia.
- rewrite length_app, repeat_length. unfold ncarved in QAE. rewrite QA. rewrite Nat2Z.inj_add, Z2Nat.id by lia. rewrite Z.mul_add_distr_r, G1, QA. reflexivity.
- pose proof (class_size_facts c Hc) as [S1 _]. pose proof (Z.mul_nonneg_nonneg newc (class_size c) Hn ltac:(clear - S1; lia)). lia.
Qed.

Lemma cr_slots_carve : forall a a' G RE m c K newc,
cr_pure a G c K -> 1 <= c <= 31 -> 0 <= newc ->
c_alloc_user (cls a c) + newc * class_size c <= c_mapped_user (cls a c) ->
cr_slots a G RE m c ->
hjunk m (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) (reg_beg (ae_L RE) c + c_alloc_user (cls a c) + newc * class_size c) ->
rw_cells asegs m (SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)))
[CB (Z.to_nat (newc * (class_size c / 8))) (repeat fa_byte (Z.to_nat (newc * (class_size c / 8))))] ->
cr_slots a' (gappend c (repeat TFree (Z.to_nat newc)) G) RE m c.
Proof.
intros a a' G RE m c K newc PU Hc Hn LEu [SL SS] UT US.
pose proof (cr_pure_div8 a G c K PU Hc) as ((qa & QA0 & QA & QAE) & _ & E8).
pose proof (class_size_facts c Hc) as [S1 S2]. unfold ncarved in QAE.
assert (CASE : forall i t, tag_at (gappend c (repeat TFree (Z.to_nat newc)) G) c i = Some t ->
tag_at G c i = Some t \/ (ncarved G c <= i < ncarved G c + newc)).
{ intros i t Ht. destruct (Z.lt_ge_cases i (ncarved G c)) as [LT|GE].
- left. rewrite tag_at_gappend_old in Ht by exact LT. exact Ht.
- right. rewrite tag_at_gappend_new in Ht by exact GE.
assert (L : (Z.to_nat (i - ncarved G c) < length (repeat TFree (Z.to_nat newc)))%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
rewrite repeat_length in L. lia. }
unfold ncarved in CASE.
split.
- intros i t Ht Hp. destruct (CASE i t Ht) as [Ho|NEW]; [exact (SL i t Ho Hp)|].
unfold slot_beg. destruct (hjunk_split _ _ (reg_beg (ae_L RE) c + i * class_size c) _ UT ltac:(nia)) as [_ J].
destruct (hjunk_split _ _ (reg_beg (ae_L RE) c + i * class_size c + class_size c) _ J ltac:(nia)) as [J' _]. exact J'.
- intros i t Ht Hp. destruct (CASE i t Ht) as [Ho|NEW]; [exact (SS i t Ho Hp)|].
unfold slot_beg.
pose proof (rw_cells_CB_repeat_sub _ _ _ _ (Z.to_nat ((i - Z.of_nat (length (G c))) * (class_size c / 8))) (Z.to_nat (class_size c / 8)) US ltac:(nia)) as R.
replace (SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) + Z.of_nat (Z.to_nat ((i - Z.of_nat (length (G c))) * (class_size c / 8))))
with (SH (reg_beg (ae_L RE) c + i * class_size c)) in R; [exact R|].
rewrite QA, SH_plus8. replace (i * class_size c) with (8 * (i * (class_size c / 8))) by nia. rewrite SH_plus8. nia.
Qed.

Lemma populate_close {BAND : Band} : forall (aa a2s : AState) G RE X (m1 m3 : mem) c (K2 : Z -> pcls) k1 k2 k3 k4 CH2 qa qm newc v,
let x := cls aa c in let x2 := cls a2s c in let nc := ncarved G c in
let rb := reg_beg (ae_L RE) c in let fb := fa_beg (ae_L RE) c in
rlay_ok RE X -> 1 <= c <= 30 ->
c_alloc_user x2 = c_alloc_user x -> c_mapped_user x2 = c_mapped_user x -> c_num_freed x2 = c_num_freed x ->
c_count x2 = c_count x -> as_cache_inited a2s = as_cache_inited aa ->
4 * (c_num_freed x + newc) <= c_mapped_fa x2 ->
hjunk m1 (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, G c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep a2s G RE X m1 c0 (K2 c0)) ->
cr_pure a2s G c (K2 c) ->
0 <= qa -> c_alloc_user x = 8 * qa -> qa = nc * (class_size c / 8) -> 0 <= qm -> c_mapped_user x = 8 * qm ->
0 <= newc -> newc * class_size c <= c_mapped_user x - c_alloc_user x ->
wmono asegs m1 m3 ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m1 m3) ->
agree_on asegs (szone RE c (c_alloc_user x)) m1 m3 ->
rw_cells asegs m3 (region_info RE + 128 * c)
[C8 (wz v); CB 8 k1; C8 (wz (c_num_freed x + newc)); C8 (wz (c_mapped_fa x2));
C8 (wz (c_alloc_user x + newc * class_size c)); C8 (wz 0); C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 k2; C1 (Z_to_bv 8 0); CB 3 k3; CB 56 k4] ->
rw_cells asegs m3 (rl_T X + 208 + 80 * c)
[C4 (wz (c_count x)); C4 (wz (if as_cache_inited aa then bmax c else 0)); C8 (wz (if as_cache_inited aa then bsize c else 0))] ->
u32arr asegs m3 (rl_T X + 208 + 80 * c + 16) CH2 -> length CH2 = 16%nat ->
(forall j, (j < length (pk_ca (K2 c)))%nat -> nth_error CH2 j = Some (wz (coff c (nth j (pk_ca (K2 c)) 0)))) ->
u32arr asegs m3 fb (map (fun i => wz (coff c i)) (pk_fl (K2 c))) ->
u32arr asegs m3 (fb + 4 * c_num_freed x) (rev (map (coffw c) (carved nc (Z.to_nat newc)))) ->
hjunk m1 (fb + 4 * c_num_freed x) (fb + c_mapped_fa x2) ->
cr_slots a2s G RE m1 c ->
hjunk m1 (rb + c_alloc_user x) (rb + c_mapped_user x) ->
rw_cells asegs m3 (SH rb + qa) [CB (Z.to_nat ((c_mapped_user x - 8 * qa) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user x - 8 * qa) / 8)))] ->
hjunk m1 (SH rb + qm) (SH rb + 469762048) ->
hjunk m1 (SH fb) (SH fb + 67108864) ->
RPrimL (set_cls c (set_alloc_user (c_alloc_user x + newc * class_size c) (set_num_freed (c_num_freed x + newc) x2)) a2s)
(gappend c (repeat TFree (Z.to_nat newc)) G) RE X m3 c v.
Proof.
intros until v; intros x x2 nc rb fb RL Hc EA EM EN EC EI LE4 HJS GNE HCall PU2 QA0 QA QAE QM0 QM N0 NEWC WMm OTH AGS
RI PC0 ACH LCH2 HCH2 FA ARR FJ HSL UT US UJ FS.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2].
pose proof PU2 as (Q1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q11 & Q12 & Q13 & Q14 & _ & R1 & R2 & R3 & R4 & R5).
rewrite ?EA, ?EM, ?EN, ?EC in *.
assert (E8 : class_size c = 8 * (class_size c / 8)) by (clear - SZ1 SZ2; Z.div_mod_to_equations; lia).
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K2 c)))) = c_num_freed x) by (rewrite length_map; exact Q1).
eapply (RPrimL_reclose a2s _ G _ RE X m1 m3 c K2 (mkPK (pk_fl (K2 c) ++ rev (carved nc (Z.to_nat newc))) (pk_ca (K2 c))) v RL HJS GNE HCall ltac:(rewrite K32; lia));
[ intros c0 Hc0; apply cls_set_cls_ne; exact Hc0
| reflexivity
| intros c0 Hc0; apply gappend_other_class; exact Hc0
| intros; lia
| exact WMm | exact OTH |].
apply class_repL_split. split; [|split].
-
unfold cr_cellsL. rewrite !cls_set_cls_eq.
cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count as_cache_inited set_cls pk_ca].
rewrite ?EC, ?EI.
split; [exists k1, k2, k3, k4; cbv beta delta [ri_cellsL]; cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count]; rewrite ?EM; unfold ri_addr; exact RI|].
split; [cbv beta delta [pc_cells]; cbn [set_alloc_user set_num_freed c_count]; rewrite ?EC, ?EI; unfold pc_addr; exact PC0|].
exists CH2. unfold pc_addr. split; [exact ACH| split; [exact LCH2| exact HCH2]].
-
apply (cr_pure_carve a2s G c (K2 c) newc); [exact PU2| lia| lia| rewrite ?EA, ?EM; lia| rewrite ?EN; exact LE4| | reflexivity].
rewrite cls_set_cls_eq, ?EA, ?EN. reflexivity.
-
intros _. rewrite !cls_set_cls_eq.
cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa pk_fl]. rewrite ?EA, ?EM, ?EN, ?EC. fold rb fb.
split. { rewrite map_app, map_rev. apply u32arr_app; [exact FA|]. rewrite LFA. exact ARR. }
split. { pose proof (hjunk_wmono _ _ _ _ FJ WMm) as FJ1.
destruct (hjunk_split _ _ (fb + 4 * (c_num_freed x + newc)) _ FJ1 ltac:(lia)) as [_ FJ2]. exact FJ2. }
split; [| rewrite KS; replace 536870912 with (8 * 67108864) by reflexivity; rewrite SH_plus8; eapply hjunk_wmono; [exact FS| exact WMm]].
apply cr_user_split. rewrite !cls_set_cls_eq.
cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa]. rewrite ?EA, ?EM, ?EN, ?EC. fold rb fb.
pose proof (hjunk_wmono _ _ _ _ UT WMm) as UT1.
destruct (hjunk_split _ _ (rb + c_alloc_user x + newc * class_size c) _ UT1 ltac:(lia)) as [UT2 UT3].
assert (NQ : 0 <= newc * (class_size c / 8) /\ 8 * (newc * (class_size c / 8)) = newc * class_size c) by (clear - N0 E8 SZ1; nia).
set (nq := newc * (class_size c / 8)) in *.
assert (CNT : Z.to_nat ((c_mapped_user x - 8 * qa) / 8) = (Z.to_nat nq + Z.to_nat ((c_mapped_user x - 8 * qa) / 8 - nq))%nat).
{ clear - NQ NEWC QA QA0 QM QM0 R3. Z.div_mod_to_equations. lia. }
rewrite CNT in US at 1. apply rw_cells_CB_split in US. destruct US as [US1 US2].
rewrite firstn_repeat' in US1 by (first [ clear - CNT E8 R3 R1 SZ1 KM nq LCH2 NEWC N0 QM QAE QA nc x newc qm qa CH2 K2 c RE G a2s; lia | lia ]). rewrite skipn_repeat' in US2.
split; [| split; [| split]].
+ eapply (cr_slots_carve a2s _ G RE m3 c (K2 c) newc); [exact PU2| lia| lia| rewrite ?EA, ?EM; lia| | |].
* eapply cr_slots_agree; [exact PU2| exact HSL| lia|]. rewrite EA. exact AGS.
* rewrite ?EA. exact UT2.
* rewrite ?EA. fold nq. rewrite QA, SH_plus8. exact US1.
+ replace (rb + (c_alloc_user x + newc * class_size c)) with (rb + c_alloc_user x + newc * class_size c) by lia. exact UT3.
+ replace (rb + (c_alloc_user x + newc * class_size c)) with (rb + 8 * (qa + nq)) by (first [ clear - CNT E8 R1 SZ1 KM nq LCH2 NEWC N0 QM QAE QA rb nc x newc qm qa CH2 K2 c RE G a2s; lia | lia ]). rewrite SH_plus8.
replace ((c_mapped_user x - (c_alloc_user x + newc * class_size c)) / 8) with ((c_mapped_user x - 8 * qa) / 8 - nq).
2:{ clear - NQ NEWC QA QA0 QM QM0 R3. Z.div_mod_to_equations. lia. }
rewrite Z2Nat.id in US2 by lia. rewrite <- Z.add_assoc in US2.
replace (Z.to_nat ((c_mapped_user x - 8 * qa) / 8) - Z.to_nat nq)%nat with (Z.to_nat ((c_mapped_user x - 8 * qa) / 8 - nq)) in US2 by (first [ clear - CNT E8 R3 R1 SZ1 KM nq LCH2 NEWC N0 QM QAE QA nc x newc qm qa CH2 K2 c RE G a2s; lia | lia ]).
exact US2.
+ rewrite KO, QM at 1. replace 3758096384 with (8 * 469762048) by reflexivity. rewrite !SH_plus8. eapply hjunk_wmono; [exact UJ| exact WMm].
Qed.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QmP7.Mq0 QYyZ.Mq0 Q9Ho.Mq1.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QmvA.Mq3.
Import QlES.
Import QnRU.Mq6.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition drain_entry : Z := 0x40e14.

Definition DRAIN_STACK : Z := RECYCLE_STACK.

Lemma qptrs_app : forall l1 l2 b1 b2, qptrs (mkQ (l1 ++ l2) b1) = qptrs (mkQ l1 b2) ++ qptrs (mkQ l2 b2).
Proof. intros. unfold qptrs. cbn [q_list]. rewrite map_app, concat_app. reflexivity. Qed.

Lemma qptrs_q0 : qptrs q0 = [].
Proof. reflexivity. Qed.

Lemma NoDup_app_comm {A} : forall (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup (l2 ++ l1).
Proof.
intros l1 l2 H. apply (Permutation_NoDup (l := l1 ++ l2)); [apply Permutation_app_comm| exact H].
Qed.

Lemma qwf_app : forall l1 l2 b1 b2, qwf (mkQ l1 b1) -> qwf (mkQ l2 b2) -> qwf (mkQ (l1 ++ l2) (b1 + b2)).
Proof.
intros l1 l2 b1 b2 [F1 B1] [F2 B2]. unfold qwf in *. cbn [q_list q_bytes] in *. split; [apply Forall_app; auto|]. rewrite map_app, fold_right_add_app. lia.
Qed.

Lemma qwf_q0 : qwf q0.
Proof. split; [constructor| reflexivity]. Qed.

Lemma q_last_app : forall RE J1 J2, J2 <> [] -> q_last RE (J1 ++ J2) = q_last RE J2.
Proof.
intros RE J1 J2 NE. destruct (split_last J2) as [[f y]|] eqn:E; pose proof (split_last_spec J2) as SL; rewrite E in SL.
- subst J2. rewrite app_assoc, !q_last_snoc. reflexivity.
- congruence.
Qed.

Lemma q_first_app : forall RE J1 J2, J1 <> [] -> q_first RE (J1 ++ J2) = q_first RE J1.
Proof. intros RE [|j J1] J2 NE; [congruence| reflexivity]. Qed.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Hypothesis recycle_spec : recycle_stmt C RE X L.

Definition drain_W (sp : Z) : list (Z * Z) :=
[ (sp - 48, sp); (QMUT, QMUT + 4); (GQ, GQ + 32); (TQ X, TQ X + 32) ].

Lemma drain_W_zone : forall a LB0 FS0 G (sp : Z) Wx lo hi x,
gcons a LB0 FS0 G RE X -> band_lo <= sp - 48 ->
Forall (fun iv => exists j, tag_at G 24 j = Some TQOwn /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx ->
In (lo, hi) (drain_W sp ++ Wx) -> lo <= x < hi -> fp_RQuar a LB0 G RE X x \/ (band_lo <= x < sp).
Proof.
intros a LB0 FS0 G sp Wx lo hi x GC CE HWx Hin Hx. unfold drain_W, QMUT, GQ, TQ in *.
apply in_app_iff in Hin as [Hin|Hin].
- cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
+ right. lia.
+ left. do 2 right; left. split; cbn [fst snd]; lia.
+ left. do 2 right; left. split; cbn [fst snd]; lia.
+ left. left. split; cbn [fst snd]; lia.
- left. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as (j & Tj & B1 & B2). cbn [fst snd] in B1, B2.
do 5 right; left. exists 24, j, TQOwn. split; [exact Tj|]. split; [reflexivity|]. split; cbn [fst snd]; rewrite ?class_size_24; lia.
Qed.

Lemma drain_W_qzone : forall a LB0 FS0 G (sp : Z) Wx lo hi x,
gcons a LB0 FS0 G RE X -> band_lo <= sp - 48 ->
Forall (fun iv => exists j, tag_at G 24 j = Some TQOwn /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx ->
In (lo, hi) (drain_W sp ++ Wx) -> lo <= x < hi -> qzone a LB0 G RE X x.
Proof. intros. edestruct drain_W_zone as [Q|Q]; try eassumption; [left; exact Q| right; lia]. Qed.

Lemma drain_tail : forall ra (sp : word) gp t2 a3 a4 a5 a6 a7 t0 t1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m m1 : word -> option byte) (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost)
(lo : Z) (JT JG JJ : list Z) (QA : aptr -> Z) (Wx : list (Z * Z)) (junk : list byte) (tq gq : qcache) (ll : list batch),
let g' := mkQ ll (q_bytes gq + q_bytes tq) in
let a1 := set_gq g' (set_tq q0 a) in
as_tq a = tq -> as_gq a = gq -> ll = q_list gq ++ q_list tq -> JJ = JG ++ JT ->
gcons a LB0 FS0 G RE X -> QOTH C a LB0 FS0 G RE X m ->

ia_inv m -> List.NoDup (JT ++ JG) -> (forall j, tag_at G 24 j = Some TQOwn -> In j (JT ++ JG)) ->
(forall c j, tag_at G c j = Some TQOwn -> c = 24) ->
List.NoDup (qall [] a) -> (forall p, In p (qall [] a) -> qptr_rep a LB0 G RE m QA p) ->
(forall c i p, tag_at G c i = Some (TQuar p) -> In p (qall [] a) /\ aptr_cls p = c) ->
0 <= q_bytes tq <= 2 * QB -> 0 <= q_bytes gq <= QB -> qwf tq -> qwf gq ->
Forall (fun j => tag_at G 24 j = Some TQOwn) JT -> Forall (fun j => tag_at G 24 j = Some TQOwn) JG ->

mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -48) -> band_lo <= lo -> lo <= bv_unsigned sp - DRAIN_STACK ->
rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
munch (drain_W (bv_unsigned sp) ++ Wx) m m1 -> wmono asegs m m1 ->
Forall (fun iv => exists j, tag_at G 24 j = Some TQOwn /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx ->
rw_cells asegs m1 (TQ X) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (q_bytes tq))] ->
rw_cells asegs m1 GQ [C8 (wz (Z.of_nat (length ll))); C8 (wz (q_first RE JJ)); C8 (wz (q_last RE JJ)); C8 (wz (q_bytes gq))] ->
rw_cells asegs m1 QMUT [C4 (wz 1)] ->
batches_mem RE m1 QA ll JJ ->
q_bytes gq + q_bytes tq <= kQMaxSize ->
evt asegs (fun ms' => aimplT atn (if kQMaxSize <? q_bytes g' then recycle (ae_L RE) a1 else tret a1) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs)) ms')
(MS (mkR ra (wz (bv_unsigned sp + -48)) gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz (TQ X)) (wz (rl_T X + 208)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x40ebc) fc None m1 (seg_rom asegs)).
Proof.
intros until ll; intros g' a1 Etq Egq Ell EJJ GC QO HI ND TQO C24 NDP REP TQP BT BG QWT QWG FJT FJG MI ST CEIL LO FR MU WM HWx TQC GQC HM BM NOREC.
assert (EQA : qall [] a = qptrs tq ++ qptrs gq) by (unfold qall; rewrite Etq, Egq; reflexivity). rewrite EQA in NDP, REP, TQP. subst ll JJ.
pose proof CEIL as CEIL'. idtac. unfold DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
unfold QB in BT, BG.
pose proof (proj1 QO) as RT.
assert (RT1 : RTconst RE X m1).
{ eapply RTconst_frame; [exact RT| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|].
intros x Fx _. apply outside_intro. intros lo' hi' Hin Hx.
destruct (drain_W_zone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx Hin Hx) as [Q|Q].
- exact (fpQ_RTconst a LB0 FS0 G RE X GC x Q Fx).
- pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(left; exact Fx)). lia. }
rtc RT1 26%nat K26.
pose proof (munch_refl (drain_W (bv_unsigned sp)) m1) as MU1. pose proof (wmono_refl asegs m1) as WM1.

pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi in PC. rewrite ?KHI_eq in PK. idtac.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (T_obj RE X)) as (_ & TKq & TCq & _). cbn [fst snd] in TKq, TCq. pose proof SH_band as SHB0.
assert (OW : forall W' x, munch W' m1 m1 -> (forall iv, In iv W' -> In iv (drain_W (bv_unsigned sp))) ->
(prim_lo RE <= x < prim_hi RE \/ 0x7fff7000 <= x < 0x10007fff8000 \/ (IA <= x < 0x171d38 \/ IA_FLAG <= x < IA_FLAG + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e)) -> outside W' x).
{ intros W' x _ SUB Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. apply SUB in Hin. unfold drain_W, QMUT, GQ, TQ, A_INSTANCE in Hin. cbn in Hin.
unfold IA, IA_FLAG in Hx. unfold prim_hi, prim_lo in *.
destruct Hx as [Hx|[Hx|[Hx|(e & He & Hx)]]].
- destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (first [ clear - Y1 Hx x CEIL' LO lo sp BAND Y2 PK TK X RE; lia | lia ]).
- pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & _ & _ & _ & _ & _ & D3). rewrite ?KHI_eq in E2. idtac.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (first [ clear - E3 Y1 Hx e x CEIL' LO lo sp BAND D E2 Y2 PK TK X RE; lia | lia ]). }
assert (OWx : forall x, ((exists c i t, tag_at G c i = Some t /\ t <> TQOwn /\ in_iv (slot_beg RE c i, class_size c) x)
\/ 0x7fff7000 <= x < 0x10007fff8000 \/ (IA <= x < 0x171d38 \/ IA_FLAG <= x < IA_FLAG + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e)) -> outside Wx x).
{ intros x Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as (j & Tj & B1 & B2). cbn [fst snd] in B1, B2.
pose proof (slot_prim _ _ _ _ _ _ GC 24 j TQOwn Tj) as (P1 & P2 & _). rewrite class_size_24 in P2. unfold IA, IA_FLAG in Hx. unfold prim_hi, prim_lo in *.
destruct Hx as [(c & i & t & Ht & NT & [S1 S2])|[Hx|[Hx|(e & He & Hx)]]]; cbn [fst snd] in *.
- assert (NE : c <> 24 \/ i <> j) by (destruct (Z.eq_dec c 24) as [->|]; [right; intros ->; rewrite Tj in Ht; inversion Ht; subst; apply NT; reflexivity| left; assumption]).
pose proof (slots_disjoint _ _ _ _ _ _ GC c i t 24 j TQOwn Ht Tj NE). rewrite class_size_24 in *. (first [ clear - H B2 B1 j Y2 Y1 hi' lo' S2 S1 i c x PK TK X RE BAND; lia | lia ]).
- lia.
- lia.
- pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & _ & _ & _ & D1 & _). unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. (first [ clear - D1 E2 P2 P1 B2 B1 j Y2 Y1 hi' lo' Hx e x PK TD TK X RE BAND; lia | lia ]). }
unfold drain_W, QOBJ, GQ, QMUT, TQ, A_INSTANCE in *.
change (967832 + 880 + 4) with 968716 in *. change (967832 + 880) with 968712 in *.
change (967832 + 888 + 32) with 968752 in *. change (967832 + 888) with 968720 in *. change (967832 + 728) with 968560 in *.
replace (rl_T X + 80 + 32) with (rl_T X + 112) in MU, MU1, OW by lia.

assert (BUILD : forall (rb bg : Z) m2,
rw_cells asegs m2 (rl_T X + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
rw_cells asegs m2 968720 [C8 (wz (Z.of_nat (length (q_list gq ++ q_list tq)))); C8 (wz (q_first RE (JG ++ JT)));
C8 (wz (q_last RE (JG ++ JT))); C8 (wz (q_bytes gq + q_bytes tq))] ->
rw_cells asegs m2 968712 [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)] ->
munch [(bv_unsigned sp + -48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112)] m1 m2 ->
wmono asegs m1 m2 -> q_bytes gq + q_bytes tq <= bg ->
RQuarM rb QB bg [] a1 LB0 G RE X m2).
{ intros rb bg m2 TQC2 GQC2 HM2 MU2 WM2 HBG.
assert (MU02 : munch ([(bv_unsigned sp + -48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112)] ++ Wx) m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx. apply outside_app in Hx as [Hx _]. exact Hx. }
pose proof (wmono_trans asegs _ _ _ WM WM2) as WM02.
assert (AG02 : forall P : Z -> Prop,
(forall x, P x -> ((exists c i t, tag_at G c i = Some t /\ t <> TQOwn /\ in_iv (slot_beg RE c i, class_size c) x)
\/ 0x7fff7000 <= x < 0x10007fff8000 \/ (986368 <= x < 0x171d38 \/ 1570184 <= x < 1570184 + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e))) -> agree_on asegs P m m2).
{ intros P HP. eapply agree_on_of_munch; [exact MU02| exact WM02|]. intros x Px _. apply outside_app. split; [| apply OWx; apply HP; exact Px].
apply OW; [apply munch_refl| intros iv Hiv; exact Hiv|].
destruct (HP x Px) as [(c & i & t & Ht & _ & [S1 S2])|Hx]; [| right; exact Hx]. left.
pose proof (slot_prim _ _ _ _ _ _ GC c i t Ht) as (P1 & P2 & _). cbn [fst snd] in S1, S2. unfold prim_hi in *. lia. }
assert (AG12 : forall P : Z -> Prop,
(forall x, P x -> (prim_lo RE <= x < prim_lo RE + 2^37 + 4096 \/ 0x7fff7000 <= x < 0x10007fff8000 \/ (986368 <= x < 0x171d38 \/ 1570184 <= x < 1570184 + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e))) -> agree_on asegs P m1 m2).
{ intros P HP. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros x Px _. apply OW; [apply munch_refl| intros iv Hiv; exact Hiv| apply HP; exact Px]. }
exists [], (JG ++ JT), QA. subst a1 g'. cbn [as_tq as_gq set_gq set_tq as_reg qall map app].
assert (SLOTZ : forall j x, In j (JG ++ JT) -> in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x ->
prim_lo RE <= x < prim_lo RE + 2^37 + 4096 \/ 0x7fff7000 <= x < 0x10007fff8000 \/ (986368 <= x < 0x171d38 \/ 1570184 <= x < 1570184 + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e)).
{ intros j x Hj Hx. assert (Tj : tag_at G 24 j = Some TQOwn).
{ apply in_app_iff in Hj as [Hj|Hj]; [exact (proj1 (List.Forall_forall _ _) FJG j Hj)| exact (proj1 (List.Forall_forall _ _) FJT j Hj)]. }
pose proof (slot_prim _ _ _ _ _ _ GC 24 j TQOwn Tj) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2 |- *.
destruct Hx as [[S1 S2]|Hx]; cbn [fst snd] in *; [left; lia| right; left]. pose proof (slot_band _ _ _ _ _ _ GC 24 j TQOwn x Tj Hx). pose proof SH_band. lia. }
split.
{
split; [exact TQC2|]. split; [exact I|]. split; [constructor| apply qwf_q0]. }
split.
{
split; [exact GQC2|]. split; [| split; [apply Forall_app; split; assumption|]].
- eapply (batches_mem_agree RE (fun x => exists j, In j (JG ++ JT) /\ (in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x)));
[apply AG12| exact BM| | |].
+ intros x (j & Hj & Hx). exact (SLOTZ j x Hj Hx).
+ apply List.Forall_forall. intros j Hj x Hx. exists j. split; [exact Hj| left; exact Hx].
+ apply List.Forall_forall. intros j Hj x Hx. exists j. split; [exact Hj| right; exact Hx].
+ apply Forall_app. split; [exact (proj1 QWG)| exact (proj1 QWT)].
- cbn [q_list q_bytes]. apply qwf_app; [exact QWG| exact QWT]. }
split; [exact HM2|].
split.
{ eapply ia_inv_agree; [apply AG02| exact HI|]; [| intros x Hx; exact Hx]. intros x Hx. right; right; left. unfold IA, IA_FLAG in Hx. lia. }
split; [apply NoDup_app_comm; exact ND|].
split; [intros j Hj; apply in_app_iff; apply or_comm; apply in_app_iff; apply TQO; exact Hj|].
split; [exact C24|].
assert (EQL : forall p, In p (qptrs {| q_list := q_list gq ++ q_list tq; q_bytes := q_bytes gq + q_bytes tq |}) <-> In p (qptrs tq ++ qptrs gq)).
{ intros p. rewrite (qptrs_app _ _ _ 0). rewrite !in_app_iff.
replace (qptrs {| q_list := q_list gq; q_bytes := 0 |}) with (qptrs gq) by (destruct gq; reflexivity).
replace (qptrs {| q_list := q_list tq; q_bytes := 0 |}) with (qptrs tq) by (destruct tq; reflexivity). (first [ clear - p SHB0 TKq TD TK SPR BG BT gq tq sp X RE BAND; tauto | tauto ]). }
split.
{ rewrite (qptrs_app _ _ _ 0).
replace (qptrs {| q_list := q_list gq; q_bytes := 0 |}) with (qptrs gq) by (destruct gq; reflexivity).
replace (qptrs {| q_list := q_list tq; q_bytes := 0 |}) with (qptrs tq) by (destruct tq; reflexivity).
rewrite qptrs_q0. cbn [app]. apply NoDup_app_comm. exact NDP. }
split.
{ intros p Hp. apply EQL in Hp. pose proof (REP p Hp) as R. destruct p as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
eapply (qchunk_mem_agree (fun x => slot_beg RE (class_of n) i <= x < slot_beg RE (class_of n) i + class_size (class_of n)
\/ SH (slot_beg RE (class_of n) i) <= x < SH (slot_beg RE (class_of n) i) + (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) / 8));
[apply AG02| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; exact Hx].
intros x [Hx|Hx]; [left; exists (class_of n), i, (TQuar (APrim id n)); split; [exact Ht|]; split; [discriminate| split; cbn [fst snd]; lia]| right; left].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia.
pose proof (slot_band _ _ _ _ _ _ GC _ _ _ x Ht ltac:(split; cbn [fst snd]; lia)). pose proof SH_band. lia.
- destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
pose proof (sec_facts _ _ _ _ _ _ GC _ Hin) as (E1 & E2 & E3 & E4 & _). cbn [se_beg se_size se_req] in E1, E2, E3, E4.
pose proof kconsts as (_ & _ & _ & _ & KP & _).
eapply (qchunk_mem_agree (fun x => mb + kPage <= x < mb + sec_map_size n \/ SH (mb + kPage) <= x < SH (mb + kPage) + (mb + sec_map_size n - (mb + kPage)) / 8));
[apply AG02| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; exact Hx].
intros x [Hx|Hx]; [do 3 right; exists (mkSec mb (sec_map_size n) n); split; [exact Hin| cbn [se_beg se_size]; lia]| right; left].
eapply (sec_band _ _ _ _ _ _ GC _ x Hin). cbn [se_beg se_size]. split; cbn [fst snd]; [lia|].
replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. lia. }
split; [intros c i p Ht; destruct (TQP c i p Ht) as [H1 H2]; split; [apply EQL; exact H1| exact H2]|].
split; [constructor|]. cbn [q_bytes q0]. unfold QB in *. lia. }
hide MU. hide WM.
step. step. step.
step. stp.
step.
recast HM [C1 (b8 1); C1 (b8 0); C1 (b8 0); C1 (b8 0)].
stp.
rewrite unsigned_lit in HM by lia.
step. step.
step.
destruct (Z.ltb_spec0 kQMaxSize (q_bytes gq + q_bytes tq)) as [BIG|SMALL]; rewrite KMX in *.
2:{
ifz.
do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. replace (268435456 <? q_bytes g') with false by (symmetry; apply Z.ltb_ge; subst g'; cbn [q_bytes]; lia).
apply aimplT_ret. apply evt_done.
unhide MU. unhide WM.
lazymatch goal with |- ?hd (MS _ _ _ _ _ ?mf _) =>
assert (MUf : munch ([(bv_unsigned sp + -48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112)] ++ Wx) m mf)
by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU1]; intros x Hx; apply outside_app in Hx as [Hx _]; exact Hx);
pose proof (wmono_trans asegs _ _ _ WM WM1) as WMf
end.
unfold qret_post. do 15 eexists. eexists. exists G. split; [reflexivity|]. split; [reflexivity|].
split; [assumption|]. split; [exact ST|].
split.
{ eapply aheap_presA_of_munch; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MUf| exact WMf|].
intros lo' hi' x Hin Hx. eapply (drain_W_zone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx); [| exact Hx].
unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [app Z.add Z.sub] in Hin |- *.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact Hin. }
split.
{
lazymatch type of MUf with munch ?W _ _ => assert (QZW : forall lo' hi' x, In (lo', hi') W -> lo' <= x < hi' -> qzone a LB0 G RE X x) end.
{ intros lo' hi' x Hin Hx. eapply (drain_W_qzone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx); [| exact Hx].
unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [app Z.add Z.sub] in Hin |- *.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact Hin. }
split.
- eapply (depot_keep_of_pzone a LB0 FS0 G RE X m _ _ GC MUf WMf). intros lo' hi' x Hin Hx.
destruct (QZW lo' hi' x Hin Hx) as [QZ|QZ]; [left; exact QZ| do 3 right; exact QZ].
- eapply (errno_keep_of_ezone a LB0 FS0 G RE X m _ _ GC MUf WMf). intros lo' hi' x Hin Hx. apply ezone_of_qzone. exact (QZW lo' hi' x Hin Hx). }
split.
{ eapply gcons_ext; [exact GC| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia]. }
split.
{ eapply (QOTH_ext C a); [| intros; reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl| apply same_tags_refl].
eapply QOTH_munch; [exact GC| exact QO| exact MUf| exact WMf|].
intros lo' hi' x Hin Hx. eapply (drain_W_qzone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx); [| exact Hx].
unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [app Z.add Z.sub] in Hin |- *.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact Hin. }
apply (BUILD 0 QB); [assumption| assumption| exact HM| exact MU1| exact WM1| unfold QB; lia]. }

exfalso. clear - BIG NOREC. lia.
Qed.

Lemma drain_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (lo : Z),
QRUN C 0 (2 * QB) QB [] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - DRAIN_STACK ->
q_bytes (as_gq a) + q_bytes (as_tq a) <= kQMaxSize ->
aimplT atn (drain (ae_L RE) a) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz (TQ X)) (wz (rl_T X + 208)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz drain_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros QR MI ST CEIL LO NOREC.
pose proof CEIL as CEIL'. idtac. unfold DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & _).
destruct QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
destruct HT as (TQC & BMT & FJT & QWT). destruct HG as (GQC & BMG & FJG & QWG). unfold QB in BND.
pose proof (batches_mem_nx_length _ _ _ _ _ _ BMT) as LT. pose proof (batches_mem_nx_length _ _ _ _ _ _ BMG) as LG.
pose proof (qwf_length_bound _ QWT) as QLT. pose proof (qwf_length_bound _ QWG) as QLG. rewrite KBB in QLT, QLG.
pose proof (proj1 QO) as RT. rtc RT 26%nat K26.
pose proof (wmono_refl asegs m) as WM.

pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.

assert (TAILEQ : forall ll tq gq, as_tq a = tq -> as_gq a = gq -> ll = q_list gq ++ q_list tq ->
drain (ae_L RE) a = (if kQMaxSize <? q_bytes gq + q_bytes tq
then recycle (ae_L RE) (set_gq (mkQ ll (q_bytes gq + q_bytes tq)) (set_tq q0 a))
else tret (set_gq (mkQ ll (q_bytes gq + q_bytes tq)) (set_tq q0 a)))).
{ intros ll tq gq E1 E2 E3. unfold drain. rewrite E1, E2. subst ll. reflexivity. }
remember (as_tq a) as tq eqn:Etq. remember (as_gq a) as gq eqn:Egq. symmetry in Etq, Egq.
assert (EQA : qall [] a = qptrs tq ++ qptrs gq) by (unfold qall; rewrite Etq, Egq; reflexivity).
destruct tq as [tl tb]. destruct gq as [gl gb]. cbn [q_list q_bytes] in *.
unfold drain_entry, QOBJ, GQ, QMUT, TQ, A_INSTANCE in *.
change (967832 + 880 + 4) with 968716 in *. change (967832 + 880) with 968712 in *.
change (967832 + 888 + 32) with 968752 in *. change (967832 + 888) with 968720 in *. change (967832 + 728) with 968560 in *.

assert (KEEP : forall (W' : list (Z * Z)) (m' : word -> option byte) bs J (jx fin : Z),
batches_mem_nx RE m QA bs J fin -> Forall bwf bs -> Forall (fun j => tag_at G 24 j = Some TQOwn) J ->
munch W' m m' -> wmono asegs m m' ->
(forall iv, In iv W' -> In iv [(bv_unsigned sp + -48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112)]
\/ (tag_at G 24 jx = Some TQOwn /\ ~ In jx J /\ slot_beg RE 24 jx <= fst iv /\ snd iv <= slot_beg RE 24 jx + 8192)) ->
batches_mem_nx RE m' QA bs J fin).
{ intros W' m' bs J jx fin BMx FB FJ MUx WMx HW.
eapply (batches_mem_nx_keep (fun x => outside W' x)); [exact BMx| exact FB| | exact WMx|].
- eapply agree_on_of_munch; [exact MUx| exact WMx|]. intros x Hx _; exact Hx.
- intros j x Hj Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
pose proof (proj1 (List.Forall_forall _ _) FJ j Hj) as Tj.
pose proof (slot_prim _ _ _ _ _ _ GC 24 j TQOwn Tj) as (P1 & P2 & P3 & _). unfold prim_hi, prim_lo in P1, P2. rewrite class_size_24 in *.
destruct (HW _ Hin) as [Hin'|(Tjx & NJ & B1 & B2)]; cbn [fst snd] in *.
+ cbn in Hin'. destruct Hx as [[S1 S2]|Hx]; cbn [fst snd] in *.
* destruct Hin' as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (first [ clear - P2 Y1 S2 x j PC LG LT CEIL' LO gl tl JG JT lo sp RE BAND P1 Y2 S1 PK P3 TD TK X; lia | lia ]).
* pose proof (slot_band _ _ _ _ _ _ GC 24 j TQOwn x Tj Hx).
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (T_obj RE X)) as (_ & TKz & _). cbn [fst snd] in TKz. pose proof SH_band.
destruct Hin' as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
+ assert (NE : 24 <> 24 \/ j <> jx) by (right; intros ->; exact (NJ Hj)).
pose proof (slots_disjoint _ _ _ _ _ _ GC 24 j TQOwn 24 jx TQOwn Tj Tjx NE) as D. rewrite class_size_24 in D.
destruct Hx as [[S1 S2]|Hx]; cbn [fst snd] in *; [(first [ clear - D B2 B1 P3 P1 Y2 Y1 hi' lo' S2 S1 x j jx PK LG LT TD TK gl tl JG JT X RE BAND; lia | lia ])|].
pose proof (slot_band _ _ _ _ _ _ GC 24 j TQOwn x Tj Hx). pose proof (slot_prim _ _ _ _ _ _ GC 24 jx TQOwn Tjx) as (Q1 & Q2 & _).
unfold prim_hi, prim_lo in Q1, Q2. pose proof SH_band. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKz & _). unfold prim_lo in PKz. rewrite ?KHI_eq in PKz. lia. }
pose proof QWT as [FBT _]. pose proof QWG as [FBG _]. cbn [q_list] in FBT, FBG.
destruct tl as [|tb0 tl'].
{
destruct JT as [|j0 JT']; [| cbn in LT; discriminate]. cbn [length Z.of_nat] in TQC.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112)] m) as MU.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
do 4 step.
recast HM [C4 (wz 0)].
amo_step (amo_aligned_intro4 968712 ltac:(lia) ltac:(reflexivity)).
do 4 step.
amo_step (amo_aligned_intro4 968712 ltac:(lia) ltac:(reflexivity)).
step. if_lit.
step. step. if_lit.
step. step. ifz.
step. step. ifz.
eapply evt_mono; [eapply (drain_tail ra sp gp t2 a3 _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ s a LB0 FS0 G lo [] JG JG QA [] _
(mkQ [] tb) (mkQ gl gb) gl Etq Egq)
| cbv beta; intros ms' H'; rewrite (TAILEQ gl _ _ eq_refl eq_refl); [exact H'| cbn [q_list]; symmetry; apply app_nil_r] ].
all: try assumption; try eassumption.
- cbn [q_list]. symmetry; apply app_nil_r.
- symmetry; apply app_nil_r.
- unfold QB in *; cbn [q_bytes]; lia.
- unfold QB in *; cbn [q_bytes]; lia.
- rewrite app_nil_r. unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [Z.add].
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact MU.
- constructor.
- unfold batches_mem. eapply (KEEP _ _ _ _ 0 0); [exact BMG| exact FBG| exact FJG| exact MU| exact WM| intros iv Hiv; left; exact Hiv]. }

destruct JT as [|j0 JT']; [cbn in LT; discriminate|]. cbn [length] in LT, TQC, QLT.
destruct (split_last gl) as [[gf gbl]|] eqn:ESG; pose proof (split_last_spec gl) as SLG; rewrite ESG in SLG; subst gl.
2:{
destruct JG as [|k0 JG']; [| cbn in LG; discriminate]. cbn [length Z.of_nat] in GQC.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112)] m) as MU.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
do 4 step.
recast HM [C4 (wz 0)].
amo_step (amo_aligned_intro4 968712 ltac:(lia) ltac:(reflexivity)).
do 4 step.
amo_step (amo_aligned_intro4 968712 ltac:(lia) ltac:(reflexivity)).
step. if_lit. step. step. if_lit.
step. step. ifz.
step. step. ifz.
step. step. ifz.
step. step.
step. step.
step. step.
stp. stp. stp.
eapply evt_mono; [eapply (drain_tail ra sp gp t2 a3 _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ s a LB0 FS0 G lo
(j0 :: JT') [] (j0 :: JT') QA [] _ (mkQ (tb0 :: tl') tb) (mkQ [] gb) (tb0 :: tl') Etq Egq)
| cbv beta; intros ms' H'; rewrite (TAILEQ (tb0 :: tl') _ _ eq_refl eq_refl); [exact H'| reflexivity] ].
all: try assumption; try eassumption.
- reflexivity.
- reflexivity.
- unfold QB in *; cbn [q_bytes]; lia.
- unfold QB in *; cbn [q_bytes]; lia.
- rewrite app_nil_r. unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [Z.add].
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact MU.
- constructor.
- unfold batches_mem. eapply (KEEP _ _ _ _ 0 0); [exact BMT| exact FBT| exact FJT| exact MU| exact WM| intros iv Hiv; left; exact Hiv]. }

destruct (split_last JG) as [[JGF jgl]|] eqn:ESJ; pose proof (split_last_spec JG) as SLJ; rewrite ESJ in SLJ; subst JG.
2:{ exfalso. rewrite length_app in LG. cbn in LG. lia. }
replace (Z.of_nat (length (gf ++ [gbl]))) with (Z.of_nat (length gf) + 1) in GQC, QLG by (rewrite length_app; cbn [length]; lia).
rewrite q_last_snoc in GQC.
unfold batches_mem in BMG. apply batches_mem_nx_snoc_inv in BMG as [BMF BL]; [| rewrite !length_app in LG; cbn in LG; lia].
destruct BL as (BCl & BAl & BJl & BSl). hide BAl. hide BJl. hide BSl.
apply Forall_app in FJG as [FJGF FJl]. apply Forall_cons_iff in FJl as [Tjl _].
apply Forall_app in FBG as [FBGF FBl]. apply Forall_cons_iff in FBl as [Bwf _].
set (Bgl := slot_beg RE 24 jgl) in *.
pose proof (slot_prim _ _ _ _ _ _ GC 24 jgl TQOwn Tjl) as (Pg1 & Pg2 & Pg3 & _). unfold prim_hi, prim_lo in Pg1, Pg2. rewrite class_size_24 in Pg2. fold Bgl in Pg1, Pg2, Pg3.
pose proof (fun y H => slot_band _ _ _ _ _ _ GC 24 jgl TQOwn y Tjl H) as SBg. fold Bgl in SBg.
assert (SHBg : 0x2008fff7000 <= SH Bgl /\ SH Bgl + 1024 <= SH band_lo).
{ split; [apply (SBg (SH Bgl))| enough (SH Bgl + 1023 < SH band_lo) by lia; apply (SBg (SH Bgl + 1023))]; split; cbn [fst snd]; rewrite ?class_size_24; try (first [ clear - QLT LG LT Bgl jgl JGF gbl gf tb tl' JT' RE BAND Pg3 Pg1 PK; lia | lia ]).
all: change (8192 / 8) with 1024; lia. }
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (T_obj RE X)) as (_ & TKg & _). cbn [fst snd] in TKg. pose proof SH_band as SHBg0.
assert (NJl : ~ In jgl (JGF ++ j0 :: JT')).
{ intros Hin. rewrite app_assoc in ND. pose proof (NoDup_remove_2 _ [] jgl ND) as NI. rewrite app_nil_r in NI. apply NI.
apply in_app_iff. apply in_app_iff in Hin. (first [ clear - Hin SHBg0 TKg SHBg TD TK SPR BND Bgl jgl JGF gb tb JT' j0 sp X RE BAND; tauto | tauto ]). }
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (968712, 968716); (968720, 968752); (rl_T X + 80, rl_T X + 112); (Bgl, Bgl + 8)] m) as MU.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
do 4 step.
recast HM [C4 (wz 0)].
amo_step (amo_aligned_intro4 968712 ltac:(lia) ltac:(reflexivity)).
do 4 step.
amo_step (amo_aligned_intro4 968712 ltac:(lia) ltac:(reflexivity)).
step. if_lit. step. step. if_lit.
step. step. ifz.
step. step. ifz.
step. step. ifz.
step.
step. step.
step.
step.
step. step.
step.
stp. stp. stp.

lazymatch type of GQC with rw_cells _ ?mm ?ad [C8 (wz ?len); C8 _; C8 ?lst; C8 ?byt] =>
change (rw_cells asegs mm ad [C8 (wz len); C8 (wz (q_first RE (JGF ++ [jgl]))); C8 lst; C8 byt]) in GQC;
replace len with (Z.of_nat (length ((gf ++ [gbl]) ++ tb0 :: tl'))) in GQC by (rewrite !length_app; cbn [length]; lia)
end.
rewrite <- (q_first_app RE (JGF ++ [jgl]) (j0 :: JT')) in GQC by (destruct JGF; discriminate).
rewrite <- (q_last_app RE (JGF ++ [jgl]) (j0 :: JT')) in GQC by discriminate.
unhide BAl. unhide BJl. unhide BSl. subst Bgl.
eapply evt_mono; [eapply (drain_tail ra sp gp t2 a3 _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ s a LB0 FS0 G lo
(j0 :: JT') (JGF ++ [jgl]) ((JGF ++ [jgl]) ++ j0 :: JT') QA [(slot_beg RE 24 jgl, slot_beg RE 24 jgl + 8)] _
(mkQ (tb0 :: tl') tb) (mkQ (gf ++ [gbl]) gb) ((gf ++ [gbl]) ++ tb0 :: tl') Etq Egq)
| cbv beta; intros ms' H'; rewrite (TAILEQ ((gf ++ [gbl]) ++ tb0 :: tl') _ _ eq_refl eq_refl); [exact H'| reflexivity] ].
all: try assumption; try eassumption.
- reflexivity.
- reflexivity.
- unfold QB in *; cbn [q_bytes]; lia.
- unfold QB in *; cbn [q_bytes]; lia.
- apply Forall_app. split; [exact FJGF| constructor; [exact Tjl| constructor]].
- unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [Z.add app].
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact MU.
- constructor; [| constructor]. exists jgl. cbn [fst snd]. split; [exact Tjl| lia].
-
unfold batches_mem. apply batches_mem_nx_app.
+ apply batches_mem_nx_snoc.
* eapply (KEEP _ _ _ _ jgl); [exact BMF| exact FBGF| exact FJGF| exact MU| exact WM|].
intros iv Hiv. cbn in Hiv. destruct Hiv as [E|[E|[E|[E|[E|[]]]]]]; try (left; rewrite <- E; cbn; (first [ clear - SHBg0 TKg SHBg TD TK SPR BND gb jgl tb sp X RE BAND; tauto | tauto ])).
right. rewrite <- E. cbn [fst snd]. split; [exact Tjl|]. split; [| lia]. intros Hin. apply NJl. apply in_app_iff. left; exact Hin.
*
split; [exact BCl|]. split; [| split].
-- eapply u64arr_agree; [| exact BAl|].
++ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Hx _. exact Hx.
++ intros x Hx. rewrite length_map in Hx. pose proof Bwf as (BW1 & BW2 & _). rewrite KBC in BW2.
apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Y1 BW2 BW1 Hx x Pg2 Pg1 PC PK QLT LG LT CEIL' LO JGF gbl gf jgl tb tl' JT' lo sp RE BAND Y2 Pg3 TD TK X; lia | lia ]).
-- eapply hjunk_wmono; [exact BJl| exact WM].
-- eapply rw_cells_agree; [| exact BSl|].
++ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Hx _. exact Hx.
++ intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Y1 Hx x SHBg0 SHBg QLT LG LT CEIL' LO JGF gbl gf jgl tb tl' JT' lo sp RE BAND Y2 Pg1 PK TKg X; lia | lia ]).
+ eapply (KEEP _ _ _ _ jgl); [exact BMT| exact FBT| exact FJT| exact MU| exact WM|].
intros iv Hiv. cbn in Hiv. destruct Hiv as [E|[E|[E|[E|[E|[]]]]]]; try (left; rewrite <- E; cbn; (first [ clear - SHBg0 TKg SHBg TD TK SPR BND gb jgl tb sp X RE BAND; tauto | tauto ])).
right. rewrite <- E. cbn [fst snd]. split; [exact Tjl|]. split; [| lia]. intros Hin. apply NJl. apply in_app_iff. right; exact Hin.
Qed.
End S.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QWRO Qu4g QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QWRO Qu4g QFQR QmP7 QmP7.Mq1 Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc.
Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma gcons_alloc_prim {BAND : Band} : forall a LB FS G RE X c i n,
gcons a LB FS G RE X -> tag_at G c i = Some TCached -> c = class_of n -> 0 <= n <= 2^26 -> from_primary n = true ->
gcons (set_next (N.succ (as_next a)) a) ((APrim (as_next a) n, slot_beg RE c i + rz_size n, n) :: LB) FS
(set_tag c i (TLive (APrim (as_next a) n)) G) RE X.
Proof.
intros a LB FS G RE X c i n GC Ht Ec Hn HP. pose proof GC as GC0. gc_split GC.
set (p := APrim (as_next a) n).
pose proof (retag_at G c i TCached (TLive p) Ht) as RT.
pose proof (tag_at_Some_lt _ _ _ _ Ht) as [I0 _].

assert (FRESH : forall c' i' t, tag_at G c' i' = Some t -> holds p t = false).
{ intros c' i' t Ht' . destruct (holds p t) eqn:E; [| reflexivity]. exfalso.
pose proof (A8b c' i' t (as_next a) n Ht' E). lia. }
assert (NOTIN : ~ In p (map ablk_id LB)).
{ intros Hin. apply in_map_iff in Hin. destruct Hin as ([[q A'] n'] & Eq & Hin). cbn in Eq. subst q.
destruct (A2 p A' n' Hin) as [[(id' & i1 & E & _ & _ & Ht1 & _)|(mb & E & _)] _]; [| discriminate].
pose proof (FRESH _ _ _ Ht1) as F. unfold holds in F. rewrite aptr_eqb_refl' in F. discriminate. }
split; [exact A1|]. split.
{ intros q Aq nq Hq. destruct Hq as [Hq|Hq].
- inversion Hq. subst q Aq nq. split; [| lia]. left. exists (as_next a), i. split; [reflexivity|]. split; [lia|]. split; [exact HP|].
split; [rewrite <- Ec, RT, !Z.eqb_refl; reflexivity|]. split; [exact I0|]. rewrite <- Ec. reflexivity.
- destruct (A2 q Aq nq Hq) as [[H1|H1] H2]; split; [| exact H2| right; exact H1| exact H2].
left. destruct H1 as (id' & i' & E & Hn' & HP' & Ht' & Hi' & HA). exists id', i'. repeat (split; [assumption|]).
split; [| split; [exact Hi'| exact HA]]. rewrite RT.
destruct (Z.eqb_spec (class_of nq) c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb]; try exact Ht'.
exfalso. rewrite EC, EI, Ht in Ht'. discriminate. }
split. { cbn [map ablk_id fst]. constructor; [exact NOTIN| exact A3]. }
split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct (Z.eqb_spec c' c) as [EC|NC]; [destruct (Z.eqb_spec i' i) as [EI|NI]|]; cbn [andb] in Hq.
- inversion Hq. subst q. exists (as_next a), n, (slot_beg RE c i + rz_size n). split; [reflexivity|]. split; [left; reflexivity| subst c'; symmetry; exact Ec].
- destruct (A4 _ _ _ Hq) as (id' & n' & A' & E & Hin & Hc'). exists id', n', A'. split; [exact E|]. split; [right; exact Hin| exact Hc'].
- destruct (A4 _ _ _ Hq) as (id' & n' & A' & E & Hin & Hc'). exists id', n', A'. split; [exact E|]. split; [right; exact Hin| exact Hc']. }
split.
{ intros c' i' q Hq. rewrite RT in Hq. destruct ((c' =? c) && (i' =? i)) eqn:E; [inversion Hq| exact (A5 _ _ _ Hq)]. }
split.
{ intros c' NE. rewrite ncarved_set_tag. cbn [cls set_next as_cls]. apply A6. intros E. apply NE.
destruct (Z.eq_dec c' c) as [->|NC]; [rewrite set_tag_class, E; reflexivity| rewrite set_tag_other_class by exact NC; exact E]. }
split; [exact A7|]. split.
{ intros c1 i1 c2 i2 q u1 u2 H1 H2 K1 K2. rewrite RT in H1, H2.
destruct (aptr_eqb q p) eqn:EQ.
- apply aptr_eqb_true in EQ. subst q.
destruct ((c1 =? c) && (i1 =? i)) eqn:E1.
+ destruct ((c2 =? c) && (i2 =? i)) eqn:E2.
* apply andb_prop in E1 as [E1a E1b]. apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E1a. apply Z.eqb_eq in E1b. apply Z.eqb_eq in E2a. apply Z.eqb_eq in E2b. lia.
* exfalso. rewrite (FRESH _ _ _ H2) in K2. discriminate.
+ exfalso. rewrite (FRESH _ _ _ H1) in K1. discriminate.
- assert (NP1 : forall u, Some u = Some (TLive p) -> holds q u = true -> False).
{ intros u E K. inversion E. subst u. unfold holds in K. rewrite K in EQ. discriminate. }
destruct ((c1 =? c) && (i1 =? i)) eqn:E1; [exfalso; exact (NP1 _ (eq_sym H1) K1)|].
destruct ((c2 =? c) && (i2 =? i)) eqn:E2; [exfalso; exact (NP1 _ (eq_sym H2) K2)|].
exact (A8 _ _ _ _ q _ _ H1 H2 K1 K2). }
split.
{ intros c1 i1 t id1 n1 H1 K1. cbn [as_next set_next]. rewrite RT in H1.
destruct ((c1 =? c) && (i1 =? i)) eqn:E.
- inversion H1. subst t. unfold holds in K1. apply aptr_eqb_true in K1. inversion K1. lia.
- pose proof (A8b _ _ _ _ _ H1 K1). lia. }
cbn [as_reg set_next]. repeat (split; [assumption|]). exact A13.
Qed.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Q13u.
Import QCiC.Mq1. Import QCNF QoNr.Mq0.
Import Qu3b.Mq6.
Import QnRU.Mqf QnRU.

Import QZzg. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Open Scope bv_scope.

Import ListNotations.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac zstep0 := zs.

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
intros f Hf. rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed.

Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia. reflexivity. Qed.

Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.

Ltac mlia := Z.div_mod_to_equations; lia.

Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
split. { apply Z.lor_nonneg. lia. }
pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
rewrite Z.shiftl_mul_pow2 in * by lia.
replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
pose proof (bytes_le_to_Z_range bs) as HR.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec0 i 8).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_u8arr : forall segs m A bs k,
u8arr segs m A bs -> length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
intros segs m A bs k [Hb Hw] HL.
assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
{ clear. induction k as [|k IH]; intros bs HL.
- exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
- destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
- rewrite Hu. exact Hb.
- rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).

Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
intros ws i v Hi Hl. unfold wval, wnth.
pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.

Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
intros ws i j v Hi Hj Hij. unfold wval, wnth.
destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
- pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
- rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.

Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. lia. Qed.

Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
change (2^9)%Z with 512%Z.
set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody y. clear x Hx.
Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
split; intros H; Z.div_mod_to_equations; lia.
Qed.

Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
(0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
apply Z.div_lt_upper_bound; [lia|].
assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed.

End Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C QKBN QV3O QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Q0Do.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QYyZ.Mqc QV3O QjgW.
Import QnRU.Mqk.
Import QlES. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Z.
Context {BAND : Band}.
Variables (a a1 : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Variables (mb msz n : Z).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Hypothesis GC1 : gcons a1 LB0 FS0 G RE X.
Hypothesis ER : as_reg a1 = as_reg a ++ [mkSec mb msz n].
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis MSZ : 4096 <= msz.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Hypothesis AVQ : mb + msz <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= mb.
Hypothesis AVR : forall e, In e (as_reg a) -> mb + msz <= se_beg e \/ se_beg e + se_size e <= mb.
Set Default Proof Using "GC GC1 ER MBP MBK MBC MSZ AVO AVP AVQ AVR".

Definition nbody (x : Z) : Prop := mb + 4096 <= x < mb + msz \/ in_sh (mb + 4096, msz - 4096) x.

Lemma nbody_nmap : forall x, nbody x -> nmap mb msz x.
Proof.
intros x [H|H]; [left; lia| right].
exact (in_sh_sub mb msz (mb + 4096) (msz - 4096) x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) H).
Qed.

Lemma nbody_RSec1 : forall x, nbody x -> fp_RSec a1 RE X x -> False.
Proof.
intros x NB F. pose proof (nbody_nmap x NB) as NM. pose proof kconsts as (_ & _ & _ & _ & KP & _).
destruct F as [H|[H|[H|H]]].
- exact (nmap_RSec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x NM ltac:(left; exact H)).
- exact (nmap_RSec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x NM ltac:(right; left; exact H)).
- destruct H as (e & He & Hx). rewrite ER in He. apply in_app_iff in He. destruct He as [He|[<-|[]]].
+ pose proof (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & E4 & E5 & E6 & _). pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 _]. rewrite <- E4 in M1.
exact (nmap_sec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR e x He ltac:(left; lia) NM).
+ cbn [se_beg] in Hx. destruct NB as [B|B]; [lia|].
pose proof (@in_sh_band BAND (mb + 4096) (msz - 4096) x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(clear - MBK MSZ; lia) ltac:(lia) B) as SB.
unfold kLowEnd, KHI in SB. rewrite KP in Hx. clear - MBK MSZ Hx SB. lia.
- destruct H as (e & He & Hx). rewrite ER in He. apply in_app_iff in He. destruct He as [He|[<-|[]]].
+ exact (nmap_sec a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR e x He ltac:(right; left; exact Hx) NM).
+ cbn [se_beg] in Hx. destruct NB as [B|B].
* pose proof (@in_sh_band BAND mb kPage x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(rewrite KP; lia) ltac:(rewrite KP; clear - MBK MSZ; lia) ltac:(rewrite KP; lia) Hx) as SB.
unfold kLowEnd, KHI in SB. clear - MBK MSZ B SB. lia.
* exact (in_sh_disjoint mb kPage (mb + 4096) (msz - 4096) x ltac:(clear - MBP; Z.div_mod_to_equations; lia) ltac:(clear - MBP; Z.div_mod_to_equations; lia)
ltac:(rewrite KP; lia) ltac:(lia) ltac:(rewrite KP; lia) Hx B).
Qed.

Definition szone (x : Z) : Prop := nbody x \/ fp_RStats RE X x \/ fp_RDepot RE X x \/ band_lo <= x.

Lemma szone_frame : forall m m' W,
munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> szone x) ->
((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RStats RE X x) -> RStats RE X m -> RStats RE X m')
/\ ((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RDepot RE X x) -> RDepot RE X m -> RDepot RE X m')
/\ (RSec a1 LB0 RE X m -> RSec a1 LB0 RE X m').
Proof.
intros m m' W MU WM HW.
assert (AG : forall P : Z -> Prop, (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> P x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx. exact (HP lo hi x Hin Hx Px). }
split; [| split].
- intros NS RS. eapply RStats_frame; [exact RS| exact WM| apply AG]. intros lo hi x Hin Hx Px. exact (NS lo hi x Hin Hx Px).
- intros ND RD. eapply RDepot_frame; [exact RD| exact WM| apply AG]. intros lo hi x Hin Hx Px. exact (ND lo hi x Hin Hx Px).
- intros RSE. eapply RSec_frame; [exact RSE| exact WM| apply AG]. intros lo hi x Hin Hx Px.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|Z]]].
+ exact (nbody_RSec1 x Z Px).
+ exact (fpS_excl _ _ _ _ _ _ GC1 x Z ltac:(right; left; exact Px)).
+ exact (fpD_excl _ _ _ _ _ _ GC1 x Z ltac:(right; left; exact Px)).
+ pose proof (fp_lt_ceil _ _ _ _ _ _ GC1 x ltac:(do 4 right; left; exact Px)). lia.
Qed.

Lemma RSec_hdr_last : forall LB m, RSec a1 LB RE X m ->
rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 (sec_size n)); C8 (Z_to_bv 64 (Z.of_nat (length (as_reg a))))].
Proof.
intros LB m RS. destruct RS as (_ & _ & _ & _ & _ & _ & H7 & _).
specialize (H7 (length (as_reg a)) (mkSec mb msz n)). rewrite ER in H7. rewrite nth_error_app2, Nat.sub_diag in H7 by lia.
destruct (H7 eq_refl) as (H & _ & _). cbn [se_beg se_size se_req] in H. exact H.
Qed.

Lemma nbody_RStats : forall x, nbody x -> fp_RStats RE X x -> False.
Proof. intros x NB F. exact (nmap_RStats a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x (nbody_nmap x NB) F). Qed.
Lemma nbody_RDepot : forall x, nbody x -> fp_RDepot RE X x -> False.
Proof. intros x NB F. exact (nmap_RDepot a LB0 FS0 G RE X GC mb msz MBP MBK MBC MSZ AVO AVP AVQ AVR x (nbody_nmap x NB) F). Qed.
End Z.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QDM6.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q67d QCiC.Mq0 Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QnRU.Mqi QOJv.Mqc Qu3b QTVW.Mq7.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac lia_ar := lazymatch goal with
| |- @eq Z _ _ => lia | |- @eq nat _ _ => lia | |- Z.le _ _ => lia | |- Z.lt _ _ => lia | |- Z.ge _ _ => lia | |- Z.gt _ _ => lia
| |- le _ _ => lia | |- lt _ _ => lia | |- ge _ _ => lia | |- gt _ _ => lia | |- ~ _ => lia | |- _ \/ _ => lia | |- False => lia | |- _ -> _ => lia
end.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation TT := (fun (_ : evA) (_ : ansA) => True).

Definition prel (c : Z) (a a' : AState) : Prop :=
(forall c', c' <> c -> cls a' c' = cls a c') /\ as_cache_inited a' = as_cache_inited a
/\ as_reg a' = as_reg a /\ as_next a' = as_next a /\ c_count (cls a' c) = c_count (cls a c).

Lemma prel_refl : forall c a, prel c a a.
Proof. intros. repeat split; reflexivity. Qed.
Lemma prel_trans : forall c a1 a2 a3, prel c a1 a2 -> prel c a2 a3 -> prel c a1 a3.
Proof. intros c a1 a2 a3 (A & B & C & D & E) (A' & B' & C' & D' & E'). repeat split; try congruence. intros c' H. rewrite A' by exact H. apply A. exact H. Qed.
Lemma prel_set_cls : forall c a x, c_count x = c_count (cls a c) -> prel c a (set_cls c x a).
Proof. intros c a x E. repeat split; try reflexivity. { intros c' H. apply cls_set_cls_ne. exact H. } rewrite cls_set_cls_eq. exact E. Qed.

Section Model.
Variable L : ALay.
Ltac tret_ok := apply tall_ret; cbn.

Lemma ensure_fa_prel a c nf : tall TT (okrel (fun r => prel c a (snd r))) (ensure_fa L a c nf).
Proof.
unfold ensure_fa. destruct (_ <=? _); [tret_ok; apply prel_refl|]. destruct (_ <? _); [exact I|].
apply tall_vis. intros x _. destruct (fixed_ok x); tret_ok; [apply prel_set_cls; reflexivity| apply prel_refl].
Qed.

Lemma populate_prel a c req : tall TT (okrel (fun r => prel c a (snd r))) (populate L a c req).
Proof.
unfold populate. eapply tall_bind_ok with (P1 := fun r => prel c a (snd r)).
{ destruct (_ <? _); [| tret_ok; apply prel_refl]. destruct (_ <? _); [exact I|].
apply tall_vis. intros x _. destruct (fixed_ok x); tret_ok; [apply prel_set_cls; reflexivity| apply prel_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
eapply tall_bind_ok with (P1 := fun r => prel c a (snd r)).
{ eapply tall_mono; [apply ensure_fa_prel|]. intros [[b s2]| |w]; cbn; [| exact (fun x => x)| exact (fun x => x)]. intros H2. eapply prel_trans; eauto. }
intros [ok2 s2] H2. cbn in H2. destruct ok2; cbn [negb]; tret_ok; [| exact H2]. eapply prel_trans; [exact H2| apply prel_set_cls; reflexivity].
Qed.

Lemma get_from_allocator_prel a c k : tall TT (okrel (fun r => prel c a (snd r))) (get_from_allocator L a c k).
Proof.
unfold get_from_allocator. eapply tall_bind_ok with (P1 := fun r => prel c a (snd r)).
{ destruct (_ <? _); [apply populate_prel| tret_ok; apply prel_refl]. }
intros [ok s1] H1. cbn in H1. destruct ok; cbn [negb]; [| tret_ok; exact H1].
destruct (_ <? _); [exact I|]. tret_ok. eapply prel_trans; [exact H1| apply prel_set_cls; reflexivity].
Qed.
End Model.

Fixpoint retag_list (c : Z) (l : list Z) (t : stag) (G : ghost) : ghost :=
match l with [] => G | i :: l' => set_tag c i t (retag_list c l' t G) end.

Lemma retag_list_other_class : forall c l t G c', c' <> c -> retag_list c l t G c' = G c'.
Proof. intros c l t G c' NE. induction l as [|i l IH]; cbn; [reflexivity|]. rewrite set_tag_other_class by exact NE. exact IH. Qed.

Lemma ncarved_retag_list : forall c l t G c', ncarved (retag_list c l t G) c' = ncarved G c'.
Proof. intros c l t G c'. induction l as [|i l IH]; cbn; [reflexivity|]. rewrite ncarved_set_tag. exact IH. Qed.

Lemma tag_at_retag_list_out : forall c l t G c' i', (c' <> c \/ ~ In i' l) -> Forall (fun i => 0 <= i) l ->
tag_at (retag_list c l t G) c' i' = tag_at G c' i'.
Proof.
intros c l t G c' i' H NN. induction l as [|i l IH]; cbn; [reflexivity|]. inversion NN; subst.
rewrite tag_at_set_tag_ne; [apply IH; [| assumption]| assumption|].
- destruct H as [H|H]; [left; exact H| right; intros K; apply H; right; exact K].
- destruct H as [H|H]; [left; exact H| right; intros ->; apply H; left; reflexivity].
Qed.

Lemma tag_at_retag_list_in : forall c l t G i, In i l -> Forall (fun i => 0 <= i) l ->
(forall j, In j l -> exists t0, tag_at G c j = Some t0) ->
tag_at (retag_list c l t G) c i = Some t.
Proof.
intros c l t G i Hin NN OLD. induction l as [|i0 l IH]; [destruct Hin|]. cbn. inversion NN; subst.
assert (OLD' : forall j, In j l -> exists t0, tag_at G c j = Some t0) by (intros j Hj; apply OLD; right; exact Hj).
destruct (Z.eq_dec i i0) as [->|NE].
-
assert (E : exists t0, tag_at (retag_list c l t G) c i0 = Some t0).
{ destruct (in_dec Z.eq_dec i0 l) as [Hl|Hl].
- exists t. apply IH; assumption.
- rewrite tag_at_retag_list_out; [apply OLD; left; reflexivity| right; exact Hl| assumption]. }
destruct E as [t0 Ht0]. exact (tag_at_set_tag_eq _ c i0 t t0 Ht0).
- destruct Hin as [->|Hin]; [congruence|]. rewrite tag_at_set_tag_ne; [apply IH; assumption| assumption| right; exact NE].
Qed.

Lemma same_tags_retag_list : forall f c l t G,
f t = false -> Forall (fun i => 0 <= i) l -> (forall j, In j l -> exists t0, tag_at G c j = Some t0 /\ f t0 = false) ->
same_tags f G (retag_list c l t G).
Proof.
intros f c l t G Hf NN OLD c' i' u Hu. destruct (Z.eq_dec c' c) as [->|NE].
- destruct (in_dec Z.eq_dec i' l) as [Hin|Hout].
+ rewrite (tag_at_retag_list_in c l t G i' Hin NN ltac:(intros j Hj; destruct (OLD j Hj) as [t0 [H _]]; exists t0; exact H)).
destruct (OLD i' Hin) as [t0 [H0 F0]]. rewrite H0. split; intros E; inversion E; subst; congruence.
+ rewrite tag_at_retag_list_out; [tauto| right; exact Hout| exact NN].
- rewrite tag_at_retag_list_out; [tauto| left; exact NE| exact NN].
Qed.

Lemma gcons_retag_list {BAND : Band} : forall a LB FS G RE X c l t,
gcons a LB FS G RE X -> Forall (fun i => 0 <= i) l ->
(forall j, In j l -> exists t0, tag_at G c j = Some t0 /\ is_live t0 = false) ->
(forall q, holds q t = false) -> is_live t = false ->
gcons a LB FS (retag_list c l t G) RE X.
Proof.
intros a LB FS G RE X c l t GC NN OLD NH NL. induction l as [|i l IH]; cbn; [exact GC|]. inversion NN; subst.
assert (OLD' : forall j, In j l -> exists t0, tag_at G c j = Some t0 /\ is_live t0 = false) by (intros j Hj; apply OLD; right; exact Hj).
specialize (IH ltac:(assumption) OLD').
assert (E : exists t0, tag_at (retag_list c l t G) c i = Some t0 /\ is_live t0 = false).
{ destruct (in_dec Z.eq_dec i l) as [Hl|Hl].
- exists t. split; [| exact NL]. apply tag_at_retag_list_in; [exact Hl| assumption| intros j Hj; destruct (OLD' j Hj) as [t0 [H _]]; exists t0; exact H].
- rewrite tag_at_retag_list_out; [apply OLD; left; reflexivity| right; exact Hl| assumption]. }
destruct E as [t0 [Ht0 NL0]]. eapply gcons_retag_nonlive; [exact IH| exact Ht0| exact NL0| exact NH| exact NL].
Qed.

Lemma gstep_retag_cached {BAND : Band} : forall RE X a G c l,
Forall (fun i => 0 <= i) l -> (forall j, In j l -> tag_at G c j = Some TFree) ->
gstep RE X a a G (retag_list c l TCached G).
Proof.
intros RE X a G c l NN OLD. split; [| split; [| split]].
- apply same_tags_retag_list; [reflexivity| exact NN| intros j Hj; exists TFree; split; [apply OLD; exact Hj| reflexivity]].
- apply same_tags_retag_list; [reflexivity| exact NN| intros j Hj; exists TFree; split; [apply OLD; exact Hj| reflexivity]].
- intros c' i' t Ht. destruct (Z.eq_dec c' c) as [->|NE]; [destruct (in_dec Z.eq_dec i' l) as [Hin|Hout]|].
+ exists TCached. apply tag_at_retag_list_in; [exact Hin| exact NN| intros j Hj; exists TFree; apply OLD; exact Hj].
+ exists t. rewrite tag_at_retag_list_out; [exact Ht| right; exact Hout| exact NN].
+ exists t. rewrite tag_at_retag_list_out; [exact Ht| left; exact NE| exact NN].
- intros LB FS GC. apply gcons_retag_list; [exact GC| exact NN| intros j Hj; exists TFree; split; [apply OLD; exact Hj| reflexivity]| intros q; reflexivity| reflexivity].
Qed.

Lemma gstep_ext {BAND : Band} : forall RE X a a' G,
(forall c, c_alloc_user (cls a' c) = c_alloc_user (cls a c)) -> (forall c, c_mapped_user (cls a' c) = c_mapped_user (cls a c)) ->
as_reg a' = as_reg a -> as_next a' = as_next a -> gstep RE X a a' G G.
Proof. intros RE X a a' G EA EM ER EN. apply gstep_state. intros LB FS GC. eapply gcons_ext; [exact GC| exact EA| exact EM| exact ER| rewrite EN; reflexivity]. Qed.

Lemma gstep_populate {BAND : Band} : forall RE X a a' G c K K' k,
1 <= c < kNumClasses -> prel c a a' ->
cr_pure a G c K -> cr_pure a' (gappend c (repeat TFree k) G) c K' ->
gstep RE X a a' G (gappend c (repeat TFree k) G).
Proof.
intros RE X a a' G c K K' k Hc (EO & EI & ER & EN & _) PU PU'.
pose proof kconsts as (_ & _ & _ & K32 & _ & _ & KM & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5).
destruct PU' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & H4 & H5).
rewrite gappend_class, length_app, repeat_length in H1.
assert (NL : Forall (fun t => is_live t = false /\ forall q, holds q t = false) (repeat TFree k)).
{ apply Forall_forall. intros t Ht. apply repeat_spec in Ht. subst t. split; [reflexivity| intros q; reflexivity]. }
split; [| split; [| split]].
- apply same_tags_gappend. apply Forall_forall. intros t Ht. apply repeat_spec in Ht. subst t. reflexivity.
- apply same_tags_gappend. apply Forall_forall. intros t Ht. apply repeat_spec in Ht. subst t. reflexivity.
- intros c' i' t Ht. exists t. apply tag_at_gappend_Some_old. exact Ht.
- intros LB FS GC. eapply gcons_gappend; [exact GC| exact Hc| exact NL| exact EO| unfold ncarved; exact G1| rewrite repeat_length; lia| lia| lia| exact H4| exact H5| exact ER| exact EN].
Qed.

Lemma In_skipn_In {A} : forall n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right; exact H. Qed.
Lemma In_firstn_In {A} : forall n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left; exact H. Qed.
Lemma NoDup_firstn {A} : forall n (l : list A), List.NoDup l -> List.NoDup (firstn n l).
Proof. intros n l H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_r _ _ H). Qed.
Lemma NoDup_skipn {A} : forall n (l : list A), List.NoDup l -> List.NoDup (skipn n l).
Proof. intros n l H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_l _ _ H). Qed.
Lemma NoDup_firstn_skipn {A} : forall n (l : list A) x, List.NoDup l -> In x (firstn n l) -> In x (skipn n l) -> False.
Proof.
intros n l x H H1 H2. rewrite <- (firstn_skipn n l) in H. induction (firstn n l) as [|y f IH]; [destruct H1|].
cbn in H. apply List.NoDup_cons_iff in H as [Hy Hf]. destruct H1 as [->|H1]; [apply Hy; apply in_or_app; right; exact H2| exact (IH Hf H1)].
Qed.

Lemma count_tag_retag_list : forall f c l t t0 G,
List.NoDup l -> Forall (fun i => 0 <= i) l -> (forall j, In j l -> tag_at G c j = Some t0) ->
count_tag f (retag_list c l t G c) = count_tag f (G c) - (if f t0 then Z.of_nat (length l) else 0) + (if f t then Z.of_nat (length l) else 0).
Proof.
intros f c l t t0 G ND NN OLD. induction l as [|i l IH]; cbn -[Z.of_nat]; [destruct (f t), (f t0); lia|].
inversion ND; subst. inversion NN; subst.
assert (OLD' : forall j, In j l -> tag_at G c j = Some t0) by (intros j Hj; apply OLD; right; exact Hj).
specialize (IH ltac:(assumption) ltac:(assumption) OLD').
pose proof (OLD i ltac:(left; reflexivity)) as Ht0.
assert (Hi : tag_at (retag_list c l t G) c i = Some t0) by (rewrite tag_at_retag_list_out; [exact Ht0| right; assumption| assumption]).
rewrite set_tag_class.
rewrite (count_tag_list_set f (retag_list c l t G c) (Z.to_nat i) t t0).
- rewrite IH. destruct (f t), (f t0); cbn [length]; lia.
- unfold tag_at in Hi. destruct (Z.ltb_spec i 0); [discriminate|]. exact Hi.
Qed.

Lemma cr_pure_move : forall a G c K k a',
cr_pure a G c K -> 1 <= c <= 31 -> 0 <= k <= c_num_freed (cls a c) -> k <= max_count c -> c_count (cls a c) = 0 ->
as_cache_inited a' = true ->
cls a' c = set_count k (set_num_freed (c_num_freed (cls a c) - k) (cls a c)) ->
let FL := pk_fl K in let nfk := Z.to_nat (c_num_freed (cls a c) - k) in
cr_pure a' (retag_list c (skipn nfk FL) TCached G) c (mkPK (firstn nfk FL) (skipn nfk FL)).
Proof.
intros a G c K k a' PU Hc Hk Hkm CNT EI Ea FL nfk.
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _).
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
fold FL in P1, P3, P5.
assert (NNF : Forall (fun i => 0 <= i) FL).
{ apply Forall_forall. intros i Hi. exact (proj1 (tag_at_Some_lt _ _ _ _ (P5 i Hi))). }
assert (NN : Forall (fun i => 0 <= i) (skipn nfk FL)).
{ apply Forall_forall. intros i Hi. exact (proj1 (List.Forall_forall _ _) NNF i (In_skipn_In _ _ _ Hi)). }
assert (OLD : forall j, In j (skipn nfk FL) -> tag_at G c j = Some TFree) by (intros j Hj; apply P5; exact (In_skipn_In _ _ _ Hj)).
assert (LF : length (firstn nfk FL) = nfk) by (rewrite length_firstn; lia).
assert (LS : Z.of_nat (length (skipn nfk FL)) = k) by (rewrite length_skipn; lia).
unfold cr_pure. rewrite Ea, EI. cbn [pk_fl pk_ca set_count set_num_freed c_num_freed c_count c_mapped_fa c_alloc_user c_mapped_user].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia_ar.
- apply NoDup_firstn. exact P3.
- apply NoDup_skipn. exact P3.
- intros i Hi. rewrite tag_at_retag_list_out; [apply P5; exact (In_firstn_In _ _ _ Hi)| | exact NN].
right. intros Hi'. exact (NoDup_firstn_skipn _ _ _ P3 Hi Hi').
- intros i Hi. apply tag_at_retag_list_in; [exact Hi| exact NN| intros j Hj; exists TFree; apply OLD; exact Hj].
- rewrite (count_tag_retag_list _ c _ TCached TFree G (NoDup_skipn _ _ P3) NN OLD). cbn. rewrite P7. lia.
- rewrite (count_tag_retag_list _ c _ TCached TFree G (NoDup_skipn _ _ P3) NN OLD). cbn. rewrite P8, CNT. lia.
- pose proof (ncarved_retag_list c (skipn nfk FL) TCached G c) as NC. unfold ncarved in NC. rewrite NC. exact G1.
Qed.

Lemma u32arr_split : forall m A ws1 ws2,
u32arr asegs m A (ws1 ++ ws2) -> u32arr asegs m A ws1 /\ u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
intros m A ws1 ws2 [B W]. rewrite u32s_app in B. apply (proj1 (bytes_at_app _ _ _ _ _)) in B as [B1 B2].
rewrite u32s_length in B2. destruct W as (W0 & W1 & W2). rewrite length_app in W1, W2.
replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) in B2 by lia.
split; split; [exact B1| | exact B2|]; (split; [lia|]; split; [lia|]); intros i Hi.
- apply W2. lia.
- replace (A + 4 * Z.of_nat (length ws1) + i) with (A + (4 * Z.of_nat (length ws1) + i)) by lia. apply W2. lia.
Qed.

Lemma cr_user_retag : forall a a' G G' RE m c,
cr_user a G RE m c ->
(forall i t', tag_at G' c i = Some t' -> tag_prim t' = true -> exists t, tag_at G c i = Some t /\ tag_prim t = true) ->
c_alloc_user (cls a' c) = c_alloc_user (cls a c) -> c_mapped_user (cls a' c) = c_mapped_user (cls a c) ->
cr_user a' G' RE m c.
Proof.
intros a a' G G' RE m c (SL & UT & SS & US & UJ) TG EA EM. unfold cr_user. rewrite EA, EM.
split; [| split; [exact UT| split; [| split; [exact US| exact UJ]]]].
- intros i t' Ht' Hp'. destruct (TG i t' Ht' Hp') as (t & Ht & Hp). exact (SL i t Ht Hp).
- intros i t' Ht' Hp'. destruct (TG i t' Ht' Hp') as (t & Ht & Hp). exact (SS i t Ht Hp).
Qed.

Lemma retag_cached_prim : forall c l G i t', Forall (fun i => 0 <= i) l -> (forall j, In j l -> tag_at G c j = Some TFree) ->
tag_at (retag_list c l TCached G) c i = Some t' -> tag_prim t' = true ->
exists t, tag_at G c i = Some t /\ tag_prim t = true.
Proof.
intros c l G i t' NN OLD Ht' Hp'. destruct (in_dec Z.eq_dec i l) as [Hin|Hout].
- exists TFree. split; [apply OLD; exact Hin| reflexivity].
- exists t'. rewrite tag_at_retag_list_out in Ht'; [| right; exact Hout| exact NN]. split; [exact Ht'| exact Hp'].
Qed.

Lemma gfa_close {BAND : Band} : forall (aX a'' : AState) (GX : ghost) RE X (m m'' : mem) c k (K : Z -> pcls) j1 j2 j3 j4 CH',
let x := cls aX c in let nf := c_num_freed x in let FL := pk_fl (K c) in let nfk := Z.to_nat (nf - k) in
let G' := retag_list c (skipn nfk FL) TCached GX in
let fb := fa_beg (ae_L RE) c in
rlay_ok RE X -> 1 <= c <= 30 -> 1 <= k <= nf -> k <= max_count c -> c_count x = 0 -> as_cache_inited aX = true ->
cls a'' c = set_count k (set_num_freed (nf - k) x) -> (forall c0, c0 <> c -> cls a'' c0 = cls aX c0) -> as_cache_inited a'' = true ->
hjunk m (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, GX c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep aX GX RE X m c0 (K c0)) ->
cr_pure aX GX c (K c) ->
wmono asegs m m'' ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m m'') ->
agree_on asegs (uzone RE c) m m'' ->
rw_cells asegs m'' (ri_addr RE c)
[C8 (wz 0); CB 8 j1; C8 (wz (nf - k)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0); C8 (wz (c_mapped_user x));
C8 (wz 0); CB 4 j2; C1 (Z_to_bv 8 0); CB 3 j3; CB 56 j4] ->
rw_cells asegs m'' (pc_addr X c) [C4 (wz k); C4 (wz (bmax c)); C8 (wz (bsize c))] ->
u32arr asegs m'' (pc_addr X c + 16) CH' -> length CH' = 16%nat ->
(forall j, (j < Z.to_nat k)%nat -> nth_error CH' j = nth_error (map (fun i => wz (coff c i)) FL) (nfk + j)%nat) ->
u32arr asegs m'' fb (map (fun i => wz (coff c i)) FL) ->
hjunk m (fb + 4 * nf) (fb + c_mapped_fa x) ->
cr_user aX GX RE m c ->
hjunk m (SH fb) (SH fb + 67108864) ->
RPrim a'' G' RE X m''.
Proof.
intros until CH'; intros x nf FL nfk G' fb RL Hc Hk Hkm CNT EI Ea EO EI'' HJS GNE HCall PU WM OTH AGU RI PC ACH LCH PR FA FJ HU FS.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof PU as (P1 & P2 & P3 & P4 & P5 & _). fold FL in P1, P3, P5.
assert (NNF : Forall (fun i => 0 <= i) FL).
{ apply Forall_forall. intros i Hi. exact (proj1 (tag_at_Some_lt _ _ _ _ (P5 i Hi))). }
assert (NN : Forall (fun i => 0 <= i) (skipn nfk FL)).
{ apply Forall_forall. intros i Hi. exact (proj1 (List.Forall_forall _ _) NNF i (In_skipn_In _ _ _ Hi)). }
assert (OLD : forall j, In j (skipn nfk FL) -> tag_at GX c j = Some TFree) by (intros j Hj; apply P5; exact (In_skipn_In _ _ _ Hj)).
assert (EG : forall c0, c0 <> c -> G' c0 = GX c0) by (intros c0 NE; apply retag_list_other_class; exact NE).
assert (LK : (length FL = nfk + Z.to_nat k)%nat) by (subst nfk nf x; lia).
assert (NFK : Z.of_nat nfk = nf - k) by (subst nfk nf x; lia).
exists (fun c0 => if c0 =? c then mkPK (firstn nfk FL) (skipn nfk FL) else K c0).
split; [eapply hjunk_wmono; [exact HJS| exact WM]|]. split.
{ intros c0 NE0. apply GNE. destruct (Z.eq_dec c0 c) as [->|NE]; [| rewrite <- (EG c0 NE); exact NE0].
intros E. apply NE0. apply length_zero_iff_nil. pose proof (ncarved_retag_list c (skipn nfk FL) TCached GX c) as NC.
unfold ncarved in NC. unfold G'. rewrite <- Nat2Z.inj_iff. rewrite NC, E. reflexivity. }
intros c0 Hc0. destruct (Z.eqb_spec c0 c) as [->|NE].
2:{ eapply class_rep_ext; [| apply EO; exact NE| rewrite EI, EI''; reflexivity| apply EG; exact NE].
eapply class_rep_agree; [apply HCall; [exact Hc0| exact NE]| rewrite K32 in Hc0; exact Hc0| apply OTH; [exact Hc0| exact NE]]. }
apply class_rep_split. split; [| split].
-
unfold cr_cells. rewrite Ea, EI''. cbn [pk_ca set_count set_num_freed c_count c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
split; [exists j1, j2, j3, j4; exact RI|]. split; [exact PC|].
exists CH'. split; [exact ACH|]. split; [exact LCH|].
intros j Hj. rewrite length_skipn in Hj. rewrite PR by lia.
rewrite nth_error_map. rewrite <- (firstn_skipn nfk FL) at 1. rewrite nth_error_app2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (nfk + j - Nat.min nfk (length FL))%nat with j by lia.
destruct (nth_error (skipn nfk FL) j) as [v|] eqn:E; cbn [option_map].
+ rewrite (nth_error_nth _ _ _ E). reflexivity.
+ exfalso. apply nth_error_None in E. rewrite length_skipn in E. lia.
-
apply (cr_pure_move aX GX c (K c) k a''); [exact PU| lia| lia| exact Hkm| exact CNT| exact EI''| exact Ea].
-
intros _. rewrite Ea. cbn [pk_fl set_count set_num_freed c_num_freed c_mapped_fa c_alloc_user c_mapped_user].
assert (SPL := u32arr_split m'' fb (map (fun i => wz (coff c i)) (firstn nfk FL)) (map (fun i => wz (coff c i)) (skipn nfk FL))
ltac:(rewrite <- map_app, firstn_skipn; exact FA)).
destruct SPL as [FA1 FA2]. rewrite length_map, length_firstn in FA2.
split; [exact FA1|]. split.
{ eapply hjunk_merge; [| eapply hjunk_wmono; [exact FJ| exact WM]].
pose proof (u32arr_hjunk m'' _ _ FA2) as J. rewrite length_map, length_skipn in J.
replace (fb + 4 * Z.of_nat (Nat.min nfk (length FL))) with (fb + 4 * (nf - k)) in J by lia.
replace (fb + 4 * (nf - k) + 4 * Z.of_nat (length FL - nfk)) with (fb + 4 * nf) in J by lia.
apply J. pose proof (rlay_prim_facts RE X RL) as (_ & PK1 & _). rewrite ?KHI_eq in PK1. unfold fb, fa_beg, reg_beg. rewrite KR, KO. unfold prim_lo in PK1. nia. }
split; [| rewrite KS; replace 536870912 with (8 * 67108864) by reflexivity; rewrite SH_plus8; eapply hjunk_wmono; [exact FS| exact WM]].
eapply (cr_user_retag aX a'' GX G'); [| intros i t' Ht' Hp'; exact (retag_cached_prim c _ GX i t' NN OLD Ht' Hp')| rewrite Ea; reflexivity| rewrite Ea; reflexivity].
eapply cr_user_agree; [exact PU| exact HU| lia| exact AGU].
Qed.

Lemma ri_stat_recast : forall m A c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 (w : word) j4t,
rw_cells asegs m A [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; C8 w; CB 48 j4t] ->
rw_cells asegs m A [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; CB 56 (le8 w ++ j4t)].
Proof.
intros until j4t; intros H. pose proof H as [[WF _] _]. cbn [cells_wf cell_wf] in WF.
eapply rw_cells_recast'; [exact H| |].
- cbn [cells_wf cell_wf]. rewrite length_app, length_le8. repeat split; try tauto. lia.
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma RPrimL_set_mutex_stk {BAND : Band} : forall a G RE X m m' cl v w lo1 hi1,
RPrimL a G RE X m cl v -> rlay_ok RE X -> band_lo <= lo1 ->
munch [(lo1, hi1); (ri_addr RE cl, ri_addr RE cl + 8)] m m' -> wmono asegs m m' ->
rw_cells asegs m' (ri_addr RE cl) [C8 (Z_to_bv 64 w)] ->
RPrimL a G RE X m' cl w.
Proof.
intros a G RE X m m' cl v w lo1 hi1 RP RL CE MU WM HEAD. pose proof RP as (K & HJ & GNE & HC & Hcl & HCL).
pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hcl.
assert (FWc : Forall (wc_ok RE X cl) [(lo1, hi1); (ri_addr RE cl, ri_addr RE cl + 8)]).
{ constructor; [cbn; left; exact CE|]. constructor; [| constructor]. cbn -[fp_cls]. do 2 right. intros z Hz. left. lia. }
eapply (RPrimL_reclose a a G G RE X m m' cl K (K cl) w RL HJ GNE HC ltac:(rewrite K32; exact Hcl));
[intros; reflexivity| reflexivity| intros; reflexivity| intros NE; exact (proj1 (GNE cl NE))| exact WM
| eapply agree_other_classes; [exact RL| exact Hcl| exact MU| exact WM| exact FWc] |].
eapply class_repL_agree_but_mutex; [exact RL| exact HCL| exact Hcl| | exact HEAD].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x [FX NX] Hx. cbn. split; [| split; [exact NX| exact I]].
pose proof (fp_cls_lt_ceil RE X RL cl x Hcl FX). lia.
Qed.
End Mqd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1 QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QKTr Q6sh.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QpME.Mq7 QjgW.
Import QQwg.
Import QmP7.Mq1 QYyZ.Mq8 QYyZ.Mqc.
Import QmvA.Mq5.
Import QFd5.Mq7.
Import QlES.
Import ListNotations. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma sec_size_facts : forall n, 0 <= n <= 2^26 -> from_primary n = false ->
65536 < sec_size n /\ sec_size n <= 2^26 + 4104 /\ sec_size n mod 8 = 0
/\ sec_map_size n = sec_size n + 4095 - (sec_size n + 4095) mod 4096 + 4096
/\ sec_map_size n mod 4096 = 0 /\ sec_size n + 4096 <= sec_map_size n < sec_size n + 8192.
Proof.
intros n Hn HP. unfold from_primary in HP. apply Z.leb_gt in HP. unfold sec_size, sec_map_size, needed, kMaxSize in *.
unfold round_up, kPage in *.
assert (R1 : rz_size n <= 2048 /\ (n <= 64512 -> rz_size n <= 1024) /\ (64512 < n -> rz_size n = 2048)).
{ unfold rz_size. repeat match goal with |- context [n <=? ?c] => destruct (Z.leb_spec0 n c) end; lia. }
destruct (Z.le_gt_cases n 64512) as [LE|GT].
{ exfalso. destruct R1 as (_ & R & _). specialize (R LE). Z.div_mod_to_equations. lia. }
destruct R1 as (_ & _ & R). rewrite (R GT) in *. replace (Z.max n 8) with n in * by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma avoids_In : forall b n avoid iv, avoids b n avoid = true -> In iv avoid -> b + n <= fst iv \/ snd iv <= b.
Proof.
intros b n avoid iv H Hin. unfold avoids in H. rewrite forallb_forall in H. specialize (H iv Hin).
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma avoid_facts : forall a b n, avoid_covers RE X -> 0 < n -> (0 < b /\ b + n <= 2^64) -> avoids b n (avoid_of (ae_L RE) a) = true ->
(appr b n /\ b + n <= band_lo) /\ (forall o, In o (rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b)
/\ (b + n <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= b) /\ (b + n <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= b)
/\ (forall e, In e (as_reg a) -> b + n <= se_beg e \/ se_beg e + se_size e <= b).
Proof.
intros a b n AVC Hn Hb AV.
assert (COV : forall o, In o (a_hull :: (0x7fff7000, KHI - 0x7fff7000) :: (band_lo, 2^64 - band_lo)
:: (prim_lo RE, 2^37 + 0x1000) :: (ptrarr_lo RE, 0x800000) :: rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b).
{ intros o Ho. destruct (AVC o Ho) as (iv & Hiv & I1 & I2).
destruct (avoids_In b n _ iv AV ltac:(unfold avoid_of; apply in_or_app; left; exact Hiv)); lia. }
split; [| split; [| split; [| split]]].
- pose proof (COV _ ltac:(left; reflexivity)) as H1. pose proof (COV _ ltac:(right; left; reflexivity)) as H2.
pose proof (COV _ ltac:(do 2 right; left; reflexivity)) as H3. cbn [fst snd] in H1, H2, H3. unfold KHI in *. lia.
- intros o Ho. apply COV. do 5 right. exact Ho.
- pose proof (COV _ ltac:(do 3 right; left; reflexivity)) as C. cbn [fst snd] in C. exact C.
- pose proof (COV _ ltac:(do 4 right; left; reflexivity)) as C. cbn [fst snd] in C. exact C.
- intros e He. destruct (avoids_In b n _ (sec_iv e) AV ltac:(unfold avoid_of; apply in_or_app; right; apply in_map; exact He)); unfold sec_iv in *; cbn [fst snd] in *; lia.
Qed.

Lemma fp_RSec_lt_ceil : forall a LB FS G x, gcons a LB FS G RE X -> fp_RSec a RE X x -> x < band_lo.
Proof.
intros a LB FS G x GC Fx. pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (_ & _ & _ & _ & KP & _).
idtac. destruct Fx as [H|[H|[H|H]]].
- destruct H as [H1 H2]; cbn [fst snd] in *. unfold A_INSTANCE in *. lia.
- destruct H as [H1 H2]; cbn [fst snd] in *. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & _ & PH & _). unfold ptrarr_hi, ptrarr_lo in *. idtac. lia.
- destruct H as (e & He & H). pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _). idtac.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1. lia.
- destruct H as (e & He & H). pose proof (hdr_band _ _ _ _ _ _ GC e x He H). lia.
Qed.

Definition ltail_W (sp parr nch mb : Z) : list (Z * Z) :=
[(sp - 96, sp); (977864, 978480); (parr + 8 * nch, parr + 8 * nch + 8); (mb, mb + 32)].

Definition ltail_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo parr nch nres mb msz sz : Z) (reg : list secent) (m : mem) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (pj' : list byte),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (mb + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (ltail_W (bv_unsigned sp) parr nch mb) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' 977864 [C8 (wz nres); C8 (wz (nch + 1))]
/\ wjunk m' 977880 69
/\ rw_cells asegs m' 978432 [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)]
/\ wjunk m' 978440 5
/\ u64arr asegs m' parr (map (fun e => wz (se_beg e)) reg ++ [wz mb])
/\ rw_cells asegs m' (parr + 8 * (nch + 1)) [CB (Z.to_nat (8 * (nres - nch - 1))) pj']
/\ rw_cells asegs m' mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz nch)].

Lemma largealloc_tail : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(rax t0 t1 t2 a1 a2 a4 a5 a6 a7 s4x s6x s7x s8x s9x t3 t4 t5 t6 : word) (m : mem)
(lo parr nch nres mb msz sz E : Z) (reg : list secent) (junk8 pj : list byte),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -96) -> lo <= bv_unsigned sp - 96 ->
rw_cells asegs m (bv_unsigned sp + -96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
ro_cells asegs m 977816 [C8 (wz 4096); C8 (wz parr)] ->
rw_cells asegs m 977864 [C8 (wz nres); C8 (wz nch)] ->
wjunk m 977880 69 ->
rw_cells asegs m 978432 [C4 (wz 1); C4 (wz 0)] ->
wjunk m 978440 5 ->
u64arr asegs m parr (map (fun e => wz (se_beg e)) reg) -> nch = Z.of_nat (length reg) ->
rw_cells asegs m (parr + 8 * nch) [CB (Z.to_nat (8 * (nres - nch))) pj] -> nch < nres -> nres <= 2^20 ->
0x647000 <= parr -> parr + 8388608 <= lo ->
rw_cells asegs m mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz 0)] ->
0x647000 <= mb -> mb + msz <= lo -> 4096 <= msz -> (mb + msz <= parr \/ parr + 8388608 <= mb) ->
0 <= E < 2^64 -> 16 <= Z.lxor E 63 <= 26 ->
evt asegs (ltail_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo parr nch nres mb msz sz reg m)
(MS (mkR rax (wz (bv_unsigned sp + -96)) gp (wz A_TP) t0 t1 t2 (wz 978440) (wz 977816)
(wz (mb + 4096)) a1 a2 (wz nch) a4 a5 a6 a7 (wz msz) (wz E) s4x (wz mb) s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F (wz 0x44008) fc None m (seg_rom asegs)).
Proof.
intros until pj; intros MI ST LO FR K43 I1 I2 I3 I4 P1 NCH P2 NLT NMX PK PH ZBh MK MH MSZ MPD HE HIDX.
assert (LM : Z.of_nat (length (map (fun e => wz (se_beg e)) reg)) = nch) by (rewrite length_map; lia).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (stk_bound _ _ _ _ ST) as SB0 || idtac.
destruct (wjunk69_open m _ I2) as (w0 & w1 & w2 & w3 & w4 & bsl & J1 & BSL & LBSL). clear I2. change (977880 + 40) with 977920 in BSL.
destruct (wjunk5_open m _ I4) as (g0 & g1 & g2 & g3 & g4 & GS). clear I4.
set (idx := Z.lxor E 63) in HIDX.
pose proof (munch_refl (ltail_W (bv_unsigned sp) parr nch mb) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold ltail_W in MU.

replace (Z.to_nat (8 * (nres - nch))) with (8 + Z.to_nat (8 * (nres - nch - 1)))%nat in P2 by lia.
destruct (rw_cells_CB_split m _ _ _ _ P2) as [P2a P2b]. clear P2. change (Z.of_nat 8) with 8 in P2b.
step.
step.
rewrite (unsigned_lit E) by lia. fold idx.
step.
step. step.
rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
replace (parr + nch * 8) with (parr + 8 * nch) by lia.
remember (parr + 8 * nch) as Q eqn:EQ.
step.
step. step. step. step.
step. step.
step.
stp.
step. step.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' : word, ms1 = MS (@bvmap_set 5 word 12 a2' R) FF (wz 0x44050) fcc rv mm ro))
end.
{ step. if_cases Hc.
- apply evt_done. eexists. simp_regs. reflexivity.
- step. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a2' ->]. simp_regs.
step. step.
rewrite (unsigned_lit idx), Z.shiftl_mul_pow2 by lia. change (2^3) with 8.

destruct (nth_error bsl (Z.to_nat (5 + idx - 5))) as [bw|] eqn:BW; [| apply nth_error_None in BW; lia].
with_mem ltac:(fun mm => pose proof (u64arr_read asegs mm _ bsl (5 + idx - 5) bw (wa (977816 + idx * 8 + 104)) BSL BW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as HR).
step.
clear HR. step.
step.
with_mem ltac:(fun mm => pose proof (u64arr_store_ok asegs mm _ bsl (5 + idx - 5) (wa (977816 + idx * 8 + 104)) BSL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK).
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc _ bsl (5 + idx - 5) (wz (bv_unsigned bw + 1)) BSL ltac:(lia)) as BSL';
replace (wa (977920 + 8 * (5 + idx - 5))) with (wa (977816 + idx * 8 + 104)) in BSL' by (unfold wa; f_equal; lia) end.
clear BSL. store_done. try clear SOK. rename BSL' into BSL.

step.
amo_step (amo_aligned_intro8 978456 ltac:(lia) ltac:(reflexivity)).
step.
amo_step (amo_aligned_intro8 978464 ltac:(lia) ltac:(reflexivity)).
step.

recast I3 [C1 (b8 1); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)].
stp.

do 11 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ltail_post. do 15 eexists. exists (drop 8 pj).
split; [reflexivity|].
subst Q. split; [unfold ltail_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact I1|].
split; [eapply (wjunk69_close _ _ [C1 (b8 (bv_unsigned (wz 0))); CB 7 (drop 1 (le8 w0))]); [exact J1| reflexivity| exact BSL| rewrite upd_length; exact LBSL]|].
change (bv_unsigned (wz 0)) with 0 in I3. split; [exact I3|].
split; [eapply wjunk5_close; exact GS|].
split; [eapply u64arr_snoc; [exact P1| rewrite length_map, <- NCH; exact P2a]|].
split; [replace (parr + 8 * (nch + 1)) with (parr + 8 * nch + 8) by lia; exact P2b|].
exact ZBh.
Qed.

Lemma largealloc_finish : forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (s : PStateA) (a a1 : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (n lo : Z)
(rax t0 t1 t2 a1r a2 a4 a5 a6 a7 s4x s6x s7x s8x s9x t3 t4 t5 t6 : word) (m1 : mem)
(mb E nres1 : Z) (junk8 pj shu : list byte) (w0 w1 w2 w3 w4 g0 g1 g2 g3 g4 : word) (bsl : list word),
let msz := sec_map_size n in let sz := sec_size n in let reg := as_reg a in let nch := Z.of_nat (length reg) in let parr := ptrarr_lo RE in
gcons a LB FS G RE X -> avoid_covers RE X -> RTconst RE X m -> RStats RE X m -> RSec a LB RE X m ->
band_lo <= lo -> lo <= bv_unsigned sp - LARGE_STACK -> 0 <= n <= 2^26 -> from_primary n = false ->
mb mod kPage = 0 -> appr mb msz -> mb + msz <= band_lo -> zavoids mb msz (avoid_of (ae_L RE) a) = true ->
munch [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8); (rl_T X + 2872, rl_T X + 2888);
(977856, 978480); (parr, parr + 0x800000)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -96) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -96) [CB 8 junk8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m1 977864 [C8 (wz nres1); C8 (wz nch)] ->
rw_cells asegs m1 977880 [CB 8 (le8 w0); C8 w1; C8 w2; C8 w3; C8 w4] -> u64arr asegs m1 977920 bsl -> length bsl = 64%nat ->
rw_cells asegs m1 978432 [C4 (wz 1); C4 (wz 0)] ->
rw_cells asegs m1 978440 [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4] ->
u64arr asegs m1 parr (map (fun e => wz (se_beg e)) reg) ->
rw_cells asegs m1 (parr + 8 * nch) [CB (Z.to_nat (8 * (nres1 - nch))) pj] ->
nch < nres1 -> nres1 <= 2^20 -> nres1 mod kPtrArrBlock = 0 -> (nres1 = as_nres a \/ nres1 = as_nres a + kPtrArrBlock) ->
rw_cells asegs m1 mb [C8 (wz mb); C8 (wz msz); C8 (wz sz); C8 (wz 0)] ->
rw_cells asegs m1 (mb + 32) [CB 4064 (repeat (b8 0) 4064)] ->
rw_cells asegs m1 (mb + 4096) [CB (Z.to_nat (msz - 4096)) (repeat (b8 0) (Z.to_nat (msz - 4096)))] ->
rw_cells asegs m1 (SH mb) [CB (Z.to_nat 512) (repeat (b8 250) (Z.to_nat 512))] ->
rw_cells asegs m1 (SH (mb + 4096)) [CB (Z.to_nat (sz / 8)) shu] ->
rw_cells asegs m1 (SH (mb + 4096 + sz)) [CB (Z.to_nat ((msz - 4096 - sz) / 8)) (repeat (b8 250) (Z.to_nat ((msz - 4096 - sz) / 8)))] ->
0 <= E < 2^64 -> 16 <= Z.lxor E 63 <= 26 ->
as_reg a1 = as_reg a ++ [mkSec mb msz n] -> as_nres a1 = nres1 -> as_tq a1 = as_tq a -> as_gq a1 = as_gq a ->
(forall c, cls a1 c = cls a c) -> as_cache_inited a1 = as_cache_inited a -> as_next a1 = as_next a -> as_spent a1 = as_spent a + sec_cost msz ->
evt asegs (large_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a LB lo n m (Some mb, a1) s)
(MS (mkR rax (wz (bv_unsigned sp + -96)) gp (wz A_TP) t0 t1 t2 (wz 978440) (wz 977816)
(wz (mb + 4096)) a1r a2 (wz nch) a4 a5 a6 a7 (wz msz) (wz E) s4x (wz mb) s6x s7x s8x s9x s10 s11 t3 t4 t5 t6)
F (wz 0x44008) fc None m1 (seg_rom asegs)).
Proof.
intros until bsl; intros msz sz reg nch parr GC AVC RT RS RSE CEIL LO Hn HP MAL MK MC AVm MU WM MI1 ST1 RT1 FR I1 J1 BSL LBSL I3 GS P1 P2 NLT NMX NMOD NRES
ZBh ZBp ZBb SFh SBu SFs HE HIDX R1 R2 R3 R4 R5 R6 R7 R8.
pose proof CEIL as CEIL'. idtac. unfold LARGE_STACK in LO.
pose proof MC as MC'. idtac. pose proof MK as MK'. apply appr_to_lia in MK; [| unfold msz; pose proof (sec_map_size_ge n ltac:(lia) HP) as [SM _]; lia| lia].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _). rewrite KP in MAL. unfold kPtrArrBlock in NMOD, NRES.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & _ & _ & _ & QK & QH & _). unfold ptrarr_hi in QH. change (al_ptrarr (ae_L RE)) with parr in QH. fold parr in QK. rewrite ?KHI_eq in QK. idtac.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _ & TQD). cbn [fst snd] in TK, TB, TQD. unfold iv_disjoint in TQD; cbn [fst snd] in TQD. fold parr in TQD.
idtac. rewrite ?KHI_eq in TK. apply appr_to_lia in QK; [| lia| unfold ptrarr_hi in *; lia].
pose proof (sec_size_facts n Hn HP) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). fold sz msz in Z1, Z2, Z3, Z4, Z5, Z6.
pose proof (avoid_facts a mb msz AVC ltac:(lia) ltac:(lia) AVm) as (_ & AVO & AVP & AVQ & AVR). fold parr in AVQ.
pose proof (AVO _ (T_obj RE X)) as TMB. cbn [fst snd] in TMB.
assert (SHB : 0x7fff8000 <= SH mb /\ SH (mb + msz) = SH mb + msz / 8 /\ SH mb + msz / 8 <= 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; (first [ clear - H39 q7 H30 H24 q4 H19 H10 H9 r1 H5 H4 r0 q0 H0 H r q TMB AVQ Z5 r4 Z4 r5 Z3 r3 Z1 TQD TK QK MK' MC' R7 q3 LBSL q1 MK MAL r7 parr reg sz msz bsl mb n a1 a X RE BAND; lia | lia ])).
destruct SHB as (SHB1 & SHB2 & SHB3).
assert (SHE1 : SH (mb + 4096) = SH mb + 512) by (rewrite !SH_eq; (first [ clear - Z5 Z4 Z3 Z1 R7 NMOD NLT LBSL MK MAL nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])).
assert (SHE2 : SH (mb + 4096 + sz) = SH mb + 512 + sz / 8) by (rewrite !SH_eq; (first [ clear - Z5 Z4 Z3 Z1 R7 NMOD NLT LBSL MK MAL nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])).
destruct RSE as (_ & _ & _ & _ & _ & _ & HD & NLE & NMX0 & NMOD0). fold reg nch in HD, NLE.
rtc RT1 25%nat K25. fold parr in K25. unfold A_INSTANCE in K25.

eapply evt_cut.
{ eapply (largealloc_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rax t0 t1 t2 a1r a2 a4 a5 a6 a7 s4x s6x s7x s8x s9x t3 t4 t5 t6 m1
lo parr nch nres1 mb msz sz E reg junk8 pj);
[exact MI1| exact ST1| lia| exact FR| exact K25| exact I1| | exact I3| | exact P1| reflexivity| exact P2| lia| lia| (first [ clear - Z6 Z1 QK R7 NLT LBSL MK NLE parr nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])| (first [ clear - Z6 Z1 QH CEIL' R7 NLT LBSL MK NLE parr nch reg sz msz bsl nres1 mb lo n a1 a RE BAND; lia | lia ])| exact ZBh| (first [ clear - Z6 Z1 R7 NLT LBSL MK NLE nch reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])| (first [ clear - Z6 Z1 MC' CEIL' R7 LBSL MK reg sz msz bsl nres1 mb lo n a1 a RE BAND; lia | lia ])| (first [ clear - Z6 Z1 R7 LBSL MK reg sz msz bsl nres1 mb n a1 a RE BAND; lia | lia ])| exact AVQ| exact HE| exact HIDX].
- eapply (wjunk69_close _ _ [CB 8 (le8 w0)]); [exact J1| reflexivity| exact BSL| exact LBSL].
- eapply wjunk5_close; exact GS. }
cbv beta. intros ms' PO.
destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & pj' & -> & MUt & WMt & MI' & ST' & I1' & J' & I3' & G' & P1' & P2' & ZBh').
unfold ltail_W in MUt.
assert (PSH : parr + 8388608 <= SH mb \/ SH mb + msz / 8 <= parr) by (clear - QK SHB1 SHB3; lia).
assert (PSM : mb + msz <= SH mb \/ SH mb + msz / 8 <= mb) by (clear - MK MC SHB1 SHB3; lia).
assert (MBL : 0x647000 <= mb) by (clear - MK Z1 Z6; lia).
hide MK; hide QK; hide MK'; hide TK; hide SHB1; hide SHB3; hide NRES; hide TQD; hide AVP; hide AVQ; hide TMB; hide MAL; hide NMOD; hide NMOD0;
hide Z3; hide Z4; hide Z5; hide HIDX.
pose proof (munch_chain' _ _ m' _ m MUt MU ltac:(sub_fp_solve)) as MU'.
unhide MK'; unhide TK; unhide SHB1; unhide SHB3; unhide NRES; unhide TQD; unhide AVP; unhide AVQ; unhide TMB; unhide MAL; unhide NMOD; unhide NMOD0;
unhide Z3; unhide Z4; unhide Z5; unhide HIDX.
pose proof (wmono_trans asegs _ _ _ WM WMt) as WM'.
clear ZBh P2 GS I3 J1 I1 FR P1 BSL MU WM ST1 K25 RT1 MI1.
hide Z3; hide Z4; hide Z5; hide MAL; hide NMOD; hide NMOD0; hide HIDX; hide NRES; hide HE; hide Hn; hide NLE; hide NMX0;
hide TK; hide TB; hide TQD; hide TMB; hide AVP; hide KR; hide KO; hide KS; hide K32; hide KU; hide CEIL'; hide MC'; hide MK'; hide NRES.

hide PSH; hide PSM.
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (mb + 32) _) in ZBp;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r;
clear - MBL MC CEIL LO SPR AVQ NLT NMX Z1 Z6; unfold nch in *; split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (SH mb) _) in SFh;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; unhide PSH; unhide PSM;
clear - SHB1 SHB2 SHB3 MBL MC CEIL LO SPR PSH PSM NLT NMX Z1 Z6; pose proof SH_band; unfold nch in *;
split; [Z.div_mod_to_equations; lia| split; [lia| split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (mb + 4096) _) in ZBb;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; rewrite ?Z2Nat.id by lia;
clear - MBL MC CEIL LO SPR AVQ NLT NMX Z1 Z6; unfold nch in *; split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (SH (mb + 4096)) _) in SBu;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; rewrite ?Z2Nat.id by (clear - Z1; Z.div_mod_to_equations; lia); unhide PSH; unhide PSM;
rewrite SHE1; clear - SHB1 SHB2 SHB3 MBL MC CEIL LO SPR PSH PSM NLT NMX Z1 Z6; pose proof SH_band; unfold nch in *;
split; [Z.div_mod_to_equations; lia| split; [lia| split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]]]].
apply (rw_cells_transport asegs (ltail_W (bv_unsigned sp) parr nch mb) m1 m' (SH (mb + 4096 + sz)) _) in SFs;
[| exact MUt| exact WMt| unfold ltail_W; cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r; rewrite ?Z2Nat.id by (clear - Z1 Z6; Z.div_mod_to_equations; lia); unhide PSH; unhide PSM;
rewrite SHE2; clear - SHB1 SHB2 SHB3 MBL MC CEIL LO SPR PSH PSM NLT NMX Z1 Z6; pose proof SH_band; unfold nch in *;
split; [Z.div_mod_to_equations; lia| split; [lia| split; [Z.div_mod_to_equations; lia| split; [Z.div_mod_to_equations; lia| exact I]]]]].
transport_after_call asegs m1 m' MUt WMt.
unhide NRES.
unhide Z3; unhide Z4; unhide Z5; unhide MAL; unhide NMOD; unhide NMOD0; unhide HIDX; unhide NRES; unhide HE; unhide Hn; unhide NLE; unhide NMX0;
unhide TK; unhide TB; unhide TQD; unhide TMB; unhide AVP; unhide KR; unhide KO; unhide KS; unhide K32; unhide KU; unhide CEIL'; unhide MC'; unhide MK'; unhide MK; unhide QK.
clear MUt WMt.

assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (977856, 978480); (parr, parr + 8388608)]).
{ clear - RL MK' MK AVO SHB1 SHB3 CEIL' CEIL LO SPR TK TB QK QH.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_free; [exact RL| exact (proj2 MK')| intros o Ho; destruct (AVO o Ho); lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [exact (rt_avoid_inst RE X RL)|].
constructor; [apply rt_avoid_ptrarr; [exact RL| subst parr; lia| subst parr; unfold ptrarr_hi, ptrarr_lo; lia]| constructor]. }
assert (FWst : Forall st_avoid [(bv_unsigned sp - 800, bv_unsigned sp); (mb, mb + msz); (SH mb, SH mb + msz / 8);
(rl_T X + 2872, rl_T X + 2888); (977856, 978480); (parr, parr + 8388608)]).
{ clear - MK MBL SHB1 CEIL LO SPR TK QK.
repeat apply Forall_cons; try apply Forall_nil;
first [apply st_avoid_above; cbn [fst]; unfold A_ERRNO; lia| apply st_avoid_low; cbn [snd]; lia
| destruct (Z_lt_le_dec (rl_T X) 0x647000); [apply st_avoid_low; cbn [snd]; lia| apply st_avoid_above; cbn [fst]; unfold A_ERRNO; lia]]. }
assert (MUf : munch (W_large (bv_unsigned sp) RE X ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m').
{ clear - MU' SHB2. unfold W_large, LARGE_STACK, A_INSTANCE. cbn [app]. rewrite SHB2. change (ptrarr_lo RE) with parr.
change (977752 + 104) with 977856. change (977752 + 728) with 978480.
refine (munch_weaken _ _ _ _ _ MU'). sub_fp_solve. }

assert (HD' : forall i e, nth_error reg i = Some e -> sec_hdr_mem m' i e).
{ intros i e Hi. pose proof (HD i e Hi) as (A1 & A2 & A3). pose proof (nth_error_In _ _ Hi) as He.
pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
rewrite ?KHI_eq in E2. idtac.
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [G1 _]. rewrite <- E4 in G1.
unfold iv_disjoint in E8; cbn [fst snd] in E8. change (ptrarr_lo RE) with parr in E8.
pose proof (proj1 (List.Forall_forall _ _) E9 _ (T_obj RE X)) as ET. unfold iv_disjoint in ET; cbn [fst snd] in ET.
pose proof (AVR e He) as EM.
assert (SE : SH (se_beg e) + 512 = SH (se_beg e + 4096) /\ 0x80000000 <= SH (se_beg e) /\ SH (se_beg e + 4096) <= 0x10007fff8000
/\ (SH (se_beg e + 4096) <= SH mb \/ SH mb + msz / 8 <= SH (se_beg e))).
{ pose proof (sec_req_facts (se_req e) ltac:(lia) E5) as [_ GE].
clear - SHB2 E1 E2 E3 EM MAL MK MC G1 E6 Z6 Z1 GE. rewrite <- SHB2. rewrite !SH_eq. Z.div_mod_to_equations. lia. }
destruct SE as (SE1 & SE2 & SE3 & SE4).
assert (AG : agree_on asegs (fun x => (se_beg e <= x < se_beg e + 4096) \/ (SH (se_beg e) <= x < SH (se_beg e) + 512)) m m').
{ eapply agree_on_of_munch; [exact MU'| exact WM'|]. intros x Hx _. cbn [outside].
clear - Hx EM E2 E3 G1 E6 E8 ET SE1 SE2 SE3 SE4 CEIL LO SPR MK MC SHB1 SHB3 QK QH TK TB Z6 Z1. (first [ clear - Hx x SE4 SE3 SE2 SE1 EM ET G1 E8 E6 E3 E2 e SHB3 SHB1 Z6 Z1 TB TK QH QK MC MK LO CEIL parr sz msz mb lo n sp X RE BAND; lia | lia ]). }
split; [| split].
- eapply rw_cells_agree; [exact AG| exact A1|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. left. lia.
- eapply hjunk_wmono; [exact A2| exact WM'].
- eapply rw_cells_agree; [exact AG| exact A3|]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. right. clear - Hz. lia. }
apply evt_done. unfold large_post. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact WM'|].
split; [eapply RTconst_munch; [exact RT| exact MU'| exact WM'| exact FWrt]|].
split; [eapply RStats_munch; [exact RS| exact MU'| exact WM'| exact FWst]|].
cbv beta iota zeta. fold msz sz.
split; [rewrite KP; reflexivity|].
split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact R7|].
split; [rewrite R2; unfold kPtrArrBlock; clear - NRES; lia|].
split; [exact R8|].
split; [rewrite KP; exact MAL|]. split; [exact MK'|]. split; [exact MC'|]. split; [exact AVm|].
split; [exact MUf|].
split.
{
unfold RSec, RSec_mem. rewrite R1, R2. change (ptrarr_lo RE) with parr. fold reg. rewrite length_app. cbn [length].
replace (Z.of_nat (length reg + 1)) with (nch + 1) by (clear; lia).
unfold SEC_NRES, SEC_JUNK, SEC_MUT, SEC_GST, A_INSTANCE.
change (977752 + 112) with 977864. change (977752 + 128) with 977880. change (977752 + 680) with 978432. change (977752 + 688) with 978440.
split; [exact I1'|]. split; [exact J'|]. split; [exact I3'|]. split; [exact G'|].
split; [rewrite map_app; cbn [map]; exact P1'|].
split; [replace (parr + 8 * nres1) with (parr + 8 * (nch + 1) + Z.of_nat (cells_size [CB (Z.to_nat (8 * (nres1 - nch - 1))) pj'])) by (cbn [cells_size csize]; clear - NLT; lia);
apply cells_hjunk; [exact P2'| clear - QK; lia]|].
split.
- intros i e Hi. destruct (Nat.lt_ge_cases i (length reg)) as [LT|GE].
+ rewrite nth_error_app1 in Hi by exact LT. exact (HD' i e Hi).
+ rewrite nth_error_app2 in Hi by exact GE.
destruct (i - length reg)%nat as [|k] eqn:EK; [| cbn in Hi; destruct k; discriminate].
cbn in Hi. injection Hi as <-. unfold sec_hdr_mem. cbn [se_beg se_size se_req]. fold sz.
replace (Z.of_nat i) with nch by (clear - GE EK; lia).
split; [exact ZBh'|]. split.
* rewrite KP. replace (mb + 4096) with (mb + 32 + Z.of_nat (cells_size [CB 4064 (repeat (b8 0) 4064)])) by (cbn; clear; lia).
apply cells_hjunk; [exact ZBp| clear - MBL; lia].
* unfold fas, fa_byte. exact SFh.
- unfold kMaxNumChunks, kPtrArrBlock. clear - NLT NMX NMOD. lia. }
rewrite KP. split; [exact ZBb|]. split.
{ replace (SH (mb + 4096 + sz)) with (SH (mb + 4096) + Z.of_nat (cells_size [CB (Z.to_nat (sz / 8)) shu])) by (cbn [cells_size csize]; clear - SHE1 SHE2 Z1; lia).
apply cells_hjunk; [exact SBu| clear - SHE1 SHB1; lia]. }
unfold fas, fa_byte. exact SFs.
Qed.
End S.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 Q9Ho.Mq4 QnRU.Mql.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).

Lemma unw_obj_head : forall m obj sz q rest bp, rw_cells asegs m obj (unw_obj obj sz q rest bp) -> length q = 5%nat -> 0 <= sz < 2^32 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz sz)] /\ exists q30 : list word, u64arr asegs m (obj + 16) q30 /\ Z.of_nat (length q30) = 30.
Proof.
intros m obj sz q rest bp H LQ SZ.
destruct (unw_obj_open m obj sz q rest bp LQ H) as (qs & rest2 & LQS & H1 & Q & _). split.
- eapply rw_cells_recast'; [exact H1| cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite (le8_split32 sz) by lia. rewrite <- !app_assoc. reflexivity.
- exists qs. split; [exact Q| exact LQS].
Qed.

End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QmP7.Mq1 QTVW.Mq7 QnRU.Mqi.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition populate_entry : Z := 0x44624.
Definition POPULATE_STACK : Z := 512.

Lemma class_size_lo : forall c, 1 <= c <= 16 -> class_size c = 32 * c.
Proof. intros c Hc. unfold class_size. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Ltac popA_finish :=
apply evt_done; do 3 eexists;
split; [ cbv delta [mkR];
repeat match goal with |- context [wz (if ?cnd then _ else _)] =>
first [ replace cnd with true by (symmetry; apply Z.ltb_lt; lia) | replace cnd with false by (symmetry; apply Z.ltb_ge; lia) ] end;
reflexivity |];
split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
split; [ match goal with H : stk asegs _ _ _ |- _ => exact H end | match goal with H : rw_cells asegs _ (bv_unsigned _ + -64) _ |- _ => exact H end ].

Lemma populate_A : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (a : AState) (c req lo v : Z) j1 j2 j3 j4,
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp + -64 ->
1 <= c <= 30 -> 0 <= req <= 8 ->
rw_cells asegs m (ri_addr RE c) (ri_cellsL v (cls a c) j1 j2 j3 j4) ->
0 <= c_alloc_user (cls a c) <= c_mapped_user (cls a c) -> c_mapped_user (cls a c) <= kFreeArrayOffset ->
evt asegs (fun ms1 => exists (a5' a6' : word) m1,
ms1 = MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (ri_addr RE c)) (wz (rl_T X + 2768))
(wz A_INSTANCE) (wz (c * 4294967296)) (wz c) (wz (c_alloc_user (cls a c))) (wz req) a5' a6' a7
(wz (reg_beg (ae_L RE) c)) (wz (c_alloc_user (cls a c) + class_size c * req)) (wz (c_mapped_user (cls a c))) (wz (class_size c))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (if c_mapped_user (cls a c) <? c_alloc_user (cls a c) + class_size c * req then 0x446c4 else 0x44798)) fc None m1 (seg_rom asegs)
/\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (bv_unsigned sp + -64)
/\ rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 2768)) (wz c) (wz (ri_addr RE c)) (wz req) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz populate_entry) fc None m (seg_rom asegs)).
Proof.
intros until j4; intros RT RL MI ST CEIL LO Hc Hreq RI AU MU0.
pose proof CEIL as CEIL'. idtac.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX). rewrite KO in MU0.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2. hide PAL.
assert (SR : 0 <= class_size c * req <= 1033280) by (first [ clear - SZ1 TB TK PK RB SPR CEIL' Hreq LO CEIL lo req c sp X RE BAND; nia | nia ]).
cbv beta delta [ri_cellsL] in RI. unfold ri_addr in *. rtc RT 24%nat K24. unfold A_INSTANCE in *.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold populate_entry.
carve_frame 64%nat ST.
do 9 step.
step. step.
step.
step. stp.
step. ifz.
step. step.
destruct (Z.leb_spec c 16) as [CLO|CHI].
- ifz. stp.
step. step. step. step. step.
rewrite !(unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^5) with 32. change (2^32) with 4294967296.
replace (c * 32) with (class_size c) by (rewrite class_size_lo by lia; lia).
rewrite (unsigned_lit (class_size c)), (unsigned_lit req) by lia.
replace (al_space_beg (ae_L RE) + c * 4294967296) with (reg_beg (ae_L RE) c) by (rewrite RB; reflexivity).
step.
destruct (Z.ltb_spec (c_mapped_user (cls a c)) (c_alloc_user (cls a c) + class_size c * req)) as [LT|GE]; ifz; [|step]; popA_finish.
- ifz.
stp. step. stp. stp. step. stp. step. stp. step.
get_reg 21%Z ltac:(fun v => replace v with (wz (class_size c)) by (clear - CHI Hc; enum_cases c 17 30; vm_compute; reflexivity)).
step. step. step. step. step.
rewrite !(unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^32) with 4294967296.
rewrite (unsigned_lit (class_size c)), (unsigned_lit req) by lia.
replace (al_space_beg (ae_L RE) + c * 4294967296) with (reg_beg (ae_L RE) c) by (rewrite RB; reflexivity).
step.
destruct (Z.ltb_spec (c_mapped_user (cls a c)) (c_alloc_user (cls a c) + class_size c * req)) as [LT|GE]; ifz; popA_finish.
Qed.
End S.

Section S2.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Definition pop_W (sp c au : Z) : list (Z * Z) :=
[ (sp - POPULATE_STACK, sp); (rl_T X + 2768, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition pop_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (G : ghost) (c au lo : Z) (m : word -> option byte) (v : Z)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (k : nat),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (pop_W (bv_unsigned sp) c au) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrimL (snd r) (gappend c (repeat TFree k) G) RE X m' c v
/\ a0 = wz (if fst r then 1 else 0).

Definition pop_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s1' : AState) (G : ghost) (c au lo : Z) (m : word -> option byte) (v : Z) (ms' : machine_state) : Prop :=
exists x1 t0 t1 t2 x9 a1 a2 a4 a5 a6 a7 x19 x22 t3 t4 t5 t6 m',
ms' = MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (ri_addr RE c)) x9 (wz A_INSTANCE) a1 a2 (wz (c_alloc_user (cls s1' c))) a4 a5 a6 a7
(wz (reg_beg (ae_L RE) c)) x19
(wz (c_mapped_user (cls s1' c))) (wz (class_size c)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x44798) fc None m' (seg_rom asegs)
/\ munch (pop_W (bv_unsigned sp) c au) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrimL s1' G RE X m' c v.
End S2.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 Q9Ho.Mq3 QnRU.Mqi.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).

Definition carved (nc : Z) (k : nat) : list Z := map (fun j => nc + Z.of_nat j) (seq 0 k).
Definition coffw (c : Z) (j : Z) : word := Z_to_bv 64 (coff c j).

Lemma carved_length : forall nc k, length (carved nc k) = k.
Proof. intros. unfold carved. rewrite length_map, length_seq. reflexivity. Qed.
Lemma carved_S : forall nc k, carved nc (S k) = carved nc k ++ [nc + Z.of_nat k].
Proof. intros. unfold carved. rewrite seq_S, map_app. reflexivity. Qed.
Lemma in_carved : forall nc k i, In i (carved nc k) <-> nc <= i < nc + Z.of_nat k.
Proof.
intros nc k i. unfold carved. rewrite in_map_iff. split.
- intros (j & <- & Hj). apply in_seq in Hj. lia.
- intros Hi. exists (Z.to_nat (i - nc)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma NoDup_carved : forall nc k, List.NoDup (carved nc k).
Proof.
intros nc k. unfold carved. apply (NoDup_map_NoDup_ForallPairs (fun j => nc + Z.of_nat j)); [| apply seq_NoDup].
intros x y _ _ E. lia.
Qed.

Lemma skipn_repeat' {A} : forall (b : A) o n, skipn o (repeat b n) = repeat b (n - o).
Proof. intros b o. induction o as [|o IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat' {A} : forall (b : A) k n, (k <= n)%nat -> firstn k (repeat b n) = repeat b k.
Proof. intros b k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

Lemma rw_cells_CB_repeat_sub : forall m A n b o len,
rw_cells asegs m A [CB n (repeat b n)] -> (o + len <= n)%nat ->
rw_cells asegs m (A + Z.of_nat o) [CB len (repeat b len)].
Proof.
intros m A n b o len H LE.
replace n with (o + (n - o))%nat in H by lia.
apply rw_cells_CB_split in H. destruct H as [_ H]. rewrite skipn_repeat' in H.
replace (o + (n - o) - o)%nat with (len + (n - o - len))%nat in H by lia. replace (n - o)%nat with (len + (n - o - len))%nat in H by lia.
apply rw_cells_CB_split in H. destruct H as [H _]. rewrite firstn_repeat' in H by lia. exact H.
Qed.

Lemma cr_pure_carve : forall a G c K newc a',
cr_pure a G c K -> 1 <= c <= 31 -> 0 <= newc ->
c_alloc_user (cls a c) + newc * class_size c <= c_mapped_user (cls a c) ->
4 * (c_num_freed (cls a c) + newc) <= c_mapped_fa (cls a c) ->
cls a' c = set_alloc_user (c_alloc_user (cls a c) + newc * class_size c) (set_num_freed (c_num_freed (cls a c) + newc) (cls a c)) ->
as_cache_inited a' = as_cache_inited a ->
cr_pure a' (gappend c (repeat TFree (Z.to_nat newc)) G) c (mkPK (pk_fl K ++ rev (carved (ncarved G c) (Z.to_nat newc))) (pk_ca K)).
Proof.
intros a G c K newc a' PU Hc Hn LEu LEf Ea Ei.
pose proof kconsts as (_ & _ & _ & _ & _ & _ & KM & _).
pose proof (cr_pure_div8 a G c K PU Hc) as ((qa & QA0 & QA & QAE) & _ & E8).
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
unfold cr_pure. rewrite Ea, Ei. cbn [pk_fl pk_ca c_num_freed c_count c_mapped_fa c_alloc_user c_mapped_user set_alloc_user set_num_freed].
rewrite gappend_class.
assert (OLD : forall i t, tag_at G c i = Some t -> 0 <= i < ncarved G c) by (intros i t Ht; exact (tag_at_Some_lt _ _ _ _ Ht)).
assert (TG : forall i, In i (pk_fl K ++ rev (carved (ncarved G c) (Z.to_nat newc))) ->
tag_at (gappend c (repeat TFree (Z.to_nat newc)) G) c i = Some TFree).
{ intros i Hi. apply in_app_or in Hi. destruct Hi as [Hi|Hi].
- apply tag_at_gappend_Some_old. exact (P5 i Hi).
- rewrite <- in_rev in Hi. apply in_carved in Hi. rewrite tag_at_gappend_new by lia.
apply nth_error_repeat. lia. }
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
- rewrite length_app, length_rev, carved_length. lia.
- apply NoDup_app; [exact P3| apply NoDup_rev; apply NoDup_carved|].
intros i Hi Hi'. rewrite <- in_rev in Hi'. apply in_carved in Hi'. pose proof (OLD i _ (P5 i Hi)). lia.
- intros i Hi. apply tag_at_gappend_Some_old. exact (P6 i Hi).
- rewrite count_tag_app, count_tag_repeat, P7. cbn. lia.
- rewrite count_tag_app, count_tag_repeat, P8. cbn. lia.
- rewrite length_app, repeat_length. unfold ncarved in QAE. rewrite QA. rewrite Nat2Z.inj_add, Z2Nat.id by lia. rewrite Z.mul_add_distr_r, G1, QA. reflexivity.
- pose proof (class_size_facts c Hc) as [S1 _]. pose proof (Z.mul_nonneg_nonneg newc (class_size c) Hn ltac:(clear - S1; lia)). lia.
Qed.

Lemma cr_slots_carve : forall a a' G RE m c K newc,
cr_pure a G c K -> 1 <= c <= 31 -> 0 <= newc ->
c_alloc_user (cls a c) + newc * class_size c <= c_mapped_user (cls a c) ->
cr_slots a G RE m c ->
hjunk m (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) (reg_beg (ae_L RE) c + c_alloc_user (cls a c) + newc * class_size c) ->
rw_cells asegs m (SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)))
[CB (Z.to_nat (newc * (class_size c / 8))) (repeat fa_byte (Z.to_nat (newc * (class_size c / 8))))] ->
cr_slots a' (gappend c (repeat TFree (Z.to_nat newc)) G) RE m c.
Proof.
intros a a' G RE m c K newc PU Hc Hn LEu [SL SS] UT US.
pose proof (cr_pure_div8 a G c K PU Hc) as ((qa & QA0 & QA & QAE) & _ & E8).
pose proof (class_size_facts c Hc) as [S1 S2]. unfold ncarved in QAE.
assert (CASE : forall i t, tag_at (gappend c (repeat TFree (Z.to_nat newc)) G) c i = Some t ->
tag_at G c i = Some t \/ (ncarved G c <= i < ncarved G c + newc)).
{ intros i t Ht. destruct (Z.lt_ge_cases i (ncarved G c)) as [LT|GE].
- left. rewrite tag_at_gappend_old in Ht by exact LT. exact Ht.
- right. rewrite tag_at_gappend_new in Ht by exact GE.
assert (L : (Z.to_nat (i - ncarved G c) < length (repeat TFree (Z.to_nat newc)))%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
rewrite repeat_length in L. lia. }
unfold ncarved in CASE.
split.
- intros i t Ht Hp. destruct (CASE i t Ht) as [Ho|NEW]; [exact (SL i t Ho Hp)|].
unfold slot_beg. destruct (hjunk_split _ _ (reg_beg (ae_L RE) c + i * class_size c) _ UT ltac:(nia)) as [_ J].
destruct (hjunk_split _ _ (reg_beg (ae_L RE) c + i * class_size c + class_size c) _ J ltac:(nia)) as [J' _]. exact J'.
- intros i t Ht Hp. destruct (CASE i t Ht) as [Ho|NEW]; [exact (SS i t Ho Hp)|].
unfold slot_beg.
pose proof (rw_cells_CB_repeat_sub _ _ _ _ (Z.to_nat ((i - Z.of_nat (length (G c))) * (class_size c / 8))) (Z.to_nat (class_size c / 8)) US ltac:(nia)) as R.
replace (SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) + Z.of_nat (Z.to_nat ((i - Z.of_nat (length (G c))) * (class_size c / 8))))
with (SH (reg_beg (ae_L RE) c + i * class_size c)) in R; [exact R|].
rewrite QA, SH_plus8. replace (i * class_size c) with (8 * (i * (class_size c / 8))) by nia. rewrite SH_plus8. nia.
Qed.

Lemma populate_close {BAND : Band} : forall (aa a2s : AState) G RE X (m1 m3 : mem) c (K2 : Z -> pcls) k1 k2 k3 k4 CH2 qa qm newc v,
let x := cls aa c in let x2 := cls a2s c in let nc := ncarved G c in
let rb := reg_beg (ae_L RE) c in let fb := fa_beg (ae_L RE) c in
rlay_ok RE X -> 1 <= c <= 30 ->
c_alloc_user x2 = c_alloc_user x -> c_mapped_user x2 = c_mapped_user x -> c_num_freed x2 = c_num_freed x ->
c_count x2 = c_count x -> as_cache_inited a2s = as_cache_inited aa ->
4 * (c_num_freed x + newc) <= c_mapped_fa x2 ->
hjunk m1 (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, G c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep a2s G RE X m1 c0 (K2 c0)) ->
cr_pure a2s G c (K2 c) ->
0 <= qa -> c_alloc_user x = 8 * qa -> qa = nc * (class_size c / 8) -> 0 <= qm -> c_mapped_user x = 8 * qm ->
0 <= newc -> newc * class_size c <= c_mapped_user x - c_alloc_user x ->
wmono asegs m1 m3 ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> agree_on asegs (fp_cls RE X c0) m1 m3) ->
agree_on asegs (szone RE c (c_alloc_user x)) m1 m3 ->
rw_cells asegs m3 (region_info RE + 128 * c)
[C8 (wz v); CB 8 k1; C8 (wz (c_num_freed x + newc)); C8 (wz (c_mapped_fa x2));
C8 (wz (c_alloc_user x + newc * class_size c)); C8 (wz 0); C8 (wz (c_mapped_user x)); C8 (wz 0); CB 4 k2; C1 (Z_to_bv 8 0); CB 3 k3; CB 56 k4] ->
rw_cells asegs m3 (rl_T X + 208 + 80 * c)
[C4 (wz (c_count x)); C4 (wz (if as_cache_inited aa then bmax c else 0)); C8 (wz (if as_cache_inited aa then bsize c else 0))] ->
u32arr asegs m3 (rl_T X + 208 + 80 * c + 16) CH2 -> length CH2 = 16%nat ->
(forall j, (j < length (pk_ca (K2 c)))%nat -> nth_error CH2 j = Some (wz (coff c (nth j (pk_ca (K2 c)) 0)))) ->
u32arr asegs m3 fb (map (fun i => wz (coff c i)) (pk_fl (K2 c))) ->
u32arr asegs m3 (fb + 4 * c_num_freed x) (rev (map (coffw c) (carved nc (Z.to_nat newc)))) ->
hjunk m1 (fb + 4 * c_num_freed x) (fb + c_mapped_fa x2) ->
cr_slots a2s G RE m1 c ->
hjunk m1 (rb + c_alloc_user x) (rb + c_mapped_user x) ->
rw_cells asegs m3 (SH rb + qa) [CB (Z.to_nat ((c_mapped_user x - 8 * qa) / 8)) (repeat fa_byte (Z.to_nat ((c_mapped_user x - 8 * qa) / 8)))] ->
hjunk m1 (SH rb + qm) (SH rb + 469762048) ->
hjunk m1 (SH fb) (SH fb + 67108864) ->
RPrimL (set_cls c (set_alloc_user (c_alloc_user x + newc * class_size c) (set_num_freed (c_num_freed x + newc) x2)) a2s)
(gappend c (repeat TFree (Z.to_nat newc)) G) RE X m3 c v.
Proof.
intros until v; intros x x2 nc rb fb RL Hc EA EM EN EC EI LE4 HJS GNE HCall PU2 QA0 QA QAE QM0 QM N0 NEWC WMm OTH AGS
RI PC0 ACH LCH2 HCH2 FA ARR FJ HSL UT US UJ FS.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2].
pose proof PU2 as (Q1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q11 & Q12 & Q13 & Q14 & _ & R1 & R2 & R3 & R4 & R5).
rewrite ?EA, ?EM, ?EN, ?EC in *.
assert (E8 : class_size c = 8 * (class_size c / 8)) by (clear - SZ1 SZ2; Z.div_mod_to_equations; lia).
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K2 c)))) = c_num_freed x) by (rewrite length_map; exact Q1).
eapply (RPrimL_reclose a2s _ G _ RE X m1 m3 c K2 (mkPK (pk_fl (K2 c) ++ rev (carved nc (Z.to_nat newc))) (pk_ca (K2 c))) v RL HJS GNE HCall ltac:(rewrite K32; lia));
[ intros c0 Hc0; apply cls_set_cls_ne; exact Hc0
| reflexivity
| intros c0 Hc0; apply gappend_other_class; exact Hc0
| intros; lia
| exact WMm | exact OTH |].
apply class_repL_split. split; [|split].
-
unfold cr_cellsL. rewrite !cls_set_cls_eq.
cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count as_cache_inited set_cls pk_ca].
rewrite ?EC, ?EI.
split; [exists k1, k2, k3, k4; cbv beta delta [ri_cellsL]; cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count]; rewrite ?EM; unfold ri_addr; exact RI|].
split; [cbv beta delta [pc_cells]; cbn [set_alloc_user set_num_freed c_count]; rewrite ?EC, ?EI; unfold pc_addr; exact PC0|].
exists CH2. unfold pc_addr. split; [exact ACH| split; [exact LCH2| exact HCH2]].
-
apply (cr_pure_carve a2s G c (K2 c) newc); [exact PU2| lia| lia| rewrite ?EA, ?EM; lia| rewrite ?EN; exact LE4| | reflexivity].
rewrite cls_set_cls_eq, ?EA, ?EN. reflexivity.
-
intros _. rewrite !cls_set_cls_eq.
cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa pk_fl]. rewrite ?EA, ?EM, ?EN, ?EC. fold rb fb.
split. { rewrite map_app, map_rev. apply u32arr_app; [exact FA|]. rewrite LFA. exact ARR. }
split. { pose proof (hjunk_wmono _ _ _ _ FJ WMm) as FJ1.
destruct (hjunk_split _ _ (fb + 4 * (c_num_freed x + newc)) _ FJ1 ltac:(lia)) as [_ FJ2]. exact FJ2. }
split; [| rewrite KS; replace 536870912 with (8 * 67108864) by reflexivity; rewrite SH_plus8; eapply hjunk_wmono; [exact FS| exact WMm]].
apply cr_user_split. rewrite !cls_set_cls_eq.
cbn [set_alloc_user set_num_freed c_mapped_user c_alloc_user c_num_freed c_mapped_fa]. rewrite ?EA, ?EM, ?EN, ?EC. fold rb fb.
pose proof (hjunk_wmono _ _ _ _ UT WMm) as UT1.
destruct (hjunk_split _ _ (rb + c_alloc_user x + newc * class_size c) _ UT1 ltac:(lia)) as [UT2 UT3].
assert (NQ : 0 <= newc * (class_size c / 8) /\ 8 * (newc * (class_size c / 8)) = newc * class_size c) by (clear - N0 E8 SZ1; nia).
set (nq := newc * (class_size c / 8)) in *.
assert (CNT : Z.to_nat ((c_mapped_user x - 8 * qa) / 8) = (Z.to_nat nq + Z.to_nat ((c_mapped_user x - 8 * qa) / 8 - nq))%nat).
{ clear - NQ NEWC QA QA0 QM QM0 R3. Z.div_mod_to_equations. lia. }
rewrite CNT in US at 1. apply rw_cells_CB_split in US. destruct US as [US1 US2].
rewrite firstn_repeat' in US1 by (first [ clear - CNT E8 R3 R1 SZ1 KM nq LCH2 NEWC N0 QM QAE QA nc x newc qm qa CH2 K2 c RE G a2s; lia | lia ]). rewrite skipn_repeat' in US2.
split; [| split; [| split]].
+ eapply (cr_slots_carve a2s _ G RE m3 c (K2 c) newc); [exact PU2| lia| lia| rewrite ?EA, ?EM; lia| | |].
* eapply cr_slots_agree; [exact PU2| exact HSL| lia|]. rewrite EA. exact AGS.
* rewrite ?EA. exact UT2.
* rewrite ?EA. fold nq. rewrite QA, SH_plus8. exact US1.
+ replace (rb + (c_alloc_user x + newc * class_size c)) with (rb + c_alloc_user x + newc * class_size c) by lia. exact UT3.
+ replace (rb + (c_alloc_user x + newc * class_size c)) with (rb + 8 * (qa + nq)) by (first [ clear - CNT E8 R1 SZ1 KM nq LCH2 NEWC N0 QM QAE QA rb nc x newc qm qa CH2 K2 c RE G a2s; lia | lia ]). rewrite SH_plus8.
replace ((c_mapped_user x - (c_alloc_user x + newc * class_size c)) / 8) with ((c_mapped_user x - 8 * qa) / 8 - nq).
2:{ clear - NQ NEWC QA QA0 QM QM0 R3. Z.div_mod_to_equations. lia. }
rewrite Z2Nat.id in US2 by lia. rewrite <- Z.add_assoc in US2.
replace (Z.to_nat ((c_mapped_user x - 8 * qa) / 8) - Z.to_nat nq)%nat with (Z.to_nat ((c_mapped_user x - 8 * qa) / 8 - nq)) in US2 by (first [ clear - CNT E8 R3 R1 SZ1 KM nq LCH2 NEWC N0 QM QAE QA nc x newc qm qa CH2 K2 c RE G a2s; lia | lia ]).
exact US2.
+ rewrite KO, QM at 1. replace 3758096384 with (8 * 469762048) by reflexivity. rewrite !SH_plus8. eapply hjunk_wmono; [exact UJ| exact WMm].
Qed.
End Mqh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QmP7.Mq1 QYyZ.Mq8 Q9Ho.Mq3.
Import QXcn QpME.Mq7.
Import QYyZ.Mqc.
Import Qu3b QmvA.
Import QlES.
Import QnRU.Mqh.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition drain_entry : Z := 0x41040.

Definition DRAIN_STACK : Z := RECYCLE_STACK.

Lemma qptrs_app : forall l1 l2 b1 b2, qptrs (mkQ (l1 ++ l2) b1) = qptrs (mkQ l1 b2) ++ qptrs (mkQ l2 b2).
Proof. intros. unfold qptrs. cbn [q_list]. rewrite map_app, concat_app. reflexivity. Qed.

Lemma qptrs_q0 : qptrs q0 = [].
Proof. reflexivity. Qed.

Lemma NoDup_app_comm {A} : forall (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup (l2 ++ l1).
Proof.
intros l1 l2 H. apply (Permutation_NoDup (l := l1 ++ l2)); [apply Permutation_app_comm| exact H].
Qed.

Lemma qwf_app : forall l1 l2 b1 b2, qwf (mkQ l1 b1) -> qwf (mkQ l2 b2) -> qwf (mkQ (l1 ++ l2) (b1 + b2)).
Proof.
intros l1 l2 b1 b2 [F1 B1] [F2 B2]. unfold qwf in *. cbn [q_list q_bytes] in *. split; [apply Forall_app; auto|]. rewrite map_app, fold_right_add_app. lia.
Qed.

Lemma qwf_q0 : qwf q0.
Proof. split; [constructor| reflexivity]. Qed.

Lemma q_last_app : forall RE J1 J2, J2 <> [] -> q_last RE (J1 ++ J2) = q_last RE J2.
Proof.
intros RE J1 J2 NE. destruct (split_last J2) as [[f y]|] eqn:E; pose proof (split_last_spec J2) as SL; rewrite E in SL.
- subst J2. rewrite app_assoc, !q_last_snoc. reflexivity.
- congruence.
Qed.

Lemma q_first_app : forall RE J1 J2, J1 <> [] -> q_first RE (J1 ++ J2) = q_first RE J1.
Proof. intros RE [|j J1] J2 NE; [congruence| reflexivity]. Qed.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Hypothesis recycle_spec : recycle_stmt C RE X L.

Definition drain_W (sp : Z) : list (Z * Z) :=
[ (sp - 48, sp); (QMUT, QMUT + 4); (GQ, GQ + 32); (TQ X, TQ X + 32) ].

Lemma drain_W_zone : forall a LB0 FS0 G (sp : Z) Wx lo hi x,
gcons a LB0 FS0 G RE X -> band_lo <= sp - 48 ->
Forall (fun iv => exists j, tag_at G 24 j = Some TQOwn /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx ->
In (lo, hi) (drain_W sp ++ Wx) -> lo <= x < hi -> fp_RQuar a LB0 G RE X x \/ (band_lo <= x < sp).
Proof.
intros a LB0 FS0 G sp Wx lo hi x GC CE HWx Hin Hx. unfold drain_W, QMUT, GQ, TQ in *.
apply in_app_iff in Hin as [Hin|Hin].
- cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
+ right. lia.
+ left. do 2 right; left. split; cbn [fst snd]; lia.
+ left. do 2 right; left. split; cbn [fst snd]; lia.
+ left. left. split; cbn [fst snd]; lia.
- left. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as (j & Tj & B1 & B2). cbn [fst snd] in B1, B2.
do 5 right; left. exists 24, j, TQOwn. split; [exact Tj|]. split; [reflexivity|]. split; cbn [fst snd]; rewrite ?class_size_24; lia.
Qed.

Lemma drain_W_qzone : forall a LB0 FS0 G (sp : Z) Wx lo hi x,
gcons a LB0 FS0 G RE X -> band_lo <= sp - 48 ->
Forall (fun iv => exists j, tag_at G 24 j = Some TQOwn /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx ->
In (lo, hi) (drain_W sp ++ Wx) -> lo <= x < hi -> qzone a LB0 G RE X x.
Proof. intros. edestruct drain_W_zone as [Q|Q]; try eassumption; [left; exact Q| right; lia]. Qed.

Lemma drain_tail : forall ra (sp : word) gp t2 a3 a4 a5 a6 a7 t0 t1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m m1 : word -> option byte) (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost)
(lo : Z) (JT JG JJ : list Z) (QA : aptr -> Z) (Wx : list (Z * Z)) (junk : list byte) (tq gq : qcache) (ll : list batch),
let g' := mkQ ll (q_bytes gq + q_bytes tq) in
let a1 := set_gq g' (set_tq q0 a) in
as_tq a = tq -> as_gq a = gq -> ll = q_list gq ++ q_list tq -> JJ = JG ++ JT ->
gcons a LB0 FS0 G RE X -> QOTH C a LB0 FS0 G RE X m ->

ia_inv m -> List.NoDup (JT ++ JG) -> (forall j, tag_at G 24 j = Some TQOwn -> In j (JT ++ JG)) ->
(forall c j, tag_at G c j = Some TQOwn -> c = 24) ->
List.NoDup (qall [] a) -> (forall p, In p (qall [] a) -> qptr_rep a LB0 G RE m QA p) ->
(forall c i p, tag_at G c i = Some (TQuar p) -> In p (qall [] a) /\ aptr_cls p = c) ->
0 <= q_bytes tq <= 2 * QB -> 0 <= q_bytes gq <= QB -> qwf tq -> qwf gq ->
Forall (fun j => tag_at G 24 j = Some TQOwn) JT -> Forall (fun j => tag_at G 24 j = Some TQOwn) JG ->

mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -48) -> band_lo <= lo -> lo <= bv_unsigned sp - DRAIN_STACK ->
rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
munch (drain_W (bv_unsigned sp) ++ Wx) m m1 -> wmono asegs m m1 ->
Forall (fun iv => exists j, tag_at G 24 j = Some TQOwn /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx ->
rw_cells asegs m1 (TQ X) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (q_bytes tq))] ->
rw_cells asegs m1 GQ [C8 (wz (Z.of_nat (length ll))); C8 (wz (q_first RE JJ)); C8 (wz (q_last RE JJ)); C8 (wz (q_bytes gq))] ->
rw_cells asegs m1 QMUT [C4 (wz 1)] ->
batches_mem RE m1 QA ll JJ ->
q_bytes gq + q_bytes tq <= kQMaxSize ->
evt asegs (fun ms' => aimplT atn (if kQMaxSize <? q_bytes g' then recycle (ae_L RE) a1 else tret a1) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs)) ms')
(MS (mkR ra (wz (bv_unsigned sp + -48)) gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz (TQ X)) (wz (rl_T X + 208)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x410e8) fc None m1 (seg_rom asegs)).
Proof.
intros until ll; intros g' a1 Etq Egq Ell EJJ GC QO HI ND TQO C24 NDP REP TQP BT BG QWT QWG FJT FJG MI ST CEIL LO FR MU WM HWx TQC GQC HM BM NOREC.
assert (EQA : qall [] a = qptrs tq ++ qptrs gq) by (unfold qall; rewrite Etq, Egq; reflexivity). rewrite EQA in NDP, REP, TQP. subst ll JJ.
pose proof CEIL as CEIL'. idtac. unfold DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
unfold QB in BT, BG.
pose proof (proj1 QO) as RT.
assert (RT1 : RTconst RE X m1).
{ eapply RTconst_frame; [exact RT| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|].
intros x Fx _. apply outside_intro. intros lo' hi' Hin Hx.
destruct (drain_W_zone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx Hin Hx) as [Q|Q].
- exact (fpQ_RTconst a LB0 FS0 G RE X GC x Q Fx).
- pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(left; exact Fx)). lia. }
rtc RT1 26%nat K26.
pose proof (munch_refl (drain_W (bv_unsigned sp)) m1) as MU1. pose proof (wmono_refl asegs m1) as WM1.

pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi in PC. rewrite ?KHI_eq in PK. idtac.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (T_obj RE X)) as (_ & TKq & TCq & _). cbn [fst snd] in TKq, TCq. pose proof SH_band as SHB0.
assert (OW : forall W' x, munch W' m1 m1 -> (forall iv, In iv W' -> In iv (drain_W (bv_unsigned sp))) ->
(prim_lo RE <= x < prim_hi RE \/ 0x7fff7000 <= x < 0x10007fff8000 \/ (IA <= x < 0x1743f8 \/ IA_FLAG <= x < IA_FLAG + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e)) -> outside W' x).
{ intros W' x _ SUB Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. apply SUB in Hin. unfold drain_W, QMUT, GQ, TQ, A_INSTANCE in Hin. cbn in Hin.
unfold IA, IA_FLAG in Hx. unfold prim_hi, prim_lo in *.
destruct Hx as [Hx|[Hx|[Hx|(e & He & Hx)]]].
- destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
- destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (first [ clear - Y1 Hx x CEIL' LO lo sp BAND Y2 PK TK X RE; lia | lia ]).
- pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & _ & _ & _ & _ & _ & D3). rewrite ?KHI_eq in E2. idtac.
pose proof (proj1 (List.Forall_forall _ _) D3 _ (T_obj RE X)) as D. unfold iv_disjoint in D; cbn [fst snd] in D.
destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (first [ clear - E3 Y1 Hx e x CEIL' LO lo sp BAND D E2 Y2 PK TK X RE; lia | lia ]). }
assert (OWx : forall x, ((exists c i t, tag_at G c i = Some t /\ t <> TQOwn /\ in_iv (slot_beg RE c i, class_size c) x)
\/ 0x7fff7000 <= x < 0x10007fff8000 \/ (IA <= x < 0x1743f8 \/ IA_FLAG <= x < IA_FLAG + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e)) -> outside Wx x).
{ intros x Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as (j & Tj & B1 & B2). cbn [fst snd] in B1, B2.
pose proof (slot_prim _ _ _ _ _ _ GC 24 j TQOwn Tj) as (P1 & P2 & _). rewrite class_size_24 in P2. unfold IA, IA_FLAG in Hx. unfold prim_hi, prim_lo in *.
destruct Hx as [(c & i & t & Ht & NT & [S1 S2])|[Hx|[Hx|(e & He & Hx)]]]; cbn [fst snd] in *.
- assert (NE : c <> 24 \/ i <> j) by (destruct (Z.eq_dec c 24) as [->|]; [right; intros ->; rewrite Tj in Ht; inversion Ht; subst; apply NT; reflexivity| left; assumption]).
pose proof (slots_disjoint _ _ _ _ _ _ GC c i t 24 j TQOwn Ht Tj NE). rewrite class_size_24 in *. (first [ clear - H B2 B1 j Y2 Y1 hi' lo' S2 S1 i c x PK TK X RE BAND; lia | lia ]).
- lia.
- lia.
- pose proof (sec_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & _ & _ & _ & D1 & _). unfold iv_disjoint, prim_lo in D1; cbn [fst snd] in D1. (first [ clear - D1 E2 P2 P1 B2 B1 j Y2 Y1 hi' lo' Hx e x PK TD TK X RE BAND; lia | lia ]). }
unfold drain_W, QOBJ, GQ, QMUT, TQ, A_INSTANCE in *.
change (977752 + 880 + 4) with 978636 in *. change (977752 + 880) with 978632 in *.
change (977752 + 888 + 32) with 978672 in *. change (977752 + 888) with 978640 in *. change (977752 + 728) with 978480 in *.
replace (rl_T X + 80 + 32) with (rl_T X + 112) in MU, MU1, OW by lia.

assert (BUILD : forall (rb bg : Z) m2,
rw_cells asegs m2 (rl_T X + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
rw_cells asegs m2 978640 [C8 (wz (Z.of_nat (length (q_list gq ++ q_list tq)))); C8 (wz (q_first RE (JG ++ JT)));
C8 (wz (q_last RE (JG ++ JT))); C8 (wz (q_bytes gq + q_bytes tq))] ->
rw_cells asegs m2 978632 [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)] ->
munch [(bv_unsigned sp + -48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112)] m1 m2 ->
wmono asegs m1 m2 -> q_bytes gq + q_bytes tq <= bg ->
RQuarM rb QB bg [] a1 LB0 G RE X m2).
{ intros rb bg m2 TQC2 GQC2 HM2 MU2 WM2 HBG.
assert (MU02 : munch ([(bv_unsigned sp + -48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112)] ++ Wx) m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx. apply outside_app in Hx as [Hx _]. exact Hx. }
pose proof (wmono_trans asegs _ _ _ WM WM2) as WM02.
assert (AG02 : forall P : Z -> Prop,
(forall x, P x -> ((exists c i t, tag_at G c i = Some t /\ t <> TQOwn /\ in_iv (slot_beg RE c i, class_size c) x)
\/ 0x7fff7000 <= x < 0x10007fff8000 \/ (996288 <= x < 0x1743f8 \/ 1580104 <= x < 1580104 + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e))) -> agree_on asegs P m m2).
{ intros P HP. eapply agree_on_of_munch; [exact MU02| exact WM02|]. intros x Px _. apply outside_app. split; [| apply OWx; apply HP; exact Px].
apply OW; [apply munch_refl| intros iv Hiv; exact Hiv|].
destruct (HP x Px) as [(c & i & t & Ht & _ & [S1 S2])|Hx]; [| right; exact Hx]. left.
pose proof (slot_prim _ _ _ _ _ _ GC c i t Ht) as (P1 & P2 & _). cbn [fst snd] in S1, S2. unfold prim_hi in *. lia. }
assert (AG12 : forall P : Z -> Prop,
(forall x, P x -> (prim_lo RE <= x < prim_lo RE + 2^37 + 4096 \/ 0x7fff7000 <= x < 0x10007fff8000 \/ (996288 <= x < 0x1743f8 \/ 1580104 <= x < 1580104 + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e))) -> agree_on asegs P m1 m2).
{ intros P HP. eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros x Px _. apply OW; [apply munch_refl| intros iv Hiv; exact Hiv| apply HP; exact Px]. }
exists [], (JG ++ JT), QA. subst a1 g'. cbn [as_tq as_gq set_gq set_tq as_reg qall map app].
assert (SLOTZ : forall j x, In j (JG ++ JT) -> in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x ->
prim_lo RE <= x < prim_lo RE + 2^37 + 4096 \/ 0x7fff7000 <= x < 0x10007fff8000 \/ (996288 <= x < 0x1743f8 \/ 1580104 <= x < 1580104 + 4)
\/ (exists e, In e (as_reg a) /\ se_beg e <= x < se_beg e + se_size e)).
{ intros j x Hj Hx. assert (Tj : tag_at G 24 j = Some TQOwn).
{ apply in_app_iff in Hj as [Hj|Hj]; [exact (proj1 (List.Forall_forall _ _) FJG j Hj)| exact (proj1 (List.Forall_forall _ _) FJT j Hj)]. }
pose proof (slot_prim _ _ _ _ _ _ GC 24 j TQOwn Tj) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2 |- *.
destruct Hx as [[S1 S2]|Hx]; cbn [fst snd] in *; [left; lia| right; left]. pose proof (slot_band _ _ _ _ _ _ GC 24 j TQOwn x Tj Hx). pose proof SH_band. lia. }
split.
{
split; [exact TQC2|]. split; [exact I|]. split; [constructor| apply qwf_q0]. }
split.
{
split; [exact GQC2|]. split; [| split; [apply Forall_app; split; assumption|]].
- eapply (batches_mem_agree RE (fun x => exists j, In j (JG ++ JT) /\ (in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x)));
[apply AG12| exact BM| | |].
+ intros x (j & Hj & Hx). exact (SLOTZ j x Hj Hx).
+ apply List.Forall_forall. intros j Hj x Hx. exists j. split; [exact Hj| left; exact Hx].
+ apply List.Forall_forall. intros j Hj x Hx. exists j. split; [exact Hj| right; exact Hx].
+ apply Forall_app. split; [exact (proj1 QWG)| exact (proj1 QWT)].
- cbn [q_list q_bytes]. apply qwf_app; [exact QWG| exact QWT]. }
split; [exact HM2|].
split.
{ eapply ia_inv_agree; [apply AG02| exact HI|]; [| intros x Hx; exact Hx]. intros x Hx. right; right; left. unfold IA, IA_FLAG in Hx. lia. }
split; [apply NoDup_app_comm; exact ND|].
split; [intros j Hj; apply in_app_iff; apply or_comm; apply in_app_iff; apply TQO; exact Hj|].
split; [exact C24|].
assert (EQL : forall p, In p (qptrs {| q_list := q_list gq ++ q_list tq; q_bytes := q_bytes gq + q_bytes tq |}) <-> In p (qptrs tq ++ qptrs gq)).
{ intros p. rewrite (qptrs_app _ _ _ 0). rewrite !in_app_iff.
replace (qptrs {| q_list := q_list gq; q_bytes := 0 |}) with (qptrs gq) by (destruct gq; reflexivity).
replace (qptrs {| q_list := q_list tq; q_bytes := 0 |}) with (qptrs tq) by (destruct tq; reflexivity). (first [ clear - p SHB0 TKq TD TK SPR BG BT gq tq sp X RE BAND; tauto | tauto ]). }
split.
{ rewrite (qptrs_app _ _ _ 0).
replace (qptrs {| q_list := q_list gq; q_bytes := 0 |}) with (qptrs gq) by (destruct gq; reflexivity).
replace (qptrs {| q_list := q_list tq; q_bytes := 0 |}) with (qptrs tq) by (destruct tq; reflexivity).
rewrite qptrs_q0. cbn [app]. apply NoDup_app_comm. exact NDP. }
split.
{ intros p Hp. apply EQL in Hp. pose proof (REP p Hp) as R. destruct p as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
pose proof (slot_prim _ _ _ _ _ _ GC _ _ _ Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
eapply (qchunk_mem_agree (fun x => slot_beg RE (class_of n) i <= x < slot_beg RE (class_of n) i + class_size (class_of n)
\/ SH (slot_beg RE (class_of n) i) <= x < SH (slot_beg RE (class_of n) i) + (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) / 8));
[apply AG02| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; exact Hx].
intros x [Hx|Hx]; [left; exists (class_of n), i, (TQuar (APrim id n)); split; [exact Ht|]; split; [discriminate| split; cbn [fst snd]; lia]| right; left].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia.
pose proof (slot_band _ _ _ _ _ _ GC _ _ _ x Ht ltac:(split; cbn [fst snd]; lia)). pose proof SH_band. lia.
- destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
pose proof (sec_facts _ _ _ _ _ _ GC _ Hin) as (E1 & E2 & E3 & E4 & _). cbn [se_beg se_size se_req] in E1, E2, E3, E4.
pose proof kconsts as (_ & _ & _ & _ & KP & _).
eapply (qchunk_mem_agree (fun x => mb + kPage <= x < mb + sec_map_size n \/ SH (mb + kPage) <= x < SH (mb + kPage) + (mb + sec_map_size n - (mb + kPage)) / 8));
[apply AG02| exact QM| intros x Hx; left; exact Hx| intros x Hx; right; exact Hx].
intros x [Hx|Hx]; [do 3 right; exists (mkSec mb (sec_map_size n) n); split; [exact Hin| cbn [se_beg se_size]; lia]| right; left].
eapply (sec_band _ _ _ _ _ _ GC _ x Hin). cbn [se_beg se_size]. split; cbn [fst snd]; [lia|].
replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. lia. }
split; [intros c i p Ht; destruct (TQP c i p Ht) as [H1 H2]; split; [apply EQL; exact H1| exact H2]|].
split; [constructor|]. cbn [q_bytes q0]. unfold QB in *. lia. }
hide MU. hide WM.
step. step. step.
step. stp.
step.
recast HM [C1 (b8 1); C1 (b8 0); C1 (b8 0); C1 (b8 0)].
stp.
rewrite unsigned_lit in HM by lia.
step. step.
step.
destruct (Z.ltb_spec0 kQMaxSize (q_bytes gq + q_bytes tq)) as [BIG|SMALL]; rewrite KMX in *.
2:{
ifz.
do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. replace (268435456 <? q_bytes g') with false by (symmetry; apply Z.ltb_ge; subst g'; cbn [q_bytes]; lia).
apply aimplT_ret. apply evt_done.
unhide MU. unhide WM.
lazymatch goal with |- ?hd (MS _ _ _ _ _ ?mf _) =>
assert (MUf : munch ([(bv_unsigned sp + -48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112)] ++ Wx) m mf)
by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU1]; intros x Hx; apply outside_app in Hx as [Hx _]; exact Hx);
pose proof (wmono_trans asegs _ _ _ WM WM1) as WMf
end.
unfold qret_post. do 15 eexists. eexists. exists G. split; [reflexivity|]. split; [reflexivity|].
split; [assumption|]. split; [exact ST|].
split.
{ eapply aheap_presA_of_munch; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MUf| exact WMf|].
intros lo' hi' x Hin Hx. eapply (drain_W_zone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx); [| exact Hx].
unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [app Z.add Z.sub] in Hin |- *.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact Hin. }
split.
{
lazymatch type of MUf with munch ?W _ _ => assert (QZW : forall lo' hi' x, In (lo', hi') W -> lo' <= x < hi' -> qzone a LB0 G RE X x) end.
{ intros lo' hi' x Hin Hx. eapply (drain_W_qzone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx); [| exact Hx].
unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [app Z.add Z.sub] in Hin |- *.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact Hin. }
split.
- eapply (depot_keep_of_pzone a LB0 FS0 G RE X m _ _ GC MUf WMf). intros lo' hi' x Hin Hx.
destruct (QZW lo' hi' x Hin Hx) as [QZ|QZ]; [left; exact QZ| do 3 right; exact QZ].
- eapply (errno_keep_of_ezone a LB0 FS0 G RE X m _ _ GC MUf WMf). intros lo' hi' x Hin Hx. apply ezone_of_qzone. exact (QZW lo' hi' x Hin Hx). }
split.
{ eapply gcons_ext; [exact GC| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia]. }
split.
{ eapply (QOTH_ext C a); [| intros; reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl| apply same_tags_refl].
eapply QOTH_munch; [exact GC| exact QO| exact MUf| exact WMf|].
intros lo' hi' x Hin Hx. eapply (drain_W_qzone a LB0 FS0 G (bv_unsigned sp) Wx lo' hi' x GC ltac:(lia) HWx); [| exact Hx].
unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [app Z.add Z.sub] in Hin |- *.
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact Hin. }
apply (BUILD 0 QB); [assumption| assumption| exact HM| exact MU1| exact WM1| unfold QB; lia]. }

exfalso. clear - BIG NOREC. lia.
Qed.

Lemma drain_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (lo : Z),
QRUN C 0 (2 * QB) QB [] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - DRAIN_STACK ->
q_bytes (as_gq a) + q_bytes (as_tq a) <= kQMaxSize ->
aimplT atn (drain (ae_L RE) a) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz (TQ X)) (wz (rl_T X + 208)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz drain_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros QR MI ST CEIL LO NOREC.
pose proof CEIL as CEIL'. idtac. unfold DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & _).
destruct QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND).
destruct HT as (TQC & BMT & FJT & QWT). destruct HG as (GQC & BMG & FJG & QWG). unfold QB in BND.
pose proof (batches_mem_nx_length _ _ _ _ _ _ BMT) as LT. pose proof (batches_mem_nx_length _ _ _ _ _ _ BMG) as LG.
pose proof (qwf_length_bound _ QWT) as QLT. pose proof (qwf_length_bound _ QWG) as QLG. rewrite KBB in QLT, QLG.
pose proof (proj1 QO) as RT. rtc RT 26%nat K26.
pose proof (wmono_refl asegs m) as WM.

pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.

assert (TAILEQ : forall ll tq gq, as_tq a = tq -> as_gq a = gq -> ll = q_list gq ++ q_list tq ->
drain (ae_L RE) a = (if kQMaxSize <? q_bytes gq + q_bytes tq
then recycle (ae_L RE) (set_gq (mkQ ll (q_bytes gq + q_bytes tq)) (set_tq q0 a))
else tret (set_gq (mkQ ll (q_bytes gq + q_bytes tq)) (set_tq q0 a)))).
{ intros ll tq gq E1 E2 E3. unfold drain. rewrite E1, E2. subst ll. reflexivity. }
remember (as_tq a) as tq eqn:Etq. remember (as_gq a) as gq eqn:Egq. symmetry in Etq, Egq.
assert (EQA : qall [] a = qptrs tq ++ qptrs gq) by (unfold qall; rewrite Etq, Egq; reflexivity).
destruct tq as [tl tb]. destruct gq as [gl gb]. cbn [q_list q_bytes] in *.
unfold drain_entry, QOBJ, GQ, QMUT, TQ, A_INSTANCE in *.
change (977752 + 880 + 4) with 978636 in *. change (977752 + 880) with 978632 in *.
change (977752 + 888 + 32) with 978672 in *. change (977752 + 888) with 978640 in *. change (977752 + 728) with 978480 in *.

assert (KEEP : forall (W' : list (Z * Z)) (m' : word -> option byte) bs J (jx fin : Z),
batches_mem_nx RE m QA bs J fin -> Forall bwf bs -> Forall (fun j => tag_at G 24 j = Some TQOwn) J ->
munch W' m m' -> wmono asegs m m' ->
(forall iv, In iv W' -> In iv [(bv_unsigned sp + -48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112)]
\/ (tag_at G 24 jx = Some TQOwn /\ ~ In jx J /\ slot_beg RE 24 jx <= fst iv /\ snd iv <= slot_beg RE 24 jx + 8192)) ->
batches_mem_nx RE m' QA bs J fin).
{ intros W' m' bs J jx fin BMx FB FJ MUx WMx HW.
eapply (batches_mem_nx_keep (fun x => outside W' x)); [exact BMx| exact FB| | exact WMx|].
- eapply agree_on_of_munch; [exact MUx| exact WMx|]. intros x Hx _; exact Hx.
- intros j x Hj Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
pose proof (proj1 (List.Forall_forall _ _) FJ j Hj) as Tj.
pose proof (slot_prim _ _ _ _ _ _ GC 24 j TQOwn Tj) as (P1 & P2 & P3 & _). unfold prim_hi, prim_lo in P1, P2. rewrite class_size_24 in *.
destruct (HW _ Hin) as [Hin'|(Tjx & NJ & B1 & B2)]; cbn [fst snd] in *.
+ cbn in Hin'. destruct Hx as [[S1 S2]|Hx]; cbn [fst snd] in *.
* destruct Hin' as [E|[E|[E|[E|[]]]]]; injection E as <- <-; (first [ clear - P2 Y1 S2 x j PC LG LT CEIL' LO gl tl JG JT lo sp RE BAND P1 Y2 S1 PK P3 TD TK X; lia | lia ]).
* pose proof (slot_band _ _ _ _ _ _ GC 24 j TQOwn x Tj Hx).
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (T_obj RE X)) as (_ & TKz & _). cbn [fst snd] in TKz. pose proof SH_band.
destruct Hin' as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
+ assert (NE : 24 <> 24 \/ j <> jx) by (right; intros ->; exact (NJ Hj)).
pose proof (slots_disjoint _ _ _ _ _ _ GC 24 j TQOwn 24 jx TQOwn Tj Tjx NE) as D. rewrite class_size_24 in D.
destruct Hx as [[S1 S2]|Hx]; cbn [fst snd] in *; [(first [ clear - D B2 B1 P3 P1 Y2 Y1 hi' lo' S2 S1 x j jx PK LG LT TD TK gl tl JG JT X RE BAND; lia | lia ])|].
pose proof (slot_band _ _ _ _ _ _ GC 24 j TQOwn x Tj Hx). pose proof (slot_prim _ _ _ _ _ _ GC 24 jx TQOwn Tjx) as (Q1 & Q2 & _).
unfold prim_hi, prim_lo in Q1, Q2. pose proof SH_band. pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PKz & _). unfold prim_lo in PKz. rewrite ?KHI_eq in PKz. lia. }
pose proof QWT as [FBT _]. pose proof QWG as [FBG _]. cbn [q_list] in FBT, FBG.
destruct tl as [|tb0 tl'].
{
destruct JT as [|j0 JT']; [| cbn in LT; discriminate]. cbn [length Z.of_nat] in TQC.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112)] m) as MU.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
do 4 step.
recast HM [C4 (wz 0)].
amo_step (amo_aligned_intro4 978632 ltac:(lia) ltac:(reflexivity)).
do 4 step.
amo_step (amo_aligned_intro4 978632 ltac:(lia) ltac:(reflexivity)).
step. if_lit.
step. step. if_lit.
step. step. ifz.
step. step. ifz.
eapply evt_mono; [eapply (drain_tail ra sp gp t2 a3 _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ s a LB0 FS0 G lo [] JG JG QA [] _
(mkQ [] tb) (mkQ gl gb) gl Etq Egq)
| cbv beta; intros ms' H'; rewrite (TAILEQ gl _ _ eq_refl eq_refl); [exact H'| cbn [q_list]; symmetry; apply app_nil_r] ].
all: try assumption; try eassumption.
- cbn [q_list]. symmetry; apply app_nil_r.
- symmetry; apply app_nil_r.
- unfold QB in *; cbn [q_bytes]; lia.
- unfold QB in *; cbn [q_bytes]; lia.
- rewrite app_nil_r. unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [Z.add].
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact MU.
- constructor.
- unfold batches_mem. eapply (KEEP _ _ _ _ 0 0); [exact BMG| exact FBG| exact FJG| exact MU| exact WM| intros iv Hiv; left; exact Hiv]. }

destruct JT as [|j0 JT']; [cbn in LT; discriminate|]. cbn [length] in LT, TQC, QLT.
destruct (split_last gl) as [[gf gbl]|] eqn:ESG; pose proof (split_last_spec gl) as SLG; rewrite ESG in SLG; subst gl.
2:{
destruct JG as [|k0 JG']; [| cbn in LG; discriminate]. cbn [length Z.of_nat] in GQC.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112)] m) as MU.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
do 4 step.
recast HM [C4 (wz 0)].
amo_step (amo_aligned_intro4 978632 ltac:(lia) ltac:(reflexivity)).
do 4 step.
amo_step (amo_aligned_intro4 978632 ltac:(lia) ltac:(reflexivity)).
step. if_lit. step. step. if_lit.
step. step. ifz.
step. step. ifz.
step. step. ifz.
step. step.
step. step.
step. step.
stp. stp. stp.
eapply evt_mono; [eapply (drain_tail ra sp gp t2 a3 _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ s a LB0 FS0 G lo
(j0 :: JT') [] (j0 :: JT') QA [] _ (mkQ (tb0 :: tl') tb) (mkQ [] gb) (tb0 :: tl') Etq Egq)
| cbv beta; intros ms' H'; rewrite (TAILEQ (tb0 :: tl') _ _ eq_refl eq_refl); [exact H'| reflexivity] ].
all: try assumption; try eassumption.
- reflexivity.
- reflexivity.
- unfold QB in *; cbn [q_bytes]; lia.
- unfold QB in *; cbn [q_bytes]; lia.
- rewrite app_nil_r. unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [Z.add].
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact MU.
- constructor.
- unfold batches_mem. eapply (KEEP _ _ _ _ 0 0); [exact BMT| exact FBT| exact FJT| exact MU| exact WM| intros iv Hiv; left; exact Hiv]. }

destruct (split_last JG) as [[JGF jgl]|] eqn:ESJ; pose proof (split_last_spec JG) as SLJ; rewrite ESJ in SLJ; subst JG.
2:{ exfalso. rewrite length_app in LG. cbn in LG. lia. }
replace (Z.of_nat (length (gf ++ [gbl]))) with (Z.of_nat (length gf) + 1) in GQC, QLG by (rewrite length_app; cbn [length]; lia).
rewrite q_last_snoc in GQC.
unfold batches_mem in BMG. apply batches_mem_nx_snoc_inv in BMG as [BMF BL]; [| rewrite !length_app in LG; cbn in LG; lia].
destruct BL as (BCl & BAl & BJl & BSl). hide BAl. hide BJl. hide BSl.
apply Forall_app in FJG as [FJGF FJl]. apply Forall_cons_iff in FJl as [Tjl _].
apply Forall_app in FBG as [FBGF FBl]. apply Forall_cons_iff in FBl as [Bwf _].
set (Bgl := slot_beg RE 24 jgl) in *.
pose proof (slot_prim _ _ _ _ _ _ GC 24 jgl TQOwn Tjl) as (Pg1 & Pg2 & Pg3 & _). unfold prim_hi, prim_lo in Pg1, Pg2. rewrite class_size_24 in Pg2. fold Bgl in Pg1, Pg2, Pg3.
pose proof (fun y H => slot_band _ _ _ _ _ _ GC 24 jgl TQOwn y Tjl H) as SBg. fold Bgl in SBg.
assert (SHBg : 0x2008fff7000 <= SH Bgl /\ SH Bgl + 1024 <= SH band_lo).
{ split; [apply (SBg (SH Bgl))| enough (SH Bgl + 1023 < SH band_lo) by lia; apply (SBg (SH Bgl + 1023))]; split; cbn [fst snd]; rewrite ?class_size_24; try (first [ clear - QLT LG LT Bgl jgl JGF gbl gf tb tl' JT' RE BAND Pg3 Pg1 PK; lia | lia ]).
all: change (8192 / 8) with 1024; lia. }
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (T_obj RE X)) as (_ & TKg & _). cbn [fst snd] in TKg. pose proof SH_band as SHBg0.
assert (NJl : ~ In jgl (JGF ++ j0 :: JT')).
{ intros Hin. rewrite app_assoc in ND. pose proof (NoDup_remove_2 _ [] jgl ND) as NI. rewrite app_nil_r in NI. apply NI.
apply in_app_iff. apply in_app_iff in Hin. (first [ clear - Hin SHBg0 TKg SHBg TD TK SPR BND Bgl jgl JGF gb tb JT' j0 sp X RE BAND; tauto | tauto ]). }
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (978632, 978636); (978640, 978672); (rl_T X + 80, rl_T X + 112); (Bgl, Bgl + 8)] m) as MU.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
do 4 step.
recast HM [C4 (wz 0)].
amo_step (amo_aligned_intro4 978632 ltac:(lia) ltac:(reflexivity)).
do 4 step.
amo_step (amo_aligned_intro4 978632 ltac:(lia) ltac:(reflexivity)).
step. if_lit. step. step. if_lit.
step. step. ifz.
step. step. ifz.
step. step. ifz.
step.
step. step.
step.
step.
step. step.
step.
stp. stp. stp.

lazymatch type of GQC with rw_cells _ ?mm ?ad [C8 (wz ?len); C8 _; C8 ?lst; C8 ?byt] =>
change (rw_cells asegs mm ad [C8 (wz len); C8 (wz (q_first RE (JGF ++ [jgl]))); C8 lst; C8 byt]) in GQC;
replace len with (Z.of_nat (length ((gf ++ [gbl]) ++ tb0 :: tl'))) in GQC by (rewrite !length_app; cbn [length]; lia)
end.
rewrite <- (q_first_app RE (JGF ++ [jgl]) (j0 :: JT')) in GQC by (destruct JGF; discriminate).
rewrite <- (q_last_app RE (JGF ++ [jgl]) (j0 :: JT')) in GQC by discriminate.
unhide BAl. unhide BJl. unhide BSl. subst Bgl.
eapply evt_mono; [eapply (drain_tail ra sp gp t2 a3 _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ s a LB0 FS0 G lo
(j0 :: JT') (JGF ++ [jgl]) ((JGF ++ [jgl]) ++ j0 :: JT') QA [(slot_beg RE 24 jgl, slot_beg RE 24 jgl + 8)] _
(mkQ (tb0 :: tl') tb) (mkQ (gf ++ [gbl]) gb) ((gf ++ [gbl]) ++ tb0 :: tl') Etq Egq)
| cbv beta; intros ms' H'; rewrite (TAILEQ ((gf ++ [gbl]) ++ tb0 :: tl') _ _ eq_refl eq_refl); [exact H'| reflexivity] ].
all: try assumption; try eassumption.
- reflexivity.
- reflexivity.
- unfold QB in *; cbn [q_bytes]; lia.
- unfold QB in *; cbn [q_bytes]; lia.
- apply Forall_app. split; [exact FJGF| constructor; [exact Tjl| constructor]].
- unfold drain_W, QMUT, GQ, TQ, A_INSTANCE. cbn [Z.add app].
replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. replace (rl_T X + 80 + 32) with (rl_T X + 112) by lia. exact MU.
- constructor; [| constructor]. exists jgl. cbn [fst snd]. split; [exact Tjl| lia].
-
unfold batches_mem. apply batches_mem_nx_app.
+ apply batches_mem_nx_snoc.
* eapply (KEEP _ _ _ _ jgl); [exact BMF| exact FBGF| exact FJGF| exact MU| exact WM|].
intros iv Hiv. cbn in Hiv. destruct Hiv as [E|[E|[E|[E|[E|[]]]]]]; try (left; rewrite <- E; cbn; (first [ clear - SHBg0 TKg SHBg TD TK SPR BND gb jgl tb sp X RE BAND; tauto | tauto ])).
right. rewrite <- E. cbn [fst snd]. split; [exact Tjl|]. split; [| lia]. intros Hin. apply NJl. apply in_app_iff. left; exact Hin.
*
split; [exact BCl|]. split; [| split].
-- eapply u64arr_agree; [| exact BAl|].
++ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Hx _. exact Hx.
++ intros x Hx. rewrite length_map in Hx. pose proof Bwf as (BW1 & BW2 & _). rewrite KBC in BW2.
apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Y1 BW2 BW1 Hx x Pg2 Pg1 PC PK QLT LG LT CEIL' LO JGF gbl gf jgl tb tl' JT' lo sp RE BAND Y2 Pg3 TD TK X; lia | lia ]).
-- eapply hjunk_wmono; [exact BJl| exact WM].
-- eapply rw_cells_agree; [| exact BSl|].
++ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Hx _. exact Hx.
++ intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; (first [ clear - Y1 Hx x SHBg0 SHBg QLT LG LT CEIL' LO JGF gbl gf jgl tb tl' JT' lo sp RE BAND Y2 Pg1 PK TKg X; lia | lia ]).
+ eapply (KEEP _ _ _ _ jgl); [exact BMT| exact FBT| exact FJT| exact MU| exact WM|].
intros iv Hiv. cbn in Hiv. destruct Hiv as [E|[E|[E|[E|[E|[]]]]]]; try (left; rewrite <- E; cbn; (first [ clear - SHBg0 TKg SHBg TD TK SPR BND gb jgl tb sp X RE BAND; tauto | tauto ])).
right. rewrite <- E. cbn [fst snd]. split; [exact Tjl|]. split; [| lia]. intros Hin. apply NJl. apply in_app_iff. right; exact Hin.
Qed.
End S.
End Mqi.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).

Definition strnlen_stub : Z := 0x4fd2c.
Definition strnlen_icpt_entry : Z := 0x50078.
Definition STRNLEN_ICPT_STACK : Z := 2144 + STRNLEN_STACK.

Lemma strnlen_res_bound : forall n buf, 0 <= n -> 0 <= strnlen_res n buf <= n
/\ memchr_len 0 n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
intros n buf Hn. unfold strnlen_res, memchr_len. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [| lia].
apply find_byte_lt in E. rewrite length_firstn in E. lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n lo : Z) (buf : list byte).
Let L := memchr_len 0 n buf.
Let R := strnlen_res n buf.
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - STRNLEN_ICPT_STACK.
Hypothesis A0 : 0 < A.
Hypothesis N0 : 0 <= n < 2^64.
Hypothesis OK : memchr_ok A 0 n buf.
Hypothesis BSTK : A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A.
Hypothesis RNG : rng_ok m A L.
Let usp := bv_unsigned sp.
Let POST := strnlen_post ra sp gp tp.

Lemma strnlen_icpt_tail : forall mf (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v s3v s4v s5v s6v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2144) -> stk asegs mf (usp + -2144) (usp + -64) ->
rw_cells asegs mf (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR rav (wz (usp + -2144)) gp tp t0 t1 t2 sp s1v (wz R) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x5013c) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
set (BAh := bytes_at) in BUF.
do 9 istep.
pose proof (stk_merge asegs _ _ _ _ ST1 ST2 ltac:(lia)) as ST. clear ST1 ST2.
release_frame FR ST (bv_unsigned sp).
step. step.
apply evt_done. unfold POST, strnlen_post. do 15 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact BUF.
Qed.

Lemma strnlen_icpt_check : forall mf (len : Z) (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v s6v t3 t4 t5 t6 : word)
(s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
len = L ->
munch [(lo, usp)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
stk asegs mf lo (usp + -2144) -> stk asegs mf (usp + -2144) (usp + -64) ->
rw_cells asegs mf (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
bytes_at asegs mf A buf ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR rav (wz (usp + -2144)) gp tp t0 t1 t2 sp (wz len) (wz R) a1 a2 a3 a4 a5 a6 a7 (wz A) s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x500f4) fc None mf (seg_rom asegs)).
Proof.
intros until s11; intros -> MU WM MI ST1 ST2 FR BUF.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (memchr_len_bound 0 n buf ltac:(lia)) as [LB _]. fold L in LB.
pose proof RNG as (RA0 & RA47 & SOK & BIG & NB).
assert (RNG' : rng_ok mf A L).
{ eapply rng_ok_munch; [exact RNG| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. cbn. rewrite !SH_eq, ?KHI_eq in *. left. Z.div_mod_to_equations. lia. }
pose proof (shadow_base_munch _ _ _ SB MU ltac:(rt_wzones)) as SB2.
pose proof (rt_consts_at_munch _ _ _ RC MU WM ltac:(rt_wzones)) as RC2.

step. step. step.
destruct (Z.eq_dec L 0) as [Lz|Lz].
{ if_cases K1; zify_cond K1; rewrite ?Lz, ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Lz; cbn in K1; lia].
step. rewrite Lz. ifz. step.
eapply strnlen_icpt_tail; [exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF]. }
destruct (Z_le_gt_dec L 64) as [N64|N65].
- unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
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
ms1 = MS (@bvmap_set 5 word 11 a1'' (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 14 a4'' (@bvmap_set 5 word 15 a5'' R)))) FF (wz 0x5013c) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (A + L + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (A + L - 1)) (SH A)) as [X1|X1].
+ ifz. replace (SH A) with (SH (A + L - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_a1 0x50210 ltac:(right; right; left; reflexivity) (Z.to_nat (SH (A + L - 1) - SH A)) (SH A)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4x. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1'' & a3'' & a4'' & a5'' & ->). simp_regs.
eapply strnlen_icpt_tail; [exact MU| exact WM| exact MI| exact ST1| exact ST2| exact FR| exact BUF].
- destruct RNG' as (_ & _ & SOK' & BIG' & _). destruct (BIG' ltac:(lia)) as [KA L43]. pose proof (SOK' ltac:(lia)) as SO2.
ifz. step. ifz. step. step. step.
pose proof (rt_mem_cells_of _ SB2 RC2) as RTM.
step. call_u rip_spec7; [exact RTM| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia| exact SO2| lia| lia| lia| exact KA|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST5 end.
step. step. step. ifz.
eapply strnlen_icpt_tail; [exact MU| exact WM| assumption| exact ST5| eassumption| eassumption| eassumption].
Qed.

Lemma strnlen_icpt_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
stk asegs m lo usp -> bytes_at asegs m A buf -> mem_inv asegs m ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strnlen_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros ST BUF MI.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold STRNLEN_ICPT_STACK, STRNLEN_STACK, MEMCHR_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
pose proof (strnlen_res_bound n buf ltac:(lia)) as [RB LR]. fold R L in RB, LR. fold R in LR.
pose proof (memchr_len_bound 0 n buf ltac:(lia)) as [LB _]. fold L in LB.
pose proof RNG as (RA0 & RA47 & _ & _ & _).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold strnlen_stub. step.
carve_frame 64%nat ST.
do 9 istep.
step. step. step. step.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof RCc as RCc'. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_15a5a8 _ RCc) as K11. pose proof (rt_161720 _ RCc) as K18. pose proof (rt_1f2663 _ RCc) as K23. clear RCc.

step. call_u tryinit_spec7; [exact K18| exact MI| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs _ lo (bv_unsigned sp + -2144) |- _ => rename H into ST1' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
step. stp. step. step. step. clear K11 K18.
first [ assert (BUF1 : bytes_at asegs mA A buf) by exact BUF
| assert (BUF1 : bytes_at asegs mA A buf) by (eapply bytes_at_transport; [exact BUF| exact MUs|]; cbn; lia) ].
clear BUF.
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SB1.
clear RCc'. pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RC1.
assert (RNG1 : rng_ok mA A L).
{ eapply rng_ok_munch; [exact RNG| exact MUs| exact WM|]. apply Forall_cons; [| apply Forall_nil]. cbn. rewrite !SH_eq, ?KHI_eq in *. left. Z.div_mod_to_equations. lia. }

step. call_u (strnlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mA A n buf lo);
[ unsigned_lits; exact ST1'| exact BUF1| exact OK| assumption| exact CEIL| unsigned_lits; unfold STRNLEN_STACK, MEMCHR_ICPT_STACK; lia
| unsigned_lits; lia| lia| lia| exact SB1| exact RC1| exact RNG1|].
match goal with H : stk asegs ?mc' lo (bv_unsigned sp + -2144), H2 : rw_cells asegs ?mc' (bv_unsigned sp + -64) _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
rename H into ST1x; rename H2 into FR' end.
match goal with H : stk asegs ?mc' (bv_unsigned sp + -2144) _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST2' end.
match goal with H : bytes_at asegs ?mc' A buf |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into BUF2 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mB end.
fold R.

step. ifz. step. stp. stp. clear K7 K23. step. ifz.

stp. step.
destruct (Z_lt_le_dec (R + 1) n) as [X1|X1].
-
ifz. step. step. step. step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply strnlen_icpt_check; [lia| exact MUs| exact WM| assumption| exact ST1x| exact ST2'| exact FR'| exact BUF2].
-
ifz. step. step. step. step. step. rewrite (unsigned_lit A), zb_lxor_ones by lia. ifz.
eapply strnlen_icpt_check; [lia| exact MUs| exact WM| assumption| exact ST1x| exact ST2'| exact FR'| exact BUF2].
Qed.
End S.

Theorem strnlen_icpt_spec {BAND : Band} :
forall (A n lo : Z) (buf : list byte),
forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
stk asegs m lo (bv_unsigned sp) -> bytes_at asegs m A buf -> memchr_ok A 0 n buf -> mem_inv asegs m ->
band_lo <= lo -> lo <= bv_unsigned sp - STRNLEN_ICPT_STACK ->
A + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= A ->
0 < A -> 0 <= n < 2^64 ->
shadow_base asegs m -> rt_consts_at asegs m ->
rng_ok m A (memchr_len 0 n buf) ->
evt asegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strnlen_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros ST BUF OK MI CEIL LO SEP A0 N0 SB RC RNG.
eapply strnlen_icpt_main; eassumption.
Qed.
