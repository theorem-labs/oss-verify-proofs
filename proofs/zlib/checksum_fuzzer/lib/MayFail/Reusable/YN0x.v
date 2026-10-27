(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0x.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN28.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ofMq (q : apathM) : apath :=
match q with MQ1 => Q1 | MQ2 => Q2 | MQ3 => Q3 | MQ4V1 => Q4V1 | MQ4V2 => Q4V2 | MQ5V1 => Q5V1 | MQ5V2 => Q5V2
| MQ6V1 => Q6V1 | MQ6V2 => Q6V2 | MQ7V1 => Q7V1 | MQ7V2 => Q7V2 end.
Definition ofMd (d : dvarM) : dvar :=
match d with MD0 => D0 | MD1 => D1 | MD2a => D2a | MD2b => D2b | MD2a' => D2a' | MD2b' => D2b' end.
Lemma toMq_of q : toMq (ofMq q) = q. Proof. destruct q; reflexivity. Qed.
Lemma toMd_of d : toMd (ofMd d) = d. Proof. destruct d; reflexivity. Qed.
Lemma nt_deq_A1s X U A g i am q d p n ap an :
Inv X (Some (g, i)) U A -> usedX X A g am ->
qfacts A g i am (toMq q) -> dfacts X A g am (toMd d) p n ap an ->
nt_deq g am A = IRet (tt, A1s A g am d p n ap an).
Proof.
intros HI Hu QF DF. pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg. pose proof (proj1 (inv_ctx HI)) as HLA.
unfold A1s. destruct d; cbn [toMd dfacts] in DF.
- destruct DF as (Hn & _). apply nt_deq_D0. exact Hn.
- destruct DF as (Hn & Hp & Hsc & Hhd & _). apply nt_deq_D1; auto; lia.
- destruct DF as (Hn & Hp & Hng & Hpg & Hpn & Up & Un & Hsc & HD).
apply nt_deq_D2a; auto; try lia; [exact (proj1 (usedX_MT _ _ _ _ Up)) | exact (proj1 (usedX_MT _ _ _ _ Un)) |].
intros E. exact (proj1 (HD g E) eq_refl).
- destruct DF as (Hn & Hp & Hng & Hpg & Hpn & Up & Un & Hsc & Hhd & Hav).
apply nt_deq_D2b; auto; try lia; [exact (proj1 (usedX_MT _ _ _ _ Up)) | exact (proj1 (usedX_MT _ _ _ _ Un))].
- destruct DF as (Hn & Hp & Hng & [-> ->] & Un & Hsc & HD).
apply nt_deq_D2a'; auto; try lia; [exact (proj1 (usedX_MT _ _ _ _ Un)) |].
intros E. exact (proj1 (HD g E) eq_refl).
- destruct DF as (Hn & Hp & Hng & [-> ->] & Un & Hsc & Hhd & Hav).
apply nt_deq_D2b'; auto; try lia. exact (proj1 (usedX_MT _ _ _ _ Un)).
Qed.
Definition nested_goal (fuel : nat) : Prop :=
forall X U L A g i am regs mem md gv q d p n ap an regs1 mem1,
(forall X' U' L' A' g' i' am' regs' mem' md', nt_goal B1 fuel X' U' L' A' g' i' am' regs' mem' md') ->
Inv X (Some (g, i)) U A -> usedX X A g am -> (forall c, 0 <= U c) ->
nt_C1 A g i am = true -> (fneed (am_sc am) <= S fuel)%nat -> bounded A ->
nt_pre B1 X (S fuel) L A regs mem md g i -> word_mem src0segs mem GUARD gv ->
validA q d = true -> qfacts A g i am (toMq q) -> dfacts X A g am (toMd d) p n ap an ->
am_maplen am = 0 ->
ntmid (g :: X) fuel L A (A1s A g am d p n ap an) g regs regs1 mem mem1 md gv ->
mreal src0segs (mkCfg (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)) md)
(nt_free_group fuel A g am (A1s A g am d p n ap an)) (nt_post B1 X (S fuel) L A regs mem md).
Section f.
Variables (X : list sptr) (U : Z -> Z) (fuel : nat) (L : layout) (A : astate) (g : sptr) (i : Z) (am : ameta).
Variables (regs regs1 : bvmap 5 word) (mem mem1 : word -> option byte) (md : Model) (gv : Z).
Variables (q : apath) (d : dvar) (p n : sptr) (ap an : ameta).
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HU : forall c, 0 <= U c.
Hypothesis HC1 : nt_C1 A g i am = true.
Hypothesis Hf : (fneed (am_sc am) <= S fuel)%nat.
Hypothesis HB : bounded A.
Hypothesis NPRE : nt_pre B1 X (S fuel) L A regs mem md g i.
Hypothesis VALID : validA q d = true.
Hypothesis QF : qfacts A g i am (toMq q).
Hypothesis DF : dfacts X A g am (toMd d) p n ap an.
Hypothesis Hml : 0 < am_maplen am.
Let s1 := A1s A g am d p n ap an.
Hypothesis NM : ntmid (g :: X) fuel L A s1 g regs regs1 mem mem1 md gv.
Let am1 := am_set_links None None am.
Let sc := am_sc am.
Let s2 := A_usg A sc am1 s1.
Let s4 := A_rec sc (A_seq s2).
Let mi : option (nat * Z) := Some (prid (am_mem am1), am_maplen am1 * 4096).
Lemma am1_fields : am_sc am1 = am_sc am /\ am_last am1 = am_last am /\ am_maplen am1 = am_maplen am /\ am_mem am1 = am_mem am.
Proof. unfold am1. destruct am; repeat split; reflexivity. Qed.
Lemma HP1 : P1 X U A g am s1.
Proof.
pose proof (step1 X U A g i am fuel HI Hu HC1 Hf) as K. rewrite (nt_deq_A1s X U A g i am q d p n ap an HI Hu QF DF) in K. exact K.
Qed.
Lemma HP2 : P2 X U A g s1 s2.
Proof.
pose proof (step2 X U A g i am fuel HI Hu HU HC1 Hf s1 HP1) as K. pose proof am1_fields as (E1 & E2 & E3 & E4).
rewrite <- E2 in K. rewrite (usage_eval A am s1 am1) in K. exact K.
Qed.
Lemma HP4 : P4 X U A g s4 mi /\ st_metas s4 = st_metas s2.
Proof.
pose proof am1_fields as (E1 & E2 & E3 & E4). unfold s4, mi, sc. rewrite E4, E3.
exact (P4_mapped X U A g i am fuel HI Hu Hf s1 s2 HP1 HP2 Hml).
Qed.
Lemma Mg4 : MT s4 g = Some (MUsed am1).
Proof.
destruct HP4 as [_ Em]. destruct HP2 as (_ & Em2 & _). destruct HP1 as (_ & Mg1 & _).
unfold MT. rewrite Em, Em2. exact Mg1.
Qed.
Lemma NDk s : (exists Y R V, Inv Y R V s) -> List.NoDup (keys s).
Proof. intros (Y & R & V & H). exact (proj1 (inv_keys H)). Qed.
Lemma AO1 : forall a, alloc_owned L s1 a -> alloc_owned L A a.
Proof.
destruct HP1 as (HI1 & _ & _ & _ & _ & _ & _ & UB1). pose proof (A1s_facts X U fuel L A g i am regs mem md q d p n ap an HI Hu NPRE VALID DF) as (Efp & _).
intros a. apply alloc_owned_same; [exact Efp|]. apply ub_same_user_blocks; [apply NDk; eauto | apply NDk; eauto | exact UB1].
Qed.
Lemma AO4 : forall a, alloc_owned L s4 a -> alloc_owned L A a.
Proof.
destruct HP4 as [(HI4 & UB4 & _ & Erg4 & _) Em]. destruct HP2 as (_ & Em2 & _). pose proof (A1s_facts X U fuel L A g i am regs mem md q d p n ap an HI Hu NPRE VALID DF) as (Efp & Erg1 & Ea1 & _).
intros a. apply alloc_owned_same.
- rewrite <- Efp. apply footprint_regions_areas; [rewrite Erg4; symmetry; exact Erg1|].
unfold s4, A_rec, A_seq, s2, A_usg. destruct (bounce_idx sc); destruct (st_seq _ =? 255); destruct (sc <? 48); cbn; exact Ea1 || reflexivity.
- apply ub_same_user_blocks; [apply NDk; eauto | apply NDk; eauto | exact UB4].
Qed.
Theorem mapped_mreal :
mreal src0segs (mkCfg (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)) md)
(nt_free_group fuel A g am s1) (nt_post B1 X (S fuel) L A regs mem md).
Proof.
pose proof HP1 as (HI1 & Mg1 & Eus & Erg1 & _). pose proof HP4 as [P4' Em4]. pose proof P4' as (HI4 & UB4 & _).
pose proof am1_fields as (E1 & E2 & E3 & E4). pose proof AO1 as AO1'. pose proof AO4 as AO4'. pose proof Mg4 as Mg4'.
pose proof (inv_groups HI g am Hu) as ((Glast & _) & Gml & Gsl & Gcl & Gmp & _).
destruct (Gmp Hml) as (r & rg & Emem & Hr & Hk & Hl & Hlen & _).
assert (Hsc64 : 0 <= am_sc am1 < 64) by (rewrite E1; destruct Gcl as [(C & _)|(C & _)]; lia).
assert (Hlast1 : 0 <= am_last am1 <= 31) by (rewrite E2; lia).
assert (Hml1 : 0 < am_maplen am1) by (rewrite E3; exact Hml).
assert (Hmem1 : am_mem am1 = YO0i.SP r 0) by (rewrite E4; exact Emem).
assert (Hrg1 : region_of s1 r = Some rg /\ rg_live rg = true /\ rg_len rg = am_maplen am1 * PGSZ).
{ split; [unfold region_of in *; rewrite Erg1; exact Hr|]. split; [exact Hl|]. rewrite E3. exact Hlen. }
destruct (free_ring_cases (g :: X) U s4 g HI4 (or_introl eq_refl)) as [fc FC].
assert (HI5 : Inv X None U (sF g s4 fc)).
{ pose proof (step4 X U A g am Hu s4 mi P4') as K. rewrite (free_meta_eval _ _ _ _ FC) in K. cbn [itok snd] in K. exact (proj1 (proj1 K)). }
rewrite (nt_free_group_mapped fuel A g am s1 am1 Mg1) by lia.
assert (Es4 : A_rec (am_sc am) (A_seq (A_usg A (am_sc am) am1 s1)) = s4) by reflexivity. rewrite Es4.
erewrite (bind_eval (free_meta g) _ s4 tt (sF g s4 fc) (free_meta_eval _ _ _ _ FC)).
unfold ret. cbn [mreal].
assert (Es4' : YN0m.s4 A s1 am1 = s4) by (unfold YN0m.s4, YN0m.s3, YN0m.s2; rewrite E1; reflexivity).
pose proof (A2_SR X (U1 X U A g) U fuel L A s1 g am1 regs regs1 mem mem1 md gv r rg NM HI1 Mg1 Hsc64 Hlast1 Hml1 Hmem1 Hrg1 Eus AO1') as R2.
rewrite Es4' in R2. specialize (R2 HI4).
eapply SR_bind; [exact R2|]. intros c' (regs3 & mem3 & -> & NF).
exact (A4_SR X U fuel L A s4 g mi regs regs3 mem mem3 md gv FE_XF (MUsed am1) fc NF HI4 Mg4' FC AO4' HI5).
Qed.
End f.
Lemma In_keys_MT s q : In q (keys s) -> exists x, MT s q = Some x.
Proof.
intros Hin. unfold MT, keys in *. destruct (mlookup (st_metas s) q) as [x|] eqn:E; [exists x; reflexivity|].
exfalso. apply (proj1 (mlookup_None_iff _ _) E). exact Hin.
Qed.
Lemma owned_img X R U L s md x :
Inv X R U s -> ledger_ok B1 L s md -> ly_ctx L = CTX -> alloc_owned L s x -> in_img1 x -> CTX <= x < CTX + CTX_SIZE.
Proof.
intros HI LG HC [(e & He & Hx) _] Himg.
destruct (In_footprint_inv s e He) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- rewrite HC in Hx. exact Hx.
- exfalso. destruct (proj1 (proj2 (inv_areas HI)) a Ha) as (ra & oa & rga & Ea & Hoa & Hoa0 & Hra & Hral & Hoalen & _). rewrite Ea in Hx. cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ LG ra rga Hra Hral) as (_ & _ & _ & Himg'). apply (Himg' x); [unfold PGSZ in *; lia|]. apply in_img1_in_img. exact Himg.
- exfalso. destruct (lg_placed _ _ _ _ LG k r Hr Hl) as (_ & _ & _ & Himg'). apply (Himg' x); [lia|]. apply in_img1_in_img. exact Himg.
Qed.
Section h.
Variables (X : list sptr) (U : Z -> Z) (fuel : nat) (L : layout) (A : astate) (g : sptr) (i : Z) (am : ameta).
Variables (regs regs1 : bvmap 5 word) (mem mem1 : word -> option byte) (md : Model) (gv : Z).
Variables (q : apath) (d : dvar) (p n : sptr) (ap an : ameta).
Hypothesis IH : forall X' U' L' A' g' i' am' regs' mem' md', nt_goal B1 fuel X' U' L' A' g' i' am' regs' mem' md'.
Hypothesis HI : Inv X (Some (g, i)) U A.
Hypothesis Hu : usedX X A g am.
Hypothesis HU : forall c, 0 <= U c.
Hypothesis HC1 : nt_C1 A g i am = true.
Hypothesis Hf : (fneed (am_sc am) <= S fuel)%nat.
Hypothesis HB : bounded A.
Hypothesis NPRE : nt_pre B1 X (S fuel) L A regs mem md g i.
Hypothesis VALID : validA q d = true.
Hypothesis QF : qfacts A g i am (toMq q).
Hypothesis DF : dfacts X A g am (toMd d) p n ap an.
Hypothesis Hml0 : am_maplen am = 0.
Let s1 := A1s A g am d p n ap an.
Hypothesis NM : ntmid (g :: X) fuel L A s1 g regs regs1 mem mem1 md gv.
Let am1 := am_set_links None None am.
Let sc := am_sc am.
Let s2 := A_usg A sc am1 s1.
Lemma am1_fields' : am_sc am1 = am_sc am /\ am_last am1 = am_last am /\ am_maplen am1 = am_maplen am /\ am_mem am1 = am_mem am.
Proof. unfold am1. destruct am; repeat split; reflexivity. Qed.
Lemma HP1' : P1 X U A g am s1.
Proof.
pose proof (step1 X U A g i am fuel HI Hu HC1 Hf) as K. rewrite (nt_deq_A1s X U A g i am q d p n ap an HI Hu QF DF) in K. exact K.
Qed.
Lemma HP2' : P2 X U A g s1 s2.
Proof.
pose proof (step2 X U A g i am fuel HI Hu HU HC1 Hf s1 HP1') as K. pose proof am1_fields' as (E1 & E2 & E3 & E4).
rewrite <- E2 in K. rewrite (usage_eval A am s1 am1) in K. exact K.
Qed.
Lemma NDk' s : (exists Y R V, Inv Y R V s) -> List.NoDup (keys s).
Proof. intros (Y & R & V & H). exact (proj1 (inv_keys H)). Qed.
Lemma AO1' : forall a, alloc_owned L s1 a -> alloc_owned L A a.
Proof.
destruct HP1' as (HI1 & _ & _ & _ & _ & _ & _ & UB1). pose proof (A1s_facts X U fuel L A g i am regs mem md q d p n ap an HI Hu NPRE VALID DF) as (Efp & _).
intros a. apply alloc_owned_same; [exact Efp|]. apply ub_same_user_blocks; [apply NDk'; eauto | apply NDk'; eauto | exact UB1].
Qed.
Theorem nested_mreal :
mreal src0segs (mkCfg (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)) md)
(nt_free_group fuel A g am s1) (nt_post B1 X (S fuel) L A regs mem md).
Proof.
pose proof HP1' as HP1. pose proof HP2' as HP2. pose proof HP1 as (HI1 & Mg1 & Eus & Erg1 & _ & _ & _ & UB1). pose proof HP2 as (HI2 & Em2 & Erg2 & Ea2 & C2 & EU2).
pose proof am1_fields' as (E1 & E2 & E3 & E4). pose proof AO1' as AO1.
assert (Hml1 : am_maplen am1 = 0) by (rewrite E3; exact Hml0).
destruct (step3n X U A g i am fuel HI Hu HC1 Hf s1 s2 HP1 HP2 Hml0)
as (g' & am' & i' & fr' & N63 & Hsc & U'A & U'2 & Hi' & F' & K' & Hoff' & Eptr & Hsc' & Hg'g & E2g' & Hff & NOSL & HI3 & U'3 & HR2g' & Hf' & HP4).
set (s3 := upd_meta g' (MUsed (am_forget am' i')) s2) in *.
assert (Es3 : YN0n.s3 A s1 am1 g' am' i' = s3) by (unfold YN0n.s3, YN0n.s2, s3, s2, sc; rewrite E1; reflexivity).
assert (U'1 : usedX (g :: X) s1 g' am') by (apply EU2; exact U'2).
assert (Emem1 : am_mem am1 = slot_start am' i') by (rewrite E4, Eptr; unfold frame_ptr; rewrite Hoff', Z.mul_0_r; apply padd_0).
assert (NOSL1 : forall c ac, usedX (g :: X) s1 c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am' i') by (intros c ac Hc; apply (NOSL c ac); apply EU2; exact Hc).
pose proof (proj1 (usedX_MT _ _ _ _ U'2)) as Mg'2.
assert (HB1 : bounded s1).
{ unfold s1, A1s, A_D1, A_D2a, A_D2b, A_D2a', A_D2b', A_unl, A_unl'. destruct d; rewrite ?bounded_set_active, ?bounded_upd_meta; exact HB. }
assert (HB3 : bounded s3).
{ unfold s3. apply bounded_upd_meta. unfold s2. apply bounded_usg; [exact HB1|]. intros H48.
pose proof (usage_ge X U A g i am fuel HI Hu HU Hf ltac:(unfold sc in *; lia)) as UG. rewrite E2. unfold usage_of in *. rewrite Eus. pose proof (proj1 HB sc). pose proof (inv_groups HI g am Hu) as ((Glast & _) & _). unfold usage_of, sc in *. lia. }
rewrite (nt_free_group_nested fuel A g am s1 am1 Mg1 g' i' am'); [| exact Hml1 | rewrite E4; exact Hff | exact Mg'2 | unfold slot_is_group; rewrite F', K'; reflexivity].
change (A_fgt A am s1 am1 g' i' am') with s3.
eapply (mreal_bind src0segs) with
(P := fun r c' => ((exists regs2 mem2, ntcall fuel L A g regs regs2 mem mem2 gv /\ nt_pre B1 (g :: X) fuel L s3 regs2 mem2 md g' i' /\ nt_post B1 (g :: X) fuel L s3 regs2 mem2 md r c') /\ nf_post (g :: X) U s3 r) /\ ntrel s3 (snd r)).
-
eapply SR_mreal.
{ pose proof (A3_SR X (U1 X U A g) U fuel L A s1 g am1 regs regs1 mem mem1 md gv g' am' i' fr' NM HI1 Mg1 ltac:(rewrite E1; lia) ltac:(rewrite E2; pose proof (proj1 (proj1 (inv_groups HI g am Hu))); lia) Hml1 Eus AO1 U'1 Hi' F' K' Emem1 Hsc' Hg'g NOSL1) as R3.
rewrite Es3 in R3. exact (R3 HI3). }
intros c2 (regs2 & mem2 & -> & NC & NPRE2).
apply mreal_tall; [| apply nontrivial_free_ntrel].
apply mreal_conj; [| apply (nontrivial_free_spec fuel (g :: X) U s3 g' i' (am_forget am' i') _ HI3 U'3 HU HR2g' Hf'); intros r Hr; exact Hr].
eapply mreal_mono; [| exact (IH (g :: X) U L s3 g' i' (am_forget am' i') regs2 mem2 md HI3 U'3 HU HR2g' Hf' HB3 NPRE2)].
intros r c' Hpost. exists regs2, mem2. split; [exact NC | split; [exact NPRE2 | exact Hpost]].
-
intros [mi s4] c' (((regs2 & mem2 & NC & NPRE2 & NPOST) & NF) & [_ NK]). cbn [fst snd] in NF, NK.
pose proof (HP4 mi s4 NF NK) as P4'. pose proof P4' as (HI4 & UB4 & C4 & Erg4 & Hmi).
destruct NPOST as (regsJ & memJ & -> & MRJ & STJ & RP & Ra0 & Ra1 & FRJ & STKJ). cbn [fst snd] in MRJ, Ra0, Ra1.
pose proof NPRE2 as (Hso & HL3 & Hcx & Hsec & _ & _ & LG3 & Hh & Hlz & Hmat & _).
pose proof NC as [Cra Cs3 Cs1 Cs2 Csp Ckeep Cfr Cgd Cret Ctp Cspf Cstkw Cunch].
destruct NK as (Krg & Kbrk & Kar & _).
assert (ESP2 : spZ regs2 = spZ regs - 96).
{ pose proof Cspf as (_ & S2 & S3). pose proof (proj1 alloc_ceiling_val). unfold spZ at 1. change (getr regs2 2) with (getr regs2 (nat_to_reg 2)). rewrite Csp. apply lit64_small. unfold NT_FRAME in *. lia. }
assert (Efp4 : footprint s4 = footprint s3) by (apply footprint_regions_areas; assumption).
assert (HL4 : layout_ok L s4) by exact (layout_ok_same' L s3 s4 HL3 Krg Efp4).
assert (LG4 : ledger_ok B1 L s4 md) by exact (ledger_ok_same' L s3 s4 md LG3 Krg Kbrk).
assert (Efp3 : footprint s3 = footprint A).
{ unfold s3. rewrite footprint_upd_meta. pose proof (A1s_facts X U fuel L A g i am regs mem md q d p n ap an HI Hu NPRE VALID DF) as (EfpA & _ & EaA & _).
rewrite <- EfpA. apply footprint_regions_areas; [rewrite Erg2; symmetry; exact Erg1|].
unfold s2, A_usg. destruct (sc <? 48); reflexivity. }
assert (UB3 : ub_same A s3).
{ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [apply ub_same_metas; exact Em2|]. unfold s3.
apply ub_same_upd_In; [eapply MT_Some_In_keys; exact Mg'2|]. rewrite Mg'2. cbn.
pose proof (inv_groups HI2 g' am' U'2) as ((_ & _ & Glen' & _) & _).
apply blocks_of_upd_slot_same; [exact Hi' | exact Glen' |]. unfold slotst_block, slot_block. cbn. rewrite F', K'. reflexivity. }
assert (AO3 : forall a, alloc_owned L s3 a -> alloc_owned L A a).
{ intros a. apply alloc_owned_same; [exact Efp3|]. apply ub_same_user_blocks; [apply NDk'; eauto | apply NDk'; exists (g :: X), (Some (g', i')), U; exact HI3 | exact UB3]. }
assert (AO4 : forall a, alloc_owned L s4 a -> alloc_owned L A a).
{ intros a. apply alloc_owned_same; [rewrite Efp4; exact Efp3|]. apply ub_same_user_blocks; [apply NDk'; eauto | apply NDk'; eauto | exact UB4]. }
pose proof (proj1 alloc_ceiling_val) as HCV. pose proof Cspf as (S16 & Sceil & S63). unfold NT_FRAME in Sceil, Cstkw, Cunch, FRJ, STKJ. rewrite ESP2 in FRJ, STKJ.
assert (LOW : forall a, alloc_owned L s3 a -> a < alloc_ceiling).
{ intros a [(e & He & Hx) _]. exact (proj2 (footprint_below (g :: X) (Some (g', i')) U L s3 md HI3 Hso Hcx LG3 e a He Hx)). }
assert (HIGH : forall a, spZ regs - 96 <= a < spZ regs -> 0 <= a < 2 ^ 64 -> mbyte src0segs memJ a = mbyte src0segs mem2 a /\ (writable_at src0segs mem2 a <-> writable_at src0segs memJ a)).
{ intros a Ha Ha'. apply (FRJ a Ha'); [intros W; pose proof (LOW a W); lia | lia]. }
assert (STK : forall a w v, spZ regs - 96 <= a -> a + Z.of_nat w <= spZ regs -> bytes_are mem2 a w v -> bytes_are memJ a w v).
{ intros a w v Ha Haw Hb k Hk. rewrite <- (Hb k Hk). apply (proj1 (HIGH (a + Z.of_nat k) ltac:(lia) ltac:(lia))). }
assert (RPn : forall k, callee_saved (Z.of_nat k) -> getr regsJ (nat_to_reg k) = getr regs2 (nat_to_reg k)).
{ intros k Hk. pose proof (callee_saved_cases _ Hk) as [Hr32 _]. rewrite <- (Nat2Z.id k). rewrite <- (Z_to_bv5_nat_to_reg _ Hr32). apply RP. exact Hk. }
assert (NF4 : ntmidF FE_RET2 (g :: X) fuel L A s4 g mi regs regsJ mem memJ md gv).
{ split.
- exact Hso.
- exact HL4.
- exact Hcx.
- exact Hsec.
- exact MRJ.
- exact STJ.
- exact LG4.
- exact (conj Hh (conj Hlz Hmat)).
- cbn [aGF]. rewrite (RPn 19%nat ltac:(unfold callee_saved; lia)). exact Cs3.
- cbn [aBASE]. exact Ra0.
- exact Ra1.
- destruct mi as [[k len]|]; cbn [mi_base mi_len]; [|lia].
destruct Hmi as (rg & Hr & Hk & Hl & Hlen & Hlen0 & _). destruct (lg_placed _ _ _ _ LG4 k rg Hr Hl) as (_ & R1 & R2 & _).
pose proof (page_round_ge len). lia.
- rewrite (RPn 9%nat ltac:(unfold callee_saved; lia)). exact Cs1.
- rewrite (RPn 18%nat ltac:(unfold callee_saved; lia)). exact Cs2.
- rewrite (RPn 2%nat ltac:(unfold callee_saved; lia)). exact Csp.
- intros r Hr. rewrite (RPn r ltac:(unfold callee_saved; cbn in Hr; lia)). apply Ckeep. exact Hr.
- destruct Cfr as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; (apply STK; [lia | cbn; lia | assumption]).
- intros k Hk. rewrite <- (Cgd k Hk). apply (FRJ (GUARD + Z.of_nat k)); [unfold GUARD, src0_D_stack_chk_guard; lia | | unfold GUARD, src0_D_stack_chk_guard; lia].
intros W. pose proof (owned_img (g :: X) (Some (g', i')) U L s3 md _ HI3 LG3 Hcx W ltac:(unfold in_img1, GUARD, src0_D_stack_chk_guard; lia)).
unfold GUARD, src0_D_stack_chk_guard, CTX, src0_D_malloc_context, CTX_SIZE in *. lia.
- exact Cret.
- exact Ctp.
- exact Cspf.
- unfold NT_FRAME. intros a Ha. destruct (Z_lt_dec a (spZ regs - 96)).
+ apply STKJ. lia.
+ apply (proj1 (proj2 (HIGH a ltac:(lia) ltac:(lia)))). apply Cstkw. lia.
- unfold NT_FRAME. intros a Ha NO NS.
destruct (FRJ a Ha (fun W => NO (AO3 a W)) ltac:(lia)) as [M1 M2].
pose proof (same_byte_views mem mem2 a (Cunch a Ha NO NS)) as [M3 M4].
split; [exact (eq_trans M1 M3) | exact (iff_trans M4 M2)]. }
destruct (free_ring_cases (g :: X) U s4 g HI4 (or_introl eq_refl)) as [fc FC].
assert (HI5 : Inv X None U (sF g s4 fc)).
{ pose proof (step4 X U A g am Hu s4 mi P4') as K. rewrite (free_meta_eval _ _ _ _ FC) in K. cbn [itok snd] in K. exact (proj1 (proj1 K)). }
destruct (In_keys_MT s4 g (proj1 (inv_X HI4 g (or_introl eq_refl)))) as [x4 Mg4].
erewrite (bind_eval (free_meta g) _ s4 tt (sF g s4 fc) (free_meta_eval _ _ _ _ FC)). unfold ret. cbn [mreal].
change (getr regs2 1) with (getr regs2 (nat_to_reg 1)). rewrite Cra.
exact (A4_SR X U fuel L A s4 g mi regs regsJ mem memJ md gv FE_RET2 x4 fc NF4 HI4 Mg4 FC AO4 HI5).
Qed.
End h.
Theorem src0_nested : forall fuel, nested_goal fuel.
Proof.
intros fuel X U L A g i am regs mem md gv q d p n ap an regs1 mem1 IH HI Hu HU HC1 Hf HB NPRE Hgv VALID QF DF Hml0 NM.
exact (nested_mreal X U fuel L A g i am regs regs1 mem mem1 md gv q d p n ap an IH HI Hu HU HC1 Hf HB NPRE VALID QF DF Hml0 NM).
Qed.
Theorem src0_ntA_of_nested : (forall fuel, nested_goal fuel) -> ntA_hyp B1.
Proof.
intros HN fuel IH X U L A g i am regs mem md HC1 HI Hu HU HR2g Hf HB NPRE.
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (ntA_cases X U A g i am HI Hu HC1) as (qM & dM & p & n & ap & an & VALID & QF & DF).
rewrite <- (toMq_of qM) in QF. rewrite <- (toMd_of dM) in DF. rewrite <- (toMq_of qM), <- (toMd_of dM), <- validA_M in VALID.
set (q := ofMq qM) in *. set (d := ofMd dM) in *. clearbody q d.
pose proof NPRE as (_ & _ & _ & _ & _ & ST & _ & Hh & Hlz & _). destruct (st_guard _ _ ST) as [gv Hgv].
rewrite (nt_tree fuel A g i am Mg), HC1. unfold nt_TA.
rewrite (bind_eval (nt_deq g am) _ A tt (A1s A g am d p n ap an) (nt_deq_A1s X U A g i am q d p n ap an HI Hu QF DF)).
assert (HI2 : Inv (g :: X) None (U1 X U A g) (A1s A g am d p n ap an)).
{ pose proof (step1 X U A g i am fuel HI Hu HC1 Hf) as K. rewrite (nt_deq_A1s X U A g i am q d p n ap an HI Hu QF DF) in K. exact (proj1 K). }
eapply SR_mreal; [eapply (A1_run q d _ _ md VALID (A1_entry_st_ok X U fuel L A g i am regs mem md gv q d p n ap an HI Hu HB NPRE Hgv VALID QF DF) Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HF1). cbn [ms_mem mkst] in HF1.
pose proof (A1_post X U fuel L A g i am regs mem md gv q d p n ap an HI Hu NPRE Hgv VALID QF DF ms1 (U1 X U A g) HS1 HF1 HI2) as NM.
rewrite (post_shapeA _ _ _ _ _ _ _ _ _ _ _ VALID ms1 HS1).
pose proof (inv_groups HI g am Hu) as (_ & Gml & _).
destruct (Z.eq_dec (am_maplen am) 0) as [Hml0 | Hml].
- exact (HN fuel X U L A g i am regs mem md gv q d p n ap an (ms_regs ms1) (ms_mem ms1) IH HI Hu HU HC1 Hf HB NPRE Hgv VALID QF DF Hml0 NM).
- exact (mapped_mreal X U fuel L A g i am regs (ms_regs ms1) mem (ms_mem ms1) md gv q d p n ap an HI Hu HU HC1 Hf NPRE VALID QF DF ltac:(lia) NM).
Qed.
Corollary src0_ntfree_of_nested : (forall fuel, nested_goal fuel) -> ntfree_hyp B1.
Proof. intros HN. apply src0_ntfree_of_A. apply src0_ntA_of_nested. exact HN. Qed.
Theorem src0_ntA : ntA_hyp B1.
Proof. apply src0_ntA_of_nested. apply src0_nested. Qed.
Theorem src0_ntfree : ntfree_hyp B1.
Proof. apply src0_ntfree_of_A. apply src0_ntA. Qed.
Theorem src0_free_realizes_closed : free_realizes B1 (MRx B1).
Proof. exact (src0_free_realizes src0_ntfree). Qed.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
