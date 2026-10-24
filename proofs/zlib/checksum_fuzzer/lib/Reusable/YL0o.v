(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP05 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN3b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL0c YL0a YL00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition memcpy_clob : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Definition memcpy_post (ss : sstate) (ra : Z) (k : nat) : sstate :=
mkSS ra (sr_sets (ss_regs ss) (junk_upd k memcpy_clob)) (ss_mem ss) None (ss_facts ss).
Definition memcpy_check (ss : sstate) (ra : Z) (nq : nat) (k : nat) : bool :=
(ss_pc ss =? src0_A_memcpy) &&
match ss_resv ss with None => true | Some _ => false end &&
sv_eqb (sr_get (ss_regs ss) 1) (SLit ra) && bv_eqb (v_jalr (Z_to_bv 64 ra) 0) (Z_to_bv 64 ra) &&
sv_eqb (sr_get (ss_regs ss) 10) (SOff nq 0) &&
ss_atoms_lt k ss && sep_check src0_msyms (ss_facts ss) (ss_mem ss).
Lemma rdn_of_present : forall segs mem n a,
a + Z.of_nat n <= 2 ^ 64 -> 0 <= a ->
(forall i, 0 <= i < Z.of_nat n -> present mem (a + i)) ->
exists bs, rdn segs mem (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
intros segs mem n. induction n as [|n IH]; intros a Hnw Ha Hp.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia)) as (bs & Hbs & Hlen).
exists (b :: bs). cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a) by lia. change (bv_unsigned 1%bv) with 1. reflexivity. }
rewrite Hbs. split; [reflexivity | cbn; lia].
Qed.
Lemma rdn_mbyte : forall segs mem n a bs i,
rdn segs mem (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (i < n)%nat ->
mbyte segs mem (a + Z.of_nat i) = nth_error bs i.
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs i H Ha Hnw Hi; [lia|].
cbn [rdn] in H.
destruct (match mem (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b|] eqn:Hb; [|discriminate].
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) in H.
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a) by lia. change (bv_unsigned 1%bv) with 1. reflexivity. }
destruct (rdn segs mem (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Hr; [|discriminate]. injection H as <-.
destruct i as [|i].
- cbn. rewrite Z.add_0_r. unfold mbyte. exact Hb.
- cbn [nth_error]. rewrite <- (IH (a + 1) rest i Hr) by lia. f_equal. lia.
Qed.
Section d.
Variable API : AllocAPI src0_msyms.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra src0_msyms MR.
Let LAWS := aa_laws API.
Theorem src0_memcpy_site : forall E ss ms md L A q qsz pl psrc szsrc src nq k ra T,
st_ok src0segs E ss ms ->
stack_anchored E (ss_facts ss) ->
memcpy_check ss ra nq k = true ->
MR L A (ms_mem ms) md ->
In (q, qsz) (user_blocks A) -> In (psrc, szsrc) (user_blocks A) -> q <> psrc ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L q) ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 src -> ptr_addr L psrc <= src -> src + pl <= ptr_addr L psrc + szsrc ->
getr (ms_regs ms) 12%bv = Z_to_bv 64 pl -> 0 < pl -> pl <= qsz ->
(forall ms',
st_ok src0segs (havoc E k (map (getr (ms_regs ms')) memcpy_clob)) (memcpy_post ss ra k) ms' ->
MR L A (ms_mem ms') md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (ptr_addr L q <= a < ptr_addr L q + pl) ->
ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
(forall bs0, blk_data src0_msyms (ms_mem ms) src bs0 -> Z.of_nat (length bs0) = pl ->
blk_data src0_msyms (ms_mem ms') (ptr_addr L q) bs0) ->
realizes src0segs (mkCfg ms' md) T) ->
realizes src0segs (mkCfg ms md) T.
Proof.
intros E ss ms md L A q qsz pl psrc szsrc src nq k ra T HS HSA Hck HMR Hq Hps Hne Ha0 Ha1 Hs1 Hs2 Ha2 Hpl Hplq HK.
unfold memcpy_check in Hck.
apply andb_prop in Hck as [Hck Hsep]. apply andb_prop in Hck as [Hck Hat]. apply andb_prop in Hck as [Hck H10].
apply andb_prop in Hck as [Hck Hjr]. apply andb_prop in Hck as [Hck Hra]. apply andb_prop in Hck as [Hpc Hrv].
apply Z.eqb_eq in Hpc. apply sv_eqb_eq in Hra. apply sv_eqb_eq in H10. apply bv_eqb_eq in Hjr.
destruct (ss_resv ss) eqn:Hrv'; [discriminate|].
destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hlz & Hmat).
pose proof (st_ok_mkst src0segs E ss ms HS Hrv') as Hshape.
pose proof (mr_blocks _ _ LAWS L A (ms_mem ms) md q qsz) as HBq.
pose proof (mr_blocks _ _ LAWS L A (ms_mem ms) md psrc szsrc) as HBs.
destruct (HBq 0 HMR Hq ltac:(lia)) as (_ & Hqlo & Hqhi & _).
destruct (HBs (src - ptr_addr L psrc) HMR Hps ltac:(lia)) as (_ & Hslo & Hshi & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
destruct (rdn_of_present src0segs (ms_mem ms) (Z.to_nat pl) src ltac:(lia) ltac:(lia)
ltac:(intros i Hi; replace (src + i) with (ptr_addr L psrc + (src - ptr_addr L psrc + i)) by lia; apply (HBs _ HMR Hps); lia))
as (bs & Hbs & Hlen).
assert (Hdisj : ptr_addr L q + pl <= src \/ src + pl <= ptr_addr L q).
{ pose proof (mr_blocks_disjoint _ _ LAWS L A (ms_mem ms) md HMR) as HD. unfold blocks in HD.
assert (Hd : ranges_disjoint (ptr_addr L q, qsz) (ptr_addr L psrc, szsrc)).
{ clear -HD Hq Hps Hne. induction (user_blocks A) as [|b bl IH]; [destruct Hq|].
cbn [map pairwise] in HD. destruct HD as [Hhd Htl].
destruct Hq as [->|Hq']; destruct Hps as [Hp'|Hp'].
- exfalso. apply Hne. congruence.
- apply Hhd. apply in_map_iff. exists (psrc, szsrc). auto.
- subst b. unfold ranges_disjoint in *. specialize (Hhd (ptr_addr L q, qsz) ltac:(apply in_map_iff; exists (q, qsz); auto)). cbn [fst snd] in *. lia.
- apply IH; assumption. }
unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia. }
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
assert (HlenZ : Z.of_nat (length bs) = pl) by (rewrite Hlen; lia).
assert (Uq : bv_unsigned (Z_to_bv 64 (ptr_addr L q)) = ptr_addr L q).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Us : bv_unsigned (Z_to_bv 64 src) = src).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Upl : bv_unsigned (Z_to_bv 64 pl) = Z.of_nat (length bs)).
{ rewrite HlenZ, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Hsrc : rdn src0segs (ms_mem ms) (Z_to_bv 64 src) (length bs) = Some bs) by (rewrite Hlen; exact Hbs).
assert (Hdst : store_ok src0segs (ms_mem ms) (Z_to_bv 64 (ptr_addr L q)) (length bs) = true).
{ apply store_ok_of_all; rewrite Uq; [lia|].
intros x Hx. pose proof (u64_range x).
destruct (HBq (bv_unsigned x - ptr_addr L q) HMR Hq ltac:(lia)) as ([b Hb] & _).
unfold wview. replace (Z_to_bv 64 (ptr_addr L q + (bv_unsigned x - ptr_addr L q))) with x in Hb
by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia).
rewrite Hb. discriminate. }
destruct (src0_memcpy bs (Z_to_bv 64 (ptr_addr L q)) (Z_to_bv 64 src) (Z_to_bv 64 pl) (ms_mem ms) (seg_rom src0segs) (ms_regs ms)
Ha0 Ha1 Ha2 Upl Hsrc Hdst ltac:(rewrite Uq; lia) ltac:(rewrite Us; lia) ltac:(rewrite Uq, Us; lia)) as (regs' & Hms & Hd' & Hfr).
apply (rz_msteps src0segs _ _ md T Hh Hlz Hms).
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (ptr_addr L q <= a < ptr_addr L q + pl) ->
wbytes (ms_mem ms) (Z_to_bv 64 (ptr_addr L q)) bs (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
{ intros a Ha Hna. destruct (Z_lt_dec a (ptr_addr L q)) as [Hlt|Hge].
- apply wbytes_below; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite !Z.mod_small by lia; lia.
- apply (wbytes_above bs (ms_mem ms) (Z_to_bv 64 (ptr_addr L q)) (Z_to_bv 64 a)).
rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite !Z.mod_small by lia; lia. }
apply HK.
+
replace (v_jalr (getr (ms_regs ms) 1%bv) 0) with (Z_to_bv 64 ra).
2:{ destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & _). rewrite (Hregs 1%bv), Hra. cbn [sv_denot ms_regs]. symmetry. exact Hjr. }
unfold memcpy_post. change (junk_upd k memcpy_clob) with ([] ++ junk_upd k memcpy_clob).
eapply (st_ok_splice_havoc src0segs k E ss (ms_regs ms) regs' _ ra (ms_mem ms) _ (ss_mem ss) [] memcpy_clob HS Hat).
* vm_compute. reflexivity.
* vm_compute. reflexivity.
* reflexivity.
* unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [_ Hm]. exact Hm.
* cbn [map fst app]. intros r Hr. apply Hfr; intros ->; cbn in Hr; discriminate.
* constructor.
* destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & HM & HG). cbn [ms_mem] in HM.
apply (mem_ok_wbytes_outside src0segs E (ms_mem ms) (ss_mem ss) (ptr_addr L q) bs HM ltac:(lia) ltac:(lia)).
intros b lo hi wlo whi x Hsk Hx Hin.
unfold skeleton in Hsk. apply in_map_iff in Hsk as (r & Hr & Hinr). unfold skel in Hr. injection Hr as <- <- <- <- <-.
assert (E10 : bv_unsigned (ew E nq) = ptr_addr L q).
{ pose proof (Hregs 10%bv) as H. cbn [ms_regs mkst] in H. rewrite H10, Ha0 in H. cbn [sv_denot] in H. rewrite Z.add_0_r in H.
apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
pose proof (u64_range (ew E nq)). rewrite !Z.mod_small in H by lia. symmetry. exact H. }
pose proof (sep_check_disjoint src0_msyms MR LAWS AX E (ms_mem ms) (ss_facts ss) L A md q qsz (ss_mem ss)
(YP09.mkRegion (Some nq) 0 pl 0 0 []) nq HG HSA HMR Hq eq_refl ltac:(cbn; lia)
ltac:(cbn [YP09.r_lo]; lia) ltac:(cbn [YP09.r_hi]; lia) ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])) Hsep r Hinr) as Hd.
unfold extent_disjoint in Hd. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hd. rewrite E10 in Hd. lia.
+
cbn [ms_mem ms_regs mkst].
eapply (mr_frame _ _ LAWS L A (ms_mem ms) _ md md HMR).
* intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho) as Hlo. unfold mbyte. rewrite Hout; [reflexivity | lia |].
intros Hin. apply (proj2 (proj2 (proj2 (HBq (a - ptr_addr L q) HMR Hq ltac:(lia))))). replace (ptr_addr L q + (a - ptr_addr L q)) with a by lia. exact Ho.
* intros a Ho [b Hb].
pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho) as Hlo. exists b. rewrite Hout; [exact Hb | lia |].
intros Hin. apply (proj2 (proj2 (proj2 (HBq (a - ptr_addr L q) HMR Hq ltac:(lia))))). replace (ptr_addr L q + (a - ptr_addr L q)) with a by lia. exact Ho.
* intros p n i Hp Hi. destruct (mr_blocks _ _ LAWS L A (ms_mem ms) md p n i HMR Hp Hi) as ([b Hb] & Hplo & Hphi & _).
destruct (Z_le_dec (ptr_addr L q) (ptr_addr L p + i)) as [H1|H1]; [destruct (Z_lt_dec (ptr_addr L p + i) (ptr_addr L q + pl)) as [H2|H2]|].
-- eexists. apply (wbytes_inside' bs (ms_mem ms) (Z_to_bv 64 (ptr_addr L q)) (Z_to_bv 64 (ptr_addr L p + i)));
rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite !Z.mod_small by lia; lia.
-- exists b. rewrite Hout by lia. exact Hb.
-- exists b. rewrite Hout by lia. exact Hb.
* reflexivity.
* exact Hh.
* exact Hlz.
* exact Hmat.
+ cbn [ms_mem mkst]. exact Hout.
+ cbn [ms_mem mkst]. intros bs0 HD0 Hlen0. unfold blk_data in HD0 |- *. change (ms_segs src0_msyms) with src0segs in *.
assert (Ebs : bs = bs0).
{ apply (nth_error_ext _ _). intros i.
destruct (lt_dec i (length bs)) as [Hi|Hi].
- rewrite <- (rdn_mbyte src0segs (ms_mem ms) (length bs) src bs i Hsrc) by lia.
rewrite (HD0 (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
- rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None bs0 i)) by lia. reflexivity. }
subst bs0. intros i Hi. unfold mbyte.
rewrite (wbytes_inside' bs (ms_mem ms) (Z_to_bv 64 (ptr_addr L q)) (Z_to_bv 64 (ptr_addr L q + i)));
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite ?Z.mod_small by lia; try lia.
replace (ptr_addr L q + i - ptr_addr L q) with i by lia.
cbn. symmetry. apply nth_error_nth'. lia.
Qed.
Definition memcpy_check0 (ss : sstate) (ra : Z) (k : nat) : bool :=
(ss_pc ss =? src0_A_memcpy) &&
match ss_resv ss with None => true | Some _ => false end &&
sv_eqb (sr_get (ss_regs ss) 1) (SLit ra) && bv_eqb (v_jalr (Z_to_bv 64 ra) 0) (Z_to_bv 64 ra) &&
ss_atoms_lt k ss && sep_check src0_msyms (ss_facts ss) (ss_mem ss).
Lemma rdn_of_mbyte : forall segs mem n a bs,
a + Z.of_nat n <= 2 ^ 64 -> 0 <= a -> length bs = n ->
(forall i, 0 <= i < Z.of_nat n -> mbyte segs mem (a + i) = nth_error bs (Z.to_nat i)) ->
rdn segs mem (Z_to_bv 64 a) n = Some bs.
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs Hnw Ha Hlen Hb.
- destruct bs; [reflexivity | cbn in Hlen; lia].
- destruct bs as [|b bs]; [cbn in Hlen; lia|]. cbn in Hlen.
cbn [rdn]. pose proof (Hb 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold mbyte in H0. cbn [Z.to_nat nth_error] in H0.
rewrite H0.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a) by lia. change (bv_unsigned 1%bv) with 1. reflexivity. }
rewrite (IH (a + 1) bs ltac:(lia) ltac:(lia) ltac:(lia)).
+ reflexivity.
+ intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. rewrite (Hb (1 + i)) by lia.
replace (Z.to_nat (1 + i)) with (Datatypes.S (Z.to_nat i)) by lia. reflexivity.
Qed.
Theorem src0_memcpy_from_abs : forall E ss ms md L A q qsz (dst src pl : Z) (bs : list byte) nq k ra T,
st_ok src0segs E ss ms ->
stack_anchored E (ss_facts ss) ->
memcpy_check0 ss ra k = true ->
MR L A (ms_mem ms) md ->
In (q, qsz) (user_blocks A) -> bv_unsigned (ew E nq) = ptr_addr L q ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 dst -> ptr_addr L q <= dst -> dst + pl <= ptr_addr L q + qsz ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 src -> 0 <= src -> src + pl <= 2 ^ 64 -> (forall i, 0 <= i < pl -> in_img src0_msyms (src + i)) ->
(forall i, 0 <= i < pl -> mbyte src0segs (ms_mem ms) (src + i) = nth_error bs (Z.to_nat i)) -> Z.of_nat (length bs) = pl ->
getr (ms_regs ms) 12%bv = Z_to_bv 64 pl -> 0 < pl ->
(forall ms',
st_ok src0segs (havoc E k (map (getr (ms_regs ms')) memcpy_clob)) (memcpy_post ss ra k) ms' ->
MR L A (ms_mem ms') md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + pl) ->
ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
(forall i, 0 <= i < pl -> mbyte src0segs (ms_mem ms') (dst + i) = nth_error bs (Z.to_nat i)) ->
realizes src0segs (mkCfg ms' md) T) ->
realizes src0segs (mkCfg ms md) T.
Proof.
intros E ss ms md L A q qsz dst src pl bs nq k ra T HS HSA Hck HMR Hq Enq Ha0 Hd1 Hd2 Ha1 Hs0 Hsnw Himg Hbs HlenZ Ha2 Hpl HK.
unfold memcpy_check0 in Hck.
apply andb_prop in Hck as [Hck Hsep]. apply andb_prop in Hck as [Hck Hat].
apply andb_prop in Hck as [Hck Hjr]. apply andb_prop in Hck as [Hck Hra]. apply andb_prop in Hck as [Hpc Hrv].
apply Z.eqb_eq in Hpc. apply sv_eqb_eq in Hra. apply bv_eqb_eq in Hjr.
destruct (ss_resv ss) eqn:Hrv'; [discriminate|].
destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hlz & Hmat).
pose proof (st_ok_mkst src0segs E ss ms HS Hrv') as Hshape.
pose proof (mr_blocks _ _ LAWS L A (ms_mem ms) md q qsz) as HBq.
destruct (HBq 0 HMR Hq ltac:(lia)) as (_ & Hqlo & Hqhi & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
assert (Hdisj : dst + pl <= src \/ src + pl <= dst).
{ destruct (Z_lt_dec (dst + pl) (src + 1)) as [|H1]; [left; lia|]. right.
destruct (Z_lt_dec (src + pl) (dst + 1)) as [|H2]; [lia|]. exfalso.
destruct (Z_le_dec src dst) as [Hle|Hgt].
- apply (ax_blocks_img AX L A (ms_mem ms) md q qsz (dst - ptr_addr L q) HMR Hq ltac:(lia)).
replace (ptr_addr L q + (dst - ptr_addr L q)) with (src + (dst - src)) by lia. apply Himg. lia.
- apply (ax_blocks_img AX L A (ms_mem ms) md q qsz (src - ptr_addr L q) HMR Hq ltac:(lia)).
replace (ptr_addr L q + (src - ptr_addr L q)) with (src + 0) by lia. apply Himg. lia. }
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
assert (Hlen : length bs = Z.to_nat pl) by lia.
assert (Ud : bv_unsigned (Z_to_bv 64 dst) = dst).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Us : bv_unsigned (Z_to_bv 64 src) = src).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Upl : bv_unsigned (Z_to_bv 64 pl) = Z.of_nat (length bs)).
{ rewrite HlenZ, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Hsrc : rdn src0segs (ms_mem ms) (Z_to_bv 64 src) (length bs) = Some bs).
{ apply (rdn_of_mbyte src0segs (ms_mem ms) (length bs) src bs); [lia | lia | reflexivity |].
intros i Hi. apply Hbs. lia. }
assert (Hdst : store_ok src0segs (ms_mem ms) (Z_to_bv 64 dst) (length bs) = true).
{ apply store_ok_of_all; rewrite Ud; [lia|].
intros x Hx. pose proof (u64_range x).
destruct (HBq (bv_unsigned x - ptr_addr L q) HMR Hq ltac:(lia)) as ([b Hb] & _).
unfold wview. replace (Z_to_bv 64 (ptr_addr L q + (bv_unsigned x - ptr_addr L q))) with x in Hb
by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia; lia).
rewrite Hb. discriminate. }
destruct (src0_memcpy bs (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 pl) (ms_mem ms) (seg_rom src0segs) (ms_regs ms)
Ha0 Ha1 Ha2 Upl Hsrc Hdst ltac:(rewrite Ud; lia) ltac:(rewrite Us; lia) ltac:(rewrite Ud, Us; lia)) as (regs' & Hms & Hd' & Hfr).
apply (rz_msteps src0segs _ _ md T Hh Hlz Hms).
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + pl) ->
wbytes (ms_mem ms) (Z_to_bv 64 dst) bs (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
{ intros a Ha Hna. destruct (Z_lt_dec a dst) as [Hlt|Hge].
- apply wbytes_below; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite !Z.mod_small by lia; lia.
- apply (wbytes_above bs (ms_mem ms) (Z_to_bv 64 dst) (Z_to_bv 64 a)).
rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite !Z.mod_small by lia; lia. }
apply HK.
+
replace (v_jalr (getr (ms_regs ms) 1%bv) 0) with (Z_to_bv 64 ra).
2:{ destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & _). rewrite (Hregs 1%bv), Hra. cbn [sv_denot ms_regs]. symmetry. exact Hjr. }
unfold memcpy_post. change (junk_upd k memcpy_clob) with ([] ++ junk_upd k memcpy_clob).
eapply (st_ok_splice_havoc src0segs k E ss (ms_regs ms) regs' _ ra (ms_mem ms) _ (ss_mem ss) [] memcpy_clob HS Hat).
* vm_compute. reflexivity.
* vm_compute. reflexivity.
* reflexivity.
* unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [_ Hm]. exact Hm.
* cbn [map fst app]. intros r Hr. apply Hfr; intros ->; cbn in Hr; discriminate.
* constructor.
* destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & HM & HG). cbn [ms_mem] in HM.
apply (mem_ok_wbytes_outside src0segs E (ms_mem ms) (ss_mem ss) dst bs HM ltac:(lia) ltac:(lia)).
intros b lo hi wlo whi x Hsk Hx Hin.
unfold skeleton in Hsk. apply in_map_iff in Hsk as (r & Hr & Hinr). unfold skel in Hr. injection Hr as <- <- <- <- <-.
pose proof (sep_check_disjoint src0_msyms MR LAWS AX E (ms_mem ms) (ss_facts ss) L A md q qsz (ss_mem ss)
(YP09.mkRegion (Some nq) (dst - ptr_addr L q) (dst - ptr_addr L q + pl) 0 0 []) nq HG HSA HMR Hq eq_refl ltac:(cbn; lia)
ltac:(cbn [YP09.r_lo]; lia) ltac:(cbn [YP09.r_hi]; lia) ltac:((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])) Hsep r Hinr) as Hd.
unfold extent_disjoint in Hd. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hd. rewrite Enq in Hd. lia.
+
cbn [ms_mem ms_regs mkst].
eapply (mr_frame _ _ LAWS L A (ms_mem ms) _ md md HMR).
* intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho) as Hlo. unfold mbyte. rewrite Hout; [reflexivity | lia |].
intros Hin. apply (proj2 (proj2 (proj2 (HBq (a - ptr_addr L q) HMR Hq ltac:(lia))))). replace (ptr_addr L q + (a - ptr_addr L q)) with a by lia. exact Ho.
* intros a Ho [b Hb].
pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho) as Hlo. exists b. rewrite Hout; [exact Hb | lia |].
intros Hin. apply (proj2 (proj2 (proj2 (HBq (a - ptr_addr L q) HMR Hq ltac:(lia))))). replace (ptr_addr L q + (a - ptr_addr L q)) with a by lia. exact Ho.
* intros p n i Hp Hi. destruct (mr_blocks _ _ LAWS L A (ms_mem ms) md p n i HMR Hp Hi) as ([b Hb] & Hplo & Hphi & _).
destruct (Z_le_dec dst (ptr_addr L p + i)) as [H1|H1]; [destruct (Z_lt_dec (ptr_addr L p + i) (dst + pl)) as [H2|H2]|].
-- eexists. apply (wbytes_inside' bs (ms_mem ms) (Z_to_bv 64 dst) (Z_to_bv 64 (ptr_addr L p + i)));
rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite !Z.mod_small by lia; lia.
-- exists b. rewrite Hout by lia. exact Hb.
-- exists b. rewrite Hout by lia. exact Hb.
* reflexivity.
* exact Hh.
* exact Hlz.
* exact Hmat.
+ cbn [ms_mem mkst]. exact Hout.
+ cbn [ms_mem mkst]. intros i Hi. unfold mbyte.
rewrite (wbytes_inside' bs (ms_mem ms) (Z_to_bv 64 dst) (Z_to_bv 64 (dst + i)));
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite ?Z.mod_small by lia; try lia.
replace (dst + i - dst) with i by lia.
cbn. symmetry. apply nth_error_nth'. lia.
Qed.
End d.
End c.
