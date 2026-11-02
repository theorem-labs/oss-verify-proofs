(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1f.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mem_ok_cons' E m r rs :
region_wf r = true -> region_ok src0segs E m r -> (forall r', In r' rs -> extent_disjoint E r r') -> mem_ok src0segs E m rs ->
mem_ok src0segs E m (r :: rs).
Proof.
intros Hwf Hr Hd (Hwfs & Hok & Hpd). split; [cbn; rewrite Hwf, Hwfs; reflexivity|]. split; [apply Forall_cons; assumption|].
split; [|exact Hpd]. clear - Hd. induction rs as [|r' rs IH]; [exact I|]. split; [apply Hd; left; reflexivity | apply IH; intros r'' H; apply Hd; right; exact H].
Qed.
Lemma all_disjoint_ext E r r' t :
r_base r' = r_base r -> r_lo r' = r_lo r -> r_hi r' = r_hi r -> all_disjoint E r t -> all_disjoint E r' t.
Proof. intros E1 E2 E3. induction t as [|x t IH]; cbn; [auto|]. intros [H1 H2]. split; [unfold extent_disjoint in *; rewrite E1, E2, E3; exact H1 | apply IH; exact H2]. Qed.
Lemma mem_ok_act E m v v' t :
mem_ok src0segs E m (R_actW v :: t) -> chunk_ok src0segs E m (base_val E (Some 33%nat)) (mkChunk 88 (CVal 8 v')) -> mem_ok src0segs E m (R_actW v' :: t).
Proof.
intros (Hwf & Hok & Hpd) Hc. split; [exact Hwf|]. split; [|split; [apply (all_disjoint_ext E (R_actW v)); [reflexivity..|exact (proj1 Hpd)] | exact (proj2 Hpd)]].
apply Forall_cons; [|exact (Forall_inv_tail Hok)]. destruct (Forall_inv Hok) as (H1 & H2 & H3 & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. apply Forall_cons; [exact Hc | apply Forall_nil].
Qed.
Lemma mem_ok_act0 E m v t : mem_ok src0segs E m (R_actW0 :: t) -> chunk_ok src0segs E m (base_val E (Some 33%nat)) (mkChunk 88 (CVal 8 v)) -> mem_ok src0segs E m (R_actW v :: t).
Proof.
intros (Hwf & Hok & Hpd) Hc. split; [exact Hwf|]. split; [|split; [apply (all_disjoint_ext E R_actW0); [reflexivity..|exact (proj1 Hpd)] | exact (proj2 Hpd)]].
apply Forall_cons; [|exact (Forall_inv_tail Hok)]. destruct (Forall_inv Hok) as (H1 & H2 & H3 & _).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. apply Forall_cons; [exact Hc | apply Forall_nil].
Qed.
Lemma in_wrange_app E rs1 rs2 a : in_wrange E (rs1 ++ rs2) a -> in_wrange E rs1 a \/ in_wrange E rs2 a.
Proof. intros (r & Hin & Hr). apply in_app_iff in Hin as [H|H]; [left | right]; exists r; auto. Qed.
Lemma sx32_inj a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> sx32 a = sx32 b -> a = b.
Proof. intros Ha Hb E. apply (f_equal (fun z => z mod 2 ^ 32)) in E. rewrite !sx32_mod32, !Z.mod_small in E by lia. exact E. Qed.
Lemma off_img_range' a0 ln : (forall x, a0 <= x < a0 + ln -> ~ in_img B x) -> 0 < ln -> a0 + ln <= 0x10000 \/ 0x51000 <= a0.
Proof.
intros Ho Hln. destruct (img_gap 0x10000 (0x51000 - 0x10000) a0 ln ltac:(intros x Hx; unfold in_img1; lia) ltac:(lia) Ho Hln); lia.
Qed.
Lemma ldiff_eq_sub a b : 0 <= a -> 0 <= b -> Z.ldiff a b = a - Z.land a b.
Proof.
intros Ha Hb. pose proof (Z.lor_ldiff_and a b) as E.
assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
rewrite <- Z.lxor_lor in E by exact D. rewrite <- Z.add_nocarry_lxor in E by exact D. lia.
Qed.
Lemma le_byte_low4 v k : (k < 4)%nat -> le_byte v 8 k = le_byte (v mod 2 ^ 32) 4 k.
Proof.
intros Hk. apply Z.bits_inj'. intros j Hj. rewrite !le_byte_testbit by lia.
destruct (j <? 8) eqn:E8; [|reflexivity]. apply Z.ltb_lt in E8.
replace (8 * Z.of_nat k + j <? 8 * Z.of_nat 8) with true by (symmetry; apply Z.ltb_lt; lia).
replace (8 * Z.of_nat k + j <? 8 * Z.of_nat 4) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite testbit_mod_pow2 by lia. replace (8 * Z.of_nat k + j <? 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma bytes_are_low4 m a v : bytes_are m a 8 v -> bytes_are m a 4 (v mod 2 ^ 32).
Proof. intros H k Hk. rewrite (H k ltac:(lia)). f_equal. f_equal. apply le_byte_low4. exact Hk. Qed.
Lemma bits_6_12 x : 0 <= x -> Z.shiftr (sll64 x 52) 58 = (x / 64) mod 64.
Proof.
intros Hx. unfold sll64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (2 ^ 64) with (2 ^ 12 * 2 ^ 52) by reflexivity. rewrite Z.mul_mod_distr_r by lia.
replace (2 ^ 58) with (2 ^ 52 * 64) by reflexivity. rewrite <- Z.div_div, Z.div_mul by lia.
replace (2 ^ 12) with (64 * 64) by reflexivity. rewrite Z.rem_mul_r by lia. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
rewrite (Z.div_small (x mod 64) 64) by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_r. reflexivity.
Qed.
Lemma mod_div_mod64 x : 0 <= x -> ((x mod 2 ^ 32) / 64) mod 64 = (x / 64) mod 64.
Proof.
intros Hx. replace (2 ^ 32) with (64 * 2 ^ 26) by reflexivity. rewrite Z.rem_mul_r by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small, Z.add_0_l by (try apply Z.mod_pos_bound; lia).
apply Z.mod_mod_divide. exists (2 ^ 20); reflexivity.
Qed.
Lemma sc_of_bits am : 0 <= am_last am <= 31 -> 0 <= am_sc am < 64 -> 0 <= am_maplen am -> ((meta_bits am mod 2 ^ 32) / 64) mod 64 = am_sc am.
Proof.
intros H1 H2 H3. rewrite mod_div_mod64 by (unfold meta_bits; lia). unfold meta_bits.
replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((am_sc am + am_maplen am * 64) * 64 + (am_last am + 32)) by lia.
rewrite Z.div_add_l, Z.div_small, Z.add_0_r by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma sx32_div64_mod64 y : 0 <= y < 2 ^ 32 -> (sx32 y / 64) mod 64 = (y / 64) mod 64.
Proof.
intros Hy. destruct (sx32_cases y) as [[_ E]|[_ E]]; rewrite E, (Z.mod_small y (2 ^ 32)) by lia; [reflexivity|].
replace (y + 2 ^ 64 - 2 ^ 32) with (y + (2 ^ 58 - 2 ^ 26) * 64) by lia. rewrite Z.div_add by lia.
replace (2 ^ 58 - 2 ^ 26) with ((2 ^ 52 - 2 ^ 20) * 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Section u.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Variables (m0 : sptr) (am0 : ameta).
Hypothesis Hhd : active_hd A sc = Some m0.
Hypothesis Mg0 : MT A m0 = Some (MUsed am0).
Hypothesis Hav0 : am_avail am0 = 0.
Let sp : Z := bv_unsigned (getr regs 2).
Definition M0 : Z := ptr_addr L m0.
Let E00 : env := E0 regs (cs L A sc g 0 M0).
Let ms0 := mkst regs (Z_to_bv 64 src0_A_alloc_slot) mem (seg_rom src0segs).
Let rom := seg_rom src0segs.
Lemma pre_factsS : YK0s.ret_ok (getr regs 1) /\ sp mod 16 = 0 /\ alloc_ceiling + stk <= sp /\ sp < 2 ^ 63 /\
(forall a, sp - stk <= a < sp -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 TP /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem a).
Proof. exact (pre_facts regs mem stk PRE). Qed.
Lemma md_factsS : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mid_md _ _ _ _ _ MID). Qed.
Lemma HctxS : ly_ctx L = YN0t.CTX.
Proof. exact (mid_ctx _ _ _ _ _ MID). Qed.
Lemma SO : syms_ok B. Proof. exact (mid_syms _ _ _ _ _ MID). Qed.
Lemma CTX_eq : YN0t.CTX = YN0j.CTX /\ YN0j.LOCK + 8 = YN0j.CTX.
Proof. unfold YN0t.CTX, YN0j.CTX, YN0j.LOCK, src0_D_malloc_context, src0_D_malloc_lock. lia. Qed.
Lemma m0_facts : usedX X A m0 am0 /\ am_sc am0 = sc /\ cs L A sc g 0 M0 34 = M0.
Proof.
destruct (m0_used X U A sc m0 am0 HI Hsc Hhd Mg0) as [Hu Hs]. split; [exact Hu|]. split; [exact Hs|]. cbn [cs]. rewrite Hhd. reflexivity.
Qed.
Section b0.
Variables (R : option (sptr * Z)) (s : astate) (mc : word -> option byte).
Hypothesis HIs : Inv X R U s.
Hypothesis RXs : rawX X s.
Hypothesis SXs : sameX A s.
Hypothesis MIDs : midrep B L s mc md.
Lemma used_metasX_eq : used_metasX X s = used_metas s.
Proof.
apply (used_metasX_all' X s RXs). intros g' am Hin.
exact (proj1 (usedX_MT _ _ _ _ (proj1 (used_metas_usedX' X R U s HIs (fun x am' Hx Hm => rawX_notused X s x am' RXs Hx Hm) g' am) Hin))).
Qed.
Lemma memrepX_iff m : memrepX B [] L s m <-> memrepX B X L s m.
Proof. unfold memrepX, imageX, tail_cellsX. rewrite used_metasX_eq, used_metasX_nil. split; intros H; exact H. Qed.
Lemma MRs : memrepX B X L s mc.
Proof. apply (proj1 (memrepX_iff mc)). apply (proj2 (memrepX_nil B L s mc)). exact (mid_mem _ _ _ _ _ MIDs). Qed.
Lemma HLs : layout_ok L s. Proof. exact (mid_layout _ _ _ _ _ MIDs). Qed.
Lemma LGs : ledger_ok B L s md. Proof. exact (mid_ledger _ _ _ _ _ MIDs). Qed.
Lemma STs : statics_ok B mc. Proof. exact (mid_statics _ _ _ _ _ MIDs). Qed.
Lemma metaS q aq : usedX X s q aq ->
let Q := ptr_addr L q in
4096 <= Q /\ Q + 40 <= alloc_ceiling /\ Q mod 8 = 0 /\ (forall x, Q <= x < Q + 40 -> ~ in_img B x) /\ (forall x, Q <= x < Q + 40 -> present mc x) /\
bytes_are mc (Q + 0) 8 (optrZ L (am_prev aq)) /\ bytes_are mc (Q + 8) 8 (optrZ L (am_next aq)) /\ bytes_are mc (Q + 16) 8 (ptr_addr L (am_mem aq)) /\
bytes_are mc (Q + 24) 4 (am_avail aq) /\ bytes_are mc (Q + 28) 4 (am_freed aq) /\ bytes_are mc (Q + 32) 8 (meta_bits aq) /\
0 <= am_avail aq < 2 ^ 32 /\ 0 <= am_freed aq < 2 ^ 32 /\ 0 <= am_last aq <= 31 /\ 0 <= am_aidx aq <= am_last aq /\ 0 <= am_sc aq < 64 /\ 0 <= am_maplen aq /\ 0 <= meta_bits aq.
Proof.
intros Hu Q. pose proof (YN0p.meta_facts X R U L s md HIs LGs q aq Hu) as (F1 & F2 & F3 & F4 & _).
pose proof (inv_groups HIs q aq Hu) as ((Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & _) & Gml & _ & Gcl & _).
assert (Hav32 : am_avail aq < 2 ^ 32) by (apply (mask_u32 _ (am_last aq)); [lia|lia|intros i Hi; apply (proj1 (Gabove i Hi))]).
assert (Hfr32 : am_freed aq < 2 ^ 32) by (apply (mask_u32 _ (am_last aq)); [lia|lia|intros i Hi; apply (proj2 (Gabove i Hi))]).
assert (Hsc64 : 0 <= am_sc aq < 64) by (destruct Gcl as [(C & _)|(C & _)]; lia).
assert (BY : forall dd w val, match val with VLo5 _ | VSec => False | _ => True end -> In (MCell (LMem (padd q dd)) w val) (meta_slot_cells q (Some (MUsed aq))) ->
bytes_are mc (Q + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (YN0p.meta_cell X R U L s mc HIs MRs q aq _ Hu Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
- intros x Hx. exact (YN0p.meta_present X R U L s mc md HIs MRs LGs q aq x Hu Hx).
- pose proof (BY 0 8%nat (optr (am_prev aq)) ltac:(destruct (am_prev aq); exact I) ltac:(cbn; left; reflexivity)) as B0. unfold optrZ. destruct (am_prev aq); exact B0.
- pose proof (BY 8 8%nat (optr (am_next aq)) ltac:(destruct (am_next aq); exact I) ltac:(cbn; right; left; reflexivity)) as B0. unfold optrZ. destruct (am_next aq); exact B0.
- exact (BY 16 8%nat (VP (am_mem aq)) I ltac:(cbn; do 2 right; left; reflexivity)).
- exact (BY 24 4%nat (VZ (am_avail aq)) I ltac:(cbn; do 3 right; left; reflexivity)).
- exact (BY 28 4%nat (VZ (am_freed aq)) I ltac:(cbn; do 4 right; left; reflexivity)).
- exact (BY 32 8%nat (VZ (meta_bits aq)) I ltac:(cbn; do 5 right; left; reflexivity)).
- unfold meta_bits. lia.
Qed.
Lemma apartS p q ap aq : usedX X s p ap -> usedX X s q aq -> p <> q -> ptr_addr L p + 40 <= ptr_addr L q \/ ptr_addr L q + 40 <= ptr_addr L p.
Proof. intros Hp Hq Hne. exact (metas_apart X R U s L p q _ _ HIs HLs (proj1 (usedX_MT _ _ _ _ Hp)) (proj1 (usedX_MT _ _ _ _ Hq)) Hne). Qed.
Lemma headS : bytes_are mc (YN0j.CTX + 80 + 8 * sc) 8 (optrZ L (active_hd s sc)).
Proof.
pose proof (YN0p.ctx_active_cell X L s mc HctxS MRs (Z.to_nat sc) ltac:(lia)) as C. rewrite (proj1 CTX_eq) in C.
rewrite Z2Nat.id in C by lia. unfold active_hd. exact C.
Qed.
Lemma ctx_writableS x : YN0j.CTX <= x < YN0j.CTX + CTX_SIZE -> writable_at src0segs mc x.
Proof. intros Hx. pose proof (so_ctx_rw B SO mc x) as [W _]; [cbn [ms_ctx B]; unfold CTX_SIZE, YN0j.CTX in *; exact Hx | exact W]. Qed.
Lemma grpS q aq : usedX X s q aq ->
let G := ptr_addr L (am_mem aq) in
4096 <= G /\ G + 16 <= alloc_ceiling /\ G mod 16 = 0 /\ (forall x, G <= x < G + 16 -> ~ in_img B x) /\ (forall x, G <= x < G + 16 -> present mc x) /\
(exists b, mbyte src0segs mc (G + 8) = Some b /\ bv_unsigned b mod 32 = am_aidx aq) /\
(exists k rg, region_of s k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ In (LMem (SP k 0), rg_len rg) (footprint s) /\
ly_reg L k <= G /\ G + 16 <= ly_reg L k + rg_len rg).
Proof.
intros Hu G. pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (inv_groups HIs q aq Hu) as ((Nlast & Naidx & Nlen & Nav & Nfrn & Ndisj & Nabove & _) & Nml & _).
destruct (used_group_region X R U s q aq HIs Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
destruct (lg_placed _ _ _ _ LGs _ _ Hr Hl) as (Ral & R4096 & Rceil & Rimg).
pose proof (used_group_aligned X R U s HIs _ q aq Hu (Nat.le_refl _)) as AL16.
assert (EG : G = ly_reg L (prid (am_mem aq)) + poff (am_mem aq)) by (unfold G, ptr_addr, loc_addr; destruct (am_mem aq); reflexivity).
unfold group_extent, UNIT, IB in Hext. pose proof (stride_pos _ _ _ _ _ (inv_groups HIs q aq Hu)) as SPn.
assert (FP : In (LMem (SP (prid (am_mem aq)) 0), rg_len rg) (footprint s)) by (apply footprint_region_In; assumption).
repeat match goal with |- _ /\ _ => split end; try lia.
- rewrite EG. replace (ly_reg L (prid (am_mem aq)) + poff (am_mem aq)) with (poff (am_mem aq) + (256 * (ly_reg L (prid (am_mem aq)) / 4096)) * 16).
+ rewrite Z.mod_add; [exact AL16 | lia].
+ pose proof (Z.div_exact (ly_reg L (prid (am_mem aq))) 4096 ltac:(lia)) as [_ E]. unfold PGSZ in Ral. specialize (E Ral). lia.
- intros x Hx. apply Rimg. lia.
- intros x Hx. apply (proj1 (Forall_forall _ _) (proj2 (proj2 MRs)) _ FP). cbn [fst snd loc_addr]. lia.
- assert (Hc : In (if am_maplen aq =? 0 then MCell (LMem (padd (am_mem aq) 8)) 1 (VLo5 (am_aidx aq)) else MCell (LMem (padd (am_mem aq) 8)) 4 (VZ (am_aidx aq))) (imageX X s)).
{ unfold imageX. rewrite !in_app_iff. right; right. apply in_flat_map. exists (q, aq). split; [| cbn [fst snd group_cells]; right; left; reflexivity].
unfold used_metasX. apply filter_In. split; [apply (used_metas_iff s q aq (proj1 (inv_keys HIs))); exact (proj1 (usedX_MT _ _ _ _ Hu)) | cbn [fst]; rewrite (proj2 (usedX_MT _ _ _ _ Hu)); reflexivity]. }
pose proof (YN0p.CELL X L s mc MRs _ Hc) as C. unfold cell_mem in C. destruct (am_maplen aq =? 0); cbn [mc_val mc_loc mc_w sval_num] in C; rewrite loc_addr_padd in C; fold G in C.
+ exact (C ltac:(lia)).
+ exists (Z_to_bv 8 (le_byte (am_aidx aq) 4 0)). split; [rewrite <- (C 0%nat ltac:(lia)); f_equal; lia|].
replace (le_byte (am_aidx aq) 4 0) with (am_aidx aq).
2:{ unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite Z.shiftr_0_r. rewrite (Z.mod_small (am_aidx aq) 4294967296) by lia. rewrite Z.mod_small by lia. reflexivity. }
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (am_aidx aq) 256) by lia. rewrite Z.mod_small by lia. reflexivity.
- exists (prid (am_mem aq)), rg. repeat (split; [assumption|]). lia.
Qed.
Lemma grp_meta_apart q aq p ap : usedX X s q aq -> usedX X s p ap ->
ptr_addr L (am_mem aq) + 16 <= ptr_addr L p \/ ptr_addr L p + 40 <= ptr_addr L (am_mem aq).
Proof.
intros Hq Hp. pose proof (grpS q aq Hq) as (_ & _ & _ & _ & _ & _ & k & rg & Hk & Hkd & Hl & He1 & R1 & R2).
pose proof (YN0p.meta_facts X R U L s md HIs LGs p ap Hp) as (_ & _ & _ & _ & a & Ha & He2 & Q1 & Q2).
pose proof HLs as (_ & _ & PW & _).
pose proof (YN2o.area_entry_not_region X R U s HIs a k rg Ha Hk Hkd) as Hne.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He2 He1 Hne) as [Dj|Dj];
unfold ranges_disjoint, crange in Dj; cbn [fst snd loc_addr] in Dj, Q1, Q2; unfold PGSZ in *; lia.
Qed.
Lemma owned_img x : alloc_owned L s x -> in_img B x -> YN0j.CTX <= x < YN0j.CTX + CTX_SIZE.
Proof.
intros [(e & He & Hx) _] Hi. pose proof (src0_img_range x Hi) as Rx.
destruct (In_footprint_inv s e He) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- rewrite HctxS, (proj1 CTX_eq) in Hx. exact Hx.
- exfalso. destruct (proj1 (proj2 (inv_areas HIs)) a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ LGs r rg Hr Hl) as (_ & _ & _ & Himg). apply (Himg x); [unfold PGSZ in *; lia | exact Hi].
- exfalso. destruct (lg_placed _ _ _ _ LGs k r Hr Hl) as (_ & _ & _ & Himg). apply (Himg x); [lia | exact Hi].
Qed.
End b0.
Definition FRAME (mc : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ WS regs x -> ~ (YN0j.CTX <= x < YN0j.CTX + CTX_SIZE) -> ~ alloc_owned L A x ->
mc (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Definition at_bnd (ss : sstate) (k : nat) (Q : env -> Prop) (s1 : astate) (m1 : sptr) (c : config) : Prop :=
exists E ms, c = mkCfg ms md /\ st_ok src0segs E ss ms /\ env_agree 40 E00 E /\ ew E k = Z_to_bv 64 (ptr_addr L m1) /\ Q E /\
rawX X s1 /\ midrep B L s1 (ms_mem ms) md /\ FRAME (ms_mem ms).
Lemma agree_facts E : env_agree 40 E00 E ->
ew E 33 = Z_to_bv 64 (YN0j.LOCK + 8 * sc) /\ ew E 2 = getr regs 2 /\ base_val E (Some 33%nat) = YN0j.LOCK + 8 * sc /\ base_val E (Some 2%nat) = sp /\
ew E 36 = Z_to_bv 64 (SCT + 2 * sc) /\ ew E 35 = Z_to_bv 64 (scl_of sc).
Proof.
intros HA. pose proof statics_layout as SL.
pose proof (agree_cs L A regs sc g 0 M0 E 33 HA ltac:(lia)) as E33. pose proof (agree_reg L A regs sc g 0 M0 E 2 HA ltac:(lia)) as E2. cbn [cs] in E33.
split; [exact E33|]. split; [exact E2|]. split; [apply (base_atom E 33 _ E33); unfold YN0j.LOCK in *; lia|]. split; [cbn [base_val]; rewrite E2; reflexivity|].
split; [exact (agree_cs L A regs sc g 0 M0 E 36 HA ltac:(lia)) | exact (agree_cs L A regs sc g 0 M0 E 35 HA ltac:(lia))].
Qed.
Lemma MEM0_skel : map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) (tl (ss_mem ss_hd)) =
[(Some 2%nat, -384, 0, -384, 0); (None, GOT, GOT + 8, 0, 0); (None, GUARD, GUARD + 8, 0, 0); (None, LIBC + 48, LIBC + 56, 0, 0)].
Proof. vm_compute. reflexivity. Qed.
Definition R_stk_hd : YP09.region := Eval vm_compute in nth 0 (tl (ss_mem ss_hd)) R_stackS.
Lemma stack_region' : tl (ss_mem ss_hd) = R_stk_hd :: tl (tl (ss_mem ss_hd)) /\ (r_base R_stk_hd, r_wlo R_stk_hd, r_whi R_stk_hd) = (Some 2%nat, -384, 0).
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.
Lemma stack_region : exists rstk t, tl (ss_mem ss_hd) = rstk :: t /\ (r_base rstk, r_wlo rstk, r_whi rstk) = (Some 2%nat, -384, 0).
Proof. exists R_stk_hd, (tl (tl (ss_mem ss_hd))). exact stack_region'. Qed.
Lemma base_disjoint E r lo hi : env_agree 40 E00 E -> In r (R_actW0 :: tl (ss_mem ss_hd)) \/ (exists v, r = R_actW v) ->
4096 <= lo -> hi <= alloc_ceiling -> (hi <= 0x10000 \/ 0x51000 <= lo) ->
hi <= base_val E (r_base r) + r_lo r \/ base_val E (r_base r) + r_hi r <= lo.
Proof.
intros HA Hr H1 H2 H3. pose proof (agree_facts E HA) as (_ & _ & B33 & B2 & _). pose proof statics_layout as SL. pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val).
assert (CASE : (r_base r, r_lo r, r_hi r) = (Some 33%nat, 88, 96) \/ In (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r) [(Some 2%nat, -384, 0, -384, 0); (None, GOT, GOT + 8, 0, 0); (None, GUARD, GUARD + 8, 0, 0); (None, LIBC + 48, LIBC + 56, 0, 0)]).
{ destruct Hr as [[<-|Hr]|[v ->]]; [left; reflexivity | right | left; reflexivity]. rewrite <- MEM0_skel. exact (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hr). }
destruct CASE as [E3|Hin].
- injection E3 as -> -> ->. rewrite B33. unfold YN0j.LOCK, YN0j.CTX in *. lia.
- cbn [In] in Hin. decompose [or] Hin; try contradiction; match goal with H : _ = (r_base r, _, _, _, _) |- _ => injection H as <- <- <- _ _ end; rewrite ?B2; cbn [base_val]; unfold ASF in *; try lia.
Qed.
Lemma base_mem_ok E ss ms (v : sv) : st_ok src0segs E ss ms -> ss_mem ss = MEM0 -> env_agree 40 E00 E ->
bytes_are (ms_mem ms) (YN0j.CTX + 80 + 8 * sc) 8 (bv_unsigned (sv_denot E v)) ->
mem_ok src0segs E (ms_mem ms) (R_actW v :: tl (ss_mem ss_hd)).
Proof.
intros HS Hm HA Hb. pose proof (st_ok_mem_ok src0segs E ss ms HS) as MOK. rewrite Hm in MOK. unfold MEM0 in MOK.
apply (mem_ok_act0 E _ v _ MOK). pose proof (agree_facts E HA) as (_ & _ & B33 & _). rewrite B33.
apply (chunk_ok_val' E _ _ _ 8 _ (bv_unsigned (sv_denot E v))); [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range |].
replace (YN0j.LOCK + 8 * sc + 88) with (YN0j.CTX + 80 + 8 * sc) by (pose proof CTX_eq; lia). exact Hb.
Qed.
Lemma midrep_transport s1 s2 mc1 mc2 :
Inv X None U s1 -> rawX X s1 -> midrep B L s1 mc1 md -> sameX s1 s2 -> rawX X s2 -> (exists R, Inv X R U s2) ->
memrepX B X L s2 mc2 -> user_blocks s2 = user_blocks s1 -> tail_cells s2 = tail_cells s1 ->
(forall a, static_owned B a -> mc2 (Z_to_bv 64 a) = mc1 (Z_to_bv 64 a)) ->
midrep B L s2 mc2 md.
Proof.
intros HI1 RX1 MID1 SX RX2 [R HI2] MR2 UBe TCe STe.
pose proof SX as (Erg & Ear & _ & _ & _ & Ebrk & _).
assert (Efp : footprint s2 = footprint s1) by (apply footprint_regions_areas; assumption).
split.
- exact (mid_syms _ _ _ _ _ MID1).
- apply (proj1 (memrepX_nil B L s2 mc2)). apply (proj2 (memrepX_iff R s2 HI2 RX2 mc2)). exact MR2.
- unfold tail_geom. rewrite TCe. apply Forall_forall. intros c Hc k Hk.
apply (alloc_owned_same L s2 s1 _ (eq_sym Efp) (eq_sym UBe)). exact (proj1 (Forall_forall _ _) (mid_tailg _ _ _ _ _ MID1) c Hc k Hk).
- apply (YN26.statics_ok_ext B mc1 mc2 (mid_statics _ _ _ _ _ MID1)). intros a Hs. apply mbyte_ext1. apply STe. exact Hs.
- apply (ledger_ok_same' L s1 s2 md (mid_ledger _ _ _ _ _ MID1) Erg Ebrk).
- eapply ledger_x_same_regions; [exact (mid_ledgerx _ _ _ _ _ MID1) | exact Erg | reflexivity | reflexivity].
- apply (layout_ok_same' L s1 s2 (mid_layout _ _ _ _ _ MID1) Erg Efp).
- exact (mid_ctx _ _ _ _ _ MID1).
- exact (mid_sec _ _ _ _ _ MID1).
- exact (mid_md _ _ _ _ _ MID1).
Qed.
Lemma agree_ext E k v : env_agree 40 E00 E -> (40 <= k)%nat -> env_agree 40 E00 (ewset E k v).
Proof. intros HA Hk. eapply env_agree_trans; [exact HA | eapply env_agree_le; [| apply env_agree_ewset]; lia]. Qed.
Lemma static_range x : static_owned B x -> 0x10000 <= x < 0x51000 /\ ~ (YN0j.CTX <= x < YN0j.CTX + CTX_SIZE).
Proof.
intros Hs. split; [| pose proof (src0_SNC x Hs) as NC; cbn [ms_ctx B] in NC; unfold YN0j.CTX; exact NC].
unfold static_owned in Hs. cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B src0_msyms] in Hs.
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs. lia.
Qed.
Lemma statics_layout2 : (YN0j.CTX + 928 <= GOT \/ GOT + 8 <= YN0j.CTX) /\ (YN0j.CTX + 928 <= GUARD \/ GUARD + 8 <= YN0j.CTX) /\
(YN0j.CTX + 928 <= LIBC + 48 \/ LIBC + 56 <= YN0j.CTX).
Proof. unfold YN0j.CTX, GOT, GUARD, LIBC, src0_D_malloc_context, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_libc. lia. Qed.
Lemma statics_layout3 : 0x10000 <= SCT /\ SCT + 96 <= YN0j.CTX /\ (SCT + 96 <= GOT \/ GOT + 8 <= SCT) /\ (SCT + 96 <= GUARD \/ GUARD + 8 <= SCT) /\
(SCT + 96 <= LIBC + 48 \/ LIBC + 56 <= SCT).
Proof. unfold SCT, YN0j.CTX, GOT, GUARD, LIBC, src0_D_size_classes, src0_D_malloc_context, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_libc. lia. Qed.
Lemma footprint_top s e : Inv X None U s -> sameX A s -> midrep B L s mem md \/ (exists mc, midrep B L s mc md) -> In e (footprint s) -> loc_addr L (fst e) + snd e <= sp - ASF.
Proof.
intros HIs SX MIDs He. pose proof pre_factsS as (_ & _ & P3 & _).
assert (M : exists mc, midrep B L s mc md) by (destruct MIDs as [M|M]; [exists mem; exact M | exact M]). destruct M as [mc M].
pose proof (YN0p.footprint_hi X None U L s md HIs (mid_syms _ _ _ _ _ M) HctxS (mid_ledger _ _ _ _ _ M) e He). unfold ASF in *. lia.
Qed.
Definition hcell (v : option sptr) : mcell := act_cell (Z.to_nat sc) v.
Lemma hcell_In s : length (st_active s) = 48%nat -> In (hcell (active_hd s sc)) (ctx_cells s).
Proof.
intros Hl. unfold hcell, act_cell, ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc).
split; [reflexivity | apply in_seq; lia].
Qed.
Lemma hcell_range v : cell_range L (hcell v) = (YN0j.CTX + 80 + 8 * sc, 8).
Proof. unfold hcell, act_cell, cell_range. cbn [mc_loc mc_w loc_addr fst snd]. rewrite HctxS, (proj1 CTX_eq), Z2Nat.id by lia. unfold CTX_active. f_equal. lia. Qed.
Lemma hcell_mem v mc : bytes_are mc (YN0j.CTX + 80 + 8 * sc) 8 (optrZ L v) -> cell_mem B L mc (hcell v).
Proof.
intros Hb. unfold cell_mem, hcell, act_cell. cbn [mc_val mc_loc mc_w loc_addr]. rewrite HctxS, (proj1 CTX_eq), Z2Nat.id by lia. unfold CTX_active.
destruct v as [q|]; cbn [optr sval_num]; intros k Hk; (etransitivity; [|exact (Hb k Hk)]); [|]; (replace (YN0j.CTX + (80 + 8 * sc) + Z.of_nat k) with (YN0j.CTX + 80 + 8 * sc + Z.of_nat k) by lia); reflexivity.
Qed.
Lemma wrange_cases E1 rs hv x : env_agree 40 E00 E1 ->
in_wrange E1 (rs ++ R_actW hv :: tl (ss_mem ss_hd)) x ->
(exists r, In r rs /\ base_val E1 (r_base r) + r_wlo r <= x < base_val E1 (r_base r) + r_whi r) \/
(YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) \/ WS regs x.
Proof.
intros HA1 (r & Hin & Hr). pose proof (agree_facts E1 HA1) as (_ & _ & B33 & B2 & _).
apply in_app_iff in Hin as [Hin|[<-|Hin]]; [left; exists r; auto | right; left | right; right].
- cbn [r_base r_wlo r_whi R_actW] in Hr. rewrite B33 in Hr. pose proof CTX_eq. lia.
- pose proof (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hin) as Hin'. rewrite MEM0_skel in Hin'. cbn [In] in Hin'.
decompose [or] Hin'; try contradiction; match goal with H : _ = (r_base r, _, _, _, _) |- _ => injection H as Eb _ _ Ewl Ewh end; rewrite <- Ewl, <- Ewh in Hr; try lia.
rewrite <- Eb, B2 in Hr. unfold WS, ASF. fold sp. lia.
Qed.
Lemma wrange_cases0 E1 rs x : env_agree 40 E00 E1 ->
in_wrange E1 (rs ++ MEM0) x ->
(exists r, In r rs /\ base_val E1 (r_base r) + r_wlo r <= x < base_val E1 (r_base r) + r_whi r) \/
(YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) \/ WS regs x.
Proof.
intros HA1 (r & Hin & Hr). pose proof (agree_facts E1 HA1) as (_ & _ & B33 & B2 & _). unfold MEM0 in Hin.
apply in_app_iff in Hin as [Hin|[<-|Hin]]; [left; exists r; auto | right; left | right; right].
- cbn [r_base r_wlo r_whi R_actW0] in Hr. rewrite B33 in Hr. pose proof CTX_eq. lia.
- pose proof (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hin) as Hin'. rewrite MEM0_skel in Hin'. cbn [In] in Hin'.
decompose [or] Hin'; try contradiction; match goal with H : _ = (r_base r, _, _, _, _) |- _ => injection H as Eb _ _ Ewl Ewh end; rewrite <- Ewl, <- Ewh in Hr; try lia.
rewrite <- Eb, B2 in Hr. unfold WS, ASF. fold sp. lia.
Qed.
Lemma tail_cells_upd s0 q am am' : MT s0 q = Some (MUsed am) -> grp_same am am' -> tail_cells (upd_meta q (MUsed am') s0) = tail_cells s0.
Proof.
intros Mq GS. unfold tail_cells. destruct (used_metas_upd s0 q am Mq) as (u1 & u2 & Eu & Eu'). unfold upd_meta. cbn [st_metas]. fold (upd_meta q (MUsed am') s0).
rewrite Eu', Eu, !flat_map_app. cbn [flat_map snd]. rewrite (group_tail_cells_same am am' GS). reflexivity.
Qed.
Section c0.
Variables (s1 : astate) (m1 : sptr) (am1 : ameta) (E : env) (ms : machine_state).
Hypothesis B1 : bnd X U A sc s1 m1 am1.
Hypothesis HS : st_ok src0segs E ss_beta ms.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis E40 : ew E 40 = Z_to_bv 64 (ptr_addr L m1).
Hypothesis RX1 : rawX X s1.
Hypothesis MID1 : midrep B L s1 (ms_mem ms) md.
Hypothesis FR1 : FRAME (ms_mem ms).
Definition nx1 : sptr := match am_next am1 with Some p => p | None => m1 end.
Definition amn1 : ameta := match MT s1 nx1 with Some (MUsed a) => a | _ => am1 end.
Definition M1 : Z := ptr_addr L m1.
Definition NX1 : Z := ptr_addr L nx1.
Lemma nx1_facts : am_next am1 = Some nx1 /\ usedX X s1 nx1 amn1 /\ am_sc amn1 = sc /\ am_freed amn1 <> 0 /\ am_avail amn1 = 0.
Proof.
destruct (links1 X U A sc Hsc s1 m1 am1 B1) as (pr & nx & amnx & Hpr & Hnx & Hun & Hsn & Hfn & Havn).
assert (E1 : nx1 = nx) by (unfold nx1; rewrite Hnx; reflexivity).
assert (E2 : amn1 = amnx) by (unfold amn1; rewrite E1, (proj1 (usedX_MT _ _ _ _ Hun)); reflexivity).
rewrite E1, E2. auto.
Qed.
Definition E1 : env := ewset (ewset (ewset (ewset E aFR1 (Z_to_bv 64 (am_freed am1))) aBITS1 (Z_to_bv 64 (meta_bits am1))) aNX1 (Z_to_bv 64 NX1)) aFR2 (Z_to_bv 64 (am_freed amn1)).
Lemma E1_agree : env_agree 44 E E1.
Proof.
unfold E1. eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aFR2; lia].
eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aNX1; lia].
eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aBITS1; lia].
eapply env_agree_le; [| apply env_agree_ewset]. unfold aFR1; lia.
Qed.
Lemma HA1 : env_agree 40 E00 E1.
Proof. eapply env_agree_trans; [exact HA | eapply env_agree_le; [| apply E1_agree]; lia]. Qed.
Lemma E1_vals : ew E1 aFR1 = Z_to_bv 64 (am_freed am1) /\ ew E1 aBITS1 = Z_to_bv 64 (meta_bits am1) /\ ew E1 aNX1 = Z_to_bv 64 NX1 /\ ew E1 aFR2 = Z_to_bv 64 (am_freed amn1) /\
ew E1 40 = Z_to_bv 64 M1.
Proof.
unfold E1, aFR1, aBITS1, aNX1, aFR2.
repeat split; rewrite ?ew_ewset_same; try reflexivity;
rewrite !ew_ewset_other by lia; rewrite ?ew_ewset_same; try reflexivity. exact E40.
Qed.
Lemma m1_facts :
4096 <= M1 /\ M1 + 40 <= alloc_ceiling /\ M1 mod 8 = 0 /\ (M1 + 40 <= 0x10000 \/ 0x51000 <= M1) /\ (forall x, M1 <= x < M1 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (M1 + 8) 8 NX1 /\ bytes_are (ms_mem ms) (M1 + 28) 4 (am_freed am1) /\ bytes_are (ms_mem ms) (M1 + 32) 8 ((meta_bits am1) mod 2 ^ 64) /\
0 < am_freed am1 < 2 ^ 32 /\ 0 <= am_last am1 <= 31 /\ 0 <= meta_bits am1 /\
4096 <= NX1 /\ NX1 + 40 <= alloc_ceiling /\ NX1 mod 8 = 0 /\ (NX1 + 40 <= 0x10000 \/ 0x51000 <= NX1) /\ (forall x, NX1 <= x < NX1 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (NX1 + 28) 4 (am_freed amn1) /\ 0 < am_freed amn1 < 2 ^ 32 /\
bytes_are (ms_mem ms) (YN0j.CTX + 80 + 8 * sc) 8 M1 /\ (nx1 <> m1 -> M1 + 40 <= NX1 \/ NX1 + 40 <= M1).
Proof.
pose proof B1 as [HI1 Hhd1 Hu1 Hs1 Hf1 Hz1 Hoth1 UB1 SX1 SP1]. pose proof nx1_facts as (Hnx & Hun & Hsn & Hfn & Havn). pose proof (proj1 alloc_ceiling_val).
pose proof (metaS None s1 (ms_mem ms) HI1 RX1 MID1 m1 am1 Hu1) as (A1 & A2 & A3 & A4 & A5 & _ & B8 & _ & _ & B28 & B32 & _ & R2 & R3 & _ & R5 & R6 & R7).
pose proof (metaS None s1 (ms_mem ms) HI1 RX1 MID1 nx1 amn1 Hun) as (C1 & C2 & C3 & C4 & C5 & _ & _ & _ & _ & D28 & _ & _ & S2 & _).
pose proof (headS None s1 (ms_mem ms) HI1 RX1 MID1) as HD. rewrite Hhd1 in HD. cbn [optrZ] in HD.
rewrite Hnx in B8. cbn [optrZ] in B8.
unfold M1, NX1. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- apply (YN0p.off_img _ A4).
- intros k Hk. rewrite le_byte_mod64. exact (B32 k Hk).
- apply (YN0p.off_img _ C4).
- intros Hne. apply (apartS None s1 (ms_mem ms) HI1 MID1 m1 nx1 am1 amn1 Hu1 Hun). intros Heq. exact (Hne (eq_sym Heq)).
Qed.
Lemma land32_of_mod x : 0 <= x -> 32 <= x mod 64 -> Z.land x 32 = 32.
Proof.
intros Hx Hm. apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec.
change 32 with (2 ^ 5). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 5 j) as [<-|Hne]; [|rewrite andb_false_r; reflexivity].
rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2 ^ 5) with 32. pose proof (Z.mod_pos_bound x 64 ltac:(lia)) as Hr.
replace (x / 32) with ((2 * (x / 64) * 32 + x mod 64) / 32) by (f_equal; pose proof (Z.div_mod x 64 ltac:(lia)); lia).
rewrite Z.div_add_l by lia. replace (x mod 64 / 32) with 1 by (apply (Z.div_unique_pos _ _ _ (x mod 64 - 32)); lia).
rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. reflexivity.
Qed.
Lemma valsB :
bv_unsigned (sv_denot E1 FRX1) = sx32 (am_freed am1) /\ bv_unsigned (sv_denot E1 ONES1) = sx32 (ones (am_last am1)) /\
bv_unsigned (sv_denot E1 (SAlu ALU_AND (SOff aBITS1 0) (SLit 32))) = 32 /\ bv_unsigned (sv_denot E1 (SExt true 32 (SOff aFR2 0))) = sx32 (am_freed amn1) /\
sv_denot E1 (SOff 40 0) = Z_to_bv 64 M1 /\ sv_denot E1 (SOff aNX1 0) = Z_to_bv 64 NX1.
Proof.
pose proof m1_facts as (A1 & A2 & _ & _ & _ & _ & _ & _ & Fr & Hl & MBp & C1 & C2 & _ & _ & _ & _ & Fn & _). pose proof (proj1 alloc_ceiling_val).
destruct E1_vals as (V44 & V45 & V46 & V47 & V40).
assert (Hbits : bv_unsigned (ew E1 aBITS1) = meta_bits am1 mod 2 ^ 64) by (rewrite V45; apply lit64_unsigned).
assert (Hl32 : (meta_bits am1 mod 2 ^ 64) mod 32 = am_last am1).
{ rewrite Z.mod_mod_divide by (exists (2 ^ 59); reflexivity). unfold meta_bits.
replace (am_last am1 + 32 + 64 * am_sc am1 + 4096 * am_maplen am1) with (am_last am1 + (1 + 2 * am_sc am1 + 128 * am_maplen am1) * 32) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
assert (Hl64 : 32 <= (meta_bits am1 mod 2 ^ 64) mod 64).
{ rewrite Z.mod_mod_divide by (exists (2 ^ 58); reflexivity). unfold meta_bits.
replace (am_last am1 + 32 + 64 * am_sc am1 + 4096 * am_maplen am1) with ((am_last am1 + 32) + (am_sc am1 + 64 * am_maplen am1) * 64) by lia.
rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
split; [|split; [|split; [|split; [|split]]]].
- cbv delta [FRX1]. rewrite U_sext32'. rewrite (den_atom0 E1 aFR1 _ V44) by lia. rewrite lit64_small by lia. reflexivity.
- cbv delta [ONES1]. cbn [sv_denot]. rewrite addw_rr_unsigned, sllw_rr_unsigned, Z.add_0_r, Z_to_bv_bv_unsigned, Hbits. rewrite (lit64_small 2) by lia. rewrite lit64_unsigned.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
pose proof (Z.mod_pos_bound (meta_bits am1) (2 ^ 64) ltac:(lia)) as QQ. rewrite (proj2 (addiw_sllw2_m1 (meta_bits am1 mod 2 ^ 64) ltac:(lia))). rewrite Hl32. reflexivity.
- cbn [sv_denot]. rewrite alu64_and, Z.add_0_r, Z_to_bv_bv_unsigned, Hbits, (lit64_small 32) by lia.
apply land32_of_mod; [pose proof (Z.mod_pos_bound (meta_bits am1) (2 ^ 64) ltac:(lia)); lia | exact Hl64].
- rewrite U_sext32'. rewrite (den_atom0 E1 aFR2 _ V47) by lia. rewrite lit64_small by lia. reflexivity.
- apply (den_atom0 E1 40 _ V40). lia.
- apply (den_atom0 E1 aNX1 _ V46). lia.
Qed.
Inductive bvar := BVn | BVs | BVss.
Definition ssB (v : bvar) : sstate := match v with BVn => ss_Bn | BVs => ss_Bs | BVss => ss_Bss end.
Definition SSB (v : bvar) : sstate := match v with BVn => SSB_n | BVs => SSB_s | BVss => SSB_ss end.
Definition bcond (v : bvar) : Prop :=
match v with
| BVn => am_freed am1 <> ones (am_last am1)
| BVs => am_freed am1 = ones (am_last am1) /\ nx1 <> m1
| BVss => am_freed am1 = ones (am_last am1) /\ nx1 = m1
end.
Lemma region_m1B (nxv : sv) : sv_denot E1 nxv = Z_to_bv 64 NX1 -> region_ok src0segs E1 (ms_mem ms) (R_m1B nxv).
Proof.
intros Hnx. pose proof m1_facts as (A1 & A2 & A8 & Aimg & Apres & B8 & B28 & B32 & Fr & Hl & MBp & C1 & C2 & _). pose proof (proj1 alloc_ceiling_val).
destruct E1_vals as (V44 & V45 & V46 & V47 & V40).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m1B]; rewrite (base_atom E1 40 M1 V40) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_ok_val' E1 _ _ _ 8 _ NX1); [rewrite Hnx; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B8].
- apply (chunk_ok_val' E1 _ _ _ 4 _ (am_freed am1)); [rewrite (den_atom0 E1 aFR1 _ V44) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B28].
- apply (chunk_ok_val' E1 _ _ _ 8 _ (meta_bits am1 mod 2 ^ 64)); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | exact B32].
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, V45. apply lit64_unsigned.
Qed.
Lemma region_m2B : region_ok src0segs E1 (ms_mem ms) R_m2B.
Proof.
pose proof m1_facts as (A1 & A2 & A8 & Aimg & Apres & B8 & B28 & B32 & Fr & Hl & MBp & C1 & C2 & C8 & Cimg & Cpres & D28 & Fn & _). pose proof (proj1 alloc_ceiling_val).
destruct E1_vals as (V44 & V45 & V46 & V47 & V40).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m2B]; rewrite (base_atom E1 aNX1 NX1 V46) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1 _ _ _ 4 _ (am_freed amn1)); [rewrite (den_atom0 E1 aFR2 _ V47) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact D28].
Qed.
Lemma B_st_ok v : bcond v -> st_ok src0segs E1 (ssB v) ms.
Proof.
intros BC. pose proof (proj1 alloc_ceiling_val) as AC.
pose proof m1_facts as (A1 & A2 & A8 & Aimg & Apres & B8 & B28 & B32 & Fr & Hl & MBp & C1 & C2 & C8 & Cimg & Cpres & D28 & Fn & HD & APART).
destruct E1_vals as (V44 & V45 & V46 & V47 & V40). pose proof valsB as (Wfr & Wones & Wand & Wfr2 & W40 & W46).
pose proof (st_ok_agree src0segs 44 E E1 ss_beta ms HS E1_agree ss_beta_atoms) as HS1.
pose proof stations_shape as (Mb & _ & _ & Fb & _).
pose proof (base_mem_ok E1 ss_beta ms (SOff 40 0) HS1 Mb HA1 ltac:(rewrite W40, lit64_small by lia; exact HD)) as BASE.
destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (Sat & Scd & Sal)). rewrite Fb in Sat.
assert (DISJ1 : forall nxv r', In r' (R_actW (SOff 40 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1 (R_m1B nxv) r').
{ intros nxv r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m1B]. rewrite (base_atom E1 40 M1 V40) by lia.
destruct (base_disjoint E1 r' M1 (M1 + 40) HA1 ltac:(destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]) ltac:(lia) ltac:(lia) Aimg); lia. }
assert (DISJ2 : forall r', In r' (R_actW (SOff 40 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1 R_m2B r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m2B]. rewrite (base_atom E1 aNX1 NX1 V46) by lia.
destruct (base_disjoint E1 r' NX1 (NX1 + 40) HA1 ltac:(destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]) ltac:(lia) ltac:(lia) Cimg); lia. }
assert (FACTS : forall c, (acond_ok E1 c) -> facts_ok E1 (mkFacts (b_atoms ++ f_atoms (ss_facts ss_hd)) [C_frb; c] [])).
{ intros c Hc. unfold facts_ok, b_atoms. cbn [f_atoms f_conds f_alias app atoms_ok conds_ok alias_ok]. split; [|split; [|exact I]].
- unfold FM, FNZ, afact_ok; cbn [af_lo af_hi af_al2]. rewrite V40, V44, V45, V46, V47, (lit64_unsigned (meta_bits am1)), !lit64_small by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. pose proof (Z.mod_pos_bound (meta_bits am1) (2 ^ 64) ltac:(lia)).
repeat (split; [lia|]). exact Sat.
- split; [|split; [exact Hc | exact I]]. unfold acond_ok. cbn [ac_c ac_a ac_b C_frb]. rewrite branch_ne, Wand. cbn [sv_denot]. rewrite (lit64_small 0) by lia. reflexivity. }
assert (CN : am_freed am1 <> ones (am_last am1) -> acond_ok E1 C_noskip).
{ intros Hne. unfold acond_ok. cbn [ac_c ac_a ac_b C_noskip]. rewrite branch_ne, Wfr, Wones.
destruct (Z.eqb_spec (sx32 (am_freed am1)) (sx32 (ones (am_last am1)))) as [Ee|]; [|reflexivity]. exfalso. apply Hne. apply sx32_inj; [lia | | exact Ee].
unfold ones. split; [pose proof (Z.pow_pos_nonneg 2 (am_last am1 + 1)); lia | pose proof (Z.pow_le_mono_r 2 (am_last am1 + 1) 32); lia]. }
assert (CS : am_freed am1 = ones (am_last am1) -> acond_ok E1 C_skip).
{ intros Ee. unfold acond_ok. cbn [ac_c ac_a ac_b C_skip]. rewrite branch_eq, Wfr, Wones, Ee. apply Z.eqb_refl. }
destruct v; cbn [bcond] in BC; unfold st_ok, ssB, ss_Bn, ss_Bs, ss_Bss, ss_B; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts];
(split; [exact S1|]; split; [rewrite S2, ss_beta_pc; reflexivity|]; split; [exact S3|]; split; [exact S4|]; split; [exact S5|]; split; [exact S6|]; split; [exact S7|]; split).
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m1B; exact W46 | exact (DISJ1 _) | exact BASE].
- apply FACTS. apply CN. exact BC.
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m1B; exact W46 | | apply mem_ok_cons'; [reflexivity | apply region_m2B | exact DISJ2 | exact BASE]].
intros r' [<-|Hr']; [|exact (DISJ1 _ r' Hr')]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m1B R_m2B].
rewrite (base_atom E1 40 M1 V40), (base_atom E1 aNX1 NX1 V46) by lia. destruct (APART (proj2 BC)); lia.
- apply FACTS. apply CS. exact (proj1 BC).
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m1B; rewrite W40; unfold NX1; rewrite (proj2 BC); reflexivity | exact (DISJ1 _) | exact BASE].
- apply FACTS. apply CS. exact (proj1 BC).
Qed.
Definition s2v (v : bvar) : astate := match v with BVn => s1 | _ => hd_upd sc (Some nx1) s1 end.
Definition m2v (v : bvar) : sptr := match v with BVn => m1 | _ => nx1 end.
Definition am2v (v : bvar) : ameta := match v with BVn => am1 | _ => amn1 end.
Lemma selB_v v : bcond v -> SEL_B sc m1 am1 s1 = IRet (m2v v, s2v v).
Proof.
intros BC. destruct v; cbn [bcond m2v s2v] in *.
- first [exact (selB_noskip sc s1 m1 am1 BC) | exact (selB_noskip X U A sc s1 m1 am1 BC)].
- exact (selB_skip sc s1 m1 am1 nx1 (proj1 BC) (proj1 nx1_facts)).
- exact (selB_skip sc s1 m1 am1 nx1 (proj1 BC) (proj1 nx1_facts)).
Qed.
Lemma B_run v : bcond v ->
SR src0segs (mkCfg ms md) (fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E1 (SSB v) ms1 /\ frame_of E1 (ss_mem (ssB v)) (ms_mem ms) (ms_mem ms1)).
Proof.
intros BC. pose proof md_factsS as (Mh & Mlz & _). pose proof (B_st_ok v BC) as HS0.
assert (RUN : run_to_ok PS_C (ssB v) (fst (sym_run_toN src0segs src0tbl FUEL PS_C (ssB v)))) by (destruct v; [apply Bn_run_ok | apply Bs_run_ok | apply Bss_run_ok]).
eapply SR_mono; [eapply (SR_run_to PS_C); [exact HS0 | exact RUN | exact Mh | exact Mlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
assert (EE : SSB v = closeF (ssB v) PS_C) by (destruct v; symmetry; [apply SSB_n_eq | apply SSB_s_eq | apply SSB_ss_eq]).
rewrite EE. unfold closeF. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS0)].
Qed.
Section d0.
Variables (v : bvar) (ms1 : machine_state).
Hypothesis BC : bcond v.
Hypothesis HS2 : st_ok src0segs E1 (SSB v) ms1.
Hypothesis HF : frame_of E1 (ss_mem (ssB v)) (ms_mem ms) (ms_mem ms1).
Lemma m2_facts : usedX X s1 (m2v v) (am2v v) /\ NX1 = ptr_addr L (m2v v) \/ v = BVn.
Proof.
clear HS2 HF.
pose proof nx1_facts as (Hnx & Hun & _). destruct v; cbn [m2v am2v]; [right; reflexivity | left | left]; auto.
Qed.
Lemma postB_regs : getr (ms_regs ms1) 10 = Z_to_bv 64 (ptr_addr L (m2v v)) /\ getr (ms_regs ms1) 13 = Z_to_bv 64 (sx32 (am_freed (am2v v))) /\
ms_pc_val ms1 = Z_to_bv 64 PS_C.
Proof.
pose proof valsB as (Wfr & Wones & Wand & Wfr2 & W40 & W46).
pose proof (st_ok_reg src0segs E1 (SSB v) ms1 10 HS2) as R10'. pose proof (st_ok_reg src0segs E1 (SSB v) ms1 13 HS2) as R13'.
destruct HS2 as (_ & S2 & _).
assert (AMN : nx1 = m1 -> amn1 = am1).
{ intros Enx. unfold amn1. rewrite Enx, (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B1))). reflexivity. }
destruct HS2 as (_ & SPC & _).
destruct v; cbn [m2v am2v SSB bcond] in *;
[ pose proof SSB_n_shape as (_ & E10 & E13) | pose proof SSB_s_shape as (_ & E10 & E13) | pose proof SSB_ss_shape as (_ & E10 & E13) ];
rewrite E10 in R10'; rewrite E13 in R13'; rewrite R10', R13', SPC; (split; [| split; [apply word_eq; rewrite ?Wfr, ?Wfr2; symmetry; rewrite ?(AMN (proj2 BC)); apply lit64_small; apply sx32_range | reflexivity]]).
- exact W40.
- exact W46.
- rewrite W40. unfold M1. rewrite <- (proj2 BC). reflexivity.
Qed.
Lemma postB_mem :
(forall x, 0 <= x < 2 ^ 64 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ WS regs x -> (ms_mem ms1) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x)) /\
bytes_are (ms_mem ms1) (YN0j.CTX + 80 + 8 * sc) 8 (ptr_addr L (m2v v)).
Proof.
pose proof valsB as (Wfr & Wones & Wand & Wfr2 & W40 & W46). destruct E1_vals as (V44 & V45 & V46 & V47 & V40).
pose proof (agree_facts E1 HA1) as (_ & _ & B33 & B2 & _). pose proof m1_facts as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & _). pose proof (proj1 alloc_ceiling_val).
split.
- intros x Hx Hnh Hns. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw.
assert (Hw' : exists rs, (forall r, In r rs -> r_wlo r = 0 /\ r_whi r = 0) /\ in_wrange E1 (rs ++ R_actW (SOff 40 0) :: tl (ss_mem ss_hd)) x).
{ destruct v; cbn [ssB ss_Bn ss_Bs ss_Bss ss_B ss_mem] in Hw; eexists; (split; [|exact Hw]); intros r Hr; cbn [In] in Hr; decompose [or] Hr; try contradiction; subst r; split; reflexivity. }
clear Hw. destruct Hw' as (rs & Hrs & Hw). destruct (wrange_cases E1 rs _ x HA1 Hw) as [(r & Hin & Hr)|[Hh|Hs]]; [| exact (Hnh Hh) | exact (Hns Hs)].
destruct (Hrs r Hin) as [E1' E2']. rewrite E1', E2' in Hr. lia.
- pose proof (st_ok_mem_ok src0segs E1 (SSB v) ms1 HS2) as (_ & MOK & _).
assert (CH : exists hv, In (R_actW hv) (ss_mem (SSB v)) /\ sv_denot E1 hv = Z_to_bv 64 (ptr_addr L (m2v v))).
{ destruct v; cbn [SSB m2v]; [rewrite (proj1 SSB_n_shape) | rewrite (proj1 SSB_s_shape) | rewrite (proj1 SSB_ss_shape)]; cbn [ss_mem ss_Bn ss_Bss ss_B app].
- exists (SOff 40 0). split; [right; left; reflexivity | exact W40].
- exists (SOff aNX1 0). split; [right; right; left; reflexivity | exact W46].
- exists (SOff 40 0). split; [right; left; reflexivity | rewrite W40; unfold M1; rewrite <- (proj2 BC); reflexivity]. }
destruct CH as (hv & Hin & Hhv). pose proof (proj1 (Forall_forall _ _) MOK _ Hin) as (_ & _ & _ & CHm). cbn [r_chunks r_base R_actW] in CHm.
pose proof (Forall_inv CHm) as C0. rewrite B33 in C0.
replace (YN0j.CTX + 80 + 8 * sc) with (YN0j.LOCK + 8 * sc + 88) by (pose proof CTX_eq; lia).
rewrite <- (Z.mod_small (ptr_addr L (m2v v)) (2 ^ (8 * Z.of_N 8))) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct m2_facts as [[_ <-]| ->]; cbn [m2v]; unfold M1, NX1 in *; lia).
apply (chunk_bytes' E1 _ _ _ 8 hv); [exact C0 | rewrite Hhv; apply lit64_small; destruct m2_facts as [[_ <-]| ->]; cbn [m2v]; unfold M1, NX1 in *; lia].
Qed.
Lemma s2_same : sameX s1 (s2v v).
Proof. clear HS2 HF BC. destruct v; cbn [s2v]; [apply sameX_refl | apply sameX_set_active | apply sameX_set_active]. Qed.
Lemma s2_facts : sameX A (s2v v) /\ rawX X (s2v v) /\ user_blocks (s2v v) = user_blocks s1 /\ tail_cells (s2v v) = tail_cells s1 /\
st_metas (s2v v) = st_metas s1 /\ active_hd (s2v v) sc = Some (m2v v) /\ length (st_active (s2v v)) = 48%nat.
Proof.
clear HS2 HF BC.
pose proof B1 as [HI1 Hhd1 Hu1 Hs1 Hf1 Hz1 Hoth1 UB1 SX1 SP1]. pose proof (proj1 (inv_ctx HI1)) as Hlen.
destruct v; cbn [s2v m2v].
- repeat (split; [first [exact SX1 | exact RX1 | reflexivity | exact Hhd1] |]). exact Hlen.
- split; [eapply sameX_trans; [exact SX1 | apply sameX_set_active]|]. split; [intros x Hx; unfold hd_upd; rewrite MT_set_active; exact (RX1 x Hx)|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold hd_upd; apply active_hd_set_active_same; rewrite Hlen; lia | unfold hd_upd; cbn; rewrite length_lupd; exact Hlen].
- split; [eapply sameX_trans; [exact SX1 | apply sameX_set_active]|]. split; [intros x Hx; unfold hd_upd; rewrite MT_set_active; exact (RX1 x Hx)|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold hd_upd; apply active_hd_set_active_same; rewrite Hlen; lia | unfold hd_upd; cbn; rewrite length_lupd; exact Hlen].
Qed.
Lemma bnd2 : bnd X U A sc (s2v v) (m2v v) (am2v v).
Proof.
clear HS2 HF.
destruct (bnd_B X U A sc Hsc s1 m1 am1 B1 (m2v v) (s2v v) (selB_v v BC)) as (am2 & B2).
pose proof (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B2))) as M2.
assert (Eam : am2 = am2v v).
{ destruct m2_facts as [[Hu _]| Ev].
- pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as M2'. pose proof s2_facts as (_ & _ & _ & _ & Em & _). unfold MT in M2, M2'. rewrite Em in M2. congruence.
- revert B2 M2. rewrite Ev. cbn [m2v s2v am2v]. intros B2 M2. pose proof (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B1))). congruence. }
rewrite <- Eam. exact B2.
Qed.
Lemma postB_memrep : memrepX B X L (s2v v) (ms_mem ms1).
Proof.
pose proof B1 as [HI1 Hhd1 Hu1 Hs1 Hf1 Hz1 Hoth1 UB1 SX1 SP1]. pose proof bnd2 as [HI2 Hhd2 _ _ _ _ _ _ SX2 SP2].
pose proof s2_facts as (_ & RX2 & UBe & TCe & Em & Hhd2' & Hlen2). pose proof (proj1 (inv_ctx HI1)) as Hlen1.
pose proof postB_mem as [OUT HB]. pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val).
pose proof SX1 as (Erg1 & Ear1 & _). pose proof SX2 as (Erg2 & Ear2 & _).
assert (Efp : footprint (s2v v) = footprint s1) by (apply footprint_regions_areas; congruence).
refine (memrepX_after B X X None None U U s1 (s2v v) L (ms_mem ms) (ms_mem ms1) [hcell (Some (m2v v))] [] (sp - ASF, ASF)
HI1 HI2 (HLs s1 (ms_mem ms) MID1) Efp ltac:(congruence) (MRs None s1 (ms_mem ms) HI1 RX1 MID1) _ _ _ _ _ _ _ _).
- intros c Hc. destruct v; cbn [s2v m2v] in Hc |- *; [right; exact Hc| |];
(apply in_app_iff in Hc as [Hc|Hc]; [| right; apply in_app_iff; right; unfold hd_upd in Hc; rewrite tail_cellsX_set_active in Hc; exact Hc]);
(destruct (imageX_set_active X s1 (Z.to_nat sc) (Some nx1) c ltac:(rewrite Hlen1; lia) Hc) as [->|Ho]; [left; left; reflexivity | right; apply in_app_iff; left; exact Ho]).
- intros c [<-|[]]. right. rewrite <- Hhd2'. apply hcell_In. exact Hlen2.
- intros c [<-|[]]. apply hcell_mem. cbn [optrZ]. exact HB.
- intros c k [<-|[]] _ [p Hp]. exfalso. cbn [hcell act_cell mc_loc] in Hp. discriminate.
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. exact (footprint_top s1 e HI1 SX1 (or_intror (ex_intro _ (ms_mem ms) MID1)) He).
- intros a Ha Hno _ Hns.
assert (NH : ~ (YN0j.CTX + 80 + 8 * sc <= a < YN0j.CTX + 80 + 8 * sc + 8)).
{ intros W. apply (Hno (hcell (Some (m2v v))) (or_introl eq_refl)). unfold in_range. rewrite hcell_range. cbn [fst snd]. lia. }
assert (NS : ~ WS regs a) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; lia).
pose proof (OUT a Ha NH NS) as EQ. split; [apply mbyte_ext1; exact EQ|]. intros [b Hb]. exists b. rewrite EQ. exact Hb.
Qed.
Lemma postB : at_bnd ss_gamma 48 (fun E' => ew E' 51 = Z_to_bv 64 (sx32 (am_freed (am2v v)))) (s2v v) (m2v v) (mkCfg ms1 md).
Proof.
pose proof B1 as [HI1 Hhd1 Hu1 Hs1 Hf1 Hz1 Hoth1 UB1 SX1 SP1]. pose proof bnd2 as [HI2 _ _ _ _ _ _ _ SX2 SP2].
pose proof s2_facts as (_ & RX2 & UBe & TCe & Em & Hhd2' & Hlen2). pose proof postB_mem as [OUT HB]. pose proof postB_regs as (G10 & G13 & GPC).
assert (MG : ss_atoms_lt 48 (SSB v) = true /\ mergeb ss_gamma (junk_regs JG 48 (SSB v)) = true) by (destruct v; [apply merge_Bn | apply merge_Bs | apply merge_Bss]).
destruct (junk_regs_ok src0segs JG 48 E1 (SSB v) ms1 HS2 (proj1 MG) eq_refl) as (E2 & HA2 & HSj).
pose proof (st_ok_merge src0segs E2 ss_gamma _ ms1 HSj (proj2 MG)) as HSg.
exists E2, ms1. split; [reflexivity|]. split; [exact HSg|].
split; [eapply env_agree_trans; [exact HA1 | eapply env_agree_le; [| exact HA2]; lia]|].
pose proof stations_shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G48 & G51 & _).
split; [| split; [| split; [exact RX2 | split]]].
- pose proof (st_ok_reg src0segs E2 ss_gamma ms1 10 HSg) as R. rewrite G48, G10 in R. cbn [sv_denot] in R. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R. symmetry. exact R.
- pose proof (st_ok_reg src0segs E2 ss_gamma ms1 13 HSg) as R. rewrite G51, G13 in R. cbn [sv_denot] in R. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R. symmetry. exact R.
- apply (midrep_transport s1 (s2v v) (ms_mem ms) (ms_mem ms1) HI1 RX1 MID1 s2_same RX2 (ex_intro _ None HI2) postB_memrep UBe TCe).
+ intros a Hs. destruct (static_range a Hs) as [R1 R2]. apply OUT; [lia | intros W; apply R2; unfold CTX_SIZE; lia | unfold WS; fold sp; pose proof pre_factsS as (_ & _ & P3 & _); pose proof alloc_ceiling_val; pose proof Hstk; unfold ASF in *; lia].
- intros x Hx Hns Hnc Hno. rewrite (OUT x Hx) by (first [intros W; apply Hnc; unfold CTX_SIZE; lia | exact Hns]). exact (FR1 x Hx Hns Hnc Hno).
Qed.
End d0.
Theorem stage_B : exists v, bcond v /\ SEL_B sc m1 am1 s1 = IRet (m2v v, s2v v) /\ bnd X U A sc (s2v v) (m2v v) (am2v v) /\
SR src0segs (mkCfg ms md) (at_bnd ss_gamma 48 (fun E' => ew E' 51 = Z_to_bv 64 (sx32 (am_freed (am2v v)))) (s2v v) (m2v v)).
Proof.
assert (V : exists v, bcond v).
{ destruct (Z.eq_dec (am_freed am1) (ones (am_last am1))) as [Ee|NE]; [|exists BVn; exact NE].
destruct (sptr_eq_dec nx1 m1) as [Ee2|NE2]; [exists BVss | exists BVs]; split; assumption. }
destruct V as [v BC]. exists v. split; [exact BC|]. split; [exact (selB_v v BC)|]. split; [exact (bnd2 v BC)|].
eapply SR_mono; [exact (B_run v BC)|]. intros c' (ms1 & -> & HS2 & HF). first [exact (postB v ms1 BC HS2 HF) | exact (postB v BC ms1 HS2 HF)].
Qed.
End c0.
Section e0.
Variables (s2 : astate) (m2 : sptr) (am2 : ameta) (E : env) (ms : machine_state).
Hypothesis B2 : bnd X U A sc s2 m2 am2.
Hypothesis HS : st_ok src0segs E ss_gamma ms.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis E48 : ew E 48 = Z_to_bv 64 (ptr_addr L m2).
Hypothesis E51 : ew E 51 = Z_to_bv 64 (sx32 (am_freed am2)).
Hypothesis RX2 : rawX X s2.
Hypothesis MID2 : midrep B L s2 (ms_mem ms) md.
Hypothesis FR2 : FRAME (ms_mem ms).
Definition nx2 : sptr := match am_next am2 with Some p => p | None => m2 end.
Definition amn2 : ameta := match MT s2 nx2 with Some (MUsed a) => a | _ => am2 end.
Definition M2 : Z := ptr_addr L m2.
Definition NX2 : Z := ptr_addr L nx2.
Definition G2 : Z := ptr_addr L (am_mem am2).
Definition aib : Z := match mbyte src0segs (ms_mem ms) (G2 + 8) with Some b => bv_unsigned b | None => 0 end.
Lemma nx2_facts : am_next am2 = Some nx2 /\ usedX X s2 nx2 amn2 /\ am_sc amn2 = sc /\ am_freed amn2 <> 0 /\ am_avail amn2 = 0 /\
(Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> nx2 <> m2 -> Z.land (am_freed amn2) (ones (am_aidx amn2)) <> 0).
Proof.
destruct (links2 X U A sc Hsc s2 m2 am2 B2) as (pr & nx & amnx & Hpr & Hnx & Hun & Hsn & Hfn & Havn & Hpart).
assert (E1' : nx2 = nx) by (unfold nx2; rewrite Hnx; reflexivity).
assert (E2' : amn2 = amnx) by (unfold amn2; rewrite E1', (proj1 (usedX_MT _ _ _ _ Hun)); reflexivity).
rewrite E1', E2'. auto 10.
Qed.
Definition E1c : env := ewset (ewset (ewset E aG2 (Z_to_bv 64 G2)) aAI2 (Z_to_bv 64 aib)) aNX2 (Z_to_bv 64 NX2).
Lemma E1c_agree : env_agree 52 E E1c.
Proof.
unfold E1c. eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aNX2; lia].
eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aAI2; lia].
eapply env_agree_le; [| apply env_agree_ewset]. unfold aG2; lia.
Qed.
Lemma HA1c : env_agree 40 E00 E1c.
Proof. eapply env_agree_trans; [exact HA | eapply env_agree_le; [| apply E1c_agree]; lia]. Qed.
Lemma E1c_vals : ew E1c aG2 = Z_to_bv 64 G2 /\ ew E1c aAI2 = Z_to_bv 64 aib /\ ew E1c aNX2 = Z_to_bv 64 NX2 /\ ew E1c 48 = Z_to_bv 64 M2 /\ ew E1c 51 = Z_to_bv 64 (sx32 (am_freed am2)).
Proof.
unfold E1c, aG2, aAI2, aNX2.
repeat split; rewrite ?ew_ewset_same; try reflexivity; rewrite !ew_ewset_other by lia; rewrite ?ew_ewset_same; try reflexivity; [exact E48 | exact E51].
Qed.
Lemma m2_factsC :
4096 <= M2 /\ M2 + 40 <= alloc_ceiling /\ M2 mod 8 = 0 /\ (M2 + 40 <= 0x10000 \/ 0x51000 <= M2) /\ (forall x, M2 <= x < M2 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (M2 + 8) 8 NX2 /\ bytes_are (ms_mem ms) (M2 + 16) 8 G2 /\ bytes_are (ms_mem ms) (M2 + 24) 4 0 /\
0 < am_freed am2 < 2 ^ 32 /\ 0 <= am_aidx am2 <= am_last am2 /\ am_last am2 <= 31 /\
4096 <= NX2 /\ NX2 + 40 <= alloc_ceiling /\ NX2 mod 8 = 0 /\ (NX2 + 40 <= 0x10000 \/ 0x51000 <= NX2) /\ (forall x, NX2 <= x < NX2 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (NX2 + 24) 4 0 /\
4096 <= G2 /\ G2 + 16 <= alloc_ceiling /\ G2 mod 16 = 0 /\ (G2 + 16 <= 0x10000 \/ 0x51000 <= G2) /\ (forall x, G2 <= x < G2 + 16 -> present (ms_mem ms) x) /\
mbyte src0segs (ms_mem ms) (G2 + 8) = Some (Z_to_bv 8 aib) /\ aib mod 32 = am_aidx am2 /\ 0 <= aib < 256 /\
(nx2 <> m2 -> M2 + 40 <= NX2 \/ NX2 + 40 <= M2) /\ (G2 + 16 <= M2 \/ M2 + 40 <= G2) /\ (G2 + 16 <= NX2 \/ NX2 + 40 <= G2).
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof nx2_facts as (Hnx & Hun & Hsn & Hfn & Havn & _). pose proof (proj1 alloc_ceiling_val).
pose proof (metaS None s2 (ms_mem ms) HI2 RX2 MID2 m2 am2 Hu2) as (A1 & A2 & A3 & A4 & A5 & _ & B8 & B16 & B24 & _ & _ & _ & R2 & R3 & R4 & _).
pose proof (metaS None s2 (ms_mem ms) HI2 RX2 MID2 nx2 amn2 Hun) as (C1 & C2 & C3 & C4 & C5 & _ & _ & _ & D24 & _).
pose proof (grpS None s2 (ms_mem ms) HI2 RX2 MID2 m2 am2 Hu2) as (G1 & G2' & G3 & G4 & G5 & (b & Hb & Hbm) & _).
rewrite Hnx in B8. cbn [optrZ] in B8. rewrite (Hz2 _ _ Hu2 Hs2) in B24. rewrite Havn in D24.
assert (Eaib : aib = bv_unsigned b) by (unfold aib; fold G2 in Hb; rewrite Hb; reflexivity). pose proof (u8_range b).
unfold M2, NX2, G2 in *. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- apply (YN0p.off_img _ A4).
- apply (YN0p.off_img _ C4).
- apply (off_img_range' _ 16 G4). lia.
- rewrite Hb, Eaib, Z_to_bv_bv_unsigned. reflexivity.
- rewrite Eaib. exact Hbm.
- intros Hne. apply (apartS None s2 (ms_mem ms) HI2 MID2 m2 nx2 am2 amn2 Hu2 Hun). intros Heq. exact (Hne (eq_sym Heq)).
- exact (grp_meta_apart None s2 (ms_mem ms) HI2 RX2 MID2 m2 am2 m2 am2 Hu2 Hu2).
- exact (grp_meta_apart None s2 (ms_mem ms) HI2 RX2 MID2 m2 am2 nx2 amn2 Hu2 Hun).
Qed.
Lemma valsC :
bv_unsigned (sv_denot E1c MA2) = sx32 (Z.land (ones (am_aidx am2)) (am_freed am2)) /\
sv_denot E1c (SOff 48 0) = Z_to_bv 64 M2 /\ sv_denot E1c (SOff aNX2 0) = Z_to_bv 64 NX2 /\ sv_denot E1c (SOff aG2 0) = Z_to_bv 64 G2.
Proof.
pose proof m2_factsC as (A1 & A2 & _ & _ & _ & _ & _ & _ & Fr & Hai & Hl & C1 & C2 & _ & _ & _ & _ & G1 & G2' & _ & _ & _ & _ & Hbm & Hb8 & _). pose proof (proj1 alloc_ceiling_val).
destruct E1c_vals as (V52 & V53 & V54 & V48 & V51).
split; [|split; [|split]].
- cbv delta [MA2 ACT2]. cbn [sv_denot]. rewrite alu64_and, addw_rr_unsigned, sllw_rr_unsigned, !Z.add_0_r, !Z_to_bv_bv_unsigned, V53, V51.
rewrite (lit64_small 2), (lit64_small aib), (lit64_small (sx32 _)) by (try apply sx32_range; lia). rewrite lit64_unsigned. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite (proj2 (addiw_sllw2_m1 aib ltac:(lia))), Hbm. apply land_sx32.
- apply (den_atom0 E1c 48 _ V48). lia.
- apply (den_atom0 E1c aNX2 _ V54). lia.
- apply (den_atom0 E1c aG2 _ V52). lia.
Qed.
Inductive cvar := CV0 | CV1.
Definition ssC (v : cvar) : sstate := match v with CV0 => ss_C0 | CV1 => ss_C1 end.
Definition SSC (v : cvar) : sstate := match v with CV0 => SSC_0 | CV1 => SSC_1 end.
Definition ccond (v : cvar) : Prop :=
match v with
| CV0 => Z.land (am_freed am2) (ones (am_aidx am2)) <> 0
| CV1 => Z.land (am_freed am2) (ones (am_aidx am2)) = 0 /\ nx2 <> m2
end.
Lemma region_m2C : region_ok src0segs E1c (ms_mem ms) (R_m2C (SOff aNX2 0)).
Proof.
pose proof m2_factsC as (A1 & A2 & A8 & Aimg & Apres & B8 & B16 & B24 & Fr & Hai & Hl & C1 & C2 & _ & _ & _ & _ & G1 & G2' & _). pose proof (proj1 alloc_ceiling_val).
destruct E1c_vals as (V52 & V53 & V54 & V48 & V51). pose proof valsC as (_ & W48 & W54 & W52).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m2C]; rewrite (base_atom E1c 48 M2 V48) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_ok_val' E1c _ _ _ 8 _ NX2); [rewrite W54; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B8].
- apply (chunk_ok_val' E1c _ _ _ 8 _ G2); [rewrite W52; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B16].
- apply (chunk_ok_val' E1c _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B24].
Qed.
Lemma region_g2 : region_ok src0segs E1c (ms_mem ms) R_g2.
Proof.
pose proof m2_factsC as (A1 & A2 & A8 & Aimg & Apres & B8 & B16 & B24 & Fr & Hai & Hl & C1 & C2 & _ & _ & _ & _ & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & _). pose proof (proj1 alloc_ceiling_val).
destruct E1c_vals as (V52 & V53 & V54 & V48 & V51).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_g2]; rewrite (base_atom E1c aG2 G2 V52) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1c _ _ _ 1 _ aib); [rewrite (den_atom0 E1c aAI2 _ V53) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
intros kk Hkk. replace kk with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256. rewrite (Z.mod_small aib 256), Z.mod_small by lia. reflexivity.
Qed.
Lemma region_nxC : region_ok src0segs E1c (ms_mem ms) R_nxC.
Proof.
pose proof m2_factsC as (A1 & A2 & A8 & Aimg & Apres & B8 & B16 & B24 & Fr & Hai & Hl & C1 & C2 & C8 & Cimg & Cpres & D24 & _). pose proof (proj1 alloc_ceiling_val).
destruct E1c_vals as (V52 & V53 & V54 & V48 & V51).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_nxC]; rewrite (base_atom E1c aNX2 NX2 V54) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1c _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact D24].
Qed.
Lemma C_st_ok v : ccond v -> st_ok src0segs E1c (ssC v) ms.
Proof.
intros CC. pose proof (proj1 alloc_ceiling_val) as AC.
pose proof m2_factsC as (A1 & A2 & A8 & Aimg & Apres & B8 & B16 & B24 & Fr & Hai & Hl & C1 & C2 & C8 & Cimg & Cpres & D24 & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & AP1 & AP2 & AP3).
destruct E1c_vals as (V52 & V53 & V54 & V48 & V51). pose proof valsC as (Wma & W48 & W54 & W52).
pose proof (st_ok_agree src0segs 52 E E1c ss_gamma ms HS E1c_agree ss_gamma_atoms) as HS1.
pose proof stations_shape as (_ & Mg & _ & _ & Fg & _).
pose proof B2 as [HI2 Hhd2 _ _ _ _ _ _ _ SP2].
pose proof (headS None s2 (ms_mem ms) HI2 RX2 MID2) as HD. rewrite Hhd2 in HD. cbn [optrZ] in HD.
pose proof (base_mem_ok E1c ss_gamma ms (SOff 48 0) HS1 Mg HA1c ltac:(rewrite W48, lit64_small by lia; exact HD)) as BASE.
destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (Sat & Scd & Sal)). rewrite Fg in Sat.
assert (BD : forall r' lo hi, In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> 4096 <= lo -> hi <= alloc_ceiling -> (hi <= 0x10000 \/ 0x51000 <= lo) -> hi <= base_val E1c (r_base r') + r_lo r' \/ base_val E1c (r_base r') + r_hi r' <= lo).
{ intros r' lo hi Hr'. apply (base_disjoint E1c r' lo hi HA1c). destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]. }
assert (Dm2 : forall r', In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1c (R_m2C (SOff aNX2 0)) r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m2C]. rewrite (base_atom E1c 48 M2 V48) by lia. destruct (BD r' M2 (M2 + 40) Hr' ltac:(lia) ltac:(lia) Aimg); lia. }
assert (Dg2 : forall r', In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1c R_g2 r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_g2]. rewrite (base_atom E1c aG2 G2 V52) by lia. destruct (BD r' G2 (G2 + 16) Hr' ltac:(lia) ltac:(lia) Gimg); lia. }
assert (Dnx : forall r', In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1c R_nxC r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_nxC]. rewrite (base_atom E1c aNX2 NX2 V54) by lia. destruct (BD r' NX2 (NX2 + 40) Hr' ltac:(lia) ltac:(lia) Cimg); lia. }
assert (FACTS : forall cs, conds_ok E1c cs -> facts_ok E1c (mkFacts (c_atoms ++ f_atoms (ss_facts ss_hd)) cs [])).
{ intros cs Hcs. unfold facts_ok, c_atoms. cbn [f_atoms f_conds f_alias app atoms_ok alias_ok]. split; [|split; [exact Hcs | exact I]].
unfold FM, afact_ok; cbn [af_lo af_hi af_al2]. rewrite V48, V51, V52, V53, V54, !lit64_small by (try apply sx32_range; lia).
change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. pose proof (sx32_range (am_freed am2)).
repeat (split; [lia|]). exact Sat. }
assert (C0ok : Z.land (am_freed am2) (ones (am_aidx am2)) <> 0 -> acond_ok E1c C_c0).
{ intros Hne. unfold acond_ok. cbn [ac_c ac_a ac_b C_c0]. rewrite branch_ne, Wma. cbn [sv_denot]. rewrite (lit64_small 0) by lia.
rewrite Z.land_comm. destruct (Z.eqb_spec (sx32 (Z.land (am_freed am2) (ones (am_aidx am2)))) 0) as [Ee|]; [|reflexivity]. exfalso. apply Hne.
assert (LR : 0 <= Z.land (am_freed am2) (ones (am_aidx am2)) < 2 ^ 32) by (split; [apply Z.land_nonneg; lia | apply (Z.le_lt_trans _ (am_freed am2)); [apply land_le_l; lia | lia]]).
apply (proj1 (sx32_zero_iff_u32 _ LR)). exact Ee. }
assert (C12ok : Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> acond_ok E1c C_c12).
{ intros Ee. unfold acond_ok. cbn [ac_c ac_a ac_b C_c12]. rewrite branch_eq, Wma. cbn [sv_denot]. rewrite (lit64_small 0) by lia. rewrite Z.land_comm, Ee. reflexivity. }
assert (CNXok : nx2 <> m2 -> acond_ok E1c C_nx2).
{ intros Hne. unfold acond_ok. cbn [ac_c ac_a ac_b C_nx2]. rewrite branch_ne, W48, W54, !lit64_small by lia. destruct (AP1 Hne); destruct (Z.eqb_spec NX2 M2); try reflexivity; lia. }
destruct v; cbn [ccond] in CC; unfold st_ok, ssC, ss_C0, ss_C1, ss_C; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts];
(split; [exact S1|]; split; [rewrite S2, ss_gamma_pc; reflexivity|]; split; [exact S3|]; split; [exact S4|]; split; [exact S5|]; split; [exact S6|]; split; [exact S7|]; split).
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m2C | | apply mem_ok_cons'; [reflexivity | apply region_g2 | exact Dg2 | exact BASE]].
intros r' [<-|Hr']; [|exact (Dm2 r' Hr')]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m2C R_g2]. rewrite (base_atom E1c 48 M2 V48), (base_atom E1c aG2 G2 V52) by lia. lia.
- apply FACTS. split; [apply C0ok; exact CC | exact I].
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m2C | | apply mem_ok_cons'; [reflexivity | apply region_g2 | | apply mem_ok_cons'; [reflexivity | apply region_nxC | exact Dnx | exact BASE]]].
+ intros r' [<-|[<-|Hr']]; [| |exact (Dm2 r' Hr')]; unfold extent_disjoint; cbn [r_base r_lo r_hi R_m2C R_g2 R_nxC];
rewrite (base_atom E1c 48 M2 V48), ?(base_atom E1c aG2 G2 V52), ?(base_atom E1c aNX2 NX2 V54) by lia; [lia | destruct (AP1 (proj2 CC)); lia].
+ intros r' [<-|Hr']; [|exact (Dg2 r' Hr')]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_g2 R_nxC]. rewrite (base_atom E1c aG2 G2 V52), (base_atom E1c aNX2 NX2 V54) by lia. lia.
- apply FACTS. split; [apply C12ok; exact (proj1 CC) | split; [apply CNXok; exact (proj2 CC) | exact I]].
Qed.
Definition s3v (v : cvar) : astate := match v with CV0 => s2 | CV1 => hd_upd sc (Some nx2) s2 end.
Definition m3v (v : cvar) : sptr := match v with CV0 => m2 | CV1 => nx2 end.
Definition am3v (v : cvar) : ameta := match v with CV0 => am2 | CV1 => amn2 end.
Lemma selC_v v : ccond v -> SEL_C sc m2 am2 s2 = IRet (m3v v, s3v v).
Proof.
intros CC. destruct v; cbn [ccond m3v s3v] in *.
- exact (selC_0 sc s2 m2 am2 CC).
- exact (selC_1 sc s2 m2 am2 nx2 (proj1 CC) (proj1 nx2_facts) (proj2 CC)).
Qed.
Lemma C_run v : ccond v ->
SR src0segs (mkCfg ms md) (fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E1c (SSC v) ms1 /\ frame_of E1c (ss_mem (ssC v)) (ms_mem ms) (ms_mem ms1)).
Proof.
intros CC. pose proof md_factsS as (Mh & Mlz & _). pose proof (C_st_ok v CC) as HS0.
assert (RUN : run_to_ok PS_D (ssC v) (fst (sym_run_toN src0segs src0tbl FUEL PS_D (ssC v)))) by (destruct v; [apply C0_run_ok | apply C1_run_ok]).
eapply SR_mono; [eapply (SR_run_to PS_D); [exact HS0 | exact RUN | exact Mh | exact Mlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
assert (EE : SSC v = closeF (ssC v) PS_D) by (destruct v; symmetry; [apply SSC_0_eq | apply SSC_1_eq]).
rewrite EE. unfold closeF. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS0)].
Qed.
Section f0.
Variables (v : cvar) (ms1 : machine_state).
Hypothesis CC : ccond v.
Hypothesis HS2 : st_ok src0segs E1c (SSC v) ms1.
Hypothesis HF : frame_of E1c (ss_mem (ssC v)) (ms_mem ms) (ms_mem ms1).
Lemma m3_facts : usedX X s2 (m3v v) (am3v v).
Proof. clear HS2 HF. pose proof nx2_facts as (Hnx & Hun & _). destruct v; cbn [m3v am3v]; [exact (b_used _ _ _ _ _ _ _ B2) | exact Hun]. Qed.
Lemma postC_regs : getr (ms_regs ms1) 10 = Z_to_bv 64 (ptr_addr L (m3v v)) /\ ms_pc_val ms1 = Z_to_bv 64 PS_D.
Proof.
pose proof valsC as (Wma & W48 & W54 & W52).
pose proof (st_ok_reg src0segs E1c (SSC v) ms1 10 HS2) as R10'. destruct HS2 as (_ & SPC & _).
destruct v; cbn [m3v SSC] in *; [ pose proof SSC_0_shape as (_ & E10) | pose proof SSC_1_shape as (_ & E10) ];
rewrite E10 in R10'; rewrite R10', SPC; (split; [| reflexivity]); [exact W48 | exact W54].
Qed.
Lemma postC_mem :
(forall x, 0 <= x < 2 ^ 64 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ WS regs x -> (ms_mem ms1) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x)) /\
bytes_are (ms_mem ms1) (YN0j.CTX + 80 + 8 * sc) 8 (ptr_addr L (m3v v)).
Proof.
pose proof valsC as (Wma & W48 & W54 & W52). destruct E1c_vals as (V52 & V53 & V54 & V48 & V51).
pose proof (agree_facts E1c HA1c) as (_ & _ & B33 & B2' & _). pose proof m2_factsC as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & _). pose proof (proj1 alloc_ceiling_val).
split.
- intros x Hx Hnh Hns. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw.
assert (Hw' : exists rs, (forall r, In r rs -> r_wlo r = 0 /\ r_whi r = 0) /\ in_wrange E1c (rs ++ R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) x).
{ destruct v; cbn [ssC ss_C0 ss_C1 ss_C ss_mem] in Hw; eexists; (split; [|exact Hw]); intros r Hr; cbn [In] in Hr; decompose [or] Hr; try contradiction; subst r; split; reflexivity. }
clear Hw. destruct Hw' as (rs & Hrs & Hw). destruct (wrange_cases E1c rs _ x HA1c Hw) as [(r & Hin & Hr)|[Hh|Hs']]; [| exact (Hnh Hh) | exact (Hns Hs')].
destruct (Hrs r Hin) as [E1' E2']. rewrite E1', E2' in Hr. lia.
- pose proof (st_ok_mem_ok src0segs E1c (SSC v) ms1 HS2) as (_ & MOK & _).
assert (CH : exists hv, In (R_actW hv) (ss_mem (SSC v)) /\ sv_denot E1c hv = Z_to_bv 64 (ptr_addr L (m3v v))).
{ destruct v; cbn [SSC m3v]; [rewrite (proj1 SSC_0_shape) | rewrite (proj1 SSC_1_shape)]; cbn [ss_mem ss_C0 ss_C app].
- exists (SOff 48 0). split; [right; right; left; reflexivity | exact W48].
- exists (SOff aNX2 0). split; [do 3 right; left; reflexivity | exact W54]. }
destruct CH as (hv & Hin & Hhv). pose proof (proj1 (Forall_forall _ _) MOK _ Hin) as (_ & _ & _ & CHm). cbn [r_chunks r_base R_actW] in CHm.
pose proof (Forall_inv CHm) as C0. rewrite B33 in C0.
replace (YN0j.CTX + 80 + 8 * sc) with (YN0j.LOCK + 8 * sc + 88) by (pose proof CTX_eq; lia).
assert (MR3 : 0 <= ptr_addr L (m3v v) < 2 ^ 64) by (destruct v; cbn [m3v]; unfold M2, NX2 in *; lia).
rewrite <- (Z.mod_small (ptr_addr L (m3v v)) (2 ^ (8 * Z.of_N 8))) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact MR3).
apply (chunk_bytes' E1c _ _ _ 8 hv); [exact C0 | rewrite Hhv; apply lit64_small; exact MR3].
Qed.
Lemma s3_same : sameX s2 (s3v v).
Proof. clear HS2 HF CC. destruct v; cbn [s3v]; [apply sameX_refl | apply sameX_set_active]. Qed.
Lemma s3_facts : sameX A (s3v v) /\ rawX X (s3v v) /\ user_blocks (s3v v) = user_blocks s2 /\ tail_cells (s3v v) = tail_cells s2 /\
st_metas (s3v v) = st_metas s2 /\ active_hd (s3v v) sc = Some (m3v v) /\ length (st_active (s3v v)) = 48%nat.
Proof.
clear HS2 HF CC.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof (proj1 (inv_ctx HI2)) as Hlen.
destruct v; cbn [s3v m3v].
- repeat (split; [first [exact SX2 | exact RX2 | reflexivity | exact Hhd2] |]). exact Hlen.
- split; [eapply sameX_trans; [exact SX2 | apply sameX_set_active]|]. split; [intros x Hx; unfold hd_upd; rewrite MT_set_active; exact (RX2 x Hx)|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold hd_upd; apply active_hd_set_active_same; rewrite Hlen; lia | unfold hd_upd; cbn; rewrite length_lupd; exact Hlen].
Qed.
Lemma bnd3 : bnd X U A sc (s3v v) (m3v v) (am3v v) /\ Z.land (am_freed (am3v v)) (ones (am_aidx (am3v v))) <> 0.
Proof.
clear HS2 HF.
destruct (bnd_C X U A sc Hsc s2 m2 am2 B2 (m3v v) (s3v v) (selC_v v CC)) as (am3 & B3 & Hm3).
pose proof (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B3))) as M3.
pose proof (proj1 (usedX_MT _ _ _ _ m3_facts)) as M3'. pose proof s3_facts as (_ & _ & _ & _ & Em & _).
assert (Eam : am3 = am3v v) by (unfold MT in M3, M3'; rewrite Em in M3; congruence).
rewrite <- Eam. split; [exact B3 | exact Hm3].
Qed.
Lemma postC_memrep : memrepX B X L (s3v v) (ms_mem ms1).
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof (proj1 bnd3) as [HI3 Hhd3 _ _ _ _ _ _ SX3 SP3].
pose proof s3_facts as (_ & RX3 & UBe & TCe & Em & Hhd3' & Hlen3). pose proof (proj1 (inv_ctx HI2)) as Hlen2.
pose proof postC_mem as [OUT HB]. pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val).
pose proof SX2 as (Erg2 & Ear2 & _). pose proof SX3 as (Erg3 & Ear3 & _).
assert (Efp : footprint (s3v v) = footprint s2) by (apply footprint_regions_areas; congruence).
refine (memrepX_after B X X None None U U s2 (s3v v) L (ms_mem ms) (ms_mem ms1) [hcell (Some (m3v v))] [] (sp - ASF, ASF)
HI2 HI3 (HLs s2 (ms_mem ms) MID2) Efp ltac:(congruence) (MRs None s2 (ms_mem ms) HI2 RX2 MID2) _ _ _ _ _ _ _ _).
- intros c Hc. destruct v; cbn [s3v m3v] in Hc |- *; [right; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc]; [| right; apply in_app_iff; right; unfold hd_upd in Hc; rewrite tail_cellsX_set_active in Hc; exact Hc].
destruct (imageX_set_active X s2 (Z.to_nat sc) (Some nx2) c ltac:(rewrite Hlen2; lia) Hc) as [->|Ho]; [left; left; reflexivity | right; apply in_app_iff; left; exact Ho].
- intros c [<-|[]]. right. rewrite <- Hhd3'. apply hcell_In. exact Hlen3.
- intros c [<-|[]]. apply hcell_mem. cbn [optrZ]. exact HB.
- intros c k [<-|[]] _ [p Hp]. exfalso. cbn [hcell act_cell mc_loc] in Hp. discriminate.
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. exact (footprint_top s2 e HI2 SX2 (or_intror (ex_intro _ (ms_mem ms) MID2)) He).
- intros a Ha Hno _ Hns.
assert (NH : ~ (YN0j.CTX + 80 + 8 * sc <= a < YN0j.CTX + 80 + 8 * sc + 8)).
{ intros W. apply (Hno (hcell (Some (m3v v))) (or_introl eq_refl)). unfold in_range. rewrite hcell_range. cbn [fst snd]. lia. }
assert (NS : ~ WS regs a) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; lia).
pose proof (OUT a Ha NH NS) as EQ. split; [apply mbyte_ext1; exact EQ|]. intros [b Hb]. exists b. rewrite EQ. exact Hb.
Qed.
Lemma postC : at_bnd ss_delta 80 (fun _ => True) (s3v v) (m3v v) (mkCfg ms1 md).
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof (proj1 bnd3) as [HI3 _ _ _ _ _ _ _ SX3 SP3].
pose proof s3_facts as (_ & RX3 & UBe & TCe & Em & Hhd3' & Hlen3). pose proof postC_mem as [OUT HB]. pose proof postC_regs as (G10 & GPC).
assert (MG : ss_atoms_lt 80 (SSC v) = true /\ mergeb ss_delta (junk_regs JD 80 (SSC v)) = true) by (destruct v; [apply merge_C0 | apply merge_C1]).
destruct (junk_regs_ok src0segs JD 80 E1c (SSC v) ms1 HS2 (proj1 MG) eq_refl) as (E2 & HA2 & HSj).
pose proof (st_ok_merge src0segs E2 ss_delta _ ms1 HSj (proj2 MG)) as HSd.
exists E2, ms1. split; [reflexivity|]. split; [exact HSd|].
split; [eapply env_agree_trans; [exact HA1c | eapply env_agree_le; [| exact HA2]; lia]|].
pose proof stations_shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G80 & _).
split; [| split; [exact I | split; [exact RX3 | split]]].
- pose proof (st_ok_reg src0segs E2 ss_delta ms1 10 HSd) as R. rewrite G80, G10 in R. cbn [sv_denot] in R. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R. symmetry. exact R.
- apply (midrep_transport s2 (s3v v) (ms_mem ms) (ms_mem ms1) HI2 RX2 MID2 s3_same RX3 (ex_intro _ None HI3) postC_memrep UBe TCe).
intros a Hs. destruct (static_range a Hs) as [R1 R2]. apply OUT; [lia | intros W; apply R2; unfold CTX_SIZE; lia | unfold WS; fold sp; pose proof pre_factsS as (_ & _ & P3 & _); pose proof alloc_ceiling_val; pose proof Hstk; unfold ASF in *; lia].
- intros x Hx Hns Hnc Hno. rewrite (OUT x Hx) by (first [intros W; apply Hnc; unfold CTX_SIZE; lia | exact Hns]). exact (FR2 x Hx Hns Hnc Hno).
Qed.
End f0.
Theorem stage_C01 : Z.land (am_freed am2) (ones (am_aidx am2)) <> 0 \/ nx2 <> m2 ->
exists v, ccond v /\ SEL_C sc m2 am2 s2 = IRet (m3v v, s3v v) /\ bnd X U A sc (s3v v) (m3v v) (am3v v) /\ Z.land (am_freed (am3v v)) (ones (am_aidx (am3v v))) <> 0 /\
SR src0segs (mkCfg ms md) (at_bnd ss_delta 80 (fun _ => True) (s3v v) (m3v v)).
Proof.
intros CASE.
assert (V : exists v, ccond v).
{ destruct (Z.eq_dec (Z.land (am_freed am2) (ones (am_aidx am2))) 0) as [Ee|NE]; [|exists CV0; exact NE].
exists CV1. split; [exact Ee|]. destruct CASE as [H|H]; [exfalso; exact (H Ee) | exact H]. }
destruct V as [v CC]. exists v. split; [exact CC|]. split; [exact (selC_v v CC)|]. split; [exact (proj1 (bnd3 v CC))|]. split; [exact (proj2 (bnd3 v CC))|].
eapply SR_mono; [exact (C_run v CC)|]. intros c' (ms1 & -> & HS2 & HF). first [exact (postC v ms1 CC HS2 HF) | exact (postC v CC ms1 HS2 HF)].
Qed.
Section g0.
Hypothesis Ec : Z.land (am_freed am2) (ones (am_aidx am2)) = 0.
Hypothesis Hnx : am_next am2 = Some m2.
Definition BITS : Z := meta_bits am2.
Definition scl : Z := scl_of sc.
Definition size : Z := class_size sc.
Definition aidx : Z := am_aidx am2.
Definition last : Z := am_last am2.
Definition span0 : Z := UNIT + size * (aidx + 2).
Definition CNT : Z := span_loop 299 (aidx + 2) span0 size.
Definition NB : Z := span_byte CNT last aib.
Definition am2' : ameta := am_set_aidx (span_cnt am2 - 1) am2.
Definition E1s : env := ewset E1c aBITS2 (Z_to_bv 64 BITS).
Lemma E1s_agree : env_agree 52 E E1s.
Proof. unfold E1s. eapply env_agree_trans; [exact E1c_agree | eapply env_agree_le; [| apply env_agree_ewset]; unfold aBITS2; lia]. Qed.
Lemma HA1s : env_agree 40 E00 E1s.
Proof. eapply env_agree_trans; [exact HA | eapply env_agree_le; [| exact E1s_agree]; lia]. Qed.
Lemma E1s_vals : ew E1s aG2 = Z_to_bv 64 G2 /\ ew E1s aAI2 = Z_to_bv 64 aib /\ ew E1s 48 = Z_to_bv 64 M2 /\ ew E1s 51 = Z_to_bv 64 (sx32 (am_freed am2)) /\
ew E1s aBITS2 = Z_to_bv 64 BITS /\ ew E1s 36 = Z_to_bv 64 (SCT + 2 * sc) /\ ew E1s 35 = Z_to_bv 64 scl /\ ew E1s aNX2 = Z_to_bv 64 NX2.
Proof.
destruct E1c_vals as (V52 & V53 & V54 & V48 & V51). pose proof (agree_facts E1s HA1s) as (_ & _ & _ & _ & E36 & E35).
unfold E1s, aBITS2, aG2, aAI2, aNX2 in *. rewrite !ew_ewset_other by lia. rewrite ew_ewset_same. repeat split; assumption.
Qed.
Lemma span_facts :
am_sc am2 = sc /\ 1 <= sc < 48 /\ 0 <= aidx < last /\ last <= 31 /\ size = 16 * scl /\ 1 <= scl <= 8191 /\ 32 <= size /\
span_stops 299 span0 size = true /\ span0 + size * (299 + 2) < 2 ^ 31 /\ 48 <= span0 /\
aidx + 2 <= CNT <= aidx + 2 + 299 /\ span_cnt am2 = span_clamp CNT last /\ aidx + 2 <= span_cnt am2 <= last + 1 /\
BITS = bits_enc last sc (am_maplen am2) /\ 0 <= am_maplen am2 /\ 0 <= BITS < 2 ^ 64.
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2].
pose proof (grp2 X U A sc Hsc s2 m2 am2 B2) as (G1 & G2' & G3 & G4 & G5). specialize (G5 Ec).
pose proof (cs_facts X U L A regs mem md sc HI Hsc MID g 0 M0) as (_ & _ & _ & C35 & _ & _ & _ & Csz). cbn [cs] in C35, Csz.
pose proof (metaS None s2 (ms_mem ms) HI2 RX2 MID2 m2 am2 Hu2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hml & Hbits).
assert (Hsc0 : sc <> 0) by (rewrite <- Hs2; exact (SP2 SPOK m2 am2 (proj1 (usedX_MT _ _ _ _ Hu2)) G5)).
pose proof (span_entry_facts sc aidx ltac:(lia) ltac:(unfold aidx; lia)) as [ST OV]. fold size in ST, OV. fold span0 in ST, OV.
pose proof (span_loop_bounds 299 (aidx + 2) span0 size) as CB. fold CNT in CB.
pose proof (span_cnt_range X U A sc Hsc s2 m2 am2 B2 Ec) as SCR.
assert (Esz : size = 16 * scl) by (unfold size, scl; exact Csz).
assert (ECNT : span_cnt am2 = span_clamp CNT last).
{ unfold span_cnt. cbv zeta. rewrite Hs2.
change (span_loop 300 (am_aidx am2 + 2) (UNIT + class_size sc * (am_aidx am2 + 2)) (class_size sc)) with (span_loop 300 (aidx + 2) span0 size).
rewrite (span_loop_fuel 299 (aidx + 2) span0 size ST). fold CNT. unfold span_clamp, last.
destruct (Z.ltb_spec (am_last am2 + 1) CNT); destruct (Z.ltb_spec CNT (am_last am2 + 1)); lia. }
pose proof (class_size_pos_ge32 sc Hsc Hsc0) as S32. fold size in S32.
assert (S48 : 48 <= span0) by (unfold span0, aidx, UNIT; nia).
assert (EB : BITS = bits_enc (am_last am2) sc (am_maplen am2)) by (unfold BITS; rewrite <- Hs2; apply meta_bits_enc).
assert (Hml52 : am_maplen am2 < 2 ^ 52).
{ pose proof (inv_groups HI2 m2 am2 Hu2) as (_ & _ & _ & _ & Gmp & _).
destruct (Z_lt_dec 0 (am_maplen am2)) as [Hpos|]; [|lia].
destruct (Gmp Hpos) as (r & rg' & Em' & Hr' & _ & Hl' & Hlen' & _).
destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID2) _ _ Hr' Hl') as (_ & A1 & A2 & _). pose proof (proj1 alloc_ceiling_val). unfold PGSZ in Hlen'. lia. }
pose proof (bits_lt64 (am_last am2) sc (am_maplen am2) ltac:(lia) ltac:(lia) ltac:(lia) Hml52) as BL. pose proof (bits_nonneg (am_last am2) sc (am_maplen am2) ltac:(lia) ltac:(lia) ltac:(lia)) as BN.
rewrite <- EB in BL, BN.
unfold aidx, last, scl in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
Qed.
Lemma m2_factsS :
bytes_are (ms_mem ms) (M2 + 8) 8 M2 /\ bytes_are (ms_mem ms) (M2 + 32) 8 BITS /\
bytes_are (ms_mem ms) (SCT + 2 * sc) 2 scl /\ nx2 = m2 /\ NX2 = M2.
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2].
pose proof (metaS None s2 (ms_mem ms) HI2 RX2 MID2 m2 am2 Hu2) as (_ & _ & _ & _ & _ & _ & B8 & _ & _ & _ & B32 & _).
rewrite Hnx in B8. cbn [optrZ] in B8.
assert (Enx : nx2 = m2) by (unfold nx2; rewrite Hnx; reflexivity).
assert (Escl : scl_of sc = znth sc size_classes) by (unfold scl_of; replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
split; [exact B8|]. split; [exact B32|]. split; [| split; [exact Enx | unfold NX2; rewrite Enx; reflexivity]].
unfold scl. rewrite Escl. apply (YN1y.sct_bytes (ms_mem ms) (STs s2 (ms_mem ms) MID2) sc). lia.
Qed.
Lemma valsS :
sv_denot E1s (SOff 48 0) = Z_to_bv 64 M2 /\ sv_denot E1s (SOff aG2 0) = Z_to_bv 64 G2 /\ sv_denot E1s (SOff aAI2 0) = Z_to_bv 64 aib /\
sv_denot E1s (SOff aBITS2 0) = Z_to_bv 64 BITS /\ sv_denot E1s (SOff 35 0) = Z_to_bv 64 scl /\ sv_denot E1s (SOff 36 0) = Z_to_bv 64 (SCT + 2 * sc) /\
base_val E1s (Some 48%nat) = M2 /\ base_val E1s (Some aG2) = G2 /\ base_val E1s (Some 36%nat) = SCT + 2 * sc /\
sv_denot E1s MA2 = sv_denot E1c MA2.
Proof.
pose proof m2_factsC as (A1 & A2 & _ & _ & _ & _ & _ & _ & Fr & Hai & Hl & _ & _ & _ & _ & _ & _ & G1 & G2' & _ & _ & _ & _ & Hbm & Hb8 & _). pose proof (proj1 alloc_ceiling_val).
pose proof span_facts as (_ & Hsc1 & _ & _ & _ & Hscl & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB).
destruct E1s_vals as (V52 & V53 & V48 & V51 & V55 & V36 & V35 & V54). pose proof statics_layout as SL.
assert (HSCT : 0 <= SCT + 2 * sc < 2 ^ 64) by (unfold SCT, src0_D_size_classes; lia).
repeat match goal with |- _ /\ _ => split end;
try (apply den_atom0; [assumption | lia]); try (apply base_atom; [assumption | lia]).
unfold E1s. apply sv_denot_ewset_free. reflexivity.
Qed.
Lemma S_st_ok : st_ok src0segs E1s ss_S ms.
Proof.
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof m2_factsC as (A1 & A2 & A8 & Aimg & Apres & _ & B16 & B24 & Fr & Hai & Hl & _ & _ & _ & _ & _ & _ & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & _ & AP2 & _).
pose proof m2_factsS as (B8 & B32 & Bsct & Enx & ENX).
pose proof span_facts as (_ & Hsc1 & _ & _ & _ & Hscl & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB).
destruct E1s_vals as (V52 & V53 & V48 & V51 & V55 & V36 & V35 & V54). pose proof valsS as (W48 & W52 & W53 & W55 & W35 & W36 & X48 & X52 & X36 & WMA).
pose proof valsC as (Wma & _).
pose proof (st_ok_agree src0segs 52 E E1s ss_gamma ms HS E1s_agree ss_gamma_atoms) as HS1.
pose proof stations_shape as (_ & Mg & _ & _ & Fg & _).
pose proof B2 as [HI2 Hhd2 _ _ _ _ _ _ _ _].
pose proof (headS None s2 (ms_mem ms) HI2 RX2 MID2) as HD. rewrite Hhd2 in HD. cbn [optrZ] in HD.
pose proof (base_mem_ok E1s ss_gamma ms (SOff 48 0) HS1 Mg HA1s ltac:(rewrite W48, lit64_small by lia; exact HD)) as BASE.
destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (Sat & Scd & Sal)). rewrite Fg in Sat.
pose proof (agree_facts E1s HA1s) as (_ & _ & B33 & B2' & _). pose proof statics_layout as SL. pose proof pre_factsS as (_ & _ & P3 & _).
assert (HSCT : 0x10000 <= SCT /\ SCT + 96 <= 0x51000) by (unfold SCT, src0_D_size_classes; lia).
assert (BD : forall r' lo hi, In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> 4096 <= lo -> hi <= alloc_ceiling -> (hi <= 0x10000 \/ 0x51000 <= lo) -> hi <= base_val E1s (r_base r') + r_lo r' \/ base_val E1s (r_base r') + r_hi r' <= lo).
{ intros r' lo hi Hr'. apply (base_disjoint E1s r' lo hi HA1s). destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]. }
assert (Dm2 : forall r', In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1s R_m2S r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m2S]. rewrite X48. destruct (BD r' M2 (M2 + 40) Hr' ltac:(lia) ltac:(lia) Aimg); lia. }
assert (Dg2 : forall r', In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1s (R_g2w (SOff aAI2 0)) r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_g2w]. rewrite X52. destruct (BD r' G2 (G2 + 16) Hr' ltac:(lia) ltac:(lia) Gimg); lia. }
assert (Dsct : forall r', In r' (R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1s R_sct r').
{ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_sct]. rewrite X36. destruct Hr' as [<-|Hr'].
- cbn [r_base r_lo r_hi R_actW]. rewrite B33. unfold YN0j.LOCK, SCT, src0_D_malloc_lock, src0_D_size_classes in *. lia.
- pose proof (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hr') as Hin'. rewrite MEM0_skel in Hin'. cbn [In] in Hin'.
decompose [or] Hin'; try contradiction; match goal with H : _ = (r_base r', _, _, _, _) |- _ => injection H as Eb El Eh _ _ end; rewrite <- El, <- Eh, <- Eb; rewrite ?B2'; cbn [base_val];
unfold GOT, GUARD, LIBC, SCT, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_libc, src0_D_size_classes, ASF in *; try lia. }
unfold st_ok, ss_S, MEM_S. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact S1|]. split; [rewrite S2, ss_gamma_pc; reflexivity|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6|]. split; [exact S7|]. split.
- cbn [app]. apply mem_ok_cons'; [reflexivity | | | apply mem_ok_cons'; [reflexivity | | | apply mem_ok_cons'; [reflexivity | | exact Dsct | exact BASE]]].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m2S]; rewrite X48; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
* apply (chunk_ok_val' E1s _ _ _ 8 _ M2); [rewrite W48; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B8].
* apply (chunk_ok_val' E1s _ _ _ 8 _ G2); [rewrite W52; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B16].
* apply (chunk_ok_val' E1s _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B24].
* apply (chunk_ok_val' E1s _ _ _ 8 _ BITS); [rewrite W55; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B32].
+ intros r' [<-|[<-|Hr']]; [| | exact (Dm2 r' Hr')]; unfold extent_disjoint; cbn [r_base r_lo r_hi R_m2S R_g2w R_sct]; rewrite X48, ?X52, ?X36; [lia|].
unfold SCT, src0_D_size_classes in *. lia.
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_g2w]; rewrite X52; [lia | lia | intros o Ho; apply present_writable; apply Gpres; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1s _ _ _ 1 _ aib); [rewrite W53; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
intros kk Hkk. replace kk with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256. rewrite (Z.mod_small aib 256), Z.mod_small by lia. reflexivity.
+ intros r' [<-|Hr']; [| exact (Dg2 r' Hr')]. unfold extent_disjoint; cbn [r_base r_lo r_hi R_g2w R_sct]; rewrite X52, X36. unfold SCT, src0_D_size_classes in *. lia.
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_sct]; rewrite X36; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val' E1s _ _ _ 2 _ scl); [rewrite W35; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | rewrite Z.add_0_r; exact Bsct].
- unfold facts_ok, s_atoms, c_atoms. cbn [f_atoms f_conds f_alias app atoms_ok conds_ok alias_ok]. split; [|split].
+ unfold FM, F_sct, F_sz, afact_ok; cbn [af_lo af_hi af_al2].
rewrite V48, V51, V52, V53, V54, V55, V36, V35, !lit64_small by (try apply sx32_range; unfold NX2 in *; try lia).
change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. pose proof (sx32_range (am_freed am2)).
pose proof m2_factsC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & C8 & _).
assert (SCT mod 2 = 0) by (unfold SCT, src0_D_size_classes; reflexivity).
repeat (split; [first [lia | split; [lia|]; split; [|lia]; rewrite Z.mul_comm, Z_mod_plus_full; assumption] |]). exact Sat.
+ split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b C_c12]. rewrite branch_eq, WMA, Wma. cbn [sv_denot]. rewrite (lit64_small 0) by lia. rewrite Z.land_comm, Ec. reflexivity.
+ split; [|exact I]. apply word_eq. cbv delta [ADDRSCT2]. cbn [sv_denot]. rewrite alu64_add, alu64_and, alu64_srl, !Z.add_0_r, !Z_to_bv_bv_unsigned, V55, V36.
pose proof span_facts as (_ & _ & _ & Hl31 & _ & _ & _ & _ & _ & _ & _ & _ & _ & EB & Hml & _).
rewrite (lit64_small BITS), (lit64_small SCT), (lit64_small 5), (lit64_small 126), (lit64_small (SCT + 2 * sc)) by (unfold SCT, src0_D_size_classes; lia).
change (5 mod 64) with 5. rewrite EB. rewrite (bits_2sc last sc (am_maplen am2)) by (unfold last in *; lia). unfold add64. rewrite Z.mod_small by (unfold SCT, src0_D_size_classes; lia). reflexivity.
Qed.
Lemma Sa_run :
SR src0segs (mkCfg ms md) (fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E1s SS_Sa ms1 /\ frame_of E1s (ss_mem ss_S) (ms_mem ms) (ms_mem ms1)).
Proof.
pose proof md_factsS as (Mh & Mlz & _).
eapply SR_mono; [eapply (SR_run_to PS_L); [exact S_st_ok | exact Sa_run_ok | exact Mh | exact Mlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
rewrite <- SS_Sa_eq. unfold closeF. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ S_st_ok)].
Qed.
Lemma land31 a : 0 <= a -> Z.land a 31 = a mod 32.
Proof. intros Ha. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma loop_regs ms1 : st_ok src0segs E1s SS_Sa ms1 ->
getr (ms_regs ms1) 5 = Z_to_bv 64 span0 /\ getr (ms_regs ms1) 16 = Z_to_bv 64 (span0 + size - 1) /\ getr (ms_regs ms1) 14 = Z_to_bv 64 (aidx + 2 - 1) /\
getr (ms_regs ms1) 15 = Z_to_bv 64 size /\ getr (ms_regs ms1) 17 = Z_to_bv 64 4096 /\
getr (ms_regs ms1) 13 = Z_to_bv 64 BITS /\ getr (ms_regs ms1) 12 = Z_to_bv 64 aib /\
ms1 = mkst (ms_regs ms1) (Z_to_bv 64 PS_L) (ms_mem ms1) (seg_rom src0segs).
Proof.
intros HS1. pose proof SS_Sa_shape as (Hpc & Hrv & _ & _ & Q5 & Q16 & Q14 & Q15 & Q17 & Q13 & Q12 & Q11 & Q10 & _).
pose proof span_facts as (_ & Hsc1 & Ha & Hl & Esz & Hscl & S32 & _ & OV & S48 & _ & _ & _ & _ & _ & HB).
pose proof m2_factsC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbm & Hb8 & _).
destruct E1s_vals as (V52 & V53 & V48 & V51 & V55 & V36 & V35 & V54). pose proof valsS as (W48 & W52 & W53 & W55 & W35 & _).
assert (Haidx : Z.land aib 31 = aidx) by (rewrite land31 by lia; unfold aidx; exact Hbm).
assert (Hsll : sll64 scl 4 = size) by (unfold sll64; rewrite Z.shiftl_mul_pow2, Z.mod_small by lia; lia).
assert (Hsll2 : sll64 aidx 4 = 16 * aidx) by (unfold sll64; rewrite Z.shiftl_mul_pow2, Z.mod_small by lia; lia).
assert (M1 : 0 <= size * (aidx + 2) < 2 ^ 31) by (unfold span0, UNIT in *; nia).
assert (M2' : 0 <= (16 * aidx + 48) * scl < 2 ^ 31) by (unfold span0, UNIT in *; nia).
repeat match goal with |- _ /\ _ => split end; rewrite ?(st_ok_reg src0segs E1s SS_Sa ms1 _ HS1), ?Q5, ?Q16, ?Q14, ?Q15, ?Q17, ?Q13, ?Q12.
- apply word_eq. cbv delta [SPAN0 SIZE AIDX]. cbn [sv_denot]. rewrite addw_rr_unsigned, mul64_unsigned, alu64_sll, alu64_add, alu64_and, !Z.add_0_r, !Z_to_bv_bv_unsigned, V35, V53.
rewrite (lit64_small scl), (lit64_small 4), (lit64_small aib), (lit64_small 31), (lit64_small 2), (lit64_small 16), (lit64_small span0) by lia.
change (4 mod 64) with 4. rewrite Hsll, Haidx. unfold add64, mul64. rewrite (Z.mod_small (aidx + 2)), Z.mod_small by lia. rewrite addw_small by lia. unfold span0, UNIT. lia.
- apply word_eq. cbv delta [SEND0 AIDX]. cbn [sv_denot]. rewrite addw_rr_unsigned, mul64_unsigned, alu64_add, alu64_sll, alu64_and, !Z.add_0_r, !Z_to_bv_bv_unsigned, V35, V53.
rewrite (lit64_small scl), (lit64_small 4), (lit64_small aib), (lit64_small 31), (lit64_small 48), (lit64_small 15), (lit64_small (span0 + size - 1)) by lia.
change (4 mod 64) with 4. rewrite Haidx, Hsll2. unfold add64, mul64. rewrite (Z.mod_small (16 * aidx + 48)), Z.mod_small by lia. rewrite addw_small by lia. unfold span0, UNIT. lia.
- apply word_eq. cbv delta [AIDX]. cbn [sv_denot]. rewrite alu64_add, alu64_and, !Z.add_0_r, !Z_to_bv_bv_unsigned, V53.
rewrite (lit64_small aib), (lit64_small 31), (lit64_small 1), (lit64_small (aidx + 2 - 1)) by lia. rewrite Haidx. unfold add64. rewrite Z.mod_small by lia. lia.
- apply word_eq. cbv delta [SIZE]. cbn [sv_denot]. rewrite alu64_sll, !Z.add_0_r, !Z_to_bv_bv_unsigned, V35. rewrite (lit64_small scl), (lit64_small 4), (lit64_small size) by lia. change (4 mod 64) with 4. exact Hsll.
- reflexivity.
- exact W55.
- exact W53.
- rewrite <- Hpc. exact (YN1d.st_ok_mkst E1s SS_Sa ms1 HS1 Hrv).
Qed.
Lemma reg_in_cons_false (r x : reg) l : reg_in r (x :: l) = false -> r <> x /\ reg_in r l = false.
Proof. cbn. intros H. apply orb_false_iff in H as [H1 H2]. split; [| exact H2]. intros ->. rewrite bv_eqb_refl in H1. discriminate. Qed.
Definition E2_of (rg : bvmap 5 word) : env :=
ewset (ewset (ewset (ewset (ewset (ewset E1s aT1 (getr rg 6)) aT0 (getr rg 5)) aA4 (getr rg 14)) aA6 (getr rg 16)) aA3 (getr rg 13)) aNB (Z_to_bv 64 NB).
Lemma E2_agree rg : env_agree 56 E1s (E2_of rg).
Proof.
unfold E2_of, aT1, aT0, aA4, aA6, aA3, aNB.
repeat (eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; lia]). apply env_agree_refl.
Qed.
Lemma E2_vals rg : ew (E2_of rg) aT1 = getr rg 6 /\ ew (E2_of rg) aT0 = getr rg 5 /\ ew (E2_of rg) aA4 = getr rg 14 /\ ew (E2_of rg) aA6 = getr rg 16 /\
ew (E2_of rg) aA3 = getr rg 13 /\ ew (E2_of rg) aNB = Z_to_bv 64 NB /\ ew (E2_of rg) 48 = Z_to_bv 64 M2 /\ ew (E2_of rg) aG2 = Z_to_bv 64 G2.
Proof.
destruct E1s_vals as (V52 & V53 & V48 & _). unfold E2_of, aT1, aT0, aA4, aA6, aA3, aNB, aG2 in *.
repeat split; rewrite ?ew_ewset_same; try reflexivity; rewrite !ew_ewset_other by lia; rewrite ?ew_ewset_same; try reflexivity; assumption.
Qed.
Lemma land224 a : 0 <= a -> Z.land a 224 = 32 * (Z.shiftr a 5 mod 8).
Proof. intros Ha. change 224 with (2 ^ 5 * Z.ones 3). rewrite land_field by lia. reflexivity. Qed.
Lemma NB_range : 0 <= NB < 256 /\ NB mod 32 = span_cnt am2 - 1 /\ NB = (span_cnt am2 - 1) + Z.land aib 224.
Proof.
pose proof span_facts as (_ & _ & Ha & Hl & _ & _ & _ & _ & _ & _ & HC & ECNT & SCR & _).
pose proof m2_factsC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbm & Hb8 & _).
unfold NB, span_byte. rewrite <- ECNT.
assert (L1 : Z.land (span_cnt am2 - 1) 31 = span_cnt am2 - 1) by (rewrite land31 by lia; apply Z.mod_small; unfold last in *; lia).
rewrite L1, land224 by lia. pose proof (Z.mod_pos_bound (Z.shiftr aib 5) 8 ltac:(lia)) as M8.
assert (OR : Z.lor (span_cnt am2 - 1) (32 * (Z.shiftr aib 5 mod 8)) = (span_cnt am2 - 1) + 32 * (Z.shiftr aib 5 mod 8)).
{ change 32 with (2 ^ 5). apply lor_add_high; unfold last in *; lia. }
rewrite OR. split; [unfold last in *; lia|]. split; [|reflexivity].
rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. unfold last in *. lia.
Qed.
Lemma span_stretch ms1 : st_ok src0segs E1s SS_Sa ms1 ->
exists rg2, msteps src0segs ms1 (mkst rg2 (Z_to_bv 64 PS_S) (ms_mem ms1) (seg_rom src0segs)) /\
getr rg2 12 = Z_to_bv 64 NB /\
(forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 16%bv -> getr rg2 r = getr (ms_regs ms1) r).
Proof.
intros HS1. pose proof (loop_regs ms1 HS1) as (G5 & G16 & G14 & G15 & G17 & G13 & G12 & Ems).
pose proof span_facts as (_ & Hsc1 & Ha & Hl & Esz & Hscl & S32 & ST & OV & S48 & HC & ECNT & SCR & EB & Hml & HB).
pose proof m2_factsC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbm & Hb8 & _).
destruct (span_loop_steps (ms_mem ms1) (seg_rom src0segs) size ltac:(lia) 299 (ms_regs ms1) (aidx + 2) span0 ST ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G5 G16 G14 G15 G17)
as (rg1 & MS1 & P14 & P15 & P17 & Pfr). fold CNT in P14.
destruct (span_tail_steps (ms_mem ms1) (seg_rom src0segs) rg1 CNT BITS aib P14
ltac:(rewrite (Pfr 13%bv) by reg_neq_tac; exact G13) ltac:(rewrite (Pfr 12%bv) by reg_neq_tac; exact G12) HB ltac:(lia) ltac:(lia))
as (rg2 & MS2 & P12 & Qfr).
exists rg2. split; [| split].
- rewrite Ems at 1. eapply msteps_trans; [exact MS1 | exact MS2].
- rewrite P12. unfold NB. rewrite EB, (bits_land31 last sc (am_maplen am2)) by (unfold last in *; lia). reflexivity.
- intros r H5 H6 H12 H13 H14 H16. rewrite (Qfr r H12 H13 H14). apply Pfr; assumption.
Qed.
Lemma Sc_st_ok ms1 rg2 : st_ok src0segs E1s SS_Sa ms1 ->
getr rg2 12 = Z_to_bv 64 NB ->
(forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 16%bv -> getr rg2 r = getr (ms_regs ms1) r) ->
st_ok src0segs (E2_of rg2) ss_Sc (mkst rg2 (Z_to_bv 64 PS_S) (ms_mem ms1) (seg_rom src0segs)).
Proof.
intros HS1 G12 Gfr. pose proof (loop_regs ms1 HS1) as (_ & _ & _ & _ & _ & _ & _ & Ems). pose proof SS_Sa_shape as (Hpc & Hrv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hat).
pose proof NB_range as (NB1 & _). destruct (E2_vals rg2) as (X1 & X2 & X3 & X4 & X5 & X6 & _).
rewrite <- ss_Sc_eq. apply st_ok_add_fact.
- rewrite Ems in HS1. apply (st_ok_set_regs src0segs 56 E1s (E2_of rg2) SS_Sa (ms_regs ms1) rg2 _ PS_S (ms_mem ms1) updS HS1 (E2_agree rg2) Hat Hrv eq_refl).
+ intros r Hr. unfold updS in Hr. cbn [map fst] in Hr.
apply reg_in_cons_false in Hr as [N6 Hr]. apply reg_in_cons_false in Hr as [N5 Hr]. apply reg_in_cons_false in Hr as [N14 Hr].
apply reg_in_cons_false in Hr as [N16 Hr]. apply reg_in_cons_false in Hr as [N13 Hr]. apply reg_in_cons_false in Hr as [N12 _].
apply Gfr; assumption.
+ unfold updS. repeat (apply Forall_cons; [split; [reflexivity | cbn [fst snd sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; first [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | rewrite X6; symmetry; exact G12] ] |]). apply Forall_nil.
- unfold afact_ok, F_nb. cbn [af_lo af_hi af_al2]. rewrite X6, lit64_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Lemma Sc_run ms2 : st_ok src0segs (E2_of (ms_regs ms2)) ss_Sc ms2 ->
SR src0segs (mkCfg ms2 md) (fun c' => exists ms3, c' = mkCfg ms3 md /\ st_ok src0segs (E2_of (ms_regs ms2)) SS_Sc ms3 /\ frame_of (E2_of (ms_regs ms2)) (ss_mem ss_Sc) (ms_mem ms2) (ms_mem ms3)).
Proof.
intros HS2. pose proof md_factsS as (Mh & Mlz & _).
eapply SR_mono; [eapply (SR_run_to PS_D); [exact HS2 | exact Sc_run_ok | exact Mh | exact Mlz]|].
intros c' (ms3 & -> & HS3 & HF). exists ms3. split; [reflexivity|]. split; [|exact HF].
rewrite <- SS_Sc_eq. unfold closeF. apply st_ok_refacts; [exact HS3 | exact (st_ok_facts_ok _ _ _ _ HS2)].
Qed.
Definition C2_end (ms3 : machine_state) : Prop :=
exists rg2, st_ok src0segs (E2_of rg2) SS_Sc ms3 /\
(forall x, 0 <= x < 2 ^ 64 -> x <> G2 + 8 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ WS regs x ->
(ms_mem ms3) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x)).
Lemma wr_S E0 b x : env_agree 40 E00 E0 -> ew E0 aG2 = Z_to_bv 64 G2 -> in_wrange E0 (MEM_S b) x ->
x = G2 + 8 \/ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) \/ WS regs x.
Proof.
intros HA0 HG Hw. pose proof m2_factsC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2' & _). pose proof (proj1 alloc_ceiling_val).
unfold MEM_S in Hw. destruct (wrange_cases E0 [R_m2S; R_g2w b; R_sct] _ x HA0 Hw) as [(r & Hin & Hr)|[Hh|Hs']]; [| right; left; exact Hh | right; right; exact Hs'].
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [r_base r_wlo r_whi R_m2S R_g2w R_sct] in Hr; try lia.
rewrite (base_atom E0 aG2 G2 HG) in Hr by lia. left. lia.
Qed.
Theorem C2_run : SR src0segs (mkCfg ms md) (fun c' => exists ms3, c' = mkCfg ms3 md /\ C2_end ms3).
Proof.
pose proof md_factsS as (Mh & Mlz & _). destruct E1s_vals as (V52 & _).
eapply SR_bind; [exact Sa_run|]. intros c1 (ms1 & -> & HS1 & HF1).
destruct (span_stretch ms1 HS1) as (rg2 & MS & G12 & Gfr).
pose proof (Sc_st_ok ms1 rg2 HS1 G12 Gfr) as HS2.
eapply (SR_msteps src0segs ms1 _ md _ Mh Mlz MS).
set (ms2 := mkst rg2 (Z_to_bv 64 PS_S) (ms_mem ms1) (seg_rom src0segs)) in *.
change rg2 with (ms_regs ms2) in HS2.
eapply SR_mono; [exact (Sc_run ms2 HS2)|]. intros c3 (ms3 & -> & HS3 & HF3).
exists ms3. split; [reflexivity|]. exists (ms_regs ms2). split; [exact HS3|].
intros x Hx N1 N2 N3. pose proof (E2_vals (ms_regs ms2)) as (_ & _ & _ & _ & _ & _ & _ & X8).
assert (HA2 : env_agree 40 E00 (E2_of (ms_regs ms2))) by (eapply env_agree_trans; [exact HA1s | eapply env_agree_le; [| apply E2_agree]; lia]).
transitivity ((ms_mem ms2) (Z_to_bv 64 x)).
- apply (HF3 (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw. pose proof (proj1 ss_Sc_shape) as Em. rewrite Em in Hw.
destruct (wr_S _ _ x HA2 X8 Hw) as [H|[H|H]]; [exact (N1 H) | exact (N2 H) | exact (N3 H)].
- change (ms_mem ms2) with (ms_mem ms1). apply (HF1 (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw. unfold ss_S in Hw. cbn [ss_mem] in Hw.
destruct (wr_S _ _ x HA1s V52 Hw) as [H|[H|H]]; [exact (N1 H) | exact (N2 H) | exact (N3 H)].
Qed.
Definition s3S : astate := sC2 s2 m2 am2.
Lemma s3_eq : s3S = upd_meta m2 (MUsed am2') s2. Proof. reflexivity. Qed.
Lemma bnd3S : bnd X U A sc s3S m2 am2' /\ Z.land (am_freed am2') (ones (am_aidx am2')) <> 0.
Proof.
destruct (bnd_C X U A sc Hsc s2 m2 am2 B2 m2 s3S (selC_2 sc s2 m2 am2 Ec Hnx)) as (am3 & B3 & Hm3).
pose proof (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B3))) as M3. unfold s3S, sC2 in M3. rewrite MT_upd_same in M3. injection M3 as E3.
fold am2' in E3. subst am3. split; [exact B3 | exact Hm3].
Qed.
Lemma s3_factsS : sameX A s3S /\ sameX s2 s3S /\ rawX X s3S /\ user_blocks s3S = user_blocks s2 /\ tail_cells s3S = tail_cells s2 /\
active_hd s3S sc = Some m2 /\ length (st_active s3S) = 48%nat /\ MT s2 m2 = Some (MUsed am2) /\ MT s3S m2 = Some (MUsed am2') /\
footprint s3S = footprint s2 /\ st_regions s3S = st_regions s2.
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof (proj1 (inv_ctx HI2)) as Hlen. pose proof (usedX_MT _ _ _ _ Hu2) as [M2e NX].
pose proof (proj1 bnd3S) as [HI3 Hhd3 Hu3 _ _ _ _ UB3 SX3 _].
assert (S23 : sameX s2 s3S) by (unfold s3S, sC2; apply (sameX_upd_meta _ _ am2); exact M2e).
split; [exact SX3|]. split; [exact S23|]. split.
{ intros x Hx. unfold s3S, sC2. rewrite MT_upd_other; [exact (RX2 x Hx)|]. intros ->. apply (proj2 (memb_In m2 X)) in Hx. rewrite Hx in NX. discriminate. }
split; [apply ub_same_user_blocks; [exact (proj1 (inv_keys HI2)) | exact (proj1 (inv_keys HI3)) |]; unfold s3S, sC2; apply ub_same_upd_In; [eapply MT_Some_In_keys; exact M2e | rewrite M2e; cbn; apply blocks_of_aidx]|].
split; [unfold s3S, sC2; apply (tail_cells_set_aidx s2 m2 am2); exact M2e|].
split; [exact Hhd3|]. split; [unfold s3S, sC2; cbn; exact Hlen|]. split; [exact M2e|]. split; [unfold s3S, sC2; apply MT_upd_same|].
split; [unfold s3S, sC2; apply footprint_upd_meta | reflexivity].
Qed.
Section h0.
Variables (ms3 : machine_state) (rg2 : bvmap 5 word).
Hypothesis HS3 : st_ok src0segs (E2_of rg2) SS_Sc ms3.
Hypothesis OUT : forall x, 0 <= x < 2 ^ 64 -> x <> G2 + 8 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ WS regs x ->
(ms_mem ms3) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x).
Let E2 := E2_of rg2.
Lemma postC2_regs : getr (ms_regs ms3) 10 = Z_to_bv 64 M2 /\ ms_pc_val ms3 = Z_to_bv 64 PS_D.
Proof.
destruct (E2_vals rg2) as (_ & _ & _ & _ & _ & _ & X48 & _). pose proof m2_factsC as (A1 & A2 & _). pose proof (proj1 alloc_ceiling_val).
pose proof (st_ok_reg src0segs E2 SS_Sc ms3 10 HS3) as R. destruct HS3 as (_ & SPC & _).
pose proof SS_Sc_shape as (_ & E10 & Epc). rewrite E10 in R. rewrite R, SPC, Epc. split; [| reflexivity]. apply (den_atom0 E2 48 _ X48). lia.
Qed.
Lemma postC2_mem :
bytes_are (ms_mem ms3) (YN0j.CTX + 80 + 8 * sc) 8 M2 /\ mbyte src0segs (ms_mem ms3) (G2 + 8) = Some (Z_to_bv 8 NB) /\ writable_at src0segs (ms_mem ms3) (G2 + 8).
Proof.
destruct (E2_vals rg2) as (_ & _ & _ & _ & _ & X61 & X48 & X52). fold E2 in X61, X48, X52.
assert (HA2 : env_agree 40 E00 E2) by (eapply env_agree_trans; [exact HA1s | eapply env_agree_le; [| apply E2_agree]; lia]).
pose proof (agree_facts E2 HA2) as (_ & _ & B33 & _). pose proof m2_factsC as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2' & _). pose proof (proj1 alloc_ceiling_val).
pose proof NB_range as (NB1 & _).
pose proof (st_ok_mem_ok src0segs E2 SS_Sc ms3 HS3) as (_ & MOK & _). rewrite (proj1 SS_Sc_shape) in MOK. unfold MEM_S in MOK. cbn [app] in MOK.
split.
- pose proof (proj1 (Forall_forall _ _) MOK (R_actW (SOff 48 0)) ltac:(cbn; auto 10)) as (_ & _ & _ & CHm). cbn [r_chunks r_base R_actW] in CHm.
pose proof (Forall_inv CHm) as C0. rewrite B33 in C0.
replace (YN0j.CTX + 80 + 8 * sc) with (YN0j.LOCK + 8 * sc + 88) by (pose proof CTX_eq; lia).
rewrite <- (Z.mod_small M2 (2 ^ (8 * Z.of_N 8))) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
apply (chunk_bytes' E2 _ _ _ 8 (SOff 48 0)); [exact C0 | rewrite (den_atom0 E2 48 _ X48) by lia; apply lit64_small; lia].
- pose proof (proj1 (Forall_forall _ _) MOK (R_g2w (SOff aNB 0)) ltac:(cbn; auto 10)) as (_ & _ & WRg & CHg). cbn [r_chunks r_base r_wlo r_whi R_g2w] in CHg, WRg.
rewrite (base_atom E2 aG2 G2 X52) in WRg by lia. split; [| apply (WRg 8); lia].
pose proof (Forall_inv CHg) as C0. rewrite (base_atom E2 aG2 G2 X52) in C0 by lia.
pose proof (chunk_bytes' E2 _ _ _ 1 (SOff aNB 0) NB C0 ltac:(rewrite (den_atom0 E2 aNB _ X61) by lia; apply lit64_small; lia)) as BY.
specialize (BY 0%nat ltac:(lia)). cbn [Z.of_nat] in BY. rewrite Z.add_0_r in BY. rewrite BY. f_equal. f_equal. apply le_byte1_small. lia.
Qed.
Lemma postC2_memrep : memrepX B X L s3S (ms_mem ms3).
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof (proj1 bnd3S) as [HI3 Hhd3 Hu3 _ _ _ _ _ SX3 _].
pose proof s3_factsS as (_ & S23 & RX3 & UBe & TCe & Hhd3' & Hlen3 & M2e & M3e & Efp & Erg). pose proof (proj1 (inv_ctx HI2)) as Hlen2.
pose proof postC2_mem as (HB & HNB & HWg). pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val). pose proof NB_range as (NB1 & NB32 & NBeq).
pose proof m2_factsC as (A1 & A2 & A8 & Aimg & Apres & _ & B16 & B24 & Fr & Hai & Hl & _ & _ & _ & _ & _ & _ & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & _).
pose proof span_facts as (_ & _ & Ha & Hla & _ & _ & _ & _ & _ & _ & _ & _ & SCR & _).
pose proof (HLs s2 (ms_mem ms) MID2) as HL2.
assert (HL3 : layout_ok L s3S) by (apply (layout_ok_same' L s2 s3S HL2 Erg Efp)).
assert (Emem : am_mem am2' = am_mem am2) by reflexivity. assert (Eml : am_maplen am2' = am_maplen am2) by reflexivity.
assert (Eai : am_aidx am2' = span_cnt am2 - 1) by reflexivity.
assert (KEEP : forall k, 0 <= k < 4 -> k <> 0 -> mbyte src0segs (ms_mem ms3) (G2 + 8 + k) = mbyte src0segs (ms_mem ms) (G2 + 8 + k)).
{ intros k Hk Hk0. apply mbyte_ext1. apply OUT; [lia | lia | | unfold WS; fold sp; pose proof Hstk; unfold ASF in *; lia].
intros W. pose proof statics_layout as SL. unfold YN0j.CTX, src0_D_malloc_context in *. destruct Gimg; lia. }
assert (HcIn : In (hcell (Some m2)) (ctx_cells s3S)) by (rewrite <- Hhd3'; apply hcell_In; exact Hlen3).
refine (memrepX_after_cells B X X None U s2 s3S L (ms_mem ms) (ms_mem ms3) [aidx_cell am2'; hcell (Some m2)] (sp - ASF, ASF)
HI2 HL2 Efp (MRs None s2 (ms_mem ms) HI2 RX2 MID2) _ _ _ _ _ _ _).
- intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
+ unfold s3S, sC2 in Hc. fold am2' in Hc. destruct (imageX_set_aidx X s2 m2 am2 (span_cnt am2 - 1) c M2e Hc) as [->|Ho]; [left; left; reflexivity | right; apply in_app_iff; left; exact Ho].
+ right. apply in_app_iff. right. unfold s3S, sC2 in Hc. exact (tail_cellsX_set_aidx X s2 m2 am2 _ c M2e Hc).
- intros nc [<-|[<-|[]]]; [left; unfold aidx_cell; destruct (am_maplen am2' =? 0); eexists; reflexivity | right; exact HcIn].
- intros nc c [<-|[<-|[]]] Hc.
+ exact (aidx_cell_exclusive X None U s3S L HI3 HL3 m2 am2' Hu3 c Hc).
+ exact (YN2u.new_cell_exclusive X None U s3S L HI3 HL3 (hcell (Some m2)) c (or_intror HcIn) Hc).
- intros nc [<-|[<-|[]]].
+
assert (OLDC : cell_mem B L (ms_mem ms) (aidx_cell am2)).
{ pose proof (MRs None s2 (ms_mem ms) HI2 RX2 MID2) as (MI & _). exact (proj1 (Forall_forall _ _) MI _ (aidx_cell_In_imageX X s2 m2 am2 (proj1 (inv_keys HI2)) Hu2)). }
unfold aidx_cell, cell_mem in OLDC |- *. rewrite Emem, Eml, Eai. fold aidx in OLDC.
destruct (am_maplen am2 =? 0) eqn:Eml0; cbn [mc_val mc_loc mc_w sval_num] in OLDC |- *; rewrite loc_addr_padd' in *; change (ms_segs B) with src0segs in *; fold G2 in OLDC; fold G2.
* intros _. exists (Z_to_bv 8 NB). split; [exact HNB|]. rewrite u8_of_Z by lia. exact NB32.
* assert (Haib : aib = aidx).
{ pose proof (OLDC 0%nat ltac:(lia)) as O0. cbn [Z.of_nat] in O0. rewrite Z.add_0_r, Hb, le_byte4_0 in O0 by lia.
apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in O0. cbv beta iota in O0. rewrite !u8_of_Z in O0 by lia. exact O0. }
assert (ENB : NB = span_cnt am2 - 1).
{ rewrite NBeq, Haib. rewrite land224 by lia. rewrite Z.shiftr_div_pow2, Z.div_small by lia. change (0 mod 8) with 0. lia. }
intros k Hk. destruct k as [|k].
-- cbn [Z.of_nat]. rewrite Z.add_0_r, HNB, ENB, le_byte4_0 by lia. reflexivity.
-- rewrite (KEEP (Z.of_nat (S k))), (OLDC (S k) Hk) by lia. f_equal. f_equal. apply le_byte4_hi; lia.
+ apply hcell_mem. cbn [optrZ]. exact HB.
- intros nc k [<-|[<-|[]]] Hk [pp Hpp].
+ unfold aidx_cell in Hk |- *. rewrite Emem, Eml in Hk |- *. assert (Hk4 : (k < 4)%nat) by (destruct (am_maplen am2 =? 0); cbn [mc_w] in Hk; lia).
assert (EL : loc_addr L (mc_loc (if am_maplen am2 =? 0 then MCell (LMem (padd (am_mem am2) 8)) 1 (VLo5 (am_aidx am2')) else MCell (LMem (padd (am_mem am2) 8)) 4 (VZ (am_aidx am2')))) = G2 + 8).
{ destruct (am_maplen am2 =? 0); cbn [mc_loc]; rewrite loc_addr_padd'; reflexivity. }
rewrite EL. destruct k as [|k].
* rewrite Z.add_0_r. apply YN08.writable_off_img_present; [lia | unfold in_img1; lia | exact HWg].
* unfold present. rewrite (OUT (G2 + 8 + Z.of_nat (S k))); [apply Gpres; lia | lia | lia | | unfold WS; fold sp; pose proof Hstk; unfold ASF in *; lia].
intros W. pose proof statics_layout as SL. unfold YN0j.CTX, src0_D_malloc_context in *. destruct Gimg; lia.
+ exfalso. cbn [hcell act_cell mc_loc] in Hpp. discriminate.
- intros e He. cbn [fst]. exact (footprint_top s2 e HI2 SX2 (or_intror (ex_intro _ (ms_mem ms) MID2)) He).
- intros a0 Ha0 Hno Hns.
assert (NH : ~ (YN0j.CTX + 80 + 8 * sc <= a0 < YN0j.CTX + 80 + 8 * sc + 8)).
{ intros W. apply (Hno (hcell (Some m2)) ltac:(right; left; reflexivity)). unfold in_range. rewrite hcell_range. cbn [fst snd]. lia. }
assert (NG : a0 <> G2 + 8).
{ intros ->. apply (Hno (aidx_cell am2') ltac:(left; reflexivity)). unfold in_range. rewrite aidx_cell_range, Emem, Eml. cbn [fst snd]. fold G2. destruct (am_maplen am2 =? 0); lia. }
assert (NS : ~ WS regs a0) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; lia).
pose proof (OUT a0 Ha0 NG NH NS) as EQ. split; [apply mbyte_ext1; exact EQ|]. intros [b Hb']. exists b. rewrite EQ. exact Hb'.
Qed.
Lemma postC2 : at_bnd ss_delta 80 (fun _ => True) s3S m2 (mkCfg ms3 md).
Proof.
pose proof B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2]. pose proof (proj1 bnd3S) as [HI3 _ _ _ _ _ _ _ SX3 _].
pose proof s3_factsS as (_ & S23 & RX3 & UBe & TCe & Hhd3' & Hlen3 & M2e & M3e & Efp & Erg). pose proof postC2_mem as (HB & HNB & _). pose proof postC2_regs as (G10 & GPC).
pose proof m2_factsC as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2' & G16 & Gimg & _). pose proof (proj1 alloc_ceiling_val).
destruct (junk_regs_ok src0segs JD 80 E2 SS_Sc ms3 HS3 (proj1 merge_Sc) eq_refl) as (E3 & HA3 & HSj).
pose proof (st_ok_merge src0segs E3 ss_delta _ ms3 HSj (proj2 merge_Sc)) as HSd.
assert (HA2 : env_agree 40 E00 E2) by (eapply env_agree_trans; [exact HA1s | eapply env_agree_le; [| apply E2_agree]; lia]).
exists E3, ms3. split; [reflexivity|]. split; [exact HSd|].
split; [eapply env_agree_trans; [exact HA2 | eapply env_agree_le; [| exact HA3]; lia]|].
pose proof stations_shape as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G80 & _).
split; [| split; [exact I | split; [exact RX3 | split]]].
- pose proof (st_ok_reg src0segs E3 ss_delta ms3 10 HSd) as R. rewrite G80, G10 in R. cbn [sv_denot] in R. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R. symmetry. exact R.
- apply (midrep_transport s2 s3S (ms_mem ms) (ms_mem ms3) HI2 RX2 MID2 S23 RX3 (ex_intro _ None HI3) postC2_memrep UBe TCe).
intros a Hs. destruct (static_range a Hs) as [R1 R2]. apply OUT; [lia | intros ->; lia | intros W; apply R2; unfold CTX_SIZE; lia | unfold WS; fold sp; pose proof pre_factsS as (_ & _ & P3 & _); pose proof Hstk; unfold ASF in *; lia].
- intros x Hx Hns Hnc Hno. rewrite (OUT x Hx).
+ exact (FR2 x Hx Hns Hnc Hno).
+ intros ->. apply Hno. apply (alloc_owned_same L A s2 (G2 + 8)); [apply footprint_regions_areas; pose proof SX2 as (Erg2 & Ear2 & _); congruence | |].
* apply ub_same_user_blocks; [exact (proj1 (inv_keys HI)) | exact (proj1 (inv_keys HI2)) | exact UB2].
* replace (G2 + 8) with (ptr_addr L (am_mem am2) + 8 + 0) by (unfold G2; lia). apply (aidx_bytes_owned X None U s2 L HI2 (HLs s2 (ms_mem ms) MID2) m2 am2 Hu2). lia.
+ intros W. apply Hnc. unfold CTX_SIZE. lia.
+ exact Hns.
Qed.
End h0.
Theorem stage_C2 :
SEL_C sc m2 am2 s2 = IRet (m2, s3S) /\ bnd X U A sc s3S m2 am2' /\ Z.land (am_freed am2') (ones (am_aidx am2')) <> 0 /\
SR src0segs (mkCfg ms md) (at_bnd ss_delta 80 (fun _ => True) s3S m2).
Proof.
split; [exact (selC_2 sc s2 m2 am2 Ec Hnx)|]. split; [exact (proj1 bnd3S)|]. split; [exact (proj2 bnd3S)|].
eapply SR_mono; [exact C2_run|]. intros c' (ms3 & -> & rg2 & HS3 & OUT). exact (postC2 ms3 rg2 HS3 OUT).
Qed.
End g0.
End e0.
Definition fsim (s : astate) : Prop :=
forall g' am' i fr, In (g', am', i, fr) (frames s) -> exists am, In (g', am, i, fr) (frames A) /\ stride_of am = stride_of am'.
Lemma fsim_refl : fsim A.
Proof. intros g' am' i fr H. exists am'. auto. Qed.
Lemma fsim_metas s s' : fsim s -> st_metas s' = st_metas s -> fsim s'.
Proof. intros F Em g' am' i fr H. unfold frames, used_metas in H. rewrite Em in H. exact (F g' am' i fr H). Qed.
Lemma fsim_upd s q am am' : fsim s -> MT s q = Some (MUsed am) -> am_slots am' = am_slots am -> am_last am' = am_last am -> stride_of am' = stride_of am -> fsim (upd_meta q (MUsed am') s).
Proof.
intros F Mq Es El Est g' amz i fr H.
destruct (used_metas_upd s q am Mq) as (u1 & u2 & Eu & Eu').
unfold frames in H. rewrite Eu' in H. rewrite !flat_map_app in H. cbn [flat_map] in H.
assert (H' : In (g', amz, i, fr) (frames s) \/ (g' = q /\ amz = am' /\ In (q, am, i, fr) (frames s))).
{ unfold frames. rewrite Eu, !flat_map_app. cbn [flat_map].
apply in_app_iff in H as [H|H]; [left; apply in_app_iff; left; exact H|].
apply in_app_iff in H as [H|H]; [| left; apply in_app_iff; right; apply in_app_iff; right; exact H].
right. apply in_flat_map in H as (j & Hj & H). unfold nth_slot in H. rewrite Es, El in *. fold (nth_slot am j) in H.
destruct (ss_fr (nth_slot am j)) eqn:Ef; [|destruct H]. destruct H as [H|[]]. injection H as <- <- <- <-.
split; [reflexivity|]. split; [reflexivity|]. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists j. split; [exact Hj|]. unfold nth_slot in Ef |- *. rewrite Ef. left. reflexivity. }
destruct H' as [H'|(-> & -> & H')]; [exact (F _ _ _ _ H')|].
destruct (F _ _ _ _ H') as (am1 & Hin & Hst). exists am1. split; [exact Hin | congruence].
Qed.
Section i0.
Variables (s3 : astate) (m3 : sptr) (am3 : ameta) (E : env) (ms : machine_state).
Hypothesis B3 : bnd X U A sc s3 m3 am3.
Hypothesis Hmask : Z.land (am_freed am3) (ones (am_aidx am3)) <> 0.
Hypothesis HS : st_ok src0segs E ss_delta ms.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis E80 : ew E 80 = Z_to_bv 64 (ptr_addr L m3).
Hypothesis RX3 : rawX X s3.
Hypothesis MID3 : midrep B L s3 (ms_mem ms) md.
Hypothesis FR3 : FRAME (ms_mem ms).
Hypothesis FS3 : fsim s3.
Definition M3 : Z := ptr_addr L m3.
Definition G3 : Z := ptr_addr L (am_mem am3).
Definition aib3 : Z := match mbyte src0segs (ms_mem ms) (G3 + 8) with Some b => bv_unsigned b | None => 0 end.
Definition mk : Z := maskD am3.
Definition fst3 : Z := firstD am3.
Definition idx3 : Z := ctz32 fst3.
Definition jidx3 : Z := srlw (mul64 (sx32 fst3) DBJ_MUL) 27.
Definition bv3 : Z := bval sc s3.
Definition BA : Z := YN0j.CTX + 880 + (sc - 7).
Definition hasb : bool := (7 <=? sc) && (sc <? 39).
Definition E1d : env :=
ewset (ewset (ewset (ewset (ewset (ewset (ewset (ewset E
aG3 (Z_to_bv 64 G3)) aAI3 (Z_to_bv 64 aib3)) aFR3 (Z_to_bv 64 (am_freed am3))) aBITS3 (Z_to_bv 64 (meta_bits am3 mod 2 ^ 32)))
aBAD (Z_to_bv 64 BA)) aBV (Z_to_bv 64 (if bv3 =? 0 then 1 else bv3))) aTQ3 (Z_to_bv 64 (DEB + jidx3))) aJ3 (Z_to_bv 64 idx3).
Lemma E1d_agree : env_agree 90 E E1d.
Proof.
unfold E1d.
repeat (eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aG3, aAI3, aFR3, aBITS3, aBAD, aBV, aTQ3, aJ3; lia]).
apply env_agree_refl.
Qed.
Lemma HA1d : env_agree 40 E00 E1d.
Proof. eapply env_agree_trans; [exact HA | eapply env_agree_le; [| apply E1d_agree]; lia]. Qed.
Lemma E1d_vals : ew E1d aG3 = Z_to_bv 64 G3 /\ ew E1d aAI3 = Z_to_bv 64 aib3 /\ ew E1d aFR3 = Z_to_bv 64 (am_freed am3) /\ ew E1d aBITS3 = Z_to_bv 64 (meta_bits am3 mod 2 ^ 32) /\
ew E1d aBAD = Z_to_bv 64 BA /\ ew E1d aBV = Z_to_bv 64 (if bv3 =? 0 then 1 else bv3) /\ ew E1d aTQ3 = Z_to_bv 64 (DEB + jidx3) /\ ew E1d aJ3 = Z_to_bv 64 idx3 /\
ew E1d 80 = Z_to_bv 64 M3.
Proof.
unfold E1d, aG3, aAI3, aFR3, aBITS3, aBAD, aBV, aTQ3, aJ3.
repeat split; rewrite ?ew_ewset_same; try reflexivity; rewrite !ew_ewset_other by lia; rewrite ?ew_ewset_same; try reflexivity. exact E80.
Qed.
Lemma mask_facts : 0 <= am_aidx am3 <= am_last am3 /\ am_last am3 <= 31 /\ 0 <= am_freed am3 < 2 ^ 32 /\ am_avail am3 = 0 /\
0 < mk < 2 ^ 32 /\ 0 < fst3 <= mk /\ 0 <= Z.ldiff (am_freed am3) (actv am3) < 2 ^ 32 /\ 0 <= bv3 <= 255 /\
0 <= idx3 < 32 /\ 0 <= jidx3 < 32 /\ znth jidx3 DEBRUIJN = idx3 /\ mk = Z.land (am_freed am3) (ones (am_aidx am3)) /\
Z.ldiff (am_freed am3) (actv am3) = am_freed am3 - mk.
Proof.
pose proof (grp3 X U A sc Hsc s3 m3 am3 B3 Hmask) as (G1 & G2 & G3' & G4 & G5 & G6 & G7 & G8).
pose proof (dbj_ctz32 mk ltac:(unfold mk; lia)) as [J1 J2]. pose proof (ctz32_lt fst3 32 ltac:(unfold fst3, firstD, mk, maskD in *; lia) ltac:(lia)) as CR.
assert (CZ : ctz32 fst3 = ctz32 mk) by (unfold fst3, firstD, mk, ctz32; rewrite lowbit_lowbit by (unfold mk in *; lia); reflexivity).
unfold idx3, jidx3, bv3, mk, fst3 in *. rewrite CZ in *. repeat (split; [first [assumption | lia | reflexivity] |]).
unfold maskD, actv. apply ldiff_eq_sub; [lia | unfold ones; pose proof (Z.pow_pos_nonneg 2 (am_aidx am3 + 1)); lia].
Qed.
Lemma m3_factsD :
4096 <= M3 /\ M3 + 40 <= alloc_ceiling /\ M3 mod 8 = 0 /\ (M3 + 40 <= 0x10000 \/ 0x51000 <= M3) /\ (forall x, M3 <= x < M3 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (M3 + 16) 8 G3 /\ bytes_are (ms_mem ms) (M3 + 24) 4 0 /\ bytes_are (ms_mem ms) (M3 + 28) 4 (am_freed am3) /\ bytes_are (ms_mem ms) (M3 + 32) 4 (meta_bits am3 mod 2 ^ 32) /\
4096 <= G3 /\ G3 + 16 <= alloc_ceiling /\ G3 mod 16 = 0 /\ (G3 + 16 <= 0x10000 \/ 0x51000 <= G3) /\ (forall x, G3 <= x < G3 + 16 -> present (ms_mem ms) x) /\
mbyte src0segs (ms_mem ms) (G3 + 8) = Some (Z_to_bv 8 aib3) /\ aib3 mod 32 = am_aidx am3 /\ 0 <= aib3 < 256 /\
(G3 + 16 <= M3 \/ M3 + 40 <= G3) /\ bytes_are (ms_mem ms) (YN0j.CTX + 80 + 8 * sc) 8 M3 /\
((meta_bits am3 mod 2 ^ 32) / 64) mod 64 = sc /\ 0 <= meta_bits am3 /\
(hasb = true -> bytes_are (ms_mem ms) BA 1 bv3 /\ writable_at src0segs (ms_mem ms) BA) /\
bytes_are (ms_mem ms) (DEB + jidx3) 1 idx3.
Proof.
pose proof B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 Hoth3 UB3 SX3 SP3]. pose proof (proj1 alloc_ceiling_val). pose proof mask_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & _).
pose proof (metaS None s3 (ms_mem ms) HI3 RX3 MID3 m3 am3 Hu3) as (A1 & A2 & A3 & A4 & A5 & _ & _ & B16 & B24 & B28 & B32 & _ & R2 & R3 & R4 & R5 & R6 & R7).
pose proof (grpS None s3 (ms_mem ms) HI3 RX3 MID3 m3 am3 Hu3) as (G1 & G2' & G3' & G4 & G5 & (b & Hb & Hbm) & _).
pose proof (headS None s3 (ms_mem ms) HI3 RX3 MID3) as HD. rewrite Hhd3 in HD. cbn [optrZ] in HD. rewrite K4 in B24.
assert (Eaib : aib3 = bv_unsigned b) by (unfold aib3; fold G3 in Hb; rewrite Hb; reflexivity). pose proof (u8_range b).
unfold M3, G3 in *. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- apply (YN0p.off_img _ A4).
- apply bytes_are_low4. exact B32.
- apply (off_img_range' _ 16 G4). lia.
- rewrite Hb, Eaib, Z_to_bv_bv_unsigned. reflexivity.
- rewrite Eaib. exact Hbm.
- exact (grp_meta_apart None s3 (ms_mem ms) HI3 RX3 MID3 m3 am3 m3 am3 Hu3 Hu3).
- rewrite <- Hs3. apply sc_of_bits; [lia | lia | exact R6].
- intros Hb8. unfold hasb in Hb8. apply andb_prop in Hb8 as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
split; [| apply (ctx_writableS (ms_mem ms)); unfold BA, CTX_SIZE; lia].
pose proof (YN0p.ctx_bounces_cell X L s3 (ms_mem ms) HctxS (MRs None s3 (ms_mem ms) HI3 RX3 MID3) (Z.to_nat (sc - 7)) ltac:(lia)) as C.
rewrite (proj1 CTX_eq), Z2Nat.id in C by lia. unfold BA, bv3, bval, bounce_idx.
replace (7 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 39) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. unfold znth. exact C.
- pose proof (deb_byte (ms_mem ms) (STs s3 (ms_mem ms) MID3) jidx3 ltac:(lia)) as D. rewrite K11 in D. exact D.
Qed.
Lemma valsD :
bv_unsigned (sv_denot E1d FRX3) = sx32 (am_freed am3) /\
sv_denot E1d (SAlu ALU_ADD FRX3 (SLit 0)) = sv_denot E1d FRX3 /\
bv_unsigned (sv_denot E1d NEWAV) = sx32 mk /\
bv_unsigned (sv_denot E1d NEWFR) mod 2 ^ 32 = am_freed am3 - mk /\
(bv_unsigned (sv_denot E1d LOWBIT3) = sx32 fst3 /\ bv_unsigned (sv_denot E1d LOWBIT3) <> 0) /\
bv_unsigned (sv_denot E1d AVAIL3') mod 2 ^ 32 = mk - fst3 /\
sv_denot E1d TQADDR3 = Z_to_bv 64 (DEB + jidx3) /\
bv_unsigned (sv_denot E1d SCM7) = (sc - 7) mod 2 ^ 64 /\
sv_denot E1d (SOff 80 0) = Z_to_bv 64 M3 /\ sv_denot E1d (SOff aG3 0) = Z_to_bv 64 G3 /\ sv_denot E1d (SOff aBAD 0) = Z_to_bv 64 BA.
Proof.
pose proof m3_factsD as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & G1 & G2' & _ & _ & _ & Hb & Hbm & Hb8 & _ & _ & Hsc3 & MBp & _).
pose proof mask_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & Kmk & Kld). pose proof (proj1 alloc_ceiling_val). pose proof statics_layout as SL.
destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80).
assert (Ufr : bv_unsigned (sv_denot E1d FRX3) = sx32 (am_freed am3)).
{ cbv delta [FRX3]. rewrite U_sext32'. rewrite (den_atom0 E1d aFR3 _ V92) by lia. rewrite lit64_small by lia. reflexivity. }
assert (Ush : bv_unsigned (sv_denot E1d SH3) = sllw 2 aib3).
{ cbv delta [SH3]. cbn [sv_denot]. rewrite sllw_rr_unsigned, Z.add_0_r, Z_to_bv_bv_unsigned, V91, (lit64_small 2), (lit64_small aib3) by lia. reflexivity. }
assert (Unav : bv_unsigned (sv_denot E1d NEWAV) = sx32 mk).
{ cbv delta [NEWAV]. cbn [sv_denot]. fold (sv_denot E1d FRX3). fold (sv_denot E1d SH3). rewrite alu64_and, addw_rr_unsigned, Ufr, Ush, lit64_unsigned.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite (proj2 (addiw_sllw2_m1 aib3 ltac:(lia))), Hbm, land_sx32, Kmk. reflexivity. }
pose proof (take_first_word (sv_denot E1d NEWAV) (sv_denot E1d LOWBIT3) mk ltac:(lia) Unav eq_refl) as [L1 L2].
assert (Uscm : bv_unsigned (sv_denot E1d SCM7) = (sc - 7) mod 2 ^ 64).
{ pose proof (Z.mod_pos_bound (meta_bits am3) (2 ^ 32) ltac:(lia)) as MB32.
assert (Uxb : bv_unsigned (sv_denot E1d (SExt true 32 (SOff aBITS3 0))) = sx32 (meta_bits am3 mod 2 ^ 32)).
{ rewrite U_sext32', (den_atom0 E1d aBITS3 _ V93) by lia. rewrite lit64_small by lia. reflexivity. }
cbv delta [SCM7]. remember (SExt true 32 (SOff aBITS3 0)) as XB eqn:EXB. cbn [sv_denot]. rewrite alu64_add, alu64_srl, alu64_sll, Uxb.
rewrite (lit64_small 52), (lit64_small 58) by lia. change (52 mod 64) with 52. change (58 mod 64) with 58.
rewrite bits_6_12 by apply sx32_range. rewrite sx32_div64_mod64 by lia. rewrite Hsc3. rewrite lit64_unsigned. unfold add64.
rewrite Zplus_mod_idemp_r. f_equal. }
repeat match goal with |- _ /\ _ => split end.
- exact Ufr.
- apply word_eq. cbn [sv_denot]. fold (sv_denot E1d FRX3). rewrite alu64_add, Ufr, (lit64_small 0) by lia. unfold add64. rewrite Z.add_0_r. apply Z.mod_small. apply sx32_range.
- exact Unav.
- cbv delta [NEWFR]. cbn [sv_denot]. fold (sv_denot E1d FRX3). fold (sv_denot E1d SH3). rewrite alu64_and, negw_unsigned, Ufr, Ush.
rewrite <- lo32_of_mod || idtac. change (bv_unsigned ?[x] mod 2 ^ 32) with (lo32 (bv_unsigned x)) || idtac.
pose proof (land_negw_sllw2_lo32 (am_freed am3) aib3 ltac:(lia) ltac:(lia)) as LN. rewrite Hbm, <- Kmk in LN. unfold lo32 in LN. exact LN.
- exact L1.
- exact L2.
- cbv delta [AVAIL3']. cbn [sv_denot]. fold (sv_denot E1d NEWAV). fold (sv_denot E1d LOWBIT3).
pose proof (take_rest_word (sv_denot E1d NEWAV) (sv_denot E1d LOWBIT3) _ mk ltac:(lia) Unav L1 eq_refl) as R. rewrite low32_unsigned in R. unfold lo32 in R. unfold fst3, firstD. fold mk. exact R.
- apply word_eq. cbv delta [TQADDR3]. cbn [sv_denot]. fold (sv_denot E1d LOWBIT3). rewrite alu64_add, srlw_rr_unsigned, mul64_unsigned, L1.
change (bv_unsigned (Z_to_bv 64 DBJ)) with DBJ_MUL. change (bv_unsigned (Z_to_bv 64 27)) with 27. fold jidx3.
rewrite (lit64_small DEB) by lia. rewrite (lit64_small (DEB + jidx3)) by lia. apply add64_small. lia.
- exact Uscm.
- apply (den_atom0 E1d 80 _ V80). lia.
- apply (den_atom0 E1d aG3 _ V90). lia.
- apply (den_atom0 E1d aBAD _ V94). unfold BA, YN0j.CTX in *; lia.
Qed.
Lemma valsD_bad : 7 <= sc -> sv_denot E1d BADX = sv_denot E1d (SOff aBAD (-888)).
Proof.
intros H7. pose proof m3_factsD as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & G1 & G2' & _ & _ & _ & Hb & Hbm & Hb8 & _ & _ & Hsc3 & MBp & _).
pose proof valsD as (_ & _ & _ & _ & _ & _ & _ & Uscm & _). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80). pose proof statics_layout as SL.
rewrite (den_atom E1d aBAD BA (-888) V94) by (unfold BA, YN0j.CTX in *; lia). apply word_eq. cbv delta [BADX]. cbn [sv_denot]. fold (sv_denot E1d SCM7).
rewrite alu64_add, Uscm, (lit64_small YN0j.LOCK) by (unfold YN0j.LOCK in *; lia).
rewrite (Z.mod_small (sc - 7)) by lia. rewrite (lit64_small (BA + -888)) by (unfold BA, YN0j.CTX in *; lia). unfold add64, BA. pose proof CTX_eq.
rewrite Z.mod_small by (unfold YN0j.LOCK, YN0j.CTX in *; lia). lia.
Qed.
Inductive dvar := DV0 | DV1 | DV2.
Definition ssD (v : dvar) : sstate := match v with DV0 => ss_DE0 | DV1 => ss_DE1 | DV2 => ss_DE2 end.
Definition SSD (v : dvar) : sstate := match v with DV0 => SSD_0 | DV1 => SSD_1 | DV2 => SSD_2 end.
Definition dcond (v : dvar) : Prop :=
match v with DV0 => hasb = false | DV1 => hasb = true /\ bv3 = 0 | DV2 => hasb = true /\ bv3 <> 0 end.
Lemma region_m3 : region_ok src0segs E1d (ms_mem ms) R_m3.
Proof.
pose proof m3_factsD as (A1 & A2 & A8 & Aimg & Apres & B16 & B24 & B28 & B32 & G1 & G2' & _). pose proof (proj1 alloc_ceiling_val). pose proof mask_facts as (K1 & K2 & K3 & _).
destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80). pose proof valsD as (_ & _ & _ & _ & _ & _ & _ & _ & W80 & W90 & _).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m3]; rewrite (base_atom E1d 80 M3 V80) by lia; [lia | lia | intros o Ho; apply present_writable; apply Apres; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_ok_val' E1d _ _ _ 8 _ G3); [rewrite W90; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B16].
- apply (chunk_ok_val' E1d _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B24].
- apply (chunk_ok_val' E1d _ _ _ 4 _ (am_freed am3)); [rewrite (den_atom0 E1d aFR3 _ V92) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B28].
- apply (chunk_ok_val' E1d _ _ _ 4 _ (meta_bits am3 mod 2 ^ 32)); [| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); apply Z.mod_pos_bound; lia | exact B32].
rewrite (den_atom0 E1d aBITS3 _ V93) by (pose proof (Z.mod_pos_bound (meta_bits am3) (2 ^ 32) ltac:(lia)); lia). apply lit64_small. pose proof (Z.mod_pos_bound (meta_bits am3) (2 ^ 32) ltac:(lia)); lia.
Qed.
Lemma region_g3 : region_ok src0segs E1d (ms_mem ms) R_g3.
Proof.
pose proof m3_factsD as (A1 & A2 & A8 & Aimg & Apres & B16 & B24 & B28 & B32 & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & _). pose proof (proj1 alloc_ceiling_val).
destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_g3]; rewrite (base_atom E1d aG3 G3 V90) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1d _ _ _ 1 _ aib3); [rewrite (den_atom0 E1d aAI3 _ V91) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
intros kk Hkk. replace kk with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256. rewrite (Z.mod_small aib3 256), Z.mod_small by lia. reflexivity.
Qed.
Lemma region_tq3 : region_ok src0segs E1d (ms_mem ms) R_tq3.
Proof.
pose proof m3_factsD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdeb). pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & _).
destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80). pose proof statics_layout as SL.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_tq3]; rewrite (base_atom E1d aTQ3 _ V96) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1d _ _ _ 1 _ idx3); [rewrite (den_atom0 E1d aJ3 idx3 V97) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 1)) with 256; lia |]. rewrite Z.add_0_r. exact Hdeb.
Qed.
Lemma region_bnc v : hasb = true -> (bv3 = 0 /\ v = SLit 0) \/ (bv3 <> 0 /\ v = SOff aBV 0) -> region_ok src0segs E1d (ms_mem ms) (R_bnc v).
Proof.
intros Hh Hv. pose proof m3_factsD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbn & _). destruct (Hbn Hh) as [Bb Bw].
pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & K8 & _). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80). pose proof statics_layout as SL.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_bnc]; rewrite (base_atom E1d aBAD _ V94) by (unfold BA, YN0j.CTX in *; lia); [unfold BA, YN0j.CTX in *; lia | unfold BA, YN0j.CTX in *; lia | intros o Ho; replace (BA + o) with BA by lia; exact Bw |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val' E1d _ _ _ 1 _ bv3); [| change (2 ^ (8 * Z.of_N 1)) with 256; lia | rewrite Z.add_0_r; exact Bb].
destruct Hv as [[Hz ->]|[Hnz ->]]; [cbn [sv_denot]; rewrite Hz; apply lit64_small; lia|].
rewrite (den_atom0 E1d aBV _ V95) by (destruct (bv3 =? 0); lia). replace (bv3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). apply lit64_small. lia.
Qed.
Definition baseD : smem := R_actW (SOff 80 0) :: tl (ss_mem ss_hd).
Lemma BD_D r' lo hi : In r' baseD -> 4096 <= lo -> hi <= alloc_ceiling -> (hi <= 0x10000 \/ 0x51000 <= lo) ->
hi <= base_val E1d (r_base r') + r_lo r' \/ base_val E1d (r_base r') + r_hi r' <= lo.
Proof. intros Hr'. apply (base_disjoint E1d r' lo hi HA1d). destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]. Qed.
Lemma BI_D r' lo hi : In r' baseD -> hi <= 0x51000 ->
(hi <= YN0j.CTX + 80 + 8 * sc \/ YN0j.CTX + 80 + 8 * sc + 8 <= lo) ->
(hi <= GOT \/ GOT + 8 <= lo) -> (hi <= GUARD \/ GUARD + 8 <= lo) -> (hi <= LIBC + 48 \/ LIBC + 56 <= lo) ->
hi <= base_val E1d (r_base r') + r_lo r' \/ base_val E1d (r_base r') + r_hi r' <= lo.
Proof.
intros Hr' Hhi D1 D2 D3 D4. pose proof (agree_facts E1d HA1d) as (_ & _ & B33 & B2 & _). pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq.
destruct Hr' as [<-|Hr'].
- cbn [r_base r_lo r_hi R_actW]. rewrite B33. lia.
- pose proof (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hr') as Hin'. rewrite MEM0_skel in Hin'. cbn [In] in Hin'.
decompose [or] Hin'; try contradiction; match goal with H : _ = (r_base r', _, _, _, _) |- _ => injection H as Eb El Eh _ _ end; rewrite <- El, <- Eh, <- Eb; rewrite ?B2; cbn [base_val]; try lia.
pose proof Hstk. unfold ASF in *. lia.
Qed.
Lemma Dm3 r' : In r' baseD -> extent_disjoint E1d R_m3 r'.
Proof.
intros Hr'. pose proof m3_factsD as (A1 & A2 & A8 & Aimg & _). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80). pose proof (proj1 alloc_ceiling_val).
unfold extent_disjoint. cbn [r_base r_lo r_hi R_m3]. rewrite (base_atom E1d 80 M3 V80) by lia. destruct (BD_D r' M3 (M3 + 40) Hr' ltac:(lia) ltac:(lia) Aimg); lia.
Qed.
Lemma Dg3 r' : In r' baseD -> extent_disjoint E1d R_g3 r'.
Proof.
intros Hr'. pose proof m3_factsD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2' & G16 & Gimg & _). destruct E1d_vals as (V90 & _). pose proof (proj1 alloc_ceiling_val).
unfold extent_disjoint. cbn [r_base r_lo r_hi R_g3]. rewrite (base_atom E1d aG3 G3 V90) by lia. destruct (BD_D r' G3 (G3 + 16) Hr' ltac:(lia) ltac:(lia) Gimg); lia.
Qed.
Lemma Dtq r' : In r' baseD -> extent_disjoint E1d R_tq3 r'.
Proof.
intros Hr'. pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & _). destruct E1d_vals as (_ & _ & _ & _ & _ & _ & V96 & _). pose proof statics_layout as SL.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_tq3]. rewrite (base_atom E1d aTQ3 _ V96) by lia.
destruct (BI_D r' (DEB + jidx3) (DEB + jidx3 + 1) Hr' ltac:(lia) ltac:(unfold YN0j.CTX in *; lia) ltac:(lia) ltac:(lia) ltac:(lia)); lia.
Qed.
Lemma Dbn vv r' : In r' baseD -> extent_disjoint E1d (R_bnc vv) r'.
Proof.
intros Hr'. destruct E1d_vals as (_ & _ & _ & _ & V94 & _). pose proof statics_layout as SL. pose proof statics_layout2 as SL2.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_bnc]. rewrite (base_atom E1d aBAD _ V94) by (unfold BA, YN0j.CTX in *; lia).
destruct (BI_D r' BA (BA + 1) Hr' ltac:(unfold BA, YN0j.CTX in *; lia) ltac:(unfold BA; lia) ltac:(unfold BA; lia) ltac:(unfold BA; lia) ltac:(unfold BA; lia)); lia.
Qed.
Lemma Dmg : extent_disjoint E1d R_m3 R_g3 /\ extent_disjoint E1d R_m3 R_tq3 /\ extent_disjoint E1d R_g3 R_tq3 /\
(forall vv, extent_disjoint E1d R_m3 (R_bnc vv) /\ extent_disjoint E1d R_g3 (R_bnc vv) /\ extent_disjoint E1d R_tq3 (R_bnc vv)).
Proof.
pose proof m3_factsD as (A1 & A2 & A8 & Aimg & Apres & B16 & B24 & B28 & B32 & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & AP & _). pose proof (proj1 alloc_ceiling_val).
pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & _). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80).
pose proof statics_layout as (SLa & SLb & SLc & SLd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLe).
unfold extent_disjoint. cbn [r_base r_lo r_hi R_m3 R_g3 R_tq3 R_bnc].
rewrite (base_atom E1d 80 M3 V80), (base_atom E1d aG3 G3 V90), (base_atom E1d aTQ3 _ V96), (base_atom E1d aBAD _ V94) by (unfold BA, YN0j.CTX in *; lia).
unfold BA. repeat split; try intros; lia.
Qed.
Lemma D_atoms : atoms_ok E1d (d_atoms ++ f_atoms (ss_facts ss_hd)).
Proof.
pose proof (st_ok_agree src0segs 90 E E1d ss_delta ms HS E1d_agree ss_delta_atoms) as HS1. pose proof stations_shape as (_ & _ & _ & _ & _ & Fd & _).
pose proof (st_ok_facts_ok _ _ _ _ HS1) as (Sat & _). rewrite Fd in Sat.
pose proof m3_factsD as (A1 & A2 & A8 & Aimg & Apres & B16 & B24 & B28 & B32 & G1 & G2' & G16 & Gimg & Gpres & Hb & Hbm & Hb8 & _). pose proof (proj1 alloc_ceiling_val).
pose proof mask_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80).
pose proof statics_layout as (SLa & SLb & SLc & SLd & _).
assert (HBA : 0x10000 <= BA <= 0x51000) by (unfold BA, YN0j.CTX in *; lia).
assert (HBV : 1 <= (if bv3 =? 0 then 1 else bv3) <= 255) by (destruct (bv3 =? 0) eqn:Eb; [lia | apply Z.eqb_neq in Eb; lia]).
pose proof (Z.mod_pos_bound (meta_bits am3) (2 ^ 32) ltac:(lia)) as MB.
unfold d_atoms. cbn [app atoms_ok]. unfold FM, afact_ok; cbn [af_lo af_hi af_al2].
rewrite V80, V90, V91, V92, V93, V94, V95, V96, V97. rewrite !lit64_small by lia.
change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat (split; [lia|]). exact Sat.
Qed.
Lemma D_conds : acond_ok E1d C_cas /\ acond_ok E1d C_nav /\ acond_ok E1d C_lb3 /\ (hasb = false -> acond_ok E1d C_e0) /\ (hasb = true -> acond_ok E1d C_e12) /\
sv_denot E1d TQADDR3 = sv_denot E1d (SOff aTQ3 0).
Proof.
pose proof mask_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80).
pose proof valsD as (Wfr & Wcas & Wnav & Wnfr & [Wlb1 Wlb2] & Wav & Wtq & Wscm & _). pose proof statics_layout as (SLa & SLb & _).
repeat match goal with |- _ /\ _ => split end; unfold acond_ok; cbn [ac_c ac_a ac_b C_cas C_nav C_lb3 C_e0 C_e12].
- rewrite branch_eq, Wcas. apply Z.eqb_refl.
- rewrite branch_ne, Wnav. cbn [sv_denot]. rewrite (lit64_small 0) by lia. destruct (Z.eqb_spec (sx32 mk) 0) as [Ee|]; [exfalso; exact (sx32_nonzero_u32 mk ltac:(lia) Ee) | reflexivity].
- rewrite branch_ne. cbn [sv_denot]. fold (sv_denot E1d LOWBIT3). rewrite (lit64_small 0) by lia. destruct (Z.eqb_spec (bv_unsigned (sv_denot E1d LOWBIT3)) 0); [exfalso; exact (Wlb2 e) | reflexivity].
- intros Hh. rewrite branch_ltu, Wscm. cbn [sv_denot]. rewrite (lit64_small 31) by lia. apply Z.ltb_lt.
unfold hasb in Hh. destruct (Z_lt_dec sc 7).
+ rewrite <- (Z_mod_plus_full (sc - 7) 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia.
+ rewrite Z.mod_small by lia. apply Bool.andb_false_iff in Hh as [Hh|Hh]; [apply Z.leb_gt in Hh; lia | apply Z.ltb_ge in Hh; lia].
- intros Hh. rewrite branch_geu, Wscm. cbn [sv_denot]. rewrite (lit64_small 31) by lia.
unfold hasb in Hh. apply andb_prop in Hh as [Hh1 Hh2]. apply Z.leb_le in Hh1. apply Z.ltb_lt in Hh2. rewrite Z.mod_small by lia.
destruct (Z.ltb_spec 31 (sc - 7)); [lia | reflexivity].
- rewrite Wtq, (den_atom0 E1d aTQ3 _ V96) by lia. reflexivity.
Qed.
Lemma D_st_ok v : dcond v -> st_ok src0segs E1d (ssD v) ms.
Proof.
intros DC.
pose proof m3_factsD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD & _). pose proof m3_factsD as (A1 & A2 & _). pose proof (proj1 alloc_ceiling_val).
pose proof valsD as (_ & _ & _ & _ & _ & _ & _ & _ & W80 & _).
pose proof (st_ok_agree src0segs 90 E E1d ss_delta ms HS E1d_agree ss_delta_atoms) as HS1.
pose proof stations_shape as (_ & _ & Md & _ & _ & Fd & _).
pose proof (base_mem_ok E1d ss_delta ms (SOff 80 0) HS1 Md HA1d ltac:(rewrite W80, lit64_small by lia; exact HD)) as BASE. fold baseD in BASE.
destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _).
pose proof D_conds as (C1 & C2 & C3 & CE0 & CE12 & ALtq). pose proof Dmg as (X1 & X2 & X3 & X4).
destruct v; cbn [dcond] in DC; unfold st_ok, ssD, ss_DE0, ss_DE1, ss_DE2, ss_Dg; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]; fold baseD;
(split; [exact S1|]; split; [rewrite S2, ss_delta_pc; reflexivity|]; split; [exact S3|]; split; [exact S4|]; split; [exact S5|]; split; [exact S6|]; split; [exact S7|]; split).
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m3 | | apply mem_ok_cons'; [reflexivity | apply region_g3 | | apply mem_ok_cons'; [reflexivity | apply region_tq3 | exact Dtq | exact BASE]]].
+ intros r' [<-|[<-|Hr']]; [exact X1 | exact X2 | exact (Dm3 r' Hr')].
+ intros r' [<-|Hr']; [exact X3 | exact (Dg3 r' Hr')].
- split; [exact D_atoms|]. split; [| split; [exact ALtq | exact I]]. repeat (split; [assumption|]). split; [apply CE0; exact DC | exact I].
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m3 | | apply mem_ok_cons'; [reflexivity | apply region_g3 | | apply mem_ok_cons'; [reflexivity | apply region_tq3 | | apply mem_ok_cons'; [reflexivity | apply region_bnc; [exact (proj1 DC) | left; split; [exact (proj2 DC) | reflexivity]] | exact (Dbn _) | exact BASE]]]].
+ intros r' [<-|[<-|[<-|Hr']]]; [exact X1 | exact X2 | exact (proj1 (X4 _)) | exact (Dm3 r' Hr')].
+ intros r' [<-|[<-|Hr']]; [exact X3 | exact (proj1 (proj2 (X4 _))) | exact (Dg3 r' Hr')].
+ intros r' [<-|Hr']; [exact (proj2 (proj2 (X4 _))) | exact (Dtq r' Hr')].
- split; [exact D_atoms|]. split; [| split; [exact ALtq | split; [apply valsD_bad; pose proof (proj1 DC) as Hh; unfold hasb in Hh; apply andb_prop in Hh as [Hh _]; apply Z.leb_le in Hh; exact Hh | exact I]]].
repeat (split; [assumption|]). split; [apply CE12; exact (proj1 DC) | exact I].
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply region_m3 | | apply mem_ok_cons'; [reflexivity | apply region_g3 | | apply mem_ok_cons'; [reflexivity | apply region_tq3 | | apply mem_ok_cons'; [reflexivity | apply region_bnc; [exact (proj1 DC) | right; split; [exact (proj2 DC) | reflexivity]] | exact (Dbn _) | exact BASE]]]].
+ intros r' [<-|[<-|[<-|Hr']]]; [exact X1 | exact X2 | exact (proj1 (X4 _)) | exact (Dm3 r' Hr')].
+ intros r' [<-|[<-|Hr']]; [exact X3 | exact (proj1 (proj2 (X4 _))) | exact (Dg3 r' Hr')].
+ intros r' [<-|Hr']; [exact (proj2 (proj2 (X4 _))) | exact (Dtq r' Hr')].
- split; [exact D_atoms|]. split; [| split; [exact ALtq | split; [apply valsD_bad; pose proof (proj1 DC) as Hh; unfold hasb in Hh; apply andb_prop in Hh as [Hh _]; apply Z.leb_le in Hh; exact Hh | exact I]]].
repeat (split; [assumption|]). split; [apply CE12; exact (proj1 DC) | exact I].
Qed.
Lemma D_run v : dcond v ->
SR src0segs (mkCfg ms md) (fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E1d (SSD v) ms1 /\ frame_of E1d (ss_mem (ssD v)) (ms_mem ms) (ms_mem ms1)).
Proof.
intros DC. pose proof md_factsS as (Mh & Mlz & _). pose proof (D_st_ok v DC) as HS0.
assert (RUN : run_to_ok PS_JR (ssD v) (fst (sym_run_toN src0segs src0tbl FUEL PS_JR (ssD v)))) by (destruct v; [apply DE0_run_ok | apply DE1_run_ok | apply DE2_run_ok]).
eapply SR_mono; [eapply (SR_run_to PS_JR); [exact HS0 | exact RUN | exact Mh | exact Mlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
assert (EE : SSD v = closeF (ssD v) PS_JR) by (destruct v; symmetry; [apply SSD_0_eq | apply SSD_1_eq | apply SSD_2_eq]).
rewrite EE. unfold closeF. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS0)].
Qed.
Definition s3f : astate := upd_meta m3 (MUsed (am3f am3)) s3.
Definition sFx : astate := if hasb && negb (bv3 =? 0) then set_bounces (zset (sc - 7) (bv3 - 1) (st_bounces s3)) s3f else s3f.
Lemma upd_meta_set_bounces q x l s0 : upd_meta q x (set_bounces l s0) = set_bounces l (upd_meta q x s0).
Proof. reflexivity. Qed.
Lemma sF_eq : sF sc s3 m3 am3 = sFx.
Proof.
unfold sF, s5, s4, sFx, s3f, bounce_idx. change (bval sc s3) with bv3. change ((7 <=? sc) && (sc <? 39)) with hasb.
destruct hasb; cbn [andb]; [|apply upd_meta_twice]. destruct (bv3 =? 0); cbn [negb]; [apply upd_meta_twice|].
rewrite upd_meta_set_bounces, upd_meta_twice. reflexivity.
Qed.
Definition cAV : mcell := MCell (LMem (padd m3 META_avail)) 4 (VZ (mk - fst3)).
Definition cFR : mcell := MCell (LMem (padd m3 META_freed)) 4 (VZ (am_freed am3 - mk)).
Definition bcell (k : nat) (v : Z) : mcell := MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ v).
Definition cBN : mcell := bcell (Z.to_nat (sc - 7)) (if bv3 =? 0 then 0 else bv3 - 1).
Definition NEWD : list mcell := [hcell (Some m3); cAV; cFR] ++ (if hasb then [cBN] else []).
Lemma bcell_In s0 k : (k < 32)%nat -> In (bcell k (nth k (st_bounces s0) 0)) (ctx_cells s0).
Proof. intros Hk. unfold ctx_cells, bcell. rewrite !in_app_iff. do 4 right. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. Qed.
Lemma ctx_cells_set_bounces s0 l c : In c (ctx_cells (set_bounces l s0)) -> (exists k, (k < 32)%nat /\ c = bcell k (nth k l 0)) \/ In c (ctx_cells s0).
Proof.
intros Hc. unfold ctx_cells in *. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_bounces] in Hc.
rewrite !in_app_iff in Hc. rewrite !in_app_iff.
destruct Hc as [H|[H|[H|[H|H]]]]; [right; auto | right; auto | right; auto | right; auto 6 |].
left. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
Qed.
Lemma imageX_set_bounces s0 l c : In c (imageX X (set_bounces l s0)) -> In c (ctx_cells (set_bounces l s0)) \/ In c (imageX X s0).
Proof.
intros Hc. unfold imageX in *. rewrite (areas_cells_ext' s0 (set_bounces l s0)) in Hc by reflexivity.
change (st_areas (set_bounces l s0)) with (st_areas s0) in Hc. change (used_metasX X (set_bounces l s0)) with (used_metasX X s0) in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [left; exact Hc | right]. apply in_app_iff. right. exact Hc.
Qed.
Lemma am3f_facts : grp_same am3 (am3f am3) /\ am_avail (am3f am3) = mk - fst3 /\ am_freed (am3f am3) = am_freed am3 - mk /\
am_prev (am3f am3) = am_prev am3 /\ am_next (am3f am3) = am_next am3 /\ am_mem (am3f am3) = am_mem am3 /\ meta_bits (am3f am3) = meta_bits am3 /\
am_slots (am3f am3) = am_slots am3 /\ am_last (am3f am3) = am_last am3 /\ stride_of (am3f am3) = stride_of am3.
Proof.
pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kmk & Kld).
unfold am3f, am3a. fold mk. change (firstD am3) with fst3. rewrite Kld. destruct am3; cbn; repeat split; reflexivity.
Qed.
Section j0.
Variables (v : dvar) (ms1 : machine_state).
Hypothesis DC : dcond v.
Hypothesis HS2 : st_ok src0segs E1d (SSD v) ms1.
Hypothesis HF : frame_of E1d (ss_mem (ssD v)) (ms_mem ms) (ms_mem ms1).
Lemma finalS_check_D : finalS_check (SSD v) (SOff aJ3 0) = true.
Proof. clear HS2 HF DC. destruct v; vm_compute; reflexivity. Qed.
Lemma postD_regs : regs_preserved regs (ms_regs ms1) /\ ew E1d 1 = getr regs 1 /\ getr (ms_regs ms1) 10 = Z_to_bv 64 idx3 /\
sr_get (ss_regs (SSD v)) 1 = SOff 1 0 /\ ss_pc (SSD v) = PS_JR /\ ss_resv (SSD v) = None.
Proof.
destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80). pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
destruct (finalS L A regs mem sc stk PRE g 0 M0 E1d (SSD v) ms1 (SOff aJ3 0) finalS_check_D HS2 HA1d) as (RP & Era & Hra & Hpc & Hrv & G10).
repeat (split; [assumption|]). split; [rewrite G10; apply (den_atom0 E1d aJ3 idx3 V97); lia|]. auto.
Qed.
Lemma postD_guard : word_mem src0segs (ms_mem ms1) GUARD g.
Proof.
clear HF DC. destruct v;
[ exact (guard_of_state L A regs sc g 0 M0 E1d _ ms1 6 HS2 HA1d ltac:(vm_compute; reflexivity))
| exact (guard_of_state L A regs sc g 0 M0 E1d _ ms1 7 HS2 HA1d ltac:(vm_compute; reflexivity))
| exact (guard_of_state L A regs sc g 0 M0 E1d _ ms1 7 HS2 HA1d ltac:(vm_compute; reflexivity)) ].
Qed.
Lemma postD_mem :
(forall x, 0 <= x < 2 ^ 64 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ (M3 + 24 <= x < M3 + 32) -> ~ (hasb = true /\ x = BA) -> ~ WS regs x ->
(ms_mem ms1) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x)) /\
bytes_are (ms_mem ms1) (YN0j.CTX + 80 + 8 * sc) 8 M3 /\
bytes_are (ms_mem ms1) (M3 + 24) 4 (mk - fst3) /\ bytes_are (ms_mem ms1) (M3 + 28) 4 (am_freed am3 - mk) /\
(hasb = true -> bytes_are (ms_mem ms1) BA 1 (if bv3 =? 0 then 0 else bv3 - 1)) /\
(forall a, M3 + 24 <= a < M3 + 32 -> writable_at src0segs (ms_mem ms1) a) /\ (forall a, WS regs a -> writable_at src0segs (ms_mem ms1) a).
Proof.
pose proof valsD as (Wfr & Wcas & Wnav & Wnfr & [Wlb1 Wlb2] & Wav & Wtq & Wscm & W80 & W90 & W94). destruct E1d_vals as (V90 & V91 & V92 & V93 & V94 & V95 & V96 & V97 & V80).
pose proof (agree_facts E1d HA1d) as (_ & _ & B33 & B2 & _). pose proof m3_factsD as (A1 & A2 & _). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
pose proof mask_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & _). pose proof statics_layout as (SLa & SLb & SLc & SLd & _).
pose proof (st_ok_mem_ok src0segs E1d (SSD v) ms1 HS2) as (_ & MOK & _).
pose proof SSD_shape as ((Sh0 & Sh1 & Sh2) & _).
assert (MEMv : exists rb, ss_mem (SSD v) = [R_m3'; R_g3; R_tq3] ++ rb ++ R_actW (SOff 80 0) :: tl (ss_mem ss_hd) /\
rb = match v with DV0 => [] | DV1 => [R_bnc (SLit 0)] | DV2 => [R_bnc (SOff aBV (-1))] end).
{ destruct v; cbn [SSD]; [rewrite Sh0 | rewrite Sh1 | rewrite Sh2]; eexists; (split; [|reflexivity]); reflexivity. }
destruct MEMv as (rb & Emem & Erb). rewrite Emem in MOK.
assert (Rm3 : region_ok src0segs E1d (ms_mem ms1) R_m3') by exact (proj1 (Forall_forall _ _) MOK _ ltac:(left; reflexivity)).
assert (Ract : region_ok src0segs E1d (ms_mem ms1) (R_actW (SOff 80 0))) by exact (proj1 (Forall_forall _ _) MOK _ ltac:(apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)).
assert (Rstk : exists rstk, region_ok src0segs E1d (ms_mem ms1) rstk /\ (r_base rstk, r_wlo rstk, r_whi rstk) = (Some 2%nat, -384, 0)).
{ destruct stack_region as (rstk & t & Et & SKR). exists rstk. split; [|exact SKR].
apply (proj1 (Forall_forall _ _) MOK). apply in_app_iff; right; apply in_app_iff; right; right. rewrite Et. left. reflexivity. }
destruct Rm3 as (_ & _ & WRm & CHm). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m3'] in WRm, CHm. rewrite (base_atom E1d 80 M3 V80) in WRm, CHm by lia.
destruct Ract as (_ & _ & _ & CHa). cbn [r_base r_chunks R_actW] in CHa. rewrite B33 in CHa.
destruct Rstk as (rstk & (_ & _ & WRs & _) & SKR). injection SKR as Eb' Ewl' Ewh'. rewrite Eb', Ewl', Ewh' in WRs. rewrite (proj1 (proj2 (proj2 (proj2 (agree_facts E1d HA1d))))) in WRs.
repeat match goal with |- _ /\ _ => split end.
- intros x Hx Hnh Hnm Hnb Hns. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw.
assert (Hw' : exists rs, (forall r, In r rs -> r = R_m3 \/ (exists vv, r = R_bnc vv /\ hasb = true) \/ (r_wlo r = 0 /\ r_whi r = 0)) /\ in_wrange E1d (rs ++ R_actW (SOff 80 0) :: tl (ss_mem ss_hd)) x).
{ destruct v; cbn [ssD ss_DE0 ss_DE1 ss_DE2 ss_Dg ss_mem app] in Hw; cbn [dcond] in DC;
[exists [R_m3; R_g3; R_tq3] | exists [R_m3; R_g3; R_tq3; R_bnc (SLit 0)] | exists [R_m3; R_g3; R_tq3; R_bnc (SOff aBV 0)]];
(split; [| cbn [app]; exact Hw]); intros r Hr; cbn [In] in Hr;
decompose [or] Hr; try contradiction; subst r; first [left; reflexivity | right; left; eexists; split; [reflexivity | exact (proj1 DC)] | right; right; split; reflexivity]. }
clear Hw. destruct Hw' as (rs & Hrs & Hw). destruct (wrange_cases E1d rs _ x HA1d Hw) as [(r & Hin & Hr)|[Hh|Hs']]; [| exact (Hnh Hh) | exact (Hns Hs')].
destruct (Hrs r Hin) as [->|[(vv & -> & Hh)|[E1' E2']]].
+ cbn [r_base r_wlo r_whi R_m3] in Hr. rewrite (base_atom E1d 80 M3 V80) in Hr by lia. apply Hnm. lia.
+ cbn [r_base r_wlo r_whi R_bnc] in Hr. rewrite (base_atom E1d aBAD BA V94) in Hr by (unfold BA, YN0j.CTX in *; lia). apply Hnb. split; [exact Hh | lia].
+ rewrite E1', E2' in Hr. lia.
- replace (YN0j.CTX + 80 + 8 * sc) with (YN0j.LOCK + 8 * sc + 88) by lia.
rewrite <- (Z.mod_small M3 (2 ^ (8 * Z.of_N 8))) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
apply (chunk_bytes' E1d _ _ _ 8 (SOff 80 0)); [exact (Forall_inv CHa) | rewrite W80; apply lit64_small; lia].
- rewrite <- Wav. apply (chunk_bytes' E1d _ _ _ 4 AVAIL3'); [exact (Forall_inv CHm) | reflexivity].
- rewrite <- Wnfr. apply (chunk_bytes' E1d _ _ _ 4 NEWFR); [exact (Forall_inv (Forall_inv_tail CHm)) | reflexivity].
- intros Hh. assert (Rb : exists vv, region_ok src0segs E1d (ms_mem ms1) (R_bnc vv) /\ bv_unsigned (sv_denot E1d vv) = (if bv3 =? 0 then 0 else bv3 - 1)).
{ destruct v; cbn [dcond] in DC; [rewrite Hh in DC; discriminate| |]; rewrite Erb in MOK.
- exists (SLit 0). split; [exact (proj1 (Forall_forall _ _) MOK _ ltac:(do 3 right; left; reflexivity))|]. cbn [sv_denot]. rewrite (proj2 DC), Z.eqb_refl. apply lit64_small. lia.
- exists (SOff aBV (-1)). split; [exact (proj1 (Forall_forall _ _) MOK _ ltac:(do 3 right; left; reflexivity))|].
replace (bv3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact (proj2 DC)).
rewrite (den_atom E1d aBV (if bv3 =? 0 then 1 else bv3) (-1) V95) by (destruct (bv3 =? 0); lia). replace (bv3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact (proj2 DC)). apply lit64_small. lia. }
destruct Rb as (vv & (_ & _ & _ & CHb) & Hvv). cbn [r_base r_chunks R_bnc] in CHb. rewrite (base_atom E1d aBAD BA V94) in CHb by (unfold BA, YN0j.CTX in *; lia).
rewrite <- (Z.mod_small (if bv3 =? 0 then 0 else bv3 - 1) (2 ^ (8 * Z.of_N 1))) by (change (2 ^ (8 * Z.of_N 1)) with 256; destruct (Z.eqb_spec bv3 0); lia).
rewrite <- (Z.add_0_r BA). apply (chunk_bytes' E1d _ _ _ 1 vv); [exact (Forall_inv CHb) | exact Hvv].
- intros a Ha. replace a with (M3 + (a - M3)) by lia. apply WRm. lia.
- intros a Ha. unfold WS, ASF in Ha. fold sp in Ha. replace a with (sp + (a - sp)) by lia. apply WRs. lia.
Qed.
Lemma sF_facts :
Inv X (Some (m3, idx3)) U sFx /\ active_hd sFx sc = Some m3 /\ MT sFx m3 = Some (MUsed (am3f am3)) /\ class_size sc <= stride_of (am3f am3) /\
ub_same A sFx /\ sameX A sFx /\ sameX s3 sFx /\ rawX X sFx /\ user_blocks sFx = user_blocks s3 /\ tail_cells sFx = tail_cells s3 /\ fsim sFx /\
length (st_active sFx) = 48%nat /\
st_bounces sFx = (if hasb && negb (bv3 =? 0) then zset (sc - 7) (bv3 - 1) (st_bounces s3) else st_bounces s3) /\ length (st_bounces s3) = 32%nat /\
(hasb = true -> nth (Z.to_nat (sc - 7)) (st_bounces sFx) 0 = (if bv3 =? 0 then 0 else bv3 - 1)).
Proof.
clear HS2 HF DC.
pose proof B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 Hoth3 UB3 SX3 SP3]. pose proof (proj1 (usedX_MT _ _ _ _ Hu3)) as M3e.
pose proof (final_D X U A sc Hsc s3 m3 am3 B3 Hmask) as (HI6 & Hhd6 & Hu6 & M6 & Hfit & Hidx & UB6 & SX6 & _).
rewrite sF_eq in HI6, Hhd6, Hu6, M6, UB6, SX6. change (ctz32 (firstD am3)) with idx3 in HI6.
pose proof am3f_facts as (GS & _ & _ & _ & _ & _ & _ & Esl & Ela & Est).
pose proof (inv_ctx HI3) as (Clen & _ & _ & C4 & _).
assert (SX36 : sameX s3 sFx).
{ unfold sFx, s3f. destruct (hasb && negb (bv3 =? 0)); [| apply (sameX_upd_meta s3 m3 am3); exact M3e].
eapply sameX_trans; [apply (sameX_upd_meta s3 m3 am3); exact M3e | apply sameX_set_bounces; cbn; apply length_zset]. }
assert (Emt : st_metas sFx = st_metas s3f) by (unfold sFx; destruct (hasb && negb (bv3 =? 0)); reflexivity).
repeat match goal with |- _ /\ _ => split end; try assumption.
- intros x Hx. replace (MT sFx x) with (MT s3 x); [exact (RX3 x Hx)|]. unfold MT at 2. rewrite Emt. change (MT s3 x = MT s3f x). unfold s3f. rewrite MT_upd_other; [reflexivity|].
intros ->. pose proof (proj2 (usedX_MT _ _ _ _ Hu3)) as NX. apply (proj2 (memb_In m3 X)) in Hx. rewrite Hx in NX. discriminate.
- rewrite (ub_same_user_blocks A sFx (proj1 (inv_keys HI)) (proj1 (inv_keys HI6)) UB6). symmetry. apply (ub_same_user_blocks A s3 (proj1 (inv_keys HI)) (proj1 (inv_keys HI3)) UB3).
- transitivity (tail_cells s3f); [unfold sFx; destruct (hasb && negb (bv3 =? 0)); reflexivity|].
unfold s3f. pose proof (tail_cellsX_upd_meta [] s3 m3 am3 (am3f am3)) as T. unfold tail_cellsX in T. rewrite !used_metasX_nil in T.
unfold tail_cells. destruct (used_metas_upd s3 m3 am3 M3e) as (u1 & u2 & Eu & Eu'). unfold upd_meta. cbn [st_metas]. fold (upd_meta m3 (MUsed (am3f am3)) s3). rewrite Eu', Eu.
rewrite !flat_map_app. cbn [flat_map snd]. rewrite (group_tail_cells_same am3 (am3f am3) GS). reflexivity.
- apply (fsim_metas s3f); [| exact Emt]. unfold s3f. apply (fsim_upd s3 m3 am3); assumption.
- unfold sFx. destruct (hasb && negb (bv3 =? 0)); cbn; exact Clen.
- unfold sFx. destruct (hasb && negb (bv3 =? 0)); reflexivity.
- intros Hh. unfold sFx. rewrite Hh. cbn [andb]. destruct (bv3 =? 0) eqn:Eb; cbn [negb st_bounces set_bounces].
+ apply Z.eqb_eq in Eb. unfold s3f, upd_meta. cbn [st_bounces]. unfold bv3, bval, bounce_idx in Eb. change ((7 <=? sc) && (sc <? 39)) with hasb in Eb. rewrite Hh in Eb. unfold znth in Eb. exact Eb.
+ unfold zset. rewrite nth_zupd, Nat.eqb_refl. replace (Nat.ltb (Z.to_nat (sc - 7)) (length (st_bounces s3))) with true; [reflexivity|].
symmetry. apply Nat.ltb_lt. rewrite C4. unfold hasb in Hh. apply andb_prop in Hh as [Hh1 Hh2]. apply Z.leb_le in Hh1. apply Z.ltb_lt in Hh2. lia.
Qed.
Lemma postD_memrep : memrepX B X L sFx (ms_mem ms1).
Proof.
pose proof B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 Hoth3 UB3 SX3 SP3]. pose proof (proj1 (usedX_MT _ _ _ _ Hu3)) as M3e.
pose proof sF_facts as (HI6 & Hhd6 & M6 & Hfit & UB6 & SX6 & SX36 & RX6 & UBe & TCe & FS6 & Hlen6 & Ebn & Lbn & Hnth).
pose proof postD_mem as (OUT & HB & HAV & HFR & HBN & Wm & Ws). pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
pose proof m3_factsD as (A1 & A2 & A8 & Aimg & _). pose proof mask_facts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & _).
pose proof am3f_facts as (GS & Fav & Ffr & Fpr & Fnx & Fmem & Fbits & _).
pose proof SX3 as (Erg3 & Ear3 & _). pose proof SX6 as (Erg6 & Ear6 & _). pose proof (proj1 (inv_ctx HI3)) as Hlen3.
assert (Efp : footprint sFx = footprint s3) by (apply footprint_regions_areas; congruence).
refine (memrepX_after B X X None (Some (m3, idx3)) U U s3 sFx L (ms_mem ms) (ms_mem ms1) NEWD [] (sp - ASF, ASF)
HI3 HI6 (HLs s3 (ms_mem ms) MID3) Efp ltac:(congruence) (MRs None s3 (ms_mem ms) HI3 RX3 MID3) _ _ _ _ _ _ _ _).
- intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
+ assert (Hc' : (hasb = true /\ c = cBN) \/ In c (imageX X s3f)).
{ unfold sFx in Hc. destruct hasb eqn:Eh; cbn [andb] in Hc; [|right; exact Hc]. destruct (bv3 =? 0) eqn:Eb; cbn [negb] in Hc; [right; exact Hc|].
destruct (imageX_set_bounces s3f _ c Hc) as [Hcc|Ho]; [|right; exact Ho].
destruct (ctx_cells_set_bounces s3f _ c Hcc) as [(k & Hk & ->)|Ho].
- destruct (Nat.eq_dec k (Z.to_nat (sc - 7))) as [->|Hne].
+ left. split; [reflexivity|]. unfold cBN. rewrite Eb. unfold zset. rewrite nth_zupd, Nat.eqb_refl.
replace (Nat.ltb (Z.to_nat (sc - 7)) (length (st_bounces s3))) with true; [reflexivity|]. symmetry. apply Nat.ltb_lt. rewrite Lbn.
unfold hasb in Eh. apply andb_prop in Eh as [Hh1 Hh2]. apply Z.leb_le in Hh1. apply Z.ltb_lt in Hh2. lia.
+ right. unfold zset. rewrite nth_zupd. replace (Nat.eqb k (Z.to_nat (sc - 7))) with false by (symmetry; apply Nat.eqb_neq; exact Hne). cbn [andb].
unfold imageX. apply in_app_iff. left. change (st_bounces s3) with (st_bounces s3f). apply bcell_In. exact Hk.
- right. unfold imageX. apply in_app_iff. left. exact Ho. }
destruct Hc' as [[Hh ->]|Hc3].
* left. unfold NEWD. rewrite Hh. apply in_app_iff. right. left. reflexivity.
* unfold s3f in Hc3. destruct (imageX_upd_meta X s3 m3 am3 (am3f am3) c M3e GS Hc3) as [Hm|Ho]; [|right; apply in_app_iff; left; exact Ho].
assert (OLD : forall c', In c' (meta_slot_cells m3 (Some (MUsed am3))) -> In c' (imageX X s3 ++ tail_cellsX X s3)).
{ intros c' Hc''. exact (YN0p.old_meta_cell X None U s3 HI3 m3 am3 c' Hu3 Hc''). }
cbn [meta_slot_cells] in Hm. rewrite Fpr, Fnx, Fmem, Fav, Ffr, Fbits in Hm.
destruct Hm as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
[ right; apply OLD; cbn; tauto | right; apply OLD; cbn; tauto | right; apply OLD; cbn; tauto
| left; unfold NEWD; apply in_app_iff; left; right; left; reflexivity
| left; unfold NEWD; apply in_app_iff; left; right; right; left; reflexivity
| right; apply OLD; cbn; tauto ].
+ right. apply in_app_iff. right. unfold tail_cellsX in Hc |- *. rewrite (used_metasX_eq _ sFx HI6 RX6) in Hc. rewrite (used_metasX_eq _ s3 HI3 RX3). fold (tail_cells sFx) in Hc. fold (tail_cells s3). rewrite <- TCe. exact Hc.
- intros c Hc. unfold NEWD in Hc. apply in_app_iff in Hc as [[<-|[<-|[<-|[]]]]|Hc].
+ right. rewrite <- Hhd6. apply hcell_In. exact Hlen6.
+ left. apply (YN2o.meta_cells_in_areas X (Some (m3, idx3)) U sFx HI6 m3 (am3f am3) _ M6). cbn. do 3 right. left. reflexivity.
+ left. apply (YN2o.meta_cells_in_areas X (Some (m3, idx3)) U sFx HI6 m3 (am3f am3) _ M6). cbn. do 4 right. left.
pose proof mask_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kld). unfold cFR. rewrite Kld. reflexivity.
+ destruct hasb eqn:Eh; [|destruct Hc]. destruct Hc as [<-|[]]. right. unfold cBN. rewrite <- (Hnth eq_refl). apply bcell_In.
unfold hasb in Eh. apply andb_prop in Eh as [Hh1 Hh2]. apply Z.leb_le in Hh1. apply Z.ltb_lt in Hh2. lia.
- intros c Hc. unfold NEWD in Hc. apply in_app_iff in Hc as [[<-|[<-|[<-|[]]]]|Hc].
+ apply hcell_mem. cbn [optrZ]. exact HB.
+ unfold cell_mem, cAV. cbn [mc_val mc_loc mc_w sval_num]. rewrite loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_avail. fold M3. intros k Hk. exact (HAV k Hk).
+ unfold cell_mem, cFR. cbn [mc_val mc_loc mc_w sval_num]. rewrite loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_freed. fold M3. intros k Hk. exact (HFR k Hk).
+ destruct hasb eqn:Eh; [|destruct Hc]. destruct Hc as [<-|[]]. unfold cell_mem, cBN, bcell. cbn [mc_val mc_loc mc_w sval_num loc_addr]. rewrite HctxS, (proj1 CTX_eq).
unfold CTX_bounces. rewrite Z2Nat.id by (unfold hasb in Eh; apply andb_prop in Eh as [Hh1 _]; apply Z.leb_le in Hh1; lia).
intros k Hk. pose proof (HBN eq_refl k Hk) as Bk. unfold BA in Bk. etransitivity; [|exact Bk]. f_equal. lia.
- intros c k Hc Hk [p Hp]. unfold NEWD in Hc. apply in_app_iff in Hc as [[<-|[<-|[<-|[]]]]|Hc].
+ exfalso. cbn [hcell act_cell mc_loc] in Hp. discriminate.
+ unfold cAV in Hk |- *. cbn [mc_loc mc_w] in Hk |- *. rewrite loc_addr_padd'. fold M3. unfold META_avail.
apply writable_off_img_present; [lia | | apply Wm; lia]. intros Hi. pose proof (m3_factsD) as (_ & _ & _ & Aoff & _). unfold in_img1 in Hi. lia.
+ unfold cFR in Hk |- *. cbn [mc_loc mc_w] in Hk |- *. rewrite loc_addr_padd'. fold M3. unfold META_freed.
apply writable_off_img_present; [lia | | apply Wm; lia]. intros Hi. pose proof (m3_factsD) as (_ & _ & _ & Aoff & _). unfold in_img1 in Hi. lia.
+ exfalso. destruct hasb; [|destruct Hc]. destruct Hc as [<-|[]]. cbn [cBN bcell mc_loc] in Hp. discriminate.
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. exact (footprint_top s3 e HI3 SX3 (or_intror (ex_intro _ (ms_mem ms) MID3)) He).
- intros a Ha Hno _ Hns.
assert (NH : ~ (YN0j.CTX + 80 + 8 * sc <= a < YN0j.CTX + 80 + 8 * sc + 8)).
{ intros W. apply (Hno (hcell (Some m3)) ltac:(unfold NEWD; apply in_app_iff; left; left; reflexivity)). unfold in_range. rewrite hcell_range. cbn [fst snd]. lia. }
assert (NM : ~ (M3 + 24 <= a < M3 + 32)).
{ intros W. destruct (Z_lt_dec a (M3 + 28)).
- apply (Hno cAV ltac:(unfold NEWD; apply in_app_iff; left; right; left; reflexivity)). unfold in_range, cell_range, cAV. cbn [fst snd mc_loc mc_w]. rewrite loc_addr_padd'. fold M3. unfold META_avail. lia.
- apply (Hno cFR ltac:(unfold NEWD; apply in_app_iff; left; right; right; left; reflexivity)). unfold in_range, cell_range, cFR. cbn [fst snd mc_loc mc_w]. rewrite loc_addr_padd'. fold M3. unfold META_freed. lia. }
assert (NB : ~ (hasb = true /\ a = BA)).
{ intros [Hh ->]. apply (Hno cBN ltac:(unfold NEWD; rewrite Hh; apply in_app_iff; right; left; reflexivity)). unfold in_range, cell_range, cBN, bcell. cbn [fst snd mc_loc mc_w loc_addr].
rewrite HctxS, (proj1 CTX_eq). unfold CTX_bounces, BA. rewrite Z2Nat.id by (unfold hasb in Hh; apply andb_prop in Hh as [Hh1 _]; apply Z.leb_le in Hh1; lia). lia. }
assert (NS : ~ WS regs a) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; lia).
pose proof (OUT a Ha NH NM NB NS) as EQ. split; [apply mbyte_ext1; exact EQ|]. intros [b Hb]. exists b. rewrite EQ. exact Hb.
Qed.
Lemma POST_D : POST X L A regs mem md sc stk g (idx3, sF sc s3 m3 am3) (mkCfg (mkst (ms_regs ms1) (getr regs 1) (ms_mem ms1) rom) md).
Proof.
pose proof (proj1 alloc_ceiling_val) as HCV. pose proof pre_factsS as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof md_factsS as (Mh & Mlz & Mmat). pose proof CTX_eq as CE.
pose proof B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 Hoth3 UB3 SX3 SP3]. pose proof (proj1 (usedX_MT _ _ _ _ Hu3)) as M3e.
pose proof sF_facts as (HI6 & Hhd6 & M6 & Hfit & UB6 & SX6 & SX36 & RX6 & UBe & TCe & FS6 & Hlen6 & _).
pose proof postD_mem as (OUT & HB & HAV & HFR & HBN & Wm & Ws). pose proof postD_regs as (RP & Era & G10 & _).
pose proof m3_factsD as (A1 & A2 & A8 & Aimg & _).
rewrite sF_eq. pose proof SX6 as (Erg & Ear & Eus & Esh & Eama & Ebrk & _).
assert (FRm1 : FRAME (ms_mem ms1)).
{ intros x Hx Hns Hnc Hno. rewrite (OUT x Hx); [exact (FR3 x Hx Hns Hnc Hno) | intros W; apply Hnc; unfold CTX_SIZE; lia | | intros [Hh ->]; apply Hnc; unfold BA, CTX_SIZE, hasb in *; apply andb_prop in Hh as [Hh1 Hh2]; apply Z.leb_le in Hh1; apply Z.ltb_lt in Hh2; lia | exact Hns].
intros W. apply Hno. pose proof SX3 as (Erg3 & Ear3 & _).
apply (alloc_owned_same L A s3 x); [apply footprint_regions_areas; assumption | apply (ub_same_user_blocks A s3 (proj1 (inv_keys HI)) (proj1 (inv_keys HI3)) UB3) |].
apply (YN2u.meta_bytes_owned X None U s3 L HI3 (HLs s3 (ms_mem ms) MID3) m3 _ (MUsed am3) M3e). unfold META_SIZE. fold M3. lia. }
exists L, (ms_regs ms1), (ms_mem ms1), md. split; [reflexivity|]. split.
{ apply (midrep_transport s3 sFx (ms_mem ms) (ms_mem ms1) HI3 RX3 MID3 SX36 RX6 (ex_intro _ (Some (m3, idx3)) HI6) postD_memrep UBe TCe).
intros a Hs. destruct (static_range a Hs) as [R1 R2]. apply OUT; [lia | intros W; apply R2; unfold CTX_SIZE; lia | lia | intros [Hh ->]; apply R2; unfold BA, CTX_SIZE, hasb in *; apply andb_prop in Hh as [Hh1 Hh2]; apply Z.leb_le in Hh1; apply Z.ltb_lt in Hh2; lia | unfold WS; fold sp; pose proof Hstk; unfold ASF in *; lia]. }
split; [unfold ama_ok; cbn [snd]; rewrite Ear, Eama, Erg; exact AMA|].
split; [unfold bounded, usage_of in *; cbn [snd]; rewrite Eus, Esh, Ear; exact BND|].
split.
{ cbn [snd]. intros g' am' i fr Hin Hk. destruct (FS6 g' am' i fr Hin) as (am & Hin' & Hst). unfold reserved_of. rewrite <- Hst. exact (RSV g' am i fr Hin' Hk). }
split; [cbn [snd]; rewrite <- sF_eq; exact (span_F X U A sc s3 m3 am3 B3 SPOK)|].
split; [apply layout_le_refl|]. split; [exact RP|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
{ cbn [snd]. intros x Hx Hnc NO _ _ NS. apply (FRm1 x Hx).
- unfold WS. unfold call_scratch in NS. fold sp. unfold spZ in NS. fold sp in NS. intros W. apply NS. left. lia.
- intros W. apply Hnc. cbn [ms_ctx B]. unfold YN0j.CTX in W. exact W.
- intros W. apply NO. left. exact W. }
split.
{ intros a Ha. unfold call_scratch in Ha. unfold spZ in Ha. fold sp in Ha.
destruct (Z_le_dec (sp - ASF) a) as [L1|L1]; [destruct (Z_lt_dec a sp) as [L2|L2]; [apply Ws; unfold WS; fold sp; lia|]|].
- exfalso. destruct Ha as [Ha|Ha]; [lia|]. pose proof (src0_img_range a (src0_errno_img a Ha)). unfold ERRNO in *. lia.
- assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (src0_img_range a (src0_errno_img a Ha)); lia]).
assert (NERR_static : forall y, ERRNO <= y < ERRNO + 4 -> ~ (YN0j.CTX <= y < YN0j.CTX + CTX_SIZE) /\ ~ alloc_owned L A y).
{ intros y Hy. assert (NC : ~ (YN0j.CTX <= y < YN0j.CTX + CTX_SIZE)) by (unfold ERRNO, src0_tp, YN0j.CTX, CTX_SIZE, src0_D_malloc_context in *; lia).
split; [exact NC|]. intros HO. apply NC. exact (owned_img None A mem HI MID y HO (src0_errno_img y Hy)). }
apply (writable_ext1 mem).
+ apply (FRm1 a Ha64); [unfold WS; fold sp; lia | |]; destruct Ha as [Ha|Ha].
* unfold YN0j.CTX, CTX_SIZE, src0_D_malloc_context. lia.
* exact (proj1 (NERR_static a Ha)).
* intros HO. destruct HO as [(e & He & Hye) _]. pose proof (YN0p.footprint_below X None U L A md HI SO HctxS (mid_ledger _ _ _ _ _ MID) e a He Hye). lia.
* exact (proj2 (NERR_static a Ha)).
+ destruct Ha as [Ha|Ha]; [apply P5; lia | apply P7; exact Ha]. }
split; [cbn [fst]; exact G10|].
split; [cbn [fst snd]; intros _ gg am' Hgg Mgg US; exfalso; rewrite Hhd6 in Hgg; injection Hgg as <-; rewrite M6 in Mgg; injection Mgg as <-; lia|].
split; [cbn [snd]; apply as_keep_same; [intros x Hx _; exact (RX6 x Hx) | exact Ear | exact Erg] | exact postD_guard].
Qed.
End j0.
Theorem stage_D : SR src0segs (mkCfg ms md) (POST X L A regs mem md sc stk g (ctz32 (firstD am3), sF sc s3 m3 am3)).
Proof.
pose proof md_factsS as (Mh & Mlz & _). pose proof pre_factsS as (P1 & _).
assert (V : exists v, dcond v).
{ destruct hasb eqn:Eh; [|exists DV0; exact Eh]. destruct (Z.eq_dec bv3 0); [exists DV1 | exists DV2]; split; auto. }
destruct V as [v DC].
eapply SR_bind; [exact (D_run v DC)|]. intros c2 (ms1 & -> & HS2 & HFr).
pose proof (postD_regs v ms1 DC HS2 HFr) as (RP & Era & G10 & Hra & Hpc & Hrv) || pose proof (postD_regs v ms1 HS2) as (RP & Era & G10 & Hra & Hpc & Hrv).
eapply (SR_final_retS E1d (SSD v) ms1 md); [exact HS2 | exact Hrv | exact Hpc | exact Hra | rewrite Era; exact P1 | exact Mh | exact Mlz |].
rewrite Era. change (ctz32 (firstD am3)) with idx3. first [exact (POST_D v ms1 DC HS2 HFr) | exact (POST_D v ms1 HS2 HFr DC)].
Qed.
End i0.
Lemma ss_hd_mem : ss_mem ss_hd = R_act :: tl (ss_mem ss_hd).
Proof. vm_compute. reflexivity. Qed.
Lemma mem_ok_act_rw E0' m t :
mem_ok src0segs E0' m (R_act :: t) -> (forall o, 88 <= o < 96 -> writable_at src0segs m (base_val E0' (Some 33%nat) + o)) -> mem_ok src0segs E0' m (R_actW (SOff 34 0) :: t).
Proof.
intros (Hwf & Hok & Hpd) Hw. split; [exact Hwf|]. split; [|split; [apply (all_disjoint_ext E0' R_act); [reflexivity..|exact (proj1 Hpd)] | exact (proj2 Hpd)]].
apply Forall_cons; [|exact (Forall_inv_tail Hok)]. destruct (Forall_inv Hok) as (H1 & H2 & _ & H4).
split; [exact H1|]. split; [exact H2|]. split; [exact Hw | exact H4].
Qed.
Definition cP (q : sptr) (v : option sptr) : mcell := MCell (LMem (padd q META_prev)) 8 (optr v).
Definition cN (q : sptr) (v : option sptr) : mcell := MCell (LMem (padd q META_next)) 8 (optr v).
Lemma links_cells q am p nx c : In c (meta_slot_cells q (Some (MUsed (am_set_links p nx am)))) -> c = cP q p \/ c = cN q nx \/ In c (meta_slot_cells q (Some (MUsed am))).
Proof.
intros Hc. destruct am; cbn -[padd META_prev META_next META_mem META_avail META_freed META_bits Z.add Z.mul] in Hc |- *.
destruct Hc as [<-|[<-|Hc]]; [left; reflexivity | right; left; reflexivity | right; right; right; right; exact Hc].
Qed.
Lemma set_prev_links p am : am_set_prev p am = am_set_links p (am_next am) am. Proof. destruct am; reflexivity. Qed.
Lemma set_next_links nx am : am_set_next nx am = am_set_links (am_prev am) nx am. Proof. destruct am; reflexivity. Qed.
Section k0.
Variables (E : env) (ms : machine_state).
Hypothesis HS : st_ok src0segs E ss_hd ms.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis HFm : FRM mem (WS regs) (ms_mem ms).
Lemma MID0 : midrep B L A (ms_mem ms) md.
Proof. exact (midrep_stack X U L A regs mem md stk HI XR AMA MID PRE Hstk (ms_mem ms) HFm). Qed.
Lemma FR0 : FRAME (ms_mem ms).
Proof. intros x Hx Hns _ _. exact (HFm x Hx Hns). Qed.
Lemma RX0 : rawX X A. Proof. exact XR. Qed.
Definition nx0 : sptr := match am_next am0 with Some p => p | None => m0 end.
Definition pr0 : sptr := match am_prev am0 with Some p => p | None => m0 end.
Definition amn0 : ameta := match MT A nx0 with Some (MUsed a) => a | _ => am0 end.
Definition amp0 : ameta := match MT A pr0 with Some (MUsed a) => a | _ => am0 end.
Definition NX0 : Z := ptr_addr L nx0.
Definition PR0 : Z := ptr_addr L pr0.
Lemma lk0 : am_prev am0 = Some pr0 /\ am_next am0 = Some nx0 /\ usedX X A pr0 amp0 /\ usedX X A nx0 amn0 /\ am_sc amp0 = sc /\ am_sc amn0 = sc /\
(nx0 = m0 <-> pr0 = m0) /\ (nx0 <> m0 -> am_freed amn0 <> 0 /\ am_avail amn0 = 0) /\
MT A pr0 = Some (MUsed amp0) /\ MT A nx0 = Some (MUsed amn0).
Proof.
destruct (links0 X U A sc m0 am0 HI Hsc Hhd Mg0) as (pr & nx & ampr & amnx & Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & _).
assert (E1' : nx0 = nx) by (unfold nx0; rewrite Hnx; reflexivity). assert (E2' : pr0 = pr) by (unfold pr0; rewrite Hpr; reflexivity).
assert (E3' : amn0 = amnx) by (unfold amn0; rewrite E1', (proj1 (usedX_MT _ _ _ _ Hun)); reflexivity).
assert (E4' : amp0 = ampr) by (unfold amp0; rewrite E2', (proj1 (usedX_MT _ _ _ _ Hup)); reflexivity).
rewrite E1', E2', E3', E4'. repeat (split; [assumption|]). split; [exact (proj1 (usedX_MT _ _ _ _ Hup)) | exact (proj1 (usedX_MT _ _ _ _ Hun))].
Qed.
Definition E1a : env := ewset (ewset (ewset E aNX0 (Z_to_bv 64 NX0)) aPR0 (Z_to_bv 64 PR0)) aFR0 (Z_to_bv 64 (am_freed am0)).
Lemma E1a_agree : env_agree 40 E E1a.
Proof.
unfold E1a. repeat (eapply env_agree_trans; [| eapply env_agree_le; [| apply env_agree_ewset]; unfold aNX0, aPR0, aFR0; lia]). apply env_agree_refl.
Qed.
Lemma HA1a : env_agree 40 E00 E1a.
Proof. eapply env_agree_trans; [exact HA | apply E1a_agree]. Qed.
Lemma E1a_vals : ew E1a aNX0 = Z_to_bv 64 NX0 /\ ew E1a aPR0 = Z_to_bv 64 PR0 /\ ew E1a aFR0 = Z_to_bv 64 (am_freed am0) /\ ew E1a 34 = Z_to_bv 64 M0.
Proof.
unfold E1a, aNX0, aPR0, aFR0. repeat split; rewrite ?ew_ewset_same; try reflexivity; rewrite !ew_ewset_other by lia; rewrite ?ew_ewset_same; try reflexivity.
pose proof (agree_cs L A regs sc g 0 M0 E1a 34 HA1a ltac:(lia)) as E34. cbn [cs] in E34. rewrite Hhd in E34. exact E34.
Qed.
Lemma m0_factsA :
4096 <= M0 /\ M0 + 40 <= alloc_ceiling /\ M0 mod 8 = 0 /\ (M0 + 40 <= 0x10000 \/ 0x51000 <= M0) /\ (forall x, M0 <= x < M0 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (M0 + 0) 8 PR0 /\ bytes_are (ms_mem ms) (M0 + 8) 8 NX0 /\ bytes_are (ms_mem ms) (M0 + 24) 4 0 /\ bytes_are (ms_mem ms) (M0 + 28) 4 (am_freed am0) /\
0 <= am_freed am0 < 2 ^ 32 /\
4096 <= NX0 /\ NX0 + 40 <= alloc_ceiling /\ NX0 mod 8 = 0 /\ (NX0 + 40 <= 0x10000 \/ 0x51000 <= NX0) /\ (forall x, NX0 <= x < NX0 + 40 -> present (ms_mem ms) x) /\
4096 <= PR0 /\ PR0 + 40 <= alloc_ceiling /\ PR0 mod 8 = 0 /\ (PR0 + 40 <= 0x10000 \/ 0x51000 <= PR0) /\ (forall x, PR0 <= x < PR0 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (YN0j.CTX + 80 + 8 * sc) 8 M0 /\
(nx0 <> m0 -> M0 + 40 <= NX0 \/ NX0 + 40 <= M0) /\ (pr0 <> m0 -> M0 + 40 <= PR0 \/ PR0 + 40 <= M0) /\ (pr0 <> nx0 -> NX0 + 40 <= PR0 \/ PR0 + 40 <= NX0).
Proof.
pose proof m0_facts as (Hu0 & Hs0 & _). pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). pose proof (proj1 alloc_ceiling_val). pose proof MID0 as MID0'.
pose proof (metaS None A (ms_mem ms) HI XR MID0' m0 am0 Hu0) as (A1 & A2 & A3 & A4 & A5 & B0 & B8 & _ & B24 & B28 & _ & _ & R2 & _).
pose proof (metaS None A (ms_mem ms) HI XR MID0' nx0 amn0 Hun) as (C1 & C2 & C3 & C4 & C5 & _).
pose proof (metaS None A (ms_mem ms) HI XR MID0' pr0 amp0 Hup) as (D1 & D2 & D3 & D4 & D5 & _).
pose proof (headS None A (ms_mem ms) HI XR MID0') as HD. rewrite Hhd in HD. cbn [optrZ] in HD.
rewrite Hpr in B0. rewrite Hnx in B8. cbn [optrZ] in B0, B8. rewrite Hav0 in B24.
unfold M0, NX0, PR0 in *. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- apply (YN0p.off_img _ A4).
- apply (YN0p.off_img _ C4).
- apply (YN0p.off_img _ D4).
- intros Hne. apply (apartS None A (ms_mem ms) HI MID0' m0 nx0 am0 amn0 Hu0 Hun). intros Heq. exact (Hne (eq_sym Heq)).
- intros Hne. apply (apartS None A (ms_mem ms) HI MID0' m0 pr0 am0 amp0 Hu0 Hup). intros Heq. exact (Hne (eq_sym Heq)).
- intros Hne. apply (apartS None A (ms_mem ms) HI MID0' nx0 pr0 amn0 amp0 Hun Hup). intros Heq. exact (Hne (eq_sym Heq)).
Qed.
Lemma valsA : sv_denot E1a (SOff 34 0) = Z_to_bv 64 M0 /\ sv_denot E1a (SOff aNX0 0) = Z_to_bv 64 NX0 /\ sv_denot E1a (SOff aPR0 0) = Z_to_bv 64 PR0 /\
bv_unsigned (sv_denot E1a (SExt true 32 (SOff aFR0 0))) = sx32 (am_freed am0).
Proof.
pose proof m0_factsA as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & Fr & C1 & C2 & _ & _ & _ & D1 & D2 & _). pose proof (proj1 alloc_ceiling_val).
destruct E1a_vals as (V40 & V41 & V42 & V34).
split; [apply (den_atom0 E1a 34 _ V34); lia|]. split; [apply (den_atom0 E1a aNX0 _ V40); lia|]. split; [apply (den_atom0 E1a aPR0 _ V41); lia|].
rewrite U_sext32'. rewrite (den_atom0 E1a aFR0 _ V42) by lia. rewrite lit64_small by lia. reflexivity.
Qed.
Inductive avar := AV1 | AV2 | AV3.
Definition ssA (v : avar) : sstate := match v with AV1 => ss_AR1 | AV2 => ss_AD2 | AV3 => ss_AD3 end.
Definition SSA (v : avar) : sstate := match v with AV1 => SSA_R1 | AV2 => SSA_D2 | AV3 => SSA_D3 end.
Definition acase (v : avar) : Prop :=
match v with
| AV1 => am_freed am0 <> 0
| AV2 => am_freed am0 = 0 /\ nx0 <> m0 /\ pr0 = nx0
| AV3 => am_freed am0 = 0 /\ nx0 <> m0 /\ pr0 <> nx0
end.
Lemma A_st_ok v : acase v -> st_ok src0segs E1a (ssA v) ms.
Proof.
intros AC. pose proof (proj1 alloc_ceiling_val) as ACV. pose proof CTX_eq as CE.
pose proof m0_factsA as (A1 & A2 & A8 & Aimg & Apres & B0 & B8 & B24 & B28 & Fr & C1 & C2 & C8 & Cimg & Cpres & D1 & D2 & D8 & Dimg & Dpres & HD & AP1 & AP2 & AP3).
destruct E1a_vals as (V40 & V41 & V42 & V34). pose proof valsA as (W34 & W40 & W41 & Wfr). pose proof lk0 as (_ & _ & _ & _ & _ & _ & Hiff & _).
pose proof (st_ok_agree src0segs 40 E E1a ss_hd ms HS E1a_agree ss_hd_atoms) as HS1.
pose proof (st_ok_mem_ok src0segs E1a ss_hd ms HS1) as MOK. rewrite ss_hd_mem in MOK.
pose proof (agree_facts E1a HA1a) as (_ & _ & B33 & B2 & _).
assert (BASE : mem_ok src0segs E1a (ms_mem ms) (R_actW (SOff 34 0) :: tl (ss_mem ss_hd))).
{ apply (mem_ok_act_rw E1a _ _ MOK). intros o Ho. rewrite B33. apply (ctx_writableS (ms_mem ms)). unfold CTX_SIZE. lia. }
destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (Sat & Scd & Sal)).
assert (BD : forall r' lo hi, In r' (R_actW (SOff 34 0) :: tl (ss_mem ss_hd)) -> 4096 <= lo -> hi <= alloc_ceiling -> (hi <= 0x10000 \/ 0x51000 <= lo) -> hi <= base_val E1a (r_base r') + r_lo r' \/ base_val E1a (r_base r') + r_hi r' <= lo).
{ intros r' lo hi Hr'. apply (base_disjoint E1a r' lo hi HA1a). destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]. }
assert (Dm0 : forall rr, r_base rr = Some 34%nat -> r_lo rr = 0 -> r_hi rr = 40 -> forall r', In r' (R_actW (SOff 34 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1a rr r').
{ intros rr Hb Hl Hh r' Hr'. unfold extent_disjoint. rewrite Hb, Hl, Hh, (base_atom E1a 34 M0 V34) by lia. destruct (BD r' M0 (M0 + 40) Hr' ltac:(lia) ltac:(lia) Aimg); lia. }
assert (Dnx : forall rr, r_base rr = Some aNX0 -> r_lo rr = 0 -> r_hi rr = 40 -> forall r', In r' (R_actW (SOff 34 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1a rr r').
{ intros rr Hb Hl Hh r' Hr'. unfold extent_disjoint. rewrite Hb, Hl, Hh, (base_atom E1a aNX0 NX0 V40) by lia. destruct (BD r' NX0 (NX0 + 40) Hr' ltac:(lia) ltac:(lia) Cimg); lia. }
assert (Dpr : forall rr, r_base rr = Some aPR0 -> r_lo rr = 0 -> r_hi rr = 40 -> forall r', In r' (R_actW (SOff 34 0) :: tl (ss_mem ss_hd)) -> extent_disjoint E1a rr r').
{ intros rr Hb Hl Hh r' Hr'. unfold extent_disjoint. rewrite Hb, Hl, Hh, (base_atom E1a aPR0 PR0 V41) by lia. destruct (BD r' PR0 (PR0 + 40) Hr' ltac:(lia) ltac:(lia) Dimg); lia. }
assert (ATOMS : forall extra, (forall k f, In (k, f) extra -> In (k, f) [FM 34; FM aNX0; FM aPR0] \/ ((k, f) = FNZ aFR0 /\ am_freed am0 <> 0)) -> atoms_ok E1a (extra ++ f_atoms (ss_facts ss_hd))).
{ intros extra Hex. induction extra as [|[k f] extra IH]; [exact Sat|]. cbn [app atoms_ok]. split; [| apply IH; intros k' f' H'; apply Hex; right; exact H'].
destruct (Hex k f (or_introl eq_refl)) as [Hin|[Ekf Hfr0]]; [cbn [In] in Hin; destruct Hin as [Ekf|[Ekf|[Ekf|[]]]] |]; unfold FM, FNZ in Ekf; injection Ekf as E1k E2f; subst k f;
unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?V34, ?V40, ?V41, ?V42, !lit64_small by lia.
- change (2 ^ 3) with 8. lia.
- change (2 ^ 3) with 8. lia.
- change (2 ^ 3) with 8. lia.
- change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (Chd : acond_ok E1a C_hd1) by (unfold acond_ok; cbn [ac_c ac_a ac_b C_hd1]; rewrite branch_ne, W34; cbn [sv_denot]; rewrite (lit64_small M0), (lit64_small 0) by lia; destruct (Z.eqb_spec M0 0); [lia | reflexivity]).
assert (Cfr : am_freed am0 <> 0 -> acond_ok E1a C_fr0).
{ intros Hne. unfold acond_ok; cbn [ac_c ac_a ac_b C_fr0]. rewrite branch_ne, Wfr. cbn [sv_denot]. rewrite (lit64_small 0) by lia.
destruct (Z.eqb_spec (sx32 (am_freed am0)) 0) as [Ee|]; [exfalso; exact (sx32_nonzero_u32 (am_freed am0) ltac:(lia) Ee) | reflexivity]. }
assert (Cnx : nx0 <> m0 -> acond_ok E1a C_nx0).
{ intros Hne. unfold acond_ok; cbn [ac_c ac_a ac_b C_nx0]. rewrite branch_ne, W40, W34, !lit64_small by lia. destruct (AP1 Hne); destruct (Z.eqb_spec NX0 M0); try reflexivity; lia. }
assert (Rm0r : region_ok src0segs E1a (ms_mem ms) R_m0r).
{ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m0r]; rewrite (base_atom E1a 34 M0 V34) by lia; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_ok_val' E1a _ _ _ 8 _ NX0); [rewrite W40; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B8].
- apply (chunk_ok_val' E1a _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B24].
- apply (chunk_ok_val' E1a _ _ _ 4 _ (am_freed am0)); [rewrite (den_atom0 E1a aFR0 _ V42) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B28]. }
assert (Rm0d : forall prv, sv_denot E1a prv = Z_to_bv 64 PR0 -> am_freed am0 = 0 -> region_ok src0segs E1a (ms_mem ms) (R_m0d prv)).
{ intros prv Hprv Hfr0. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m0d]; rewrite (base_atom E1a 34 M0 V34) by lia; [lia | lia | intros o Ho; apply present_writable; apply Apres; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_ok_val' E1a _ _ _ 8 _ PR0); [rewrite Hprv; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B0].
- apply (chunk_ok_val' E1a _ _ _ 8 _ NX0); [rewrite W40; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B8].
- apply (chunk_ok_val' E1a _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B24].
- apply (chunk_ok_val' E1a _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | rewrite <- Hfr0; exact B28]. }
assert (Rw : forall k base wlo whi, (k = aNX0 /\ base = NX0) \/ (k = aPR0 /\ base = PR0) -> 0 <= wlo -> whi <= 40 -> region_ok src0segs E1a (ms_mem ms) (YP09.mkRegion (Some k) 0 40 wlo whi [])).
{ intros k base wlo whi Hk Hwlo Hwhi.
assert (Hb : base_val E1a (Some k) = base /\ forall x, base <= x < base + 40 -> present (ms_mem ms) x) by (destruct Hk as [[-> ->]|[-> ->]]; split; [apply (base_atom E1a aNX0 NX0 V40); lia | exact Cpres | apply (base_atom E1a aPR0 PR0 V41); lia | exact Dpres]).
destruct Hb as [Hb Hp]. apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite Hb; [destruct Hk as [[_ ->]|[_ ->]]; lia | destruct Hk as [[_ ->]|[_ ->]]; lia | intros o Ho; apply present_writable; apply Hp; lia | apply Forall_nil]. }
destruct v; cbn [acase] in AC; unfold st_ok, ssA, ss_AR1, ss_AD2, ss_AD3; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts];
(split; [exact S1|]; split; [exact S2|]; split; [exact S3|]; split; [exact S4|]; split; [exact S5|]; split; [exact S6|]; split; [exact S7|]; split).
- cbn [app]. apply mem_ok_cons'; [reflexivity | exact Rm0r | apply Dm0; reflexivity | exact BASE].
- split; [apply ATOMS; intros k f Hin; cbn [In] in Hin; destruct Hin as [H|[H|[H|[]]]]; [left; rewrite <- H; left; reflexivity | left; rewrite <- H; right; left; reflexivity | right; split; [symmetry; exact H | exact AC]] |].
split; [| exact I]. split; [exact Chd|]. split; [apply Cfr; exact AC | exact I].
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply Rm0d; [rewrite W40; unfold NX0, PR0; rewrite (proj2 (proj2 AC)); reflexivity | exact (proj1 AC)] | | apply mem_ok_cons'; [reflexivity | apply (Rw aNX0 NX0); [left; auto | lia | lia] | apply Dnx; reflexivity | exact BASE]].
intros r' [<-|Hr']; [| apply Dm0; [reflexivity..| exact Hr']]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_m0d R_m1d2]. rewrite (base_atom E1a 34 M0 V34), (base_atom E1a aNX0 NX0 V40) by lia. destruct (AP1 (proj1 (proj2 AC))); lia.
- split; [apply ATOMS; intros k f Hin; cbn [In] in Hin; destruct Hin as [H|[H|[]]]; left; rewrite <- H; [left | right; left]; reflexivity |].
split; [| exact I]. split; [exact Chd|]. split; [apply Cnx; exact (proj1 (proj2 AC)) | exact I].
- cbn [app]. apply mem_ok_cons'; [reflexivity | apply Rm0d; [exact W41 | exact (proj1 AC)] | | apply mem_ok_cons'; [reflexivity | apply (Rw aPR0 PR0); [right; auto | lia | lia] | | apply mem_ok_cons'; [reflexivity | apply (Rw aNX0 NX0); [left; auto | lia | lia] | apply Dnx; reflexivity | exact BASE]]].
+ intros r' [<-|[<-|Hr']]; [| | apply Dm0; [reflexivity..| exact Hr']]; unfold extent_disjoint; cbn [r_base r_lo r_hi R_m0d R_prd3 R_nxd3];
rewrite (base_atom E1a 34 M0 V34), ?(base_atom E1a aPR0 PR0 V41), ?(base_atom E1a aNX0 NX0 V40) by lia.
* assert (Hpm : pr0 <> m0) by (intros Ep; apply (proj1 (proj2 AC)); apply (proj2 Hiff); exact Ep). destruct (AP2 Hpm); lia.
* destruct (AP1 (proj1 (proj2 AC))); lia.
+ intros r' [<-|Hr']; [| apply Dpr; [reflexivity..| exact Hr']]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_prd3 R_nxd3]. rewrite (base_atom E1a aPR0 PR0 V41), (base_atom E1a aNX0 NX0 V40) by lia. destruct (AP3 (proj2 (proj2 AC))); lia.
- split; [apply ATOMS; intros k f Hin; cbn [In] in Hin; destruct Hin as [H|[H|[H|[]]]]; left; rewrite <- H; [left | right; left | right; right; left]; reflexivity |].
split; [| exact I]. split; [exact Chd|]. split; [apply Cnx; exact (proj1 (proj2 AC)) | exact I].
Qed.
Definition s1v (v : avar) : astate :=
match v with AV1 => sA_rot A sc nx0 | AV2 => sA_D2 A sc m0 am0 nx0 amn0 | AV3 => sA_D3 A sc m0 am0 pr0 nx0 amp0 amn0 end.
Lemma stepA_v v : acase v -> STEP_A sc m0 am0 A = IRet (Some nx0, s1v v).
Proof.
intros AC. pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). destruct v; cbn [acase s1v] in *.
- exact (stepA_R1 A sc m0 am0 nx0 AC Hnx).
- destruct AC as (Hfr & Hne & Epn). apply (stepA_D2 X U A sc m0 am0 HI Hsc Hhd Mg0 nx0 amn0 Hfr); [rewrite <- Epn; exact Hpr | exact Hnx | exact Hne | exact Mn].
- destruct AC as (Hfr & Hne & Hpn). apply (stepA_D3 X U A sc m0 am0 HI Hsc Hhd Mg0 pr0 nx0 amp0 amn0 Hfr Hpr Hnx Hne); [intros Ep; apply Hne; apply (proj2 Hiff); exact Ep | exact Hpn | exact Mp | exact Mn].
Qed.
Lemma s1_same v : acase v -> sameX A (s1v v).
Proof.
intros AC. pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). destruct v; cbn [acase s1v] in *.
- apply sameX_R1.
- apply (sameX_D2 A sc m0 am0 Mg0 nx0 amn0 Mn (proj1 (proj2 AC))).
- apply (sameX_D3 A sc m0 am0 Mg0 pr0 nx0 amp0 amn0 Mp Mn (proj1 (proj2 AC))); [intros Ep; apply (proj1 (proj2 AC)); apply (proj2 Hiff); exact Ep | exact (proj2 (proj2 AC))].
Qed.
Lemma s1_span v : acase v -> span_ok A -> span_ok (s1v v).
Proof.
intros AC. pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). destruct v; cbn [acase s1v] in *.
- apply span_R1.
- apply (span_D2 A sc m0 am0 Mg0 nx0 amn0 Mn (proj1 (proj2 AC))).
- apply (span_D3 A sc m0 am0 Mg0 pr0 nx0 amp0 amn0 Mp Mn (proj1 (proj2 AC))); [intros Ep; apply (proj1 (proj2 AC)); apply (proj2 Hiff); exact Ep | exact (proj2 (proj2 AC))].
Qed.
Lemma A_run v : acase v ->
SR src0segs (mkCfg ms md) (fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E1a (SSA v) ms1 /\ frame_of E1a (ss_mem (ssA v)) (ms_mem ms) (ms_mem ms1)).
Proof.
intros AC. pose proof md_factsS as (Mh & Mlz & _). pose proof (A_st_ok v AC) as HS0.
assert (RUN : run_to_ok PS_B (ssA v) (fst (sym_run_toN src0segs src0tbl FUEL PS_B (ssA v)))) by (destruct v; [apply AR1_run_ok | apply AD2_run_ok | apply AD3_run_ok]).
eapply SR_mono; [eapply (SR_run_to PS_B); [exact HS0 | exact RUN | exact Mh | exact Mlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
assert (EE : SSA v = closeF (ssA v) PS_B) by (destruct v; symmetry; [apply SSA_R1_eq | apply SSA_D2_eq | apply SSA_D3_eq]).
rewrite EE. unfold closeF. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS0)].
Qed.
Definition wrA (v : avar) (x : Z) : Prop :=
match v with
| AV1 => False
| AV2 => (M0 <= x < M0 + 16) \/ (NX0 <= x < NX0 + 16)
| AV3 => (M0 <= x < M0 + 16) \/ (PR0 + 8 <= x < PR0 + 16) \/ (NX0 <= x < NX0 + 8)
end.
Definition NEWA (v : avar) : list mcell :=
match v with
| AV1 => [hcell (Some nx0)]
| AV2 => [hcell (Some nx0); cP m0 None; cN m0 None; cP nx0 (Some nx0); cN nx0 (Some nx0)]
| AV3 => [hcell (Some nx0); cP m0 None; cN m0 None; cN pr0 (Some nx0); cP nx0 (Some pr0)]
end.
Section l0.
Variables (v : avar) (ms1 : machine_state).
Hypothesis AC : acase v.
Hypothesis HS2 : st_ok src0segs E1a (SSA v) ms1.
Hypothesis HF : frame_of E1a (ss_mem (ssA v)) (ms_mem ms) (ms_mem ms1).
Lemma postA_regs : getr (ms_regs ms1) 10 = Z_to_bv 64 NX0 /\ ms_pc_val ms1 = Z_to_bv 64 PS_B.
Proof.
pose proof valsA as (W34 & W40 & W41 & Wfr).
pose proof (st_ok_reg src0segs E1a (SSA v) ms1 10 HS2) as R10'. destruct HS2 as (_ & SPC & _).
assert (E10 : sr_get (ss_regs (SSA v)) 10 = SOff aNX0 0) by (destruct v; [exact (proj2 SSA_R1_shape) | exact (proj2 SSA_D2_shape) | exact (proj2 SSA_D3_shape)]).
assert (EPC : ss_pc (SSA v) = PS_B) by (destruct v; vm_compute; reflexivity).
rewrite E10 in R10'. rewrite R10', SPC, EPC. split; [exact W40 | reflexivity].
Qed.
Lemma postA_mem :
(forall x, 0 <= x < 2 ^ 64 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ wrA v x -> ~ WS regs x ->
(ms_mem ms1) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x)) /\
bytes_are (ms_mem ms1) (YN0j.CTX + 80 + 8 * sc) 8 NX0 /\
(v <> AV1 -> bytes_are (ms_mem ms1) (M0 + 0) 8 0 /\ bytes_are (ms_mem ms1) (M0 + 8) 8 0 /\ forall a, M0 <= a < M0 + 16 -> writable_at src0segs (ms_mem ms1) a) /\
(v = AV2 -> bytes_are (ms_mem ms1) (NX0 + 0) 8 NX0 /\ bytes_are (ms_mem ms1) (NX0 + 8) 8 NX0 /\ forall a, NX0 <= a < NX0 + 16 -> writable_at src0segs (ms_mem ms1) a) /\
(v = AV3 -> bytes_are (ms_mem ms1) (PR0 + 8) 8 NX0 /\ bytes_are (ms_mem ms1) (NX0 + 0) 8 PR0 /\
(forall a, PR0 + 8 <= a < PR0 + 16 -> writable_at src0segs (ms_mem ms1) a) /\ (forall a, NX0 <= a < NX0 + 8 -> writable_at src0segs (ms_mem ms1) a)).
Proof.
pose proof valsA as (W34 & W40 & W41 & Wfr). destruct E1a_vals as (V40 & V41 & V42 & V34).
pose proof (agree_facts E1a HA1a) as (_ & _ & B33 & B2 & _). pose proof m0_factsA as (A1 & A2 & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & _ & _ & _ & D1 & D2 & _). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
pose proof (st_ok_mem_ok src0segs E1a (SSA v) ms1 HS2) as (_ & MOK & _).
assert (RD : forall r o (w : N) e val, In r (ss_mem (SSA v)) -> In (mkChunk o (CVal w e)) (r_chunks r) -> bv_unsigned (sv_denot E1a e) = val -> 0 <= val < 2 ^ (8 * Z.of_N w) ->
bytes_are (ms_mem ms1) (base_val E1a (r_base r) + o) (N.to_nat w) val).
{ intros r o w e val Hr Hc Hv Hrange. pose proof (proj1 (Forall_forall _ _) MOK _ Hr) as (_ & _ & _ & CH).
rewrite <- (Z.mod_small val (2 ^ (8 * Z.of_N w))) by exact Hrange. apply (chunk_bytes' E1a _ _ _ w e); [exact (proj1 (Forall_forall _ _) CH _ Hc) | exact Hv]. }
assert (WR : forall r o, In r (ss_mem (SSA v)) -> r_wlo r <= o < r_whi r -> writable_at src0segs (ms_mem ms1) (base_val E1a (r_base r) + o)).
{ intros r o Hr Ho. pose proof (proj1 (Forall_forall _ _) MOK _ Hr) as (_ & _ & W & _). exact (W o Ho). }
assert (U0 : bv_unsigned (sv_denot E1a (SLit 0)) = 0) by (cbn [sv_denot]; apply lit64_small; lia).
assert (U40 : bv_unsigned (sv_denot E1a (SOff aNX0 0)) = NX0) by (rewrite W40; apply lit64_small; lia).
assert (U41 : bv_unsigned (sv_denot E1a (SOff aPR0 0)) = PR0) by (rewrite W41; apply lit64_small; lia).
pose proof (base_atom E1a 34 M0 V34 ltac:(lia)) as B34. pose proof (base_atom E1a aNX0 NX0 V40 ltac:(lia)) as B40. pose proof (base_atom E1a aPR0 PR0 V41 ltac:(lia)) as B41.
split; [|split; [|split; [|split]]].
- intros x Hx Hnh Hnw Hns. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw.
assert (Hw' : exists rs, (forall r, In r rs -> (r_wlo r = 0 /\ r_whi r = 0) \/ (forall y, base_val E1a (r_base r) + r_wlo r <= y < base_val E1a (r_base r) + r_whi r -> wrA v y)) /\
in_wrange E1a (rs ++ R_actW (SOff 34 0) :: tl (ss_mem ss_hd)) x).
{ destruct v; cbn [ssA ss_AR1 ss_AD2 ss_AD3 ss_mem] in Hw; [exists [R_m0r] | exists [R_m0d (SOff aNX0 0); R_m1d2] | exists [R_m0d (SOff aPR0 0); R_prd3; R_nxd3]];
(split; [| cbn [app]; exact Hw]); intros r Hr; cbn [In] in Hr; decompose [or] Hr; try contradiction; subst r;
first [left; split; reflexivity | right; cbn [r_base r_wlo r_whi R_m0d R_m1d2 R_prd3 R_nxd3 wrA]; rewrite ?B34, ?B40, ?B41; intros y Hy; lia]. }
clear Hw. destruct Hw' as (rs & Hrs & Hw). destruct (wrange_cases E1a rs _ x HA1a Hw) as [(r & Hin & Hr)|[Hh|Hs']]; [| exact (Hnh Hh) | exact (Hns Hs')].
destruct (Hrs r Hin) as [[E1' E2']|Hy]; [rewrite E1', E2' in Hr; lia | exact (Hnw (Hy x Hr))].
- assert (Hin : In (R_actW (SOff aNX0 0)) (ss_mem (SSA v))) by (destruct v; cbn [SSA]; [rewrite (proj1 SSA_R1_shape) | rewrite (proj1 SSA_D2_shape) | rewrite (proj1 SSA_D3_shape)]; apply in_app_iff; left; cbn; auto).
pose proof (RD _ 88 8%N (SOff aNX0 0) NX0 Hin ltac:(left; reflexivity) U40 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base R_actW] in R. rewrite B33 in R.
replace (YN0j.CTX + 80 + 8 * sc) with (YN0j.LOCK + 8 * sc + 88) by lia. exact R.
- intros Hv. assert (Hin : In (R_m0z 0 16) (ss_mem (SSA v))) by (destruct v; cbn [SSA]; [exfalso; exact (Hv eq_refl) | rewrite (proj1 SSA_D2_shape) | rewrite (proj1 SSA_D3_shape)]; left; reflexivity).
split; [|split].
+ pose proof (RD _ 0 8%N (SLit 0) 0 Hin ltac:(cbn; auto) U0 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base R_m0z] in R. rewrite B34 in R. exact R.
+ pose proof (RD _ 8 8%N (SLit 0) 0 Hin ltac:(cbn; auto) U0 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base R_m0z] in R. rewrite B34 in R. exact R.
+ intros a Ha. replace a with (base_val E1a (r_base (R_m0z 0 16)) + (a - M0)) by (cbn [r_base R_m0z]; rewrite B34; lia). apply WR; [exact Hin | cbn [r_wlo r_whi R_m0z]; lia].
- intros ->.
set (r1 := YP09.mkRegion (Some aNX0) 0 40 0 16 [mkChunk 0 (CVal 8 (SOff aNX0 0)); mkChunk 8 (CVal 8 (SOff aNX0 0))]).
assert (Hin : In r1 (ss_mem SSA_D2)) by (rewrite (proj1 SSA_D2_shape); right; left; reflexivity).
split; [|split].
+ pose proof (RD _ 0 8%N (SOff aNX0 0) NX0 Hin ltac:(cbn; auto) U40 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base r1] in R. rewrite B40 in R. exact R.
+ pose proof (RD _ 8 8%N (SOff aNX0 0) NX0 Hin ltac:(cbn; auto) U40 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base r1] in R. rewrite B40 in R. exact R.
+ intros a Ha. replace a with (base_val E1a (r_base r1) + (a - NX0)) by (cbn [r_base r1]; rewrite B40; lia). apply WR; [exact Hin | unfold r1; cbn [r_wlo r_whi]; lia].
- intros ->.
set (rp := YP09.mkRegion (Some aPR0) 0 40 8 16 [mkChunk 8 (CVal 8 (SOff aNX0 0))]). set (rn := YP09.mkRegion (Some aNX0) 0 40 0 8 [mkChunk 0 (CVal 8 (SOff aPR0 0))]).
assert (Hinp : In rp (ss_mem SSA_D3)) by (rewrite (proj1 SSA_D3_shape); right; left; reflexivity).
assert (Hinn : In rn (ss_mem SSA_D3)) by (rewrite (proj1 SSA_D3_shape); right; right; left; reflexivity).
split; [|split; [|split]].
+ pose proof (RD _ 8 8%N (SOff aNX0 0) NX0 Hinp ltac:(cbn; auto) U40 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base rp] in R. rewrite B41 in R. exact R.
+ pose proof (RD _ 0 8%N (SOff aPR0 0) PR0 Hinn ltac:(cbn; auto) U41 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)) as R. cbn [r_base rn] in R. rewrite B40 in R. exact R.
+ intros a Ha. replace a with (base_val E1a (r_base rp) + (a - PR0)) by (cbn [r_base rp]; rewrite B41; lia). apply WR; [exact Hinp | unfold rp; cbn [r_wlo r_whi]; lia].
+ intros a Ha. replace a with (base_val E1a (r_base rn) + (a - NX0)) by (cbn [r_base rn]; rewrite B40; lia). apply WR; [exact Hinn | unfold rn; cbn [r_wlo r_whi]; lia].
Qed.
Lemma s1_facts : rawX X (s1v v) /\ fsim (s1v v) /\ tail_cells (s1v v) = tail_cells A /\ length (st_active (s1v v)) = 48%nat /\
MT (s1v v) m0 = Some (MUsed (match v with AV1 => am0 | _ => am0' am0 end)) /\
(v = AV2 -> MT (s1v v) nx0 = Some (MUsed (am_set_links (Some nx0) (Some nx0) amn0))) /\
(v = AV3 -> MT (s1v v) nx0 = Some (MUsed (am_set_prev (Some pr0) amn0)) /\ MT (s1v v) pr0 = Some (MUsed (am_set_next (Some nx0) amp0))).
Proof.
clear HS2 HF. pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). pose proof m0_facts as (Hu0 & _).
pose proof (proj2 (usedX_MT _ _ _ _ Hu0)) as NX0'. pose proof (proj2 (usedX_MT _ _ _ _ Hun)) as NXn. pose proof (proj2 (usedX_MT _ _ _ _ Hup)) as NXp.
pose proof (proj1 (inv_ctx HI)) as Hlen.
assert (NIn : forall q, memb q X = false -> forall x, In x X -> x <> q) by (intros q Hq x Hx ->; apply (proj2 (memb_In q X)) in Hx; rewrite Hx in Hq; discriminate).
assert (TC : forall s0 q am am', MT s0 q = Some (MUsed am) -> grp_same am am' -> tail_cells (upd_meta q (MUsed am') s0) = tail_cells s0).
{ intros s0 q am am' Mq GS. unfold tail_cells. destruct (used_metas_upd s0 q am Mq) as (u1 & u2 & Eu & Eu'). unfold upd_meta. cbn [st_metas]. fold (upd_meta q (MUsed am') s0).
rewrite Eu', Eu, !flat_map_app. cbn [flat_map snd]. rewrite (group_tail_cells_same am am' GS). reflexivity. }
assert (GL : forall p n am, grp_same am (am_set_links p n am)) by (intros; apply grp_same_links).
destruct v; cbn [s1v acase] in AC |- *.
-   unfold sA_rot, hd_upd. split; [intros x Hx; rewrite MT_set_active; exact (XR x Hx)|]. split; [apply (fsim_metas A); [apply fsim_refl | reflexivity]|].
split; [reflexivity|]. split; [cbn; rewrite length_lupd; exact Hlen|]. split; [rewrite MT_set_active; exact Mg0|]. split; intros; discriminate.
-   destruct AC as (Hfr & Hne & Epn). unfold sA_D2, hd_upd.
assert (Hnm : nx0 <> m0) by exact Hne. assert (Hmn : m0 <> nx0) by (intros EE; exact (Hnm (eq_sym EE))).
split; [intros x Hx; rewrite MT_upd_other by exact (NIn _ NX0' x Hx); rewrite MT_set_active, MT_upd_other by exact (NIn _ NXn x Hx); exact (XR x Hx)|].
split.
{ apply (fsim_upd _ m0 am0); [apply (fsim_metas (upd_meta nx0 (MUsed (am_set_links (Some nx0) (Some nx0) amn0)) A)); [apply (fsim_upd A nx0 amn0); [apply fsim_refl | exact Mn | destruct amn0; reflexivity..] | reflexivity] | rewrite MT_set_active, MT_upd_other by exact Hmn; exact Mg0 | destruct am0; reflexivity..]. }
split; [rewrite (TC _ m0 am0); [cbn [upd_meta set_active st_metas]; change (tail_cells (set_active ?l ?s0)) with (tail_cells s0); apply (TC A nx0 amn0); [exact Mn | apply GL] | rewrite MT_set_active, MT_upd_other by exact Hmn; exact Mg0 | unfold am0'; apply GL]|].
split; [cbn; rewrite length_lupd; exact Hlen|]. split; [apply MT_upd_same|]. split; [intros _; rewrite MT_upd_other by exact Hnm; rewrite MT_set_active; apply MT_upd_same | intros; discriminate].
-   destruct AC as (Hfr & Hne & Hpn). unfold sA_D3, hd_upd.
assert (Hnm : nx0 <> m0) by exact Hne. assert (Hpm : pr0 <> m0) by (intros Ep; apply Hne; apply (proj2 Hiff); exact Ep). assert (Hnp : nx0 <> pr0) by (intros Enp; exact (Hpn (eq_sym Enp))).
assert (Hmn : m0 <> nx0) by (intros EE; exact (Hnm (eq_sym EE))). assert (Hmp : m0 <> pr0) by (intros EE; exact (Hpm (eq_sym EE))).
split; [intros x Hx; rewrite MT_upd_other by exact (NIn _ NX0' x Hx); rewrite MT_set_active, MT_upd_other by exact (NIn _ NXn x Hx); rewrite MT_upd_other by exact (NIn _ NXp x Hx); exact (XR x Hx)|].
split.
{ apply (fsim_upd _ m0 am0).
- apply (fsim_metas (upd_meta nx0 (MUsed (am_set_prev (Some pr0) amn0)) (upd_meta pr0 (MUsed (am_set_next (Some nx0) amp0)) A))); [|reflexivity].
apply (fsim_upd _ nx0 amn0); [apply (fsim_upd A pr0 amp0); [apply fsim_refl | exact Mp | destruct amp0; reflexivity..] | rewrite MT_upd_other by exact Hnp; exact Mn | destruct amn0; reflexivity..].
- rewrite MT_set_active. rewrite MT_upd_other by exact Hmn. rewrite MT_upd_other by exact Hmp. exact Mg0.
- destruct am0; reflexivity.
- destruct am0; reflexivity.
- destruct am0; reflexivity. }
split.
{ rewrite (TC _ m0 am0); [| rewrite MT_set_active; rewrite MT_upd_other by exact Hmn; rewrite MT_upd_other by exact Hmp; exact Mg0 | unfold am0'; apply GL].
cbn [upd_meta set_active st_metas]. change (tail_cells (set_active ?l ?s0)) with (tail_cells s0).
rewrite (TC _ nx0 amn0); [| rewrite MT_upd_other by exact Hnp; exact Mn | rewrite set_prev_links; apply GL].
apply (TC A pr0 amp0); [exact Mp | rewrite set_next_links; apply GL]. }
split; [cbn; rewrite length_lupd; exact Hlen|]. split; [apply MT_upd_same|]. split; [intros; discriminate|]. intros _.
rewrite (MT_upd_other m0) by exact Hnm. rewrite (MT_upd_other m0) by exact Hpm. rewrite !MT_set_active. split; [apply MT_upd_same|]. rewrite MT_upd_other by exact Hpn. apply MT_upd_same.
Qed.
Lemma bnd1 : exists am1, bnd X U A sc (s1v v) nx0 am1.
Proof. clear HS2 HF. exact (bnd_A X U A sc m0 am0 HI Hsc Hhd Mg0 Hav0 nx0 (s1v v) (stepA_v v AC) (s1_same v AC) (s1_span v AC)). Qed.
Lemma cPN_mem q vv mc (Q : Z) : ptr_addr L q = Q -> (bytes_are mc (Q + 0) 8 (optrZ L vv) -> cell_mem B L mc (cP q vv)) /\ (bytes_are mc (Q + 8) 8 (optrZ L vv) -> cell_mem B L mc (cN q vv)).
Proof.
intros EQ. unfold cell_mem, cP, cN. cbn [mc_val mc_loc mc_w]. rewrite !loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_prev, META_next. rewrite EQ.
split; intros Hb; destruct vv; cbn [optr sval_num optrZ] in *; intros k Hk; exact (Hb k Hk).
Qed.
Lemma postA_memrep : memrepX B X L (s1v v) (ms_mem ms1).
Proof.
pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). pose proof m0_facts as (Hu0 & _).
destruct bnd1 as (am1 & B1). pose proof B1 as [HI1 Hhd1 _ _ _ _ _ UB1 SX1 SP1].
pose proof s1_facts as (RX1 & FS1 & TC1 & Hlen1 & M0f & M2f & M3f). pose proof (proj1 (inv_ctx HI)) as Hlen0.
pose proof postA_mem as (OUT & HB & Wm0 & W2 & W3). pose proof pre_factsS as (_ & _ & P3 & _). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
pose proof m0_factsA as (A1 & A2 & A8 & Aimg & Apres & _ & _ & _ & _ & _ & C1 & C2 & C8 & Cimg & Cpres & D1 & D2 & D8 & Dimg & Dpres & _).
pose proof SX1 as (Erg1 & Ear1 & _). pose proof MID0 as MID0'.
assert (Efp : footprint (s1v v) = footprint A) by (apply footprint_regions_areas; congruence).
assert (OLD : forall q aq c', usedX X A q aq -> In c' (meta_slot_cells q (Some (MUsed aq))) -> In c' (imageX X A ++ tail_cellsX X A)).
{ intros q aq c' Hq Hc'. exact (YN0p.old_meta_cell X None U A HI q aq c' Hq Hc'). }
assert (GL : forall p' n' am, grp_same am (am_set_links p' n' am)) by (intros; apply grp_same_links).
refine (memrepX_after B X X None None U U A (s1v v) L (ms_mem ms) (ms_mem ms1) (NEWA v) [] (sp - ASF, ASF)
HI HI1 (HLs A (ms_mem ms) MID0') Efp ltac:(congruence) (MRs None A (ms_mem ms) HI XR MID0') _ _ _ _ _ _ _ _).
-   intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
2:{ right. apply in_app_iff. right. unfold tail_cellsX in Hc |- *. rewrite (used_metasX_eq _ (s1v v) HI1 RX1) in Hc. rewrite (used_metasX_eq _ A HI XR). fold (tail_cells (s1v v)) in Hc. rewrite TC1 in Hc. exact Hc. }
unfold NEWA. destruct v; cbn [s1v acase] in AC, Hc |- *.
+ unfold sA_rot, hd_upd in Hc. destruct (imageX_set_active X A (Z.to_nat sc) (Some nx0) c ltac:(rewrite Hlen0; lia) Hc) as [->|Ho]; [left; left; reflexivity | right; apply in_app_iff; left; exact Ho].
+ destruct AC as (Hfr & Hne & Epn). assert (Hmn : m0 <> nx0) by (intros EE; exact (Hne (eq_sym EE))). unfold sA_D2, hd_upd in Hc.
destruct (imageX_upd_meta X _ m0 am0 (am0' am0) c ltac:(rewrite MT_set_active, MT_upd_other by exact Hmn; exact Mg0) (GL _ _ _) Hc) as [Hm|Hc1].
{ apply links_cells in Hm as [->|[->|Hm]]; [left; right; left; reflexivity | left; right; right; left; reflexivity | right; exact (OLD _ _ _ Hu0 Hm)]. }
cbn [upd_meta set_active st_active st_metas] in Hc1.
match type of Hc1 with In c (imageX X (set_active ?l ?s0)) => destruct (imageX_set_active X s0 (Z.to_nat sc) (Some nx0) c ltac:(cbn; rewrite Hlen0; lia) Hc1) as [->|Hc2] end; [left; left; reflexivity|].
destruct (imageX_upd_meta X A nx0 amn0 _ c Mn (GL _ _ _) Hc2) as [Hm|Ho]; [| right; apply in_app_iff; left; exact Ho].
apply links_cells in Hm as [->|[->|Hm]]; [left; do 3 right; left; reflexivity | left; do 4 right; left; reflexivity | right; exact (OLD _ _ _ Hun Hm)].
+ destruct AC as (Hfr & Hne & Hpn). assert (Hmn : m0 <> nx0) by (intros EE; exact (Hne (eq_sym EE))). assert (Hpm : pr0 <> m0) by (intros Ep; apply Hne; apply (proj2 Hiff); exact Ep).
assert (Hmp : m0 <> pr0) by (intros EE; exact (Hpm (eq_sym EE))). assert (Hnp : nx0 <> pr0) by (intros EE; exact (Hpn (eq_sym EE))).
unfold sA_D3, hd_upd in Hc.
destruct (imageX_upd_meta X _ m0 am0 (am0' am0) c ltac:(rewrite MT_set_active; rewrite MT_upd_other by exact Hmn; rewrite MT_upd_other by exact Hmp; exact Mg0) (GL _ _ _) Hc) as [Hm|Hc1].
{ apply links_cells in Hm as [->|[->|Hm]]; [left; right; left; reflexivity | left; right; right; left; reflexivity | right; exact (OLD _ _ _ Hu0 Hm)]. }
cbn [upd_meta set_active st_active st_metas] in Hc1.
match type of Hc1 with In c (imageX X (set_active ?l ?s0)) => destruct (imageX_set_active X s0 (Z.to_nat sc) (Some nx0) c ltac:(cbn; rewrite Hlen0; lia) Hc1) as [->|Hc2] end; [left; left; reflexivity|].
destruct (imageX_upd_meta X _ nx0 amn0 (am_set_prev (Some pr0) amn0) c ltac:(rewrite MT_upd_other by exact Hnp; exact Mn) ltac:(rewrite set_prev_links; apply GL) Hc2) as [Hm|Hc3].
{ rewrite set_prev_links in Hm. apply links_cells in Hm as [->|[->|Hm]]; [left; do 4 right; left; reflexivity | right; apply (OLD _ _ _ Hun); cbn; right; left; reflexivity | right; exact (OLD _ _ _ Hun Hm)]. }
destruct (imageX_upd_meta X A pr0 amp0 (am_set_next (Some nx0) amp0) c Mp ltac:(rewrite set_next_links; apply GL) Hc3) as [Hm|Ho]; [| right; apply in_app_iff; left; exact Ho].
rewrite set_next_links in Hm. apply links_cells in Hm as [->|[->|Hm]]; [right; apply (OLD _ _ _ Hup); cbn; left; reflexivity | left; do 3 right; left; reflexivity | right; exact (OLD _ _ _ Hup Hm)].
-   intros c Hc. unfold NEWA in Hc.
assert (HH : c = hcell (Some nx0) -> In c (areas_cells (s1v v) (st_areas (s1v v))) \/ In c (ctx_cells (s1v v))) by (intros ->; right; rewrite <- Hhd1; apply hcell_In; exact Hlen1).
assert (HM : forall q aq, MT (s1v v) q = Some (MUsed aq) -> (c = cP q (am_prev aq) \/ c = cN q (am_next aq)) -> In c (areas_cells (s1v v) (st_areas (s1v v))) \/ In c (ctx_cells (s1v v))).
{ intros q aq Mq Hc'. left. apply (YN2o.meta_cells_in_areas X None U (s1v v) HI1 q aq c Mq). destruct Hc' as [-> | ->]; cbn; [left | right; left]; reflexivity. }
destruct v; cbn [acase] in AC.
+ destruct Hc as [<-|[]]. apply HH. reflexivity.
+ destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [apply HH; reflexivity | apply (HM m0 (am0' am0) M0f); left | apply (HM m0 (am0' am0) M0f); right | apply (HM nx0 _ (M2f eq_refl)); left | apply (HM nx0 _ (M2f eq_refl)); right]; destruct am0, amn0; reflexivity.
+ destruct (M3f eq_refl) as [Mn1 Mp1]. destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [apply HH; reflexivity | apply (HM m0 (am0' am0) M0f); left | apply (HM m0 (am0' am0) M0f); right | apply (HM pr0 _ Mp1); right | apply (HM nx0 _ Mn1); left]; destruct am0, amn0, amp0; reflexivity.
-   intros c Hc. unfold NEWA in Hc.
destruct v; cbn [acase] in AC.
+ destruct Hc as [<-|[]]. apply hcell_mem. cbn [optrZ]. exact HB.
+ destruct (Wm0 ltac:(discriminate)) as (Bm0 & Bm8 & _). destruct (W2 eq_refl) as (Bn0 & Bn8 & _).
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [apply hcell_mem; cbn [optrZ]; exact HB | apply (proj1 (cPN_mem m0 None _ M0 eq_refl)); exact Bm0 | apply (proj2 (cPN_mem m0 None _ M0 eq_refl)); exact Bm8 | apply (proj1 (cPN_mem nx0 (Some nx0) _ NX0 eq_refl)); exact Bn0 | apply (proj2 (cPN_mem nx0 (Some nx0) _ NX0 eq_refl)); exact Bn8].
+ destruct (Wm0 ltac:(discriminate)) as (Bm0 & Bm8 & _). destruct (W3 eq_refl) as (Bp8 & Bn0 & _).
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [apply hcell_mem; cbn [optrZ]; exact HB | apply (proj1 (cPN_mem m0 None _ M0 eq_refl)); exact Bm0 | apply (proj2 (cPN_mem m0 None _ M0 eq_refl)); exact Bm8 | apply (proj2 (cPN_mem pr0 (Some nx0) _ PR0 eq_refl)); exact Bp8 | apply (proj1 (cPN_mem nx0 (Some pr0) _ NX0 eq_refl)); exact Bn0].
-   intros c k Hc Hk [p Hp]. unfold NEWA in Hc.
assert (PW : forall a, writable_at src0segs (ms_mem ms1) a -> (M0 <= a < M0 + 40 \/ NX0 <= a < NX0 + 40 \/ PR0 <= a < PR0 + 40) -> present (ms_mem ms1) a).
{ intros a Wa Ha. apply writable_off_img_present; [lia | unfold in_img1; lia | exact Wa]. }
destruct v; cbn [acase] in AC.
+ destruct Hc as [<-|[]]. exfalso. cbn [hcell act_cell mc_loc] in Hp. discriminate.
+ destruct (Wm0 ltac:(discriminate)) as (_ & _ & Wa). destruct (W2 eq_refl) as (_ & _ & Wb).
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [exfalso; cbn [hcell act_cell mc_loc] in Hp; discriminate | | | |];
unfold cP, cN in Hk |- *; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd'; unfold META_prev, META_next; fold M0; fold NX0;
(apply PW; [first [apply Wa; lia | apply Wb; lia] | lia]).
+ destruct (Wm0 ltac:(discriminate)) as (_ & _ & Wa). destruct (W3 eq_refl) as (_ & _ & Wb & Wc).
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [exfalso; cbn [hcell act_cell mc_loc] in Hp; discriminate | | | |];
unfold cP, cN in Hk |- *; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd'; unfold META_prev, META_next; fold M0; fold NX0; fold PR0;
(apply PW; [first [apply Wa; lia | apply Wb; lia | apply Wc; lia] | lia]).
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. exact (footprint_top A e HI (sameX_refl A) (or_introl MID) He).
- intros a Ha Hno _ Hns.
assert (NH : ~ (YN0j.CTX + 80 + 8 * sc <= a < YN0j.CTX + 80 + 8 * sc + 8)).
{ intros W. apply (Hno (hcell (Some nx0)) ltac:(clear; unfold NEWA; destruct v; left; reflexivity)). unfold in_range. rewrite hcell_range. cbn [fst snd]. lia. }
assert (NC : forall q vv Q, ptr_addr L q = Q -> (In (cP q vv) (NEWA v) -> ~ (Q <= a < Q + 8)) /\ (In (cN q vv) (NEWA v) -> ~ (Q + 8 <= a < Q + 16))).
{ intros q vv Q EQ. split; intros Hin W; apply (Hno _ Hin); unfold in_range, cell_range, cP, cN; cbn [fst snd mc_loc mc_w]; rewrite loc_addr_padd'; unfold META_prev, META_next; rewrite EQ; lia. }
assert (NW : ~ wrA v a).
{ unfold wrA. destruct v; cbn [acase] in AC; [intros [] | |]; cbn [NEWA] in NC.
- pose proof (NC m0 None M0 eq_refl) as [N1 N2]. pose proof (NC nx0 (Some nx0) NX0 eq_refl) as [N3 N4]. cbn [In] in N1, N2, N3, N4. intros [W|W]; [destruct (Z_lt_dec a (M0 + 8)); [apply N1 | apply N2] | destruct (Z_lt_dec a (NX0 + 8)); [apply N3 | apply N4]]; auto 10; lia.
- pose proof (NC m0 None M0 eq_refl) as [N1 N2]. pose proof (NC nx0 (Some pr0) NX0 eq_refl) as [N3 _]. pose proof (NC pr0 (Some nx0) PR0 eq_refl) as [_ N4]. cbn [In] in N1, N2, N3, N4.
intros [W|[W|W]]; [destruct (Z_lt_dec a (M0 + 8)); [apply N1 | apply N2] | apply N4 | apply N3]; auto 10; lia. }
assert (NS : ~ WS regs a) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; lia).
pose proof (OUT a Ha NH NW NS) as EQ. split; [apply mbyte_ext1; exact EQ|]. intros [b Hb]. exists b. rewrite EQ. exact Hb.
Qed.
Lemma postA : at_bnd ss_beta 40 (fun _ => True) (s1v v) nx0 (mkCfg ms1 md) /\ fsim (s1v v) /\ (exists am1, bnd X U A sc (s1v v) nx0 am1).
Proof.
pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn). pose proof m0_facts as (Hu0 & _).
destruct bnd1 as (am1 & B1). pose proof B1 as [HI1 Hhd1 _ _ _ _ _ UB1 SX1 SP1].
pose proof s1_facts as (RX1 & FS1 & TC1 & Hlen1 & _). pose proof postA_mem as (OUT & HB & _). pose proof postA_regs as (G10 & GPC).
pose proof m0_factsA as (A1 & A2 & A8 & Aimg & Apres & _ & _ & _ & _ & _ & C1 & C2 & C8 & Cimg & Cpres & D1 & D2 & D8 & Dimg & Dpres & _). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
destruct E1a_vals as (V40 & _). pose proof MID0 as MID0'.
assert (MG : ss_atoms_lt 43 (SSA v) = true /\ mergeb ss_beta (junk_regs [11%bv] 43 (SSA v)) = true) by (destruct v; [apply merge_AR1 | apply merge_AD2 | apply merge_AD3]).
destruct (junk_regs_ok src0segs [11%bv] 43 E1a (SSA v) ms1 HS2 (proj1 MG) eq_refl) as (E2 & HA2 & HSj).
pose proof (st_ok_merge src0segs E2 ss_beta _ ms1 HSj (proj2 MG)) as HSb.
assert (OWN : forall x, wrA v x -> alloc_owned L A x).
{ intros x W. assert (K : forall q aq, MT A q = Some (MUsed aq) -> ptr_addr L q <= x < ptr_addr L q + 40 -> alloc_owned L A x).
{ intros q aq Mq Hx. exact (YN2u.meta_bytes_owned X None U A L HI (HLs A (ms_mem ms) MID0') q x (MUsed aq) Mq Hx). }
unfold wrA in W. destruct v; [destruct W | |]; unfold M0, NX0, PR0 in W.
- destruct W as [W|W]; [exact (K m0 am0 Mg0 ltac:(lia)) | exact (K nx0 amn0 Mn ltac:(lia))].
- destruct W as [W|[W|W]]; [exact (K m0 am0 Mg0 ltac:(lia)) | exact (K pr0 amp0 Mp ltac:(lia)) | exact (K nx0 amn0 Mn ltac:(lia))]. }
split; [|split; [exact FS1 | exists am1; exact B1]].
exists E2, ms1. split; [reflexivity|]. split; [exact HSb|].
split; [eapply env_agree_trans; [exact HA1a | eapply env_agree_le; [| exact HA2]; lia]|].
split; [rewrite (proj1 HA2 40%nat ltac:(lia)); exact V40|]. split; [exact I|]. split; [exact RX1|]. split.
- apply (midrep_transport A (s1v v) (ms_mem ms) (ms_mem ms1) HI XR MID0' (s1_same v AC) RX1 (ex_intro _ None HI1) postA_memrep).
+ exact (ub_same_user_blocks A (s1v v) (proj1 (inv_keys HI)) (proj1 (inv_keys HI1)) UB1).
+ exact TC1.
+ intros a Hs. destruct (static_range a Hs) as [R1 R2]. apply OUT; [lia | intros W; apply R2; unfold CTX_SIZE; lia | intros W; pose proof (OWN a W) as HO; apply R2; exact (owned_img None A mem HI MID a HO ltac:(apply in_img1_in_img; unfold in_img1; lia)) | unfold WS; fold sp; pose proof pre_factsS as (_ & _ & P3 & _); pose proof Hstk; unfold ASF in *; lia].
- intros x Hx Hns Hnc Hno. rewrite (OUT x Hx); [exact (FR0 x Hx Hns Hnc Hno) | intros W; apply Hnc; unfold CTX_SIZE; lia | intros W; exact (Hno (OWN x W)) | exact Hns].
Qed.
End l0.
Theorem stage_A : am_freed am0 <> 0 \/ nx0 <> m0 ->
exists v, acase v /\ STEP_A sc m0 am0 A = IRet (Some nx0, s1v v) /\ (exists am1, bnd X U A sc (s1v v) nx0 am1) /\ fsim (s1v v) /\
SR src0segs (mkCfg ms md) (at_bnd ss_beta 40 (fun _ => True) (s1v v) nx0).
Proof.
intros CASE. pose proof lk0 as (Hpr & Hnx & Hup & Hun & Hsp & Hsn & Hiff & Hnf & Mp & Mn).
assert (V : exists v, acase v).
{ destruct (Z.eq_dec (am_freed am0) 0) as [Efr|NE]; [|exists AV1; exact NE].
assert (Hne : nx0 <> m0) by (destruct CASE as [H|H]; [exfalso; exact (H Efr) | exact H]).
destruct (sptr_eq_dec pr0 nx0) as [Ep|Np]; [exists AV2 | exists AV3]; cbn; auto. }
destruct V as [v AC]. exists v. split; [exact AC|]. split; [exact (stepA_v v AC)|].
assert (P : forall ms1, st_ok src0segs E1a (SSA v) ms1 -> frame_of E1a (ss_mem (ssA v)) (ms_mem ms) (ms_mem ms1) ->
at_bnd ss_beta 40 (fun _ => True) (s1v v) nx0 (mkCfg ms1 md) /\ fsim (s1v v) /\ (exists am1, bnd X U A sc (s1v v) nx0 am1)).
{ intros ms1 HS2 HF. first [exact (postA v ms1 AC HS2 HF) | exact (postA v AC ms1 HS2 HF)]. }
split; [| split].
- destruct (bnd1 v AC) as [am1 B1]; exists am1; exact B1.
- exact (proj1 (proj2 (s1_facts v AC))).
- eapply SR_mono; [exact (A_run v AC)|]. intros c' (ms1 & -> & HS2 & HF). exact (proj1 (P ms1 HS2 HF)).
Qed.
End k0.
Definition hnx : sptr := match am_next am0 with Some p => p | None => m0 end.
Definition FALL_hyp (fuel : nat) : Prop := am_freed am0 = 0 -> am_next am0 = Some m0 ->
mreal src0segs (mkCfg ms0 md) (alloc_slot (S (S fuel)) sc n A) (POST X L A regs mem md sc stk g).
Lemma POST_transport s1 mem1 r c' :
sameX A s1 -> user_blocks s1 = user_blocks A -> rawX X s1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WS regs x -> ~ (YN0j.CTX <= x < YN0j.CTX + CTX_SIZE) -> ~ alloc_owned L A x -> mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
POST X L s1 regs mem1 md sc stk g r c' -> POST X L A regs mem md sc stk g r c'.
Proof.
intros SX UBe RX1 FRm (L' & regs' & mem' & md' & Ec & MID' & AMA' & BND' & RSV' & SPOK' & LE & RP & VM & FRP & SCR & G10 & UND & AK & GW).
pose proof SX as (Erg & Ear & _).
exists L', regs', mem', md'. repeat (split; [assumption|]). split.
{ unfold layout_le in *. rewrite <- Erg. exact LE. }
split; [exact RP|]. split; [exact VM|]. split; [| split; [exact SCR | split; [exact G10 | split; [exact UND | split; [apply (as_keep_trans X A s1); [apply as_keep_same; [intros x Hx _; exact (RX1 x Hx) | exact Ear | exact Erg] | exact AK] | exact GW]]]]].
intros x Hx Hnc NO NO' NN NS. rewrite (FRP x Hx Hnc); [| | exact NO' | exact NN | exact NS].
- apply FRm; [exact Hx | unfold call_scratch in NS; unfold WS, spZ in *; fold sp; intros W; apply NS; left; pose proof Hstk; unfold ASF in *; lia | cbn [ms_ctx B] in Hnc; unfold YN0j.CTX; exact Hnc | intros W; apply NO; left; exact W].
- intros [W|W]; apply NO; [left | right; exact W]. apply (alloc_owned_same L A s1 x); [apply footprint_regions_areas; assumption | exact UBe | exact W].
Qed.
Section n0.
Hypothesis Hfr0 : am_freed am0 = 0.
Hypothesis Hnx00 : am_next am0 = Some m0.
Variables (E : env) (ms : machine_state).
Hypothesis HS : st_ok src0segs E ss_hd ms.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis HFm : FRM mem (WS regs) (ms_mem ms).
Lemma MIDf : midrep B L A (ms_mem ms) md.
Proof. exact (midrep_stack X U L A regs mem md stk HI XR AMA MID PRE Hstk (ms_mem ms) HFm). Qed.
Definition s1f : astate := sA_D1 A sc m0 am0.
Lemma pr00 : am_prev am0 = Some m0.
Proof.
destruct (links0 X U A sc m0 am0 HI Hsc Hhd Mg0) as (pr & nx & ampr & amnx & Hpr & Hnx & _ & _ & _ & _ & Hiff & _).
rewrite Hnx00 in Hnx. injection Hnx as <-. rewrite Hpr. f_equal. apply (proj1 Hiff). reflexivity.
Qed.
Lemma m0_factsF :
4096 <= M0 /\ M0 + 40 <= alloc_ceiling /\ M0 mod 8 = 0 /\ (M0 + 40 <= 0x10000 \/ 0x51000 <= M0) /\ (forall x, M0 <= x < M0 + 40 -> present (ms_mem ms) x) /\
bytes_are (ms_mem ms) (M0 + 0) 8 M0 /\ bytes_are (ms_mem ms) (M0 + 8) 8 M0 /\ bytes_are (ms_mem ms) (M0 + 24) 4 0 /\ bytes_are (ms_mem ms) (M0 + 28) 4 0 /\
bytes_are (ms_mem ms) (YN0j.CTX + 80 + 8 * sc) 8 M0 /\ bytes_are (ms_mem ms) (SCT + 2 * sc) 2 (scl_of sc) /\ 1 <= scl_of sc <= 8191 /\
ew E 36 = Z_to_bv 64 (SCT + 2 * sc) /\ ew E 35 = Z_to_bv 64 (scl_of sc) /\ ew E 34 = Z_to_bv 64 M0.
Proof.
pose proof m0_facts as (Hu0 & Hs0 & C34). pose proof (proj1 alloc_ceiling_val). pose proof MIDf as MID0'.
pose proof (metaS None A (ms_mem ms) HI XR MID0' m0 am0 Hu0) as (A1 & A2 & A3 & A4 & A5 & B0 & B8 & _ & B24 & B28 & _).
pose proof (headS None A (ms_mem ms) HI XR MID0') as HD. rewrite Hhd in HD. cbn [optrZ] in HD.
rewrite pr00 in B0. rewrite Hnx00 in B8. cbn [optrZ] in B0, B8. rewrite Hav0 in B24. rewrite Hfr0 in B28.
pose proof (cs_facts X U L A regs mem md sc HI Hsc MID g 0 M0) as (_ & _ & _ & C35 & _). cbn [cs] in C35.
pose proof (agree_facts E HA) as (_ & _ & _ & _ & E36 & E35).
assert (Escl : scl_of sc = znth sc size_classes) by (unfold scl_of; replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
unfold M0 in *. repeat match goal with |- _ /\ _ => split end; auto; try lia.
- apply (YN0p.off_img _ A4).
- rewrite Escl. apply (YN1y.sct_bytes (ms_mem ms) (STs A (ms_mem ms) MID0') sc). lia.
- rewrite <- C34. exact (agree_cs L A regs sc g 0 (ptr_addr L m0) E 34 HA ltac:(lia)).
Qed.
Lemma F_st_ok : st_ok src0segs E ss_AD1g ms.
Proof.
pose proof (proj1 alloc_ceiling_val) as ACV. pose proof CTX_eq as CE. pose proof statics_layout3 as (SL0 & SL1 & SL2 & SL3 & SL4). pose proof statics_layout as (_ & _ & SLc1 & SLc2 & _).
pose proof m0_factsF as (A1 & A2 & A8 & Aimg & Apres & B0 & B8 & B24 & B28 & HD & Bsct & Hscl & E36 & E35 & E34).
pose proof (st_ok_mem_ok src0segs E ss_hd ms HS) as MOK. rewrite ss_hd_mem in MOK.
pose proof (agree_facts E HA) as (_ & _ & B33 & B2 & _).
assert (BASE : mem_ok src0segs E (ms_mem ms) (R_actW (SOff 34 0) :: tl (ss_mem ss_hd))).
{ apply (mem_ok_act_rw E _ _ MOK). intros o Ho. rewrite B33. apply (ctx_writableS (ms_mem ms)). unfold CTX_SIZE. lia. }
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (Sat & Scd & Sal)).
pose proof (base_atom E 34 M0 E34 ltac:(lia)) as V34. pose proof (base_atom E 36 (SCT + 2 * sc) E36 ltac:(lia)) as V36.
assert (W34 : sv_denot E (SOff 34 0) = Z_to_bv 64 M0) by (apply (den_atom0 E 34 _ E34); lia).
unfold st_ok, ss_AD1g. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [exact S6|]. split; [exact S7|]. split.
- cbn [app]. apply mem_ok_cons'; [reflexivity | | | apply mem_ok_cons'; [reflexivity | | | exact BASE]].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m0d1]; rewrite V34; [lia | lia | intros o Ho; apply present_writable; apply Apres; lia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
* apply (chunk_ok_val' E _ _ _ 8 _ M0); [rewrite W34; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B0].
* apply (chunk_ok_val' E _ _ _ 8 _ M0); [rewrite W34; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact B8].
* apply (chunk_ok_val' E _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B24].
* apply (chunk_ok_val' E _ _ _ 4 _ 0); [cbn [sv_denot]; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact B28].
+ intros r' [<-|Hr'].
* unfold extent_disjoint. cbn [r_base r_lo r_hi R_m0d1 R_sct]. rewrite V34, V36. lia.
* unfold extent_disjoint. cbn [r_base r_lo r_hi R_m0d1]. rewrite V34.
destruct (base_disjoint E r' M0 (M0 + 40) HA ltac:(destruct Hr' as [<-|H]; [right; eexists; reflexivity | left; right; exact H]) ltac:(lia) ltac:(lia) Aimg); lia.
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_sct]; rewrite V36; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val' E _ _ _ 2 _ (scl_of sc)); [rewrite (den_atom0 E 35 _ E35) by lia; apply lit64_small; lia | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | rewrite Z.add_0_r; exact Bsct].
+ intros r' Hr'. unfold extent_disjoint. cbn [r_base r_lo r_hi R_sct]. rewrite V36. destruct Hr' as [<-|Hr'].
* cbn [r_base r_lo r_hi R_actW]. rewrite B33. lia.
* pose proof (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hr') as Hin'. rewrite MEM0_skel in Hin'. cbn [In] in Hin'.
decompose [or] Hin'; try contradiction; match goal with H : _ = (r_base r', _, _, _, _) |- _ => injection H as Eb El Eh _ _ end; rewrite <- El, <- Eh, <- Eb; rewrite ?B2; cbn [base_val]; try lia.
pose proof pre_factsS as (_ & _ & P3 & _). pose proof Hstk. unfold ASF in *. lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias app atoms_ok conds_ok alias_ok]. split; [|split].
+ unfold FM, F_sct, F_sz, afact_ok; cbn [af_lo af_hi af_al2]. rewrite E34, E36, E35, !lit64_small by lia.
change (2 ^ 3) with 8. change (2 ^ 1) with 2. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (SCT mod 2 = 0) by (unfold SCT, src0_D_size_classes; reflexivity).
split; [lia|]. split; [split; [lia|]; split; [|lia]; rewrite Z.mul_comm, Z_mod_plus_full; assumption|]. split; [lia | exact Sat].
+ split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b C_hd1]. rewrite branch_ne, W34. cbn [sv_denot]. rewrite (lit64_small M0), (lit64_small 0) by lia. destruct (Z.eqb_spec M0 0); [lia | reflexivity].
+ split; [|exact I]. apply word_eq. cbv delta [ADDR36]. cbn [sv_denot]. rewrite alu64_add, alu64_sll, !Z.add_0_r, !Z_to_bv_bv_unsigned.
rewrite (proj1 HA 10%nat) by lia. unfold E00. rewrite (E0_reg regs _ 10) by lia. replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : reg) by (apply bv_eq; reflexivity). rewrite R10, E36.
rewrite (lit64_small 1), (lit64_small SCT), (lit64_small sc), (lit64_small (SCT + 2 * sc)) by lia. change (1 mod 64) with 1.
unfold sll64, add64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite (Z.mod_small (sc * 2)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma F_run : SR src0segs (mkCfg ms md) (fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SSA_D1g ms1 /\ frame_of E (ss_mem ss_AD1g) (ms_mem ms) (ms_mem ms1)).
Proof.
pose proof md_factsS as (Mh & Mlz & _). pose proof F_st_ok as HS0.
eapply SR_mono; [eapply (SR_run_to src0_A_alloc_meta); [exact HS0 | exact AD1g_run_ok | exact Mh | exact Mlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
rewrite <- SSA_D1g_eq. unfold closeF. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS0)].
Qed.
Lemma s1f_facts : Inv X None U s1f /\ active_hd s1f sc = None /\ ub_same A s1f /\ sameX A s1f /\ MT s1f m0 = Some (MUsed (am0' am0)) /\
rawX X s1f /\ fsim s1f /\ tail_cells s1f = tail_cells A /\ user_blocks s1f = user_blocks A /\ length (st_active s1f) = 48%nat /\
(forall c, 0 <= c -> c <> sc -> active_hd s1f c = active_hd A c).
Proof.
pose proof m0_facts as (Hu0 & _). pose proof (proj2 (usedX_MT _ _ _ _ Hu0)) as NX0'. pose proof (proj1 (inv_ctx HI)) as Hlen.
destruct (post_D1 X U A sc m0 am0 HI Hsc Hhd Mg0 Hav0 Hfr0 Hnx00) as (HI1 & Hhd1 & Hoth1 & UB1 & SX1 & M1).
unfold s1f. repeat (split; [assumption|]). split.
{ intros x Hx. unfold sA_D1, hd_upd. rewrite MT_upd_other; [rewrite MT_set_active; exact (XR x Hx)|]. intros ->. apply (proj2 (memb_In m0 X)) in Hx. rewrite Hx in NX0'. discriminate. }
split; [unfold sA_D1, hd_upd; apply (fsim_upd _ m0 am0); [apply (fsim_metas A); [apply fsim_refl | reflexivity] | rewrite MT_set_active; exact Mg0 | destruct am0; reflexivity..]|].
split.
{ unfold sA_D1, hd_upd. rewrite (tail_cells_upd _ m0 am0); [reflexivity | rewrite MT_set_active; exact Mg0 | apply grp_same_links]. }
split; [exact (ub_same_user_blocks A _ (proj1 (inv_keys HI)) (proj1 (inv_keys HI1)) UB1)|].
split; [unfold sA_D1, hd_upd; cbn; rewrite length_lupd; exact Hlen | exact Hoth1].
Qed.
Lemma g0_regs_check' : forallb (fun r : reg => existsb (bv_eqb r) [11; 12; 19]%bv || (sv_eqb (sr_get (ss_regs ss_G0) r) (sr_get (ss_regs SSA_D1g) r) && sv_free 34 (sr_get (ss_regs ss_G0) r))) all_regs = true.
Proof. vm_compute. reflexivity. Qed.
Section o0.
Variable ms1 : machine_state.
Hypothesis HS2 : st_ok src0segs E SSA_D1g ms1.
Hypothesis HF : frame_of E (ss_mem ss_AD1g) (ms_mem ms) (ms_mem ms1).
Lemma postF_mem :
(forall x, 0 <= x < 2 ^ 64 -> ~ (YN0j.CTX + 80 + 8 * sc <= x < YN0j.CTX + 80 + 8 * sc + 8) -> ~ (M0 <= x < M0 + 16) -> ~ WS regs x ->
(ms_mem ms1) (Z_to_bv 64 x) = (ms_mem ms) (Z_to_bv 64 x)) /\
bytes_are (ms_mem ms1) (YN0j.CTX + 80 + 8 * sc) 8 0 /\ bytes_are (ms_mem ms1) (M0 + 0) 8 0 /\ bytes_are (ms_mem ms1) (M0 + 8) 8 0 /\
(forall a, M0 <= a < M0 + 16 -> writable_at src0segs (ms_mem ms1) a) /\ (forall a, WS regs a -> writable_at src0segs (ms_mem ms1) a).
Proof.
pose proof m0_factsF as (A1 & A2 & A8 & Aimg & Apres & _ & _ & _ & _ & _ & _ & _ & E36 & E35 & E34). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
pose proof (agree_facts E HA) as (_ & _ & B33 & B2 & _). pose proof (base_atom E 34 M0 E34 ltac:(lia)) as V34.
pose proof (st_ok_mem_ok src0segs E SSA_D1g ms1 HS2) as (_ & MOK & _). rewrite (proj1 SSA_D1g_shape) in MOK.
pose proof (proj1 (Forall_forall _ _) MOK (R_m0z 0 16) ltac:(left; reflexivity)) as (_ & _ & WRm & CHm). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_m0z] in WRm, CHm. rewrite V34 in WRm, CHm.
pose proof (proj1 (Forall_forall _ _) MOK (R_actW (SLit 0)) ltac:(right; right; left; reflexivity)) as (_ & _ & _ & CHa). cbn [r_base r_chunks R_actW] in CHa. rewrite B33 in CHa.
destruct stack_region as (rstk & t & Et & SKR).
pose proof (proj1 (Forall_forall _ _) MOK rstk ltac:(do 3 right; rewrite Et; left; reflexivity)) as (_ & _ & WRs & _). injection SKR as Eb' Ewl' Ewh'. rewrite Eb', Ewl', Ewh', B2 in WRs.
assert (U0 : bv_unsigned (sv_denot E (SLit 0)) = 0) by (cbn [sv_denot]; apply lit64_small; lia).
split; [|split; [|split; [|split; [|split]]]].
- intros x Hx Hnh Hnm Hns. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx. intros Hw.
destruct (wrange_cases E [R_m0d1; R_sct] _ x HA Hw) as [(r & Hin & Hr)|[Hh|Hs']]; [| exact (Hnh Hh) | exact (Hns Hs')].
destruct Hin as [<-|[<-|[]]]; cbn [r_base r_wlo r_whi R_m0d1 R_sct] in Hr; [rewrite V34 in Hr; apply Hnm; lia | lia].
- replace (YN0j.CTX + 80 + 8 * sc) with (YN0j.LOCK + 8 * sc + 88) by lia. apply (chunk_bytes' E _ _ _ 8 (SLit 0) 0); [exact (Forall_inv CHa) | exact U0].
- apply (chunk_bytes' E _ _ _ 8 (SLit 0) 0); [exact (Forall_inv (Forall_inv_tail CHm)) | exact U0].
- apply (chunk_bytes' E _ _ _ 8 (SLit 0) 0); [exact (Forall_inv CHm) | exact U0].
- intros a Ha. replace a with (M0 + (a - M0)) by lia. apply WRm. lia.
- intros a Ha. unfold WS, ASF in Ha. fold sp in Ha. replace a with (sp + (a - sp)) by lia. apply WRs. lia.
Qed.
Lemma postF_memrep : memrepX B X L s1f (ms_mem ms1).
Proof.
pose proof m0_facts as (Hu0 & _). pose proof s1f_facts as (HI1 & Hhd1 & UB1 & SX1 & M1 & RX1 & FS1 & TC1 & UBe & Hlen1 & _). pose proof (proj1 (inv_ctx HI)) as Hlen0.
pose proof postF_mem as (OUT & HB & B0 & B8 & Wm & Ws). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE. pose proof MIDf as MID0'.
pose proof m0_factsF as (A1 & A2 & A8 & Aimg & _). pose proof SX1 as (Erg1 & Ear1 & _).
assert (Efp : footprint s1f = footprint A) by (apply footprint_regions_areas; congruence).
refine (memrepX_after B X X None None U U A s1f L (ms_mem ms) (ms_mem ms1) [hcell None; cP m0 None; cN m0 None] [] (sp - ASF, ASF)
HI HI1 (HLs A (ms_mem ms) MID0') Efp ltac:(congruence) (MRs None A (ms_mem ms) HI XR MID0') _ _ _ _ _ _ _ _).
- intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
2:{ right. apply in_app_iff. right. unfold tail_cellsX in Hc |- *. rewrite (used_metasX_eq _ s1f HI1 RX1) in Hc. rewrite (used_metasX_eq _ A HI XR). fold (tail_cells s1f) in Hc. rewrite TC1 in Hc. exact Hc. }
unfold s1f, sA_D1, hd_upd in Hc.
destruct (imageX_upd_meta X _ m0 am0 (am0' am0) c ltac:(rewrite MT_set_active; exact Mg0) (grp_same_links _ _ _) Hc) as [Hm|Hc1].
{ apply links_cells in Hm as [->|[->|Hm]]; [left; right; left; reflexivity | left; right; right; left; reflexivity | right; exact (YN0p.old_meta_cell X None U A HI m0 am0 c Hu0 Hm)]. }
destruct (imageX_set_active X A (Z.to_nat sc) None c ltac:(rewrite Hlen0; lia) Hc1) as [->|Ho]; [left; left; reflexivity | right; apply in_app_iff; left; exact Ho].
- intros c [<-|[<-|[<-|[]]]].
+ right. rewrite <- Hhd1. apply hcell_In. exact Hlen1.
+ left. apply (YN2o.meta_cells_in_areas X None U s1f HI1 m0 (am0' am0) _ M1). destruct am0; cbn; left; reflexivity.
+ left. apply (YN2o.meta_cells_in_areas X None U s1f HI1 m0 (am0' am0) _ M1). destruct am0; cbn; right; left; reflexivity.
- intros c [<-|[<-|[<-|[]]]]; [apply hcell_mem; cbn [optrZ]; exact HB | |].
+ unfold cell_mem, cP. cbn [mc_val mc_loc mc_w optr sval_num]. rewrite loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_prev. fold M0. exact B0.
+ unfold cell_mem, cN. cbn [mc_val mc_loc mc_w optr sval_num]. rewrite loc_addr_padd'. change (ms_segs B) with src0segs. unfold META_next. fold M0. exact B8.
- intros c k Hc Hk [p Hp]. destruct Hc as [<-|[<-|[<-|[]]]]; [exfalso; cbn [hcell act_cell mc_loc] in Hp; discriminate | |];
unfold cP, cN in Hk |- *; cbn [mc_loc mc_w] in Hk |- *; rewrite loc_addr_padd'; unfold META_prev, META_next; fold M0;
(apply writable_off_img_present; [lia | unfold in_img1; lia | apply Wm; lia]).
- intros d c [].
- intros d a [].
- intros e He. cbn [fst]. exact (footprint_top A e HI (sameX_refl A) (or_introl MID) He).
- intros a Ha Hno _ Hns.
assert (NH : ~ (YN0j.CTX + 80 + 8 * sc <= a < YN0j.CTX + 80 + 8 * sc + 8)).
{ intros W. apply (Hno (hcell None) (or_introl eq_refl)). unfold in_range. rewrite hcell_range. cbn [fst snd]. lia. }
assert (NM : ~ (M0 <= a < M0 + 16)).
{ intros W. destruct (Z_lt_dec a (M0 + 8)).
- apply (Hno (cP m0 None) ltac:(right; left; reflexivity)). unfold in_range, cell_range, cP. cbn [fst snd mc_loc mc_w]. rewrite loc_addr_padd'. fold M0. unfold META_prev. lia.
- apply (Hno (cN m0 None) ltac:(right; right; left; reflexivity)). unfold in_range, cell_range, cN. cbn [fst snd mc_loc mc_w]. rewrite loc_addr_padd'. fold M0. unfold META_next. lia. }
assert (NS : ~ WS regs a) by (unfold WS; unfold in_range in Hns; cbn [fst snd] in Hns; fold sp; lia).
pose proof (OUT a Ha NH NM NS) as EQ. split; [apply mbyte_ext1; exact EQ|]. intros [b Hb]. exists b. rewrite EQ. exact Hb.
Qed.
Lemma F_ctx : midrep B L s1f (ms_mem ms1) md /\ FRAME (ms_mem ms1) /\ rawX X s1f /\ ama_ok s1f /\ bounded s1f /\ rsv_ok s1f /\ span_ok s1f /\
(st_init_done s1f = false -> auxv_pre B (ly_sec L) (spZ regs) (ms_mem ms1)) /\ callee_pre B regs (ms_mem ms1) stk /\ word_mem src0segs (ms_mem ms1) GUARD g.
Proof.
pose proof m0_facts as (Hu0 & _). pose proof s1f_facts as (HI1 & Hhd1 & UB1 & SX1 & M1 & RX1 & FS1 & TC1 & UBe & Hlen1 & _).
pose proof postF_mem as (OUT & HB & B0 & B8 & Wm & Ws). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE. pose proof MIDf as MID0'.
pose proof m0_factsF as (A1 & A2 & A8 & Aimg & _). pose proof SX1 as (Erg & Ear & Eus & Esh & Eama & Ebrk & Einit & _).
pose proof pre_factsS as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof statics_layout as (_ & _ & SLc1 & SLc2 & _). pose proof Hstk as Hstk'. unfold ASF, AS_STACK in Hstk'.
assert (OWN : forall x, M0 <= x < M0 + 16 -> alloc_owned L A x).
{ intros x W. exact (YN2u.meta_bytes_owned X None U A L HI (HLs A (ms_mem ms) MID0') m0 x (MUsed am0) Mg0 ltac:(unfold META_SIZE; fold M0; lia)). }
assert (FRm1 : FRAME (ms_mem ms1)).
{ intros x Hx Hns Hnc Hno. rewrite (OUT x Hx); [exact (HFm x Hx Hns) | intros W; apply Hnc; unfold CTX_SIZE; lia | intros W; exact (Hno (OWN x W)) | exact Hns]. }
assert (SAME : forall x, 0 <= x < 2 ^ 64 -> ~ WS regs x -> ~ (YN0j.CTX <= x < YN0j.CTX + CTX_SIZE) -> ~ alloc_owned L A x -> (ms_mem ms1) (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) by exact FRm1.
assert (IMG : forall x, in_img B x -> ~ (YN0j.CTX <= x < YN0j.CTX + CTX_SIZE) -> (ms_mem ms1) (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hi Hnc. pose proof (src0_img_range x Hi). apply SAME; [lia | unfold WS; fold sp; pose proof Hstk; unfold ASF in *; lia | exact Hnc | intros HO; apply Hnc; exact (owned_img None A mem HI MID x HO Hi)]. }
split; [|split; [exact FRm1 | split; [exact RX1 | split; [| split; [| split; [| split; [unfold s1f; apply (span_D1 A sc m0 am0 Mg0); exact SPOK | split; [| split]]]]]]]].
- apply (midrep_transport A s1f (ms_mem ms) (ms_mem ms1) HI XR MID0' SX1 RX1 (ex_intro _ None HI1) postF_memrep UBe TC1).
intros a Hs. destruct (static_range a Hs) as [R1 R2]. apply OUT; [lia | intros W; apply R2; unfold CTX_SIZE; lia | intros W; pose proof (OWN a W) as HO; apply R2; exact (owned_img None A mem HI MID a HO ltac:(apply in_img1_in_img; unfold in_img1; lia)) | unfold WS; fold sp; pose proof Hstk; unfold ASF in *; lia].
- unfold ama_ok in *. rewrite Ear, Eama, Erg. exact AMA.
- unfold bounded, usage_of in *. rewrite Eus, Esh, Ear. exact BND.
- intros g' am' i fr Hin Hk. destruct (FS1 g' am' i fr Hin) as (am & Hin' & Hst). unfold reserved_of. rewrite <- Hst. exact (RSV g' am i fr Hin' Hk).
- intros Hinit. rewrite Einit in Hinit. apply (auxv_pre_ext (ly_sec L) (spZ regs) mem (ms_mem ms1)); [| | exact (AUXP Hinit)].
+ intros x Hx. apply mbyte_ext1. unfold spZ in Hx. fold sp in Hx. apply SAME; [lia | unfold WS; fold sp; lia | unfold YN0j.CTX, CTX_SIZE in *; lia |].
intros [(e & He & Hxe) _]. pose proof (YN0p.footprint_below X None U L A md HI SO HctxS (mid_ledger _ _ _ _ _ MID) e x He Hxe). lia.
+ intros x Hx. assert (SOx : static_owned B x) by (unfold static_owned; right; right; left; exact Hx).
apply mbyte_ext1. apply IMG; [exact (so_statics_img _ SO x SOx) | exact (proj2 (static_range x SOx))].
- unfold callee_pre. unfold spZ. fold sp. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [| split; [exact P6|]].
+ intros a Ha. destruct (Z_le_dec (sp - ASF) a); [apply Ws; unfold WS; fold sp; lia|].
apply (writable_ext1 mem); [| apply P5; exact Ha]. apply SAME; [lia | unfold WS; fold sp; lia | unfold YN0j.CTX, CTX_SIZE in *; lia |].
intros [(e & He & Hxe) _]. pose proof (YN0p.footprint_below X None U L A md HI SO HctxS (mid_ledger _ _ _ _ _ MID) e a He Hxe). lia.
+ intros a Ha. apply (writable_ext1 mem); [| apply P7; exact Ha]. apply IMG; [exact (src0_errno_img a Ha)|]. unfold errno_addr in Ha. cbn [ms_tp ms_errno_off B src0_msyms] in Ha. unfold src0_tp, YN0j.CTX, CTX_SIZE, src0_D_malloc_context in *. lia.
- apply (word_mem_ext1 mem); [| exact Hg]. intros k Hk. pose proof statics_layout as (_ & _ & _ & _ & _ & _ & G1 & G2 & _).
apply IMG; [apply in_img1_in_img; unfold in_img1; lia|]. pose proof statics_layout2 as (_ & SG & _). unfold CTX_SIZE. lia.
Qed.
Definition Eg : env := ewset E 34 (Z_to_bv 64 0).
Lemma Eg_agree : env_agree 40 (E0 regs (cs L s1f sc g 0 M0)) Eg.
Proof.
pose proof s1f_facts as (_ & Hhd1 & _). destruct HA as [HAw HAd]. split.
- intros k Hk. unfold Eg. cbn [ew ewset]. destruct (Nat.eqb_spec k 34) as [->|Hne].
+ rewrite E0_cx by lia. cbn [cs]. rewrite Hhd1. reflexivity.
+ rewrite (HAw k Hk). unfold E00.
destruct (Nat.lt_ge_cases k 32) as [Hlt|Hge].
* destruct k as [|k']; [reflexivity|]. rewrite !E0_reg by lia. reflexivity.
* rewrite !E0_cx by lia. f_equal. unfold cs. destruct k as [|k1]; [lia|]. do 40 (destruct k1 as [|k1]; [first [reflexivity | exfalso; apply Hne; reflexivity | lia] |]). reflexivity.
- unfold Eg. cbn [ed ewset]. rewrite HAd. reflexivity.
Qed.
Lemma G0_st_ok : st_ok src0segs Eg ss_G0 ms1.
Proof.
pose proof m0_factsF as (A1 & A2 & A8 & Aimg & Apres & _ & _ & _ & _ & _ & _ & Hscl & E36 & E35 & E34). pose proof (proj1 alloc_ceiling_val). pose proof CTX_eq as CE.
pose proof statics_layout3 as (SL0 & SL1 & SL2 & SL3 & SL4). pose proof statics_layout as (_ & _ & SLc1 & SLc2 & _).
pose proof (agree_facts E HA) as (E33 & E2 & B33 & B2 & _). pose proof postF_mem as (OUT & HB & _).
pose proof HS2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & (Sat & Scd & Sal)).
pose proof SSA_D1g_shape as (Smem & Spc & Srv & G11 & G12 & G19). pose proof g0_regs_check as (_ & H11 & H12 & H19 & H0 & Hpc & Hrv). pose proof g0_mem_shape as (Gmem & Gwf & Gfree & Gfacts).
assert (Eg36 : ew Eg 36 = ew E 36) by reflexivity. assert (Eg33 : ew Eg 33 = ew E 33) by reflexivity. assert (Eg2 : ew Eg 2 = ew E 2) by reflexivity.
unfold st_ok. split; [exact S1|]. split; [rewrite S2, Spc, Hpc; reflexivity|]. split; [exact S3|]. split; [rewrite S4, Srv, Hrv; reflexivity|]. split; [exact S5|]. split; [exact S6|]. split; [|split].
-   intros r. rewrite (S7 r).
pose proof (proj1 (forallb_forall _ _) g0_regs_check' r (all_regs_in r)) as Cr. apply orb_prop in Cr as [Cr|Cr].
+ cbn [existsb] in Cr. rewrite !orb_true_iff in Cr. destruct Cr as [Cr|[Cr|[Cr|Cr]]]; try discriminate; apply bv_eqb_eq in Cr; subst r.
* rewrite G11, H11. cbn [sv_denot]. unfold Eg. rewrite ew_ewset_other by lia. rewrite (proj1 HA 37%nat) by lia. unfold E00. rewrite E0_cx by lia. cbn [cs]. reflexivity.
* rewrite G12, H12. cbn [sv_denot]. unfold Eg. rewrite ew_ewset_other by lia. rewrite (proj1 HA 38%nat) by lia. unfold E00. rewrite E0_cx by lia. cbn [cs]. rewrite E34. reflexivity.
* rewrite G19, H19. apply word_eq. cbn [sv_denot]. unfold Eg. rewrite ew_ewset_other by lia. rewrite alu64_sll, (proj1 HA 10%nat) by lia. unfold E00. rewrite (E0_reg regs _ 10) by lia.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : reg) by (apply bv_eq; reflexivity). rewrite R10, E36, !Z.add_0_r, (lit64_small 1) by lia.
rewrite (lit64_small (SCT + 2 * sc)) by lia. change (1 mod 64) with 1. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite !Z_to_bv_bv_unsigned. rewrite !lit64_small by lia. rewrite Z.mod_small by lia. lia.
+ apply andb_prop in Cr as [C1 C2]. apply sv_eqb_eq in C1. unfold Eg. rewrite (sv_denot_ewset_free 34 _ E _ C2), C1. reflexivity.
-   rewrite Gmem. rewrite Smem in S8. pose proof S8 as (_ & MOK & PD).
split; [exact Gwf|]. split.
+ cbn [app]. cbn [forallb] in Gfree. apply andb_prop in Gfree as [Fsct Frest].
apply Forall_cons; [apply (region_ok_ewset_free 34 _ E); [exact Fsct | exact (proj1 (Forall_forall _ _) MOK R_sct ltac:(apply in_app_iff; left; right; left; reflexivity))]|].
apply Forall_cons.
*   apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_act base_val]; rewrite Eg33; change (bv_unsigned (ew E 33)) with (base_val E (Some 33%nat)); rewrite B33; [lia | lia | intros; lia |].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val' Eg _ _ _ 8 _ 0); [cbn [sv_denot]; unfold Eg; rewrite ew_ewset_same; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia |].
replace (YN0j.LOCK + 8 * sc + 88) with (YN0j.CTX + 80 + 8 * sc) by lia. exact HB.
* apply Forall_forall. intros r' Hr'. apply (region_ok_ewset_free 34 _ E); [exact (proj1 (forallb_forall _ _) Frest r' Hr') | exact (proj1 (Forall_forall _ _) MOK r' ltac:(apply in_app_iff; right; exact Hr'))].
+
cbn [app pairwise_disjoint all_disjoint]. cbn [app pairwise_disjoint all_disjoint] in PD. destruct PD as (Dm0 & Dsct & Dact & Drest).
assert (AD : forall rr l, all_disjoint E rr l -> r_base rr <> Some 34%nat -> (forall r', In r' l -> r_base r' <> Some 34%nat) -> all_disjoint Eg rr l).
{ intros rr l. induction l as [|x l IH]; cbn; [auto|]. intros [D1 D2] Hb Hl. split; [| apply IH; [exact D2 | exact Hb | intros r'' H''; apply Hl; right; exact H'']].
unfold extent_disjoint in *. unfold Eg. rewrite !base_val_ewset_other; [exact D1 | apply Hl; left; reflexivity | exact Hb]. }
assert (BS : forall r', In r' (tl (ss_mem ss_hd)) -> r_base r' <> Some 34%nat).
{ intros r' Hr' Eb. pose proof (in_map (fun r => (r_base r, r_lo r, r_hi r, r_wlo r, r_whi r)) _ _ Hr') as Hin'. rewrite MEM0_skel in Hin'. cbn [In] in Hin'.
decompose [or] Hin'; try contradiction; match goal with H : _ = (r_base r', _, _, _, _) |- _ => injection H as Eb' _ _ _ _ end; rewrite Eb in Eb'; discriminate. }
split; [| split; [apply (all_disjoint_ext Eg (R_actW (SLit 0))); [reflexivity..|]; apply AD; [exact Dact | discriminate | exact BS] |]].
* split; [| apply AD; [exact (proj2 Dsct) | discriminate | exact BS]].
unfold extent_disjoint. cbn [r_base r_lo r_hi R_sct R_act base_val]. rewrite Eg33, Eg36.
change (bv_unsigned (ew E 33)) with (base_val E (Some 33%nat)). change (bv_unsigned (ew E 36)) with (base_val E (Some 36%nat)). rewrite B33, (base_atom E 36 (SCT + 2 * sc) E36) by lia. lia.
* clear - Drest AD BS. revert Drest BS. generalize (tl (ss_mem ss_hd)) as l. intros l. induction l as [|x l IH]; cbn; [auto|]. intros [D1 D2] BS. split; [| apply IH; [exact D2 | intros r' H'; apply BS; right; exact H']].
apply AD; [exact D1 | apply BS; left; reflexivity | intros r' H'; apply BS; right; exact H'].
-   rewrite Gfacts. cbn [ss_facts] in Sat. unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok app] in Sat |- *.
destruct Sat as (_ & F36 & F35 & F33 & F34 & F2 & F10 & F11 & _).
assert (AF : forall k f, k <> 34%nat -> afact_ok E k f -> afact_ok Eg k f) by (intros k f Hk Hf; unfold afact_ok in *; unfold Eg; rewrite ew_ewset_other by exact Hk; exact Hf).
split; [repeat (split; [apply AF; [discriminate | assumption] |]) |].
+ split; [unfold afact_ok, F_hd, Eg; cbn [af_lo af_hi af_al2]; rewrite ew_ewset_same, (lit64_small 0) by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia|].
repeat (split; [apply AF; [discriminate | assumption] |]). exact I.
+ split; [|exact I]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b C_hd0 sv_denot]. unfold Eg. rewrite ew_ewset_same, (lit64_small 0) by lia. apply branch_eq.
Qed.
Lemma F_done fuel : (forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= S (S fuel))%nat -> SEG_group_at fuel ->
mreal src0segs (mkCfg ms1 md) (ibind (alloc_group (S fuel) sc n s1f) KS) (POST X L A regs mem md sc stk g).
Proof.
intros HU Hbud Hneed SG.
pose proof s1f_facts as (HI1 & Hhd1 & UB1 & SX1 & M1 & RX1 & FS1 & TC1 & UBe & Hlen1 & _).
pose proof F_ctx as (MID1 & FR1 & _ & AMA1 & BND1 & RSV1 & SPOK1 & AUXP1 & PRE1 & Hg1).
assert (AT : at_st L s1f regs (ms_mem ms1) sc g 0 M0 ss_G0 (WS regs) md (mkCfg ms1 md)).
{ exists Eg, ms1. split; [reflexivity|]. split; [exact G0_st_ok|]. split; [exact Eg_agree|]. intros x _ _. reflexivity. }
pose proof (SG X U L s1f regs (ms_mem ms1) md sc n stk g 0 M0 HI1 RX1 AMA1 BND1 RSV1 SPOK1 Hsc Hn MID1 AUXP1 PRE1 Hstk R10 R11 Hg1 HU Hbud Hneed) as SGB.
eapply mreal_mono; [| exact (from_G0 X U L s1f regs (ms_mem ms1) md sc n stk HI1 RX1 AMA1 BND1 RSV1 SPOK1 MID1 AUXP1 PRE1 Hstk AMH g 0 M0 fuel (mkCfg ms1 md) Hhd1 SGB AT)].
intros r c' P. exact (POST_transport s1f (ms_mem ms1) r c' SX1 UBe RX1 FR1 P).
Qed.
End o0.
Theorem stage_F fuel : (forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= S (S fuel))%nat -> SEG_group_at fuel ->
SR src0segs (mkCfg ms md) (fun c' => mreal src0segs c' (ibind (alloc_group (S fuel) sc n s1f) KS) (POST X L A regs mem md sc stk g)).
Proof.
intros HU Hbud Hneed SG. eapply SR_mono; [exact F_run|]. intros c' (ms1 & -> & HS2 & HF). exact (F_done ms1 HS2 HF fuel HU Hbud Hneed SG).
Qed.
End n0.
Theorem fall_main fuel : (forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= S (S fuel))%nat -> SEG_group_at fuel -> FALL_hyp fuel.
Proof.
intros HU Hbud Hneed SG Hfr0 Hnx00. red. rewrite alloc_slot_tree, (try_avail_slow A sc m0 am0 Hhd Mg0 Hav0), (stepA_D1 X U A sc m0 am0 HI Hsc Mg0 Hfr0 Hnx00).
cbn [ibind KA fst snd]. unfold after_try. cbn [fst snd Z.eqb negb].
eapply mreal_SR_pre; [exact (reach_hd X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk R10 R11 g Hg 0 M0)|].
intros c1 (E & ms & -> & HS & HA & HF).
eapply mreal_SR_pre; [exact (stage_F Hfr0 Hnx00 E ms HS HA HF fuel HU Hbud Hneed SG)|]. intros c' H. exact H.
Qed.
Theorem slice_slow : forall fuel, FALL_hyp fuel -> mreal src0segs (mkCfg ms0 md) (alloc_slot (S (S fuel)) sc n A) (POST X L A regs mem md sc stk g).
Proof.
intros fuel FALL. pose proof md_factsS as (Mh & Mlz & _).
destruct (links0 X U A sc m0 am0 HI Hsc Hhd Mg0) as (pr & nx & ampr & amnx & Hpr & Hnx & _).
destruct (Z.eq_dec (am_freed am0) 0) as [Efr|Hfr]; [destruct (sptr_eq_dec nx m0) as [Enx|Hne]; [apply FALL; [exact Efr | rewrite <- Enx; exact Hnx]|]|];
(rewrite alloc_slot_tree, (try_avail_slow A sc m0 am0 Hhd Mg0 Hav0));
(eapply mreal_SR_pre; [exact (reach_hd X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk R10 R11 g Hg 0 M0)|]);
intros c1 (E & ms & -> & HS & HA & HF);
[ destruct (stage_A E ms HS HA HF ltac:(right; unfold nx0; rewrite Hnx; exact Hne)) as (v & AC & EQA & [am1 B1] & FS1 & SRA)
| destruct (stage_A E ms HS HA HF ltac:(left; exact Hfr)) as (v & AC & EQA & [am1 B1] & FS1 & SRA) ];
rewrite EQA; cbn [ibind KA fst snd];
rewrite (TA_B_eval X U A sc (s1v v) (nx0) am1 B1), ibind_assoc;
(eapply mreal_SR_pre; [exact SRA|]); intros c2 (E2 & ms2 & -> & HS2 & HA2 & E40 & _ & RX1 & MID1 & FR1);
destruct (stage_B (s1v v) nx0 am1 E2 ms2 B1 HS2 HA2 E40 RX1 MID1 FR1) as (vb & BC & EQB & B2 & SRB);
rewrite EQB; cbn [ibind fst snd].
all: assert (FS2 : fsim (s2v (s1v v) nx0 am1 vb)) by (apply (fsim_metas (s1v v)); [exact FS1 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (s2_facts (s1v v) nx0 am1 B1 RX1 vb))))))]).
all: set (s2 := s2v (s1v v) nx0 am1 vb) in *; set (m2 := m2v nx0 am1 vb) in *; set (am2 := am2v (s1v v) nx0 am1 vb) in *.
all: destruct (links2 X U A sc Hsc s2 m2 am2 B2) as (pr2 & nxt2 & amn & _ & Hnxt2 & _);
destruct (Z.eq_dec (Z.land (am_freed am2) (ones (am_aidx am2))) 0) as [Ec|Nc]; [destruct (sptr_eq_dec nxt2 m2) as [En2|Nn2]|].
all: try ((eapply mreal_SR_pre; [exact SRB|]); intros c3 (E3 & ms3 & -> & HS3 & HA3 & E48 & E51 & RX2 & MID2 & FR2);
destruct (stage_C2 s2 m2 am2 E3 ms3 B2 HS3 HA3 E48 E51 RX2 MID2 FR2 Ec ltac:(rewrite <- En2; exact Hnxt2)) as (EQC & B3 & Hm3 & SRC);
rewrite (TA_C_eval X U A sc s2 m2 am2 B2), ibind_assoc, EQC; cbn [ibind fst snd];
rewrite (TA_D_eval X U A sc Hsc (s3S s2 m2 am2) m2 (am2' am2) B3 Hm3); cbn [ibind]; unfold after_try; cbn [fst snd];
pose proof (grp3 X U A sc Hsc (s3S s2 m2 am2) m2 (am2' am2) B3 Hm3) as (_ & _ & _ & _ & Mr & LB & _);
(replace (firstD (am2' am2) =? 0) with false by (symmetry; apply Z.eqb_neq; lia)); cbn [negb mreal];
assert (FS3 : fsim (s3S s2 m2 am2)) by (apply (fsim_upd s2 m2 am2 (am2' am2) FS2 (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B2)))); reflexivity);
(eapply SR_bind; [exact SRC|]); intros c4 (E4 & ms4 & -> & HS4 & HA4 & E80 & _ & RX3 & MID3 & FR3);
exact (stage_D (s3S s2 m2 am2) m2 (am2' am2) E4 ms4 B3 Hm3 HS4 HA4 E80 RX3 MID3 FR3 FS3)).
all: (eapply mreal_SR_pre; [exact SRB|]); intros c3 (E3 & ms3 & -> & HS3 & HA3 & E48 & E51 & RX2 & MID2 & FR2).
all: match goal with |- _ =>
first [ destruct (stage_C01 s2 m2 am2 E3 ms3 B2 HS3 HA3 E48 E51 RX2 MID2 FR2 ltac:(right; unfold nx2; fold am2; rewrite Hnxt2; exact Nn2)) as (vc & CC & EQC & B3 & Hm3 & SRC)
| destruct (stage_C01 s2 m2 am2 E3 ms3 B2 HS3 HA3 E48 E51 RX2 MID2 FR2 ltac:(left; exact Nc)) as (vc & CC & EQC & B3 & Hm3 & SRC) ] end.
all: rewrite (TA_C_eval X U A sc s2 m2 am2 B2), ibind_assoc, EQC; cbn [ibind fst snd].
all: set (s3 := s3v s2 m2 am2 vc) in *; set (m3 := m3v m2 am2 vc) in *; set (am3 := am3v s2 m2 am2 vc) in *.
all: rewrite (TA_D_eval X U A sc Hsc s3 m3 am3 B3 Hm3); cbn [ibind]; unfold after_try; cbn [fst snd].
all: pose proof (grp3 X U A sc Hsc s3 m3 am3 B3 Hm3) as (_ & _ & _ & _ & Mr & LB & _);
(replace (firstD am3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia)); cbn [negb mreal].
all: assert (FS3 : fsim s3) by (apply (fsim_metas s2); [exact FS2 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (s3_facts s2 m2 am2 B2 RX2 vc))))))]).
all: (eapply SR_bind; [exact SRC|]); intros c4 (E4 & ms4 & -> & HS4 & HA4 & E80 & _ & RX3 & MID3 & FR3).
all: exact (stage_D s3 m3 am3 E4 ms4 B3 Hm3 HS4 HA4 E80 RX3 MID3 FR3 FS3).
Qed.
End u.
Definition SEG_fall : Prop :=
forall fuel X U L A regs mem md sc n stk g m0 am0,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
active_hd A sc = Some m0 -> MT A m0 = Some (MUsed am0) -> am_avail am0 = 0 -> (forall k, U k = 0) ->
as_budget sc <= stk -> (need sc <= S (S fuel))%nat -> SEG_group_at fuel ->
FALL_hyp X L A regs mem md sc n stk g m0 am0 fuel.
Theorem src0_SEG_fall : alloc_meta_hyp B -> SEG_fall.
Proof.
intros AMH fuel X U L A regs mem md sc n stk g m0 am0 HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg Hhd Mg0 Hav0 HU Hbud Hneed SG.
exact (fall_main X U L A regs mem md sc n stk HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 AMH g Hg m0 am0 Hhd Mg0 Hav0 fuel HU Hbud Hneed SG).
Qed.
Theorem src0_SEG_head : alloc_meta_hyp B -> forall fuel, SEG_group_at fuel -> SEG_head_at fuel.
Proof.
intros AMH fuel SG X U L A regs mem md sc n stk g HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg Hhd HU Hbud Hneed.
destruct (active_hd A sc) as [m0|] eqn:Ehd; [|exfalso; exact (Hhd eq_refl)].
destruct (head_used X None U A sc m0 HI Hsc Ehd) as (am0 & Hu0 & Hs0). pose proof (proj1 (usedX_MT _ _ _ _ Hu0)) as Mg0.
destruct (Z.eq_dec (am_avail am0) 0) as [Hav0|Hav].
- apply (slice_slow X U L A regs mem md sc n stk HI RX AMA BND RSV SPOK Hsc Hn MID PRE Hstk R10 R11 g Hg m0 am0 Ehd Mg0 Hav0).
eapply src0_SEG_fall; eassumption.
- exact (slice_T1 X U L A regs mem md sc n stk HI RX AMA BND RSV SPOK Hsc Hn MID PRE Hstk R10 R11 g Hg m0 am0 Ehd Mg0 Hav fuel).
Qed.
Corollary src0_SEG_head_all : alloc_meta_hyp B -> SEG_group -> SEG_head.
Proof. intros AMH SG fuel. exact (src0_SEG_head AMH fuel (SG fuel)). Qed.
Theorem src0_SEG_head_partial : alloc_meta_hyp B -> True -> forall fuel, SEG_group_at fuel -> SEG_head_at fuel.
Proof. intros AMH _. exact (src0_SEG_head AMH). Qed.
End h.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
