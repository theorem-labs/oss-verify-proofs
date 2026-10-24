(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0v YK02 YP0n YM06 YK1j YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO14 YO0v YO0q YO0u YO15 YO10 YO12 YO11 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02
YN2b YN2e YN0g YN0d YN0c YN25 YN0a YN0p
YN2j YN2h YN2n YN2m YN2d YN2i
YN2k YN0j YN0h YN0i YN1k YN2w YN1d YN31 YN0z
YN13 YN1m YN15 YN16 YN17 YN18 YN12 YN1n YN1b
YN26 YN2a YN2u YN2p YN30 YN2v YN04 YN1o YN1c YN19.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Open Scope mm_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, DEB, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_debruijn32 in *.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma availN0_lo32 : forall E K, ew E 61 = Z_to_bv 64 K -> 1 <= K <= 32 ->
bv_unsigned (sv_denot E AVAILN) mod 2 ^ 32 = (2 ^ K - 1) mod 2 ^ 32.
Proof.
intros E K E61 HK. unfold AVAILN. cbn [sv_denot]. rewrite E61, (lit64_small K) by lia. rewrite alu64_add, sllw_rr_unsigned, !lit64_small by lia.
change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). rewrite sllw_2 by lia. rewrite (Z.mod_small (K + -1) 32) by lia. replace (K + -1 + 1) with K by lia.
unfold add64. rewrite mod64_mod32. rewrite <- Zplus_mod_idemp_l, sx32_mod32, Zplus_mod_idemp_l.
replace (2 ^ K + (2 ^ 64 - 1)) with (2 ^ K - 1 + 2 ^ 32 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma availN_lo32 : forall E K, ew E 61 = Z_to_bv 64 K -> 1 <= K <= 32 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 AVAILN) (SLit (-1)))) mod 2 ^ 32 = (ones (K - 1) - 1) mod 2 ^ 32.
Proof.
intros E K E61 HK. pose proof (availN0_lo32 E K E61 HK) as H0.
cbn [sv_denot] in H0 |- *. rewrite alu64_add, sext32_val, sx32_u64. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
unfold add64. rewrite mod64_mod32, <- Zplus_mod_idemp_l, sx32_mod32. rewrite H0, Zplus_mod_idemp_l. unfold ones.
replace (K - 1 + 1) with K by lia. replace (2 ^ K - 1 + (2 ^ 64 - 1)) with (2 ^ K - 1 - 1 + 2 ^ 32 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma freedN_lo32 : forall E K, ew E 61 = Z_to_bv 64 K -> 1 <= K <= 32 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 61 (-1))) (SAlu ALU_XOR (SExt true 32 AVAILN) (SLit (-1))))) mod 2 ^ 32 = 0.
Proof.
intros E K E61 HK. pose proof (availN0_lo32 E K E61 HK) as H0. unfold AVAILN in H0 |- *.
cbn [sv_denot] in H0 |- *. rewrite alu64_add, sllw_rr_unsigned, alu64_xor, sext32_val, sx32_u64.
set (u := bv_unsigned (alu64 ALU_ADD _ _)) in *.
rewrite E61, !lit64_small by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 K) + -1))) with (K - 1) by (rewrite (lit64_small K), lit64_small by lia; lia).
rewrite sllw_2 by lia. rewrite (Z.mod_small (K - 1) 32) by lia. replace (K - 1 + 1) with K by lia.
pose proof (sx32_range u) as Ru.
unfold add64. rewrite mod64_mod32.
rewrite <- Zplus_mod_idemp_r. rewrite <- (mod64_mod32 (Z.lxor (sx32 u) (Z.ones 64))). rewrite (lxor_ones_mod (sx32 u) Ru).
rewrite <- Zminus_mod_idemp_r, sx32_mod32, H0, Zminus_mod_idemp_r. rewrite Zplus_mod_idemp_r. rewrite <- Zplus_mod_idemp_l, sx32_mod32, Zplus_mod_idemp_l.
replace (2 ^ K + (2 ^ 64 - 1 - (2 ^ K - 1))) with (0 + 2 ^ 32 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma bitsN_val : forall E sc K, ew E 10 = Z_to_bv 64 sc -> ew E 61 = Z_to_bv 64 K -> 0 <= sc < 48 -> 1 <= K <= 32 ->
sv_denot E BITSN = Z_to_bv 64 ((K - 1) + 32 + 64 * sc).
Proof.
intros E sc K E10 E61 Hsc HK. unfold BITSN. apply (proj2 (word_eq _ _)). cbn [sv_denot].
rewrite E10, E61, (lit64_small sc), (lit64_small K), Z.add_0_r by lia.
rewrite alu64_add, alu64_or, alu64_or, alu64_sll, alu64_and, !lit64_small by lia. change (6 mod 64) with 6.
rewrite sll64_small by (change (2 ^ 6) with 64; lia). change (2 ^ 6) with 64.
replace (Z.land (K + -1) 31) with (K - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; lia).
rewrite Z.lor_0_r. replace (sc * 64) with (2 ^ 6 * sc) by (change (2 ^ 6) with 64; lia).
rewrite (lor_add_high' (K - 1) sc 6 ltac:(change (2 ^ 6) with 64; lia) ltac:(lia)).
rewrite add64_small by (change (2 ^ 6) with 64; lia). change (2 ^ 6) with 64. lia.
Qed.
Lemma aidxN_byte : forall E K, ew E 61 = Z_to_bv 64 K -> 1 <= K <= 32 -> 0 <= bv_unsigned (ew E 95) <= 255 ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SAlu ALU_AND (SOff 95 0) (SLit 224)) (SAlu ALU_AND (SOff 61 (-1)) (SLit 31)))) mod 2 ^ 8
= Z.lor (Z.land (bv_unsigned (ew E 95)) 224) (K - 1)
/\ 0 <= Z.lor (Z.land (bv_unsigned (ew E 95)) 224) (K - 1) < 256 /\ (Z.lor (Z.land (bv_unsigned (ew E 95)) 224) (K - 1)) mod 32 = K - 1.
Proof.
intros E K E61 HK H95. set (b := bv_unsigned (ew E 95)) in *.
assert (HB : 0 <= Z.land b 224 < 2 ^ 8).
{ split; [apply Z.land_nonneg; lia|]. apply (Z.le_lt_trans _ b); [| lia]. apply zland_le_l; lia. }
assert (HR : 0 <= Z.lor (Z.land b 224) (K - 1) < 2 ^ 8) by (apply lor_range; lia).
split; [| split; [exact HR|]].
- cbn [sv_denot]. rewrite E61, (lit64_small K), Z.add_0_r, Z_to_bv_bv_unsigned by lia. fold b. rewrite alu64_or, !alu64_and, !lit64_small by lia.
change 31 with (Z.ones 5). rewrite Z.land_ones, (Z.mod_small (K + -1) (2 ^ 5)) by lia. replace (K + -1) with (K - 1) by lia. apply Z.mod_small. exact HR.
- change 32 with (2 ^ 5). rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, <- Z.land_assoc. change (Z.land 224 (Z.ones 5)) with 0. rewrite Z.land_0_r, Z.lor_0_l.
rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma usageN_val : forall E u K, ew E 97 = Z_to_bv 64 u -> ew E 61 = Z_to_bv 64 K -> 0 <= u < 2 ^ 48 -> 1 <= K <= 32 ->
sv_denot E (SAlu ALU_ADD (SOff 61 0) (SOff 97 0)) = Z_to_bv 64 (u + K).
Proof.
intros E u K E97 E61 Hu HK. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E97, E61, (lit64_small u), (lit64_small K), !Z.add_0_r by lia.
rewrite alu64_add, !lit64_small by lia. rewrite add64_small by lia. lia.
Qed.
Lemma hdrN_byte : forall E idx, ew E 64 = Z_to_bv 64 idx -> 0 <= idx <= 31 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 64 0) (SLit 31)) (SLit 192))) mod 2 ^ 8 = (idx + 192) mod 2 ^ 8.
Proof.
intros E idx E64 Hi. cbn [sv_denot]. rewrite E64, (lit64_small idx), Z.add_0_r by lia. rewrite alu64_add, alu64_and, !lit64_small by lia.
change 31 with (Z.ones 5). rewrite Z.land_ones, (Z.mod_small idx (2 ^ 5)) by lia. rewrite add64_small by lia. reflexivity.
Qed.
Section s.
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
Variables (j1 j2 : Z).
Hypothesis HU : forall k, U k = 0.
Hypothesis HB : as_budget sc <= stk.
Variable fuel : nat.
Hypothesis HN : (need sc <= S (S fuel))%nat.
Hypothesis IH : ASH fuel.
Let sp : Z := bv_unsigned (getr regs 2).
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let sv_cs' := sv_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let nu : Z := cs L A sc g j1 j2 35.
Local Notation POSTn := (POST X L A regs mem md sc stk g).
Section NA.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis AK1 : as_keep X A s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis Km : In m (keys s1).
Hypothesis NXm : memb m X = false.
Hypothesis US1 : forall g' am, usedX (m :: X) s1 g' am <-> usedX X A g' am.
Hypothesis ACT1 : st_active s1 = st_active A.
Hypothesis LEN1 : (length (st_regions A) <= length (st_regions s1))%nat.
Hypothesis LE1 : layout_le A L L1.
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Hypothesis VM1 : exists vm', md1 = with_vmmaps vm' md.
Hypothesis FR1 : forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s1 x ->
mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis ERRW1 : forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a.
Variable E : env.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis E40 : ew E 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis E56 : ew E 56 = Z_to_bv 64 (usage_of s1 sc).
Hypothesis E61 : ew E 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc)).
Hypothesis E62 : ew E 62 = Z_to_bv 64 (16 * nu * initial_cnt sc (usage_of s1 sc)).
Let K : Z := initial_cnt sc (usage_of s1 sc).
Let k : Z := nu * K.
Let total : Z := 16 * k + 12.
Let j : Z := jof k.
Hypothesis ARM : class_size sc * K + UNIT <= PGSZ / 2.
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Local Notation FRM1n := (FRM1 regs mem1).
Let key_factsR' := key_factsR U L A regs sc g j1 j2 fuel HN.
Let mslot_zeroR' := mslot_zeroR U L A regs sc g j1 j2 fuel HN.
Let owned_low_mid' := owned_low_mid U L A regs sc g j1 j2 fuel HN.
Let active_word_mid' := active_word_mid U L A regs sc g j1 j2 fuel HN.
Let ctr_bytes_mid' := ctr_bytes_mid L A regs sc g j1 j2 fuel HN.
Let owned_mono' := owned_mono X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk g j1 j2 fuel HN.
Let nonmap_keep' := nonmap_keep X U L A regs mem md sc n stk HI Hsc Hn MID PRE Hstk g j1 j2 fuel HN.
Let XC1n' : Xclean (m :: X) s1 := XC1n X m s1 RX1 Mm.
Let rawX1' : rawX (m :: X) s1 := rawX1 X m s1 RX1 Mm.
Let facts_N' := facts_N X U L A regs mem md sc HI Hsc MID g j1 j2 fuel HN s1 LEN1 ARM.
Let statics1' := statics1 L A regs mem sc stk PRE Hstk g j1 j2 fuel HN s1 L1 mem1 md1 LEN1 MID1.
Local Notation NRbase' := (NRbase X L A regs md sc stk g j1 j2 m s1 L1 mem1 E).
Local Notation NRpost' := (NRpost X U L A regs md sc stk g j1 j2 m s1 L1 mem1 E).
Section NC.
Variables (idx : Z) (sq : astate) (L' : layout) (mem' : word -> option byte) (md' : Model) (E' : env) (hg : sptr) (am : ameta).
Hypothesis NRB : NRbase' sq L' mem' md' E'.
Hypothesis Hidx0 : 0 <= idx.
Hypothesis E64 : ew E' 64 = Z_to_bv 64 idx.
Hypothesis HIq : Inv (m :: X) (Some (hg, idx)) U sq.
Hypothesis Hhd : active_hd sq j = Some hg.
Hypothesis Uhg : usedX (m :: X) sq hg am.
Hypothesis Hscj : am_sc am = j.
Hypothesis Hfit : total + IB <= stride_of am.
Hypothesis HidxL : idx <= am_last am.
Hypothesis E80 : ew E' 80 = Z_to_bv 64 (ptr_addr L' hg).
Hypothesis E81 : ew E' 81 = Z_to_bv 64 (st_mmap_counter sq).
Variable ms0 : machine_state.
Hypothesis HS0 : st_ok src0segs E' (ss_NRs j) ms0.
Hypothesis Hmm0 : ms_mem ms0 = mem'.
Let Mhq : m_halted md' = None := proj1 (mid_md _ _ _ _ _ (proj1 (proj2 NRB))).
Let Mlzq : m_vm_lazy md' = [] := proj1 (proj2 (mid_md _ _ _ _ _ (proj1 (proj2 NRB)))).
Lemma sq_facts : layout_le s1 L1 L' /\ midrep B L' sq mem' md' /\ ama_ok sq /\ bounded sq /\ rsv_ok sq /\ span_ok sq /\
as_keep (m :: X) s1 sq /\ ub_same s1 sq /\ heads_below s1 sq j /\ (exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp - stk <= x < sp) -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) ->
~ owned B L1 s1 x -> ~ owned B L' sq x -> ~ in_nonmap_region L' sq x -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)) /\
(forall a, (sp - stk <= a < sp - 144 \/ ERRNO <= a < ERRNO + 4) -> writable_at src0segs mem' a) /\
word_mem src0segs mem' GUARD g /\ env_agree 64 E E' /\
Xclean (m :: X) sq /\ In m (keys sq) /\ rawm sq m /\ ptr_addr L' m = ptr_addr L1 m /\ rawX (m :: X) sq /\ env_agree 40 E00 E' /\ ew E' 40 = Z_to_bv 64 (ptr_addr L1 m).
Proof.
pose proof NRB as (LE' & MID' & AMA' & BND' & RSV' & SPOK' & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE).
assert (RXq : rawX (m :: X) sq) by exact (rawX_keep (m :: X) s1 sq rawX1' AK').
repeat (split; [assumption|]). split.
{ intros x am' Hx Hu. destruct (RXq x Hx) as [Mq|Mq]; rewrite Mq in Hu; discriminate. }
split; [exact (proj1 (inv_X HIq m (or_introl eq_refl)))|].
split; [exact (RXq m (or_introl eq_refl))|].
split.
{ destruct (key_factsR' (m :: X) None L1 s1 mem1 md1 m HI1 MID1 Km) as (_ & _ & _ & _ & PR). destruct LE' as (_ & _ & _ & Y4).
unfold ptr_addr. rewrite !loc_addr_LMem, (Y4 (prid m) PR). reflexivity. }
split; [exact RXq|].
split; [eapply env_agree_trans; [exact HA | eapply env_agree_le; [| exact HAE]; lia]|].
rewrite (proj1 HAE 40%nat) by lia. exact E40.
Qed.
Let NXq : memb m X = false := NXm.
Let HidxB : 0 <= idx <= am_last am := conj Hidx0 HidxL.
Lemma nfacts : In k KSET /\ (j = 15 \/ j = 19 \/ j = 23) /\ class_size j = csz j /\ total + IB <= class_size j /\ 28 <= k <= 126 /\
total = UNIT + K * class_size sc - IB /\ sc <= 23 /\ sc < j /\ 0 <= j < 48 /\ 2 <= K <= 32 /\ 1 <= nu /\
size_to_class (totalN sc K) = j /\ totalN sc K = total /\ (sc <= 26 -> 2 <= K) /\ active_hd sq sc = None /\ csn 34 = 0 /\ active_hd A sc = None.
Proof.
pose proof facts_N' as (HK & Hj & J3 & Hcs & Hfit' & Hk & Etot & H23 & Hscj' & NN & Hj48 & HKr & Hnu).
pose proof sq_facts as (_ & _ & _ & _ & _ & _ & _ & _ & HBel & _).
destruct cs_facts' as (_ & _ & C34 & _ & _ & _ & HD & _).
assert (Etn : totalN sc K = total) by (unfold totalN; symmetry; exact Etot).
assert (ACT : csn 34 = 0).
{ destruct (NR_shapes j J3) as (_ & _ & _ & _ & _ & FC & _).
assert (HC : In (mkAC BC_EQ (SOff 34 0) (SLit 0)) (f_conds (ss_facts (ss_NRs j)))) by (change (ss_facts (ss_NRs j)) with facts_NR; rewrite FC; left; reflexivity).
pose proof (st_ok_cond E' (ss_NRs j) ms0 _ HS0 HC) as T. cbn [ac_c ac_a ac_b] in T.
pose proof sq_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HA' & _).
assert (E34 : ew E' 34 = Z_to_bv 64 (csn 34)) by (exact (agree_cs' E' 34 HA' ltac:(lia))).
rewrite (den_off0 E' 34 (csn 34) E34), den_lit, branch_eq, !lit64_small in T by lia. apply Z.eqb_eq in T. exact T. }
assert (HA0 : active_hd A sc = None) by (apply (proj1 HD); exact ACT).
assert (HQ0 : active_hd sq sc = None).
{ rewrite (HBel sc) by (split; [exact (proj1 Hsc) | exact Hscj']). unfold active_hd. rewrite ACT1. exact HA0. }
repeat (split; [assumption |]). split; [rewrite Etn; exact Hj|]. split; [exact Etn|]. split; [intros _; exact (proj1 HKr)|].
split; [exact HQ0|]. split; [exact ACT | exact HA0].
Qed.
Let NSq := fun (Hsc26 : sc <= 26 -> 2 <= K) (HhdN : active_hd sq sc = None) (Ej : size_to_class (totalN sc K) = j) (Mraw : rawm sq m) (RXq : rawX (m :: X) sq) => tt.
Local Notation P0 := (ptr_addr L' (pN am idx)).
Local Notation G := (ptr_addr L' hg).
Local Notation ST := (stride_of am).
Local Notation sNq := (sN sq m hg am idx sc K j).
Local Notation amNq := (amN m am idx sc K).
Local Notation amEq := (amE am idx j).
Lemma geoN : exists kr ko GLO rg,
am_mem am = SP kr ko /\ ly_reg L' kr = GLO /\ ST = class_size j /\ pN am idx = SP kr (ko + UNIT + ST * idx) /\ P0 = GLO + ko + 16 + ST * idx /\
region_of sq kr = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ 0 <= ko /\
ko + 16 + ST * (am_last am + 1) <= rg_len rg /\ 0 <= ST * idx /\ ST * idx + ST <= ST * (am_last am + 1) /\
4096 <= GLO /\ GLO + rg_len rg <= alloc_ceiling /\ GLO mod 4096 = 0 /\ ko mod 16 = 0 /\ ST mod 16 = 0 /\
(forall x, GLO <= x < GLO + rg_len rg -> ~ in_img B x /\ present mem' x) /\
In (LMem (SP kr 0), rg_len rg) (footprint sq) /\
(forall q x, In q (keys sq) -> ptr_addr L' q <= x < ptr_addr L' q + 40 -> ~ (GLO <= x < GLO + rg_len rg)) /\
4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall x, G <= x < G + 40 -> ~ in_img B x /\ present mem' x) /\ In hg (keys sq) /\
total + IB <= ST /\ 16 <= ST /\ ST * (am_last am + 1) < 2 ^ 20.
Proof.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
pose proof (proj1 alloc_ceiling_val) as AC.
pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc ltac:(lia) H26 ARM HidxB Ej) as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & _ & Sp & Khg & NXhg).
destruct (pN_region X U sq m hg am idx sc K j HIq Uhg Hscj Hsc ltac:(lia) H26 ARM HidxB Ej) as (kr & ko & rg & Emem & EpN & Hr & Hrk & Hrl & Hko & Hfit2 & P1 & P2 & Hko16 & Hst16 & InR).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID') kr rg Hr Hrl) as (Ral & R4096 & Rceil & Rimg).
pose proof (used_group_region (m :: X) (Some (hg, idx)) U sq hg am HIq Uhg) as (rg' & Hr' & _ & _ & _ & Hext & _). rewrite Emem in Hr', Hext. cbn [prid poff] in Hr', Hext. rewrite Hr in Hr'. injection Hr' as <-.
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' hg HIq MID' Khg) as (RBg & ALg & _).
exists kr, ko, (ly_reg L' kr), rg.
split; [exact Emem|]. split; [reflexivity|]. split; [exact Hstr|]. split; [exact EpN|].
split; [rewrite EpN; unfold ptr_addr; cbn [loc_addr]; unfold UNIT; lia|].
split; [exact Hr|]. split; [exact Hrk|]. split; [exact Hrl|]. split; [exact Hko|].
split; [unfold group_extent, UNIT, IB in Hext; lia|]. split; [exact P1|]. split; [exact P2|].
split; [exact R4096|]. split; [exact Rceil|]. split; [unfold PGSZ in Ral; exact Ral|]. split; [exact Hko16|]. split; [exact Hst16|].
split; [intros x Hx; split; [exact (Rimg x Hx) | exact (memrep_present B L' sq mem' kr rg x (mid_mem _ _ _ _ _ MID') Hr Hrk Hrl Hx)]|].
split; [exact InR|].
split.
{ intros q x Hq Hx HG.
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' q HIq MID' Hq) as (_ & _ & _ & (a & ka & Ha & Hka & Eq) & _).
pose proof (inv_areas HIq) as (_ & Hareas & _). destruct (Hareas a Ha) as (r & o & rga & Ear & Ho & Hlo & Hra & Hla & Hlen & Hknd).
assert (Hne : (LMem a, PGSZ) <> (LMem (SP kr 0), rg_len rg)).
{ intros EE. injection EE as E1 _. rewrite Ear in E1. injection E1 as -> _. rewrite Hr in Hra. injection Hra as <-. rewrite Hrk in Hknd. exact Hknd. }
assert (Hina : In (LMem a, PGSZ) (footprint sq)) by (right; apply in_app_iff; left; apply in_map_iff; eexists; split; [reflexivity | exact Ha]).
pose proof (mid_layout _ _ _ _ _ MID') as (_ & _ & PW & _).
assert (PG : ptr_addr L' a <= x < ptr_addr L' a + PGSZ) by (rewrite Eq in Hx; unfold slot_of in Hx; rewrite ptr_addr_padd in Hx; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia).
destruct (pairwise_map_In ranges_disjoint (crange L') (footprint sq) _ _ PW Hina InR Hne) as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; unfold ptr_addr in PG; rewrite Ear in PG, D; cbn [loc_addr] in PG; clear - D PG HG; lia. }
split; [destruct (RBg G ltac:(unfold META_SIZE; lia)) as (_ & _ & R0); lia|].
split; [destruct (RBg (G + 39) ltac:(unfold META_SIZE; lia)) as (_ & _ & R0); lia|].
split; [exact ALg|]. split; [intros x Hx; destruct (RBg x ltac:(unfold META_SIZE; lia)) as (P & NI & _); exact (conj NI P)|].
split; [exact Khg|]. split; [exact Hfit|]. split; [exact Sp | exact Gext].
Qed.
Definition WD0 (x : Z) : Prop := WSn x \/ ptr_addr L1 m <= x < ptr_addr L1 m + 40.
Lemma WD0_low : forall x, x < alloc_ceiling -> ~ (ptr_addr L1 m <= x < ptr_addr L1 m + 40) -> ~ WD0 x.
Proof. intros x Hx Hm [Hw|Hw]; [| exact (Hm Hw)]. pose proof pre_facts' as (_ & _ & P3 & _). unfold WS, ASF in *. lia. Qed.
Lemma enf_call : forall ms1, st_ok src0segs E' (ss_NE j) ms1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WD0 x -> ms_mem ms1 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) ->
exists regsF memF,
msteps src0segs ms1 (mkst regsF (Z_to_bv 64 PS_RAE) memF (seg_rom src0segs)) /\
getr regsF 10 = Z_to_bv 64 P0 /\
(forall r : reg, ~ YN04.eclob r -> getr regsF r = getr (ms_regs ms1) r) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (P0 - 4 <= x < P0) -> memF (Z_to_bv 64 x) = ms_mem ms1 (Z_to_bv 64 x)) /\
mbyte src0segs memF (P0 - 4) = Some (Z_to_bv 8 0) /\ mbyte src0segs memF (P0 - 3) = Some (Z_to_bv 8 idx) /\
(forall k, (k < 2)%nat -> mbyte src0segs memF (P0 - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ST * idx / 16) 2 k))) /\
(forall a, ms_mem ms1 a <> None -> memF a <> None) /\
(forall x, writable_at src0segs (ms_mem ms1) x -> writable_at src0segs memF x).
Proof.
intros ms1 HS1 F1.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc ltac:(lia) H26 ARM HidxB Ej) as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & Hhdr & Sp & Khg & NXhg).
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & _ & Gext').
destruct (NE_regs j J3) as (RG & MEMe & PCe & FAe & RVe).
pose proof HS1 as (_ & _ & _ & _ & _ & _ & Hregs & Hmem & HFacts).
set (regs1 := ms_regs ms1) in *. set (mm1 := ms_mem ms1) in *.
assert (Ems : ms1 = mkst regs1 (Z_to_bv 64 src0_A_enframe) mm1 (seg_rom src0segs)) by (rewrite <- PCe; exact (st_ok_mkst E' (ss_NE j) ms1 HS1 RVe)).
assert (RD : forall r v, In (r, v) (combine [1; 2; 4; 10; 11; 12; 13; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
[SLit PS_RAE; SOff 2 (-144); SLit TP; SOff 80 0; SOff 64 0; SLit (csz j - 4); SExt true 32 (SOff 81 0);
SOff 10 0; SOff 40 0; SOff 61 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SLit SCT; SOff 26 0; SOff 27 0]) ->
getr regs1 r = sv_denot E' v).
{ intros r v Hin. unfold regs_at in RG. rewrite <- (regs_at_In _ _ _ r v RG Hin). apply Hregs. }
set (Mb := ptr_addr L' (am_mem am)). set (cls := znth j size_classes). set (c64 := bv_unsigned (getr regs1 13)).
assert (Ecls : class_size j = cls * 16) by (unfold class_size, UNIT; subst cls; lia).
assert (M1F : YN04.mapped1 (am_last am) (am_maplen am) = false).
{ unfold YN04.mapped1. pose proof (inv_groups HIq hg am Uhg) as (_ & _ & _ & Gcl & _).
destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. destruct (C26 ltac:(lia)) as [C|C]; [rewrite C; reflexivity|].
destruct (am_maplen am =? 0); [reflexivity|]. cbn [negb andb]. apply Z.eqb_neq. exact C. }
assert (STE : YN04.stride (am_last am) (am_maplen am) cls = ST) by (unfold YN04.stride; rewrite M1F, Hstr; lia).
assert (STA : YN04.start Mb idx (am_last am) (am_maplen am) cls = P0) by (unfold YN04.start; rewrite STE, EP0; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; lia).
assert (Hml52 : am_maplen am < 2 ^ 52).
{ pose proof (inv_groups HIq hg am Uhg) as (_ & _ & _ & _ & Gmp & _). destruct (Z_lt_dec 0 (am_maplen am)) as [Hpos|]; [|lia].
destruct (Gmp Hpos) as (r & rg2 & Em' & Hr2 & _ & Hl2 & Hlen2 & _). destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID') _ _ Hr2 Hl2) as (_ & A1 & A2 & _). unfold PGSZ in Hlen2. lia. }
assert (LOWEQ : forall x, x < alloc_ceiling -> 0 <= x -> ~ (ptr_addr L1 m <= x < ptr_addr L1 m + 40) -> mm1 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros x Hx H0 Hm. apply F1; [clear - Hx H0 AC; lia | exact (WD0_low x Hx Hm)]. }
pose proof (YN0i.keys_apart (m :: X) (Some (hg, idx)) U L' sq regs mem' md' HIq MID' m hg Kmq Khg ltac:(intros EE; rewrite EE in NXhg; cbn in NXhg; rewrite sptr_eqb_refl in NXhg; discriminate)) as APm. rewrite Eqm in APm. unfold META_SIZE in APm.
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' hg HIq MID' Khg) as (RBg & ALg & CELLg & _).
rewrite (proj1 (usedX_MT _ _ _ _ Uhg)) in CELLg.
assert (HGoff : forall y, G <= y < G + 40 -> mm1 (Z_to_bv 64 y) = mem' (Z_to_bv 64 y)).
{ intros y Hy. apply LOWEQ; [clear - Hy G2; lia | clear - Hy G1; lia | clear - Hy APm; lia]. }
assert (Hbits : word_mem src0segs mm1 (G + 32) (YN04.bits (am_last am) j (am_maplen am))).
{ apply (word_mem_ext1 mem'); [intros kk Hkk; apply HGoff; clear - Hkk; lia|].
pose proof (memrep_cell B L' sq mem' _ (mid_mem _ _ _ _ _ MID') (CELLg _ ltac:(cbn; do 5 right; left; reflexivity))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C. rewrite loc_addr_padd_ in C. unfold META_bits in C.
unfold YN04.bits. rewrite <- Hscj, <- meta_bits_enc. exact C. }
assert (HM : word_mem src0segs mm1 (G + 16) Mb).
{ apply (word_mem_ext1 mem'); [intros kk Hkk; apply HGoff; clear - Hkk; lia|].
pose proof (memrep_cell B L' sq mem' _ (mid_mem _ _ _ _ _ MID') (CELLg _ ltac:(cbn; do 2 right; left; reflexivity))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C. rewrite loc_addr_padd_ in C. unfold META_mem in C. exact C. }
destruct (so_size_classes _ (mid_syms _ _ _ _ _ MID') (Z.to_nat j) ltac:(lia)) as (clo & chi & Hlo & Hhi & Hsum). rewrite Z2Nat.id in Hlo, Hhi by lia.
assert (Hcls : YN04.mapped1 (am_last am) (am_maplen am) = false -> j < 48 /\
mbyte src0segs mm1 (src0_D_size_classes + 2 * j) = Some clo /\ mbyte src0segs mm1 (src0_D_size_classes + 2 * j + 1) = Some chi /\ bv_unsigned clo + 256 * bv_unsigned chi = cls).
{ intros _. pose proof (st_tables _ _ (mid_statics _ _ _ _ _ MID')) as STB. pose proof (mid_syms _ _ _ _ _ MID') as SO.
cbn [ms_segs ms_size_classes src0_msyms] in Hlo, Hhi, STB. unfold table_addr in STB. cbn [ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms] in STB.
assert (IMG2 : forall d, 0 <= d < 96 -> mm1 (Z_to_bv 64 (src0_D_size_classes + d)) = mem' (Z_to_bv 64 (src0_D_size_classes + d))).
{ intros d Hd. pose proof (so_img_hi _ SO (src0_D_size_classes + d)) as Hhi'. pose proof (m_range X U m s1 L1 mem1 md1 HI1 Km MID1) as MR.
assert (SO1 : static_owned B (src0_D_size_classes + d)) by (unfold static_owned, table_addr; cbn; lits; clear - Hd; lia).
apply LOWEQ; [apply Hhi'; apply (so_statics_img _ SO); exact SO1 | clear - Hd; lits; lia |].
intros Hmx. destruct (MR _ Hmx) as [NI _]. apply NI. apply (so_statics_img _ SO). exact SO1. }
split; [clear - Hj48; lia|]. split; [| split; [| subst cls; unfold znth; rewrite <- Hsum; reflexivity]].
- rewrite (mbyte_ext1 mem' mm1) by (apply (IMG2 (2 * j)); clear - Hj48; lia). rewrite STB by (clear - Hj48; lia). exact Hlo.
- rewrite (mbyte_ext1 mem' mm1) by (replace (src0_D_size_classes + 2 * j + 1) with (src0_D_size_classes + (2 * j + 1)) by (clear; lia); apply (IMG2 (2 * j + 1)); clear - Hj48; lia). rewrite STB by (clear - Hj48; lia). exact Hhi. }
assert (SLOT : forall x, P0 - 4 <= x < P0 + ST - 4 -> GLO <= x < GLO + rg_len rg) by (intros x Hx; clear - Hx EP0 HfitR P1' P2' Hko; lia).
assert (SLOTEQ : forall x, P0 - 4 <= x < P0 + ST - 4 -> mm1 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros x Hx. specialize (SLOT x Hx). apply LOWEQ; [clear - SLOT Rceil; lia | clear - SLOT R4096; lia | intros Hmx; apply (KEYS m x Kmq); [rewrite Eqm; exact Hmx | exact SLOT] ]. }
assert (PRES1 : forall x, P0 - 4 <= x < P0 + ST - 4 -> present mm1 x).
{ intros x Hx. destruct (RNG x (SLOT x Hx)) as [_ [b Hb]]. exists b. rewrite (SLOTEQ x Hx). exact Hb. }
assert (Hc4 : mbyte src0segs mm1 (YN04.start Mb idx (am_last am) (am_maplen am) cls - 4) = Some (Z_to_bv 8 0)).
{ rewrite STA. rewrite (mbyte_ext1 mem' mm1) by (apply SLOTEQ; clear - Sp; lia).
assert (Hin : In (slot_chk am idx) (image sq)).
{ unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (hg, am). split; [apply (used_metas_iff sq hg am (proj1 (inv_keys HIq))); exact (proj1 (usedX_MT _ _ _ _ Uhg))|].
cbn [fst snd]. rewrite group_cells_eq. apply in_app_iff. right. apply in_flat_map. exists idx. split; [apply In_zseq; lia|]. rewrite slot_cells_eq. left. reflexivity. }
pose proof (memrep_cell B L' sq mem' _ (mid_mem _ _ _ _ _ MID') Hin) as C. unfold cell_mem, slot_chk in C. cbn [mc_loc mc_w mc_val sval_num] in C.
specialize (C 0%nat ltac:(lia)). rewrite loc_addr_padd_, Z.add_0_r in C. change (ptr_addr L' (slot_start am idx)) with P0 in C. replace (P0 + -4) with (P0 - 4) in C by lia. exact C. }
destruct (PRES1 (P0 - 3) ltac:(clear - Sp; lia)) as [b3 Hb3]. destruct (PRES1 (P0 - 2) ltac:(clear - Sp; lia)) as [b2lo Hb2lo]. destruct (PRES1 (P0 - 1) ltac:(clear - Sp; lia)) as [b2hi Hb2hi].
assert (MB : forall x b, mm1 (Z_to_bv 64 x) = Some b -> GLO <= x < GLO + rg_len rg -> mbyte src0segs mm1 x = Some b).
{ intros x b Hb Hx. rewrite mbyte_off_img; [exact Hb | clear - Hx R4096 Rceil AC; lia | intros Hi; exact (proj1 (RNG x Hx) (in_img1_img x Hi))]. }
assert (Hdisj : G + 24 <= YN04.start Mb idx (am_last am) (am_maplen am) cls - 4 \/ YN04.start Mb idx (am_last am) (am_maplen am) cls + YN04.stride (am_last am) (am_maplen am) cls <= G + 16).
{ rewrite STA, STE. destruct (Z_le_dec (G + 24) (P0 - 4)) as [|N1]; [left; assumption|]. right.
destruct (Z_le_dec (P0 + ST) (G + 16)) as [|N2]; [assumption|]. exfalso.
destruct (Z_lt_le_dec G (P0 - 4)).
- apply (KEYS hg (P0 - 4) Khg); [clear - N1 l; lia | apply SLOT; clear - Sp; lia].
- apply (KEYS hg G Khg); [clear; lia | ]. clear - N2 l EP0 HfitR P1' P2' Hko Sp. lia. }
destruct (enframe_steps mm1 (seg_rom src0segs) G Mb idx (ST - 4) c64 (am_last am) j (am_maplen am) cls clo chi b3 b2lo b2hi
ltac:(clear - Glast; lia) ltac:(clear - Hj48; lia) ltac:(clear - Gml Hml52; lia) ltac:(clear - G1 G2 AC; lia) Hbits HM Hcls
ltac:(subst c64; apply u64_range) ltac:(clear - HidxB Glast; lia) ltac:(rewrite STE; clear - Sp; lia)
ltac:(rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia)
ltac:(rewrite STE; clear - Gext' P1' P2' Sp; nia) Hc4
ltac:(rewrite STA; apply MB; [exact Hb3 | apply SLOT; clear - Sp; lia])
ltac:(rewrite STA; apply MB; [exact Hb2lo | apply SLOT; clear - Sp; lia])
ltac:(rewrite STA; apply MB; [exact Hb2hi | apply SLOT; clear - Sp; lia])
ltac:(unfold YN04.end_; rewrite STA, STE; intros x Hx; apply present_writable; apply PRES1; exact Hx)
Hdisj regs1
ltac:(rewrite (RD 10%bv (SOff 80 0)) by inlist; cbn [sv_denot]; rewrite E80, Z.add_0_r, u64_of_Z by (clear - G1 G2 AC; lia); reflexivity)
ltac:(rewrite (RD 11%bv (SOff 64 0)) by inlist; cbn [sv_denot]; rewrite E64, Z.add_0_r, u64_of_Z by (clear - HidxB Glast; lia); reflexivity)
ltac:(rewrite (RD 12%bv (SLit (csz j - 4))) by inlist; cbn [sv_denot]; rewrite Hstr, Hcs; reflexivity)
ltac:(subst c64; symmetry; apply Z_to_bv_bv_unsigned))
as (regsF & MS & RA0 & RF).
pose proof (geom_facts Mb idx (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi ltac:(subst c64; apply u64_range) ltac:(clear - HidxB Glast; lia) ltac:(rewrite STE; clear - Sp; lia)
ltac:(rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia)
ltac:(rewrite STE; clear - Gext' P1' P2' Sp; nia)) as (Go & Gs & Gq & Ge & Gr & Gqe & Gsl).
rewrite STE in Gs. rewrite STA in Gq.
assert (OFF0 : YN04.off (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi = 0) by (clear - Go Gs; lia).
pose proof (code_range Mb idx (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi ltac:(subst c64; apply u64_range) ltac:(clear - HidxB Glast; lia) ltac:(rewrite STE; clear - Sp; lia)
ltac:(rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia)
ltac:(rewrite STE; clear - Gext' P1' P2' Sp; nia)) as [Cr1 Cr2].
assert (RSV0 : YN04.reserved (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi = 0) by (unfold YN04.reserved in *; rewrite STE in *; clear - OFF0 Gr; lia).
assert (CODE0 : YN04.code (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi = 0) by (clear - Cr1 Cr2 RSV0; lia).
assert (H16 : YN04.hdr16v idx (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi = ST * idx / 16) by (unfold YN04.hdr16v; rewrite OFF0, STE; lia).
set (memF := YN04.memF mm1 Mb idx (ST - 4) c64 (am_last am) (am_maplen am) cls b3 b2lo b2hi) in *.
assert (R1 : getr regs1 1 = Z_to_bv 64 PS_RAE) by (rewrite (RD 1%bv (SLit PS_RAE)) by inlist; reflexivity).
rewrite R1 in MS. rewrite (ret_ok_even (Z_to_bv 64 PS_RAE)) in MS by (vm_compute; reflexivity).
exists regsF, memF. rewrite Ems.
split; [exact MS|]. split; [rewrite RA0, Gq, OFF0; f_equal; lia|]. split; [exact RF|].
pose proof (memF_hdr mm1 Mb idx (ST - 4) c64 (am_last am) j (am_maplen am) cls b3 b2lo b2hi
ltac:(clear - Glast; lia) ltac:(clear - Hj48; lia) ltac:(clear - Gml Hml52; lia) ltac:(subst c64; apply u64_range) ltac:(clear - HidxB Glast; lia) ltac:(rewrite STE; clear - Sp; lia)
ltac:(rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia)
ltac:(rewrite STE; clear - Gext' P1' P2' Sp; nia) Hc4) as (Fc4 & F3 & F16 & _).
fold memF in Fc4, F3, F16. rewrite STA in Fc4, F3, F16. rewrite OFF0, CODE0 in F3. cbn [Z.eqb] in F3. rewrite OFF0, H16 in F16. cbn [Z.eqb] in F16.
split; [| split; [exact Fc4 | split; [rewrite F3; f_equal; f_equal; lia | split; [exact F16 | split]]]].
- intros x Hx Hnw. cbn [ms_mem]. subst memF. apply (memF_frame mm1 Mb idx (ST - 4) c64 (am_last am) j (am_maplen am) cls b3 b2lo b2hi);
[clear - Glast; lia | clear - Hj48; lia | clear - Gml Hml52; lia | subst c64; apply u64_range | clear - HidxB Glast; lia | rewrite STE; clear - Sp; lia
| rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia
| rewrite STE; clear - Gext' P1' P2' Sp; nia | exact Hx |].
unfold YN04.written, YN04.end_. rewrite STA, Gq, OFF0, STE. clear - Hnw. lia.
- intros a0 Ha0. cbn [ms_mem] in Ha0. subst memF. apply (memF_present mm1 Mb idx (ST - 4) c64 (am_last am) j (am_maplen am) cls b3 b2lo b2hi);
[clear - Glast; lia | clear - Hj48; lia | clear - Gml Hml52; lia | subst c64; apply u64_range | clear - HidxB Glast; lia | rewrite STE; clear - Sp; lia
| rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia
| rewrite STE; clear - Gext' P1' P2' Sp; nia | exact Ha0].
- intros x Hx. cbn [ms_mem] in Hx. subst memF. apply (memF_writable mm1 Mb idx (ST - 4) c64 (am_last am) j (am_maplen am) cls b3 b2lo b2hi);
[clear - Glast; lia | clear - Hj48; lia | clear - Gml Hml52; lia | subst c64; apply u64_range | clear - HidxB Glast; lia | rewrite STE; clear - Sp; lia
| rewrite STE; subst Mb; rewrite Emem; unfold ptr_addr; cbn [loc_addr]; clear - EGLO R4096 Rceil AC Hko HfitR P1' P2'; lia
| rewrite STE; clear - Gext' P1' P2' Sp; nia | exact Hx].
Qed.
Lemma NF_shapes : forall jj, jj = 15 \/ jj = 19 \/ jj = 23 ->
ss_regs (junk_regs NE_JUNK 83 (mkSS PS_RAE (sr_set (ss_regs (ss_NE jj)) 10 (SOff 82 0)) [] None (mkFacts [] [] []))) = ss_regs ss_NF
/\ regs_atoms_lt 82 (ss_regs (ss_NE jj)) = true /\ regs_atoms_lt 94 (ss_regs ss_NF) = true
/\ ss_mem ss_NF = R_q :: mem_NR /\ ss_facts ss_NF = facts_NF /\ ss_pc ss_NF = PS_RAE /\ ss_resv ss_NF = None
/\ facts_atoms_lt 82 facts_NR = true /\ forallb (region_atoms_lt 82) mem_NR = true
/\ mem_NR = [R_mslot; R_frame; R_got; R_guard; R_pgsz; R_tabs] /\ regions_wf (R_q :: mem_NR) = true.
Proof. intros jj [->|[->| ->]]; vm_compute; repeat split; reflexivity. Qed.
Definition WD1 (x : Z) : Prop := WD0 x \/ P0 - 4 <= x < P0.
Lemma station_NF : forall ms1 regsF memF,
st_ok src0segs E' (ss_NE j) ms1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WD0 x -> ms_mem ms1 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) ->
getr regsF 10 = Z_to_bv 64 P0 ->
(forall r : reg, ~ YN04.eclob r -> getr regsF r = getr (ms_regs ms1) r) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (P0 - 4 <= x < P0) -> memF (Z_to_bv 64 x) = ms_mem ms1 (Z_to_bv 64 x)) ->
mbyte src0segs memF (P0 - 3) = Some (Z_to_bv 8 idx) ->
(forall k, (k < 2)%nat -> mbyte src0segs memF (P0 - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ST * idx / 16) 2 k))) ->
(forall a, ms_mem ms1 a <> None -> memF a <> None) ->
(forall x, writable_at src0segs (ms_mem ms1) x -> writable_at src0segs memF x) ->
exists EF, st_ok src0segs EF ss_NF (mkst regsF (Z_to_bv 64 PS_RAE) memF (seg_rom src0segs)) /\
env_agree 82 E' EF /\ ew EF 82 = Z_to_bv 64 P0 /\ ew EF 94 = Z_to_bv 64 (ST * idx / 16) /\ 0 <= bv_unsigned (ew EF 95) <= 255.
Proof.
intros ms1 regsF memF HS1 F1 RA0 RF FF F3 F16 FP FW.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc ltac:(lia) H26 ARM HidxB Ej) as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & Hhdr & Sp & Khg & NXhg).
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & _ & Gext').
destruct (NE_regs j J3) as (RG & MEMe & PCe & FAe & RVe). destruct (NF_shapes j J3) as (RSH & AT82 & AT94 & MEMf & FAf & PCf & RVf & FAT82 & RAT & EmemNR & RWF).
pose proof HS1 as (_ & _ & _ & _ & _ & _ & Hregs & Hmem & HFacts). rewrite FAe in HFacts.
set (regs1 := ms_regs ms1) in *. set (mm1 := ms_mem ms1) in *.
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
assert (U40 : bv_unsigned (ew E' 40) = ptr_addr L1 m) by (rewrite E40'; destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; clear - R AC; lia).
assert (Er2 : ew E' 2 = getr regs 2) by (apply (agree_reg' E' 2 HA'); lia).
assert (SLOT : forall x, P0 - 4 <= x < P0 + ST - 4 -> GLO <= x < GLO + rg_len rg) by (intros x Hx; clear - Hx EP0 HfitR P1' P2' Hko; lia).
assert (P0R : 4096 <= P0 - 4 /\ P0 + ST - 4 <= alloc_ceiling /\ P0 mod 16 = 0).
{ split; [| split]; [clear - EP0 R4096 Hko P1'; lia | clear - Rceil Sp HfitR EP0 P1' P2' Hko; lia |].
rewrite EP0. rewrite Z.add_mod, (Z.add_mod (GLO + ko)), (Z.add_mod GLO) by lia. rewrite <- (Z.mod_mod_divide GLO 4096 16) by (exists 256; reflexivity).
rewrite Ral, Z.mul_mod, Hst16, Hko16 by lia. reflexivity. }
destruct P0R as (P0a & P0b & P0c).
set (E1 := ewset E' 82 (Z_to_bv 64 P0)).
assert (HA1 : env_agree 82 E' E1) by (apply env_agree_ewset).
set (base0 := mkSS PS_RAE (sr_set (ss_regs (ss_NE j)) 10 (SOff 82 0)) [] None (mkFacts [] [] [])).
assert (HSI : st_ok src0segs E1 base0 (mkst (regupd regs1 10 (getr regsF 10)) (Z_to_bv 64 PS_RAE) memF (seg_rom src0segs))).
{ unfold st_ok, mkst, base0; cbn. repeat (split; [reflexivity|]). split; [| split; [apply mem_ok_intro; [reflexivity | apply Forall_nil | exact I] | repeat split; apply Forall_nil || exact I]].
apply (regs_ok_set E1 (ss_regs (ss_NE j)) regs1 10 (getr regsF 10) (SOff 82 0)).
- eapply (regs_ok_agree 82 E' E1); [exact HA1 | exact AT82 | exact Hregs].
- cbn [sv_denot]. subst E1. rewrite ew_ewset_same, RA0, u64_of_Z, Z.add_0_r by (clear - P0a P0b Sp AC; lia). reflexivity. }
assert (AT83 : ss_atoms_lt 83 base0 = true).
{ unfold ss_atoms_lt, base0. cbn [ss_regs ss_mem ss_facts ss_resv mem_atoms_lt facts_atoms_lt forallb f_atoms f_conds f_alias andb].
rewrite (regs_atoms_lt_set 83 (ss_regs (ss_NE j)) 10 (SOff 82 0)); [reflexivity | apply (regs_atoms_lt_mono 82 83); [lia | exact AT82] | reflexivity]. }
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) NE_JUNK = true) by (vm_compute; reflexivity).
assert (EXT : forall r0, ~ In r0 NE_JUNK -> getr regsF r0 = getr (regupd regs1 10 (getr regsF 10)) r0).
{ apply (reg_cases_lit (fun r0 => ~ In r0 NE_JUNK -> getr regsF r0 = getr (regupd regs1 10 (getr regsF 10)) r0)).
intros r0 Hr0 Hnj. cbv [all_regs In] in Hr0.
repeat (destruct Hr0 as [<-|Hr0]; [ first [ solve [exfalso; apply Hnj; inlist]
| unfold getr, regupd, reg_get; rewrite bvmap_get_set_same; reflexivity
| rewrite getr_other by (intros HH; discriminate HH); apply RF; unfold YN04.eclob; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); discriminate HH ] |]).
destruct Hr0. }
destruct (st_ok_clobber src0segs NE_JUNK 83 E1 _ _ regsF (Z_to_bv 64 PS_RAE) memF (seg_rom src0segs) HSI AT83 NZ EXT) as (En2 & HA2 & HS2).
pose proof HS2 as (_ & _ & _ & _ & _ & _ & RR2 & _). subst base0. cbn [ss_regs ss_pc ss_mem ss_resv ss_facts] in RR2. rewrite RSH in RR2.
assert (B8 : exists b8, mbyte src0segs memF (P0 + 8) = Some b8).
{ destruct (RNG (P0 + 8) (SLOT (P0 + 8) ltac:(clear - Sp; lia))) as [NI [b Hb]].
assert (Hb1 : mm1 (Z_to_bv 64 (P0 + 8)) = Some b) by (rewrite (F1 (P0 + 8) ltac:(clear - P0a P0b Sp AC; lia)); [exact Hb|]; apply WD0_low; [clear - P0b Sp; lia | intros Hmx; exact (KEYS m (P0 + 8) Kmq ltac:(rewrite Eqm; exact Hmx) (SLOT (P0 + 8) ltac:(clear - Sp; lia)))]).
destruct (memF (Z_to_bv 64 (P0 + 8))) as [b8|] eqn:Eb8; [| exfalso; exact (FP _ ltac:(rewrite Hb1; discriminate) Eb8)].
exists b8. rewrite mbyte_off_img; [exact Eb8 | clear - P0a P0b Sp AC; lia | intros Hi; exact (NI (in_img1_img _ Hi))]. }
destruct B8 as [b8 Hb8]. pose proof (u8_range b8) as Rb8.
set (EF := ewset (ewset En2 94 (Z_to_bv 64 (ST * idx / 16))) 95 (Z_to_bv 64 (bv_unsigned b8))).
assert (HA23 : env_agree 94 En2 EF) by (subst EF; apply env_agree_ewset2; lia).
assert (HA3 : env_agree 82 E' EF) by (eapply env_agree_trans; [exact HA1 | eapply env_agree_le; [| eapply env_agree_trans; [exact HA2 | eapply env_agree_le; [| exact HA23]]]]; lia).
assert (H16r : 0 <= ST * idx / 16 <= 65535).
{ split; [apply Z.div_pos; clear - P1'; lia|].
assert (LT : ST * idx / 16 < 65536) by (apply Z.div_lt_upper_bound; [lia|]; clear - Gext' P1' P2' Sp; nia). clear - LT. lia. }
assert (EF_82 : ew EF 82 = Z_to_bv 64 P0) by (rewrite (proj1 HA23 82%nat), (proj1 HA2 82%nat) by lia; subst E1; apply ew_ewset_same).
assert (EF_94 : ew EF 94 = Z_to_bv 64 (ST * idx / 16)) by (subst EF; rewrite ew_ewset_other by lia; apply ew_ewset_same).
assert (EF_95 : ew EF 95 = Z_to_bv 64 (bv_unsigned b8)) by (subst EF; apply ew_ewset_same).
assert (EF_64 : ew EF 64 = Z_to_bv 64 idx) by (rewrite (proj1 HA3 64%nat) by lia; exact E64).
assert (U82 : bv_unsigned (ew EF 82) = P0) by (rewrite EF_82; apply u64_of_Z; clear - P0a P0b Sp AC; lia).
assert (U40' : bv_unsigned (ew EF 40) = ptr_addr L1 m) by (rewrite (proj1 HA3 40%nat) by lia; exact U40).
assert (U2 : bv_unsigned (ew EF 2) = sp) by (rewrite (proj1 HA3 2%nat) by lia; rewrite Er2; reflexivity).
exists EF. split; [| split; [exact HA3 | split; [exact EF_82 | split; [exact EF_94 | rewrite EF_95, u64_of_Z by (clear - Rb8; lia); clear - Rb8; lia]]]].
assert (LOWEQ : forall x, 0 <= x -> x < alloc_ceiling -> ~ (ptr_addr L1 m <= x < ptr_addr L1 m + 40) -> ~ (P0 - 4 <= x < P0) -> memF (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros x H0 Hx Hm Hp. rewrite (FF x ltac:(clear - H0 Hx AC; lia) Hp). apply F1; [clear - Hx H0 AC; lia | exact (WD0_low x Hx Hm)]. }
assert (IMGEQ : forall x, in_img B x -> memF (Z_to_bv 64 x) = mm1 (Z_to_bv 64 x)).
{ intros x Hx. pose proof (src0_img_range x Hx). apply FF; [clear - H AC; lia|].
intros Hp. exact (proj1 (RNG x (SLOT x ltac:(clear - Hp Sp; lia))) Hx). }
assert (OLDREG : forall r0, In r0 mem_NR -> region_ok src0segs EF memF r0).
{ intros r0 Hr0.
assert (RO : region_ok src0segs E' mm1 r0).
{ pose proof Hmem as (_ & RA & _). rewrite MEMe in RA. destruct (NR_shapes j J3) as (_ & _ & _ & MEMs & _). rewrite MEMs in RA.
rewrite Forall_forall in RA. apply RA. rewrite EmemNR in Hr0. cbn [In] in Hr0 |- *. clear - Hr0. tauto. }
assert (RA82 : region_atoms_lt 82 r0 = true) by (rewrite forallb_forall in RAT; exact (RAT r0 Hr0)).
apply (region_ok_agree src0segs 82 E' EF memF r0 HA3 RA82).
assert (WFr : region_wf r0 = true) by (rewrite EmemNR in Hr0; destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; reflexivity).
apply (region_ok_transport src0segs E' mm1 memF r0 RO WFr); [| intros x _ Hw; exact (FW x Hw)].
intros x Hx. rewrite EmemNR in Hr0.
destruct Hr0 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [r_base r_lo r_hi base_val R_mslot R_frame R_got R_guard R_pgsz R_tabs] in Hx; rewrite ?U40, ?Er2 in Hx.
-   apply mbyte_ext1. apply FF; [clear - Hx RBm AC; destruct (RBm x ltac:(lia)) as (_ & _ & R); lia|]. intros Hp. exact (KEYS m x Kmq ltac:(rewrite Eqm; clear - Hx; lia) (SLOT x ltac:(clear - Hp Sp; lia))).
-   apply mbyte_ext1. fold sp in Hx. unfold ASF in *. apply FF; [clear - Hx P3 P4 Hstk AC; lia|]. intros Hp. pose proof (SLOT x ltac:(clear - Hp Sp; lia)). clear - H Hx Rceil P3 Hstk. lia.
- apply mbyte_ext1. apply IMGEQ. apply src0_rwseg_img. lits. clear - Hx. lia.
- apply mbyte_ext1. apply IMGEQ. apply src0_rwseg_img. lits. clear - Hx. lia.
- apply mbyte_ext1. apply IMGEQ. apply src0_rwseg_img. lits. clear - Hx. lia.
- apply mbyte_ext1. apply IMGEQ. apply src0_tabs_img. lits. clear - Hx. lia. }
assert (MEM : mem_ok src0segs EF memF (ss_mem ss_NF)).
{ rewrite MEMf. apply mem_ok_intro.
- exact RWF.
- apply Forall_cons; [| apply Forall_forall; exact OLDREG].
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_q]; rewrite U82; [clear - P0a; lia | clear - P0b Sp AC; lia | |].
+ intros o Ho. apply FW. apply present_writable.
destruct (RNG (P0 + o) (SLOT (P0 + o) ltac:(clear - Ho Sp; lia))) as [NI [b Hb]]. exists b.
rewrite (F1 (P0 + o) ltac:(clear - P0a P0b Sp Ho AC; lia)); [exact Hb|]. apply WD0_low; [clear - P0b Sp Ho; lia|].
intros Hmx. exact (KEYS m (P0 + o) Kmq ltac:(rewrite Eqm; exact Hmx) (SLOT (P0 + o) ltac:(clear - Ho Sp; lia))).
+ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
* apply (chunk_ok_cval src0segs EF memF P0 (-3) 1 (SOff 64 0) idx); [apply den_off0; exact EF_64 | clear - HidxB Glast; lia |].
intros kk Hkk. destruct kk; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. replace (P0 + -3) with (P0 - 3) by lia. rewrite F3. f_equal. f_equal.
unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !(Z.mod_small idx 256) by (clear - HidxB Glast; lia). reflexivity.
* apply (chunk_ok_cval src0segs EF memF P0 (-2) 2 (SOff 94 0) (ST * idx / 16)); [apply den_off0; exact EF_94 | clear - H16r; lia |].
intros kk Hkk. replace (P0 + -2 + Z.of_nat kk) with (P0 - 2 + Z.of_nat kk) by lia. exact (F16 kk Hkk).
* apply (chunk_ok_cval src0segs EF memF P0 8 1 (SOff 95 0) (bv_unsigned b8)); [apply den_off0; exact EF_95 | clear - Rb8; lia |].
intros kk Hkk. destruct kk; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb8. f_equal. unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite !(Z.mod_small (bv_unsigned b8) 256) by (clear - Rb8; lia). symmetry. apply Z_to_bv_bv_unsigned.
- rewrite EmemNR. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [base_val r_base r_lo r_hi R_q R_mslot R_frame R_got R_guard R_pgsz R_tabs].
rewrite ?U82, ?U40', ?U2.
assert (IMGp : forall lo, in_img B lo -> ~ (P0 - 3 <= lo < P0 + 9)) by (intros lo Hlo Hx; exact (proj1 (RNG lo (SLOT lo ltac:(clear - Hx Sp; lia))) Hlo)).
assert (IMGm : forall lo, in_img B lo -> ~ (ptr_addr L1 m <= lo < ptr_addr L1 m + 40)) by (intros lo Hlo Hx; exact (proj1 (proj2 (RBm lo Hx)) Hlo)).
assert (Pm : P0 + 9 <= ptr_addr L1 m + 0 \/ ptr_addr L1 m + 40 <= P0 + -3).
{ destruct (Z_le_dec (P0 + 9) (ptr_addr L1 m)) as [|Hn1]; [left; lia|]. destruct (Z_le_dec (ptr_addr L1 m + 40) (P0 - 3)) as [|Hn2]; [right; lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) (P0 - 3)) as [Hl3|Hl3].
- apply (KEYS m (P0 - 3) Kmq); [rewrite Eqm; clear - Hn2 Hl3; lia | apply SLOT; clear - Sp; lia].
- apply (KEYS m (ptr_addr L' m) Kmq); [clear; lia | rewrite Eqm; apply SLOT; clear - Hn1 Hl3 Sp; lia]. }
pose proof (m_range X U m s1 L1 mem1 md1 HI1 Km MID1) as MR.
unfold ASF in *. lits.
repeat split; try (clear - Pm; lia); try (clear - P0a P0b Sp Rceil P3 Hstk; lia).
all: try match goal with
| |- ?h <= P0 + -3 \/ P0 + 9 <= ?l =>
destruct (Z_le_dec h (P0 - 3)); [left; lia|]; destruct (Z_le_dec (P0 + 9) l); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (P0 - 3) l);
[apply (IMGp l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGp (P0 - 3)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
| |- P0 + 9 <= ?l \/ ?h <= P0 + -3 =>
destruct (Z_le_dec (P0 + 9) l); [left; lia|]; destruct (Z_le_dec h (P0 - 3)); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (P0 - 3) l);
[apply (IMGp l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGp (P0 - 3)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
end.
all: try match goal with
| |- ?h <= ptr_addr L1 m + 0 \/ ptr_addr L1 m + 40 <= ?l =>
destruct (Z_le_dec h (ptr_addr L1 m)); [left; lia|]; destruct (Z_le_dec (ptr_addr L1 m + 40) l); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (ptr_addr L1 m) l);
[apply (IMGm l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGm (ptr_addr L1 m)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
| |- ptr_addr L1 m + 40 <= ?l \/ ?h <= ptr_addr L1 m + 0 =>
destruct (Z_le_dec (ptr_addr L1 m + 40) l); [left; lia|]; destruct (Z_le_dec h (ptr_addr L1 m)); [right; lia|]; exfalso;
destruct (Z_lt_le_dec (ptr_addr L1 m) l);
[apply (IMGm l); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]
| apply (IMGm (ptr_addr L1 m)); [first [apply src0_rwseg_img; lia | apply src0_tabs_img; lits; lia] | lia]]
end.
all: fold sp; clear - MR P3 P4 Hstk AC; try lia.
left. destruct (MR (ptr_addr L1 m + 39) ltac:(lia)) as [_ R]. lia. }
assert (FOK : facts_ok EF facts_NF).
{ unfold facts_NF. apply facts_ok_add_atom; [apply facts_ok_add_atom; [apply facts_ok_add_atom|]|].
- eapply (facts_ok_agree 82 E' EF); [exact HA3 | exact FAT82 | exact HFacts].
- unfold afact_ok, F_q. cbn [af_lo af_hi af_al2]. rewrite U82. change (2 ^ 4) with 16. assert (Ht : 460 <= total) by (subst total; clear - Hk; lia); unfold IB in HfitS; split; [clear - P0a P0b HfitS Ht AC; lia|]. split; [exact P0c | clear - P0b HfitS Ht AC; lia].
- unfold afact_ok, F_h16. cbn [af_lo af_hi af_al2]. rewrite EF_94, u64_of_Z by (clear - H16r; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - H16r. lia.
- unfold afact_ok, F_b8. cbn [af_lo af_hi af_al2]. rewrite EF_95, u64_of_Z by (clear - Rb8; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - Rb8. lia. }
unfold st_ok, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
pose proof HS2 as (T1 & T2 & T3 & T4 & T5 & T6 & _).
rewrite PCf, RVf, FAf.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [eapply (regs_ok_agree 94 En2 EF); [exact HA23 | exact AT94 | exact RR2] |].
split; [exact MEM | exact FOK].
Qed.
Definition SKs0 : list (option nat * Z * Z) := [(Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0)].
Definition SKs1 : list (option nat * Z * Z) := (Some 82%nat, -3, 9) :: SKs0.
Definition SKs2 : list (option nat * Z * Z) := (Some 33%nat, 88, 96) :: (Some 33%nat, 472, 480) :: SKs1.
Definition WD2 (x : Z) : Prop := WD0 x \/ P0 - 3 <= x < P0 + 9.
Definition WD3 (x : Z) : Prop := WD2 x \/ csn 33 + 88 <= x < csn 33 + 96 \/ csn 33 + 472 <= x < csn 33 + 480.
Lemma ivl_dec : forall a b x, {a <= x < b} + {~ (a <= x < b)}.
Proof. intros a b x. destruct (Z_le_dec a x); [destruct (Z_lt_dec x b); [left; lia | right; lia] | right; lia]. Qed.
Lemma WD3_dec : forall x, {WD3 x} + {~ WD3 x}.
Proof.
intros x. unfold WD3, WD2, WD0, WS.
destruct (ivl_dec (sp - ASF) sp x) as [H1|H1]; [left; left; left; left; exact H1|]. destruct (ivl_dec (ptr_addr L1 m) (ptr_addr L1 m + 40) x) as [H2|H2]; [left; left; left; right; exact H2|].
destruct (ivl_dec (P0 - 3) (P0 + 9) x) as [H3|H3]; [left; left; right; exact H3|]. destruct (ivl_dec (csn 33 + 88) (csn 33 + 96) x) as [H4|H4]; [left; right; left; exact H4|].
destruct (ivl_dec (csn 33 + 472) (csn 33 + 480) x) as [H5|H5]; [left; right; right; exact H5|]. right.
intros [[[H|H]|H]|[H|H]]; [exact (H1 H) | exact (H2 H) | exact (H3 H) | exact (H4 H) | exact (H5 H)].
Qed.
Lemma skelsS : forall jj, jj = 15 \/ jj = 19 \/ jj = 23 ->
wsub (ss_mem (ss_NRs jj)) SKs0 = true /\ wsub (ss_mem ss_NF) SKs1 = true /\ wsub (ss_mem ss_nz) SKs1 = true /\ wsub (ss_mem ss_NL) SKs1 = true /\ wsub (ss_mem ss_NT) SKs2 = true /\
ss_mem ss_NL = ss_mem ss_nz /\ ss_facts ss_NL = facts_NF /\ ss_pc ss_NL = PS_ZE /\ ss_resv ss_NL = None /\ ss_regs ss_NL = sr_set (sr_set (ss_regs ss_nz) 11 (SLit 0)) 12 (SOff 96 0) /\
regs_atoms_lt 96 (ss_regs ss_nz) = true /\ mem_atoms_lt 96 (ss_mem ss_nz) = true /\ facts_atoms_lt 96 facts_NF = true /\ ss_resv ss_nz = None /\
regs_atoms_lt 97 (ss_regs ss_nt0) = true /\ mem_atoms_lt 97 (ss_mem ss_nt0) = true /\ ss_resv ss_nt0 = None /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_nz) = [(Some 82%nat, -3, 9); (Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56); (None, DEB, DEB + 159)] /\
forallb region_wf (ss_mem ss_nz) = true /\ regions_wf (R_useN :: R_actW :: ss_mem ss_nz) = true.
Proof. intros jj [->|[->| ->]]; vm_compute; repeat split; reflexivity. Qed.
Lemma SKs0_WD0 : forall Ex b lo hi x, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) ->
In (b, lo, hi) SKs0 -> base_val Ex b + lo <= x < base_val Ex b + hi -> WD0 x.
Proof.
intros Ex b lo hi x HAx Ex40 Hin Hx. pose proof sq_facts as (_ & MID' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kmq & _ & Eqm & _).
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm. pose proof (proj1 alloc_ceiling_val) as AC.
unfold SKs0 in Hin. cbn [In] in Hin. unfold WD0, WS.
destruct Hin as [H|[H|[]]]; injection H as <- <- <-; cbn [base_val] in Hx.
- rewrite Ex40, u64_of_Z in Hx by (destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); clear - R AC; lia). right. lia.
- left. exact (YN13.win_stack L A regs sc g j1 j2 s1 Ex x HAx Hx).
Qed.
Lemma SKs1_WD2 : forall Ex b lo hi x, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew Ex 82 = Z_to_bv 64 P0 ->
In (b, lo, hi) SKs1 -> base_val Ex b + lo <= x < base_val Ex b + hi -> WD2 x.
Proof.
intros Ex b lo hi x HAx Ex40 Ex82 Hin Hx. unfold SKs1 in Hin. cbn [In] in Hin. unfold WD2.
destruct Hin as [H|Hin].
- injection H as <- <- <-. cbn [base_val] in Hx. destruct geoN as (kr & ko & GLO & rg & _ & _ & _ & _ & EP0 & _ & _ & _ & Hko & HfitR & P1' & P2' & R4096 & Rceil & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Sp & _).
pose proof (proj1 alloc_ceiling_val) as AC. rewrite Ex82, u64_of_Z in Hx by (clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia). right. clear - Hx. lia.
- left. exact (SKs0_WD0 Ex b lo hi x HAx Ex40 Hin Hx).
Qed.
Lemma SKs2_WD3 : forall Ex b lo hi x, env_agree 40 E00 Ex -> ew Ex 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew Ex 82 = Z_to_bv 64 P0 ->
In (b, lo, hi) SKs2 -> base_val Ex b + lo <= x < base_val Ex b + hi -> WD3 x.
Proof.
intros Ex b lo hi x HAx Ex40 Ex82 Hin Hx. unfold SKs2 in Hin. cbn [In] in Hin. unfold WD3.
assert (E33 : bv_unsigned (ew Ex 33) = csn 33) by (rewrite (agree_cs' Ex 33 HAx) by lia; apply u64_of_Z; destruct cs_facts' as (C33 & _); lits; lia).
destruct Hin as [H|[H|Hin]]; [injection H as <- <- <-; cbn [base_val] in Hx; rewrite E33 in Hx; right; left; lia
| injection H as <- <- <-; cbn [base_val] in Hx; rewrite E33 in Hx; right; right; lia |].
left. exact (SKs1_WD2 Ex b lo hi x HAx Ex40 Ex82 Hin Hx).
Qed.
Lemma den_s8 : forall Ex, ew Ex 35 = Z_to_bv 64 nu -> sv_denot Ex (SAlu ALU_SLL (SOff 35 0) (SLit 4)) = Z_to_bv 64 (16 * nu).
Proof.
intros Ex E35. destruct cs_facts' as (_ & _ & _ & C35 & _). fold nu in C35.
cbn [sv_denot]. rewrite E35. apply (proj2 (word_eq _ _)). rewrite alu64_sll. rewrite (lit64_small nu) by lia. rewrite Z.add_0_r, (lit64_small nu), (lit64_small 4), (lit64_small (16 * nu)) by lia.
change (4 mod 64) with 4. rewrite sll64_small by (change (2 ^ 4) with 16; lia). change (2 ^ 4) with 16. lia.
Qed.
Lemma station_NL : forall Ef ms2 regs3 mem3 va2,
st_ok src0segs Ef ss_nz ms2 -> env_agree 40 E00 Ef -> ew Ef 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew Ef 82 = Z_to_bv 64 P0 ->
(forall r : reg, r <> 11%bv -> r <> 12%bv -> getr regs3 r = getr (ms_regs ms2) r) ->
getr regs3 11 = Z_to_bv 64 0 -> getr regs3 12 = va2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (P0 + 12 <= x < P0 + ST) -> mem3 (Z_to_bv 64 x) = ms_mem ms2 (Z_to_bv 64 x)) ->
(forall x, writable_at src0segs (ms_mem ms2) x -> writable_at src0segs mem3 x) ->
st_ok src0segs (ewset Ef 96 va2) ss_NL (mkst regs3 (Z_to_bv 64 PS_ZE) mem3 (seg_rom src0segs)) /\ env_agree 96 Ef (ewset Ef 96 va2) /\ ew (ewset Ef 96 va2) 96 = va2.
Proof.
intros Ef ms2 regs3 mem3 va2 HS2 HAf Ef40 Ef82 RO Q11 Q12 F3 W3.
pose proof nfacts as (HK & J3 & _). pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & Sp & Gext').
destruct (skelsS j J3) as (_ & _ & _ & _ & _ & MEMl & FAl & PCl & RVl & RGl & RAT & MAT & FAT & RVz & _ & _ & _ & SKz & WFz & _).
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
set (El := ewset Ef 96 va2).
assert (HA6 : env_agree 96 Ef El) by (apply env_agree_ewset).
assert (U40 : bv_unsigned (ew Ef 40) = ptr_addr L1 m) by (rewrite Ef40; destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; clear - R AC; lia).
assert (U82 : bv_unsigned (ew Ef 82) = P0) by (rewrite Ef82; apply u64_of_Z; clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
assert (Er2 : ew Ef 2 = getr regs 2) by (apply (agree_reg' Ef 2 HAf); lia).
pose proof HS2 as (_ & _ & _ & _ & _ & _ & Hregs & Hmem & HFacts).
split; [| split; [exact HA6 | subst El; apply ew_ewset_same]].
unfold st_ok, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
rewrite PCl, RVl, RGl, MEMl, FAl.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{
intros r. pose proof (regs_ok_agree 96 Ef El _ (ms_regs ms2) HA6 RAT Hregs r) as HR.
destruct (bv_eqb r 12) eqn:E12; [apply bv_eqb_eq in E12; subst r; rewrite sr_get_set_same by reflexivity; cbn [sv_denot]; rewrite Q12; subst El; rewrite ew_ewset_same, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
assert (N12 : r <> 12%bv) by (intros HH; rewrite HH, (proj2 (bv_eqb_eq _ _) eq_refl) in E12; discriminate). rewrite (sr_get_set_other _ 12 r _ N12).
destruct (bv_eqb r 11) eqn:E11; [apply bv_eqb_eq in E11; subst r; rewrite sr_get_set_same by reflexivity; cbn [sv_denot]; exact Q11|].
assert (N11 : r <> 11%bv) by (intros HH; rewrite HH, (proj2 (bv_eqb_eq _ _) eq_refl) in E11; discriminate). rewrite (sr_get_set_other _ 11 r _ N11). rewrite (RO r N11 N12). exact HR. }
split.
{
pose proof Hmem as (WF2 & RA2 & PD2). split; [exact WF2|]. split; [| exact (pairwise_disjoint_agree 96 Ef El _ HA6 MAT PD2)].
rewrite Forall_forall in RA2 |- *. intros r0 Hr0.
assert (RA96 : region_atoms_lt 96 r0 = true) by (exact (proj1 (forallb_forall _ _) MAT r0 Hr0)).
apply (region_ok_agree src0segs 96 Ef El mem3 r0 HA6 RA96).
apply (region_ok_transport src0segs Ef (ms_mem ms2) mem3 r0 (RA2 r0 Hr0) (proj1 (forallb_forall _ _) WFz r0 Hr0)); [| intros x _ Hw; exact (W3 x Hw)].
intros x Hx. apply mbyte_ext1. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr0. rewrite SKz in Hr0. cbn [In] in Hr0.
destruct Hr0 as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3 in Hx; cbn [base_val] in Hx; rewrite ?U82, ?U40, ?Er2 in Hx; fold sp in Hx.
- apply F3; [clear - Hx EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia | clear - Hx; lia].
- apply F3; [destruct (RBm x ltac:(clear - Hx; lia)) as (_ & _ & R); clear - R AC; lia|]. intros Hp. apply (KEYS m x Kmq); [rewrite Eqm; clear - Hx; lia|]. clear - Hp EP0 HfitR P1' P2' Hko Sp. lia.
- unfold ASF in *. apply F3; [clear - Hx P3 P4 Hstk AC; lia|]. intros Hp. clear - Hp Hx EP0 HfitR P1' P2' Hko Rceil P3 Hstk. lia.
- apply F3; [lits; clear - Hx; lia|]. intros Hp. apply (proj1 (RNG x ltac:(clear - Hp EP0 HfitR P1' P2' Hko Sp; lia))). apply src0_rwseg_img. lits. clear - Hx. lia.
- apply F3; [lits; clear - Hx; lia|]. intros Hp. apply (proj1 (RNG x ltac:(clear - Hp EP0 HfitR P1' P2' Hko Sp; lia))). apply src0_rwseg_img. lits. clear - Hx. lia.
- apply F3; [lits; clear - Hx; lia|]. intros Hp. apply (proj1 (RNG x ltac:(clear - Hp EP0 HfitR P1' P2' Hko Sp; lia))). apply src0_rwseg_img. lits. clear - Hx. lia.
- apply F3; [lits; clear - Hx; lia|]. intros Hp. apply (proj1 (RNG x ltac:(clear - Hp EP0 HfitR P1' P2' Hko Sp; lia))). apply src0_tabs_img. lits. clear - Hx. lia. }
eapply (facts_ok_agree 96 Ef El); [exact HA6 | exact FAT |]. rewrite <- (proj2 (proj2 nz_regs)). exact HFacts.
Qed.
Lemma station_NT : forall El ms4,
st_ok src0segs El ss_nt0 ms4 -> env_agree 40 E00 El -> ew El 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew El 82 = Z_to_bv 64 P0 ->
(forall x, CTX <= x < CTX + CTX_SIZE -> ms_mem ms4 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) ->
st_ok src0segs (ewset El 97 (Z_to_bv 64 (usage_of sq sc))) ss_NT ms4 /\ env_agree 97 El (ewset El 97 (Z_to_bv 64 (usage_of sq sc))) /\
ew (ewset El 97 (Z_to_bv 64 (usage_of sq sc))) 97 = Z_to_bv 64 (usage_of sq sc).
Proof.
intros El ms4 HS4 HAl El40 El82 CTXK.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). destruct cs_facts' as (C33 & _).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & Sp & Gext').
destruct (skelsS j J3) as (_ & _ & _ & _ & _ & MEMl & FAl & PCl & RVl & RGl & _ & _ & _ & _ & RAT & MAT & RVt & SKz & WFz & RWF).
pose proof NT_shape as (ENT & MEMt & FAt & PCt).
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
destruct BNDq as (BU & _). pose proof (BU sc) as BUs.
set (Et := ewset El 97 (Z_to_bv 64 (usage_of sq sc))).
assert (HA7 : env_agree 97 El Et) by (apply env_agree_ewset).
assert (Et97 : ew Et 97 = Z_to_bv 64 (usage_of sq sc)) by (subst Et; apply ew_ewset_same).
assert (HAt : env_agree 40 E00 Et) by (eapply env_agree_trans; [exact HAl | eapply env_agree_le; [| exact HA7]; lia]).
assert (U33 : bv_unsigned (ew Et 33) = csn 33) by (rewrite (agree_cs' Et 33 HAt) by lia; apply u64_of_Z; lits; lia).
assert (U40 : bv_unsigned (ew Et 40) = ptr_addr L1 m) by (rewrite (proj1 HA7 40%nat), El40 by lia; destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; clear - R AC; lia).
assert (U82 : bv_unsigned (ew Et 82) = P0) by (rewrite (proj1 HA7 82%nat), El82 by lia; apply u64_of_Z; clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
assert (U2 : bv_unsigned (ew Et 2) = sp) by (rewrite (agree_reg' Et 2 HAt) by lia; reflexivity).
split; [| exact (conj HA7 Et97)].
pose proof (st_ok_agree src0segs 97 El Et ss_nt0 ms4 HS4 HA7 ltac:(unfold ss_atoms_lt; rewrite RAT, MAT, FAt, (proj2 (proj2 nz_regs)); vm_compute; reflexivity)) as HS5.
rewrite ENT.
assert (APART : forall lo hi r0, CTX <= lo -> lo < hi -> hi <= CTX + CTX_SIZE -> In r0 (ss_mem ss_nt0) ->
hi <= base_val Et (r_base r0) + r_lo r0 \/ base_val Et (r_base r0) + r_hi r0 <= lo).
{ intros lo hi r0 Hlo Hlh Hhi Hr0. rewrite MEMt in Hr0. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr0. rewrite SKz in Hr0. cbn [In] in Hr0.
pose proof (mid_syms _ _ _ _ _ MID') as SO.
destruct Hr0 as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?U82, ?U40, ?U2; fold sp; try (unfold CTX_SIZE in *; lits; lia).
- destruct (Z_le_dec (P0 + 9) lo) as [|Hn1]; [right; lia|]. left. destruct (Z_le_dec hi (P0 - 3)) as [|Hn2]; [lia|]. exfalso.
destruct (Z_lt_le_dec (P0 - 3) lo) as [Hl3|Hl3]; [apply (proj1 (RNG lo ltac:(clear - Hn1 Hl3 EP0 HfitR P1' P2' Hko Sp; lia))) | apply (proj1 (RNG (P0 - 3) ltac:(clear - EP0 HfitR P1' P2' Hko Sp; lia)))];
apply (so_ctx_img _ SO); change (ms_ctx B) with CTX; clear - Hlo Hlh Hhi Hn1 Hn2 Hl3; lia.
- destruct (Z_le_dec (ptr_addr L1 m + 40) lo) as [|Hn1]; [right; lia|]. left. destruct (Z_le_dec hi (ptr_addr L1 m)) as [|Hn2]; [lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) lo) as [Hl3|Hl3]; [destruct (RBm lo ltac:(lia)) as (_ & NI & _) | destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & NI & _)];
apply NI; apply (so_ctx_img _ SO); change (ms_ctx B) with CTX; clear - Hlo Hlh Hhi Hn1 Hn2 Hl3; lia. }
assert (HS6 : st_ok src0segs Et (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) ms4).
{ apply (st_ok_add_region src0segs Et _ _ R_actW HS5); [vm_compute; reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_actW]; rewrite U33; [lits; lia | lits; lia | |].
+ intros o Ho. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID') (ms_mem ms4) (csn 33 + o) ltac:(change (ms_ctx B) with CTX; cbn [cs]; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs Et (ms_mem ms4) (csn 33) 88 (SOff 34 0) 0); [apply den_off0; rewrite (agree_cs' Et 34 HAt) by lia; rewrite C34; reflexivity|].
apply (word_mem_ext1 mem'); [intros kk Hkk; apply CTXK; cbn [cs]; unfold CTX_SIZE; lits; lia|].
cbn [cs]. replace (LOCK + 8 * sc + 88) with (CTX + (CTX_active + 8 * Z.of_nat (Z.to_nat sc))) by (unfold CTX_active; lits; lia).
change 0 with (sval_num L' (optr None)). rewrite <- HhdN. unfold active_hd.
apply (ctx_word_gen L' sq mem' md' _ _ MID'); [| destruct (nth (Z.to_nat sc) (st_active sq) None); intros z; discriminate].
unfold ctx_cells. rewrite !in_app_iff. right. left. apply in_map_iff. exists (Z.to_nat sc). split; [reflexivity | apply in_seq; lia].
- apply Forall_forall. intros r0 Hr0. unfold extent_disjoint. cbn [r_base r_lo r_hi R_actW base_val]. rewrite U33. apply (APART (csn 33 + 88) (csn 33 + 96) r0); cbn [cs]; unfold CTX_SIZE; try (lits; lia). exact Hr0. }
assert (HS7 : st_ok src0segs Et (add_atom (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) 97 F_useN) ms4).
{ apply (st_ok_add_fact src0segs Et _ ms4 97 F_useN HS6). unfold afact_ok, F_useN. cbn [af_lo af_hi af_al2]. rewrite Et97, u64_of_Z by (clear - BUs; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - BUs. lia. }
change (st_ok src0segs Et (mkSS (ss_pc (add_atom (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) 97 F_useN))
(ss_regs (add_atom (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) 97 F_useN))
(R_useN :: ss_mem (add_atom (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) 97 F_useN))
(ss_resv (add_atom (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) 97 F_useN))
(ss_facts (add_atom (mkSS (ss_pc ss_nt0) (ss_regs ss_nt0) (R_actW :: ss_mem ss_nt0) None (ss_facts ss_nt0)) 97 F_useN))) ms4).
apply (st_ok_add_region src0segs Et _ _ R_useN HS7); [vm_compute; reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_useN]; rewrite U33; [lits; lia | lits; lia | |].
+ intros o Ho. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID') (ms_mem ms4) (csn 33 + o) ltac:(change (ms_ctx B) with CTX; cbn [cs]; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs Et (ms_mem ms4) (csn 33) 472 (SOff 97 0) (usage_of sq sc)); [apply den_off0; exact Et97|].
apply (word_mem_ext1 mem'); [intros kk Hkk; apply CTXK; cbn [cs]; unfold CTX_SIZE; lits; lia|].
cbn [cs]. exact (usage_word L' sq mem' md' sc MID' Hsc).
- apply Forall_cons; [unfold extent_disjoint; cbn [r_base r_lo r_hi R_actW R_useN base_val]; rewrite U33; first [left; lia | right; lia]|].
apply Forall_forall. intros r0 Hr0. unfold extent_disjoint. cbn [r_base r_lo r_hi R_useN base_val]. rewrite U33. apply (APART (csn 33 + 472) (csn 33 + 480) r0); cbn [cs]; unfold CTX_SIZE; try (lits; lia). exact Hr0.
Qed.
Definition FINpost (c : config) : Prop :=
exists En ms5, c = mkCfg ms5 md' /\ st_ok src0segs En ss_nE ms5 /\ env_agree 40 E00 En /\
ew En 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew En 82 = Z_to_bv 64 P0 /\ ew En 64 = Z_to_bv 64 idx /\ ew En 94 = Z_to_bv 64 (ST * idx / 16) /\
0 <= bv_unsigned (ew En 95) <= 255 /\ ew En 61 = Z_to_bv 64 K /\ ew En 97 = Z_to_bv 64 (usage_of sq sc) /\ ew En 10 = Z_to_bv 64 sc /\
(forall x, 0 <= x < 2 ^ 64 -> ~ WD3 x -> ~ (P0 - 4 <= x < P0) -> ~ (P0 + 12 <= x < P0 + ST) -> ms_mem ms5 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) /\
mbyte src0segs (ms_mem ms5) (P0 - 4) = Some (Z_to_bv 8 0) /\
(forall i, 0 <= i <= K -> ms_mem ms5 (Z_to_bv 64 (P0 + 12 + i * (16 * nu))) = Some (Z_to_bv 8 0)) /\
(forall x, P0 + 12 <= x < P0 + ST -> (forall i, 0 <= i <= K -> x <> P0 + 12 + i * (16 * nu)) -> ms_mem ms5 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) /\
(forall x, present mem' x -> 0 <= x < 2 ^ 64 -> ~ in_img B x -> present (ms_mem ms5) x).
Theorem reach_nE : SR src0segs (mkCfg ms0 md') FINpost.
Proof.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc ltac:(lia) H26 ARM HidxB Ej) as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & Hhdr & Sp & Khg & NXhg).
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & _ & Gext').
destruct (skelsS j J3) as (W0 & W1 & W2 & W3 & W4 & MEMl & FAl & PCl & RVl & RGl & _ & _ & _ & RVz & _ & _ & RVt & SKz & WFz & _).
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_enframe E' (ss_NRs j) (ss_NE j) RS_running); [exact Mhq | exact Mlzq | exact HS0 | exact (run_NRs j J3) |].
intros ms1 HS1 Hfr1.
assert (F1 : forall x, 0 <= x < 2 ^ 64 -> ~ WD0 x -> ms_mem ms1 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ rewrite <- Hmm0. apply (frame_keepN regs WD0 E' (ss_mem (ss_NRs j)) SKs0 (ms_mem ms0) _ (ms_mem ms0) Hfr1 W0); [intros b lo hi x Hin Hx; exact (SKs0_WD0 E' b lo hi x HA' E40' Hin Hx) | intros; reflexivity]. }
destruct (enf_call ms1 HS1 F1) as (regsF & memF & MS & RA0 & RF & FF & Fc4 & F3 & F16 & FP & FW).
eapply (SR_msteps src0segs _ _ md' _ Mhq Mlzq MS).
destruct (station_NF ms1 regsF memF HS1 F1 RA0 RF FF F3 F16 FP FW) as (EF & HSF & HAF & EF82 & EF94 & EF95).
assert (HAF' : env_agree 40 E00 EF) by (eapply env_agree_trans; [exact HA' | eapply env_agree_le; [| exact HAF]; lia]).
assert (EF40 : ew EF 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite (proj1 HAF 40%nat) by lia; exact E40').
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL EF ss_NF ss_nz); [exact Mhq | exact Mlzq | exact HSF | apply run_NF |].
intros ms2 HS2 Hfr2. cbn [ms_mem] in Hfr2.
assert (F2 : forall x, 0 <= x < 2 ^ 64 -> ~ WD2 x -> ms_mem ms2 (Z_to_bv 64 x) = memF (Z_to_bv 64 x)).
{ apply (frame_keepN regs WD2 EF (ss_mem ss_NF) SKs1 memF _ memF Hfr2 W1); [intros b lo hi x Hin Hx; exact (SKs1_WD2 EF b lo hi x HAF' EF40 EF82 Hin Hx) | intros; reflexivity]. }
pose proof HS2 as (_ & _ & _ & _ & _ & _ & Hregs2 & Hmem2 & _).
pose proof (st_ok_mkst EF ss_nz ms2 HS2 RVz) as Ems2. rewrite ss_nz_pc in Ems2.
destruct nz_regs as (RGz & _ & _).
assert (RD : forall r v, In (r, v) (combine [10; 11; 12; 24]%bv [SOff 82 0; SOff 61 1; SOff 82 12; SAlu ALU_SLL (SOff 35 0) (SLit 4)]) -> getr (ms_regs ms2) r = sv_denot EF v).
{ intros r v Hin. unfold regs_at in RGz. rewrite <- (regs_at_In _ _ _ r v RGz Hin). apply Hregs2. }
assert (EF61 : ew EF 61 = Z_to_bv 64 K) by (rewrite (proj1 HAF 61%nat), (proj1 HAE 61%nat) by lia; exact E61).
assert (EF35 : ew EF 35 = Z_to_bv 64 nu) by (exact (agree_cs' EF 35 HAF' ltac:(lia))).
assert (Q11 : getr (ms_regs ms2) 11 = Z_to_bv 64 (Z.of_nat (Z.to_nat (K + 1)))).
{ rewrite (RD 11%bv (SOff 61 1)) by inlist. cbn [sv_denot]. rewrite EF61, u64_of_Z by (clear - HKr; lia). f_equal. clear - HKr. lia. }
assert (Q12 : getr (ms_regs ms2) 12 = Z_to_bv 64 (P0 + 12)).
{ rewrite (RD 12%bv (SOff 82 12)) by inlist. cbn [sv_denot]. rewrite EF82, u64_of_Z by (clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia). reflexivity. }
assert (Q24 : getr (ms_regs ms2) 24 = Z_to_bv 64 (16 * nu)) by (rewrite (RD 24%bv (SAlu ALU_SLL (SOff 35 0) (SLit 4))) by inlist; exact (den_s8 EF EF35)).
assert (TOT : 12 + K * (16 * nu) + 4 <= ST) by (clear - HfitS Etot; subst total k; unfold UNIT, IB in *; nia).
destruct cs_facts' as (_ & _ & _ & C35 & _). fold nu in C35.
assert (NUK : 16 * nu <= 16 * 8191 /\ 0 <= (K + 1) * (16 * nu) <= 33 * (16 * 8191)) by (clear - C35 HKr; nia).
assert (LW : forall i : nat, (i < Z.to_nat (K + 1))%nat -> writable_at src0segs (ms_mem ms2) (P0 + 12 + Z.of_nat i * (16 * nu))).
{ intros i Hi. assert (Hii : 0 <= Z.of_nat i * (16 * nu) <= K * (16 * nu)) by (clear - Hi Hnu HKr; nia).
assert (RG : P0 - 4 <= P0 + 12 + Z.of_nat i * (16 * nu) <= P0 + ST - 4) by (clear - Hii TOT Hnu; nia).
set (t := Z.of_nat i * (16 * nu)) in *. clearbody t. set (t' := K * (16 * nu)) in *. clearbody t'.
apply (writable_ext1 memF); [apply F2; [clear - RG EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia|] | apply FW; apply present_writable].
- unfold WD2. intros [Hw|Hw]; [| clear - Hw Hii; lia].
revert Hw. apply (WD0_low (P0 + 12 + t)); [clear - RG EP0 Hko P1' P2' HfitR Rceil; lia|]. intros Hmx. apply (KEYS m (P0 + 12 + t) Kmq); [rewrite Eqm; exact Hmx | clear - RG EP0 HfitR P1' P2' Hko; lia].
- assert (RGN : GLO <= P0 + 12 + t < GLO + rg_len rg) by (clear - RG EP0 HfitR P1' P2' Hko; lia).
destruct (RNG (P0 + 12 + t) RGN) as [_ [b Hb]]. exists b. rewrite (F1 (P0 + 12 + t) ltac:(clear - RG EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia)); [exact Hb|].
apply WD0_low; [clear - RG EP0 Hko P1' P2' HfitR Rceil; lia|]. intros Hmx. apply (KEYS m (P0 + 12 + t) Kmq); [rewrite Eqm; exact Hmx | exact RGN]. }
rewrite Ems2.
destruct (zero_loop (Z.to_nat (K + 1)) (seg_rom src0segs) (ms_regs ms2) (ms_mem ms2) (P0 + 12) (16 * nu) ltac:(clear - HKr; lia) Q11 Q12 Q24
ltac:(clear - EP0 Hko P1' R4096; lia) ltac:(clear - Hnu; lia) ltac:(rewrite Z2Nat.id by (clear - HKr; lia); clear - NUK EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia) LW)
as (regs3 & MS3 & R11' & R12' & RO).
change (Z_to_bv 64 PS_ZL') with (Z_to_bv 64 PS_ZL) in MS3. change (Z_to_bv 64 PS_ZE') with (Z_to_bv 64 PS_ZE) in MS3.
eapply (SR_msteps src0segs _ _ md' _ Mhq Mlzq MS3).
set (mem3 := zmem (ms_mem ms2) (P0 + 12) (16 * nu) (Z.to_nat (K + 1))) in *.
assert (F3z : forall x, 0 <= x < 2 ^ 64 -> ~ (P0 + 12 <= x < P0 + ST) -> mem3 (Z_to_bv 64 x) = ms_mem ms2 (Z_to_bv 64 x)).
{ intros x Hx Hn'. subst mem3. apply zmem_other; [exact Hx | clear - EP0 Hko P1' R4096; lia | clear - Hnu; lia | rewrite Z2Nat.id by (clear - HKr; lia); clear - NUK EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia |].
intros i Hi Ei. apply Hn'. assert (Hii : 0 <= Z.of_nat i * (16 * nu) <= K * (16 * nu)) by (clear - Hi Hnu HKr; nia). clear - Ei Hii TOT Hnu. nia. }
destruct (station_NL EF ms2 regs3 mem3 _ HS2 HAF' EF40 EF82 RO R11' R12' F3z ltac:(intros x Hw; subst mem3; apply zmem_writable; exact Hw)) as (HS3 & HA6 & EL96).
set (EL := ewset EF 96 (Z_to_bv 64 (P0 + 12 + Z.of_nat (Z.to_nat (K + 1)) * (16 * nu)))) in *.
assert (HAL' : env_agree 40 E00 EL) by (eapply env_agree_trans; [exact HAF' | eapply env_agree_le; [| exact HA6]; lia]).
assert (EL40 : ew EL 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite (proj1 HA6 40%nat) by lia; exact EF40).
assert (EL82 : ew EL 82 = Z_to_bv 64 P0) by (rewrite (proj1 HA6 82%nat) by lia; exact EF82).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL EL ss_NL ss_nt0); [exact Mhq | exact Mlzq | exact HS3 | apply run_NL |].
intros ms4 HS4 Hfr4. cbn [ms_mem] in Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WD2 x -> ms_mem ms4 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
{ apply (frame_keepN regs WD2 EL (ss_mem ss_NL) SKs1 mem3 _ mem3 Hfr4 W3); [intros b lo hi x Hin Hx; exact (SKs1_WD2 EL b lo hi x HAL' EL40 EL82 Hin Hx) | intros; reflexivity]. }
assert (F4' : forall x, 0 <= x < 2 ^ 64 -> ~ WD2 x -> ~ (P0 - 4 <= x < P0) -> ~ (P0 + 12 <= x < P0 + ST) -> ms_mem ms4 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros x Hx Hw Hp Hl. rewrite (F4 x Hx Hw), (F3z x Hx Hl), (F2 x Hx Hw). rewrite (FF x Hx Hp).
apply F1; [exact Hx | intros Hw0; apply Hw; left; exact Hw0]. }
assert (CTXK : forall x, CTX <= x < CTX + CTX_SIZE -> ms_mem ms4 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros x Hx. pose proof (so_ctx_img _ (mid_syms _ _ _ _ _ MID') x ltac:(change (ms_ctx B) with CTX; exact Hx)) as Hi. pose proof (src0_img_range x Hi) as Ri.
apply F4'; [clear - Ri; lia | | intros Hl; exact (proj1 (RNG x ltac:(clear - Hl EP0 HfitR P1' P2' Hko Sp; lia)) Hi) | intros Hl; exact (proj1 (RNG x ltac:(clear - Hl EP0 HfitR P1' P2' Hko Sp; lia)) Hi)].
unfold WD2. intros [Hw|Hw]; [| exact (proj1 (RNG x ltac:(clear - Hw EP0 HfitR P1' P2' Hko Sp; lia)) Hi)].
revert Hw. apply WD0_low; [clear - Ri AC; lia | intros Hmx; exact (proj1 (proj2 (RBm x Hmx)) Hi)]. }
destruct (station_NT EL ms4 HS4 HAL' EL40 EL82 CTXK) as (HS5 & HA7 & ET97).
set (ET := ewset EL 97 (Z_to_bv 64 (usage_of sq sc))) in *.
assert (HAT' : env_agree 40 E00 ET) by (eapply env_agree_trans; [exact HAL' | eapply env_agree_le; [| exact HA7]; lia]).
assert (ET40 : ew ET 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite (proj1 HA7 40%nat) by lia; exact EL40).
assert (ET82 : ew ET 82 = Z_to_bv 64 P0) by (rewrite (proj1 HA7 82%nat) by lia; exact EL82).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL ET ss_NT ss_nE); [exact Mhq | exact Mlzq | exact HS5 | apply run_NT |].
intros ms5 HS6 Hfr5.
assert (F5 : forall x, 0 <= x < 2 ^ 64 -> ~ WD3 x -> ms_mem ms5 (Z_to_bv 64 x) = ms_mem ms4 (Z_to_bv 64 x)).
{ apply (frame_keepN regs WD3 ET (ss_mem ss_NT) SKs2 (ms_mem ms4) _ (ms_mem ms4) Hfr5 W4); [intros b lo hi x Hin Hx; exact (SKs2_WD3 ET b lo hi x HAT' ET40 ET82 Hin Hx) | intros; reflexivity]. }
apply SR_ret. exists ET, ms5. split; [reflexivity|]. split; [exact HS6|]. split; [exact HAT'|]. split; [exact ET40|]. split; [exact ET82|].
split; [rewrite (proj1 HA7 64%nat), (proj1 HA6 64%nat), (proj1 HAF 64%nat) by lia; exact E64|].
split; [rewrite (proj1 HA7 94%nat), (proj1 HA6 94%nat) by lia; exact EF94|].
split; [rewrite (proj1 HA7 95%nat), (proj1 HA6 95%nat) by lia; exact EF95|].
split; [rewrite (proj1 HA7 61%nat), (proj1 HA6 61%nat) by lia; exact EF61|].
split; [exact ET97|].
split; [rewrite (proj1 HA7 10%nat), (proj1 HA6 10%nat), (proj1 HAF 10%nat), (proj1 HAE 10%nat) by lia; rewrite (agree_reg' E 10 HA) by lia; exact R10|].
assert (OFF3 : forall x, P0 - 4 <= x <= P0 + ST - 4 -> ~ (P0 - 3 <= x < P0 + 9) -> ~ WD3 x).
{ intros x Hx Hq. assert (RGN : GLO <= x < GLO + rg_len rg) by (clear - Hx EP0 HfitR P1' P2' Hko; lia). pose proof (proj1 (RNG x RGN)) as NI.
unfold WD3, WD2. intros [[Hw|Hw]|[Hw|Hw]]; [| exact (Hq Hw) | apply NI; apply src0_rwseg_img; cbn [cs] in Hw; lits; clear - Hw Hsc; lia | apply NI; apply src0_rwseg_img; cbn [cs] in Hw; lits; clear - Hw Hsc; lia].
revert Hw. apply WD0_low; [clear - RGN Rceil; lia | intros Hmx; exact (KEYS m x Kmq ltac:(rewrite Eqm; exact Hmx) RGN)]. }
split.
{ intros x Hx Hw Hp Hl. rewrite (F5 x Hx Hw). apply F4'; [exact Hx | intros Hw2; apply Hw; left; exact Hw2 | exact Hp | exact Hl]. }
split.
{ assert (X4 : 0 <= P0 - 4 < 2 ^ 64) by (clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
unfold mbyte in Fc4 |- *. cbn [ms_mem] in F2.
rewrite (F5 (P0 - 4) X4 (OFF3 (P0 - 4) ltac:(clear - Sp; lia) ltac:(clear; lia))), (F4 (P0 - 4) X4), (F3z (P0 - 4) X4), (F2 (P0 - 4) X4); [exact Fc4 | | clear; lia |];
unfold WD2; (intros [Hw|Hw]; [| clear - Hw; lia]); revert Hw; (apply WD0_low; [clear - EP0 Hko P1' P2' HfitR Rceil Sp; lia|]); intros Hmx; exact (KEYS m (P0 - 4) Kmq ltac:(rewrite Eqm; exact Hmx) ltac:(clear - EP0 Hko P1' P2' HfitR Sp; lia)). }
split.
{ intros i Hi. set (t := i * (16 * nu)). assert (Hii : 0 <= t <= K * (16 * nu)) by (subst t; clear - Hi Hnu HKr; nia).
set (t' := K * (16 * nu)) in *. clearbody t'.
assert (HX : 0 <= P0 + 12 + t < 2 ^ 64) by (clear - Hii TOT EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
assert (NW2 : ~ WD2 (P0 + 12 + t)).
{ unfold WD2; intros [Hw|Hw]; [| clear - Hw Hii; lia]; revert Hw; apply WD0_low; [clear - Hii TOT EP0 Hko P1' P2' HfitR Rceil; lia|]; intros Hmx. apply (KEYS m (P0 + 12 + t) Kmq); [rewrite Eqm; exact Hmx | clear - Hii TOT EP0 Hko P1' P2' HfitR; lia]. }
rewrite (F5 (P0 + 12 + t) HX (OFF3 (P0 + 12 + t) ltac:(clear - Hii TOT; lia) ltac:(clear - Hii; lia))), (F4 (P0 + 12 + t) HX NW2).
subst mem3 t. replace i with (Z.of_nat (Z.to_nat i)) by (clear - Hi; lia). apply zmem_at; [clear - EP0 Hko P1' R4096; lia | clear - Hnu; lia | rewrite Z2Nat.id by (clear - HKr; lia); clear - NUK EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia | clear - Hi HKr; lia]. }
split.
{ intros x Hx Hn'. assert (HX : 0 <= x < 2 ^ 64) by (clear - Hx EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
assert (NW2 : ~ WD2 x).
{ unfold WD2; intros [Hw|Hw]; [| clear - Hw Hx; lia]. revert Hw. apply WD0_low; [clear - Hx EP0 Hko P1' P2' HfitR Rceil; lia|]. intros Hmx. exact (KEYS m x Kmq ltac:(rewrite Eqm; exact Hmx) ltac:(clear - Hx EP0 Hko P1' P2' HfitR Sp; lia)). }
rewrite (F5 x HX), (F4 x HX NW2); [| intros Hw3; unfold WD3 in Hw3; destruct Hw3 as [Hw|[Hw|Hw]]; [exact (NW2 Hw) | | ];
(apply (proj1 (RNG x ltac:(clear - Hx EP0 Hko P1' P2' HfitR Sp; lia))); apply src0_rwseg_img; cbn [cs] in Hw; lits; clear - Hw Hsc; lia)].
subst mem3. rewrite zmem_other; [| exact HX | clear - EP0 Hko P1' R4096; lia | clear - Hnu; lia | rewrite Z2Nat.id by (clear - HKr; lia); clear - NUK EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia |].
- cbn [ms_mem] in F2. rewrite (F2 x HX NW2), (FF x HX) by (clear - Hx; lia). apply F1; [exact HX | intros Hw0; apply NW2; left; exact Hw0].
- intros i0 Hi0. rewrite <- (Z2Nat.id (K + 1)) in Hi0 by (clear - HKr; lia). pose proof (Hn' (Z.of_nat i0) ltac:(clear - Hi0 HKr; lia)). exact H. }
intros x [b Hb] HX NIx.
assert (WFIN : forall i0 r0, nth_error (ss_mem ss_nE) i0 = Some r0 -> base_val ET (r_base r0) + r_wlo r0 <= x < base_val ET (r_base r0) + r_whi r0 -> present (ms_mem ms5) x).
{ intros i0 r0 Hi0 Hx0. apply (writable_off_img_present _ x HX ltac:(intros Hi; exact (NIx (in_img1_img x Hi)))). exact (writable_of_region regs ET ss_nE ms5 i0 r0 x HS6 Hi0 Hx0). }
pose proof nE_facts as (_ & FIRST4 & SKIP4 & (rstk & Hrstk & Brstk & LOrstk & HIrstk) & _).
assert (U33 : bv_unsigned (ew ET 33) = csn 33) by (rewrite (agree_cs' ET 33 HAT') by lia; apply u64_of_Z; destruct cs_facts' as (C33 & _); lits; lia).
assert (U82 : bv_unsigned (ew ET 82) = P0) by (rewrite ET82; apply u64_of_Z; clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
assert (U40 : bv_unsigned (ew ET 40) = ptr_addr L1 m) by (rewrite ET40; destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; clear - R AC; lia).
assert (U2 : bv_unsigned (ew ET 2) = sp) by (rewrite (agree_reg' ET 2 HAT') by lia; reflexivity).
assert (NTH : forall i0, (i0 < 4)%nat -> nth_error (ss_mem ss_nE) i0 = nth_error (firstn 4 (ss_mem ss_nE)) i0).
{ intros i0 Hi0. rewrite <- (firstn_skipn 4 (ss_mem ss_nE)) at 1. rewrite nth_error_app1; [reflexivity|]. rewrite FIRST4. cbn [length]. exact Hi0. }
destruct (WD3_dec x) as [Hw3|Hw3].
2: destruct (ivl_dec (P0 + 12) (P0 + ST) x) as [Hl|Hl].
-
unfold WD3, WD2, WD0, WS in Hw3.
destruct Hw3 as [[[Hw|Hw]|Hw]|[Hw|Hw]].
+ apply (WFIN 4%nat rstk Hrstk). rewrite Brstk, LOrstk, HIrstk. cbn [base_val]. rewrite (agree_reg' ET 2 HAT') by lia. replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. clear - Hw. lia.
+ apply (WFIN 3%nat _ ltac:(rewrite NTH by lia; rewrite FIRST4; reflexivity)). cbn [r_base r_wlo r_whi base_val]. rewrite U40. clear - Hw. lia.
+ apply (WFIN 2%nat _ ltac:(rewrite NTH by lia; rewrite FIRST4; reflexivity)). cbn [r_base r_wlo r_whi base_val]. rewrite U82. clear - Hw. lia.
+ apply (WFIN 1%nat _ ltac:(rewrite NTH by lia; rewrite FIRST4; reflexivity)). cbn [r_base r_wlo r_whi base_val]. rewrite U33. clear - Hw. lia.
+ apply (WFIN 0%nat _ ltac:(rewrite NTH by lia; rewrite FIRST4; reflexivity)). cbn [r_base r_wlo r_whi base_val]. rewrite U33. clear - Hw. lia.
-
unfold present. rewrite (F5 x HX Hw3), (F4 x HX ltac:(intros Hw; apply Hw3; left; exact Hw)).
destruct (mem3 (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; reflexivity|]. exfalso. revert Eb. subst mem3. apply zmem_present. cbn [ms_mem] in F2.
rewrite (F2 x HX ltac:(intros Hw; apply Hw3; left; exact Hw)). apply FP. rewrite (F1 x HX ltac:(intros Hw; apply Hw3; left; left; exact Hw)). rewrite Hb. discriminate.
- destruct (ivl_dec (P0 - 4) P0 x) as [Hp|Hp].
+ unfold present. rewrite (F5 x HX Hw3), (F4 x HX ltac:(intros Hw; apply Hw3; left; exact Hw)), (F3z x HX Hl). cbn [ms_mem] in F2. rewrite (F2 x HX ltac:(intros Hw; apply Hw3; left; exact Hw)).
destruct (memF (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; reflexivity|]. exfalso. apply (FP (Z_to_bv 64 x)); [| exact Eb]. rewrite (F1 x HX ltac:(intros Hw; apply Hw3; left; left; exact Hw)), Hb. discriminate.
+ exists b. rewrite <- Hb. rewrite (F5 x HX Hw3). apply F4'; [exact HX | intros Hw; apply Hw3; left; exact Hw | exact Hp | exact Hl].
Qed.
Lemma HK1 : 1 <= K <= 32. Proof. pose proof nfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKr & _). lia. Qed.
Lemma H26q : sc <= 26 -> 2 <= K. Proof. pose proof nfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKr & _). lia. Qed.
Lemma Ejq : size_to_class (totalN sc K) = j. Proof. pose proof nfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ej & _). exact Ej. Qed.
Lemma HhdNq : active_hd sq sc = None. Proof. pose proof nfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HhdN & _). exact HhdN. Qed.
Lemma Mrawq : rawm sq m. Proof. pose proof sq_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mq & _). exact Mq. Qed.
Lemma RXq' : rawX (m :: X) sq. Proof. pose proof sq_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RXq & _). exact RXq. Qed.
Let sN_post' := sN_post X U sq m hg am idx sc K j HIq NXq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd HhdNq Ejq Mrawq RXq'.
Let image_sN' := image_sN X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd Ejq Mrawq.
Let sN_lists' := sN_lists X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd Ejq Mrawq.
Let ctx_cells_sN' := ctx_cells_sN X U sq m hg am idx sc K j HIq Hsc.
Let sN_inv' := sN_inv X U sq m hg am idx sc K j HIq NXq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd HhdNq Ejq RXq'.
Let old_image_body' := old_image_body X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq RXq'.
Let old_tail_body' := old_tail_body X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq RXq'.
Let loop_addr_12' := loop_addr_12 X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq.
Let sN_MT' := sN_MT X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd Ejq.
Let sN_keys' := sN_keys X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd Ejq.
Let sN_rawX' := sN_rawX X U sq m hg am idx sc K j HIq NXq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd Ejq RXq'.
Let amN_fields' := amN_fields m am idx sc K HK1.
Let amE_fields' := amE_fields X sq m hg am idx j Uhg Hscj HidxB.
Let sN_fields' := sN_fields sq m hg am idx sc K j.
Lemma new_bytes : forall En ms5,
st_ok src0segs En ss_nE ms5 -> env_agree 40 E00 En ->
ew En 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew En 82 = Z_to_bv 64 P0 -> ew En 64 = Z_to_bv 64 idx -> ew En 94 = Z_to_bv 64 (ST * idx / 16) ->
0 <= bv_unsigned (ew En 95) <= 255 -> ew En 61 = Z_to_bv 64 K -> ew En 97 = Z_to_bv 64 (usage_of sq sc) -> ew En 10 = Z_to_bv 64 sc ->
let mem5 := ms_mem ms5 in
word_mem src0segs mem5 (csn 33 + 472) (usage_of sq sc + K) /\
word_mem src0segs mem5 (csn 33 + 88) (ptr_addr L1 m) /\
word_mem src0segs mem5 P0 (ptr_addr L1 m) /\
(exists b8, mbyte src0segs mem5 (P0 + 8) = Some b8 /\ bv_unsigned b8 mod 32 = K - 1) /\
mbyte src0segs mem5 (P0 - 3) = Some (Z_to_bv 8 (idx + 192)) /\
(forall k, (k < 2)%nat -> mbyte src0segs mem5 (P0 - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ST * idx / 16) 2 k))) /\
word_mem src0segs mem5 (ptr_addr L1 m) (ptr_addr L1 m) /\
word_mem src0segs mem5 (ptr_addr L1 m + 8) (ptr_addr L1 m) /\
word_mem src0segs mem5 (ptr_addr L1 m + 16) P0 /\
(forall k, (k < 4)%nat -> mbyte src0segs mem5 (ptr_addr L1 m + 24 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ones (K - 1) - 1) 4 k))) /\
(forall k, (k < 4)%nat -> mbyte src0segs mem5 (ptr_addr L1 m + 28 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 0 4 k))) /\
word_mem src0segs mem5 (ptr_addr L1 m + 32) ((K - 1) + 32 + 64 * sc).
Proof.
intros En ms5 HS HAn En40 En82 En64 En94 En95 En61 En97 En10. cbv zeta.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof (proj1 alloc_ceiling_val) as AC. destruct cs_facts' as (C33 & _).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & Sp & Gext').
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
destruct BNDq as (BU & _). pose proof (BU sc) as BUs.
pose proof nE_facts as (_ & FIRST4 & _).
assert (NTH : forall i0, (i0 < 4)%nat -> nth_error (ss_mem ss_nE) i0 = nth_error (firstn 4 (ss_mem ss_nE)) i0).
{ intros i0 Hi0. rewrite <- (firstn_skipn 4 (ss_mem ss_nE)) at 1. rewrite nth_error_app1; [reflexivity|]. rewrite FIRST4. cbn [length]. exact Hi0. }
pose proof (NTH 0%nat ltac:(lia)) as R0. pose proof (NTH 1%nat ltac:(lia)) as R1. pose proof (NTH 2%nat ltac:(lia)) as R2. pose proof (NTH 3%nat ltac:(lia)) as R3.
rewrite FIRST4 in R0, R1, R2, R3. cbn [nth_error] in R0, R1, R2, R3.
assert (U33 : bv_unsigned (ew En 33) = csn 33) by (rewrite (agree_cs' En 33 HAn) by lia; apply u64_of_Z; lits; lia).
assert (U82 : bv_unsigned (ew En 82) = P0) by (rewrite En82; apply u64_of_Z; clear - EP0 Hko P1' P2' HfitR R4096 Rceil AC Sp; lia).
assert (U40 : bv_unsigned (ew En 40) = ptr_addr L1 m) by (rewrite En40; destruct (RBm (ptr_addr L1 m) ltac:(lia)) as (_ & _ & R); apply u64_of_Z; clear - R AC; lia).
assert (D40 : sv_denot En (SOff 40 0) = Z_to_bv 64 (ptr_addr L1 m)) by (exact (den_off0 En 40 _ En40)).
split; [rewrite <- U33; apply (word_of_chunk_at En ss_nE ms5 0 _ 33 472 _ _ HS R0 eq_refl ltac:(left; reflexivity)); exact (usageN_val En _ _ En97 En61 BUs HK1)|].
split; [rewrite <- U33; apply (word_of_chunk_at En ss_nE ms5 1 _ 33 88 _ _ HS R1 eq_refl ltac:(left; reflexivity)); exact D40|].
split; [replace P0 with (bv_unsigned (ew En 82) + 0) by lia; apply (word_of_chunk_at En ss_nE ms5 2 _ 82 0 _ _ HS R2 eq_refl ltac:(right; left; reflexivity)); exact D40|].
split.
{ destruct (aidxN_byte En K En61 HK1 En95) as (AB & ABr & ABm).
pose proof (chunk_bytes_cval src0segs En (ms_mem ms5) (bv_unsigned (ew En 82)) 8 1 _ (Z.lor (Z.land (bv_unsigned (ew En 95)) 224) (K - 1)) (st_ok_chunk src0segs En ss_nE ms5 2 _ _ HS R2 ltac:(left; reflexivity))
ltac:(change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8); rewrite AB; symmetry; apply Z.mod_small; exact ABr) 0 ltac:(lia)) as T.
rewrite U82 in T. cbn [Z.of_nat] in T. rewrite Z.add_0_r in T. eexists. split; [exact T|].
unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256. rewrite !(Z.mod_small (Z.lor (Z.land (bv_unsigned (ew En 95)) 224) (K - 1)) 256) by exact ABr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (Z.lor (Z.land (bv_unsigned (ew En 95)) 224) (K - 1)) 256) by exact ABr. exact ABm. }
split.
{ pose proof (chunk_bytes_cval src0segs En (ms_mem ms5) (bv_unsigned (ew En 82)) (-3) 1 _ (idx + 192) (st_ok_chunk src0segs En ss_nE ms5 2 _ _ HS R2 ltac:(right; right; left; reflexivity)) ltac:(change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8); exact (hdrN_byte En idx En64 ltac:(pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq) as (Glast & _); clear - HidxB Glast; lia))) 0 ltac:(lia)) as T.
rewrite U82 in T. cbn [Z.of_nat] in T. rewrite Z.add_0_r in T. replace (P0 + -3) with (P0 - 3) in T by lia. rewrite T. f_equal. f_equal.
unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256. pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq) as (Glast & _).
rewrite !(Z.mod_small (idx + 192) 256) by (clear - HidxB Glast; lia). reflexivity. }
split.
{ intros kk Hkk. replace (P0 - 2 + Z.of_nat kk) with (bv_unsigned (ew En 82) + -2 + Z.of_nat kk) by lia.
apply (chunk_bytes_cval src0segs En (ms_mem ms5) (bv_unsigned (ew En 82)) (-2) 2 (SOff 94 0) (ST * idx / 16) (st_ok_chunk src0segs En ss_nE ms5 2 _ _ HS R2 ltac:(right; right; right; left; reflexivity))); [| exact Hkk].
rewrite (den_off0 En 94 _ En94).
assert (LT : 0 <= ST * idx / 16 < 65536) by (split; [apply Z.div_pos; clear - P1'; lia | apply Z.div_lt_upper_bound; [lia|]; clear - Gext' P1' P2' Sp; nia]). rewrite lit64_small by (clear - LT; lia). reflexivity. }
assert (M_m : forall off sv v, In (mkChunk off (CVal 8 sv)) [mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 24 (CVal 4 (SAlu ALU_ADD (SExt true 32 AVAILN) (SLit (-1))));
mkChunk 32 (CVal 8 BITSN); mkChunk 16 (CVal 8 (SOff 82 0));
mkChunk 28 (CVal 4 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 61 (-1))) (SAlu ALU_XOR (SExt true 32 AVAILN) (SLit (-1)))))] ->
sv_denot En sv = Z_to_bv 64 v -> word_mem src0segs (ms_mem ms5) (ptr_addr L1 m + off) v).
{ intros off sv v Hin Hv. rewrite <- U40. exact (word_of_chunk_at En ss_nE ms5 3 _ 40 off sv v HS R3 eq_refl Hin Hv). }
split; [replace (ptr_addr L1 m) with (ptr_addr L1 m + 0) at 1 by lia; apply (M_m 0 (SOff 40 0)); [inlist | exact D40]|].
split; [apply (M_m 8 (SOff 40 0)); [inlist | exact D40]|].
split; [apply (M_m 16 (SOff 82 0)); [inlist | exact (den_off0 En 82 _ En82)]|].
split.
{ intros kk Hkk. rewrite <- U40. apply (chunk_bytes_cval src0segs En (ms_mem ms5) _ 24 4 _ _ (st_ok_chunk src0segs En ss_nE ms5 3 _ _ HS R3 ltac:(right; right; left; reflexivity))); [| exact Hkk].
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact (availN_lo32 En K En61 HK1). }
split.
{ intros kk Hkk. rewrite <- U40. apply (chunk_bytes_cval src0segs En (ms_mem ms5) _ 28 4 _ _ (st_ok_chunk src0segs En ss_nE ms5 3 _ _ HS R3 ltac:(do 5 right; left; reflexivity))); [| exact Hkk].
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). rewrite (freedN_lo32 En K En61 HK1). reflexivity. }
apply (M_m 32 BITSN); [inlist|]. exact (bitsN_val En sc K En10 En61 Hsc HK1).
Qed.
Let NEW_in_image' := NEW_in_image X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Hhd Ejq Mrawq.
Local Notation NEWq := (NEW sq m am idx sc K j).
Definition LOOPA (y : Z) : Prop := exists i, 0 <= i <= K /\ y = P0 + 12 + i * (16 * nu).
Definition Z0 (y : Z) : Prop := LOOPA y \/ y = P0 - 4.
Lemma LOOPA_dec : forall y, {LOOPA y} + {~ LOOPA y}.
Proof.
intros y. pose proof nfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKr & Hnu & _). clear - HKr Hnu.
set (i0 := (y - P0 - 12) / (16 * nu)).
assert (DIV : forall i, (P0 + 12 + i * (16 * nu) - P0 - 12) / (16 * nu) = i) by (intros i; replace (P0 + 12 + i * (16 * nu) - P0 - 12) with (i * (16 * nu)) by lia; apply Z_div_mult; lia).
destruct (Z.eq_dec y (P0 + 12 + i0 * (16 * nu))) as [Ey0|NE].
- destruct (Z_le_dec 0 i0) as [H0|H0]; [destruct (Z_le_dec i0 K) as [H1|H1]; [left; exists i0; split; [lia | exact Ey0]|]|];
right; intros (i & Hi & Ey); pose proof (DIV i) as Di; rewrite <- Ey in Di; subst i0; lia.
- right. intros (i & Hi & Ey). apply NE. subst i0. rewrite Ey, (DIV i). reflexivity.
Qed.
Lemma Z0_dec : forall y, {Z0 y} + {~ Z0 y}.
Proof. intros y. unfold Z0. destruct (LOOPA_dec y) as [H|H]; [left; left; exact H|]. destruct (Z.eq_dec y (P0 - 4)) as [Ey|Ey]; [left; right; exact Ey|]. right. intros [H'|H']; [exact (H H') | exact (Ey H')]. Qed.
Lemma zero_cell : forall c y, In c (image sq) \/ In c (tail_cells sq) -> Z0 y ->
loc_addr L' (mc_loc c) <= y < loc_addr L' (mc_loc c) + Z.of_nat (mc_w c) -> mc_w c = 1%nat /\ mc_val c = VZ 0.
Proof.
intros c y Hc Hy Hcov. pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & _).
pose proof sq_facts as (LE' & MID' & _).
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & Sp & Gext').
assert (TOT : 12 + K * (16 * nu) + 4 <= ST) by (clear - HfitS Etot; subst total k; unfold UNIT, IB in *; nia).
assert (Hy' : exists t, y = P0 + 12 + 16 * t /\ GLO <= y < GLO + rg_len rg).
{ destruct Hy as [(i & Hi & ->) | ->].
- exists (i * nu). assert (Hii : 0 <= i * (16 * nu) <= K * (16 * nu)) by (clear - Hi Hnu HKr; nia). split; [clear; lia|]. clear - Hii TOT EP0 HfitR P1' P2' Hko. lia.
- exists (-1). split; [clear; lia|]. clear - EP0 HfitR P1' P2' Hko Sp. lia. }
destruct Hy' as (t & Ey & RGN).
apply (cells_at_12 (m :: X) (Some (hg, idx)) U sq L' HIq (XCq X sq m RXq') (mid_layout _ _ _ _ _ MID') kr rg y Hr Hrl Hrk ltac:(rewrite EGLO; exact RGN)
ltac:(rewrite Ey; exact (loop_addr_12' L' kr ko t Emem)) c ltac:(apply in_app_iff; exact Hc) Hcov).
Qed.
Lemma keys_vs_regions : forall q x kk rg, In q (keys sq) -> ptr_addr L' q <= x < ptr_addr L' q + 40 ->
region_of sq kk = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> ~ (ly_reg L' kk <= x < ly_reg L' kk + rg_len rg).
Proof.
intros q x kk rg Hq Hx Hk Hkd Hl HG. pose proof sq_facts as (LE' & MID' & _).
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' q HIq MID' Hq) as (_ & _ & _ & (a & ka & Ha & Hka & Eq) & _).
pose proof (inv_areas HIq) as (_ & Hareas & _). destruct (Hareas a Ha) as (r & o & rga & Ear & Ho & Hlo & Hra & Hla & Hlen & Hknd).
pose proof (footprint_region_In sq _ _ Hk Hkd Hl) as InR.
assert (Hne : (LMem a, PGSZ) <> (LMem (SP kk 0), rg_len rg)).
{ intros EE. injection EE as E1 _. rewrite Ear in E1. injection E1 as -> _. rewrite Hk in Hra. injection Hra as <-. rewrite Hkd in Hknd. exact Hknd. }
assert (Hina : In (LMem a, PGSZ) (footprint sq)) by (right; apply in_app_iff; left; apply in_map_iff; eexists; split; [reflexivity | exact Ha]).
pose proof (mid_layout _ _ _ _ _ MID') as (_ & _ & PW & _).
assert (PG : ptr_addr L' a <= x < ptr_addr L' a + PGSZ) by (rewrite Eq in Hx; unfold slot_of in Hx; rewrite ptr_addr_padd in Hx; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia).
destruct (pairwise_map_In ranges_disjoint (crange L') (footprint sq) _ _ PW Hina InR Hne) as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; unfold ptr_addr in PG; rewrite Ear in PG, D; cbn [loc_addr] in PG; clear - D PG HG; lia.
Qed.
Lemma midrep_sN : forall En ms5,
st_ok src0segs En ss_nE ms5 -> env_agree 40 E00 En ->
ew En 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew En 82 = Z_to_bv 64 P0 -> ew En 64 = Z_to_bv 64 idx -> ew En 94 = Z_to_bv 64 (ST * idx / 16) ->
0 <= bv_unsigned (ew En 95) <= 255 -> ew En 61 = Z_to_bv 64 K -> ew En 97 = Z_to_bv 64 (usage_of sq sc) -> ew En 10 = Z_to_bv 64 sc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WD3 x -> ~ (P0 - 4 <= x < P0) -> ~ (P0 + 12 <= x < P0 + ST) -> ms_mem ms5 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) ->
mbyte src0segs (ms_mem ms5) (P0 - 4) = Some (Z_to_bv 8 0) ->
(forall i, 0 <= i <= K -> ms_mem ms5 (Z_to_bv 64 (P0 + 12 + i * (16 * nu))) = Some (Z_to_bv 8 0)) ->
(forall x, P0 + 12 <= x < P0 + ST -> (forall i, 0 <= i <= K -> x <> P0 + 12 + i * (16 * nu)) -> ms_mem ms5 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)) ->
(forall x, present mem' x -> 0 <= x < 2 ^ 64 -> ~ in_img B x -> present (ms_mem ms5) x) ->
midrep B L' sNq (ms_mem ms5) md'.
Proof.
intros En ms5 HS HAn En40 En82 En64 En94 En95 En61 En97 En10 OLD Fc4 ZER LOLD PRES.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). destruct cs_facts' as (C33 & _).
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq) as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & Hhdr & Sp0 & Khg & NXhg).
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & Sp & Gext').
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
destruct (new_bytes En ms5 HS HAn En40 En82 En64 En94 En95 En61 En97 En10) as (Muse & Mact & Mp0 & (b8 & Mp8 & Mp8m) & Mpm3 & Mpm2 & Mm0 & Mm8 & Mm16 & Mm24 & Mm28 & Mm32).
pose proof sN_lists' as ((v1 & v2 & u1 & u2 & Ev & Ev' & Eu & Eu') & UBe & FPe & ROe & TCe & GCe & UMe & FRe).
pose proof sN_fields' as (Qm & Qr & Qar & Qb & _). pose proof amN_fields' as (Nmem & Nlast & Npr & Nnx & Nsc & Nml & Nai & Nav & Nfr & Nst & Next & Nsl).
pose proof sN_inv' as (HIN & HhdN' & UN & EHN & UBN & XCN).
pose proof (mid_syms _ _ _ _ _ MID') as SO. pose proof (mid_mem _ _ _ _ _ MID') as MR.
set (mem5 := ms_mem ms5) in *.
assert (TOT : 12 + K * (16 * nu) + 4 <= ST) by (clear - HfitS Etot; subst total k; unfold UNIT, IB in *; nia).
assert (HLN : layout_ok L' sNq) by (exact (layout_ok_same L' sq sNq (mid_layout _ _ _ _ _ MID') Qr FPe)).
assert (ZB : forall y, Z0 y -> mbyte src0segs mem5 y = Some (Z_to_bv 8 0)).
{ intros y [(i & Hi & ->)| ->]; [| exact Fc4]. assert (Hii : 0 <= i * (16 * nu) <= K * (16 * nu)) by (clear - Hi Hnu HKr; nia).
set (t := i * (16 * nu)) in *. assert (RGN : GLO <= P0 + 12 + t < GLO + rg_len rg) by (clear - Hii TOT EP0 HfitR P1' P2' Hko; lia).
rewrite mbyte_off_img; [subst t; exact (ZER i Hi) | clear - RGN R4096 Rceil AC; lia | intros Hi'; exact (proj1 (RNG _ RGN) (in_img1_img _ Hi'))]. }
assert (OLDB : forall y, 0 <= y < 2 ^ 64 -> ~ WD3 y -> ~ Z0 y -> mem5 (Z_to_bv 64 y) = mem' (Z_to_bv 64 y)).
{ intros y Hy Hw Hz. destruct (ivl_dec (P0 + 12) (P0 + ST) y) as [Hl|Hl].
- apply LOLD; [exact Hl|]. intros i Hi Ey. apply Hz. left. exists i. exact (conj Hi Ey).
- apply OLD; [exact Hy | exact Hw | | exact Hl]. intros Hp. destruct (Z.eq_dec y (P0 - 4)) as [Ey|Ey]; [apply Hz; right; exact Ey|]. apply Hw. left. right. clear - Hp Ey. lia. }
assert (OLDCELL : forall c, In c (image sq) \/ In c (tail_cells sq) ->
(forall kk, (kk < mc_w c)%nat -> 0 <= loc_addr L' (mc_loc c) + Z.of_nat kk < 2 ^ 64 /\ ~ WD3 (loc_addr L' (mc_loc c) + Z.of_nat kk)) ->
cell_mem B L' mem5 c).
{ intros c Hc Hoff.
assert (C : cell_mem B L' mem' c) by (destruct Hc as [Hc|Hc]; [exact (memrep_cell B L' sq mem' c MR Hc) | exact (memrep_tail B L' sq mem' c MR Hc)]).
unfold cell_mem in C |- *. destruct c as [lc w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v as [z|p|z|].
1,2,4: intros kk Hkk; destruct (Hoff kk Hkk) as [Ykk NW]; destruct (Z0_dec (loc_addr L' lc + Z.of_nat kk)) as [Zy|Zy];
[ destruct (zero_cell _ _ Hc Zy ltac:(cbn [mc_loc mc_w]; clear - Hkk; lia)) as [W1 V1]; cbn [mc_w mc_val] in W1, V1;
first [ discriminate V1
| injection V1 as ->; subst w; destruct kk; [| lia]; cbn [Z.of_nat] in *; rewrite ZB by exact Zy; cbn [sval_num]; rewrite YN03.le_byte_0; reflexivity ]
| rewrite (mbyte_ext1 mem' mem5) by (exact (OLDB _ Ykk NW Zy)); exact (C kk Hkk) ].
intros Hw0. destruct (Hoff 0%nat Hw0) as [Y0 NW0]. rewrite Z.add_0_r in Y0, NW0. destruct (Z0_dec (loc_addr L' lc)) as [Zy|Zy].
- destruct (zero_cell _ _ Hc Zy ltac:(cbn [mc_loc mc_w]; clear - Hw0; lia)) as [_ V1]. discriminate V1.
- destruct (C Hw0) as (b & Hb & Hbz). exists b. rewrite (mbyte_ext1 mem' mem5) by (exact (OLDB _ Y0 NW0 Zy)). exact (conj Hb Hbz). }
assert (ADDR : forall c kk, In c (image sq) \/ In c (tail_cells sq) -> (kk < mc_w c)%nat ->
0 <= loc_addr L' (mc_loc c) + Z.of_nat kk < alloc_ceiling /\ (in_img B (loc_addr L' (mc_loc c) + Z.of_nat kk) -> exists off, mc_loc c = LCtx off)).
{ intros c kk Hc Hkk.
destruct (cellX_in_footprint (m :: X) (Some (hg, idx)) U sq L' HIq c) as (e & He & Ie).
{ unfold imageX, tail_cellsX. rewrite (used_metasX_eqq X U sq m hg idx HIq RXq'). fold (image sq). fold (tail_cells sq). apply in_app_iff. exact Hc. }
unfold range_incl, cell_range, crange in Ie. cbn [fst snd] in Ie.
destruct (In_footprint_inv sq e He) as [-> | [(ar & Har & ->) | (kk' & rg' & Hrg' & Hkd' & Hlv' & ->)]]; cbn [fst snd loc_addr] in Ie.
- rewrite (mid_ctx _ _ _ _ _ MID') in Ie. pose proof (so_ctx_lo _ SO). pose proof (so_ctx_hi _ SO). split; [clear - Ie H H0 Hkk; lia|].
intros _. destruct (mc_loc c) as [off|p] eqn:El; [exists off; reflexivity|]. exfalso.
destruct Hc as [Hc|Hc].
+ destruct (In_image_inv sq c Hc) as [Hcc | [(a0 & next & Ha0 & Hca) | (g0 & am0 & Hg0 & Hcg)]].
* destruct (In_ctx_cells sq c Hcc) as (off & Eo & _). rewrite El in Eo. discriminate.
* destruct (area_cell_home L' sq a0 next c Ha0 Hca) as [In1 I1]. pose proof (mid_layout _ _ _ _ _ MID') as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L') (footprint sq) _ _ PW (or_introl eq_refl : In (LCtx 0, CTX_SIZE) (footprint sq)) In1 ltac:(discriminate)) as [D|D];
unfold ranges_disjoint, range_incl, cell_range, crange in *; cbn [fst snd loc_addr] in *; rewrite (mid_ctx _ _ _ _ _ MID') in *; rewrite El in *; cbn [loc_addr] in *; clear - D I1 Ie Hkk; lia.
* apply (used_metas_usedX' (m :: X) (Some (hg, idx)) U sq HIq XCq) in Hg0.
destruct (group_cell_homeX (m :: X) (Some (hg, idx)) U sq L' HIq g0 am0 c Hg0 Hcg) as (rg0 & _ & _ & _ & In1 & I1). pose proof (mid_layout _ _ _ _ _ MID') as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L') (footprint sq) _ _ PW (or_introl eq_refl : In (LCtx 0, CTX_SIZE) (footprint sq)) In1 ltac:(discriminate)) as [D|D];
unfold ranges_disjoint, range_incl, cell_range, crange in *; cbn [fst snd loc_addr] in *; rewrite (mid_ctx _ _ _ _ _ MID') in *; rewrite El in *; cbn [loc_addr] in *; clear - D I1 Ie Hkk; lia.
+ destruct (tail_cell_region (m :: X) (Some (hg, idx)) U sq HIq XCq c Hc) as (p0 & rg0 & El0 & Hrg0 & Hkd0 & Hlv0 & Hpo0 & Hpw0). rewrite El in El0. injection El0 as ->.
pose proof (mid_layout _ _ _ _ _ MID') as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L') (footprint sq) _ _ PW (or_introl eq_refl : In (LCtx 0, CTX_SIZE) (footprint sq)) (footprint_region_In sq _ _ Hrg0 Hkd0 Hlv0) ltac:(discriminate)) as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; rewrite (mid_ctx _ _ _ _ _ MID') in D; destruct p0 as [r0 o0]; cbn [loc_addr prid poff] in *; clear - D Ie Hkk Hpo0 Hpw0; lia.
- destruct (areas_off_img B (m :: X) (Some (hg, idx)) U L' sq mem' md' HIq MID' ar (loc_addr L' (mc_loc c) + Z.of_nat kk) Har ltac:(unfold ptr_addr; cbn [loc_addr]; clear - Ie Hkk; destruct ar; lia)) as [NI Rx].
split; [clear - Rx; lia | intros Hi; exfalso; exact (NI Hi)].
- pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID') kk' rg' Hrg' Hlv') as (_ & A1 & A2 & Aimg).
split; [clear - Ie Hkk A1 A2; lia | intros Hi; exfalso; exact (Aimg (loc_addr L' (mc_loc c) + Z.of_nat kk) ltac:(clear - Ie Hkk; lia) Hi)]. }
assert (COVER : forall y, (ptr_addr L1 m <= y < ptr_addr L1 m + 40 \/ P0 - 3 <= y < P0 + 9 \/ csn 33 + 88 <= y < csn 33 + 96 \/ csn 33 + 472 <= y < csn 33 + 480) ->
exists nw, In nw NEWq /\ loc_addr L' (mc_loc nw) <= y < loc_addr L' (mc_loc nw) + Z.of_nat (mc_w nw)).
{ intros y Hy. unfold NEW.
assert (LM : forall off, loc_addr L' (LMem (padd m off)) = ptr_addr L1 m + off) by (intros off; rewrite loc_addr_padd_, Eqm; reflexivity).
assert (LP : forall off, loc_addr L' (LMem (padd (pN am idx) off)) = P0 + off) by (intros off; rewrite loc_addr_padd_; reflexivity).
assert (LC : forall off, loc_addr L' (LCtx off) = CTX + off) by (intros off; cbn [loc_addr]; rewrite (mid_ctx _ _ _ _ _ MID'); reflexivity).
destruct Hy as [Hy|[Hy|[Hy|Hy]]].
- assert (CASE : exists off w v, In (MCell (LMem (padd m off)) w v) (meta_slot_cells m (Some (MUsed amNq))) /\ off <= y - ptr_addr L1 m < off + Z.of_nat w).
{ cbn [meta_slot_cells]. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits.
destruct (Z_lt_le_dec (y - ptr_addr L1 m) 8); [exists 0, 8%nat, (optr (am_prev amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (y - ptr_addr L1 m) 16); [exists 8, 8%nat, (optr (am_next amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (y - ptr_addr L1 m) 24); [exists 16, 8%nat, (VP (am_mem amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (y - ptr_addr L1 m) 28); [exists 24, 4%nat, (VZ (am_avail amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (y - ptr_addr L1 m) 32); [exists 28, 4%nat, (VZ (am_freed amNq)); split; [inlist | lia]|].
exists 32, 8%nat, (VZ (meta_bits amNq)). split; [inlist | lia]. }
destruct CASE as (off & w & v & Hin & Hoff). exists (MCell (LMem (padd m off)) w v). split; [rewrite !in_app_iff; right; left; exact Hin|]. cbn [mc_loc mc_w]. rewrite LM. clear - Hoff. lia.
- destruct (Z_lt_le_dec y (P0 - 2)); [| destruct (Z_lt_le_dec y P0); [| destruct (Z_lt_le_dec y (P0 + 8))]].
+ exists (N3 am idx). split; [apply in_app_iff; left; inlist|]. unfold N3. cbn [mc_loc mc_w]. rewrite LP. clear - Hy l; lia.
+ exists (N16 am idx j). split; [apply in_app_iff; left; inlist|]. unfold N16. cbn [mc_loc mc_w]. rewrite LP. clear - l l0; lia.
+ exists (MCell (LMem (pN am idx)) 8 (VP m)). split; [rewrite !in_app_iff; right; right; apply GCe; left; reflexivity|]. cbn [mc_loc mc_w]. change (loc_addr L' (LMem (pN am idx))) with P0. clear - l0 l1; lia.
+ exists (MCell (LMem (padd (pN am idx) 8)) 1 (VLo5 (K - 1))). split; [rewrite !in_app_iff; right; right; apply GCe; right; left; reflexivity|]. cbn [mc_loc mc_w]. rewrite LP. clear - Hy l1; lia.
- exists (Nact m sc). split; [apply in_app_iff; left; inlist|]. unfold Nact. cbn [mc_loc mc_w]. rewrite LC. cbn [cs] in Hy. unfold CTX_active. lits. clear - Hy. lia.
- exists (Nuse sq sc K). split; [apply in_app_iff; left; inlist|]. unfold Nuse. cbn [mc_loc mc_w]. rewrite LC. cbn [cs] in Hy. unfold CTX_usage. lits. clear - Hy. lia. }
pose proof (image_cells_disjointX X (Some (m, 0)) U sNq L' HIN XCN HLN) as PWN.
assert (DISJ : forall c nw y, In c (image sNq) -> In nw (image sNq) -> c <> nw ->
loc_addr L' (mc_loc c) <= y < loc_addr L' (mc_loc c) + Z.of_nat (mc_w c) -> loc_addr L' (mc_loc nw) <= y < loc_addr L' (mc_loc nw) + Z.of_nat (mc_w nw) -> False).
{ intros c nw y Hc Hnw Hne Hyc Hyn. destruct (pairwise_map_In ranges_disjoint (cell_range L') (image sNq) _ _ PWN Hc Hnw Hne) as [D|D]; unfold ranges_disjoint, cell_range in D; cbn [fst snd] in D; clear - D Hyc Hyn; lia. }
assert (NEWOK : forall c, In c NEWq -> cell_mem B L' mem5 c).
{ intros c Hc. unfold NEW in Hc. rewrite !in_app_iff in Hc. cbn [In] in Hc.
assert (LM : forall off, loc_addr L' (LMem (padd m off)) = ptr_addr L1 m + off) by (intros off; rewrite loc_addr_padd_, Eqm; reflexivity).
assert (LP : forall off, loc_addr L' (LMem (padd (pN am idx) off)) = P0 + off) by (intros off; rewrite loc_addr_padd_; reflexivity).
assert (LC : forall off, loc_addr L' (LCtx off) = CTX + off) by (intros off; cbn [loc_addr]; rewrite (mid_ctx _ _ _ _ _ MID'); reflexivity).
destruct Hc as [[<-|[<-|[<-|[<-|[]]]]]|[Hc|Hc]].
- unfold Nuse, cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite LC. change (ms_segs B) with src0segs.
replace (CTX + (CTX_usage + 8 * sc)) with (csn 33 + 472) by (cbn [cs]; unfold CTX_usage; lits; lia). exact Muse.
- unfold Nact, cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite LC. change (ms_segs B) with src0segs. change (loc_addr L' (LMem m)) with (ptr_addr L' m). rewrite Eqm.
replace (CTX + (CTX_active + 8 * sc)) with (csn 33 + 88) by (cbn [cs]; unfold CTX_active; lits; lia). exact Mact.
- unfold N3, cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite LP. change (ms_segs B) with src0segs. intros kk Hkk. destruct kk; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
replace (P0 + -3) with (P0 - 3) by lia. rewrite Mpm3. f_equal. f_equal. unfold le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !(Z.mod_small (idx + 192) 256) by (clear - HidxB Glast; lia). reflexivity.
- unfold N16, cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite LP. change (ms_segs B) with src0segs. intros kk Hkk. replace (P0 + -2 + Z.of_nat kk) with (P0 - 2 + Z.of_nat kk) by lia. rewrite <- Hstr. unfold UNIT. exact (Mpm2 kk Hkk).
- cbn [meta_slot_cells optr] in Hc. rewrite Npr, Nnx, Nmem, Nav, Nfr in Hc. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num optr]; rewrite LM; change (ms_segs B) with src0segs.
+ change (loc_addr L' (LMem m)) with (ptr_addr L' m). rewrite Eqm, Z.add_0_r. exact Mm0.
+ change (loc_addr L' (LMem m)) with (ptr_addr L' m). rewrite Eqm. exact Mm8.
+ change (loc_addr L' (LMem (pN am idx))) with P0. exact Mm16.
+ exact Mm24.
+ intros kk Hkk. rewrite (Mm28 kk Hkk). reflexivity.
+ unfold meta_bits. rewrite Nlast, Nsc, Nml. replace (K - 1 + 32 + 64 * sc + 4096 * 0) with (K - 1 + 32 + 64 * sc) by lia. exact Mm32.
- apply GCe in Hc as [-> | [-> | (i & Hi & ->)]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num].
+ change (loc_addr L' (LMem (pN am idx))) with P0. change (loc_addr L' (LMem m)) with (ptr_addr L' m). rewrite Eqm. change (ms_segs B) with src0segs. exact Mp0.
+ rewrite LP. intros _. exists b8. change (ms_segs B) with src0segs. exact (conj Mp8 Mp8m).
+ rewrite loc_addr_padd_. unfold slot_start. rewrite Nmem, Nst, ptr_addr_padd. change (ptr_addr L' (pN am idx)) with P0. change (ms_segs B) with src0segs.
intros kk Hkk. destruct kk; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, YN03.le_byte_0. rewrite Hcs0 || idtac.
replace (P0 + (UNIT + class_size sc * i) + -4) with (P0 + 12 + i * (16 * nu)) by (rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cs_facts'))))))); fold nu; unfold UNIT; lia).
apply ZB. left. exists i. split; [lia | reflexivity]. }
assert (IMG : forall c, In c (image sNq) -> cell_mem B L' mem5 c).
{ intros c Hc. destruct (In_dec mcell_eq_dec c NEWq) as [Hnew|Hold]; [exact (NEWOK c Hnew)|].
destruct (image_sN' c Hc) as [Hnew|HcO]; [exact (NEWOK c Hnew)|].
apply OLDCELL; [left; exact HcO|]. intros kk Hkk. destruct (ADDR c kk (or_introl HcO) Hkk) as [Rk IMGk]. split; [clear - Rk AC; lia|].
intros Hw3. unfold WD3, WD2, WD0, WS in Hw3.
assert (COV : ptr_addr L1 m <= loc_addr L' (mc_loc c) + Z.of_nat kk < ptr_addr L1 m + 40 \/ P0 - 3 <= loc_addr L' (mc_loc c) + Z.of_nat kk < P0 + 9 \/
csn 33 + 88 <= loc_addr L' (mc_loc c) + Z.of_nat kk < csn 33 + 96 \/ csn 33 + 472 <= loc_addr L' (mc_loc c) + Z.of_nat kk < csn 33 + 480).
{ destruct Hw3 as [[[Hw|Hw]|Hw]|[Hw|Hw]]; [exfalso; unfold ASF in *; clear - Hw Rk P3 Hstk; lia | left; exact Hw | right; left; exact Hw | right; right; left; exact Hw | right; right; right; exact Hw]. }
destruct (COVER _ COV) as (nw & Hnw & Hyn). apply (DISJ c nw (loc_addr L' (mc_loc c) + Z.of_nat kk) Hc (NEW_in_image' nw Hnw)); [| clear - Hkk; lia | exact Hyn].
intros ->. exact (Hold Hnw). }
assert (TAIL : forall c, In c (tail_cells sNq) -> cell_mem B L' mem5 c).
{ intros c Hc. apply TCe in Hc as [HcO | ->].
- apply OLDCELL; [right; exact HcO|]. intros kk Hkk. destruct (ADDR c kk (or_intror HcO) Hkk) as [Rk IMGk]. split; [clear - Rk AC; lia|].
destruct (tail_cell_region (m :: X) (Some (hg, idx)) U sq HIq XCq c HcO) as (p0 & rg0 & El0 & Hrg0 & Hkd0 & Hlv0 & Hpo0 & Hpw0).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID') _ rg0 Hrg0 Hlv0) as (_ & B1 & B2 & Bimg).
assert (INR : ly_reg L' (prid p0) <= loc_addr L' (mc_loc c) + Z.of_nat kk < ly_reg L' (prid p0) + rg_len rg0) by (rewrite El0; destruct p0 as [r0 o0]; cbn [loc_addr prid poff] in *; clear - Hkk Hpo0 Hpw0; lia).
intros Hw3. unfold WD3, WD2, WD0, WS in Hw3. destruct Hw3 as [[[Hw|Hw]|Hw]|[Hw|Hw]].
+ unfold ASF in *. clear - Hw Rk P3 Hstk. lia.
+ exact (keys_vs_regions m _ (prid p0) rg0 Kmq ltac:(rewrite Eqm; exact Hw) Hrg0 Hkd0 Hlv0 INR).
+ apply (old_tail_body' L' c kk (mid_layout _ _ _ _ _ MID') HcO Hkk). unfold IB. assert (KN : 32 <= K * (16 * nu)) by (clear - HKr Hnu; nia). clear - Hw TOT KN. lia.
+ apply (Bimg _ INR). apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. cbn [cs] in Hw. unfold CTX_SIZE. lits. clear - Hw Hsc. lia.
+ apply (Bimg _ INR). apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. cbn [cs] in Hw. unfold CTX_SIZE. lits. clear - Hw Hsc. lia.
- unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. rewrite loc_addr_padd_. change (ptr_addr L' (pN am idx)) with P0. change (ms_segs B) with src0segs.
intros kk Hkk. destruct kk; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, YN03.le_byte_0. apply ZB. left. exists K. split; [lia|].
unfold totalN, UNIT, IB. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cs_facts'))))))). fold nu. clear. lia. }
assert (FOOT : Forall (foot_ok L' mem5) (footprint sNq)).
{ rewrite FPe. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) e He) as FO.
destruct (In_footprint_inv sq e He) as [-> | [(ar & Har & ->) | (kk & rg2 & Hrg2 & Hkd2 & Hlv2 & ->)]]; cbn [foot_ok fst snd] in FO |- *; [exact I | |].
- intros x Hx. destruct (areas_off_img B (m :: X) (Some (hg, idx)) U L' sq mem' md' HIq MID' ar x Har Hx) as [NI Rx]. apply PRES; [exact (FO x Hx) | clear - Rx AC; lia | exact NI].
- intros x Hx. pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID') _ rg2 Hrg2 Hlv2) as (_ & B1 & B2 & Bimg). cbn [loc_addr] in Hx.
apply PRES; [exact (FO x Hx) | clear - Hx B1 B2 AC; lia | exact (Bimg x ltac:(clear - Hx; lia))]. }
destruct (ledger_same B L' sq md' (mid_ledger _ _ _ _ _ MID') (mid_ledgerx _ _ _ _ _ MID') sNq md' Qr Qb eq_refl eq_refl eq_refl) as [LG5 LX5].
split.
- exact SO.
- split; [apply Forall_forall; exact IMG | split; [apply Forall_forall; exact TAIL | exact FOOT]].
- exact (tail_geom_of_Inv X (Some (m, 0)) U sNq L' HIN XCN HLN).
- apply (YN2d.statics_ok_ext B sq 0 mem'); [| exact (mid_statics _ _ _ _ _ MID')]. intros x Hx.
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)) as Hhi. pose proof (src0_img_range x (so_statics_img _ SO x Hx)) as Ri.
apply OLDB; [clear - Ri; lia | |].
+ unfold WD3, WD2, WD0, WS. intros [[[Hw|Hw]|Hw]|[Hw|Hw]]; [unfold ASF in *; clear - Hw Hhi P3 Hstk; lia | exact (proj1 (proj2 (RBm x Hw)) (so_statics_img _ SO x Hx)) | exact (proj1 (RNG x ltac:(clear - Hw EP0 HfitR P1' P2' Hko Sp; lia)) (so_statics_img _ SO x Hx)) | |];
apply (src0_SNC x Hx); change (ms_ctx B) with CTX; cbn [cs] in Hw; unfold CTX_SIZE; lits; clear - Hw Hsc; lia.
+ intros Hz. assert (RGN : GLO <= x < GLO + rg_len rg).
{ destruct Hz as [(i & Hi & ->)| ->]; [| clear - EP0 HfitR P1' P2' Hko Sp; lia]. assert (Hii : 0 <= i * (16 * nu) <= K * (16 * nu)) by (clear - Hi Hnu HKr; nia). clear - Hii TOT EP0 HfitR P1' P2' Hko. lia. }
exact (proj1 (RNG x RGN) (so_statics_img _ SO x Hx)).
- exact LG5.
- exact LX5.
- exact HLN.
- exact (mid_ctx _ _ _ _ _ MID').
- exact (mid_sec _ _ _ _ _ MID').
- exact (mid_md _ _ _ _ _ MID').
Qed.
Lemma finalsE : finalS_check ss_nE (SLit 0) = true /\ nth_error (ss_mem ss_nE) 6 = Some R_guard /\
(exists rstk, nth_error (ss_mem ss_nE) 4 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0).
Proof. vm_compute. split; [reflexivity|]. split; [reflexivity|]. eexists. repeat split; reflexivity. Qed.
Theorem leaf_nsucc : mreal src0segs (mkCfg ms0 md') (ibind (nest_rest sc m K j idx sq) KS) POSTn.
Proof.
pose proof nfacts as (HK & J3 & Hcs & HfitJ & Hk & Etot & H23 & Hscj' & Hj48 & HKr & Hnu & Ej & Etn & H26 & HhdN & C34 & HA0).
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7). assert (EASF : ASF = 384) by reflexivity.
pose proof sq_facts as (LE' & MID' & AMAq & BNDq & RSVq & SPOKq & AK' & UB & HBel & VM' & FR' & SCR' & GD' & HAE & XCq & Kmq & Mq & Eqm & RXq & HA' & E40').
pose proof (G_facts X U sq m hg am idx sc K j HIq Uhg Hscj Hsc HK1 H26q ARM HidxB Ejq) as (Glast & Glen & Hstr & Hfr & Hal & Gml & Gext & Rctr & Hhdr & Sp0 & Khg & NXhg).
destruct geoN as (kr & ko & GLO & rg & Emem & EGLO & _ & EpN & EP0 & Hr & Hrk & Hrl & Hko & HfitR & P1' & P2' & R4096 & Rceil & Ral & Hko16 & Hst16 & RNG & InR & KEYS & G1 & G2 & G3 & G4 & _ & HfitS & Sp & Gext').
destruct (key_factsR' (m :: X) (Some (hg, idx)) L' sq mem' md' m HIq MID' Kmq) as (RBm & _). rewrite Eqm in RBm. unfold META_SIZE in RBm.
pose proof sN_lists' as ((v1 & v2 & u1 & u2 & Ev & Ev' & Eu & Eu') & UBe & FPe & ROe & TCe & GCe & UMe & FRe).
pose proof sN_fields' as (Qm & Qr & Qar & Qb & _). pose proof amN_fields' as (Nmem & Nlast & Npr & Nnx & Nsc & Nml & Nai & Nav & Nfr & Nst & Next & Nsl).
destruct (sN_post' AMAq BNDq RSVq SPOKq HU) as (AMAN & BNDN & RSVN & SPOKN & AKN & USGN & HDN).
pose proof sN_inv' as (HIN & HhdN' & UN & EHN & UBN & XCN).
rewrite (nest_rest_eq sc m K j idx sq hg am Hhd (proj1 (usedX_MT _ _ _ _ Uhg)) Hstr HidxB HhdN). cbn [KS fst snd ibind mreal].
change (nest_st sc m K hg am idx j sq) with sNq.
apply (SR_bind _ _ _ _ reach_nE). intros c' (En & ms5 & -> & HS & HAn & En40 & En82 & En64 & En94 & En95 & En61 & En97 & En10 & OLD & Fc4 & ZER & LOLD & PRES).
pose proof finalsE as (CK & G6 & (rstk & Hrstk & Brstk & LOrstk & HIrstk)).
destruct (finalS L A regs mem sc stk PRE g j1 j2 En ss_nE ms5 (SLit 0) CK HS HAn) as (PRS & E1 & Hra & Hpc & Hrv & RA0).
apply (SR_final_retS En ss_nE ms5 md' _ HS Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mhq | exact Mlzq |].
pose proof (midrep_sN En ms5 HS HAn En40 En82 En64 En94 En95 En61 En97 En10 OLD Fc4 ZER LOLD PRES) as MIDN.
assert (OWe : forall x, owned B L' sNq x <-> owned B L' sq x).
{ intros x. unfold owned, alloc_owned, in_footprint, in_user_block. rewrite FPe, UBe. split; exact (fun H => H). }
assert (NMe : forall x, in_nonmap_region L' sNq x <-> in_nonmap_region L' sq x).
{ intros x. unfold in_nonmap_region. split; intros [P Q]; (split; [destruct P as (r0 & rg0 & H); exists r0, rg0; rewrite ?ROe in *; exact H | intros (r0 & rg0 & H); apply Q; exists r0, rg0; rewrite ?ROe in *; exact H]). }
assert (TOT : 12 + K * (16 * nu) + 4 <= ST) by (clear - HfitS Etot; subst total k; unfold UNIT, IB in *; nia).
assert (HLN : layout_ok L' sNq) by (exact (layout_ok_same L' sq sNq (mid_layout _ _ _ _ _ MID') Qr FPe)).
assert (CELLOWN : forall c x, In c (image sNq) -> loc_addr L' (mc_loc c) <= x < loc_addr L' (mc_loc c) + Z.of_nat (mc_w c) -> owned B L' sNq x).
{ intros c x Hc Hx. left. split.
- destruct (cellX_in_footprint X (Some (m, 0)) U sNq L' HIN c) as (e & He & Ie).
{ unfold imageX. apply in_app_iff. left. unfold image in Hc. rewrite !in_app_iff in Hc |- *. destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; exact Hc | right; right].
unfold used_metasX. rewrite (filter_all_In _ (used_metas sNq)); [exact Hc|]. intros [g0 a0] Hg0. cbn [fst].
destruct (memb g0 X) eqn:EM; [| reflexivity]. exfalso. apply (proj1 (memb_In g0 X)) in EM.
apply (used_metas_iff sNq g0 a0 (proj1 (inv_keys HIN))) in Hg0. exact (XCN g0 a0 EM Hg0). }
exists e. split; [exact He|]. unfold range_incl, cell_range, crange in Ie. cbn [fst snd] in Ie. clear - Ie Hx. lia.
- intros (b & Hb & Hbx). pose proof (image_outside_user_blocksX X (Some (m, 0)) U sNq L' HIN XCN HLN c b Hc Hb) as D.
unfold ranges_disjoint, cell_range, block_range in D. cbn [fst snd] in D. clear - D Hx Hbx. lia. }
assert (TAILOWN : forall c x, In c (tail_cells sNq) -> loc_addr L' (mc_loc c) <= x < loc_addr L' (mc_loc c) + Z.of_nat (mc_w c) -> owned B L' sNq x).
{ intros c x Hc Hx. left. pose proof (proj1 (Forall_forall _ _) (tail_geom_of_Inv X (Some (m, 0)) U sNq L' HIN XCN HLN) c Hc (Z.to_nat (x - loc_addr L' (mc_loc c))) ltac:(clear - Hx; lia)) as T.
rewrite Z2Nat.id in T by (clear - Hx; lia). replace (loc_addr L' (mc_loc c) + (x - loc_addr L' (mc_loc c))) with x in T by lia. exact T. }
assert (WOWN : forall x, (ptr_addr L1 m <= x < ptr_addr L1 m + 40 \/ P0 - 3 <= x < P0 + 9 \/ P0 - 4 <= x < P0 \/ (P0 + 12 <= x < P0 + ST /\ LOOPA x)) -> owned B L' sNq x).
{ intros x Hx.
assert (LM : forall off, loc_addr L' (LMem (padd m off)) = ptr_addr L1 m + off) by (intros off; rewrite loc_addr_padd_, Eqm; reflexivity).
assert (LP : forall off, loc_addr L' (LMem (padd (pN am idx) off)) = P0 + off) by (intros off; rewrite loc_addr_padd_; reflexivity).
destruct Hx as [Hx|[Hx|[Hx|[_ (i & Hi & ->)]]]].
- assert (CASE : exists off w v, In (MCell (LMem (padd m off)) w v) (meta_slot_cells m (Some (MUsed amNq))) /\ off <= x - ptr_addr L1 m < off + Z.of_nat w).
{ cbn [meta_slot_cells]. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits.
destruct (Z_lt_le_dec (x - ptr_addr L1 m) 8); [exists 0, 8%nat, (optr (am_prev amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (x - ptr_addr L1 m) 16); [exists 8, 8%nat, (optr (am_next amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (x - ptr_addr L1 m) 24); [exists 16, 8%nat, (VP (am_mem amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (x - ptr_addr L1 m) 28); [exists 24, 4%nat, (VZ (am_avail amNq)); split; [inlist | lia]|].
destruct (Z_lt_le_dec (x - ptr_addr L1 m) 32); [exists 28, 4%nat, (VZ (am_freed amNq)); split; [inlist | lia]|].
exists 32, 8%nat, (VZ (meta_bits amNq)). split; [inlist | lia]. }
destruct CASE as (off & w & v & Hin & Hoff). apply (CELLOWN (MCell (LMem (padd m off)) w v)); [apply NEW_in_image'; unfold NEW; rewrite !in_app_iff; right; left; exact Hin|]. cbn [mc_loc mc_w]. rewrite LM. clear - Hoff. lia.
- destruct (Z_lt_le_dec x (P0 - 2)); [| destruct (Z_lt_le_dec x P0); [| destruct (Z_lt_le_dec x (P0 + 8))]].
+ apply (CELLOWN (N3 am idx)); [apply NEW_in_image'; unfold NEW; apply in_app_iff; left; inlist|]. unfold N3. cbn [mc_loc mc_w]. rewrite LP. clear - Hx l; lia.
+ apply (CELLOWN (N16 am idx j)); [apply NEW_in_image'; unfold NEW; apply in_app_iff; left; inlist|]. unfold N16. cbn [mc_loc mc_w]. rewrite LP. clear - l l0; lia.
+ apply (CELLOWN (MCell (LMem (pN am idx)) 8 (VP m))); [apply NEW_in_image'; unfold NEW; rewrite !in_app_iff; right; right; apply GCe; left; reflexivity|]. cbn [mc_loc mc_w]. change (loc_addr L' (LMem (pN am idx))) with P0. clear - l0 l1; lia.
+ apply (CELLOWN (MCell (LMem (padd (pN am idx) 8)) 1 (VLo5 (K - 1)))); [apply NEW_in_image'; unfold NEW; rewrite !in_app_iff; right; right; apply GCe; right; left; reflexivity|]. cbn [mc_loc mc_w]. rewrite LP. clear - Hx l1; lia.
-
assert (X3 : x = P0 - 4 \/ P0 - 3 <= x < P0) by (clear - Hx; lia). destruct X3 as [-> | X3].
+ apply (CELLOWN (slot_chk amEq idx)).
* unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (hg, amEq). split; [apply UMe; right; left; reflexivity|]. cbn [fst snd].
rewrite group_cells_eq. apply in_app_iff. right. apply in_flat_map. exists idx. pose proof amE_fields' as (_ & Fl & _). split; [apply In_zseq; rewrite Fl; lia|]. rewrite slot_cells_eq. left. reflexivity.
* unfold slot_chk. cbn [mc_loc mc_w]. rewrite loc_addr_padd_. pose proof amE_fields' as (Fm & _ & _ & _ & Fst & _).
replace (ptr_addr L' (slot_start amEq idx)) with P0 by (unfold pN, slot_start; rewrite Fm, Fst; reflexivity). clear. lia.
+ destruct (Z_lt_le_dec x (P0 - 2)).
* apply (CELLOWN (N3 am idx)); [apply NEW_in_image'; unfold NEW; apply in_app_iff; left; inlist|]. unfold N3. cbn [mc_loc mc_w]. rewrite LP. clear - X3 l; lia.
* apply (CELLOWN (N16 am idx j)); [apply NEW_in_image'; unfold NEW; apply in_app_iff; left; inlist|]. unfold N16. cbn [mc_loc mc_w]. rewrite LP. clear - X3 l; lia.
- destruct (Z_lt_le_dec i K) as [Hi'|Hi'].
+ apply (CELLOWN (MCell (LMem (padd (slot_start amNq i) (-4))) 1 (VZ 0))); [apply NEW_in_image'; unfold NEW; rewrite !in_app_iff; right; right; apply GCe; right; right; exists i; split; [lia | reflexivity]|].
cbn [mc_loc mc_w]. rewrite loc_addr_padd_. unfold slot_start. rewrite Nmem, Nst, ptr_addr_padd. change (ptr_addr L' (pN am idx)) with P0.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cs_facts'))))))). fold nu. unfold UNIT. clear - Hi. lia.
+ assert (Ei : i = K) by lia. subst i. apply (TAILOWN (MCell (LMem (padd (pN am idx) (totalN sc K))) 1 (VZ 0))); [apply TCe; right; reflexivity|].
cbn [mc_loc mc_w]. rewrite LP. unfold totalN, UNIT, IB. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 cs_facts'))))))). fold nu. clear. lia. }
exists L', (ms_regs ms5), (ms_mem ms5), md'. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [exact MIDN|]. split; [exact AMAN|]. split; [exact BNDN|]. split; [exact RSVN|]. split; [exact SPOKN|]. split.
{ destruct LE1 as (Y1 & Y2 & Y3 & Y4). destruct LE' as (Z1 & Z2 & Z3 & Z4). split; [congruence|]. split; [congruence|]. split; [congruence|].
intros r0 Hr0. rewrite (Z4 r0) by lia. exact (Y4 r0 Hr0). }
split; [exact PRS|]. split; [exact VM'|]. split.
{ intros x Hx Nc No No' Nn Ns. unfold call_scratch, spZ in Ns. change (errno_addr B) with ERRNO in Ns. fold sp in Ns. change (ms_ctx B) with CTX in Nc.
assert (No2 : ~ owned B L' sq x) by (intros Ho; apply No'; apply (proj2 (OWe x)); exact Ho).
assert (Nn2 : ~ in_nonmap_region L' sq x) by (intros Hn'; apply Nn; apply (proj2 (NMe x)); exact Hn').
assert (COMMON : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ rewrite (FR' x Hx); [| clear - Ns; lia | clear - Ns; lia | exact Nc | | exact No2 | exact Nn2].
2:{ intros Ho. apply No2. exact (owned_mono' (m :: X) (m :: X) (Some (hg, idx)) s1 sq L1 L' x HI1 XC1n' HIq AK' UB LE' Ho). }
apply (FR1 x Hx); [unfold WS; clear - Ns EASF Hstk; lia | clear - Ns; lia | exact Nc |].
intros Hn1. apply Nn2. exact (nonmap_keep' (m :: X) (m :: X) (Some (hg, idx)) s1 sq L1 L' x HI1 XC1n' HIq AK' UB LE' Hn1 No2). }
assert (NW3 : ~ WD3 x).
{ unfold WD3, WD2, WD0, WS. intros [[[Hw|Hw]|Hw]|[Hw|Hw]].
+ clear - Hw Ns EASF Hstk. lia.
+ exact (No' (WOWN x (or_introl Hw))).
+ exact (No' (WOWN x (or_intror (or_introl Hw)))).
+ apply Nc. cbn [cs] in Hw. unfold CTX_SIZE. lits. clear - Hw Hsc. lia.
+ apply Nc. cbn [cs] in Hw. unfold CTX_SIZE. lits. clear - Hw Hsc. lia. }
destruct (ivl_dec (P0 + 12) (P0 + ST) x) as [Hl|Hl].
- destruct (LOOPA_dec x) as [HL|HL]; [exfalso; exact (No' (WOWN x (or_intror (or_intror (or_intror (conj Hl HL))))))|].
rewrite (LOLD x Hl) by (intros i Hi Ei; apply HL; exists i; exact (conj Hi Ei)). exact COMMON.
- rewrite (OLD x Hx NW3); [exact COMMON | | exact Hl]. intros Hp. exact (No' (WOWN x (or_intror (or_intror (or_introl Hp))))). }
split.
{ intros a0 Ha0. unfold call_scratch, spZ in Ha0. change (errno_addr B) with ERRNO in Ha0. fold sp in Ha0.
destruct (Z_lt_le_dec a0 (sp - ASF)) as [Hlo|Hhi]; [| destruct Ha0 as [Ha0|Ha0]; [| lits; lia]].
- assert (NW3 : ~ WD3 a0).
{ unfold WD3, WD2, WD0, WS. intros [[[Hw|Hw]|Hw]|[Hw|Hw]]; [clear - Hw Hlo; lia | | | |].
+ destruct (RBm a0 Hw) as (_ & _ & R). destruct Ha0 as [Ha0|Ha0]; [clear - R Ha0 P3 Hstk EASF; lia | apply (proj1 (proj2 (RBm a0 Hw))); apply src0_rwseg_img; lits; clear - Ha0; lia].
+ destruct Ha0 as [Ha0|Ha0]; [clear - Hw Ha0 P3 Hstk EASF EP0 HfitR P1' P2' Hko Rceil Sp; lia | apply (proj1 (RNG a0 ltac:(clear - Hw EP0 HfitR P1' P2' Hko Sp; lia))); apply src0_rwseg_img; lits; clear - Ha0; lia].
+ cbn [cs] in Hw. destruct Ha0 as [Ha0|Ha0]; [pose proof (so_ctx_hi _ (mid_syms _ _ _ _ _ MID')) as CH; change (ms_ctx B) with CTX in CH; unfold CTX_SIZE in CH; lits; clear - Hw Ha0 P3 Hstk EASF CH Hsc; lia | lits; clear - Hw Ha0 Hsc; lia].
+ cbn [cs] in Hw. destruct Ha0 as [Ha0|Ha0]; [pose proof (so_ctx_hi _ (mid_syms _ _ _ _ _ MID')) as CH; change (ms_ctx B) with CTX in CH; unfold CTX_SIZE in CH; lits; clear - Hw Ha0 P3 Hstk EASF CH Hsc; lia | lits; clear - Hw Ha0 Hsc; lia]. }
assert (NP : ~ (P0 - 4 <= a0 < P0) /\ ~ (P0 + 12 <= a0 < P0 + ST)).
{ destruct Ha0 as [Ha0|Ha0]; [split; intros Hw; clear - Hw Ha0 P3 Hstk EASF EP0 HfitR P1' P2' Hko Rceil Sp; lia|].
split; intros Hw; (apply (proj1 (RNG a0 ltac:(clear - Hw EP0 HfitR P1' P2' Hko Sp; lia))); apply src0_rwseg_img; lits; clear - Ha0; lia). }
destruct NP as [NP1 NP2].
apply (writable_ext1 mem'); [apply OLD; [lits; clear - Ha0 Hlo P3 P4 AC Hstk EASF; lia | exact NW3 | exact NP1 | exact NP2] | apply SCR'; clear - Ha0 Hlo EASF; lia].
- apply (writable_of_region regs En ss_nE ms5 4 rstk a0 HS Hrstk). rewrite Brstk, LOrstk, HIrstk. cbn [base_val]. rewrite (agree_reg' En 2 HAn ltac:(lia)).
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. clear - Hhi Ha0. lia. }
split; [rewrite RA0; apply bv_eq; reflexivity|].
split.
{ intros _ gg aa Hgg Haa Hlt. exfalso. rewrite HDN in Hgg. injection Hgg as <-. rewrite (sN_MT' m), sptr_eqb_refl in Haa. injection Haa as <-. rewrite Nst in Hlt. clear - Hlt. lia. }
split; [| exact (guard_of_state L A regs sc g j1 j2 En ss_nE ms5 6 HS HAn G6)].
eapply as_keep_trans; [exact AK1|]. eapply as_keep_trans; [exact (as_keep_cons m X s1 sq AK') | exact AKN].
Qed.
End NC.
Theorem nsucc : NSUCC X U L A regs mem md sc stk g j1 j2 m s1 L1 mem1 E.
Proof.
intros r c' Hge (L' & mem' & md' & E' & Ec & BASE & [[Hm1 _] | [_ (E64 & hg & am & HI' & Hhd & Uhg & Hsc' & Hfit' & Hidx & E80 & E81 & HS')]]); [lia|].
rewrite Ec. rewrite Ec in HS'. cbn [cfg_ms] in HS'.
destruct r as [idx sq]. cbn [fst snd] in *.
exact (leaf_nsucc idx sq L' mem' md' E' hg am BASE Hge E64 HI' Hhd Uhg Hsc' Hfit' Hidx E80 _ HS' eq_refl).
Qed.
End NA.
Theorem nsucc_all : NSUCC_all X U L A regs mem md sc stk g j1 j2.
Proof.
intros m s1 L1 mem1 md1 E HI1 RX1 AK1 Mm Km NXm US1 ACT1 LEN1 LE1 MID1 AMA1 BND1 VM1 FR1 ERRW1 HA E40 E56 E61 E62 ARM.
apply (nsucc m s1 L1 mem1 md1); assumption.
Qed.
End s.
Theorem src0_NEST_SUCC : NEST_SUCC.
Proof.
intros X U L A regs mem md sc n stk g j1 j2 fuel HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN IH.
eapply (nsucc_all X U L A regs mem md sc n stk) with (fuel := fuel); eassumption.
Qed.
Theorem src0_SEG_nest : alloc_meta_hyp B -> SEG_nest.
Proof. intros AMH. exact (src0_SEG_nest_partial AMH src0_NEST_SUCC). Qed.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
