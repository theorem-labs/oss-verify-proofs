(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN14.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition mp_usage (s : astate) (sc u : Z) : Z := if Z.even sc && (sc <? 32) then u + usage_of s (sc + 1) else u.
Definition mp_red (sc size cnt0 : Z) : Z :=
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt0) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt0) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt0) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt0) then 5
else cnt0.
Definition mp_cnt1 (s : astate) (sc cnt0 u : Z) : Z :=
if (mp_usage s sc u <? 4 * cnt0) && negb (is_bouncing s sc) then mp_red sc (class_size sc) cnt0 else cnt0.
Definition mp_rq (req : Z) : Z := page_round (req + IB + UNIT).
Definition mp_fin (s : astate) (sc req cnt1 u' : Z) : Z * Z :=
if negb (is_bouncing s sc) && (cnt1 <=? 7) then
if (mp_rq req <? class_size sc + UNIT) || ((4 * PGSZ <=? mp_rq req) && (u' <? 2 * cnt1)) then (1, mp_rq req)
else (cnt1, page_round (class_size sc * cnt1 + UNIT))
else (cnt1, page_round (class_size sc * cnt1 + UNIT)).
Lemma mmap_plan_eq : forall s sc req cnt0 u,
mmap_plan s sc req cnt0 u = mp_fin s sc req (mp_cnt1 s sc cnt0 u) (mp_usage s sc u).
Proof. reflexivity. Qed.
Lemma mp_red_r0 : forall sc size c, Z.land sc 3 = 0 -> mp_red sc size c = if 8 * PGSZ <? size * c then 3 else if 2 * PGSZ <? size * c then 5 else c.
Proof. intros sc size c H. unfold mp_red. rewrite H. reflexivity. Qed.
Lemma mp_red_r1 : forall sc size c, Z.land sc 3 = 1 -> mp_red sc size c = if 8 * PGSZ <? size * c then 2 else c.
Proof. intros sc size c H. unfold mp_red. rewrite H. cbn [Z.eqb andb]. destruct (8 * PGSZ <? size * c); reflexivity. Qed.
Lemma mp_red_r2 : forall sc size c, Z.land sc 3 = 2 -> mp_red sc size c = if 4 * PGSZ <? size * c then 3 else c.
Proof. intros sc size c H. unfold mp_red. rewrite H. cbn [Z.eqb andb]. destruct (4 * PGSZ <? size * c); reflexivity. Qed.
Lemma mp_red_r3 : forall sc size c, Z.land sc 3 = 3 -> mp_red sc size c = c.
Proof. intros sc size c H. unfold mp_red. rewrite H. reflexivity. Qed.
Lemma mp_cnt1_keep : forall s sc c u, (4 * c <= mp_usage s sc u \/ is_bouncing s sc = true) -> mp_cnt1 s sc c u = c.
Proof.
intros s sc c u [H|H]; unfold mp_cnt1.
- replace (mp_usage s sc u <? 4 * c) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- rewrite H. rewrite andb_false_r. reflexivity.
Qed.
Lemma mp_cnt1_red : forall s sc c u, mp_usage s sc u < 4 * c -> is_bouncing s sc = false -> mp_cnt1 s sc c u = mp_red sc (class_size sc) c.
Proof. intros s sc c u H1 H2. unfold mp_cnt1. rewrite H2. replace (mp_usage s sc u <? 4 * c) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma mp_usage_plain : forall s sc u, (Z.even sc = false \/ 32 <= sc) -> mp_usage s sc u = u.
Proof.
intros s sc u [H|H]; unfold mp_usage; [rewrite H; reflexivity|].
replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.
Lemma mp_usage_coarse : forall s sc u, Z.even sc = true -> sc <= 31 -> mp_usage s sc u = u + usage_of s (sc + 1).
Proof. intros s sc u H1 H2. unfold mp_usage. rewrite H1. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma round_machine : forall x, 0 <= x -> x + Z.land (- x) 4095 = page_round x.
Proof.
intros x Hx. rewrite land_4095. unfold page_round, PGSZ.
pose proof (Z_div_mod_eq_full x 4096) as E1. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as B1.
pose proof (Z_div_mod_eq_full (- x) 4096) as E2. pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)) as B2.
pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096) as E3. pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)) as B3.
nia.
Qed.
Section e.
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
Section MB.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Variable E3 : env.
Hypothesis HA3 : env_agree 40 E00 E3.
Hypothesis E3_40 : ew E3 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis E3_56 : ew E3 56 = Z_to_bv 64 (usage_of s1 sc).
Hypothesis E3_61 : ew E3 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc)).
Hypothesis E3_62 : ew E3 62 = Z_to_bv 64 (16 * nu * initial_cnt sc (usage_of s1 sc)).
Hypothesis E3_67 : ew E3 67 = Z_to_bv 64 (if is_bouncing s1 sc then 1 else 0).
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Let usage : Z := usage_of s1 sc.
Let usage2 : Z := usage_of s1 (sc + 1).
Let K : Z := initial_cnt sc usage.
Let s3 : astate := seq_st (ab_st sc s1).
Let cnt1 : Z := mp_cnt1 s1 sc K usage.
Let usage' : Z := mp_usage s1 sc usage.
Let plan : Z * Z := mmap_plan s1 sc n K usage.
Let E4 : env := ewset E3 73 (Z_to_bv 64 usage2).
Definition FRcB (mm : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (CTX <= x < CTX + CTX_SIZE) -> mm (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x).
Definition CWB (E : env) (ss : sstate) (c : config) : Prop :=
exists ms, c = mkCfg ms md1 /\ st_ok src0segs E ss ms /\ midrep B L1 s3 (ms_mem ms) md1 /\ FRcB (ms_mem ms).
Lemma s3_facts : Inv (m :: X) None U s3 /\ Xclean (m :: X) s3 /\ ama_ok s3 /\ usage_of s3 (sc + 1) = usage2 /\ bounded s3.
Proof.
pose proof (ab_st_fields sc s1) as (F1 & F2 & F3 & F4 & F5 & _ & _ & _ & _ & _ & _ & F12). pose proof (seq_st_fields (ab_st sc s1)) as (G1 & G2 & G3 & G4 & G5 & _ & _ & _ & _ & _ & G11).
subst s3 usage2. split; [apply Inv_seq_st; apply Inv_ab_st; exact HI1|]. split.
{ intros x am Hx Hu. unfold MT in Hu. rewrite G1, F1 in Hu. exact (XC1 X m s1 RX1 Mm x am Hx Hu). }
split; [unfold ama_ok; rewrite G2, F2, G11, F12, G3, F3; exact AMA1|]. split; [unfold usage_of; rewrite G5, F5; reflexivity|].
unfold bounded, usage_of. rewrite G5, F5, G2, F2. destruct BND1 as (B1 & B2 & B3). split; [exact B1|]. split; [| exact B3].
subst. unfold seq_st. destruct (st_seq (ab_st sc s1) =? 255); cbn; unfold ab_st; destruct (bounce_idx sc); try exact B2; destruct (negb _ && _); exact B2.
Qed.
Lemma E4_facts : env_agree 73 E3 E4 /\ env_agree 40 E00 E4 /\ ew E4 73 = Z_to_bv 64 usage2 /\ ew E4 10 = Z_to_bv 64 sc /\ ew E4 11 = Z_to_bv 64 n /\
ew E4 33 = Z_to_bv 64 (csn 33) /\ ew E4 35 = Z_to_bv 64 nu /\ ew E4 56 = Z_to_bv 64 usage /\ ew E4 61 = Z_to_bv 64 K /\ ew E4 62 = Z_to_bv 64 (16 * nu * K) /\
ew E4 67 = Z_to_bv 64 (if is_bouncing s1 sc then 1 else 0).
Proof.
assert (AG : env_agree 73 E3 E4) by (split; [intros k Hk; subst E4; rewrite ew_ewset_other by lia; reflexivity | reflexivity]).
assert (AG' : env_agree 40 E00 E4) by (eapply env_agree_trans; [exact HA3 | eapply env_agree_le; [| exact AG]; lia]).
destruct AG as [Y D]. split; [exact (conj Y D)|]. split; [exact AG'|]. split; [subst E4; apply ew_ewset_same|].
split; [rewrite (agree_reg' E4 10 AG') by lia; exact R10|]. split; [rewrite (agree_reg' E4 11 AG') by lia; exact R11|].
split; [exact (agree_cs' E4 33 AG' ltac:(lia))|]. split; [exact (agree_cs' E4 35 AG' ltac:(lia))|].
rewrite !Y by lia. repeat split; assumption.
Qed.
Lemma ranges : 0 <= usage < 2 ^ 48 /\ 0 <= usage2 < 2 ^ 48 /\ 1 <= K <= 32 /\ 16 * nu * K < 2 ^ 20 /\ 1 <= nu <= 8191 /\ class_size sc = 16 * nu /\ (sc <= 26 -> 2 <= K).
Proof.
destruct BND1 as (B1 & _). pose proof (initial_cnt_facts sc usage Hsc) as (K1 & K2 & K3).
destruct cs_facts' as (_ & _ & _ & C35 & _ & _ & _ & CS). subst usage usage2 K nu.
split; [apply B1|]. split; [apply B1|]. split; [exact K1|]. split; [rewrite CS in K2; lia|]. split; [exact C35|]. split; [exact CS | exact K3].
Qed.
Lemma cwb_run : forall E S ss ss' st (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL S ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(forall ms', st_ok src0segs E ss' ms' -> midrep B L1 s3 (ms_mem ms') md1 -> FRcB (ms_mem ms') -> SR src0segs (mkCfg ms' md1) Q) ->
forall cfg, CWB E ss cfg -> SR src0segs cfg Q.
Proof.
intros E S ss ss' st Q RUN NE WSB HA KQ cfg (ms & -> & HS & HM & HF). pose proof s3_facts as (I3 & X3 & A3 & _).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL S E ss ss' st); [exact Mh1 | exact Mlz1 | exact HS | exact RUN |].
intros ms' HS' Hfr.
assert (ST : forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ms_mem ms' (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)).
{ intros x Hx Hw. apply (frame_of_at E _ _ _ x Hfr Hx). intros Hin. destruct (in_wrange_wsub regs E _ SKS x WSB Hin) as (b & lo & hi & Hl & Hx').
unfold SKS in Hl. destruct Hl as [Hl|[]]. injection Hl as <- <- <-. exact (Hw (win_stack L A regs sc g j1 j2 s1 E x HA Hx')). }
apply KQ; [destruct st; first [exact HS' | destruct NE] | |].
- exact (midrep_stack_gen U regs mem stk PRE Hstk (m :: X) L1 s3 (ms_mem ms) md1 (ms_mem ms') I3 X3 A3 HM ST).
- intros x Hx Hw Hc. rewrite (ST x Hx Hw). exact (HF x Hx Hw Hc).
Qed.
Lemma cwb_node : forall E S ss ss' c a b (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL S ss = (ss', RS_stopped (SR_branch c a b)) -> wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true -> forall cfg, CWB E (add_cond ss' (mkAC c a b)) cfg -> SR src0segs cfg Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false -> forall cfg, CWB E (add_cond ss' (mkAC (neg_bc c) a b)) cfg -> SR src0segs cfg Q) ->
forall cfg, CWB E ss cfg -> SR src0segs cfg Q.
Proof.
intros E S ss ss' c a b Q RUN WSB HA KT KF. apply (cwb_run E S ss ss' _ Q RUN I WSB HA).
intros ms' HS' HM' HF'. apply (SR_sym_branch src0segs E ss' ms' md1 Q c a b HS').
- intros Hb HSb. apply (KT Hb). exists ms'. repeat (split; [reflexivity || assumption|]). exact HF'.
- intros Hb HSb. apply (KF Hb). exists ms'. repeat (split; [reflexivity || assumption|]). exact HF'.
Qed.
Lemma cwb_leaf : forall E S ss ss' (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL S ss = (ss', RS_running) -> wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(forall cfg, CWB E ss' cfg -> SR src0segs cfg Q) -> forall cfg, CWB E ss cfg -> SR src0segs cfg Q.
Proof.
intros E S ss ss' Q RUN WSB HA KQ. apply (cwb_run E S ss ss' _ Q RUN I WSB HA).
intros ms' HS' HM' HF'. apply KQ. exists ms'. repeat (split; [reflexivity || assumption|]). exact HF'.
Qed.
Lemma cwb_station : forall E E' S ss ss' ssS st (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL S ss = (ss', RS_stopped st) -> wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(forall ms, st_ok src0segs E ss' ms -> midrep B L1 s3 (ms_mem ms) md1 -> st_ok src0segs E' ssS ms) ->
(forall cfg, CWB E' ssS cfg -> SR src0segs cfg Q) -> forall cfg, CWB E ss cfg -> SR src0segs cfg Q.
Proof.
intros E E' S ss ss' ssS st Q RUN WSB HA ST KQ. apply (cwb_run E S ss ss' _ Q RUN I WSB HA).
intros ms' HS' HM' HF'. apply KQ. exists ms'. split; [reflexivity|]. split; [exact (ST ms' HS' HM') |]. split; [exact HM' | exact HF'].
Qed.
Lemma residue_facts : forall r, sc mod 4 = r -> Z.land sc 3 = r /\ Z.land sc 1 = r mod 2 /\ Z.even sc = Z.even r.
Proof.
intros r Hr. assert (L3' : Z.land sc 3 = sc mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
assert (L1' : Z.land sc 1 = sc mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
split; [lia|]. split.
- rewrite L1', <- Hr. pose proof (Z_div_mod_eq_full sc 4). pose proof (Z_div_mod_eq_full sc 2). pose proof (Z_div_mod_eq_full (sc mod 4) 2).
pose proof (Z.mod_pos_bound sc 4). pose proof (Z.mod_pos_bound sc 2). pose proof (Z.mod_pos_bound (sc mod 4) 2). lia.
- rewrite <- Hr.
destruct (Z.even sc) eqn:E1; destruct (Z.even (sc mod 4)) eqn:E2; try reflexivity; exfalso.
+ apply Z.even_spec in E1. destruct E1 as [k Hk]. assert (Hodd : Z.odd (sc mod 4) = true) by (rewrite <- Z.negb_even, E2; reflexivity).
apply Z.odd_spec in Hodd. destruct Hodd as [k' Hk']. pose proof (Z_div_mod_eq_full sc 4). lia.
+ apply Z.even_spec in E2. destruct E2 as [k Hk]. assert (Hodd : Z.odd sc = true) by (rewrite <- Z.negb_even, E1; reflexivity).
apply Z.odd_spec in Hodd. destruct Hodd as [k' Hk']. pose proof (Z_div_mod_eq_full sc 4). lia.
Qed.
Lemma conds_r_ok : forall r ms, sc mod 4 = r -> 0 <= r < 4 -> st_ok src0segs E4 ss_M1 ms -> st_ok src0segs E4 (ss_M1r r) ms.
Proof.
intros r ms Hr R4 HS. destruct (residue_facts r Hr) as (L3 & L1' & EV). destruct E4_facts as (_ & _ & _ & E10 & _).
assert (R2 : 0 <= r mod 2 < 2) by (apply Z.mod_pos_bound; lia).
assert (D1 : sv_denot E4 a5_1 = Z_to_bv 64 (r mod 2)).
{ unfold a5_1. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E10, alu64_and. rewrite (lit64_small sc) by lia. rewrite Z.add_0_r, !lit64_small by lia. exact L1'. }
assert (D3 : sv_denot E4 a5_3 = Z_to_bv 64 r).
{ unfold a5_3. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E10, alu64_and. rewrite (lit64_small sc) by lia. rewrite Z.add_0_r, !lit64_small by lia. exact L3. }
unfold ss_M1r, conds_r. cbn [fold_left].
repeat apply st_ok_add_cond; try exact HS.
- rewrite D1, den_lit. destruct (Z.even r) eqn:ER.
+ rewrite branch_eq, !lit64_small by lia. apply Z.eqb_eq. apply Z.even_spec in ER. destruct ER as [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
+ rewrite branch_ne, !lit64_small by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. intros H0.
assert (Hodd : Z.odd r = true) by (rewrite <- Z.negb_even, ER; reflexivity). apply Z.odd_spec in Hodd. destruct Hodd as [k ->].
rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full in H0. rewrite Z.mod_small in H0 by lia. lia.
- rewrite D3, den_lit. assert (C : r = 1 \/ r <> 1) by lia. destruct C as [->|C]; [rewrite Z.eqb_refl, branch_eq|replace (r =? 1) with false by (symmetry; apply Z.eqb_neq; lia); rewrite branch_ne]; rewrite !lit64_small by lia; [apply Z.eqb_refl | apply Bool.negb_true_iff; apply Z.eqb_neq; lia].
- rewrite D3, den_lit. assert (C : r = 2 \/ r <> 2) by lia. destruct C as [->|C]; [rewrite Z.eqb_refl, branch_eq|replace (r =? 2) with false by (symmetry; apply Z.eqb_neq; lia); rewrite branch_ne]; rewrite !lit64_small by lia; [apply Z.eqb_refl | apply Bool.negb_true_iff; apply Z.eqb_neq; lia].
- rewrite D3, den_lit. assert (C : r = 0 \/ r <> 0) by lia. destruct C as [->|C]; [rewrite Z.eqb_refl, branch_eq|replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia); rewrite branch_ne]; rewrite !lit64_small by lia; [apply Z.eqb_refl | apply Bool.negb_true_iff; apply Z.eqb_neq; lia].
Qed.
Definition skel_M1 := [(Some 33%nat, 472, 480); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)].
Lemma station_U2 : forall ss ms, map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss) = skel_M1 -> ss_resv ss = None -> sc <= 31 ->
st_ok src0segs E4 ss ms -> midrep B L1 s3 (ms_mem ms) md1 -> st_ok src0segs E4 (stU2 ss) ms.
Proof.
intros ss ms SK RV H31 HS HM. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts' as (C33 & C33m & _). destruct E4_facts as (_ & AG4 & E73 & E10 & E11 & E33 & _). pose proof ranges as (_ & RU2 & _).
pose proof s3_facts as (_ & _ & _ & U3 & _).
assert (B33 : bv_unsigned (ew E4 33) = csn 33) by (rewrite E33; apply lit64_small; lits; lia).
assert (B2 : bv_unsigned (ew E4 2) = sp) by (rewrite (agree_reg' E4 2 AG4) by lia; reflexivity).
assert (HS1 : st_ok src0segs E4 (mkSS (ss_pc ss) (ss_regs ss) (R_use2 :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms).
{ apply (st_ok_add_region src0segs E4 _ ms R_use2 HS); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_use2]; rewrite B33; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E4 (ms_mem ms) (csn 33) 480 _ usage2).
+ apply den_off0. exact E73.
+ rewrite <- U3. cbn [cs]. replace (LOCK + 8 * sc + 480) with (LOCK + 8 * (sc + 1) + 472) by lia. exact (usage_word L1 s3 (ms_mem ms) md1 (sc + 1) HM ltac:(lia)).
- apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite SK in Hr'. unfold skel_M1 in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_use2 base_val]. rewrite B33.
cbn [In] in Hr'.
repeat (destruct Hr' as [Hr'|Hr']; [apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr'; cbn in Hr'; injection Hr' as <- <- <-; cbn [base_val]; rewrite ?B33, ?B2; lits; lia |]).
destruct Hr'. }
apply (st_ok_add_fact src0segs E4 _ ms 73 F_use2) in HS1. 2:{ unfold afact_ok, F_use2. cbn [af_lo af_hi af_al2]. rewrite E73, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
unfold stU2. rewrite <- RV. exact HS1.
Qed.
Lemma btK1 : forall (b : bool), branch_taken BC_LT (sv_denot E4 (SLit 31)) (sv_denot E4 (SOff 10 0)) = b -> if b then 32 <= sc else sc <= 31.
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & E10 & _). rewrite (den_off0 E4 10 sc E10), den_lit, branch_lt, !lit64_small in H by lia.
unfold s64 in H. replace (31 <? 2 ^ 63) with true in H by reflexivity. replace (sc <? 2 ^ 63) with true in H by (symmetry; apply Z.ltb_lt; lia).
destruct b; [destruct (31 <? sc) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate] | destruct (31 <? sc) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia]].
Qed.
Lemma btK2a : forall (b : bool), branch_taken BC_GEU (sv_denot E4 (SOff 56 0)) (sv_denot E4 (SAlu ALU_SLL (SOff 61 0) (SLit 2))) = b -> if b then 4 * K <= usage else usage < 4 * K.
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & _ & _ & _ & _ & E56 & E61 & _). pose proof ranges as (RU & _ & RK & _).
rewrite (den_off0 E4 56 usage E56), branch_geu, lit64_small in H by lia. cbn [sv_denot] in H. rewrite E61, alu64_sll in H.
rewrite (lit64_small K) in H by lia. rewrite Z.add_0_r, (lit64_small K), (lit64_small 2) in H by lia. change (2 mod 64) with 2 in H.
rewrite sll64_small in H by (change (2 ^ 2) with 4; lia). change (2 ^ 2) with 4 in H.
destruct b; [destruct (usage <? K * 4) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia] | destruct (usage <? K * 4) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate]].
Qed.
Lemma btK2b : forall (b : bool), branch_taken BC_GEU (sv_denot E4 (SAlu ALU_ADD (SOff 56 0) (SOff 73 0))) (sv_denot E4 (SAlu ALU_SLL (SOff 61 0) (SLit 2))) = b ->
if b then 4 * K <= usage + usage2 else usage + usage2 < 4 * K.
Proof.
intros b H. destruct E4_facts as (_ & _ & E73 & _ & _ & _ & _ & E56 & E61 & _). pose proof ranges as (RU & RU2 & RK & _).
rewrite branch_geu in H. cbn [sv_denot] in H. rewrite E56, E73, E61, alu64_add, alu64_sll in H.
rewrite (lit64_small K), (lit64_small usage), (lit64_small usage2) in H by lia. rewrite !Z.add_0_r, (lit64_small K), (lit64_small usage), (lit64_small usage2), (lit64_small 2) in H by lia.
change (2 mod 64) with 2 in H. rewrite sll64_small in H by (change (2 ^ 2) with 4; lia). change (2 ^ 2) with 4 in H. rewrite add64_small in H by lia.
destruct b; [destruct (usage + usage2 <? K * 4) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia] | destruct (usage + usage2 <? K * 4) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate]].
Qed.
Lemma btK3_gen : forall E' (b : bool), ew E' 67 = Z_to_bv 64 (if is_bouncing s1 sc then 1 else 0) ->
branch_taken BC_NE (sv_denot E' (SOff 67 0)) (sv_denot E' (SLit 0)) = b -> is_bouncing s1 sc = b.
Proof.
intros E' b E67 H. rewrite (den_off0 E' 67 _ E67), den_lit, branch_ne in H. destruct (is_bouncing s1 sc); rewrite !lit64_small in H by lia; cbn in H; destruct b; congruence.
Qed.
Lemma btK3 : forall (b : bool), branch_taken BC_NE (sv_denot E4 (SOff 67 0)) (sv_denot E4 (SLit 0)) = b -> is_bouncing s1 sc = b.
Proof. intros b H. destruct E4_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E67). exact (btK3_gen E4 b E67 H). Qed.
Lemma btK5 : forall (b : bool), branch_taken BC_LTU (sv_denot E4 (SLit 32768)) (sv_denot E4 (SOff 62 0)) = b -> if b then 32768 < 16 * nu * K else 16 * nu * K <= 32768.
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E62 & _). pose proof ranges as (_ & _ & RK & RV & RN & _).
rewrite (den_off0 E4 62 _ E62), den_lit, branch_ltu, !lit64_small in H by nia.
destruct b; [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; exact H.
Qed.
Lemma btK5g : forall (b : bool), branch_taken BC_GEU (sv_denot E4 (SLit 32768)) (sv_denot E4 (SOff 62 0)) = b -> if b then 16 * nu * K <= 32768 else 32768 < 16 * nu * K.
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E62 & _). pose proof ranges as (_ & _ & RK & RV & RN & _).
rewrite (den_off0 E4 62 _ E62), den_lit, branch_geu, !lit64_small in H by nia.
destruct b; [destruct (32768 <? 16 * nu * K) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia] | destruct (32768 <? 16 * nu * K) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate]].
Qed.
Lemma btK6 : forall (b : bool), branch_taken BC_GEU (sv_denot E4 (SLit 16384)) (sv_denot E4 (SOff 62 0)) = b -> if b then 16 * nu * K <= 16384 else 16384 < 16 * nu * K.
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E62 & _). pose proof ranges as (_ & _ & RK & RV & RN & _).
rewrite (den_off0 E4 62 _ E62), den_lit, branch_geu, !lit64_small in H by nia.
destruct b; [destruct (16384 <? 16 * nu * K) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia] | destruct (16384 <? 16 * nu * K) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate]].
Qed.
Lemma btK7 : forall (b : bool), branch_taken BC_GEU (sv_denot E4 (SLit 8192)) (sv_denot E4 (SOff 62 0)) = b -> if b then 16 * nu * K <= 8192 else 8192 < 16 * nu * K.
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E62 & _). pose proof ranges as (_ & _ & RK & RV & RN & _).
rewrite (den_off0 E4 62 _ E62), den_lit, branch_geu, !lit64_small in H by nia.
destruct b; [destruct (8192 <? 16 * nu * K) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia] | destruct (8192 <? 16 * nu * K) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate]].
Qed.
Lemma btK4 : forall (b : bool),
branch_taken BC_NE (sv_denot E4 (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0)))) (sv_denot E4 (SLit 0)) = b ->
if b then Z.land sc 3 = 0 /\ 32768 < 16 * nu * K else (Z.land sc 3 <> 0 \/ 16 * nu * K <= 32768).
Proof.
intros b H. destruct E4_facts as (_ & _ & _ & E10 & _ & _ & _ & _ & _ & E62 & _). pose proof ranges as (_ & _ & RK & RV & RN & _).
assert (L3 : 0 <= Z.land sc 3 < 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; pose proof (Z.mod_pos_bound sc 4); lia).
rewrite branch_ne, den_lit in H. cbn [sv_denot] in H. rewrite E10, E62, !alu64_and, !alu64_sltu, alu64_and in H.
rewrite (lit64_small sc), (lit64_small (16 * nu * K)) in H by nia. rewrite !Z.add_0_r, (lit64_small sc), (lit64_small (16 * nu * K)), (lit64_small 3), (lit64_small 1), (lit64_small 32768), (lit64_small 0) in H by nia.
unfold sltu in H.
destruct (Z.land sc 3 <? 1) eqn:Y1; [apply Z.ltb_lt in Y1 | apply Z.ltb_ge in Y1]; destruct (32768 <? 16 * nu * K) eqn:Y2; [apply Z.ltb_lt in Y2 | apply Z.ltb_ge in Y2 | apply Z.ltb_lt in Y2 | apply Z.ltb_ge in Y2]; cbn in H; destruct b; try discriminate; first [split; lia | left; lia | right; lia].
Qed.
Definition CNpost (c : config) : Prop :=
exists E5 ms, c = mkCfg ms md1 /\ st_ok src0segs E5 ss_CN ms /\ env_agree 74 E4 E5 /\ ew E5 74 = Z_to_bv 64 cnt1 /\ ew E5 75 = Z_to_bv 64 usage' /\
midrep B L1 s3 (ms_mem ms) md1 /\ FRcB (ms_mem ms).
Lemma cnt1_range : 1 <= cnt1 <= 32 /\ 0 <= usage' < 2 ^ 49.
Proof.
pose proof ranges as (RU & RU2 & RK & _). subst cnt1 usage'. split.
- unfold mp_cnt1, mp_red. destruct (_ && negb _); [| lia]. repeat (destruct (_ && _); [lia|]). lia.
- unfold mp_usage. destruct (Z.even sc && (sc <? 32)); lia.
Qed.
Lemma to_CN : forall ss ms cv uv, cn_check ss = true -> st_ok src0segs E4 ss ms ->
sv_denot E4 (sr_get (ss_regs ss) 25) = Z_to_bv 64 cv -> sv_denot E4 (sr_get (ss_regs ss) 10) = Z_to_bv 64 uv -> cv = cnt1 -> uv = usage' ->
midrep B L1 s3 (ms_mem ms) md1 -> FRcB (ms_mem ms) -> CNpost (mkCfg ms md1).
Proof.
intros ss ms cv uv CK HS D25 D10 -> -> HM HF. pose proof cnt1_range as [CR UR].
unfold cn_check in CK. apply andb_prop in CK as [CK MG]. apply andb_prop in CK as [AT FS].
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) CN_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs CN_JUNK 74 E4 ss ms HS AT NZ) as (E5 & [Y D5] & HS5).
assert (R25 : sr_get (ss_regs (junk_regs CN_JUNK 74 ss)) 25 = SOff 74 0).
{ unfold CN_JUNK. cbn [junk_regs ss_regs]. rewrite !sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (R10' : sr_get (ss_regs (junk_regs CN_JUNK 74 ss)) 10 = SOff 75 0).
{ unfold CN_JUNK. cbn [junk_regs ss_regs]. rewrite !sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (E74 : ew E5 74 = Z_to_bv 64 cnt1).
{ pose proof (st_ok_regs_ok _ E5 _ ms HS5 25%bv) as X1. pose proof (st_ok_regs_ok _ E4 _ ms HS 25%bv) as X2. rewrite R25 in X1. rewrite D25 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
assert (E75 : ew E5 75 = Z_to_bv 64 usage').
{ pose proof (st_ok_regs_ok _ E5 _ ms HS5 10%bv) as X1. pose proof (st_ok_regs_ok _ E4 _ ms HS 10%bv) as X2. rewrite R10' in X1. rewrite D10 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
assert (HFM : facts_ok E5 facts_CN).
{ destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HF0). pose proof (facts_subb_sound E4 _ _ FS HF0) as HF1.
assert (AG : env_agree 74 E4 E5) by (split; [exact Y | exact D5]).
pose proof (facts_ok_agree 74 E4 E5 (ss_facts ss_M1) AG ltac:(vm_compute; reflexivity) HF1) as (Y1 & Y2 & Y3).
unfold facts_CN. split; [| split; [exact Y2 | exact I]]. cbn [f_atoms atoms_ok]. split; [| split; [| exact Y1]].
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E74, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E75, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exists E5, ms. split; [reflexivity|]. split.
{ exact (st_ok_merge src0segs E5 ss_CN (setfacts facts_CN (junk_regs CN_JUNK 74 ss)) ms (st_ok_setfacts src0segs E5 _ ms facts_CN HS5 HFM) MG). }
split; [exact (conj Y D5)|]. split; [exact E74|]. split; [exact E75|]. split; [exact HM | exact HF].
Qed.
Lemma tree_b0 : sc mod 4 = 0 -> forall cfg, CWB E4 (ss_M1r 0) cfg -> SR src0segs cfg CNpost.
Proof.
intros Hr. destruct (residue_facts 0 Hr) as (L3 & _ & EV). cbn [Z.even] in EV. pose proof ranges as (RU & RU2 & RK & RV & RN & CS & K26). destruct E4_facts as (_ & AG4 & E73 & E10 & E11 & E33 & E35 & E56 & E61 & E62 & E67).
assert (W_b0_ : wsub (ss_mem ss_b0_) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_T : wsub (ss_mem ss_b0_T) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TT : wsub (ss_mem ss_b0_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TF : wsub (ss_mem ss_b0_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFT : wsub (ss_mem ss_b0_TFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFF : wsub (ss_mem ss_b0_TFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFT : wsub (ss_mem ss_b0_TFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFTT : wsub (ss_mem ss_b0_TFFTT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFTF : wsub (ss_mem ss_b0_TFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFTFT : wsub (ss_mem ss_b0_TFFTFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFTFF : wsub (ss_mem ss_b0_TFFTFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFF : wsub (ss_mem ss_b0_TFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFFT : wsub (ss_mem ss_b0_TFFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFFF : wsub (ss_mem ss_b0_TFFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFFFT : wsub (ss_mem ss_b0_TFFFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_TFFFFF : wsub (ss_mem ss_b0_TFFFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_F : wsub (ss_mem ss_b0_F) SKS = true) by (vm_compute; reflexivity).
assert (WU_b0_F : wsub (ss_mem (stU2 ss_b0_F)) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_Fu : wsub (ss_mem ss_b0_Fu) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FT : wsub (ss_mem ss_b0_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FF : wsub (ss_mem ss_b0_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFT : wsub (ss_mem ss_b0_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFF : wsub (ss_mem ss_b0_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFT : wsub (ss_mem ss_b0_FFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFTT : wsub (ss_mem ss_b0_FFFTT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFTF : wsub (ss_mem ss_b0_FFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFTFT : wsub (ss_mem ss_b0_FFFTFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFTFF : wsub (ss_mem ss_b0_FFFTFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFF : wsub (ss_mem ss_b0_FFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFFT : wsub (ss_mem ss_b0_FFFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFFF : wsub (ss_mem ss_b0_FFFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFFFT : wsub (ss_mem ss_b0_FFFFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b0_FFFFFF : wsub (ss_mem ss_b0_FFFFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_root : wsub (ss_mem (ss_M1r 0)) SKS = true) by (vm_compute; reflexivity).
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_ W_root AG4); intros B0; pose proof (btK1 _ B0) as F0; cbv iota in F0.
-
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_T W_b0_ AG4); intros B1; pose proof (btK2a _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TT W_b0_T AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_TT ms_ (K) (usage) cn_b0_TT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_plain s1 sc usage (or_intror F0)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_TF W_b0_T AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFT W_b0_TF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_TFT ms_ (K) (usage) cn_b0_TFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_TFF W_b0_TF AG4); intros B3; pose proof (btK4 _ B3) as F3; cbv iota in F3.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_TFFT W_b0_TFF AG4); intros B4; pose proof (btK5 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFFTT W_b0_TFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_TFFTT ms_ (3) (usage) cn_b0_TFFTT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r0 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
first [ replace (2 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (2 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
++
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_TFFTF W_b0_TFFT AG4); intros B5; pose proof (btK7 _ B5) as F5; cbv iota in F5.
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFFTFT W_b0_TFFTF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFFTFF W_b0_TFFTF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_TFFF W_b0_TFF AG4); intros B4; pose proof (btK5 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFFFT W_b0_TFFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
++
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_TFFFF W_b0_TFFF AG4); intros B5; pose proof (btK7 _ B5) as F5; cbv iota in F5.
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFFFFT W_b0_TFFFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_TFFFFT ms_ (K) (usage) cn_b0_TFFFFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r0 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
first [ replace (2 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (2 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_TFFFFF W_b0_TFFFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_TFFFFF ms_ (5) (usage) cn_b0_TFFFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r0 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
first [ replace (2 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (2 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
-
assert (SK_F : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_b0_F) = skel_M1) by (vm_compute; reflexivity).
apply (cwb_station E4 E4 PS_CN _ _ (stU2 ss_b0_F) _ _ gs_b0_F W_b0_ AG4); [intros ms_ HS_ HM_; exact (station_U2 ss_b0_F ms_ SK_F eq_refl ltac:(lia) HS_ HM_) |].
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_Fu WU_b0_F AG4); intros B1; pose proof (btK2b _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FT W_b0_Fu AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_FT ms_ (K) (usage + usage2) cn_b0_FT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ change (sr_get (ss_regs ss_b0_FT) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_FF W_b0_Fu AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFT W_b0_FF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_FFT ms_ (K) (usage + usage2) cn_b0_FFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ change (sr_get (ss_regs ss_b0_FFT) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_FFF W_b0_FF AG4); intros B3; pose proof (btK4 _ B3) as F3; cbv iota in F3.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_FFFT W_b0_FFF AG4); intros B4; pose proof (btK5 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFFTT W_b0_FFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_FFFTT ms_ (3) (usage + usage2) cn_b0_FFFTT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ change (sr_get (ss_regs ss_b0_FFFTT) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)); exact F1 | exact F2]). rewrite (mp_red_r0 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
first [ replace (2 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (2 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
++
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_FFFTF W_b0_FFFT AG4); intros B5; pose proof (btK7 _ B5) as F5; cbv iota in F5.
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFFTFT W_b0_FFFTF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFFTFF W_b0_FFFTF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_FFFF W_b0_FFF AG4); intros B4; pose proof (btK5 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFFFT W_b0_FFFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
++
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b0_FFFFF W_b0_FFFF AG4); intros B5; pose proof (btK7 _ B5) as F5; cbv iota in F5.
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFFFFT W_b0_FFFFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_FFFFFT ms_ (K) (usage + usage2) cn_b0_FFFFFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ change (sr_get (ss_regs ss_b0_FFFFFT) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)); exact F1 | exact F2]). rewrite (mp_red_r0 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
first [ replace (2 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (2 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
**
apply (cwb_leaf E4 PS_CN _ _ _ gs_b0_FFFFFF W_b0_FFFFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b0_FFFFFF ms_ (5) (usage + usage2) cn_b0_FFFFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ change (sr_get (ss_regs ss_b0_FFFFFF) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)); exact F1 | exact F2]). rewrite (mp_red_r0 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
first [ replace (2 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (2 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
Qed.
Lemma tree_b1 : sc mod 4 = 1 -> forall cfg, CWB E4 (ss_M1r 1) cfg -> SR src0segs cfg CNpost.
Proof.
intros Hr. destruct (residue_facts 1 Hr) as (L3 & _ & EV). cbn [Z.even] in EV. pose proof ranges as (RU & RU2 & RK & RV & RN & CS & K26). destruct E4_facts as (_ & AG4 & E73 & E10 & E11 & E33 & E35 & E56 & E61 & E62 & E67).
assert (W_b1_ : wsub (ss_mem ss_b1_) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_T : wsub (ss_mem ss_b1_T) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TT : wsub (ss_mem ss_b1_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TF : wsub (ss_mem ss_b1_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TFT : wsub (ss_mem ss_b1_TFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TFF : wsub (ss_mem ss_b1_TFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TFFT : wsub (ss_mem ss_b1_TFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TFFTT : wsub (ss_mem ss_b1_TFFTT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TFFTF : wsub (ss_mem ss_b1_TFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_TFFF : wsub (ss_mem ss_b1_TFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_F : wsub (ss_mem ss_b1_F) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FT : wsub (ss_mem ss_b1_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FF : wsub (ss_mem ss_b1_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FFT : wsub (ss_mem ss_b1_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FFF : wsub (ss_mem ss_b1_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FFFT : wsub (ss_mem ss_b1_FFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FFFTT : wsub (ss_mem ss_b1_FFFTT) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FFFTF : wsub (ss_mem ss_b1_FFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_b1_FFFF : wsub (ss_mem ss_b1_FFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_root : wsub (ss_mem (ss_M1r 1)) SKS = true) by (vm_compute; reflexivity).
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_ W_root AG4); intros B0; pose proof (btK1 _ B0) as F0; cbv iota in F0.
-
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_T W_b1_ AG4); intros B1; pose proof (btK2a _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_TT W_b1_T AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_TT ms_ (K) (usage) cn_b1_TT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_plain s1 sc usage (or_intror F0)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_TF W_b1_T AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_TFT W_b1_TF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_TFT ms_ (K) (usage) cn_b1_TFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_TFF W_b1_TF AG4); intros B3; pose proof (btK5g _ B3) as F3; cbv iota in F3.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_TFFT W_b1_TFF AG4); intros B4; pose proof (btK4 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_TFFTT W_b1_TFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_TFFTF W_b1_TFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_TFFTF ms_ (K) (usage) cn_b1_TFFTF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r1 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_TFFF W_b1_TFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_TFFF ms_ (2) (usage) cn_b1_TFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r1 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
-
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_F W_b1_ AG4); intros B1; pose proof (btK2a _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_FT W_b1_F AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_FT ms_ (K) (usage) cn_b1_FT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_plain s1 sc usage (or_introl EV)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_FF W_b1_F AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_FFT W_b1_FF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_FFT ms_ (K) (usage) cn_b1_FFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_FFF W_b1_FF AG4); intros B3; pose proof (btK5g _ B3) as F3; cbv iota in F3.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b1_FFFT W_b1_FFF AG4); intros B4; pose proof (btK4 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_FFFTT W_b1_FFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_FFFTF W_b1_FFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_FFFTF ms_ (K) (usage) cn_b1_FFFTF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_introl EV)); exact F1 | exact F2]). rewrite (mp_red_r1 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b1_FFFF W_b1_FFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b1_FFFF ms_ (2) (usage) cn_b1_FFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_introl EV)); exact F1 | exact F2]). rewrite (mp_red_r1 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (8 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (8 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
Qed.
Lemma tree_b2 : sc mod 4 = 2 -> forall cfg, CWB E4 (ss_M1r 2) cfg -> SR src0segs cfg CNpost.
Proof.
intros Hr. destruct (residue_facts 2 Hr) as (L3 & _ & EV). cbn [Z.even] in EV. pose proof ranges as (RU & RU2 & RK & RV & RN & CS & K26). destruct E4_facts as (_ & AG4 & E73 & E10 & E11 & E33 & E35 & E56 & E61 & E62 & E67).
assert (W_b2_ : wsub (ss_mem ss_b2_) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_T : wsub (ss_mem ss_b2_T) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TT : wsub (ss_mem ss_b2_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TF : wsub (ss_mem ss_b2_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TFT : wsub (ss_mem ss_b2_TFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TFF : wsub (ss_mem ss_b2_TFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TFFT : wsub (ss_mem ss_b2_TFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TFFTT : wsub (ss_mem ss_b2_TFFTT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TFFTF : wsub (ss_mem ss_b2_TFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_TFFF : wsub (ss_mem ss_b2_TFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_F : wsub (ss_mem ss_b2_F) SKS = true) by (vm_compute; reflexivity).
assert (WU_b2_F : wsub (ss_mem (stU2 ss_b2_F)) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_Fu : wsub (ss_mem ss_b2_Fu) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FT : wsub (ss_mem ss_b2_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FF : wsub (ss_mem ss_b2_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FFT : wsub (ss_mem ss_b2_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FFF : wsub (ss_mem ss_b2_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FFFT : wsub (ss_mem ss_b2_FFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FFFTT : wsub (ss_mem ss_b2_FFFTT) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FFFTF : wsub (ss_mem ss_b2_FFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_b2_FFFF : wsub (ss_mem ss_b2_FFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_root : wsub (ss_mem (ss_M1r 2)) SKS = true) by (vm_compute; reflexivity).
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_ W_root AG4); intros B0; pose proof (btK1 _ B0) as F0; cbv iota in F0.
-
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_T W_b2_ AG4); intros B1; pose proof (btK2a _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_TT W_b2_T AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_TT ms_ (K) (usage) cn_b2_TT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_plain s1 sc usage (or_intror F0)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_TF W_b2_T AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_TFT W_b2_TF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_TFT ms_ (K) (usage) cn_b2_TFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_TFF W_b2_TF AG4); intros B3; pose proof (btK6 _ B3) as F3; cbv iota in F3.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_TFFT W_b2_TFF AG4); intros B4; pose proof (btK4 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_TFFTT W_b2_TFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_TFFTF W_b2_TFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_TFFTF ms_ (K) (usage) cn_b2_TFFTF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r2 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (4 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (4 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_TFFF W_b2_TFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_TFFF ms_ (3) (usage) cn_b2_TFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r2 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (4 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (4 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
-
assert (SK_F : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_b2_F) = skel_M1) by (vm_compute; reflexivity).
apply (cwb_station E4 E4 PS_CN _ _ (stU2 ss_b2_F) _ _ gs_b2_F W_b2_ AG4); [intros ms_ HS_ HM_; exact (station_U2 ss_b2_F ms_ SK_F eq_refl ltac:(lia) HS_ HM_) |].
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_Fu WU_b2_F AG4); intros B1; pose proof (btK2b _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_FT W_b2_Fu AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_FT ms_ (K) (usage + usage2) cn_b2_FT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ change (sr_get (ss_regs ss_b2_FT) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_FF W_b2_Fu AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_FFT W_b2_FF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_FFT ms_ (K) (usage + usage2) cn_b2_FFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ change (sr_get (ss_regs ss_b2_FFT) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_FFF W_b2_FF AG4); intros B3; pose proof (btK6 _ B3) as F3; cbv iota in F3.
--
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b2_FFFT W_b2_FFF AG4); intros B4; pose proof (btK4 _ B4) as F4; cbv iota in F4.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_FFFTT W_b2_FFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
++
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_FFFTF W_b2_FFFT AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_FFFTF ms_ (K) (usage + usage2) cn_b2_FFFTF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ change (sr_get (ss_regs ss_b2_FFFTF) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)); exact F1 | exact F2]). rewrite (mp_red_r2 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (4 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (4 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b2_FFFF W_b2_FFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b2_FFFF ms_ (3) (usage + usage2) cn_b2_FFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_lit. }
{ change (sr_get (ss_regs ss_b2_FFFF) 10) with (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)). apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E73, alu64_add. rewrite (lit64_small usage), (lit64_small usage2) by lia. rewrite !Z.add_0_r, (lit64_small usage), (lit64_small usage2), add64_small, lit64_small by lia. reflexivity. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_coarse s1 sc usage EV ltac:(lia)); exact F1 | exact F2]). rewrite (mp_red_r2 sc (class_size sc) K L3). rewrite ?CS.
first [ replace (4 * PGSZ <? 16 * nu * K) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ; lia) | replace (4 * PGSZ <? 16 * nu * K) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ; lia) | idtac ].
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_coarse s1 sc usage EV ltac:(lia)). }
Qed.
Lemma tree_b3 : sc mod 4 = 3 -> forall cfg, CWB E4 (ss_M1r 3) cfg -> SR src0segs cfg CNpost.
Proof.
intros Hr. destruct (residue_facts 3 Hr) as (L3 & _ & EV). cbn [Z.even] in EV. pose proof ranges as (RU & RU2 & RK & RV & RN & CS & K26). destruct E4_facts as (_ & AG4 & E73 & E10 & E11 & E33 & E35 & E56 & E61 & E62 & E67).
assert (W_b3_ : wsub (ss_mem ss_b3_) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_T : wsub (ss_mem ss_b3_T) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_TT : wsub (ss_mem ss_b3_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_TF : wsub (ss_mem ss_b3_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_TFT : wsub (ss_mem ss_b3_TFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_TFF : wsub (ss_mem ss_b3_TFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_TFFT : wsub (ss_mem ss_b3_TFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_TFFF : wsub (ss_mem ss_b3_TFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_F : wsub (ss_mem ss_b3_F) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_FT : wsub (ss_mem ss_b3_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_FF : wsub (ss_mem ss_b3_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_FFT : wsub (ss_mem ss_b3_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_FFF : wsub (ss_mem ss_b3_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_FFFT : wsub (ss_mem ss_b3_FFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_b3_FFFF : wsub (ss_mem ss_b3_FFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_root : wsub (ss_mem (ss_M1r 3)) SKS = true) by (vm_compute; reflexivity).
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_ W_root AG4); intros B0; pose proof (btK1 _ B0) as F0; cbv iota in F0.
-
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_T W_b3_ AG4); intros B1; pose proof (btK2a _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_TT W_b3_T AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b3_TT ms_ (K) (usage) cn_b3_TT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_plain s1 sc usage (or_intror F0)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_TF W_b3_T AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_TFT W_b3_TF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b3_TFT ms_ (K) (usage) cn_b3_TFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_TFF W_b3_TF AG4); intros B3; pose proof (btK4 _ B3) as F3; cbv iota in F3.
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_TFFT W_b3_TFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_TFFF W_b3_TFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b3_TFFF ms_ (K) (usage) cn_b3_TFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_intror F0)); exact F1 | exact F2]). rewrite (mp_red_r3 sc (class_size sc) K L3). rewrite ?CS.
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_intror F0)). }
-
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_F W_b3_ AG4); intros B1; pose proof (btK2a _ B1) as F1; cbv iota in F1.
+
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_FT W_b3_F AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b3_FT ms_ (K) (usage) cn_b3_FT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. left. rewrite (mp_usage_plain s1 sc usage (or_introl EV)). exact F1. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
+
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_FF W_b3_F AG4); intros B2; pose proof (btK3 _ B2) as F2; cbv iota in F2.
*
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_FFT W_b3_FF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b3_FFT ms_ (K) (usage) cn_b3_FFT HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. apply mp_cnt1_keep. right. exact F2. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
*
apply (cwb_node E4 PS_CN _ _ _ _ _ _ gs_b3_FFF W_b3_FF AG4); intros B3; pose proof (btK4 _ B3) as F3; cbv iota in F3.
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_FFFT W_b3_FFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
exfalso. lia.
--
apply (cwb_leaf E4 PS_CN _ _ _ gs_b3_FFFF W_b3_FFF AG4). intros cfg_ (ms_ & -> & HS_ & HM_ & HF_). apply SR_ret.
apply (to_CN ss_b3_FFFF ms_ (K) (usage) cn_b3_FFFF HS_); [ | | | | exact HM_ | exact HF_].
{ apply den_off0. exact E61. }
{ apply den_off0. exact E56. }
{ symmetry. cbv delta [cnt1]. rewrite (mp_cnt1_red s1 sc K usage) by (first [rewrite (mp_usage_plain s1 sc usage (or_introl EV)); exact F1 | exact F2]). rewrite (mp_red_r3 sc (class_size sc) K L3). rewrite ?CS.
reflexivity. }
{ symmetry. cbv delta [usage']. exact (mp_usage_plain s1 sc usage (or_introl EV)). }
Qed.
Lemma reach_CN : forall ms, st_ok src0segs E3 ss_M1 ms -> midrep B L1 s3 (ms_mem ms) md1 -> FRcB (ms_mem ms) -> SR src0segs (mkCfg ms md1) CNpost.
Proof.
intros ms HS HM HF. destruct E4_facts as (AG34 & _).
assert (HS4 : st_ok src0segs E4 ss_M1 ms) by (eapply (st_ok_agree src0segs 73 E3 E4); [exact HS | exact AG34 | vm_compute; reflexivity]).
assert (R4 : 0 <= sc mod 4 < 4) by (apply Z.mod_pos_bound; lia).
assert (CW0 : forall r, sc mod 4 = r -> CWB E4 (ss_M1r r) (mkCfg ms md1)).
{ intros r Hr. exists ms. split; [reflexivity|]. split; [apply (conds_r_ok r ms Hr ltac:(lia) HS4)|]. split; [exact HM | exact HF]. }
assert (C : sc mod 4 = 0 \/ sc mod 4 = 1 \/ sc mod 4 = 2 \/ sc mod 4 = 3) by lia.
destruct C as [Hr|[Hr|[Hr|Hr]]]; [exact (tree_b0 Hr _ (CW0 0 Hr)) | exact (tree_b1 Hr _ (CW0 1 Hr)) | exact (tree_b2 Hr _ (CW0 2 Hr)) | exact (tree_b3 Hr _ (CW0 3 Hr))].
Qed.
Section B2.
Variable E5 : env.
Hypothesis AG5 : env_agree 74 E4 E5.
Hypothesis E5_74 : ew E5 74 = Z_to_bv 64 cnt1.
Hypothesis E5_75 : ew E5 75 = Z_to_bv 64 usage'.
Lemma E5_facts : env_agree 40 E00 E5 /\ ew E5 11 = Z_to_bv 64 n /\ ew E5 35 = Z_to_bv 64 nu /\ ew E5 67 = Z_to_bv 64 (if is_bouncing s1 sc then 1 else 0).
Proof.
destruct E4_facts as (_ & AG4 & _ & _ & E11 & _ & E35 & _ & _ & _ & E67). destruct AG5 as [Y D].
split; [eapply env_agree_trans; [exact AG4 | eapply env_agree_le; [| exact (conj Y D)]; lia]|]. rewrite !Y by lia. repeat split; assumption.
Qed.
Definition RQ : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20).
Definition NX : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SOff 74 0))
(SAlu ALU_AND (SAlu ALU_SUB (SLit 18446744073709551600) (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SOff 74 0))) (SLit 4095))) (SLit 16).
Lemma den_rq : sv_denot E5 RQ = Z_to_bv 64 (mp_rq n).
Proof.
destruct E5_facts as (_ & E11 & _). unfold RQ, mp_rq. apply (proj2 (word_eq _ _)). cbn [sv_denot].
rewrite E11, !alu64_add, alu64_and, alu64_sub. rewrite (lit64_small n) by (unfold MMAP_THRESHOLD in Hn; lia).
rewrite !Z.add_0_r, (lit64_small n), (lit64_small (n + 20)), (lit64_small 0), (lit64_small 4095), (lit64_small 20) by (unfold MMAP_THRESHOLD in Hn; lia).
unfold sub64. rewrite Z.sub_0_l.
assert (HL : Z.land ((- (n + 20)) mod 2 ^ 64) 4095 = Z.land (- (n + 20)) 4095).
{ rewrite !land_4095. symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 52); reflexivity]. }
rewrite HL. pose proof (round_machine (n + 20) ltac:(lia)) as RM. unfold IB, UNIT.
assert (0 <= Z.land (- (n + 20)) 4095 < 4096) by (rewrite land_4095; apply Z.mod_pos_bound; lia).
unfold MMAP_THRESHOLD in Hn. rewrite (add64_small n) by lia. rewrite add64_small by lia.
pose proof (page_round_ge (n + 4 + 16)). pose proof (page_round_lt (n + 4 + 16)). unfold PGSZ in *.
replace (n + 4 + 16) with (n + 20) in * by lia. rewrite lit64_small by lia. lia.
Qed.
Lemma den_needed : sv_denot E5 NX = Z_to_bv 64 (page_round (16 * nu * cnt1 + 16)).
Proof.
destruct E5_facts as (_ & _ & E35 & _). pose proof cnt1_range as [CR _]. pose proof ranges as (_ & _ & _ & _ & RN & _).
unfold NX. apply (proj2 (word_eq _ _)). cbn [sv_denot].
rewrite E35, E5_74, !alu64_add, alu64_and, alu64_sub, !mul64_unsigned, !alu64_sll. rewrite (lit64_small nu), (lit64_small cnt1) by lia.
rewrite !Z.add_0_r, (lit64_small nu), (lit64_small cnt1), (lit64_small 4), (lit64_small 4095), (lit64_small 16), (lit64_small 18446744073709551600) by lia.
change (4 mod 64) with 4. rewrite sll64_small by (change (2 ^ 4) with 16; lia). change (2 ^ 4) with 16. rewrite mul64_small by nia.
set (P := nu * 16 * cnt1). assert (HP : 16 <= P <= 8191 * 16 * 32) by (subst P; nia).
unfold sub64. replace ((18446744073709551600 - P) mod 2 ^ 64) with (2 ^ 64 - (P + 16)) by (rewrite Z.mod_small by lia; lia).
assert (HL : Z.land (2 ^ 64 - (P + 16)) 4095 = Z.land (- (P + 16)) 4095).
{ rewrite !land_4095. replace (2 ^ 64 - (P + 16)) with (- (P + 16) + (2 ^ 52) * 4096) by lia. rewrite Z_mod_plus_full. reflexivity. }
rewrite HL. assert (0 <= Z.land (- (P + 16)) 4095 < 4096) by (rewrite land_4095; apply Z.mod_pos_bound; lia).
pose proof (round_machine (P + 16) ltac:(lia)) as RM.
pose proof (page_round_ge (P + 16)). pose proof (page_round_lt (P + 16)). unfold PGSZ in *.
rewrite (add64_small P) by lia. rewrite add64_small by lia.
replace (16 * nu * cnt1) with P by (subst P; lia). rewrite lit64_small by lia. lia.
Qed.
Lemma plan_facts : 1 <= fst plan <= 32 /\ 4096 <= snd plan <= 2 ^ 20 /\ snd plan mod 4096 = 0 /\ 16 * nu * cnt1 < 2 ^ 20 /\ 4096 <= mp_rq n <= 131072.
Proof.
pose proof cnt1_range as [CR _]. pose proof ranges as (_ & _ & RK & RV & RN & CS & _).
assert (HC : 16 * nu * cnt1 < 2 ^ 20).
{ subst cnt1. unfold mp_cnt1. destruct (_ && negb _); [| exact RV]. unfold mp_red. repeat (destruct (_ && _); [nia|]). exact RV. }
assert (RQ1 : 4096 <= mp_rq n <= 131072).
{ unfold mp_rq, IB, UNIT, MMAP_THRESHOLD in *. pose proof (page_round_ge (n + 4 + 16)). pose proof (page_round_mod (n + 4 + 16)).
pose proof (page_round_mono (n + 4 + 16) 131072 ltac:(lia)). replace (page_round 131072) with 131072 in H1 by reflexivity. unfold PGSZ in *.
pose proof (Z_div_mod_eq_full (page_round (n + 4 + 16)) 4096). lia. }
assert (ND : forall c, 1 <= c -> 16 * nu * c < 2 ^ 20 -> 4096 <= page_round (class_size sc * c + UNIT) <= 2 ^ 20 /\ page_round (class_size sc * c + UNIT) mod 4096 = 0).
{ intros c Hc1 Hc2. rewrite CS. unfold UNIT. pose proof (page_round_ge (16 * nu * c + 16)). pose proof (page_round_mod (16 * nu * c + 16)).
pose proof (page_round_mono (16 * nu * c + 16) (2 ^ 20) ltac:(lia)). replace (page_round (2 ^ 20)) with (2 ^ 20) in H1 by reflexivity. unfold PGSZ in *.
pose proof (Z_div_mod_eq_full (page_round (16 * nu * c + 16)) 4096). nia. }
subst plan. rewrite mmap_plan_eq. fold usage' cnt1. unfold mp_fin.
destruct (negb (is_bouncing s1 sc) && (cnt1 <=? 7)); [destruct (_ || _)|]; cbn [fst snd].
- pose proof (page_round_mod (n + IB + UNIT)) as M. unfold mp_rq in *. unfold PGSZ in M. lia.
- destruct (ND cnt1 ltac:(lia) HC). lia.
- destruct (ND cnt1 ltac:(lia) HC). lia.
Qed.
Lemma btK8 : forall (b : bool), branch_taken BC_NE (sv_denot E5 (SOff 67 0)) (sv_denot E5 (SLit 0)) = b -> is_bouncing s1 sc = b.
Proof. intros b H. destruct E5_facts as (_ & _ & _ & E67). exact (btK3_gen E5 b E67 H). Qed.
Lemma btK9 : forall (b : bool), branch_taken BC_LTU (sv_denot E5 (SLit 7)) (sv_denot E5 (SOff 74 0)) = b -> if b then 7 < cnt1 else cnt1 <= 7.
Proof.
intros b H. pose proof cnt1_range as [CR _]. rewrite (den_off0 E5 74 _ E5_74), den_lit, branch_ltu, !lit64_small in H by lia.
destruct b; [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; exact H.
Qed.
Lemma btK10 : forall (b : bool), branch_taken BC_GEU (sv_denot E5 RQ) (sv_denot E5 (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16))) = b ->
if b then 16 * nu + 16 <= mp_rq n else mp_rq n < 16 * nu + 16.
Proof.
intros b H. destruct E5_facts as (_ & _ & E35 & _). pose proof ranges as (_ & _ & _ & _ & RN & _). pose proof plan_facts as (_ & _ & _ & _ & RQR).
rewrite den_rq, branch_geu, lit64_small in H by lia. cbn [sv_denot] in H. rewrite E35, alu64_add, alu64_sll in H.
rewrite (lit64_small nu) in H by lia. rewrite Z.add_0_r, (lit64_small nu), (lit64_small 4), (lit64_small 16) in H by lia. change (4 mod 64) with 4 in H.
rewrite sll64_small in H by (change (2 ^ 4) with 16; lia). change (2 ^ 4) with 16 in H. rewrite add64_small in H by lia.
destruct b; [destruct (mp_rq n <? nu * 16 + 16) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia] | destruct (mp_rq n <? nu * 16 + 16) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate]].
Qed.
Lemma btK11 : forall (b : bool), branch_taken BC_LTU (sv_denot E5 RQ) (sv_denot E5 (SLit 16384)) = b -> if b then mp_rq n < 16384 else 16384 <= mp_rq n.
Proof.
intros b H. pose proof plan_facts as (_ & _ & _ & _ & RQR). rewrite den_rq, den_lit, branch_ltu, !lit64_small in H by lia.
destruct b; [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; exact H.
Qed.
Lemma btK12 : forall (b : bool), branch_taken BC_LTU (sv_denot E5 (SOff 75 0)) (sv_denot E5 (SAlu ALU_SLL (SOff 74 0) (SLit 1))) = b -> if b then usage' < 2 * cnt1 else 2 * cnt1 <= usage'.
Proof.
intros b H. pose proof cnt1_range as [CR UR]. rewrite (den_off0 E5 75 _ E5_75), branch_ltu, lit64_small in H by lia. cbn [sv_denot] in H.
rewrite E5_74, alu64_sll in H. rewrite (lit64_small cnt1) in H by lia. rewrite Z.add_0_r, (lit64_small cnt1), (lit64_small 1) in H by lia. change (1 mod 64) with 1 in H.
rewrite sll64_small in H by (change (2 ^ 1) with 2; lia). change (2 ^ 1) with 2 in H.
destruct b; [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; lia.
Qed.
Definition MMpost (c : config) : Prop :=
exists E6 ms, c = mkCfg ms md1 /\ st_ok src0segs E6 ss_MM ms /\ env_agree 81 E5 E6 /\ ew E6 81 = Z_to_bv 64 (snd plan) /\ ew E6 82 = Z_to_bv 64 (fst plan) /\
midrep B L1 s3 (ms_mem ms) md1 /\ FRcB (ms_mem ms).
Lemma to_MM : forall ss ms nv cv, mm_check ss = true -> st_ok src0segs E5 ss ms ->
sv_denot E5 (sr_get (ss_regs ss) 19) = Z_to_bv 64 nv -> sv_denot E5 (sr_get (ss_regs ss) 25) = Z_to_bv 64 cv -> (cv, nv) = plan ->
midrep B L1 s3 (ms_mem ms) md1 -> FRcB (ms_mem ms) -> MMpost (mkCfg ms md1).
Proof.
intros ss ms nv cv CK HS D19 D25 EP HM HF. pose proof plan_facts as (P1 & P2 & P3 & _). rewrite <- EP in P1, P2, P3. cbn [fst snd] in P1, P2, P3.
unfold mm_check in CK. apply andb_prop in CK as [CK MG]. apply andb_prop in CK as [AT FS].
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) MM_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs MM_JUNK 81 E5 ss ms HS AT NZ) as (E6 & [Y D6] & HS6).
assert (R19 : sr_get (ss_regs (junk_regs MM_JUNK 81 ss)) 19 = SOff 81 0).
{ unfold MM_JUNK. cbn [junk_regs ss_regs]. rewrite !sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (R25 : sr_get (ss_regs (junk_regs MM_JUNK 81 ss)) 25 = SOff 82 0).
{ unfold MM_JUNK. cbn [junk_regs ss_regs]. rewrite !sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (E81 : ew E6 81 = Z_to_bv 64 nv).
{ pose proof (st_ok_regs_ok _ E6 _ ms HS6 19%bv) as X1. pose proof (st_ok_regs_ok _ E5 _ ms HS 19%bv) as X2. rewrite R19 in X1. rewrite D19 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
assert (E82 : ew E6 82 = Z_to_bv 64 cv).
{ pose proof (st_ok_regs_ok _ E6 _ ms HS6 25%bv) as X1. pose proof (st_ok_regs_ok _ E5 _ ms HS 25%bv) as X2. rewrite R25 in X1. rewrite D25 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
assert (HFM : facts_ok E6 facts_MM).
{ destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HF0). pose proof (facts_subb_sound E5 _ _ FS HF0) as HF1.
assert (AG : env_agree 81 E5 E6) by (split; [exact Y | exact D6]).
assert (AG46 : env_agree 74 E4 E6) by (eapply env_agree_trans; [exact AG5 | eapply env_agree_le; [| exact AG]; lia]).
pose proof (facts_ok_agree 81 E5 E6 (ss_facts ss_M1) AG ltac:(vm_compute; reflexivity) HF1) as (Y1 & Y2 & Y3). pose proof cnt1_range as [CR UR].
unfold facts_MM, facts_CN. split; [| split; [exact Y2 | exact I]]. cbn [f_atoms atoms_ok]. split; [| split; [| split; [| split; [| exact Y1]]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
- rewrite E81, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 12) with 4096. exact P3.
- rewrite E82, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r.
- rewrite (Y 74%nat), E5_74, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r.
- rewrite (Y 75%nat), E5_75, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exists E6, ms. split; [reflexivity|]. split.
{ exact (st_ok_merge src0segs E6 ss_MM (setfacts facts_MM (junk_regs MM_JUNK 81 ss)) ms (st_ok_setfacts src0segs E6 _ ms facts_MM HS6 HFM) MG). }
split; [exact (conj Y D6)|]. rewrite <- EP. cbn [fst snd]. split; [exact E81|]. split; [exact E82|]. split; [exact HM | exact HF].
Qed.
Lemma plan_keep : (is_bouncing s1 sc = true \/ 7 < cnt1 \/ (16 * nu + 16 <= mp_rq n /\ (mp_rq n < 16384 \/ 2 * cnt1 <= usage'))) ->
(cnt1, page_round (16 * nu * cnt1 + 16)) = plan.
Proof.
intros H. pose proof ranges as (_ & _ & _ & _ & _ & CS & _). subst plan. rewrite mmap_plan_eq. fold usage' cnt1. unfold mp_fin. rewrite CS. unfold UNIT.
destruct H as [H|[H|[H1 H2]]].
- rewrite H. reflexivity.
- replace (cnt1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. reflexivity.
- destruct (negb _ && _); [| reflexivity].
replace (mp_rq n <? 16 * nu + 16) with false by (symmetry; apply Z.ltb_ge; lia).
destruct H2 as [H2|H2]; [replace (4 * PGSZ <=? mp_rq n) with false by (symmetry; apply Z.leb_gt; unfold PGSZ; lia) | replace (usage' <? 2 * cnt1) with false by (symmetry; apply Z.ltb_ge; lia); rewrite andb_false_r]; reflexivity.
Qed.
Lemma plan_one : is_bouncing s1 sc = false -> cnt1 <= 7 -> (mp_rq n < 16 * nu + 16 \/ (16384 <= mp_rq n /\ usage' < 2 * cnt1)) -> (1, mp_rq n) = plan.
Proof.
intros H1 H2 H3. pose proof ranges as (_ & _ & _ & _ & _ & CS & _). subst plan. rewrite mmap_plan_eq. fold usage' cnt1. unfold mp_fin. rewrite CS, H1. unfold UNIT.
replace (cnt1 <=? 7) with true by (symmetry; apply Z.leb_le; lia). cbn [negb andb].
destruct H3 as [H3|[H3 H4]].
- replace (mp_rq n <? 16 * nu + 16) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- replace (4 * PGSZ <=? mp_rq n) with true by (symmetry; apply Z.leb_le; unfold PGSZ; lia). replace (usage' <? 2 * cnt1) with true by (symmetry; apply Z.ltb_lt; lia). rewrite orb_true_r. reflexivity.
Qed.
Lemma tree_c : forall cfg, CWB E5 ss_CN cfg -> SR src0segs cfg MMpost.
Proof.
destruct E5_facts as (AG05 & E11 & E35 & E67). pose proof cnt1_range as [CR UR]. pose proof ranges as (RU & RU2 & RK & RV & RN & CS & K26). pose proof plan_facts as (P1 & P2 & P3 & P4 & P5).
assert (W0 : wsub (ss_mem ss_CN) SKS = true) by (vm_compute; reflexivity).
assert (W1 : wsub (ss_mem ss_c_) SKS = true) by (vm_compute; reflexivity).
assert (W2 : wsub (ss_mem ss_c_F) SKS = true) by (vm_compute; reflexivity).
assert (W3 : wsub (ss_mem ss_c_FF) SKS = true) by (vm_compute; reflexivity).
assert (W4 : wsub (ss_mem ss_c_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W5 : wsub (ss_mem ss_c_FFTF) SKS = true) by (vm_compute; reflexivity).
assert (DN : forall ss, sr_get (ss_regs ss) 19 = NX -> sv_denot E5 (sr_get (ss_regs ss) 19) = Z_to_bv 64 (page_round (16 * nu * cnt1 + 16))) by (intros ss ->; exact den_needed).
assert (DQ : forall ss, sr_get (ss_regs ss) 19 = SAlu ALU_ADD RQ (SLit 0) -> sv_denot E5 (sr_get (ss_regs ss) 19) = Z_to_bv 64 (mp_rq n)).
{ intros ss ->. change (sv_denot E5 (SAlu ALU_ADD RQ (SLit 0))) with (alu64 ALU_ADD (sv_denot E5 RQ) (Z_to_bv 64 0)).
rewrite den_rq. apply (proj2 (word_eq _ _)). rewrite alu64_add, !lit64_small by lia. rewrite add64_small by lia. lia. }
assert (N1 : sr_get (ss_regs ss_c_T) 19 = NX /\ sr_get (ss_regs ss_c_FT) 19 = NX /\ sr_get (ss_regs ss_c_FFTT) 19 = NX /\ sr_get (ss_regs ss_c_FFTFF) 19 = NX /\
sr_get (ss_regs ss_c_FFTFT) 19 = SAlu ALU_ADD RQ (SLit 0) /\ sr_get (ss_regs ss_c_FFF) 19 = SAlu ALU_ADD RQ (SLit 0)) by (vm_compute; repeat split; reflexivity).
destruct N1 as (N1 & N2 & N3 & N4 & N5 & N6).
apply (cwb_node E5 PS_MM _ _ _ _ _ _ gs_c_ W0 AG05); intros B0; pose proof (btK8 _ B0) as F0; cbv iota in F0.
- apply (cwb_leaf E5 PS_MM _ _ _ gs_c_T W1 AG05). intros cfg (ms & -> & HS & HM & HF). apply SR_ret.
apply (to_MM ss_c_T ms _ cnt1 mm_c_T HS (DN _ N1) (den_off0 _ _ _ E5_74) (plan_keep (or_introl F0)) HM HF).
- apply (cwb_node E5 PS_MM _ _ _ _ _ _ gs_c_F W1 AG05); intros B1; pose proof (btK9 _ B1) as F1; cbv iota in F1.
+ apply (cwb_leaf E5 PS_MM _ _ _ gs_c_FT W2 AG05). intros cfg (ms & -> & HS & HM & HF). apply SR_ret.
apply (to_MM ss_c_FT ms _ cnt1 mm_c_FT HS (DN _ N2) (den_off0 _ _ _ E5_74) (plan_keep (or_intror (or_introl F1))) HM HF).
+ apply (cwb_node E5 PS_MM _ _ _ _ _ _ gs_c_FF W2 AG05); intros B2; pose proof (btK10 _ B2) as F2; cbv iota in F2.
* apply (cwb_node E5 PS_MM _ _ _ _ _ _ gs_c_FFT W3 AG05); intros B3; pose proof (btK11 _ B3) as F3; cbv iota in F3.
-- apply (cwb_leaf E5 PS_MM _ _ _ gs_c_FFTT W4 AG05). intros cfg (ms & -> & HS & HM & HF). apply SR_ret.
apply (to_MM ss_c_FFTT ms _ cnt1 mm_c_FFTT HS (DN _ N3) (den_off0 _ _ _ E5_74) (plan_keep (or_intror (or_intror (conj F2 (or_introl F3))))) HM HF).
-- apply (cwb_node E5 PS_MM _ _ _ _ _ _ gs_c_FFTF W4 AG05); intros B4; pose proof (btK12 _ B4) as F4; cbv iota in F4.
++ apply (cwb_leaf E5 PS_MM _ _ _ gs_c_FFTFT W5 AG05). intros cfg (ms & -> & HS & HM & HF). apply SR_ret.
apply (to_MM ss_c_FFTFT ms _ 1 mm_c_FFTFT HS (DQ _ N5) (den_lit _ _) (plan_one F0 F1 (or_intror (conj F3 F4))) HM HF).
++ apply (cwb_leaf E5 PS_MM _ _ _ gs_c_FFTFF W5 AG05). intros cfg (ms & -> & HS & HM & HF). apply SR_ret.
apply (to_MM ss_c_FFTFF ms _ cnt1 mm_c_FFTFF HS (DN _ N4) (den_off0 _ _ _ E5_74) (plan_keep (or_intror (or_intror (conj F2 (or_intror F4))))) HM HF).
* apply (cwb_leaf E5 PS_MM _ _ _ gs_c_FFF W3 AG05). intros cfg (ms & -> & HS & HM & HF). apply SR_ret.
apply (to_MM ss_c_FFF ms _ 1 mm_c_FFF HS (DQ _ N6) (den_lit _ _) (plan_one F0 F1 (or_introl F2)) HM HF).
Qed.
End B2.
Definition MMpostE (c : config) : Prop :=
exists E6 ms, c = mkCfg ms md1 /\ st_ok src0segs E6 ss_MM ms /\ env_agree 73 E3 E6 /\
ew E6 81 = Z_to_bv 64 (snd plan) /\ ew E6 82 = Z_to_bv 64 (fst plan) /\ midrep B L1 s3 (ms_mem ms) md1 /\ FRcB (ms_mem ms).
Theorem reach_MM : forall ms, st_ok src0segs E3 ss_M1 ms -> midrep B L1 s3 (ms_mem ms) md1 -> FRcB (ms_mem ms) -> SR src0segs (mkCfg ms md1) MMpostE.
Proof.
intros ms HS HM HF. destruct E4_facts as (AG34 & _).
eapply SR_bind; [exact (reach_CN ms HS HM HF)|]. intros c (E5 & ms5 & -> & HS5 & AG5 & E74 & E75 & HM5 & HF5).
eapply SR_bind; [apply (tree_c E5 AG5 E74 E75); exists ms5; split; [reflexivity|]; split; [exact HS5|]; split; [exact HM5 | exact HF5] |].
intros c (E6 & ms6 & -> & HS6 & AG6 & E81 & E82 & HM6 & HF6). apply SR_ret. exists E6, ms6. split; [reflexivity|]. split; [exact HS6|]. split.
- eapply env_agree_trans; [exact AG34|]. eapply env_agree_trans; [eapply env_agree_le; [| exact AG5]; lia | eapply env_agree_le; [| exact AG6]; lia].
- split; [exact E81|]. split; [exact E82|]. split; [exact HM6 | exact HF6].
Qed.
End MB.
End e.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
