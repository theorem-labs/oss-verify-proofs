(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n
YI00 YI02 YI01 YI07 YI03.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ubs2_errno_low_lzw : errno_addr ubs2_msyms + 4 <= alloc_ceiling.
Proof.   pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs2_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Lemma ubs2_memset_spec : memset_spec ubs2_msyms ubs2_A_memset.
Proof. exact ubs2_memset. Qed.
Definition LZW_STK : Z := 208 + 8192.
Definition PC_HEAD : Z := ubs2_A_LZW_GenerateStream + 0x174.
Definition PC_INNER : Z := ubs2_A_LZW_GenerateStream + 0x1e4.
Definition PC_EMITC : Z := ubs2_A_LZW_GenerateStream + 0x254.
Definition PC_TIMISS : Z := ubs2_A_LZW_GenerateStream + 0x270.
Definition PC_RST1 : Z := ubs2_A_LZW_GenerateStream + 0x298.
Definition PC_LMZERO : Z := ubs2_A_LZW_GenerateStream + 0x30c.
Definition PC_SW2 : Z := ubs2_A_LZW_GenerateStream + 0x36c.
Definition PC_TMMISS : Z := ubs2_A_LZW_GenerateStream + 0x3a0.
Definition PC_RST2 : Z := ubs2_A_LZW_GenerateStream + 0x3dc.
Definition PC_TAIL : Z := ubs2_A_LZW_GenerateStream + 0x460.
Definition PC_CLEAN : Z := ubs2_A_LZW_GenerateStream + 0x494.
Definition PC_EIDX : Z := ubs2_A_LZW_GenerateStream + 0x504.
Definition PC_EXIT : Z := ubs2_A_LZW_GenerateStream + 0x510.
Record lzw_cx := mkCX {
x_sp : Z;
x_ti : Z; x_lm : Z; x_lc : Z; x_li : Z; x_tm : Z; x_ld : Z;
x_img : Z; x_nP : Z; x_idl : Z; x_icl : Z; x_pR : Z;
x_MR : Z;
x_bi : Z; x_Li : Z;
x_gp : Z }.
Definition x_cap (cx : lzw_cx) : Z := cap (x_nP cx) (x_MR cx).
Definition x_tisz (cx : lzw_cx) : Z := 2 * x_idl cx * x_idl cx.
Definition x_tmsz (cx : lzw_cx) : Z := 4098 * x_idl cx.
Definition cx_ok (cx : lzw_cx) : Prop :=
2 <= x_idl cx <= 256 /\ 1 <= x_nP cx <= 100000000 /\
x_MR cx * (4094 - x_idl cx) <= x_nP cx < (x_MR cx + 1) * (4094 - x_idl cx) /\ 0 <= x_MR cx /\
0 <= x_icl cx <= 12 /\
x_sp cx mod 16 = 0 /\ alloc_ceiling + 8192 <= x_sp cx /\ x_sp cx + 208 < 2 ^ 63 /\
alloc_ceiling <= x_pR cx /\ x_pR cx + 16 < 2 ^ 63 /\ (x_pR cx + 16 <= x_sp cx \/ x_sp cx + 208 <= x_pR cx) /\
4096 <= x_bi cx /\ x_bi cx <= x_img cx /\ x_img cx + x_nP cx <= x_bi cx + x_Li cx /\ x_bi cx + x_Li cx <= alloc_ceiling.
Definition cx_tabs (cx : lzw_cx) : list (Z * Z) :=
[ (x_ti cx, x_tisz cx); (x_lm cx, 8192); (x_lc cx, 4096); (x_li cx, 8192); (x_tm cx, x_tmsz cx);
(x_ld cx, 2 * x_cap cx) ].
Definition cx_blocks (cx : lzw_cx) (bl : list (Z * Z)) : Prop :=
(forall b, In b (cx_tabs cx) -> In b bl) /\ In (x_bi cx, x_Li cx) bl.
Fixpoint seps_from (b : Z * Z) (l : list (Z * Z)) : Prop :=
match l with
| [] => True
| c :: r => (fst b + snd b <= fst c \/ fst c + snd c <= fst b) /\ seps_from b r
end.
Fixpoint seps (l : list (Z * Z)) : Prop :=
match l with [] => True | b :: r => seps_from b r /\ seps r end.
Definition cx_seps (cx : lzw_cx) : Prop := seps (cx_tabs cx ++ [(x_bi cx, x_Li cx)]).
Definition zz_disj (b c : Z * Z) : Prop := fst b + snd b <= fst c \/ fst c + snd c <= fst b.
Lemma seps_from_nth : forall b l j d, seps_from b l -> (j < length l)%nat -> zz_disj b (nth j l d).
Proof.
intros b l. induction l as [|c r IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; cbn [nth]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.
Lemma seps_nth : forall l i j d, seps l -> (i < j)%nat -> (j < length l)%nat -> zz_disj (nth i l d) (nth j l d).
Proof.
induction l as [|b r IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply seps_from_nth; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Fixpoint ranges (l : list (Z * Z)) : Prop :=
match l with [] => True | (a, n) :: r => (4096 <= a /\ a + n <= alloc_ceiling /\ a mod 16 = 0 /\ 0 < n) /\ ranges r end.
Definition cx_ranges (cx : lzw_cx) : Prop := ranges (cx_tabs cx).
Definition wtok (STK sp0 : Z) (FP bl0 : list (Z * Z)) (b : Z * Z) : Prop :=
forall blc i, In b blc -> 0 <= i < snd b -> wr_byte STK sp0 FP bl0 blc (fst b + i).
Definition cx_wtok (STK sp0 : Z) (FP bl0 : list (Z * Z)) (cx : lzw_cx) : Prop :=
forall b, In b (cx_tabs cx) -> wtok STK sp0 FP bl0 b.
Definition cx_win (STK sp0 : Z) (cx : lzw_cx) : Prop :=
sp0 - STK <= x_sp cx - 8192 /\ x_sp cx + 208 <= sp0 /\ True /\ True.
Definition lzw_regs_fix (regs : bvmap 5 word) (cx : lzw_cx) : Prop :=
getr regs 2 = Z_to_bv 64 (x_sp cx) /\ getr regs 8 = Z_to_bv 64 (x_ti cx) /\ getr regs 27 = Z_to_bv 64 (x_lm cx) /\
getr regs 9 = Z_to_bv 64 (x_lc cx) /\ getr regs 18 = Z_to_bv 64 (x_li cx) /\ getr regs 21 = Z_to_bv 64 (x_tm cx) /\
getr regs 22 = Z_to_bv 64 (x_ld cx) /\ getr regs 25 = Z_to_bv 64 (x_idl cx) /\ getr regs 23 = Z_to_bv 64 (2 * x_idl cx) /\
getr regs 4 = Z_to_bv 64 (ms_tp ubs2_msyms) /\ getr regs 3 = Z_to_bv 64 (x_gp cx).
Definition REGS_FIXL : list reg := [2; 8; 27; 9; 18; 21; 22; 25; 23; 4; 3]%bv.


Definition stack_at (mem : word -> option byte) (cx : lzw_cx) : Prop :=
val_mem ubs2segs mem (x_sp cx + 48) 8 (x_idl cx + 2) /\ val_mem ubs2segs mem (x_sp cx + 56) 8 (x_icl cx) /\
val_mem ubs2segs mem (x_sp cx + 64) 8 (x_pR cx) /\ val_mem ubs2segs mem (x_sp cx + 72) 8 (x_img cx + 1) /\
val_mem ubs2segs mem (x_sp cx + 80) 8 (x_tisz cx) /\ val_mem ubs2segs mem (x_sp cx + 88) 8 (x_img cx) /\
val_mem ubs2segs mem (x_sp cx + 96) 8 (x_nP cx).

Definition tables_at (mem : word -> option byte) (cx : lzw_cx) (X : lzw_abs) : Prop :=
arr16 ubs2segs mem (x_ti cx) (la_TI X) /\ arr16 ubs2segs mem (x_lm cx) (la_LM X) /\
arr16 ubs2segs mem (x_li cx) (la_LI X) /\ arr16 ubs2segs mem (x_tm cx) (la_TM X).
Definition AC : Z := alloc_ceiling.
Definition cx_extra (cx : lzw_cx) : list word :=
[ Z_to_bv 64 (x_img cx); Z_to_bv 64 (x_nP cx); Z_to_bv 64 (x_icl cx); Z_to_bv 64 (x_pR cx); Z_to_bv 64 (x_tisz cx) ].
Definition common_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 8192) (2^63) 4); (8%nat, mkAF 4096 CEIL_MAX 4); (27%nat, mkAF 4096 CEIL_MAX 4); (9%nat, mkAF 4096 CEIL_MAX 4);
(18%nat, mkAF 4096 CEIL_MAX 4); (21%nat, mkAF 4096 CEIL_MAX 4); (22%nat, mkAF 4096 CEIL_MAX 4); (25%nat, mkAF 2 256 0); (23%nat, mkAF 4 512 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 1 100000000 0); (34%nat, mkAF 0 12 0); (35%nat, mkAF CEIL_MIN (2^63) 0); (36%nat, mkAF 8 131072 0) ].
Definition stack_chunks : list YQ0b.chunk :=
[ mkChunk 48 (CVal 8 (SOff 25%nat 2)); mkChunk 56 (CVal 8 (SOff 34%nat 0)); mkChunk 64 (CVal 8 (SOff 35%nat 0));
mkChunk 72 (CVal 8 (SOff 32%nat 1)); mkChunk 80 (CVal 8 (SOff 36%nat 0)); mkChunk 88 (CVal 8 (SOff 32%nat 0));
mkChunk 96 (CVal 8 (SOff 33%nat 0)) ].
Definition stack_region (w : bool) (extra : list YQ0b.chunk) : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 104 0 (if w then 48 else 0) (extra ++ stack_chunks).
Definition lzw_ss (pc : Z) (sr : list sv) (w : bool) (extra : list YQ0b.chunk) (rs : smem) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr (stack_region w extra :: rs) None (mkFacts (common_facts ++ fs) cs al).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Section g.
Variables (regs : bvmap 5 word) (cx : lzw_cx) (more : list word).
Hypothesis HF : lzw_regs_fix regs cx.
Let E := Ereg regs (cx_extra cx ++ more).
Lemma E_reg : forall (r : reg) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r.
Proof. intros r n H. apply ew_Ereg_nat. exact H. Qed.
Lemma E_sp : ew E 2 = Z_to_bv 64 (x_sp cx).   Proof. rewrite (E_reg 2%bv) by reflexivity. apply HF. Qed.
Lemma E_ti : ew E 8 = Z_to_bv 64 (x_ti cx).   Proof. rewrite (E_reg 8%bv) by reflexivity. apply HF. Qed.
Lemma E_lm : ew E 27 = Z_to_bv 64 (x_lm cx).  Proof. rewrite (E_reg 27%bv) by reflexivity. apply HF. Qed.
Lemma E_lc : ew E 9 = Z_to_bv 64 (x_lc cx).   Proof. rewrite (E_reg 9%bv) by reflexivity. apply HF. Qed.
Lemma E_li : ew E 18 = Z_to_bv 64 (x_li cx).  Proof. rewrite (E_reg 18%bv) by reflexivity. apply HF. Qed.
Lemma E_tm : ew E 21 = Z_to_bv 64 (x_tm cx).  Proof. rewrite (E_reg 21%bv) by reflexivity. apply HF. Qed.
Lemma E_ld : ew E 22 = Z_to_bv 64 (x_ld cx).  Proof. rewrite (E_reg 22%bv) by reflexivity. apply HF. Qed.
Lemma E_idl : ew E 25 = Z_to_bv 64 (x_idl cx). Proof. rewrite (E_reg 25%bv) by reflexivity. apply HF. Qed.
Lemma E_idl2 : ew E 23 = Z_to_bv 64 (2 * x_idl cx). Proof. rewrite (E_reg 23%bv) by reflexivity. apply HF. Qed.
Lemma E_img : ew E 32 = Z_to_bv 64 (x_img cx). Proof. subst E. rewrite (ew_Ereg_extra regs _ 0). reflexivity. Qed.
Lemma E_nP : ew E 33 = Z_to_bv 64 (x_nP cx).   Proof. subst E. rewrite (ew_Ereg_extra regs _ 1). reflexivity. Qed.
Lemma E_icl : ew E 34 = Z_to_bv 64 (x_icl cx). Proof. subst E. rewrite (ew_Ereg_extra regs _ 2). reflexivity. Qed.
Lemma E_pR : ew E 35 = Z_to_bv 64 (x_pR cx).   Proof. subst E. rewrite (ew_Ereg_extra regs _ 3). reflexivity. Qed.
Lemma E_tisz : ew E 36 = Z_to_bv 64 (x_tisz cx). Proof. subst E. rewrite (ew_Ereg_extra regs _ 4). reflexivity. Qed.
Lemma E_more : forall j, ew E (37 + j) = nth j more (Z_to_bv 64 0).
Proof. intros j. subst E. replace (37 + j)%nat with (32 + (5 + j))%nat by lia. rewrite ew_Ereg_extra. reflexivity. Qed.
End g.
Lemma tisz_range : forall idl, 2 <= idl <= 256 -> 8 <= 2 * idl * idl <= 131072.
Proof. intros idl H. nia. Qed.
Lemma lzw_st_ok : forall cx regs more mem pc w extra rs fs cs al xvals,
cx_ok cx -> cx_ranges cx -> lzw_regs_fix regs cx -> stack_at mem cx ->
(forall a, x_sp cx <= a < x_sp cx + 48 -> writable_at ubs2segs mem a) ->
let E := Ereg regs (cx_extra cx ++ more) in
Forall2 (fun c ov => c = mkChunk (fst ov) (CVal 8 (fst (snd ov))) /\ 0 <= fst ov /\ fst ov + 8 <= 48 /\
sv_denot E (fst (snd ov)) = Z_to_bv 64 (snd (snd ov)) /\ 0 <= snd (snd ov) < 2 ^ 64 /\
val_mem ubs2segs mem (x_sp cx + fst ov) 8 (snd (snd ov))) extra xvals ->
regions_wf (stack_region w extra :: rs) = true ->
Forall (region_ok ubs2segs E mem) rs ->
all_disjoint E (stack_region w extra) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs2segs E (lzw_ss pc sr_atoms w extra rs fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)).
Proof.
intros cx regs more mem pc w extra rs fs cs al xvals Hcx Hrg HF Hst Hw E Hextra Hwf Hrs Had Hpd Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct cx as [sp ti lm lc li tm ld img nP idl icl pR MRv bi Li gp].
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & Hbi1 & Hbi2 & Hbi3 & Hbi4).
pose proof Hrg as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & _).
destruct Hst as (S48 & S56 & S64 & S72 & S80 & S88 & S96).
unfold x_tisz, x_tmsz, x_cap in *.
cbn [x_sp x_ti x_lm x_lc x_li x_tm x_ld x_img x_nP x_idl x_icl x_pR x_MR fst snd] in *.
pose proof (tisz_range idl Hidl) as Htisz.
pose proof (E_sp regs _ more HF) as HE2. pose proof (E_ti regs _ more HF) as HE8. pose proof (E_lm regs _ more HF) as HE27.
pose proof (E_lc regs _ more HF) as HE9. pose proof (E_li regs _ more HF) as HE18. pose proof (E_tm regs _ more HF) as HE21.
pose proof (E_ld regs _ more HF) as HE22. pose proof (E_idl regs _ more HF) as HE25. pose proof (E_idl2 regs _ more HF) as HE23.
pose proof (E_img regs {| x_sp := sp; x_ti := ti; x_lm := lm; x_lc := lc; x_li := li; x_tm := tm; x_ld := ld; x_img := img; x_nP := nP; x_idl := idl; x_icl := icl; x_pR := pR; x_MR := MRv; x_bi := bi; x_Li := Li; x_gp := gp |} more) as HE32.
pose proof (E_nP regs {| x_sp := sp; x_ti := ti; x_lm := lm; x_lc := lc; x_li := li; x_tm := tm; x_ld := ld; x_img := img; x_nP := nP; x_idl := idl; x_icl := icl; x_pR := pR; x_MR := MRv; x_bi := bi; x_Li := Li; x_gp := gp |} more) as HE33.
pose proof (E_icl regs {| x_sp := sp; x_ti := ti; x_lm := lm; x_lc := lc; x_li := li; x_tm := tm; x_ld := ld; x_img := img; x_nP := nP; x_idl := idl; x_icl := icl; x_pR := pR; x_MR := MRv; x_bi := bi; x_Li := Li; x_gp := gp |} more) as HE34.
pose proof (E_pR regs {| x_sp := sp; x_ti := ti; x_lm := lm; x_lc := lc; x_li := li; x_tm := tm; x_ld := ld; x_img := img; x_nP := nP; x_idl := idl; x_icl := icl; x_pR := pR; x_MR := MRv; x_bi := bi; x_Li := Li; x_gp := gp |} more) as HE35.
pose proof (E_tisz regs {| x_sp := sp; x_ti := ti; x_lm := lm; x_lc := lc; x_li := li; x_tm := tm; x_ld := ld; x_img := img; x_nP := nP; x_idl := idl; x_icl := icl; x_pR := pR; x_MR := MRv; x_bi := bi; x_Li := Li; x_gp := gp |} more) as HE36.
unfold x_tisz in HE36.
cbn [x_sp x_ti x_lm x_lc x_li x_tm x_ld x_img x_nP x_idl x_icl x_pR] in HE2, HE8, HE27, HE9, HE18, HE21, HE22, HE25, HE23, HE32, HE33, HE34, HE35, HE36.
apply entry_st_ok_full.
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|exact Hrs].
unfold region_ok, stack_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; destruct w; lia|].
apply Forall_app. split.
+ clear Hrs Had Hpd Hfs Hcs Hal Hwf. induction Hextra as [|c ov cs' ovs [Hc (Ho1 & Ho2 & Hden & Hv & Hval)] HFA IH]; [constructor|].
constructor; [|exact IH]. rewrite Hc. eapply chunk_ok_val; [exact Hden | | cbn; lia | exact Hval].
change (8 * Z.of_N 8) with 64. lia.
+ unfold stack_chunks.
Ltac ck S HE := eapply chunk_ok_val; [ | | | exact S];
[ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; f_equal; lia
| change (8 * Z.of_N 8) with 64; lia
| cbn; lia ].
constructor; [ck S48 HE25|]. constructor; [ck S56 HE34|]. constructor; [ck S64 HE35|]. constructor; [ck S72 HE32|].
constructor; [ck S80 HE36|]. constructor; [ck S88 HE32|]. constructor; [ck S96 HE33|]. constructor.
- split; [exact Had | exact Hpd].
- split; [|split; [exact Hcs | exact Hal]].
unfold lzw_ss. cbn [f_atoms]. apply atoms_ok_app; [|exact Hfs].
cbn [atoms_ok common_facts]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE27, HE9, HE18, HE21, HE22, HE25, HE23, HE32, HE33, HE34, HE35, HE36, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [assumption | lia].
Qed.
End S.
Definition tail_post (cx : lzw_cx) (X : lzw_abs) (regs' : bvmap 5 word) (mem' : word -> option byte) (X' : lzw_abs) : Prop :=
lzw_regs_fix regs' cx /\ stack_at mem' cx /\ tables_at mem' cx X' /\ lzw_inv (x_idl cx) (x_nP cx) X' /\
getr regs' 13 = Z_to_bv 64 (la_lp X') /\ getr regs' 28 = Z_to_bv 64 (la_dp X') /\ getr regs' 7 = Z_to_bv 64 (la_mp X') /\
getr regs' 26 = Z_to_bv 64 (la_s X') /\ getr regs' 5 = Z_to_bv 64 (x_nP cx - 1) /\ getr regs' 6 = Z_to_bv 64 (x_nP cx - 1) /\
la_s X < la_s X' <= x_nP cx.




Definition rst_pre (cx : lzw_cx) (X : lzw_abs) (s' : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
lzw_regs_fix regs cx /\ stack_at mem cx /\ tables_at mem cx X /\ lzw_inv (x_idl cx) (x_nP cx) X /\ la_dp X = 4096 /\
getr regs 10 = Z_to_bv 64 (la_lp X) /\ getr regs 13 = Z_to_bv 64 (la_lp X + 1) /\ getr regs 26 = Z_to_bv 64 s' /\
getr regs 5 = Z_to_bv 64 (x_nP cx - 1) /\ getr regs 6 = Z_to_bv 64 (x_nP cx - 1) /\
la_s X < s' <= x_nP cx /\ s' - 1 < x_nP cx.
Lemma st_ok_region_nth : forall E ss ms i r,
st_ok ubs2segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok ubs2segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok ubs2segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.

Definition sw2_pre (cx : lzw_cx) (X : lzw_abs) (s1 q c : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
lzw_regs_fix regs cx /\ stack_at mem cx /\
tables_at mem cx (mkLA TI LM LI (zero_range TM (Z.to_nat ((mp - 1) * x_idl cx)) (Z.to_nat (x_idl cx))) s lp dp mp Cn R) /\
lzw_inv (x_idl cx) (x_nP cx) X /\ dp < 4096 /\
0 <= q < 4096 /\ nth (Z.to_nat q) LI 0 <> 0 /\ nth (Z.to_nat q) LM 0 = 0 /\ 0 <= c < x_idl cx /\ s < s1 <= x_nP cx - 1 /\
getr regs 19 = Z_to_bv 64 (x_lm cx + 2 * q) /\ getr regs 20 = Z_to_bv 64 c /\ getr regs 24 = Z_to_bv 64 (x_nP cx - 1) /\
getr regs 26 = Z_to_bv 64 s1 /\
val_mem ubs2segs mem (x_sp cx + 8) 8 ((mp - 1) * x_idl cx) /\ val_mem ubs2segs mem (x_sp cx + 16) 8 (lp + 1) /\
val_mem ubs2segs mem (x_sp cx + 24) 8 dp /\ val_mem ubs2segs mem (x_sp cx + 32) 8 mp /\ val_mem ubs2segs mem (x_sp cx + 40) 8 (x_nP cx - 1).
Lemma val_mem_of_chunk8 : forall E mem r p a off e v,
region_ok ubs2segs E mem r -> r_base r = Some p -> In (mkChunk off (CVal 8 e)) (r_chunks r) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem ubs2segs mem (a + off) 8 v.
Proof.
intros E mem r p a off e v HR Hb Hin Hp He Hv.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
change 8%nat with (N.to_nat 8).
eapply val_of_chunk_ok; [exact Hc | exact He | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia].
Qed.
Definition above_eq (cx : lzw_cx) (m m' : word -> option byte) : Prop :=
forall a, x_sp cx + 48 <= a < 2 ^ 64 -> mbyte ubs2segs m' a = mbyte ubs2segs m a.



End f.
Ltac Ucond Hc :=
first [ rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_geu_U in Hc ];
rewrite ?U_SOff, ?U_SLit in Hc;
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- _ => rewrite H in Hc end;
rewrite ?unsigned_lit_small in Hc by lia;
rewrite ?zcanon_id in Hc by (unfold M64; lia);
first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc
| apply (proj1 (Bool.negb_true_iff _)) in Hc; first [apply Z.ltb_ge in Hc | apply Z.eqb_neq in Hc]
| apply (proj1 (Bool.negb_false_iff _)) in Hc; first [apply Z.ltb_lt in Hc | apply Z.eqb_eq in Hc] ].
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma frame_of_ro' : forall E rs (m m' : word -> option byte),
frame_of E rs m m' -> all_ro rs = true -> forall x, m' x = m x.
Proof. intros E rs m m' HF Hro x. exact (frame_of_ro E rs m m' Hro HF x). Qed.
End h.
Ltac mem_unchanged_ro :=
intros x;
repeat match goal with
| HF : frame_of _ _ _ _ |- _ => rewrite (frame_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) x); clear HF
end;
reflexivity.
Ltac reg_val HS r :=
let H := fresh "Hrv" in
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
pose proof (st_ok_reg segs E ss ms r HS) as H;
eval_sr_get_in H;
try (erewrite denot_addoff_mulm1 in H; [ | eassumption | eassumption | lia | lia | lia ]);
cbn [sv_denot] in H;
repeat (rewrite ew_havoc_old in H; [|cbv; lia]);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H
end;
repeat match goal with HE : ew ?E ?n = Z_to_bv 64 _ |- _ => rewrite HE in H end;
rewrite ?unsigned_lit_small in H by lia;
first [ exact H | rewrite H; f_equal; lia ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
