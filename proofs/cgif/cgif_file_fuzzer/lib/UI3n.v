(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_errno_low_lzw : errno_addr ubs0_msyms + 4 <= alloc_ceiling.
Proof.   pose proof (proj1 alloc_ceiling_val). enough (errno_addr ubs0_msyms + 4 <= CEIL_MIN) by lia. vm_compute. intros H'. discriminate H'. Qed.
Lemma ubs0_memset_spec : memset_spec ubs0_msyms ubs0_A_memset.
Proof. exact ubs0_memset. Qed.
Definition TPC_HEAD : Z := ubs0_A_LZW_GenerateStream + 0x138.
Definition TPC_INNER : Z := ubs0_A_LZW_GenerateStream + 0x208.
Definition TPC_EMITC : Z := ubs0_A_LZW_GenerateStream + 0x32c.
Definition TPC_TIMISS : Z := ubs0_A_LZW_GenerateStream + 0x370.
Definition TPC_MISS : Z := ubs0_A_LZW_GenerateStream + 0x3e0.
Definition TPC_RST : Z := ubs0_A_LZW_GenerateStream + 0x49c.
Definition TPC_DPINC : Z := ubs0_A_LZW_GenerateStream + 0x5dc.
Definition TPC_TAIL : Z := ubs0_A_LZW_GenerateStream + 0x5e8.
Definition TPC_EXIT : Z := ubs0_A_LZW_GenerateStream + 0x5f0.
Definition TPC_EALLOC : Z := ubs0_A_LZW_GenerateStream + 0x6c8.
Definition TPC_EIDX : Z := ubs0_A_LZW_GenerateStream + 0x6d0.
Definition TPC_CLEAN : Z := ubs0_A_LZW_GenerateStream + 0x6e8.
Record lzw_tcx := mkTCX {
y_sp : Z;
y_g : Z;
y_ti : Z; y_lm : Z; y_lc : Z; y_li : Z; y_tm : Z; y_ld : Z;
y_img : Z; y_nP : Z; y_idl : Z; y_icl : Z; y_pR : Z;
y_MR : Z; y_bi : Z; y_Li : Z; y_gp : Z }.
Definition y_cap (cx : lzw_tcx) : Z := cap (y_nP cx) (y_MR cx).
Definition y_tisz (cx : lzw_tcx) : Z := 2 * y_idl cx * y_idl cx.
Definition y_tmsz (cx : lzw_tcx) : Z := 4098 * y_idl cx.
Definition y_nimg (cx : lzw_tcx) : Z := 2 ^ 64 - 1 - y_img cx.
Definition tcx_ok (cx : lzw_tcx) : Prop :=
2 <= y_idl cx <= 256 /\ 1 <= y_nP cx <= 100000000 /\
y_MR cx * (4094 - y_idl cx) <= y_nP cx < (y_MR cx + 1) * (4094 - y_idl cx) /\ 0 <= y_MR cx /\
0 <= y_icl cx <= 12 /\
y_sp cx mod 16 = 0 /\ alloc_ceiling + 8224 <= y_sp cx /\ y_sp cx + 128 < 2 ^ 63 /\
alloc_ceiling <= y_pR cx /\ y_pR cx + 16 < 2 ^ 63 /\ y_sp cx + 112 <= y_pR cx /\ y_pR cx mod 8 = 0 /\
4096 <= y_bi cx /\ y_bi cx <= y_img cx /\ y_img cx + y_nP cx <= y_bi cx + y_Li cx /\ y_bi cx + y_Li cx <= alloc_ceiling /\
0 <= y_gp cx < 2 ^ 64.
Definition tcx_tabs (cx : lzw_tcx) : list (Z * Z) :=
[ (y_ti cx, y_tisz cx); (y_lm cx, 8192); (y_lc cx, 4096); (y_li cx, 8192); (y_tm cx, y_tmsz cx);
(y_ld cx, 2 * y_cap cx); (y_g cx, 72) ].
Definition tcx_blocks (cx : lzw_tcx) (bl : list (Z * Z)) : Prop :=
(forall b, In b (tcx_tabs cx) -> In b bl) /\ In (y_bi cx, y_Li cx) bl.
Fixpoint seps_from (b : Z * Z) (l : list (Z * Z)) : Prop :=
match l with
| [] => True
| c :: r => (fst b + snd b <= fst c \/ fst c + snd c <= fst b) /\ seps_from b r
end.
Fixpoint seps (l : list (Z * Z)) : Prop :=
match l with [] => True | b :: r => seps_from b r /\ seps r end.
Definition tcx_seps (cx : lzw_tcx) : Prop := seps (tcx_tabs cx ++ [(y_bi cx, y_Li cx)]).
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
Lemma tcx_sep : forall cx, tcx_seps cx -> forall i j, (i < j)%nat -> (j < 8)%nat ->
zz_disj (nth i (tcx_tabs cx ++ [(y_bi cx, y_Li cx)]) (0, 0)) (nth j (tcx_tabs cx ++ [(y_bi cx, y_Li cx)]) (0, 0)).
Proof. intros cx H i j Hij Hj. apply seps_nth; [exact H | exact Hij | cbn; lia]. Qed.
Fixpoint ranges (l : list (Z * Z)) : Prop :=
match l with [] => True | (a, n) :: r => (4096 <= a /\ a + n <= alloc_ceiling /\ a mod 16 = 0 /\ 0 < n) /\ ranges r end.
Definition tcx_ranges (cx : lzw_tcx) : Prop := ranges (tcx_tabs cx).
Definition tcx_wtok (STK sp0 : Z) (FP bl0 : list (Z * Z)) (cx : lzw_tcx) : Prop :=
forall b, In b (tcx_tabs cx) -> wtok' STK sp0 FP bl0 b.
Definition tcx_win (STK sp0 : Z) (cx : lzw_tcx) : Prop :=
sp0 - STK <= y_sp cx - 8224 /\ y_sp cx + 112 <= sp0.
Definition tlzw_regs_fix (regs : bvmap 5 word) (cx : lzw_tcx) : Prop :=
getr regs 2 = Z_to_bv 64 (y_sp cx) /\ getr regs 8 = Z_to_bv 64 (y_g cx) /\
getr regs 20 = Z_to_bv 64 (y_idl cx) /\ getr regs 21 = Z_to_bv 64 (2 * y_idl cx) /\
getr regs 18 = Z_to_bv 64 (y_pR cx) /\ getr regs 19 = Z_to_bv 64 (y_icl cx) /\ getr regs 9 = Z_to_bv 64 2 /\
getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) /\ getr regs 3 = Z_to_bv 64 (y_gp cx).
Definition TREGS_FIXL : list reg := [2; 8; 20; 21; 18; 19; 9; 4; 3]%bv.
Lemma tregs_fixl_not_memset : forall r : reg, In r TREGS_FIXL -> reg_in r MEMSET_CLOB = false.
Proof.
intros r Hr. cbv [TREGS_FIXL In] in Hr.
repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]). destruct Hr.
Qed.
Lemma tlzw_regs_fix_kept : forall regs regs' cx,
tlzw_regs_fix regs cx -> (forall r, In r TREGS_FIXL -> getr regs' r = getr regs r) -> tlzw_regs_fix regs' cx.
Proof.
intros regs regs' cx H HK. unfold tlzw_regs_fix in *. rewrite !HK by (cbv; tauto). exact H.
Qed.
Definition gen_at (mem : word -> option byte) (cx : lzw_tcx) (lp dp mp : Z) : Prop :=
val_mem ubs0segs mem (y_g cx) 8 (y_ti cx) /\ val_mem ubs0segs mem (y_g cx + 8) 8 (y_lm cx) /\
val_mem ubs0segs mem (y_g cx + 16) 8 (y_lc cx) /\ val_mem ubs0segs mem (y_g cx + 24) 8 (y_li cx) /\
val_mem ubs0segs mem (y_g cx + 32) 8 (y_tm cx) /\ val_mem ubs0segs mem (y_g cx + 40) 8 (y_ld cx) /\
val_mem ubs0segs mem (y_g cx + 48) 8 (y_img cx) /\ val_mem ubs0segs mem (y_g cx + 56) 4 (y_nP cx) /\
val_mem ubs0segs mem (y_g cx + 60) 4 lp /\ val_mem ubs0segs mem (y_g cx + 64) 2 dp /\ val_mem ubs0segs mem (y_g cx + 66) 2 mp.
Lemma gen_at_frame : forall mem mem' cx lp dp mp,
gen_at mem cx lp dp mp -> (forall a, y_g cx <= a < y_g cx + 72 -> mbyte ubs0segs mem' a = mbyte ubs0segs mem a) ->
gen_at mem' cx lp dp mp.
Proof.
intros mem mem' cx lp dp mp (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hfr.
repeat split; intros k Hk; (rewrite Hfr; [first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 | apply H9 | apply H10 | apply H11]; exact Hk | cbn in Hk; lia]).
Qed.
Definition ttables_at (mem : word -> option byte) (cx : lzw_tcx) (X : lzw_abs) : Prop :=
arr16 ubs0segs mem (y_ti cx) (la_TI X) /\ arr16 ubs0segs mem (y_lm cx) (la_LM X) /\
arr16 ubs0segs mem (y_li cx) (la_LI X) /\ arr16 ubs0segs mem (y_tm cx) (la_TM X).
Definition AC : Z := alloc_ceiling.
Definition NOTLO : Z := 2 ^ 64 - 1 - alloc_ceiling.
Definition tcx_extra (cx : lzw_tcx) (lp dp mp : Z) : list word :=
[ Z_to_bv 64 (y_ti cx); Z_to_bv 64 (y_lm cx); Z_to_bv 64 (y_lc cx); Z_to_bv 64 (y_li cx); Z_to_bv 64 (y_tm cx);
Z_to_bv 64 (y_ld cx); Z_to_bv 64 (y_img cx); Z_to_bv 64 (y_nP cx); Z_to_bv 64 (y_nimg cx);
Z_to_bv 64 lp; Z_to_bv 64 dp; Z_to_bv 64 mp ].
Definition tcommon_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 8224) (2^63) 4); (8%nat, mkAF 4096 CEIL_MAX 4); (20%nat, mkAF 2 256 0); (21%nat, mkAF 4 512 0);
(18%nat, mkAF CEIL_MIN (2^63) 3); (19%nat, mkAF 0 12 0);
(32%nat, mkAF 4096 CEIL_MAX 4); (33%nat, mkAF 4096 CEIL_MAX 4); (34%nat, mkAF 4096 CEIL_MAX 4); (35%nat, mkAF 4096 CEIL_MAX 4);
(36%nat, mkAF 4096 CEIL_MAX 4); (37%nat, mkAF 4096 CEIL_MAX 4); (38%nat, mkAF 4096 CEIL_MAX 0); (39%nat, mkAF 1 100000000 0);
(40%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2^64 - 4097) 0); (41%nat, mkAF 0 134217726 0); (42%nat, mkAF 4 4096 0); (43%nat, mkAF 1 2047 0) ].
Definition tcommon_alias : list (sv * sv) := [ (SAlu ALU_XOR (SOff 38%nat 0) (SLit (-1)), SOff 40%nat 0) ].
Definition gen_chunks : list YP09.chunk :=
[ mkChunk 0 (CVal 8 (SOff 32%nat 0)); mkChunk 8 (CVal 8 (SOff 33%nat 0)); mkChunk 16 (CVal 8 (SOff 34%nat 0));
mkChunk 24 (CVal 8 (SOff 35%nat 0)); mkChunk 32 (CVal 8 (SOff 36%nat 0)); mkChunk 40 (CVal 8 (SOff 37%nat 0));
mkChunk 48 (CVal 8 (SOff 38%nat 0)); mkChunk 56 (CVal 4 (SOff 39%nat 0)); mkChunk 60 (CVal 4 (SOff 41%nat 0));
mkChunk 64 (CVal 2 (SOff 42%nat 0)); mkChunk 66 (CVal 2 (SOff 43%nat 0)) ].
Definition gen_region (w : bool) : YP09.region := YP09.mkRegion (Some 8%nat) 0 72 (if w then 60 else 0) (if w then 68 else 0) gen_chunks.
Definition tlzw_ss (pc : Z) (sr : list sv) (w : bool) (rs : smem) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr (gen_region w :: rs) None (mkFacts (tcommon_facts ++ fs) cs (tcommon_alias ++ al)).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Section g.
Variables (regs : bvmap 5 word) (cx : lzw_tcx) (lp dp mp : Z) (more : list word).
Hypothesis HF : tlzw_regs_fix regs cx.
Let E := Ereg regs (tcx_extra cx lp dp mp ++ more).
Lemma TE_reg : forall (r : reg) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r.
Proof using. intros r n H. apply ew_Ereg_nat. exact H. Qed.
Lemma TE_sp : ew E 2 = Z_to_bv 64 (y_sp cx).   Proof using HF. rewrite (TE_reg 2%bv) by reflexivity. apply HF. Qed.
Lemma TE_g : ew E 8 = Z_to_bv 64 (y_g cx).     Proof using HF. rewrite (TE_reg 8%bv) by reflexivity. apply HF. Qed.
Lemma TE_idl : ew E 20 = Z_to_bv 64 (y_idl cx). Proof using HF. rewrite (TE_reg 20%bv) by reflexivity. apply HF. Qed.
Lemma TE_idl2 : ew E 21 = Z_to_bv 64 (2 * y_idl cx). Proof using HF. rewrite (TE_reg 21%bv) by reflexivity. apply HF. Qed.
Lemma TE_pR : ew E 18 = Z_to_bv 64 (y_pR cx).  Proof using HF. rewrite (TE_reg 18%bv) by reflexivity. apply HF. Qed.
Lemma TE_icl : ew E 19 = Z_to_bv 64 (y_icl cx). Proof using HF. rewrite (TE_reg 19%bv) by reflexivity. apply HF. Qed.
Lemma TE_x : forall j w, nth_error (tcx_extra cx lp dp mp) j = Some w -> ew E (32 + j) = w.
Proof using.
intros j w Hj. subst E. rewrite ew_Ereg_extra. rewrite app_nth1.
- apply nth_error_nth. exact Hj.
- apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
Qed.
Lemma TE_ti : ew E 32 = Z_to_bv 64 (y_ti cx).   Proof using. apply (TE_x 0). reflexivity. Qed.
Lemma TE_lm : ew E 33 = Z_to_bv 64 (y_lm cx).   Proof using. apply (TE_x 1). reflexivity. Qed.
Lemma TE_lc : ew E 34 = Z_to_bv 64 (y_lc cx).   Proof using. apply (TE_x 2). reflexivity. Qed.
Lemma TE_li : ew E 35 = Z_to_bv 64 (y_li cx).   Proof using. apply (TE_x 3). reflexivity. Qed.
Lemma TE_tm : ew E 36 = Z_to_bv 64 (y_tm cx).   Proof using. apply (TE_x 4). reflexivity. Qed.
Lemma TE_ld : ew E 37 = Z_to_bv 64 (y_ld cx).   Proof using. apply (TE_x 5). reflexivity. Qed.
Lemma TE_img : ew E 38 = Z_to_bv 64 (y_img cx). Proof using. apply (TE_x 6). reflexivity. Qed.
Lemma TE_nP : ew E 39 = Z_to_bv 64 (y_nP cx).   Proof using. apply (TE_x 7). reflexivity. Qed.
Lemma TE_nimg : ew E 40 = Z_to_bv 64 (y_nimg cx). Proof using. apply (TE_x 8). reflexivity. Qed.
Lemma TE_lp : ew E 41 = Z_to_bv 64 lp.          Proof using. apply (TE_x 9). reflexivity. Qed.
Lemma TE_dp : ew E 42 = Z_to_bv 64 dp.          Proof using. apply (TE_x 10). reflexivity. Qed.
Lemma TE_mp : ew E 43 = Z_to_bv 64 mp.          Proof using. apply (TE_x 11). reflexivity. Qed.
Lemma TE_more : forall j, ew E (44 + j) = nth j more (Z_to_bv 64 0).
Proof using.
intros j. subst E. replace (44 + j)%nat with (32 + (12 + j))%nat by lia. rewrite ew_Ereg_extra.
change (12 + j)%nat with (length (tcx_extra cx lp dp mp) + j)%nat. apply app_nth2_plus.
Qed.
End g.
Lemma ttisz_range : forall idl, 2 <= idl <= 256 -> 8 <= 2 * idl * idl <= 131072.
Proof using. intros idl H. nia. Qed.
Lemma alias_nimg : forall E n k img,
ew E n = Z_to_bv 64 img -> ew E k = Z_to_bv 64 (2 ^ 64 - 1 - img) -> 0 <= img < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = sv_denot E (SOff k 0).
Proof using.
intros E n k img Hn Hk Hr. apply U_inj. rewrite (U_not E n img Hn Hr). rewrite (U_atom E k _ Hk) by lia. reflexivity.
Qed.
Lemma tlzw_st_ok : forall cx regs lp dp mp more mem pc w rs fs cs al,
tcx_ok cx -> tcx_ranges cx -> tlzw_regs_fix regs cx -> gen_at mem cx lp dp mp ->
(w = true -> forall a, y_g cx + 60 <= a < y_g cx + 68 -> writable_at ubs0segs mem a) ->
0 <= lp <= 134217726 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
let E := Ereg regs (tcx_extra cx lp dp mp ++ more) in
regions_wf (gen_region w :: rs) = true ->
Forall (region_ok ubs0segs E mem) rs ->
all_disjoint E (gen_region w) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs0segs E (tlzw_ss pc sr_atoms w rs fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)).
Proof using.
intros cx regs lp dp mp more mem pc w rs fs cs al Hcx Hrg HF HG Hw Hlp Hdp Hmp E Hwf Hrs Had Hpd Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof Hrg as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
unfold y_tisz, y_tmsz, y_cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
pose proof (TE_sp regs cx lp dp mp more HF) as HE2. pose proof (TE_g regs cx lp dp mp more HF) as HE8.
pose proof (TE_idl regs cx lp dp mp more HF) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HF) as HE21.
pose proof (TE_pR regs cx lp dp mp more HF) as HE18. pose proof (TE_icl regs cx lp dp mp more HF) as HE19.
pose proof (ttisz_range (y_idl cx) Hidl) as Htisz.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_nimg regs cx lp dp mp more) as HE40. pose proof (TE_lp regs cx lp dp mp more) as HE41.
pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
unfold y_nimg in HE40.
apply entry_st_ok_full.
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|exact Hrs].
unfold region_ok, gen_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct w; [apply Hw; [reflexivity | lia] | lia]. }
unfold gen_chunks.
Ltac ck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia | first [exact S | rewrite Z.add_0_r; exact S] ].
constructor; [ck V0 HE32|]. constructor; [ck V8 HE33|]. constructor; [ck V16 HE34|]. constructor; [ck V24 HE35|].
constructor; [ck V32 HE36|]. constructor; [ck V40 HE37|]. constructor; [ck V48 HE38|]. constructor; [ck V56 HE39|].
constructor; [ck V60 HE41|]. constructor; [ck V64 HE42|]. constructor; [ck V66 HE43|]. constructor.
- split; [exact Had | exact Hpd].
- split; [|split; [exact Hcs|]].
+ unfold tlzw_ss. cbn [f_atoms]. apply atoms_ok_app; [|exact Hfs].
cbn [atoms_ok tcommon_facts]. unfold afact_ok, AC, NOTLO. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE20, HE21, HE18, HE19, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE40, HE41, HE42, HE43, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [assumption | lia].
+ unfold tlzw_ss. cbn [f_alias]. split; [|exact Hal].
apply (alias_nimg _ 38 40 (y_img cx) HE38 HE40). lia.
Qed.
End S.
Lemma tmbyte_eq_of1 : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte ubs0segs m' a = mbyte ubs0segs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
Lemma tframe_of_ro' : forall E rs (m m' : word -> option byte),
frame_of E rs m m' -> all_ro rs = true -> forall x, m' x = m x.
Proof. intros E rs m m' HF Hro x. exact (frame_of_ro E rs m m' Hro HF x). Qed.
Lemma tframe_mbyte : forall E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r)) ->
mbyte ubs0segs m' a = mbyte ubs0segs m a.
Proof.
intros E rs m m' a HF Ha Hout. apply tmbyte_eq_of1. apply HF.
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Lemma st_ok_set_reg' : forall segs E ss ms (r : reg) e,
st_ok segs E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms r e HS Hr0 He. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He. apply (st_ok_reg segs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
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
Ltac mem_unchanged_ro :=
intros x;
repeat match goal with
| HF : frame_of _ _ _ _ |- _ => rewrite (tframe_of_ro' _ _ _ _ HF ltac:(vm_compute; reflexivity) x); clear HF
end;
reflexivity.
Ltac treg_val HS r :=
let H := fresh "Hrv" in
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
pose proof (st_ok_reg segs E ss ms r HS) as H;
eval_sr_get_in H;
cbn [sv_denot] in H;
repeat (rewrite ew_havoc_old in H; [|cbv; lia]);
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H
end;
repeat match goal with HE : ew ?E ?n = Z_to_bv 64 _ |- _ => rewrite HE in H end;
rewrite ?unsigned_lit_small in H by lia;
first [ exact H | rewrite H; f_equal; lia ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
