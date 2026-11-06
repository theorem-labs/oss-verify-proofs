(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0z YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF0w YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF19 YF0o YF0s YF2e YF2b YF2c YF2g YF2v YF2o YF33 YF0p YF0l YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma val_mem_aview {imgk : img} : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. img_refl. Qed.
Lemma same_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma same_io_with_vm_backing : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; img_refl. Qed.
Lemma AR_model_same {imgk : img} : forall B ly S W mem md md',
AR tfxsegs B ly S W mem md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
AR tfxsegs B ly S W mem md'.
Proof.
intros B ly S W mem md md' (M & L & Bu & MW & HS) Hv Hl He. split; [img_try (img_exact M)|]. split; [img_try (img_exact (ALedger_same tfxsegs ly S md md' L Hv Hl He)) |].
split; [img_try (img_exact Bu)|]. split; [img_try (img_exact (amwf_same md md' Hv Hl MW)) | img_try (img_exact HS)].
Qed.
Lemma val_mem_aview_xfer {imgk : img} : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfxsegs H' m' (a + Z.of_nat k) = aview tfxsegs H m (a + Z.of_nat k)) ->
val_mem tfxsegs (mrestrict H m) a n v -> val_mem tfxsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HA Hv k Hk. pose proof (Hv k Hk) as E. pose proof (HA k Hk) as A. unfold aview in A. rewrite E in A. cbn [option_map] in A.
destruct (mbyte tfxsegs (mrestrict H' m') (a + Z.of_nat k)) as [b'|]; cbn [option_map] in A; [|img_try (discriminate)].
injection A as A. f_equal. img_apply bv_eq. rewrite A. img_refl.
Qed.
Lemma val_mem_mbyte_in {imgk : img} : forall (m : word -> option byte) a (n : nat) v a', val_mem tfxsegs m a n v -> a <= a' < a + Z.of_nat n ->
exists b, mbyte tfxsegs m a' = Some b.
Proof.
intros m a n v a' Hv Ha. exists (Z_to_bv 8 (YP0g.le_byte v n (Z.to_nat (a' - a)))).
replace a' with (a + Z.of_nat (Z.to_nat (a' - a))) at 1 by img_lia. img_apply Hv. img_lia.
Qed.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Hypothesis DR : tfx_dorecycle_spec B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : drain_pre B ly X W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Local Notation GLv := (YF2e.GLv ly gq).
Local Notation TFv := (YF2e.TFv ly tq).
Local Notation TLv := (YF2e.TLv ly tq).
Local Notation M := (YF0p.M B ly X W regs mem md PRE).
Local Notation HSP := (YF0p.HSP B ly X W regs mem md PRE).
Local Notation HI := (YF0p.HI B ly X W regs mem md PRE).
Local Notation IMG := (YF0p.IMG B ly X W regs mem md PRE).
Local Notation batch_facts := (YF0p.batch_facts B ly X W regs mem md PRE).
Local Notation g_facts := (YF0p.g_facts B ly X W regs mem md PRE).
Local Notation t_facts := (YF0p.t_facts B ly X W regs mem md PRE).
Local Notation L := (YF0l.L X).
Local Notation addr := (YF0l.addr ly).
Local Notation firstaddr := (YF0l.firstaddr ly).
Local Notation lastaddr := (YF0l.lastaddr ly).
Local Notation zlen := YF0l.zlen.
Local Notation sp1 := (YF0l.sp1 regs).
Local Notation DW := (YF0l.DW ly X regs).
Local Notation LST := (YF0l.LST ly X W regs mem md).
Local Notation ATDR := (YF0l.ATDR ly X W regs mem md).
Let WF : Wf (as_universe B) X := am_wf B ly X _ M.
Let LO : layout_ok ly := am_layout B ly X _ M.
Lemma HTSD : ly_tsd ly = TFX_TSD. Proof. rewrite (am_tsd B ly X _ M). img_apply (ts_tsd _ TB). Qed.
Lemma L0_LST : forall W' c', YF2e.at_L0 W ly regs mem md gq tq W' c' -> LST [] L W' c'.
Proof.
intros W' c' (-> & regs' & mem' & mat & -> & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R5 & R1 & RS & MQ & PRES & CELLS).
cbv zeta in CELLS. destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CGL & Cs80 & Cs72 & Cs64 & Cs56 & Cs48 & Cs40 & Cs32 & Cs24 & Cs16 & Cs8).
pose proof HSP as [S1 S2]. fold sp0 in S1, S2. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & EG). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & ET).
split; [img_refl|]. exists regs', mem', mat. split; [img_refl|].
split; [img_try (rewrite R2; unfold YF0l.sp1, LFRAME; img_refl)|]. split; [img_try (img_exact R10)|]. split; [img_try (img_exact R11)|]. split; [img_try (img_exact R12)|]. split; [img_try (img_exact R13)|].
split; [img_try (rewrite R14; img_refl)|]. split; [img_try (rewrite R15; img_refl)|].
split; [img_try (rewrite R16; unfold YF2e.LSZv, YF2e.GSZv, YF2e.TSZv, YF0l.zlen, YF0l.L; rewrite length_app, Nat2Z.inj_add; img_refl)|].
split; [img_try (rewrite R5; unfold YF2e.LFv, YF2e.GFv, YF2e.TFv, YF0l.firstaddr, YF0l.L, YF0l.addr; destruct G; [destruct Tq; img_refl | img_refl])|].
split; [img_try (img_exact R1)|]. split; [img_try (img_exact RS)|].
split. { intros x Hx. img_apply MQ. intros Hw. img_apply Hx. unfold YF0l.DW. unfold YF2e.WIN, YF2e.WINA in Hw. fold sp0 in Hw. unfold LFRAME. fold sp0.
destruct Hw as [Hw|[Hw|Hw]]; [img_try (left; img_exact Hw) | img_try (right; left; img_exact Hw) | img_try (right; right; left; img_exact Hw)]. }
split. { intros a Ha. destruct (YF0p.WIN_dec ly X regs a) as [Hw|Hw].
- img_apply PRES; [img_try (img_exact Hw) | img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; img_lia)].
- pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
img_apply (apresent_same H0 mem); [img_try (img_apply MQ; rewrite unsigned_lit_small by (unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; img_lia); img_exact Hw) | img_try (img_apply HPRES; img_exact Ha)]. }
cbv zeta.
split; [img_try (img_exact C152)|].
split; [img_try (unfold YF2e.LSZv, YF2e.GSZv, YF2e.TSZv in C160; unfold YF0l.zlen, YF0l.L; rewrite length_app, Nat2Z.inj_add; img_exact C160)|].
split; [img_try (unfold YF2e.LFv, YF2e.GFv, YF2e.TFv in C168; unfold YF0l.firstaddr, YF0l.L, YF0l.addr; destruct G; [destruct Tq; img_exact C168 | img_exact C168])|].
split; [img_try (img_exact C176)|].
split; [img_try (unfold YF2e.LBv, YF2e.GBv, YF2e.TBv in C184; rewrite (YF0l.sum_L B ly X W regs mem md PRE); img_exact C184)|].
split; [img_try (img_exact Cq0)|]. split; [img_try (img_exact Cq8)|]. split; [img_try (img_exact Cq16)|]. split; [img_try (img_exact Cq24)|].
split. { intros _ lb initr Hrev. destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (_ & EQ & _). unfold YF0l.addr. rewrite <- EQ. img_exact (CGL lb initr Hrev). }
split. { intros i b Hi. destruct i; discriminate Hi. }
split. {
intros i b Hi. pose proof (nth_error_In _ _ Hi) as INb. apply YF0l.L_all in INb.
destruct (batch_facts b INb) as (L1 & L2 & L3 & L4 & L5 & _).
pose proof (YF0s.batches_nodup B ly X _ M) as ND. unfold all_batches in ND.
assert (OLDQ : Forall (cell_holds B ly rd0) (quar_cells X)).
{ img_apply Forall_forall. intros c Hc. img_apply (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M)). unfold acells. rewrite !in_app_iff. do 4 right; left. img_exact Hc. }
unfold quar_cells, qc_cells in OLDQ. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_cons_iff in OLDQ as [_ OLDQ]. apply Forall_app in OLDQ as [OT OG].
do 4 (apply Forall_cons_iff in OT as [_ OT]). do 4 (apply Forall_cons_iff in OG as [_ OG]).
assert (VMQ : forall a (n : nat) v, (forall j, 0 <= j < Z.of_nat n -> ~ YF2e.WIN ly regs gq (a + j) /\ 0 <= a + j < 2 ^ 64) ->
val_mem tfxsegs (mrestrict H0 mem) a n v -> val_mem tfxsegs (mrestrict H0 mem') a n v).
{ intros a n v Hn Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k Hk. destruct (Hn (Z.of_nat k) ltac:(img_lia)) as [N1 N2]. img_apply MQ. rewrite unsigned_lit_small by img_exact N2. img_exact N1. }
assert (NW : forall j, 0 <= j < 16 -> (forall lb initr, rev G = lb :: initr -> b_self b <> b_self lb \/ 8 <= j) -> ~ YF2e.WIN ly regs gq (addr b + j) /\ 0 <= addr b + j < 2 ^ 64).
{ intros j Hj NL. pose proof (YF0p.GEO B ly X W regs mem md PRE) as (G_PT & _ & _ & G_PS & _). pose proof (YF0p.AQ B TB) as EAQ. unfold o_quar in EAQ.
split; [| img_try (ceil; unfold YF0l.addr, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)].
unfold YF2e.WIN, YF2e.WINF, YF2e.WINA. fold sp0. unfold YF0l.addr. intros [Y|[[Y|[Y|Y]]|[NE Y]]].
- unfold DSTACK, kPrimResvSize, kSpaceSize, kBatchBytes in *. img_lia.
- rewrite EAQ in Y. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. img_lia.
- rewrite EAQ in Y. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *. img_lia.
- unfold t_qc, kThreadObjSize, kPrimResvSize, kSpaceSize, kBatchBytes in *. img_lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [img_try (img_apply NE; rewrite <- (rev_involutive G), Hrev; img_refl)|].
destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (INlb & EQ & _). rewrite EQ in Y.
destruct (NL lb initr eq_refl) as [NEQ|J8]; [|img_try (unfold kBatchBytes in *; img_lia)].
pose proof (YF0s.batches_apart B ly X _ M _ HSP b lb INb INlb NEQ) as D. unfold zdisjoint, YF0s.addr, kBatchBytes in D. cbn [fst snd] in D. img_lia. }
split.
-
destruct (YF0s.cat_next X [] L ltac:(img_refl) i b Hi) as [(i' & Hi' & EN)|[(i' & Hi' & Si & EN)|(initr & Hrev & Sj & EN)]].
+   unfold next_addr. img_change (YF0l.L X) with (G ++ Tq). fold (next_exp (G ++ Tq) i).
pose proof (proj1 (Forall_forall _ _) OT _ (proj2 (In_batch_cells Tq _) (ex_intro _ i' (ex_intro _ b (conj Hi' (or_introl eq_refl)))))) as C.
pose proof (cell_holds_val_mem B ly H0 mem (batch_exp b) 8 (next_exp Tq i') C) as V. cbn [aeval] in V. rewrite <- EN in V.
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with (aeval B ly (next_exp (G ++ Tq) i)) by (img_try (unfold next_exp; destruct (nth_error (G ++ Tq) (S i)); img_refl)).
img_apply (VMQ _ 8%nat); [|img_try (img_exact V)]. intros j Hj. img_apply NW; [img_lia|]. intros lb initr Hrev. left.
destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (_ & _ & _). assert (EGr : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
rewrite EGr, map_app, map_app in ND. cbn [map] in ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & _ & N3).
intros E. img_apply (N3 (b_self b)); [img_try (img_apply in_app_iff; left; img_apply in_map; eapply nth_error_In; img_exact Hi') | img_try (left; symmetry; img_exact E)].
+   unfold next_addr. img_change (YF0l.L X) with (G ++ Tq). fold (next_exp (G ++ Tq) i).
pose proof (proj1 (Forall_forall _ _) OG _ (proj2 (In_batch_cells G _) (ex_intro _ i' (ex_intro _ b (conj Hi' (or_introl eq_refl)))))) as C.
pose proof (cell_holds_val_mem B ly H0 mem (batch_exp b) 8 (next_exp G i') C) as V. cbn [aeval] in V. rewrite <- EN in V.
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with (aeval B ly (next_exp (G ++ Tq) i)) by (img_try (unfold next_exp; destruct (nth_error (G ++ Tq) (S i)); img_refl)).
img_apply (VMQ _ 8%nat); [|img_try (img_exact V)]. intros j Hj. img_apply NW; [img_lia|]. intros lb initr Hrev. left.
assert (EGr : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
rewrite EGr, map_app, map_app in ND. cbn [map] in ND. apply NoDup_app_iff in ND as (_ & N2 & _). apply NoDup_app_iff in N2 as (_ & _ & N4).
rewrite EGr in Hi', Si. rewrite length_app in Si. cbn [length] in Si. rewrite nth_error_app1 in Hi' by img_lia.
intros E. img_apply (N4 (b_self b)); [img_try (img_apply in_map; eapply nth_error_In; img_exact Hi') | img_try (left; symmetry; img_exact E)].
+   unfold next_addr. img_change (YF0l.L X) with (G ++ Tq).
destruct (YF0p.glast_facts B ly X W regs mem md PRE b initr Hrev) as (_ & EQ & _).
replace (match nth_error (G ++ Tq) (S i) with Some b3 => SB + b_self b3 | None => 0 end) with TFv.
2:{ unfold YF2e.TFv. rewrite nth_error_app2 by img_lia. rewrite Sj, Nat.sub_diag. destruct Tq; img_refl. }
unfold YF0l.addr. rewrite <- EQ. img_exact (CGL b initr Hrev).
-
assert (C : cell_holds B ly rd0 (z8 (aoff (batch_exp b) 8) (b_bytes b))).
{ unfold all_batches in INb. apply in_app_iff in INb as [INb'|INb'].
- apply In_nth_error in INb' as [i' Hi']. img_apply (proj1 (Forall_forall _ _) OT). img_apply In_batch_cells. exists i', b. split; [img_try (img_exact Hi')|]. right. left. img_refl.
- apply In_nth_error in INb' as [i' Hi']. img_apply (proj1 (Forall_forall _ _) OG). img_apply In_batch_cells. exists i', b. split; [img_try (img_exact Hi')|]. right. left. img_refl. }
pose proof (cell_holds_val_mem B ly H0 mem _ 8 (ANum (b_bytes b)) C) as V. cbn [aeval aoff batch_exp] in V.
replace (SB + (b_self b + 8)) with (addr b + 8) in V by (img_try (unfold YF0l.addr; img_lia)).
img_apply (VMQ _ 8%nat); [|img_try (img_exact V)]. intros j Hj. replace (addr b + 8 + j) with (addr b + (8 + j)) by img_lia. img_apply NW; [img_lia|]. intros; right; img_lia. }
unfold YF0l.sp1, LFRAME. fold sp0.
split; [img_try (replace (sp0 - 80 + 8) with (sp0 - 72) by img_lia; img_exact Cs72)|]. split; [img_try (replace (sp0 - 80 + 24) with (sp0 - 56) by img_lia; img_exact Cs56)|].
split; [img_try (replace (sp0 - 80 + 32) with (sp0 - 48) by img_lia; img_exact Cs48)|]. split; [img_try (replace (sp0 - 80 + 40) with (sp0 - 40) by img_lia; img_exact Cs40)|].
split; [img_try (replace (sp0 - 80 + 48) with (sp0 - 32) by img_lia; img_exact Cs32)|]. split; [img_try (replace (sp0 - 80 + 56) with (sp0 - 24) by img_lia; img_exact Cs24)|].
split; [img_try (replace (sp0 - 80 + 64) with (sp0 - 16) by img_lia; img_exact Cs16)|]. replace (sp0 - 80 + 72) with (sp0 - 8) by img_lia; img_exact Cs8.
Qed.
Local Notation XT := (YF0s.XT X).
Local Notation HTB := (YF0p.HTB B ly X W regs mem md PRE).
Lemma S'_nil : YF0s.S' X [] L = XT.
Proof. unfold YF0s.S', YF0s.XT, YF0l.L. cbn [sum_bytes fold_right st_qglobal qc_bytes set_qglobal set_qthread]. unfold set_qglobal. cbn. f_equal. f_equal. img_lia. Qed.
Lemma FIN_a : forall W' c', YF2e.at_RETD W ly regs mem md gq tq W' c' -> drain_leaf B ly X W regs mem md (tt, XT) W' c'.
Proof.
intros W' c' HR.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & R2 & CS & MQ & PRESW & CELLS). cbv zeta in CELLS.
destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CGL).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
pose proof (YF0p.AQ B TB) as EAQ.
assert (WD : forall a, YF2e.WIN ly regs gq a -> YF0s.D B ly X [] sp0 a).
{ intros a Hw. unfold YF0s.D, YF0s.DT, YF0s.DQ, YF0s.DL, YF0s.DS.
unfold YF2e.WIN, YF2e.WINF, YF2e.WINA in Hw. fold sp0 in Hw. rewrite EAQ in Hw.
unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- do 4 right. clear - Hw. unfold DSTACK. img_lia.
- right; left. left. img_lia.
- right; left. right. img_lia.
- left. img_exact Hw.
- right; right; left. split; [img_try (img_exact Hq)|]. unfold YF0s.GLv, YF0s.addr. unfold YF2e.GLv in Hw. destruct (rev G); [img_try (img_exact Hw) | img_try (img_exact Hw)]. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0s.D B ly X [] sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (MQ (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros X'. img_exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem' x); discriminate)|].
destruct (mem' x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (YF0p.WIN_dec ly X regs a') as [C|C].
-
assert (CASE : YF2e.WINF ly a' \/ kHighMemBeg <= a').
{ pose proof C as C'. unfold YF2e.WIN, YF2e.WINA in C'. fold sp0 in C'.
destruct C' as [Y|[Y|[Hq Y]]]; [img_try (right) | img_try (left; img_exact Y) | img_try (right)].
- clear - Y HSP' hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *. img_lia.
- destruct (rev G) as [|lb initr] eqn:Hrev; [img_try (exfalso; img_apply Hq; rewrite <- (rev_involutive G), Hrev; img_refl)|].
destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (_ & _ & L1 & _). clear - Y L1 hP1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia. }
destruct CASE as [LOWa|HIGHa].
+
assert (SOMEb : exists b, mbyte tfxsegs (mrestrict (w_H W) mem') a' = Some b).
{ unfold YF2e.WINF in LOWa. destruct LOWa as [IN|[IN|IN]].
- exists (Z_to_bv 8 0); img_apply C152; img_exact IN.
- destruct (Z_lt_le_dec a' (A_QUAR + 168)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C160); img_lia)|].
destruct (Z_lt_le_dec a' (A_QUAR + 176)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C168); img_lia)|].
destruct (Z_lt_le_dec a' (A_QUAR + 184)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C176); img_lia) | img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C184); img_lia)].
- destruct (Z_lt_le_dec a' (T + t_qc + 8)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq0); img_lia)|].
destruct (Z_lt_le_dec a' (T + t_qc + 16)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq8); img_lia)|].
destruct (Z_lt_le_dec a' (T + t_qc + 24)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq16); img_lia) | img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq24); img_lia)]. }
destruct SOMEb as [b Hb]. unfold mbyte, mrestrict in Hb. rewrite Ex, Hx, E', ROM in Hb. discriminate.
+ destruct (PRESW a' C HIGHa) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MQ x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (YF0p.WIN_dec ly X regs a) as [C|C].
- exfalso. pose proof (YF0p.WIN_zone B TB ly X W regs mem md PRE a C) as Z3. fold sp0 in Z3.
destruct (Z_lt_le_dec a kHighMemBeg) as [LOWa|HIGHa].
+ pose proof (ts_inst _ TB) as EI. clear - Z3 LOWa Ha hT1 hP1 HSP' hS1 EI. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kThreadObjSize, kHighMemBeg, kLowShadowBeg, TFX_INST, DSTACK, o_q_cmutex, o_q_size in *. img_lia.
+ destruct (PRESW a C HIGHa) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- img_apply (MQ x). rewrite Ux. img_exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0h.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_t : forall j i, 0 <= j < 4 -> (i < 8)%nat -> rd' (T + t_qc + 8 * j + Z.of_nat i) = Some (YG0h.le_byte 0 8 i)).
{ intros j i Hj Hi. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by img_lia.
destruct J as [-> | [-> | [-> | ->]]].
- img_apply (VM _ _ 8%nat _ _ Cq0); [img_lia | img_refl | img_try (img_exact Hi)].
- img_apply (VM _ _ 8%nat _ _ Cq8); [img_lia | img_refl | img_try (img_exact Hi)].
- img_apply (VM _ _ 8%nat _ _ Cq16); [img_lia | img_refl | img_try (img_exact Hi)].
- img_apply (VM _ _ 8%nat _ _ Cq24); [img_lia | img_refl | img_try (img_exact Hi)]. }
assert (NEW_mx : forall i, 0 <= i < 4 -> rd' (as_inst B + o_q_cmutex + i) = Some 0).
{ intros i Hi. (subst rd'; cbv beta). unfold aview. replace (as_inst B + o_q_cmutex + i) with (A_QUAR + 152 + i) by (img_try (rewrite EAQ; unfold o_quar, o_q_cmutex; img_lia)).
rewrite (C152 (A_QUAR + 152 + i)) by img_lia. img_refl. }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_size + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length L)) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C160); [img_try (rewrite EAQ; unfold o_quar, o_q_size; img_lia)|]. unfold YF2e.LSZv, YF2e.GSZv, YF2e.TSZv, YF0l.L. rewrite length_app. img_lia. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_first + Z.of_nat i) = Some (YG0h.le_byte (YF0s.RFv ly L) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C168); [img_try (rewrite EAQ; unfold o_quar, o_q_first; img_lia)|].
unfold YF2e.LFv, YF2e.GFv, YF2e.TFv, YF0s.RFv, YF0s.addr, YF0l.L. destruct G; [img_try (destruct Tq; img_refl) | img_refl]. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_last + Z.of_nat i) = Some (YG0h.le_byte (YF0s.RLv ly L) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C176); [img_try (rewrite EAQ; unfold o_quar, o_q_last; img_lia)|].
unfold YF2e.TLv, YF0s.RLv, YF0s.addr, YF0l.L. rewrite rev_app_distr.
pose proof (YF0p.Tq_ne B ly X W regs mem md PRE) as NE. destruct (rev Tq) as [|lb rt] eqn:RT; [img_try (exfalso; img_apply NE; rewrite <- (rev_involutive Tq), RT; img_refl) | img_refl]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_bytes + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes gq + qc_bytes tq - sum_bytes []) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C184); [img_try (rewrite EAQ; unfold o_quar, o_q_bytes; img_lia)|]. unfold YF2e.LBv, YF2e.GBv, YF2e.TBv. cbn [sum_bytes fold_right]. img_lia. }
assert (NEW_J : forall lb initr, rev G = lb :: initr -> (length ([] : list batch) < length G)%nat ->
forall kk, (kk < 8)%nat -> rd' (YF0s.addr ly lb + Z.of_nat kk) = Some (YG0h.le_byte (YF0s.TFv ly X) 8 kk)).
{ intros lb initr Hrev _. img_apply (VM _ _ 8%nat _ _ (CGL lb initr Hrev)).
- unfold YF2e.GLv, YF0s.addr. rewrite Hrev. img_refl.
- unfold YF2e.TFv, YF0s.TFv, YF0s.addr. destruct Tq; img_refl. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc) as OLDc.
destruct (proj1 (Forall_forall _ _) (YF0p.CONST_OUT B TB ly X W regs mem md PRE HTSD) c Hc) as [[EC EW]|[[EC EW]|OUT]].
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. (subst e w; cbv beta).
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfx_const Tfx_const_sym Tfx_const_abs Tfx_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [img_try (first [congruence | discriminate]) |]). destruct Hc. }
(subst v; cbv beta). intros k Hk. (subst rd'; cbv beta). unfold aview. cbn [aeval]. rewrite (C152 ((0xa6eca + D_10c0) + Z.of_nat k)) by (img_try (rewrite EAQ, (ts_inst _ TB); unfold TFX_INST, o_quar; img_lia)).
cbn [option_map]. f_equal. unfold YG0h.le_byte. rewrite Z.shiftr_0_l. img_refl.
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. (subst e w; cbv beta).
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfx_const Tfx_const_sym Tfx_const_abs Tfx_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [img_try (first [congruence | discriminate]) |]). destruct Hc. }
(subst v; cbv beta). intros k Hk. (subst rd'; cbv beta).
rewrite <- (OLDc k Hk). img_apply AG.
+ cbn [aeval]. img_lia.
+ cbn [aeval]. intros HD. apply (YF0s.D_cases B ly X rd M' [] L eq_refl sp0 HSP' IMG) in HD.
destruct HD as [[Y _]|[[_ Y]|[(b2 & Hb2 & Y & _)|Y]]].
* clear - Y Hk hT1. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. img_lia.
* unfold YF0s.DQ in Y. rewrite (ts_inst _ TB) in Y. clear - Y Hk. unfold TFX_INST, o_q_cmutex, o_q_size in *. img_lia.
* destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold YF0s.addr in Y. clear - Y L4 Hk. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
* clear - Y Hk hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
- eapply (cell_holds_agree B ly rd); [img_try (img_exact OLDc)|].
intros i Hi. (subst rd rd'; cbv beta). destruct (OUT i Hi) as (X1 & X2 & _). img_apply aview_same.
img_apply (MQ (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact X2. img_exact X1. }
pose proof (YF0s.drain_fin_ARm B TB ly X rd rd' M' (proj1 (proj2 PRE))   [] L eq_refl sp0 HSP' IMG AG VIS NEW_t NEW_mx NEW_qs NEW_qf NEW_ql NEW_qb NEW_J CONST') as MF.
rewrite S'_nil in MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
cbn [fst snd].
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wle_refl | split; [|split; [|split]]]])].
-   split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [| img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
pose proof (YF0s.ALedger_S' ly X [] L tfxsegs md LED) as LED'. rewrite S'_nil in LED'. img_exact LED'.
+ destruct BUD as [BUD PIN]. split; [| img_try (pose proof (YF0s.asecA_S' ly X [] L _ PIN) as PIN'; rewrite S'_nil in PIN'; img_exact PIN')].
eapply Z.le_trans; [img_try (img_exact BUD)|]. pose proof (YF0s.abudget_S' X [] L) as EB. rewrite S'_nil in EB. rewrite EB. img_apply Z.le_refl.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly X _ (w_H W) mem mem' (al_img_env tfxsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [img_try (img_exact MF) |]. pose proof (YF0s.frames' X [] L) as EF. rewrite S'_nil in EF. img_exact EF.
*   pose proof (YF0s.sec_extents' ly X [] L) as ES. rewrite S'_nil in ES. img_exact ES.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
intros HD. apply (YF0s.D_cases B ly X rd M' [] L eq_refl sp0 HSP' IMG) in HD. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
destruct HD as [[Y _]|[[Y _]|[(b2 & Hb2 & Y & _)|Y]]].
-- clear - Y SBg hT1. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. img_lia.
-- rewrite (ts_inst _ TB) in Y. clear - Y SBg. unfold TFX_INST, o_q_cmutex, o_q_bytes in *. img_lia.
-- destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold YF0s.addr in Y. clear - Y L4 SBg. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
-- clear - Y SBg hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear - R R2 CS. unfold YF2e.SREGS in CS.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst r; cbv beta); cbn; first [img_exact R2 | img_apply CS; cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right])].
- img_apply same_io_with_vm_backing.
-
intros a Ha NO NO' NS NE. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0s.D_owned B ly X rd M' [] L eq_refl sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch, spZ; left; img_exact O)].
-
intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (YF0p.WIN_dec ly X regs a) as [Hw|Hw].
+ img_apply PRESW; [img_try (img_exact Hw) | img_try (clear - Ha hS1 HSP'; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; img_lia)].
+ img_apply (apresent_same H0 mem); [img_try (img_apply MQ; rewrite unsigned_lit_small by (clear - Ha hS1 hS2 HSP' Usp; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *; img_lia); img_exact Hw) | img_try (img_apply HPRES; img_exact Ha)].
Qed.
Lemma DRPRE : forall P R W' c', ATDR P R W' c' -> L = P ++ R -> sum_bytes R <= kQuarantineMax ->
exists regs2 mem2 mat, W' = W /\ c' = cfg_at tfxsegs A_DoRecycle regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs2 2 = w64 sp1 /\ getr regs2 1 = w64 (0x33844 + D_150) /\ getr regs2 13 = getr regs 13 /\
(forall r : bv 5, In r YF0l.SREGS -> getr regs2 r = getr regs r) /\
(forall x : word, ~ DW P (bv_unsigned x) -> mem2 x = mem x) /\
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) /\
(let m := mrestrict H0 mem2 in
val_mem tfxsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfxsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfxsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfxsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfxsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfxsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ YF0s.D B ly X P sp0 a -> aview tfxsegs H0 mem2 a = rd0 a) /\
dr_pre B ly (YF0s.S' X P R) P W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros P R W' c' HA HL HRB.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HA as (-> & regs' & mem' & mat & -> & R2 & R10 & R11 & R12 & R13 & R1 & CS & MQ & PRS & CELLS). cbv zeta in CELLS.
destruct CELLS as (C152 & C160 & C168 & C176 & C184 & Cq0 & Cq8 & Cq16 & Cq24 & CG & CP & Ct0 & Ct8 & Ct16 & Ct24 & Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
pose proof (YF0p.AQ B TB) as EAQ.
assert (PL : forall b, In b P -> In b L) by (img_try (intros b Hb; rewrite HL; img_apply in_app_iff; left; img_exact Hb)).
assert (RL : forall b, In b R -> In b L) by (img_try (intros b Hb; rewrite HL; img_apply in_app_iff; right; img_exact Hb)).
assert (WD : forall a, DW P a -> YF0s.D B ly X P sp0 a).
{ intros a Hw. unfold YF0s.D, YF0s.DT, YF0s.DQ, YF0s.DL, YF0s.DP, YF0s.DS.
unfold YF0l.DW, YF2e.WINF in Hw. fold sp0 in Hw. rewrite EAQ in Hw. unfold o_quar, o_q_cmutex, o_q_size in *.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b & Hb & Hw)]]].
- do 4 right. clear - Hw. unfold DSTACK, LFRAME in *. img_lia.
- right; left. left. img_lia.
- right; left. right. img_lia.
- left. img_exact Hw.
- right; right; left. split; [img_try (img_exact Hq)|]. unfold YF0s.GLv, YF0s.addr. unfold YF2e.GLv in Hw. destruct (rev G); [img_try (img_exact Hw) | img_try (img_exact Hw)].
- right; right; right; left. exists b. split; [img_try (img_exact Hb)|]. unfold YF0s.addr. unfold YF0l.addr in Hw. img_exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0s.D B ly X P sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (MQ (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros X'. img_exact (ND (WD a X')). }
assert (DWV : forall a, DW P a -> exists b, mbyte tfxsegs (mrestrict (w_H W) mem') a = Some b).
{ intros a Hw. unfold YF0l.DW, YF2e.WINF in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[[Hq Hw]|(b & Hb & Hw)]]].
- img_apply apresent_mbyte. img_apply PRS. clear - Hw. unfold DSTACK, LFRAME in *. img_lia.
- exists (Z_to_bv 8 0). img_apply C152. img_exact Hw.
- destruct (Z_lt_le_dec a (A_QUAR + 168)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C160); img_lia)|].
destruct (Z_lt_le_dec a (A_QUAR + 176)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C168); img_lia)|].
destruct (Z_lt_le_dec a (A_QUAR + 184)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C176); img_lia) | img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ C184); img_lia)].
- destruct (Z_lt_le_dec a (T + t_qc + 8)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq0); img_lia)|].
destruct (Z_lt_le_dec a (T + t_qc + 16)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq8); img_lia)|].
destruct (Z_lt_le_dec a (T + t_qc + 24)); [img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq16); img_lia) | img_try (img_apply (val_mem_mbyte_in _ _ 8%nat _ _ Cq24); img_lia)].
-
destruct (rev G) as [|lb initr] eqn:Hrev; [img_try (exfalso; img_apply Hq; rewrite <- (rev_involutive G), Hrev; img_refl)|].
destruct (YF0p.glast_facts B ly X W regs mem md PRE lb initr Hrev) as (INlb & EQ & _).
assert (EG3 : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
unfold YF2e.GLv in Hw. rewrite Hrev in Hw.
destruct (Nat.lt_ge_cases (length P) (length G)) as [LT|GE].
+ img_apply (val_mem_mbyte_in _ _ 8%nat _ _ (CG LT lb initr eq_refl)). unfold YF0l.addr. img_lia.
+
assert (HP : nth_error P (length (rev initr)) = Some lb).
{ pose proof HL as HL'. unfold YF0l.L in HL'. rewrite EG3, <- app_assoc in HL'.
pose proof (f_equal (fun l => nth_error l (length (rev initr))) HL') as E1. cbn beta in E1.
rewrite nth_error_app2, Nat.sub_diag in E1 by img_lia. cbn [app nth_error] in E1. rewrite nth_error_app1 in E1 by (img_try (rewrite EG3, length_app in GE; cbn [length] in GE; img_lia)). symmetry. img_exact E1. }
img_apply (val_mem_mbyte_in _ _ 8%nat _ _ (CP _ _ HP)). unfold YF0l.addr. img_lia.
-
apply In_nth_error in Hb as [i Hi]. img_apply (val_mem_mbyte_in _ _ 8%nat _ _ (CP i b Hi)). img_lia. }
assert (DP_dec : forall l a, (exists b, In b l /\ addr b <= a < addr b + 8) \/ ~ (exists b, In b l /\ addr b <= a < addr b + 8)).
{ clear. induction l as [|b0 t IH]; intros a.
- right. intros (b & Hb & _). img_exact Hb.
- destruct (IH a) as [(b & Hb & Rg)|N]; [img_try (left; exists b; split; [right; img_exact Hb | img_exact Rg])|].
destruct (Z_lt_le_dec a (addr b0)) as [L1|L1]; [|img_try (destruct (Z_lt_le_dec a (addr b0 + 8)) as [L2|L2]; [left; exists b0; split; [left; img_refl | img_lia]|])].
all: right; intros (b & [<-|Hb] & Rg); [img_lia | img_try (img_exact (N (ex_intro _ b (conj Hb Rg))))]. }
assert (DW_dec : forall a, DW P a \/ ~ DW P a).
{ intros a. destruct (YF0p.WIN_dec ly X regs a) as [Hw|Hw].
- left. unfold YF0l.DW. unfold YF2e.WIN, YF2e.WINA in Hw. fold sp0 in Hw. unfold LFRAME. fold sp0.
destruct Hw as [Hw|[Hw|Hw]]; [img_try (left; img_exact Hw) | img_try (right; left; img_exact Hw) | img_try (right; right; left; img_exact Hw)].
- destruct (DP_dec P a) as [Hp|Hp]; [img_try (left; unfold YF0l.DW; right; right; right; img_exact Hp)|].
right. intros HD. unfold YF0l.DW in HD. unfold LFRAME in HD. fold sp0 in HD.
destruct HD as [Y|[Y|[Y|Y]]]; [img_try (img_apply Hw) | img_try (img_apply Hw) | img_try (img_apply Hw) | img_try (img_exact (Hp Y))]; unfold YF2e.WIN, YF2e.WINA; fold sp0; [img_try (left; img_exact Y) | img_try (right; left; img_exact Y) | img_try (right; right; img_exact Y)]. }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem' x); discriminate)|].
destruct (mem' x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (DW_dec a') as [C|C].
- destruct (DWV a' C) as [b Hb]. unfold mbyte, mrestrict in Hb. rewrite Ex, Hx, E', ROM in Hb. discriminate.
- rewrite (MQ x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (DW_dec a) as [C|C].
- exfalso. destruct (DWV a C) as [b Hb]. unfold mbyte, mrestrict in Hb.
rewrite (seg_rom_none_high a) in Hb by (img_try (clear - Ha; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighShadowEnd, TFX_IMG_END in *; img_lia)).
fold x in Hb. rewrite Hx in Hb. discriminate.
- img_apply (MQ x). rewrite Ux. img_exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0h.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_t : forall j i, 0 <= j < 4 -> (i < 8)%nat -> rd' (T + t_qc + 8 * j + Z.of_nat i) = Some (YG0h.le_byte 0 8 i)).
{ intros j i Hj Hi. assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by img_lia.
destruct J as [-> | [-> | [-> | ->]]].
- img_apply (VM _ _ 8%nat _ _ Cq0); [img_lia | img_refl | img_try (img_exact Hi)].
- img_apply (VM _ _ 8%nat _ _ Cq8); [img_lia | img_refl | img_try (img_exact Hi)].
- img_apply (VM _ _ 8%nat _ _ Cq16); [img_lia | img_refl | img_try (img_exact Hi)].
- img_apply (VM _ _ 8%nat _ _ Cq24); [img_lia | img_refl | img_try (img_exact Hi)]. }
assert (NEW_mx : forall i, 0 <= i < 4 -> rd' (as_inst B + o_q_cmutex + i) = Some 0).
{ intros i Hi. (subst rd'; cbv beta). unfold aview. replace (as_inst B + o_q_cmutex + i) with (A_QUAR + 152 + i) by (img_try (rewrite EAQ; unfold o_quar, o_q_cmutex; img_lia)).
rewrite (C152 (A_QUAR + 152 + i)) by img_lia. img_refl. }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_size + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length R)) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C160); [img_try (rewrite EAQ; unfold o_quar, o_q_size; img_lia) | img_refl]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_first + Z.of_nat i) = Some (YG0h.le_byte (YF0s.RFv ly R) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C168); [img_try (rewrite EAQ; unfold o_quar, o_q_first; img_lia)|]. unfold YF0l.firstaddr, YF0s.RFv, YF0s.addr, YF0l.addr. destruct R; img_refl. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_last + Z.of_nat i) = Some (YG0h.le_byte (YF0s.RLv ly R) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C176); [img_try (rewrite EAQ; unfold o_quar, o_q_last; img_lia)|]. unfold YF0l.lastaddr, YF0s.RLv, YF0s.addr, YF0l.addr. destruct (rev R); img_refl. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (as_inst B + o_q_bytes + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes gq + qc_bytes tq - sum_bytes P) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ C184); [img_try (rewrite EAQ; unfold o_quar, o_q_bytes; img_lia)|].
pose proof (YF0l.sum_L B ly X W regs mem md PRE) as SL. rewrite HL, sum_bytes_app in SL. img_lia. }
assert (NEW_P : forall i b2, nth_error P i = Some b2 -> forall kk, (kk < 8)%nat -> rd' (YF0s.addr ly b2 + Z.of_nat kk) = Some (YG0h.le_byte (next_addr ly P i) 8 kk)).
{ intros i b2 Hi. img_apply (VM _ _ 8%nat _ _ (CP i b2 Hi)); img_refl. }
assert (NEW_J : forall lb initr, rev G = lb :: initr -> (length P < length G)%nat ->
forall kk, (kk < 8)%nat -> rd' (YF0s.addr ly lb + Z.of_nat kk) = Some (YG0h.le_byte (YF0s.TFv ly X) 8 kk)).
{ intros lb initr Hrev LT. img_apply (VM _ _ 8%nat _ _ (CG LT lb initr Hrev)); [img_refl|].
unfold YF2e.TFv, YF0s.TFv, YF0s.addr. destruct Tq; img_refl. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc) as OLDc.
destruct (proj1 (Forall_forall _ _) (YF0p.CONST_OUT B TB ly X W regs mem md PRE HTSD) c Hc) as [[EC EW]|[[EC EW]|OUT]].
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. (subst e w; cbv beta).
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfx_const Tfx_const_sym Tfx_const_abs Tfx_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [img_try (first [congruence | discriminate]) |]). destruct Hc. }
(subst v; cbv beta). intros k Hk. (subst rd'; cbv beta). unfold aview. cbn [aeval]. rewrite (C152 ((0xa6eca + D_10c0) + Z.of_nat k)) by (img_try (rewrite EAQ, (ts_inst _ TB); unfold TFX_INST, o_quar; img_lia)).
cbn [option_map]. f_equal. unfold YG0h.le_byte. rewrite Z.shiftr_0_l. img_refl.
-
unfold cell_holds in OLDc |- *. destruct c as [e w v]; cbn [c_at c_w c_val] in *. (subst e w; cbv beta).
pose proof (ts_const _ TB) as TC.
assert (Hv : v = AV (ANum 0)).
{ clear - Hc TC. rewrite TC in Hc. cbv [Tfx_const Tfx_const_sym Tfx_const_abs Tfx_const_shadow app In z8 z4 z2 z1 c8 c4 c2 c1] in Hc.
repeat (destruct Hc as [Hc|Hc]; [img_try (first [congruence | discriminate]) |]). destruct Hc. }
(subst v; cbv beta). intros k Hk. (subst rd'; cbv beta).
rewrite <- (OLDc k Hk). img_apply AG.
+ cbn [aeval]. img_lia.
+ cbn [aeval]. intros HD. apply (YF0s.D_cases B ly X rd M' P R HL sp0 HSP' IMG) in HD.
destruct HD as [[Y _]|[[_ Y]|[(b2 & Hb2 & Y & _)|Y]]].
* clear - Y Hk hT1. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. img_lia.
* unfold YF0s.DQ in Y. rewrite (ts_inst _ TB) in Y. clear - Y Hk. unfold TFX_INST, o_q_cmutex, o_q_size in *. img_lia.
* destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold YF0s.addr in Y. clear - Y L4 Hk. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
* clear - Y Hk hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
- eapply (cell_holds_agree B ly rd); [img_try (img_exact OLDc)|].
intros i Hi. (subst rd rd'; cbv beta). destruct (OUT i Hi) as (X1 & X2 & X3 & X4). img_apply aview_same.
img_apply (MQ (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact X2. intros HDW.
unfold YF0l.DW in HDW. unfold LFRAME in HDW. fold sp0 in HDW.
destruct HDW as [Y|[Y|[Y|(b2 & Hb2 & Y)]]].
+ img_apply X1. unfold YF2e.WIN. fold sp0. left. img_exact Y.
+ img_apply X1. unfold YF2e.WIN. right; left. img_exact Y.
+ img_apply X1. unfold YF2e.WIN, YF2e.WINA. right; right. img_exact Y.
+ img_apply X4. destruct (batch_facts b2 (proj1 (YF0l.L_all X b2) (PL b2 Hb2))) as (L1 & L2 & _). unfold YF0l.addr in Y.
clear - Y L1 L2 hSP1 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia. }
pose proof (YF0s.drain_fin_ARm B TB ly X rd rd' M' (proj1 (proj2 PRE)) P R HL sp0 HSP' IMG AG VIS NEW_t NEW_mx NEW_qs NEW_qf NEW_ql NEW_qb NEW_J CONST') as MF.
pose proof (YF0s.drain_fin_plist B ly X rd rd' M' P R HL sp0 HSP' IMG AG NEW_P) as PLIST.
assert (Usp1 : 0 <= sp1 < 2 ^ 64) by (img_try (unfold YF0l.sp1, LFRAME; fold sp0; clear - Usp HSP' hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; img_lia)).
assert (SP1 : bv_unsigned (w64 sp1) = sp1) by (img_try (unfold w64; rewrite unsigned_lit_small by img_exact Usp1; img_refl)).
exists regs', mem', mat. split; [img_refl|]. split; [img_refl|].
split; [img_try (img_exact R2)|]. split; [img_try (img_exact R1)|]. split; [img_try (img_exact R13)|]. split; [img_try (img_exact CS)|]. split; [img_try (img_exact MQ)|]. split; [img_try (img_exact PRS)|].
split; [img_try (cbv zeta; splits; assumption)|]. split; [img_try (img_exact AG)|].
unfold dr_pre, spZ, raZ. rewrite R2, R1, R11, R12, SP1. unfold w64 at 1. rewrite unsigned_lit_small by (img_try (clear; img_lia)).
split; [|img_try (split; [img_exact (YF0s.RIS' B ly X rd M' (proj1 (proj2 PRE)) P R HL) | split; [img_refl | split; [| split; [| split; [img_apply YK0s.ret_ok_even; img_refl | split; [clear; img_lia | split; [|split; [|split; [|split; [|split; [|split; [|split; [img_refl|split; [img_refl|split]]]]]]]]]]]]]])].
-   split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [| img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)]. img_exact (YF0s.ALedger_S' ly X P R tfxsegs md LED).
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF0s.asecA_S' ly X P R _ PIN))].
eapply Z.le_trans; [img_try (img_exact BUD)|]. rewrite (YF0s.abudget_S' X P R). img_apply Z.le_refl.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly X _ (w_H W) mem mem' (al_img_env tfxsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [img_try (img_exact MF) | img_try (img_exact (YF0s.frames' X P R))].
*   img_exact (YF0s.sec_extents' ly X P R).
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
intros HD. apply (YF0s.D_cases B ly X rd M' P R HL sp0 HSP' IMG) in HD. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
destruct HD as [[Y _]|[[Y _]|[(b2 & Hb2 & Y & _)|Y]]].
-- clear - Y SBg hT1. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. img_lia.
-- rewrite (ts_inst _ TB) in Y. clear - Y SBg. unfold TFX_INST, o_q_cmutex, o_q_bytes in *. img_lia.
-- destruct (batch_facts b2 Hb2) as (_ & _ & _ & L4 & _). unfold YF0s.addr in Y. clear - Y L4 SBg. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
-- clear - Y SBg hS1. unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *. img_lia.
-   cbn. pose proof (YF0l.sum_L B ly X W regs mem md PRE) as SL. rewrite HL, sum_bytes_app in SL. cbn in SL. clear - SL HRB. img_lia.
-
unfold plist_cells, qc_cells. cbn [qc_list qc_bytes].
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. img_apply (VM _ _ 8%nat _ _ Ct0); [img_lia | img_refl | img_try (img_exact Hkk)]. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. img_apply (VM _ _ 8%nat _ _ Ct8); [img_lia | | img_try (img_exact Hkk)].
unfold YF0l.firstaddr, YF0l.addr. destruct P; img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. img_apply (VM _ _ 8%nat _ _ Ct16); [img_lia | | img_try (img_exact Hkk)].
unfold YF0l.lastaddr, YF0l.addr. destruct (rev P); img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk. img_apply (VM _ _ 8%nat _ _ Ct24); [img_lia | img_refl | img_try (img_exact Hkk)]. }
img_exact PLIST.
- replace sp1 with (sp0 + (-5) * 16) by (img_try (unfold YF0l.sp1, LFRAME; fold sp0; img_lia)). rewrite Z_mod_plus_full. img_exact Hal.
- unfold YF0l.sp1, LFRAME, DRSTACK. fold sp0. clear - Hlo. unfold DSTACK in *. img_lia.
- unfold YF0l.sp1, LFRAME. fold sp0. clear - Hhi. img_lia.
- intros a Ha. img_apply PRS. unfold YF0l.sp1, LFRAME, DRSTACK in Ha. fold sp0 in Ha. clear - Ha. unfold DSTACK. img_lia.
- rewrite (CS 3%bv ltac:(img_try (cbn; tauto))). img_exact Hgp.
- rewrite (CS 4%bv ltac:(img_try (cbn; tauto))). img_exact Htp.
-   pose proof (YF0l.len_L B ly X W regs mem md PRE) as LL. rewrite HL in LL.
unfold YF0l.zlen, EV_MAX in LL. rewrite length_app, Nat2Z.inj_add in LL. clear - LL. img_lia.
-
unfold YF0s.S', YF0s.XT. cbn [st_cache_inited set_qglobal set_qthread].
pose proof PRE as PRE2. destruct PRE2 as (_ & DRX & _). img_apply (wf_qinited _ _ _ _ _ WF). unfold all_batches.
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QB. intros E. apply app_eq_nil in E as [E _]. rewrite E in QB. cbn in QB.
clear - DRX QB. unfold kQuarantineCacheMax in DRX. img_lia.
Qed.
Lemma EPI : forall P R regs2 mem2 mat r W6 c6,
L = P ++ R ->
getr regs2 2 = w64 sp1 -> getr regs2 1 = w64 (0x33844 + D_150) -> (forall r5 : bv 5, In r5 YF0l.SREGS -> getr regs2 r5 = getr regs r5) ->
(forall a, sp0 - DSTACK <= a < sp0 -> apresent H0 mem2 a) ->
(let m := mrestrict H0 mem2 in
val_mem tfxsegs m (sp1 + 32) 8 (bv_unsigned (getr regs 20)) /\ val_mem tfxsegs m (sp1 + 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfxsegs m (sp1 + 48) 8 (bv_unsigned (getr regs 18)) /\ val_mem tfxsegs m (sp1 + 56) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfxsegs m (sp1 + 64) 8 (bv_unsigned (getr regs 8)) /\ val_mem tfxsegs m (sp1 + 72) 8 (bv_unsigned (getr regs 1))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ YF0s.D B ly X P sp0 a -> aview tfxsegs H0 mem2 a = rd0 a) ->
AR tfxsegs B ly (YF0s.S' X P R) W mem2 (with_vm_backing (m_vm_lazy md) mat md) ->
dr_leaf B ly (YF0s.S' X P R) W regs2 mem2 (with_vm_backing (m_vm_lazy md) mat md) r W6 c6 ->
SRr tfxsegs W6 c6 (drain_leaf B ly X W regs mem md r).
Proof.
intros P R regs2 mem2 mat [ru X3] W6 c6 HL R2 R1 CS PRS2 SLOTS AG2 AR2 HDL. cbv zeta in SLOTS. destruct SLOTS as (Cs32 & Cs40 & Cs48 & Cs56 & Cs64 & Cs72).
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & HQL & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2).
assert (Usp1 : 0 <= sp1 < 2 ^ 64) by (img_try (unfold YF0l.sp1, LFRAME; fold sp0; clear - Usp HSP' hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; img_lia)).
assert (SP1 : bv_unsigned (w64 sp1) = sp1) by (img_try (unfold w64; rewrite unsigned_lit_small by img_exact Usp1; img_refl)).
destruct HDL as (regs3 & mem3 & md3 & -> & (AR3 & LLE & WLE & CS3 & SIO & FR3 & PRS3) & PRE3). cbn [fst snd] in *.
unfold spZ, raZ, ascratch in FR3, PRS3, PRE3. rewrite R2, SP1 in FR3, PRS3, PRE3. unfold spZ in FR3. rewrite R2, SP1 in FR3.
assert (NOWN : forall a, sp0 - DSTACK <= a < sp0 -> ~ aowned B ly (YF0s.S' X P R) a /\ ~ aowned B ly X3 a).
{ intros a Ha. split.
- img_apply (AR_stack_law_ok tfxsegs B ly _ W mem2 _ a AR2). clear - Ha Hlo Hhi. unfold DSTACK in *. img_lia.
- img_apply (AR_stack_law_ok tfxsegs B ly X3 W6 mem3 md3 a AR3). clear - Ha Hlo Hhi. unfold DSTACK in *. img_lia. }
assert (AGS : forall a, sp0 - DSTACK <= a < sp0 -> ~ (sp1 - DRSTACK <= a < sp1 + 32) -> aview tfxsegs (w_H W6) mem3 a = aview tfxsegs H0 mem2 a).
{ intros a Ha Hn. destruct (NOWN a Ha) as [N1 N2]. img_apply FR3; [img_try (clear - Ha Usp hS1 HSP'; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg in *; img_lia) | img_try (img_exact N1) | img_try (img_exact N2) | | img_try (clear - Hn; unfold DRSTACK in *; img_lia)].
intros [Hs|Hs]; [img_try (clear - Hs Hn; unfold DRSTACK in *; img_lia)|]. rewrite (ts_errno _ TB) in Hs. clear - Hs Ha hS1 HSP'. unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_ERRNO, DSTACK, kHighMemBeg in *. img_lia. }
assert (PRS6 : forall a, sp0 - DSTACK <= a < sp0 -> apresent (w_H W6) mem3 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp1 - DRSTACK)) as [L1|L1]; [|img_try (destruct (Z_lt_le_dec a sp1) as [L2|L2]; [img_apply PRS3; img_lia | destruct (Z_lt_le_dec a (sp1 + 32)) as [L3|L3]; [img_apply PRE3; img_lia|]])].
all: pose proof (PRS2 a Ha) as P0; apply apresent_mbyte in P0 as [b Hb];
assert (A : aview tfxsegs H0 mem2 a = Some (bv_unsigned b)) by (img_try (unfold aview; rewrite Hb; img_refl));
rewrite <- (AGS a Ha ltac:(img_lia)) in A; apply aview_some in A as (b' & Hb' & _);
img_exact (mbyte_high_apresent (w_H W6) mem3 a b' ltac:(img_try (clear - Ha Usp hS1 HSP'; unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, TFX_IMG_END in *; img_lia)) Hb'). }
set (vra := bv_unsigned (getr regs 1)). set (vs0 := bv_unsigned (getr regs 8)). set (vs1 := bv_unsigned (getr regs 9)).
set (vs2 := bv_unsigned (getr regs 18)). set (vs3 := bv_unsigned (getr regs 19)). set (vs4 := bv_unsigned (getr regs 20)).
assert (CS3' : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs3 r = getr regs2 r) by (img_try (intros r5 z Hz <-; img_exact (CS3 z Hz))).
assert (Q2 : getr regs3 2 = w64 sp1) by (img_try (rewrite (CS3' 2%bv 2 ltac:(unfold acallee_saved; img_lia) ltac:(img_apply bv_eq; (img_case; vm_compute); img_refl)); img_exact R2)).
assert (Q4 : getr regs3 4 = w64 TFX_TP).
{ rewrite (CS3' 4%bv 4 ltac:(img_try (unfold acallee_saved; img_lia)) ltac:(img_try (img_apply bv_eq; (img_case; vm_compute); img_refl))), (CS 4%bv ltac:(img_try (cbn; tauto))), Htp, (ts_tp _ TB). img_refl. }
assert (XF : forall a (n : nat) v, sp1 + 32 <= a -> a + Z.of_nat n <= sp0 -> val_mem tfxsegs (mrestrict H0 mem2) a n v -> val_mem tfxsegs (mrestrict (w_H W6) mem3) a n v).
{ intros a n v H1 H2 Hv. eapply val_mem_aview_xfer; [|img_try (img_exact Hv)]. intros k Hk. img_apply AGS; unfold YF0l.sp1, LFRAME, DRSTACK in *; fold sp0 in H1 |- *; clear - H1 H2 Hk HSP' hS1; unfold DSTACK in *; img_lia. }
assert (FHX : YF2o.free_hyps W6 regs3 mem3 vra vs0 vs1 vs2 vs3 vs4).
{ constructor.
- img_exact Q4.
- (subst vra; cbv beta). unfold w64. rewrite Z_to_bv_bv_unsigned. img_exact Hra.
- rewrite Q2, SP1. unfold YF0l.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. img_lia.
- rewrite Q2, SP1. replace sp1 with (sp0 + (-5) * 16) by (img_try (unfold YF0l.sp1, LFRAME; fold sp0; img_lia)). rewrite Z_mod_plus_full. img_exact Hal.
- (subst vra vs0 vs1 vs2 vs3 vs4; cbv beta). splits; img_apply u64_range.
-
rewrite restrict_mkst_fx. unfold YF2o.SS0, YF2o.SR0, sr_set. cbn [bv_eqb]. unfold YF2o.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros XX; discriminate) | img_try (cbn [sv_denot]; img_exact Q4)].
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. fold (YF2o.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). unfold YF2o.REG0, YF2o.R_STK. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite (YF2o.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2, SP1. unfold LFRAME.
split; [img_try (clear - Usp1; img_lia)|]. split; [img_try (unfold YF0l.sp1, LFRAME; fold sp0; clear - HSP' hS2; unfold kHighMemEnd in *; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
assert (CA : forall a k0 x, ew (YF2o.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W6) mem3) (sp1 + a) (N.to_nat 8) x ->
YQ0b.chunk_ok tfxsegs (YF2o.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) (mrestrict (w_H W6) mem3) sp1 (YQ0b.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros a k0 x Hk0 Hr Hm. eapply chunk_ok_val; [| img_try (img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact Hr) | img_try (cbn; img_lia) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
* img_apply (CA 72 32%nat vra); [img_refl | img_try ((subst vra; cbv beta); img_apply u64_range) | img_try (img_apply XF; [img_lia | unfold YF0l.sp1, LFRAME; fold sp0; cbn; img_lia | img_exact Cs72])].
* img_apply (CA 64 33%nat vs0); [img_refl | img_try ((subst vs0; cbv beta); img_apply u64_range) | img_try (img_apply XF; [img_lia | unfold YF0l.sp1, LFRAME; fold sp0; cbn; img_lia | img_exact Cs64])].
* img_apply (CA 56 34%nat vs1); [img_refl | img_try ((subst vs1; cbv beta); img_apply u64_range) | img_try (img_apply XF; [img_lia | unfold YF0l.sp1, LFRAME; fold sp0; cbn; img_lia | img_exact Cs56])].
* img_apply (CA 48 35%nat vs2); [img_refl | img_try ((subst vs2; cbv beta); img_apply u64_range) | img_try (img_apply XF; [img_lia | unfold YF0l.sp1, LFRAME; fold sp0; cbn; img_lia | img_exact Cs48])].
* img_apply (CA 40 36%nat vs3); [img_refl | img_try ((subst vs3; cbv beta); img_apply u64_range) | img_try (img_apply XF; [img_lia | unfold YF0l.sp1, LFRAME; fold sp0; cbn; img_lia | img_exact Cs40])].
* img_apply (CA 32 37%nat vs4); [img_refl | img_try ((subst vs4; cbv beta); img_apply u64_range) | img_try (img_apply XF; [img_lia | unfold YF0l.sp1, LFRAME; fold sp0; cbn; img_lia | img_exact Cs32])].
+   cbn [pairwise_disjoint all_disjoint YF2o.REG0]. split; img_exact I.
+ fold (YF2o.E0 regs3 vra vs0 vs1 vs2 vs3 vs4). split; [|img_try (split; img_exact I)].
assert (AF : forall k0 Xv lo hi al, ew (YF2o.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok (YF2o.E0 regs3 vra vs0 vs1 vs2 vs3 vs4) k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
assert (SAL : sp1 mod 16 = 0) by (img_try (replace sp1 with (sp0 + (-5) * 16) by (unfold YF0l.sp1, LFRAME; fold sp0; img_lia); rewrite Z_mod_plus_full; img_exact Hal)).
cbn [YF2o.FFX f_atoms atoms_ok].
split. { img_apply (AF 2%nat sp1); [img_try (rewrite (YF2o.E2 regs3 vra vs0 vs1 vs2 vs3 vs4), Q2; img_refl) | img_try (img_exact Usp1) | | img_try (img_change (2 ^ 4) with 16; img_exact SAL) | img_lia].
unfold YF0l.sp1, LFRAME. fold sp0. clear - HSP' hS1 hS2. unfold zone3, TFX_IMG_LO, kLowShadowBeg, DSTACK, kHighMemBeg, kHighMemEnd in *. img_lia. }
split. { img_apply (AF 32%nat vra); [img_refl | img_try ((subst vra; cbv beta); img_apply u64_range) | img_try (pose proof (u64_range (getr regs 1)); (subst vra; cbv beta); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 33%nat vs0); [img_refl | img_try ((subst vs0; cbv beta); img_apply u64_range) | img_try (pose proof (u64_range (getr regs 8)); (subst vs0; cbv beta); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 34%nat vs1); [img_refl | img_try ((subst vs1; cbv beta); img_apply u64_range) | img_try (pose proof (u64_range (getr regs 9)); (subst vs1; cbv beta); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 35%nat vs2); [img_refl | img_try ((subst vs2; cbv beta); img_apply u64_range) | img_try (pose proof (u64_range (getr regs 18)); (subst vs2; cbv beta); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (AF 36%nat vs3); [img_refl | img_try ((subst vs3; cbv beta); img_apply u64_range) | img_try (pose proof (u64_range (getr regs 19)); (subst vs3; cbv beta); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split; [|img_try (img_exact I)]. { img_apply (AF 37%nat vs4); [img_refl | img_try ((subst vs4; cbv beta); img_apply u64_range) | img_try (pose proof (u64_range (getr regs 20)); (subst vs4; cbv beta); img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. } }
unfold cfg_at, raZ. rewrite <- (wvb_self md3) at 1. rewrite R1. unfold w64 at 2. rewrite (unsigned_lit_small (0x33844 + D_150)) by (img_try (clear; img_lia)).
eapply SRr_mono; [img_try (img_exact (YF33.segX W6 regs3 mem3 md3 vra vs0 vs1 vs2 vs3 vs4 (m_vm_materialized md3) FHX))|].
intros W7 c7 _ (-> & regs4 & mat4 & -> & T2 & T1 & T8 & T9 & T18 & T19 & T20 & TS).
rewrite Q2, SP1 in T2. unfold LFRAME in T2.
exists regs4, mem3, (with_vm_backing (m_vm_lazy md3) mat4 md3). split; [img_try ((subst vra; cbv beta); img_refl)|].
assert (CSx : forall z (r5 : bv 5), Z_to_bv 5 z = r5 -> getr regs4 r5 = getr regs r5 -> getr regs4 (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)) by (img_try (intros z r5 <- E; img_exact E)).
assert (VIA3 : forall (r5 : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r5 -> In r5 YF2o.SREGS -> In r5 YF0l.SREGS -> getr regs4 r5 = getr regs r5).
{ intros r5 z Hz Ez I1 I2. rewrite (TS r5 I1), (CS3' r5 z Hz Ez). img_apply CS. img_exact I2. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_exact WLE | split; [|split; [|split]]]])].
- img_apply (AR_model_same B ly X3 W6 mem3 md3); [img_try (img_exact AR3) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
- intros r Hr. pose proof Hr as Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia. clear Hr'.
repeat match type of RR with _ \/ _ => destruct RR as [RR|RR] end; (subst r; cbv beta).
+ img_apply (CSx _ 2%bv); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)|]. rewrite T2. unfold YF0l.sp1, LFRAME. fold sp0. replace (sp0 - 80 + 80) with sp0 by img_lia. unfold sp0, w64. img_apply Z_to_bv_bv_unsigned.
+ img_apply (VIA3 3%bv 3 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 4%bv 4 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (CSx _ 8%bv); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)|]. rewrite T8. (subst vs0; cbv beta). unfold w64. img_apply Z_to_bv_bv_unsigned.
+ img_apply (CSx _ 9%bv); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)|]. rewrite T9. (subst vs1; cbv beta). unfold w64. img_apply Z_to_bv_bv_unsigned.
+ img_apply (CSx _ 18%bv); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)|]. rewrite T18. (subst vs2; cbv beta). unfold w64. img_apply Z_to_bv_bv_unsigned.
+ img_apply (CSx _ 19%bv); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)|]. rewrite T19. (subst vs3; cbv beta). unfold w64. img_apply Z_to_bv_bv_unsigned.
+ img_apply (CSx _ 20%bv); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)|]. rewrite T20. (subst vs4; cbv beta). unfold w64. img_apply Z_to_bv_bv_unsigned.
+ img_apply (VIA3 21%bv 21 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 22%bv 22 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 23%bv 23 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 24%bv 24 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 25%bv 25 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 26%bv 26 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
+ img_apply (VIA3 27%bv 27 Hr); [img_try (img_apply bv_eq; (img_case; vm_compute); img_refl) | img_try (cbn; tauto) | img_try (cbn; tauto)].
- eapply same_io_trans; [img_try (img_apply same_io_with_vm_backing)|]. eapply same_io_trans; [img_try (img_exact SIO) | img_try (img_apply same_io_with_vm_backing)].
-
intros a Ha NO NO3 NS NF. unfold ascratch, spZ in NS. fold sp0 in NS.
assert (NOS : ~ aowned B ly (YF0s.S' X P R) a).
{ intros O. img_apply NO. img_exact (aowned_same_cf B ly X _ a (YF0s.S'_chunks X P R) (YF0s.S'_fs X P R) O). }
transitivity (aview tfxsegs H0 mem2 a).
+ img_apply FR3; [img_try (img_exact Ha) | img_try (img_exact NOS) | img_try (img_exact NO3) | | img_try (intros HE; img_apply NS; left; unfold YF0l.sp1, LFRAME in HE; fold sp0 in HE; clear - HE; unfold DSTACK; img_lia)].
intros [Hs|Hs]; img_apply NS; [img_try (left; unfold YF0l.sp1, LFRAME, DRSTACK in Hs; fold sp0 in Hs; clear - Hs; unfold DSTACK; img_lia) | img_try (right; img_exact Hs)].
+ img_apply AG2; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0s.D_owned B ly X _ M P R HL sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; left; img_exact O)].
- intros a Ha. img_apply PRS6. unfold spZ in Ha. img_exact Ha.
Qed.
Lemma drain_body_unfold :
drain_body X X = (if qc_bytes gq + qc_bytes tq <=? kQuarantineMax then ret tt else recycle_body (transfer_g X)) XT.
Proof. unfold drain_body, bind, put. cbn [ibind]. img_refl. Qed.
Theorem tfx_drain_arm : amreal tfxsegs (drain_body X X) W (cfg_at tfxsegs A_Drain regs mem md) (drain_leaf B ly X W regs mem md).
Proof.
pose proof (YF0p.FH_ok B TB ly X W regs mem md PRE) as FH.
pose proof (YF0l.sum_L B ly X W regs mem md PRE) as SL. pose proof (YF0l.len_L B ly X W regs mem md PRE) as LL.
assert (WALK : (kQuarantineMax < qc_bytes gq + qc_bytes tq -> 2 * (kBatchBytes * Z.of_nat (length L)) <= qc_bytes gq + qc_bytes tq) ->
SRr tfxsegs W (cfg_at tfxsegs A_Drain regs mem md) (YF2e.postD W ly regs mem md gq tq)).
{ intros HM. unfold cfg_at, A_Drain. rewrite <- (wvb_self md) at 1.
assert (HM' : kQuarantineMax < YF2e.LBv gq tq -> 2 * (kBatchBytes * YF2e.LSZv gq tq) <= YF2e.LBv gq tq).
{ unfold YF2e.LBv, YF2e.GBv, YF2e.TBv, YF2e.LSZv, YF2e.GSZv, YF2e.TSZv. intros H1.
unfold YF0l.L in HM. rewrite length_app, Nat2Z.inj_add in HM. img_exact (HM H1). }
destruct G as [|g0 G'] eqn:EG.
- img_apply (YF2b.segDE W ly regs mem md gq tq (m_vm_materialized md) FH); [img_try (img_exact EG) | img_try (img_exact HM')].
- img_apply (YF2c.segDN W ly regs mem md gq tq (m_vm_materialized md) FH); [img_try (rewrite EG; discriminate) | img_try (img_exact HM')]. }
rewrite drain_body_unfold. unfold YF2e.postD, YF2e.LBv, YF2e.GBv, YF2e.TBv in WALK.
destruct (Z.leb_spec (qc_bytes gq + qc_bytes tq) kQuarantineMax) as [LE|GT].
-
cbn [amreal ret]. eapply SRr_mono; [img_try (img_exact (WALK ltac:(intros; img_lia)))|]. intros W' c' _ HR. img_exact (FIN_a W' c' HR).
-
unfold recycle_body, mcheck. cbn [qc_list qc_bytes transfer_g].
destruct (Z.leb_spec (2 * (kBatchBytes * Z.of_nat (length (G ++ Tq)))) (qc_bytes gq + qc_bytes tq)) as [MC|MC].
2:{   unfold bind, fail. cbn [ibind amreal]. img_exact I. }
unfold bind at 1. unfold ret. cbn [ibind].
destruct (pop_batches 100000 (transfer_g X) []) as [g' P] eqn:EP.
pose proof (pop_batches_spec _ _ _ _ _ EP) as (P0 & EP0 & EL & EB). cbn [rev app] in EP0. (subst P0; cbv beta). cbn [transfer_g qc_list qc_bytes] in EL, EB.
assert (LEN : (length (qc_list (transfer_g X)) < 100000)%nat).
{ cbn [transfer_g qc_list]. unfold YF0l.zlen, YF0l.L, EV_MAX in LL. img_apply Nat2Z.inj_lt. rewrite of_nat_100000. img_lia. }
pose proof (pop_batches_stop _ _ _ _ _ EP LEN) as STOP.
destruct g' as [R s]. cbn [qc_list qc_bytes] in EL, EB, STOP.
assert (HL : L = P ++ R) by img_exact EL.
assert (SR : sum_bytes R <= kQuarantineMax).
{ rewrite HL, sum_bytes_app in SL. destruct STOP as [S1|S1]; [img_try (unfold kQuarantineMin, kQuarantineMax in *; img_lia) | img_try ((subst R; cbv beta); cbn; unfold kQuarantineMax; img_lia)]. }
unfold bind, modify. cbn [ibind].
img_change (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (YF0s.S' X P R) || (replace (set_qglobal {| qc_list := R; qc_bytes := s |} XT) with (YF0s.S' X P R) by (img_try (unfold YF0s.S'; cbn [st_qglobal qc_bytes YF0s.XT set_qglobal]; rewrite EB; img_refl))).
img_apply amreal_after_SRr.
eapply SRr_bind; [img_try (img_exact (WALK ltac:(intros _; unfold YF0l.L; img_exact MC)))|]. intros W1 c1 _ H1.
pose proof (L0_LST W1 c1 H1) as H2.
eapply SRr_bind.
{ img_apply (YF0l.LOOP B TB ly X W regs mem md PRE L [] 100000%nat W1 c1 H2 eq_refl); [img_try (rewrite SL; unfold kQuarantineMin, kQuarantineMax in *; img_lia) | img_try (img_exact LEN)]. }
intros W2 c2 _ H3. cbn beta zeta in H3. cbn [rev] in H3. rewrite SL in H3. img_change (YF0l.L X) with (G ++ Tq) in H3. unfold transfer_g in EP. rewrite EP in H3. cbn [fst snd qc_list] in H3.
destruct (DRPRE P R W2 c2 H3 HL SR) as (regs2 & mem2 & mat & -> & -> & R2 & R1 & R13 & CS & MQ & PRS & SLOTS & AG & DPRE).
img_apply SRr_ret. eapply amreal_then_SRr; [img_try (img_exact (DR ly _ P W regs2 mem2 _ DPRE))|].
intros r W6 c6 HDL. img_exact (EPI P R regs2 mem2 mat r W6 c6 HL R2 R1 CS PRS SLOTS AG (proj1 DPRE) HDL).
Qed.
End f.
Theorem tfx_drain_ok {imgk : img} : forall B, TfxSyms B -> tfx_dorecycle_spec B -> tfx_drain_spec B.
Proof. intros B TB DR ly X W regs mem md PRE. img_exact (tfx_drain_arm B TB DR ly X W regs mem md PRE). Qed.
End d.
