(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMseg_mbc.v (commit fe876300d09, Quarantine::Drain walk set; file sha256 8a767a21473c) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 7 image addresses moved by code-verified function pairs (7 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 10 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMseg_mbc.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (17 numerals; per-numeral report). *)
(* MergeBatches' copy loop (0x33c3c-0x33c4c), one word:
     0x33c3c ld t5, 0(t2); 0x33c40 t2 += 8; 0x33c44 sd t5, 0(t3); 0x33c48 t3 += 8; 0x33c4c bne t2, t4 -> 0x33c3c.
   t2 = [src] (the successor's slot being read), t3 = [dst] (the current batch's next free slot), t4 = [endp] (the end of
   the successor's slots); the word read is [w].  Back to 0x33c3c [at_CNEXT] or on to 0x33c50 [at_CDONE]; the only
   word written is dst. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kSpaceSize, TFIB_IMG_END,
kBatchBytes, kBatchSlots, TFIB_TP, A_QUAR, A_ALLOCATOR, o_quar in *.
Lemma zcanon_negadd_r : forall a b, 0 <= b <= a -> a < M64 -> zcanon (a + zcanon (b * zcanon (-1))) = a - b.
Proof. intros a b H H2. rewrite Z.add_comm. exact (zcanon_negadd a b H H2). Qed.
Ltac zneg := repeat (first [ rewrite zcanon_negadd | rewrite zcanon_negadd_r ]; [ | zlia | unfold M64; zlia ]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (src dst endp w : Z).
Variable mat0 : list word.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33c3c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Definition XW : list word := [ w64 src; w64 dst; w64 endp; w64 w ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma EqSRC : ew E0 32 = w64 src. Proof. reflexivity. Qed.
Lemma EqDST : ew E0 33 = w64 dst. Proof. reflexivity. Qed.
Lemma EqEND : ew E0 34 = w64 endp. Proof. reflexivity. Qed.
Lemma EqW : ew E0 35 = w64 w. Proof. reflexivity. Qed.
(* the word read, the word written *)
Definition R_SRC : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35%nat 0))].
Definition R_DST : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 8 [].
Definition REG0 : smem := [ R_SRC; R_DST ].
Definition FFC : facts := mkFacts
[ (32%nat, mkAF kHighMemBeg CEIL_MAX 3);
(33%nat, mkAF kHighMemBeg CEIL_MAX 3);
(34%nat, mkAF kHighMemBeg CEIL_MAX 3);
(35%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set sr_atoms 7%bv (SOff 32%nat 0)) 28%bv (SOff 33%nat 0)) 29%bv (SOff 34%nat 0).
Definition SS0 : sstate := mkSS 0x33c3c SR0 REG0 None FFC.
Record free_hyps : Prop := FreeHyps {
fh_Hsrc : kHighMemBeg <= src /\ src + 8 <= endp /\ endp <= ASAN_CEIL /\ src mod 8 = 0 /\ endp mod 8 = 0;
fh_Hdst : kHighMemBeg <= dst /\ dst + 8 <= ASAN_CEIL /\ dst mod 8 = 0;
fh_Hdisj : src + 8 <= dst \/ dst + 8 <= src;
fh_Hw : 0 <= w < 2 ^ 64;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33c3c) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hsrc Hdst Hdisj Hw SEED].
Lemma derived_ranges :
kHighMemBeg <= src /\ src + 8 <= endp /\ endp <= ASAN_CEIL /\ kHighMemBeg <= dst /\ dst + 8 <= ASAN_CEIL /\
0 <= w < 2 ^ 64 /\ ASAN_CEIL <= CEIL_MAX.
Proof.
open_FH. destruct Hsrc as (S1 & S2 & S3 & _). destruct Hdst as (D1 & D2 & _).
clear - S1 S2 S3 D1 D2 Hw. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop := dst <= a < dst + 8.
Definition win_sub (t w : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst w)) && (snd (fst w) <=? snd (fst t)) && (snd t <=? snd w).
Lemma win_sub_sound : forall E a t w, win_sub t w = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w.
Proof.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Definition WSK : list (option nat * Z * Z) := [(Some 33%nat, 0, 8)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK.
Proof.
intros E HE t a Hin Hr. pose proof derived_ranges as DR. unfold WSK in Hin. cbn [In] in Hin. destruct Hin as [<-|[]].
cbn [fst snd base_val] in Hr. rewrite HE in Hr by (cbv; lia). rewrite EqDST in Hr. unfold w64 in Hr.
rewrite unsigned_lit_small in Hr by (clear - DR; numconst; lia). unfold WIN. lia.
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
(* Every register but t2, t3, t4 (t4 is the atom endp) and t5. *)
Definition SREGS : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%bv.
Definition at_CNEXT (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ src + 8 <> endp /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33c3c) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 7 = w64 (src + 8) /\ getr regs' 28 = w64 (dst + 8) /\ getr regs' 29 = w64 endp /\
MEQ mem' /\ val_mem tfibsegs (mrestrict (w_H W) mem') dst 8 w.
Definition at_CDONE (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ src + 8 = endp /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33c50) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 7 = w64 (src + 8) /\ getr regs' 28 = w64 (dst + 8) /\ getr regs' 29 = w64 endp /\
MEQ mem' /\ val_mem tfibsegs (mrestrict (w_H W) mem') dst 8 w.
Definition postC : world tfibsegs -> config -> Prop := if src + 8 =? endp then at_CDONE else at_CNEXT.

Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; zneg; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l; first [ reflexivity | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 33) = _ |- _ => rewrite B end; zlia ].
Ltac zev_close := cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; zneg; zcanon_simp; zlia.
Ltac tV := first
[ reflexivity
| cbn [sv_denot]; rewrite ?EqSRC, ?EqDST, ?EqEND, ?EqW; unfold w64; rewrite ?Zbv_add_unsigned;
first [ reflexivity | f_equal; zlia ]
| apply denot_by_zev; [ reflexivity | numconst; zlia | zev_close ] ].
Ltac tR := first [ zlia | numconst; zlia | apply u64_range ].
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_zev HS r :=
let Q := fresh "Q" in
pose proof (st_ok_reg_denot (w_H W) E0 _ _ r HS) as Q; cbn [ms_regs restrict] in Q;
lazymatch type of Q with _ = sv_denot _ (sr_get ?sr ?rr) => let t := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with t in Q end;
rewrite Q; clear Q;
apply denot_by_zev; [ reflexivity | numconst; zlia | zev_close ].
Ltac reg_val HS r := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV | reg_zev HS r ].
Ltac reg_keep HS := lazymatch goal with |- getr _ ?r = getr _ _ =>
let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_entry HS r k end.
Ltac sregs HS := intros r Hr; cbn [SREGS In] in Hr;
repeat match type of Hr with
| _ = r \/ _ => let E := fresh "E" in destruct Hr as [E|Hr]; [subst r; reg_keep HS|]
| _ = r => subst r; reg_keep HS
| False => destruct Hr
end.
Ltac fin_copy HS :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [assumption|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [sregs HS|];
split; [reg_val HS (7%bv : bv 5)|];
split; [reg_val HS (28%bv : bv 5)|];
split; [reg_val HS (29%bv : bv 5)|];
split; [assumption|];
memv HS 1%nat 0%nat; [tA | tV | tR]
end.

Lemma segC : SRr tfibsegs W cfg0 postC.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK_ok E0 HE0) as SKW.
assert (R32 : rho_of E0 32%nat = src) by (unfold rho_of; rewrite EqSRC; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R33 : rho_of E0 33%nat = dst) by (unfold rho_of; rewrite EqDST; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R34 : rho_of E0 34%nat = endp) by (unfold rho_of; rewrite EqEND; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R35 : rho_of E0 35%nat = w) by (unfold rho_of; rewrite EqW; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (BV33 : bv_unsigned (ew E0 33) = dst) by exact R33.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
- (* bne taken: src + 8 <> endp *)
assert (HN : src + 8 <> endp) by (clear - Hc DR R32 R34; zbranch Hc; apply Bool.negb_true_iff in Hc; apply Z.eqb_neq in Hc; exact Hc).
unfold postC. destruct (Z.eqb_spec (src + 8) endp) as [X|_]; [exfalso; exact (HN X)|].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33c3c. meq_acc SKW.
fin_copy HS.
- assert (HN : src + 8 = endp) by (clear - Hc DR R32 R34; zbranch Hc; apply Bool.negb_false_iff in Hc; apply Z.eqb_eq in Hc; exact Hc).
unfold postC. destruct (Z.eqb_spec (src + 8) endp) as [_|X]; [|exfalso; exact (X HN)].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33c50. meq_acc SKW.
fin_copy HS.
Qed.
End WK.
End d.
