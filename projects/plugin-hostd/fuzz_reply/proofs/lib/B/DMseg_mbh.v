(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMseg_mbh.v (commit fe876300d09, Quarantine::Drain walk set; file sha256 5cb952738ac0) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 13 image addresses moved by code-verified function pairs (12 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 21 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMseg_mbh.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (34 numerals; per-numeral report). *)
(* MergeBatches (0x33bcc, frame 0x10), the outer loop head 0x33c04, one pass of the test.

   The loop's registers: sp = MergeBatches' sp (its frame holds ra = 0x33a90 at sp + 8); a0 = the global list
   (A_QUAR + 160: count +0, first +8, last +16, bytes +24); a2 = the bytes extracted so far [tot]; a4 = the current
   batch [cur]; t0 = its successor [nx]; a5 = kBatchSlots (1021).  A batch object: next +0, size +8, count +16, slots
   from +24.
   - 0x33c04-0x33c10: t1 = count(cur) + count(nx); bltu 1021 < t1 -> 0x33bf8: cur := nx, t0 := nx->next; beqz ->
     0x33ce8 (list bytes -= tot, ld ra, ret to 0x33a90) [at_EXH], else back to 0x33c04 [at_ADV];
   - else 0x33c14-0x33c1c: a3 = size(cur), beqz (size >> 13) -> 0x33d18, the CHECK_GE die path (excluded:
     size(cur) >= kBatchBytes); 0x33c20 beqz count(nx) -> 0x33c50 [at_TOTAIL], else the copy loop's set-up
     0x33c24-0x33c38 (t2 = nx + 24, t3 = cur + 24 + 8 * count(cur), t4 = nx + 24 + 8 * count(nx)) to the copy loop
     head 0x33c3c [at_TOCOPY].
   Nothing is stored before 0x33ce8, so the only window is the list's byte count. *)
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
(* sub rd, a, b denotes zcanon (a + zcanon (b * zcanon (-1))) (YFeu.zcanon_negadd has the operands swapped). *)
Lemma zcanon_negadd_r : forall a b, 0 <= b <= a -> a < M64 -> zcanon (a + zcanon (b * zcanon (-1))) = a - b.
Proof. intros a b H H2. rewrite Z.add_comm. exact (zcanon_negadd a b H H2). Qed.
Ltac zneg := repeat (first [ rewrite zcanon_negadd | rewrite zcanon_negadd_r ]; [ | zlia | unfold M64; zlia ]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (cur nx ccnt ncnt csz nnx lbytes tot : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33c04) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Definition XW : list word := [ w64 cur; w64 nx; w64 ccnt; w64 ncnt; w64 csz; w64 nnx; w64 lbytes; w64 tot ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma EqCUR : ew E0 32 = w64 cur. Proof. reflexivity. Qed.
Lemma EqNX : ew E0 33 = w64 nx. Proof. reflexivity. Qed.
Lemma EqCC : ew E0 34 = w64 ccnt. Proof. reflexivity. Qed.
Lemma EqNC : ew E0 35 = w64 ncnt. Proof. reflexivity. Qed.
Lemma EqCS : ew E0 36 = w64 csz. Proof. reflexivity. Qed.
Lemma EqNN : ew E0 37 = w64 nnx. Proof. reflexivity. Qed.
Lemma EqLB : ew E0 38 = w64 lbytes. Proof. reflexivity. Qed.
Lemma EqTOT : ew E0 39 = w64 tot. Proof. reflexivity. Qed.
(* MergeBatches' frame (ra at +8), the list's byte count, cur's size and count, nx's next and count. *)
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SLit 0x33a90))].
Definition R_LH : YP09.region :=
YP09.mkRegion None (A_QUAR + 184) (A_QUAR + 192) (A_QUAR + 184) (A_QUAR + 192) [YP09.mkChunk (A_QUAR + 184) (CVal 8 (SOff 38%nat 0))].
Definition R_CUR : YP09.region :=
YP09.mkRegion (Some 32%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 36%nat 0)); YP09.mkChunk 16 (CVal 8 (SOff 34%nat 0))].
Definition R_NX : YP09.region :=
YP09.mkRegion (Some 33%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 37%nat 0)); YP09.mkChunk 16 (CVal 8 (SOff 35%nat 0))].
Definition REG0 : smem := [ R_STK; R_LH; R_CUR; R_NX ].
Definition FFH : facts := mkFacts
[ (2%nat, mkAF kHighMemBeg (kHighMemEnd - 16) 4);
(32%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(33%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(34%nat, mkAF 0 1021 0);
(35%nat, mkAF 0 1021 0);
(36%nat, mkAF 8192 (2 ^ 40) 0);
(37%nat, mkAF 0 CEIL_MAX 13);
(38%nat, mkAF 0 (2 ^ 40) 0);
(39%nat, mkAF 0 (2 ^ 40) 0) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv (SLit (A_QUAR + 160))) 12%bv (SOff 39%nat 0))
14%bv (SOff 32%nat 0)) 5%bv (SOff 33%nat 0)) 15%bv (SLit 1021).
Definition SS0 : sstate := mkSS 0x33c04 SR0 REG0 None FFH.
Record free_hyps : Prop := FreeHyps {
fh_Hsp : kHighMemBeg <= sp0 /\ sp0 + 16 <= kHighMemEnd;
fh_Hsp_al : sp0 mod 16 = 0;
fh_Hcur : kHighMemBeg <= cur /\ cur + kBatchBytes <= ASAN_CEIL /\ cur mod 8192 = 0;
fh_Hnx : kHighMemBeg <= nx /\ nx + kBatchBytes <= ASAN_CEIL /\ nx mod 8192 = 0;
fh_Hcnt : 0 <= ccnt <= kBatchSlots /\ 0 <= ncnt <= kBatchSlots;
fh_Hcsz : kBatchBytes <= csz <= 2 ^ 40;
fh_Hnnx : 0 <= nnx < ASAN_CEIL /\ nnx mod 8192 = 0;
fh_Htot : 0 <= tot <= lbytes /\ lbytes <= 2 ^ 40;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33c04) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hsp Hsp_al Hcur Hnx Hcnt Hcsz Hnnx Htot SEED].
Lemma derived_ranges :
kHighMemBeg <= sp0 /\ sp0 + 16 <= kHighMemEnd /\
kHighMemBeg <= cur /\ cur + kBatchBytes <= ASAN_CEIL /\ kHighMemBeg <= nx /\ nx + kBatchBytes <= ASAN_CEIL /\
0 <= ccnt <= 1021 /\ 0 <= ncnt <= 1021 /\ 8192 <= csz <= 2 ^ 40 /\ 0 <= nnx < ASAN_CEIL /\
0 <= tot <= lbytes /\ lbytes <= 2 ^ 40 /\ ASAN_CEIL <= CEIL_MAX.
Proof.
open_FH. destruct Hsp as [S1 S2]. destruct Hcur as (C1 & C2 & _). destruct Hnx as (N1 & N2 & _). destruct Hcnt as [K1 K2].
destruct Hnnx as (M1 & _). destruct Hcsz as [Z1 Z2]. destruct Htot as [T1 T2].
clear - S1 S2 C1 C2 N1 N2 K1 K2 M1 Z1 Z2 T1 T2. numconst. repeat split; lia.
Qed.
(* The only window: the list's byte count. *)
Definition WIN (a : Z) : Prop := A_QUAR + 184 <= a < A_QUAR + 192.
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
Definition WSK : list (option nat * Z * Z) := [(None, A_QUAR + 184, A_QUAR + 192)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK_ok : forall E : env, sk_ok E WSK.
Proof.
intros E t a Hin Hr. unfold WSK in Hin. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. unfold WIN. lia.
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
(* The registers the loop keeps from its head (ra, gp, tp, s0-s11, a1, a6, a7). *)
Definition SREGS : list (bv 5) := [1; 3; 4; 8; 9; 11; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* The callee-saved registers, gp and tp (MergeBatches' return). *)
Definition SREGSX : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_ADV (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33c04) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 12 = w64 tot /\ getr regs' 15 = w64 1021 /\
getr regs' 14 = w64 nx /\ getr regs' 5 = w64 nnx /\
MEQ mem' /\ val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 184) 8 lbytes.
Definition at_EXH (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33a90) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 + 16) /\ getr regs' 1 = w64 0x33a90 /\ (forall r : bv 5, In r SREGSX -> getr regs' r = getr regs0 r) /\
MEQ mem' /\ val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 184) 8 (lbytes - tot).
Definition at_TOCOPY (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33c3c) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 12 = w64 tot /\ getr regs' 15 = w64 1021 /\
getr regs' 14 = w64 cur /\ getr regs' 5 = w64 nx /\
getr regs' 6 = w64 (ccnt + ncnt) /\ getr regs' 13 = w64 csz /\
getr regs' 7 = w64 (nx + 24) /\ getr regs' 28 = w64 (cur + 24 + 8 * ccnt) /\ getr regs' 29 = w64 (nx + 24 + 8 * ncnt) /\
MEQ mem' /\ val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 184) 8 lbytes.
Definition at_TOTAIL (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33c50) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 12 = w64 tot /\ getr regs' 15 = w64 1021 /\
getr regs' 14 = w64 cur /\ getr regs' 5 = w64 nx /\
getr regs' 6 = w64 (ccnt + ncnt) /\ getr regs' 13 = w64 csz /\
MEQ mem' /\ val_mem tfibsegs (mrestrict (w_H W) mem') (A_QUAR + 184) 8 lbytes.
Definition postH : world tfibsegs -> config -> Prop :=
if 1021 <? ccnt + ncnt then (if nnx =? 0 then at_EXH else at_ADV)
else (if ncnt =? 0 then at_TOTAIL else at_TOCOPY).

Ltac meq_acc SKOK :=
match goal with
| M : MEQ ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQ_frame E _ rs ma mb SKOK ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YP09.mkChunk ?o _) :: ?t => let e := eval vm_compute in (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; zneg; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l; first [ reflexivity | zlia | numconst; zlia ].
Ltac zev_close := cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; zneg; zcanon_simp; zlia.
Ltac tV := first
[ reflexivity
| cbn [sv_denot]; rewrite ?EqCUR, ?EqNX, ?EqCC, ?EqNC, ?EqCS, ?EqNN, ?EqLB, ?EqTOT; unfold w64; rewrite ?Zbv_add_unsigned;
first [ reflexivity | f_equal; zlia ]
| apply denot_by_zev; [ reflexivity | numconst; zlia | zev_close ] ].
Ltac tR := first [ zlia | numconst; zlia | apply u64_range ].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
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
Ltac sregs HS := intros r Hr; cbn [SREGS SREGSX In] in Hr;
repeat match type of Hr with
| _ = r \/ _ => let E := fresh "E" in destruct Hr as [E|Hr]; [subst r; reg_keep HS|]
| _ = r => subst r; reg_keep HS
| False => destruct Hr
end.
Ltac reg_any HS := lazymatch goal with |- getr _ ?r = _ => reg_val HS r end.
Ltac fin_loop HS :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_entry HS (2%bv : bv 5) 2%nat|];
split; [sregs HS|];
split; [reg_lit HS (10%bv : bv 5)|];
split; [reg_val HS (12%bv : bv 5)|];
split; [reg_lit HS (15%bv : bv 5)|];
repeat (split; [first [ assumption | reg_any HS | memvo HS 1%nat (A_QUAR + 184); [tA | tV | tR]
  | match goal with |- ?g => idtac "LOOPGOAL" g; fail end ]|]);
first [ assumption | memvo HS 1%nat (A_QUAR + 184); [tA | tV | tR] | match goal with |- ?g => idtac "LASTGOAL" g; fail end ]
end.
(* The exit: the symbolic run follows MergeBatches' ret (ra = 0x33a90 is a literal from the frame) and stops at
   0x33a90. *)
Ltac fin_exit HS :=
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let HshR := fresh "HshR" in
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [idtac "X1"; rewrite HshR at 1; reflexivity|];
split; [idtac "X2"; let Q := fresh "Q" in rreg HS (2%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; unfold w64; f_equal; unfold sp0; zlia|];
split; [reg_lit HS (1%bv : bv 5)|];
split; [idtac "X3"; sregs HS|];
split; [idtac "X4"; assumption|];
idtac "X5"; memvo HS 1%nat (A_QUAR + 184);
[ tA | tV | tR ]
end.

Lemma segH : SRr tfibsegs W cfg0 postH.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ. pose proof (WSK_ok E0) as SKW.
assert (R32 : rho_of E0 32%nat = cur) by (unfold rho_of; rewrite EqCUR; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R33 : rho_of E0 33%nat = nx) by (unfold rho_of; rewrite EqNX; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R34 : rho_of E0 34%nat = ccnt) by (unfold rho_of; rewrite EqCC; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R35 : rho_of E0 35%nat = ncnt) by (unfold rho_of; rewrite EqNC; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R36 : rho_of E0 36%nat = csz) by (unfold rho_of; rewrite EqCS; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R37 : rho_of E0 37%nat = nnx) by (unfold rho_of; rewrite EqNN; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R38 : rho_of E0 38%nat = lbytes) by (unfold rho_of; rewrite EqLB; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R39 : rho_of E0 39%nat = tot) by (unfold rho_of; rewrite EqTOT; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
- (* bltu 1021 < count(cur) + count(nx): advance *)
assert (HA : 1021 < ccnt + ncnt) by (clear - Hc DR R34 R35; zbranch Hc; apply Z.ltb_lt in Hc; zlia).
unfold postH. destruct (Z.ltb_spec 1021 (ccnt + ncnt)) as [_|X]; [|exfalso; clear - X HA; zlia].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
+ assert (HN : nnx = 0) by (clear - Hc0 DR R37; zbranch Hc0; apply Z.eqb_eq in Hc0; exact Hc0).
destruct (Z.eqb_spec nnx 0) as [_|X]; [|exfalso; exact (X HN)].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33a90. meq_acc SKW.
fin_exit HS.
+ assert (HN : nnx <> 0) by (clear - Hc0 DR R37; zbranch Hc0; apply Z.eqb_neq in Hc0; exact Hc0).
destruct (Z.eqb_spec nnx 0) as [X|_]; [exfalso; exact (HN X)|].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33c04. meq_acc SKW.
fin_loop HS.
- (* count(cur) + count(nx) <= 1021: merge *)
assert (HA : ccnt + ncnt <= 1021) by (clear - Hc DR R34 R35; zbranch Hc; apply Z.ltb_ge in Hc; zlia).
unfold postH. destruct (Z.ltb_spec 1021 (ccnt + ncnt)) as [X|_]; [exfalso; clear - X HA; zlia|].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
(* the CHECK_GE branch 0x33c1c (size(cur) >> 13 = 0) is decided by the fact size(cur) >= 8192 (atom 36) *)
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
+ assert (HN : ncnt = 0) by (clear - Hc0 DR R35; zbranch Hc0; apply Z.eqb_eq in Hc0; exact Hc0).
destruct (Z.eqb_spec ncnt 0) as [_|X]; [|exfalso; exact (X HN)].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33c50. meq_acc SKW.
fin_loop HS.
+ assert (HN : ncnt <> 0) by (clear - Hc0 DR R35; zbranch Hc0; apply Z.eqb_neq in Hc0; exact Hc0).
destruct (Z.eqb_spec ncnt 0) as [X|_]; [exfalso; exact (HN X)|].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33c3c. meq_acc SKW.
fin_loop HS.
Qed.
End WK.
End d.
