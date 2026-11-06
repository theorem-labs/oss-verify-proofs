(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMseg_rj.v (commit 68fe993efc49, Quarantine::Drain walk set; file sha256 83e1ef777ded) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 7 image addresses moved by code-verified function pairs (6 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 12 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMseg_rj.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (19 numerals; per-numeral report). *)
(* Recycle after MergeBatches returns: 0x33a90 -> the dequeue loop head 0x33ae4, or (nothing left to dequeue)
   -> DoRecycle's entry 0x33d50.

   At 0x33a90 the saved registers hold Recycle's arguments (s0 = inst + 0xa0 = A_QUAR + 160, s1 = kQuarantineMin,
   s2 = A_QUAR, s3 = Drain's a3, s4 = ly_T + t_cache; DMsegD.at_MB).  The code restores a0..a3, RELOADS the list's
   count from 0(s0) (the merge changed it), reads the temp list's count and last from Recycle's frame and the list's
   bytes from 0xb8(a0), and tests kQuarantineMin >= bytes:
   - no: 0x33ab4 t0 := the list's first batch, 0x33ab8 j 0x33ae4 [at_RJL], the released dequeue loop's head
     (YFgl's shell: a4 = temp count, a5 = temp last, a6 = list count, t0 = first);
   - yes: 0x33b40-0x33b4c unlock both mutex bytes, 0x33b50 a1 := sp, 0x33b54 jal DoRecycle [at_RJX].
   The segment writes only the two mutex bytes (on the second path). *)
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
kBatchBytes, kBatchSlots, TFIB_TP, A_QUAR, A_ALLOCATOR, o_quar, kQuarantineMin, kQuarantineMax in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (lcnt lfirst lbytes tcnt tlast : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33a90) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Definition XW : list word := [ w64 lcnt; w64 lfirst; w64 lbytes; w64 tcnt; w64 tlast ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma Eq32 : ew E0 32 = w64 lcnt. Proof. reflexivity. Qed.
Lemma Eq33 : ew E0 33 = w64 lfirst. Proof. reflexivity. Qed.
Lemma Eq34 : ew E0 34 = w64 lbytes. Proof. reflexivity. Qed.
Lemma Eq35 : ew E0 35 = w64 tcnt. Proof. reflexivity. Qed.
Lemma Eq36 : ew E0 36 = w64 tlast. Proof. reflexivity. Qed.
(* the mutex word (both locks held), the list's header, the temp list's header on Recycle's frame *)
Definition R_QW : YP09.region :=
YP09.mkRegion None (A_QUAR + 152) (A_QUAR + 156) (A_QUAR + 152) (A_QUAR + 156)
[YP09.mkChunk (A_QUAR + 152) (CVal 1 (SLit 1)); YP09.mkChunk (A_QUAR + 153) (CVal 1 (SLit 1)); YP09.mkChunk (A_QUAR + 154) (CZero 2)].
Definition R_LH : YP09.region :=
YP09.mkRegion None (A_QUAR + 160) (A_QUAR + 192) (A_QUAR + 160) (A_QUAR + 160)
[YP09.mkChunk (A_QUAR + 160) (CVal 8 (SOff 32%nat 0)); YP09.mkChunk (A_QUAR + 168) (CVal 8 (SOff 33%nat 0));
YP09.mkChunk (A_QUAR + 184) (CVal 8 (SOff 34%nat 0))].
Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 32 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35%nat 0)); YP09.mkChunk 16 (CVal 8 (SOff 36%nat 0))].
Definition REG0 : smem := [ R_QW; R_LH; R_STK ].
Definition FFR : facts := mkFacts
[ (2%nat, mkAF kHighMemBeg (kHighMemEnd - 32) 4);
(32%nat, mkAF 0 (2 ^ 40) 0);
(33%nat, mkAF 0 CEIL_MAX 13);
(34%nat, mkAF 0 (2 ^ 31) 0);
(35%nat, mkAF 0 (2 ^ 40) 0);
(36%nat, mkAF 0 CEIL_MAX 13) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set (sr_set sr_atoms 8%bv (SLit (A_QUAR + 160))) 9%bv (SLit kQuarantineMin)) 18%bv (SLit A_QUAR).
Definition SS0 : sstate := mkSS 0x33a90 SR0 REG0 None FFR.
Record free_hyps : Prop := FreeHyps {
fh_Hsp : kHighMemBeg <= sp0 /\ sp0 + 32 <= kHighMemEnd;
fh_Hsp_al : sp0 mod 16 = 0;
fh_Hl : 0 <= lcnt <= 2 ^ 40 /\ 0 <= lfirst < ASAN_CEIL /\ lfirst mod 8192 = 0 /\ 0 <= lbytes <= 2 ^ 31;
fh_Ht : 0 <= tcnt <= 2 ^ 40 /\ 0 <= tlast < ASAN_CEIL /\ tlast mod 8192 = 0;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33a90) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hsp Hsp_al Hl Ht SEED].
Lemma derived_ranges :
kHighMemBeg <= sp0 /\ sp0 + 32 <= kHighMemEnd /\ 0 <= lcnt <= 2 ^ 40 /\ 0 <= lfirst < ASAN_CEIL /\
0 <= lbytes <= 2 ^ 31 /\ 0 <= tcnt <= 2 ^ 40 /\ 0 <= tlast < ASAN_CEIL /\ ASAN_CEIL <= CEIL_MAX.
Proof.
open_FH. destruct Hsp as [S1 S2]. destruct Hl as (L1 & L2 & _ & L4). destruct Ht as (T1 & T2 & _).
clear - S1 S2 L1 L2 L4 T1 T2. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop := A_QUAR + 152 <= a < A_QUAR + 156.
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
Definition WSK : list (option nat * Z * Z) := [(None, A_QUAR + 152, A_QUAR + 156)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK_ok : forall E : env, sk_ok E WSK.
Proof. intros E t a Hin Hr. unfold WSK in Hin. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. unfold WIN. lia. Qed.
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
(* the registers both ends keep from 0x33a90 (ra is kept on the loop path, set by the call on the other) *)
Definition SREGS : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_RJL (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ kQuarantineMin < lbytes /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33ae4) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 8 = w64 (A_QUAR + 160) /\ getr regs' 9 = w64 kQuarantineMin /\ getr regs' 18 = w64 A_QUAR /\
getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = w64 kQuarantineMin /\
getr regs' 12 = getr regs0 20 /\ getr regs' 13 = getr regs0 19 /\
getr regs' 14 = w64 tcnt /\ getr regs' 15 = w64 tlast /\ getr regs' 16 = w64 lcnt /\ getr regs' 5 = w64 lfirst /\
getr regs' 1 = getr regs0 1 /\ MEQ mem'.
Definition at_RJX (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ lbytes <= kQuarantineMin /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_DoRecycle) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 A_QUAR /\ getr regs' 11 = getr regs0 2 /\
getr regs' 12 = getr regs0 20 /\ getr regs' 13 = getr regs0 19 /\ getr regs' 1 = w64 0x33b58 /\
MEQ mem' /\ (forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs (mrestrict (w_H W) mem') a = Some (Z_to_bv 8 0)).
Definition postR : world tfibsegs -> config -> Prop := if kQuarantineMin <? lbytes then at_RJL else at_RJX.

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
Ltac czero HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := eval cbv in (YP09.r_chunks rg) in
let j := chunk_index cs off 0%nat in
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
eapply (st_ok_chunk_zero (w_H W) E0 _ msx i _ j _ _ _ HS); [reflexivity | reflexivity | cbn [base_val YP09.r_base]] end end end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; zcanon_simp; intros Hc.
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l; first [ reflexivity | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; unfold sp0; zlia ].
Ltac tV := first
[ reflexivity
| cbn [sv_denot]; rewrite ?Eq32, ?Eq33, ?Eq34, ?Eq35, ?Eq36; unfold w64; rewrite ?Zbv_add_unsigned; first [ reflexivity | f_equal; zlia ] ].
Ltac tR := first [ zlia | numconst; zlia | apply u64_range ].
Ltac reg_lit HS r := let Q := fresh "Q" in rreg HS r Q; rewrite Q; reflexivity.
Ltac reg_entry HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ apply Er; reflexivity | cbn [sv_denot]; rewrite (Er k r eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned ].
Ltac reg_val HS r := first [ let Q := fresh "Q" in rreg HS r Q; rewrite Q; tV | reg_entry HS r 0%nat ].
Ltac reg_keep HS := lazymatch goal with |- getr _ ?r = getr _ _ =>
let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in reg_entry HS r k end.
Ltac sregs HS := intros r Hr; cbn [SREGS In] in Hr;
repeat match type of Hr with
| _ = r \/ _ => let E := fresh "E" in destruct Hr as [E|Hr]; [subst r; reg_keep HS|]
| _ = r => subst r; reg_keep HS
| False => destruct Hr
end.

Lemma segR : SRr tfibsegs W cfg0 postR.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ. pose proof (WSK_ok E0) as SKW.
assert (R32 : rho_of E0 32%nat = lcnt) by (unfold rho_of; rewrite Eq32; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R33 : rho_of E0 33%nat = lfirst) by (unfold rho_of; rewrite Eq33; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R34 : rho_of E0 34%nat = lbytes) by (unfold rho_of; rewrite Eq34; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R35 : rho_of E0 35%nat = tcnt) by (unfold rho_of; rewrite Eq35; unfold w64; apply unsigned_lit_small; clear - DR; zlia).
assert (R36 : rho_of E0 36%nat = tlast) by (unfold rho_of; rewrite Eq36; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
srr_run_sh tfibtbl_rtG_ok HS. meq_acc SKW.
srr_branch_sh tfibtbl_rtG_ok HS.
- (* bgeu kQuarantineMin, bytes: nothing to dequeue *)
assert (HLE : lbytes <= kQuarantineMin) by (clear - Hc DR R34; zbranch Hc; apply Bool.negb_true_iff in Hc; apply Z.ltb_ge in Hc; numconst; zlia).
unfold postR. destruct (Z.ltb_spec kQuarantineMin lbytes) as [X|_]; [exfalso; clear - X HLE; zlia|].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33d50. meq_acc SKW.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [exact HLE|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_entry HS (2%bv : bv 5) 2%nat|];
split; [sregs HS|];
split; [first [reg_lit HS (10%bv : bv 5) | reg_val HS (10%bv : bv 5)]|];
split; [let Q := fresh "Q" in rreg HS (11%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite E2; reflexivity|];
split; [reg_entry HS (12%bv : bv 5) 20%nat|];
split; [reg_entry HS (13%bv : bv 5) 19%nat|];
split; [first [reg_lit HS (1%bv : bv 5) | reg_val HS (1%bv : bv 5)]|];
split; [assumption|];
intros a Ha;
assert (C : a = A_QUAR + 152 \/ a = A_QUAR + 153 \/ A_QUAR + 154 <= a < A_QUAR + 156) by (clear - Ha; zlia);
destruct C as [-> |[-> |C]];
[ let V := fresh "V" in
  assert (V : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 152) 1 0) by (memvo HS 0%nat (A_QUAR + 152); [tA | tV | zlia]);
  apply (proj1 (val_mem1_byte _ _ _)) in V; exact V
| let V := fresh "V" in
  assert (V : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msx)) (A_QUAR + 153) 1 0) by (memvo HS 0%nat (A_QUAR + 153); [tA | tV | zlia]);
  apply (proj1 (val_mem1_byte _ _ _)) in V; exact V
| czero HS 0%nat (A_QUAR + 154); clear - C; numconst; zlia ]
end.
- (* the list still has more than kQuarantineMin bytes: the dequeue loop *)
assert (HGT : kQuarantineMin < lbytes) by (clear - Hc DR R34; zbranch Hc; apply Bool.negb_false_iff in Hc; apply Z.ltb_lt in Hc; numconst; zlia).
unfold postR. destruct (Z.ltb_spec kQuarantineMin lbytes) as [_|X]; [|exfalso; clear - X HGT; zlia].
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_to_sh tfibtbl_rtG_ok HS 0x33ae4. meq_acc SKW.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|]; split; [exact HGT|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_entry HS (2%bv : bv 5) 2%nat|];
split; [sregs HS|];
split; [first [reg_lit HS (8%bv : bv 5) | reg_val HS (8%bv : bv 5)]|];
split; [first [reg_lit HS (9%bv : bv 5) | reg_val HS (9%bv : bv 5)]|];
split; [first [reg_lit HS (18%bv : bv 5) | reg_val HS (18%bv : bv 5)]|];
split; [first [reg_lit HS (10%bv : bv 5) | reg_val HS (10%bv : bv 5)]|];
split; [first [reg_lit HS (11%bv : bv 5) | reg_val HS (11%bv : bv 5)]|];
split; [reg_entry HS (12%bv : bv 5) 20%nat|];
split; [reg_entry HS (13%bv : bv 5) 19%nat|];
split; [reg_val HS (14%bv : bv 5)|];
split; [reg_val HS (15%bv : bv 5)|];
split; [reg_val HS (16%bv : bv 5)|];
split; [reg_val HS (5%bv : bv 5)|];
split; [reg_entry HS (1%bv : bv 5) 1%nat|];
assumption
end.
Qed.
End WK.
End d.
