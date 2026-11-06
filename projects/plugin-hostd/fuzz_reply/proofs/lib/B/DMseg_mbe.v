(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMseg_mbe.v (commit fe876300d09, Quarantine::Drain walk set; file sha256 33517ecfd409) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 9 image addresses moved by code-verified function pairs (8 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py), and 15 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMseg_mbe.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (24 numerals; per-numeral report). *)
(* MergeBatches' entry, 0x33bcc -> the loop head 0x33c04 (frame 0x10).
     0x33bcc sp -= 16; 0x33bd0 sd ra,8(sp); 0x33bd4 ld a4,8(a0) = the list's first batch [lfirst];
     0x33bd8 beqz a4 -> 0x33d00 (the empty list; excluded: lfirst is a batch object, so lfirst <> 0);
     0x33bdc ld t0,0(a4) = its successor [fnx]; 0x33be0 beqz t0 -> 0x33d00 (a one-batch list; excluded by the
     premise fnx <> 0); 0x33be4-0x33bf0 a2 := 0, a5 := 1021, a6 := -8192, a7 := 8192; 0x33bf4 j 0x33c04.
   Both beqz are decided by the atoms' ranges (both >= kHighMemBeg), so the two exits are unreachable here. *)
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
Definition M8192 : Z := 18446744073709543424.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WK.
Variables (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (lfirst fnx : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x33bcc) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Definition XW : list word := [ w64 lfirst; w64 fnx ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma Eq32 : ew E0 32 = w64 lfirst. Proof. reflexivity. Qed.
Lemma Eq33 : ew E0 33 = w64 fnx. Proof. reflexivity. Qed.
(* the new frame (ra at sp0 - 8), the list's first-batch word, the first batch's next word *)
Definition R_STK : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition R_LH : YP09.region :=
YP09.mkRegion None (A_QUAR + 160) (A_QUAR + 176) (A_QUAR + 160) (A_QUAR + 160)
[YP09.mkChunk (A_QUAR + 168) (CVal 8 (SOff 32%nat 0))].
Definition R_F : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33%nat 0))].
Definition REG0 : smem := [ R_STK; R_LH; R_F ].
Definition FFE : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + 16) kHighMemEnd 4);
(32%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(33%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13) ] [] [].
Definition SR0 : list sv :=
sr_set (sr_set sr_atoms 1%bv (SLit 0x33a90)) 10%bv (SLit (A_QUAR + 160)).
Definition SS0 : sstate := mkSS 0x33bcc SR0 REG0 None FFE.
Record free_hyps : Prop := FreeHyps {
fh_Hsp : kHighMemBeg + 16 <= sp0 /\ sp0 <= kHighMemEnd;
fh_Hsp_al : sp0 mod 16 = 0;
fh_Hra : getr regs0 1 = w64 0x33a90;
fh_Hf : kHighMemBeg <= lfirst /\ lfirst + kBatchBytes <= ASAN_CEIL /\ lfirst mod 8192 = 0;
fh_Hn : kHighMemBeg <= fnx /\ fnx + kBatchBytes <= ASAN_CEIL /\ fnx mod 8192 = 0;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x33bcc) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [Hsp Hsp_al Hra Hf Hn SEED].
Lemma derived_ranges :
kHighMemBeg + 16 <= sp0 /\ sp0 <= kHighMemEnd /\ kHighMemBeg <= lfirst /\ lfirst + kBatchBytes <= ASAN_CEIL /\
kHighMemBeg <= fnx /\ fnx + kBatchBytes <= ASAN_CEIL /\ ASAN_CEIL <= CEIL_MAX.
Proof.
open_FH. destruct Hsp as [S1 S2]. destruct Hf as (F1 & F2 & _). destruct Hn as (N1 & N2 & _).
clear - S1 S2 F1 F2 N1 N2. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop := sp0 - 16 <= a < sp0.
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
Definition WSK : list (option nat * Z * Z) := [(Some 2%nat, -16, 0)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK.
Proof.
intros E HE t a Hin Hr. unfold WSK in Hin. cbn [In] in Hin. destruct Hin as [<-|[]].
cbn [fst snd base_val] in Hr. rewrite HE in Hr by (cbv; lia). rewrite E2 in Hr. unfold WIN, sp0. lia.
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
(* every register but ra (the shell pins it to the literal 0x33a90), sp, a2, a4, a5, a6, a7 and t0 *)
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition at_MBH (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33c04) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 (sp0 - 16) /\ getr regs' 1 = w64 0x33a90 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 12 = w64 0 /\ getr regs' 14 = w64 lfirst /\ getr regs' 5 = w64 fnx /\
getr regs' 15 = w64 1021 /\ getr regs' 16 = w64 M8192 /\ getr regs' 17 = w64 8192 /\
MEQ mem' /\ (forall a, WIN a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (sp0 - 8) 8 0x33a90.

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
Ltac tA := cbn [base_val YP09.r_base]; rewrite ?Z.add_0_l; first [ reflexivity | zlia | numconst; zlia
| match goal with B : bv_unsigned (ew _ 2) = _ |- _ => rewrite B end; unfold sp0; zlia ].
Ltac zev_close := cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw; rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
unfold M8192 in *; zcanon_simp; zlia.
Ltac tV := first
[ reflexivity
| cbn [sv_denot]; apply bv_eq; unfold M8192, w64; vm_compute; reflexivity
| cbn [sv_denot]; rewrite ?Eq32, ?Eq33; unfold w64; rewrite ?Zbv_add_unsigned; first [ reflexivity | f_equal; zlia ]
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
Ltac sregs HS := intros r Hr; cbn [SREGS In] in Hr;
repeat match type of Hr with
| _ = r \/ _ => let E := fresh "E" in destruct Hr as [E|Hr]; [subst r; reg_keep HS|]
| _ = r => subst r; reg_keep HS
| False => destruct Hr
end.
Ltac off_by tac := first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold TFIB_IMG_END; tac ].

Lemma segE : SRr tfibsegs W cfg0 at_MBH.
Proof.
open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof derived_ranges as DR.
lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof MEQ_0 as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (intros; reflexivity).
pose proof (WSK_ok E0 HE0) as SKW.
assert (R32 : rho_of E0 32%nat = lfirst) by (unfold rho_of; rewrite Eq32; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (R33 : rho_of E0 33%nat = fnx) by (unfold rho_of; rewrite Eq33; unfold w64; apply unsigned_lit_small; clear - DR; numconst; zlia).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
srr_run_to_sh tfibtbl_rtG_ok HS 0x33c04. meq_acc SKW.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR;
apply SRr_ret; split; [reflexivity|];
eexists (ms_regs msx), (ms_mem msx), _;
split; [rewrite HshR at 1; reflexivity|];
split; [reg_val HS (2%bv : bv 5)|];
split; [first [reg_lit HS (1%bv : bv 5) | reg_val HS (1%bv : bv 5)]|];
split; [sregs HS|];
split; [first [reg_lit HS (10%bv : bv 5) | reg_val HS (10%bv : bv 5)]|];
split; [reg_val HS (12%bv : bv 5)|];
split; [reg_val HS (14%bv : bv 5)|];
split; [reg_val HS (5%bv : bv 5)|];
split; [reg_val HS (15%bv : bv 5)|];
split; [reg_val HS (16%bv : bv 5)|];
split; [reg_val HS (17%bv : bv 5)|];
split; [assumption|];
split; [intros a Ha Hh; unfold WIN in Ha; eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS);
  [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV2; unfold sp0 in *; clear - Ha; zlia
  | off_by ltac:(clear - Ha Hh DR; unfold sp0 in *; numconst; zlia)]|];
memvo HS 0%nat (-8); [tA | tV | tR]
end.
Qed.
End WK.
End d.
