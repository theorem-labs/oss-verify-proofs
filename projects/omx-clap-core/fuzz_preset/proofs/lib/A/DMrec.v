(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrec.v (commit 67deba317dfb, blob fbebf86b478d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 4 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFha AFhk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Module RZ.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Definition YFRAME : Z := 112.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFIB_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFIB_TP, TFIB_TSD,
A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax, YFRAME, kFreeArrayOffset in *.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (b nx bb sz qb lz : Z).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Definition XW : list word :=
[ w64 T; w64 0; w64 SB; w64 0; w64 0; w64 0; w64 0; w64 0; w64 b; w64 nx; w64 bb; w64 0; w64 0; w64 0; w64 sz; w64 qb; w64 0; w64 lz ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EqB : ew E0 40 = w64 b. Proof. reflexivity. Qed.
Lemma EqNX : ew E0 41 = w64 nx. Proof. reflexivity. Qed.
Lemma EqBB : ew E0 42 = w64 bb. Proof. reflexivity. Qed.
Lemma EqSZ : ew E0 46 = w64 sz. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 47 = w64 qb. Proof. reflexivity. Qed.
Lemma EqLZ : ew E0 49 = w64 lz. Proof. reflexivity. Qed.

Definition R_STK : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 (YFRAME + 32) YFRAME (YFRAME + 32)
[YP09.mkChunk 8 (CVal 8 (SOff 32%nat t_cache));
YP09.mkChunk (YFRAME + 0) (CVal 8 (SOff 46%nat 0)); YP09.mkChunk (YFRAME + 8) (CVal 8 (SOff 40%nat 0));
YP09.mkChunk (YFRAME + 16) (CVal 8 (SOff 49%nat 0)); YP09.mkChunk (YFRAME + 24) (CVal 8 (SOff 47%nat 0))].

Definition R_B : YP09.region :=
YP09.mkRegion (Some 40%nat) 0 24 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 41%nat 0)); YP09.mkChunk 8 (CVal 8 (SOff 42%nat 0)); YP09.mkChunk 16 (CVal 8 (SLit 0))].
Definition REG0 : smem := [ R_STK; R_B; fatom8 (A_ALLOCATOR + 32) 34%nat ].
Definition FFZ : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + DRSTACK - YFRAME) (kHighMemEnd - YFRAME - 32) 4);
(32%nat, mkAF 4096 (CEIL_MAX - 4096) 12);
(34%nat, mkAF kHighMemBeg CEIL_MAX 16);
(40%nat, mkAF kHighMemBeg (CEIL_MAX - 8192) 13);
(41%nat, mkAF 0 CEIL_MAX 13);
(42%nat, mkAF 0 (2 ^ 64 - 1) 0);
(46%nat, mkAF 1 (2 ^ 40) 0);
(47%nat, mkAF 0 (2 ^ 64 - 1) 0);
(49%nat, mkAF 0 CEIL_MAX 0) ] [] [].
Definition SS0 : sstate := mkSS 0x34750 AFha.SR0 REG0 None FFZ.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x34750) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hsp : ly_stk_lo ly + DRSTACK <= sp0 + YFRAME /\ sp0 + YFRAME + 32 <= ly_stk_hi ly;
fh_Hsp_al : sp0 mod 16 = 0;
fh_pres : forall a, sp0 + YFRAME <= a < sp0 + YFRAME + 32 -> apresent (w_H W) mem0 a;
fh_regs : getr regs0 8 = w64 (sp0 + YFRAME) /\ getr regs0 9 = w64 A_ALLOCATOR /\ getr regs0 18 = w64 (A_ALLOCATOR + 64) /\
getr regs0 19 = w64 (A_ALLOCATOR + 688) /\ getr regs0 21 = w64 (2 ^ 37) /\ getr regs0 10 = w64 sz;
fh_Hb : SB + region_off kBatchClass <= b /\ b + kBatchBytes <= SB + region_off kBatchClass + kFreeArrayOffset /\ b mod 8192 = 0;
fh_Hnx : 0 <= nx < ASAN_CEIL /\ nx mod 8192 = 0;
fh_Hby : 0 <= bb < 2 ^ 64 /\ 0 <= qb < 2 ^ 64;
fh_Hsz : 1 <= sz < 2 ^ 40;
fh_Hlz : 0 <= lz < ASAN_CEIL;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x34750) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hsp Hsp_al Hpres Hregs Hb Hnx Hby Hsz Hlz SEED].
Lemma LYB :
kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\ SB mod 65536 = 0 /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ T mod 4096 = 0.
Proof.
open_FH.
pose proof (lo_high ly LY) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) (Forall_nth_f _ _ 2 _ (lo_app ly LY) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LY) eq_refl eq_refl)) as ZT.
assert (ZT2 : ly_T ly + kThreadObjSize <= ASAN_CEIL) by (clear - ZT; unfold zone3 in ZT; lia).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in ly LY) as HSPC. pose proof (lo_space_al ly LY) as SAL.
pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
unfold zdisjoint in PSTK. cbn [fst snd] in *. unfold SB, T in *.
repeat match goal with |- _ /\ _ => split end; first [exact ZT | exact TAL | exact ZT2 | clear ZT; lia].
Qed.
Lemma derived_ranges :
kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL /\ SB mod 65536 = 0 /\ SB + 24 * 2 ^ 32 <= b /\ b + kBatchBytes <= SB + 24 * 2 ^ 32 + kFreeArrayOffset /\ b mod 8192 = 0 /\
0 <= nx < ASAN_CEIL /\ 0 <= bb < 2 ^ 64 /\ 0 <= qb < 2 ^ 64 /\ 1 <= sz < 2 ^ 40 /\ 0 <= lz < ASAN_CEIL /\
4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg + DRSTACK - YFRAME <= sp0 /\ sp0 + YFRAME + 32 <= kHighMemEnd.
Proof.
open_FH. pose proof LYB as LB. destruct Hb as (B1 & B2 & B3). destruct Hsp as [S1 S2].
assert (RO : region_off kBatchClass = 24 * 2 ^ 32) by reflexivity. rewrite RO in B1, B2.
clear - LB B1 B2 B3 S1 S2 Hnx Hby Hsz Hlz. numconst. repeat split; lia.
Qed.
Definition WIN (a : Z) : Prop := sp0 + YFRAME <= a < sp0 + YFRAME + 32.
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
Definition WSK0 : list (option nat * Z * Z) := [(Some 2%nat, YFRAME, YFRAME + 32)].
Definition sk_ok (E : env) (SK : list (option nat * Z * Z)) : Prop :=
forall t a, In t SK -> base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Lemma WSK0_ok : forall E : env, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> sk_ok E WSK0.
Proof.
intros E HE t a Hin Hr. unfold WSK0 in Hin. cbn [In] in Hin. unfold WIN. unfold aHAVf in *.
destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (cbv; lia). rewrite E2 in Hr. unfold sp0 in *. lia.
Qed.
Lemma windows_WIN : forall (E : env) SK rs a,
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E SK rs a HSK Hb0 Hw. destruct (in_wrange_windows E rs a Hw) as (b0 & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb0 _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (t & Hint & Hsub). exact (HSK t a Hint (win_sub_sound E a _ t Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> m x = mem0 x.
Lemma MEQ_frame : forall (E : env) SK rs (m m' : word -> option byte),
sk_ok E SK -> forallb (fun t => existsb (win_sub t) SK || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQ m -> MEQ m'.
Proof. intros E SK rs m m' HSK Hb0 HF M x Hx. rewrite <- (M x Hx). apply HF. intros Hw. apply Hx. exact (windows_WIN E SK rs _ HSK Hb0 Hw). Qed.
Lemma MEQ_0 : MEQ mem0. Proof. intros x _. reflexivity. Qed.
Definition SREGS : list (bv 5) := [3; 4; 8; 9; 18; 19; 21; 26; 27]%bv.
Definition LZn : Z := if nx =? 0 then 0 else lz.

Definition at_CD0 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 A_CDealloc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = getr regs0 2 /\ getr regs' 1 = w64 0x347d4 /\ (forall r : bv 5, In r SREGS -> getr regs' r = getr regs0 r) /\
getr regs' 10 = w64 (T + t_cache) /\ getr regs' 11 = w64 A_ALLOCATOR /\ getr regs' 12 = w64 kBatchClass /\ getr regs' 13 = w64 b /\
MEQ mem' /\
(forall a, WIN a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (sp0 + YFRAME) 8 (sz - 1) /\ val_mem tfibsegs m (sp0 + YFRAME + 8) 8 nx /\
val_mem tfibsegs m (sp0 + YFRAME + 16) 8 LZn /\ val_mem tfibsegs m (sp0 + YFRAME + 24) 8 (zcanon (qb - bb)).

Ltac off_by tac :=
first [ apply off_img_high; tac | unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |].
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
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac uncond HS := unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac unpin HS := cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := eval vm_compute in (ss_pc ss) in idtac "PC" pc;
let r := eval vm_compute in (sym_step_sh tfibsegs tfibtbl_rtG ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
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
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; apply Z_to_bv_bv_unsigned ].

End d.
End c.
End RZ.
