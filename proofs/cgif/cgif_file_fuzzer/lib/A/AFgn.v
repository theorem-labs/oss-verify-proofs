(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF,
TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section WF.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Definition tr : list Z := call_trace ly 0x52a6c regs0 ch.
Definition LENv : Z := Z.of_nat (length tr).
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 (ly_top ly); w64 LENv; w64 0xa7200; w64 0; w64 0; w64 SHADOW_OFF ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. exact (Er 10 10%bv eq_refl). Qed.
Lemma E4 : ew E0 4 = getr regs0 4. Proof. exact (Er 4 4%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.
Lemma EaIM : ew E0 37 = w64 0xa7200. Proof. reflexivity. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. reflexivity. Qed.
Definition AL (k x : Z) : Prop := x mod k = 0.
Let m0 := mrestrict (w_H W) mem0.
Definition REG0 : smem :=
[ YP09.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 [];
flit1 0xa6cd8 1; flit4 0xa6cfc 30; flit8 0x9df88 0x137b28; flit8 0x137b48 0x1e00010000;
flit1 0xa5860 1; flit4 0xa5864 0; flit1 0xa585c 1;
flit8 0x9df90 0xa37f8; flit8 0xa3828 0xbe00000000; flits8 0xa3840 [0x1000100000000; 0x101010101000001];
flit8 0x9df98 0xa5ff8; fatom8 0xa5ff8 aSHB;
flit8 0x9dfa0 0xa6ce8; flit8 0x9dfa8 0xa6cf0; flit8 0x9dfb0 0xa6ce0;
flit8 0xa6ce0 0x7fffffffffff; flit8 0xa6ce8 0; flit8 0xa6cf0 0;
flit8 0x9dfb8 0x9fe28; flit8 0x9fe28 0x97698;
flit8 0x9df78 0x135aa0; flit8 0x135aa0 4096;
flit8 0x137ac8 0;
flit8 0xa2cb0 0x10000000; flit8 0xa2cc0 0x100000;
flit8 (TFIB_TP - 88) TFIB_TSD; fatom8 TFIB_TSD aC;
YP09.mkRegion (Some aC) 0 160 0 0 [YP09.mkChunk 8 (CVal 4 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SOff aT 0))];
YP09.mkRegion (Some aT) 0 80 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aC 0)); YP09.mkChunk 8 (CVal 8 (SOff aTOP 0));
YP09.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YP09.mkChunk 40 (CVal 1 (SLit 0))];
YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YP09.mkChunk t_unwinding (CVal 1 (SLit 0))] ].
Definition FFN : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3);
(aSB, mkAF kHighMemBeg CEIL_MAX 16);
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aIM, mkAF 0xa7200 (0xa7200 + 8 * 0x7fff) 3);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12) ] [] [].
Definition SS0 : sstate := mkSS 0x5292c (sr_set (sr_set sr_atoms 4%bv (SLit TFIB_TP)) 10%bv (SLit 0)) REG0 None FFN.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x5292c) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Hp10 : getr regs0 10 = w64 0;
fh_Htp : getr regs0 4 = w64 TFIB_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hra4096 : 4096 <= bv_unsigned (getr regs0 1);
fh_Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : AL 16 sp0;
fh_Hch : if sp0 + 16 <? ly_top ly then
(if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [];
fh_HIAL : val_mem tfibsegs m0 TFIB_IAL_FLAG 1 (if ii then 1 else 0) /\ val_mem tfibsegs m0 (TFIB_IAL_FLAG + 1) 1 0 /\
(if ii then val_mem tfibsegs m0 TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16)
else val_mem tfibsegs m0 TFIB_IAL_W 8 0 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 0) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0));
fh_IA1 : tfib_ialloc_spec;
fh_U1 : tfib_unwind_spec;
fh_SEED : st_ok tfibsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 0x5292c) mem0 (seg_rom tfibsegs)))
}.
Hypothesis FH : free_hyps.
Ltac open_FH :=
pose proof (fh_LY FH) as LY;
pose proof (fh_IMG FH) as IMG;
pose proof (fh_Hp10 FH) as Hp10;
pose proof (fh_Htp FH) as Htp;
pose proof (fh_Hra FH) as Hra;
pose proof (fh_Hra4096 FH) as Hra4096;
pose proof (fh_Hsp FH) as Hsp;
pose proof (fh_Hsp_al FH) as Hsp_al;
pose proof (fh_Hch FH) as Hch;
pose proof (fh_HIAL FH) as HIAL;
pose proof (fh_IA1 FH) as IA1;
pose proof (fh_U1 FH) as U1;
pose proof (fh_SEED FH) as SEED.
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\
zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
open_FH.
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth_f _ _ 6 _ HA eq_refl) as IC.
pose proof (Forall_nth_f _ _ 4 _ HA eq_refl) as INB. pose proof (Forall_nth_f _ _ 5 _ HA eq_refl) as ISB.
cbn beta in IT, IC, INB, ISB. cbn [fst snd] in IT, IC, INB, ISB.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) IC (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(clear_all; unfold kNodesBlockSize; lia) INB (pairwise_ij_f _ _ 4 4 _ _ HD eq_refl eq_refl)) as ZNB.
pose proof (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(clear_all; unfold kStoreBlockSize; lia) ISB (pairwise_ij_f _ _ 5 3 _ _ HD eq_refl eq_refl)) as ZSB.
clear HA HD. unfold in_high in IP. cbn [fst snd] in IP. unfold T, SB in *.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
split; [clear - IP; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [clear - HSP; lia|]. split; [clear - HSP; lia|]. split; [clear - IP; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; lia|].
split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; lia|].
clear - T1 T2 T3 T4 T5 T6 T7. repeat split; lia.
Qed.
Lemma LYBD : zone3 (ly_D ly) 4096 /\ ly_D ly + 4096 <= ASAN_CEIL /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly).
Proof.
open_FH.
pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LY) eq_refl) as ID. cbn beta in ID. cbn [fst snd] in ID.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(clear_all; lia) ID (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & _ & DD & _).
do 6 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PD _].
do 4 (apply Forall_cons_iff in DT as [_ DT]). apply Forall_cons_iff in DT as [TD _].
apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in *. cbn [fst snd] in *. unfold T.
split; [exact ZD|]. split; [clear - ZD; unfold zone3 in ZD; lia|]. repeat split; assumption.
Qed.
Lemma LYD :
let P := (ly_prim ly, kPrimResvSize) in let Tt := (ly_T ly, kThreadObjSize) in let NB := (ly_NB ly, kNodesBlockSize) in
let SBb := (ly_SB ly, kStoreBlockSize) in let C := (ly_C ly, 256) in let STK := (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) in
(zdisjoint P Tt /\ zdisjoint P NB /\ zdisjoint P SBb /\ zdisjoint P C /\ zdisjoint P STK) /\
(zdisjoint Tt NB /\ zdisjoint Tt SBb /\ zdisjoint Tt C /\ zdisjoint Tt STK) /\
(zdisjoint NB SBb /\ zdisjoint NB C /\ zdisjoint NB STK) /\ (zdisjoint SBb C /\ zdisjoint SBb STK) /\ zdisjoint C STK.
Proof.
open_FH.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & DF & DNB & DSB & DC & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [PNB DP]. apply Forall_cons_iff in DP as [PSB DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TNB DT]. apply Forall_cons_iff in DT as [TSB DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DNB as [NBSB DNB]. apply Forall_cons_iff in DNB as [NBC DNB]. apply Forall_cons_iff in DNB as [_ DNB]. apply Forall_cons_iff in DNB as [NBSTK _].
apply Forall_cons_iff in DSB as [SBC DSB]. apply Forall_cons_iff in DSB as [_ DSB]. apply Forall_cons_iff in DSB as [SBSTK _]. apply Forall_cons_iff in DC as [_ DC]. apply Forall_cons_iff in DC as [CSTK _].
cbn zeta. repeat split; assumption.
Qed.
Lemma iv_vs_stack : forall lo len, zdisjoint (lo, len) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ->
ly_stk_lo ly <= sp0 - ASTACK -> sp0 <= ly_stk_hi ly -> lo + len <= sp0 - ASTACK \/ sp0 <= lo.
Proof. open_FH. intros lo len D H1 H2. unfold zdisjoint in D. cbn [fst snd] in D. lia. Qed.
Lemma stack_ivs :
(T + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - ASTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly) /\ (ly_NB ly + kNodesBlockSize <= sp0 - ASTACK \/ sp0 <= ly_NB ly) /\
(ly_SB ly + kStoreBlockSize <= sp0 - ASTACK \/ sp0 <= ly_SB ly).
Proof.
open_FH.
pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & T1 & T2 & T3 & T4 & T5).
pose proof LYD as ((_ & _ & _ & _ & PSTK) & (_ & _ & _ & TSTK) & (_ & _ & NBSTK) & (_ & SBSTK) & CSTK).
destruct Hsp as (S1 & S2 & S3).
assert (A1 : ly_stk_lo ly <= sp0 - ASTACK) by lia. assert (A2 : sp0 <= ly_stk_hi ly) by lia.
split; [exact (iv_vs_stack _ _ TSTK A1 A2)|]. split; [exact (iv_vs_stack _ _ PSTK A1 A2)|]. split; [exact (iv_vs_stack _ _ CSTK A1 A2)|].
split; [exact (iv_vs_stack _ _ NBSTK A1 A2)|]. exact (iv_vs_stack _ _ SBSTK A1 A2).
Qed.
Definition WIN (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Definition WSKEL : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, 0); (Some 32%nat, t_unwinding, t_unwinding + 1)].
Definition win_sub (t u : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst u)) && (snd (fst u) <=? snd (fst t)) && (snd t <=? snd u).
Lemma win_sub_sound : forall E a t u, win_sub t u = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst u)) + snd (fst u) <= a < base_val E (fst (fst u)) + snd u.
Proof.
open_FH.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Lemma WSKEL_WIN : forall (E : env) a t,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In t WSKEL ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Proof.
open_FH.
intros E a t HE Hin Hr. pose proof LYB as HF.
unfold WSKEL in Hin. cbn [In] in Hin. unfold WIN.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia);
rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
Qed.
Lemma windows_WIN : forall (E : env) rs a,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
open_FH.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
exact (WSKEL_WIN E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma frame_WIN : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WIN (bv_unsigned x) -> m' x = m x.
Proof. open_FH. intros E rs m m' HE Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_WIN E rs _ HE Hb Hw). Qed.
Lemma WIN_zone : forall a, WIN a -> ~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64.
Proof.
open_FH.
intros a Hw. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & HF). destruct Hsp as (S1 & S2 & S3).
unfold WIN in Hw. destruct Hw as [Hs | Ht].
- clear - Hs S1 S2 S3 HF. ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *. lia.
- clear - Ht F1. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *. lia.
Qed.
Lemma WIN_off : forall a, WIN a -> off_img a.
Proof. intros a Hw. destruct (WIN_zone a Hw) as (A & B & C). unfold off_img. clear - A B C. unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END in *. lia. Qed.
Lemma WIN_not_high : forall a, sp0 <= a < ly_top ly -> ~ WIN a.
Proof.
open_FH.
intros a Ha Hw. pose proof LYB as HF. destruct Hsp as (S1 & S2 & S3).
destruct Hw as [Hs | Ht].
- unfold ASTACK in *. lia.
- pose proof LYD as (_ & (_ & _ & _ & TSTK) & _ & _ & _). unfold zdisjoint in TSTK. cbn [fst snd] in TSTK.
unfold kThreadObjSize, ASTACK, t_unwinding in *. lia.
Qed.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. open_FH. intros E r rs H. induction rs as [|r' rs IH]; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx]. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
open_FH.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Lemma kept_of_frame_hi : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, off_img a -> apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
open_FH.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr; [exact Hh|]. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Lemma kept_of_vframe : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall a, ~ X a -> 0 <= a < 2 ^ 64 -> mbyte tfibsegs (mrestrict (w_H W) m1) a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
open_FH.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply Hfr; [exact Hno | exact Hr].
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _). exact (zone3_off_img _ _ a F7 Ha). Qed.
Lemma off_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). exact (zone3_off_img _ _ a F9 Ha). Qed.
Lemma off_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _). exact (zone3_off_img _ _ a F11 Ha). Qed.
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Lemma pres_off_of_frame : forall (m m1 : word -> option byte) (X : Z -> Prop),
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, X a -> TFIB_IMG_LO <= a) ->
(forall a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
forall a, off_img a -> apresent (w_H W) m a -> apresent (w_H W) m1 a.
Proof.
set (Hd := w_H W). clearbody Hd. clear_all.
intros m m1 X Hfr HX Hpr a [Hlo|Hhi] Hp; [|exact (Hpr a Hhi Hp)].
destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply Hfr.
rewrite unsigned_lit_small by (unfold TFIB_IMG_LO in Hlo; lia). intros HXa. pose proof (HX _ HXa). lia.
Qed.
Definition SKEL_TAIL : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0).
Definition IZONE (a : Z) : Prop := (TFIB_IAL_LO <= a < TFIB_IAL_HI) \/ (TFIB_IAL_FLAG <= a < TFIB_IAL_FLAG + 4).
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFIB_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFIB_IMG_LO)) /\
((hi <= TFIB_IAL_LO \/ TFIB_IAL_HI <= lo) /\ (hi <= TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= lo)).
Lemma zone_lit : forall lo hi wlo whi,
TFIB_IMG_LO <= lo -> hi <= TFIB_IMG_END -> (hi <= TFIB_IAL_LO \/ TFIB_IAL_HI <= lo) -> (hi <= TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= lo) ->
whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
open_FH. intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3 Hz5.
pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & T3 & T4 & T5). destruct Hsp as (S1 & S2 & S3).
unfold RFACTS. clear - Hz0 Hz1 Hz2 Hz3 Hz5 T1 T5 S1. numconst. unfold sp0 in *. lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
open_FH. intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (F1 & _).
pose proof stack_ivs as (IT & _).
unfold RFACTS. clear - Hz0 Hz1 Hz2 F1 IT. numconst. unfold T, sp0 in *. lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> (whi <= wlo \/ (ly_C ly <= wlo /\ whi <= ly_C ly + 256)) -> RFACTS lo hi wlo whi.
Proof.
open_FH. intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _).
pose proof stack_ivs as (_ & _ & IC & _).
unfold RFACTS. clear - Hz0 Hz1 Hz2 F7 IC. numconst. unfold sp0 in *. lia.
Qed.
Lemma tail_facts : forall (E : env) r,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAIL ->
let b := base_val E (YP09.r_base r) in
(b + YP09.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YP09.r_lo r) /\ 0 <= b + YP09.r_lo r /\ b + YP09.r_hi r <= 2 ^ 64 /\
(YP09.r_whi r <= YP09.r_wlo r \/ (TFIB_IMG_END <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= 2 ^ 64) \/ (0 <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= TFIB_IMG_LO)) /\
((b + YP09.r_hi r <= TFIB_IAL_LO \/ TFIB_IAL_HI <= b + YP09.r_lo r) /\ (b + YP09.r_hi r <= TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= b + YP09.r_lo r)).
Proof.
open_FH.
intros E r HE Hin. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & LB).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
let sk := eval vm_compute in SKEL_TAIL in change SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (clear - F1 F7; numconst; unfold T in *; lia).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R)
by (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END in *; lia) end.
all: first [ apply zone_lit; clear; numconst; unfold TFIB_TSD, TFIB_TP; lia
| apply zone_T; clear - F1 F2; numconst; unfold T in *; lia
| apply zone_C; clear - F7 F8; numconst; lia ].
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> ~ IZONE (bv_unsigned x) -> m x = mem0 x.
Definition IAL_POST (m : word -> option byte) : Prop :=
let m' := mrestrict (w_H W) m in
val_mem tfibsegs m' TFIB_IAL_FLAG 1 1 /\ val_mem tfibsegs m' (TFIB_IAL_FLAG + 1) 1 0 /\
val_mem tfibsegs m' TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m' (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0)).
Definition MEQI (m : word -> option byte) : Prop := MEQ m /\ IAL_POST m.
Lemma MEQI_frame : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQI m -> MEQI m'.
Proof.
open_FH. intros E rs m m' HE Hb HF [M I].
assert (LOWEQ : forall a, IZONE a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
unfold IZONE in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha.
pose proof (WIN_zone _ (windows_WIN E rs _ HE Hb Hw)) as (Hh & _). rewrite unsigned_lit_small in Hh by lia.
apply Hh. unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END. lia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply HF. intros Hw. apply Hx. exact (windows_WIN E rs _ HE Hb Hw).
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold IAL_POST.
assert (V : forall a (n : nat) v, (forall k, (k < n)%nat -> IZONE (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v).
{ intros a n v Hz Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. apply LOWEQ, Hz, Hk. }
unfold IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *.
split; [apply V; [intros k Hk; lia | exact I1]|]. split; [apply V; [intros k Hk; lia | exact I2]|].
split; [apply V; [intros k Hk; lia | exact I3]|]. split; [apply V; [intros k Hk; lia | exact I4]|].
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) m m' a) by (apply LOWEQ; lia). apply I5. exact Ha.
Qed.
Lemma notWIN_img : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ WIN a.
Proof. open_FH. intros a Ha Hw. destruct (WIN_zone a Hw) as (A & _). exact (A Ha). Qed.
Lemma notWIN_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WIN a.
Proof. open_FH. intros a Ha Hw. destruct (WIN_zone a Hw) as (_ & B & _). exact (B Ha). Qed.
Lemma notWIN_Thead : forall a, T <= a < T + 80 -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB. pose proof stack_ivs as (IT & _).
unfold WIN in Hw. unfold kThreadObjSize, ASTACK, t_unwinding in *. unfold T in *. lia.
Qed.
Lemma notWIN_C : forall a, ly_C ly <= a < ly_C ly + 256 -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB.
pose proof stack_ivs as (_ & _ & IC & _). pose proof LYD as (_ & (_ & _ & DTC & _) & _).
unfold zdisjoint in DTC. cbn [fst snd] in DTC.
unfold WIN in Hw. unfold kThreadObjSize, ASTACK, t_unwinding in *. unfold T in *. lia.
Qed.
Lemma notWIN_D : forall a, ly_D ly <= a < ly_D ly + 4096 -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB. pose proof LYBD as (D1 & D2 & PD & TD & DSTK).
unfold WIN in Hw. clear - Ha Hw DSTK TD Hsp. unfold ASTACK, t_unwinding, kThreadObjSize in *. unfold T in *. lia.
Qed.
Lemma notWIN_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB.
pose proof stack_ivs as (_ & _ & _ & INB & _). pose proof LYD as (_ & (DTNB & _) & _).
unfold zdisjoint in DTNB. cbn [fst snd] in DTNB.
unfold WIN in Hw. unfold kThreadObjSize, kNodesBlockSize, ASTACK, t_unwinding in *. unfold T in *. lia.
Qed.
Lemma notWIN_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB.
pose proof stack_ivs as (_ & _ & _ & _ & ISB). pose proof LYD as (_ & (_ & DTSB & _) & _).
unfold zdisjoint in DTSB. cbn [fst snd] in DTSB.
unfold WIN in Hw. unfold kThreadObjSize, kStoreBlockSize, ASTACK, t_unwinding in *. unfold T in *. lia.
Qed.
End WF.
End c.
