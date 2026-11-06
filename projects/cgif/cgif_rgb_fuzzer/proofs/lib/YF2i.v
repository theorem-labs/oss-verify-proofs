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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, zone3cases, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, IAL_STK, IFRAME, SHADOW_OFF,
TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W, TFX_IAL_FLAG, TFX_TP, TFX_TSD in *.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WF. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable ii : bool.
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Definition tr : list Z := call_trace ly (0x53244 + D_2c4) regs0 ch.
Definition LENv : Z := Z.of_nat (length tr).
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 (ly_top ly); w64 LENv; w64 (0xab3c0 + D_10c0); w64 0; w64 0; w64 SHADOW_OFF ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. img_exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. img_exact (Er 10 10%bv eq_refl). Qed.
Lemma E4 : ew E0 4 = getr regs0 4. Proof. img_exact (Er 4 4%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. img_refl. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. img_refl. Qed.
Lemma EaIM : ew E0 37 = w64 (0xab3c0 + D_10c0). Proof. img_refl. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. img_refl. Qed.
Definition AL (k x : Z) : Prop := x mod k = 0.
Let m0 := mrestrict (w_H W) mem0.
Definition REG0 {imgk : img} : smem :=
[ YQ0b.mkRegion (Some 2%nat) (- ASTACK) 0 (- ASTACK) 0 [];
flit1 (0xaae98 + D_10c0) 1; flit4 (0xaaebc + D_10c0) 30; flit8 (0xa2150 + D_10f0) (0x13bce8 + D_10c0); flit8 (0x13bd08 + D_10c0) 0x1e00010000;
flit1 (0xa9a20 + D_10c0) 1; flit4 (0xa9a24 + D_10c0) 0; flit1 (0xa9a1c + D_10c0) 1;
flit8 (0xa2158 + D_10f0) (0xa79b8 + D_10c0); flit8 (0xa79e8 + D_10c0) 0xbe00000000; flits8 (0xa7a00 + D_10c0) [0x1000100000000; 0x101010101000001];
flit8 (0xa2160 + D_10f0) (0xaa1b8 + D_10c0); fatom8 (0xaa1b8 + D_10c0) aSHB;
flit8 (0xa2168 + D_10f0) (0xaaea8 + D_10c0); flit8 (0xa2170 + D_10f0) (0xaaeb0 + D_10c0); flit8 (0xa2178 + D_10f0) (0xaaea0 + D_10c0);
flit8 (0xaaea0 + D_10c0) 0x7fffffffffff; flit8 (0xaaea8 + D_10c0) 0; flit8 (0xaaeb0 + D_10c0) 0;
flit8 (0xa2180 + D_10f0) (0xa4000 + D_10f0); flit8 (0xa4000 + D_10f0) (0x9b894 + D_10ec);
flit8 (0xa2140 + D_10f0) (0x139c60 + D_10c0); flit8 (0x139c60 + D_10c0) 4096;
flit8 (0x13bc88 + D_10c0) 0;
flit8 (0xa6e70 + D_10c0) 0x10000000; flit8 (0xa6e80 + D_10c0) 0x100000;
flit8 (TFX_TP - 88) TFX_TSD; fatom8 TFX_TSD aC;
YQ0b.mkRegion (Some aC) 0 160 0 0 [YQ0b.mkChunk 8 (CVal 4 (SLit 0)); YQ0b.mkChunk 152 (CVal 8 (SOff aT 0))];
YQ0b.mkRegion (Some aT) 0 80 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff aC 0)); YQ0b.mkChunk 8 (CVal 8 (SOff aTOP 0));
YQ0b.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YQ0b.mkChunk 40 (CVal 1 (SLit 0))];
YQ0b.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YQ0b.mkChunk t_unwinding (CVal 1 (SLit 0))] ].
Definition FFN {imgk : img} : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)    ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3);
(aSB, mkAF kHighMemBeg CEIL_MAX 16);
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aIM, mkAF (0xab3c0 + D_10c0) ((0xab3c0 + D_10c0) + 8 * 0x7fff) 3);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12) ] [] [].
Definition SS0 {imgk : img} : sstate := mkSS (0x53100 + D_2c4) (sr_set (sr_set sr_atoms 4%bv (SLit TFX_TP)) 10%bv (SLit 0)) REG0 None FFN.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53100 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Record free_hyps : Prop := FreeHyps {
fh_LY : layout_ok ly;
fh_IMG : img_cover ly;
fh_Hp10 : getr regs0 10 = w64 0;
fh_Htp : getr regs0 4 = w64 TFX_TP;
fh_Hra : YK0s.ret_ok (getr regs0 1);
fh_Hra4096 : 4096 <= bv_unsigned (getr regs0 1);
fh_Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly;
fh_Hsp_al : AL 16 sp0;
fh_Hch : if sp0 + 16 <? ly_top ly then
(if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfxsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [];
fh_HIAL : val_mem tfxsegs m0 TFX_IAL_FLAG 1 (if ii then 1 else 0) /\ val_mem tfxsegs m0 (TFX_IAL_FLAG + 1) 1 0 /\
(if ii then val_mem tfxsegs m0 TFX_IAL_W 8 4096 /\ val_mem tfxsegs m0 (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16)
else val_mem tfxsegs m0 TFX_IAL_W 8 0 /\ val_mem tfxsegs m0 (TFX_IAL_W + 8) 8 0) /\
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m0 a = Some (Z_to_bv 8 0));
fh_IA1 : tfx_ialloc_spec;
fh_U1 : tfx_unwind_spec;
fh_SEED : st_ok tfxsegs E0 SS0 (restrict (w_H W) (mkst regs0 (w64 (0x53100 + D_2c4)) mem0 (seg_rom tfxsegs)))
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
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear_all; img_lia)) IC (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(img_try (clear_all; unfold kNodesBlockSize; img_lia)) INB (pairwise_ij_f _ _ 4 4 _ _ HD eq_refl eq_refl)) as ZNB.
pose proof (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(img_try (clear_all; unfold kStoreBlockSize; img_lia)) ISB (pairwise_ij_f _ _ 5 3 _ _ HD eq_refl eq_refl)) as ZSB.
clear HA HD. unfold in_high in IP. cbn [fst snd] in IP. unfold T, SB in *.
split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|].
split; [img_try (clear - IP; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in *; img_lia)|]. split; [img_try (clear - HSP; img_lia)|]. split; [img_try (clear - HSP; img_lia)|]. split; [img_try (clear - IP; img_lia)|].
split; [img_try (img_exact ZC)|]. split; [img_try (clear - ZC; unfold zone3 in ZC; img_lia)|].
split; [img_try (img_exact ZNB)|]. split; [img_try (clear - ZNB; unfold zone3 in ZNB; img_lia)|].
split; [img_try (img_exact ZSB)|]. split; [img_try (clear - ZSB; unfold zone3 in ZSB; img_lia)|].
clear - T1 T2 T3 T4 T5 T6 T7. repeat split; img_lia.
Qed.
Lemma LYBD : zone3 (ly_D ly) 4096 /\ ly_D ly + 4096 <= ASAN_CEIL /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly).
Proof.
open_FH.
pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LY) eq_refl) as ID. cbn beta in ID. cbn [fst snd] in ID.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(img_try (clear_all; img_lia)) ID (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & _ & DD & _).
do 6 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PD _].
do 4 (apply Forall_cons_iff in DT as [_ DT]). apply Forall_cons_iff in DT as [TD _].
apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in *. cbn [fst snd] in *. unfold T.
split; [img_try (img_exact ZD)|]. split; [img_try (clear - ZD; unfold zone3 in ZD; img_lia)|]. repeat split; assumption.
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
Proof. open_FH. intros lo len D H1 H2. unfold zdisjoint in D. cbn [fst snd] in D. img_lia. Qed.
Lemma stack_ivs :
(T + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - ASTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly) /\ (ly_NB ly + kNodesBlockSize <= sp0 - ASTACK \/ sp0 <= ly_NB ly) /\
(ly_SB ly + kStoreBlockSize <= sp0 - ASTACK \/ sp0 <= ly_SB ly).
Proof.
open_FH.
pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & T1 & T2 & T3 & T4 & T5).
pose proof LYD as ((_ & _ & _ & _ & PSTK) & (_ & _ & _ & TSTK) & (_ & _ & NBSTK) & (_ & SBSTK) & CSTK).
destruct Hsp as (S1 & S2 & S3).
assert (A1 : ly_stk_lo ly <= sp0 - ASTACK) by img_lia. assert (A2 : sp0 <= ly_stk_hi ly) by img_lia.
split; [img_try (img_exact (iv_vs_stack _ _ TSTK A1 A2))|]. split; [img_try (img_exact (iv_vs_stack _ _ PSTK A1 A2))|]. split; [img_try (img_exact (iv_vs_stack _ _ CSTK A1 A2))|].
split; [img_try (img_exact (iv_vs_stack _ _ NBSTK A1 A2))|]. img_exact (iv_vs_stack _ _ SBSTK A1 A2).
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
- apply Nat.eqb_eq in H1. (subst; cbv beta). img_lia.
- img_lia.
Qed.
Lemma WSKEL_WIN : forall (E : env) a t,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In t WSKEL ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Proof.
open_FH.
intros E a t HE Hin Hr. pose proof LYB as HF.
unfold WSKEL in Hin. cbn [In] in Hin. unfold WIN.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, aHAVf in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (img_try ((img_case; cbv); img_lia));
rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia;
unfold sp0 in *; img_lia.
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
img_exact (WSKEL_WIN E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma frame_WIN : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WIN (bv_unsigned x) -> m' x = m x.
Proof. open_FH. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN E rs _ HE Hb Hw). Qed.
Lemma WIN_zone : forall a, WIN a -> ~ (TFX_IMG_LO <= a < TFX_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64.
Proof.
open_FH.
intros a Hw. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & HF). destruct Hsp as (S1 & S2 & S3).
unfold WIN in Hw. destruct Hw as [Hs | Ht].
- clear - Hs S1 S2 S3 HF. ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg in *. img_lia.
- clear - Ht F1. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg in *. img_lia.
Qed.
Lemma WIN_off : forall a, WIN a -> off_img a.
Proof. intros a Hw. destruct (WIN_zone a Hw) as (A & B & C). unfold off_img. clear - A B C. unfold zone3, kLowShadowBeg, TFX_IMG_LO, TFX_IMG_END in *. img_lia. Qed.
Lemma WIN_not_high : forall a, sp0 <= a < ly_top ly -> ~ WIN a.
Proof.
open_FH.
intros a Ha Hw. pose proof LYB as HF. destruct Hsp as (S1 & S2 & S3).
destruct Hw as [Hs | Ht].
- unfold ASTACK in *. img_lia.
- pose proof LYD as (_ & (_ & _ & _ & TSTK) & _ & _ & _). unfold zdisjoint in TSTK. cbn [fst snd] in TSTK.
unfold kThreadObjSize, ASTACK, t_unwinding in *. img_lia.
Qed.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. open_FH. intros E r rs H. induction rs as [|r' rs IH]; cbn; [img_try (img_exact I)|]. split; [img_try (img_apply H; left; img_refl) | img_try (img_apply IH; intros x Hx; img_apply H; right; img_exact Hx)]. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
region_kept tfxsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
open_FH.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. img_apply apresent_writable_off; [img_try (img_exact Hh)|]. img_apply Hpr. img_apply writable_off_apresent; [img_try (img_exact Hh) | img_try (img_exact Hw)].
Qed.
Lemma kept_of_frame_hi : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, off_img a -> apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
region_kept tfxsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
open_FH.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. img_apply apresent_writable_off; [img_try (img_exact Hh)|]. img_apply Hpr; [img_try (img_exact Hh)|]. img_apply writable_off_apresent; [img_try (img_exact Hh) | img_try (img_exact Hw)].
Qed.
Lemma kept_of_vframe : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall a, ~ X a -> 0 <= a < 2 ^ 64 -> mbyte tfxsegs (mrestrict (w_H W) m1) a = mbyte tfxsegs (mrestrict (w_H W) m) a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
region_kept tfxsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
open_FH.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply Hfr; [img_try (img_exact Hno) | img_try (img_exact Hr)].
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. img_apply apresent_writable_off; [img_try (img_exact Hh)|]. img_apply Hpr. img_apply writable_off_apresent; [img_try (img_exact Hh) | img_try (img_exact Hw)].
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _). img_exact (zone3_off_img _ _ a F7 Ha). Qed.
Lemma off_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). img_exact (zone3_off_img _ _ a F9 Ha). Qed.
Lemma off_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _). img_exact (zone3_off_img _ _ a F11 Ha). Qed.
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac
| img_apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Lemma pres_off_of_frame : forall (m m1 : word -> option byte) (X : Z -> Prop),
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, X a -> TFX_IMG_LO <= a) ->
(forall a, TFX_IMG_END <= a < 2 ^ 64 -> apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
forall a, off_img a -> apresent (w_H W) m a -> apresent (w_H W) m1 a.
Proof.
set (Hd := w_H W). clearbody Hd. clear_all.
intros m m1 X Hfr HX Hpr a [Hlo|Hhi] Hp; [|img_try (img_exact (Hpr a Hhi Hp))].
destruct Hp as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite <- Hb. img_apply Hfr.
rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_LO in Hlo; img_lia)). intros HXa. pose proof (HX _ HXa). img_lia.
Qed.
Definition SKEL_TAIL {imgk : img} : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0).
Definition IZONE {imgk : img} (a : Z) : Prop := (TFX_IAL_LO <= a < TFX_IAL_HI) \/ (TFX_IAL_FLAG <= a < TFX_IAL_FLAG + 4).
Definition RFACTS {imgk : img} (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFX_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFX_IMG_LO)) /\
((hi <= TFX_IAL_LO \/ TFX_IAL_HI <= lo) /\ (hi <= TFX_IAL_FLAG \/ TFX_IAL_FLAG + 4 <= lo)).
Lemma zone_lit : forall lo hi wlo whi,
TFX_IMG_LO <= lo -> hi <= TFX_IMG_END -> (hi <= TFX_IAL_LO \/ TFX_IAL_HI <= lo) -> (hi <= TFX_IAL_FLAG \/ TFX_IAL_FLAG + 4 <= lo) ->
whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
open_FH. intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3 Hz5.
pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & T3 & T4 & T5). destruct Hsp as (S1 & S2 & S3).
unfold RFACTS. clear - Hz0 Hz1 Hz2 Hz3 Hz5 T1 T5 S1. numconst. unfold sp0 in *. img_lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
open_FH. intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (F1 & _).
pose proof stack_ivs as (IT & _).
unfold RFACTS. clear - Hz0 Hz1 Hz2 F1 IT. numconst. unfold T, sp0 in *. img_lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> (whi <= wlo \/ (ly_C ly <= wlo /\ whi <= ly_C ly + 256)) -> RFACTS lo hi wlo whi.
Proof.
open_FH. intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _).
pose proof stack_ivs as (_ & _ & IC & _).
unfold RFACTS. clear - Hz0 Hz1 Hz2 F7 IC. numconst. unfold sp0 in *. img_lia.
Qed.
Lemma tail_facts : forall (E : env) r,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAIL ->
let b := base_val E (YQ0b.r_base r) in
(b + YQ0b.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YQ0b.r_lo r) /\ 0 <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= 2 ^ 64 /\
(YQ0b.r_whi r <= YQ0b.r_wlo r \/ (TFX_IMG_END <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= 2 ^ 64) \/ (0 <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= TFX_IMG_LO)) /\
((b + YQ0b.r_hi r <= TFX_IAL_LO \/ TFX_IAL_HI <= b + YQ0b.r_lo r) /\ (b + YQ0b.r_hi r <= TFX_IAL_FLAG \/ TFX_IAL_FLAG + 4 <= b + YQ0b.r_lo r)).
Proof.
open_FH.
intros E r HE Hin. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & LB).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi] in *.
let sk := img_ev constr:(SKEL_TAIL) in img_change SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <- <- <-)|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (img_try (clear - HE; (img_case; cbv); img_lia)); rewrite ?E2, ?EaT, ?EaC, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (img_try (clear - F1 F7; numconst; unfold T in *; img_lia)).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R)
by (img_try (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold zone3, kLowShadowBeg, TFX_IMG_LO, TFX_IMG_END in *; img_lia)) end.
all: first [ img_apply zone_lit; clear; numconst; unfold TFX_TSD, TFX_TP; img_lia
| img_apply zone_T; clear - F1 F2; numconst; unfold T in *; img_lia
| img_apply zone_C; clear - F7 F8; numconst; img_lia ].
Qed.
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> ~ IZONE (bv_unsigned x) -> m x = mem0 x.
Definition IAL_POST (m : word -> option byte) : Prop :=
let m' := mrestrict (w_H W) m in
val_mem tfxsegs m' TFX_IAL_FLAG 1 1 /\ val_mem tfxsegs m' (TFX_IAL_FLAG + 1) 1 0 /\
val_mem tfxsegs m' TFX_IAL_W 8 4096 /\ val_mem tfxsegs m' (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16) /\
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m' a = Some (Z_to_bv 8 0)).
Definition MEQI (m : word -> option byte) : Prop := MEQ m /\ IAL_POST m.
Lemma MEQI_frame : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQI m -> MEQI m'.
Proof.
open_FH. intros E rs m m' HE Hb HF [M I].
assert (LOWEQ : forall a, IZONE a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
{ intros a Ha. img_apply HF. intros Hw.
unfold IZONE in Ha. unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in Ha.
pose proof (WIN_zone _ (windows_WIN E rs _ HE Hb Hw)) as (Hh & _). rewrite unsigned_lit_small in Hh by img_lia.
img_apply Hh. unfold zone3, kLowShadowBeg, TFX_IMG_LO, TFX_IMG_END. img_lia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN E rs _ HE Hb Hw).
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold IAL_POST.
assert (V : forall a (n : nat) v, (forall k, (k < n)%nat -> IZONE (a + Z.of_nat k)) ->
val_mem tfxsegs (mrestrict (w_H W) m) a n v -> val_mem tfxsegs (mrestrict (w_H W) m') a n v).
{ intros a n v Hz Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k Hk. apply LOWEQ, Hz, Hk. }
unfold IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IAL_W in *.
split; [img_try (img_apply V; [intros k Hk; img_lia | img_exact I1])|]. split; [img_try (img_apply V; [intros k Hk; img_lia | img_exact I2])|].
split; [img_try (img_apply V; [intros k Hk; img_lia | img_exact I3])|]. split; [img_try (img_apply V; [intros k Hk; img_lia | img_exact I4])|].
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) m m' a) by (img_try (img_apply LOWEQ; img_lia)). img_apply I5. img_exact Ha.
Qed.
Lemma notWIN_img : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ~ WIN a.
Proof. open_FH. intros a Ha Hw. destruct (WIN_zone a Hw) as (A & _). img_exact (A Ha). Qed.
Lemma notWIN_shb : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WIN a.
Proof. open_FH. intros a Ha Hw. destruct (WIN_zone a Hw) as (_ & B & _). img_exact (B Ha). Qed.
Lemma notWIN_Thead : forall a, T <= a < T + 80 -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB. pose proof stack_ivs as (IT & _).
unfold WIN in Hw. unfold kThreadObjSize, ASTACK, t_unwinding in *. unfold T in *. img_lia.
Qed.
Lemma notWIN_C : forall a, ly_C ly <= a < ly_C ly + 256 -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB.
pose proof stack_ivs as (_ & _ & IC & _). pose proof LYD as (_ & (_ & _ & DTC & _) & _).
unfold zdisjoint in DTC. cbn [fst snd] in DTC.
unfold WIN in Hw. unfold kThreadObjSize, ASTACK, t_unwinding in *. unfold T in *. img_lia.
Qed.
Lemma notWIN_D : forall a, ly_D ly <= a < ly_D ly + 4096 -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB. pose proof LYBD as (D1 & D2 & PD & TD & DSTK).
unfold WIN in Hw. clear - Ha Hw DSTK TD Hsp. unfold ASTACK, t_unwinding, kThreadObjSize in *. unfold T in *. img_lia.
Qed.
Lemma notWIN_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB.
pose proof stack_ivs as (_ & _ & _ & INB & _). pose proof LYD as (_ & (DTNB & _) & _).
unfold zdisjoint in DTNB. cbn [fst snd] in DTNB.
unfold WIN in Hw. unfold kThreadObjSize, kNodesBlockSize, ASTACK, t_unwinding in *. unfold T in *. img_lia.
Qed.
Lemma notWIN_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> ~ WIN a.
Proof.
open_FH. intros a Ha Hw. pose proof LYB as LB.
pose proof stack_ivs as (_ & _ & _ & _ & ISB). pose proof LYD as (_ & (_ & DTSB & _) & _).
unfold zdisjoint in DTSB. cbn [fst snd] in DTSB.
unfold WIN in Hw. unfold kThreadObjSize, kStoreBlockSize, ASTACK, t_unwinding in *. unfold T in *. img_lia.
Qed.
End WF.
End c.
