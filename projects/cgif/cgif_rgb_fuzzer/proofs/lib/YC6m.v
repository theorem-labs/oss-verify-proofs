(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC6k YC6t YC7c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma hk_av_byte : forall H (m : word -> option byte) a v,
mbyte trasegs (mrestrict H m) a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> aview trasegs H m a = Some v.
Proof.
intros H m a v Hb Hv. unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma colour_ext : forall a b : colour, cR a = cR b -> cG a = cG b -> cB a = cB b -> a = b.
Proof. intros [[ar ag] ab] [[br bg] bb]. unfold cR, cG, cB. cbn [fst snd]. intros -> -> ->. reflexivity. Qed.
Section H2.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_tra.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 + 2 * ESTACK <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Let HSTK512 : 512 <= STK. Proof. unfold ESTACK in HSTK. lia. Qed.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BR := (at_BR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK512 Hfmt HN Himgl HimgP).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation pxc := (pxc fmt imgl).
Lemma hspill_kept : forall (W : world trasegs) (mem mem' : word -> option byte) i ha,
hspill s1v W mem i ha ->
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
hspill s1v W mem' i ha.
Proof.
intros W mem mem' i ha [H72 H56] Hk. split.
- apply (rg_val_mem_blk_kept (w_H W) (w_H W) mem mem' (s1v + 72) 8 _ 8 _ H72); [|lia|lia]. intros j Hj. apply Hk. lia.
- apply (rg_val_mem_blk_kept (w_H W) (w_H W) mem mem' (s1v + 56) 8 _ 8 _ H56); [|lia|lia]. intros j Hj. apply Hk. lia.
Qed.
Lemma hk_pix_views : forall (W : world trasegs) (mem : word -> option byte) i, arr8 trasegs (mrestrict (w_H W) mem) img imgl -> 0 <= i < N ->
aview trasegs (w_H W) mem (img + fmt * i) = Some (cR (pxc i)) /\ aview trasegs (w_H W) mem (img + fmt * i + 1) = Some (cG (pxc i)) /\
aview trasegs (w_H W) mem (img + fmt * i + 2) = Some (cB (pxc i)) /\ colour_ok (pxc i).
Proof.
intros W mem i Himg Hi.
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4) by (destruct Hfmt as [Hf | Hf]; rewrite Hf; clear - Hi; lia).
assert (PB : forall j, 0 <= j < 3 -> mbyte trasegs (mrestrict (w_H W) mem) (img + fmt * i + j) = Some (Z_to_bv 8 (getz imgl (fmt * i + j))) /\ 0 <= getz imgl (fmt * i + j) < 256).
{ intros j Hj. rewrite <- Z.add_assoc. apply (arr8_getz trasegs _ img imgl); [exact Himg | rewrite Himgl; clear - Hfi Hj; lia]. }
destruct (PB 0 ltac:(lia)) as [P0 R0]. replace (fmt * i + 0) with (fmt * i) in P0, R0 by lia. rewrite Z.add_0_r in P0. destruct (PB 1 ltac:(lia)) as [P1 R1]. destruct (PB 2 ltac:(lia)) as [P2 R2].
unfold YC7c.pxc, colour_ok, cR, cG, cB, mkcol. cbn [fst snd].
split; [apply hk_av_byte; assumption|]. split; [apply hk_av_byte; assumption|]. split; [apply hk_av_byte; assumption|]. lia.
Qed.
Lemma hk_key_views : forall (W : world trasegs) (mem : word -> option byte) keys kys h, arr8 trasegs (mrestrict (w_H W) mem) keys kys -> 0 <= h -> 3 * h + 3 <= zlen kys ->
aview trasegs (w_H W) mem (keys + 3 * h) = Some (cR (col_at kys h)) /\ aview trasegs (w_H W) mem (keys + 3 * h + 1) = Some (cG (col_at kys h)) /\
aview trasegs (w_H W) mem (keys + 3 * h + 2) = Some (cB (col_at kys h)).
Proof.
intros W mem keys kys h Hk Hh Hlen.
destruct (arr8_getz trasegs _ keys kys (3 * h) Hk ltac:(lia)) as [B0 R0].
destruct (arr8_getz trasegs _ keys kys (3 * h + 1) Hk ltac:(lia)) as [B1 R1].
destruct (arr8_getz trasegs _ keys kys (3 * h + 2) Hk ltac:(lia)) as [B2 R2].
unfold col_at, cR, cG, cB, mkcol. cbn [fst snd].
split; [apply hk_av_byte; assumption|].
split; [replace (keys + 3 * h + 1) with (keys + (3 * h + 1)) by lia; apply hk_av_byte; assumption|].
replace (keys + 3 * h + 2) with (keys + (3 * h + 2)) by lia; apply hk_av_byte; assumption.
Qed.
Lemma hl_bcmp : forall lyc Sc W regs mem md k C i ha j,
at_BC lyc Sc W regs mem md k C i ha j ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_bcmp_tra) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 v,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_BR) mem2 (seg_rom trasegs)) md2 /\ at_BR lyc Sc W regs2 mem2 md2 k C i ha j v).
Proof.
intros lyc Sc W regs mem md k C i ha j HAT.
destruct HAT as (HC & (Hi & Hha & Hop & G27) & Hz & Hsp & (G20 & G21 & G22 & G23 & G24 & G26) & (js & Hjs & Hj) & Hused & G10 & G11 & G12 & G1).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *.
set (T := ht_T (ac_H C)) in *. set (c := pxc i) in *. set (hj := cyc T (hash0 T c) j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; lia).
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
assert (Hkin : In (ac_h C, 3 * T) (ablocks B lyc Sc)).
{ apply (hcore_in_tbl B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ _ _ (proj1 HC)).
unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4) by (destruct Hfmt as [Hf | Hf]; rewrite Hf; clear - Hi; lia).
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfi; lia)) as [_ HrqI]. pose proof (req_size_pos (3 * T) ltac:(clear - RT1; lia)) as [_ HrqK].
eapply SRr_mono.
{ apply (hk_bcmp_call B LAWS ABCMP STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 HSTK lyc Sc W regs mem md k (img + fmt * i) (ac_h C + 3 * hj) 3 (Z_to_bv 64 HL_BR)
img (fmt * N) (ac_h C) (3 * T) HJ G10 G11 G12 ltac:(lia) G2 G3 G4 G1 ltac:(apply ret_ok_even; vm_compute; reflexivity) Himgin
ltac:(clear - Hfi; lia) ltac:(clear - Hfi HrqI; lia) Hkin ltac:(clear - Rhj; lia) ltac:(clear - Rhj HrqK; lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hout2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v. split; [reflexivity|].
assert (RK : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r) by (intros r Hr; exact (aregs_get regs regs2 r HP2 Hr)).
destruct (hcore_ceil B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK512 _ _ _ _ _ _ _ _ (proj1 HC)) as [Hceil H47].
pose proof (asan_consts) as (C1 & _).
split.
{ apply (HRS lyc Sc W regs mem md k C regs2 mem2 md2 HC HJ2).
- intros r Hr. apply RK. exact (hk_const_saved r Hr).
- intros a Ha _ Hn. exact (Hout2 a Ha Hn). }
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (RK 27%bv ltac:(unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate)); exact G27|].
split; [exact Hz|].
split; [apply (hspill_kept W mem mem2 i ha Hsp); intros a Ha; apply Hout2; [clear - Ha Hceil H47 C1; lia | clear - Ha; lia]|].
split.
{ assert (SV : forall r : bv 5, In r [20; 21; 22; 23; 24; 26]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. apply RK. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate|]). destruct Hr. }
unfold hprobe_regs. rewrite (SV 20%bv), (SV 21%bv), (SV 22%bv), (SV 23%bv), (SV 24%bv), (SV 26%bv) by (cbv; tauto). repeat split; assumption. }
split; [exists js; split; assumption|]. split; [exact Hused|]. split; [exact Hv|].
destruct (hk_pix_views W mem i Himg Hi) as (V0 & V1 & V2 & Cok).
destruct (hk_key_views W mem (ac_h C) (ht_keys (ac_H C)) hj Ah ltac:(lia) ltac:(rewrite L2; clear - Rhj; lia)) as (K0 & K1 & K2).
fold c in V0, V1, V2, Cok. unfold key. set (kc := col_at (ht_keys (ac_H C)) hj) in *.
rewrite Hcmp. split.
- intros Q. pose proof (Q 0 ltac:(lia)) as Q0. pose proof (Q 1 ltac:(lia)) as Q1. pose proof (Q 2 ltac:(lia)) as Q2. rewrite !Z.add_0_r in Q0.
rewrite V0, K0 in Q0. rewrite V1, K1 in Q1. rewrite V2, K2 in Q2. injection Q0 as Q0. injection Q1 as Q1. injection Q2 as Q2.
apply colour_ext; [exact (eq_sym Q0) | exact (eq_sym Q1) | exact (eq_sym Q2)].
- intros Hcc i0 Hi0. assert (Hi3 : i0 = 0 \/ i0 = 1 \/ i0 = 2) by lia.
destruct Hi3 as [-> | [-> | ->]]; [rewrite !Z.add_0_r, V0, K0 | rewrite V1, K1 | rewrite V2, K2]; f_equal; f_equal; symmetry; exact Hcc.
Qed.
End H2.
