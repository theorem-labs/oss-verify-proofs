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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition H_col (H : htab) (which : bool) (idx : Z) (c : colour) : htab :=
if which then mkHT (ht_frequ H) (set_col (ht_keys H) idx c) (ht_used H) (ht_pal H) (ht_colidx H) (ht_cnt H) (ht_T H)
else mkHT (ht_frequ H) (ht_keys H) (ht_used H) (set_col (ht_pal H) idx c) (ht_colidx H) (ht_cnt H) (ht_T H).
Definition C_col (C : acht) (which : bool) (idx : Z) (c : colour) : acht := ac_with C (H_col (ac_H C) which idx c) (ac_ent C).
Lemma hk_byte_of_av : forall H (m : word -> option byte) a v, aview trasegs H m a = Some v -> mbyte trasegs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Hv. unfold aview in Hv. destruct (mbyte trasegs (mrestrict H m) a) as [b|]; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section H5.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 + 2 * ESTACK <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Let HSTK512 : 512 <= STK. Proof. unfold ESTACK in HSTK. lia. Qed.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M1C := (at_M1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M1R := (at_M1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2C := (at_M2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2R := (at_M2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HSTEP := (hcore_raw_step B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK512 Hfmt HN Himgl HimgP).
Local Notation OTHERK := (hk_tbl_other_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation CEILF := (hcore_ceil B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK512).
Local Notation pxc := (pxc fmt imgl).
Lemma hl_pix_copy : forall (which : bool) lyc Sc W regs mem md k Cm i idx (raw : word),
hcore_raw lyc Sc W regs mem md k Cm -> 0 <= i < N -> 0 <= idx < ac_T Cm ->
getr regs 10 = Z_to_bv 64 ((if which then ac_h Cm else ac_p Cm) + 3 * idx) -> getr regs 11 = Z_to_bv 64 (img + fmt * i) ->
getr regs 12 = Z_to_bv 64 3 -> getr regs 1 = raw -> YK0s.ret_ok raw ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_asan_memcpy) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom trasegs)) md2 /\
hcore_raw lyc Sc W regs2 mem2 md2 k (C_col Cm which idx (pxc i)) /\ aregs_preserved regs regs2 /\
(forall a, s1v <= a < s1v + 512 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a)).
Proof.
intros which lyc Sc W regs mem md k Cm i idx raw HC Hi Hidx G10 G11 G12 G1 Hraw.
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept).
pose proof (proj1 HJ) as HAR. pose proof (asan_consts) as (C1 & _).
destruct (IMGF _ _ _ _ _ _ _ _ HC) as (Himgin & Hi4096 & Hiceil).
destruct (CEILF _ _ _ _ _ _ _ _ HC) as [Hceil H47].
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H Cm)) in *.
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
set (c := pxc i). set (pix := img + fmt * i) in *.
set (bd := if which then ac_h Cm else ac_p Cm) in *.
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4) by (destruct Hfmt as [Hf | Hf]; rewrite Hf; clear - Hi; lia).
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfi; lia)) as [_ HrqI]. pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
assert (Hbdin : In (bd, 3 * T) (ac_blocks tb Cm)) by (subst bd; unfold ac_blocks, cht_blocks, ac_T; fold T; destruct which; cbn; tauto).
assert (Hbdin' : In (bd, 3 * T) (ablocks B lyc Sc)).
{ apply (hcore_in_tbl B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ _ _ HC). exact Hbdin. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md bd (3 * T) HAR Hbdin') as (_ & Hd4096 & Hdceil & _).
pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb Cm) (img, fmt * N) (bd, 3 * T) HAR HPerm HimgP Hbdin) as Hsep.
unfold zdisjoint, block_rng in Hsep. cbn [fst snd] in Hsep.
eapply SRr_mono.
{ apply (hk_memcpy_call B LAWS AMEMCPY STK sp0 FP ly S W0 mem0 md0 own s1v Hs1 ltac:(unfold ESTACK in *; lia) lyc Sc W regs mem md k (bd + 3 * idx) pix 3 raw
bd (3 * T) img (fmt * N) HJ G10 G11 G12 ltac:(lia) G2 G3 G4 G1 Hraw Hbdin' ltac:(clear - Hidx; lia) ltac:(clear - Hidx HrqK; lia)
(proj2 (Hperm bd (3 * T) Hbdin)) Himgin ltac:(subst pix; clear - Hfi; lia) ltac:(subst pix; clear - Hfi HrqI; lia)).
subst pix. clear - Hsep Hidx HrqK Hfi HrqI. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcp & Hout2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
assert (RK : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r) by (intros r Hr; exact (aregs_get regs regs2 r HP2 Hr)).
split; [|split; [exact HP2|]].
2: { intros a Ha. apply Hout2; [clear - Ha Hceil H47 C1; lia | clear - Ha Hdceil HrqK Hidx Hceil; lia | clear - Ha; lia]. }
destruct (hk_pix_views sp0 img fmt N imgl Hfmt Himgl W mem i Himg Hi) as (V0 & V1 & V2 & Cok).
fold c in V0, V1, V2, Cok. fold pix in V0, V1, V2.
assert (B0 : mbyte trasegs (mrestrict (w_H W) mem2) (bd + 3 * idx) = Some (Z_to_bv 8 (cR c))).
{ apply hk_byte_of_av. rewrite <- V0. pose proof (Hcp 0 ltac:(lia)) as X. rewrite !Z.add_0_r in X. exact X. }
assert (B1 : mbyte trasegs (mrestrict (w_H W) mem2) (bd + 3 * idx + 1) = Some (Z_to_bv 8 (cG c))) by (apply hk_byte_of_av; rewrite <- V1; exact (Hcp 1 ltac:(lia))).
assert (B2 : mbyte trasegs (mrestrict (w_H W) mem2) (bd + 3 * idx + 2) = Some (Z_to_bv 8 (cB c))) by (apply hk_byte_of_av; rewrite <- V2; exact (Hcp 2 ltac:(lia))).
assert (KT : forall a, 0 <= a < alloc_ceiling -> ~ (bd <= a < bd + req_size (3 * T)) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha Hnb. apply Hout2; [clear - Ha C1; lia | clear - Hnb Hidx HrqK; lia | clear - Ha Hceil; lia]. }
assert (KIN : forall j, 0 <= j < 3 * T -> ~ (3 * idx <= j < 3 * idx + 3) -> mbyte trasegs (mrestrict (w_H W) mem2) (bd + j) = mbyte trasegs (mrestrict (w_H W) mem) (bd + j)).
{ intros j Hj Hnj. apply (mbyte_of_aview trasegs). apply Hout2; [clear - Hj Hd4096 Hdceil HrqK C1; lia | clear - Hnj; lia | clear - Hj Hdceil HrqK Hceil; lia]. }
apply (HSTEP lyc Sc W regs mem md k Cm (C_col Cm which idx c) regs2 mem2 md2 HC HJ2).
- intros r Hr. apply RK. exact (hk_const_saved r Hr).
- intros a Ha _ Hnb Hnt. apply Hout2; [exact Ha | | exact Hnb]. intros Hx. apply Hnt. exists bd, (3 * T). split; [exact Hbdin | clear - Hx Hidx HrqK; lia].
- destruct which; reflexivity.
- destruct which.
+ pose proof (OTHERK lyc Sc W regs mem md k Cm [(tb, CHT_SIZE); (ac_f Cm, 4 * T)] (ac_h Cm, 3 * T) [(ac_u Cm, T); (ac_p Cm, 3 * T); (ac_x Cm, 4 * T)] mem2 HC
ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; reflexivity) KT) as KO.
apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 tb LAY_Cht _ 48 Hobj lay_inside_Cht). exact (KO (tb, CHT_SIZE) ltac:(cbn; tauto)).
+ pose proof (OTHERK lyc Sc W regs mem md k Cm [(tb, CHT_SIZE); (ac_f Cm, 4 * T); (ac_h Cm, 3 * T); (ac_u Cm, T)] (ac_p Cm, 3 * T) [(ac_x Cm, 4 * T)] mem2 HC
ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; reflexivity) KT) as KO.
apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem mem2 tb LAY_Cht _ 48 Hobj lay_inside_Cht). exact (KO (tb, CHT_SIZE) ltac:(cbn; tauto)).
- assert (KBG : forall (l1 l2 : list (Z * Z)), ac_blocks tb Cm = l1 ++ (bd, 3 * T) :: l2 -> forall b n, In (b, n) (l1 ++ l2) -> 0 <= n -> forall a, b <= a < b + n ->
mbyte trasegs (mrestrict (w_H W) mem2) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros l1 l2 El b n Hin Hn0 a Ha. apply (mbyte_of_aview trasegs).
pose proof (OTHERK lyc Sc W regs mem md k Cm l1 (bd, 3 * T) l2 mem2 HC El KT (b, n) Hin) as Kb. cbn [fst snd] in Kb.
pose proof (req_size_pos n Hn0) as [_ Hrq]. replace a with (b + (a - b)) by lia. apply Kb. clear - Ha Hrq. lia. }
unfold C_col, ac_with, H_col. destruct which; cbn [ac_f ac_h ac_u ac_p ac_x ac_H ht_frequ ht_keys ht_used ht_pal ht_colidx].
+ pose proof (KBG [(tb, CHT_SIZE); (ac_f Cm, 4 * T)] [(ac_u Cm, T); (ac_p Cm, 3 * T); (ac_x Cm, 4 * T)] ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; reflexivity)) as KB.
split; [apply (arr32_frame trasegs _ _ _ _ Af); intros a Ha; apply (KB (ac_f Cm) (4 * T)); [cbn; tauto | clear - RT3; lia | rewrite L3 in Ha; exact Ha]|].
split; [apply (arr8_set_col_mem _ _ (ac_h Cm) (ht_keys (ac_H Cm)) idx c Ah ltac:(clear - Hidx; lia) ltac:(rewrite L2; clear - Hidx; lia) Cok B0 B1 B2); intros j Hj Hnj; apply KIN; [rewrite L2 in Hj; exact Hj | exact Hnj]|].
split; [apply (arr8_frame trasegs _ _ _ _ Au); intros a Ha; apply (KB (ac_u Cm) T); [cbn; tauto | clear - RT3; lia | rewrite L1 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ap); intros a Ha; apply (KB (ac_p Cm) (3 * T)); [cbn; tauto | clear - RT3; lia | rewrite L5 in Ha; exact Ha]|].
apply (arr32_frame trasegs _ _ _ _ Ax); intros a Ha; apply (KB (ac_x Cm) (4 * T)); [cbn; tauto | clear - RT3; lia | rewrite L4 in Ha; exact Ha].
+ pose proof (KBG [(tb, CHT_SIZE); (ac_f Cm, 4 * T); (ac_h Cm, 3 * T); (ac_u Cm, T)] [(ac_x Cm, 4 * T)] ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; reflexivity)) as KB.
split; [apply (arr32_frame trasegs _ _ _ _ Af); intros a Ha; apply (KB (ac_f Cm) (4 * T)); [cbn; tauto | clear - RT3; lia | rewrite L3 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ah); intros a Ha; apply (KB (ac_h Cm) (3 * T)); [cbn; tauto | clear - RT3; lia | rewrite L2 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Au); intros a Ha; apply (KB (ac_u Cm) T); [cbn; tauto | clear - RT3; lia | rewrite L1 in Ha; exact Ha]|].
split; [apply (arr8_set_col_mem _ _ (ac_p Cm) (ht_pal (ac_H Cm)) idx c Ap ltac:(clear - Hidx; lia) ltac:(rewrite L5; clear - Hidx; lia) Cok B0 B1 B2); intros j Hj Hnj; apply KIN; [rewrite L5 in Hj; exact Hj | exact Hnj]|].
apply (arr32_frame trasegs _ _ _ _ Ax); intros a Ha; apply (KB (ac_x Cm) (4 * T)); [cbn; tauto | clear - RT3; lia | rewrite L4 in Ha; exact Ha].
- unfold ht_lens, C_col, ac_with, H_col. destruct which; cbn [ac_H ht_frequ ht_keys ht_used ht_pal ht_colidx ht_T]; rewrite ?zlen_set_col; exact Hlens.
Qed.
Lemma hl_m1 : forall lyc Sc W regs mem md k C i ha h cf,
at_M1C lyc Sc W regs mem md k C i ha h cf ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_asan_memcpy) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_M1R) mem2 (seg_rom trasegs)) md2 /\ at_M1R lyc Sc W regs2 mem2 md2 k C i ha h cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf (HC & (Hi & Hha & Hop & G27) & Hsp & HG & (G20 & G21 & G23 & G24 & G26 & S296) & G10 & G11 & G12 & G1).
pose proof HG as (Hinv & Hz & Hfs & Hfree & Rcf).
pose proof (find_slot_range _ _ Hinv _ _ Hfs) as Rh.
pose proof Hinv as (_ & (Hcnt & _) & _).
eapply SRr_mono.
{ apply (hl_pix_copy true lyc Sc W regs mem md k C i h (Z_to_bv 64 HL_M1R) HC Hi Rh G10 G11 G12 G1). apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HC2 & HP2 & KF).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
assert (RK : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r) by (intros r Hr; exact (aregs_get regs regs2 r HP2 Hr)).
assert (SV : forall r : bv 5, In r [20; 21; 23; 24; 26; 27]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. apply RK. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate|]). destruct Hr. }
split; [exact HC2|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (SV 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact (hspill_kept sp0 s1v W mem mem2 i ha Hsp KF)|].
split; [exact HG|].
unfold hins_regs. rewrite (SV 20%bv ltac:(cbv; tauto)), (SV 21%bv ltac:(cbv; tauto)), (SV 23%bv ltac:(cbv; tauto)), (SV 24%bv ltac:(cbv; tauto)), (SV 26%bv ltac:(cbv; tauto)).
split; [exact G20|]. split; [exact G21|]. split; [exact G23|]. split; [exact G24|]. split; [exact G26|].
apply (rg_val_mem_blk_kept (w_H W) (w_H W) mem mem2 (s1v + 296) 8 _ 8 _ S296); [|lia|lia]. intros j Hj. apply KF. lia.
Qed.
Lemma hl_m2 : forall lyc Sc W regs mem md k C i ha h cf,
at_M2C lyc Sc W regs mem md k C i ha h cf ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 A_asan_memcpy) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_M2R) mem2 (seg_rom trasegs)) md2 /\ at_M2R lyc Sc W regs2 mem2 md2 k C i ha h cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf (HC & (Hi & Hha & Hop & G27) & Hsp & HG & (G20 & G21 & G23 & G24 & G26 & S296) & G10 & G11 & G12 & G1).
pose proof HG as (Hinv & Hz & Hfs & Hfree & Rcf).
pose proof (find_slot_range _ _ Hinv _ _ Hfs) as Rh.
pose proof Hinv as (_ & (Hcnt & _) & _).
eapply SRr_mono.
{ apply (hl_pix_copy false lyc Sc W regs mem md k (C_m1 C h (pxc i)) i (ht_cnt (ac_H C)) (Z_to_bv 64 HL_M2R) HC Hi Hcnt G10 G11 G12 G1). apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HC2 & HP2 & KF).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
assert (RK : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r) by (intros r Hr; exact (aregs_get regs regs2 r HP2 Hr)).
assert (SV : forall r : bv 5, In r [20; 21; 23; 24; 26; 27]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. apply RK. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved; vm_compute; repeat first [left; reflexivity | right]; split; discriminate|]). destruct Hr. }
split; [exact HC2|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (SV 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact (hspill_kept sp0 s1v W mem mem2 i ha Hsp KF)|].
split; [exact HG|].
unfold hins_regs. rewrite (SV 20%bv ltac:(cbv; tauto)), (SV 21%bv ltac:(cbv; tauto)), (SV 23%bv ltac:(cbv; tauto)), (SV 24%bv ltac:(cbv; tauto)), (SV 26%bv ltac:(cbv; tauto)).
split; [exact G20|]. split; [exact G21|]. split; [exact G23|]. split; [exact G24|]. split; [exact G26|].
apply (rg_val_mem_blk_kept (w_H W) (w_H W) mem mem2 (s1v + 296) 8 _ 8 _ S296); [|lia|lia]. intros j Hj. apply KF. lia.
Qed.
End H5.
