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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section H4.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_BR := (at_BR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_PA := (at_PA B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation FRAMEF := (hk_frame_facts B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK Hsp32).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Local Notation at_M1C := (at_M1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_RT := (at_RT B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HSTEP := (hcore_raw_step B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation OTHERK := (hk_tbl_other_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Lemma hl_pa_ins : forall lyc Sc W regs mem md k C i ha h cf,
at_PA lyc Sc W regs mem md k C i ha h cf -> usedz (ac_H C) h = 0 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_PA) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 A_asan_memcpy) mem2 (seg_rom trasegs)) md2 /\ at_M1C lyc Sc W regs2 mem2 md2 k C i ha h cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf HAT Hfree.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (Hi & Hha & Hop & G27) & Hz & [SP72 SP56] & (js & Ejs & Ehjs & Ecf) & G20 & G22 & G23 & G24 & G26 & G13 & G28 & G29 & (G5 & G6 & G7 & G16 & G17)).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *. set (c := pxc i) in *.
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (Rh : 0 <= h < T) by (rewrite Ehjs; apply cyc_range; clear - RT3; lia).
assert (Rcf : cf = 0 \/ cf = 1) by (rewrite Ecf; destruct (js <? 31); auto).
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & Hu4096 & Huceil & Huapp & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
assert (Hkin : In (ac_h C, 3 * T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR Hkin) as (_ & Hh4096 & Hhceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
destruct (arr8_getz trasegs _ (ac_u C) (ht_used (ac_H C)) h Au ltac:(rewrite L1; exact Rh)) as [Buh _].
change (getz (ht_used (ac_H C)) h) with (usedz (ac_H C) h) in Buh. rewrite Hfree in Buh.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [i; ha; ac_u C + h]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 (ac_u C + h)) by exact (HV 22%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 (ac_u C)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E24 : ew E 24 = Z_to_bv 64 h) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (E26 : ew E 26 = Z_to_bv 64 h) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (E22 : ew E 22 = Z_to_bv 64 (ac_h C)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (E13 : ew E 13 = Z_to_bv 64 cf) by (rewrite (HE 13%nat 13%bv eq_refl); exact G13).
assert (U54 : bv_unsigned (ew E 54) = ac_u C + h) by (rewrite E54; apply unsigned_lit_small; clear - Hu4096 Huceil HrqT Rh C1; lia).
set (xat := [(22%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF 4096 140737479966720 0); (24%nat, mkAF 0 16777215 0); (26%nat, mkAF 0 16777215 0); (54%nat, mkAF 4096 140737479966720 0)]).
assert (HsepU : ac_u C + h + 1 <= tb \/ tb + 48 <= ac_u C + h).
{ assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T tb CHT_SIZE HAR Huin Htbin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. clear - Hd HrqT Rh. lia. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_PA false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [YQ0b.mkRegion (Some 54%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit 0))]] xat
[] [(SAlu ALU_ADD (SOff 23 0) (SOff 24 0), SOff 54 0)] [mkSHE 54 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _)) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U54.
split; [clear - Hu4096 Rh; lia|]. split; [clear - Huceil HrqT Rh C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (ac_u C + h) 0 1 _ 0); [reflexivity | lia | lia |].
rewrite Z.add_0_r. apply (val_mem_byte trasegs); [exact Buh | lia]. }
{ intros e [<- | []]. unfold extent_of_region. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U54. clear - HsepU Huceil HrqT Rh. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. auto. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E22, E23, E24, E26, U54.
rewrite !unsigned_lit_small by (clear - Rh HT5 Hu4096 Huceil HrqT Hh4096 Hhceil HrqK C1; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rh HT5 Hu4096 Huceil HrqT Hh4096 Hhceil HrqK C1. repeat split; lia. }
{ exact I. }
{ cbn [alias_ok]. split; [|exact I]. apply U_inj. rewrite (U_atom E 54 (ac_u C + h) E54) by (clear - Hu4096 Huceil HrqT Rh C1; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 (ac_u C) E23) by (clear - Hu4096 Huceil HrqT C1 HT5; lia). rewrite (U_atom E 24 h E24) by (clear - Rh HT5; lia).
apply zcanon_id. unfold M64. clear - Hu4096 Huceil HrqT Rh C1. lia. }
{ apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 54 (ac_u C + h) 1 (ac_u C + h) 0 1).
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_u C) T _ _ HAR Huin); clear - Rh HrqT; lia.
- unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U54.
- lia.
- lia.
- intros x Hx. revert Hx Huapp Rh HrqT. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_asan_memcpy.
{ apply (hk_awr_ok s1v tb fmt _ false _ _ [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | []] & Hr). cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 24; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]);
assert (SP296 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 296) 8 cf)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 6%nat 296 304 296 304 [ck 296 (SOff 13 0)] 296 (SOff 13 0) cf HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 13 cf 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E13 | clear - Rcf; lia] | clear - Rcf; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
pose proof (HRS lyc Sc W regs mem md k C _ _ _ HC HJ ltac:(intros r Hr; apply HKR; apply in_or_app; left; exact Hr) ltac:(intros a Ha H1 _; exact (KM1 a Ha H1))) as [HCr' _].
split; [exact HCr'|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [split; [exact SP72' | exact SP56']|].
split; [split; [exact Hinv|]; split; [exact Hz|]; split; [rewrite Ehjs; exact (find_slot_of_off _ c js Ejs)|]; split; [exact Hfree | exact Rcf]|].
split.
{ unfold hins_regs. rewrite (HKR 20%bv ltac:(cbv; tauto)), (HKR 24%bv ltac:(cbv; tauto)), (HKR 26%bv ltac:(cbv; tauto)).
split; [exact G20|].
split; [apply (RD 21%bv (SOff 28 0) i eq_refl); [rewrite (denot_off E 28 i 0), Z.add_0_r; [reflexivity | rewrite (HE 28%nat 28%bv eq_refl); exact G28 | clear - Hi HN; lia] | reflexivity]|].
split; [apply (RD 23%bv (SOff 29 0) ha eq_refl); [rewrite (denot_off E 29 ha 0), Z.add_0_r; [reflexivity | rewrite (HE 29%nat 29%bv eq_refl); exact G29 | clear - Hha; lia] | reflexivity]|].
split; [exact G24|]. split; [exact G26 | exact SP296]. }
split.
{ apply (RD 10%bv (SAlu ALU_ADD (SOff 22 0) (SMd M_MUL (SOff 26 0) (SLit 3))) (ac_h C + 3 * h) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply (U_add_mul3' E 26 22 h (ac_h C) E26 ltac:(clear - Rh; lia) E22 ltac:(clear - Hh4096; lia)). clear - Hhceil HrqK Rh C1. lia. }
split; [apply (RD 11%bv (SOff 20 0) (img + fmt * i) eq_refl); [|reflexivity]; rewrite (denot_off E 20 (img + fmt * i) 0), Z.add_0_r; [reflexivity | rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hi4096 Hiceil C1 Hi Hfmt HN; nia]|].
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit 534780) HL_M1R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_pa_hit : forall lyc Sc W regs mem md k C i ha h cf,
at_PA lyc Sc W regs mem md k C i ha h cf -> usedz (ac_H C) h <> 0 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_PA) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_RT) mem2 (seg_rom trasegs)) md2 /\ at_RT lyc Sc W regs2 mem2 md2 k (C_hit C h) i ha cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf HAT Hused.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (Hi & Hha & Hop & G27) & Hz & [SP72 SP56] & (js & Ejs & Ehjs & Ecf) & G20 & G22 & G23 & G24 & G26 & G13 & G28 & G29 & (G5 & G6 & G7 & G16 & G17)).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *. set (c := pxc i) in *.
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (Rh : 0 <= h < T) by (rewrite Ehjs; apply cyc_range; clear - RT3; lia).
assert (Rcf : cf = 0 \/ cf = 1) by (rewrite Ecf; destruct (js <? 31); auto).
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & Hu4096 & Huceil & Huapp & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
assert (Hkin : In (ac_h C, 3 * T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR Hkin) as (_ & Hh4096 & Hhceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
destruct (arr8_getz trasegs _ (ac_u C) (ht_used (ac_H C)) h Au ltac:(rewrite L1; exact Rh)) as [Buh _].
change (getz (ht_used (ac_H C)) h) with (usedz (ac_H C) h) in Buh.
assert (Hused1 : usedz (ac_H C) h = 1) by (destruct (inv_used01 _ _ Hinv h Rh) as [X | X]; [contradiction | exact X]). rewrite Hused1 in Buh.
assert (Hslot : in_slot (ac_H C) h) by (split; [exact Rh | exact Hused]).
pose proof Hinv as (_ & _ & _ & I4 & _). destruct (I4 h Hslot) as (Hci & Hent & Hf1).
pose proof (zsum_pos_le (ac_ent C) _ _ _ (ent_freq_pos _ _ Hinv) Hent) as Hfle.
set (fv := freq (ac_H C) h) in *.
assert (Hfin : In (ac_f C, 4 * T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_f C) (4 * T) HAR Hfin) as (Hf16 & Hf4096 & Hfceil & Hfapp & Hfpres & _).
pose proof (req_size_pos (4 * T) ltac:(clear - RT3; lia)) as [_ HrqF].
destruct (arr32_getz trasegs _ (ac_f C) (ht_frequ (ac_H C)) h Af ltac:(rewrite L3; exact Rh)) as [Vfh Rfh].
change (getz (ht_frequ (ac_H C)) h) with fv in Vfh, Rfh.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [i; ha; ac_u C + h; ac_f C + 4 * h; fv]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 (ac_u C + h)) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 (ac_f C + 4 * h)) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 fv) by exact (HV 24%nat _ eq_refl).
assert (E23 : ew E 23 = Z_to_bv 64 (ac_u C)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E24 : ew E 24 = Z_to_bv 64 h) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U54 : bv_unsigned (ew E 54) = ac_u C + h) by (rewrite E54; apply unsigned_lit_small; clear - Hu4096 Huceil HrqT Rh C1; lia).
assert (U55 : bv_unsigned (ew E 55) = ac_f C + 4 * h) by (rewrite E55; apply unsigned_lit_small; clear - Hf4096 Hfceil HrqF Rh C1; lia).
set (xat := [(23%nat, mkAF 4096 140737479966720 0); (24%nat, mkAF 0 16777215 0); (33%nat, mkAF 4096 140737479966720 4); (54%nat, mkAF 4096 140737479966720 0);
(55%nat, mkAF 4096 140737479966720 2); (56%nat, mkAF 1 10000 0)]).
set (ureg := YQ0b.mkRegion (Some 54%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit 1))]).
set (freg := YQ0b.mkRegion (Some 55%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 56 0))]).
assert (HsepU : ac_u C + h + 1 <= tb \/ tb + 48 <= ac_u C + h).
{ assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T tb CHT_SIZE HAR Huin Htbin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. clear - Hd HrqT Rh. lia. }
assert (HsepF : ac_f C + 4 * h + 4 <= tb \/ tb + 48 <= ac_f C + 4 * h).
{ assert (Hne : (ac_f C, 4 * T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_f C) (4 * T) tb CHT_SIZE HAR Hfin Htbin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. clear - Hd HrqF Rh. lia. }
assert (HsepUF : ac_u C + h + 1 <= ac_f C + 4 * h \/ ac_f C + 4 * h + 4 <= ac_u C + h).
{ assert (Hne : (ac_u C, T) <> (ac_f C, 4 * T)) by (intros X; injection X as _ X; clear - X RT3; lia).
pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T (ac_f C) (4 * T) HAR Huin Hfin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd HrqT HrqF Rh. lia. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_PA false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [ureg; freg] xat
[] [(SAlu ALU_ADD (SOff 23 0) (SOff 24 0), SOff 54 0); (SAlu ALU_ADD (SAlu ALU_SLL (SOff 24 0) (SLit 2)) (SOff 33 0), SOff 55 0)] [mkSHE 54 0 1; mkSHE 55 0 4]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _)) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold ureg, freg, region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite ?U54, ?U55.
- split; [clear - Hu4096 Rh; lia|]. split; [clear - Huceil HrqT Rh C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (ac_u C + h) 0 1 _ 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. apply (val_mem_byte trasegs); [exact Buh | lia].
- split; [clear - Hf4096 Rh; lia|]. split; [clear - Hfceil HrqF Rh C1; lia|].
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hfpres (ac_f C + 4 * h + o) ltac:(clear - Ho Rh HrqF; lia)))|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (ac_f C + 4 * h) 0 4 _ fv); [rewrite (denot_off E 56 fv 0 E56), Z.add_0_r; [reflexivity | clear - Rfh; lia] | exact Rfh | lia |].
rewrite Z.add_0_r. exact Vfh. }
{ intros e [<- | [<- | []]]; unfold extent_of_region, ureg, freg; cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?U54, ?U55.
- clear - HsepU Huceil HrqT Rh. lia.
- clear - HsepF Hfceil HrqF Rh. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, ureg, freg, zdisj. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U54, U55. clear - HsepUF. repeat split; try exact I; lia. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E23, E24, E33, U54, U55, E56.
rewrite !unsigned_lit_small by (clear - Rh HT5 Hu4096 Huceil HrqT Hf4096 Hfceil HrqF C1 Hf1 Hfle Hz Hi HN; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
change (2 ^ 4) with 16. change (2 ^ 2) with 4.
assert (Hm4 : (ac_f C + 4 * h) mod 4 = 0).
{ rewrite Z.add_mod, (Z.mul_comm 4 h), Z.mod_mul by lia. rewrite Z.add_0_r, Z.mod_mod by lia.
clear - Hf16. pose proof (Z.div_mod (ac_f C) 16 ltac:(lia)) as D. rewrite Hf16, Z.add_0_r in D. rewrite D.
replace (16 * (ac_f C / 16)) with ((4 * (ac_f C / 16)) * 4) by lia. apply Z_mod_mult. }
clear - Rh HT5 Hu4096 Huceil HrqT Hf4096 Hfceil HrqF C1 Hf1 Hfle Hz Hi HN Hf16 Hm4. repeat split; lia. }
{ exact I. }
{ cbn [alias_ok]. split; [|split; [|exact I]]; apply U_inj.
- rewrite (U_atom E 54 (ac_u C + h) E54) by (clear - Hu4096 Huceil HrqT Rh C1; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 23 (ac_u C) E23) by (clear - Hu4096 Huceil HrqT C1 HT5; lia). rewrite (U_atom E 24 h E24) by (clear - Rh HT5; lia).
apply zcanon_id. unfold M64. clear - Hu4096 Huceil HrqT Rh C1. lia.
- rewrite (U_atom E 55 (ac_f C + 4 * h) E55) by (clear - Hf4096 Hfceil HrqF Rh C1; lia).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 24 h E24) by (clear - Rh HT5; lia). rewrite (U_lit E 2) by lia.
rewrite (U_atom E 33 (ac_f C) E33) by (clear - Hf4096 Hfceil HrqF C1 HT5; lia).
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (h * 4)) by (unfold M64; clear - Rh HT5; lia). rewrite zcanon_id by (unfold M64; clear - Hf4096 Hfceil HrqF Rh C1; lia). lia. }
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 54 (ac_u C + h) 1 (ac_u C + h) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_u C) T _ _ HAR Huin); clear - Rh HrqT; lia.
+ unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U54.
+ lia.
+ lia.
+ intros x Hx. revert Hx Huapp Rh HrqT. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 55 (ac_f C + 4 * h) 4 (ac_f C + 4 * h) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_f C) (4 * T) _ _ HAR Hfin); clear - Rh HrqF; lia.
+ unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U55.
+ lia.
+ lia.
+ intros x Hx. revert Hx Hfapp Rh HrqF. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_RT.
{ apply (hk_awr_ok s1v tb fmt _ false _ _ [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 55%nat (ac_f C + 4 * h)); [reflexivity | exact U55 | | apply awr_ok_nil].
unfold freg. cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha.
destruct (Hperm (ac_f C) (4 * T) ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as [_ Hw].
replace a with (ac_f C + (a - ac_f C)) by lia. apply Hw; [exact Hfin | clear - Ha Rh HrqF; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (ac_f C + 4 * h <= a < ac_f C + 4 * h + 4) ->
aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnf. apply (hk_frame_kept s1v tb fmt _ false _ _ [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | [<- | []]] & Hr); unfold ureg, freg in Hr; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; fold vals in Hr; fold E in Hr; rewrite ?U55 in Hr; clear - Hr Hnf; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [5; 6; 7; 13; 16; 17; 27; 28; 29]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 57 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 57 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]);
assert (VF' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (ac_f C + 4 * h) 4 (fv + 1))
by (destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 10%nat eq_refl)) as HR; cbn [ms_mem restrict] in HR;
pose proof (field_of_region Ex _ 55 (ac_f C + 4 * h) _ 0 4 0 4 0 4%N (SOff 56 1) (fv + 1) HR ltac:(rewrite (proj1 HAE1) by lia; exact U55) ltac:(left; reflexivity)
ltac:(apply denot_off; [rewrite (proj1 HAE1) by lia; exact E56 | clear - Rfh; lia]) ltac:(clear - Hf1 Hfle Hz Hi HN; cbn; lia) ltac:(lia)) as X;
rewrite Z.add_0_r in X; exact X) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
assert (KT : forall a, 0 <= a < alloc_ceiling -> ~ (ac_f C <= a < ac_f C + req_size (4 * T)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hnf. apply KM1; [clear - Ha C1; lia | clear - Ha Fceil; lia | clear - Hnf Rh HrqF; lia]. }
pose proof (OTHERK lyc Sc W regs mem md k C [(tb, CHT_SIZE)] (ac_f C, 4 * T) [(ac_h C, 3 * T); (ac_u C, T); (ac_p C, 3 * T); (ac_x C, 4 * T)] (ms_mem ms) (proj1 HC)
ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; reflexivity) KT) as KO.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HCr' : hcore_raw lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (C_hit C h)) end.
{ apply (HSTEP lyc Sc W regs mem md k C (C_hit C h) _ _ _ (proj1 HC) HJ).
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnt. apply KM1; [exact Ha | exact H1|]. intros Hx. apply Hnt. exists (ac_f C), (4 * T).
split; [unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto | clear - Hx Rh HrqF; lia].
- reflexivity.
- apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem (ms_mem ms) tb LAY_Cht _ 48 Hobj lay_inside_Cht). exact (KO (tb, CHT_SIZE) ltac:(cbn; tauto)).
- unfold C_hit, ac_with, ht_hit. cbn [ac_f ac_h ac_u ac_p ac_x ac_H ht_frequ ht_keys ht_used ht_pal ht_colidx].
assert (KB : forall b n, In (b, n) [(ac_h C, 3 * T); (ac_u C, T); (ac_p C, 3 * T); (ac_x C, 4 * T)] -> forall a, b <= a < b + n ->
mbyte trasegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros b n Hin a Ha. apply (mbyte_of_aview trasegs). pose proof (KO (b, n) ltac:(cbn [app]; right; exact Hin)) as Kb. cbn [fst snd] in Kb.
assert (Hn0 : 0 <= n) by (cbn [In] in Hin; destruct Hin as [X | [X | [X | [X | []]]]]; injection X as _ <-; clear - RT3; lia).
pose proof (req_size_pos n Hn0) as [_ Hrq].
replace a with (b + (a - b)) by lia. apply Kb. clear - Ha Hrq. lia. }
split.
{ apply (arr32_setz_mem _ _ (ac_f C) (ht_frequ (ac_H C)) h (fv + 1) Af); [rewrite L3; exact Rh | clear - Hf1 Hfle Hz Hi HN; lia | exact VF'|].
intros j Hj Hne kk Hkk. apply (mbyte_of_aview trasegs). rewrite L3 in Hj. apply KM1; [clear - Hj Hkk Hf4096 Hfceil HrqF C1; lia | clear - Hj Hkk Hfceil HrqF Fceil; lia | clear - Hj Hne Hkk; lia]. }
split; [apply (arr8_frame trasegs _ _ _ _ Ah); intros a Ha; apply (KB (ac_h C) (3 * T)); [cbn; tauto | rewrite L2 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Au); intros a Ha; apply (KB (ac_u C) T); [cbn; tauto | rewrite L1 in Ha; exact Ha]|].
split; [apply (arr8_frame trasegs _ _ _ _ Ap); intros a Ha; apply (KB (ac_p C) (3 * T)); [cbn; tauto | rewrite L5 in Ha; exact Ha]|].
apply (arr32_frame trasegs _ _ _ _ Ax); intros a Ha; apply (KB (ac_x C) (4 * T)); [cbn; tauto | rewrite L4 in Ha; exact Ha].
- unfold ht_lens, C_hit, ac_with, ht_hit. cbn [ac_H ht_frequ ht_keys ht_used ht_pal ht_colidx ht_T]. rewrite zlen_setz. exact Hlens. }
split; [split; [exact HCr' | exact (ht_hit_inv _ _ Hinv h Hslot)]|].
split; [exact Hi|]. split; [exact Hha|].
split; [unfold C_hit, ac_with; cbn [ac_ent]; rewrite (ht_hit_sum _ _ Hinv h Hslot); clear - Hz; lia|].
split; [split; [exact SP72' | exact SP56']|]. split; [exact Rcf|].
split.
{ rewrite (HKR 5%bv ltac:(cbv; tauto)), (HKR 6%bv ltac:(cbv; tauto)), (HKR 7%bv ltac:(cbv; tauto)), (HKR 16%bv ltac:(cbv; tauto)), (HKR 17%bv ltac:(cbv; tauto)), (HKR 27%bv ltac:(cbv; tauto)).
repeat split; assumption. }
split; [apply (RD 10%bv (SOff 32 40) (tb + 40) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [rewrite (HKR 13%bv ltac:(cbv; tauto)); exact G13|].
split; [apply (RD 14%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [rewrite (HKR 28%bv ltac:(cbv; tauto)); exact G28 | rewrite (HKR 29%bv ltac:(cbv; tauto)); exact G29].
Qed.
End H4.
