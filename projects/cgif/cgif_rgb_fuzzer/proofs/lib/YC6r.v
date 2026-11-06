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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section H7.
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
Local Notation at_M1R := (at_M1R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2C := (at_M2C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_M2R := (at_M2R B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRRS := (hcore_raw_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation APARTN := (hk_tbl_apart_nth B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Local Notation at_TL := (at_TL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Lemma hl_rt_stay_small : forall lyc Sc W regs mem md k C i ha cf,
at_RT lyc Sc W regs mem md k C i ha cf -> (cf = 0 /\ ac_T C < MAX_TABLE_SIZE) ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_RT) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_TAIL) mem2 (seg_rom trasegs)) md2 /\ at_TL lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha cf (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) [HCASE0 HCASE1].
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 524309 16777216 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ []))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite app_nil_r. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = T / 16777216).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (clear - HT5; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply zcanon_id. unfold M64. split; [apply Z.div_pos; clear - HT5; lia | apply Z.div_lt_upper_bound; clear - HT5; lia]. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (13%bv, SLit 0); (14%bv, SOff 32 44)] [] [] [] [] [] xat [mkAC BC_EQ (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T []
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G13, HCASE0. reflexivity.
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (clear - Rcnt HT5; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rcnt HT5. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, USRL, (U_lit E 0) by lia. apply Z.eqb_eq. apply Z.div_small. clear - HT5 HCASE1. unfold MAX_TABLE_SIZE in HCASE1. lia. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 52 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_TAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ [] [] [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 52 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ [] [] [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ []))) _) by (apply (env_agree_le 52 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [5; 6; 7; 16; 17; 27; 28]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 ha)
by (rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms 12%bv HS); change (sr_get (ss_regs ssx) 12%bv) with (SOff 29 0);
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAE1) by lia; rewrite (HE 29%nat 29%bv eq_refl); exact G29) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
split.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)].
intros r Hr. apply HKR. apply in_or_app. left. exact Hr. }
rewrite (HKR 5%bv ltac:(cbv; clear; tauto)), (HKR 6%bv ltac:(cbv; clear; tauto)), (HKR 7%bv ltac:(cbv; clear; tauto)), (HKR 16%bv ltac:(cbv; clear; tauto)),
(HKR 17%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)), (HKR 28%bv ltac:(cbv; clear; tauto)).
split; [repeat split; assumption|]. split; [exact G28|]. split; [exact R12|]. split; [exact Hi|]. split; [exact Hha | exact Hz].
Qed.
Lemma hl_rt_stay_max : forall lyc Sc W regs mem md k C i ha cf,
at_RT lyc Sc W regs mem md k C i ha cf -> ac_T C = MAX_TABLE_SIZE ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_RT) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_TAIL) mem2 (seg_rom trasegs)) md2 /\ at_TL lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha cf (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) HCASE.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 524309 16777216 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ []))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite app_nil_r. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = T / 16777216).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (clear - HT5; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply zcanon_id. unfold M64. split; [apply Z.div_pos; clear - HT5; lia | apply Z.div_lt_upper_bound; clear - HT5; lia]. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (14%bv, SOff 32 44)] [] [] [] [] [] xat [mkAC BC_NE (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T []
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (clear - Rcnt HT5; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rcnt HT5. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, USRL, (U_lit E 0) by lia. apply Bool.negb_true_iff, Z.eqb_neq. fold T in HCASE. rewrite HCASE. unfold MAX_TABLE_SIZE. clear. intros X. vm_compute in X. discriminate X. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 52 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_TAIL.
{ apply (hk_awr_ok s1v tb fmt E false _ [] [] [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 52 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ [] [] [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ []))) _) by (apply (env_agree_le 52 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [5; 6; 7; 16; 17; 27; 28]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 ha)
by (rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms 12%bv HS); change (sr_get (ss_regs ssx) 12%bv) with (SOff 29 0);
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAE1) by lia; rewrite (HE 29%nat 29%bv eq_refl); exact G29) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
split.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)].
intros r Hr. apply HKR. apply in_or_app. left. exact Hr. }
rewrite (HKR 5%bv ltac:(cbv; clear; tauto)), (HKR 6%bv ltac:(cbv; clear; tauto)), (HKR 7%bv ltac:(cbv; clear; tauto)), (HKR 16%bv ltac:(cbv; clear; tauto)),
(HKR 17%bv ltac:(cbv; clear; tauto)), (HKR 27%bv ltac:(cbv; clear; tauto)), (HKR 28%bv ltac:(cbv; clear; tauto)).
split; [repeat split; assumption|]. split; [exact G28|]. split; [exact R12|]. split; [exact Hi|]. split; [exact Hha | exact Hz].
Qed.
End H7.
