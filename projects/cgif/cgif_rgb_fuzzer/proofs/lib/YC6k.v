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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition HL_TAIL : Z := 0x82ef0.
Definition HL_BNE : Z := 0x82f08.
Section H0.
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
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hl_home := (hl_home tb fmt hv27 hv26 hv23 hv22 hv17 hv16).
Definition at_TL (lyc : alayout) (Sc : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z)
(C : acht) (i ha : Z) : Prop :=
hcore lyc Sc W regs mem md k C /\
(getr regs 5 = Z_to_bv 64 (tb + 8) /\ getr regs 6 = Z_to_bv 64 (tb + 16) /\ getr regs 7 = Z_to_bv 64 fmt /\
getr regs 16 = Z_to_bv 64 hv16 /\ getr regs 17 = Z_to_bv 64 hv17 /\ getr regs 27 = Z_to_bv 64 hv27) /\
getr regs 28 = Z_to_bv 64 i /\ getr regs 12 = Z_to_bv 64 ha /\
0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ zsum (map snd (ac_ent C)) <= i + 1.
Hypothesis HimgP : In (img, fmt * N) PROT.
Lemma hk_frame_facts : forall lyc Sc W regs mem md k C, hcore_raw lyc Sc W regs mem md k C ->
alloc_ceiling <= s1v /\ s1v + 512 <= 2 ^ 47 /\ s1v mod 32 = 0 /\ (forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a).
Proof.
intros lyc Sc W regs mem md k C HC. destruct HC as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
split; [clear - Hs1 HSTK Hceil Hslo; lia|]. split; [clear - Hs1 Hshi H47; lia|]. split.
- rewrite Hs1. rewrite Zminus_mod, Hsp32. reflexivity.
- intros a Ha. apply Hpres. clear - Ha Hs1 HSTK. lia.
Qed.
Lemma hk_img_facts : forall lyc Sc W regs mem md k C, hcore_raw lyc Sc W regs mem md k C ->
In (img, fmt * N) (ablocks B lyc Sc) /\ 4096 <= img /\ img + fmt * N <= alloc_ceiling.
Proof.
intros lyc Sc W regs mem md k C HC.
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & HPerm & _). pose proof (proj1 HJ) as HAR.
assert (Hin : In (img, fmt * N) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. left. exact HimgP. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md img (fmt * N) HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn0).
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfmt HN; nia)) as [_ Hrq].
split; [exact Hin|]. split; [exact H4096 | clear - Hceil Hrq; lia].
Qed.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation at_HL := (at_HL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_HX := (at_HX B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Lemma hl_tail : forall lyc Sc W regs mem md k C i ha,
at_TL lyc Sc W regs mem md k C i ha ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_TAIL) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
(i + 1 < N /\ c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_HEAD) mem2 (seg_rom trasegs)) md2 /\ at_HL lyc Sc W regs2 mem2 md2 k C (i + 1) ha) \/
(i + 1 = N /\ c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_EXIT) mem2 (seg_rom trasegs)) md2 /\ at_HX lyc Sc W regs2 mem2 md2 k C ha)).
Proof.
intros lyc Sc W regs mem md k C i ha HAT.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (G5 & G6 & G7 & G16 & G17 & G27) & G28 & G12 & Hi & Hha & Hz).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (hk_frame_facts _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (hk_img_facts _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
set (xat := [(28%nat, mkAF 0 9999 0); (51%nat, mkAF 1 10000 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ []))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite app_nil_r. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E51 : ew E 51 = Z_to_bv 64 N) by exact (HV 19%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_TAIL false [] [] [] [] [] [] xat [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) []
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _) (Forall_nil _) (Forall_nil _) (Forall_nil _) (Forall_nil _)
(Forall_nil _) ltac:(intros e []) I) as [HS SHOK].
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold vals. fold E.
rewrite (HE 28%nat 28%bv eq_refl), G28, E51.
rewrite !unsigned_lit_small by (clear - Hi HN; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Hi HN. repeat split; lia. }
{ exact I. }
{ exact I. }
{ constructor. }
fold vals in HS, SHOK. fold E in HS, SHOK.
assert (HAE : env_agree 52 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_BNE.
{ apply (hk_awr_ok s1v tb fmt E false [] [] [] [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
rename HFr into HFr1. clear HF HG.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 52 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false [] [] [] [] [] _ _ _ HFr1); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (UT3 : U E (SOff 28 1) = i + 1).
{ apply (U_atom_off E 28 i 1); [rewrite (HE 28%nat 28%bv eq_refl); exact G28 | clear - Hi HN; lia | clear - Hi HN; lia]. }
assert (UN : U E (SOff 51 0) = N) by (apply (U_atom E 51 N E51); clear - HN; lia).
assert (FIN : forall Ex ss' ms' md' (HS' : st_ok trasegs Ex ss' (restrict (w_H W) ms')), env_agree 52 E Ex -> ss_resv ss' = None ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) (HK_CONST ++ [5; 6; 7; 16; 17; 27; 12]%bv) = true ->
sr_get (ss_regs ss') 28 = SOff 28 1 -> sr_get (ss_regs ss') 29 = SOff 12 0 ->
sr_get (ss_regs ss') 22 = SOff 45 0 -> sr_get (ss_regs ss') 23 = SOff 43 0 -> sr_get (ss_regs ss') 26 = SOff 42 0 ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
hcore lyc Sc W (ms_regs ms') (ms_mem ms') md' k C /\ hl_home (ms_regs ms') /\
getr (ms_regs ms') 28 = Z_to_bv 64 (i + 1) /\ getr (ms_regs ms') 29 = Z_to_bv 64 ha /\ getr (ms_regs ms') 12 = Z_to_bv 64 ha).
{ intros Ex ss' ms' md' HS' HAEx Hrv QK Q28 Q29 Q22 Q23 Q26 HJ' HK'.
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ []))) Ex) by (apply (env_agree_le 52 32); [lia | exact HAEx]).
pose proof (regs_kept_of_st_ok trasegs Ex ss' _ regs _ _ HS' HAE32 QK) as HKR. cbn [ms_regs restrict] in HKR.
assert (RD : forall (r : bv 5) n v, sr_get (ss_regs ss') r = SOff n 0 -> (n < 52)%nat -> ew E n = Z_to_bv 64 v -> getr (ms_regs ms') r = Z_to_bv 64 v).
{ intros r n v Q Hn En. rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ss' ms' r HS'), Q. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (proj1 HAEx) by exact Hn. exact En. }
split.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ'); [|intros a Ha H1 _; exact (HK' a Ha H1)].
intros r Hr. apply HKR. apply in_or_app. left. exact Hr. }
split.
{ unfold hl_home.
rewrite (HKR 5%bv ltac:(cbv; tauto)), (HKR 6%bv ltac:(cbv; tauto)), (HKR 7%bv ltac:(cbv; tauto)), (HKR 16%bv ltac:(cbv; tauto)),
(HKR 17%bv ltac:(cbv; tauto)), (HKR 27%bv ltac:(cbv; tauto)).
split; [exact G5|]. split; [exact G6|]. split; [exact G7|]. split; [exact G16|]. split; [exact G17|].
split; [exact (RD 22%bv 45%nat hv22 Q22 ltac:(lia) (HV 13%nat _ eq_refl))|].
split; [exact (RD 23%bv 43%nat hv23 Q23 ltac:(lia) (HV 11%nat _ eq_refl))|].
split; [exact (RD 26%bv 42%nat hv26 Q26 ltac:(lia) (HV 10%nat _ eq_refl)) | exact G27]. }
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ss' ms' 28%bv HS'), Q28.
rewrite (denot_off Ex 28 i 1); [reflexivity | rewrite (proj1 HAEx) by lia; rewrite (HE 28%nat 28%bv eq_refl); exact G28 | clear - Hi HN; lia]. }
split; [|rewrite HKR by (cbv; tauto); exact G12].
exact (RD 29%bv 12%nat ha Q29 ltac:(lia) ltac:(rewrite (HE 12%nat 12%bv eq_refl); exact G12)). }
srr_branch_tok tratbl_lib_ok HS SHOK hk_Bspan.
-
rewrite branch_ne_U, UT3, UN in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE2 : env_agree 52 E Ex) by (env_agree_chain HAE1) end.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_HEAD.
{ apply (hk_awr_ok s1v tb fmt _ false [] [] [] [] [] STK sp0 FP _ _ lyc own); [exact U9 | exact Hs1 | exact HSTK | exact U32 | intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE3 : env_agree 52 E Ex) by (env_agree_chain HAE2) end.
destruct (FIN _ _ _ _ HS HAE3 eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl HJ) as (HC' & HH' & R28 & R29 & R12).
{ intros a Ha Hn. rewrite <- (KM1 a Ha Hn).
apply (hk_frame_kept s1v tb fmt _ false [] [] [] [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. left. split; [clear - Hc Hi; lia|]. split; [reflexivity|].
split; [exact HC'|]. split; [exact HH'|]. split; [exact R28|]. split; [exact R29|].
split; [clear - Hc Hi; lia|]. split; [exact Hha | exact Hz].
-
rewrite branch_ne_U, UT3, UN in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE2 : env_agree 52 E Ex) by (env_agree_chain HAE1) end.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_EXIT.
{ apply (hk_awr_ok s1v tb fmt _ false [] [] [] [] [] STK sp0 FP _ _ lyc own); [exact U9 | exact Hs1 | exact HSTK | exact U32 | intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE3 : env_agree 52 E Ex) by (env_agree_chain HAE2) end.
destruct (FIN _ _ _ _ HS HAE3 eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl HJ) as (HC' & HH' & R28 & R29 & R12).
{ intros a Ha Hn. rewrite <- (KM1 a Ha Hn).
apply (hk_frame_kept s1v tb fmt _ false [] [] [] [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. right. split; [exact Hc|]. split; [reflexivity|].
split; [exact HC'|]. split; [exact HH'|]. split; [exact R12|]. split; [exact Hha|]. rewrite <- Hc. exact Hz.
Qed.
End H0.
