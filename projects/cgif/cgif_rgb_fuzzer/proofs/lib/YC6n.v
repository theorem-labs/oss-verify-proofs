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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC6k YC6t YC7c YC6l YC6m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition CFE (a : sv) : sv := SAlu ALU_XOR (SAlu ALU_SLTU a (SLit 31)) (SLit 1).
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_CFE : forall E a x, U E a = x -> 0 <= x < 2 ^ 63 -> U E (CFE a) = if x <? 31 then 0 else 1.
Proof.
intros E a x Ha Hx. unfold CFE. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, Ha.
rewrite (zcanon_id 31), (zcanon_id 1) by (unfold M64; lia).
destruct (Z.ltb_spec x 31); cbn [Z.b2z]; rewrite ?(zcanon_id 1), ?(zcanon_id 0) by (unfold M64; lia); reflexivity.
Qed.
End b.
Section H3.
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
Local Notation pxc := (pxc fmt imgl).
Lemma hl_br_match : forall lyc Sc W regs mem md k C i ha j,
at_BR lyc Sc W regs mem md k C i ha j (Z_to_bv 64 0) ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_BR) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_PA) mem2 (seg_rom trasegs)) md2 /\
at_PA lyc Sc W regs2 mem2 md2 k C i ha (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j) (if j <? 31 then 0 else 1)).
Proof.
intros lyc Sc W regs mem md k C i ha j HAT.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (Hi & Hha & Hop & G27) & Hz & [SP72 SP56] & (G20 & G21 & G22 & G23 & G24 & G26) & (js & Ejs & Hj) & Hused & G10 & Hv0).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *. set (c := pxc i) in *. set (hj := cyc T (hash0 T c) j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; clear - RT3; lia).
pose proof (find_off_le_cnt _ _ Hinv c js Ejs) as Hjc.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _).
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
assert (Rj : 0 <= j <= 10000) by (clear - Hj Hjc Hzl Hlen Hz Hi HN; lia).
assert (Ejj : j = js).
{ destruct (Z.eq_dec j js) as [|Hne]; [assumption|]. exfalso.
destruct (probe_step _ _ Hinv c js j Ejs ltac:(clear - Hj Hne; lia)) as (_ & _ & Hkne & _). apply Hkne. apply Hv0. reflexivity. }
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n v, nth_error (vals ++ xv) n = Some v -> ew E (32 + n) = Z_to_bv 64 v).
{ intros n v Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
set (xat := [(24%nat, mkAF 0 10000 0); (26%nat, mkAF 0 16777215 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_BR false [(10%bv, SLit 0)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] xat [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G10. reflexivity. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HE 24%nat 24%bv eq_refl), G24, (HE 26%nat 26%bv eq_refl), G26.
rewrite !unsigned_lit_small by (clear - Rj Rhj RT1; unfold MAX_TABLE_SIZE in RT1; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold MAX_TABLE_SIZE in RT1. clear - Rj Rhj RT1. repeat split; lia. }
{ exact I. } { exact I. } { constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_PA.
{ apply (hk_awr_ok s1v tb fmt _ false _ _ [] [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ [] [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 22; 23; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e v, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 v)
by (intros r e v Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) j) with hj.
assert (E26 : ew E 26 = Z_to_bv 64 hj) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (E24 : ew E 24 = Z_to_bv 64 j) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72' | exact SP56']|].
split; [exists js; split; [exact Ejs|]; split; [subst hj; rewrite Ejj; reflexivity | rewrite Ejj; reflexivity]|].
split; [rewrite (HKR 20%bv ltac:(cbv; tauto)); exact G20|].
split; [rewrite (HKR 22%bv ltac:(cbv; tauto)); exact G22|].
split; [rewrite (HKR 23%bv ltac:(cbv; tauto)); exact G23|].
split; [apply (RD 24%bv (SOff 26 0) hj eq_refl); [rewrite (denot_off E 26 hj 0 E26), Z.add_0_r; [reflexivity | clear - Rhj RT2; lia] | reflexivity]|].
split; [rewrite (HKR 26%bv ltac:(cbv; tauto)); exact G26|].
split.
{ apply (RD 13%bv (CFE (SOff 24 0)) (if j <? 31 then 0 else 1) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply U_CFE; [apply (U_atom E 24 j E24); clear - Rj; lia | clear - Rj; lia]. }
split; [apply (RD 28%bv (SOff 52 0) i eq_refl); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity]|].
split; [apply (RD 29%bv (SOff 53 0) ha eq_refl); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity]|].
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
split; [apply (RD 5%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 6%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 7%bv (SLit fmt) fmt eq_refl eq_refl eq_refl)|].
split; [apply (RD 16%bv (SOff 47 0) hv16 eq_refl); [rewrite (denot_off E 47 hv16 0 (HV 15%nat _ eq_refl) O16), Z.add_0_r; reflexivity | reflexivity]|].
apply (RD 17%bv (SOff 46 0) hv17 eq_refl); [rewrite (denot_off E 46 hv17 0 (HV 14%nat _ eq_refl) O17), Z.add_0_r; reflexivity | reflexivity].
Qed.
Lemma hl_br_next : forall lyc Sc W regs mem md k C i ha j v,
at_BR lyc Sc W regs mem md k C i ha j v -> v <> Z_to_bv 64 0 ->
usedz (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) <> 0 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_BR) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 A_bcmp_tra) mem2 (seg_rom trasegs)) md2 /\ at_BC lyc Sc W regs2 mem2 md2 k C i ha (j + 1)).
Proof.
intros lyc Sc W regs mem md k C i ha j v HAT Hvne Hnext.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (Hi & Hha & Hop & G27) & Hz & [SP72 SP56] & (G20 & G21 & G22 & G23 & G24 & G26) & (js & Ejs & Hj) & Hused & G10 & Hv0).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *. set (c := pxc i) in *. set (hj := cyc T (hash0 T c) j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; clear - RT3; lia).
pose proof (find_off_le_cnt _ _ Hinv c js Ejs) as Hjc.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _).
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
assert (Rj : 0 <= j <= 10000) by (clear - Hj Hjc Hzl Hlen Hz Hi HN; lia).
assert (Hlt : j < js).
{ destruct (Z.eq_dec j js) as [Heq|Hne]; [|clear - Hj Hne; lia]. exfalso.
destruct (probe_end _ _ Hinv c js Ejs) as (_ & _ & [Hu0 | (_ & Hkc & _)]); rewrite <- Heq in *.
- apply Hused. exact Hu0.
- apply Hvne. apply Hv0. exact Hkc. }
destruct (probe_step _ _ Hinv c js j Ejs ltac:(clear - Hj Hlt; lia)) as (_ & _ & _ & _ & Esucc & Rnext).
fold T in Esucc, Rnext. fold hj in Esucc, Rnext. set (hn := probe_next T hj) in *.
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) with (cyc T (hash0 T c) (j + 1)) in Hnext. rewrite Esucc in Hnext.
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & Hu4096 & Huceil & Huapp & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
destruct (arr8_getz trasegs _ (ac_u C) (ht_used (ac_H C)) hn Au ltac:(rewrite L1; exact Rnext)) as [Bun Run].
change (getz (ht_used (ac_H C)) hn) with (usedz (ac_H C) hn) in Bun, Run.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [i; ha; ac_u C + hn]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 (ac_u C + hn)) by exact (HV 22%nat _ eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 T) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (E23 : ew E 23 = Z_to_bv 64 (ac_u C)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E24 : ew E 24 = Z_to_bv 64 j) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (E26 : ew E 26 = Z_to_bv 64 hj) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U54 : bv_unsigned (ew E 54) = ac_u C + hn) by (rewrite E54; apply unsigned_lit_small; clear - Hu4096 Huceil HrqT Rnext C1; lia).
set (xat := [(21%nat, mkAF 524309 16777216 0); (23%nat, mkAF 4096 140737479966720 0); (24%nat, mkAF 0 10000 0); (26%nat, mkAF 0 16777215 0); (54%nat, mkAF 4096 140737479966720 0)]).
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (HsepU : ac_u C + hn + 1 <= tb \/ tb + 48 <= ac_u C + hn).
{ assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T tb CHT_SIZE HAR Huin Htbin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. clear - Hd HrqT Rnext. lia. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_BR false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [YQ0b.mkRegion (Some 54%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit 1))]] xat
[mkAC BC_NE (SOff 10 0) (SLit 0)] [(SAlu ALU_ADD (SOff 23 0) (sv_nextz 26 21), SOff 54 0)] [mkSHE 54 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _)) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U54.
split; [clear - Hu4096 Rnext; lia|]. split; [clear - Huceil HrqT Rnext C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (ac_u C + hn) 0 1 _ 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. apply (val_mem_byte trasegs); [rewrite Bun; f_equal; f_equal; destruct (inv_used01 _ _ Hinv hn Rnext) as [X | X]; [contradiction | exact X] | lia]. }
{ intros e [<- | []]. unfold extent_of_region. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U54. clear - HsepU Huceil HrqT Rnext. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. auto. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E21, E23, E24, E26, U54.
rewrite !unsigned_lit_small by (clear - Rj Rhj HT5 Hu4096 Huceil HrqT C1; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rj Rhj HT5 Hu4096 Huceil HrqT Rnext C1. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U.
apply Bool.negb_true_iff, Z.eqb_neq. rewrite (U_lit E 0) by lia. unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 10%nat 10%bv eq_refl), G10.
intros X. apply Hvne. apply bv_eq. rewrite X. reflexivity.
}
{ cbn [alias_ok]. split; [|exact I]. apply U_inj. rewrite (U_atom E 54 (ac_u C + hn) E54) by (clear - Hu4096 Huceil HrqT Rnext C1; lia).
apply (U_u_next E 23 26 21 (ac_u C) hj T E23 E26 E21 Rhj); [clear - HT5; lia | clear - Hu4096; lia | clear - Huceil HrqT C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 54 (ac_u C + hn) 1 (ac_u C + hn) 0 1).
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_u C) T _ _ HAR Huin); clear - Rnext HrqT; lia.
- unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U54.
- lia.
- lia.
- intros x Hx. revert Hx Huapp Rnext HrqT. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_bcmp_tra.
{ apply (hk_awr_ok s1v tb fmt _ false _ _ [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | []] & Hr). cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 23; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
assert (UNX : U E (sv_next 26 21) = hn) by exact (U_sv_next E 26 21 hj T E26 E21 Rhj ltac:(clear - HT5; lia)).
assert (DNX : sv_denot E (sv_next 26 21) = Z_to_bv 64 hn) by (rewrite denot_lit_U, UNX; reflexivity).
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72' | exact SP56']|].
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) with (cyc T (hash0 T c) (j + 1)). rewrite Esucc.
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as (_ & Hh4096 & Hhceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
split.
{ unfold hprobe_regs. change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) with (cyc T (hash0 T c) (j + 1)). rewrite Esucc. change (ac_T C) with T.
rewrite (HKR 20%bv ltac:(cbv; tauto)), (HKR 21%bv ltac:(cbv; tauto)), (HKR 22%bv ltac:(cbv; tauto)), (HKR 23%bv ltac:(cbv; tauto)).
split; [exact G20|]. split; [exact G21|]. split; [exact G22|]. split; [exact G23|].
split; [apply (RD 24%bv (SOff 24 1) (j + 1) eq_refl); [apply denot_off; [exact E24 | clear - Rj; lia] | reflexivity] | exact (RD 26%bv (sv_next 26 21) hn eq_refl DNX eq_refl)]. }
split; [exists js; split; [exact Ejs | clear - Hj Hlt; lia]|].
split; [exact Hnext|].
split; [apply (RD 10%bv (SOff 20 0) (img + fmt * i) eq_refl); [|reflexivity]; rewrite (denot_off E 20 (img + fmt * i) 0), Z.add_0_r; [reflexivity | rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hi4096 Hiceil C1 Hi Hfmt HN; nia]|].
split.
{ apply (RD 11%bv (SAlu ALU_ADD (SOff 22 0) (ZXE (TRIPLE (sv_next 26 21)))) (ac_h C + 3 * hn) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply (U_base_triple E 22 (ac_h C) (sv_next 26 21) hn); [rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hh4096; lia | clear - Hhceil HrqK Rnext C1; lia | exact UNX | clear - Rnext HT5; lia]. }
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit 534492) HL_BR eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_br_free : forall lyc Sc W regs mem md k C i ha j v,
at_BR lyc Sc W regs mem md k C i ha j v -> v <> Z_to_bv 64 0 ->
usedz (ac_H C) (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) = 0 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_BR) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_PA) mem2 (seg_rom trasegs)) md2 /\ at_PA lyc Sc W regs2 mem2 md2 k C i ha (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) (if j + 1 <? 31 then 0 else 1)).
Proof.
intros lyc Sc W regs mem md k C i ha j v HAT Hvne Hnext.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (Hi & Hha & Hop & G27) & Hz & [SP72 SP56] & (G20 & G21 & G22 & G23 & G24 & G26) & (js & Ejs & Hj) & Hused & G10 & Hv0).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *. set (c := pxc i) in *. set (hj := cyc T (hash0 T c) j) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; clear - RT3; lia).
pose proof (find_off_le_cnt _ _ Hinv c js Ejs) as Hjc.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _).
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
assert (Rj : 0 <= j <= 10000) by (clear - Hj Hjc Hzl Hlen Hz Hi HN; lia).
assert (Hlt : j < js).
{ destruct (Z.eq_dec j js) as [Heq|Hne]; [|clear - Hj Hne; lia]. exfalso.
destruct (probe_end _ _ Hinv c js Ejs) as (_ & _ & [Hu0 | (_ & Hkc & _)]); rewrite <- Heq in *.
- apply Hused. exact Hu0.
- apply Hvne. apply Hv0. exact Hkc. }
destruct (probe_step _ _ Hinv c js j Ejs ltac:(clear - Hj Hlt; lia)) as (_ & _ & _ & _ & Esucc & Rnext).
fold T in Esucc, Rnext. fold hj in Esucc, Rnext. set (hn := probe_next T hj) in *.
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) with (cyc T (hash0 T c) (j + 1)) in Hnext. rewrite Esucc in Hnext.
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & Hu4096 & Huceil & Huapp & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
destruct (arr8_getz trasegs _ (ac_u C) (ht_used (ac_H C)) hn Au ltac:(rewrite L1; exact Rnext)) as [Bun Run].
change (getz (ht_used (ac_H C)) hn) with (usedz (ac_H C) hn) in Bun, Run.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [i; ha; ac_u C + hn]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 (ac_u C + hn)) by exact (HV 22%nat _ eq_refl).
assert (E21 : ew E 21 = Z_to_bv 64 T) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (E23 : ew E 23 = Z_to_bv 64 (ac_u C)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E24 : ew E 24 = Z_to_bv 64 j) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (E26 : ew E 26 = Z_to_bv 64 hj) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U54 : bv_unsigned (ew E 54) = ac_u C + hn) by (rewrite E54; apply unsigned_lit_small; clear - Hu4096 Huceil HrqT Rnext C1; lia).
set (xat := [(21%nat, mkAF 524309 16777216 0); (23%nat, mkAF 4096 140737479966720 0); (24%nat, mkAF 0 10000 0); (26%nat, mkAF 0 16777215 0); (54%nat, mkAF 4096 140737479966720 0)]).
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (HsepU : ac_u C + hn + 1 <= tb \/ tb + 48 <= ac_u C + hn).
{ assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T tb CHT_SIZE HAR Huin Htbin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd. clear - Hd HrqT Rnext. lia. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_BR false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [YQ0b.mkRegion (Some 54%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit 0))]] xat
[mkAC BC_NE (SOff 10 0) (SLit 0); mkAC BC_NE (sv_next 26 21) (SLit (-1))] [(SAlu ALU_ADD (SOff 23 0) (sv_nextz 26 21), SOff 54 0)] [mkSHE 54 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _)) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U54.
split; [clear - Hu4096 Rnext; lia|]. split; [clear - Huceil HrqT Rnext C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (ac_u C + hn) 0 1 _ 0); [reflexivity | lia | lia |].
rewrite Z.add_0_r. apply (val_mem_byte trasegs); [rewrite Bun, Hnext; reflexivity | lia]. }
{ intros e [<- | []]. unfold extent_of_region. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U54. clear - HsepU Huceil HrqT Rnext. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. auto. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E21, E23, E24, E26, U54.
rewrite !unsigned_lit_small by (clear - Rj Rhj HT5 Hu4096 Huceil HrqT C1; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rj Rhj HT5 Hu4096 Huceil HrqT Rnext C1. repeat split; lia. }
{ cbn [conds_ok]. split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U; apply Bool.negb_true_iff, Z.eqb_neq.
- rewrite (U_lit E 0) by lia. unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE 10%nat 10%bv eq_refl), G10.
intros X. apply Hvne. apply bv_eq. rewrite X. reflexivity.
- rewrite (U_sv_next E 26 21 hj T E26 E21 Rhj ltac:(clear - HT5; lia)). rewrite U_SLit. fold hn. change (zcanon (-1)) with (2 ^ 64 - 1). clear - Rnext HT5. lia.
}
{ cbn [alias_ok]. split; [|exact I]. apply U_inj. rewrite (U_atom E 54 (ac_u C + hn) E54) by (clear - Hu4096 Huceil HrqT Rnext C1; lia).
apply (U_u_next E 23 26 21 (ac_u C) hj T E23 E26 E21 Rhj); [clear - HT5; lia | clear - Hu4096; lia | clear - Huceil HrqT C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 54 (ac_u C + hn) 1 (ac_u C + hn) 0 1).
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_u C) T _ _ HAR Huin); clear - Rnext HrqT; lia.
- unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U54.
- lia.
- lia.
- intros x Hx. revert Hx Huapp Rnext HrqT. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_PA.
{ apply (hk_awr_ok s1v tb fmt _ false _ _ [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | []] & Hr). cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 22; 23; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 55 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 55 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
assert (UNX : U E (sv_next 26 21) = hn) by exact (U_sv_next E 26 21 hj T E26 E21 Rhj ltac:(clear - HT5; lia)).
assert (DNX : sv_denot E (sv_next 26 21) = Z_to_bv 64 hn) by (rewrite denot_lit_U, UNX; reflexivity).
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72' | exact SP56']|].
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) (j + 1)) with (cyc T (hash0 T c) (j + 1)). rewrite Esucc.
assert (Ejs1 : js = j + 1).
{ destruct (Z.eq_dec js (j + 1)) as [|Hne]; [assumption|]. exfalso.
destruct (probe_step _ _ Hinv c js (j + 1) Ejs ltac:(clear - Hj Hlt Hne; lia)) as (_ & Hun & _). apply Hun. fold T. rewrite Esucc. exact Hnext. }
split; [exists js; split; [exact Ejs|]; split; [rewrite Ejs1; symmetry; exact Esucc | rewrite Ejs1; reflexivity]|].
split; [rewrite (HKR 20%bv ltac:(cbv; tauto)); exact G20|].
split; [rewrite (HKR 22%bv ltac:(cbv; tauto)); exact G22|].
split; [rewrite (HKR 23%bv ltac:(cbv; tauto)); exact G23|].
split.
{ apply (RD 24%bv (sv_nextz 26 21) hn eq_refl); [|reflexivity]. rewrite denot_lit_U. f_equal. exact (U_sv_nextz E 26 21 hj T E26 E21 Rhj ltac:(clear - HT5; lia)). }
split; [exact (RD 26%bv (sv_next 26 21) hn eq_refl DNX eq_refl)|].
split.
{ apply (RD 13%bv (CFE (SOff 24 1)) (if j + 1 <? 31 then 0 else 1) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply U_CFE; [apply (U_atom_off E 24 j 1 E24); clear - Rj; lia | clear - Rj; lia]. }
split; [apply (RD 28%bv (SOff 52 0) i eq_refl); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | reflexivity]|].
split; [apply (RD 29%bv (SOff 53 0) ha eq_refl); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | reflexivity]|].
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
split; [apply (RD 5%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 6%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 7%bv (SLit fmt) fmt eq_refl eq_refl eq_refl)|].
split; [apply (RD 16%bv (SOff 47 0) hv16 eq_refl); [rewrite (denot_off E 47 hv16 0 (HV 15%nat _ eq_refl) O16), Z.add_0_r; reflexivity | reflexivity]|].
apply (RD 17%bv (SOff 46 0) hv17 eq_refl); [rewrite (denot_off E 46 hv17 0 (HV 14%nat _ eq_refl) O17), Z.add_0_r; reflexivity | reflexivity].
Qed.
End H3.
