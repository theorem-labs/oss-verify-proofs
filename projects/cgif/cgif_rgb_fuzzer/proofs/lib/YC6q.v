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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section H6.
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
Lemma hl_m1r : forall lyc Sc W regs mem md k C i ha h cf,
at_M1R lyc Sc W regs mem md k C i ha h cf ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_M1R) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 A_asan_memcpy) mem2 (seg_rom trasegs)) md2 /\ at_M2C lyc Sc W regs2 mem2 md2 k C i ha h cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf (HC & (Hi & Hha & Hop & G27) & [SP72 SP56] & HG & (G20 & G21 & G23 & G24 & G26 & S296)).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HG as (Hinv & Hz & Hfs & Hfree & Rcf).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ HC) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
change (ac_T (C_m1 C h (pxc i))) with (ac_T C) in HTc, HPerm.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
assert (Rcnt : 0 <= ht_cnt (ac_H C) <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
assert (Hpin : In (ac_p C, 3 * T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T, C_m1, ac_with. cbn [ac_f ac_h ac_u ac_p ac_x ac_H H_m1 ht_T]. fold T. cbn. tauto. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_p C) (3 * T) HAR Hpin) as (Hp16 & Hp4096 & Hpceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqP].
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [i; ha; cf]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 (ht_cnt (ac_H C))) by exact (HV 6%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 cf) by exact (HV 22%nat _ eq_refl).
set (xat := [(36%nat, mkAF 4096 140737479966720 4); (38%nat, mkAF 0 10000 0)]).
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_M1R false [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [ck 296 (SOff 54 0)] [] xat [] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _)) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ cf); [rewrite (denot_off E 54 cf 0 E54), Z.add_0_r; [reflexivity | clear - Rcf; lia] | clear - Rcf; lia | lia | exact S296]. }
{ apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E36, E38.
rewrite !unsigned_lit_small by (clear - Rcnt Hp4096 Hpceil HrqP C1 RT3; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
clear - Rcnt Hp4096 Hpceil HrqP C1 RT3 Hp16. repeat split; lia. }
{ exact I. } { exact I. } { constructor. }
assert (HAE : env_agree 55 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_asan_memcpy.
{ apply (hk_awr_ok s1v tb fmt _ false _ _ [] _ [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 55 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ [] _ [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 55 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [20; 21; 23; 24; 26; 27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
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
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 6%nat 296 304 296 304 [ck 296 (SOff 54 0)] 296 (SOff 54 0) cf HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 54 cf 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E54 | clear - Rcf; lia] | clear - Rcf; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
split; [apply (HRRS lyc Sc W regs mem md k _ _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [split; [exact SP72' | exact SP56']|]. split; [exact HG|].
split.
{ unfold hins_regs. rewrite (HKR 20%bv ltac:(cbv; tauto)), (HKR 21%bv ltac:(cbv; tauto)), (HKR 23%bv ltac:(cbv; tauto)), (HKR 24%bv ltac:(cbv; tauto)), (HKR 26%bv ltac:(cbv; tauto)).
repeat split; assumption. }
split.
{ apply (RD 10%bv (SAlu ALU_ADD (SOff 36 0) (SMd M_MUL (SOff 38 0) (SLit 3))) (ac_p C + 3 * ht_cnt (ac_H C)) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply (U_add_mul3' E 38 36 (ht_cnt (ac_H C)) (ac_p C) E38 ltac:(clear - Rcnt; lia) E36 ltac:(clear - Hp4096; lia)). clear - Hpceil HrqP Rcnt C1 RT3. lia. }
split; [apply (RD 11%bv (SOff 20 0) (img + fmt * i) eq_refl); [|reflexivity]; rewrite (denot_off E 20 (img + fmt * i) 0), Z.add_0_r; [reflexivity | rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - Hi4096 Hiceil C1 Hi Hfmt HN; nia]|].
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit 534856) HL_M2R eq_refl eq_refl eq_refl)].
Qed.
Lemma hl_m2r : forall lyc Sc W regs mem md k C i ha h cf,
at_M2R lyc Sc W regs mem md k C i ha h cf ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_M2R) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_RT) mem2 (seg_rom trasegs)) md2 /\ at_RT lyc Sc W regs2 mem2 md2 k (C_ins C h (pxc i)) i ha cf).
Proof.
intros lyc Sc W regs mem md k C i ha h cf (HC & (Hi & Hha & Hop & G27) & [SP72 SP56] & HG & (G20 & G21 & G23 & G24 & G26 & S296)).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HG as (Hinv & Hz & Hfs & Hfree & Rcf).
pose proof HC as (HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ HC) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ HC) as (Himgin & Hi4096 & Hiceil).
set (c := pxc i) in *. set (Cm := C_m2 C h c) in *.
change (ac_T Cm) with (ac_T C) in HTc, HPerm, Hk.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof (find_slot_range _ _ Hinv _ _ Hfs) as Rh. fold T in Rh.
pose proof Hinv as (HL0 & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof HL0 as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
assert (HT5 : 524309 <= T <= 16777216) by (clear - HTc; cbv [ts_chain In] in HTc; lia).
assert (Hblk : ac_blocks tb Cm = [(tb, CHT_SIZE); (ac_f C, 4 * T); (ac_h C, 3 * T); (ac_u C, T); (ac_p C, 3 * T); (ac_x C, 4 * T)]) by reflexivity.
assert (Hin : forall b n, In (b, n) (ac_blocks tb Cm) -> In (b, n) (ablocks B lyc Sc)).
{ intros b n Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. exact Hb. }
assert (IBt : In (tb, CHT_SIZE) (ac_blocks tb Cm)) by (rewrite Hblk; cbn; tauto).
assert (IBf : In (ac_f C, 4 * T) (ac_blocks tb Cm)) by (rewrite Hblk; cbn; tauto).
assert (IBh : In (ac_h C, 3 * T) (ac_blocks tb Cm)) by (rewrite Hblk; cbn; tauto).
assert (IBu : In (ac_u C, T) (ac_blocks tb Cm)) by (rewrite Hblk; cbn; tauto).
assert (IBp : In (ac_p C, 3 * T) (ac_blocks tb Cm)) by (rewrite Hblk; cbn; tauto).
assert (IBx : In (ac_x C, 4 * T) (ac_blocks tb Cm)) by (rewrite Hblk; cbn; tauto).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)) by (apply Hin; rewrite Hblk; cbn; tauto).
assert (Hfin : In (ac_f C, 4 * T) (ablocks B lyc Sc)) by (apply Hin; rewrite Hblk; cbn; tauto).
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)) by (apply Hin; rewrite Hblk; cbn; tauto).
assert (Hxin : In (ac_x C, 4 * T) (ablocks B lyc Sc)) by (apply Hin; rewrite Hblk; cbn; tauto).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_f C) (4 * T) HAR Hfin) as (Hf16 & Hf4096 & Hfceil & Hfapp & Hfpres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (Hu16 & Hu4096 & Huceil & Huapp & Hupres & _).
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_x C) (4 * T) HAR Hxin) as (Hx16 & Hx4096 & Hxceil & Hxapp & Hxpres & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT]. pose proof (req_size_pos (4 * T) ltac:(clear - RT3; lia)) as [_ HrqF].
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
assert (AP : forall (p q : nat) x y, nth_error (ac_blocks tb Cm) p = Some x -> nth_error (ac_blocks tb Cm) q = Some y -> p <> q ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x) by (intros p q x y; exact (APARTN lyc Sc W regs mem md k Cm p q x y HC)).
rewrite Hblk in AP.
pose proof (AP 0%nat 1%nat _ _ eq_refl eq_refl ltac:(lia)) as A01. pose proof (AP 0%nat 2%nat _ _ eq_refl eq_refl ltac:(lia)) as A02.
pose proof (AP 0%nat 3%nat _ _ eq_refl eq_refl ltac:(lia)) as A03. pose proof (AP 0%nat 4%nat _ _ eq_refl eq_refl ltac:(lia)) as A04.
pose proof (AP 0%nat 5%nat _ _ eq_refl eq_refl ltac:(lia)) as A05. pose proof (AP 1%nat 2%nat _ _ eq_refl eq_refl ltac:(lia)) as A12.
pose proof (AP 1%nat 3%nat _ _ eq_refl eq_refl ltac:(lia)) as A13. pose proof (AP 1%nat 4%nat _ _ eq_refl eq_refl ltac:(lia)) as A14.
pose proof (AP 1%nat 5%nat _ _ eq_refl eq_refl ltac:(lia)) as A15. pose proof (AP 2%nat 3%nat _ _ eq_refl eq_refl ltac:(lia)) as A23.
pose proof (AP 2%nat 5%nat _ _ eq_refl eq_refl ltac:(lia)) as A25. pose proof (AP 3%nat 4%nat _ _ eq_refl eq_refl ltac:(lia)) as A34.
pose proof (AP 3%nat 5%nat _ _ eq_refl eq_refl ltac:(lia)) as A35. pose proof (AP 4%nat 5%nat _ _ eq_refl eq_refl ltac:(lia)) as A45.
cbn [fst snd] in A01, A02, A03, A04, A05, A12, A13, A14, A15, A23, A25, A34, A35, A45. change (req_size CHT_SIZE) with 48 in A01, A02, A03, A04, A05. clear AP.
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (xv := [i; ha; cf; ac_u C + h; ac_x C + 4 * h; ac_f C + 4 * h]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (ac_f C)) by exact (HV 1%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 (ac_x C)) by exact (HV 5%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (E54 : ew E 54 = Z_to_bv 64 cf) by exact (HV 22%nat _ eq_refl).
assert (E55 : ew E 55 = Z_to_bv 64 (ac_u C + h)) by exact (HV 23%nat _ eq_refl).
assert (E56 : ew E 56 = Z_to_bv 64 (ac_x C + 4 * h)) by exact (HV 24%nat _ eq_refl).
assert (E57 : ew E 57 = Z_to_bv 64 (ac_f C + 4 * h)) by exact (HV 25%nat _ eq_refl).
assert (E24 : ew E 24 = Z_to_bv 64 h) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U55 : bv_unsigned (ew E 55) = ac_u C + h) by (rewrite E55; apply unsigned_lit_small; clear - Hu4096 Huceil HrqT Rh C1; lia).
assert (U56 : bv_unsigned (ew E 56) = ac_x C + 4 * h) by (rewrite E56; apply unsigned_lit_small; clear - Hx4096 Hxceil HrqF Rh C1; lia).
assert (U57 : bv_unsigned (ew E 57) = ac_f C + 4 * h) by (rewrite E57; apply unsigned_lit_small; clear - Hf4096 Hfceil HrqF Rh C1; lia).
set (xat := [(24%nat, mkAF 0 16777215 0); (33%nat, mkAF 4096 140737479966720 4); (35%nat, mkAF 4096 140737479966720 4); (37%nat, mkAF 4096 140737479966720 4);
(38%nat, mkAF 0 10000 0); (55%nat, mkAF 4096 140737479966720 0); (56%nat, mkAF 4096 140737479966720 2); (57%nat, mkAF 4096 140737479966720 2)]).
set (ur := YQ0b.mkRegion (Some 55%nat) 0 1 0 1 []). set (xr := YQ0b.mkRegion (Some 56%nat) 0 4 0 4 []). set (fr := YQ0b.mkRegion (Some 57%nat) 0 4 0 4 []).
set (A1 := (SAlu ALU_ADD (SOff 24 0) (SOff 35 0), SOff 55 0)).
set (A2 := (SAlu ALU_ADD (SAlu ALU_SLL (SOff 24 0) (SLit 2)) (SOff 37 0), SOff 56 0)).
set (A3 := (SAlu ALU_ADD (SAlu ALU_SLL (SOff 24 0) (SLit 2)) (SOff 33 0), SOff 57 0)).
assert (Hm4 : forall b, b mod 16 = 0 -> (b + 4 * h) mod 4 = 0).
{ intros b Hb. rewrite Z.add_mod, (Z.mul_comm 4 h), Z.mod_mul by lia. rewrite Z.add_0_r, Z.mod_mod by lia.
pose proof (Z.div_mod b 16 ltac:(lia)) as D. rewrite Hb, Z.add_0_r in D. rewrite D. replace (16 * (b / 16)) with ((4 * (b / 16)) * 4) by lia. apply Z_mod_mult. }
assert (U4H : forall n b, ew E n = Z_to_bv 64 b -> 4096 <= b -> b + 4 * T <= 140737479966720 -> U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff 24 0) (SLit 2)) (SOff n 0)) = b + 4 * h).
{ intros n b En Hb0 Hb1. rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 24 h E24) by (clear - Rh HT5; lia). rewrite (U_lit E 2) by lia.
rewrite (U_atom E n b En) by (clear - Hb0 Hb1 HT5; lia). change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (h * 4)) by (unfold M64; clear - Rh HT5; lia). rewrite zcanon_id by (unfold M64; clear - Hb0 Hb1 Rh; lia). lia. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_M2R true [] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [ck 296 (SOff 54 0)] [ur; xr; fr] xat [] [A1; A2; A3] [mkSHE 55 0 1; mkSHE 56 0 4; mkSHE 57 0 4]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj eq_refl eq_refl (Forall_nil _)) as [HS SHOK].
all: fold vals; fold E.
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 296 8 _ cf); [rewrite (denot_off E 54 cf 0 E54), Z.add_0_r; [reflexivity | clear - Rcf; lia] | clear - Rcf; lia | lia | exact S296]. }
{ repeat apply Forall_cons; try apply Forall_nil; unfold ur, xr, fr, region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite ?U55, ?U56, ?U57.
- split; [clear - Hu4096 Rh; lia|]. split; [clear - Huceil HrqT Rh C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hupres (ac_u C + h + o) ltac:(clear - Ho Rh HrqT; lia))).
- split; [clear - Hx4096 Rh; lia|]. split; [clear - Hxceil HrqF Rh C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hxpres (ac_x C + 4 * h + o) ltac:(clear - Ho Rh HrqF; lia))).
- split; [clear - Hf4096 Rh; lia|]. split; [clear - Hfceil HrqF Rh C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hfpres (ac_f C + 4 * h + o) ltac:(clear - Ho Rh HrqF; lia))). }
{ intros e [<- | [<- | [<- | []]]]; unfold extent_of_region, ur, xr, fr; cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; rewrite ?U55, ?U56, ?U57.
- clear - A03 Huceil HrqT Rh. lia.
- clear - A05 Hxceil HrqF Rh. lia.
- clear - A01 Hfceil HrqF Rh. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, ur, xr, fr, zdisj. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U55, U56, U57.
clear - A13 A35 A15 HrqT HrqF Rh. repeat split; try exact I; lia. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E24, E33, E35, E37, E38, U55, U56, U57.
rewrite !unsigned_lit_small by (clear - Rh HT5 Rcnt Hu4096 Huceil HrqT Hf4096 Hfceil Hx4096 Hxceil HrqF C1; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
change (2 ^ 4) with 16. change (2 ^ 2) with 4. pose proof (Hm4 _ Hx16) as Mx. pose proof (Hm4 _ Hf16) as Mf.
clear - Rh HT5 Rcnt Hu4096 Huceil HrqT Hf4096 Hfceil Hx4096 Hxceil HrqF C1 Hu16 Hf16 Hx16 Mx Mf. repeat split; lia. }
{ exact I. }
{ subst A1 A2 A3. cbn [alias_ok]. split; [|split; [|split; [|exact I]]]; apply U_inj.
- rewrite (U_atom E 55 (ac_u C + h) E55) by (clear - Hu4096 Huceil HrqT Rh C1; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 24 h E24) by (clear - Rh HT5; lia). rewrite (U_atom E 35 (ac_u C) E35) by (clear - Hu4096 Huceil HrqT C1 HT5; lia).
rewrite zcanon_id by (unfold M64; clear - Hu4096 Huceil HrqT Rh C1; lia). lia.
- rewrite (U_atom E 56 (ac_x C + 4 * h) E56) by (clear - Hx4096 Hxceil HrqF Rh C1; lia). apply (U4H 37%nat (ac_x C) E37); [exact Hx4096 | clear - Hxceil HrqF C1; lia].
- rewrite (U_atom E 57 (ac_f C + 4 * h) E57) by (clear - Hf4096 Hfceil HrqF Rh C1; lia). apply (U4H 33%nat (ac_f C) E33); [exact Hf4096 | clear - Hfceil HrqF C1; lia]. }
{ assert (UB : U E hk_Bx = SHADOW_OFF) by (unfold U, hk_Bx; cbn [sv_denot]; rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
repeat apply Forall_cons; try apply Forall_nil.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 55 (ac_u C + h) 1 (ac_u C + h) 0 1); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_u C) T _ _ HAR Huin); clear - Rh HrqT; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U55.
+ intros x Hx. revert Hx Huapp Rh HrqT. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 56 (ac_x C + 4 * h) 4 (ac_x C + 4 * h) 0 4); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_x C) (4 * T) _ _ HAR Hxin); clear - Rh HrqF; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U56.
+ intros x Hx. revert Hx Hxapp Rh HrqF. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 57 (ac_f C + 4 * h) 4 (ac_f C + 4 * h) 0 4); [|exact UB| | lia | lia |].
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md (ac_f C) (4 * T) _ _ HAR Hfin); clear - Rh HrqF; lia.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U57.
+ intros x Hx. revert Hx Hfapp Rh HrqF. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_RT.
{ assert (PW : forall b n, In (b, n) (ac_blocks tb Cm) -> forall a, b <= a < b + req_size n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ intros b n Hb a Ha. destruct (Hperm b n Hb) as [_ Hw]. replace a with (b + (a - b)) by lia. apply Hw; [exact (Hin b n Hb) | clear - Ha; lia]. }
apply (hk_awr_ok s1v tb fmt _ true _ _ [] _ _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32).
- intros _ a Ha. apply (PW tb CHT_SIZE IBt). change (req_size CHT_SIZE) with 48. exact Ha.
- eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 55%nat (ac_u C + h)); [reflexivity | exact U55 | |].
{ unfold ur. cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. apply (PW (ac_u C) T IBu). clear - Ha Rh HrqT. lia. }
eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 56%nat (ac_x C + 4 * h)); [reflexivity | exact U56 | |].
{ unfold xr. cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. apply (PW (ac_x C) (4 * T) IBx). clear - Ha Rh HrqF. lia. }
eapply (awr_ok_cons_gen _ _ _ STK sp0 FP _ _ lyc own 57%nat (ac_f C + 4 * h)); [reflexivity | exact U57 | | apply awr_ok_nil].
unfold fr. cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. apply (PW (ac_f C) (4 * T) IBf). clear - Ha Rh HrqF. lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> ~ (tb <= a < tb + 48) -> ~ (ac_u C + h <= a < ac_u C + h + 1) ->
~ (ac_x C + 4 * h <= a < ac_x C + 4 * h + 4) -> ~ (ac_f C + 4 * h <= a < ac_f C + 4 * h + 4) ->
aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn Hnt Hnu Hnx Hnf. apply (hk_frame_kept s1v tb fmt _ true _ _ [] _ _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros _; exact Hnt|].
intros (rr & [<- | [<- | [<- | []]]] & Hr); unfold ur, xr, fr in Hr; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; fold vals in Hr; fold E in Hr;
rewrite ?U55, ?U56, ?U57 in Hr; clear - Hr Hnu Hnx Hnf; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]);
destruct (st_ok_mem_ok trasegs Ex ssx _ HS) as (_ & Hrs & _);
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 8%nat eq_refl)) as HRtb;
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 9%nat eq_refl)) as HRu;
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 10%nat eq_refl)) as HRx;
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In (ss_mem ssx) 11%nat eq_refl)) as HRf;
cbn [ms_mem restrict] in HRtb, HRu, HRx, HRf;
assert (DA : forall n z, (n < 58)%nat -> ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot Ex (SOff n 0) = Z_to_bv 64 z)
by (intros n z Hn En Hz0; rewrite (denot_off Ex n z 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact En | exact Hz0]);
assert (UX32 : bv_unsigned (ew Ex 32) = tb) by (rewrite (proj1 HAE1) by lia; exact U32);
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 0 8%N (SOff 33 0) (ac_f C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 33%nat _ ltac:(lia) E33 Bf) Bf ltac:(lia)) as Vf';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 8 8%N (SOff 34 0) (ac_h C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 34%nat _ ltac:(lia) (HV 2%nat _ eq_refl) Bh) Bh ltac:(lia)) as Vh';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 16 8%N (SOff 35 0) (ac_u C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 35%nat _ ltac:(lia) E35 Bu) Bu ltac:(lia)) as Vu';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 24 8%N (SOff 36 0) (ac_p C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 36%nat _ ltac:(lia) (HV 4%nat _ eq_refl) Bp) Bp ltac:(lia)) as Vp';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 32 8%N (SOff 37 0) (ac_x C) HRtb UX32 ltac:(cbn; clear; tauto) (DA 37%nat _ ltac:(lia) E37 Bx) Bx ltac:(lia)) as Vx';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 40 4%N (SOff 38 1) (cnt + 1) HRtb UX32 ltac:(cbn; clear; tauto)
ltac:(apply denot_off; [rewrite (proj1 HAE1) by lia; exact E38 | clear - Rcnt; lia]) ltac:(clear - Rcnt; cbn; lia) ltac:(lia)) as Vc';
pose proof (field_of_region Ex _ 32 tb _ 0 48 0 48 44 4%N (SOff 39 0) T HRtb UX32 ltac:(cbn; clear; tauto) (DA 39%nat _ ltac:(lia) (HV 7%nat _ eq_refl) ltac:(clear - HT5; lia)) ltac:(clear - HT5; cbn; lia) ltac:(lia)) as VT';
pose proof (field_of_region Ex _ 55 (ac_u C + h) _ 0 1 0 1 0 1%N (SLit 1) 1 HRu ltac:(rewrite (proj1 HAE1) by lia; exact U55) ltac:(cbn; clear; tauto) eq_refl ltac:(cbn; lia) ltac:(lia)) as Vuh;
pose proof (field_of_region Ex _ 56 (ac_x C + 4 * h) _ 0 4 0 4 0 4%N (SOff 38 0) cnt HRx ltac:(rewrite (proj1 HAE1) by lia; exact U56) ltac:(cbn; clear; tauto)
(DA 38%nat _ ltac:(lia) E38 ltac:(clear - Rcnt; lia)) ltac:(clear - Rcnt; cbn; lia) ltac:(lia)) as Vxh;
pose proof (field_of_region Ex _ 57 (ac_f C + 4 * h) _ 0 4 0 4 0 4%N (SLit 1) 1 HRf ltac:(rewrite (proj1 HAE1) by lia; exact U57) ltac:(cbn; clear; tauto) eq_refl ltac:(cbn; lia) ltac:(lia)) as Vfh end.
rewrite !Z.add_0_r in Vf', Vuh, Vxh, Vfh.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
assert (KB : forall b n, In (b, n) (ac_blocks tb Cm) -> forall a, b <= a < b + req_size n -> ~ (tb <= a < tb + 48) -> ~ (ac_u C + h <= a < ac_u C + h + 1) ->
~ (ac_x C + 4 * h <= a < ac_x C + 4 * h + 4) -> ~ (ac_f C + 4 * h <= a < ac_f C + 4 * h + 4) ->
mbyte trasegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte trasegs (mrestrict (w_H W) mem) a).
{ intros b n Hb a Ha N1 N2 N3 N4. apply (mbyte_of_aview trasegs).
destruct (al_blocks _ _ LAWS lyc Sc W mem md b n HAR (Hin b n Hb)) as (_ & Hb4096 & Hbceil & _).
apply KM1; [clear - Ha Hb4096 Hbceil C1; lia | clear - Ha Hbceil Fceil; lia | exact N1 | exact N2 | exact N3 | exact N4]. }
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HCr' : hcore_raw lyc Sc W (ms_regs ms) (ms_mem ms) mdx k (C_ins C h c)) end.
{ apply (HSTEP lyc Sc W regs mem md k Cm (C_ins C h c) _ _ _ HC HJ).
- intros r Hr. apply HKR. apply in_or_app. left. exact Hr.
- intros a Ha H1 _ Hnt. apply KM1; [exact Ha | exact H1 | | | |]; intros Hx; apply Hnt.
+ exists tb, CHT_SIZE. split; [exact IBt | change (req_size CHT_SIZE) with 48; exact Hx].
+ exists (ac_u C), T. split; [exact IBu | clear - Hx Rh HrqT; lia].
+ exists (ac_x C), (4 * T). split; [exact IBx | clear - Hx Rh HrqF; lia].
+ exists (ac_f C), (4 * T). split; [exact IBf | clear - Hx Rh HrqF; lia].
- reflexivity.
- change (obj_at trasegs (mrestrict (w_H W) (ms_mem ms)) tb LAY_Cht [ac_f C; ac_h C; ac_u C; ac_p C; ac_x C; cnt + 1; T]).
cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split; [split; [exact Vf' | exact Bf]|]. split; [split; [exact Vh' | exact Bh]|]. split; [split; [exact Vu' | exact Bu]|].
split; [split; [exact Vp' | exact Bp]|]. split; [split; [exact Vx' | exact Bx]|]. split; [split; [exact Vc' | clear - Rcnt; lia]|].
split; [split; [exact VT' | clear - HT5; lia]|]. exact I.
- change (cht_arrays trasegs (mrestrict (w_H W) (ms_mem ms)) (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_ins (ac_H C) h c 1)).
unfold cht_arrays, ht_ins. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx]. fold cnt.
change (ht_frequ (ac_H Cm)) with (ht_frequ (ac_H C)) in Af. change (ht_keys (ac_H Cm)) with (set_col (ht_keys (ac_H C)) h c) in Ah.
change (ht_used (ac_H Cm)) with (ht_used (ac_H C)) in Au. change (ht_pal (ac_H Cm)) with (set_col (ht_pal (ac_H C)) cnt c) in Ap.
change (ht_colidx (ac_H Cm)) with (ht_colidx (ac_H C)) in Ax.
change (ac_f Cm) with (ac_f C) in Af. change (ac_h Cm) with (ac_h C) in Ah. change (ac_u Cm) with (ac_u C) in Au. change (ac_p Cm) with (ac_p C) in Ap. change (ac_x Cm) with (ac_x C) in Ax.
split.
{ apply (arr32_setz_mem _ _ (ac_f C) (ht_frequ (ac_H C)) h 1 Af); [rewrite L3; exact Rh | lia | exact Vfh|].
intros j Hj Hne kk Hkk. rewrite L3 in Hj. apply (KB (ac_f C) (4 * T) IBf); [clear - Hj Hkk HrqF; lia | clear - Hj Hkk A01 HrqF; lia | clear - Hj Hkk A13 HrqF HrqT Rh; lia | clear - Hj Hkk A15 HrqF Rh; lia | clear - Hj Hkk Hne; lia]. }
split.
{ apply (arr8_frame trasegs _ _ _ _ Ah). intros a Ha. rewrite zlen_set_col, L2 in Ha.
apply (KB (ac_h C) (3 * T) IBh); [clear - Ha HrqK; lia | clear - Ha A02 HrqK; lia | clear - Ha A23 HrqK HrqT Rh; lia | clear - Ha A25 HrqK HrqF Rh; lia | clear - Ha A12 HrqK HrqF Rh; lia]. }
split.
{ apply (arr8_setz_mem _ _ (ac_u C) (ht_used (ac_H C)) h 1 Au); [rewrite L1; exact Rh | lia | |].
- pose proof (Vuh 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. exact X.
- intros j Hj Hne. rewrite L1 in Hj. apply (KB (ac_u C) T IBu); [clear - Hj HrqT; lia | clear - Hj A03 HrqT; lia | clear - Hj Hne; lia | clear - Hj A35 HrqT HrqF Rh; lia | clear - Hj A13 HrqT HrqF Rh; lia]. }
split.
{ apply (arr8_frame trasegs _ _ _ _ Ap). intros a Ha. rewrite zlen_set_col, L5 in Ha.
apply (KB (ac_p C) (3 * T) IBp); [clear - Ha HrqK; lia | clear - Ha A04 HrqK; lia | clear - Ha A34 HrqK HrqT Rh; lia | clear - Ha A45 HrqK HrqF Rh; lia | clear - Ha A14 HrqK HrqF Rh; lia]. }
apply (arr32_setz_mem _ _ (ac_x C) (ht_colidx (ac_H C)) h cnt Ax); [rewrite L4; exact Rh | clear - Rcnt; lia | exact Vxh|].
intros j Hj Hne kk Hkk. rewrite L4 in Hj. apply (KB (ac_x C) (4 * T) IBx); [clear - Hj Hkk HrqF; lia | clear - Hj Hkk A05 HrqF; lia | clear - Hj Hkk A35 HrqF HrqT Rh; lia | clear - Hj Hkk Hne; lia | clear - Hj Hkk A15 HrqF Rh; lia].
- change (ht_lens (ht_ins (ac_H C) h c 1)). unfold ht_lens, ht_ins. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_T]. rewrite !zlen_setz, !zlen_set_col. exact HL0. }
pose proof (hk_pix_views sp0 img fmt N imgl Hfmt Himgl W mem i Himg Hi) as (_ & _ & _ & Cok). fold c in Cok.
split; [split; [exact HCr'|]; unfold C_ins, ac_with; cbn [ac_H ac_ent]; apply (ht_ins_inv _ _ Hinv h c 1 Hfs Hfree Cok ltac:(lia)); fold cnt; fold T; clear - Rcnt HT5; lia|].
split; [exact Hi|]. split; [exact Hha|].
split; [unfold C_ins, ac_with; cbn [ac_ent]; rewrite map_app, zsum_app; cbn [map snd zsum]; clear - Hz; lia|].
split; [split; [exact SP72' | exact SP56']|]. split; [exact Rcf|].
split.
{ split; [apply (RD 5%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 6%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 7%bv (SLit fmt) fmt eq_refl eq_refl eq_refl)|].
split; [apply (RD 16%bv (SOff 47 0) hv16 eq_refl); [rewrite (denot_off E 47 hv16 0 (HV 15%nat _ eq_refl) O16), Z.add_0_r; reflexivity | reflexivity]|].
split; [apply (RD 17%bv (SOff 46 0) hv17 eq_refl); [rewrite (denot_off E 46 hv17 0 (HV 14%nat _ eq_refl) O17), Z.add_0_r; reflexivity | reflexivity]|].
rewrite (HKR 27%bv ltac:(cbv; clear; tauto)). exact G27. }
split; [apply (RD 10%bv (SOff 32 40) (tb + 40) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 13%bv (SOff 54 0) cf eq_refl); [rewrite (denot_off E 54 cf 0 E54), Z.add_0_r; [reflexivity | clear - Rcf; lia] | reflexivity]|].
split; [apply (RD 14%bv (SOff 32 44) (tb + 44) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 28%bv (SOff 21 0) i eq_refl); [rewrite (denot_off E 21 i 0), Z.add_0_r; [reflexivity | rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hi HN; lia] | reflexivity]|].
apply (RD 29%bv (SOff 23 0) ha eq_refl); [rewrite (denot_off E 23 ha 0), Z.add_0_r; [reflexivity | rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hha; lia] | reflexivity].
Qed.
End H6.
