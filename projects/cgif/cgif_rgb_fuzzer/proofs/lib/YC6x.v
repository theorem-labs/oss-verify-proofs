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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC7d YC6k YC6t YC7c YC6l YC6m YC6n YC6o YC6p YC6q YC6r YC6u YC77 YC78 YC79.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
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
Local Notation at_RA1C := (at_RA1C B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation cfgat regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs)) md).
Lemma hl_rs0_T0 : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C = 524309 ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA1C lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) HTK.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
assert (ETn : ac_Tn C = 1048583) by (unfold ac_Tn; rewrite HTK; reflexivity).
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 524309 524309 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (rewrite HTK; clear; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite HTK. reflexivity. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (13%bv, SLit 1); (14%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] xat
[mkAC BC_EQ (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl ltac:(assumption) eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G13. reflexivity.
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (rewrite ?HTK; clear - Rcnt; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite HTK. clear - Rcnt. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, USRL, (U_lit E 0) by lia. reflexivity. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_realloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ [2; 9; 8; 3; 4; 25; 19]%bv HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
assert (HK18 : getr (ms_regs ms) 18 = getr regs 18)
by (rewrite G18; apply (RD 18%bv (SOff 44 0) hv18 eq_refl); [rewrite (denot_off E 44 hv18 0 (HV 12%nat _ eq_refl) O18), Z.add_0_r; reflexivity | reflexivity]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HC' : hcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C) end.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)]. intros r Hr. unfold HK_CONST in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; try (apply HKR; cbv; clear; tauto). exact HK18. }
destruct HC' as [HCr' Hinv'].
pose proof HCr' as (_ & _ & _ & _ & (Af' & Ah' & Au' & _) & _).
split; [|split; [|split]].
- split; [exact (rcore_of_hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HCr')|].
split; [split; [exact Af' | split; [exact Ah' | exact Au']]|].
split; [split; [exact Hinv|]; split; [exact HTc|]; split; [unfold ac_T; fold T; rewrite HTK; unfold MAX_TABLE_SIZE; clear; lia|]; split; [exact Hi|]; split; [exact Hha | exact Hz]|].
split; [split; [unfold ac_T; fold T; clear - Hk; lia | exact (proj2 Hk)]|]. split; [split; [exact SP72' | exact SP56']|].
rewrite ETn.
split; [exact (RD 20%bv (SLit 3145749) 3145749 eq_refl eq_refl eq_refl)|].
split; [apply (RD 21%bv (SOff 32 24) (tb + 24) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 22%bv (SLit 1048583) 1048583 eq_refl eq_refl eq_refl)|].
apply (RD 26%bv (SOff 42 0) hv26 eq_refl); [rewrite (denot_off E 42 hv26 0 (HV 10%nat _ eq_refl) O26), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 10%bv (SOff 36 0) (ac_p C) eq_refl); [rewrite (denot_off E 36 (ac_p C) 0 E36 Bp), Z.add_0_r; reflexivity | reflexivity].
- rewrite ETn. exact (RD 11%bv (SLit 3145749) 3145749 eq_refl eq_refl eq_refl).
- exact (RD 1%bv (SLit HL_RA1R) HL_RA1R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_rs0_T1 : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C = 1048583 ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA1C lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) HTK.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
assert (ETn : ac_Tn C = 2097169) by (unfold ac_Tn; rewrite HTK; reflexivity).
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 1048583 1048583 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (rewrite HTK; clear; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite HTK. reflexivity. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (13%bv, SLit 1); (14%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] xat
[mkAC BC_EQ (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl ltac:(assumption) eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G13. reflexivity.
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (rewrite ?HTK; clear - Rcnt; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite HTK. clear - Rcnt. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, USRL, (U_lit E 0) by lia. reflexivity. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_realloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ [2; 9; 8; 3; 4; 25; 19]%bv HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
assert (HK18 : getr (ms_regs ms) 18 = getr regs 18)
by (rewrite G18; apply (RD 18%bv (SOff 44 0) hv18 eq_refl); [rewrite (denot_off E 44 hv18 0 (HV 12%nat _ eq_refl) O18), Z.add_0_r; reflexivity | reflexivity]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HC' : hcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C) end.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)]. intros r Hr. unfold HK_CONST in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; try (apply HKR; cbv; clear; tauto). exact HK18. }
destruct HC' as [HCr' Hinv'].
pose proof HCr' as (_ & _ & _ & _ & (Af' & Ah' & Au' & _) & _).
split; [|split; [|split]].
- split; [exact (rcore_of_hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HCr')|].
split; [split; [exact Af' | split; [exact Ah' | exact Au']]|].
split; [split; [exact Hinv|]; split; [exact HTc|]; split; [unfold ac_T; fold T; rewrite HTK; unfold MAX_TABLE_SIZE; clear; lia|]; split; [exact Hi|]; split; [exact Hha | exact Hz]|].
split; [split; [unfold ac_T; fold T; clear - Hk; lia | exact (proj2 Hk)]|]. split; [split; [exact SP72' | exact SP56']|].
rewrite ETn.
split; [exact (RD 20%bv (SLit 6291507) 6291507 eq_refl eq_refl eq_refl)|].
split; [apply (RD 21%bv (SOff 32 24) (tb + 24) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 22%bv (SLit 2097169) 2097169 eq_refl eq_refl eq_refl)|].
apply (RD 26%bv (SOff 42 0) hv26 eq_refl); [rewrite (denot_off E 42 hv26 0 (HV 10%nat _ eq_refl) O26), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 10%bv (SOff 36 0) (ac_p C) eq_refl); [rewrite (denot_off E 36 (ac_p C) 0 E36 Bp), Z.add_0_r; reflexivity | reflexivity].
- rewrite ETn. exact (RD 11%bv (SLit 6291507) 6291507 eq_refl eq_refl eq_refl).
- exact (RD 1%bv (SLit HL_RA1R) HL_RA1R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_rs0_T2 : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C = 2097169 ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA1C lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) HTK.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
assert (ETn : ac_Tn C = 4194319) by (unfold ac_Tn; rewrite HTK; reflexivity).
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 2097169 2097169 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (rewrite HTK; clear; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite HTK. reflexivity. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (13%bv, SLit 1); (14%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] xat
[mkAC BC_EQ (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl ltac:(assumption) eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G13. reflexivity.
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (rewrite ?HTK; clear - Rcnt; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite HTK. clear - Rcnt. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, USRL, (U_lit E 0) by lia. reflexivity. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_realloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ [2; 9; 8; 3; 4; 25; 19]%bv HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
assert (HK18 : getr (ms_regs ms) 18 = getr regs 18)
by (rewrite G18; apply (RD 18%bv (SOff 44 0) hv18 eq_refl); [rewrite (denot_off E 44 hv18 0 (HV 12%nat _ eq_refl) O18), Z.add_0_r; reflexivity | reflexivity]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HC' : hcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C) end.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)]. intros r Hr. unfold HK_CONST in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; try (apply HKR; cbv; clear; tauto). exact HK18. }
destruct HC' as [HCr' Hinv'].
pose proof HCr' as (_ & _ & _ & _ & (Af' & Ah' & Au' & _) & _).
split; [|split; [|split]].
- split; [exact (rcore_of_hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HCr')|].
split; [split; [exact Af' | split; [exact Ah' | exact Au']]|].
split; [split; [exact Hinv|]; split; [exact HTc|]; split; [unfold ac_T; fold T; rewrite HTK; unfold MAX_TABLE_SIZE; clear; lia|]; split; [exact Hi|]; split; [exact Hha | exact Hz]|].
split; [split; [unfold ac_T; fold T; clear - Hk; lia | exact (proj2 Hk)]|]. split; [split; [exact SP72' | exact SP56']|].
rewrite ETn.
split; [exact (RD 20%bv (SLit 12582957) 12582957 eq_refl eq_refl eq_refl)|].
split; [apply (RD 21%bv (SOff 32 24) (tb + 24) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 22%bv (SLit 4194319) 4194319 eq_refl eq_refl eq_refl)|].
apply (RD 26%bv (SOff 42 0) hv26 eq_refl); [rewrite (denot_off E 42 hv26 0 (HV 10%nat _ eq_refl) O26), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 10%bv (SOff 36 0) (ac_p C) eq_refl); [rewrite (denot_off E 36 (ac_p C) 0 E36 Bp), Z.add_0_r; reflexivity | reflexivity].
- rewrite ETn. exact (RD 11%bv (SLit 12582957) 12582957 eq_refl eq_refl eq_refl).
- exact (RD 1%bv (SLit HL_RA1R) HL_RA1R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_rs0_T3 : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C = 4194319 ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA1C lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) HTK.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
assert (ETn : ac_Tn C = 8388617) by (unfold ac_Tn; rewrite HTK; reflexivity).
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 4194319 4194319 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (rewrite HTK; clear; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite HTK. reflexivity. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (13%bv, SLit 1); (14%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] xat
[mkAC BC_EQ (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl ltac:(assumption) eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G13. reflexivity.
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (rewrite ?HTK; clear - Rcnt; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite HTK. clear - Rcnt. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, USRL, (U_lit E 0) by lia. reflexivity. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_realloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ [2; 9; 8; 3; 4; 25; 19]%bv HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
assert (HK18 : getr (ms_regs ms) 18 = getr regs 18)
by (rewrite G18; apply (RD 18%bv (SOff 44 0) hv18 eq_refl); [rewrite (denot_off E 44 hv18 0 (HV 12%nat _ eq_refl) O18), Z.add_0_r; reflexivity | reflexivity]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HC' : hcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C) end.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)]. intros r Hr. unfold HK_CONST in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; try (apply HKR; cbv; clear; tauto). exact HK18. }
destruct HC' as [HCr' Hinv'].
pose proof HCr' as (_ & _ & _ & _ & (Af' & Ah' & Au' & _) & _).
split; [|split; [|split]].
- split; [exact (rcore_of_hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HCr')|].
split; [split; [exact Af' | split; [exact Ah' | exact Au']]|].
split; [split; [exact Hinv|]; split; [exact HTc|]; split; [unfold ac_T; fold T; rewrite HTK; unfold MAX_TABLE_SIZE; clear; lia|]; split; [exact Hi|]; split; [exact Hha | exact Hz]|].
split; [split; [unfold ac_T; fold T; clear - Hk; lia | exact (proj2 Hk)]|]. split; [split; [exact SP72' | exact SP56']|].
rewrite ETn.
split; [exact (RD 20%bv (SLit 25165851) 25165851 eq_refl eq_refl eq_refl)|].
split; [apply (RD 21%bv (SOff 32 24) (tb + 24) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 22%bv (SLit 8388617) 8388617 eq_refl eq_refl eq_refl)|].
apply (RD 26%bv (SOff 42 0) hv26 eq_refl); [rewrite (denot_off E 42 hv26 0 (HV 10%nat _ eq_refl) O26), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 10%bv (SOff 36 0) (ac_p C) eq_refl); [rewrite (denot_off E 36 (ac_p C) 0 E36 Bp), Z.add_0_r; reflexivity | reflexivity].
- rewrite ETn. exact (RD 11%bv (SLit 25165851) 25165851 eq_refl eq_refl eq_refl).
- exact (RD 1%bv (SLit HL_RA1R) HL_RA1R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_rs0_T4 : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C = 8388617 ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA1C lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha (HC & Hi & Hha & Hz & [SP72 SP56] & Rcf & (G5 & G6 & G7 & G16 & G17 & G27) & G10 & G13 & G14 & G28 & G29) HTK.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
assert (ETn : ac_Tn C = 16777216) by (unfold ac_Tn; rewrite HTK; reflexivity).
unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hinv as (_ & (Hcnt & Hlen & _) & _). fold T in Hcnt.
pose proof (zsum_ge_length (ac_ent C) (ent_freq_pos _ _ Hinv)) as Hzl.
set (cnt := ht_cnt (ac_H C)) in *.
assert (Rcnt : 0 <= cnt <= 10000) by (clear - Hcnt Hzl Hlen Hz Hi HN; lia).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([_ Bf] & [_ Bh] & [_ Bu] & [_ Bp] & [_ Bx] & [_ Bc] & [_ BT] & _). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
set (xat := [(38%nat, mkAF 0 10000 0); (39%nat, mkAF 8388617 8388617 0)]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T).
set (xv := [i; ha]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall n z, nth_error (vals ++ xv) n = Some z -> ew E (32 + n) = Z_to_bv 64 z).
{ intros n z Hn. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 (ac_p C)) by exact (HV 4%nat _ eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 cnt) by exact (HV 6%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 i) by exact (HV 20%nat _ eq_refl).
assert (E53 : ew E 53 = Z_to_bv 64 ha) by exact (HV 21%nat _ eq_refl).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (USRL : U E (SAlu ALU_SRL (SOff 39 0) (SLit 24)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 39 T E39) by (rewrite HTK; clear; lia). rewrite (U_lit E 24) by lia. change (Z.land 24 63) with 24.
rewrite HTK. reflexivity. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_RT false [(10%bv, SOff 32 40); (13%bv, SLit 1); (14%bv, SOff 32 44)] [ck 56 (SOff 53 0)] [ck 72 (SOff 52 0)] [] [] [] xat
[mkAC BC_EQ (SAlu ALU_SRL (SOff 39 0) (SLit 24)) (SLit 0)] [] []
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) cnt T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl ltac:(assumption) eq_refl eq_refl) as [HS SHOK].
all: fold vals; fold E.
{ repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
- rewrite G10. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G13. reflexivity.
- rewrite G14. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 56 8 _ ha); [rewrite (denot_off E 53 ha 0 E53), Z.add_0_r; [reflexivity | clear - Hha; lia] | clear - Hha; lia | lia | exact SP56]. }
{ apply Forall_cons; [|apply Forall_nil]. unfold ck. apply (chunk_ok_val trasegs E _ s1v 72 8 _ i); [rewrite (denot_off E 52 i 0 E52), Z.add_0_r; [reflexivity | clear - Hi HN; lia] | clear - Hi HN; lia | lia | exact SP72]. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ intros e []. }
{ exact I. }
{ subst xat. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E38, E39.
rewrite !unsigned_lit_small by (rewrite ?HTK; clear - Rcnt; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite HTK. clear - Rcnt. repeat split; lia. }
{ cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, USRL, (U_lit E 0) by lia. reflexivity. }
{ exact I. }
{ constructor. }
assert (HAE : env_agree 54 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_realloc_tra.
{ apply (hk_awr_ok s1v tb fmt E false _ _ _ [] [] STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 54 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb fmt _ false _ _ _ [] [] _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X | intros (rr & [] & _)]. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 54 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ [2; 9; 8; 3; 4; 25; 19]%bv HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e z, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 z -> sv_atoms_lt 54 e = true -> getr (ms_regs ms) r = Z_to_bv 64 z)
by (intros r e z Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 54 E Ex e HAE1 Hat); exact Dv);
assert (SP72' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 52 0)] 72 (SOff 52 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 52 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E52 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56' : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 53 0)] 56 (SOff 53 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 53 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E53 | clear - Hha; lia] | clear - Hha; lia]) end.
assert (HK18 : getr (ms_regs ms) 18 = getr regs 18)
by (rewrite G18; apply (RD 18%bv (SOff 44 0) hv18 eq_refl); [rewrite (denot_off E 44 hv18 0 (HV 12%nat _ eq_refl) O18), Z.add_0_r; reflexivity | reflexivity]).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => assert (HC' : hcore lyc Sc W (ms_regs ms) (ms_mem ms) mdx k C) end.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [|intros a Ha H1 _; exact (KM1 a Ha H1)]. intros r Hr. unfold HK_CONST in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; try (apply HKR; cbv; clear; tauto). exact HK18. }
destruct HC' as [HCr' Hinv'].
pose proof HCr' as (_ & _ & _ & _ & (Af' & Ah' & Au' & _) & _).
split; [|split; [|split]].
- split; [exact (rcore_of_hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HCr')|].
split; [split; [exact Af' | split; [exact Ah' | exact Au']]|].
split; [split; [exact Hinv|]; split; [exact HTc|]; split; [unfold ac_T; fold T; rewrite HTK; unfold MAX_TABLE_SIZE; clear; lia|]; split; [exact Hi|]; split; [exact Hha | exact Hz]|].
split; [split; [unfold ac_T; fold T; clear - Hk; lia | exact (proj2 Hk)]|]. split; [split; [exact SP72' | exact SP56']|].
rewrite ETn.
split; [exact (RD 20%bv (SLit 50331648) 50331648 eq_refl eq_refl eq_refl)|].
split; [apply (RD 21%bv (SOff 32 24) (tb + 24) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [exact (RD 22%bv (SLit 16777216) 16777216 eq_refl eq_refl eq_refl)|].
apply (RD 26%bv (SOff 42 0) hv26 eq_refl); [rewrite (denot_off E 42 hv26 0 (HV 10%nat _ eq_refl) O26), Z.add_0_r; reflexivity | reflexivity].
- apply (RD 10%bv (SOff 36 0) (ac_p C) eq_refl); [rewrite (denot_off E 36 (ac_p C) 0 E36 Bp), Z.add_0_r; reflexivity | reflexivity].
- rewrite ETn. exact (RD 11%bv (SLit 50331648) 50331648 eq_refl eq_refl eq_refl).
- exact (RD 1%bv (SLit HL_RA1R) HL_RA1R eq_refl eq_refl eq_refl).
Qed.
Lemma hl_rs0 : forall lyc Sc W regs mem md k C i ha,
at_RT lyc Sc W regs mem md k C i ha 1 -> ac_T C < MAX_TABLE_SIZE ->
SRr trasegs W (cfgat regs HL_RT mem md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2, c2 = cfgat regs2 A_realloc_tra mem2 md2 /\ at_RA1C lyc Sc W regs2 mem2 md2 k C i ha).
Proof.
intros lyc Sc W regs mem md k C i ha HRT Hlt.
pose proof HRT as (((_ & _ & _ & _ & _ & _ & _ & HTc & _) & _) & _).
cbv [ts_chain In] in HTc. unfold MAX_TABLE_SIZE in Hlt.
destruct HTc as [HT | [HT | [HT | [HT | [HT | [HT | []]]]]]]; symmetry in HT;
[exact (hl_rs0_T0 _ _ _ _ _ _ _ _ _ _ HRT HT) | exact (hl_rs0_T1 _ _ _ _ _ _ _ _ _ _ HRT HT) | exact (hl_rs0_T2 _ _ _ _ _ _ _ _ _ _ HRT HT)
| exact (hl_rs0_T3 _ _ _ _ _ _ _ _ _ _ HRT HT) | exact (hl_rs0_T4 _ _ _ _ _ _ _ _ _ _ HRT HT) | exfalso; rewrite HT in Hlt; clear - Hlt; lia].
Qed.
End b.
