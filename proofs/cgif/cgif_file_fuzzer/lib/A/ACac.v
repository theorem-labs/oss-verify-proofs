(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACai ACam ACan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac psrr_branch_pi RUNP BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_step_pi tpi ss) in
lazymatch r with
| PStop (SR_branch ?c ?a ?b) => apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
| _ => fail "psrr_branch_pi: state is not stuck at a branch:" r
end end
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma st_ok_pi_add_cond : forall E ss ms c a b, st_ok_pi SEGS VAL E ss ms -> branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok_pi SEGS VAL E (add_cond ss (mkAC c a b)) ms.
Proof. intros E ss ms c a b HS Hb. exact (st_ok_add_cond SEGS E (abs_ss VAL ss) ms c a b HS Hb). Qed.
Lemma denot_add_atoms : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (a + b).
Proof.
intros E n1 n2 a b H1 H2 Ha Hb Hab. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 a H1), (U_atom E n2 b H2) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma aview_kept_ro : forall E rs H (m m' : word -> option byte),
(forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) ->
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hro HF a Ha. apply (aview_kept_out E rs H m m' HF a Ha).
intros (r & Hin & Hr). pose proof (Hro r Hin). lia.
Qed.
Lemma regions_kept_out2 : forall E H (m m2 : word -> option byte) lo hi lo2 hi2 rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (lo2 <= a < hi2) -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo \/ hi <= base_val E (YP09.r_base r) + YP09.r_lo r) /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo2 \/ hi2 <= base_val E (YP09.r_base r) + YP09.r_lo r)) rs ->
Forall (region_kept SEGS E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi lo2 hi2 rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3 & H4). split; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma denot_mul_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (h * w).
Proof.
intros E nh nw h w Hh Hw Rh Rw. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 32 - 1) * (2 ^ 32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh h Hh) by lia. rewrite (U_atom E nw w Hw) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma il_denot_shadow : forall E n b p k,
ew E n = Z_to_bv 64 p -> ew E b = Z_to_bv 64 SB -> 0 <= p -> p + k < 2 ^ 47 -> 0 <= k ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (SB + (p + k) / 8).
Proof.
intros E n b p k Hn Hb Hp Hk Hk0. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom_off E n p k Hn) by lia. rewrite (U_atom E b SB Hb) by (unfold SB; lia).
rewrite (zcanon_id 3) by (rewrite M64_val; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((p + k) / 8)) by (rewrite M64_val; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (0 <= (p + k) / 8) by (apply Z.div_pos; lia). assert ((p + k) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite (Z.add_comm SB). apply zcanon_id. rewrite M64_val. unfold SB. lia.
Qed.
Lemma il_src_val : forall img i w, 0 <= img -> 0 <= i < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> img + i * w < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 img) (mul_div M_MUL (Z_to_bv 64 i) (Z_to_bv 64 w)) = Z_to_bv 64 (img + i * w).
Proof.
intros img i w Himg Hi Hw Hs. rewrite zmd64_sound. unfold zmd64. cbn [zmd_raw].
rewrite (zcanon_id i), (zcanon_id w) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; nia). apply alu64_add_lit.
Qed.
Lemma il_src_val_b : forall img i w, 0 <= img -> 0 <= i < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> img + i * w < 2 ^ 64 ->
alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 i) (Z_to_bv 64 w)) (Z_to_bv 64 img) = Z_to_bv 64 (img + i * w).
Proof.
intros img i w Himg Hi Hw Hs. rewrite zmd64_sound. unfold zmd64. cbn [zmd_raw].
rewrite (zcanon_id i), (zcanon_id w) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; nia).
replace (img + i * w) with (i * w + img) by lia. apply alu64_add_lit.
Qed.
Lemma il_cond_src : forall E ni nw nimg i w img,
ew E ni = Z_to_bv 64 i -> ew E nw = Z_to_bv 64 w -> ew E nimg = Z_to_bv 64 img ->
0 <= img -> 0 <= i < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> img + i * w < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff ni 0) (SOff nw 0)) (SOff nimg 0))) (sv_denot E (SOff nimg 0)) = true.
Proof.
intros E ni nw nimg i w img Hi Hw Himg Rimg Ri Rw Hs. unfold branch_taken. rewrite bv_ltu_unsigned. cbn [sv_denot].
rewrite Hi, Hw, Himg, !Z.add_0_r, !Z_to_bv_bv_unsigned. rewrite il_src_val_b by lia.
assert (0 <= i * w) by (apply Z.mul_nonneg_nonneg; lia).
rewrite !unsigned_lit_small by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma il_U_src : forall E ni nw nimg i w img,
ew E ni = Z_to_bv 64 i -> ew E nw = Z_to_bv 64 w -> ew E nimg = Z_to_bv 64 img ->
0 <= img -> 0 <= i < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> img + i * w < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff ni 0) (SOff nw 0)) (SOff nimg 0)) = img + i * w.
Proof.
intros E ni nw nimg i w img Hi Hw Himg Rimg Ri Rw Hs. assert (0 <= i * w) by (apply Z.mul_nonneg_nonneg; lia).
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E ni i Hi), (U_atom E nw w Hw), (U_atom E nimg img Himg) by lia.
rewrite (zcanon_id (i * w)) by (rewrite M64_val; lia). rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
Lemma il_cond_nz : forall E ni nw nimg i w img,
ew E ni = Z_to_bv 64 i -> ew E nw = Z_to_bv 64 w -> ew E nimg = Z_to_bv 64 img ->
1 <= img -> 0 <= i < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> img + i * w < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SAlu ALU_ADD (SMd M_MUL (SOff ni 0) (SOff nw 0)) (SOff nimg 0)) (SLit 1)))) (sv_denot E (SLit 0)) = true.
Proof.
intros E ni nw nimg i w img Hi Hw Himg Rimg Ri Rw Hs. assert (0 <= i * w) by (apply Z.mul_nonneg_nonneg; lia).
rewrite branch_ne_U, U_SAlu, U_SAlu, !U_SLit, (il_U_src E ni nw nimg i w img Hi Hw Himg) by lia.
cbn [zalu_raw]. rewrite (zcanon_id 1), (zcanon_id 0) by (rewrite M64_val; lia).
destruct (Z.ltb_spec (img + i * w) 1) as [Hlt | Hge]; [lia|]. rewrite (zcanon_id 0) by (rewrite M64_val; lia).
change (Z.lxor 1 0) with 1. rewrite (zcanon_id 1) by (rewrite M64_val; lia). reflexivity.
Qed.
Lemma il_cond_next : forall E ncur nw cur w,
ew E ncur = Z_to_bv 64 cur -> ew E nw = Z_to_bv 64 w -> 0 <= cur -> 0 <= w -> cur + w < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SAlu ALU_ADD (SOff ncur 0) (SOff nw 0))) (sv_denot E (SOff ncur 0)) = true.
Proof.
intros E ncur nw cur w Hcur Hw Rcur Rw Hs. unfold branch_taken. rewrite bv_ltu_unsigned. cbn [sv_denot].
rewrite Hw, Hcur, !Z.add_0_r, !Z_to_bv_bv_unsigned. unfold w64. rewrite alu64_add_lit.
rewrite !unsigned_lit_small by lia. apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Section IL.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Definition ILN_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 27; 28; 29; 30; 31]%bv.
Definition ILN_KEPT' : list (bv 5) := [2; 3; 4; 8; 9; 20; 23; 25]%bv.
Lemma iln_clob_cases : forall r : bv 5, reg_in r ILN_CLOB = false ->
r = 0%bv \/ r = 19%bv \/ r = 21%bv \/ r = 22%bv \/ r = 24%bv \/ r = 26%bv \/ In r ILN_KEPT'.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity
| right; right; right; right; left; reflexivity | right; right; right; right; right; left; reflexivity
| vm_compute in Hr; discriminate | right; right; right; right; right; right; cbv; tauto] |]). destruct Hin.
Qed.
Definition ILN4_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 27; 28; 29; 30; 31]%bv.
Definition ILN4_KEPT' : list (bv 5) := [2; 3; 4; 8; 9; 20; 23; 25]%bv.
Lemma iln4_clob_cases : forall r : bv 5, reg_in r ILN4_CLOB = false ->
r = 0%bv \/ r = 19%bv \/ r = 21%bv \/ r = 22%bv \/ r = 24%bv \/ r = 26%bv \/ In r ILN4_KEPT'.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity
| right; right; right; right; left; reflexivity | right; right; right; right; right; left; reflexivity
| vm_compute in Hr; discriminate | right; right; right; right; right; right; cbv; tauto] |]). destruct Hin.
Qed.
Definition sh_of (n : nat) (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff 32 0).
Definition iln_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 12 (CVal 2 (SOff 34 0)); YP09.mkChunk 14 (CVal 2 (SOff 35 0))] ].
Lemma iln_regions_ro : forall r, In r iln_regions -> YP09.r_whi r <= YP09.r_wlo r.
Proof. intros r [<- | []]. cbn. lia. Qed.
Definition iln_regs :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 21%bv (SOff 25 12)) 22%bv (SOff 25 14)) 26%bv (sh_of 25 0)) 19%bv (sh_of 25 12)) 24%bv (sh_of 25 14).
Definition iln_facts (cur : nat) : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (cur, HPTR 0); (25%nat, HPTR 3); (33%nat, HPTR 0);
(34%nat, mkAF 1 65535 0); (35%nat, mkAF 1 65535 0); (18%nat, mkAF 0 65535 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_iln (cur : nat) (pc : Z) : sstate := mkSS pc iln_regs iln_regions None (iln_facts cur).
Ltac iln_obl HJx Hx25 Hx32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 25 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 25 (cfp + 8) c Hx25) by lia | rewrite (U_atom Ex 25 (cfp + 8) Hx25) by lia ];
eapply (obl_of_range SEGS _ _ Ex (SOff 32 0) _ len cfp 40);
[ eapply (range_addressable_entry_frame SEGS _ LAWS); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & Hrg & Hxr); cbn [In] in Hrg; destruct Hrg as [<- | []]; cbn [fst snd] in Hxr; clear - Hxr Hrh C2 C3; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; change (req_size RAW_SIZE) with 48 in *; lia
| exact HAR0 | exact HRA ]
| rewrite (U_atom Ex 32 SB Hx32); [reflexivity | unfold SB; lia] | lia | lia ] end.
End IL.
End e.
End d.
