(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YI04.v:380-382, for libreac/fuzz_identity's ASan build (lib/A). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI16 YI00 YO0a YO0c YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentFrame IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require IdentSpec.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.IdentSpec(dg).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma pp_Uadd : forall E a b x y, U E a = x -> U E b = y -> 0 <= x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. lia. Qed.
Lemma pp_Uaddw : forall E a b x y, U E a = x -> U E b = y -> U E (SAlu ALU_ADD a b) = (x + y) mod 2 ^ 64.
Proof. intros E a b x y Ha Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. reflexivity. Qed.
Lemma pp_Uadd0 : forall E a x, U E a = x -> U E (SAlu ALU_ADD a (SLit 0)) = x.
Proof.
intros E a x Ha. pose proof (U_range E a) as Hr. rewrite Ha in Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. exact Hr.
Qed.
Lemma pp_Uaddm1 : forall E a x, U E a = x -> 1 <= x -> U E (SAlu ALU_ADD a (SLit (-1))) = x - 1.
Proof.
intros E a x Ha Hx. pose proof (U_range E a) as Hr. rewrite Ha in Hr. unfold M64 in Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit.
assert (Hm : zcanon (-1) = 2 ^ 64 - 1) by reflexivity. rewrite Hm. unfold zcanon, M64.
replace (x + (2 ^ 64 - 1)) with ((x - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
apply Z.mod_small. lia.
Qed.
Lemma pp_Uzx : forall E a x, U E a = x -> 0 <= x < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = x.
Proof.
intros E a x Ha Hx. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit.
change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
rewrite (Z.mod_small (x * 2 ^ 32)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply Z.mod_small. lia.
Qed.
Lemma pp_Uneg : forall E a x, U E a = x -> 0 < x < 2 ^ 64 -> U E (SAlu ALU_SUB (SLit 0) a) = 2 ^ 64 - x.
Proof.
intros E a x Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. change (zcanon 0) with 0. unfold zcanon, M64.
replace (0 - x) with ((2 ^ 64 - x) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma pp_Usrl3 : forall E a x, U E a = x -> U E (SAlu ALU_SRL a (SLit 3)) = x / 8.
Proof.
intros E a x Ha. pose proof (U_range E a) as Hr. rewrite Ha in Hr. unfold M64 in Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma pp_bv_eqm : forall z1 z2, z1 mod 2 ^ 64 = z2 mod 2 ^ 64 -> Z_to_bv 64 z1 = Z_to_bv 64 z2.
Proof.
intros z1 z2 H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). exact H.
Qed.
Lemma pp_vm1 : forall segs H (m : word -> option byte) a v,
aview segs H m a = Some v -> 0 <= v < 256 -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv Hr kk Hk.
assert (kk = 0)%nat by lia. subst kk. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [bb|] eqn:Hb; cbn in Hv; [| discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte, bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, <- Hv, !Z.mod_mod by lia.
pose proof (bv_unsigned_in_range 8 bb) as Hbr. change (bv_modulus 8) with 256 in Hbr.
rewrite (Z.mod_small (bv_unsigned bb) 256) by lia. reflexivity.
Qed.
Lemma pp_nth_rep : forall n i, (i < n)%nat -> nth i (map bv_unsigned (repeat (dg 0) n)) 0 = 48.
Proof.
induction n as [|n IH]; intros i Hi; [lia|].
destruct i as [|i]; cbn [repeat map nth]; [reflexivity | apply IH; lia].
Qed.
Lemma pp_hull_sub : forall (rd rd' : Z -> option Z) x n x' n',
shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
shadow_hull_vis rd' x' n'.
Proof.
intros rd rd' x n x' n' H H1 H2 H3 Hk s Hs.
assert (Hs' : shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8)
by (unfold shadow_addr in *; lia).
rewrite (Hk s Hs'). exact (H s Hs').
Qed.
Definition PP_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%bv.
Lemma pp_cs : forall (regs regs' : bvmap 5 word),
(forall q : bv 5, In q PP_KEPT -> getr regs' q = getr regs q) ->
forall r, acallee_saved r -> r <> 21 -> r <> 22 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs' HK r Hr H21 H22. apply HK. unfold acallee_saved in Hr. cbv [PP_KEPT In].
assert (H : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H as [->|H]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Ltac pp_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Ltac pp_keep KEEP PRES :=
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
lazymatch type of KEEP with forall a, _ -> aview ?sg _ _ a = aview _ _ ?mb a =>
let K2 := fresh "KEEP" in let P2 := fresh "PRES" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> aview sg H m1 a = aview sg H mb a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hin := fresh "Hin" in
    intros a Ha; transitivity (aview sg H m0 a); [| exact (KEEP a Ha)];
    apply (kept_of_frame Ex rs H m0 m1 (fun _ => False) HFr);
    [intros ? ? ? ? Hin; cbn in Hin; destruct Hin | exact Ha | tauto]);
assert (P2 : forall a, apresent H mb a -> apresent H m1 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; eapply apresent_grows; [exact HG | apply PRES; exact Ha]);
clear KEEP PRES; rename K2 into KEEP; rename P2 into PRES;
repeat match goal with H' : frame_of _ _ _ _ |- _ => clear H' | H' : mem_grows _ _ |- _ => clear H' end
end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IS___asan_memset).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma pd_pad : forall (K mn T p o : Z) (P : list byte)
W (regs : bvmap 5 word) memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k,
1 <= K <= 10 -> 0 <= mn <= 10 -> Z.of_nat (length P) = K ->
4096 <= T -> T + 10 <= alloc_ceiling -> in_app T 10 ->
p mod 8 = 0 -> (in_app p 8 \/ (alloc_ceiling <= p /\ p + 8 <= 2 ^ 47)) ->
spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 11 = Z_to_bv 64 K -> getr regs 19 = Z_to_bv 64 p -> getr regs 21 = Z_to_bv 64 mn ->
getr regs 23 = Z_to_bv 64 SHADOW_OFF -> getr regs 26 = Z_to_bv 64 T ->
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall a, T <= a < T + 10 -> awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF T 10 ->
shadow_hull_vis (aview SEGS (w_H W) memc) T 10 ->
garr8 SEGS (mrestrict (w_H W) memc) T (map bv_unsigned P) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 356))) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (AF_put_dec + 452))) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 10 = Z_to_bv 64 (T + Z.max K mn - 1) /\ getr regs' 13 = Z_to_bv 64 (T + Z.max K mn - 1) /\
getr regs' 12 = Z_to_bv 64 (- Z.max K mn) /\ getr regs' 14 = Z_to_bv 64 (SHADOW_OFF + p / 8) /\
getr regs' 21 = Z_to_bv 64 (Z.max K mn) /\
(forall r, acallee_saved r -> r <> 21 -> r <> 22 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
garr8 SEGS (mrestrict (w_H W) mem') T (map bv_unsigned (P ++ repeat (dg 0) (Z.to_nat (Z.max K mn - K)))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (T <= a < T + 10) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
intros K mn T p o P W regs memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k
HK Hmn HlenP HT0 HT1 HTapp Hp8 Hpapp Hsp Ho16 Ho0 HoS Hgp Htp G11 G19 G21 G23 G26 HJ HWR HRA HHULL HGA.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
clear Hstatic.
pose proof HTapp as HTb.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HTb.
assert (Hpb : 4096 <= p /\ p + 8 <= 2 ^ 47)
by (destruct Hpapp as [Hq | Hq]; [unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hq |]; lia).
clear Hpapp.
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
by (intros nn q Hq; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat (2%bv : bv 5) eq_refl).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (E11 : ew E 11 = Z_to_bv 64 K) by (rewrite (EE 11%nat (11%bv : bv 5) eq_refl); exact G11).
assert (E19 : ew E 19 = Z_to_bv 64 p) by (rewrite (EE 19%nat (19%bv : bv 5) eq_refl); exact G19).
assert (E21 : ew E 21 = Z_to_bv 64 mn) by (rewrite (EE 21%nat (21%bv : bv 5) eq_refl); exact G21).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 23%nat (23%bv : bv 5) eq_refl); exact G23).
assert (E26 : ew E 26 = Z_to_bv 64 T) by (rewrite (EE 26%nat (26%bv : bv 5) eq_refl); exact G26).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_put_dec + 356) sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 356))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full E (AF_put_dec + 356) sr_atoms regs [] (mkFacts [] [] []) (mrestrict (w_H W) memc)).
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- apply Forall_nil.
- cbn. tauto.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 23 0) [] E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a)
by (intros; reflexivity).
assert (PRES : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a Ha; exact Ha).
assert (UZX : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 32)) (SLit 32)) = K)
by (apply pp_Uzx; [apply (U_atom E 11 K E11); lia | lia]).
assert (U14 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 23 0)) = p / 8 + SHADOW_OFF).
{ apply pp_Uadd; [apply pp_Usrl3; apply (U_atom E 19 p E19); lia | apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia |].
  split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | unfold SHADOW_OFF; lia] | ].
  assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply awr_ok_nil. }
pp_keep KEEP PRES.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_geu_U, (U_atom E 11 K E11), (U_atom E 21 mn E21) in Hc by lia.
  assert (HKm : mn <= K) by (destruct (Z.ltb_spec K mn); [discriminate Hc | lia]). clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { apply awr_ok_nil. }
  pp_keep KEEP PRES.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + exfalso. rewrite branch_ltu_U, UZX, (U_atom E 21 mn E21) in Hc by lia.
    destruct (Z.ltb_spec K mn); [lia | discriminate Hc].
  + paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_put_dec + 452).
    { apply awr_ok_nil. }
    pp_keep KEEP PRES.
    pose proof HS as HSf.
    pmkst HS.
    pp_reg HS (10%bv : bv 5) Rg10. pp_reg HS (12%bv : bv 5) Rg12. pp_reg HS (13%bv : bv 5) Rg13.
    pp_reg HS (14%bv : bv 5) Rg14. pp_reg HS (21%bv : bv 5) Rg21.
    pose proof (regs_kept_of_st_ok_pi E _ _ regs [] PP_KEPT HSf HAE ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict] in HKR.
    assert (UZ0 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 32)) (SLit 32)) (SLit 0)) = K)
    by (apply pp_Uadd0; exact UZX).
    assert (UTK : U E (SAlu ALU_ADD (SOff 26 0)
    (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 32)) (SLit 32)) (SLit 0))) = T + K)
    by (apply pp_Uadd; [apply (U_atom E 26 T E26); lia | exact UZ0 | lia]).
    rewrite (Z.max_l K mn) by lia.
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?ms2) _ (ms_mem ?ms2) _) ?md2] =>
    exists (ms_regs ms2), (ms_mem ms2), md2 end.
    split; [reflexivity|]. split; [exact HJ|].
    split; [rewrite Rg10, denot_lit_U; f_equal; apply pp_Uadd0; apply pp_Uaddm1; [exact UTK | lia]|].
    split; [rewrite Rg13, denot_lit_U; f_equal; apply pp_Uaddm1; [exact UTK | lia]|].
    split.
    { rewrite Rg12, denot_lit_U, (pp_Uneg E _ K UZ0) by lia. apply pp_bv_eqm.
      replace (2 ^ 64 - K) with (- K + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    split; [rewrite Rg14, denot_lit_U, U14; f_equal; lia|].
    split; [rewrite Rg21, denot_lit_U, UZ0; reflexivity|].
    split; [exact (pp_cs regs _ HKR)|].
    split.
    { rewrite Z.sub_diag. cbn [Z.to_nat repeat]. rewrite app_nil_r.
      intros j Hj. destruct (HGA j Hj) as [Hv Hb]. split; [| exact Hb].
      rewrite length_map in Hj.
      eapply (val_mem_kept SEGS (w_H W) (w_H W) memc _ (T + Z.of_nat j) 1); [| exact Hv].
      intros kk Hkk. apply KEEP. lia. }
    split.
    { intros a Ha _ _. apply KEEP. exact Ha. }
    { exact PRES. }
- rewrite branch_geu_U, (U_atom E 11 K E11), (U_atom E 21 mn E21) in Hc by lia.
  assert (HKm : K < mn) by (destruct (Z.ltb_spec K mn); [lia | discriminate Hc]). clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { apply awr_ok_nil. }
  pp_keep KEEP PRES.
  rename KEEP into KEEPA. rename PRES into PRESA.
  prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  pp_reg HS (10%bv : bv 5) Ra0. pp_reg HS (12%bv : bv 5) Ra2.
  pmkst HS.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
    eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA IS___asan_memset) AMEMSET W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc _ k (T + K) 48 (mn - K) o (Z_to_bv 64 (BASE + 8224)) HJ) end.
    - rewrite Ra0, denot_lit_U. unfold w64. f_equal.
      apply pp_Uadd; [apply (U_atom E 26 T E26); lia | exact UZX | lia].
    - rewrite Ra1. reflexivity.
    - rewrite Ra2, denot_lit_U. unfold w64. f_equal.
      rewrite (pp_Uadd E _ (SLit 1) (mn - K - 1) 1); [lia | | apply U_lit; lia | lia].
      apply pp_Uzx; [| lia].
      rewrite (pp_Uaddw E _ _ (2 ^ 64 - 1 - K) mn (U_not E 11 K E11 ltac:(lia)) (U_atom E 21 mn E21 ltac:(lia))).
      replace (2 ^ 64 - 1 - K + mn) with ((mn - K - 1) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Rsp. first [rewrite Usp | rewrite E2]. exact Hsp.
    - exact Ho16.
    - exact Ho0.
    - exact HoS.
    - rewrite Rgp. exact E3.
    - rewrite Rtp. exact E4.
    - first [exact Rra | rewrite Rra; reflexivity].
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [apply HWR; lia | lia].
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
    - intros x Hx. destruct (HRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [| exact Hok].
      rewrite KEEPA; [exact Hs |]. unfold shadow_of_addr, SHADOW_OFF.
      split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
      assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
    - intros _. apply (pp_hull_sub _ _ T 10 (T + K) (mn - K) HHULL); [lia | lia | lia |].
      intros s Hs. apply KEEPA. unfold shadow_addr, SHADOW_OFF in Hs. lia.
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Heff & Hfr2 & Hpres2 & Hsame).
  jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)).
  rewrite <- restrict_mkst_fx in HS2.
  clear HS SHOK. rename HS2 into HS.
  assert (HEI2 : img_env VAL A_LIM (havoc E 200 (map (getr regs2) CLOB)))
  by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; reflexivity]).
  assert (SHOK : sh_ok SEGS (SOff 23 0) [] (havoc E 200 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
  by (apply Forall_nil).
  assert (F11 : ew (havoc E 200 (map (getr regs2) CLOB)) 11 = Z_to_bv 64 K) by (rewrite ew_havoc_old by lia; exact E11).
  assert (F19 : ew (havoc E 200 (map (getr regs2) CLOB)) 19 = Z_to_bv 64 p) by (rewrite ew_havoc_old by lia; exact E19).
  assert (F21 : ew (havoc E 200 (map (getr regs2) CLOB)) 21 = Z_to_bv 64 mn) by (rewrite ew_havoc_old by lia; exact E21).
  assert (F23 : ew (havoc E 200 (map (getr regs2) CLOB)) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite ew_havoc_old by lia; exact E23).
  assert (F26 : ew (havoc E 200 (map (getr regs2) CLOB)) 26 = Z_to_bv 64 T) by (rewrite ew_havoc_old by lia; exact E26).
  assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) (havoc E 200 (map (getr regs2) CLOB)))
  by (split; [intros nn Hnn; rewrite ew_havoc_old by lia; exact (proj1 HAE nn Hnn) | cbn [havoc ed]; exact (proj2 HAE)]).
  assert (VZX : U (havoc E 200 (map (getr regs2) CLOB)) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 32)) (SLit 32)) = K)
  by (apply pp_Uzx; [apply (U_atom _ 11 K F11); lia | lia]).
  assert (V14 : U (havoc E 200 (map (getr regs2) CLOB)) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 23 0)) = p / 8 + SHADOW_OFF).
  { apply pp_Uadd; [apply pp_Usrl3; apply (U_atom _ 19 p F19); lia | apply (U_atom _ 23 SHADOW_OFF F23); unfold SHADOW_OFF; lia |].
    split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | unfold SHADOW_OFF; lia] | ].
    assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF. lia. }
  assert (VTM : U (havoc E 200 (map (getr regs2) CLOB)) (SAlu ALU_ADD (SOff 21 (-1)) (SOff 26 0)) = mn - 1 + T)
  by (apply pp_Uadd; [apply (U_atom_off _ 21 mn (-1) F21); lia | apply (U_atom _ 26 T F26); lia | lia]).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a)
  by (intros; reflexivity).
  assert (PRES : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem2 a) by (intros a Ha; exact Ha).
  paj_run_tok RUN HS HJ2 SHOK Bspan.
  { apply awr_ok_nil. }
  pp_keep KEEP PRES.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + paj_run_to_tok RUNTO HS HJ2 SHOK Bspan (AF_put_dec + 452).
    { apply awr_ok_nil. }
    pp_keep KEEP PRES.
    pose proof HS as HSf.
    pmkst HS.
    pp_reg HS (10%bv : bv 5) Rg10. pp_reg HS (12%bv : bv 5) Rg12. pp_reg HS (13%bv : bv 5) Rg13.
    pp_reg HS (14%bv : bv 5) Rg14. pp_reg HS (21%bv : bv 5) Rg21.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] PP_KEPT HSf HAE2 ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict] in HKR.
    rewrite (Z.max_r K mn) by lia.
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?ms2) _ (ms_mem ?ms2) _) ?md2] =>
    exists (ms_regs ms2), (ms_mem ms2), md2 end.
    split; [reflexivity|]. split; [exact HJ2|].
    split; [rewrite Rg10, denot_lit_U, VTM; f_equal; lia|].
    split; [rewrite Rg13, denot_lit_U, VTM; f_equal; lia|].
    split.
    { rewrite Rg12, denot_lit_U, (pp_Uneg _ _ mn (U_atom _ 21 mn F21 ltac:(lia))) by lia. apply pp_bv_eqm.
      replace (2 ^ 64 - mn) with (- mn + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    split; [rewrite Rg14, denot_lit_U, V14; f_equal; lia|].
    split; [rewrite Rg21, denot_lit_U, (U_atom _ 21 mn F21) by lia; reflexivity|].
    split; [exact (pp_cs regs _ HKR)|].
    split.
    { intros j Hj. rewrite length_map, length_app, repeat_length in Hj. rewrite map_app.
      destruct (Nat.lt_ge_cases j (length P)) as [Hjl | Hjg].
      - rewrite app_nth1 by (rewrite length_map; lia).
        destruct (HGA j ltac:(rewrite length_map; lia)) as [Hv Hb]. split; [| exact Hb].
        eapply (val_mem_kept SEGS (w_H W) (w_H W) memc _ (T + Z.of_nat j) 1); [| exact Hv].
        intros kk Hkk. rewrite KEEP by lia. rewrite Hfr2 by lia. apply KEEPA. lia.
      - rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
        rewrite pp_nth_rep by lia. split; [| lia].
        apply pp_vm1; [| lia].
        rewrite KEEP by lia.
        replace (T + Z.of_nat j) with (T + K + (Z.of_nat j - K)) by lia.
        rewrite Heff by lia. reflexivity. }
    split.
    { intros a Ha HnT Hnw. rewrite KEEP by exact Ha. rewrite Hfr2 by lia. apply KEEPA. exact Ha. }
    { intros a Ha. apply PRES. apply Hpres2. apply PRESA. exact Ha. }
  + exfalso. rewrite branch_ltu_U, VZX, (U_atom _ 21 mn F21) in Hc by lia.
    destruct (Z.ltb_spec K mn); [discriminate Hc | lia].
Qed.
End e.
End d.
End b.
