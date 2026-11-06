(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase YC1h GrantRo YC88 ACj1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* reac_ctrl_identity_poll_block (0x82d3c) of fuzz_grant's ASan build: for an index
   0..5 and a non-null 34-byte destination the call copies the i-th row of the image's
   read-only table GRANT_GROUPB (object 19, 0x21040) through __asan_memcpy and returns
   0; for any other index it returns -1 and writes nothing outside its own stack.
   Model: GrantSweepModel.GBz (Pau's address-free row of the identity poll). *)
Lemma ipb_le5 : forall i, - 2 ^ 31 <= i < 2 ^ 31 -> (i mod 2 ^ 64 <=? 5) = ((0 <=? i) && (i <=? 5))%bool.
Proof.
intros i Hi. destruct (Z_lt_le_dec i 0) as [Hneg|Hpos].
- rewrite <- (Z.mod_add i 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (i + 1 * 2 ^ 64)) by lia.
replace (0 <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
apply Z.leb_gt. lia.
- rewrite (Z.mod_small i) by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. reflexivity.
Qed.
Lemma ipb_gbz_len : forall i, length (GBz i) = 34%nat.
Proof.
intros i. unfold GBz, gb_tail.
repeat (match goal with |- context [if ?c then _ else _] => destruct c end); reflexivity.
Qed.
Lemma ipb_gball_nth : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat ->
nth (Z.to_nat (34 * i) + j)%nat GBallz 0 = nth j (GBz i) 0.
Proof.
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]]; intros j Hj;
(do 34 (destruct j as [|j]; [vm_compute; reflexivity|]); exfalso; lia).
Qed.
Lemma ipb_gbz_rangeb : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat ->
((0 <=? nth j (GBz i) 0) && (nth j (GBz i) 0 <? 256))%bool = true.
Proof.
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct E as [-> | [-> | [-> | [-> | [-> | ->]]]]]; intros j Hj;
(do 34 (destruct j as [|j]; [vm_compute; reflexivity|]); exfalso; lia).
Qed.
Lemma ipb_gbz_range : forall i, 0 <= i <= 5 -> forall j, (j < 34)%nat -> 0 <= nth j (GBz i) 0 < 256.
Proof.
intros i Hi j Hj. pose proof (ipb_gbz_rangeb i Hi j Hj) as H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma ipb_gball_len : length GBallz = 204%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma ipb_sh_small : forall x, 0 <= x -> x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x H0 H1. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 H0 ltac:(lia)).
assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma ipb_hull_small : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (2147450880 + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Definition A_ctrl_identity_poll_blockP : Z := BASE + AF_reac_ctrl_identity_poll_block.
Definition TIPB_STK : Z := 16 + ESTACK.
Definition IPB_SB : Z := 0x7fff8000.
Definition A_GRANT_GROUPB : Z := VAL (A_OBJ 19).
Lemma ipb_tbl_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a [(s & Hs & _ & Hr) | Hgot].
- apply pa_img_range. exists s. split; [exact Hs | exact Hr].
- apply pa_img_range. apply pa_relro_img. exact Hgot.
Qed.
Lemma ipb_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Section h.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Definition tipb_kept (W : world SEGS) (memc mem2 : word -> option byte) (sp o : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TIPB_STK <= a < sp) -> ~ (o <= a < o + 34) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a.
Definition tipb_post (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem0 md0 own lyc Sc
(W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (i o : Z)
: world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\ tipb_kept W memc mem2 (spZ regs) o /\
(if ((0 <=? i) && (i <=? 5))%bool
then getr regs2 10 = w64 0 /\ garr8 SEGS (mrestrict (w_H W) mem2) o (GBz i)
else getr regs2 10 = w64 (-1) /\
(forall a, o <= a < o + 34 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)).
Definition tctrl_identity_poll_block_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i o : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 i -> - 2 ^ 31 <= i < 2 ^ 31 -> getr regs 11 = w64 o ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TIPB_STK -> spZ regs <= sp0 ->
(spZ regs <= o \/ o + 34 <= spZ regs - TIPB_STK) ->
(forall a, o <= a < o + 34 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
(A_GRANT_GROUPB + 204 <= o \/ o + 34 <= A_GRANT_GROUPB) ->
amem_range o 34 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 34 ->
shadow_hull_vis (aview SEGS (w_H W) memc) o 34 ->
garr8 SEGS (mrestrict (w_H W) memc) A_GRANT_GROUPB GBallz ->
In (A_GRANT_GROUPB, 204) GLOBS ->
IMG_LO + 64 <= A_GRANT_GROUPB -> A_GRANT_GROUPB + 204 + 64 <= IMG_HI ->
SRr SEGS W (cfg_at SEGS A_ctrl_identity_poll_blockP regs memc mdc)
(tipb_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs i o).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis HGM : globs_marked SEGS B GLOBS.
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Definition IBx : sv := SOff 32 0.
Definition IBspan : Z * Z := (IPB_SB, IPB_SB + 2 ^ 44 - 1).
Definition ipb_regions : smem := [ stack_region 16 ].
Definition ipb_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] [].
Definition ss_ipb : sstate := mkSS AF_reac_ctrl_identity_poll_block sr_atoms ipb_regions None ipb_facts.
Definition ipb_SH : list shent := [].
Definition EI (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma ipb_denot_tbl : forall E np ni p i, ew E np = Z_to_bv 64 p -> ew E ni = Z_to_bv 64 i ->
0 <= p -> p + 34 * i + 34 <= 2 ^ 63 -> 0 <= i < 6 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff ni 0) (SLit 34)) (SOff np 0)) = Z_to_bv 64 (p + 34 * i).
Proof.
intros E np ni p i Hp Hi Rp Rpi Ri. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite U_SLit, (U_atom E ni i Hi), (U_atom E np p Hp) by lia.
rewrite (zcanon_id 34) by (unfold M64; lia). rewrite (zcanon_id (i * 34)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ipb_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TIPB_STK -> spZ regs <= sp0 ->
st_ok_pi SEGS VAL (EI regs) ss_ipb
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_ctrl_identity_poll_blockP) memc (seg_rom SEGS)))
/\ sh_ok SEGS IBx ipb_SH (EI regs) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hlo Hhi.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold TIPB_STK in Hlo; lia).
rewrite restrict_mkst_fx.
set (E := EI regs) in *.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold EI; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_ipb, A_ctrl_identity_poll_blockP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ipb_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable SEGS). apply Hpres. unfold TIPB_STK in Hlo. lia.
+ cbn [ipb_regions pairwise_disjoint all_disjoint]. exact (conj I I).
+ split; [|split; [exact I | exact I]].
cbn [ipb_facts f_atoms atoms_ok].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
- unfold sh_ok, ipb_SH. apply Forall_nil.
Qed.
Ltac ipb_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].
Ltac ipb_keep K H rg Wx HU :=
lazymatch type of K with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (H : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg - 16 <= a < spZ rg) ->
aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
by (intros a Ha Hn; apply (ipb_aview_of_frame Wx Ex rsx mA mB a K); [|exact Ha];
intros (r & Hin & Hr); vm_compute in Hin;
destruct Hin as [Hin | Hin]; [subst r | destruct Hin];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
rewrite HU in Hr; lia)
end.
Theorem pb_ctrl_identity_poll_block : tctrl_identity_poll_block_spec.
Proof.
unfold tctrl_identity_poll_block_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i o
HJ HROD Hra Hra4 Hgp Htp H10 Hi H11 Hal16 Hlo Hhi Hdisj Hwr Hsep Hamr HRAo Hhull Htbl HinG Hm1 Hm2.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ipb_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hlo Hhi) as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold TIPB_STK in Hlo; lia).
assert (Ho4096 : 4096 <= o).
{ destruct (Hwr o ltac:(lia)) as [Hw _].
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k o HJ Hw)
as (_ & [[Hc1 _] | [[[Ha1 _] _] | (cid & pos & _ & [[[Ha1 _] _] | [[Hs1 _] _]])]]); lia. }
assert (Ho47 : o + 34 <= 140737488355327)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (HloU : sp0 - STK <= spZ regs - 4112) by (unfold TIPB_STK in Hlo; lia).
unfold TIPB_STK in Hdisj.
assert (Htb0 : IMG_LO + 64 <= A_GRANT_GROUPB /\ A_GRANT_GROUPB + 268 <= IMG_TOP) by lia.
assert (Hmod : (spZ regs - 16 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite Hal16 in D1. rewrite Hsp0al in D2.
replace (spZ regs - 16 - sp0) with ((spZ regs / 16 - 1 - sp0 / 16) * 16) by lia.
apply Z_mod_mult. }
remember (EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
by (intros n Hn; subst E; unfold EI; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Eo19 : ew E (A_OBJ 19) = Z_to_bv 64 A_GRANT_GROUPB)
by (unfold A_GRANT_GROUPB; subst E; unfold EI; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ui : U E (SOff 10 0) = i mod 2 ^ 64).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite Z_to_bv_unsigned. reflexivity. }
assert (Uo : U E (SOff 11 0) = o mod 2 ^ 64).
{ unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite Z_to_bv_unsigned. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 A_ctrl_identity_poll_blockP) with (Z_to_bv 64 A_ctrl_identity_poll_blockP).
(* ------------------------------------------------------------------ *)
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF HG. ipb_keep HFr KA regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK IBspan.
- (* 5 <u i : the index is out of range *)
rewrite branch_ltu_U, U_SLit, Ui in Hc. rewrite (zcanon_id 5) in Hc by (unfold M64; lia).
apply Z.ltb_lt in Hc.
assert (Hout : ((0 <=? i) && (i <=? 5))%bool = false)
by (rewrite <- ipb_le5 by lia; apply Z.leb_gt; lia).
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF HG. ipb_keep HFr KB regs W Usp. clear HFr.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tipb_post. split; [reflexivity|].
eexists _, _, _.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); reflexivity | reflexivity]]
| vm_compute; reflexivity]|].
split.
{ unfold tipb_kept, TIPB_STK. intros a Ha Hn1 Hn2. cbn [ms_mem].
rewrite (KB a Ha ltac:(lia)). exact (KA a Ha ltac:(lia)). }
rewrite Hout. split; [cbn [ms_regs]; rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
intros a Ha. cbn [ms_mem].
rewrite (KB a ltac:(lia) ltac:(lia)). exact (KA a ltac:(lia) ltac:(lia)).
- (* 0 <= i <= 5 *)
rewrite branch_ltu_U, U_SLit, Ui in Hc. rewrite (zcanon_id 5) in Hc by (unfold M64; lia).
apply Z.ltb_ge in Hc.
assert (Hin5 : ((0 <=? i) && (i <=? 5))%bool = true)
by (rewrite <- ipb_le5 by lia; apply Z.leb_le; lia).
assert (Hi5 : 0 <= i <= 5).
{ apply andb_prop in Hin5 as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. lia. }
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF HG. ipb_keep HFr KC1 regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK IBspan.
+ (* the destination is 0: impossible, it is a client byte *)
exfalso.
lazymatch goal with H : branch_taken BC_EQ _ _ = true |- _ =>
rewrite branch_eq_U, Uo, U_SLit in H; rewrite (zcanon_id 0) in H by (unfold M64; lia);
apply Z.eqb_eq in H; rewrite (Z.mod_small o) in H by lia; lia end.
+ (* the copy *)
paj_run_tok RUN HS HJ SHOK IBspan; [ipb_awr regs Usp|].
clear HF HG. ipb_keep HFr KC regs W Usp. clear HFr.
lazymatch type of KC with forall a, _ -> _ -> aview _ _ ?mT a = _ =>
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview SEGS (w_H W) mT a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn; rewrite (KC a Ha Hn); rewrite (KC1 a Ha Hn); exact (KA a Ha Hn)) end.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2.
prreg HS (3%bv : bv 5) Rgp2. prreg HS (4%bv : bv 5) Rtp2.
assert (Eo19' : ew E 260%nat = Z_to_bv 64 A_GRANT_GROUPB) by exact Eo19.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (A_GRANT_GROUPB + 34 * i))
(ipb_denot_tbl E 260%nat 10%nat A_GRANT_GROUPB i Eo19' E10 ltac:(lia) ltac:(lia) ltac:(lia)) Ra1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
assert (HspT : spZ rT = spZ regs - 16)
by (unfold spZ at 1; rewrite Rsp2, Usp; rewrite unsigned_lit_small by lia; lia) end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY W rT mT
STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k o (A_GRANT_GROUPB + 34 * i) 34
(spZ regs - 16 - sp0) _ HJ) end.
- rewrite Ra0, E11. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia.
- lia.
- lia.
- rewrite HspT. lia.
- exact Hmod.
- lia.
- lia.
- rewrite Rgp2, E3. exact Hgp.
- rewrite Rtp2, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
- intros a Ha. split; [exact (proj1 (Hwr a ltac:(lia))) | lia].
- exact Hamr.
- eapply (range_addressable_agree (aview SEGS (w_H W) memc) _ SHADOW_OFF o 34); [|exact HRAo].
intros x Hx. pose proof (ipb_sh_small x ltac:(lia) ltac:(lia)) as Hsx.
apply KT; lia.
- intros _ s Hs. pose proof (ipb_hull_small o 34 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hss.
rewrite (KT s ltac:(lia) ltac:(lia)). apply Hhull. exact Hs.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split.
- rewrite (KT a ltac:(lia) ltac:(lia)).
pose proof (proj1 (Htbl (Z.to_nat (a - A_GRANT_GROUPB)) ltac:(rewrite ipb_gball_len; lia)) 0%nat ltac:(lia)) as V0.
replace (A_GRANT_GROUPB + Z.of_nat (Z.to_nat (a - A_GRANT_GROUPB)) + Z.of_nat 0) with a in V0
by (rewrite Z2Nat.id by lia; lia).
unfold aview. rewrite V0. discriminate.
- rewrite HspT. lia. }
split; [lia|].
split; [unfold amem_range, kLowMemEnd; left; lia|].
lazymatch goal with HJX : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT ?mdT _ |- _ =>
destruct (ro_read_ok_glob SEGS B GLOBS lyc Sc W mT mdT A_GRANT_GROUPB 204
(A_GRANT_GROUPB + 34 * i) 34 HGM HinG HIMGSH (proj1 HJX)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [HRA' HH'] end.
split; [exact HRA' | intros _; exact HH']. }
cbv beta. intros W2 c2 _ Hpost.
destruct Hpost as (HW2 & regs2 & mem2 & md2 & Hc2 & HJX2 & HP2 & Ha0' & Heff & Hfrc & Hpres2).
subst W2. subst c2.
pose proof HJX2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2' & _ & _ & _).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
- intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply Hfrc; lia.
- intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
rewrite Usp in Ha. apply (apresent_writable SEGS). apply Hpres2'. lia. }
specialize (HSX HRKX). rewrite <- restrict_mkst_fx in HSX.
assert (SHOKX : sh_ok SEGS IBx ipb_SH (havoc E 33 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
by (unfold sh_ok, ipb_SH; apply Forall_nil).
assert (HEIX : img_env VAL A_LIM (havoc E 33 (map (getr regs2) CLOB)))
by (apply img_env_havoc; [exact HEI | cbv; lia]).
paj_run_tok RUN HSX HJX2 SHOKX IBspan; [ipb_awr regs Usp|].
clear HF HG. ipb_keep HFr KD regs W Usp. clear HFr.
prreg HSX (10%bv : bv 5) R10. prreg HSX (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HSX eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tipb_post. split; [reflexivity|].
eexists _, _, _.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJX2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HSX);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); reflexivity | reflexivity]]
| vm_compute; reflexivity]|].
split.
{ unfold tipb_kept, TIPB_STK. intros a Ha Hn1 Hn2. cbn [ms_mem].
rewrite (KD a Ha ltac:(lia)). rewrite (Hfrc a Ha ltac:(lia) ltac:(lia)).
exact (KT a Ha ltac:(lia)). }
rewrite Hin5. split; [cbn [ms_regs]; rewrite R10; reflexivity|].
intros j Hj. rewrite ipb_gbz_len in Hj. split.
{ intros kk Hkk. assert (Hkk0 : kk = 0%nat) by lia. subst kk.
pose proof (proj1 (Htbl (Z.to_nat (34 * i) + j)%nat ltac:(rewrite ipb_gball_len; lia)) 0%nat ltac:(lia)) as V0.
rewrite <- (ipb_gball_nth i Hi5 j Hj). cbn [ms_mem]. rewrite <- V0.
replace (A_GRANT_GROUPB + Z.of_nat (Z.to_nat (34 * i) + j) + Z.of_nat 0)
with (A_GRANT_GROUPB + 34 * i + Z.of_nat j) by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
replace (o + Z.of_nat j + Z.of_nat 0) with (o + Z.of_nat j) by lia.
apply (mbyte_of_aview_eq SEGS).
rewrite (KD (o + Z.of_nat j) ltac:(lia) ltac:(lia)).
rewrite (Heff (Z.of_nat j) ltac:(lia)).
exact (KT (A_GRANT_GROUPB + 34 * i + Z.of_nat j) ltac:(lia) ltac:(lia)).
}
exact (ipb_gbz_range i Hi5 j Hj).
Qed.
End h.
End f.
End d.
