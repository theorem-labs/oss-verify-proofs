(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of rec_code_declared on fuzz_command.asan, in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (cmpPixel's leaf walk): a seed lemma at the entry, then the executor's run/branch loop to every return. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdObj CmdRo CmdZsh PaNoChain rec_code_declared_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* the table's 58 entries as the 4-byte words the image holds (RO_rec_codes, lib/A/Prog/CmdRo.v) *)
Definition rcd_u32 : list Z := Eval vm_compute in
map (fun k => bytes_le_to_Z (firstn 4 (skipn (4 * k) RO_rec_codes))) (seq 0 58).
Definition rcd_chunks : list YP09.chunk := Eval vm_compute in
map (fun k => YP09.mkChunk (4 * Z.of_nat k) (CVal 4 (SLit (nth k rcd_u32 0)))) (seq 0 58).
(* atoms: 0..31 the registers at entry, 32 the shadow base; A_OBJ 0 the GOT word of the shadow-base cell, A_OBJ 12
   the cell, A_OBJ 40 the table rec_codes (lib/A/Prog/CmdList.v slots 0x2c98, 0x2ca4) *)
Definition rcd_Bx : sv := SOff 32 0.
Definition rcd_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 32; YP09.mkRegion (Some (A_OBJ 40)) 0 232 0 0 rcd_chunks ].
Definition rcd_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (A_OBJ 40, mkAF 0x21ba0 0x21ba0 3) ] [] [].
Definition ss_rcd : sstate := mkSS AF_rec_code_declared sr_atoms rcd_regions None rcd_facts.
Definition rcd_SH : list shent := [ mkSHE (A_OBJ 40) 0 232 ].
Definition rcd_extra : list word := [Z_to_bv 64 SB].
(* the table's entries as the executor holds them after `lw`: each 32-bit entry sign-extended to 64 bits *)
Definition rcd_s64 : list Z := Eval vm_compute in map (fun r => r mod 2 ^ 64) RecFacts.rec_codes.
Lemma rcd_s64_eq : rcd_s64 = map (fun r => r mod 2 ^ 64) RecFacts.rec_codes.
Proof. vm_compute. reflexivity. Qed.
Lemma rcd_s64_In : forall v, existsb (Z.eqb v) rcd_s64 = true -> In v rcd_s64.
Proof. intros v H. apply existsb_exists in H as (x & Hx & Hv). apply Z.eqb_eq in Hv. subst x. exact Hx. Qed.
Lemma rcd_codes_range : forall r, In r RecFacts.rec_codes -> -2^31 <= r < 2^31.
Proof.
assert (H : forallb (fun r => (-2^31 <=? r) && (r <? 2^31)) RecFacts.rec_codes = true) by (vm_compute; reflexivity).
intros r Hr. rewrite forallb_forall in H. specialize (H r Hr). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma rcd_hit : forall c v, -2^31 <= c < 2^31 -> In v rcd_s64 -> Z_to_bv 64 v = Z_to_bv 64 c -> RecFacts.declared c = true.
Proof.
intros c v Rc Hv Heq. rewrite rcd_s64_eq in Hv. apply in_map_iff in Hv as (r & <- & Hr).
pose proof (rcd_codes_range r Hr) as Rr.
apply (f_equal bv_unsigned) in Heq. rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq.
change (bv_modulus 64) with (2 ^ 64) in Heq. rewrite Z.mod_mod in Heq by lia.
assert (Hrc : r = c) by (clear - Heq Rr Rc; Z.div_mod_to_equations; lia). subst r.
unfold RecFacts.declared. apply existsb_exists. exists c. split; [exact Hr | apply Z.eqb_refl].
Qed.
Lemma rcd_miss : forall c, -2^31 <= c < 2^31 -> (forall v, In v rcd_s64 -> Z_to_bv 64 v <> Z_to_bv 64 c) ->
RecFacts.declared c = false.
Proof.
intros c Rc H. destruct (RecFacts.declared c) eqn:Hd; [exfalso|reflexivity].
unfold RecFacts.declared in Hd. apply existsb_exists in Hd as (r & Hr & Hcr). apply Z.eqb_eq in Hcr. subst r.
apply (H (c mod 2 ^ 64)).
- rewrite rcd_s64_eq. exact (in_map (fun r => r mod 2 ^ 64) _ _ Hr).
- apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma rcd_br : forall E v c b, ew E 10 = Z_to_bv 64 c ->
branch_taken BC_EQ (sv_denot E (SLit v)) (sv_denot E (SOff 10 0)) = b -> (b = true <-> Z_to_bv 64 v = Z_to_bv 64 c).
Proof.
intros E v c b H10 Hb. subst b. rewrite branch_eq_U. unfold U. cbn [sv_denot].
rewrite H10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite Z.eqb_eq.
split; [intros H; apply bv_eq; exact H | intros ->; reflexivity].
Qed.
Lemma rcd_br_ne : forall E v c, ew E 10 = Z_to_bv 64 c ->
branch_taken BC_EQ (sv_denot E (SLit v)) (sv_denot E (SOff 10 0)) = false -> Z_to_bv 64 v <> Z_to_bv 64 c.
Proof. intros E v c H10 Hb Heq. apply (proj2 (rcd_br E v c false H10 Hb)) in Heq. discriminate Heq. Qed.
(* the image bytes of the table, entry by entry, as the chunks of the symbolic region hold them *)
Lemma rcd_u32_range : forall k, (k < 58)%nat -> 0 <= nth k rcd_u32 0 < 2 ^ 32.
Proof.
assert (H : forallb (fun v => (0 <=? v) && (v <? 2 ^ 32)) rcd_u32 = true) by (vm_compute; reflexivity).
intros k Hk. rewrite forallb_forall in H.
assert (Hl : (k < length rcd_u32)%nat) by (change (length rcd_u32) with 58%nat; exact Hk).
specialize (H (nth k rcd_u32 0) (nth_In rcd_u32 0 Hl)).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma rcd_bytes : forall k j, (k < 58)%nat -> (j < 4)%nat ->
Z_to_bv 8 (le_byte (nth k rcd_u32 0) 4 j) = nth (4 * k + j) RO_rec_codes (Z_to_bv 8 0).
Proof.
assert (H : forallb (fun k => forallb (fun j => Z.eqb (bv_unsigned (Z_to_bv 8 (le_byte (nth k rcd_u32 0) 4 j)))
(bv_unsigned (nth (4 * k + j) RO_rec_codes (Z_to_bv 8 0)))) (seq 0 4)) (seq 0 58) = true) by (vm_compute; reflexivity).
intros k j Hk Hj. rewrite forallb_forall in H. specialize (H k ltac:(apply in_seq; lia)).
rewrite forallb_forall in H. specialize (H j ltac:(apply in_seq; lia)). apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Lemma rcd_mbytes : forall segs H mem, cmd_ro_ok (aview segs H mem) -> forall i, (i < 232)%nat ->
mbyte segs (mrestrict H mem) (0x21ba0 + Z.of_nat i) = Some (nth i RO_rec_codes (Z_to_bv 8 0)).
Proof.
intros segs H mem HRO i Hi.
assert (HA : abytes_atR (aview segs H mem) 0x21ba0 RO_rec_codes)
by (unfold cmd_ro_ok, cmd_ro_bytes in HRO; decompose [and] HRO; assumption).
specialize (HA i ltac:(apply Nat.lt_le_trans with 232%nat; [exact Hi | apply Nat.leb_le; vm_compute; reflexivity])).
unfold aview in HA.
destruct (mbyte segs (mrestrict H mem) (0x21ba0 + Z.of_nat i)) as [b|]; cbn in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma rcd_chunks_ok : forall segs E m base,
(forall i, (i < 232)%nat -> mbyte segs m (base + Z.of_nat i) = Some (nth i RO_rec_codes (Z_to_bv 8 0))) ->
Forall (YP09.chunk_ok segs E m base) rcd_chunks.
Proof.
intros segs E m base H.
assert (HC : rcd_chunks = map (fun k => YP09.mkChunk (4 * Z.of_nat k) (CVal 4 (SLit (nth k rcd_u32 0)))) (seq 0 58))
by (vm_compute; reflexivity).
rewrite HC. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk.
pose proof (rcd_u32_range k ltac:(lia)) as Rk.
apply (chunk_ok_val segs E m base (4 * Z.of_nat k) 4 (SLit (nth k rcd_u32 0)) (nth k rcd_u32 0)).
- reflexivity.
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Rk.
- cbn. lia.
- intros j Hj. change (N.to_nat 4) with 4%nat in Hj |- *.
replace (base + 4 * Z.of_nat k + Z.of_nat j) with (base + Z.of_nat (4 * k + j)) by lia.
rewrite H by lia. rewrite <- (rcd_bytes k j ltac:(lia) Hj). reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Definition EC (regs : bvmap 5 word) : env := Eimg (Ereg regs rcd_extra).
Lemma rcd_val_objs : cmd_val_objs -> VAL (A_OBJ 0) = 0xa63f0 /\ VAL (A_OBJ 12) = 0xb10b8 /\ VAL (A_OBJ 40) = 0x21ba0.
Proof.
intros HVO.
rewrite (HVO 0%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)), (HVO 12%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)),
(HVO 40%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
vm_compute. repeat split.
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* rec_codes is a registered global of 232 bytes (asan_globals descriptor): its bytes lie in the allocator record's
   zero-shadow range (0x21b80, 0x21c88 - 0x21b80) (lib/A/AF0m.v Tfib_zero_shadow), so they are addressable at every
   AR state (CmdZsh's cmd_addressable_in) *)
Lemma rcd_zsh : forall ly S W mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF 0x21ba0 232.
Proof.
intros ly S W mem md HAR.
assert (Hin : In (0x21b80, 0x21c88 - 0x21b80) AF0m.Tfib_zero_shadow)
by (unfold AF0m.Tfib_zero_shadow; repeat (first [left; reflexivity | right])).
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md _ 0x21ba0 232 HAR Hin); cbn [fst snd]; first [reflexivity | lia].
Qed.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Lemma rcd_entry : forall ly S W (regs : bvmap 5 word) mem md,
afn_pre_na SEGS B REC_CODE_DECLARED_STK ly S W regs mem md ->
cmd_ro_ok (aview SEGS (w_H W) mem) -> cmd_val_objs ->
st_ok_pi SEGS VAL (EC regs) ss_rcd
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rec_code_declared)) mem (seg_rom SEGS)))
/\ sh_ok SEGS rcd_Bx rcd_SH (EC regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HPRE HRO HVO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CODE_DECLARED_STK = 16) by reflexivity.
destruct (rcd_val_objs HVO) as (V0 & V12 & V40).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell, V0, V12 in Kgot. rewrite HBcell, V12 in Kcell.
rewrite restrict_mkst_fx.
set (E := EC regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs rcd_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 0xa63f0)
by (subst E; unfold EC; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V0; reflexivity).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 0xb10b8)
by (subst E; unfold EC; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V12; reflexivity).
assert (EO40 : ew E (A_OBJ 40) = Z_to_bv 64 0x21ba0)
by (subst E; unfold EC; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V40; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (rcd_mbytes SEGS (w_H W) mem HRO) as HMB.
split.
- unfold ss_rcd. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rcd_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 0) 0xa63f0 EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) 0xb10b8);
[cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) 0xb10b8 EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 rcd_Bx SB);
[unfold rcd_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB (A_OBJ 40) 0x21ba0 EO40) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply rcd_chunks_ok. exact HMB.
+ apply pairwise_disjoint_of_extents. unfold rcd_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) 0xa63f0 EO0), (VB (A_OBJ 12) 0xb10b8 EO12), (VB (A_OBJ 40) 0x21ba0 EO40) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite WS in Hstk0, Hslo. clear - Hslo Hshi H47 C1 Hceil.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rcd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, EO40, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite WS in Hslo. clear - Hal16 Hslo Hshi H47 C1 Hceil. unfold SB.
repeat split; first [lia | reflexivity].
- unfold sh_ok, rcd_SH. constructor; [|constructor].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
assert (UB : U E rcd_Bx = SB)
by (unfold U, rcd_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; apply unsigned_lit_small; unfold SB; lia).
assert (UT : U E (SOff (A_OBJ 40) 0) = 0x21ba0)
by (unfold U; cbn [sv_denot]; rewrite EO40, Z.add_0_r, Z_to_bv_bv_unsigned; apply unsigned_lit_small; lia).
rewrite UB, UT. split.
+ rewrite <- (aview_rd_of SEGS). pose proof (rcd_zsh ly S W mem md HAR) as Z1.
replace (0x21ba0 + 0) with 0x21ba0 by lia. replace (232 - 0) with 232 by lia. exact Z1.
+ intros a Ha. cbn [Z.min Z.max] in Ha. unfold SB. lia.
Qed.
(* The walk: the executor runs from the entry to the compare of each entry (beq a5,a0 at 0x891a8); the inline check
   before it (0x8919c-0x891a0) is removed by the tokens, since the table's shadow is addressable. Each compare splits:
   equal returns 1 (0x891d4), not equal goes on to the next entry; after the 58th, 0 is returned (0x891dc). *)
Theorem trec_code_declared_spec_holds : trec_code_declared_spec B MT.
Proof.
unfold trec_code_declared_spec.
intros ly S W regs mem md c HPRE HROD H10 Rc HRO HVO Hev.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rcd_entry ly S W regs mem md HPRE HRO HVO) as [HS SHOK].
pose proof (ajournal_init_na SEGS B REC_CODE_DECLARED_STK [] ly S W regs mem md HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
unfold YK0s.ret_ok in Hra.
remember (EC regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs rcd_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs rcd_extra) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_rec_code_declared)) with (Z_to_bv 64 (BASE + AF_rec_code_declared)).
let ew_c Ex := first [exact E10 | cbn [ew ewset]; rewrite ?ew_ewset_other by lia; exact E10] in
let br_hit := idtac;
lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?Ex (SLit ?v)) (sv_denot ?Ex (SOff 10 0)) = true |- _ =>
let H10x := fresh "H10x" in let HIT := fresh "HIT" in
assert (H10x : ew Ex 10 = Z_to_bv 64 c) by ew_c Ex;
pose proof (rcd_hit c v Rc (rcd_s64_In v ltac:(vm_compute; reflexivity)) (proj1 (rcd_br Ex v c true H10x Hb) eq_refl)) as HIT;
clear Hb H10x
end in
let br_miss := idtac;
lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?Ex (SLit ?v)) (sv_denot ?Ex (SOff 10 0)) = false |- _ =>
let H10x := fresh "H10x" in let NE := fresh "NE" in
assert (H10x : ew Ex 10 = Z_to_bv 64 c) by ew_c Ex;
pose proof (rcd_br_ne Ex v c H10x Hb) as NE; clear Hb H10x
end in
let rcd_val := idtac;
lazymatch goal with
| HIT : RecFacts.declared c = true |- _ => rewrite HIT; reflexivity
| |- _ =>
let v := fresh "v" in let Hv := fresh "Hv" in
rewrite (rcd_miss c Rc ltac:(intros v Hv; unfold rcd_s64 in Hv; cbn [In] in Hv;
repeat (destruct Hv as [<-|Hv]; [assumption|]); destruct Hv)); reflexivity
end in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in let HAEx := fresh "HAEx" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
(* the last entry's check leaves two fresh atoms (the token and the slow path's register), so the env at a return
   may be E extended by ewset *)
assert (HAEx : env_agree 32 (Ereg regs rcd_extra) Ex)
by (first [exact HAE | destruct HAE as [HA HD]; split;
[intros n Hn; rewrite !ew_ewset_other by lia; apply HA; exact Hn | rewrite !ed_ewset; exact HD]]);
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold apost_base;
eexists _, _, _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs rcd_extra HS); [exact HAEx | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10; rcd_val|];
(* no call, no frame: the run keeps the layout and the allocator state *)
split; [apply Permutation_refl | split; reflexivity]
end in
let rec go n := idtac;
lazymatch n with Datatypes.O => fail "go: out of fuel" | Datatypes.S ?m =>
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
(* the run leaves the model as with_vm_backing (m_vm_lazy md) mat md in the goal and in the journal; name it, so that
   58 runs in a row do not nest it 58 deep (unnamed, the term doubles at each run) *)
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
tryif is_var mdq then idtac else (let mdv := fresh "mdv" in set (mdv := mdq) in *; clearbody mdv) end;
srr_norm_model;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM rcd_Bx rcd_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K rcd_Bx Bspan rcd_SH (start K rcd_Bx Bspan rcd_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan; [br_hit; go m | br_miss; go m]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end end in
(* 58 compares, one return each, and the return after the last *)
go 60%nat.
Qed.
End h.
End f.
End d.
