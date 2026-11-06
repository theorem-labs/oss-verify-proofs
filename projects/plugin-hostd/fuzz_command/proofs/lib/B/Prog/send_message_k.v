(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/send_message_k.v (the ASan walk,
   a working branch 4f5a539710b) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86bf8):
   B's instruction stream is A's with only the pc-relative offsets changed (the program points keep their offsets
   from the entry), so the walk is A's at B's addresses (a Theorem Labs lane's pairing, a Theorem Labs lane's reloc). Re-fitted to a Theorem Labs lane's
   statement passes 4 and 5 (a working branch f490061c104): the contract's premises carry rounding mode 0 in place of
   astack_pres, and its post is apost_baseF. *)
(* Modified by Theorem Labs, 2026-10: the walk kit of send_message on plugin-hostd/fuzz_command's ASan+UBSan image, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close, a caller with calls) at
   origin/ossv/recipes c8557374ad2e, with the class-1 side-stack frame steps of A/ACk4.v, A/ACk5.v and A/ACkc.v
   (cgif_newgif and flushFrame): module paths, fuzz_command's listing (csym, cmd_listing), atoms below A_TEXT for the
   walk's own values, the symbolic states of send_message. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the walk tactics (cgif lib/A/ACkc.v, ACk5.v) *)
Ltac rnLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac rnB := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end.
Ltac rnTLF := lazymatch goal with T : PALibF _ |- _ => T end.
Ltac rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "rnHEI: no img_env fact for" E end.
Ltac hei_pose Eo kk ws :=
let Ho := rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 32)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
(* rebase the valuation after a havoc: every recorded atom fact moves to the new valuation *)
Ltac rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 32)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 32 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* ---------------------------------------------------------------- send_message's symbolic states *)
(* program points, as listing offsets (entry BASE + AF_send_message = 0x86bf8 on the pinned image) *)
Definition SM_ANDI_NEXT : Z := AF_send_message + 0x3c.     (* 0x86c34, after `andi sp,sp,-32` *)
Definition SM_RET_MALLOC : Z := AF_send_message + 0x118.   (* 0x86d10, the malloc wrapper's return *)
Definition SM_J : Z := AF_send_message + 0x138.            (* 0x86d30, after the copy *)
Definition SM_RET_RCL : Z := AF_send_message + 0x160.      (* 0x86d58, rec_clear's return *)
Definition SM_RET_VR : Z := AF_send_message + 0x168.       (* 0x86d60, verbs_receive's return *)
Definition SM_RET_FREE : Z := AF_send_message + 0x170.     (* 0x86d68, the free wrapper's return *)
(* the shadow base atom; the shadow band *)
Definition SMBx : sv := SOff 32 0.
Definition SMBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* atoms 32..34: the shadow base, the use-after-return cell, g_quitting's address *)
Definition sm_extra (uar : Z) : list word := map (Z_to_bv 64) [SB; uar; A_G_QUITTING].
Definition sm_regions0 : smem :=
[ stack_region 96; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition sm_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2);
  (34%nat, mkAF A_G_QUITTING A_G_QUITTING 2) ].
Definition ss_sm0 : sstate := mkSS AF_send_message sr_atoms sm_regions0 None (mkFacts sm_atoms0 [] []).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Lemma sm_entry : forall W ly S regs mem md ch,
afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sm_extra (as_uar_cell B)))) ss_sm0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_send_message)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : 96 <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sm_extra (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (sm_extra (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth sm_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_sm0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sm_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. rewrite <- SB_SHADOW_OFF in Kcell. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold sm_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hob0 Hob1 Hob12 Huar Hsep HSTK. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok sm_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB, A_G_QUITTING; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Huar Huar4 Hal16 HSTK. clear. unfold SB, A_G_QUITTING. intros.
repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia | match goal with |- ?g => idtac "FACTGOAL" g; fail end].
Qed.
End e.

(* ---------------------------------------------------------------- the segment interface
   The walk is split at the return points of malloc (P1), after the copy (P2, 0x86d30), after rec_clear (P3) and
   after verbs_receive (P4). Each segment file proves the statement at its start point from the statement at its end
   point (cgif_close's backward chain, A/ACh1.v:804-805). Every statement takes the entry state (ly S W regs mem md
   ch and the arguments) with the contract's premises bundled in `sm_cx`, the current state (lyc Sc Wc regs1 memc mdc)
   with concrete facts, and concludes the contract's post `sm_post` from the configuration at the point. *)
Section i.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the contract's premises, in the order of tsend_message_spec *)
Definition sm_cx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (ch : list (Z * Z * Z)) (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z)) : Prop :=
afn_pre SEGS B SEND_MESSAGE_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
Z.of_nat (length (frames S)) <= 3 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\ cmd_val_objs /\
getr regs 10 = w64 src /\ 0 <= src < 2 ^ 64 /\ getr regs 11 = w64 n /\ 0 <= n <= 8192 /\
Z.of_nat (length D) = n /\ abytes_atR (rdW W mem) src D /\
(n <> 0 -> in_blockA rest src n) /\
Permutation (ablocks B ly S) (O ++ rest) /\
rec_repA B ly S (rdW W mem) R O /\
(length (r_calls R) <= 2)%nat /\
(r_refuse R <> 0 -> declared (r_code R) = true) /\
st_nev S + EV_SEND_MESSAGE R D <= EV_MAX /\ blocks_bytes S + LIVE_SEND_MESSAGE <= LIVE_MAX /\
mo_ok MT S (XM_SEND_MESSAGE MT R D).
(* the contract's post, as tsend_message_spec states it *)
Definition sm_post (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (R : rstate) (D : list byte) (O rest : list (Z * Z)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SEND_MESSAGE_STK (ablocks_fp O ++ cmd_PG) regs ly S W mem md (EV_SEND_MESSAGE R D)
(fun ly' S' W' regs' mem' md' =>
 let '(R', _, quit) := vr_runA (RecModel.rec_clear R) D in
 exists O',
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 aval_mem (rdW W' mem') A_G_QUITTING 4 (if quit then 1 else 0) /\
 Permutation (ablocks B ly' S') (O' ++ rest) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SEND_MESSAGE /\
 mo_le MT S S' (XM_SEND_MESSAGE MT R D)).
(* the realigned stack pointer: `addi sp,sp,-96; andi sp,sp,-32` *)
Definition sm_sp1 (sp0 : Z) : Z := 32 * ((sp0 - 96) / 32).
(* the shadow address of the side-stack frame F, the value s7 holds *)
Definition SB_F (F : Z) : Z := SB + F / 8.
(* the prologue's saves: (offset from the entry sp, register) *)
Definition sm_saved_list : list (Z * Z) :=
[(-8, 1); (-16, 8); (-24, 9); (-32, 18); (-40, 19); (-48, 20); (-56, 21); (-64, 22); (-72, 23); (-80, 24); (-88, 25)].
Definition sm_saved (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
forall o r, In (o, r) sm_saved_list -> val_mem SEGS m (spZ regs + o) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the callee-saved registers every point after the frame set-up shares (F = frame_addr ly 1 fpos) *)
Definition sm_regs_core (regs regs1 : bvmap 5 word) (F n src : Z) : Prop :=
getr regs1 2 = w64 (sm_sp1 (spZ regs)) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = getr regs 2 /\ getr regs1 9 = w64 (sm_sp1 (spZ regs)) /\
getr regs1 18 = w64 F /\ getr regs1 19 = w64 n /\ getr regs1 20 = w64 src /\
getr regs1 23 = w64 (SB_F F) /\ getr regs1 24 = w64 F /\ getr regs1 25 = w64 SB /\
getr regs1 26 = getr regs 26 /\ getr regs1 27 = getr regs 27.
(* the frame's bytes the later steps read: the flag pointer at F + 120, msg.sender_id = 7 at F + 32, and the zero
   shadow bytes of msg (F + 32 .. F + 56) at SB_F F + 4 .. + 6 *)
Definition sm_frame (m : word -> option byte) (F FL : Z) : Prop :=
val_mem SEGS m (F + 120) 8 FL /\ val_mem SEGS m (F + 32) 4 7 /\
val_mem SEGS m (SB_F F + 4) 1 0 /\ val_mem SEGS m (SB_F F + 5) 1 0 /\ val_mem SEGS m (SB_F F + 6) 1 0.
(* the journal from the entry, with the frame (1, fpos) of this call on top *)
Definition sm_jr (FP : list (Z * Z)) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (fpos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
(memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
ajournal SEGS B SEND_MESSAGE_STK (spZ regs) FP ly S W mem md [(1, fpos)] lyc Sc Wc memc mdc k /\
frames Sc = (1, fpos) :: frames S.
(* P1: the malloc wrapper returned the copy's block res (0x86d10) *)
Definition SM_P1_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z))
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc (k fpos res : Z),
sm_cx ly S W regs mem md ch src n D R O rest ->
sm_jr [] ly S W regs mem md fpos lyc Sc Wc memc mdc k -> k <= 1 ->
sm_regs_core regs regs1 (frame_addr ly 1 fpos) n src -> getr regs1 10 = w64 res ->
sm_saved regs (mrestrict (w_H Wc) memc) ->
sm_frame (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) ->
ablocks B lyc Sc = ablocks B ly S ++ [(res, Z.max n 1)] -> 4096 <= res -> ~ In (res, Z.max n 1) (ablocks B ly S) ->
mo_le MT S Sc (mo_malloc MT (Z.max n 1)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SM_RET_MALLOC)) memc (seg_rom SEGS)) mdc)
(sm_post ly S W regs mem md R D O rest).
(* P2: after the copy, at 0x86d30 (both len = 0 and len <> 0 join here) *)
Definition SM_P2_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z))
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc (k fpos res : Z),
sm_cx ly S W regs mem md ch src n D R O rest ->
sm_jr [] ly S W regs mem md fpos lyc Sc Wc memc mdc k -> k <= 1 ->
sm_regs_core regs regs1 (frame_addr ly 1 fpos) n src ->
getr regs1 21 = w64 (frame_addr ly 1 fpos + 32) -> getr regs1 22 = w64 res ->
sm_saved regs (mrestrict (w_H Wc) memc) ->
sm_frame (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) ->
ablocks B lyc Sc = ablocks B ly S ++ [(res, Z.max n 1)] -> 4096 <= res -> ~ In (res, Z.max n 1) (ablocks B ly S) ->
abytes_atR (rdW Wc memc) res D ->
mo_le MT S Sc (mo_malloc MT (Z.max n 1)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SM_J)) memc (seg_rom SEGS)) mdc)
(sm_post ly S W regs mem md R D O rest).
(* P3: rec_clear returned (0x86d58); g_quitting holds 0, the recorder holds rec_clear R over O1 *)
Definition SM_P3_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z))
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc (k fpos res : Z) (O1 : list (Z * Z)),
sm_cx ly S W regs mem md ch src n D R O rest ->
sm_jr (ablocks_fp O ++ cmd_PG) ly S W regs mem md fpos lyc Sc Wc memc mdc k -> k <= 1 + EV_REC_CLEAR R ->
sm_regs_core regs regs1 (frame_addr ly 1 fpos) n src ->
getr regs1 21 = w64 (frame_addr ly 1 fpos + 32) -> getr regs1 22 = w64 res ->
sm_saved regs (mrestrict (w_H Wc) memc) ->
sm_frame (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos + 40) 8 res ->
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos + 48) 8 n ->
4096 <= res -> ~ In (res, Z.max n 1) (ablocks B ly S) ->
Permutation (ablocks B lyc Sc) (O1 ++ (res, Z.max n 1) :: rest) -> incl O1 O -> ~ In (res, Z.max n 1) O1 ->
abytes_atR (rdW Wc memc) res D ->
rec_repA B lyc Sc (rdW Wc memc) (RecModel.rec_clear R) O1 ->
aval_mem (rdW Wc memc) A_G_QUITTING 4 0 ->
blocks_bytes Sc <= blocks_bytes S + Z.max n 1 ->
mo_le MT S Sc (mo_malloc MT 8192 + XM_REC_CLEAR MT R) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SM_RET_RCL)) memc (seg_rom SEGS)) mdc)
(sm_post ly S W regs mem md R D O rest).
(* P4: verbs_receive returned (0x86d60) *)
Definition SM_P4_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z))
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc (k fpos res : Z),
sm_cx ly S W regs mem md ch src n D R O rest ->
sm_jr (ablocks_fp O ++ cmd_PG) ly S W regs mem md fpos lyc Sc Wc memc mdc k ->
k <= 1 + EV_REC_CLEAR R + ev_vr (RecModel.rec_clear R) D ->
sm_regs_core regs regs1 (frame_addr ly 1 fpos) n src ->
getr regs1 21 = w64 (frame_addr ly 1 fpos + 32) -> getr regs1 22 = w64 res ->
sm_saved regs (mrestrict (w_H Wc) memc) ->
sm_frame (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr ly 1 fpos + 40) 8 res ->
4096 <= res -> ~ In (res, Z.max n 1) (ablocks B ly S) ->
(let '(R', _, quit) := vr_runA (RecModel.rec_clear R) D in
 exists O', rec_repA B lyc Sc (rdW Wc memc) R' O' /\
 aval_mem (rdW Wc memc) A_G_QUITTING 4 (if quit then 1 else 0) /\
 Permutation (ablocks B lyc Sc) (O' ++ (res, Z.max n 1) :: rest) /\ ~ In (res, Z.max n 1) O') ->
blocks_bytes Sc <= blocks_bytes S + Z.max n 1 + LIVE_VERBS_RECEIVE ->
mo_le MT S Sc (mo_malloc MT 8192 + XM_REC_CLEAR MT R + XM_VERBS_RECEIVE MT (RecModel.rec_clear R) D) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SM_RET_VR)) memc (seg_rom SEGS)) mdc)
(sm_post ly S W regs mem md R D O rest).
(* the entry segment's conclusion: the contract's form with its premises bundled *)
Definition SM_P0_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (src n : Z) (D : list byte) (R : rstate) (O rest : list (Z * Z)),
sm_cx ly S W regs mem md ch src n D R O rest ->
SRr SEGS W (cfg_at SEGS (BASE + AF_send_message) regs mem md) (sm_post ly S W regs mem md R D O rest).
End i.
End f.
End d.
