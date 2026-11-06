(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at fb6520a9cda; derived by derive_y.py (frozen b7b132fb12a7) for reac-pw/fuzz_role's asan-ubsan image (fuzz_role.asan-ubsan): module lib.A.Img0 -> lib.AU.Img0 (lib/A/RPgBase.v and RPgCSpec.v stay shared), the addresses moved to that image, the tops rl_check_absent_A / rl_check_role_A / rl_check_malformed_A -> _B; by hand: the code table grows from 31 to 34 words (one `unimp` after each `jal abort`), the comments below restated at that image. The Modified-by lines above describe how lib/A/RPgCheck.v was made and quote that file's asan-image values. *)
(* The three check functions of fuzz_role.asan-ubsan (unstripped sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a;
   the pinned b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0 has the same bytes):
     check_absent 0x82a80 (11 words): addi sp,sp,-0x10; sd ra,8(sp); 0x82a88 bnez a0,0x82aa0; addi a0,zero,0x5a;
       0x82a90 bne a1,a0,0x82aa0; ld ra,8(sp); addi sp,sp,0x10; 0x82a9c ret; 0x82aa0 jal __asan_handle_no_return;
       jal abort; 0x82aa8 unimp.
     check_role 0x82aac (11 words): addi sp,sp,-0x10; sd ra,8(sp); addi a3,zero,1; 0x82ab8 bne a0,a3,0x82acc;
       0x82abc bne a1,a2,0x82acc; ld ra,8(sp); addi sp,sp,0x10; 0x82ac8 ret; 0x82acc jal __asan_handle_no_return;
       jal abort; 0x82ad4 unimp.
     check_malformed 0x82ad8 (12 words): addi sp,sp,-0x10; sd ra,8(sp); addi a2,zero,-1; 0x82ae4 bne a0,a2,0x82afc;
       addi a0,zero,0x5a; 0x82aec bne a1,a0,0x82afc; ld ra,8(sp); addi sp,sp,0x10; 0x82af8 ret;
       0x82afc jal __asan_handle_no_return; jal abort; 0x82b04 unimp.
   The words equal the asan image's 0x82bb4 / 0x82bdc / 0x82c04 except the two `jal` (their targets moved) and the
   `unimp` after the `jal abort`, which does not return: no path of the walk reaches it.
   The only store is `sd ra,8(sp)` into the 16-byte save slot [sp - 16, sp) (awr_stk: inside the caller's stack
   window by the contract's two window premises); the only load is `ld ra,8(sp)` from it. No instrumented check.
   WHY THE ABORT PATHS ARE UNREACHABLE: each abort branch compares the argument registers with a constant or with
   each other, and the contract fixes them: check_absent a0 = 0 and a1 = 0x5a, check_malformed a0 = -1 and
   a1 = 0x5a, check_role a0 = 1 and a1 = a2. The entry state ss_ck holds a0 and a1 as those literals (and a2 as the
   atom of a1 for check_role); ck_regs_ok shows the machine registers agree with it (the premises H10 / H11 / H12).
   The engine then decides every `bne` as not taken, so one run reaches the `ret` and the jal at the abort address
   is never stepped. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: the three check functions, the table the engine reads their code from ---- *)
Definition A_CHECK_ABSENT : Z := 0x82a80.
Definition A_CHECK_ROLE : Z := 0x82aac.
Definition A_CHECK_MALFORMED : Z := 0x82ad8.
(* the 34 4-byte instruction words 0x82a80 .. 0x82b04: check_absent (11), check_role (11), check_malformed (12) *)
Definition ck_tbl : ctable := build_table rsegs A_CHECK_ABSENT 34 TEmpty.
Lemma ck_tbl_ok : table_ok rsegs ck_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_ABSENT. lia. Qed.
Lemma ck_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma ck_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the walk's context: env slot 32 is the shadow base (no shadow entry is used) [RPgCfgChanges.v] ---- *)
Definition ck_SB : Z := 0x7fff8000.
Definition ck_Bx : sv := SOff 32 0.
Definition ck_Bspan : Z * Z := (ck_SB, ck_SB + 2 ^ 44 - 1).
Definition ck_extra : list word := [Z_to_bv 64 ck_SB].

(* ---- the entry state: the 16-byte save slot, sp in [2^46, 2^47], registers fixed by the contract ---- *)
(* the save slot [sp - 16, sp) [knock lib/A/ACeh.v stack_region] *)
Definition ck_stack_region (frame : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- frame) 0 (- frame) 0 [].
Definition ck_regions : smem := [ ck_stack_region 16 ].
(* sp in [2^46, 2^47], 16-aligned: the save slot's window lies outside the shadow band [QPgCheck.v check_facts] *)
Definition ck_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
(* the entry registers: sr_atoms with the overrides ov (register, value the contract fixes) *)
Definition ck_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Definition ss_ck (pc : Z) (ov : list (bv 5 * sv)) : sstate := mkSS pc (ck_sr ov) ck_regions None ck_facts.

(* an override of a register by a value it already has keeps regs_ok *)
Lemma regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma ck_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (ck_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold ck_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
Lemma ck_lit : forall E v, sv_denot E (SLit v) = w64 v.
Proof. intros E v. reflexivity. Qed.
Lemma ck_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma ck_entry : forall pc ov (W : world rsegs) regs memc, 0 <= pc ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs ck_extra) (snd p) = getr regs (fst p)) ov ->
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok rsegs (Ereg regs ck_extra) (ss_ck pc ov) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc ov W regs memc Hpc Hov Hpres Hhi Hal.
rewrite restrict_mkst_fx.
set (E := Ereg regs ck_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold ss_ck. apply (entry_st_ok_full rsegs); change (Ereg regs ck_extra) with E.
- apply ck_regs_ok. exact Hov.
- vm_compute. reflexivity.
- unfold ck_regions, ck_stack_region. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [ck_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End b.

(* ---- the walk's plumbing [RPgCfgChanges.v cfg_run / cfg_keep, QPgCheck.v awr_stk / kwr_stk] ---- *)
Lemma same_io_wvb_ck : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in [RPgCfgChanges.v kept_run] *)
Lemma ck_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
(* the write-range obligation: the save slot [sp - 16, sp) lies in the caller's stack allowance [QPgCheck.v] *)
Ltac awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
(* every write window of a state lies in the save slot [sp - 16, sp) [QPgCheck.v] *)
Ltac kwr_stk :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia | lia ] | ]);
destruct Hr.
Ltac ck_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok ck_tbl_ok HS HJ SHOK ck_Bspan; [awr | ] end.
Ltac ck_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (ck_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the `ret` leaf, into RPgCSpec's rl_post at fx2 = fx, E = False and R = True: the memory clause from KE
   [RPgCfgChanges.v cfg_leaf, QPgCheck.v qd_leaf] *)
Ltac ck_leaf :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at rsegs ck_tbl ck_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_ck]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz _; exact (KE a Ha Hz) | exact I]
end.
(* the common start of the three walks: the journal's stack facts, the entry state, the env facts *)
Ltac ck_start pc ov :=
lazymatch goal with
| HJ : ajournal _ _ ?STK ?sp0 _ _ _ _ _ _ _ ?lyc ?Sc ?W ?memc _ _, Hal16 : spZ ?regs mod 16 = 0,
  Hwlo : ?sp0 - ?STK <= spZ ?regs - T_check_STK, Hwhi : spZ ?regs <= ?sp0 |- _ =>
pose proof ck_wx as Hwx; pose proof ck_segs_low as Hsegs;
let Hpres := fresh "Hpres" in let Hstk := fresh "Hstk" in
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _);
let Hsp0al := fresh "Hsp0al" in let Hstk0 := fresh "Hstk0" in let Hceil := fresh "Hceil" in
let Hslo := fresh "Hslo" in let Hshi := fresh "Hshi" in let H47 := fresh "H47" in
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _);
let C1 := fresh "C1" in pose proof asan_consts as (C1 & _);
unfold T_check_STK in Hwlo;
let HS := fresh "HS" in
pose proof (ck_entry pc ov W regs memc ltac:(unfold pc; lia)) as HS;
lazymatch type of HS with ?P -> _ => let HO := fresh "HO" in assert (HO : P); [|specialize (HS HO); clear HO] end;
[ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; split;
  first [ (let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz)
        | (rewrite ck_lit; symmetry; assumption)
        | (rewrite (ck_atom _ _ 11 11%bv eq_refl); first [assumption | symmetry; assumption]) ]
| ];
specialize (HS ltac:(intros a Ha; apply Hpres; lia) ltac:(lia) Hal16);
remember (Ereg regs ck_extra) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs ck_extra) E) by (subst E; apply env_agree_refl);
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
clear HE;
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) memc)) by constructor;
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity);
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* check_absent: a0 = 0, a1 = 0x5a. 0x82a88 bnez a0 and 0x82a90 bne a1,a0 (a0 = 0x5a there) are decided not taken. *)
Theorem rl_check_absent_B : rl_check_absent_specX rsegs B MT A_CHECK_ABSENT.
Proof using MTL LAWS.
unfold rl_check_absent_specX, rl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11.
ck_start A_CHECK_ABSENT [((10%bv : bv 5), SLit 0); ((11%bv : bv 5), SLit 0x5a)].
(* 0x82a80 .. 0x82a98, stop at 0x82a9c ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.

(* check_role: a0 = 1, a2 = a1 (the atom of a1). 0x82ab8 bne a0,a3 (a3 = 1) and 0x82abc bne a1,a2 are decided
   not taken. *)
Theorem rl_check_role_B : rl_check_role_specX rsegs B MT A_CHECK_ROLE.
Proof using MTL LAWS.
unfold rl_check_role_specX, rl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H12.
ck_start A_CHECK_ROLE [((10%bv : bv 5), SLit 1); ((12%bv : bv 5), SOff 11 0)].
(* 0x82aac .. 0x82ac4, stop at 0x82ac8 ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.

(* check_malformed: a0 = -1, a1 = 0x5a. 0x82ae4 bne a0,a2 (a2 = -1) and 0x82aec bne a1,a0 (a0 = 0x5a) are decided
   not taken. *)
Theorem rl_check_malformed_B : rl_check_malformed_specX rsegs B MT A_CHECK_MALFORMED.
Proof using MTL LAWS.
unfold rl_check_malformed_specX, rl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11.
ck_start A_CHECK_MALFORMED [((10%bv : bv 5), SLit (-1)); ((11%bv : bv 5), SLit 0x5a)].
(* 0x82ad8 .. 0x82af4, stop at 0x82af8 ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.
End c.

Print Assumptions rl_check_absent_B.
Print Assumptions rl_check_role_B.
Print Assumptions rl_check_malformed_B.
