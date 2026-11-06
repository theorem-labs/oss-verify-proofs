(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* The four check functions of fuzz_rate.asan without a call (unstripped sha256
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3; the pinned
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a has the same loaded bytes), capstone:
     check_absent 0x83690 (11 words): addi sp,sp,-0x10; sd ra,8(sp); 0x83698 bnez a0,0x836b4; lui a0,0x5a5a6;
       addiw a0,a0,-0x5a6 (a0 = 0x5a5a5a5a); 0x836a4 bne a1,a0,0x836b4; ld ra,8(sp); addi sp,sp,0x10; 0x836b0 ret;
       0x836b4 jal __asan_handle_no_return; jal abort.
     check_rate 0x836bc (10 words): addi sp,sp,-0x10; sd ra,8(sp); addi a3,zero,1; 0x836c8 bne a0,a3,0x836dc;
       0x836cc bne a1,a2,0x836dc; ld ra,8(sp); addi sp,sp,0x10; 0x836d8 ret; 0x836dc jal __asan_handle_no_return;
       jal abort (the same words as role's check_role 0x82bdc but the PC-relative fields).
     check_malformed 0x836e4 (12 words): addi sp,sp,-0x10; sd ra,8(sp); addi a2,zero,-1; 0x836f0 bne a0,a2,0x8370c;
       lui a0,0x5a5a6; addiw a0,a0,-0x5a6; 0x836fc bne a1,a0,0x8370c; ld ra,8(sp); addi sp,sp,0x10; 0x83708 ret;
       0x8370c jal __asan_handle_no_return; jal abort.
     check_decide 0x83714 (8 words): addi sp,sp,-0x10; sd ra,8(sp); 0x8371c bne a0,a1,0x8372c; ld ra,8(sp);
       addi sp,sp,0x10; 0x83728 ret; 0x8372c jal __asan_handle_no_return; jal abort.
   The only store is `sd ra,8(sp)` into the 16-byte save slot [sp - 16, sp) (awr_stk: inside the caller's stack
   window by the contract's two window premises); the only load is `ld ra,8(sp)` from it. No instrumented check.
   WHY THE ABORT PATHS ARE UNREACHABLE: each abort branch compares the argument registers with a constant or with
   each other, and the contract fixes them: check_absent a0 = 0 and a1 = 0x5a5a5a5a, check_malformed a0 = -1 and
   a1 = 0x5a5a5a5a, check_rate a0 = 1 and a1 = a2, check_decide a0 = a1. The entry state ss_ck holds a0 and a1 as
   those literals (a2 as the atom of a1 for check_rate, a1 as the atom of a0 for check_decide); ck_regs_ok shows the
   machine registers agree with it (the premises H10 / H11 / H12). The engine then decides every `bne` as not taken,
   so one run reaches the `ret` and the jal at the abort address is never stepped (no walk of
   __asan_handle_no_return is needed). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the image: the four check functions, the table the engine reads their code from ---- *)
Definition A_CHECK_ABSENT : Z := 0x83690.
Definition A_CHECK_RATE : Z := 0x836bc.
Definition A_CHECK_MALFORMED : Z := 0x836e4.
Definition A_CHECK_DECIDE : Z := 0x83714.
(* the 41 4-byte instruction words 0x83690 .. 0x83730: check_absent (11), check_rate (10), check_malformed (12),
   check_decide (8) *)
Definition ck_tbl : ctable := build_table rsegs A_CHECK_ABSENT 41 TEmpty.
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
(* the `ret` leaf, into RtPgCSpec's rt_cpost at fx2 = fx, E = False and R = True: the memory clause from KE
   [role's RPgCfgChanges.v cfg_leaf, QPgCheck.v qd_leaf] *)
Ltac ck_leaf :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
eapply (SRr_ret_at rsegs ck_tbl ck_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
cbv beta delta [rt_cpost rt_cpost_g]; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [exact I|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_ck]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz _; exact (KE a Ha Hz) | exact I]
end.
(* the common start of the four walks: the journal's stack facts, the entry state, the env facts *)
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
        | (rewrite (ck_atom _ _ 11 11%bv eq_refl); first [assumption | symmetry; assumption])
        | (rewrite (ck_atom _ _ 10 10%bv eq_refl); first [assumption | symmetry; assumption]) ]
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

(* ---- the callee-saved registers across a call cut [role's RPgCheckStr.v cs_eq .. sp_of_st_ok, pres_of_cs] ---- *)
Definition cs_eq (L : list (bv 5)) (ra rb : bvmap 5 word) : Prop := forall r, In r L -> getr rb r = getr ra r.
Lemma cs_eq_trans : forall L r1 r2 r3, cs_eq L r1 r2 -> cs_eq L r2 r3 -> cs_eq L r1 r3.
Proof. intros L r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
(* every register of the callee-saved set except sp *)
Definition L_ANS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma cs_eq_of_pres : forall L r1 r2, (forall r, In r L -> acallee_saved (bv_unsigned r)) ->
aregs_preserved r1 r2 -> cs_eq L r1 r2.
Proof.
intros L r1 r2 HL HP r Hr. pose proof (HP (bv_unsigned r) (HL r Hr)) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Lemma L_ANS_cs : forall r, In r L_ANS -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [L_ANS In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Lemma pres_of_cs : forall regs regsF, cs_eq L_ANS regs regsF -> spZ regsF = spZ regs -> aregs_preserved regs regsF.
Proof.
intros regs regsF HC H2 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc];
[first [ (apply bv_eq; exact H2) | (apply HC; cbv [L_ANS In]; repeat (first [left; apply bv_eq; reflexivity | right])) ] | ]);
subst; first [ (apply bv_eq; exact H2) | (apply HC; cbv [L_ANS In]; repeat (first [left; apply bv_eq; reflexivity | right])) ].
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cs_eq_of_st_ok : forall H E ss ms regs0 extra L,
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
cs_eq L regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 extra L HS [HA _] Hcs r Hin.
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma sp_of_st_ok : forall H E ss ms regs0 extra c,
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
sr_get (ss_regs ss) (2%bv : bv 5) = SOff 2 c -> spZ (ms_regs ms) = zcanon (spZ regs0 + c).
Proof.
intros H E ss ms regs0 extra c HS [HA _] Hsr. unfold spZ.
rewrite (st_ok_restrict_reg rsegs H E ss ms (2%bv : bv 5) HS), Hsr, denot_SOff.
rewrite HA by lia. rewrite (ew_Ereg_nat regs0 extra 2 (2%bv : bv 5) eq_refl). reflexivity.
Qed.
End a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* check_absent: a0 = 0, a1 = 0x5a5a5a5a. 0x83698 bnez a0 and 0x836a4 bne a1,a0 (a0 = 0x5a5a5a5a there, from
   0x8369c lui / 0x836a0 addiw) are decided not taken. *)
Theorem rt_check_absent_A : rt_check_absent_specX rsegs B MT A_CHECK_ABSENT.
Proof using MTL LAWS.
unfold rt_check_absent_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11.
ck_start A_CHECK_ABSENT [((10%bv : bv 5), SLit 0); ((11%bv : bv 5), SLit 0x5a5a5a5a)].
(* 0x83690 .. 0x836ac, stop at 0x836b0 ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.

(* check_rate: a0 = 1, a2 = a1 (the atom of a1). 0x836c8 bne a0,a3 (a3 = 1) and 0x836cc bne a1,a2 are decided
   not taken. *)
Theorem rt_check_rate_A : rt_check_rate_specX rsegs B MT A_CHECK_RATE.
Proof using MTL LAWS.
unfold rt_check_rate_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H12.
ck_start A_CHECK_RATE [((10%bv : bv 5), SLit 1); ((12%bv : bv 5), SOff 11 0)].
(* 0x836bc .. 0x836d4, stop at 0x836d8 ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.

(* check_malformed: a0 = -1, a1 = 0x5a5a5a5a. 0x836f0 bne a0,a2 (a2 = -1) and 0x836fc bne a1,a0 (a0 = 0x5a5a5a5a)
   are decided not taken. *)
Theorem rt_check_malformed_A : rt_check_malformed_specX rsegs B MT A_CHECK_MALFORMED.
Proof using MTL LAWS.
unfold rt_check_malformed_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11.
ck_start A_CHECK_MALFORMED [((10%bv : bv 5), SLit (-1)); ((11%bv : bv 5), SLit 0x5a5a5a5a)].
(* 0x836e4 .. 0x83704, stop at 0x83708 ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.

(* check_decide: a1 = a0 (the atom of a0). 0x8371c bne a0,a1 is decided not taken. *)
Theorem rt_check_decide_A : rt_check_decide_specX rsegs B MT A_CHECK_DECIDE.
Proof using MTL LAWS.
unfold rt_check_decide_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H11.
ck_start A_CHECK_DECIDE [((11%bv : bv 5), SOff 10 0)].
(* 0x83714 .. 0x83724, stop at 0x83728 ret *)
ck_run awr_stk. ck_keep kwr_stk.
ck_leaf.
Qed.
End c.

Print Assumptions rt_check_absent_A.
Print Assumptions rt_check_rate_A.
Print Assumptions rt_check_malformed_A.
Print Assumptions rt_check_decide_A.
