(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_changes 0x82ec8 against lib/A/RPgCSpec.v's rl_cfg_changes_specX on the concrete image lib/A/Img0.v rsegs; the plain walk it replaces is lib/Prog/reac_role_cfg_changes.v (snez of the xor). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); the table is this file's cfg_tbl over the two cfg functions; qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 8063f9199d5; derived by derive_y.py (frozen b7b132fb12a7) for reac-pw/fuzz_role's asan-ubsan image (fuzz_role.asan-ubsan): module lib.A.Img0 -> lib.AU.Img0 (lib/A/RPgBase.v and RPgCSpec.v stay shared), the addresses moved to that image, the top rl_cfg_changes_A -> rl_cfg_changes_B; the comments below restated by hand at that image. The Modified-by lines above describe how lib/A/RPgCfgChanges.v was made and quote that file's asan-image values. *)
(* reac_role_cfg_changes, 0x83108, 12 bytes, 3 instructions (fuzz_role.asan-ubsan, unstripped sha256
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a; the pinned b255d4935da5 has the same bytes):
     0x83108 xor a0,a0,a1; 0x8310c snez a0,a0; 0x83110 ret.
   A pure leaf: no sp move, no store, no load, no shadow check. The engine runs the first two instructions to the
   `ret`; a0 there is sltu 0, (a0 xor a1), which is rl_changes cur req (U_snez_xor). No region, so no byte is
   written and the post's memory clause holds at every address. The same 12 bytes are the asan image's 0x82ec8
   (0 words differ) and so the plain image's 0x143e8 (the function has no pc-relative field). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: the two cfg functions, the table the engine reads their code from ---- *)
Definition A_CFG_CHANGES : Z := 0x83108.
Definition A_CFG_APPLY : Z := 0x83114.
(* the two strings reac_role_cfg_apply_state forms (0x83118 auipc a0,0xfff9e + addi a0,a0,0x468 and 0x83124
   auipc a0,0xfff9e + addi a0,a0,0x49c): "role_reestablish_pending" (24 bytes and its NUL) at 0x21580 and "applied"
   (7 bytes and its NUL) at 0x215c0, read out of the pinned file *)
Definition A_STR_PENDING : Z := 0x21580.
Definition A_STR_APPLIED : Z := 0x215c0.
(* the ten 4-byte instruction words 0x83108 .. 0x8312c: cfg_changes (3) then cfg_apply_state (7) *)
Definition cfg_tbl : ctable := build_table rsegs A_CFG_CHANGES 10 TEmpty.
Lemma cfg_tbl_ok : table_ok rsegs cfg_tbl.
Proof. apply build_table_ok0. unfold A_CFG_CHANGES. lia. Qed.
Lemma cfg_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma cfg_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the walk's context: env slot 32 is the shadow base (no shadow entry is used) [fuzz_qdisc QPgRt.v] ---- *)
Definition SBr : Z := 0x7fff8000.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SBr, SBr + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SBr].

(* ---- the value at the `ret` ---- *)
(* `xor a0,a0,a1; snez a0,a0` on the two 64-bit words cur and req: rl_changes cur req *)
Lemma snez_xor_Z : forall cur req, 0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
(if 0 <? Z.lxor cur req then 1 else 0) = rl_changes cur req.
Proof.
intros cur req Hc Hr. unfold rl_changes.
pose proof (YO0a.lxor_range cur req 64 Hc Hr) as Hx.
destruct (Z.eqb_spec cur req) as [->|Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- assert (N : Z.lxor cur req <> 0) by (intros Z0; apply Hne; apply Z.lxor_eq_0_iff; exact Z0).
destruct (Z.ltb_spec 0 (Z.lxor cur req)); [reflexivity | lia].
Qed.

Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in [fuzz_qdisc QPgSlots.v kept_run] *)
Lemma kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

(* ---- the walk's plumbing [fuzz_qdisc QPgSlots.v kwr_ro / qd_run / qd_keep / qd_branch / qd_r10 / qd_leaf] ---- *)
Ltac cfg_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac cfg_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok cfg_tbl_ok HS HJ SHOK RTBspan; [awr | ] end.
Ltac cfg_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac cfg_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok cfg_tbl_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac cfg_r10 R10 :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs ms) (10%bv : bv 5) = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS)
end.
(* the `ret` leaf, into RPgCSpec's rl_post at fx2 = fx: mtac closes the memory clause from KE, vtac the clause on
   a0 from R10 *)
Ltac cfg_leaf mtac vtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in cfg_r10 R10;
eapply (SRr_ret_at rsegs cfg_tbl cfg_tbl_ok cfg_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [mtac | rewrite R10; vtac]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state of a cfg function at pc: the registers as atoms, no region, no fact *)
Definition ss_cfg (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma cfg_entry : forall pc (W : world rsegs) regs memc, 0 <= pc ->
st_ok rsegs (Ereg regs rt_extra) (ss_cfg pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc Hpc.
rewrite restrict_mkst_fx.
unfold ss_cfg. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Theorem rl_cfg_changes_B : rl_cfg_changes_specX rsegs B MT A_CFG_CHANGES.
Proof using MTL LAWS.
unfold rl_cfg_changes_specX, rl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cur req
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 Hcur H11 Hreq.
pose proof cfg_wx as Hwx. pose proof cfg_segs_low as Hsegs.
pose proof (cfg_entry A_CFG_CHANGES W regs memc ltac:(unfold A_CFG_CHANGES; lia)) as HS.
remember (Ereg regs rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 req) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
clear HE.
assert (SHOK : sh_ok rsegs RTBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 A_CFG_CHANGES) with (Z_to_bv 64 A_CFG_CHANGES).
(* 0x83108 xor a0,a0,a1; 0x8310c snez a0,a0; stop at 0x83110 ret *)
cfg_run awr_ok_tac. cfg_keep cfg_kwr_ro.
cfg_leaf ltac:(intros a Ha _ _; exact (KE a Ha (fun x => x)))
ltac:(rewrite denot_lit_U; apply (f_equal (Z_to_bv 64));
rewrite ?U_SAlu, ?U_SLit; cbn [zalu_raw];
rewrite (U_atom E 10 cur E10 Hcur), (U_atom E 11 req E11 Hreq);
unfold zcanon, M64; rewrite (Z.mod_small (Z.lxor cur req)) by (apply YO0a.lxor_range; lia);
rewrite ?Z.mod_0_l by lia; rewrite snez_xor_Z by lia; unfold rl_changes; destruct (cur =? req); reflexivity).
Qed.
End d.
End b.
