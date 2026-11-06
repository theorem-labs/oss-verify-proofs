(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgSlots.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for fuzz_qdisc's image A) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks reac_role_cfg_changes 0x82ec8 against lib/A/RPgCSpec.v's rl_cfg_changes_specX on the concrete image lib/A/Img0.v rsegs; the plain walk it replaces is lib/Prog/reac_role_cfg_changes.v (snez of the xor). The leaf's post is RPgCSpec's rl_post (the float state fx kept, no extra bytes E); the table is this file's cfg_tbl over the two cfg functions; qdisc's region of the divisor constant, its arithmetic lemmas and its three branches are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own
   code table, wx / segs_low, kept_run, the run / keep / branch / r10 chain and the `ret` leaf) and the a0 split of
   lib/A/RPgCfgApply.v at the same commit, for reac-pw/fuzz_rate's image A (fuzz_rate.asan): it walks
   reac_rate_is_closed 0x83fbc, reac_rate_bit 0x83ff0, reac_rate_best_drivable 0x84034 and reac_rate_cfg_decide 0x84448
   against lib/A/RtPgCSpec.v's rt_is_closed_specX / rt_bit_specX / rt_best_drivable_specX / rt_cfg_decide_specX on the
   image module's loaded segments; the leaf's post is rt_cpost (through rt_cpost_g with O = True); the value at the
   `ret` is stated over the integer of each argument register (bv_unsigned) as the contracts read it; new: the value
   lemmas lf_U_* of the engine's results and their RateCfg answers, and the case splits of the plain walks
   (lib/Prog/reac_rate_{is_closed,bit,best_drivable,cfg_decide}.v of the plain image). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgLeaf.v at a2647881ba31, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the theorem names rt_*_A -> rt_*_B; the Modified-by lines above describe how lib/A/RtPgLeaf.v was made and quote that file's image-A values; the code below carries image B's values. *)
(* Four leaf functions of fuzz_rate.asan-ubsan (pinned sha256 c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14;
   symbols from the unstripped twin a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, which holds the
   same loaded bytes):
     reac_rate_is_closed 0x84220 (13 words): lui a1,0xb; addiw a2,a1,-956 (44100); li a1,1; 0x8422c beq a0,a2,0x8424c;
       lui a2,0xc; addiw a2,a2,-1152 (48000); 0x84238 beq a0,a2,0x8424c; lui a1,0x17; addiw a1,a1,1792 (96000);
       xor a0,a0,a1; seqz a1,a0; 0x8424c mv a0,a1; 0x84250 ret.
     reac_rate_bit 0x84254 (17 words): lui; addiw a1 = 44100; 0x8425c beq a0,a1,0x84288; lui; addiw a1 = 96000;
       0x84268 beq a0,a1,0x84280; lui; addiw a1 = 48000; 0x84274 bne a0,a1,0x84290; li a0,2; ret;
       0x84280 li a0,4; ret; 0x84288 li a0,1; ret; 0x84290 li a0,0; 0x84294 ret.
     reac_rate_best_drivable 0x84298 (16 words): andi a1,a0,4; 0x8429c bnez a1,0x842c0; andi a1,a0,2;
       0x842a4 bnez a1,0x842cc; slli a0,a0,0x3f; lui a1,0xb; srai a0,a0,0x3f; addiw a1,a1,-956; and a0,a0,a1;
       0x842bc ret; 0x842c0 lui; addiw a0 = 96000; ret; 0x842cc lui; addiw a0 = 48000; 0x842d4 ret.
     reac_rate_cfg_decide 0x846f8 (21 words): li a3,1; 0x846fc bne a0,a3,0x84708; li a3,3; j 0x84744;
       0x84708 lui; addiw a0 = 44100; 0x84710 beq a1,a0,0x84738; lui; addiw a0 = 96000; 0x8471c beq a1,a0,0x84734;
       lui; addiw a0 = 48000; 0x84728 bne a1,a0,0x84744; li a3,2; j 0x84738; 0x84734 li a3,4;
       0x84738 and a2,a3,a2; seqz a3,a2; slli a3,a3,0x1; 0x84744 mv a0,a3; 0x84748 ret.
   Pure leaves: no sp move, no store, no load, no shadow check (byte-identical to the plain image's 0x149c0 /
   0x149f4 / 0x14a38 / 0x14c04, compared on the pinned fuzz_rate.plain 2bbd88d40188). The entry state holds every argument register as
   its atom; the engine stops at each branch on an argument, which is split (branch_eq_U / branch_ne_U) and its
   condition turned into one on the argument's integer value; each side runs to its `ret`. No region, so no byte is
   written and the post's memory clause holds at every address. The value in a0 at each `ret` is the engine's
   expression; the lf_U_* lemmas give its integer, and RateCfg's answer is matched on the side's conditions. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.reac_pw.fuzz_rate.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: the loaded segments of fuzz_rate.asan-ubsan, the four functions, the table the engine reads their
   code from ---- *)
Local Notation rsegs := AsanUbsan.M.loaded_segments.
Definition A_IS_CLOSED : Z := 0x84220.
Definition A_BIT : Z := 0x84254.
Definition A_BEST : Z := 0x84298.
Definition A_CFG_DECIDE : Z := 0x846f8.
(* the 46 words 0x84220 .. 0x842d4 (is_closed 13, bit 17, best_drivable 16) and the 21 words 0x846f8 .. 0x84748 *)
Definition lf_tbl : ctable := build_table rsegs A_CFG_DECIDE 21 (build_table rsegs A_IS_CLOSED 46 TEmpty).
Lemma lf_tbl_ok : table_ok rsegs lf_tbl.
Proof. apply build_table_ok; [unfold A_CFG_DECIDE; lia|]. apply build_table_ok0. unfold A_IS_CLOSED. lia. Qed.
Lemma lf_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma lf_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

(* ---- the walk's context: env slot 32 is the shadow base (no shadow entry is used) ---- *)
Definition lf_SB : Z := 0x7fff8000.
Definition lf_Bx : sv := SOff 32 0.
Definition lf_Bspan : Z * Z := (lf_SB, lf_SB + 2 ^ 44 - 1).
Definition lf_extra : list word := [Z_to_bv 64 lf_SB].

Lemma lf_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a run keeps every byte outside the zone its write windows lie in *)
Lemma lf_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

(* ---- the walk's plumbing ---- *)
Ltac lf_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
Ltac lf_run :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok lf_tbl_ok HS HJ SHOK lf_Bspan; [awr_ok_tac | ] end.
Ltac lf_keep :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (lf_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by lf_kwr_ro end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac lf_step := lf_run; lf_keep.
Ltac lf_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok lf_tbl_ok HS SH lf_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac lf_r10 R10 :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs ms) (10%bv : bv 5) = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS)
end.
(* the `ret` leaf, into RtPgCSpec's rt_cpost at fx2 = fx, O = True, E = False: the memory clause from KE, vtac the
   clause on a0 from R10 *)
Ltac lf_leaf vtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in lf_r10 R10;
eapply (SRr_ret_at rsegs lf_tbl lf_tbl_ok lf_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
unfold rt_cpost, rt_cpost_g; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew E 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [reflexivity|];
split; [eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok; [exact HS | eassumption | vm_compute; reflexivity]|];
split; [reflexivity|];
split; [exact I|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply lf_same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha _ _; exact (KE a Ha (fun x => x)) | cbv beta; rewrite R10; vtac]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state of a leaf at pc: the registers as atoms, no region, no fact *)
Definition ss_lf (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma lf_entry : forall pc (W : world rsegs) regs memc, 0 <= pc ->
st_ok rsegs (Ereg regs lf_extra) (ss_lf pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc Hpc.
rewrite restrict_mkst_fx.
unfold ss_lf. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
End b.

(* the common start of the four walks: the entry state, the env facts of ra and the three argument registers *)
Ltac lf_start pc :=
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W ?memc _ _ |- SRr _ _ (cfg_at _ _ ?regs _ _) _ =>
pose proof lf_wx as Hwx; pose proof lf_segs_low as Hsegs;
pose proof (lf_entry pc W regs memc ltac:(unfold pc; lia)) as HS;
remember (Ereg regs lf_extra) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs lf_extra) E) by (subst E; apply env_agree_refl);
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
assert (E11 : ew E 11 = getr regs 11) by (subst E; exact (ew_Ereg_nat regs _ 11 11%bv eq_refl));
assert (E12 : ew E 12 = getr regs 12) by (subst E; exact (ew_Ereg_nat regs _ 12 12%bv eq_refl));
clear HE;
assert (SHOK : sh_ok rsegs lf_Bx [] E (mrestrict (w_H W) memc)) by constructor;
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity);
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.
Lemma lf_atom_of : forall w : word, w = w64 (bv_unsigned w) /\ 0 <= bv_unsigned w < 2 ^ 64.
Proof.
intros w. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ w) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
Qed.
(* the integer v of an argument register (Hv0 : v = bv_unsigned w, w the register) as the atom of E: En becomes
   ew E n = w64 v, Hv its range *)
Ltac lf_atom v Hv0 En Hv :=
let Hw := fresh "Hw" in
lazymatch type of Hv0 with ?v' = bv_unsigned ?w =>
destruct (lf_atom_of w) as [Hw Hv]; rewrite <- Hv0 in Hw, Hv; clear Hv0; rewrite Hw in En; clear Hw
end.

(* ---- the values the engine leaves in a0, as integers ---- *)
Lemma lf_lit : forall E v, sv_denot E (SLit v) = w64 v.
Proof. intros E v. reflexivity. Qed.
(* `addi rd,rs,0` (mv) *)
Lemma lf_U_add0 : forall E a, U E (SAlu ALU_ADD a (SLit 0)) = U E a.
Proof.
intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
apply zcanon_id. apply U_range.
Qed.
(* `sltiu rd,rs,1` (seqz) *)
Lemma lf_U_sltu1 : forall E a, U E (SAlu ALU_SLTU a (SLit 1)) = if U E a =? 0 then 1 else 0.
Proof.
intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 1) by (unfold M64; lia).
pose proof (U_range E a) as R.
destruct (Z.eqb_spec (U E a) 0) as [-> | Hn]; [reflexivity|].
destruct (Z.ltb_spec (U E a) 1); [lia|]. reflexivity.
Qed.
Lemma lf_U_xor_lit : forall E a m, 0 <= m < 2 ^ 64 -> U E (SAlu ALU_XOR a (SLit m)) = Z.lxor (U E a) m.
Proof.
intros E a m Hm. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id m) by (unfold M64; lia).
apply zcanon_id. pose proof (U_range E a). unfold M64 in *. apply (YO0a.lxor_range _ _ 64); lia.
Qed.
Lemma lf_U_sll1 : forall E a, U E (SAlu ALU_SLL a (SLit 1)) = (2 * U E a) mod 2 ^ 64.
Proof.
intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 1) by (unfold M64; lia).
change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64. f_equal. lia.
Qed.
(* `slli rd,rs,63; srai rd,rd,63`: all ones when bit 0 is set, else 0 *)
Lemma lf_U_sra_sll63 : forall E a,
U E (SAlu ALU_SRA (SAlu ALU_SLL a (SLit 63)) (SLit 63)) = if Z.odd (U E a) then 2 ^ 64 - 1 else 0.
Proof.
intros E a. rewrite !U_SAlu, !U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 63) by (unfold M64; lia).
change (Z.land 63 63) with 63.
assert (Hs : zcanon (Z.shiftl (U E a) 63) = (if Z.odd (U E a) then 1 else 0) * 2 ^ 63).
{ unfold zcanon, M64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 64) with (2 * 2 ^ 63).
  rewrite Z.mul_mod_distr_r by lia. rewrite Zmod_odd. reflexivity. }
rewrite Hs. destruct (Z.odd (U E a)); vm_compute; reflexivity.
Qed.
Lemma lf_U_sext0 : forall E a c, 0 <= c < 2 ^ 64 ->
U E (SAlu ALU_AND (SAlu ALU_SRA (SAlu ALU_SLL a (SLit 63)) (SLit 63)) (SLit c)) = if Z.odd (U E a) then c else 0.
Proof.
intros E a c Hc. rewrite U_and_lit by exact Hc. rewrite lf_U_sra_sll63.
destruct (Z.odd (U E a)).
- change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
- apply Z.land_0_l.
Qed.
(* the bit tests `andi rd,rs,4` / `andi rd,rs,2` against 0 *)
Lemma lf_land4 : forall m, (Z.land m 4 =? 0) = negb (Z.testbit m 2).
Proof. intros m. change (Z.land m 4) with (Z.land m (2 ^ 2)). apply RateCfg.testbit_land_pow. lia. Qed.
Lemma lf_land2 : forall m, (Z.land m 2 =? 0) = negb (Z.testbit m 1).
Proof. intros m. change (Z.land m 2) with (Z.land m (2 ^ 1)). apply RateCfg.testbit_land_pow. lia. Qed.

(* ---- RateCfg's answers on each side's conditions ---- *)
Lemma lf_best_bits : forall m,
RateCfg.rate_best m = if Z.testbit m 2 then 96000 else if Z.testbit m 1 then 48000 else if Z.odd m then 44100 else 0.
Proof. intros m. unfold RateCfg.rate_best. rewrite Z.bit0_odd. reflexivity. Qed.
Lemma lf_bit_0 : forall hz, hz <> 44100 -> hz <> 48000 -> hz <> 96000 -> RateCfg.rate_bit hz = 0.
Proof.
intros hz H1 H2 H3. unfold RateCfg.rate_bit, RateCfg.RATE_44K1, RateCfg.RATE_48K, RateCfg.RATE_96K.
destruct (Z.eqb_spec hz 44100); [lia|]. destruct (Z.eqb_spec hz 48000); [lia|].
destruct (Z.eqb_spec hz 96000); [lia|]. reflexivity.
Qed.
Lemma lf_closed_lxor : forall hz, hz <> 44100 -> hz <> 48000 ->
(if Z.lxor hz 96000 =? 0 then 1 else 0) = RateCfg.rate_closed hz.
Proof.
intros hz H1 H2. unfold RateCfg.rate_closed, RateCfg.rate_bit, RateCfg.RATE_44K1, RateCfg.RATE_48K, RateCfg.RATE_96K.
destruct (Z.eqb_spec hz 44100); [lia|]. destruct (Z.eqb_spec hz 48000); [lia|].
destruct (Z.eqb_spec hz 96000) as [-> | H3]; [reflexivity|].
destruct (Z.eqb_spec (Z.lxor hz 96000) 0) as [X | _]; [apply (proj1 (Z.lxor_eq_0_iff _ _)) in X; exfalso; exact (H3 X) | reflexivity].
Qed.
Lemma lf_decide_slave : forall hz mask, RateCfg.decide_res 1 hz mask = 3.
Proof. intros hz mask. reflexivity. Qed.
Lemma lf_decide_nc : forall role hz mask, role <> 1 -> RateCfg.rate_bit hz = 0 -> RateCfg.decide_res role hz mask = 1.
Proof.
intros role hz mask Hr Hb. unfold RateCfg.decide_res. destruct (Z.eqb_spec role 1); [contradiction|].
rewrite Hb. reflexivity.
Qed.
Lemma lf_decide_bit : forall role hz mask b, role <> 1 -> RateCfg.rate_bit hz = b -> b <> 0 ->
RateCfg.decide_res role hz mask = if Z.land mask b =? 0 then 2 else 0.
Proof.
intros role hz mask b Hr Hb Hb0. unfold RateCfg.decide_res, RateCfg.REFUSE_ROLE_SLAVE, RateCfg.REFUSE_NOT_CLOSED,
RateCfg.REFUSE_NOT_DRIVABLE, RateCfg.REFUSE_NONE.
destruct (Z.eqb_spec role 1); [contradiction|]. rewrite Hb. destruct (Z.eqb_spec b 0); [contradiction|].
rewrite Z.land_comm. reflexivity.
Qed.
(* the value of cfg_decide's tail `and a2,a3,a2; seqz a3,a2; slli a3,a3,1; mv a0,a3` with a3 the rate's bit b *)
Ltac lf_dec_tail b Hrole Hbit :=
lazymatch goal with E12 : ew ?E 12 = w64 ?mask, Hm : 0 <= ?mask < 2 ^ 64 |- _ =>
rewrite denot_lit_U; unfold w64; f_equal;
rewrite lf_U_add0, lf_U_sll1, lf_U_sltu1, U_and_lit, (U_atom E 12 mask E12 Hm) by lia;
rewrite (lf_decide_bit _ _ mask b Hrole Hbit) by lia;
destruct (Z.land mask b =? 0); reflexivity
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* reac_rate_is_closed(hz): 1 when hz is 44100 or 48000 (the two beq), else seqz (hz xor 96000). *)
Theorem rt_is_closed_B : rt_is_closed_specX rsegs B MT A_IS_CLOSED.
Proof using MTL LAWS.
unfold rt_is_closed_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
lf_start A_IS_CLOSED.
remember (bv_unsigned (getr regs 10)) as hz eqn:Hz0. lf_atom hz Hz0 E10 Hhz.
(* 0x84220 .. 0x84228, stop at 0x8422c beq a0,a2 (a2 = 44100) *)
lf_step. lf_branch Hb; rewrite branch_eq_U, (U_atom E 10 hz E10 Hhz), U_lit in Hb by lia.
- (* hz = 44100: 0x8424c mv a0,a1 (a1 = 1), stop at 0x84250 ret *)
  apply Z.eqb_eq in Hb. subst hz. lf_step. lf_leaf ltac:(rewrite lf_lit; reflexivity).
- apply Z.eqb_neq in Hb.
  (* 0x84230, 0x84234, stop at 0x84238 beq a0,a2 (a2 = 48000) *)
  lf_step. lf_branch Hb2; rewrite branch_eq_U, (U_atom E 10 hz E10 Hhz), U_lit in Hb2 by lia.
  + apply Z.eqb_eq in Hb2. subst hz. lf_step. lf_leaf ltac:(rewrite lf_lit; reflexivity).
  + (* 0x8423c .. 0x8424c: a0 = seqz (hz xor 96000); stop at 0x84250 ret *)
    apply Z.eqb_neq in Hb2. lf_step.
    lf_leaf ltac:(rewrite denot_lit_U; unfold w64; f_equal;
      rewrite lf_U_add0, lf_U_sltu1, lf_U_xor_lit, (U_atom E 10 hz E10 Hhz) by lia;
      exact (lf_closed_lxor hz Hb Hb2)).
Qed.

(* reac_rate_bit(hz): 1 / 4 / 2 for 44100 / 96000 / 48000 (in the code's order), else 0. *)
Theorem rt_bit_B : rt_bit_specX rsegs B MT A_BIT.
Proof using MTL LAWS.
unfold rt_bit_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
lf_start A_BIT.
remember (bv_unsigned (getr regs 10)) as hz eqn:Hz0. lf_atom hz Hz0 E10 Hhz.
(* stop at 0x8425c beq a0,a1 (44100) *)
lf_step. lf_branch Hb; rewrite branch_eq_U, (U_atom E 10 hz E10 Hhz), U_lit in Hb by lia.
- (* 0x84288 li a0,1; stop at 0x8428c ret *)
  apply Z.eqb_eq in Hb. subst hz. lf_step. lf_leaf ltac:(rewrite lf_lit; reflexivity).
- apply Z.eqb_neq in Hb.
  (* stop at 0x84268 beq a0,a1 (96000) *)
  lf_step. lf_branch Hb2; rewrite branch_eq_U, (U_atom E 10 hz E10 Hhz), U_lit in Hb2 by lia.
  + (* 0x84280 li a0,4; stop at 0x84284 ret *)
    apply Z.eqb_eq in Hb2. subst hz. lf_step. lf_leaf ltac:(rewrite lf_lit; reflexivity).
  + apply Z.eqb_neq in Hb2.
    (* stop at 0x84274 bne a0,a1 (48000) *)
    lf_step. lf_branch Hb3; rewrite branch_ne_U, (U_atom E 10 hz E10 Hhz), U_lit in Hb3 by lia.
    * (* 0x84290 li a0,0; stop at 0x84294 ret *)
      apply Bool.negb_true_iff, Z.eqb_neq in Hb3. lf_step.
      lf_leaf ltac:(rewrite lf_lit, (lf_bit_0 hz Hb Hb3 Hb2); reflexivity).
    * (* 0x84278 li a0,2; stop at 0x8427c ret *)
      apply Bool.negb_false_iff, Z.eqb_eq in Hb3. subst hz. lf_step. lf_leaf ltac:(rewrite lf_lit; reflexivity).
Qed.

(* reac_rate_best_drivable(mask): 96000 on bit 2, else 48000 on bit 1, else 44100 masked by bit 0. *)
Theorem rt_best_drivable_B : rt_best_drivable_specX rsegs B MT A_BEST.
Proof using MTL LAWS.
unfold rt_best_drivable_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
lf_start A_BEST.
remember (bv_unsigned (getr regs 10)) as mask eqn:Hm0. lf_atom mask Hm0 E10 Hmask.
(* stop at 0x8429c bnez a1 (a1 = mask & 4) *)
lf_step. lf_branch Hb; rewrite branch_ne_U, U_and_lit, (U_atom E 10 mask E10 Hmask), U_lit, lf_land4,
  Bool.negb_involutive in Hb by lia.
- (* bit 2: 0x842c0 .. 0x842c8 a0 = 96000; stop at 0x842d4 ret *)
  lf_step. lf_leaf ltac:(rewrite lf_lit, lf_best_bits, Hb; reflexivity).
- (* stop at 0x842a4 bnez a1 (a1 = mask & 2) *)
  lf_step. lf_branch Hb2; rewrite branch_ne_U, U_and_lit, (U_atom E 10 mask E10 Hmask), U_lit, lf_land2,
    Bool.negb_involutive in Hb2 by lia.
  + (* bit 1: 0x842cc .. 0x842d0 a0 = 48000; stop at 0x842d4 ret *)
    lf_step. lf_leaf ltac:(rewrite lf_lit, lf_best_bits, Hb, Hb2; reflexivity).
  + (* 0x842a8 .. 0x842b8: a0 = (mask << 63 >> 63, arithmetic) & 44100; stop at 0x842bc ret *)
    lf_step.
    lf_leaf ltac:(rewrite denot_lit_U; unfold w64; f_equal;
      rewrite lf_U_sext0, (U_atom E 10 mask E10 Hmask) by lia; rewrite lf_best_bits, Hb, Hb2; reflexivity).
Qed.

(* reac_rate_cfg_decide(role, hz, mask): 3 when role = 1; else the rate's bit b (44100, 96000, 48000 in the code's
   order) gives 2 when mask & b = 0 and 0 otherwise; no closed rate gives 1. *)
Theorem rt_cfg_decide_B : rt_cfg_decide_specX rsegs B MT A_CFG_DECIDE.
Proof using MTL LAWS.
unfold rt_cfg_decide_specX, rt_cpre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
lf_start A_CFG_DECIDE.
remember (bv_unsigned (getr regs 10)) as role eqn:Hr0. lf_atom role Hr0 E10 Hrole.
remember (bv_unsigned (getr regs 11)) as hz eqn:Hz0. lf_atom hz Hz0 E11 Hhz.
remember (bv_unsigned (getr regs 12)) as mask eqn:Hm0. lf_atom mask Hm0 E12 Hmask.
(* 0x846f8 li a3,1; stop at 0x846fc bne a0,a3 *)
lf_step. lf_branch Hb; rewrite branch_ne_U, (U_atom E 10 role E10 Hrole), U_lit in Hb by lia.
- apply Bool.negb_true_iff, Z.eqb_neq in Hb.
  (* 0x84708, 0x8470c; stop at 0x84710 beq a1,a0 (44100) *)
  lf_step. lf_branch Hb2; rewrite branch_eq_U, (U_atom E 11 hz E11 Hhz), U_lit in Hb2 by lia.
  + (* 0x84738 .. 0x84744 with a3 = 1; stop at 0x84748 ret *)
    apply Z.eqb_eq in Hb2. subst hz. lf_step.
    lf_leaf ltac:(idtac; lf_dec_tail 1 Hb (eq_refl : RateCfg.rate_bit 44100 = 1)).
  + apply Z.eqb_neq in Hb2.
    (* stop at 0x8471c beq a1,a0 (96000) *)
    lf_step. lf_branch Hb3; rewrite branch_eq_U, (U_atom E 11 hz E11 Hhz), U_lit in Hb3 by lia.
    * (* 0x84734 li a3,4; 0x84738 .. 0x84744; stop at 0x84748 ret *)
      apply Z.eqb_eq in Hb3. subst hz. lf_step.
      lf_leaf ltac:(idtac; lf_dec_tail 4 Hb (eq_refl : RateCfg.rate_bit 96000 = 4)).
    * apply Z.eqb_neq in Hb3.
      (* stop at 0x84728 bne a1,a0 (48000) *)
      lf_step. lf_branch Hb4; rewrite branch_ne_U, (U_atom E 11 hz E11 Hhz), U_lit in Hb4 by lia.
      -- (* 0x84744 mv a0,a3 (a3 = 1); stop at 0x84748 ret *)
         apply Bool.negb_true_iff, Z.eqb_neq in Hb4. lf_step.
         lf_leaf ltac:(rewrite lf_lit, (lf_decide_nc role hz mask Hb (lf_bit_0 hz Hb2 Hb4 Hb3)); reflexivity).
      -- (* 0x8472c li a3,2; j 0x84738; 0x84738 .. 0x84744; stop at 0x84748 ret *)
         apply Bool.negb_false_iff, Z.eqb_eq in Hb4. subst hz. lf_step.
         lf_leaf ltac:(idtac; lf_dec_tail 2 Hb (eq_refl : RateCfg.rate_bit 48000 = 2)).
- (* role = 1: 0x84700 li a3,3; j 0x84744; mv a0,a3; stop at 0x84748 ret *)
  apply Bool.negb_false_iff, Z.eqb_eq in Hb. subst role. lf_step.
  lf_leaf ltac:(rewrite lf_lit, lf_decide_slave; reflexivity).
Qed.
End c.

Print Assumptions rt_is_closed_B.
Print Assumptions rt_bit_B.
Print Assumptions rt_best_drivable_B.
Print Assumptions rt_cfg_decide_B.
