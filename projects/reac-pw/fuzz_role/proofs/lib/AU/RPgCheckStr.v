(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/RPgCheck.v at fb6520a9cda (its entry state ss_ck, regs_ok_override, the save-slot region and awr_stk / kwr_stk, ck_kept_run, the ret leaf) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_answer 0x82c30 and check_code 0x82c80 against lib/A/RPgCSpec.v's rl_check_answer_specX / rl_check_code_specX on lib/A/Img0.v rsegs. Each function is cut at its calls of the strcmp wrapper (0x41ad0): the run to the call, the call through lib/A/RPgStrcmp.v's aj_strcmp_at (the wrapper's contract astrcmp_realizes is the Section hypothesis ASTRCMP), and a fresh entry state after the call whose save slot holds the caller's ra (and s0) from the extra env slots 33 / 34; the callee-saved registers are threaded across the cuts with cs_eq. The snez-of-xor value lemma is lib/A/RPgCfgChanges.v's snez_xor_Z, restated. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b01; derived by derive_y.py (frozen b7b132fb12a7) for reac-pw/fuzz_role's asan-ubsan image (fuzz_role.asan-ubsan): modules lib.A.Img0 / RPgCheck -> lib.AU.Img0 / RPgCheck (lib/A/RPgBase.v, RPgCSpec.v and RPgStrcmp.v stay shared), the addresses moved to that image, the tops rl_check_answer_A / rl_check_code_A -> _B; by hand: the four literals by their text (derive_y paired the .str.N names, which shift by two in that image), the code table grows from 39 to 41 words (one `unimp` after each `jal abort`), the comments below restated at that image. The Modified-by lines above describe how lib/A/RPgCheckStr.v was made and quote that file's asan-image values. *)
(* check_answer 0x82b08 (21 words) and check_code 0x82b5c (20 words) of fuzz_role.asan-ubsan (unstripped sha256
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a; the pinned
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0 has the same bytes):
     check_answer: addi sp,sp,-0x10; sd ra,8(sp); xor a4,a2,a3; snez a4,a4; 0x82b18 bne a0,a4,0x82b50;
       0x82b1c bne a2,a3,0x82b2c; a2 := 0x214c0 ("applied", auipc / addi); j 0x82b34; 0x82b2c a2 := 0x21480
       ("role_reestablish_pending"); 0x82b34 mv a0,a1; mv a1,a2; 0x82b3c jal wrapper_strcmp 0x41b68;
       0x82b40 bnez a0,0x82b50; ld ra,8(sp); addi sp,sp,0x10; 0x82b4c ret; 0x82b50 jal __asan_handle_no_return;
       jal abort; 0x82b58 unimp.
     check_code: addi sp,sp,-0x10; sd ra,8(sp); sd s0,0(sp); mv s0,a1; a1 := 0x214e0 ("none");
       0x82b74 jal wrapper_strcmp; 0x82b78 bnez a0,0x82ba0; a1 := 0x21500 ("malformed"); mv a0,s0;
       0x82b88 jal wrapper_strcmp; 0x82b8c bnez a0,0x82ba0; ld ra,8(sp); ld s0,0(sp); addi sp,sp,0x10;
       0x82b9c ret; 0x82ba0 jal __asan_handle_no_return; jal abort; 0x82ba8 unimp.
   The words equal the asan image's 0x82c30 / 0x82c80 except the `jal` words (their targets moved), the auipc /
   addi pairs of the four literals (here .str.35 / .str.34 / .str.36 / .str.37, there .str.33 / .str.32 / .str.34 /
   .str.35: the same text and NUL), and the `unimp` after the `jal abort`, which does not return: no path of the
   walk reaches it.
   WHY THE ABORT PATHS ARE UNREACHABLE. check_answer's `bne a0,a4`: a0 = rl_changes cur req (the premise) and
   a4 = snez (cur xor cur') is the same value (snez_xor_Z), so the taken side is refuted. Every `bnez a0` after a
   wrapper call: both strings have the same text (the contract's rl_cstr premises: the argument string and the
   function's own literal), so they meet at the NUL with c1 = c2 = 0 (RPgStrcmp.v str_meet_of_cstr) and the
   wrapper returns strcmp_res 0 0 = 0; the entry state after the call holds a0 as the literal 0, so the engine
   decides the bnez not taken. The only stores are the saves into the 16-byte slot [sp - 16, sp); the wrapper
   writes only below the callee's sp - 16 (2 ESTACK); so every byte outside [sp - T_cmp_STK, sp) is kept. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgStrcmp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image: the two functions, one code table over both ---- *)
Definition A_CHECK_ANSWER : Z := 0x82b08.
Definition A_CHECK_CODE : Z := 0x82b5c.
Definition A_STRCMP : Z := 0x41b68.
Definition A_LIT_APPLIED : Z := 0x214c0.
Definition A_LIT_PENDING : Z := 0x21480.
Definition A_LIT_NONE : Z := 0x214e0.
Definition A_LIT_MALFORMED : Z := 0x21500.
(* the 41 4-byte words 0x82b08 .. 0x82ba8: check_answer (21), check_code (20) *)
Definition sc_tbl : ctable := build_table rsegs A_CHECK_ANSWER 41 TEmpty.
Lemma sc_tbl_ok : table_ok rsegs sc_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_ANSWER. lia. Qed.

(* ---- values ---- *)
(* `xor a4,a2,a3; snez a4,a4` on the two 64-bit words cur and req [lib/A/RPgCfgChanges.v snez_xor_Z] *)
Lemma sc_snez_xor : forall cur req, 0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
(if 0 <? Z.lxor cur req then 1 else 0) = rl_changes cur req.
Proof.
intros cur req Hc Hr. unfold rl_changes.
pose proof (YO0a.lxor_range cur req 64 Hc Hr) as Hx.
destruct (Z.eqb_spec cur req) as [->|Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- assert (N : Z.lxor cur req <> 0) by (intros Z0; apply Hne; apply Z.lxor_eq_0_iff; exact Z0).
destruct (Z.ltb_spec 0 (Z.lxor cur req)); [reflexivity | lia].
Qed.

(* ---- the callee-saved registers across the cuts ---- *)
Definition cs_eq (L : list (bv 5)) (ra rb : bvmap 5 word) : Prop := forall r, In r L -> getr rb r = getr ra r.
Lemma cs_eq_trans : forall L r1 r2 r3, cs_eq L r1 r2 -> cs_eq L r2 r3 -> cs_eq L r1 r3.
Proof. intros L r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
(* every register of the call-free part of the callee-saved set except sp (and s0 for check_code) *)
Definition L_ANS : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition L_CODE : list (bv 5) := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
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
Lemma L_CODE_sub : forall r, In r L_CODE -> In r L_ANS.
Proof. intros r Hr. cbv [L_CODE L_ANS In] in *. tauto. Qed.
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
(* a register that the state holds as the extra slot 32 + j *)
Lemma extra_of_st_ok : forall H E ss ms regs0 extra j (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs0 extra ->
sr_get (ss_regs ss) r = SOff (32 + j) 0 -> getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros H E ss ms regs0 extra j r HS HE Hsr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE, ew_Ereg_extra.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (nth j extra (Z_to_bv 64 0))) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.

(* ---- the save slot of the run before a call: the value of one of its chunks ---- *)
Lemma st_ok_region_nth : forall H E ss ms i r,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros H E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

(* ---- strings kept by a write below 2^46 ---- *)
Lemma rl_cstr_kept : forall H (m m' : word -> option byte) a s lo hi,
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs H m' x = aview rsegs H m x) -> 2 ^ 46 <= lo ->
rl_cstr rsegs H m a s -> rl_cstr rsegs H m' a s.
Proof.
intros H m m' a s lo hi HK Hlo (Hc & Hn & Hf & Ha0 & Hhi & Himg & Ham & Hra & Hhv).
assert (Hlow : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < kLowMemEnd)
by (intros i Hi; apply ck_segs_low; apply Himg; exact Hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Kx : forall x, 0 <= x < 2 ^ 46 -> aview rsegs H m' x = aview rsegs H m x) by (intros x Hx; apply HK; lia).
assert (Hsh : forall x, a <= x <= a + Z.of_nat (length s) -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46).
{ intros x Hx. pose proof (Hlow (x - a) ltac:(lia)) as Hl. unfold shadow_of_addr, SHADOW_OFF. rewrite C5 in Hl.
assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
split; [intros i Hi; rewrite Kx by (pose proof (Hlow i ltac:(lia)); rewrite C5 in *; lia); exact (Hc i Hi)|].
split; [rewrite Kx by (pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)); rewrite C5 in *; lia); exact Hn|].
split; [exact Hf|]. split; [exact Ha0|]. split; [exact Hhi|]. split; [exact Himg|]. split; [exact Ham|].
split.
- intros x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite Kx; [exact Hsv | apply Hsh; lia].
- intros t Ht. rewrite Kx; [exact (Hhv t Ht)|].
pose proof (Hlow 0 ltac:(lia)) as L0. pose proof (Hlow (Z.of_nat (length s)) ltac:(lia)) as L1.
unfold shadow_addr, SHADOW_OFF in Ht. rewrite C5 in L0, L1.
replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Ht by lia.
assert (0 <= a / 8) by (apply Z.div_pos; lia).
assert ((a + Z.of_nat (length s)) / 8 <= a + Z.of_nat (length s)) by (apply Z.div_le_upper_bound; lia).
assert (0 <= (0x7fff8000 + a / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
assert ((0x7fff8000 + (a + Z.of_nat (length s)) / 8) / 8 * 8 <= 0x7fff8000 + (a + Z.of_nat (length s)) / 8)
by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
lia.
Qed.

End a.

(* ---- the entry state after a call ---- *)
(* env Ereg regs2 [shadow base; ra0; s00]: slot 33 holds the caller's ra, slot 34 its s0; a0 is the literal 0 (the
   wrapper's answer); the save slot [sp, sp + 16) at the call's sp holds the chunks cs *)
Definition sc_extra (ra0 s00 : word) : list word := [Z_to_bv 64 ck_SB; ra0; s00].
Definition sc_slot (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 0 cs.
Definition ss_ret (pc : Z) (cs : list YP09.chunk) : sstate :=
mkSS pc (ck_sr [((10%bv : bv 5), SLit 0)]) [sc_slot cs] None ck_facts.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma sc_ret_entry : forall pc cs (W : world rsegs) regs2 ra0 s00 memc, 0 <= pc ->
getr regs2 (10%bv : bv 5) = w64 0 ->
2 ^ 46 <= spZ regs2 <= 2 ^ 47 - 16 -> spZ regs2 mod 16 = 0 ->
Forall (YP09.chunk_ok rsegs (Ereg regs2 (sc_extra ra0 s00)) (mrestrict (w_H W) memc) (spZ regs2)) cs ->
regions_wf [sc_slot cs] = true ->
st_ok rsegs (Ereg regs2 (sc_extra ra0 s00)) (ss_ret pc cs)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc cs W regs2 ra0 s00 memc Hpc H10 Hsp Hal Hcs Hwf.
rewrite restrict_mkst_fx.
set (E := Ereg regs2 (sc_extra ra0 s00)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs2) by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
unfold ss_ret. apply (entry_st_ok_full rsegs); change (Ereg regs2 (sc_extra ra0 s00)) with E.
- apply ck_regs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
+ intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
+ rewrite ck_lit. symmetry. exact H10.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok, sc_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. exact Hcs.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [ck_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End b.

(* ---- the leaf after the last call [RPgCheck.v ck_leaf with the aregs, model and memory chains given] ---- *)
Lemma same_io_wvb_sc : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Ltac sc_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok sc_tbl_ok HS HJ SHOK ck_Bspan; [awr | ] end.
Ltac sc_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok sc_tbl_ok HS SH ck_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_sc]; kio].

Lemma pres_of_cs : forall regs regsF, cs_eq L_ANS regs regsF -> spZ regsF = spZ regs -> aregs_preserved regs regsF.
Proof.
intros regs regsF HC H2 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc];
[first [ (apply bv_eq; exact H2) | (apply HC; cbv [L_ANS In]; repeat (first [left; apply bv_eq; reflexivity | right])) ] | ]);
subst; first [ (apply bv_eq; exact H2) | (apply HC; cbv [L_ANS In]; repeat (first [left; apply bv_eq; reflexivity | right])) ].
Qed.
Lemma pres_of_cs8 : forall regs regsF, cs_eq L_CODE regs regsF -> spZ regsF = spZ regs ->
getr regsF (8%bv : bv 5) = getr regs (8%bv : bv 5) -> aregs_preserved regs regsF.
Proof.
intros regs regsF HC H2 H8 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc];
[first [ (apply bv_eq; exact H2) | exact H8
       | (apply HC; cbv [L_CODE In]; repeat (first [left; apply bv_eq; reflexivity | right])) ] | ]);
subst; first [ (apply bv_eq; exact H2) | exact H8 | (apply HC; cbv [L_CODE In]; repeat (first [left; apply bv_eq; reflexivity | right])) ].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the strcmp wrapper's contract at its 4-byte jump 0x41b68 (lib/Reusable/AStrcmpDef.v, fuzz_identity's text); the
   relocated wrapper walk discharges it *)
Hypothesis ASTRCMP : astrcmp_realizes rsegs B A_STRCMP.

(* a string of the image lies below kLowMemEnd, so below every stack address *)
Lemma rl_cstr_low : forall H m a s, rl_cstr rsegs H m a s ->
forall b, a <= b <= a + Z.of_nat (length s) -> 0 <= b < kLowMemEnd.
Proof.
intros H m a s (_ & _ & _ & _ & _ & Himg & _) b Hb. replace b with (a + (b - a)) by lia. apply ck_segs_low. apply Himg. lia.
Qed.
Lemma mod16_off : forall sp sp0 c, sp mod 16 = 0 -> sp0 mod 16 = 0 -> c mod 16 = 0 -> (sp - c - sp0) mod 16 = 0.
Proof.
intros sp sp0 c H1 H2 H3.
pose proof (Z.div_mod sp 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
pose proof (Z.div_mod c 16 ltac:(lia)) as D3.
rewrite H1 in D1. rewrite H2 in D2. rewrite H3 in D3.
replace (sp - c - sp0) with ((sp / 16 - c / 16 - sp0 / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* ---- one call of the wrapper on two strings of the same text, from a caller whose save slot is at sp - 16 ---- *)
(* The call state: a0 = x, a1 = y, ra = raw, sp = the caller's entry sp minus 16; both strings hold the text t
   (at the caller's entry memory memc, and kept since: KT keeps every byte outside [sp - 16, sp)). After the call
   the wrapper's answer is 0, every callee-saved register is as at the call, and only [sp - 16 - 2 ESTACK, sp - 16)
   changed. *)
Lemma sc_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) regsT memT mdT
x y (t : list Z) raw klo (Q : world rsegs -> config -> Prop),
rl_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
getr regsT (10%bv : bv 5) = w64 x -> getr regsT (11%bv : bv 5) = w64 y -> getr regsT (1%bv : bv 5) = raw ->
YK0s.ret_ok raw -> spZ regsT = spZ regs - 16 -> cs_eq L_CODE regs regsT ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (klo <= a < spZ regs) -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a) ->
2 ^ 46 <= klo ->
rl_cstr rsegs (w_H W) memc x t -> rl_cstr rsegs (w_H W) memc y t -> Z.of_nat (length t) < 2 ^ 31 ->
(forall regs2 mem2 md2,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
aregs_preserved regsT regs2 -> same_io mdT md2 -> getr regs2 (10%bv : bv 5) = w64 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 - 2 * ESTACK <= a < spZ regs - 16) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) ->
SRr rsegs W (mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_STRCMP) memT (seg_rom rsegs)) mdT) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsT memT mdT x y t raw klo Q
HP HJT R10 R11 R1 Hraw RSP HCS KT Hklo Hx Hy Hlen K.
destruct HP as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_cmp_STK in Hwlo.
assert (HxT : rl_cstr rsegs (w_H W) memT x t) by (eapply rl_cstr_kept; [exact KT | exact Hklo | exact Hx]).
assert (HyT : rl_cstr rsegs (w_H W) memT y t) by (eapply rl_cstr_kept; [exact KT | exact Hklo | exact Hy]).
pose proof (rl_cstr_low _ _ _ _ HxT) as Lx. pose proof (rl_cstr_low _ _ _ _ HyT) as Ly.
destruct (str_meet_of_cstr rsegs t W memT x t y (cstr_at_of_rl_cstr rsegs W memT x t HxT)
(cstr_at_of_rl_cstr rsegs W memT y t HyT)) as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres).
assert (H0 : strcmp_res c1 c2 = 0) by (apply Hres; reflexivity).
assert (Hwin : forall b, (x <= b <= x + Z.of_nat (length t) \/ y <= b <= y + Z.of_nat (length t)) ->
~ (spZ regsT - ESTACK <= b < spZ regsT)).
{ intros b [Hb|Hb]; [pose proof (Lx b Hb) | pose proof (Ly b Hb)]; rewrite C5 in *; lia. }
destruct (rl_cstr_args rsegs W regsT memT x t kk HxT ltac:(lia) ltac:(intros b Hb; apply Hwin; left; exact Hb))
as (Hx0 & Hxk & Hsx & Hmx & Hrx & Hhx).
destruct (rl_cstr_args rsegs W regsT memT y t kk HyT ltac:(lia) ltac:(intros b Hb; apply Hwin; right; exact Hb))
as (Hy0 & Hyk & Hsy & Hmy & Hry & Hhy).
assert (G3 : getr regsT 3 = w64 (as_gp B)) by (rewrite (HCS (3%bv : bv 5) ltac:(cbv [L_CODE In]; left; reflexivity)); exact Hgp).
assert (G4 : getr regsT 4 = w64 (as_tp B)) by (rewrite (HCS (4%bv : bv 5) ltac:(cbv [L_CODE In]; right; left; reflexivity)); exact Htp).
eapply SRr_bind.
{ eapply (aj_strcmp_at rsegs B LAWS ck_segs_low A_STRCMP ASTRCMP W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k x y kk c1 c2 (spZ regs - 16 - sp0) raw HJT
R10 R11 Hx0 Hy0 ltac:(lia) Hxk Hyk Hmeet ltac:(lia) (mod16_off _ _ 16 Hal16 Hsp0al eq_refl) ltac:(lia) ltac:(lia)
G3 G4 R1 Hraw Hsx Hsy); try (intros a Ha; pose proof (Lx a ltac:(lia)); rewrite C5 in *; lia);
try (intros a Ha; pose proof (Ly a ltac:(lia)); rewrite C5 in *; lia); assumption. }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & H10 & HK2 & _).
apply K; [exact HJ2 | exact HP2 | exact Hsame | rewrite H10, H0; reflexivity |].
intros a Ha Hn. apply HK2; [exact Ha|]. intros Hw. apply Hn. lia.
Qed.

Lemma cs_eq_code_of_ans : forall r1 r2, cs_eq L_ANS r1 r2 -> cs_eq L_CODE r1 r2.
Proof. intros r1 r2 H r Hr. apply H. apply L_CODE_sub. exact Hr. Qed.

(* the value of the save slot's chunk at sp - 8 after the run to a call: the caller's ra *)
Ltac slot_val HS B2 E1 Hv rgs :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
lazymatch r with Some ?rg =>
let Hr := fresh "Hr" in assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
let Hreg := fresh "Hreg" in pose proof (st_ok_region_nth _ _ _ _ 0 _ HS Hr) as Hreg; clear Hr;
pose proof (field_of_region _ _ _ _ _ _ _ _ _ (-8) 8 (SOff 1 0) (raZ rgs) Hreg B2) as Hv;
clear Hreg;
specialize (Hv ltac:(cbn; tauto));
specialize (Hv ltac:(apply bv_eq; rewrite denot_SOff, Z.add_0_r, E1; unfold raZ; rewrite Z_to_bv_bv_unsigned;
  apply zcanon_id; pose proof (bv_unsigned_in_range _ (getr rgs 1)) as Hbnd; change (bv_modulus 64) with (2 ^ 64) in Hbnd;
  unfold M64; lia));
specialize (Hv ltac:(unfold raZ; pose proof (bv_unsigned_in_range _ (getr rgs 1)) as Hbnd;
  change (bv_modulus 64) with (2 ^ 64) in Hbnd; cbn; lia) ltac:(cbn; lia));
change (N.to_nat 8) with 8%nat in Hv
end end.

(* check_answer after its call: the entry state at 0x82b40 (a0 = 0, the slot [sp - 16, sp) holding ra at sp - 8),
   one run through `bnez a0` (not taken), `ld ra,8(sp)`, `addi sp,sp,0x10` to the ret, and the leaf. *)
Lemma ans_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) regsT memT mdT
x y (t : list Z),
rl_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
same_io mdc mdT ->
getr regsT (10%bv : bv 5) = w64 x -> getr regsT (11%bv : bv 5) = w64 y ->
getr regsT (1%bv : bv 5) = w64 0x82b40 -> spZ regsT = spZ regs - 16 -> cs_eq L_ANS regs regsT ->
val_mem rsegs (mrestrict (w_H W) memT) (spZ regs - 8) 8 (raZ regs) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a) ->
rl_cstr rsegs (w_H W) memc x t -> rl_cstr rsegs (w_H W) memc y t -> Z.of_nat (length t) < 2 ^ 31 ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_STRCMP) memT (seg_rom rsegs)) mdT)
(rl_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).
Proof using MTL LAWS ASTRCMP.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsT memT mdT x y t
HP HJT HioT R10 R11 R1 RSP HCS HSLOT KT Hx Hy Hlen.
pose proof HP as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_cmp_STK in Hwlo.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
apply (sc_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsT memT mdT x y t (w64 0x82b40) (spZ regs - 16) _
HP HJT R10 R11 R1 ltac:(vm_compute; reflexivity) RSP (cs_eq_code_of_ans _ _ HCS) KT ltac:(lia) Hx Hy Hlen).
intros regs2 mem2 md2 HJ HP2 Hsame H10 HK2.
assert (SP2 : spZ regs2 = spZ regs - 16).
{ rewrite <- RSP. unfold spZ. f_equal. exact (HP2 2 ltac:(unfold acallee_saved; lia)). }
assert (HV2 : val_mem rsegs (mrestrict (w_H W) mem2) (spZ regs2 + 8) 8 (raZ regs)).
{ rewrite SP2. replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia.
eapply (val_mem_kept rsegs); [|exact HSLOT]. intros kk Hkk. apply HK2; [lia | change (Z.of_nat 8) with 8 in Hkk; lia]. }
pose proof (sc_ret_entry 0x82b40 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))] W regs2 (getr regs 1) (Z_to_bv 64 0) mem2
ltac:(lia) H10 ltac:(rewrite SP2; lia) ltac:(rewrite SP2; pose proof (mod16_off _ 0 16 Hal16 eq_refl eq_refl) as M16; rewrite Z.sub_0_r in M16; exact M16))
as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val rsegs _ _ _ 8 8 (SOff 33 0) (raZ regs)); [
apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [sc_extra nth];
unfold raZ; rewrite Z_to_bv_bv_unsigned; apply zcanon_id; pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb;
change (bv_modulus 64) with (2 ^ 64) in Hb; unfold M64; lia
| unfold raZ; pose proof (bv_unsigned_in_range _ (getr regs 1)) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb; cbn; lia
| cbn; lia
| exact HV2 ])
ltac:(vm_compute; reflexivity)).
remember (Ereg regs2 (sc_extra (getr regs 1) (Z_to_bv 64 0))) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 (sc_extra (getr regs 1) (Z_to_bv 64 0))) E) by (subst E; apply env_agree_refl).
assert (E33 : ew E 33 = getr regs 1) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B2 : bv_unsigned (ew E 2) = spZ regs2) by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
clear HE.
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem2 a)
by (intros; reflexivity).
change (w64 0x82b40) with (Z_to_bv 64 0x82b40).
(* 0x82b40 bnez a0 (a0 = 0: not taken), ld ra,8(sp), addi sp,sp,0x10; stop at 0x82b4c ret *)
sc_run awr_stk. ck_keep kwr_stk.
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs2 _ 16 HS HAE ltac:(vm_compute; reflexivity)) as SPF;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ L_ANS HS HAE ltac:(vm_compute; reflexivity)) as CSF
end;
eapply (SRr_ret_at rsegs sc_tbl sc_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists.
split; [rewrite R1', E33, Hra; reflexivity|].
split; [reflexivity|].
split; [eapply ajournal_materialize; eassumption|].
split.
{ apply pres_of_cs.
- eapply cs_eq_trans; [exact HCS|]. eapply cs_eq_trans; [exact (cs_eq_of_pres L_ANS _ _ L_ANS_cs HP2)|]. exact CSF.
- rewrite SPF, SP2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. apply zcanon_id. unfold M64. lia. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [exact HioT|]; eapply same_io_trans; [exact Hsame|]; kio|].
split; [apply mo_le_refl; assumption|].
split; [|exact I].
intros a Ha Hz _. rewrite (KE a Ha (fun z => z)).
rewrite (HK2 a Ha ltac:(intros Hw; apply Hz; unfold T_cmp_STK; lia)).
apply KT; [exact Ha|]. intros Hw; apply Hz; unfold T_cmp_STK; lia.
Qed.

(* check_answer(changes, state, cur, req) *)
Theorem rl_check_answer_B : rl_check_answer_specX rsegs B MT A_CHECK_ANSWER A_LIT_APPLIED A_LIT_PENDING.
Proof using MTL LAWS ASTRCMP.
unfold rl_check_answer_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cur req s HP H10 H11 H12 Hcur H13 Hreq Hs Hla Hlp.
pose proof HP as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hwlo' : sp0 - STK <= spZ regs - 16) by (unfold T_cmp_STK in Hwlo; lia).
assert (Hrc : 0 <= rl_changes cur req < 2 ^ 64) by (unfold rl_changes; destruct (cur =? req); lia).
pose proof (ck_entry A_CHECK_ANSWER [] W regs memc ltac:(unfold A_CHECK_ANSWER; lia) (Forall_nil _)
ltac:(intros a Ha; apply Hpres; lia) ltac:(lia) Hal16) as HS.
remember (Ereg regs ck_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ck_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (rl_changes cur req)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 s) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 req) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
clear HE.
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_ANSWER) with (Z_to_bv 64 A_CHECK_ANSWER).
(* 0x82b08 .. 0x82b14; stop at 0x82b18 bne a0,a4 *)
sc_run awr_stk. ck_keep kwr_stk.
sc_branch Hn.
{ (* taken would reach the abort: a0 = rl_changes cur req = snez (cur xor req) = a4 *)
exfalso. rewrite branch_ne_U in Hn. rewrite (U_atom E 10 (rl_changes cur req) E10 Hrc) in Hn.
rewrite ?U_SAlu, ?U_SLit in Hn. cbn [zalu_raw] in Hn.
rewrite (U_atom E 12 cur E12 Hcur), (U_atom E 13 req E13 Hreq) in Hn.
unfold zcanon, M64 in Hn. rewrite (Z.mod_small (Z.lxor cur req)) in Hn by (apply YO0a.lxor_range; lia).
rewrite ?Z.mod_0_l in Hn by lia. rewrite sc_snez_xor in Hn by lia.
unfold rl_changes in Hn. destruct (cur =? req); cbn in Hn; discriminate Hn. }
clear Hn.
(* 0x82b1c bne a2,a3 *)
sc_run awr_stk. ck_keep kwr_stk.
sc_branch Hb.
all: rewrite branch_ne_U, (U_atom E 12 cur E12 Hcur), (U_atom E 13 req E13 Hreq) in Hb.
- (* taken: cur <> req, a2 = "role_reestablish_pending" (0x21480); run to the call *)
apply negb_true_iff in Hb. rewrite Hb in Hs.
sc_run awr_stk. ck_keep kwr_stk.
let R10' := fresh "R10'" in rreg HS (10%bv : bv 5) R10';
let R11' := fresh "R11'" in rreg HS (11%bv : bv 5) R11';
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
let Hv := fresh "Hv" in slot_val HS B2 E1 Hv regs;
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs _ (-16) HS HAE ltac:(vm_compute; reflexivity)) as SPT;
pose proof (cs_eq_of_st_ok _ _ ss ms regs _ L_ANS HS HAE ltac:(vm_compute; reflexivity)) as CST;
rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl);
replace (ss_pc ss) with A_STRCMP by (vm_compute; reflexivity)
end.
eapply (ans_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ s A_LIT_PENDING STR_PENDING HP);
[ eassumption | kio | rewrite R10', E11; reflexivity | rewrite R11'; reflexivity | rewrite R1'; reflexivity
| rewrite SPT; apply zcanon_id; unfold M64; lia | exact CST | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Hv
| exact KE | exact Hs | exact Hlp | cbn; lia ].
- (* not taken: cur = req, a2 = "applied" (0x214c0); run to the call *)
apply negb_false_iff in Hb. rewrite Hb in Hs.
sc_run awr_stk. ck_keep kwr_stk.
let R10' := fresh "R10'" in rreg HS (10%bv : bv 5) R10';
let R11' := fresh "R11'" in rreg HS (11%bv : bv 5) R11';
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
let Hv := fresh "Hv" in slot_val HS B2 E1 Hv regs;
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs _ (-16) HS HAE ltac:(vm_compute; reflexivity)) as SPT;
pose proof (cs_eq_of_st_ok _ _ ss ms regs _ L_ANS HS HAE ltac:(vm_compute; reflexivity)) as CST;
rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl);
replace (ss_pc ss) with A_STRCMP by (vm_compute; reflexivity)
end.
eapply (ans_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ s A_LIT_APPLIED STR_APPLIED HP);
[ eassumption | kio | rewrite R10', E11; reflexivity | rewrite R11'; reflexivity | rewrite R1'; reflexivity
| rewrite SPT; apply zcanon_id; unfold M64; lia | exact CST | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Hv
| exact KE | exact Hs | exact Hla | cbn; lia ].
Qed.

Lemma den_atom_reg : forall E regs0 extra n (r : bv 5), E = Ereg regs0 extra -> Z.of_nat n = bv_unsigned r ->
sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs0 r)).
Proof.
intros E regs0 extra n r HE Hn. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE, (ew_Ereg_nat regs0 extra n r Hn).
rewrite Z_to_bv_bv_unsigned. apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 r)) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.
Lemma den_extra : forall E regs0 extra j (w : word), E = Ereg regs0 extra -> nth j extra (Z_to_bv 64 0) = w ->
sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned w).
Proof.
intros E regs0 extra j w HE Hj. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE, ew_Ereg_extra, Hj.
rewrite Z_to_bv_bv_unsigned. apply zcanon_id. pose proof (bv_unsigned_in_range _ w) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
Qed.
Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb. Qed.
(* the value of a chunk of the first region (the save slot) of a run's state *)
Ltac slot_chunk HS B2 Hv od e v Hden :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
lazymatch r with Some ?rg =>
let Hr := fresh "Hr" in assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
let Hreg := fresh "Hreg" in pose proof (st_ok_region_nth _ _ _ _ 0 _ HS Hr) as Hreg; clear Hr;
pose proof (field_of_region _ _ _ _ _ _ _ _ _ od 8 e v Hreg B2 ltac:(cbn; tauto) Hden) as Hv;
clear Hreg;
specialize (Hv ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); first [apply word_range | unfold raZ; apply word_range])
  ltac:(cbn; lia));
change (N.to_nat 8) with 8%nat in Hv
end end.
(* the slot chunks of check_code after a call: the caller's s0 at sp + 0, its ra at sp + 8 (sp = the call's) *)
Definition code_slot : list YP09.chunk := [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Lemma code_slot_ok : forall (W : world rsegs) regs2 (regs : bvmap 5 word) mem2,
val_mem rsegs (mrestrict (w_H W) mem2) (spZ regs2 + 0) 8 (bv_unsigned (getr regs 8)) ->
val_mem rsegs (mrestrict (w_H W) mem2) (spZ regs2 + 8) 8 (raZ regs) ->
Forall (YP09.chunk_ok rsegs (Ereg regs2 (sc_extra (getr regs 1) (getr regs 8))) (mrestrict (w_H W) mem2) (spZ regs2)) code_slot.
Proof.
intros W regs2 regs mem2 H0 H8. unfold code_slot. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_ok_val rsegs _ _ _ 0 8 (SOff 34 0) (bv_unsigned (getr regs 8))); [| apply word_range | cbn; lia | exact H0].
change 34%nat with (32 + 2)%nat. apply (den_extra _ regs2 _ 2 _ eq_refl). reflexivity.
- apply (chunk_ok_val rsegs _ _ _ 8 8 (SOff 33 0) (raZ regs)); [| apply word_range | cbn; lia | exact H8].
change 33%nat with (32 + 1)%nat. apply (den_extra _ regs2 _ 1 _ eq_refl). reflexivity.
Qed.

(* check_code after its second call: the entry state at 0x82b8c (a0 = 0, the slot holding s0 and ra), one run
   through `bnez a0` (not taken), `ld ra,8(sp)`, `ld s0,0(sp)`, `addi sp,sp,0x10` to the ret, and the leaf. *)
Lemma code_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) regs3 mem3 md3,
rl_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k ->
same_io mdc md3 -> getr regs3 (10%bv : bv 5) = w64 0 ->
spZ regs3 = spZ regs - 16 -> cs_eq L_CODE regs regs3 ->
val_mem rsegs (mrestrict (w_H W) mem3) (spZ regs - 8) 8 (raZ regs) ->
val_mem rsegs (mrestrict (w_H W) mem3) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_cmp_STK <= a < spZ regs) -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a) ->
SRr rsegs W (mkCfg (mkst regs3 (w64 0x82b8c) mem3 (seg_rom rsegs)) md3)
(rl_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs3 mem3 md3 HP HJ Hio3 H10 SP3 HCS HRA HS0 K3.
pose proof HP as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJ0.
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
assert (Hwlo' : sp0 - STK <= spZ regs - (16 + 2 * ESTACK)) by (unfold T_cmp_STK in Hwlo; exact Hwlo).
pose proof (sc_ret_entry 0x82b8c code_slot W regs3 (getr regs 1) (getr regs 8) mem3 ltac:(lia) H10
ltac:(rewrite SP3; lia)
ltac:(rewrite SP3; pose proof (mod16_off _ 0 16 Hal16 eq_refl eq_refl) as M16; rewrite Z.sub_0_r in M16; exact M16)
(code_slot_ok W regs3 regs mem3 ltac:(rewrite SP3, Z.add_0_r; exact HS0)
ltac:(rewrite SP3; replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia; exact HRA))
ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg regs3 (sc_extra (getr regs 1) (getr regs 8))) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 (sc_extra (getr regs 1) (getr regs 8))) E) by (subst E; apply env_agree_refl).
assert (E33 : ew E 33 = getr regs 1) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (B2 : bv_unsigned (ew E 2) = spZ regs3) by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) mem3 a)
by (intros; reflexivity).
change (w64 0x82b8c) with (Z_to_bv 64 0x82b8c).
(* 0x82b8c bnez a0 (a0 = 0: not taken), ld ra, ld s0, addi sp; stop at 0x82b9c ret *)
sc_run awr_stk. ck_keep kwr_stk.
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs3 _ 16 HS HAE ltac:(vm_compute; reflexivity)) as SPF;
pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ L_CODE HS HAE ltac:(vm_compute; reflexivity)) as CSF;
pose proof (extra_of_st_ok _ _ ss ms regs3 _ 2 (8%bv : bv 5) HS HE ltac:(vm_compute; reflexivity)) as S0F
end;
eapply (SRr_ret_at rsegs sc_tbl sc_tbl_ok ck_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; eexists; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists.
split; [rewrite R1', E33, Hra; reflexivity|].
split; [reflexivity|].
split; [eapply ajournal_materialize; eassumption|].
split.
{ apply pres_of_cs8.
- eapply cs_eq_trans; [exact HCS|]. exact CSF.
- rewrite SPF, SP3. replace (spZ regs - 16 + 16) with (spZ regs) by lia. apply zcanon_id. unfold M64. lia.
- rewrite S0F. reflexivity. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [exact Hio3|]; kio|].
split; [apply mo_le_refl; assumption|].
split; [|exact I].
intros a Ha Hz _. rewrite (KE a Ha (fun z => z)). exact (K3 a Ha Hz).
Qed.

(* check_code between its calls: the entry state at 0x82b78 (a0 = 0, s0 = sm, the slot holding s0 and ra), one
   run through `bnez a0` (not taken), a1 := 0x21500, `mv a0,s0` and the `jal` to the wrapper, the second call, and
   code_tail. *)
Lemma code_mid : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) regs2 mem2 md2 sm,
rl_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
same_io mdc md2 -> getr regs2 (10%bv : bv 5) = w64 0 -> getr regs2 (8%bv : bv 5) = w64 sm ->
spZ regs2 = spZ regs - 16 -> cs_eq L_CODE regs regs2 ->
val_mem rsegs (mrestrict (w_H W) mem2) (spZ regs - 8) 8 (raZ regs) ->
val_mem rsegs (mrestrict (w_H W) mem2) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_cmp_STK <= a < spZ regs) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
rl_cstr rsegs (w_H W) memc sm STR_MALFORMED -> rl_cstr rsegs (w_H W) memc A_LIT_MALFORMED STR_MALFORMED ->
SRr rsegs W (mkCfg (mkst regs2 (w64 0x82b78) mem2 (seg_rom rsegs)) md2)
(rl_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_cmp_STK regs lyc Sc W memc mdc
(fun f => f = fx) (fun _ => False) (fun _ _ _ => True)).
Proof using MTL LAWS ASTRCMP.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 sm HP HJ Hio2 H10 H8 SP2 HCS HRA HS0 K2 Hsm Hlm.
pose proof HP as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJ0.
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
assert (Hwlo' : sp0 - STK <= spZ regs - (16 + 2 * ESTACK)) by (unfold T_cmp_STK in Hwlo; exact Hwlo).
pose proof (sc_ret_entry 0x82b78 code_slot W regs2 (getr regs 1) (getr regs 8) mem2 ltac:(lia) H10
ltac:(rewrite SP2; lia)
ltac:(rewrite SP2; pose proof (mod16_off _ 0 16 Hal16 eq_refl eq_refl) as M16; rewrite Z.sub_0_r in M16; exact M16)
(code_slot_ok W regs2 regs mem2 ltac:(rewrite SP2, Z.add_0_r; exact HS0)
ltac:(rewrite SP2; replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia; exact HRA))
ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg regs2 (sc_extra (getr regs 1) (getr regs 8))) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 (sc_extra (getr regs 1) (getr regs 8))) E) by (subst E; apply env_agree_refl).
assert (E8 : ew E 8 = getr regs2 8) by (subst E; exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs2) by (subst E; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem2 a)
by (intros; reflexivity).
change (w64 0x82b78) with (Z_to_bv 64 0x82b78).
(* 0x82b78 bnez a0 (a0 = 0: not taken), a1 := 0x21500, mv a0,s0, 0x82b88 jal: stop at 0x41b68 *)
sc_run awr_stk. ck_keep kwr_stk.
let R10' := fresh "R10'" in rreg HS (10%bv : bv 5) R10';
let R11' := fresh "R11'" in rreg HS (11%bv : bv 5) R11';
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs2 _ 0 HS HAE ltac:(vm_compute; reflexivity)) as SPT;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ L_CODE HS HAE ltac:(vm_compute; reflexivity)) as CST;
rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl);
replace (ss_pc ss) with A_STRCMP by (vm_compute; reflexivity)
end.
assert (SPT' : spZ (ms_regs ms) = spZ regs - 16) by (rewrite SPT, Z.add_0_r, SP2; apply zcanon_id; unfold M64; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 - 2 * ESTACK <= a < spZ regs) ->
aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hz. rewrite (KE a Ha (fun z => z)). apply K2; [exact Ha|]. unfold T_cmp_STK. lia. }
apply (sc_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs ms) (ms_mem ms) _ sm A_LIT_MALFORMED
STR_MALFORMED (w64 0x82b8c) (spZ regs - 16 - 2 * ESTACK) _ HP ltac:(eassumption)
ltac:(rewrite R10', E8; exact H8) ltac:(rewrite R11'; reflexivity) ltac:(rewrite R1'; reflexivity)
ltac:(vm_compute; reflexivity) SPT' (cs_eq_trans _ _ _ _ HCS CST) KT ltac:(lia) Hsm Hlm ltac:(cbn; lia)).
intros regs3 mem3 md3 HJ3 HP3 Hio3 H103 HK3.
assert (SP3 : spZ regs3 = spZ regs - 16).
{ rewrite <- SPT'. unfold spZ. f_equal. exact (HP3 2 ltac:(unfold acallee_saved; lia)). }
apply (code_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs3 mem3 md3 HP HJ3).
- eapply same_io_trans; [exact Hio2|]. eapply same_io_trans; [|exact Hio3]. kio.
- exact H103.
- exact SP3.
- eapply cs_eq_trans; [exact (cs_eq_trans _ _ _ _ HCS CST)|].
exact (cs_eq_of_pres L_CODE _ _ (fun r Hr => L_ANS_cs r (L_CODE_sub r Hr)) HP3).
- eapply (val_mem_kept rsegs); [|exact HRA]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
match goal with |- aview _ _ _ ?q = _ => rewrite (HK3 q ltac:(lia) ltac:(lia)), (KE q ltac:(lia) (fun z => z)); reflexivity end.
- eapply (val_mem_kept rsegs); [|exact HS0]. intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
match goal with |- aview _ _ _ ?q = _ => rewrite (HK3 q ltac:(lia) ltac:(lia)), (KE q ltac:(lia) (fun z => z)); reflexivity end.
- intros a Ha Hz. rewrite (HK3 a Ha ltac:(unfold T_cmp_STK in Hz; lia)). rewrite (KE a Ha (fun z => z)).
exact (K2 a Ha Hz).
Qed.

(* check_code(none, malformed) *)
Theorem rl_check_code_B : rl_check_code_specX rsegs B MT A_CHECK_CODE A_LIT_NONE A_LIT_MALFORMED.
Proof using MTL LAWS ASTRCMP.
unfold rl_check_code_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sn sm HP H10 H11 Hsn Hsm Hln Hlm.
pose proof HP as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hwlo' : sp0 - STK <= spZ regs - 16) by (unfold T_cmp_STK in Hwlo; lia).
pose proof (ck_entry A_CHECK_CODE [] W regs memc ltac:(unfold A_CHECK_CODE; lia) (Forall_nil _)
ltac:(intros a Ha; apply Hpres; lia) ltac:(lia) Hal16) as HS.
remember (Ereg regs ck_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ck_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 sn) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 sm) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (D1 : sv_denot E (SOff 1 0) = Z_to_bv 64 (raZ regs)) by (exact (den_atom_reg E regs ck_extra 1 1%bv HE eq_refl)).
assert (D8 : sv_denot E (SOff 8 0) = Z_to_bv 64 (bv_unsigned (getr regs 8))) by (exact (den_atom_reg E regs ck_extra 8 8%bv HE eq_refl)).
clear HE.
assert (SHOK : sh_ok rsegs ck_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_CHECK_CODE) with (Z_to_bv 64 A_CHECK_CODE).
(* 0x82b5c .. 0x82b70, 0x82b74 jal: stop at 0x41b68 *)
sc_run awr_stk. ck_keep kwr_stk.
let R10' := fresh "R10'" in rreg HS (10%bv : bv 5) R10';
let R11' := fresh "R11'" in rreg HS (11%bv : bv 5) R11';
let R1' := fresh "R1'" in rreg HS (1%bv : bv 5) R1';
let R8' := fresh "R8'" in rreg HS (8%bv : bv 5) R8';
let Hv := fresh "Hra8" in slot_chunk HS B2 Hv (-8) (SOff 1 0) (raZ regs) D1;
let Hv := fresh "Hs0" in slot_chunk HS B2 Hv (-16) (SOff 8 0) (bv_unsigned (getr regs 8)) D8;
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (sp_of_st_ok _ _ ss ms regs _ (-16) HS HAE ltac:(vm_compute; reflexivity)) as SPT;
pose proof (cs_eq_of_st_ok _ _ ss ms regs _ L_CODE HS HAE ltac:(vm_compute; reflexivity)) as CST;
rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl);
replace (ss_pc ss) with A_STRCMP by (vm_compute; reflexivity)
end.
assert (SPT' : spZ (ms_regs ms) = spZ regs - 16) by (rewrite SPT; apply zcanon_id; unfold M64; lia).
apply (sc_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs ms) (ms_mem ms) _ sn A_LIT_NONE
STR_NONE (w64 0x82b78) (spZ regs - 16) _ HP ltac:(eassumption)
ltac:(rewrite R10', E10; reflexivity) ltac:(rewrite R11'; reflexivity) ltac:(rewrite R1'; reflexivity)
ltac:(vm_compute; reflexivity) SPT' CST KE ltac:(lia) Hsn Hln ltac:(cbn; lia)).
intros regs2 mem2 md2 HJ2 HP2 Hio2 H102 HK2.
assert (SP2 : spZ regs2 = spZ regs - 16).
{ rewrite <- SPT'. unfold spZ. f_equal. exact (HP2 2 ltac:(unfold acallee_saved; lia)). }
apply (code_mid STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 sm HP HJ2).
- eapply same_io_trans; [|exact Hio2]. kio.
- exact H102.
- transitivity (getr (ms_regs ms) (8%bv : bv 5)); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | rewrite R8', E11; reflexivity].
- exact SP2.
- eapply cs_eq_trans; [exact CST|].
exact (cs_eq_of_pres L_CODE _ _ (fun r Hr => L_ANS_cs r (L_CODE_sub r Hr)) HP2).
- eapply (val_mem_kept rsegs); [|replace (spZ regs - 8) with (spZ regs + -8) by lia; exact Hra8].
intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HK2; lia.
- eapply (val_mem_kept rsegs); [|replace (spZ regs - 16) with (spZ regs + -16) by lia; exact Hs0].
intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HK2; lia.
- intros a Ha Hz. rewrite (HK2 a Ha ltac:(unfold T_cmp_STK in Hz; lia)). apply KE; [exact Ha|].
unfold T_cmp_STK in Hz; lia.
- exact Hsm.
- exact Hlm.
Qed.
End c.

Print Assumptions rl_check_answer_B.
Print Assumptions rl_check_code_B.
