(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 57c6c35a3757 (the stage form of
   a walk with calls: a run to the `jal`, the callee's contract through SRr_bind, a fresh entry state at the return
   pc; tl_enter, tl_r234, tl_sp_of_cs) for reac-pw/fuzz_rate's image A: rate's pcs, registers, callees and contracts
   (lib/A/RtPgCSpec.v), the cut states of lib/A/RtPgSeg.v and the M02 seam of lib/A/RtPgM02Base.v; the asked[t]
   check, the two closed_list scans, the zone of the two .data.rel.ro tables and the latch of the decide loop are
   new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgDec.v at 25294b2cbc77 for image B
   (fuzz_rate.asan-ubsan): image B's pcs, code table and callee addresses; the turn counter is s10 = t with the bound
   s9 = 2 (no turn flag), asked[t] is the real-frame cell R + 0x198 + 4 t read twice without a check (no asked[t]
   check, a second load before reac_rate_bit), the role is s5, cfg_decide's answer is held in s6 and the mask is
   reloaded into s6 from R + 0x148, closed_list is s2 and the shadow offset s4; the cuts are lib/AU/RtPgSegB.v's, the
   M02 seam lib/AU/RtPgM02BaseB.v's, the callees' walks lib/AU's. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's). Proves no
   function (kind: segment lemma): the piece "one turn of the decide loop" of LLVMFuzzerTestOneInput's segment M02,
   whose statement is lib/AU/RtPgSegB.v's rsb_piece_W13_stmt; nothing here restates a cut.

   THE CODE (fuzz_rate.c:263-269; DEC = 0x82e44 is the loop's head, T2 = 0x82f8c the pc after it):
     0x82e44 slli s8,s10,2; addi a0,s1,408; add s8,a0,s8 (s8 = R + 0x198 + 4 t); 0x82e50 lw s7,0(s8) (asked[t],
             sign-extended, no check); mv a0,s5; mv a1,s7; mv a2,s6 (the mask); 0x82e60 jal cfg_decide
     0x82e64 mv s6,a0; li a1,3; 0x82e6c bnez s5 -> 0x82f2c (a slave: the expectation is 3)
     0x82e70 the first bit_of scan over closed_list (s2 = 0x21520; a1 counts 3, 2, 1; each word checked, the check
             of closed_list[2] on its slow block 0x82ea4); `beq s7,a3` 0x82e8c -> 0x82eb4; not found: 0x82f04 a1 := 1
     0x82eb4 the second scan finds the same index i (slow block 0x82ef4) -> 0x82f0c a0 := 1 << i;
             0x82f1c ld a1,0x148(s1); and a0,a0,a1; seqz a1,a0; slli a1,a1,1 (2 or 0)
     0x82f2c mv a0,s6; 0x82f30 jal check_decide; 0x82f34 mv a0,s6; jal refuse_code; 0x82f3c mv a1,s6; jal check_code;
     0x82f44 lw s11,0(s8) (asked[t] again, no check); mv a0,s11; jal bit; 0x82f50 mv s7,a0; mv a0,s11; jal is_closed;
     0x82f5c mv s8,a0; ld s6,0x148(s1); mv a0,s6; jal best_drivable; 0x82f6c mv a4,a0; mv a0,s11; mv a1,s7;
             mv a2,s8; mv a3,s6; 0x82f80 jal check_list
     0x82f84 addi s10,s10,1; 0x82f88 bne s10,s9 -> DEC; 0x82f8c T2.

   HOW. The turn is cut at each call, in RPgM02Tail's form: a stage lemma per return pc (dtb_s0 at DEC, dtb_s1 at
   0x82e64, dtb_s2 .. dtb_s7 at 0x82f34 .. 0x82f6c, dtb_latch at 0x82f84) runs the token engine (lib/Reusable/YCbn.v,
   shadow base s4 = atom 20) from a fresh entry state to the callee's entry, applies the callee's contract through
   SRr_bind (RtPgM02BaseB.m2b_pre_call for its rt_cpre) and gives the return state, through m2b_core_call, to the
   next stage. dtb_s0 is entered with s10 as the literal t, so the engine forms s8 = R + 0x198 + 4 t as an offset of
   s1 and reads asked[t] from the real-frame region of that turn. The turn's two instrumented checks are `bnez`
   checks whose slow block returns: the engine leaves each as a token and asks the 4-byte access addressable, which
   rt_i32tab (closed_list) pays. dtb_s1 splits the role and the asked value: a slave (the engine runs straight to
   check_decide with a1 = 3), one of the three closed rates (the asked value is a literal, so the engine decides
   both scans), or none of them (three `beq` splits, whose taken arms contradict rate_bit = 0). In every case the
   inline expectation equals RateCfg.decide_res, cfg_decide's answer (the dtb_dec lemmas), which is check_decide's
   premise. refuse_code's answer is the address of the text check_code compares with (m2b_site_strs carried to the
   call: dtb_strs); dtb_s4 reads asked[t] again through s8 (its cell is above R, so every callee keeps it), and bit,
   is_closed and best_drivable give check_list its premises by construction. Every callee returns at the float
   state it was called at, so the whole turn is at the cut's own float state. The latch decides `bne s10,s9` on the
   literals t + 1 and 2, and rt_dec_turn_B rebuilds RtPgSegB's DEC cut at turn 1, or its T2 cut, from the DEC cut it
   started at: every register of the cut is callee-saved and kept (dtb_Lk), s6 holds the mask again, and no byte
   outside [R - T_SEG_STK, R) is written (dtb_kept).

   SECTION HYPOTHESES of rt_dec_turn_B (Section m): MTL : ameter_laws MT; HBgot / HBcell (as_got_shadow B = 0x9c170,
   as_shadow_cell B = 0xa4f38, which lib/AU/RtPgRefuseB.v's, lib/AU/RtPgCheckCode.v's and lib/AU/RtPgCheckList.v's
   walks take); ASTRCMP : the strcmp wrapper's contract (lib/Reusable/AStrcmpDef.v astrcmp_realizes at 0x421f4) at
   every float state, for check_code. The callees are the theorems of lib/AU/RtPgLeaf.v (cfg_decide, bit, is_closed,
   best_drivable), lib/AU/RtPgCheck.v (check_decide), lib/AU/RtPgRefuseB.v (refuse_code), lib/AU/RtPgCheckCode.v
   (check_code) and lib/AU/RtPgCheckList.v (check_list). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgRefuse RtPgCheckCode RtPgRefuseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgLeaf RtPgCheckList.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgM02BaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================= the image ======================================= *)
(* the return pcs of the turn's eight calls; DEC = RSB_DEC is the turn's first pc *)
Definition DTB_R_CFG : Z := 0x82e64.
Definition DTB_R_CDEC : Z := 0x82f34.
Definition DTB_R_REF : Z := 0x82f3c.
Definition DTB_R_CODE : Z := 0x82f44.
Definition DTB_R_BIT : Z := 0x82f50.
Definition DTB_R_CLO : Z := 0x82f5c.
Definition DTB_R_BEST : Z := 0x82f6c.
Definition DTB_LATCH : Z := 0x82f84.

(* the 82 4-byte words 0x82e44 .. 0x82f88: the turn, its two slow blocks 0x82ea4 and 0x82ef4 and the latch; T2
   0x82f8c, the two report jumps' targets 0x832e0 / 0x832f8 and every callee lie outside it, as the engine's stop
   pcs *)
Definition dtb_tbl : ctable := build_table rsegs RSB_DEC 82 TEmpty.
Lemma dtb_tbl_ok : table_ok rsegs dtb_tbl.
Proof. apply build_table_ok0. unfold RSB_DEC. lia. Qed.

(* the registers the turn keeps from DEC to its latch: s5 (the role), s0, s1, s2 (&closed_list), s3, s4 (the shadow
   offset), s9 (2), s10 (t); every one callee-saved and written by no instruction before the latch *)
Definition dtb_L : list (bv 5) := [21; 8; 9; 18; 19; 20; 25; 26]%bv.
(* the same without s5 (the slave test reads s5 as a literal) *)
Definition dtb_L' : list (bv 5) := [8; 9; 18; 19; 20; 25; 26]%bv.
(* the scan stage keeps dtb_L' and s8 (it writes s6, and reads s5 and, for a closed rate, s7 as literals) *)
Definition dtb_L1 : list (bv 5) := [8; 9; 18; 19; 20; 25; 26; 24]%bv.
(* the head stage keeps dtb_L without s10 (a literal there) and s6 (the mask) *)
Definition dtb_L0 : list (bv 5) := [21; 8; 9; 18; 19; 20; 25; 22]%bv.
(* dtb_L and s6, s7, s8, s11, the values the calls hand on *)
Definition dtb_Lf : list (bv 5) := [21; 8; 9; 18; 19; 20; 25; 26; 22; 23; 24; 27]%bv.
(* dtb_Lf without s11 (bit's stage writes it), without s7 (is_closed's stage writes it) and without s6, s8
   (best_drivable's stage writes them) *)
Definition dtb_L4 : list (bv 5) := [21; 8; 9; 18; 19; 20; 25; 26; 22; 23; 24]%bv.
Definition dtb_L5 : list (bv 5) := [21; 8; 9; 18; 19; 20; 25; 26; 22; 24; 27]%bv.
Definition dtb_L6 : list (bv 5) := [21; 8; 9; 18; 19; 20; 25; 26; 23; 27]%bv.
(* the registers DEC's cut and T2's cut name, both lists kept: dtb_L without s10 *)
Definition dtb_Lk : list (bv 5) := [8; 9; 18; 19; 20; 21; 25]%bv.
(* the latch keeps dtb_Lk without s9 (a literal there) and s6 *)
Definition dtb_LL : list (bv 5) := [8; 9; 18; 19; 20; 21; 22]%bv.

Ltac dtb_cs_tac :=
intros r Hr; cbv [dtb_L In] in Hr; unfold acallee_saved;
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]);
destruct Hr.
Lemma dtb_L_cs : forall r, In r dtb_L -> acallee_saved (bv_unsigned r).
Proof. dtb_cs_tac. Qed.

Ltac dtb_in := cbv [dtb_L dtb_L' dtb_L1 dtb_L0 dtb_Lf dtb_L4 dtb_L5 dtb_L6 dtb_Lk dtb_LL In];
  repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma dtb_cs_cons : forall L r1 r2 (x : bv 5), cs_eq L r1 r2 -> getr r2 x = getr r1 x -> cs_eq (x :: L) r1 r2.
Proof. intros L r1 r2 x H Hx r [<- | Hr]; [exact Hx | exact (H r Hr)]. Qed.
Lemma dtb_cs_sub : forall L L' r1 r2, cs_eq L r1 r2 -> (forall r, In r L' -> In r L) -> cs_eq L' r1 r2.
Proof. intros L L' r1 r2 H Hs r Hr. exact (H r (Hs r Hr)). Qed.
Lemma dtb_Lf_L : forall r, In r dtb_L -> In r dtb_Lf.
Proof. intros r Hr. cbv [dtb_L dtb_Lf In] in *. tauto. Qed.
Lemma dtb_L4_L : forall r, In r dtb_L -> In r dtb_L4.
Proof. intros r Hr. cbv [dtb_L dtb_L4 In] in *. tauto. Qed.
Lemma dtb_L5_L : forall r, In r dtb_L -> In r dtb_L5.
Proof. intros r Hr. cbv [dtb_L dtb_L5 In] in *. tauto. Qed.
Lemma dtb_L6_L : forall r, In r dtb_L -> In r dtb_L6.
Proof. intros r Hr. cbv [dtb_L dtb_L6 In] in *. tauto. Qed.
Lemma dtb_L'_L1 : forall r, In r dtb_L' -> In r dtb_L1.
Proof. intros r Hr. cbv [dtb_L' dtb_L1 In] in *. tauto. Qed.
Lemma dtb_L_L0' : forall r, In r dtb_L -> In r (26%bv :: dtb_L0).
Proof. intros r Hr. cbv [dtb_L dtb_L0 In] in *. tauto. Qed.
Lemma dtb_L_Lk : forall r, In r dtb_Lk -> In r dtb_L.
Proof. intros r Hr. cbv [dtb_L dtb_Lk In] in *. tauto. Qed.
Lemma dtb_Lk_LL : forall r, In r dtb_Lk -> In r (25%bv :: dtb_LL).
Proof. intros r Hr. cbv [dtb_Lk dtb_LL In] in *. tauto. Qed.
(* [RPgM02Tail.v tl_r234] *)
Lemma dtb_r234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Proof.
intros r1 r2 H r Hr; destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma dtb_sp_of_cs : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. unfold spZ. rewrite (H 2%bv); [reflexivity | cbv [In]; left; reflexivity]. Qed.
Lemma dtb_w64_unsigned : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma dtb_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r. rewrite !unsigned_lit_small by exact Hv.
apply zcanon_id. unfold M64. lia.
Qed.

(* ======================================= arithmetic ======================================= *)
(* asked[t] as the `lw` loads it: the 4-byte value u sign-extended, as the integer value of the 64-bit word *)
Definition dtb_sx (u : Z) : Z := if u <? 2 ^ 31 then u else u - 2 ^ 32.
Definition dtb_v (u : Z) : Z := dtb_sx u mod 2 ^ 64.
Lemma dtb_v_range : forall u, 0 <= dtb_v u < 2 ^ 64.
Proof. intros u. unfold dtb_v. apply Z.mod_pos_bound. lia. Qed.
Lemma dtb_v_small : forall u, 0 <= u < 2 ^ 31 -> dtb_v u = u.
Proof.
intros u Hu. unfold dtb_v, dtb_sx. destruct (Z.ltb_spec u (2 ^ 31)); [|lia]. apply Z.mod_small. lia.
Qed.
Lemma dtb_swrap32 : forall u, 0 <= u < 2 ^ 32 -> bv_swrap 32 u = dtb_sx u.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, dtb_sx.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (u + 2 ^ 31) with ((u + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma dtb_U_sext : forall E (n : nat) u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = dtb_v u.
Proof.
intros E n u H Hu. rewrite U_SExt, (U_atom E n u H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia. rewrite dtb_swrap32 by lia.
unfold zcanon, M64, dtb_v. reflexivity.
Qed.
Lemma dtb_rate_bit_v : forall u, 0 <= u < 2 ^ 32 -> RateCfg.rate_bit (dtb_v u) = RateCfg.rate_bit u.
Proof.
intros u Hu. unfold dtb_v, dtb_sx.
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. reflexivity.
- replace (u - 2 ^ 32) with ((u - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  unfold RateCfg.rate_bit, RateCfg.RATE_44K1, RateCfg.RATE_48K, RateCfg.RATE_96K.
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end; first [reflexivity | lia].
Qed.
(* the inline expectation's answers for a master, as RateCfg.decide_res gives them (a slave's 3 is decide_res 1 by
   computation) *)
Lemma dtb_dec_nc : forall v mask, RateCfg.rate_bit v = 0 -> RateCfg.decide_res 0 v mask = 1.
Proof. intros v mask H. unfold RateCfg.decide_res. rewrite H. reflexivity. Qed.
Lemma dtb_dec_bit : forall v mask b, RateCfg.rate_bit v = b -> b <> 0 ->
RateCfg.decide_res 0 v mask = if Z.land mask b =? 0 then 2 else 0.
Proof.
intros v mask b H Hb. unfold RateCfg.decide_res. rewrite H, Z.land_comm.
destruct (Z.eqb_spec b 0); [lia|]. reflexivity.
Qed.
Lemma dtb_dec_range : forall role v mask, 0 <= RateCfg.decide_res role v mask <= 4.
Proof. intros role v mask. pose proof (RateCfg.decide_res_range role v mask). lia. Qed.
(* asked[1]: the u32 of the four header bytes is below 2^32 *)
Lemma dtb_lor_shiftl_add : forall x y k, 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y ->
Z.lor x (Z.shiftl y k) = x + Z.shiftl y k.
Proof.
intros x y k Hk Hx Hy.
assert (HL : Z.land x (Z.shiftl y k) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i k) as [Hl|Hg].
  - rewrite (Z.testbit_neg_r y (i - k)) by lia. apply andb_false_r.
  - destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
    pose proof (Z.log2_lt_pow2 x k ltac:(lia)) as Hlg. lia. }
rewrite <- (Z.lxor_lor _ _ HL). rewrite <- (Z.add_nocarry_lxor _ _ HL). reflexivity.
Qed.
Lemma dtb_other_range : forall e : rt_renv, rt_hdr_ok e -> 0 <= rsb_other e < 2 ^ 32.
Proof.
intros e (_ & _ & _ & H3 & H4 & H5 & H6). unfold rsb_other.
rewrite (Z.lor_comm (Z.shiftl (q_b4 e) 8)), (Z.lor_comm (Z.shiftl (q_b6 e) 8)).
rewrite (dtb_lor_shiftl_add (q_b3 e) (q_b4 e) 8) by lia.
rewrite (dtb_lor_shiftl_add (q_b5 e) (q_b6 e) 8) by lia.
rewrite (dtb_lor_shiftl_add (q_b3 e + Z.shiftl (q_b4 e) 8) (q_b5 e + Z.shiftl (q_b6 e) 8) 16)
  by (rewrite ?Z.shiftl_mul_pow2 by lia; lia).
rewrite !Z.shiftl_mul_pow2 by lia. lia.
Qed.
(* asked[t]'s address R + 0x198 + 4 t is 4-aligned *)
Lemma dtb_al4 : forall R c, R mod 16 = 0 -> c mod 4 = 0 -> (R + c) mod 4 = 0.
Proof.
intros R c HR Hc. apply (proj2 (Z.mod_divide _ 4 ltac:(lia))).
apply (proj1 (Z.mod_divide _ 16 ltac:(lia))) in HR. apply (proj1 (Z.mod_divide _ 4 ltac:(lia))) in Hc.
destruct HR as (a & Ha). destruct Hc as (b & Hb). exists (4 * a + b). lia.
Qed.

(* ======================================= the image's strings and tables ======================================= *)
(* refuse_code's and check_code's tables lie in [0x9bf00, 0x9c000) of .data.rel.ro (inside the RW PT_LOAD
   [0x9b998, 0x9d000)), their shadow bytes in [SHADOW_OFF + 0x137e0, SHADOW_OFF + 0x13800); the strings and
   closed_list lie in RtPgM02BaseB's zone m2b_kz *)
Definition dtb_tz (a : Z) : Prop :=
(0x9bf00 <= a < 0x9c000) \/ (SHADOW_OFF + 0x137e0 <= a < SHADOW_OFF + 0x13800).
Lemma dtb_img_relro : forall a, 0x9b998 <= a < 0x9d000 -> in_img rsegs a.
Proof.
intros a Ha.
assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x9b998) &&
  (0x9d000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
exists sg. split; [exact Hin | lia].
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma dtb_ra_kept : forall (Zn : Z -> Prop) H H' (m m' : word -> option byte) a n,
(forall x, Zn x -> aview rsegs H' m' x = aview rsegs H m x) ->
(forall x, a <= x < a + n -> Zn (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview rsegs H m) SHADOW_OFF a n -> range_addressable (aview rsegs H' m') SHADOW_OFF a n.
Proof.
intros Zn H H' m m' a n HK HZ Hra x Hx.
destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite HK; [exact Hsv | exact (HZ x Hx)].
Qed.
(* closed_list (12 bytes at 0x21520) carried by RtPgM02BaseB's zone *)
Lemma dtb_i32_kept : forall H H' (m m' : word -> option byte) t vs,
(forall x, m2b_kz x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x10800 <= t -> t + 4 * Z.of_nat (length vs) <= 0x2e000 ->
rt_i32tab rsegs H m t vs -> rt_i32tab rsegs H' m' t vs.
Proof.
intros H H' m m' t vs HK Hlo Hhi (Himg & Hal & Hv & Hra).
split; [exact Himg|]. split; [exact Hal|].
split.
- intros i Hi. eapply (val_mem_kept rsegs H H' m m'); [|exact (Hv i Hi)].
  intros k Hk. apply HK. left. cbn in Hk. lia.
- apply (dtb_ra_kept m2b_kz H H' m m' t _ HK); [|exact Hra].
  intros x Hx. right. unfold shadow_of_addr, SHADOW_OFF.
  assert (0x2100 <= x / 8 < 0x5c00) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia.
Qed.
Lemma dtb_u64_kept : forall H H' (m m' : word -> option byte) t vs,
(forall x, dtb_tz x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x9bf00 <= t -> t + 8 * Z.of_nat (length vs) <= 0x9c000 ->
rt_u64tab rsegs H m t vs -> rt_u64tab rsegs H' m' t vs.
Proof.
intros H H' m m' t vs HK Hlo Hhi (Himg & Hal & Hb & Hv & Hra).
split; [exact Himg|]. split; [exact Hal|]. split; [exact Hb|].
split.
- intros i Hi. eapply (val_mem_kept rsegs H H' m m'); [|exact (Hv i Hi)].
  intros k Hk. apply HK. left. cbn in Hk. lia.
- apply (dtb_ra_kept dtb_tz H H' m m' t _ HK); [|exact Hra].
  intros x Hx. right. unfold shadow_of_addr, SHADOW_OFF.
  assert (0x137e0 <= x / 8 < 0x13800) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia.
Qed.
End k.

(* the lengths of the texts check_code compares *)
Lemma dtb_len_code : forall k, (length (rt_code_of_txt k) <= 12)%nat.
Proof.
intros k. unfold rt_code_of_txt, RateCfg.code_of_res. rewrite length_map.
destruct (k =? 1); [vm_compute; lia|]. destruct (k =? 2); [vm_compute; lia|].
destruct (k =? 3); [vm_compute; lia|]. destruct (k =? 4); vm_compute; lia.
Qed.
Lemma dtb_len_refuse : forall r, (length (rt_refuse_txt r) <= 12)%nat.
Proof.
intros r. unfold rt_refuse_txt. rewrite length_map.
destruct (RateCfg.refuse_code_res_cases r) as [E|[E|[E|[E|E]]]]; rewrite E; vm_compute; lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* no byte of the tables' zone is in M02's write set or in the callees' stack (m2b_keep_img for the tables' bytes;
   a shadow byte of the zone can be hz's only if F's own bytes were image addresses) *)
Lemma dtb_tz_ok : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, dtb_tz a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rsb_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a [Ha|Ha]; [exact (m2b_keep_img B cx Hpre Hpod a (dtb_img_relro a ltac:(lia)))|].
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
assert (HF8 : q_F (x_e rsegs cx) = 8 * (q_F (x_e rsegs cx) / 8)).
{ pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
  assert (q_F (x_e rsegs cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; lia); rewrite F32; reflexivity).
  lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
rewrite HR. unfold T_SEG_STK, ASTACK. unfold SHADOW_OFF in Ha.
split; [lia|]. split; [lia|].
unfold rsb_E2, rt_inw. cbn [hi_w2 rate_himg_B]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]];
  try lia;
  (unfold shadow_addr, SHADOW_OFF in Hw;
   assert (HFz : 0x9b998 <= q_F (x_e rsegs cx) < 0x9d000) by lia;
   exact (Fimg (q_F (x_e rsegs cx)) ltac:(lia) (dtb_img_relro _ HFz))).
- lia.
Qed.

(* the premises the turn's callees read, from m2b_site_strs at the segment's start, at a cut's memory *)
Lemma dtb_strs : forall (cx : rsb_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
(forall i, 0 <= i < 4 -> rt_cstr rsegs (w_H W2) mem2 (nth (Z.to_nat i) CC_CS 0) (rt_code_of_txt (i + 1))) /\
rt_cstr rsegs (w_H W2) mem2 CC_LNONE (rt_code_of_txt 0) /\
(forall r, 0 <= r <= 4 -> rt_cstr rsegs (w_H W2) mem2 (rt_refuse RF_CS RF_COV r) (rt_refuse_txt r)) /\
rt_i32tab rsegs (w_H W2) mem2 RSB_CLOSED RateCfg.closed_list /\
rt_u64tab rsegs (w_H W2) mem2 CC_TBL CC_CS /\ rt_u64tab rsegs (w_H W2) mem2 RF_TBL RF_CS.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
pose proof Hcore as (_ & _ & _ & _ & _ & _ & HKc).
assert (HK : forall x, m2b_kz x ->
  aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (m2b_kz_ok B cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE). exact (HKc x Hx64 Hstk HE). }
assert (HT : forall x, dtb_tz x ->
  aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (dtb_tz_ok cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE). exact (HKc x Hx64 Hstk HE). }
pose proof Hpre as Hpre'. unfold rsb_pre in Hpre'.
destruct (m2b_site_strs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre')
as (SC & SN & SR & _ & _ & _ & _ & _ & _ & ST & _ & TC & TR).
split.
{ intros i Hi. pose proof (dtb_len_code (i + 1)) as L.
  assert (Hn : 0x21540 <= nth (Z.to_nat i) CC_CS 0 <= 0x215a0).
  { assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
    destruct C as [->|[->|[->| ->]]]; split; vm_compute; intro Hc; discriminate Hc. }
  apply (m2b_cstr_kept _ _ _ _ _ _ HK); [lia | lia | exact (SC i Hi)]. }
split.
{ pose proof (dtb_len_code 0) as L.
  apply (m2b_cstr_kept _ _ _ _ _ _ HK); [unfold CC_LNONE; lia | unfold CC_LNONE; lia | exact SN]. }
split.
{ intros r Hr. pose proof (dtb_len_refuse r) as L.
  assert (Hn : 0x21600 <= rt_refuse RF_CS RF_COV r <= 0x21680).
  { assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) as C by lia.
    destruct C as [->|[->|[->|[->| ->]]]]; split; vm_compute; intro Hc; discriminate Hc. }
  apply (m2b_cstr_kept _ _ _ _ _ _ HK); [lia | lia | exact (SR r Hr)]. }
split; [apply (dtb_i32_kept _ _ _ _ _ _ HK); [unfold RSB_CLOSED; lia | cbn; unfold RSB_CLOSED; lia | exact ST]|].
split; [apply (dtb_u64_kept _ _ _ _ _ _ HT); [unfold CC_TBL; lia | cbn; unfold CC_TBL; lia | exact TC]|].
apply (dtb_u64_kept _ _ _ _ _ _ HT); [unfold RF_TBL; lia | cbn; unfold RF_TBL; lia | exact TR].
Qed.
End s.

(* every byte outside the callees' stack [R - T_SEG_STK, R) as in (W0, mem0) *)
Definition dtb_kept (cx : rsb_scx rsegs) (W0 : world rsegs) (mem0 : word -> option byte) (W2 : world rsegs)
(mem2 : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a.
(* asked[t]'s cell (x = R + 0x198 + 4 t, its 4-byte value u) at DEC's memory, which dtb_s4 reads again *)
Definition dtb_ax (cx : rsb_scx rsegs) (x u : Z) (W0 : world rsegs) (mem0 : word -> option byte) : Prop :=
(x = q_R (x_e rsegs cx) + 0x198 \/ x = q_R (x_e rsegs cx) + 0x19c) /\ 0 <= u < 2 ^ 32 /\
val_mem rsegs (mrestrict (w_H W0) mem0) x 4 u.
(* what every stage reads from DEC's registers and memory: s1 = R, s2 = &closed_list, s4 = the shadow offset, and
   the mask cell R + 0x148 *)
Definition dtb_fix (cx : rsb_scx rsegs) (regs0 : bvmap 5 word) (W0 : world rsegs) (mem0 : word -> option byte) : Prop :=
getr regs0 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)) /\ getr regs0 (Z_to_bv 5 18) = w64 RSB_CLOSED /\
getr regs0 (Z_to_bv 5 20) = w64 SHADOW_OFF /\ 0 <= q_mask (x_e rsegs cx) < 256 /\
val_mem rsegs (mrestrict (w_H W0) mem0) (q_R (x_e rsegs cx) + 0x148) 8 (q_mask (x_e rsegs cx)).

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a value at or above R at DEC's memory is the same at a later memory the turn reached *)
Lemma dtb_val_kept : forall (cx : rsb_scx rsegs) W0 mem0 W2 mem2 a (n : nat) v,
0 <= a -> q_R (x_e rsegs cx) <= a -> a + Z.of_nat n <= 2 ^ 64 -> dtb_kept cx W0 mem0 W2 mem2 ->
val_mem rsegs (mrestrict (w_H W0) mem0) a n v -> val_mem rsegs (mrestrict (w_H W2) mem2) a n v.
Proof.
intros cx W0 mem0 W2 mem2 a n v Ha0 Ha Hn Hk Hv.
apply (val_mem_kept rsegs (w_H W0) (w_H W2) mem0 mem2); [|exact Hv].
intros k Hk'. cbn in Hk'. apply Hk; lia.
Qed.
End v.

(* ======================================= the entry states of the stages that read memory ======================================= *)
(* DEC: asked[t] at R + o (o = 0x198 + 4 t) in the real frame at s1 (atom 9), as the extra atom 32 = its 4-byte
   value; s10 is entered as the literal t *)
Definition dtb_rask (lo hi : Z) : YP09.region := YP09.mkRegion (Some 9%nat) lo hi 0 0 [YP09.mkChunk lo (CVal 4 (SOff 32 0))].
Definition dtb_facts0 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
(* 0x82e64: closed_list at s2 (atom 18), and the mask cell R + 0x148, whose 8 bytes are s6's value *)
Definition dtb_rcl : YP09.region := YP09.mkRegion (Some 18%nat) 0 12 0 0
  [YP09.mkChunk 0 (CVal 4 (SLit 44100)); YP09.mkChunk 4 (CVal 4 (SLit 48000)); YP09.mkChunk 8 (CVal 4 (SLit 96000))].
Definition dtb_rmask : YP09.region := YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0 [YP09.mkChunk 0x148 (CVal 8 (SOff 22 0))].
Definition dtb_facts1 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF RSB_CLOSED RSB_CLOSED 0);
            (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
(* 0x82f44: asked[t] at s8 (atom 24), as the extra atom 32 *)
Definition dtb_rask4 : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition dtb_facts4 : facts :=
  mkFacts [ (24%nat, mkAF (2 ^ 46) (2 ^ 47 + 0x1a0) 2); (32%nat, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
(* 0x82f5c: the mask cell R + 0x148 at s1 (atom 9), as the extra atom 32 *)
Definition dtb_rmask6 : YP09.region := YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0 [YP09.mkChunk 0x148 (CVal 8 (SOff 32 0))].
Definition dtb_facts6 : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].

Lemma dtb_ew : forall regs2 extra (n : nat) r v, (n < 32)%nat -> Z.of_nat n = r ->
getr regs2 (Z_to_bv 5 r) = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs2 extra) n) = v.
Proof.
intros regs2 extra n r v Hn Hr H Hv. rewrite (m2b_ereg regs2 extra n Hn), Hr, H. apply dtb_w64_unsigned. exact Hv.
Qed.
Lemma dtb_ew' : forall regs2 extra (n : nat) r v, (n < 32)%nat -> Z.of_nat n = r ->
getr regs2 (Z_to_bv 5 r) = w64 v -> ew (Ereg regs2 extra) n = Z_to_bv 64 v.
Proof. intros regs2 extra n r v Hn Hr H. rewrite (m2b_ereg regs2 extra n Hn), Hr, H. reflexivity. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma dtb_ent0 : forall (t o : Z) (W : world rsegs) regs2 mem2 R u,
getr regs2 (Z_to_bv 5 9) = w64 R -> getr regs2 (Z_to_bv 5 26) = w64 t ->
0 <= u < 2 ^ 32 -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + o) 4 u -> (o = 0x198 \/ o = 0x19c) ->
st_ok rsegs (Ereg regs2 [w64 u]) (mkSS RSB_DEC (ck_sr [((26%bv : bv 5), SLit t)]) [dtb_rask o (o + 4)] None dtb_facts0)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 RSB_DEC) mem2 (seg_rom rsegs))).
Proof.
intros t o W regs2 mem2 R u H9 H26 Hu HR HRal Hva Ho.
assert (E9 : bv_unsigned (ew (Ereg regs2 [w64 u]) 9) = R) by (apply (dtb_ew regs2 _ 9 9 R); [lia | reflexivity | exact H9 | lia]).
assert (E32 : ew (Ereg regs2 [w64 u]) 32 = Z_to_bv 64 u) by exact (ew_Ereg_extra regs2 [w64 u] 0).
apply (m2b_entry RSB_DEC [((26%bv : bv 5), SLit t)] [dtb_rask o (o + 4)] dtb_facts0 W regs2 [w64 u] mem2).
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
  + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
  + rewrite ck_lit. symmetry. exact H26.
- destruct Ho as [-> | ->]; vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (rtmb_ro_region rsegs _ _ mem2 9 R o (o + 4)); [exact E9 | destruct Ho; lia | destruct Ho; lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R o 4 (SOff 32 0) u); [exact (dtb_den_atom _ 32 u E32 ltac:(lia)) | cbn; lia | cbn; lia |].
  exact Hva.
- unfold dtb_rask. cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. unfold dtb_facts0. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E9, E32, unsigned_lit_small by lia.
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
Qed.

Lemma dtb_ent1 : forall ov (W : world rsegs) regs2 mem2 R mask,
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 []) (snd p) = getr regs2 (fst p)) ov ->
getr regs2 (Z_to_bv 5 9) = w64 R -> getr regs2 (Z_to_bv 5 18) = w64 RSB_CLOSED ->
getr regs2 (Z_to_bv 5 20) = w64 SHADOW_OFF -> getr regs2 (Z_to_bv 5 22) = w64 mask ->
0 <= mask < 2 ^ 64 -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x148) 8 mask ->
rt_i32tab rsegs (w_H W) mem2 RSB_CLOSED RateCfg.closed_list ->
st_ok rsegs (Ereg regs2 []) (mkSS DTB_R_CFG (ck_sr ov) [dtb_rcl; dtb_rmask] None dtb_facts1)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 DTB_R_CFG) mem2 (seg_rom rsegs))).
Proof.
intros ov W regs2 mem2 R mask Hov H9 H18 H20 H22 Hm HR HRal Hvm (_ & _ & Hv & _).
assert (E9 : bv_unsigned (ew (Ereg regs2 []) 9) = R) by (apply (dtb_ew regs2 _ 9 9 R); [lia | reflexivity | exact H9 | lia]).
assert (E18 : bv_unsigned (ew (Ereg regs2 []) 18) = RSB_CLOSED)
by (apply (dtb_ew regs2 _ 18 18 RSB_CLOSED); [lia | reflexivity | exact H18 | unfold RSB_CLOSED; lia]).
assert (E20 : bv_unsigned (ew (Ereg regs2 []) 20) = SHADOW_OFF)
by (apply (dtb_ew regs2 _ 20 20 SHADOW_OFF); [lia | reflexivity | exact H20 | unfold SHADOW_OFF; lia]).
assert (E22 : ew (Ereg regs2 []) 22 = Z_to_bv 64 mask) by (apply (dtb_ew' regs2 _ 22 22 mask); [lia | reflexivity | exact H22]).
apply (m2b_entry DTB_R_CFG ov [dtb_rcl; dtb_rmask] dtb_facts1 W regs2 [] mem2 Hov).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (rtmb_ro_region rsegs _ _ mem2 18 RSB_CLOSED 0 12); [exact E18 | unfold RSB_CLOSED; lia | unfold RSB_CLOSED; lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val rsegs _ _ RSB_CLOSED 0 4 (SLit 44100) 44100); [reflexivity | cbn; lia | cbn; lia |].
      exact (Hv 0 ltac:(cbn; lia)).
    * apply (chunk_ok_val rsegs _ _ RSB_CLOSED 4 4 (SLit 48000) 48000); [reflexivity | cbn; lia | cbn; lia |].
      exact (Hv 1 ltac:(cbn; lia)).
    * apply (chunk_ok_val rsegs _ _ RSB_CLOSED 8 4 (SLit 96000) 96000); [reflexivity | cbn; lia | cbn; lia |].
      exact (Hv 2 ltac:(cbn; lia)).
  + apply (rtmb_ro_region rsegs _ _ mem2 9 R 0x148 0x150); [exact E9 | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ R 0x148 8 (SOff 22 0) mask); [exact (dtb_den_atom _ 22 mask E22 Hm) | cbn; lia | cbn; lia |].
    exact Hvm.
- unfold dtb_rcl, dtb_rmask. cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E18, E9. left. unfold RSB_CLOSED. lia.
- split; [|split; [exact I | exact I]]. unfold dtb_facts1. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E9, E18, E20.
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF, RSB_CLOSED. repeat split; lia.
Qed.

Lemma dtb_ent4 : forall (W : world rsegs) regs2 mem2 x u,
getr regs2 (Z_to_bv 5 24) = w64 x -> 0 <= u < 2 ^ 32 -> 2 ^ 46 <= x <= 2 ^ 47 + 0x1a0 -> x mod 4 = 0 ->
val_mem rsegs (mrestrict (w_H W) mem2) x 4 u ->
st_ok rsegs (Ereg regs2 [w64 u]) (mkSS DTB_R_CODE (ck_sr []) [dtb_rask4] None dtb_facts4)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 DTB_R_CODE) mem2 (seg_rom rsegs))).
Proof.
intros W regs2 mem2 x u H24 Hu Hx Hx4 Hva.
assert (E24 : bv_unsigned (ew (Ereg regs2 [w64 u]) 24) = x) by (apply (dtb_ew regs2 _ 24 24 x); [lia | reflexivity | exact H24 | lia]).
assert (E32 : ew (Ereg regs2 [w64 u]) 32 = Z_to_bv 64 u) by exact (ew_Ereg_extra regs2 [w64 u] 0).
apply (m2b_entry DTB_R_CODE [] [dtb_rask4] dtb_facts4 W regs2 [w64 u] mem2 (Forall_nil _)).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (rtmb_ro_region rsegs _ _ mem2 24 x 0 4); [exact E24 | lia | lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ x 0 4 (SOff 32 0) u); [exact (dtb_den_atom _ 32 u E32 ltac:(lia)) | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Hva.
- unfold dtb_rask4. cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. unfold dtb_facts4. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E24, E32, unsigned_lit_small by lia.
  change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
Qed.

Lemma dtb_ent6 : forall (W : world rsegs) regs2 mem2 R mask,
getr regs2 (Z_to_bv 5 9) = w64 R -> 0 <= mask < 2 ^ 64 -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x148) 8 mask ->
st_ok rsegs (Ereg regs2 [w64 mask]) (mkSS DTB_R_CLO (ck_sr []) [dtb_rmask6] None dtb_facts6)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 DTB_R_CLO) mem2 (seg_rom rsegs))).
Proof.
intros W regs2 mem2 R mask H9 Hm HR HRal Hvm.
assert (E9 : bv_unsigned (ew (Ereg regs2 [w64 mask]) 9) = R) by (apply (dtb_ew regs2 _ 9 9 R); [lia | reflexivity | exact H9 | lia]).
assert (E32 : ew (Ereg regs2 [w64 mask]) 32 = Z_to_bv 64 mask) by exact (ew_Ereg_extra regs2 [w64 mask] 0).
apply (m2b_entry DTB_R_CLO [] [dtb_rmask6] dtb_facts6 W regs2 [w64 mask] mem2 (Forall_nil _)).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (rtmb_ro_region rsegs _ _ mem2 9 R 0x148 0x150); [exact E9 | lia | lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R 0x148 8 (SOff 32 0) mask); [exact (dtb_den_atom _ 32 mask E32 Hm) | cbn; lia | cbn; lia |].
  exact Hvm.
- unfold dtb_rmask6. cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]]. unfold dtb_facts6. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E9.
  change (2 ^ 4) with 16. repeat split; lia.
Qed.
End e.

(* ======================================= the run tactics over the turn's table ======================================= *)
Ltac dtb_run :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok dtb_tbl_ok HS HJ SHOK M2B_Bspan end.
Ltac dtb_run_to stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok dtb_tbl_ok HS HJ SHOK M2B_Bspan stop end.
Ltac dtb_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok dtb_tbl_ok HS SH M2B_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

(* the enter step of a run that starts at a cut with no memory access before its next call: the registers as atoms
   with the overrides ov, no region, no fact [RPgM02Tail.v tl_enter] *)
Ltac dtb_enter ov :=
lazymatch goal with |- SRr _ ?W (cfg_at _ ?pc ?regs ?mem ?md) _ =>
let HS := fresh "HS" in
pose proof (m2b_entry pc ov [] (mkFacts [] [] []) W regs [] mem) as HS;
specialize (HS ltac:(repeat (apply Forall_cons; [cbn [fst snd]; split;
  [ let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | rewrite ck_lit; symmetry; assumption ] | ]); apply Forall_nil) eq_refl (Forall_nil _) I ltac:(repeat split));
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs []) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W) mem)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem a)
by (intros; reflexivity);
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.

(* a register below 32 in an environment that agrees with the entry's below 32 *)
Lemma dtb_U_ag : forall E' regs2 extra (n : nat) c v, env_agree 32 (Ereg regs2 extra) E' -> (n < 32)%nat ->
getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E' (SOff n c) = v + c.
Proof.
intros E' regs2 extra n c v [HA _] Hn H Hv Hc. apply U_atom_off; [|exact Hv | exact Hc].
rewrite (HA n Hn), (m2b_ereg regs2 extra n Hn), H. reflexivity.
Qed.
Lemma dtb_ew_ag : forall E' regs2 extra (n : nat) v, env_agree 32 (Ereg regs2 extra) E' -> (n < 32)%nat ->
getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> ew E' n = Z_to_bv 64 v.
Proof. intros E' regs2 extra n v [HA _] Hn H. rewrite (HA n Hn), (m2b_ereg regs2 extra n Hn), H. reflexivity. Qed.
Lemma dtb_ew_ag2 : forall E' regs2 extra (n : nat), env_agree 32 (Ereg regs2 extra) E' -> (n < 32)%nat ->
ew E' n = getr regs2 (Z_to_bv 5 (Z.of_nat n)).
Proof. intros E' regs2 extra n [HA _] Hn. rewrite (HA n Hn). exact (m2b_ereg regs2 extra n Hn). Qed.
Lemma dtb_dec_w : forall x role v mask, x = w64 (RateCfg.decide_res role v mask) -> 0 <= bv_unsigned x <= 4.
Proof.
intros x role v mask ->. pose proof (dtb_dec_range role v mask). rewrite dtb_w64_unsigned by lia. exact H.
Qed.
(* the found arm's value, in the engine's 64-bit form *)
Lemma dtb_expect_bv : forall (E : env) mask b, 0 <= mask < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
alu64 ALU_SLL (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 mask) (Z_to_bv 64 b)) (Z_to_bv 64 1)) (Z_to_bv 64 1) =
w64 (if Z.land mask b =? 0 then 2 else 0).
Proof.
intros E mask b Hm Hb.
transitivity (sv_denot E (SAlu ALU_SLL (SAlu ALU_SLTU (SAlu ALU_AND (SLit mask) (SLit b)) (SLit 1)) (SLit 1)));
[reflexivity|].
rewrite denot_lit_U, lf_U_sll1, lf_U_sltu1, U_and_lit, U_lit by lia.
destruct (Z.land mask b =? 0); reflexivity.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = 0x9c170.
Hypothesis HBcell : as_shadow_cell B = 0xa4f38.
Hypothesis ASTRCMP : astrcmp_realizes rsegs B A_STRCMP.

(* what reaching the latch means: rsb_core, sp = R, the registers of dtb_L as at DEC, s6 = the mask, every byte
   outside the callees' stack as at DEC *)
Definition dtb_K (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word) (W0 : world rsegs)
(mem0 : word -> option byte) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> spZ regs3 = q_R (x_e rsegs cx) ->
cs_eq dtb_L regs0 regs3 -> getr regs3 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) ->
dtb_kept cx W0 mem0 W3 mem3 ->
SRr rsegs W3 (cfg_at rsegs DTB_LATCH regs3 mem3 md3) POST.

(* the common start of a stage: the stack facts, the journal, the entry state (overrides ov), the run to the
   callee's entry, the kept memory *)
Ltac dt_stage0 ov :=
lazymatch goal with Hpre : rsb_pre _ _ ?cx, Hcore : rsb_core _ _ _ ?cx _ _ _ _ _ _ _ |- _ =>
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp);
pose proof rtmb_B_wx as Hwx; pose proof ck_segs_low as Hsegs; pose proof (AR_laws_ok rsegs B) as LAWS;
pose proof (proj1 Hcore) as HJ end;
dtb_enter ov;
dtb_run; [m2b_awr|];
ck_keep kwr_stk.
(* at the callee's entry pcC: the registers of L and sp / gp / tp as in regs2, the goal in mkCfg form *)
Ltac dt_at pcC regs2 L :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
let CL := fresh "CL" in let C234 := fresh "C234" in
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ L HS HAE ltac:(vm_compute; reflexivity)) as CL;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
replace (ss_pc ss) with pcC by (vm_compute; reflexivity)
end.
(* rsb_core and sp at the callee's entry [RPgM02Tail.v tl_coreT] *)
Ltac dt_coreT :=
lazymatch goal with
| Hcore : rsb_core _ _ _ ?cx ?E2 ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _,
  C234 : cs_eq _ ?regs2 (ms_regs ?ms), KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?ms) a = _,
  Hsp : spZ ?regs2 = _ |- _ =>
  let HcoreT := fresh "HcoreT" in let HspT := fresh "HspT" in
  assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx)) by (rewrite (dtb_sp_of_cs _ _ C234); exact Hsp);
  assert (HcoreT : rsb_core rsegs B MT cx E2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
        (dtb_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2b_io | apply (mo_le_refl MT MTL) |];
      intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
Ltac dt_pre T :=
lazymatch goal with HcoreT : rsb_core _ _ _ ?cx _ _ _ _ _ _ _, Hpre : rsb_pre _ _ ?cx, R1' : getr _ 1 = w64 _,
  HspT : spZ _ = _ |- _ =>
apply (m2b_pre_call B MT cx _ _ _ _ _ _ _ T Hpre HcoreT);
[ rewrite R1'; vm_compute; reflexivity
| unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
| exact HspT | unfold T_cmp_STK, T_check_STK, T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia ]
end.
(* after the callee's post: the returned state, at the stage's own float state *)
Ltac dt_post T Hpost :=
lazymatch goal with HcoreT : rsb_core _ _ _ ?cx _ ?ly2 ?S2 ?W2 (ms_regs ?ms) (ms_mem ?ms) _, Hpre : rsb_pre _ _ ?cx,
  HspT : spZ _ = _, R1' : getr _ 1 = w64 _ |- _ =>
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _
  (fun _ _ => True) _ _ _ Hpre HcoreT HspT ltac:(unfold T_cmp_STK, T_check_STK, T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & HR3);
subst fx3; subst; rewrite R1'
end.
(* the next stage's three carried facts (Hp the callee's aregs_preserved, CL the run's kept registers) *)
Ltac dt_sp3 Hp HspT := rewrite (m2b_sp_pres _ _ Hp); exact HspT.
Ltac dt_cs3 L Lsub CL Hp := exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ L (dtb_cs_sub _ _ _ _ CL Lsub))
  (cs_eq_of_pres dtb_L _ _ dtb_L_cs Hp)).
Ltac dt_kept3 Hk3 KE Hk :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
intros a Ha Hs;
rewrite (Hk3 a Ha ltac:(unfold T_cmp_STK, T_check_STK, T_leaf_STK, T_SEG_STK, ASTACK, ESTACK in *; lia) (fun x => x));
rewrite (KE a Ha (fun x => x)); exact (Hk a Ha Hs).
(* a register of a kept list, from the state before the call through the call *)
Ltac dt_keep r Hp CL := etransitivity; [exact (Hp r ltac:(unfold acallee_saved; lia))|];
  etransitivity; [exact (CL (Z_to_bv 5 r) ltac:(dtb_in))|].

(* ---- S7: 0x82f6c mv a4,a0; mv a0,s11; mv a1,s7; mv a2,s8; mv a3,s6; jal check_list -> the latch ---- *)
Lemma dtb_s7 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 23) = w64 (RateCfg.rate_bit (bv_unsigned (getr regs2 (Z_to_bv 5 27)))) ->
getr regs2 (Z_to_bv 5 24) = w64 (RateCfg.rate_closed (bv_unsigned (getr regs2 (Z_to_bv 5 27)))) ->
getr regs2 (Z_to_bv 5 10) = w64 (RateCfg.rate_best (bv_unsigned (getr regs2 (Z_to_bv 5 22)))) ->
getr regs2 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_BEST regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H23 H24 H10 H22 HL Hkept HK.
dt_stage0 (@nil (bv 5 * sv)).
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R12" in rreg HS (12%bv : bv 5) R.
let R := fresh "R13" in rreg HS (13%bv : bv 5) R.
let R := fresh "R14" in rreg HS (14%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
dt_at A_CHECK_LIST regs2 dtb_Lf.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f84) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E22 : ew E 22 = getr regs2 (Z_to_bv 5 22)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E23 : ew E 23 = getr regs2 (Z_to_bv 5 23)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E27 : ew E 27 = getr regs2 (Z_to_bv 5 27)) by (subst E; apply ew_Ereg_nat; reflexivity).
dt_coreT.
destruct (dtb_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (_ & _ & _ & TCL & _).
eapply SRr_bind.
{ apply (rt_check_list_B B MT MTL (AR_laws_ok rsegs B) HBgot HBcell (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - dt_pre T_check_STK.
  - rewrite R11, R10, E23, E27. exact H23.
  - rewrite R12, R10, E24, E27. exact H24.
  - rewrite R14, R13, E10, E22. exact H10.
  - exact TCL. }
intros W3 c3 _ Hpost.
dt_post T_check_STK Hpost.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3);
  [dt_sp3 Hpres3 HspT | dt_cs3 HL dtb_Lf_L CL Hpres3 | dt_keep 22 Hpres3 CL; exact H22 | dt_kept3 Hkept3 KE Hkept].
Qed.

(* ---- S6: 0x82f5c mv s8,a0; ld s6,0x148(s1); mv a0,s6; jal best_drivable -> 0x82f6c ---- *)
Lemma dtb_s6 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 23) = w64 (RateCfg.rate_bit (bv_unsigned (getr regs2 (Z_to_bv 5 27)))) ->
getr regs2 (Z_to_bv 5 10) = w64 (RateCfg.rate_closed (bv_unsigned (getr regs2 (Z_to_bv 5 27)))) ->
dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_CLO regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H23 H10 HF HL Hkept HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof rtmb_B_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
pose proof HF as (H9 & _ & _ & Hm & Hvm).
assert (H9r : getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)))
by (etransitivity; [exact (HL (Z_to_bv 5 9) ltac:(dtb_in)) | exact H9]).
assert (Hvmr : val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x148) 8 (q_mask (x_e rsegs cx)))
by (apply (dtb_val_kept cx W0 mem0 W2 mem2); [lia | lia | lia | exact Hkept | exact Hvm]).
pose proof (dtb_ent6 W2 regs2 mem2 (q_R (x_e rsegs cx)) (q_mask (x_e rsegs cx)) H9r ltac:(lia) H46 Hal Hvmr) as HS.
remember (Ereg regs2 [w64 (q_mask (x_e rsegs cx))]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [w64 (q_mask (x_e rsegs cx))]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
unfold cfg_at. change (w64 DTB_R_CLO) with (Z_to_bv 64 DTB_R_CLO).
dtb_run; [m2b_awr | ].
ck_keep kwr_stk.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
let R := fresh "R24" in rreg HS (24%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
dt_at A_BEST regs2 dtb_L6.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f6c) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (q_mask (x_e rsegs cx)))
by (subst E; exact (ew_Ereg_extra regs2 [w64 (q_mask (x_e rsegs cx))] 0)).
assert (W22 : getr (ms_regs ms) (22%bv : bv 5) = w64 (q_mask (x_e rsegs cx)))
by (etransitivity; [exact R22|]; first [rewrite E32; reflexivity | exact (dtb_den_atom _ 32 _ E32 ltac:(lia))]).
assert (W10 : getr (ms_regs ms) (10%bv : bv 5) = w64 (q_mask (x_e rsegs cx)))
by (etransitivity; [exact R10|]; first [rewrite E32; reflexivity | exact (dtb_den_atom _ 32 _ E32 ltac:(lia))]).
dt_coreT.
eapply SRr_bind.
{ apply (rt_best_drivable_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  dt_pre T_leaf_STK. }
intros W3 c3 _ Hpost.
dt_post T_leaf_STK Hpost.
assert (K27 : getr regs3 (Z_to_bv 5 27) = getr regs2 (Z_to_bv 5 27)) by (dt_keep 27 Hpres3 CL; reflexivity).
assert (K22 : getr regs3 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)))
by (etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|]; exact W22).
apply (dtb_s7 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3).
- dt_sp3 Hpres3 HspT.
- rewrite K27. dt_keep 23 Hpres3 CL. exact H23.
- rewrite K27. etransitivity; [exact (Hpres3 24 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact R24|]. rewrite E10. exact H10.
- etransitivity; [exact HR3|]. rewrite K22, W10. reflexivity.
- exact K22.
- dt_cs3 HL dtb_L6_L CL Hpres3.
- dt_kept3 Hkept3 KE Hkept.
- exact HK.
Qed.

(* ---- S5: 0x82f50 mv s7,a0; mv a0,s11; jal is_closed -> 0x82f5c ---- *)
Lemma dtb_s5 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 (RateCfg.rate_bit (bv_unsigned (getr regs2 (Z_to_bv 5 27)))) ->
dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_BIT regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 HF HL Hkept HK.
dt_stage0 (@nil (bv 5 * sv)).
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
dt_at A_IS_CLOSED regs2 dtb_L5.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f5c) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E27 : ew E 27 = getr regs2 (Z_to_bv 5 27)) by (subst E; apply ew_Ereg_nat; reflexivity).
dt_coreT.
eapply SRr_bind.
{ apply (rt_is_closed_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  dt_pre T_leaf_STK. }
intros W3 c3 _ Hpost.
dt_post T_leaf_STK Hpost.
assert (K27 : getr regs3 (Z_to_bv 5 27) = getr regs2 (Z_to_bv 5 27)) by (dt_keep 27 Hpres3 CL; reflexivity).
apply (dtb_s6 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3).
- dt_sp3 Hpres3 HspT.
- rewrite K27. etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact R23|]. rewrite E10. exact H10.
- rewrite K27. etransitivity; [exact HR3|]. rewrite R10, E27. reflexivity.
- exact HF.
- dt_cs3 HL dtb_L5_L CL Hpres3.
- dt_kept3 Hkept3 KE Hkept.
- exact HK.
Qed.

(* ---- S4: 0x82f44 lw s11,0(s8) (asked[t] again, no check); mv a0,s11; jal bit -> 0x82f50 ---- *)
Lemma dtb_s4 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 x u,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 24) = w64 x -> dtb_ax cx x u W0 mem0 -> dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_CODE regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 x u Hpre Hpod Hcore Hsp H24 Hax HF HL Hkept HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof rtmb_B_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
pose proof Hax as (Hx & Hu & Hva).
assert (Hx4 : x mod 4 = 0)
by (destruct Hx as [-> | ->]; apply dtb_al4; first [exact Hal | reflexivity]).
assert (Hvar : val_mem rsegs (mrestrict (w_H W2) mem2) x 4 u)
by (apply (dtb_val_kept cx W0 mem0 W2 mem2); [destruct Hx; lia | destruct Hx; lia | destruct Hx; lia | exact Hkept | exact Hva]).
pose proof (dtb_ent4 W2 regs2 mem2 x u H24 Hu ltac:(destruct Hx; lia) Hx4 Hvar) as HS.
remember (Ereg regs2 [w64 u]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 [w64 u]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity).
unfold cfg_at. change (w64 DTB_R_CODE) with (Z_to_bv 64 DTB_R_CODE).
dtb_run; [m2b_awr | ].
ck_keep kwr_stk.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
lazymatch goal with HS : st_ok _ ?Ec ?ss (restrict ?H ?msc) |- _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
  let e27 := eval vm_compute in (sr_get (ss_regs ss) (27%bv : bv 5)) in
  assert (R10 : getr (ms_regs msc) (10%bv : bv 5) = sv_denot Ec e10) by exact (st_ok_restrict_reg rsegs H Ec ss msc _ HS);
  assert (R27 : getr (ms_regs msc) (27%bv : bv 5) = sv_denot Ec e27) by exact (st_ok_restrict_reg rsegs H Ec ss msc _ HS);
  assert (E32 : ew Ec 32 = Z_to_bv 64 u) by (rewrite HE; cbn [ew ewset havoc Nat.eqb]; exact (ew_Ereg_extra regs2 [w64 u] 0))
end.
assert (U10 : bv_unsigned (getr (ms_regs ms) (10%bv : bv 5)) = dtb_v u).
{ rewrite R10. lazymatch goal with |- bv_unsigned (sv_denot ?Ec ?v) = _ => change (U Ec v = dtb_v u) end.
  rewrite lf_U_add0. exact (dtb_U_sext _ 32 u E32 Hu). }
assert (W27 : getr (ms_regs ms) (27%bv : bv 5) = w64 (dtb_v u)).
{ etransitivity; [exact R27|]. rewrite denot_lit_U, (dtb_U_sext _ 32 u E32 Hu). reflexivity. }
dt_at A_BIT regs2 dtb_L4.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f50) by exact R1.
dt_coreT.
eapply SRr_bind.
{ apply (rt_bit_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  dt_pre T_leaf_STK. }
intros W3 c3 _ Hpost.
dt_post T_leaf_STK Hpost.
assert (K27 : getr regs3 (Z_to_bv 5 27) = w64 (dtb_v u))
by (etransitivity; [exact (Hpres3 27 ltac:(unfold acallee_saved; lia))|]; exact W27).
apply (dtb_s5 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3).
- dt_sp3 Hpres3 HspT.
- rewrite K27, (dtb_w64_unsigned (dtb_v u) (dtb_v_range u)). etransitivity; [exact HR3|]. rewrite U10. reflexivity.
- exact HF.
- dt_cs3 HL dtb_L4_L CL Hpres3.
- dt_kept3 Hkept3 KE Hkept.
- exact HK.
Qed.

(* ---- S3: 0x82f3c mv a1,s6; jal check_code -> 0x82f44 ---- *)
Lemma dtb_s3 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 x u,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
0 <= bv_unsigned (getr regs2 (Z_to_bv 5 22)) <= 4 ->
getr regs2 (Z_to_bv 5 10) = w64 (rt_refuse RF_CS RF_COV (bv_unsigned (getr regs2 (Z_to_bv 5 22)))) ->
getr regs2 (Z_to_bv 5 24) = w64 x -> dtb_ax cx x u W0 mem0 -> dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_REF regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 x u Hpre Hpod Hcore Hsp H22 H10 H24 Hax HF HL Hkept HK.
dt_stage0 (@nil (bv 5 * sv)).
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
dt_at A_CHECK_CODE regs2 dtb_Lf.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f44) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E22 : ew E 22 = getr regs2 (Z_to_bv 5 22)) by (subst E; apply ew_Ereg_nat; reflexivity).
dt_coreT.
destruct (dtb_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (SC & SN & SR & _ & TC & _).
eapply SRr_bind.
{ apply (rt_check_code_B B MT MTL (AR_laws_ok rsegs B) HBgot HBcell ASTRCMP (x_STK rsegs cx) (x_sp0 rsegs cx)
    (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx)
    (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)
    (rt_refuse RF_CS RF_COV (bv_unsigned (getr regs2 (Z_to_bv 5 22))))).
  - dt_pre T_cmp_STK.
  - rewrite R10, E10. exact H10.
  - rewrite R11, E22. lia.
  - rewrite R11, E22. exact (SR _ H22).
  - reflexivity.
  - exact TC.
  - exact SC.
  - exact SN. }
intros W3 c3 _ Hpost.
dt_post T_cmp_STK Hpost.
apply (dtb_s4 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 x u Hpre Hpod Hcore3);
  [dt_sp3 Hpres3 HspT | dt_keep 24 Hpres3 CL; exact H24 | exact Hax | exact HF | dt_cs3 HL dtb_Lf_L CL Hpres3
  | dt_kept3 Hkept3 KE Hkept | exact HK].
Qed.

(* ---- S2: 0x82f34 mv a0,s6; jal refuse_code -> 0x82f3c ---- *)
Lemma dtb_s2 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 x u,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
0 <= bv_unsigned (getr regs2 (Z_to_bv 5 22)) <= 4 ->
getr regs2 (Z_to_bv 5 24) = w64 x -> dtb_ax cx x u W0 mem0 -> dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_CDEC regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 x u Hpre Hpod Hcore Hsp H22 H24 Hax HF HL Hkept HK.
dt_stage0 (@nil (bv 5 * sv)).
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
dt_at A_REFUSE regs2 dtb_Lf.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f3c) by exact R1.
assert (E22 : ew E 22 = getr regs2 (Z_to_bv 5 22)) by (subst E; apply ew_Ereg_nat; reflexivity).
dt_coreT.
destruct (dtb_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (_ & _ & _ & _ & _ & TR).
eapply SRr_bind.
{ apply (rt_refuse_code_B B MT MTL (AR_laws_ok rsegs B) HBgot HBcell (x_STK rsegs cx) (x_sp0 rsegs cx)
    (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx)
    (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms)).
  - dt_pre T_check_STK.
  - reflexivity.
  - unfold RF_COV. lia.
  - exact TR. }
intros W3 c3 _ Hpost.
dt_post T_check_STK Hpost.
assert (K22 : getr regs3 (Z_to_bv 5 22) = getr regs2 (Z_to_bv 5 22)) by (dt_keep 22 Hpres3 CL; reflexivity).
apply (dtb_s3 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 x u Hpre Hpod Hcore3).
- dt_sp3 Hpres3 HspT.
- rewrite K22. exact H22.
- rewrite K22. etransitivity; [exact HR3|]. rewrite R10, E22. reflexivity.
- dt_keep 24 Hpres3 CL. exact H24.
- exact Hax.
- exact HF.
- dt_cs3 HL dtb_Lf_L CL Hpres3.
- dt_kept3 Hkept3 KE Hkept.
- exact HK.
Qed.

(* ---- check_decide's call, entered from the scan stage with a0 = a1 and s6 = cfg_decide's answer -> 0x82f34 ---- *)
Lemma dtb_cdec : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regsT memT mdT x u,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regsT memT mdT -> spZ regsT = q_R (x_e rsegs cx) ->
getr regsT 1 = w64 0x82f34 -> getr regsT (Z_to_bv 5 10) = getr regsT (Z_to_bv 5 11) ->
0 <= bv_unsigned (getr regsT (Z_to_bv 5 22)) <= 4 ->
getr regsT (Z_to_bv 5 24) = w64 x -> dtb_ax cx x u W0 mem0 -> dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regsT -> dtb_kept cx W0 mem0 W2 memT -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs A_CHECK_DECIDE regsT memT mdT) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regsT memT mdT x u Hpre Hpod HcoreT HspT R1' Heq H22 H24 Hax HF HL Hkept HK.
eapply SRr_bind.
{ apply (rt_check_decide_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
    (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2
    memT mdT (x_k rsegs cx) regsT).
  - apply (m2b_pre_call B MT cx _ _ _ _ _ _ _ T_check_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_check_STK, T_SEG_STK, ASTACK; lia ].
  - exact Heq. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 regsT memT _ _
  (fun _ _ => True) _ _ _ Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia)
  ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3; subst. rewrite R1'.
apply (dtb_s2 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 x u Hpre Hpod Hcore3).
- rewrite (m2b_sp_pres _ _ Hpres3). exact HspT.
- rewrite (Hpres3 22 ltac:(unfold acallee_saved; lia)). exact H22.
- rewrite (Hpres3 24 ltac:(unfold acallee_saved; lia)). exact H24.
- exact Hax.
- exact HF.
- exact (cs_eq_trans _ _ _ _ HL (cs_eq_of_pres dtb_L _ _ dtb_L_cs Hpres3)).
- intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun f => f)).
  exact (Hkept a Ha Hs).
- exact HK.
Qed.

(* the scan stage's helpers: the agreement of the current environment, the token obligation of closed_list[c/4] *)
Ltac dtb_hae HAE HAEc :=
lazymatch goal with HS : st_ok _ ?Ec _ _ |- _ => assert (HAEc : env_agree 32 _ Ec) by (env_agree_chain HAE) end.
Ltac dtb_obl Hra HAEc :=
lazymatch goal with |- range_addressable (rd_of _ (mrestrict ?H ?m)) (U ?E M2B_Bx) (U ?E (SOff 18 ?c)) 4 =>
apply (obl_of_range rsegs H m E M2B_Bx (U E (SOff 18 c)) 4 RSB_CLOSED 12 Hra);
[ unfold M2B_Bx; rewrite (dtb_U_ag E _ _ 20 0 SHADOW_OFF HAEc ltac:(lia)); [reflexivity | assumption | | ];
  unfold SHADOW_OFF; lia
| rewrite (dtb_U_ag E _ _ 18 c RSB_CLOSED HAEc ltac:(lia)); [| assumption | unfold RSB_CLOSED; lia | ]; unfold RSB_CLOSED; lia
| rewrite (dtb_U_ag E _ _ 18 c RSB_CLOSED HAEc ltac:(lia)); [| assumption | unfold RSB_CLOSED; lia | ]; unfold RSB_CLOSED; lia ]
end.

(* the scan stage's tail at check_decide's entry: s6 = a0 = cfg_decide's answer, a1 = the expectation, sp / gp / tp,
   s8 and dtb_L kept *)
Ltac s1_tail Hexp H10 H21 H24 Hax HF HL HK Hkept Hpre Hpod :=
  ck_keep kwr_stk;
  lazymatch goal with HS : st_ok _ ?Ec ?ss (restrict ?H ?ms), HAE : env_agree 32 (Ereg ?regs2 []) _ |- _ =>
  let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
  let R10 := fresh "R10" in rreg HS (10%bv : bv 5) R10;
  let R22 := fresh "R22" in rreg HS (Z_to_bv 5 22) R22;
  let R21 := fresh "R21" in rreg HS (21%bv : bv 5) R21;
  let HAEc := fresh "HAEc" in assert (HAEc : env_agree 32 (Ereg regs2 []) Ec) by (env_agree_chain HAE);
  let CL := fresh "CL" in let C234 := fresh "C234" in
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ dtb_L1 HS HAEc ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAEc ltac:(vm_compute; reflexivity)) as C234;
  let E10 := fresh "E10" in
  assert (E10 : ew Ec 10 = getr regs2 (Z_to_bv 5 10)) by exact (dtb_ew_ag2 Ec regs2 [] 10 HAEc ltac:(lia));
  rewrite (st_ok_restrict_mkst rsegs H Ec ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_DECIDE by (vm_compute; reflexivity);
  dt_coreT;
  lazymatch goal with HcoreT : rsb_core _ _ _ _ _ _ _ _ _ _ _, HspT : spZ _ = _ |- _ =>
  lazymatch type of HK with dtb_K ?cx ?POST ?regs0 ?W0 ?mem0 =>
  lazymatch type of Hax with dtb_ax _ ?x ?u _ _ =>
  apply (dtb_cdec cx POST regs0 W0 mem0 _ _ _ _ _ _ x u Hpre Hpod HcoreT HspT);
  [ exact R1
  | etransitivity; [exact R10|]; etransitivity; [exact E10|]; etransitivity; [exact H10|]; symmetry; exact Hexp
  | refine (dtb_dec_w _ _ _ _ (eq_trans R22 (eq_trans E10 H10)))
  | etransitivity; [exact (CL (Z_to_bv 5 24) ltac:(dtb_in))|]; exact H24
  | exact Hax
  | exact HF
  | refine (cs_eq_trans _ _ _ _ HL (dtb_cs_cons dtb_L' _ _ 21%bv (dtb_cs_sub _ _ _ _ CL dtb_L'_L1) _));
    etransitivity; [exact R21|]; symmetry; etransitivity; [exact H21|]; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
    intros a Ha Hs; lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ms) a = _ |- _ =>
    rewrite (KE a Ha (fun x => x)) end; exact (Hkept a Ha Hs)
  | exact HK ]
  end end end end.
(* a taken `beq s7,a3` arm: s7 = the asked value equals a closed rate, against rate_bit = 0 *)
Ltac s1_refute Hc H23 Hb' :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ec _) _ = _ =>
  lazymatch goal with HAE : env_agree 32 (Ereg ?regs2 []) _ |- _ =>
  let HAEc := fresh "HAEc" in assert (HAEc : env_agree 32 (Ereg regs2 []) Ec) by (env_agree_chain HAE);
  lazymatch type of H23 with getr _ _ = w64 ?v =>
  rewrite branch_eq_U, (dtb_U_ag Ec regs2 [] 23 0 v HAEc ltac:(lia) H23 (dtb_v_range _)
    ltac:(rewrite Z.add_0_r; apply dtb_v_range)), U_lit in Hc by lia;
  apply Z.eqb_eq in Hc; rewrite Z.add_0_r in Hc; exfalso; rewrite Hc in Hb'; vm_compute in Hb'; discriminate Hb'
  end end end.
(* closed_list's shadow bytes after a part of the scan, which wrote no byte *)
Ltac s1_next Hra HraN :=
  ck_keep kwr_stk;
  lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ ?H (ms_mem ?ms) a = aview _ ?H ?m0 a |- _ =>
  assert (HraN : range_addressable (aview rsegs H (ms_mem ms)) SHADOW_OFF RSB_CLOSED 12)
  by (apply (dtb_ra_kept (fun x => 0 <= x < 2 ^ 64) H H m0 (ms_mem ms) RSB_CLOSED 12);
      [ let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; exact (KE y Hy (fun f => f))
      | let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; unfold shadow_of_addr, SHADOW_OFF, RSB_CLOSED in Hy |- *;
        pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia); lia
      | exact Hra ]) end.
(* the scan stage's entry at 0x82e64 with the overrides ov *)
Ltac s1_enter ov H9 H18 H20 H22 Hm H46 Hal Hvm TCL :=
  lazymatch goal with |- SRr _ ?W (cfg_at _ _ ?regs2 ?mem2 _) _ =>
  lazymatch type of Hvm with val_mem _ _ (?R + _) _ ?mask =>
  let HS := fresh "HS" in
  pose proof (dtb_ent1 ov W regs2 mem2 R mask) as HS;
  specialize (HS ltac:(repeat (apply Forall_cons; [cbn [fst snd]; split;
    [ let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
    | rewrite ck_lit; symmetry; assumption ] | ]); apply Forall_nil) H9 H18 H20 H22 ltac:(lia) H46 Hal Hvm TCL);
  let E := fresh "E" in let HE := fresh "HE" in
  remember (Ereg regs2 []) as E eqn:HE;
  let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl);
  let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W) mem2)) by constructor;
  let KE := fresh "KE" in
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem2 a)
  by (intros; reflexivity);
  unfold cfg_at; change (w64 DTB_R_CFG) with (Z_to_bv 64 DTB_R_CFG)
  end end.

(* ---- S1: 0x82e64 mv s6,a0; the expectation (the slave test, the two bit_of scans); jal check_decide ---- *)
Lemma dtb_s1 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 role u x,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
(role = 0 \/ role = 1) ->
getr regs2 (Z_to_bv 5 10) = w64 (RateCfg.decide_res role (dtb_v u) (q_mask (x_e rsegs cx))) ->
getr regs2 (Z_to_bv 5 21) = w64 role -> getr regs2 (Z_to_bv 5 23) = w64 (dtb_v u) ->
getr regs2 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) -> getr regs2 (Z_to_bv 5 24) = w64 x ->
dtb_ax cx x u W0 mem0 -> dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs DTB_R_CFG regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 role u x Hpre Hpod Hcore Hsp Hrole
  H10 H21 H23 H22 H24 Hax HF HL Hkept HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof rtmb_B_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
pose proof Hax as (_ & Hu & _).
pose proof HF as (H9 & H18 & H20 & Hm & Hvm).
assert (H9r : getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)))
by (etransitivity; [exact (HL (Z_to_bv 5 9) ltac:(dtb_in)) | exact H9]).
assert (H18r : getr regs2 (Z_to_bv 5 18) = w64 RSB_CLOSED)
by (etransitivity; [exact (HL (Z_to_bv 5 18) ltac:(dtb_in)) | exact H18]).
assert (H20r : getr regs2 (Z_to_bv 5 20) = w64 SHADOW_OFF)
by (etransitivity; [exact (HL (Z_to_bv 5 20) ltac:(dtb_in)) | exact H20]).
assert (Hvmr : val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + 0x148) 8 (q_mask (x_e rsegs cx)))
by (apply (dtb_val_kept cx W0 mem0 W2 mem2); [lia | lia | lia | exact Hkept | exact Hvm]).
clear H9 H18 H20 Hvm.
destruct (dtb_strs B MT cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore) as (_ & _ & _ & TCL & _).
pose proof TCL as (_ & _ & _ & Hra). change (4 * Z.of_nat (length RateCfg.closed_list)) with 12 in Hra.
destruct Hrole as [-> | ->].
2:{ (* a slave: 0x82e6c bnez s5 taken, a1 = 3 *)
  dtb_enter [((21%bv : bv 5), SLit 1)].
  dtb_run; [m2b_awr|].
  assert (Hexp : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (RateCfg.decide_res 1 (dtb_v u) (q_mask (x_e rsegs cx)))).
  { let R11 := fresh "R11" in rreg HS (11%bv : bv 5) R11. etransitivity; [exact R11|]. reflexivity. }
  s1_tail Hexp H10 H21 H24 Hax HF HL HK Hkept Hpre Hpod. }
(* role 0: the asked value is one of the three closed rates, or none of them *)
destruct (RateCfg.rate_bit_cases u) as [[Hc _]|[[Hc _]|[[Hc _]|(Hn1 & Hn2 & Hn3 & Hb)]]].
1-3: subst u; unfold RateCfg.RATE_44K1, RateCfg.RATE_48K, RateCfg.RATE_96K in *;
  rewrite dtb_v_small in H10, H23 by lia;
  lazymatch type of H23 with getr _ _ = w64 ?c =>
  s1_enter [((21%bv : bv 5), SLit 0); ((23%bv : bv 5), SLit c)] H9r H18r H20r H22 Hm H46 Hal Hvmr TCL end;
  dtb_run; [dtb_obl Hra HAE .. | m2b_awr | ];
  lazymatch goal with HS : st_ok _ ?Ec ?ss (restrict ?H ?ms) |- _ =>
  let R11 := fresh "R11" in rreg HS (11%bv : bv 5) R11;
  assert (HAEc : env_agree 32 (Ereg regs2 []) Ec) by (env_agree_chain HAE) end.
- assert (Hexp : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (RateCfg.decide_res 0 44100 (q_mask (x_e rsegs cx)))).
  { etransitivity; [exact R11|]. rewrite (dtb_dec_bit 44100 (q_mask (x_e rsegs cx)) 1) by (reflexivity || lia).
    rewrite (dtb_ew_ag _ regs2 [] 22 (q_mask (x_e rsegs cx)) HAE ltac:(lia) H22).
    exact (dtb_expect_bv E (q_mask (x_e rsegs cx)) 1 ltac:(lia) ltac:(lia)). }
  s1_tail Hexp H10 H21 H24 Hax HF HL HK Hkept Hpre Hpod.
- assert (Hexp : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (RateCfg.decide_res 0 48000 (q_mask (x_e rsegs cx)))).
  { etransitivity; [exact R11|]. rewrite (dtb_dec_bit 48000 (q_mask (x_e rsegs cx)) 2) by (reflexivity || lia).
    rewrite (dtb_ew_ag _ regs2 [] 22 (q_mask (x_e rsegs cx)) HAE ltac:(lia) H22).
    exact (dtb_expect_bv E (q_mask (x_e rsegs cx)) 2 ltac:(lia) ltac:(lia)). }
  s1_tail Hexp H10 H21 H24 Hax HF HL HK Hkept Hpre Hpod.
- assert (Hexp : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (RateCfg.decide_res 0 96000 (q_mask (x_e rsegs cx)))).
  { etransitivity; [exact R11|]. rewrite (dtb_dec_bit 96000 (q_mask (x_e rsegs cx)) 4) by (reflexivity || lia).
    rewrite (dtb_ew_ag _ regs2 [] 22 (q_mask (x_e rsegs cx)) HAE ltac:(lia) H22).
    exact (dtb_expect_bv E (q_mask (x_e rsegs cx)) 4 ltac:(lia) ltac:(lia)). }
  s1_tail Hexp H10 H21 H24 Hax HF HL HK Hkept Hpre Hpod.
- (* none of them: three `beq s7,a3` splits, each taken arm contradicts rate_bit u = 0 *)
  assert (Hb' : RateCfg.rate_bit (dtb_v u) = 0) by (rewrite dtb_rate_bit_v by exact Hu; exact Hb).
  s1_enter [((21%bv : bv 5), SLit 0)] H9r H18r H20r H22 Hm H46 Hal Hvmr TCL.
  dtb_run; [dtb_obl Hra HAE .. | m2b_awr | ].
  s1_next Hra Hra1. dtb_branch Hc1; [s1_refute Hc1 H23 Hb' |].
  dtb_hae HAE HAE1. dtb_run; [dtb_obl Hra1 HAE1 .. | m2b_awr | ].
  s1_next Hra Hra2. dtb_branch Hc2; [s1_refute Hc2 H23 Hb' |].
  dtb_hae HAE HAE2. dtb_run; [dtb_obl Hra2 HAE2 .. | m2b_awr | ].
  s1_next Hra Hra3. dtb_branch Hc3; [s1_refute Hc3 H23 Hb' |].
  dtb_hae HAE HAE3. dtb_run; [dtb_obl Hra3 HAE3 .. | m2b_awr | ].
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ =>
  assert (Hexp : getr (ms_regs msc) (Z_to_bv 5 11) = w64 (RateCfg.decide_res 0 (dtb_v u) (q_mask (x_e rsegs cx))))
  by (let R11 := fresh "R11" in rreg HS (11%bv : bv 5) R11; etransitivity; [exact R11|];
      rewrite (dtb_dec_nc _ _ Hb'); reflexivity) end.
  s1_tail Hexp H10 H21 H24 Hax HF HL HK Hkept Hpre Hpod.
Qed.

(* ---- S0: DEC 0x82e44, s8 := R + 0x198 + 4 t; lw s7,0(s8) (no check); mv a0,s5; mv a1,s7; mv a2,s6;
   jal cfg_decide ---- *)
Lemma dtb_s0 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 t o role u,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
(t = 0 /\ o = 0x198 \/ t = 1 /\ o = 0x19c) -> (role = 0 \/ role = 1) -> 0 <= u < 2 ^ 32 ->
getr regs2 (Z_to_bv 5 26) = w64 t -> getr regs2 (Z_to_bv 5 21) = w64 role ->
getr regs2 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) ->
val_mem rsegs (mrestrict (w_H W0) mem0) (q_R (x_e rsegs cx) + o) 4 u -> dtb_fix cx regs0 W0 mem0 ->
cs_eq dtb_L regs0 regs2 -> dtb_kept cx W0 mem0 W2 mem2 -> dtb_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs RSB_DEC regs2 mem2 md2) POST.
Proof using MTL HBgot HBcell ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 t o role u Hpre Hpod Hcore Hsp Hto Hrole Hu
  H26 H21 H22 Hva HF HL Hkept HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof rtmb_B_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
pose proof HF as (H9 & _ & _ & Hm & _).
assert (H9r : getr regs2 (Z_to_bv 5 9) = w64 (q_R (x_e rsegs cx)))
by (etransitivity; [exact (HL (Z_to_bv 5 9) ltac:(dtb_in)) | exact H9]).
assert (Hvar : val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + o) 4 u)
by (apply (dtb_val_kept cx W0 mem0 W2 mem2); [destruct Hto as [[_ ->]|[_ ->]]; lia .. | exact Hkept | exact Hva]).
destruct Hto as [[-> ->]|[-> ->]].
all: pose proof (dtb_ent0 _ _ W2 regs2 mem2 (q_R (x_e rsegs cx)) u H9r H26 Hu H46 Hal Hvar
  ltac:(first [left; reflexivity | right; reflexivity])) as HS.
all: remember (Ereg regs2 [w64 u]) as E eqn:HE.
all: assert (HAE : env_agree 32 (Ereg regs2 [w64 u]) E) by (subst E; apply env_agree_refl).
all: assert (SHOK : sh_ok rsegs M2B_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
all: assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
all: unfold cfg_at; change (w64 RSB_DEC) with (Z_to_bv 64 RSB_DEC).
all: dtb_run; [m2b_awr | ].
all: ck_keep kwr_stk.
all: let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
all: let R := fresh "R12" in rreg HS (12%bv : bv 5) R.
all: let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
all: let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
all: lazymatch goal with HS : st_ok _ ?Ec ?ss (restrict ?H ?msc) |- _ =>
  let e11 := eval vm_compute in (sr_get (ss_regs ss) (11%bv : bv 5)) in
  let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
  let e24 := eval vm_compute in (sr_get (ss_regs ss) (24%bv : bv 5)) in
  assert (R11 : getr (ms_regs msc) (11%bv : bv 5) = sv_denot Ec e11) by exact (st_ok_restrict_reg rsegs H Ec ss msc _ HS);
  assert (R23 : getr (ms_regs msc) (23%bv : bv 5) = sv_denot Ec e23) by exact (st_ok_restrict_reg rsegs H Ec ss msc _ HS);
  assert (R24 : getr (ms_regs msc) (24%bv : bv 5) = sv_denot Ec e24) by exact (st_ok_restrict_reg rsegs H Ec ss msc _ HS);
  assert (E32 : ew Ec 32 = Z_to_bv 64 u) by (rewrite HE; cbn [ew ewset havoc Nat.eqb]; exact (ew_Ereg_extra regs2 [w64 u] 0));
  assert (HAEc : env_agree 32 (Ereg regs2 [w64 u]) Ec) by (env_agree_chain HAE)
end.
(* one conjunction, which dt_post's subst leaves alone *)
all: assert (UU : bv_unsigned (getr (ms_regs ms) (10%bv : bv 5)) = role /\
  bv_unsigned (getr (ms_regs ms) (11%bv : bv 5)) = dtb_v u /\
  bv_unsigned (getr (ms_regs ms) (12%bv : bv 5)) = q_mask (x_e rsegs cx))
  by (split; [|split];
      [ rewrite R10, (dtb_ew_ag E regs2 [w64 u] 21 role HAE ltac:(lia) H21); apply dtb_w64_unsigned; lia
      | rewrite R11; lazymatch goal with |- bv_unsigned (sv_denot ?Ec ?v) = _ => change (U Ec v = dtb_v u) end;
        rewrite lf_U_add0; exact (dtb_U_sext _ 32 u E32 Hu)
      | rewrite R12, (dtb_ew_ag E regs2 [w64 u] 22 (q_mask (x_e rsegs cx)) HAE ltac:(lia) H22);
        apply dtb_w64_unsigned; lia ]).
all: lazymatch type of Hvar with val_mem _ _ (?R + ?o) _ _ =>
  assert (W24 : getr (ms_regs ms) (24%bv : bv 5) = w64 (R + o))
  by (apply bv_eq; rewrite R24;
      lazymatch goal with |- bv_unsigned (sv_denot ?Ec ?v) = _ => change (U Ec v = bv_unsigned (w64 (R + o))) end;
      rewrite dtb_w64_unsigned by lia;
      rewrite (dtb_U_ag _ regs2 [w64 u] 9 o (q_R (x_e rsegs cx)) HAEc ltac:(lia) H9r ltac:(lia) ltac:(lia));
      reflexivity) end.
all: assert (R26e : getr (ms_regs ms) (26%bv : bv 5) = getr regs2 (26%bv : bv 5))
  by (etransitivity; [exact R26|]; symmetry; etransitivity; [exact H26|]; reflexivity).
all: dt_at A_CFG_DECIDE regs2 dtb_L0.
all: assert (R1' : getr (ms_regs ms) 1 = w64 0x82e64) by exact R1.
all: dt_coreT.
all: eapply SRr_bind;
  [ apply (rt_cfg_decide_B B MT MTL (AR_laws_ok rsegs B) (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx)
      (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
      (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _ (x_k rsegs cx) (ms_regs ms));
    dt_pre T_leaf_STK
  | ].
all: intros W3 c3 _ Hpost.
all: dt_post T_leaf_STK Hpost.
all: lazymatch type of Hvar with val_mem _ _ ?x _ _ =>
  apply (dtb_s1 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 role u x Hpre Hpod Hcore3);
  [ dt_sp3 Hpres3 HspT
  | exact Hrole
  | destruct UU as (U10 & U11 & U12); etransitivity; [exact HR3|]; f_equal; f_equal; [exact U10 | exact U11 | exact U12]
  | dt_keep 21 Hpres3 CL; exact H21
  | etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|]; etransitivity; [exact R23|];
    rewrite denot_lit_U, (dtb_U_sext _ 32 u E32 Hu); reflexivity
  | dt_keep 22 Hpres3 CL; exact H22
  | etransitivity; [exact (Hpres3 24 ltac:(unfold acallee_saved; lia))|]; exact W24
  | split; [first [left; reflexivity | right; reflexivity] | split; [exact Hu | exact Hva]]
  | exact HF
  | exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL (dtb_cs_sub _ _ _ _ (dtb_cs_cons dtb_L0 _ _ 26%bv CL R26e) dtb_L_L0'))
      (cs_eq_of_pres dtb_L _ _ dtb_L_cs Hpres3))
  | dt_kept3 Hkept3 KE Hkept
  | exact HK ] end.
Qed.

(* ---- the latch 0x82f84: addi s10,s10,1; bne s10,s9 -> DEC; T2 ---- *)
Lemma dtb_latch : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 (t : Z),
rsb_pre rsegs B cx -> (t = 0 \/ t = 1) ->
getr regs0 (Z_to_bv 5 26) = w64 t -> getr regs0 (Z_to_bv 5 25) = w64 2 ->
(t = 0 -> forall ly4 S4 W4 regs4 mem4 md4,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 -> spZ regs4 = q_R (x_e rsegs cx) ->
  cs_eq dtb_Lk regs0 regs4 -> getr regs4 (Z_to_bv 5 26) = w64 1 ->
  getr regs4 (Z_to_bv 5 22) = w64 (q_mask (x_e rsegs cx)) -> dtb_kept cx W0 mem0 W4 mem4 ->
  SRr rsegs W4 (cfg_at rsegs RSB_DEC regs4 mem4 md4) POST) ->
(t = 1 -> forall ly4 S4 W4 regs4 mem4 md4,
  rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 -> spZ regs4 = q_R (x_e rsegs cx) ->
  cs_eq dtb_Lk regs0 regs4 -> dtb_kept cx W0 mem0 W4 mem4 ->
  SRr rsegs W4 (cfg_at rsegs RSB_T2 regs4 mem4 md4) POST) ->
dtb_K cx POST regs0 W0 mem0.
Proof using MTL.
intros cx POST regs0 W0 mem0 t Hpre Ht H26 H25 KD KT ly2 S2 W2 regs2 mem2 md2 Hcore Hsp HL H22 Hkept.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof rtmb_B_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (proj1 Hcore) as HJ.
assert (H26' : getr regs2 (Z_to_bv 5 26) = w64 t) by (etransitivity; [exact (HL (Z_to_bv 5 26) ltac:(dtb_in))| exact H26]).
assert (H25' : getr regs2 (Z_to_bv 5 25) = w64 2) by (etransitivity; [exact (HL (Z_to_bv 5 25) ltac:(dtb_in))| exact H25]).
destruct Ht as [-> | ->].
- dtb_enter [((26%bv : bv 5), SLit 0); ((25%bv : bv 5), SLit 2)].
  dtb_run_to RSB_DEC; [m2b_awr|].
  ck_keep kwr_stk.
  let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
  let R := fresh "R25" in rreg HS (25%bv : bv 5) R.
  dt_at RSB_DEC regs2 dtb_LL.
  dt_coreT.
  apply (KD eq_refl ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HcoreT HspT).
  + refine (cs_eq_trans _ _ _ _ (dtb_cs_sub _ _ _ _ HL dtb_L_Lk) (dtb_cs_sub _ _ _ _ (dtb_cs_cons dtb_LL _ _ 25%bv CL _) dtb_Lk_LL)).
    etransitivity; [exact R25|]. symmetry. etransitivity; [exact H25'|]. reflexivity.
  + etransitivity; [exact R26|]. reflexivity.
  + etransitivity; [exact (CL (Z_to_bv 5 22) ltac:(dtb_in))|]. exact H22.
  + intros a Ha Hs. rewrite (KE a Ha (fun f => f)). exact (Hkept a Ha Hs).
- dtb_enter [((26%bv : bv 5), SLit 1); ((25%bv : bv 5), SLit 2)].
  dtb_run; [m2b_awr|].
  ck_keep kwr_stk.
  let R := fresh "R25" in rreg HS (25%bv : bv 5) R.
  dt_at RSB_T2 regs2 dtb_LL.
  dt_coreT.
  apply (KT eq_refl ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HcoreT HspT).
  + refine (cs_eq_trans _ _ _ _ (dtb_cs_sub _ _ _ _ HL dtb_L_Lk) (dtb_cs_sub _ _ _ _ (dtb_cs_cons dtb_LL _ _ 25%bv CL _) dtb_Lk_LL)).
    etransitivity; [exact R25|]. symmetry. etransitivity; [exact H25'|]. reflexivity.
  + intros a Ha Hs. rewrite (KE a Ha (fun f => f)). exact (Hkept a Ha Hs).
Qed.
End w.

(* ======================================= the cut facts the turn keeps ======================================= *)
(* a location of a cut whose value the turn keeps: a register of dtb_Lk, or a cell of the real frame at or above R *)
Definition dtb_loc_ok (l : rt_loc) : bool :=
match l with
| LReg r => existsb (Z.eqb r) [8; 9; 18; 19; 20; 21; 25]
| LCell XR o => (0 <=? o) && (o <=? 0x1f8)
| LCell _ _ => false
end.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma dtb_at_kept : forall (cx : rsb_scx rsegs) W0 mem0 regs0 W4 mem4 regs4 L,
rsb_pre rsegs B cx -> forallb dtb_loc_ok (map fst L) = true ->
rsb_at_cx rsegs cx W0 mem0 regs0 L -> cs_eq dtb_Lk regs0 regs4 -> dtb_kept cx W0 mem0 W4 mem4 ->
rsb_at_cx rsegs cx W4 mem4 regs4 L.
Proof.
intros cx W0 mem0 regs0 W4 mem4 regs4 L Hpre Hok Hat HL Hk.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & _).
unfold rsb_at_cx, rsb_at in *.
apply Forall_forall. intros [l v] Hin.
pose proof (proj1 (Forall_forall _ _) Hat _ Hin) as Hv.
assert (Hl : dtb_loc_ok l = true).
{ apply (proj1 (forallb_forall _ _) Hok). apply in_map_iff. exists (l, v). split; [reflexivity | exact Hin]. }
destruct l as [r | b o]; cbn [fst snd rt_at] in Hv |- *.
- cbn [dtb_loc_ok existsb] in Hl.
  etransitivity; [|exact Hv]. apply HL.
  repeat (apply orb_prop in Hl; destruct Hl as [Hl | Hl]; [apply Z.eqb_eq in Hl; subst r; dtb_in |]).
  discriminate Hl.
- destruct b; cbn [dtb_loc_ok] in Hl; try discriminate Hl.
  apply andb_prop in Hl. destruct Hl as [Hl1 Hl2]. apply Z.leb_le in Hl1, Hl2.
  cbn [rt_xv] in Hv |- *.
  apply (val_mem_kept rsegs (w_H W0) (w_H W4) mem0 mem4); [|exact Hv].
  intros k Hk'. cbn in Hk'. apply Hk; lia.
Qed.

Lemma dtb_ask_kept : forall (cx : rsb_scx rsegs) rec W0 mem0 W4 mem4,
rsb_pre rsegs B cx -> rsb_ask_at rsegs cx rec W0 mem0 -> dtb_kept cx W0 mem0 W4 mem4 -> rsb_ask_at rsegs cx rec W4 mem4.
Proof.
intros cx rec W0 mem0 W4 mem4 Hpre (H0 & H1) Hk.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & _).
split; (apply (dtb_val_kept cx W0 mem0 W4 mem4); [lia | lia | lia | exact Hk | assumption]).
Qed.

Lemma dtb_fsh_kept : forall (cx : rsb_scx rsegs) W0 mem0 W4 mem4 pat,
rsb_pre rsegs B cx -> (length pat <= 128)%nat ->
rsb_fsh_at rsegs cx W0 mem0 pat -> dtb_kept cx W0 mem0 W4 mem4 -> rsb_fsh_at rsegs cx W4 mem4 pat.
Proof.
intros cx W0 mem0 W4 mem4 pat Hpre Hlen Hf Hk i Hi.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & _ & _).
assert (D1 : 0 <= q_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
unfold T_SEG_STK, ASTACK in Hceil.
assert (D2 : q_F (x_e rsegs cx) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
rewrite (Hk (shadow_addr (q_F (x_e rsegs cx)) + i)); [exact (Hf i Hi) | |];
unfold shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK; lia.
Qed.

Lemma dtb_pp_kept : forall (cx : rsb_scx rsegs) W0 mem0 W4 mem4 l,
rsb_pre rsegs B cx -> Z.of_nat (length l) = Layout.PP_SIZE ->
rsb_pp_at rsegs cx W0 mem0 l -> dtb_kept cx W0 mem0 W4 mem4 -> rsb_pp_at rsegs cx W4 mem4 l.
Proof.
intros cx W0 mem0 W4 mem4 l Hpre Hlen Hp Hk j Hj.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & _).
pose proof (m2b_pp B cx Hpre) as (P4096 & Pceil & _).
unfold rsb_u8s in Hj. rewrite length_map in Hj.
destruct (Hp j ltac:(unfold rsb_u8s; rewrite length_map; exact Hj)) as [Hv Hr].
split; [|exact Hr].
apply (val_mem_kept rsegs (w_H W0) (w_H W4) mem0 mem4); [|exact Hv].
intros k Hk'. cbn in Hk'. apply Hk; unfold T_SEG_STK, ASTACK in *; lia.
Qed.

(* the part of a cut every cut of the decide loop shares, at the state the latch leaves *)
Lemma dtb_base_kept : forall (fx0 : YK11.FPState) (cx : rsb_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4,
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx0) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly4 S4 W4 regs4 mem4 md4 -> dtb_kept cx W2 mem2 W4 mem4 ->
rsb_chk_base (fx := fx0) rsegs B MT cx fx2 rec ly4 S4 W4 regs4 mem4 md4.
Proof.
intros fx0 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4 Hpre
  (_ & Hfxk & Hfsh & _ & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hnpod) Hcore4 Hk.
split; [exact Hcore4|]. split; [exact Hfxk|].
split; [apply (dtb_fsh_kept cx W2 mem2 W4 mem4 rsb_PB Hpre ltac:(unfold rsb_PB; rewrite rtmb_sh_len; lia) Hfsh Hk)|].
split; [exact (m2b_rom_at B MT cx ly4 S4 W4 regs4 mem4 md4 Hpre Hpod Hcore4)|].
split; [exact (dtb_pp_kept cx W2 mem2 W4 mem4 _ Hpre (Layout.length_pp_bytes rec Hwf) Hpp Hk)|].
exact (conj Hwf (conj Hlen (conj Hpod0 (conj Hpod Hnpod)))).
Qed.
End r.

(* ======================================= the piece: one turn of the decide loop ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = 0x9c170.
Hypothesis HBcell : as_shadow_cell B = 0xa4f38.
Hypothesis ASTRCMP : forall fx' : YK11.FPState, astrcmp_realizes (fx := fx') rsegs B A_STRCMP.

Theorem rt_dec_turn_B : rsb_piece_W13_stmt rsegs B MT.
Proof using MTL HBgot HBcell ASTRCMP.
unfold rsb_piece_W13_stmt.
intros cx POST inp t Hst KDEC KT2 fx2 ly2 S2 W2 regs2 mem2 md2 rec Hcut.
destruct Hst as (Hpre & _).
destruct Hcut as (Hbase & Hat & Hask & Ht).
pose proof Hbase as (Hcore & _ & Hfsh & _ & _ & _ & _ & _ & Hpod & _).
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhdr & _).
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof Hhdr as (Hfl & Hmk & _).
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ pose proof Hcore as (_ & Hr & _). rewrite <- HR. unfold spZ. f_equal. exact (Hr 2 ltac:(lia)). }
pose proof Hat as Hat0.
unfold rsb_at_cx, rsb_at, rsb_L_DEC, rsb_L_dec in Hat0. cbn [app] in Hat0.
rewrite !Forall_cons_iff in Hat0.
destruct Hat0 as (A8 & A9 & A19 & C10 & C18 & C60 & C168 & C148 & C178 & A20 & A26 & A25 & A21 & A22 & A18 & _).
cbn [fst snd rt_at rt_xv] in A9, A20, A26, A25, A21, A22, A18, C148.
rewrite (Z.mod_small (q_mask (x_e rsegs cx))) in C148 by lia.
assert (Hrole : Z.b2z (Z.testbit (q_fl (x_e rsegs cx)) 1) = 0 \/ Z.b2z (Z.testbit (q_fl (x_e rsegs cx)) 1) = 1)
by (destruct (Z.testbit (q_fl (x_e rsegs cx)) 1); cbn; lia).
assert (HF : dtb_fix cx regs2 W2 mem2) by (split; [exact A9 | split; [exact A18 | split; [exact A20 | split; [exact Hmk | exact C148]]]]).
destruct Hask as (Hask0 & Hask1).
destruct t as [|[|t']]; [| | lia].
- (* turn 0: asked[0] at R + 0x198; the latch goes back to the head with asked[1] *)
  apply (dtb_s0 (fx := fx2) B MT MTL HBgot HBcell (ASTRCMP fx2)
    cx POST regs2 W2 mem2 ly2 S2 W2 regs2 mem2 md2 0 0x198 _ (rsb_ask0 rsegs cx rec mod 2 ^ 32)
    Hpre Hpod Hcore Hsp (or_introl (conj eq_refl eq_refl)) Hrole ltac:(apply Z.mod_pos_bound; lia)).
  + exact A26.
  + exact A21.
  + exact A22.
  + exact Hask0.
  + exact HF.
  + intros r _. reflexivity.
  + intros a _ _. reflexivity.
  + apply (dtb_latch (fx := fx2) B MT MTL cx POST regs2 W2 mem2 0 Hpre (or_introl eq_refl) A26 A25).
    * intros _ ly4 S4 W4 regs4 mem4 md4 Hcore4 Hsp4 HL4 H26' H22' Hk4.
      apply (KDEC fx2 ly4 S4 W4 regs4 mem4 md4 rec).
      split; [exact (dtb_base_kept B MT fx cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4 Hpre Hbase Hcore4 Hk4)|].
      split; [|split; [exact (dtb_ask_kept B cx rec W2 mem2 W4 mem4 Hpre (conj Hask0 Hask1) Hk4) | lia]].
      unfold rsb_at_cx, rsb_at, rsb_L_DEC. apply Forall_app. split.
      { apply (dtb_at_kept B cx W2 mem2 regs2 W4 mem4 regs4 (rsb_L_dec rsegs cx) Hpre ltac:(reflexivity)); [|exact HL4 | exact Hk4].
        unfold rsb_at_cx, rsb_at, rsb_L_DEC in Hat. exact (proj1 (proj1 (Forall_app _ _ _) Hat)). }
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rt_at].
      -- etransitivity; [exact (HL4 (Z_to_bv 5 20) ltac:(dtb_in))|]. exact A20.
      -- rewrite H26'. reflexivity.
      -- etransitivity; [exact (HL4 (Z_to_bv 5 25) ltac:(dtb_in))|]. exact A25.
      -- etransitivity; [exact (HL4 (Z_to_bv 5 21) ltac:(dtb_in))|]. exact A21.
      -- exact H22'.
      -- etransitivity; [exact (HL4 (Z_to_bv 5 18) ltac:(dtb_in))|]. exact A18.
    * intros Hc. discriminate Hc.
- (* turn 1: asked[1] at R + 0x19c; the latch leaves to T2 *)
  apply (dtb_s0 (fx := fx2) B MT MTL HBgot HBcell (ASTRCMP fx2)
    cx POST regs2 W2 mem2 ly2 S2 W2 regs2 mem2 md2 1 0x19c _ (rsb_other (x_e rsegs cx))
    Hpre Hpod Hcore Hsp (or_intror (conj eq_refl eq_refl)) Hrole (dtb_other_range _ Hhdr)).
  + exact A26.
  + exact A21.
  + exact A22.
  + exact Hask1.
  + exact HF.
  + intros r _. reflexivity.
  + intros a _ _. reflexivity.
  + apply (dtb_latch (fx := fx2) B MT MTL cx POST regs2 W2 mem2 1 Hpre (or_intror eq_refl) A26 A25).
    * intros Hc. discriminate Hc.
    * intros _ ly4 S4 W4 regs4 mem4 md4 Hcore4 Hsp4 HL4 Hk4.
      apply (KT2 fx2 ly4 S4 W4 regs4 mem4 md4 rec).
      split; [exact (dtb_base_kept B MT fx cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly4 S4 W4 regs4 mem4 md4 Hpre Hbase Hcore4 Hk4)|].
      apply (dtb_at_kept B cx W2 mem2 regs2 W4 mem4 regs4 (rsb_L_dec rsegs cx) Hpre ltac:(reflexivity)); [|exact HL4 | exact Hk4].
      unfold rsb_at_cx, rsb_at, rsb_L_DEC in Hat. exact (proj1 (proj1 (Forall_app _ _ _) Hat)).
Qed.
End m.
Print Assumptions rt_dec_turn_B.
