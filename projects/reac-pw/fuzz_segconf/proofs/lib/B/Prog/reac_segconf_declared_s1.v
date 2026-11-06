(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   entry to the memchr call 0x86ef8 (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/A/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ef8; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths, module names and numbers changed; 673 of its 801 lines of code are new or changed and 399 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/reac_segconf_declared_s1.v (commit 6121a10279e4).
   Segment S1 of the image-B walk of reac_segconf_declared (fuzz_segconf.asan-ubsan, entry 0x89e7c; the interface is
   reac_segconf_declared_d.v): from the entry to the loop head KL (0x8a000) at pass 0, or to the join KX (0x8a0fc)
   when c->n <= 0. Written against image B's code, in the form of plugin-hostd/fuzz_command's
   lib/B/Prog/check_reply_s1.v (origin/ossv/recipes 501c0d516c69: entry seed, prologue token run, the class-1 frame
   call through aj_stack_malloc_atS, the state after it, a plain run over the frame set-up, the frame's shadow made
   read-only, a token run) and of this unit's lib/B/Prog/check_segments_s1.v (the entry seed over the
   position-abstract listing, the fold of UBSan's alignment test, `blez` on c->n). Image B differs from image A by
   a frame of 224 (A 192), the slots 32 / 40 / 48 / 80 / 88 / 112 of s1 (A 16 / 24 / 32 / 40 / 48 / 56), the
   registers s11 / s5 / s7 / s4, UBSan's `andi a1,s6,7; bnez a1` at 0x89fa0-0x89fa4, and the longer loop set-up
   (a3 = ~c, a4 = 32, s2 = 0, 24(s1) = (c + 0x2c80) & 7 + 3).
   The stretch:
     0x89e7c .. 0x89ef0  the frame of 224 (a zero word at sp0 - 224, 13 saves at sp0 - 8 .. sp0 - 104), s0 = sp0,
                         `andi sp,sp,-32` (s1 = dc_sp1 sp0, the entry seed's alias of atom 34), the spills of
                         a3 / a2 / a1 to 72 / 64 / 56(s1), the GOT loads of the use-after-return flag (1: `beqz a2`
                         at 0x89eec falls through, the flag cell's region holds 1 by AR's const law) and of the
                         shadow base (s5), s6 = c
     0x89ef4             `jal frame_alloc_1` with a0 = 96: aj_stack_malloc_atS (PaCall.v) with SM1 / SMP and room
                         (sa_room: count_cid_le_length); F = frame_addr ly 1 fpos, FL its flag cell
     0x89ef8 .. 0x89f98  `bnez a0` at 0x89f04 is taken (F >= 4096, the fact HPTR 5 of F's atom), so the real-stack
                         probe loop 0x89f08 .. 0x89f20 is dead; 112(s1) = F, the frame header, F's shadow (f1 x4,
                         f8 f8 f2 f2, f8, f3 x3), 40(s1) = 32(s1) = F; a plain run (writable shadow region)
     0x89f9c .. 0x89fc8  `beqz s6` (c >= 4096: falls through), UBSan's `andi a1,s6,7; bnez a1` (0x89fa0, 0x89fa4:
                         folded to 0 by c's alignment fact 2^4, from declared_pre's c mod 16 = 0, so the trap 0x8a1f8
                         is not taken), the inline check of c + 0x2c80 (passed by the shadow entry of c's live
                         block, AR's block shadow law), `lw a0,0(s7)` = c->n = |rc_seg rc| (rconf_enc, kept over the
                         frame call by the journal's block clause), `blez a0`
     0x8a0f8             c->n = 0: `sd zero,88(s1)`, to KX with dc_res = (0, tb) (dcl_go_nil)
     0x89fcc .. 0x89ffc  c->n > 0: the loop's registers and 24 / 48 / 80 / 88(s1), to KL at pass 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCall PaWalk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module DPMem := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.
Module DPZB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.

(* ---------- the program points (offsets from the listing's base) ---------- *)
(* 0x89f9c, `beqz s6`: the end of the frame set-up, where the plain run stops *)
Definition DC1_SET : Z := AF_reac_segconf_declared + 0x120.

(* ---------- the symbolic state at the entry ---------- *)
(* atoms 0 .. 31 the entry registers, 32 the shadow base SB, 33 the use-after-return flag cell, 34 the realigned
   stack pointer s1 = dc_sp1 sp0, 35 c->n *)
Definition dc1_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (-224) (-216) (-224) (-216) [].
Definition dc1_stk1 : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition dc1_slot : YP09.region := YP09.mkRegion (Some 34%nat) 24 120 24 120 [].
Definition dc1_regions0 : smem :=
  [dc1_stk0; dc1_stk1; dc1_slot; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33].
Definition dc1_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
(* c: a live heap block below the allocator's ceiling (at most 2^47 - 2^23), 16-aligned: the bound keeps its shadow
   inside the shadow band, the alignment folds UBSan's `andi a1,s6,7` (0x89fa0) to 0 *)
Definition dc1_cF : afact := mkAF 4096 (2 ^ 47 - 2 ^ 23) 4.
Definition dc1_atoms0 : list (nat * afact) :=
  [(2%nat, dc1_spF); (10%nat, dc1_cF); (32%nat, mkAF SB SB 0); (33%nat, mkAF 65536 6299648 2);
   (34%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (35%nat, mkAF 0 32 0)].
Definition dc1_alias0 : list (sv * sv) := [(SAlu ALU_AND (SOff 2 (-224)) (SLit (-32)), SOff 34 0)].
Definition dc1_ss0 : sstate :=
  mkSS AF_reac_segconf_declared sr_atoms dc1_regions0 None (mkFacts dc1_atoms0 [] dc1_alias0).
Definition dc1_Bx : sv := SOff 32 0.
Definition dc1_extra (uar sp nn : Z) : list word := map w64 [SB; uar; dc_sp1 sp; nn].
(* the regions the walk adds after the frame call, F the frame (atom 40 = a0 after the call), FL its flag cell (52),
   SB + F / 8 its shadow (53): the frame's tail with the flag pointer, its header, its shadow, c->n *)
Definition dc1_tail : YP09.region := YP09.mkRegion (Some 40%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 52 0))].
Definition dc1_head : YP09.region := YP09.mkRegion (Some 40%nat) 0 32 0 32 [].
Definition dc1_fsh : YP09.region := YP09.mkRegion (Some 53%nat) 0 16 0 16 [].
Definition dc1_cn : YP09.region := YP09.mkRegion (Some 10%nat) 0x2c80 0x2c84 0 0 [YP09.mkChunk 0x2c80 (CVal 4 (SOff 35 0))].
(* the shadow entry of c's block, which passes the inline check of c + 0x2c80 *)
Definition dc1_SH : list shent := [mkSHE 10 0 16616].

(* ---------- small facts ---------- *)
Lemma dc1_afact : forall E m v lo hi al,
  ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.
Lemma dc1_val_mem_of_sa : forall segs H mem a n v, sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma dc1_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (DPMem.le4 (Z_to_bv 64 v)) seg_spec.ZERO) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold DPMem.le4. rewrite unsigned_lit_small by lia.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth Z.of_nat];
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.mul_0_r, ?Z.shiftr_0_r; try reflexivity; f_equal; f_equal; lia.
Qed.
Lemma dc1_u32_at : forall (rd : reader) a bs k v, sa_bytes rd a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  seg_spec.u32_enc v (seg_spec.fldz k 4 bs) -> sa_val rd (a + k) 4 v.
Proof.
intros rd a bs k v H Hk Hl (Hv & E) j Hj.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (H (Z.to_nat k + j)%nat) by lia. f_equal.
rewrite <- (dc1_le4_byte v j Hv Hj). rewrite <- E. unfold seg_spec.fldz, seg_spec.fld.
change (Z.to_nat 4) with 4%nat. rewrite nth_firstn, nth_skipn.
replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
(* `not a3,s6` (xori -1, 0x89fe0) *)
Lemma dc1_not_w : forall x k, 0 <= x < 2 ^ 64 -> k mod 2 ^ 64 = 2 ^ 64 - 1 ->
  alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x k Hx Hk. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small x) by lia.
replace (bv_unsigned (Z_to_bv 64 k)) with 18446744073709551615
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Hk; reflexivity).
rewrite (DPZB.zb_lxor_ones x Hx). rewrite unsigned_lit_small by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma dc1_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* `blez a0` is `bge zero, a0` *)
Lemma dc1_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !dc1_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
Lemma dc1_sp1_bounds : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 240 <= dc_sp1 sp0 <= sp0 - 224 /\ dc_sp1 sp0 mod 32 = 0 /\ dc_sp1 sp0 = 32 * ((sp0 + -224) / 32).
Proof.
intros sp0 H. destruct (dc_sp1_facts sp0 H) as [H1 H2]. split; [lia|]. split; [exact H1|].
unfold dc_sp1. pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)). replace (sp0 + -224) with (sp0 - 224) by lia. lia.
Qed.

(* ---------- the walk's tactics (check_reply_s1.v's s1_norm / s1_add / s1_dj / s1_name_md) ---------- *)
Definition dc1_box (P : Prop) : Prop := P.
(* normalize a symbolic state *)
Ltac dc1_norm HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.
(* add a region to the symbolic state: its region_ok at the state's memory and its disjointness from the others *)
Ltac dc1_add HS r0 rok rdj :=
  let r := eval vm_compute in r0 in
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssv ?msv =>
  let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in
  assert (Rok : region_ok sg Ev (ms_mem msv) r); [rok | ];
  assert (Rdj : all_disjoint Ev r (ss_mem ssv)); [rdj | ];
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pi_add_region Ev ssv msv r HS eq_refl Rok Rdj) as HS3;
  clear HS Rok Rdj; rename HS3 into HS; dc1_norm HS end.
(* rewrite the atoms' values *)
Ltac dc1_U := repeat match goal with H : bv_unsigned (ew ?Ev ?k) = _ |- context [bv_unsigned (ew ?Ev ?k)] => rewrite H end.
Ltac dc1_dj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; dc1_U;
  unfold dc1_box, SB in *; repeat split; lia.
(* name the model after a run *)
Ltac dc1_name_md := try match goal with |- context [with_vm_backing ?a ?b ?c] =>
  let m := fresh "mdv" in set (m := with_vm_backing a b c) in *; clearbody m end.
(* make the first region based at atom n read-only *)
Ltac dc1_ro HS n :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs n in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; lia))) as HS3;
  clear HS; rename HS3 into HS; dc1_norm HS end.
Ltac dc1_inl := repeat (first [left; reflexivity | right]).
(* a register word is a 64-bit value *)
Ltac dc1_rng :=
  try unfold dc_a1; try unfold dc_a2; try unfold dc_a3;
  lazymatch goal with |- 0 <= bv_unsigned ?x < 2 ^ 64 =>
  let H := fresh "HRg" in pose proof (bv_unsigned_in_range 64 x) as H;
  change (bv_modulus 64) with (2 ^ 64) in H; exact H end.
(* the i-th region of the state, with its region_ok *)
Ltac dc1_rnth HS i HR :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth i rs got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict] in HR end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition dc1E (regs : bvmap 5 word) (uar nn : Z) : env := Eimg (Ereg regs (dc1_extra uar (spZ regs) nn)).
Lemma dc1_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
  ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof using.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.
Lemma dc1E_atoms : forall regs uar nn,
  ew (dc1E regs uar nn) 32 = w64 SB /\ ew (dc1E regs uar nn) 33 = w64 uar /\
  ew (dc1E regs uar nn) 34 = w64 (dc_sp1 (spZ regs)) /\ ew (dc1E regs uar nn) 35 = w64 nn.
Proof using.
intros regs uar nn. unfold dc1E, dc1_extra.
set (l := [SB; uar; dc_sp1 (spZ regs); nn]).
split; [exact (dc1_ex_w64 regs l 0 ltac:(unfold A_TEXT; lia) ltac:(subst l; cbn; lia))|].
split; [exact (dc1_ex_w64 regs l 1 ltac:(unfold A_TEXT; lia) ltac:(subst l; cbn; lia))|].
split; [exact (dc1_ex_w64 regs l 2 ltac:(unfold A_TEXT; lia) ltac:(subst l; cbn; lia))|].
exact (dc1_ex_w64 regs l 3 ltac:(unfold A_TEXT; lia) ltac:(subst l; cbn; lia)).
Qed.
(* an 8-byte field of a region, as the cuts' rdword *)
Lemma dc1_rd8 : forall E (W : world SEGS) msx n b cs lo hi wlo whi od e v,
  region_ok SEGS E (mrestrict (w_H W) msx) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) msx) (b + od) = Some v.
Proof using.
intros E W msx n b cs lo hi wlo whi od e v HR Hb Hin Hd Hv.
apply rdword_of_val_mem; [|exact Hv].
exact (field_of_region E _ n b cs lo hi wlo whi od 8%N e v HR Hb Hin Hd
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)).
Qed.
(* the thirteen saved registers in the prologue's stack region *)
Ltac dc1_saved_tac HRstk Ev2x AGx EEx U2x :=
  let j := fresh "j" in let r := fresh "r" in let Hj := fresh "Hj" in
  intros j r Hj;
  do 13 (destruct j as [|j];
    [ cbn [nth_error dc_saved] in Hj; injection Hj as <-;
      lazymatch goal with
      | |- rdword _ (?spx - 8 - 8 * Z.of_nat ?k) = Some (bv_unsigned (getr ?regsx (Z_to_bv 5 ?r0))) =>
        let off := eval cbv in (- 8 - 8 * Z.of_nat k) in
        let kr := eval cbv in (Z.to_nat r0) in
        replace (spx - 8 - 8 * Z.of_nat k) with (spx + off) by (cbn; lia);
        apply (dc1_rd8 Ev2x _ _ 2%nat spx _ _ _ _ _ off (SOff kr 0)
                 (bv_unsigned (getr regsx (Z_to_bv 5 r0))) HRstk U2x);
        [ dc1_inl
        | cbn [sv_denot]; rewrite Z.add_0_r, (AGx kr) by lia;
          rewrite (EEx kr (Z_to_bv 5 r0)) by (vm_compute; reflexivity); reflexivity
        | dc1_rng ]
      end
    | ]);
  cbn in Hj; destruct j; discriminate.

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* ---------- the journal with no footprint, and what it keeps ---------- *)
(* a journal with the empty footprint is one with any footprint: every clause that the footprint weakens holds *)
Lemma dc1_widen : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof using.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & K1 & K2 & K3 & K4 & K5 & H14 & H15 & H16 & H17).
assert (Hnil : forall r : Z * Z, In r [] -> In r FP) by (intros r Hr; destruct Hr).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact (aos_step_mono [] FP md md' (sink_open_mono [] FP Hnil) H5)|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
split; [intros a Ha Hs _; exact (K1 a Ha Hs (inFP_nil a))|].
split; [intros p n i Hp Hp' Hi _; exact (K2 p n i Hp Hp' Hi (inFP_nil (p + i)))|].
split; [intros a Hi Ho He Hf; exact (K3 a Hi Ho He (fp_spares_mono [] FP a Hnil Hf))|].
split; [intros cid pos a Hc Ha _; exact (K4 cid pos a Hc Ha (inFP_nil a))|].
split; [intros p n i Hp Hp' Hi; exfalso; exact (inFP_nil _ (K5 p n i Hp Hp' Hi))|].
split; [exact H14|]. split; [exact H15|]. split; [exact H16 | exact H17].
Qed.
(* the bytes of an entry block the journal keeps *)
Lemma dc1_blk_kept : forall STK sp0 ly S W mem md own ly' S' mem' md' k b m q n,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W mem' md' k ->
  ablocks B ly' S' = ablocks B ly S -> In (b, m) (ablocks B ly S) -> b <= q -> q + n <= b + m -> 0 <= n ->
  forall j, 0 <= j < n -> rdW W mem' (q + j) = rdW W mem (q + j).
Proof using.
intros STK sp0 ly S W mem md own ly' S' mem' md' k b m q n HJ Eab Hin Hb Hq Hn j Hj.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
replace (q + j) with (b + (q + j - b)) by lia.
apply (K2 b m); [exact Hin | rewrite Eab; exact Hin | lia | apply inFP_nil].
Qed.
(* c->n at a state after the entry with the entry's blocks: rconf_enc's field, kept *)
Lemma dc1_n_kept : forall c ly' S' mem' md' k own,
  dc_pre B DC_STK RLO RHI GOTW GUARD c ->
  ajournal SEGS B DC_STK (dc_sp0 c) [] (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) own ly' S' (x_W c) mem' md' k ->
  ablocks B ly' S' = ablocks B (x_ly c) (x_S c) ->
  sa_val (rdW (x_W c) mem') (x_c c + DC_RC_N) 4 (dc_nn c) /\ (length (dc_segs c) <= 32)%nat.
Proof using.
intros c ly' S' mem' md' k own HP HJ Eab.
pose proof HP as [_ _ _ _ _ _ _ _ _ _ HDP _ _].
destruct HDP as (_ & _ & (bs & Hbs & Hlen & Hle32 & _ & Hn & _) & (pb & nb & Hin & Hp1 & Hp2) & _).
split; [|exact Hle32].
unfold seg_spec.SEG_C_SIZE in Hlen, Hp2.
pose proof (dc1_u32_at _ _ bs seg_spec.RC_N _ Hbs ltac:(unfold seg_spec.RC_N; lia)
  ltac:(unfold seg_spec.RC_N; lia) Hn) as HV0.
unfold seg_spec.RC_N in HV0.
intros kk Hk. unfold DC_RC_N, dc_nn, dc_segs.
rewrite (dc1_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ pb nb (x_c c + 0x2c80) 4 HJ Eab Hin ltac:(lia) ltac:(lia) ltac:(lia)
  (Z.of_nat kk) ltac:(lia)).
exact (HV0 kk Hk).
Qed.
(* the table and its count cell at a state after the entry with the entry's blocks: vtab_pre's, kept *)
Lemma dc1_tab_kept : forall c ly' S' mem' md' k own,
  dc_pre B DC_STK RLO RHI GOTW GUARD c ->
  ajournal SEGS B DC_STK (dc_sp0 c) [] (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) own ly' S' (x_W c) mem' md' k ->
  ablocks B ly' S' = ablocks B (x_ly c) (x_S c) ->
  dc_tab c (x_tb c) (x_W c) mem'.
Proof using.
intros c ly' S' mem' md' k own HP HJ Eab.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _].
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & (bs & Hbs & Henc) & Hmax & (b & m & Hin & Hb1 & Hb2) & _ & _ & _ & _ & HV & HDST & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & _ & K4 & _).
unfold seg_spec.RVLAN_SIZE in Hb2.
pose proof (proj1 Henc) as Hlb.
split; [|split; [|split; [lia | lia]]].
- exists bs. split; [|exact Henc].
  intros i Hi. rewrite <- (Hbs i Hi).
  exact (dc1_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ b m (x_tab c) (Z.of_nat (length bs)) HJ Eab Hin ltac:(lia)
    ltac:(rewrite Hlb; lia) ltac:(lia) (Z.of_nat i) ltac:(lia)).
- intros kk Hk. rewrite <- (HV kk Hk).
  destruct HDST as [((cid & pos & Hf & Hcid & Hf1 & Hf2) & _) | [((b2 & m2 & Hin2 & Hq1 & Hq2) & _) | (Hs1 & Hs2 & _ & _)]].
  + apply (K4 cid pos); [exact Hf | left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil].
  + exact (dc1_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ b2 m2 (x_n c) 4 HJ Eab Hin2 Hq1 Hq2 ltac:(lia) (Z.of_nat kk) ltac:(lia)).
  + pose proof asan_consts as (C1 & _). unfold dc_sp0 in *.
    apply K1; [lia | lia | apply inFP_nil].
Qed.

(* ---------- the entry seed ---------- *)
Lemma dc1_entry : forall ly S W (regs : bvmap 5 word) mem md ch (c nn : Z),
  afn_pre SEGS B DC_STK ly S W regs mem md ch ->
  getr regs 10 = w64 c -> 4096 <= c <= 2 ^ 47 - 2 ^ 23 -> c mod 16 = 0 -> 0 <= nn <= 32 ->
  st_ok_pi SEGS VAL (dc1E regs (as_uar_cell B) nn) dc1_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_declared)) mem (seg_rom SEGS))).
Proof using TL TLF.
intros ly S W regs mem md ch c nn HPRE H10 Hc Hc16 Hnn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : DC_STK = 12592) by reflexivity.
destruct (al_const _ _ (AR_laws_ok SEGS B) ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kgu.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 1 ltac:(lia)) as HguR. pose proof (palf_sep B TLF) as Hsep.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 1)) as R1.
pose proof (pa_val_range (A_OBJ 12)) as R12.
unfold kImgEnd in *.
rewrite restrict_mkst_fx.
set (sp := spZ regs) in *.
destruct (dc1_sp1_bounds sp Hal16) as (Hs1b & Hs1a & Hs1e).
destruct (dc1E_atoms regs (as_uar_cell B) nn) as (E32 & E33 & E34 & E35). fold sp in E34.
set (E := dc1E regs (as_uar_cell B) nn) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E2 : ew E 2 = Z_to_bv 64 sp) by (rewrite (EE 2%nat 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (Hwr : forall o, sp - 240 <= o < sp -> writable_at SEGS (mrestrict (w_H W) mem) o)
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia).
assert (Rs1 : 2 ^ 46 <= dc_sp1 sp) by lia.
unfold dc1_ss0. apply pa_entry_st_ok_full.
- unfold dc1E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dc1_regions0, dc1_stk0, dc1_stk1, dc1_slot, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply Hwr. lia.
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply Hwr. lia.
  + rewrite (VB 34%nat (dc_sp1 sp) E34) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply Hwr. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgu).
  + rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold dc1_regions0, dc1_stk0, dc1_stk1, dc1_slot, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 34%nat (dc_sp1 sp) E34) by lia. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia.
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  cbn [zseps zseps_from fst snd] in Hsep.
  clear - Hsep Hs1b Hslo Hstk0 Hceil C1 HcellR HgotR HguR Huar HST. unfold ASAN_CEIL in *.
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [dc1_atoms0 f_atoms atoms_ok]. unfold dc1_spF, dc1_cF.
    split; [apply (dc1_afact E 2 sp); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hal16 | lia]|].
    split; [apply (dc1_afact E 10 c); [exact E10 | lia | lia | change (2 ^ 4) with 16; exact Hc16 | lia]|].
    split; [apply (dc1_afact E 32 SB); [exact E32 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (dc1_afact E 33 (as_uar_cell B)); [exact E33 | lia | lia | change (2 ^ 2) with 4; exact Huar4 | lia]|].
    split; [apply (dc1_afact E 34 (dc_sp1 sp)); [exact E34 | lia | lia | change (2 ^ 5) with 32; exact Hs1a | lia]|].
    split; [apply (dc1_afact E 35 nn); [exact E35 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    exact I.
  + cbn [dc1_alias0 f_alias alias_ok]. split; [|exact I].
    rewrite (denot_and_m32 E 2 sp (-224) E2) by lia. rewrite sv_denot_SOff0, E34. unfold w64. f_equal. lia.
Qed.

(* ---------- the segment ---------- *)
Lemma dc_S1 : dc_S1P B DC_STK RLO RHI GOTW GUARD.
Proof using TL TLF ML SM1 SMP LAWS errno_low RUN RUNTO RUNTOP BR.
intros c HPRE HKX HKL.
pose proof HPRE as [HAFN HROD H10 HC64 H11 HT64 H12 HM64 H13 HN64 HDP HROOM HNEV].
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HDP as (Hc0 & Hc16 & HRC & (pb & nb & Hin & Hp1 & Hp2) & HAC & HVT & HD1 & HD2 & HSSP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
assert (HST : DC_STK = 12592) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hpb16 & Hpb4096 & Hpbc & Hpbapp & Hpbpres & _ & Hnbr).
assert (Hreq : req_size nb = nb) by (unfold req_size; destruct (Z.eqb_spec nb 0); [unfold seg_spec.SEG_C_SIZE in Hp2; lia | reflexivity]).
rewrite Hreq in Hpbc, Hpbapp, Hpbpres.
unfold seg_spec.SEG_C_SIZE in Hp2.
assert (Hc : 4096 <= x_c c <= 2 ^ 47 - 2 ^ 23) by lia.
set (nn := dc_nn c).
assert (Hnnd : nn = Z.of_nat (length (dc_segs c))) by reflexivity.
assert (Hnn : 0 <= nn <= 32).
{ destruct HRC as (bs & _ & _ & Hle32 & _). unfold nn, dc_nn, dc_segs. lia. }
set (sp0 := spZ (x_regs c)) in *.
destruct (dc1_sp1_bounds sp0 Hal16) as (Hs1b & Hs1a & Hs1e).
set (s1 := dc_sp1 sp0) in *.
pose proof (dc1_entry _ _ _ _ _ _ _ _ nn HAFN H10 Hc Hc16 Hnn) as HS.
pose proof (ajournal_init SEGS B DC_STK [] _ _ _ _ _ _ _ HAFN) as HJ.
destruct (dc1E_atoms (x_regs c) (as_uar_cell B) nn) as (E32 & E33 & E34 & E35). fold sp0 s1 in E34.
assert (HEI : img_env VAL A_LIM (dc1E (x_regs c) (as_uar_cell B) nn)) by (unfold dc1E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (dc1E (x_regs c) (as_uar_cell B) nn) n = getr (x_regs c) r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
remember (dc1E (x_regs c) (as_uar_cell B) nn) as E eqn:HE. clear HE.
assert (SHOK : sh_ok SEGS dc1_Bx [] E (mrestrict (w_H (x_W c)) (x_mem c))) by apply Forall_nil.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U34 : bv_unsigned (ew E 34) = s1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_declared)) with (Z_to_bv 64 (BASE + AF_reac_segconf_declared)).
(* 0x89e7c .. 0x89ef0: the prologue, the spills, the two GOT loads, `beqz a2` (the flag is 1), to the frame call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; try rewrite HST; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; try rewrite HST; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 34%nat) (d := s1 - sp0);
    [reflexivity | rewrite U34; lia | cbn; try rewrite HST; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG. dc1_name_md.
(* 0x89ef4: __asan_stack_malloc_1(96) at s1 = sp0 + (s1 - sp0) *)
pose proof (proj1 HJ) as HAR1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1. rewrite (pal_cell B TL) in Kcell1.
apply (val_mem_of_rdword SEGS) in Kgot1. apply (val_mem_of_rdword SEGS) in Kcell1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
assert (Hsm : pa_sigma SS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1)
  by exact (palf_sm B TLF 1 ltac:(right; left; reflexivity)).
rewrite Hsm.
pose proof (count_cid_le_length 1 (frames (x_S c))) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 (SM1 fx) ltac:(lia) (x_W c) (ms_regs msX) (ms_mem msX)
    DC_STK sp0 [] (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [] (x_ly c) (x_S c) _ 0 (s1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E34. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (s1 - sp0) with ((2 * (s1 / 32) - sp0 / 16) * 16)
      by (pose proof (Z.div_mod s1 32 ltac:(lia)); pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - lia.
  - rewrite HST. unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold AF_reac_segconf_declared; lia | reflexivity].
  - change (fs_frames 1) with 8192. unfold sa_room in HROOM. lia. }
cbv beta. clear R2 R3 R4 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HK & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot2. rewrite (pal_cell B TL) in Kcell2.
apply (val_mem_of_rdword SEGS) in Kgot2. apply (val_mem_of_rdword SEGS) in Kcell2.
(* the state after the call: the prologue's stack stores, the spills, the shadow GOT word and cell *)
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | try rewrite HST; lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | try rewrite HST; lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact U34 | lia | try rewrite HST; lia | lia | lia | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
      [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot1 | exact Kgot2 | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
      [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell1 | exact Kcell2 | lia]. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ev1 := havoc E 36 (map (getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (apply img_env_havoc; [exact HEI | rewrite length_map; unfold A_TEXT; cbn; lia]).
(* the frame F = frame_addr ly 1 fpos, its flag cell FL, its shadow SB + F / 8; c's block *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFoff.
assert (Hin2 : In (pb, nb) (ablocks B (x_ly c) S2)) by (rewrite Eab; exact Hin).
pose proof (sep_block_frame SEGS B LAWS (x_ly c) S2 (x_W c) mem2 md2 pb nb 1 fpos HAR2 Hin2 Hfin2) as HdCF.
pose proof (blk_off_imgP B (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) pb nb HAR Hin) as Hcoff.
rewrite Hreq in HdCF, Hcoff.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
set (F := frame_addr (x_ly c) 1 fpos) in *. set (FL := flag_addr (x_ly c) 1 fpos) in *.
unfold zdisjoint in HdCF. cbn [fst snd] in HdCF.
assert (HFLb : 4096 <= FL < alloc_ceiling) by (clear - HFLapp HFLce; unfold in_app in HFLapp; lia).
assert (ZONES : dc1_box ((F + 128 <= 0x10000 \/ (0x602000 <= F /\ F + 128 <= 0x7fff7000) \/ 0x10007fff8000 <= F) /\
  (pb + nb <= 0x10000 \/ (0x602000 <= pb /\ pb + nb <= 0x7fff7000) \/ 0x10007fff8000 <= pb) /\
  (pb + nb <= F \/ F + 128 <= pb))).
{ unfold dc1_box. clear - HFoff HFapp Hcoff Hpbapp HdCF HF4096 Hpb4096.
  unfold off_img, in_app, kImgEnd, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
clear HFoff HFapp Hcoff HdCF HFLapp.
assert (RF : 0 <= F < 2 ^ 64) by lia. assert (RFL : 0 <= FL < 2 ^ 64) by lia.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (E40a : ew Ev1 40 = Z_to_bv 64 F).
{ subst Ev1. unfold havoc, CLOB. cbn [ew map nth Nat.ltb Nat.leb Nat.sub]. exact Ha0. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 52 Ev1 ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc Ev1 52 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Ev2 eqn:HEv2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HEv2; apply img_env_havoc; [exact HEI1 | unfold A_TEXT; cbn; lia]).
assert (AG : forall k, (k < 36)%nat -> ew Ev2 k = ew E k)
  by (intros k Hk; rewrite HEv2, ew_havoc_old by lia; subst Ev1; apply ew_havoc_old; lia).
assert (E40 : ew Ev2 40 = Z_to_bv 64 F) by (rewrite HEv2, ew_havoc_old by lia; exact E40a).
assert (E52 : ew Ev2 52 = Z_to_bv 64 FL)
  by (rewrite HEv2; exact (ew_havoc_new Ev1 52 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E53 : ew Ev2 53 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HEv2; exact (ew_havoc_new Ev1 52 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HEv2 E40a.
assert (E32' : ew Ev2 32 = Z_to_bv 64 SB) by (rewrite AG by lia; exact E32).
assert (E35' : ew Ev2 35 = Z_to_bv 64 nn) by (rewrite AG by lia; exact E35).
assert (E10' : ew Ev2 10 = Z_to_bv 64 (x_c c)) by (rewrite AG, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
assert (U40 : bv_unsigned (ew Ev2 40) = F) by (rewrite E40; apply unsigned_lit_small; lia).
assert (U52 : bv_unsigned (ew Ev2 52) = FL) by (rewrite E52; apply unsigned_lit_small; lia).
assert (U53 : bv_unsigned (ew Ev2 53) = SB + F / 8) by (rewrite E53; apply unsigned_lit_small; unfold SB; lia).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG by lia; exact Usp).
assert (U34b : bv_unsigned (ew Ev2 34) = s1) by (rewrite AG by lia; exact U34).
assert (U10 : bv_unsigned (ew Ev2 10) = x_c c) by (rewrite E10'; apply unsigned_lit_small; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in HcellR, HgotR.
assert (U241 : bv_unsigned (ew Ev2 241) = VAL (A_OBJ 0)) by exact (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)).
assert (U253 : bv_unsigned (ew Ev2 253) = VAL (A_OBJ 12)) by exact (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)).
(* facts of F and of its shadow, and the shadow alias of F *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 40 (HPTR 5) HS
    ltac:(apply (dc1_afact Ev 40 F); [exact E40 | lia | lia | change (2 ^ 5) with 32; exact HFal | lia])) as HS3 end.
clear HS. rename HS3 into HS.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HFd8 : F / 8 = 4 * (F / 32))
  by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 53 (mkAF (SB + 512) (SB + 2 ^ 44) 2) HS
    ltac:(apply (dc1_afact Ev 53 (SB + F / 8)); [exact E53 | unfold SB; lia | unfold SB; lia
          | change (2 ^ 2) with 4; rewrite HFd8; unfold SB;
            replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 40 32 53 F SB E40 RF E32' E53)) as HS3 end.
clear HS. rename HS3 into HS. dc1_norm HS.
(* the values the added regions hold at the state after the call *)
assert (VFL : val_mem SEGS (mrestrict (w_H (x_W c)) mem2) (F + 120) 8 FL).
{ replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
destruct (dc1_n_kept c (x_ly c) S2 mem2 md2 0 [(1, fpos)] HPRE HJ2 Eab) as [VN _].
apply dc1_val_mem_of_sa in VN. unfold DC_RC_N in VN. fold nn in VN.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
(* the frame's tail with the flag pointer at 120, its header and its shadow (writable for the set-up's stores),
   c->n *)
dc1_add HS dc1_tail
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U40; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val SEGS _ _ F 120 8 (SOff 52 0) FL);
          [cbn [sv_denot]; rewrite U52, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact VFL])
  ltac:(dc1_dj).
dc1_add HS dc1_head
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U40; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(dc1_dj).
dc1_add HS dc1_fsh
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U53; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSpres o ltac:(lia))))
  ltac:(dc1_dj).
dc1_add HS dc1_cn
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U10; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val SEGS _ _ (x_c c) 0x2c80 4 (SOff 35 0) nn);
          [cbn [sv_denot]; rewrite E35', Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact VN])
  ltac:(dc1_dj).
(* 0x89ef8 .. 0x89f98: `bnez a0` taken (F >= 4096), 112(s1) = F, the frame header, F's shadow, 40(s1) = 32(s1) = F;
   a plain run (the frame's shadow is a writable region) to `beqz s6` at 0x89f9c *)
paj_run_to_sh RUNTOP HS HJ2 DC1_SET.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 53%nat) (b := SB + F / 8); [reflexivity | exact U53 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia. }
  eapply awr_ok_cons_gen with (n := 40%nat) (b := F); [reflexivity | exact U40 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 34%nat) (d := s1 - sp0);
    [reflexivity | rewrite U34b; lia | cbn; try rewrite HST; lia | cbn; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG. dc1_name_md.
(* 0x89f9c: the frame set-up done *)
(* the frame's shadow and header read-only for the token run (a writable window that the facts do not keep off the
   shadow span breaks sh_static_ok's cells_safe_b; the rest of the stretch writes neither) *)
dc1_ro HS 53%nat. dc1_ro HS 40%nat.
(* the shadow entry of c's block: AR's block shadow law at the current state *)
pose proof (proj1 HJ2) as HAR3.
assert (UBx : U Ev2 dc1_Bx = SHADOW_OFF) by (unfold dc1_Bx; rewrite (U_atom Ev2 32 SB E32') by (unfold SB; lia); reflexivity).
assert (UC : U Ev2 (SOff 10 0) = x_c c) by (apply U_atom; [exact E10' | lia]).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H (x_W c)) ?ms3) =>
  assert (SHOK : sh_ok SEGS dc1_Bx dc1_SH Ev2 (mrestrict (w_H (x_W c)) (ms_mem ms3)));
  [ unfold sh_ok, dc1_SH; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H (x_W c)) (ms_mem ms3) Ev2 dc1_Bx 10%nat (x_c c) 16616 (x_c c) 0 16616
      (range_addressable_of_block SEGS B LAWS _ _ _ _ _ pb nb (x_c c) 16616 HAR3 Hin2 ltac:(lia) ltac:(rewrite Hreq; lia))
      UBx UC); [lia | lia | intros x Hx; unfold dc1_box in ZONES; unfold SHADOW_OFF; lia]
  | ] end.
(* 0x89f9c .. 0x89fc8: `beqz s6` (c >= 4096), UBSan's `andi a1,s6,7; bnez a1` (0 by c's alignment fact), the inline
   check of c + 0x2c80 (the shadow entry), c->n, to `blez a0` *)
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 34%nat) (d := s1 - sp0);
    [reflexivity | rewrite U34b; lia | cbn; try rewrite HST; lia | cbn; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
dc1_name_md.
(* the atoms the two cuts read back: the registers the frame part keeps, the three spilled arguments *)
assert (F2 : ew Ev2 2 = w64 sp0) by (unfold w64; rewrite <- U2; symmetry; apply Z_to_bv_bv_unsigned).
assert (F34 : ew Ev2 34 = w64 s1) by (rewrite AG by lia; exact E34).
assert (F3 : ew Ev2 3 = w64 (as_gp B)) by (rewrite AG, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp).
assert (F4 : ew Ev2 4 = w64 (as_tp B)) by (rewrite AG, (EE 4%nat 4%bv eq_refl) by lia; exact Htp).
assert (F11 : ew Ev2 11 = getr (x_regs c) 11) by (rewrite AG by lia; exact (EE 11%nat 11%bv eq_refl)).
assert (F12 : ew Ev2 12 = getr (x_regs c) 12) by (rewrite AG by lia; exact (EE 12%nat 12%bv eq_refl)).
assert (F13 : ew Ev2 13 = getr (x_regs c) 13) by (rewrite AG by lia; exact (EE 13%nat 13%bv eq_refl)).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* `blez a0` taken: c->n <= 0, so rc_seg is empty; 0x8a0f8 `sd zero,88(s1)`, to KX *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
  rewrite (dc1_bge0 Ev2 35 nn E35' ltac:(lia)) in Hbr. apply Z.leb_le in Hbr.
  assert (Hnil : rc_seg (x_rc c) = []).
  { assert (Hl : (length (dc_segs c) = 0)%nat) by lia.
    unfold dc_segs in Hl. destruct (rc_seg (x_rc c)) as [|q l]; [reflexivity | cbn in Hl; lia]. }
  assert (Hres : dc_res (dc_setpos c fpos) = (0, x_tb c)) by exact (dcl_go_nil (x_rc c) (x_tb c) (x_max c) Hnil).
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan DC_KX.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
    eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
    eapply awr_ok_cons_stack_off with (n := 34%nat) (d := s1 - sp0);
      [reflexivity | rewrite U34b; lia | cbn; try rewrite HST; lia | cbn; lia |].
    do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  dc1_name_md.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
  dc1_rnth HS 3%nat HRtail. dc1_rnth HS 5%nat HRstk. dc1_rnth HS 6%nat HRslot.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (27%bv : bv 5) P27.
  pose proof (dc1_tab_kept c (x_ly c) S2 (ms_mem ms3) _ 0 [(1, fpos)] HPRE HJ2 Eab) as HTAB.
  assert (V32 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 32) = Some F)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 32 (SOff 40 0) F HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U40; reflexivity) ltac:(lia))).
  assert (V40 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 40) = Some F)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 40 (SOff 40 0) F HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U40; reflexivity) ltac:(lia))).
  assert (V56 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 56) = Some (dc_a1 c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 56 (SOff 11 0) (dc_a1 c) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, F11; reflexivity) ltac:(dc1_rng))).
  assert (V64 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 64) = Some (dc_a2 c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 64 (SOff 12 0) (dc_a2 c) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, F12; reflexivity) ltac:(dc1_rng))).
  assert (V72 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 72) = Some (dc_a3 c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 72 (SOff 13 0) (dc_a3 c) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, F13; reflexivity) ltac:(dc1_rng))).
  assert (VFLG : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (F + 120) = Some FL)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 40%nat F _ 120 128 0 0 120 (SOff 52 0) FL HRtail U40
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U52; reflexivity) ltac:(lia))).
  assert (V88 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 88) = Some 0)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 88 (SLit 0) 0 HRslot U34b
          ltac:(dc1_inl) ltac:(reflexivity) ltac:(lia))).
  pmkst HS.
  apply (HKX fpos (x_ly c) S2 (x_W c) (ms_regs ms3) (ms_mem ms3) _).
  unfold INV_KX.
  split.
  { constructor.
    - eapply dc1_widen; exact HJ2.
    - rewrite P2; exact F34.
    - rewrite P3; exact F3.
    - rewrite P4; exact F4.
    - rewrite P8; exact F2.
    - rewrite P9; exact F34.
    - rewrite P27; exact E53.
    - dc1_saved_tac HRstk Ev2 AG EE U2.
    - exact V32.
    - exact V40.
    - exact V56.
    - exact V64.
    - exact V72.
    - exact VFLG. }
  split; [constructor; [rewrite Eab; apply Permutation_refl | reflexivity | exists fS2; exact ES2]|].
  rewrite Hres. cbn [fst snd].
  split; [exact HTAB|]. split; [lia|]. rewrite Z.mod_0_l by lia. exact V88.
- (* `blez a0` not taken: c->n > 0; 0x89fcc .. 0x89ffc, the loop's registers and slots, to KL at pass 0 *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
  rewrite (dc1_bge0 Ev2 35 nn E35' ltac:(lia)) in Hbr. apply Z.leb_gt in Hbr.
  assert (Hpos : (0 < length (dc_segs c))%nat) by lia.
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan DC_KL.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]).
    eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
    eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; try rewrite HST; lia | cbn; lia |].
    eapply awr_ok_cons_stack_off with (n := 34%nat) (d := s1 - sp0);
      [reflexivity | rewrite U34b; lia | cbn; try rewrite HST; lia | cbn; lia |].
    do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  dc1_name_md.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
  dc1_rnth HS 3%nat HRtail. dc1_rnth HS 5%nat HRstk. dc1_rnth HS 6%nat HRslot.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (27%bv : bv 5) P27.
  prreg HS (13%bv : bv 5) P13. prreg HS (14%bv : bv 5) P14. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26.
  assert (P20 : getr (ms_regs ms3) 20 = w64 (SB + (x_c c + DC_RC_N) / 8)).
  { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hw ?msx) =>
      pose proof (st_ok_pi_restrict_reg Hw Ex ssx msx (20%bv : bv 5) HS) as Q20;
      let e := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in
      change (sr_get (ss_regs ssx) (20%bv : bv 5)) with e in Q20;
      cbn [ms_regs restrict mkst] in Q20; rewrite Q20; unfold DC_RC_N;
      exact (denot_shx Ex 10 32 11392 (x_c c) SB E10' E32' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) end. }
  pose proof (dc1_tab_kept c (x_ly c) S2 (ms_mem ms3) _ 0 [(1, fpos)] HPRE HJ2 Eab) as HTAB.
  assert (V32 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 32) = Some F)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 32 (SOff 40 0) F HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U40; reflexivity) ltac:(lia))).
  assert (V40 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 40) = Some F)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 40 (SOff 40 0) F HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U40; reflexivity) ltac:(lia))).
  assert (V56 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 56) = Some (dc_a1 c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 56 (SOff 11 0) (dc_a1 c) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, F11; reflexivity) ltac:(dc1_rng))).
  assert (V64 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 64) = Some (dc_a2 c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 64 (SOff 12 0) (dc_a2 c) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, F12; reflexivity) ltac:(dc1_rng))).
  assert (V72 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 72) = Some (dc_a3 c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 72 (SOff 13 0) (dc_a3 c) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, F13; reflexivity) ltac:(dc1_rng))).
  assert (VFLG : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (F + 120) = Some FL)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 40%nat F _ 120 128 0 0 120 (SOff 52 0) FL HRtail U40
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U52; reflexivity) ltac:(lia))).
  assert (V48 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 48) = Some (SB + F / 8))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 48 (SOff 53 0) (SB + F / 8) HRslot U34b
          ltac:(dc1_inl) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, U53; reflexivity) ltac:(unfold SB; lia))).
  assert (V80 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 80) = Some (2 ^ 64 - 1 - x_c c))
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 80
          (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (2 ^ 64 - 1 - x_c c) HRslot U34b ltac:(dc1_inl)
          ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10'; apply dc1_not_w; [lia | reflexivity])
          ltac:(lia))).
  assert (V88 : rdword (aview SEGS (w_H (x_W c)) (ms_mem ms3)) (s1 + 88) = Some 0)
    by (apply (dc1_rd8 Ev2 (x_W c) (ms_mem ms3) 34%nat s1 _ 24 120 24 120 88 (SLit 0) 0 HRslot U34b
          ltac:(dc1_inl) ltac:(reflexivity) ltac:(lia))).
  assert (L24 : getr (ms_regs ms3) 24 = w64 (Z.of_nat 0)) by (rewrite P24; reflexivity).
  assert (L22 : getr (ms_regs ms3) 22 = w64 (x_c c + 356 * Z.of_nat 0))
    by (rewrite P22, E10'; unfold w64; f_equal; lia).
  assert (L25 : getr (ms_regs ms3) 25 = w64 (x_c c + 356 * Z.of_nat 0 + DC_IGN))
    by (rewrite P25, U10; unfold w64, DC_IGN; f_equal; lia).
  assert (L23 : getr (ms_regs ms3) 23 = w64 (x_c c + DC_RC_N))
    by (rewrite P23, U10; unfold w64, DC_RC_N; f_equal; lia).
  assert (L19 : getr (ms_regs ms3) 19 = w64 (F + 32)) by (rewrite P19, U40; reflexivity).
  assert (L26 : getr (ms_regs ms3) 26 = w64 (F + 64)) by (rewrite P26, U40; reflexivity).
  assert (L21 : getr (ms_regs ms3) 21 = w64 SB) by (rewrite P21; exact E32').
  assert (L18 : getr (ms_regs ms3) 18 = w64 (356 * Z.of_nat 0))
    by (rewrite P18; unfold w64; f_equal; lia).
  assert (L13 : getr (ms_regs ms3) 13 = w64 (2 ^ 64 - 1 - x_c c))
    by (rewrite P13, E10'; unfold w64; apply dc1_not_w; [lia | reflexivity]).
  assert (L14 : getr (ms_regs ms3) 14 = w64 32) by (rewrite P14; reflexivity).
  pmkst HS.
  apply (HKL fpos (x_tb c) 0 (x_ly c) S2 (x_W c) (ms_regs ms3) (ms_mem ms3) _).
  unfold INV_KL.
  (* the loop's cut carries c, F and SB through the projections of dc_setpos (conversion) *)
  split.
  { constructor.
    - eapply dc1_widen; exact HJ2.
    - rewrite P2; exact F34.
    - rewrite P3; exact F3.
    - rewrite P4; exact F4.
    - rewrite P8; exact F2.
    - rewrite P9; exact F34.
    - rewrite P27; exact E53.
    - dc1_saved_tac HRstk Ev2 AG EE U2.
    - exact V32.
    - exact V40.
    - exact V56.
    - exact V64.
    - exact V72.
    - exact VFLG. }
  split; [constructor; [rewrite Eab; apply Permutation_refl | reflexivity | exists fS2; exact ES2]|].
  split; [exact HTAB|].
  split; [exact Hpos|].
  split; [split; [reflexivity | cbn [Z.of_nat]; lia]|].
  split.
  { unfold dc_lregs.
    split; [exact L24|]. split; [exact L22|]. split; [exact L25|]. split; [exact L23|].
    split; [exact P20|]. split; [exact L19|]. split; [exact L26|]. split; [exact L21 | exact L18]. }
  split; [unfold dc_aregs; split; [exact L13 | exact L14]|].
  unfold dc_lslots. split; [exact V48|]. split; [exact V80 | exact V88].
Qed.

End e.
End f.
End d.
