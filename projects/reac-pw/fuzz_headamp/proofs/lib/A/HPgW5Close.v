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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 256 of its 291 lines of code are new or changed and 255 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Close.v at dc0c32440025 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (CL 0x82484 -> LATCH 0x82528), registers (s6 / s7 / s2 for role's
   s4 / s5 / s7) and real-frame cells (at R+0xe0, first R+0x110, the cursor R+0x100, &has_params R+0x88,
   &params_struct R+0x70 for role's R+0xa0 / 0xd0 / 0xc8 / 0x50 / 0x40); the real frame is 0x1e0 bytes; rm_ / rl_
   become rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v, with its module paths, addresses and numbers changed; 45 of its 287 lines of code are new or changed and 49 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Close.v at 164759458cd; module paths changed, rm_ -> hm_, rl_ -> hd_, the walk moved to image A of fuzz_headamp (CL 0x82a14 -> LATCH 0x82ac0, the cells R+0xc0 / 0xe8 / 0x78 / 0x58, the pp->len check in its `beqz; j` form), the cursor's frame-cell store replaced by headamp's `mv s11,s9` on both arms (s11 joins the clobber list, the post gives s11 = the cursor, the real-frame region is read-only and the write set has no frame cell), R + 0x1e0 <= sp0, the AR_laws Section hypothesis replaced by the kernel theorem YG0q.AR_laws_ok. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses from the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the params Struct's close,
   CL 0x82a14 -> LATCH 0x82ac0, in LLVMFuzzerTestOneInput (pod.h:434-437). Proves no function (kind: segment lemma).

   THE CODE
     0x82a14  lbu a0,0(s4); beqz a0,8; j 0x83b20   the check of the 8-byte load of pp->len (s4 = (pp+0x4000)>>3 + K)
     0x82a20  ld a0,0xc0(s1); add a0,s11,a0          a0 = pp + at (s11 = pp inside the pod loop)
     0x82a28-0x82a38  the check of the first byte of the 4-byte store at pp + at (slow block 0x82b88); a1 = len
     0x82a3c-0x82a4c  the check of its last byte pp + at + 3 (slow block 0x82b94)
     0x82a50  ld a2,0xc0(s1); subw a1,a1,a2; addi a1,a1,-8      len - at - 8
     0x82a5c-0x82a74  the four `sb` of pod_patch32(pp, at, len - at - 8)
     0x82a78  ld a0,0xe8(s1) (first); 0x82a7c beqz a0 -> 0x82abc
     0x82a80-0x82a9c  first: the check of pp + 0x400c (slow block 0x82c48, back to 0x82a94), 0x82a94 mv s11,s9
              (the cursor back into s11), has_params := 1
     0x82aa0-0x82ab8  first: the check of pp + 0x4010 (slow block 0x82c58), params_struct := 1, j 0x82ac0
     0x82abc  not first: mv s11,s9
   Every check is on pp's bytes, covered by the shadow entries (27, 0x4000, 0x4018) and (33, 0, 16) of
   w5_shent_blk; the error paths are not reached. first is 0 or 1 by the start state; the walk takes the two
   values as two runs, so `beqz` is decided. The piece writes no real-frame cell: at the end s11 holds the cursor
   (s9, unchanged), which is where the latch cut keeps it. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgMem HPgW5Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the start state at 0x82a14: atoms 33 = pp + atv, 34 = atv, 35 = len ---- *)
Definition cl_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((20%bv : bv 5), w5_sh 27 0x4000); ((21%bv : bv 5), SOff 27 0x4000);
   ((23%bv : bv 5), w5_Bx)].
(* the real-frame cells the piece reads (at, first, &pp->has_params, &pp->params_struct); it writes none of them *)
Definition cl_slots (f : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x100 0 0
   [YP09.mkChunk 0xc0 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xe8 (CVal 8 (SLit f));
    YP09.mkChunk 0x78 (CVal 8 (SOff 27 0x400c)); YP09.mkChunk 0x58 (CVal 8 (SOff 27 0x4010))].
Definition cl_fields (f : Z) : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4018 0x400c (0x400c + 8 * f)
   [YP09.mkChunk 0x4000 (CVal 8 (SOff 35 0))].
Definition cl_at : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition cl_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4); (27%nat, mkAF 4096 140737479966720 4);
           (32%nat, mkAF W5_SB W5_SB 0);
           (33%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 16 5440 0); (35%nat, mkAF 16 5440 0)]
   [] [(SAlu ALU_ADD (SOff 27 0) (SOff 34 0), SOff 33 0)].
Definition ss_cl (f : Z) : sstate := mkSS 0x82a14 (w5_sr cl_ov) [cl_slots f; cl_fields f; cl_at] None cl_facts.
Definition cl_SH : list shent := [mkSHE 27 0x4000 0x4018; mkSHE 33 0 16].
Definition cl_extra (pp atv len : Z) : list word := [w64 W5_SB; w64 (pp + atv); w64 atv; w64 len].

(* the value the four `sb` store: len - atv - 8, as the engine computes it from `subw` and `addi` *)
Definition cl_X : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit 18446744073709551615)) (SLit (-8))) (SOff 35 0).
Lemma cl_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma cl_U_X : forall E atv len, ew E 34 = Z_to_bv 64 atv -> ew E 35 = Z_to_bv 64 len ->
0 < atv < 2 ^ 32 -> 0 <= len < 2 ^ 32 -> atv + 8 <= len -> U E cl_X = len - atv - 8.
Proof.
intros E atv len H34 H35 Ha Hl Hal. unfold cl_X.
rewrite !U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 34 atv H34), (U_atom E 35 len H35), !U_SLit by lia.
rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
rewrite (cl_zc (atv * 18446744073709551615) (atv - 1) (18446744073709551616 - atv)) by lia.
rewrite (cl_zc (-8) (-1) (18446744073709551616 - 8)) by lia.
rewrite (cl_zc (18446744073709551616 - atv + (18446744073709551616 - 8)) 1 (18446744073709551616 - atv - 8)) by lia.
apply (cl_zc _ 1); lia.
Qed.
Lemma cl_U_Xs : forall E atv len k, ew E 34 = Z_to_bv 64 atv -> ew E 35 = Z_to_bv 64 len ->
0 < atv < 2 ^ 32 -> 0 <= len < 2 ^ 32 -> atv + 8 <= len -> (k = 8 \/ k = 16 \/ k = 24) ->
U E (SAlu ALU_SRL cl_X (SLit k)) = Z.shiftr (len - atv - 8) k.
Proof.
intros E atv len k H34 H35 Ha Hl Hal Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite (cl_U_X E atv len) by assumption.
rewrite U_SLit.
assert (HL : Z.land (zcanon k) 63 = k) by (destruct Hk as [-> | [-> | ->]]; reflexivity).
rewrite HL.
assert (0 <= Z.shiftr (len - atv - 8) k <= len - atv - 8).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
apply zcanon_id. unfold M64. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma w5_close_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv len fsv cur : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R ->
  getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 25 = w64 cur -> getr regs 27 = w64 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x58) 8 (pp + 0x4010) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 8 <= len -> len <= 5440 -> (fsv = 0 \/ fsv = 1) -> 0 <= cur < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs 0x82a14 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82ac0 [10; 11; 12; 13; 14; 27]%bv
      (fun a => (pp + atv <= a < pp + atv + 4) \/ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4014))
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 (len - atv - 8)) /\
        getr regs2 27 = w64 cur /\
        (fsv = 1 -> hm_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Z_to_le_bytes 4 1) /\
                    hm_bytes rsegs (w_H W2) mem2 (pp + 0x4010) (Z_to_le_bytes 4 1)))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv len fsv cur
  HJ Hpp Hfresh H2 H9 H20 H21 H23 H25 H27 Vc0 Ve8 V78 V58 Vlen HR16 HRlo HRhi Hat Hal Hlen Hfst Hcur.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
set (E := Ereg regs (cl_extra pp atv len)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E25 : ew E 25 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 len) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (cl_extra pp atv len)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5_Bx cl_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5_shent_blk B lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4018 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5_shent_blk B lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + atv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = len) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr cl_ov) regs).
{ apply (w5_regs_ok E regs (cl_extra pp atv len)); [exact HE|]. unfold cl_ov.
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_sh E 27 pp 0x4000 E27 E32) by lia. rewrite H20. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w5_den_off E 27 pp 0x4000 E27) by lia. rewrite H21. reflexivity. }
  apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold w5_Bx. rewrite (w5_den_off E 32 W5_SB 0 E32) by (unfold W5_SB; lia).
    rewrite Z.add_0_r, H23. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E cl_facts).
{ split; [| split; [exact I |]].
  - cbn [cl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U27, U32, U33, U34, U35.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [cl_facts f_alias alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 pp E27), (U_atom E 34 atv E34), (U_atom E 33 (pp + atv) E33) by lia.
    apply zcanon_id. unfold M64. lia. }
destruct Hfst as [-> | ->].
all: lazymatch goal with Vd : val_mem _ _ (_ + 0xe8) 8 ?f |- _ =>
  assert (HS : st_ok rsegs E (ss_cl f) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82a14) memc (seg_rom rsegs))));
  [ rewrite restrict_mkst_fx; unfold ss_cl; apply (w5_entry rsegs _ _ regs (cl_extra pp atv len) E); [exact HE| | | | |];
    [ exact HR0
    | vm_compute; reflexivity
    | unfold cl_slots, cl_fields, cl_at;
      repeat apply Forall_cons; try apply Forall_nil;
      first
      [ apply (hm_rw_region rsegs E (w_H W) memc 9 R);
        [ exact U9 | lia | lia | intros o Ho; lia | ];
        repeat apply Forall_cons; try apply Forall_nil;
        first
        [ apply (chunk_ok_val rsegs E _ R 0xc0 8 (SOff 34 0) atv);
          [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc0 ]
        | apply (chunk_ok_val rsegs E _ R 0xe8 8 (SLit f) f);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vd ]
        | apply (chunk_ok_val rsegs E _ R 0x78 8 (SOff 27 0x400c) (pp + 0x400c));
          [ rewrite (w5_den_off E 27 pp 0x400c E27) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V78 ]
        | apply (chunk_ok_val rsegs E _ R 0x58 8 (SOff 27 0x4010) (pp + 0x4010));
          [ rewrite (w5_den_off E 27 pp 0x4010 E27) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V58 ] ]
      | apply (hm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 35 0) len);
        [ rewrite (w5_den_off E 35 len 0 E35) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ]
      | apply (hm_rw_region rsegs E (w_H W) memc 33 (pp + atv));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ] ]
    | unfold cl_slots, cl_fields, cl_at; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
      cbn [r_base r_lo r_hi base_val]; rewrite U9, U27, U33; repeat split; try exact I; lia
    | exact HFK ]
  | ] end.
all: unfold cfg_at; change (w64 0x82a14) with (Z_to_bv 64 0x82a14).
all: aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x82ac0.
(* the write windows: the flag words and the size word in pp (the real-frame region is read-only) *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp);
    [ reflexivity | exact U27
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (pp + atv));
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the end state at 0x82ac0 *)
all: apply SRr_ret; unfold w5_post.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
    exact (w5_regs_kept E Ef 40 (w5_sr cl_ov) (ss_regs ssf) regs (ms_regs msf) [10; 11; 12; 13; 14; 27]%bv HR0 HRf
             (env_agree_refl 40 E) ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w5_same_io_wvb]|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hst := fresh "Hst" in let Hn := fresh "Hn" in
    intros a Ha Hst Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U27, ?U33 in Hb; apply Hn; lia | ]);
    destruct Hr
  | ] end.
(* what the piece wrote, from the end state's regions *)
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  let HM := fresh "HM" in pose proof HSf as (_ & _ & _ & _ & _ & _ & _ & (_ & HM & _) & _);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rf := fresh "Rf" in let Ra := fresh "Ra" in
  apply Forall_cons_iff in HM as [_ HM]; apply Forall_cons_iff in HM as [Rf HM];
  apply Forall_cons_iff in HM as [Ra _];
  let Cf := fresh "Cf" in let Ca := fresh "Ca" in
  destruct Rf as (_ & _ & _ & Cf); destruct Ra as (_ & _ & _ & Ca);
  cbn [r_chunks r_base base_val] in Cf, Ca; rewrite U27 in Cf; rewrite U33 in Ca;
  rewrite Forall_forall in Cf, Ca
  end.
all: assert (M0 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 0) = Some (Z_to_bv 8 (len - atv - 8))).
all: try (rewrite <- (cl_U_X E atv len E34 E35) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M1 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 1) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 8))).
all: try (rewrite <- (cl_U_Xs E atv len 8 E34 E35) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M2 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 2) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 16))).
all: try (rewrite <- (cl_U_Xs E atv len 16 E34 E35) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M3 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 3) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 24))).
all: try (rewrite <- (cl_U_Xs E atv len 24 E34 E35) by lia; apply (w5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: split;
  [ apply hm_bytes_aview; intros i Hi; rewrite length_Z_to_le_bytes in Hi;
    rewrite hm_nth_le_bytes by lia; unfold aview;
    destruct i as [|[|[|[|i]]]]; [| | | | lia];
    [ change (Z.of_nat 0) with 0; rewrite M0; cbn [option_map]; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity
    | change (Z.of_nat 1) with 1; rewrite M1; reflexivity
    | change (Z.of_nat 2) with 2; rewrite M2; reflexivity
    | change (Z.of_nat 3) with 3; rewrite M3; reflexivity ]
  |].
(* s11 at the end: the run's last write to register 27 is `mv s11,s9`, the start atom 25 = the cursor *)
all: split;
  [ lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
      let HRf := fresh "HRf" in pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
      transitivity (sv_denot Ef (sr_get (ss_regs ssf) 27%bv)); [exact (HRf 27%bv)|];
      let v := eval vm_compute in (sr_get (ss_regs ssf) 27%bv) in
      replace (sr_get (ss_regs ssf) 27%bv) with v by (vm_compute; reflexivity)
    end;
    rewrite (w5_den_off E 25 cur 0 E25) by lia; rewrite Z.add_0_r; reflexivity
  |].
all: intros Hf1; try discriminate Hf1; split; apply hm_bytes_of_val.
all: first
  [ apply (val_of_chunk_ok rsegs E _ pp 0x400c 4 (SLit 1) 1);
    [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ]
  | apply (val_of_chunk_ok rsegs E _ pp 0x4010 4 (SLit 1) 1);
    [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ] ].
Qed.
End c.

Print Assumptions w5_close_core.
