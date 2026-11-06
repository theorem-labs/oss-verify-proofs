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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 270 of its 306 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aKind.v at f6a13f6f19c8 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan); every pc and register is rate's (in.n is
   the register s8 itself instead of the frame cell [R+0xf8], so the entry state has no frame region and the in.n = 0
   arm writes nothing; the shadow offset is s2; the cursor stays in s9; a5 keeps in.n of the kind read; the dispatch
   block writes s6); the post and the chaining are RtPgSteps.v's rts_blk_post / rts_blk_seq / rts_jt_block. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aKind.v, with its module paths, module names and numbers changed; 188 of its 339 lines of code are new or changed and 155 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aKind.v at 80bf14ccf11; ported to
   reac-pw/fuzz_headamp image B (the cursor in s5, what is left in s10, no frame cell read, the shadow base s11),
   kind mod 10 proved by Z.div facts instead of a check over all 256 bytes, and the post is lib/AU/HPgSteps.v's
   hdu_blk_postE. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the block lemma w6b_kind of lib/AU/HPgW6aBase.v, 0x818d0 .. the case entry of ent_build's
   `switch (kind % 10)` (pod.h:279-281, fuzz.h:37-43). Proves no function (kind: segment lemma).
     0x818d0  beqz s10 -> 0x819c0                      nothing left: stop at D0E
     0x818d4 .. 0x818e0  s2 := s5 + 1; a6 := 1; t2 := 10; `bltu a6,s2` (fuzz.h:42; its trap arm 0x818e4 is dead
                         because 1 <= s5)
     0x818e8  t1 := s10; a7 := s5; 0x818f0 .. 0x818fc the shadow check of s5 (NE-SLOW, slow block 0x82770 back to
              0x81900, its report arm 0x82778 dead by the check's own obligation)
     0x81900  a0 := lbu(a7) = the kind byte b
     0x81904 .. 0x81918  a1 := (b - 10 ((b * 0xcd) >> 11)) & 0xff = b mod 10
     0x8191c  s4 := t1 - 1; 0x81920 a2 := 8; 0x81924 bltu a2,a1 -> 0x82004 (case 9), else 0x81928
     0x81928 .. 0x81948  lib/AU/HPgSteps.v hdu_jt_block, chained by lib/AU/HPgCaseB.v cb_blk_seq.
   The engine's entry state: no region when nothing is left (s10 pinned to 0); else the one-byte region at the
   cursor s5 holding b (atom 32), the atom facts 1 <= s5 <= 2^47 - 2 (amem_range), 1 <= s10 <= 2^63 and
   s11 = SHADOW_OFF (the shadow base, SOff 27 0). The engine follows the check's slow block and leaves one
   obligation, paid from w6b_in's range_addressable. No byte is written. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgCaseB HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== kind % 10 ========================================
   0xcd * b >> 11 = b / 10 on a byte: b * 205 = 2048 (b / 10) + (2 (b / 10) + 205 (b mod 10)), and the last term is
   at most 2 * 25 + 205 * 9 = 1895 < 2048. *)
Lemma kd_div10 : forall b, 0 <= b < 256 -> b * 205 / 2048 = b / 10.
Proof.
intros b Hb.
assert (Hd : b = 10 * (b / 10) + b mod 10) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
assert (Hq : 0 <= b / 10 < 26) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
symmetry. apply (Z.div_unique_pos (b * 205) 2048 (b / 10) (2 * (b / 10) + 205 * (b mod 10))); lia.
Qed.

(* the engine's a1 at 0x81924, over the kind byte's atom 32 *)
Definition kd_a1 : sv :=
  SAlu ALU_AND
    (SAlu ALU_SUB (SOff 32 0)
       (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 205)) (SLit 11)) (SLit 10)))
    (SLit 255).
Section ka. Context {fx : YK11.FPState}.
Lemma kd_a1_mod : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> sv_denot E kd_a1 = Z_to_bv 64 (b mod 10).
Proof.
intros E b H Hb. rewrite denot_lit_U. f_equal.
pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
assert (Hq : 0 <= b / 10 < 26) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (U0 : U E (SOff 32 0) = b) by (apply (U_atom E 32 b H); lia).
assert (U1 : U E (SMd M_MUL (SOff 32 0) (SLit 205)) = b * 205).
{ rewrite U_SMd, U0, U_SLit. cbn [zmd_raw]. unfold zcanon, M64.
  rewrite (Z.mod_small 205) by lia. apply Z.mod_small. lia. }
assert (U2 : U E (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 205)) (SLit 11)) = b / 10).
{ rewrite U_SAlu, U1, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite (Z.mod_small 11) by lia. change (Z.land 11 63) with 11.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 11) with 2048. rewrite (kd_div10 b Hb).
  apply Z.mod_small. lia. }
assert (U3 : U E (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 205)) (SLit 11)) (SLit 10)) = b / 10 * 10).
{ rewrite U_SMd, U2, U_SLit. cbn [zmd_raw]. unfold zcanon, M64.
  rewrite (Z.mod_small 10) by lia. apply Z.mod_small. lia. }
assert (U4 : U E (SAlu ALU_SUB (SOff 32 0)
  (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 205)) (SLit 11)) (SLit 10))) = b mod 10).
{ rewrite U_SAlu, U0, U3. cbn [zalu_raw]. unfold zcanon, M64.
  replace (b - b / 10 * 10) with (b mod 10) by (rewrite (Z.mod_eq b 10) by lia; ring).
  apply Z.mod_small. lia. }
assert (Hl : Z.land (b mod 10) 255 = b mod 10).
{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
unfold kd_a1. rewrite U_SAlu, U4, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small 255) by lia. rewrite Hl. apply Z.mod_small. lia.
Qed.
End ka.

(* ======================================== the entry states ======================================== *)
Definition kd_byte : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition kd_G : facts :=
  mkFacts [(21%nat, mkAF 1 (2 ^ 47 - 2) 0); (26%nat, mkAF 1 (2 ^ 63) 0); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 255 0)] [] [].
Definition kd_ss1 : sstate := mkSS W6B_RET sr_atoms [kd_byte] None kd_G.
Definition kd_ss0 : sstate := mkSS W6B_RET sr_atoms [] None (mkFacts [] [] []).
Definition kd_Bx : sv := SOff 27 0.
Definition kd_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kd_extra (b : Z) : list word := [w64 b].
(* the registers the run to 0x82004 / 0x81928 sets: t1, t2, a0 = b, a1 = b mod 10, a2 = 8, a6, a7, s2, s4 *)
Definition kd_clob : list (bv 5) := [6; 7; 10; 11; 12; 16; 17; 18; 20]%bv.
Definition kd_Rc (b cur nl : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 10 = w64 b /\ getr regs2 11 = w64 (b mod 10) /\ getr regs2 12 = w64 8 /\
getr regs2 6 = w64 (nl + 1) /\ getr regs2 7 = w64 10 /\ getr regs2 16 = w64 1 /\
getr regs2 17 = w64 cur /\ getr regs2 18 = w64 (cur + 1) /\ getr regs2 20 = w64 nl.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* a pure-read block's post with fewer clobbered registers and a stronger R is a block post (lib/AU/HPgCaseB.v
   cb_post_of_blk then makes it an hdu_blk_postE) *)
Lemma kd_blk_post_mono : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob'
  (R R' : bvmap 5 word -> Prop) W2 c2,
  incl clob clob' ->
  (forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) -> R regs2 -> R' regs2) ->
  hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob R W2 c2 ->
  hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob' R' W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' R R' W2 c2 Hi HR
  (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR2).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ|].
split; [intros r Hr0 Hn; apply Hr; [exact Hr0 | intros X; apply Hn; apply Hi; exact X]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|]. split; [exact Hm|].
exact (HR regs2 Hr HR2).
Qed.
(* ---- the case rr = []: `beqz s10` 0x818d0 taken ---- *)
Lemma kd_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos,
  cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 26 = w64 0 ->
  SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
  (hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D0E [] (fun _ => True)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H26.
pose proof Hctx as (HJ & _).
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HS0 : st_ok rsegs (Ereg regs []) kd_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_lit rsegs _ _ _ (26%bv : bv 5) 0 HS0 eq_refl H26) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts kd_ss0] in HS.
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at. change (w64 W6B_RET) with (Z_to_bv 64 W6B_RET).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span W6B_D0E.
all: try solve [awr_ok_tac].
lazymatch type of HS with st_ok _ ?E2 _ _ =>
  assert (HAE2 : env_agree 32 (Ereg regs []) E2) by env_agree_chain HAE end.
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((26%bv : bv 5), SLit 0)] HS HAE2);
        [ intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst; cbn [sv_denot]; exact (eq_sym H26)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split; [|exact I].
intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin.
Qed.

(* ---- the case rr = b :: r: the run to 0x81924, the branch on b mod 10, the run to its target ---- *)
Ltac kd_reg HS HAx E21x E26x E32x :=
  rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HS);
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
  cbn [sv_denot];
  rewrite ?(HAx 21%nat), ?(HAx 26%nat), ?(HAx 32%nat) by lia;
  rewrite ?E21x, ?E26x, ?E32x;
  rewrite ?unsigned_lit_small by lia;
  unfold w64; f_equal; lia.
Ltac kd_finish ms2 HS HJ HAE2 HFr1 HFr lyc Sc regs W :=
  apply SRr_ret;
  lazymatch goal with |- _ (mkCfg ms2 ?md2) => red; exists lyc, Sc, (ms_regs ms2), (ms_mem ms2), md2 end;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms2 HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms2 regs _ (w_H W) _ HS HAE2); vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in
    intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [rewrite (HFr1 (Z_to_bv 64 a)); [reflexivity|]|];
    let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (rr & Hin & Hr); cbv [In ss_mem add_cond kd_ss1] in Hin;
    repeat (destruct Hin as [<-|Hin]; [cbn in Hr; lia|]); destruct Hin
  | unfold kd_Rc ].

Lemma kd_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos cur
  (bb : byte) (r : list byte),
  cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 21 = w64 cur -> getr regs 26 = w64 (Z.of_nat (length (bb :: r))) -> getr regs 27 = w64 SHADOW_OFF ->
  w6b_in W memc R cur (bb :: r) ->
  SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
  (hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
    (if bv_unsigned bb mod 10 =? 9 then W6B_D9 else JT_PC) kd_clob
    (kd_Rc (bv_unsigned bb) cur (Z.of_nat (length r)))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r Hctx H21 H26 H27 Hin.
pose proof Hctx as (HJ & _).
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (Cursor.byte_range bb) as Hb.
destruct Hin as (Hg & Hra & Hc0 & Hc1 & Hamem & _).
remember (Z.of_nat (length (bb :: r))) as n eqn:Hneq.
remember (Z.of_nat (length r)) as nl eqn:Hnl.
assert (Hn1 : n = nl + 1) by (rewrite Hneq, Hnl; cbn [length]; lia).
clear Hneq.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem.
assert (Hcur : 1 <= cur <= 2 ^ 47 - 2) by lia.
clear Hamem.
destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv0 _]. clear Hg.
cbn [nth map Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
remember (bv_unsigned bb) as b eqn:Hbeq.
pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
assert (E21 : ew (Ereg regs (kd_extra b)) 21 = Z_to_bv 64 cur)
  by (rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E26 : ew (Ereg regs (kd_extra b)) 26 = Z_to_bv 64 n)
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew (Ereg regs (kd_extra b)) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew (Ereg regs (kd_extra b)) 32 = Z_to_bv 64 b) by exact (ew_Ereg_extra regs (kd_extra b) 0).
assert (HS : st_ok rsegs (Ereg regs (kd_extra b)) kd_ss1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, kd_byte. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E21, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact Hv0].
  - cbn. tauto.
  - assert (HF21 : afact_ok (Ereg regs (kd_extra b)) 21 (mkAF 1 (2 ^ 47 - 2) 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E21, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF26 : afact_ok (Ereg regs (kd_extra b)) 26 (mkAF 1 (2 ^ 63) 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E26, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF27 : afact_ok (Ereg regs (kd_extra b)) 27 (mkAF SHADOW_OFF SHADOW_OFF 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E27, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF32 : afact_ok (Ereg regs (kd_extra b)) 32 (mkAF 0 255 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    exact (conj (conj HF21 (conj HF26 (conj HF27 (conj HF32 I)))) (conj I I)). }
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs (kd_extra b)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 33 (Ereg regs (kd_extra b)) (Ereg regs (kd_extra b))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6B_RET) with (Z_to_bv 64 W6B_RET).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span JT_PC.
all: try solve [ eapply obl_of_range; [exact Hra | | |];
                 [ apply (U_atom _ 27 SHADOW_OFF E27); unfold SHADOW_OFF; lia
                 | rewrite (U_atom _ 21 cur E21) by lia; lia
                 | rewrite (U_atom _ 21 cur E21) by lia; lia ] ].
all: try solve [awr_ok_tac].
rename HFr into HFr1.
lazymatch type of HS with st_ok _ ?E1 _ _ =>
  assert (HAE1 : env_agree 33 (Ereg regs (kd_extra b)) E1) by env_agree_chain HAE end.
pose proof HAE1 as [HA1 _].
assert (E32' : forall E', (forall i, (i < 33)%nat -> ew E' i = ew (Ereg regs (kd_extra b)) i) ->
  ew E' 32 = Z_to_bv 64 b) by (intros E' HE'; rewrite (HE' 32%nat) by lia; exact E32).
srr_branch_tok w6b_tbl_ok HS SHOK kd_span.
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E32' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Hm9 : b mod 10 = 9) by lia. rewrite (proj2 (Z.eqb_eq _ _) Hm9).
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span W6B_D9.
  all: try solve [awr_ok_tac].
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 33 (Ereg regs (kd_extra b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  split; [kd_reg HS HA2 E21 E26 E32|].
  split; [rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HS);
          lazymatch type of HS with st_ok _ _ ?ssf _ => change (sr_get (ss_regs ssf) (11%bv : bv 5)) with kd_a1 end;
          exact (kd_a1_mod _ b (E32' _ HA2) ltac:(lia))|].
  repeat (split; [kd_reg HS HA2 E21 E26 E32|]).
  kd_reg HS HA2 E21 E26 E32.
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E32' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Hm9 : b mod 10 <> 9) by lia. rewrite (proj2 (Z.eqb_neq _ _) Hm9).
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span JT_PC.
  all: try solve [awr_ok_tac].
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 33 (Ereg regs (kd_extra b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  split; [kd_reg HS HA2 E21 E26 E32|].
  split; [rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HS);
          lazymatch type of HS with st_ok _ _ ?ssf _ => change (sr_get (ss_regs ssf) (11%bv : bv 5)) with kd_a1 end;
          exact (kd_a1_mod _ b (E32' _ HA2) ltac:(lia))|].
  repeat (split; [kd_reg HS HA2 E21 E26 E32|]).
  kd_reg HS HA2 E21 E26 E32.
Qed.

(* ======================================== the theorem ======================================== *)
Local Ltac kd_nin := cbv; first [discriminate | intros [X|[X|[X|[X|[]]]]]; discriminate X].
Theorem w6b_kind : w6b_kind_stmt B MT.
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur rr Hctx H2 H9 H27 H21 H26 Hin.
destruct rr as [|bb r].
- eapply SRr_mono; [exact (kd_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H26)|].
  intros W2 c2 _ HP. left. split; [reflexivity|].
  apply (cb_post_of_blk B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D0E [] (fun _ => True)
    (fun _ => False) W2 c2). exact HP.
- assert (Hrom : rom_view rsegs W memc) by (destruct Hctx as (_ & _ & _ & _ & _ & _ & X); exact X).
  pose proof (kd_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r
    Hctx H21 H26 H27 Hin) as H1.
  pose proof (Cursor.byte_range bb) as Hb.
  remember (bv_unsigned bb) as b eqn:Hbeq.
  remember (Z.of_nat (length r)) as nl eqn:Hnl.
  pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
  eapply SRr_mono; [| intros W2 c2 _ HP; right; exists bb, r; split; [reflexivity | rewrite <- Hbeq, <- Hnl; exact HP]].
  unfold w6b_case_pc.
  destruct (Z.eqb_spec (b mod 10) 9) as [E9|E9].
  + cbv beta iota in H1 |- *.
    eapply SRr_mono; [exact H1|]. intros W2 c2 _ HP.
    apply (cb_post_of_blk B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D9 w6b_kind_clob
      (w6b_kind_R b cur nl) (fun _ => False) W2 c2).
    apply (kd_blk_post_mono STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D9 kd_clob w6b_kind_clob
      (kd_Rc b cur nl) (w6b_kind_R b cur nl) W2 c2);
      [ intros x Hx; cbn [kd_clob w6b_kind_clob In] in Hx |- *; tauto | | exact HP ].
    intros regs2 _ (R10 & R11 & R12 & R6 & R7 & R16 & R17 & R18 & R20).
    unfold w6b_kind_R. repeat (split; [assumption|]). left. exact E9.
  + cbv beta iota in H1 |- *.
    eapply SRr_mono.
    * eapply (cb_blk_seq B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_RET JT_PC
        (jt_tgt (b mod 10)) kd_clob [10; 11; 12; 13]%bv (kd_Rc b cur nl) (w6b_kind_R b cur nl)).
      { exact H1. }
      intros W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1
        (R10 & R11 & R12 & R6 & R7 & R16 & R17 & R18 & R20).
      assert (Hrom1 : rom_view rsegs W1 mem1) by (intros a Ha; rewrite Hm1; exact (Hrom a Ha)).
      eapply SRr_mono;
        [exact (hdu_jt_block B MT MTL (YG0q.AR_laws_ok rsegs B) STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k
                  regs1 (b mod 10) HJ1 ltac:(lia) R11 Hrom1)|].
      intros W2 c2 _ HP.
      apply (kd_blk_post_mono STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 (jt_tgt (b mod 10))
        [10; 11; 12; 13]%bv [10; 11; 12; 13]%bv (jt_R (b mod 10) regs1) (w6b_kind_R b cur nl) W2 c2);
        [apply incl_refl | | exact HP].
      intros regs2 Hk (J11 & J12 & J10 & J13).
      rewrite R10 in J13. unfold w64 in J13. rewrite unsigned_lit_small in J13 by lia.
      rewrite (Z.mod_small b 256) in J13 by lia.
      unfold w6b_kind_R.
      rewrite (Hk 17%bv), (Hk 18%bv), (Hk 6%bv), (Hk 20%bv), (Hk 7%bv), (Hk 16%bv) by kd_nin.
      repeat (split; [assumption|]). right. exact J13.
    * intros W2 c2 _ HP.
      apply (cb_post_of_blk B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (jt_tgt (b mod 10))
        w6b_kind_clob (w6b_kind_R b cur nl) (fun _ => False) W2 c2).
      apply (kd_blk_post_mono STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (jt_tgt (b mod 10))
        (kd_clob ++ [10; 11; 12; 13]%bv) w6b_kind_clob (w6b_kind_R b cur nl) (w6b_kind_R b cur nl) W2 c2);
        [ intros x Hx; apply in_app_or in Hx; cbn [kd_clob w6b_kind_clob In] in Hx |- *; tauto
        | intros regs2 _ X; exact X | exact HP ].
Qed.

End d.
End b.

Print Assumptions w6b_kind.
