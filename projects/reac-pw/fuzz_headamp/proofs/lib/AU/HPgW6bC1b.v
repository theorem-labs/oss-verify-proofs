(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638 and the definitions
   w7_kept, w7_hull, w7_strok, w7_strz of proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638, for
   reac-pw/fuzz_headamp's image B: w7_ -> hw7b_, role's image A code and record -> fuzz_headamp.asan-ubsan's (its own
   code table, pcs, registers and real-frame cells, measured on image B), module paths; the statements of the walk's
   blocks and call steps are new (hw7b_*_stmt), one per block of image B's own code; its hw7b_post,
   hw7b_post_of_run, hw7b_kept, hw7b_hull, hw7b_ra_kept, hw7b_hull_kept, hw7b_strok, hw7b_strz, hw7b_strok_kept and
   hw7b_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW7bBase.v, with its numbers changed; 102 of its 142 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bIter.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rm_ prefix renamed, every pc moved by the code's uniform shift +0xd20, the strlen trampoline 0x41b98 and __asan_memcpy 0x51d0c (W7_STRLEN / W7_MEMCPY of lib/A/HPgW7bBase.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW7bIter.v; 467 of its 535 lines of code are new or changed and 74 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1.v at f3898085bda (the vocab strings,
   the model of a case-1 turn, e62's bytes at the join, the bounds of the shadow hulls, c1_calls and the block
   lemma w6b_c1) for reac-pw/fuzz_headamp's image B: image B's vocab table and pcs, e62 at F+0x210 with its body
   at F+0x218, the strlen wrapper at STRLEN_ENTRY_B and __asan_memcpy at 0x51d8c through HPgCaseB.cb_memcpy_at,
   the string facts taken from HPgBase.hd_cstr (which carries the tail of the NUL's word, so role's
   c1_vtail / c1_vtail_chk are dropped), and the post HPgSteps.hdu_blk_postE / HPgCaseBJ.cj_J_R. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW6bC1.v, with its module paths and module names changed; 321 of its 365 lines of code are new or changed and 491 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1a.v at f3898085bda (c1_head, c1_vcell,
   c1_set: one engine run per block from an entry state to a call or to the next block) for reac-pw/fuzz_headamp's
   image B: image B's code, registers and real-frame cells (below); the head runs from the kit's entry state
   HPgW6bBase.ss_hb (a6 pinned to 1, s4 to 0 when no byte is left) and splits `beqz s4` itself; the UBSan
   pointer tests of image B are decided by the engine from the cursor's and the index's ranges; the post is
   HPgCaseB.cb_post. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW6bC1a.v; 261 of its 316 lines of code are new or changed and 310 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1b.v at f3898085bda (c1_tail: the entry
   state of the tail, the split on bit 7 of the kind byte, one engine run per arm) for reac-pw/fuzz_headamp's image
   B: image B's code, registers and real-frame cells (below), e62 at F+0x210 with its body at F+0x218, the kind byte
   and the cursor read back from the two spills [R+0x58] and [R+0x110] (image A kept them in registers), the UBSan
   pointer tests of pod.h:215 decided from atom 33 = [R+0xe8], and the post HPgCaseB.cb_post. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the tail of case 1 of
   ent_build's `switch (kind % 10)` (pod.h:213-217, 290-294) inside LLVMFuzzerTestOneInput (0x80c40), from the
   return of __asan_memcpy (0x8215c) to the join J 0x82618. Proves no function (kind: segment lemma).

   THE CODE (s2 = x18 = s4 = x20 = len, s7 = x23 = F + 0x218 = &e62.body, s5 = x21 = what was left at the case
   entry, s1 = x9 = R, s11 = x27 = SHADOW_OFF):
     0x8215c  ld a0,0xe8(s1); bgeu a0,s2        the UBSan pointer test of pod.h:215 ([R+0xe8] = -(F+0x219))
     0x82168  a0 := s2 + 1; a1 := s7 + s2; sb zero,0(a1)      the NUL (no instrumented check)
     0x82174  a1 := [R+0x130] (= &e62); sw 8,0(a1) (e62.type = POD_STRING); sw a0,4(a1) (e62.size = len + 1)
     0x82184  s7 := [R+0x148] (= pp); t1 := s5; a3 := [R+0x110] (the cursor); a1 := [R+0x58] (the kind byte)
     0x82194  bgez a1 -> 0x82208                 bit 7 of the kind byte clear
     0x82198  addi a1,zero,0x5d; bltu a1,s4 -> 0x82208        len > 93 (never: len <= 18)
     0x821a0  ld a1,0xe8(s1); bltu s2,a1; a0 := [R+0x118] + s2 + 1; the shadow check of a0 (slow block 0x82840);
              sb 'x',0(a0); ld a0,0xe8(s1); bgeu a0,s2+2; a0 := [R+0x118] + s2 + 2; the shadow check (0x8284c);
              sb zero,0(a0); s2 := s2 + 3; s4 := [R+0x130]; sw s2,4(s4) (e62.size = len + 3); j 0x82614
     0x82208  s2 := [R+0x138] (= &pp->len); s4 := [R+0x130] (= &e62); j 0x82618
     0x82614  s2 := [R+0x138]                                                                     -> J 0x82618
   THE ENTRY STATE, over Ereg regs [F; [R+0xe8]; the kind byte; the cursor; pp] (atoms 32 .. 36):
     hb1_tR   based at s1 = R: the read-only cells [R+0x58] .. [R+0x148].
     hb1_tE1  based at F: e62.type, e62.size [F+0x210, F+0x218), written.
     hb1_tE2  based at F: e62.body[len .. len + 3), written, 0 at the entry (the memcpy wrote body[0 .. len) only).
     s2, s4 pinned to the literal len, s7 to F + 0x218. The shadow entry over e62 (HPgW6bBase.hb_SH, atom 32,
     [0x210, 0x278)) covers both checked stores, so the token engine asks no obligation: e62 is in scope.
   The branch on the kind byte is split by srr_branch_tok; len takes the five lengths of the vocab strings
   (12, 13, 14, 15, 18), each a closed numeral in the state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgW6bBase HPgW6bC1k HPgW6bC1a HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the entry state ======================================== *)
Definition hb1_tR : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x150 0 0
  [ YP09.mkChunk 0x58 (CVal 8 (SOff 34 0)); YP09.mkChunk 0xe8 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x110 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x118 (CVal 8 (SOff 32 0x218));
    YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210)); YP09.mkChunk 0x138 (CVal 8 (SOff 36 0x4000));
    YP09.mkChunk 0x148 (CVal 8 (SOff 36 0)) ].
Definition hb1_tE1 : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x218 0x210 0x218 [].
Definition hb1_tE2 (n : Z) : YP09.region :=
  YP09.mkRegion (Some 32%nat) (0x218 + n) (0x21b + n) (0x218 + n) (0x21b + n) [YP09.mkChunk (0x218 + n) (CZero 3)].
Definition hb1_tf : facts :=
  mkFacts [ (9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 4096 0x7fffff800000 5); (33%nat, mkAF HB_E8LO HB_E8HI 0) ] [] [].
Definition hb1_tss (n : Z) : sstate := mkSS HB1_MCR sr_atoms [hb1_tR; hb1_tE1; hb1_tE2 n] None hb1_tf.
Definition hb1_tx (F e8 kds cur pp : Z) : list word := [w64 F; w64 e8; w64 kds; w64 cur; w64 pp].
(* the five lengths of the vocab strings *)
Definition hb1_lens : list Z := [12; 13; 14; 15; 18].
(* the bytes the tail writes; the stored size and second body byte by the kind's bit 7 *)
Definition hb1_tail_wr (F n : Z) : Z -> Prop := fun a => (F + 0x210 <= a < F + 0x218) \/ (F + 0x218 + n <= a < F + 0x21b + n).
Definition hb1_ty (kd : Z) : Z := if kd <? 128 then 1 else 3.
Definition hb1_xb (kd : Z) : Z := if kd <? 128 then 0 else 0x78.
(* the registers the tail may change *)
Definition hb1_tclob : list (bv 5) := [6; 10; 11; 12; 13; 18; 20; 23]%bv.

Lemma hb1_tss_wf : forall n, In n hb1_lens -> regions_wf (ss_mem (hb1_tss n)) = true.
Proof. intros n Hn. repeat (destruct Hn as [<-|Hn]; [vm_compute; reflexivity|]). destruct Hn. Qed.
(* `bgez a1` with a1 the kind byte sign-extended is taken exactly when bit 7 is clear *)
Lemma hb1_bgez : forall E kd, ew E 34 = Z_to_bv 64 ((kd - 256 * (kd / 128)) mod 2 ^ 64) -> 0 <= kd < 256 ->
  branch_taken BC_GE (sv_denot E (SOff 34 0)) (sv_denot E (SLit 0)) = (kd <? 128).
Proof.
intros E kd H Hk. cbn [sv_denot]. rewrite H.
apply Bool.eqb_prop.
exact (cb_all256 (fun kd => Bool.eqb (branch_taken BC_GE
  (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ((kd - 256 * (kd / 128)) mod 2 ^ 64)) + 0)) (Z_to_bv 64 0)) (kd <? 128))
  ltac:(vm_compute; reflexivity) kd Hk).
Qed.
Lemma hb1_vm1_zero : forall m a, mbyte rsegs m a = Some (Z_to_bv 8 0) -> val_mem rsegs m a 1 0.
Proof. intros m a H k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r. exact H. Qed.

(* the write windows of a tail state lie in Zn *)
Ltac hb1_kwr2 B9 B32 :=
  let a := fresh "a" in let r0 := fresh "r0" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
  intros a (r0 & Hin & Hb);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r0 rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B9, ?B32 in Hb; cbv beta;
     unfold hb1_tail_wr; lia|]);
  destruct Hin.
(* the windows of a tail state: hb1_tR read only, the two e62 windows in the frame (4, pos) *)
Ltac hb1_awr_t B32 pos Hown HFa :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat _); [reflexivity | exact B32 |
      cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 4, pos; split; [exact Hown|]; left;
      unfold in_zr; cbn [fst snd]; rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia |] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the shadow entry over e62, for any extra list whose first word is F *)
Lemma hb1_shok : forall (regs : bvmap 5 word) extra (H : word -> bool) mem F,
  getr regs 27 = w64 SHADOW_OFF -> nth 0 extra (Z_to_bv 64 0) = Z_to_bv 64 F -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0x210) 104 ->
  (forall a, F + 0x210 <= a < F + 0x278 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) ->
  sh_ok rsegs HBx hb_SH (Ereg regs extra) (mrestrict H mem).
Proof.
intros regs extra H mem F H27 H32 HF1 HF2 Hra Hap. pose proof (@asan_consts rc) as (Hceil & _).
assert (U27 : U (Ereg regs extra) (SOff 27 0) = SHADOW_OFF).
{ apply U_atom; [rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity | unfold SHADOW_OFF; lia]. }
assert (U32 : U (Ereg regs extra) (SOff 32 0) = F).
{ apply U_atom; [rewrite (ew_Ereg_extra regs _ 0); exact H32 | lia]. }
apply Forall_cons; [|apply Forall_nil]. unfold shent_ok. cbn [she_m she_lo she_hi].
unfold HBx. rewrite U27, U32. split.
- rewrite <- (aview_rd_of rsegs). exact Hra.
- unfold app_apart. cbn [she_m she_lo she_hi]. unfold HBx. rewrite U27, U32. intros a Ha. apply Hap. lia.
Qed.

(* a zero byte of a CZero chunk of a run's last state *)
Lemma hb1_zero_at : forall E ss H ms i r off len j a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) -> 0 <= j < len -> a = base_val E (YP09.r_base r) + off + j ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a 1 0.
Proof.
intros E ss H ms i r off len j a HS Hi Hc Hj ->. apply hb1_vm1_zero.
exact (hb_chunk_zero E _ r off len (hb_region E ss (restrict H ms) r HS (nth_error_In _ _ Hi)) Hc j Hj).
Qed.

(* the entry state, for any length *)
Lemma hb1_tail_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F n kds e8 cur pp,
  regions_wf (ss_mem (hb1_tss n)) = true ->
  getr regs 9 = w64 R -> alloc_ceiling <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
  getr regs 27 = w64 SHADOW_OFF ->
  4096 <= F -> F + 1024 <= alloc_ceiling -> F mod 32 = 0 -> 0 <= n <= 18 ->
  0 <= kds < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
  HB_E8LO <= e8 <= HB_E8HI ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x58) 8 kds ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 e8 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  (forall a, F + 0x210 <= a < F + 0x278 -> apresent (w_H W) memc a) ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x218 + n + i) = Some (Z_to_bv 8 0)) ->
  st_ok rsegs (Ereg regs (hb1_tx F e8 kds cur pp)) (hb1_tss n)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 HB1_MCR) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F n kds e8 cur pp Hwf H9 HR1 HR2 HR3 H27 HF1 HF2 HF3 Hn Hkds Hcur Hpp1 Hpp2 He8
  V58 Ve8 V110 V118 V130 V138 V148 Pe Ez.
pose proof (@asan_consts rc) as (Hceil & _).
unfold HB_E8LO, HB_E8HI in He8.
set (E := Ereg regs (hb1_tx F e8 kds cur pp)).
assert (B9 : bv_unsigned (ew E 9) = R) by exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (B27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by exact (hb_U_reg regs _ 27 27%bv _ eq_refl H27 ltac:(unfold SHADOW_OFF; lia)).
assert (E32 : ew E 32 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 0).
assert (E33 : ew E 33 = Z_to_bv 64 e8) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 1).
assert (E34 : ew E 34 = Z_to_bv 64 kds) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 2).
assert (E35 : ew E 35 = Z_to_bv 64 cur) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 3).
assert (E36 : ew E 36 = Z_to_bv 64 pp) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 4).
assert (B32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (B33 : bv_unsigned (ew E 33) = e8) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B34 : bv_unsigned (ew E 34) = kds) by (rewrite E34; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = cur) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B36 : bv_unsigned (ew E 36) = pp) by (rewrite E36; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold hb1_tss. apply (entry_st_ok_full rsegs);
  try change (Ereg regs (hb1_tx F e8 kds cur pp)) with E.
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok, hb1_tR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ R 0x58 8 (SOff 34 0) kds);
        [cbn [sv_denot]; rewrite B34, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V58].
    * apply (chunk_ok_val rsegs E _ R 0xe8 8 (SOff 33 0) e8);
        [cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Ve8].
    * apply (chunk_ok_val rsegs E _ R 0x110 8 (SOff 35 0) cur);
        [cbn [sv_denot]; rewrite B35, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V110].
    * apply (chunk_ok_val rsegs E _ R 0x118 8 (SOff 32 0x218) (F + 0x218));
        [cbn [sv_denot]; rewrite B32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V118].
    * apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 32 0x210) (F + 0x210));
        [cbn [sv_denot]; rewrite B32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V130].
    * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 36 0x4000) (pp + 0x4000));
        [cbn [sv_denot]; rewrite B36; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V138].
    * apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 36 0) pp);
        [cbn [sv_denot]; rewrite B36, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V148].
  + unfold region_ok, hb1_tE1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Pe. lia.
  + unfold region_ok, hb1_tE2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B32. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Pe; lia|].
    apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
    replace (F + (0x218 + n) + i) with (F + 0x218 + n + i) by lia. apply Ez. exact Hi.
- apply pairwise_disjoint_of_extents. unfold hb1_tR, hb1_tE1, hb1_tE2. cbn [map]. unfold extent_of_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite B9, B32. repeat split; first [exact I | lia].
- unfold facts_ok. cbn [hb1_tf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|split; [|split; [|split; [|exact I]]]].
  + apply (hb1_af _ _ R _ _ _ B9); [lia | change (2 ^ 4) with 16; exact HR3 | lia].
  + apply (hb1_af _ _ SHADOW_OFF _ _ _ B27); [lia | reflexivity | lia].
  + apply (hb1_af _ _ F _ _ _ B32); [lia | change (2 ^ 5) with 32; exact HF3 | lia].
  + apply (hb1_af _ _ e8 _ _ _ B33); [unfold HB_E8LO, HB_E8HI; lia | apply Z.mod_1_r | lia].
Qed.

Section d.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* what the tail leaves at J *)
Definition hb1_tail_R (W : world rsegs) (F n kd cur pp : Z) (regs : bvmap 5 word) :
  bvmap 5 word -> (word -> option byte) -> Prop :=
fun regs2 mem2 =>
  getr regs2 13 = w64 cur /\ getr regs2 6 = getr regs 21 /\ getr regs2 18 = w64 (pp + Layout.OFF_LEN) /\
  getr regs2 20 = w64 (F + 0x210) /\ getr regs2 23 = w64 pp /\
  val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 8 /\
  val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 (n + hb1_ty kd) /\
  val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x218 + n) 1 0 /\
  val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x218 + n + 1) 1 (hb1_xb kd) /\
  val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x218 + n + 2) 1 0.

(* ======================================== hb1_tail: 0x8215c .. J ======================================== *)
Lemma hb1_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F pos n kd cur pp,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  R mod 32 = 0 -> R + 0x220 <= sp0 -> sp0 - STK <= R - T_SEG_STK ->
  In (4, pos) own -> F = frame_addr lyc 4 pos ->
  In n hb1_lens -> 0 <= kd < 256 ->
  getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
  getr regs 18 = w64 n -> getr regs 20 = w64 n -> getr regs 23 = w64 (F + 0x218) ->
  0 <= cur < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x58) 8 ((kd - 256 * (kd / 128)) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 ((- (F + 0x219)) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  (forall i, 0 <= i < 3 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x218 + n + i) = Some (Z_to_bv 8 0)) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 HB1_MCR) memc (seg_rom rsegs)) mdc)
  (cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB_J regs memc mdc hb1_tclob (hb1_tail_wr F n)
     (hb1_tail_R W F n kd cur pp regs)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos n kd cur pp HJ HR32 HRsp HspR Hown HFa Hn Hkd
  H9 H27 H18 H20 H23 Hcur Hpp1 Hpp2 V58 Ve8 V110 V118 V130 V138 V148 Ez Hrae.
pose proof hb_wx as Hwx. pose proof hb_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@asan_consts rc) as (Hac & _).
assert (HT : T_SEG_STK = 16384) by reflexivity. rewrite HT in HspR.
pose proof (hb1_mod16 R HR32) as HR16.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & Happ & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, Happ, HFpres, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in Happ, HFpres, HFceil.
assert (Hn18 : 0 <= n <= 18) by (repeat (destruct Hn as [<-|Hn]; [lia|]); destruct Hn).
assert (Pe : forall a, F + 0x210 <= a < F + 0x278 -> apresent (w_H W) memc a)
  by (intros a Ha; exact (proj1 (HFpres a ltac:(lia)))).
assert (Hap : forall a, F + 0x210 <= a < F + 0x278 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia. }
pose proof (hb_e8_range F HF4096 HFceil) as He8.
set (kds := (kd - 256 * (kd / 128)) mod 2 ^ 64) in *.
set (e8 := (- (F + 0x219)) mod 2 ^ 64) in *.
assert (Hkds : 0 <= kds < 2 ^ 64) by (subst kds; apply Z.mod_pos_bound; lia).
assert (HRa : alloc_ceiling <= R) by lia.
assert (HRb : R + 0x220 <= 2 ^ 47) by lia.
clear Hsp0al HSTK0 Hceil Hslo Hshi H47 HFpres Happ.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ hb1_tail_wr F n a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
assert (Hgr0 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
destruct Hn as [<-|[<-|[<-|[<-|[<-|[]]]]]];
(lazymatch goal with |- context [hb1_tail_wr F ?n0] =>
 pose proof (hb1_tail_entry W regs memc R F n0 kds e8 cur pp (hb1_tss_wf n0 ltac:(cbn [In hb1_lens]; tauto))
   H9 HRa HRb HR16 H27 HF4096 HFceil HF32 ltac:(lia) Hkds Hcur Hpp1 Hpp2 He8 V58 Ve8 V110 V118 V130 V138 V148 Pe Ez)
   as HS0;
 set (E := Ereg regs (hb1_tx F e8 kds cur pp)) in HS0;
 assert (B9 : bv_unsigned (ew E 9) = R) by exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia));
 assert (E32 : ew E 32 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 0);
 assert (E34 : ew E 34 = Z_to_bv 64 kds) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 2);
 assert (E35 : ew E 35 = Z_to_bv 64 cur) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 3);
 assert (E36 : ew E 36 = Z_to_bv 64 pp) by exact (ew_Ereg_extra regs (hb1_tx F e8 kds cur pp) 4);
 assert (B32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia);
 (* s2, s4 := the literal len; s7 := F + 0x218 *)
 pose proof (st_ok_pin_lit rsegs _ _ _ (18%bv : bv 5) n0 HS0 eq_refl
   ltac:(cbn [ms_regs restrict mkst]; rewrite H18; reflexivity)) as HS1;
 pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) n0 HS1 eq_refl
   ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS2;
 pose proof (st_ok_pin_sv rsegs _ _ _ (23%bv : bv 5) (SOff 32 0x218) HS2 eq_refl
   ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite H23, E32, unsigned_lit_small by lia; reflexivity)) as HS;
 clear HS0 HS1 HS2;
 cbn [ss_pc ss_regs ss_mem ss_resv ss_facts hb1_tss] in HS;
 assert (SHOK : sh_ok rsegs HBx hb_SH E (mrestrict (w_H W) memc))
   by exact (hb1_shok regs (hb1_tx F e8 kds cur pp) (w_H W) memc F H27 eq_refl HF4096 HFceil Hrae Hap);
 assert (HAE : env_agree 32 E E) by apply env_agree_refl;
 aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_J;
 [ hb1_awr_t B32 pos Hown HFa
 | lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end;
   pose proof (cb_kept_run (hb1_tail_wr F n0) _ _ (w_H W) memc memc (ms_mem ms1) KE HFr
     ltac:(hb1_kwr2 B9 B32)) as KE1;
   clear KE HF HFr; rename KE1 into KE;
   pose proof (mem_grows_trans _ _ _ Hgr0 HG) as G1; clear Hgr0 HG; rename G1 into Hgr0;
   srr_branch_tok hb_tbl_ok HS SHOK HBspan;
   (rewrite (hb1_bgez E kd E34 Hkd) in Hc; unfold hb1_tail_R, hb1_ty, hb1_xb; rewrite Hc;
    aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_J;
    [ hb1_awr_t B32 pos Hown HFa
    | lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ =>
      pose proof (cb_kept_run (hb1_tail_wr F n0) _ _ (w_H W) memc (ms_mem ms1) (ms_mem m) KE HFr
        ltac:(hb1_kwr2 B9 B32)) as KE2;
      eapply (cb_post_of_run B);
      [ exact HS | reflexivity | reflexivity | exact HJ | cb_kio
      | eapply (regs_kept_of_st_ok rsegs _ _ m regs (hb1_tx F e8 kds cur pp) (w_H W) _ HS);
          [env_agree_chain HAE | vm_compute; reflexivity]
      | exact KE2 | exact (mem_grows_trans _ _ _ Hgr0 HG) | ];
      split; [hb1_reg HS (13%bv : bv 5); cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia;
              unfold w64; f_equal; lia|];
      split; [hb1_reg HS (6%bv : bv 5); exact (hb1_atom regs _ 21 21%bv eq_refl)|];
      split; [hb1_reg HS (18%bv : bv 5); cbn [sv_denot]; rewrite E36, unsigned_lit_small by lia;
              unfold w64, Layout.OFF_LEN; f_equal; lia|];
      split; [hb1_reg HS (20%bv : bv 5); cbn [sv_denot]; rewrite E32, unsigned_lit_small by lia;
              unfold w64; f_equal; lia|];
      split; [hb1_reg HS (23%bv : bv 5); cbn [sv_denot]; rewrite E36, unsigned_lit_small by lia;
              unfold w64; f_equal; lia|];
      split;
      [ eapply (cb_val_at _ _ (w_H W) m 1%nat _ 0x210 4%N _ _ F _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia] |];
      split;
      [ eapply (cb_val_at _ _ (w_H W) m 1%nat _ 0x214 4%N _ _ F _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia] |];
      split;
      [ eapply (cb_val_at _ _ (w_H W) m 2%nat _ (0x218 + n0) 1%N _ _ F _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia] |];
      split;
      [ first
        [ eapply (cb_val_at _ _ (w_H W) m 2%nat _ (0x219 + n0) 1%N _ _ F _);
            [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]
        | eapply (hb1_zero_at _ _ (w_H W) m 2%nat _ (0x219 + n0) 2 0 _);
            [exact HS | reflexivity | hb1_in | lia | cbn [YP09.r_base base_val]; rewrite B32; lia] ] |];
      first
      [ eapply (cb_val_at _ _ (w_H W) m 2%nat _ (0x21a + n0) 1%N _ _ F _);
          [exact HS | reflexivity | hb1_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]
      | eapply (hb1_zero_at _ _ (w_H W) m 2%nat _ (0x219 + n0) 2 1 _);
          [exact HS | reflexivity | hb1_in | lia | cbn [YP09.r_base base_val]; rewrite B32; lia] ]
      end ]) ]
 end).
Qed.
End d.
End b.

Print Assumptions hb1_tail.
