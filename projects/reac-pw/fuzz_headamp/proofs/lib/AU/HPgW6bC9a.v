(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC9.v at f3898085bda (c9_model, the
   register helpers, blocks A and C with their entry states), with the block post w7_post / w7_post_of_run of
   proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v and kept_run of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at
   the same commit (the licence lines above are theirs), for reac-pw/fuzz_headamp's image B: image B's pcs, the
   e62 pod object at F+0x210 read through R+0x130, R+0x118, R+0x40, pp through R+0x148 and R+0x138, the two
   pointer-overflow tests of the head, s7 set in the head, the tail's moves into t1, s4, a3 and s2, and image B's
   code table HPgW6bBase.hb_tbl. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the two engine runs of
   ent_build's case 9 (the default arm of the `switch (kind % 10)`, pod.h:367-377) in LLVMFuzzerTestOneInput
   (0x80c40), on each side of its one call. Proves no function (kind: segment lemma).

   THE HEAD  0x82004 .. the `jal` at 0x82054 (-> __asan_memcpy 0x51d8c, which returns at 0x82058):
     ld a0,0x130(s1)                      a0 := [R+0x130] = F + 0x210 (&e62)
     a1 := 14; sw a1,0(a0); sw a1,8(a0)   e62.type := POD_STRUCT, e62.body[0..4) := 14
     a0 := -5; ld a1,0x118(s1)            a1 := [R+0x118] = F + 0x218 (&e62.body)
     ld s7,0x148(s1)                      s7 := [R+0x148] = pp
     bgeu a0,a1 0x82028                   the pointer-overflow test of body + 4: taken (else `j` 0x83a14, unimp)
     ld a0,0x130(s1); a1 := 8; sw a1,0xc(a0)   e62.body[4..8) := POD_STRING
     a0 := -9; ld a1,0x118(s1); bgeu a0,a1 0x82044   the test of body + 8: taken (else 0x83a14)
     a1 := 0x21160 (ent_build.s, auipc/addi); a2 := 14; ld a0,0x40(s1) (a0 := [R+0x40] = F + 0x220 = &e62.body[8])
     jal 0x51d8c                          ra := 0x82058
   THE TAIL  0x82058 .. J 0x82618:
     ld a0,0x130(s1); a1 := 24; sw a1,4(a0)   e62.size := 24
     mv t1,s4 (t1 := |r|, what is left); mv s4,a0 (s4 := &e62); j 0x82610
     mv a3,s2 (a3 := the cursor c); ld s2,0x138(s1) (s2 := [R+0x138] = pp + 0x4000 = &pp->len)
   The case reads no input byte and its code holds no shadow check: each run is one run of the plain engine over
   HPgW6bBase.hb_tbl. The engine decides both `bgeu` tests from the interval of atom 32 = F
   ([4096, 0x7fffff800000]: F + 0x218 <= 2^64 - 9), so the two `unimp` arms are never stepped.
   The head's state reads the four R-cells R+0x40, R+0x118, R+0x130, R+0x148 and writes e62's first 16 bytes; the
   tail's reads R+0x130 and R+0x138 and writes e62's size word. The call between them and the case's post are in
   lib/AU/HPgW6bC9.v. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSteps HPgCaseBJ HPgW6bBase HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition H9_RET : Z := 0x82058.      (* after the `jal` to __asan_memcpy at 0x82054 *)

(* ===================== the head's symbolic state =====================
   The registers are their own atoms; the extra atoms are 32 = F (the frame for locals) and 33 = pp.
     rRa  [R+0x40, R+0x150)  read only, with the four cells the head loads:
          R+0x40 = F + 0x220, R+0x118 = F + 0x218, R+0x130 = F + 0x210, R+0x148 = pp
     rEa  [F+0x210, F+0x220) written: e62.type and e62.body[0..8)
   Atom 32's interval decides the two pointer-overflow tests. *)
Definition h9_rRa : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x150 0 0
  [YP09.mkChunk 0x40 (CVal 8 (SOff 32 0x220)); YP09.mkChunk 0x118 (CVal 8 (SOff 32 0x218));
   YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210)); YP09.mkChunk 0x148 (CVal 8 (SOff 33 0))].
Definition h9_rEa : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x220 0x210 0x220 [].
Definition h9_facts : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (32%nat, mkAF 4096 0x7fffff800000 0)] [] [].
Definition ss_h9A : sstate := mkSS HB_D9 sr_atoms [h9_rRa; h9_rEa] None h9_facts.
Definition h9_extra (F pp : Z) : list word := [Z_to_bv 64 F; Z_to_bv 64 pp].
Definition h9_wrA (F : Z) : Z -> Prop := fun a => F + 0x210 <= a < F + 0x220.

(* ===================== the tail's symbolic state =====================
     rRc  [R+0x130, R+0x140) read only: R+0x130 = F + 0x210, R+0x138 = pp + 0x4000
     rEc  [F+0x214, F+0x218) written: e62.size *)
Definition h9_rRc : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x140 0 0
  [YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210)); YP09.mkChunk 0x138 (CVal 8 (SOff 33 0x4000))].
Definition h9_rEc : YP09.region := YP09.mkRegion (Some 32%nat) 0x214 0x218 0x214 0x218 [].
Definition ss_h9C : sstate := mkSS H9_RET sr_atoms [h9_rRc; h9_rEc] None h9_facts.
Definition h9_wrC (F : Z) : Z -> Prop := fun a => F + 0x214 <= a < F + 0x218.

(* ======================================== the model ======================================== *)
Lemma h9_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 9 ->
  ent_build (b :: r) = (Ent POD_STRUCT 24 (le32 14 ++ le32 POD_STRING ++ S9 ++ [NUL] ++ zeros 2), r).
Proof.
intros b r H. unfold ent_build, Cursor.fuzz_u8. cbv beta iota. rewrite H. reflexivity.
Qed.

Lemma h9_den_off : forall E n (v o : Z), bv_unsigned (ew E n) = v -> sv_denot E (SOff n o) = Z_to_bv 64 (v + o).
Proof. intros E n v o H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

(* every register outside hw6b_clob is callee-saved: the call in the middle of the case keeps it *)
Lemma h9_clob_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r hw6b_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr0 Hn. pose proof (u5_range r) as Hb.
assert (HI : forall z, bv_unsigned r = z -> In (Z_to_bv 5 z) hw6b_clob -> False).
{ intros z Hz Hmem. apply Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r), Hz. exact Hmem. }
unfold acallee_saved.
assert (H : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/
  bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 10 \/ bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/
  bv_unsigned r = 15 \/ bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/
  bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
  bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/
  bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
repeat (destruct H as [H|H];
  [ first [ lia
          | destruct (HI _ H ltac:(unfold hw6b_clob; cbv [In];
              repeat (first [left; apply bv_eq; reflexivity | right]))) ]
  | ]).
first [ lia
      | destruct (HI _ H ltac:(unfold hw6b_clob; cbv [In];
          repeat (first [left; apply bv_eq; reflexivity | right]))) ].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the register r of the engine's last state, as its symbolic value's denotation *)
Ltac h9_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.
Ltac h9_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Section d.
Variable B : asyms.

(* ===================== the head: 0x82004 -> __asan_memcpy 0x51d8c ===================== *)
Lemma h9_A_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F pp,
getr regs 9 = w64 R -> alloc_ceiling + T_SEG_STK <= R -> R + 0x220 <= 2 ^ 47 -> R mod 32 = 0 ->
4096 <= F -> F + 1024 <= alloc_ceiling -> 4096 <= pp -> pp + Layout.PP_SIZE <= alloc_ceiling ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x40) 8 (F + 0x220) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
(forall a, F + 0x210 <= a < F + 0x220 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (h9_extra F pp)) ss_h9A
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HB_D9) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F pp H9 HR1 HR2 HR32 HF1 HF2 Hp1 Hp2 V40 V118 V130 V148 Pe.
pose proof (@asan_consts rc) as (Hceil0 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
rewrite restrict_mkst_fx. set (E := Ereg regs (h9_extra F pp)).
assert (U9 : bv_unsigned (ew E 9) = R) by exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = pp).
{ subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (HR16 : R mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide R 32 ltac:(lia))) in HR32.
  destruct HR32 as [q Hq]. exists (2 * q). lia. }
unfold ss_h9A. apply (entry_st_ok_full rsegs); try change (Ereg regs (h9_extra F pp)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, h9_rRa.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ R 0x40 8 (SOff 32 0x220) (F + 0x220));
        [exact (h9_den_off E 32 F 0x220 U32) | change (8 * Z.of_N 8) with 64; lia | lia | exact V40].
    * apply (chunk_ok_val rsegs E _ R 0x118 8 (SOff 32 0x218) (F + 0x218));
        [exact (h9_den_off E 32 F 0x218 U32) | change (8 * Z.of_N 8) with 64; lia | lia | exact V118].
    * apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 32 0x210) (F + 0x210));
        [exact (h9_den_off E 32 F 0x210 U32) | change (8 * Z.of_N 8) with 64; lia | lia | exact V130].
    * apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 33 0) pp);
        [rewrite (h9_den_off E 33 pp 0 U33), Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact V148].
  + unfold region_ok, h9_rEa.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs). apply Pe. lia.
- apply pairwise_disjoint_of_extents; unfold h9_rRa, h9_rEa; cbn [map]; unfold extent_of_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    rewrite ?U9, ?U32. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]]. cbn [h9_facts f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite U9, U32. repeat split; try lia;
    first [change (2 ^ 4) with 16; exact HR16 | change (2 ^ 0) with 1; apply Z.mod_1_r].
Qed.

Lemma h9_A : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F pp,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> alloc_ceiling + T_SEG_STK <= R -> R + 0x220 <= 2 ^ 47 -> R mod 32 = 0 ->
4096 <= F -> F + 1024 <= alloc_ceiling -> 4096 <= pp -> pp + Layout.PP_SIZE <= alloc_ceiling ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x40) 8 (F + 0x220) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
(forall a, F + 0x210 <= a < F + 0x220 -> apresent (w_H W) memc a) ->
(forall a, F + 0x210 <= a < F + 0x220 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (cfg_at rsegs HB_D9 regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB_MEMCPY regs memc mdc
  [1; 10; 11; 12; 23]%bv (h9_wrA F)
  (fun regs2 mem2 => getr regs2 1 = w64 H9_RET /\ getr regs2 10 = w64 (F + 0x220) /\
     getr regs2 11 = w64 HB_S /\ getr regs2 12 = w64 14 /\ getr regs2 23 = w64 pp /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 14 /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x218) 4 14 /\
     val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x21c) 4 8)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp
  HJ H9 HR1 HR2 HR32 HF1 HF2 Hp1 Hp2 V40 V118 V130 V148 Pe HWR.
pose proof hb_wx as Hwx. pose proof hb_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof (@asan_consts rc) as (Hceil0 & _).
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
set (E := Ereg regs (h9_extra F pp)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(unfold T_SEG_STK, ASTACK in HR1; lia)). }
assert (U32 : bv_unsigned (ew E 32) = F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = pp).
{ subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs E ss_h9A (restrict (w_H W) (mkst regs (Z_to_bv 64 HB_D9) memc (seg_rom rsegs))))
  by exact (h9_A_entry W regs memc R F pp H9 HR1 HR2 HR32 HF1 HF2 Hp1 Hp2 V40 V118 V130 V148 Pe).
unfold cfg_at. change (w64 HB_D9) with (Z_to_bv 64 HB_D9).
aj_run_to hb_tbl_ok HS HJ HB_MEMCPY.
- lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp fp b0 bc lyx ow) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
    [ reflexivity | exact U32
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWR; lia
    | apply awr_ok_nil ].
- eapply (cb_post_of_run B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB_MEMCPY regs memc mdc);
    [exact HS | reflexivity | reflexivity | exact HJ | cb_kio | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs (h9_extra F pp) (w_H W) _ HS);
      [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (cb_kept_run (h9_wrA F) _ _ (w_H W) memc memc (ms_mem ms)
      (fun x _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (rg & Hin & Hb). cbv beta.
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
    unfold h9_wrA. destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U32 in Hb; lia.
  + cbv beta.
    split; [h9_reg HS; reflexivity|].
    split; [h9_reg HS; rewrite (h9_den_off E 32 F 0x220 U32); reflexivity|].
    split; [h9_reg HS; reflexivity|].
    split; [h9_reg HS; reflexivity|].
    split; [h9_reg HS; rewrite (h9_den_off E 33 pp 0 U33), Z.add_0_r; reflexivity|].
    split; [eapply (cb_val_at_rng E _ (w_H W) ms 1%nat _ 0x210 4%N _ 14 F (F + 0x210));
            [exact HS | reflexivity | h9_in | cbn [YP09.r_base base_val]; exact U32
            | reflexivity | cbn; lia | lia | lia]|].
    split; [eapply (cb_val_at_rng E _ (w_H W) ms 1%nat _ 0x218 4%N _ 14 F (F + 0x218));
            [exact HS | reflexivity | h9_in | cbn [YP09.r_base base_val]; exact U32
            | reflexivity | cbn; lia | lia | lia]|].
    eapply (cb_val_at_rng E _ (w_H W) ms 1%nat _ 0x21c 4%N _ 8 F (F + 0x21c));
      [exact HS | reflexivity | h9_in | cbn [YP09.r_base base_val]; exact U32
      | reflexivity | cbn; lia | lia | lia].
Qed.

(* ===================== the tail: 0x82058 -> J 0x82618 ===================== *)
Lemma h9_C_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R F pp,
getr regs 9 = w64 R -> alloc_ceiling + T_SEG_STK <= R -> R + 0x220 <= 2 ^ 47 -> R mod 32 = 0 ->
4096 <= F -> F + 1024 <= alloc_ceiling -> 4096 <= pp -> pp + Layout.PP_SIZE <= alloc_ceiling ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
(forall a, F + 0x214 <= a < F + 0x218 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (h9_extra F pp)) ss_h9C
  (restrict (w_H W) (mkst regs (Z_to_bv 64 H9_RET) memc (seg_rom rsegs))).
Proof.
intros W regs memc R F pp H9 HR1 HR2 HR32 HF1 HF2 Hp1 Hp2 V130 V138 Pe.
pose proof (@asan_consts rc) as (Hceil0 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
rewrite restrict_mkst_fx. set (E := Ereg regs (h9_extra F pp)).
assert (U9 : bv_unsigned (ew E 9) = R) by exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = pp).
{ subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (HR16 : R mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide R 32 ltac:(lia))) in HR32.
  destruct HR32 as [q Hq]. exists (2 * q). lia. }
unfold ss_h9C. apply (entry_st_ok_full rsegs); try change (Ereg regs (h9_extra F pp)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, h9_rRc.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 32 0x210) (F + 0x210));
        [exact (h9_den_off E 32 F 0x210 U32) | change (8 * Z.of_N 8) with 64; lia | lia | exact V130].
    * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 33 0x4000) (pp + 0x4000));
        [exact (h9_den_off E 33 pp 0x4000 U33) | change (8 * Z.of_N 8) with 64; lia | lia | exact V138].
  + unfold region_ok, h9_rEc.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs). apply Pe. lia.
- apply pairwise_disjoint_of_extents; unfold h9_rRc, h9_rEc; cbn [map]; unfold extent_of_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    rewrite ?U9, ?U32. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]]. cbn [h9_facts f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite U9, U32. repeat split; try lia;
    first [change (2 ^ 4) with 16; exact HR16 | change (2 ^ 0) with 1; apply Z.mod_1_r].
Qed.

Lemma h9_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F pp c n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> alloc_ceiling + T_SEG_STK <= R -> R + 0x220 <= 2 ^ 47 -> R mod 32 = 0 ->
4096 <= F -> F + 1024 <= alloc_ceiling -> 4096 <= pp -> pp + Layout.PP_SIZE <= alloc_ceiling ->
getr regs 18 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 20 = w64 n -> 0 <= n < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
(forall a, F + 0x214 <= a < F + 0x218 -> apresent (w_H W) memc a) ->
(forall a, F + 0x214 <= a < F + 0x218 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (cfg_at rsegs H9_RET regs memc mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB_J regs memc mdc
  [6; 10; 11; 13; 18; 20]%bv (h9_wrC F)
  (fun regs2 mem2 => getr regs2 6 = w64 n /\ getr regs2 13 = w64 c /\ getr regs2 18 = w64 (pp + 0x4000) /\
     getr regs2 20 = w64 (F + 0x210) /\ val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 24)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp c n
  HJ H9 HR1 HR2 HR32 HF1 HF2 Hp1 Hp2 H18 Hc H20 Hn V130 V138 Pe HWE.
pose proof hb_wx as Hwx. pose proof hb_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof (@asan_consts rc) as (Hceil0 & _).
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
set (E := Ereg regs (h9_extra F pp)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(unfold T_SEG_STK, ASTACK in HR1; lia)). }
assert (U18 : bv_unsigned (ew E 18) = c) by exact (hb_U_reg regs _ 18 18%bv c eq_refl H18 Hc).
assert (U20 : bv_unsigned (ew E 20) = n) by exact (hb_U_reg regs _ 20 20%bv n eq_refl H20 Hn).
assert (U32 : bv_unsigned (ew E 32) = F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = pp).
{ subst E. rewrite (ew_Ereg_extra regs _ 1). cbn [nth h9_extra]. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs E ss_h9C (restrict (w_H W) (mkst regs (Z_to_bv 64 H9_RET) memc (seg_rom rsegs))))
  by exact (h9_C_entry W regs memc R F pp H9 HR1 HR2 HR32 HF1 HF2 Hp1 Hp2 V130 V138 Pe).
unfold cfg_at. change (w64 H9_RET) with (Z_to_bv 64 H9_RET).
aj_run_to hb_tbl_ok HS HJ HB_J.
- lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp fp b0 bc lyx ow) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
    [ reflexivity | exact U32
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWE; lia
    | apply awr_ok_nil ].
- eapply (cb_post_of_run B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HB_J regs memc mdc);
    [exact HS | reflexivity | reflexivity | exact HJ | cb_kio | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs (h9_extra F pp) (w_H W) _ HS);
      [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (cb_kept_run (h9_wrC F) _ _ (w_H W) memc memc (ms_mem ms)
      (fun x _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (rg & Hin & Hb). cbv beta.
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
    unfold h9_wrC. destruct Hin as [<-|[<-|[]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U32 in Hb; lia.
  + cbv beta.
    split; [h9_reg HS; rewrite (h9_den_off E 20 n 0 U20); unfold w64; f_equal; lia|].
    split; [h9_reg HS; rewrite (h9_den_off E 18 c 0 U18); unfold w64; f_equal; lia|].
    split; [h9_reg HS; rewrite (h9_den_off E 33 pp 0x4000 U33); reflexivity|].
    split; [h9_reg HS; rewrite (h9_den_off E 32 F 0x210 U32); reflexivity|].
    eapply (cb_val_at_rng E _ (w_H W) ms 1%nat _ 0x214 4%N _ 24 F (F + 0x214));
      [exact HS | reflexivity | h9_in | cbn [YP09.r_base base_val]; exact U32
      | reflexivity | cbn; lia | lia | lia].
Qed.

End d.
End b.

Print Assumptions h9_model.
Print Assumptions h9_clob_cs.
Print Assumptions h9_A.
Print Assumptions h9_C.
