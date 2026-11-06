(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build (lib/A).
   The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/IngestSegName.v; 399 of its 445 lines of code are new or changed and 1026 lines of the source are left out. *)
(* sb_dec's segment C (fuzz_identity.asan 0x836e8 .. the ret at 0x8377c, 38 slots; sb_dec_inv.v seg_sbd_C): from the
   end of the emit loop (sbd_B_end) to tsb_dec_post. One plain run from 0x836e8 to the ret:
     0x836e8..0x836f8  shadow byte 4 of the frame := 0xf8, the frame's first word := 0x45e0360e;
     0x836fc           beqz a0 (a0 = the frame, at least 4096: not taken);
     0x83700..0x83720  the frame's 8 shadow bytes := 0xf5;
     0x83724..0x83728  ld a0,56(a0) (the flag address) and sb zero,0(a0): the release of the side-stack frame
                       (IdentFrame aj_flag_store_pi, own (0, pos) :: own -> own);
     0x8372c..0x8377c  j 0x83750, the epilogue (the nine saves at entry sp - 8 .. entry sp - 72), ret.
   The post: the caller's journal after the release, the callee-saved registers from the saves, tcj_kept carried
   across the release (its writes are the frame (0, pos), its shadow and the flag byte; none lies in a heap block
   or a frame of the entry state, in the image, or above the allocator ceiling), and the struct sb and the digits
   as segment B left them (the release writes none of their bytes). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 YC81 YC4b YC45 YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec sb_dec_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x836e8 -----------------------------------------------------------------------------
   Atoms: 0..31 the registers at the cut (8 = s0 = the entry sp, 16 = a6 = the frame F, 17 = a7 = F's shadow),
   32 = SB, 33 = the flag address FL, 34..42 = the entry values of ra, s0, s1, s2 .. s7 (the nine saves). a0 holds
   F too (sbd_common); the walk names it by atom 16, so that ld a0,56(a0) reads the frame region. *)
Definition sbc_rflag : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition sbc_rshadow : YP09.region := YP09.mkRegion (Some 17%nat) 0 8 0 8 [].
Definition sbc_rframe : YP09.region := YP09.mkRegion (Some 16%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 33 0))].
Definition sbc_rstack : YP09.region := YP09.mkRegion (Some 8%nat) (-72) 0 0 0
  [YP09.mkChunk (-8) (CVal 8 (SOff 34 0)); YP09.mkChunk (-16) (CVal 8 (SOff 35 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 36 0)); YP09.mkChunk (-32) (CVal 8 (SOff 37 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 38 0)); YP09.mkChunk (-48) (CVal 8 (SOff 39 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 40 0)); YP09.mkChunk (-64) (CVal 8 (SOff 41 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 42 0))].
Definition sbc_rs0 : smem := [sbc_rflag; sbc_rshadow; sbc_rframe; sbc_rstack].
Definition sbc_facts0 : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (16%nat, mkAF 4096 (2 ^ 47) 6);
           (17%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (33%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition sbc_ss0 : sstate := mkSS (AF_sb_dec + SBD_B_END) sr_atoms sbc_rs0 None sbc_facts0.
Definition sbc_extra (regs0 : bvmap 5 word) (fl : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 fl; getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19;
   getr regs0 20; getr regs0 21; getr regs0 22; getr regs0 23].

(* The bytes the run may write: the flag byte, the frame's shadow, the frame's first word. *)
Lemma sbc_wrange : forall E a, in_wrange E sbc_rs0 a ->
  bv_unsigned (ew E 33) <= a < bv_unsigned (ew E 33) + 1 \/
  bv_unsigned (ew E 17) <= a < bv_unsigned (ew E 17) + 8 \/
  bv_unsigned (ew E 16) <= a < bv_unsigned (ew E 16) + 8.
Proof.
intros E a (r & Hr & Ha). unfold sbc_rs0 in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | []]]]];
unfold sbc_rflag, sbc_rshadow, sbc_rframe, sbc_rstack in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
Qed.
Lemma sbc_mbyte_kept : forall segs E rs (m m' : word -> option byte) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> mbyte segs m' a = mbyte segs m a.
Proof.
intros segs E rs m m' a HF Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
Lemma sbc_val_mem_kept : forall segs (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros segs m m' a n v Hk Hv k Hkn. rewrite (Hk k Hkn). exact (Hv k Hkn). Qed.
Lemma sbc_present_grows : forall (H : word -> bool) (m1 m2 : word -> option byte) a,
  mem_grows (mrestrict H m1) (mrestrict H m2) -> apresent H m1 a -> apresent H m2 a.
Proof.
intros H m1 m2 a HG (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
rewrite Hh, Hb in HG. destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
exfalso. apply HG; [discriminate | reflexivity].
Qed.
Lemma sbc_u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof. intros x. exact (bv_unsigned_in_range 64 x). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma sbc_ew_low : forall (regs2 : bvmap 5 word) extra (i : nat) (r : bv 5),
  Z.of_nat i = bv_unsigned r -> ew (Eimg (Ereg regs2 extra)) i = getr regs2 r.
Proof.
intros regs2 extra i r Hi. pose proof (bv_unsigned_in_range 5 r) as Q. change (bv_modulus 5) with 32 in Q.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hi.
Qed.
Lemma sbc_ew_extra : forall (regs2 : bvmap 5 word) extra (j : nat),
  (j < 200)%nat -> ew (Eimg (Ereg regs2 extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs2 extra j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma sbc_aview_kept : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) a,
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m2 a = aview SEGS H m1 a.
Proof.
intros E rs H m1 m2 a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* The start state holds at the cut. *)
Lemma sbc_start : forall (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (W : world SEGS) sp F FL,
  getr regs2 8 = w64 sp -> getr regs2 16 = w64 F -> getr regs2 17 = w64 (SB + F / 8) ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling + 72 <= sp ->
  4096 <= F -> F + 64 <= alloc_ceiling -> in_app F 64 -> F mod 64 = 0 ->
  4096 <= FL -> FL < alloc_ceiling -> app_addr FL -> (FL < F \/ F + 64 <= FL) ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem2 a) ->
  (forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (SB + F / 8 + i)) ->
  apresent (w_H W) mem2 FL ->
  val_mem SEGS (rd W mem2) (F + 56) 8 FL ->
  val_mem SEGS (rd W mem2) (sp - 8) 8 (raZ regs0) ->
  val_mem SEGS (rd W mem2) (sp - 16) 8 (bv_unsigned (getr regs0 8)) ->
  val_mem SEGS (rd W mem2) (sp - 24) 8 (bv_unsigned (getr regs0 9)) ->
  val_mem SEGS (rd W mem2) (sp - 32) 8 (bv_unsigned (getr regs0 18)) ->
  val_mem SEGS (rd W mem2) (sp - 40) 8 (bv_unsigned (getr regs0 19)) ->
  val_mem SEGS (rd W mem2) (sp - 48) 8 (bv_unsigned (getr regs0 20)) ->
  val_mem SEGS (rd W mem2) (sp - 56) 8 (bv_unsigned (getr regs0 21)) ->
  val_mem SEGS (rd W mem2) (sp - 64) 8 (bv_unsigned (getr regs0 22)) ->
  val_mem SEGS (rd W mem2) (sp - 72) 8 (bv_unsigned (getr regs0 23)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs2 (sbc_extra regs0 FL))) sbc_ss0
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_B_END))) mem2 (seg_rom SEGS))).
Proof.
intros regs0 regs2 mem2 W sp F FL R8 R16 R17 Hsp Hsp16 Hspc HF0 HFc HFapp HF64 HL0 HLc HLapp HLF HFp HSp HLp VF
  V1 V2 V3 V4 V5 V6 V7 V8 V9.
pose proof asan_consts as (C1 & _).
assert (DF : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite DF at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.div_mul. lia. }
assert (HF8r : 512 <= F / 8 <= 2 ^ 44 - 8) by (rewrite HF8; lia).
remember (Eimg (Ereg regs2 (sbc_extra regs0 FL))) as E eqn:HE.
assert (EL : forall (i : nat) (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r)
  by (intros i r Hi; rewrite HE; exact (sbc_ew_low regs2 _ i r Hi)).
assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j (sbc_extra regs0 FL) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; apply sbc_ew_extra; clear - Hj; lia).
pose proof (EL 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EL 16%nat 16%bv eq_refl) as E16. rewrite R16 in E16.
pose proof (EL 17%nat 17%bv eq_refl) as E17. rewrite R17 in E17.
pose proof (EX 1%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E33.
pose proof (EX 2%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E34.
pose proof (EX 3%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E35.
pose proof (EX 4%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E36.
pose proof (EX 5%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E37.
pose proof (EX 6%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E38.
pose proof (EX 7%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E39.
pose proof (EX 8%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E40.
pose proof (EX 9%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E41.
pose proof (EX 10%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E42.
unfold sbc_extra in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
cbn [Nat.add nth] in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
assert (U8 : bv_unsigned (ew E 8) = sp) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (U16 : bv_unsigned (ew E 16) = F) by (rewrite E16; unfold w64; apply unsigned_lit_small; lia).
assert (U17 : bv_unsigned (ew E 17) = SB + F / 8) by (rewrite E17; unfold w64; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
assert (SV : forall (i : nat) (w : word), ew E i = w -> sv_denot E (SOff i 0) = Z_to_bv 64 (bv_unsigned w)).
{ intros i w Hi. cbn [sv_denot]. rewrite Hi, Z.add_0_r. reflexivity. }
unfold sbc_ss0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sbc_rs0, sbc_rflag, sbc_rshadow, sbc_rframe, sbc_rstack.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HLp.
  + rewrite U17. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HSp. lia.
  + rewrite U16. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply HFp. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 56 8 (SOff 33 0) FL); [| cbn; lia | cbn; lia | exact VF].
      cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons); [ | | | | | | | | | apply Forall_nil].
    * apply (chunk_ok_val SEGS E _ sp (-8) 8 (SOff 34 0) (raZ regs0)); [exact (SV _ _ E34) | apply sbc_u64 | cbn; lia |].
      replace (sp + -8) with (sp - 8) by lia. exact V1.
    * apply (chunk_ok_val SEGS E _ sp (-16) 8 (SOff 35 0) (bv_unsigned (getr regs0 8))); [exact (SV _ _ E35) | apply sbc_u64 | cbn; lia |].
      replace (sp + -16) with (sp - 16) by lia. exact V2.
    * apply (chunk_ok_val SEGS E _ sp (-24) 8 (SOff 36 0) (bv_unsigned (getr regs0 9))); [exact (SV _ _ E36) | apply sbc_u64 | cbn; lia |].
      replace (sp + -24) with (sp - 24) by lia. exact V3.
    * apply (chunk_ok_val SEGS E _ sp (-32) 8 (SOff 37 0) (bv_unsigned (getr regs0 18))); [exact (SV _ _ E37) | apply sbc_u64 | cbn; lia |].
      replace (sp + -32) with (sp - 32) by lia. exact V4.
    * apply (chunk_ok_val SEGS E _ sp (-40) 8 (SOff 38 0) (bv_unsigned (getr regs0 19))); [exact (SV _ _ E38) | apply sbc_u64 | cbn; lia |].
      replace (sp + -40) with (sp - 40) by lia. exact V5.
    * apply (chunk_ok_val SEGS E _ sp (-48) 8 (SOff 39 0) (bv_unsigned (getr regs0 20))); [exact (SV _ _ E39) | apply sbc_u64 | cbn; lia |].
      replace (sp + -48) with (sp - 48) by lia. exact V6.
    * apply (chunk_ok_val SEGS E _ sp (-56) 8 (SOff 40 0) (bv_unsigned (getr regs0 21))); [exact (SV _ _ E40) | apply sbc_u64 | cbn; lia |].
      replace (sp + -56) with (sp - 56) by lia. exact V7.
    * apply (chunk_ok_val SEGS E _ sp (-64) 8 (SOff 41 0) (bv_unsigned (getr regs0 22))); [exact (SV _ _ E41) | apply sbc_u64 | cbn; lia |].
      replace (sp + -64) with (sp - 64) by lia. exact V8.
    * apply (chunk_ok_val SEGS E _ sp (-72) 8 (SOff 42 0) (bv_unsigned (getr regs0 23))); [exact (SV _ _ E42) | apply sbc_u64 | cbn; lia |].
      replace (sp + -72) with (sp - 72) by lia. exact V9.
- apply pairwise_disjoint_of_extents. unfold sbc_rs0, sbc_rflag, sbc_rshadow, sbc_rframe, sbc_rstack.
  cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U17, U16, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  repeat split; lia.
- split; [|split; exact I].
  unfold sbc_facts0. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U8, U16, U17, U33.
  assert (M17 : (SB + F / 8) mod 2 ^ 3 = 0).
  { rewrite HF8. unfold SB. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
    change (2 ^ 3) with 8. apply Z_mod_mult. }
  change (2 ^ 4) with 16. change (2 ^ 6) with 64. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; unfold SB; lia.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).

(* What the call has kept of its entry state survives a run that wrote only bytes outside K's complement. *)
Lemma sbc_tcj_kept : forall STK lyc Sc W memc m1 m2 sp (Er K : Z -> Prop),
  tcj_kept B STK lyc Sc W memc W m1 sp Er ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> K a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> K (b + i)) ->
  (forall a, in_img SEGS a -> K a) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) -> K a) ->
  (forall a, K a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
  tcj_kept B STK lyc Sc W memc W m2 sp Er.
Proof.
intros STK lyc Sc W memc m1 m2 sp Er K (T1 & T2 & T3 & T4 & T5 & T6) K1 K2 K3 K4 HK HP.
split; [intros a Ha Hw He; rewrite (HK a (K1 a Ha)); exact (T1 a Ha Hw He)|].
split; [intros b m i Hin Hi He; rewrite (HK _ (K2 b m i Hin Hi)); exact (T2 b m i Hin Hi He)|].
split; [intros a Hi Hns He; rewrite (HK a (K3 a Hi)); exact (T3 a Hi Hns He)|].
split; [intros cid pos a Hin Hr He; rewrite (HK a (K4 cid pos a Hin Hr)); exact (T4 cid pos a Hin Hr He)|].
split; [intros a Ha Hw Hp; exact (HP a (T5 a Ha Hw Hp))|].
intros a Ha. exact (HP a (T6 a Ha)).
Qed.

(* The release's bytes (the flag byte, the frame (0, pos) and its shadow) lie below the allocator ceiling, off the
   image, and in no heap block and no frame zone of the entry state. *)
Lemma sbc_apart : forall ly2 S2 W mem2 md2 lyc Sc pos a,
  AR SEGS B ly2 S2 W mem2 md2 -> frames S2 = (0, pos) :: frames Sc ->
  ablocks B ly2 S2 = ablocks B lyc Sc ->
  (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  (a = flag_addr ly2 0 pos \/ in_zr a (frame_rng ly2 (0, pos)) \/
   in_zr a (shadow_addr (frame_addr ly2 0 pos), fs_frame_bytes 0 / 8)) ->
  a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size m)) /\
  (forall cid q, In (cid, q) (frames Sc) ->
     ~ (in_zr a (frame_rng lyc (cid, q)) \/ in_zr a (shadow_addr (frame_addr lyc cid q), fs_frame_bytes cid / 8))).
Proof.
intros ly2 S2 W mem2 md2 lyc Sc pos a HAR Hfrs Hab Efa Ha.
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL ly2 S2 W mem2 md2 0 pos HAR Hin) as (_ & HFLo & (_ & HFLimg) & (_ & _ & HFLc)).
destruct Ha as [-> | Hz].
- split; [exact HFLc|]. split; [exact HFLimg|]. split.
  + intros b m Hb Hr. rewrite <- Hab in Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & Hbp & _).
    exact (proj2 (Hbp _ Hr) HFLo).
  + intros cid q Hq Hr. assert (Hq2 : In (cid, q) (frames S2)) by (rewrite Hfrs; right; exact Hq).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid q HAR Hq2) as (_ & _ & Hfp & Hsp).
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- !Efa in Hr.
    destruct Hr as [Hr | Hr]; [exact (proj2 (Hfp _ Hr) HFLo)|].
    pose proof (Hsp (flag_addr ly2 0 pos - shadow_addr (frame_addr ly2 cid q)) ltac:(lia)) as (_ & Hno).
    replace (shadow_addr (frame_addr ly2 cid q) + (flag_addr ly2 0 pos - shadow_addr (frame_addr ly2 cid q)))
      with (flag_addr ly2 0 pos) in Hno by ring.
    exact (Hno HFLo).
- pose proof (frame_zone SEGS B LAWS ly2 S2 W mem2 md2 0 pos a HAR Hin Hz) as (Hc & Hz').
  split; [exact Hc|]. split.
  + intros Him. pose proof (pa_segs_low a Him) as Hlo. destruct Hz' as [(Hf & _) | Hs].
    * exact (frm_img SEGS B LAWS ly2 S2 W mem2 md2 0 pos a HAR Hin Hf Him).
    * lia.
  + split.
    * intros b m Hb Hr. rewrite <- Hab in Hb.
      apply (block_not_frame_zone SEGS B LAWS ly2 S2 W mem2 md2 b m (a - b) 0 pos HAR Hb Hin ltac:(lia)).
      replace (b + (a - b)) with a by ring. exact Hz.
    * intros cid q Hq Hr. apply in_split in Hq as (l2 & l3 & Eq).
      apply (frames_zone_disj SEGS B LAWS ly2 S2 W mem2 md2 (0, pos) (cid, q) [] l2 l3 a HAR).
      -- rewrite Hfrs, Eq. reflexivity.
      -- cbn [fst snd]. exact Hz.
      -- unfold frame_rng in *. cbn [fst snd] in *. rewrite !Efa. exact Hr.
Qed.

Ltac sbc_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [sv_denot] in Hr; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hr
  end.

Theorem seg_sbd_C_holds : seg_sbd_C B.
Proof.
unfold seg_sbd_C. intros g pos W2 c2 Hpre HBe.
destruct g as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs0 b v md p cap n ov].
unfold sbd_pre in Hpre. unfold sbd_B_end, sbd_cut, sbd_common in HBe. unfold tsb_dec_rec_at in Hpre.
unfold sq_sp, sq_F, sq_acc, sq_over, sq_kd, sq_D in *.
cbn [sq_STK sq_sp0 sq_FP sq_ly sq_S sq_W0 sq_mem0 sq_md0 sq_own sq_lyc sq_Sc sq_W sq_memc sq_mdc sq_k sq_regs
  sq_b sq_v sq_md sq_p sq_cap sq_n sq_ov] in *.
destruct HBe as (-> & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & Hab & _ & HC & HP).
destruct HP as (Vp & Vcap & Vn & Vov & Vd).
destruct HC as (R8 & (sp1 & _ & _ & _ & _) & R3 & R4 & R24 & R25 & R26 & R27 & R10 & R16 & R17 & _ & _ &
  Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Hflag).
destruct Hpre as (HJc & Hra & _ & _ & _ & Hal16 & Hwin & Hsp & _ & _ & _ & _ & _ & _ & Hb0 & Hb63 & _ &
  Hrec & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQ & _ & _ & _).
pose proof (proj1 HJ) as HAR2. pose proof (proj1 HJc) as HARc.
pose proof HJ as (_ & Hly2 & _ & _ & _ & Hfrs2 & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (EF : ly_F ly2 = ly_F lyc).
{ destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Eslo : ly_stk_lo lyc = ly_stk_lo ly) by (destruct Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
assert (Efa : forall c q, frame_addr ly2 c q = frame_addr lyc c q) by (intros c q; unfold frame_addr; rewrite EF; reflexivity).
assert (Efl : forall c q, flag_addr ly2 c q = flag_addr lyc c q) by (intros c q; unfold flag_addr; rewrite EF; reflexivity).
assert (HfrsS2 : frames S2 = (0, pos) :: frames Sc) by (rewrite Hfrs2, Hfrsc; reflexivity).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite HfrsS2; left; reflexivity).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Hspr : alloc_ceiling + 4208 <= spZ regs0 <= 2 ^ 47) by (clear - Hwin Hsp Hceil Hslo Hshi H47 WS; lia).
assert (Hbc : alloc_ceiling <= b) by (destruct Hrec as [Hr1 _]; clear - Hr1 Eslo Hceil; lia).
destruct (frames_bounds SEGS B LAWS ly2 S2 W mem2 md2 0 pos HAR2 Hin2) as (HF0 & HFc & HFapp).
destruct (frame_al64 SEGS B ly2 S2 W mem2 md2 0 pos HAR2 Hin2) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W mem2 md2 0 pos HAR2 Hin2) as (_ & _ & HFp & HSp).
destruct (FFL ly2 S2 W mem2 md2 0 pos HAR2 Hin2) as (HLp & HLo & (HLapp & _) & (HL0 & _ & HLc)).
rewrite Efa in HF0, HFc, HFapp, HF64, HFp, HSp. rewrite Efl in HLp, HLo, HLapp, HL0, HLc.
change (fs_frame_bytes 0 / 8) with 8 in HSp. change (fs_frame_bytes 0) with 64 in HFc, HFapp, HFp, Hflag.
unfold shadow_addr in HSp. rewrite <- SB_SHADOW_OFF in HSp.
assert (HLF : flag_addr lyc 0 pos < frame_addr lyc 0 pos \/ frame_addr lyc 0 pos + 64 <= flag_addr lyc 0 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 0 pos) (frame_addr lyc 0 pos)) as [H|H]; [left; exact H|].
  destruct (Z_lt_le_dec (flag_addr lyc 0 pos) (frame_addr lyc 0 pos + 64)) as [H'|H']; [|right; exact H'].
  exfalso. exact (proj2 (HFp _ (conj H H')) HLo). }
(* the start state *)
remember (Eimg (Ereg regs2 (sbc_extra regs0 (flag_addr lyc 0 pos)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall (i : nat) (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r)
  by (intros i r Hi; rewrite HE; exact (sbc_ew_low regs2 _ i r Hi)).
assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j (sbc_extra regs0 (flag_addr lyc 0 pos)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; apply sbc_ew_extra; clear - Hj; lia).
pose proof (EX 1%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E33. pose proof (EX 2%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E34.
pose proof (EX 3%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E35. pose proof (EX 4%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E36.
pose proof (EX 5%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E37. pose proof (EX 6%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E38.
pose proof (EX 7%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E39. pose proof (EX 8%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E40.
pose proof (EX 9%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E41. pose proof (EX 10%nat ltac:(apply Nat.ltb_lt; reflexivity)) as E42.
unfold sbc_extra in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
cbn [Nat.add nth] in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
assert (U33 : bv_unsigned (ew E 33) = flag_addr lyc 0 pos)
  by (rewrite E33; apply unsigned_lit_small; clear - HL0 HLc C1; lia).
assert (U16 : bv_unsigned (ew E 16) = frame_addr lyc 0 pos)
  by (rewrite (EL 16%nat 16%bv eq_refl), R16; unfold w64; apply unsigned_lit_small; clear - HF0 HFc C1; lia).
assert (HF8m : 0 <= frame_addr lyc 0 pos / 8 < 2 ^ 44).
{ clear - HF0 HFc C1. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (U17 : bv_unsigned (ew E 17) = SB + frame_addr lyc 0 pos / 8)
  by (rewrite (EL 17%nat 17%bv eq_refl), R17; unfold w64; apply unsigned_lit_small; clear - HF8m; unfold SB; lia).
assert (HS0 : st_ok_pi SEGS VAL E sbc_ss0
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_B_END))) mem2 (seg_rom SEGS)))).
{ rewrite HE. apply (sbc_start regs0 regs2 mem2 W (spZ regs0) (frame_addr lyc 0 pos) (flag_addr lyc 0 pos) R8 R16 R17
    ltac:(clear - Hspr C1; lia) Hal16 ltac:(clear - Hspr; lia) HF0 HFc HFapp HF64 HL0 HLc HLapp HLF
    (fun a Ha => proj1 (HFp a ltac:(clear - Ha; lia))) (fun i Hi => proj1 (HSp i Hi)) HLp);
  [|exact Q1|exact Q2|exact Q3|exact Q4|exact Q5|exact Q6|exact Q7|exact Q8|exact Q9].
  replace (frame_addr lyc 0 pos + 56) with (frame_addr lyc 0 pos + 64 - 8) by ring.
  exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 16 0) HS0 ltac:(vm_compute; reflexivity)
  ltac:(rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite U16, Z.add_0_r, R10; reflexivity)) as HS.
clear HS0.
(* where the run may write *)
assert (Hwr_W : forall a, in_wrange E sbc_rs0 a ->
  a = flag_addr ly2 0 pos \/ in_zr a (frame_rng ly2 (0, pos)) \/
  in_zr a (shadow_addr (frame_addr ly2 0 pos), fs_frame_bytes 0 / 8)).
{ intros a Ha. apply sbc_wrange in Ha. rewrite U33, U17, U16 in Ha.
  unfold frame_rng, in_zr, shadow_addr. cbn [fst snd]. rewrite Efl, !Efa.
  change (fs_frame_bytes 0 / 8) with 8. change (fs_frame_bytes 0) with 64. rewrite <- SB_SHADOW_OFF.
  clear - Ha. lia. }
assert (HAP : forall a, in_wrange E sbc_rs0 a ->
  a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall bb m, In (bb, m) (ablocks B lyc Sc) -> ~ (bb <= a < bb + req_size m)) /\
  (forall cid q, In (cid, q) (frames Sc) ->
     ~ (in_zr a (frame_rng lyc (cid, q)) \/ in_zr a (shadow_addr (frame_addr lyc cid q), fs_frame_bytes cid / 8))))
  by (intros a Hin; exact (sbc_apart ly2 S2 W mem2 md2 lyc Sc pos a HAR2 HfrsS2 Hab Efa (Hwr_W a Hin))).
(* the run: the release, the epilogue, up to the ret *)
unfold cfg_at, A_sb_dec, w64.
replace (BASE + AF_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END)) by ring.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_B_END))) mem2 (seg_rom SEGS))) in HJ.
paj_run_flag_sh RUNF HS HJ.
- apply Z.le_refl.
- intros a Ha. cbn [ss_mem] in Ha. destruct (Hwr_W a Ha) as [Ha' | [Ha' | Ha']].
  + right. exact Ha'.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. left. exact Ha'.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. right. exact Ha'.
- intros msr HSr. rewrite Efl.
  pose proof (st_ok_pi_region_nth E _ msr 0 _ HSr eq_refl) as HR.
  pose proof (field_of_region E (ms_mem msr) 33%nat (flag_addr lyc 0 pos) _ 0 1 0 1 0 1%N (SLit 0) 0 HR U33
    ltac:(left; reflexivity) eq_refl ltac:(split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity)
    ltac:(apply Z.leb_le; reflexivity)) as V.
  pose proof (V 0%nat ltac:(apply Nat.ltb_lt; reflexivity)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0.
- cbn [ms_mem mkst] in HF, HFr, HG.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  sbc_reg HS (1%bv : bv 5) F1. rewrite E34 in F1.
  sbc_reg HS (2%bv : bv 5) F2. rewrite (EL 8%nat 8%bv eq_refl), R8 in F2. unfold w64, spZ in F2. rewrite Z_to_bv_bv_unsigned in F2.
  sbc_reg HS (3%bv : bv 5) F3. rewrite (EL 3%nat 3%bv eq_refl), R3 in F3.
  sbc_reg HS (4%bv : bv 5) F4. rewrite (EL 4%nat 4%bv eq_refl), R4 in F4.
  sbc_reg HS (8%bv : bv 5) F8. rewrite E35 in F8.
  sbc_reg HS (9%bv : bv 5) F9. rewrite E36 in F9.
  sbc_reg HS (18%bv : bv 5) F18. rewrite E37 in F18.
  sbc_reg HS (19%bv : bv 5) F19. rewrite E38 in F19.
  sbc_reg HS (20%bv : bv 5) F20. rewrite E39 in F20.
  sbc_reg HS (21%bv : bv 5) F21. rewrite E40 in F21.
  sbc_reg HS (22%bv : bv 5) F22. rewrite E41 in F22.
  sbc_reg HS (23%bv : bv 5) F23. rewrite E42 in F23.
  sbc_reg HS (24%bv : bv 5) F24. rewrite (EL 24%nat 24%bv eq_refl), R24 in F24.
  sbc_reg HS (25%bv : bv 5) F25. rewrite (EL 25%nat 25%bv eq_refl), R25 in F25.
  sbc_reg HS (26%bv : bv 5) F26. rewrite (EL 26%nat 26%bv eq_refl), R26 in F26.
  sbc_reg HS (27%bv : bv 5) F27. rewrite (EL 27%nat 27%bv eq_refl), R27 in F27.
  (* the bytes the post reads *)
  assert (Hbk : forall a, b <= a < b + 32 -> mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem2) a).
  { intros a Ha. apply (sbc_mbyte_kept SEGS E _ _ _ a HFr); [clear - Ha Hb0 Hb63; lia|].
    intros Hin. destruct (HAP a Hin) as (Hc & _). clear - Ha Hc Hbc. lia. }
  assert (Hdk : 0 < sb_dec_c.sb_dec_room cap n -> forall a,
     p + n <= a < p + n + sb_dec_c.sb_dec_acc v md cap n -> mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem2) a).
  { intros Hroom a Ha. destruct (HQ Hroom) as (_ & _ & Hdst & _).
    destruct (Hdst a Ha) as [(bb & m & Hbb & Hr) | (cid & q & Hq & Hr)].
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ bb m HARc Hbb) as (_ & Hb4096 & Hbc' & _).
      apply (sbc_mbyte_kept SEGS E _ _ _ a HFr); [clear - Hr Hb4096 Hbc' C1; lia|].
      intros Hin. destruct (HAP a Hin) as (_ & _ & Hnb & _). exact (Hnb bb m Hbb Hr).
    - destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid q HARc Hq) as (Hq4096 & Hqc & _).
      apply (sbc_mbyte_kept SEGS E _ _ _ a HFr);
        [unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; clear - Hr Hq4096 Hqc C1; lia|].
      intros Hin. destruct (HAP a Hin) as (_ & _ & _ & Hnf). exact (Hnf cid q Hq (or_introl Hr)). }
  unfold tsb_dec_post. cbv beta. split; [reflexivity|].
  exists ly2, (stack_free_state 0 pos S2), (ms_regs ms), (ms_mem ms). eexists.
  split; [f_equal; f_equal; rewrite F1; exact Hra|].
  split; [unfold EV_SB_DEC; rewrite Z.add_0_r; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split; [apply aregs_preserved_eqs; assumption|].
  split; [pose proof HJ as (_ & _ & _ & _ & _ & Hf3 & _); rewrite Hf3, Hfrsc; reflexivity|].
  split.
  { assert (Eab3 : ablocks B ly2 (stack_free_state 0 pos S2) = ablocks B ly2 S2)
      by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    rewrite Eab3, Hab. apply Permutation_refl. }
  split.
  { apply (sbc_tcj_kept SB_DEC_STK lyc Sc W memc mem2 (ms_mem ms) (spZ regs0) _
      (fun a => 0 <= a < 2 ^ 64 /\ ~ in_wrange E sbc_rs0 a) HK).
    - intros a Ha. split; [clear - Ha C1; lia|]. intros Hin. destruct (HAP a Hin) as (Hc & _). clear - Ha Hc. lia.
    - intros bb m i Hbb Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb m HARc Hbb) as (_ & Hb4096 & Hbc' & _).
      split; [clear - Hi Hb4096 Hbc' C1; lia|]. intros Hin. destruct (HAP _ Hin) as (_ & _ & Hnb & _).
      apply (Hnb bb m Hbb). clear - Hi. lia.
    - intros a Hi. pose proof (pa_segs_low a Hi) as Hlo. split; [unfold kLowMemEnd in Hlo; clear - Hlo; lia|].
      intros Hin. destruct (HAP a Hin) as (_ & Hni & _). exact (Hni Hi).
    - intros cid q a Hq Hr. pose proof (frame_zone SEGS B LAWS lyc Sc W memc mdc cid q a HARc Hq Hr) as (Hc & Hz).
      split.
      + destruct Hz as [((Hz1 & _) & (Hz3 & _)) | Hz];
        [clear - Hc Hz1 Hz3 C1; lia | unfold kLowMemEnd in Hz; clear - Hc Hz C1; lia].
      + intros Hin. destruct (HAP a Hin) as (_ & _ & _ & Hnf). exact (Hnf cid q Hq Hr).
    - intros a (Ha & Hn). exact (sbc_aview_kept E _ (w_H W) mem2 (ms_mem ms) a HFr Ha Hn).
    - intros a Hp. exact (sbc_present_grows (w_H W) mem2 (ms_mem ms) a HG Hp). }
  split; [apply (sbc_val_mem_kept SEGS (rd W mem2)); [intros kk Hkk; apply Hbk; clear - Hkk; lia | exact Vp]|].
  split; [apply (sbc_val_mem_kept SEGS (rd W mem2)); [intros kk Hkk; apply Hbk; clear - Hkk; lia | exact Vcap]|].
  split; [apply (sbc_val_mem_kept SEGS (rd W mem2)); [intros kk Hkk; apply Hbk; clear - Hkk; lia | exact Vn]|].
  split; [apply (sbc_val_mem_kept SEGS (rd W mem2)); [intros kk Hkk; apply Hbk; clear - Hkk; lia | exact Vov]|].
  apply (garr8_frame SEGS (rd W mem2)); [exact Vd|].
  intros a Ha.
  pose proof (firstn_le_length (Z.to_nat (sb_dec_c.sb_dec_acc v md cap n)) (sb_dec_c.sb_dec_D v md)) as Hlen.
  assert (Hacc0 : 0 < sb_dec_c.sb_dec_acc v md cap n) by (clear - Ha Hlen; lia).
  assert (Hroom : 0 < sb_dec_c.sb_dec_room cap n) by (unfold sb_dec_c.sb_dec_acc in Hacc0; clear - Hacc0; lia).
  apply (Hdk Hroom). clear - Ha Hlen Hacc0. lia.
Qed.
End h.
End f.
End d.
