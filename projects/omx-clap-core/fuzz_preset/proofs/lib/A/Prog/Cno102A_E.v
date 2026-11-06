(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 1214 of its 1315 lines of code are new or changed and 1889 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_Base.v, with its module names changed; 1363 of its 1481 lines of code are new or changed and 1197 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_Rpn.v, with its module names changed; 1048 of its 1190 lines of code are new or changed and 1339 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the FIRST FIVE
   SEGMENTS of the re-walk of check_no_overread (cno) against the text tcheck_no_overread_specX, CA0-CA4 as ONE
   stretch (FREE-PIECES-102 Part 7 row R7-3):
   entry + fake frame (__asan_stack_malloc_3 at +112, the capacity rule), the frame poison (+160 .. +384), the three
   inlined padded copies (+388 .. +608: __wrap_malloc (size + 16), __asan_memcpy if size, __asan_memset 16 x fill;
   the NULL arms store g_own_ran_out).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   rule-24 lookup (lookups/r7-3/idx-*.txt, 14:5xZ): check_no_overread rc=0, 0 UNRELEASED hits on live heads; the
   plan's R24Lookup (the internal file PLAN-cno-caw-102.md section 2): no walk keyed to cno A' 0x81904 or the #102 pins.
   STATUS: this file states the five segments and cn_seg_E_of_segs, and proves cn_CA1; cn_CA0, cn_CA2, cn_CA3 and
   cn_CA4 are proved in Cno102A_E0.v, Cno102A_E2.v, Cno102A_E3.v and Cno102A_E4.v.
   CONTRACT: written against Cno102A_Base.v (sha256 a5941c674468; internal record): cn_pre,
   the cuts cn_at_poison / cn_at_copy1 / cn_at_copy2 / cn_at_copy3 / cn_at_init / cn_at_init3 and their exits
   (this tree's Cno102A_Base.v, THE ROOM POSITION: no room position; each cut carries cn_prog over the events since entry).
   THE ONE ADDED PREMISE cn_fp (ruled 2026-10-29 15:20Z): cn_pre says nothing of ci_fpos D,
   while cn_frame (in cn_base) fixes the frame at ci_fpos D; the position is the one __asan_stack_malloc_3 returns at
   ci_S D (YG00.v:579 stack_malloc is a deterministic state program). The top (R7-5) discharges cn_fp from
   YGcallScf.stack_malloc_progress_any and sets ci_fpos := that position.
   RUNTIME-OPTION CELLS this stretch reads (relocation rule, ruled 2026-10-29 15:22Z): the UAR flag
   __asan_option_detect_stack_use_after_return (lw at +92, through the GOT word A_OBJ 1; the base: it holds 1 by the
   ARx const law, YCbqG.v alx_const) and the shadow base __asan_shadow_memory_dynamic_address (ld at +96, through
   A_OBJ 0). Not a relocation: a new walk of the A' pin.
   PARAMETRIC over {PA : PAImg A_prog_listing}; type-checks on this tree, against its Cno102A_Base.v.
   Numerals: offsets (DERIVED, 4 x slot inside cno); 3 (the frame class). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallMxmn YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YN2e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Cno102A_Base.
(* YF0v.v (through YGcallMxmn) sets the zify euclidean-division flag to false globally; lia here reads Z.div / Z.modulo
   with their equations (Cno102A_R5.v's setting) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section ce. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).

(* THE ADDED PREMISE (ruled 2026-10-29 15:20Z; exactly this name and text) *)
Definition cn_fp (D : cn_in) : Prop :=
  exists S1, apath (stack_malloc CN_CID (ci_S D)) [] (PFake CN_CID (ci_fpos D), S1).

(* the entry configuration of the stretch: the text's entry state at cno's entry *)
Definition cn_entry_cfg (D : cn_in) : config :=
  @cn_cfg SEGS fx (SIGMA AS_check_no_overread) (ci_regs D) (ci_mem D) (ci_md D).

(* ---- THE FIVE SEGMENTS (forward form, the internal file lane-102.md :29-30) ---- *)
(* CA0 Entry: 0 -> 160 (CN_POISON) *)
Definition cn_seg_CA0 : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D, cn_pre (fx := fx) B ARx CTX0 D -> cn_fp D -> P (ci_mem D) ->
  SRr SEGS (ci_W D) (cn_entry_cfg D)
    (fun W' c' => cn_ex_poison (fx := fx) B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
(* CA1 Poison: 160 -> 388 (CN_COPY1), call-free *)
Definition cn_seg_CA1 : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P ->
  forall D fxk ly S Hp W regs mem md k,
  cn_pre (fx := fx) B ARx CTX0 D -> cn_at_poison (fx := fx) B ARx D fxk ly S Hp W regs mem md k -> P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_POISON) regs mem md)
    (fun W' c' => cn_ex_copy1 (fx := fx) B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
(* CA2 Copy1: 388 -> 460 (CN_COPY2) *)
Definition cn_seg_CA2 : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_copy1 (fx := fx) B ARx D fxk ly S Hp W regs mem md k -> P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_COPY1) regs mem md)
    (fun W' c' => cn_ex_copy2 (fx := fx) B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
(* CA3 Copy2: 460 -> 532 (CN_COPY3) *)
Definition cn_seg_CA3 : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 own,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_copy2 (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 own -> P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_COPY2) regs mem md)
    (fun W' c' => cn_ex_copy3 (fx := fx) B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
(* CA4 Copy3: 532 -> 608 (CN_INIT) / 792 (CN_INIT3) *)
Definition cn_seg_CA4 : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 own,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_copy3 (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 own -> P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_COPY3) regs mem md)
    (fun W' c' => (cn_ex_init (fx := fx) B ARx D W' c' \/ cn_ex_init3 (fx := fx) B ARx D W' c') /\
                  P (ms_mem (cfg_ms c'))).
(* THE STRETCH (R7-3): entry -> CN_INIT \/ CN_INIT3 *)
Definition cn_seg_E : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D, cn_pre (fx := fx) B ARx CTX0 D -> cn_fp D -> P (ci_mem D) ->
  SRr SEGS (ci_W D) (cn_entry_cfg D)
    (fun W' c' => (cn_ex_init (fx := fx) B ARx D W' c' \/ cn_ex_init3 (fx := fx) B ARx D W' c') /\
                  P (ms_mem (cfg_ms c'))).

(* the stretch from its five segments (SRr_bind at the four inner cuts) *)
Lemma cn_seg_E_of_segs : cn_seg_CA0 -> cn_seg_CA1 -> cn_seg_CA2 -> cn_seg_CA3 -> cn_seg_CA4 -> cn_seg_E.
Proof.
intros H0 H1 H2 H3 H4 P PL PC D HPRE HFP HP.
eapply SRr_bind; [exact (H0 P PL PC D HPRE HFP HP)|].
intros W1 c1 _ ((fxk1 & ly1 & S1 & Hp1 & regs1 & mem1 & md1 & k1 & -> & HAT1) & HP1).
eapply SRr_bind; [exact (H1 P PL D fxk1 ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HPRE HAT1 HP1)|].
intros W2 c2 _ ((fxk2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & -> & HAT2) & HP2).
eapply SRr_bind; [exact (H2 P PL PC D fxk2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HPRE HAT2 HP2)|].
intros W3 c3 _ ((fxk3 & ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & r1 & own1 & -> & HAT3) & HP3).
eapply SRr_bind; [exact (H3 P PL PC D fxk3 ly3 S3 Hp3 W3 regs3 mem3 md3 k3 r1 own1 HPRE HAT3 HP3)|].
intros W4 c4 _ ((fxk4 & ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & q1 & q2 & own2 & -> & HAT4) & HP4).
exact (H4 P PL PC D fxk4 ly4 S4 Hp4 W4 regs4 mem4 md4 k4 q1 q2 own2 HPRE HAT4 HP4).
Qed.

End ce.

(* ======== Cno102A_R5.v's image-free facts, hand steps and frame-geometry lemmas (blob
   f2aa165bbe8a, :79-484, :509-552, :567-581, :624-627), COPIED with the prefix e5 (e5_ -> e5_, h_ / s_ / f_ -> e5h_ / e5s_ / e5f_)
   so that this file does not depend on CA5's file; the proofs are unchanged ======== *)
(* ======== 1. image-free facts ======== *)
Lemma e5_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod x 32 ltac:(lia)). change (2 ^ 5) with 32. lia.
Qed.

Section e5u. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma e5_apr_aview : forall H (m : word -> option byte) a, apresent H m a -> aview segs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma e5_apr_wr : forall H (m : word -> option byte) a, apresent H m a -> writable_at segs (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma e5_grows_of_apr : forall H (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *.
destruct (H x) eqn:Ehx; [exfalso; exact (Hx eq_refl)|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ehx | exists b; exact Em]).
destruct (Hp _ Ha) as [Hh' [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hh', Hb'. rewrite Hh' in Ehx. rewrite Hb'. discriminate.
Qed.

Lemma e5_grows_trans : forall (m1 m2 m3 : word -> option byte), mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. exact (H2 x (H1 x Hx)). Qed.

Lemma e5_aview_vis : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros H m m' a Hg Hv. unfold aview, mbyte in *.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E1.
- pose proof (Hg (Z_to_bv 64 a) ltac:(rewrite E1; discriminate)) as Hg'.
  destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; exact (Hg' eq_refl)].
- destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.

Lemma e5_mbyte_of_aview : forall H (m : word -> option byte) a v, aview segs H m a = Some v -> 0 <= v < 256 ->
  mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Ha Hv. unfold aview in Ha. destruct (mbyte segs (mrestrict H m) a) as [b|]; cbn in Ha; [|discriminate].
injection Ha as Hb. f_equal. apply bv_eq. rewrite <- Hb. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 8) with 256. lia.
Qed.

Lemma e5_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by exact Hv. apply Z.mod_small. exact Hv.
Qed.

Lemma e5_val_mem1_of_aview : forall H (m : word -> option byte) a v, aview segs H m a = Some v -> 0 <= v < 256 ->
  val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Ha Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, e5_le_byte1 by exact Hv.
exact (e5_mbyte_of_aview H m a v Ha Hv).
Qed.

Lemma e5_aview_of_val_mem1 : forall H (m : word -> option byte) a v, val_mem segs (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview segs H m a = Some v.
Proof.
intros H m a v Hm Hv. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r, e5_le_byte1 in Hm by exact Hv.
unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma e5_rdn1 : forall (m : word -> option byte) a v, val_mem segs m a 1 v -> 0 <= v < 256 ->
  rdn segs m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof.
intros m a v Hm Hv. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r, e5_le_byte1 in Hm by exact Hv.
unfold mbyte in Hm. cbn [rdn]. destruct (m (Z_to_bv 64 a)) as [b|]; [injection Hm as ->; reflexivity|].
rewrite Hm. reflexivity.
Qed.
End e5u.

(* ======== 2. the hand steps over `@YK11.mkst fz` configs (H5RttS3.v :147-249's forms, the memory steps added;
   the continuation takes any model the step may materialize) ======== *)
Section e5stp. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).
#[local] Abbreviation hcfg regs pc mem md := (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md).

Lemma e5_pc4 : forall k, 0 <= k -> k + 4 < 2 ^ 40 -> v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof.
intros k Hk0 Hk4. pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma e5h_addi : forall (W : world SEGS) regs mem md Q w k k' (rd rs : bv 5) (imm : bv 12),
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rd rs imm Hpl Hdec Hrd Hk0 Hk4 -> HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (e5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  exact (HK model' Hsame).
Qed.

Lemma e5h_ld : forall (W : world SEGS) regs mem md Q w k k' (rd rs : bv 5) (imm : bv 12) a v,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rd rs imm a v Hpl Hdec Hrd Hk0 Hk4 -> Ha Ha0 Ha8 Hw HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hw) as Hv.
apply val_mem_word_mem in Hv.
destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hv Ha0 Ha8) as (bs & Hbs & Hle).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_ld SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm bs (Z_to_bv 64 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) by first [rewrite Ha; exact Hbs | exact Hle].
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (e5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  exact (HK model' Hsame).
Qed.

Lemma e5h_lbu : forall (W : world SEGS) regs mem md Q w k k' (rd rs : bv 5) (imm : bv 12) a v,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v -> 0 <= v < 256 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rd rs imm a v Hpl Hdec Hrd Hk0 Hk4 -> Ha Hm Hv HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (e5_rdn1 SEGS (mrestrict (w_H W) mem) a v Hm Hv) as Hr.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_lbu SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm (Z_to_bv 8 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) by (rewrite Ha; exact Hr).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (e5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 v))) with (Z_to_bv 64 v); [exact (HK model' Hsame)|].
  rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 8) with 256. lia.
Qed.

(* one byte store: the new memory is the old one but at a, which now reads the low byte of rs2 *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Lemma e5h_sb : forall (W : world SEGS) regs mem md Q w k k' (rs1 rs2 : bv 5) (imm : bv 12) a,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  w_H W (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict (w_H W) mem) a -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, bv_unsigned x <> a -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     aview SEGS (w_H W) mem' a = Some (bv_unsigned (getr regs rs2) mod 256) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + k') mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rs1 rs2 imm a Hpl Hdec Hk0 Hk4 -> Ha Ha64 Hh Hwv HPm HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
set (addr := v_addi (getr regs rs1) (bv_signed imm)) in *.
set (bt := Z_to_bv 8 (bv_unsigned (getr regs rs2))).
assert (Hok : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) addr 1 = true).
{ cbn [RiscvSemantics.store_ok]. unfold writable_at in Hwv. rewrite Ha.
  destruct (wview SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 a)); [reflexivity | contradiction]. }
eapply (SRr_step_inv SEGS pa_wx P PLAW W); [reflexivity | | exact HPm |].
- rewrite restrict_mkst_fx.
  rewrite (step_sb SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hok).
  reflexivity.
- intros model' Hsame HP'. rewrite (e5_pc4 k Hk0 Hk4).
  set (mem' := munrestrict (w_H W) mem (fun x : word => if bv_eqb x addr then Some bt else mrestrict (w_H W) mem x)).
  refine (HK model' mem' Hsame _ _ _ _ HP').
  + intros x Hx. unfold mem', munrestrict, mrestrict. cbv beta. destruct (w_H W x) eqn:Ex; [reflexivity|].
    destruct (bv_eqb x addr) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_true_iff in Eb. apply Hx.
    rewrite Eb, Ha, unsigned_lit_small by exact Ha64. reflexivity.
  + intros x Hx. unfold mem', munrestrict, mrestrict in *. cbv beta in *. destruct (w_H W x) eqn:Ex; [exact Hx|].
    destruct (bv_eqb x addr); [discriminate | exact Hx].
  + intros x Hx. unfold mem', munrestrict. cbv beta. rewrite Hx. reflexivity.
  + unfold aview, mbyte, mem', munrestrict, mrestrict. cbv beta. rewrite <- Ha. rewrite <- Ha in Hh. rewrite Hh.
    replace (bv_eqb addr addr) with true by (symmetry; apply bv_eqb_true_iff; reflexivity).
    cbn [option_map]. unfold bt. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* `jal ra, s` at a PCall slot: the callee's entry with ra = the return slot *)
Lemma e5h_call : forall (W : world SEGS) regs mem md Q k k' (s : asym),
  plookup pl_tpi k = Some (PCall s 1%bv) -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs 1%bv (Z_to_bv 64 (BASE + k'))) (pa_sigma s) mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' s Hpl Hk0 Hk4 -> HK.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- pl_tpi_eq in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with context [Jal ?r ?im] => rename r into rdj; rename im into imm end.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd _]. apply reg_eqb_eq in Hrd. subst rdj.
apply Z.eqb_eq in Ht.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 wz) 1%bv imm (pa_fetch_ok _ _ Hfw)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  reflexivity.
- intros model' Hsame. cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (1%bv : bv 5) 0) with false by reflexivity. rewrite (e5_pc4 k Hk0 Hk4).
  replace (btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)) with (Z_to_bv 64 (pa_sigma s)); [exact (HK model' Hsame)|].
  unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Ht. unfold zcanon.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, M64. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---- the slot checks: a closed boolean on the listing, decided by vm_compute at the use (no evar) ---- *)
Definition e5_slot (k : Z) (f : instr -> bool) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) => match decode_any (Z_to_bv 32 w) with Some (i, isz) => (isz =? 4) && f i | None => false end
  | _ => false
  end.
Definition e5f_addi (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with OpImm ALU_ADD rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition e5f_ld (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with Load SZ8 true rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition e5f_lbu (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with Load SZ1 false rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition e5f_sb (rs1 rs2 : bv 5) (n : Z) (i : instr) : bool :=
  match i with Store SZ1 rs1' rs2' imm => bv_eqb rs1' rs1 && bv_eqb rs2' rs2 && (bv_signed imm =? n) | _ => false end.

Lemma e5_slot_ok : forall k f, e5_slot k f = true ->
  exists w i, plookup pl_tpi k = Some (PW w) /\ decode_any (Z_to_bv 32 w) = Some (i, 4%Z) /\ f i = true.
Proof.
intros k f H. unfold e5_slot in H.
destruct (plookup pl_tpi k) as [[w| | | | | ]|]; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz]|] eqn:Hd; [|discriminate H].
apply andb_prop in H as [Hz Hf]. apply Z.eqb_eq in Hz. subst isz. exists w, i. auto.
Qed.

Lemma e5s_addi : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) n,
  e5_slot k (e5f_addi rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (v_addi (getr regs rs) n)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs n Hs Hrd Hk0 Hk4 Hk' HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf. lazymatch type of Hf with e5f_addi _ _ _ (OpImm ?al _ _ _) = true => destruct al; try discriminate Hf end.
unfold e5f_addi in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (e5h_addi W regs mem md Q w k _ _ _ _ Hpl Hdec Hrd Hk0 Hk4 eq_refl HK).
Qed.

Lemma e5s_ld : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) n a v,
  e5_slot k (e5f_ld rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) n = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs n a v Hs Hrd Hk0 Hk4 Hk' Ha Ha0 Ha8 Hw HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with e5f_ld _ _ _ (Load ?sz ?sg _ _ _) = true => destruct sz; try discriminate Hf; destruct sg; try discriminate Hf end.
unfold e5f_ld in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (e5h_ld W regs mem md Q w k _ _ _ _ a v Hpl Hdec Hrd Hk0 Hk4 eq_refl Ha Ha0 Ha8 Hw HK).
Qed.

Lemma e5s_lbu : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) n a v,
  e5_slot k (e5f_lbu rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) n = Z_to_bv 64 a ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v -> 0 <= v < 256 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs n a v Hs Hrd Hk0 Hk4 Hk' Ha Hm Hv HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with e5f_lbu _ _ _ (Load ?sz ?sg _ _ _) = true => destruct sz; try discriminate Hf; destruct sg; try discriminate Hf end.
unfold e5f_lbu in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (e5h_lbu W regs mem md Q w k _ _ _ _ a v Hpl Hdec Hrd Hk0 Hk4 eq_refl Ha Hm Hv HK).
Qed.

Lemma e5s_sb : forall (W : world SEGS) regs mem md Q k k' (rs1 rs2 : bv 5) n a,
  e5_slot k (e5f_sb rs1 rs2 n) = true -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs1) n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  w_H W (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict (w_H W) mem) a -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, bv_unsigned x <> a -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     aview SEGS (w_H W) mem' a = Some (bv_unsigned (getr regs rs2) mod 256) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + k') mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rs1 rs2 n a Hs Hk0 Hk4 Hk' Ha Ha64 Hh Hwv HPm HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with e5f_sb _ _ _ (Store ?sz _ _ _) = true => destruct sz; try discriminate Hf end.
unfold e5f_sb in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (e5h_sb W regs mem md Q w k _ _ _ _ a Hpl Hdec Hk0 Hk4 eq_refl Ha Ha64 Hh Hwv HPm HK).
Qed.

Lemma e5_apr_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|]. specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh, Hb in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; [discriminate | reflexivity]].
Qed.

(* n stores of zero to n consecutive bytes s2v + j .. through s2 (the shadow unpoison runs) *)
Fixpoint e5_sb_slots (k j : Z) (n : nat) : bool :=
  match n with O => true | S n' => e5_slot k (e5f_sb 18%bv 0%bv j) && e5_sb_slots (k + 4) (j + 1) n' end.

Lemma e5h_sbn : forall n (W : world SEGS) regs mem md Q k j s2v,
  getr regs 18%bv = Z_to_bv 64 s2v -> 0 <= s2v < 2 ^ 64 ->
  0 <= k -> k + 4 * Z.of_nat n < 2 ^ 40 -> 0 <= s2v + j -> s2v + j + Z.of_nat n <= 2 ^ 64 ->
  e5_sb_slots k j n = true ->
  (forall i, 0 <= i < Z.of_nat n -> apresent (w_H W) mem (s2v + j + i)) -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, ~ (s2v + j <= bv_unsigned x < s2v + j + Z.of_nat n) ->
        mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     (forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W) mem' (s2v + j + i) = Some 0) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + (k + 4 * Z.of_nat n)) mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
induction n as [|n IH]; intros W regs mem md Q k j s2v Hs2 Hs2r Hk0 Hk4 Hj0 Hj1 Hsl Hpr HPm HK.
- replace (k + 4 * Z.of_nat 0) with k in HK by lia.
  apply (HK md mem (same_but_materialized_refl md)); [intros x _; reflexivity | intros x Hx; exact Hx |
    intros x _; reflexivity | intros i Hi; cbn in Hi; lia | exact HPm].
- rewrite Nat2Z.inj_succ in Hk4, Hj1, Hpr, HK. cbn [e5_sb_slots] in Hsl. apply andb_prop in Hsl as [Hs Hsl].
  pose proof (Hpr 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  apply (e5s_sb W regs mem md Q k (k + 4) 18%bv 0%bv j (s2v + j) Hs Hk0 ltac:(lia) eq_refl); [| lia | exact (proj1 H0) |
    exact (e5_apr_wr _ _ _ _ H0) | exact HPm |].
  { rewrite Hs2. unfold v_addi. rewrite unsigned_lit_small by lia. reflexivity. }
  intros md1 mem1 Hs1 Hf1 Hg1 Hh1 Hv1 HP1. change (getr regs 0%bv) with (Z_to_bv 64 0) in Hv1.
  change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in Hv1.
  apply (IH W regs mem1 md1 Q (k + 4) (j + 1) s2v Hs2 Hs2r ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsl).
  { intros i Hi. apply (e5_apr_grows _ mem mem1 _ Hg1). replace (s2v + (j + 1) + i) with (s2v + j + (i + 1)) by lia.
    apply Hpr. lia. }
  { exact HP1. }
  intros md' mem' Hs' Hf' Hg' Hh' Hv' HP'.
  replace (k + 4 + 4 * Z.of_nat n) with (k + 4 * (Z.of_nat n + 1)) in * by lia.
  apply (HK md' mem' (same_but_materialized_trans _ _ _ Hs1 Hs')).
  + intros x Hx. rewrite Hf' by lia. apply Hf1. lia.
  + exact (e5_grows_trans _ _ _ Hg1 Hg').
  + intros x Hx. rewrite (Hh' x Hx). exact (Hh1 x Hx).
  + intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    * rewrite Z.add_0_r. rewrite <- Hv1. apply aview_eq_of. apply Hf'.
      rewrite unsigned_lit_small by lia. lia.
    * replace (s2v + j + i) with (s2v + (j + 1) + (i - 1)) by lia. apply Hv'. lia.
  + exact HP'.
Qed.
End e5stp.

Lemma e5_cs : forall z : Z, ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%bool = true ->
  acallee_saved z.
Proof.
intros z H. unfold acallee_saved.
repeat (apply Bool.orb_prop in H as [H|H]); try (apply Z.eqb_eq in H; lia).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma e5_pres : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Ltac e5_bvne := let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E.
(* a register of a later state, back to an earlier one: through regupd and the memset's aregs_preserved *)
Ltac e5_rs := repeat first
  [ rewrite getr_same by e5_bvne
  | rewrite getr_other by e5_bvne
  | match goal with H : aregs_preserved ?r1 ?r2 |- context [getr ?r2 ?r] =>
      rewrite (e5_pres r1 r2 r H) by (apply e5_cs; reflexivity) end ].
Ltac e5_in := solve [repeat (first [left; reflexivity | right])].
Ltac e5_consts := unfold kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd, kHighMemEnd, SHADOW_OFF, ESTACK in *.

(* ======== THE STEP KIT: Cno102A_R5.v's section 2 (h_addi, h_ld, h_sb, e5h_call, e5_slot and the s_ forms), plus the steps this
   stretch adds: sd (with the stored word), lui / addiw / auipc at a PHi slot / addi at a PAddHi slot (the value is not
   read by any cut, so the continuation takes ANY value), srli / add (exact), and a run of sb through s2 ======== *)
Section stp2. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).
#[local] Abbreviation hcfg regs pc mem md := (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md).

Definition f_sd (rs1 rs2 : bv 5) (n : Z) (i : instr) : bool :=
  match i with Store SZ8 rs1' rs2' imm => bv_eqb rs1' rs1 && bv_eqb rs2' rs2 && (bv_signed imm =? n) | _ => false end.
Definition f_lui (rd : bv 5) (i : instr) : bool := match i with Lui rd' _ => bv_eqb rd' rd | _ => false end.
Definition f_addiw (rd rs : bv 5) (i : instr) : bool :=
  match i with OpImm32 rd' rs' _ => bv_eqb rd' rd && bv_eqb rs' rs | _ => false end.
Definition f_srli (rd rs : bv 5) (sh : Z) (i : instr) : bool :=
  match i with ShiftImm ALU_SRL rd' rs' sh' => bv_eqb rd' rd && bv_eqb rs' rs && (bv_unsigned sh' =? sh) | _ => false end.
Definition f_add (rd rs1 rs2 : bv 5) (i : instr) : bool :=
  match i with Op ALU_ADD rd' a b => bv_eqb rd' rd && bv_eqb a rs1 && bv_eqb b rs2 | _ => false end.

(* one step that changes rd only *)
Lemma e_reg_step : forall (W : world SEGS) regs mem md Q k k' (rd : bv 5) v,
  0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  RiscvSemantics.step SEGS (@YK11.mkst fz regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fz (regupd regs rd v) (v_addi (Z_to_bv 64 (BASE + k)) 4) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall md', same_but_materialized md md' -> SRr SEGS W (hcfg (regupd regs rd v) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd v Hk0 Hk4 -> Hst HK.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
intros model' Hsame. rewrite (e5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
exact (HK model' Hsame).
Qed.

Lemma s_lui : forall (W : world SEGS) regs mem md Q k k' (rd : bv 5),
  e5_slot k (f_lui rd) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall v md', same_but_materialized md md' -> SRr SEGS W (hcfg (regupd regs rd v) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd Hs Hrd Hk0 Hk4 Hk' HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf). destruct i; try discriminate Hf.
unfold f_lui in Hf. apply reg_eqb_eq in Hf. subst.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply e_reg_step; [exact Hk0 | exact Hk4 | reflexivity | | exact (HK _)].
rewrite (step_lui SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd imm (pa_fetch_ok _ _ Hl)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec). rewrite Hrd. reflexivity.
Qed.

Lemma s_addiw : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5),
  e5_slot k (f_addiw rd rs) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall v md', same_but_materialized md md' -> SRr SEGS W (hcfg (regupd regs rd v) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs Hs Hrd Hk0 Hk4 Hk' HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf). destruct i; try discriminate Hf.
unfold f_addiw in Hf. apply andb_prop in Hf as [E1 E2]. apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. subst.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply e_reg_step; [exact Hk0 | exact Hk4 | reflexivity | | exact (HK _)].
rewrite (step_addiw SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm (pa_fetch_ok _ _ Hl)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec). rewrite Hrd. reflexivity.
Qed.

Lemma s_srli : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) sh,
  e5_slot k (f_srli rd rs sh) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (v_srli (getr regs rs) sh)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs sh Hs Hrd Hk0 Hk4 Hk' HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf). destruct i; try discriminate Hf.
lazymatch type of Hf with f_srli _ _ _ (ShiftImm ?o _ _ _) = true => destruct o; try discriminate Hf end.
unfold f_srli in Hf. apply andb_prop in Hf as [Hf E3]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in E3. subst.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply e_reg_step; [exact Hk0 | exact Hk4 | reflexivity | | exact HK].
rewrite (step_srli SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs _ (pa_fetch_ok _ _ Hl)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec). rewrite Hrd. reflexivity.
Qed.

Lemma s_add : forall (W : world SEGS) regs mem md Q k k' (rd rs1 rs2 : bv 5),
  e5_slot k (f_add rd rs1 rs2) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs1 rs2 Hs Hrd Hk0 Hk4 Hk' HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf). destruct i; try discriminate Hf.
lazymatch type of Hf with f_add _ _ _ (Op ?o _ _ _) = true => destruct o; try discriminate Hf end.
unfold f_add in Hf. apply andb_prop in Hf as [Hf E3]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply reg_eqb_eq in E3. subst.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply e_reg_step; [exact Hk0 | exact Hk4 | reflexivity | | exact HK].
rewrite (step_add SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd _ _ (pa_fetch_ok _ _ Hl)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec). rewrite Hrd. reflexivity.
Qed.

(* `auipc rd` at a PHi slot (its word checked by the certificate): rd gets SOME value *)
Lemma h_phi : forall (W : world SEGS) regs mem md Q k k' (rd : bv 5) j,
  plookup pl_tpi k = Some (PHi rd j) -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall v md', same_but_materialized md md' -> SRr SEGS W (hcfg (regupd regs rd v) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd j Hpl Hrd Hk0 Hk4 Hk' HK.
pose proof Hpl as Hpl'. rewrite <- pl_tpi_eq in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hr _]. apply reg_eqb_eq in Hr. subst.
eapply e_reg_step; [exact Hk0 | exact Hk4 | reflexivity | | exact (HK _)].
rewrite (step_auipc SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ _ imm (pa_fetch_ok _ _ Hfw)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec). rewrite Hrd. reflexivity.
Qed.

(* `addi rd, rs, lo` at a PAddHi slot: rd gets SOME value *)
Lemma h_paddhi : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) j a off,
  plookup pl_tpi k = Some (PAddHi rd rs j a off) -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall v md', same_but_materialized md md' -> SRr SEGS W (hcfg (regupd regs rd v) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs j a off Hpl Hrd Hk0 Hk4 Hk' HK.
pose proof Hpl as Hpl'. rewrite <- pl_tpi_eq in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with context [OpImm ?o _ _ _] => destruct o; try discriminate Hck end.
apply andb_prop in Hck as [Hck _]. apply andb_prop in Hck as [Hr _]. apply reg_eqb_eq in Hr. subst.
eapply e_reg_step; [exact Hk0 | exact Hk4 | reflexivity | | exact (HK _)].
rewrite (step_addi SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ _ _ imm (pa_fetch_ok _ _ Hfw)
  (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec). rewrite Hrd. reflexivity.
Qed.

Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.

(* one 8-byte store: the new memory is the old one but at [a, a + 8), which now reads the word in rs2 *)
Lemma h_sd : forall (W : world SEGS) regs mem md Q w k k' (rs1 rs2 : bv 5) (imm : bv 12) a,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> apresent (w_H W) mem (a + i)) -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, ~ (a <= bv_unsigned x < a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     val_mem SEGS (mrestrict (w_H W) mem') a 8 (bv_unsigned (getr regs rs2)) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + k') mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rs1 rs2 imm a Hpl Hdec Hk0 Hk4 -> Ha Ha0 Ha8 Hpr HPm HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
set (addr := v_addi (getr regs rs1) (bv_signed imm)) in *.
set (bs := word_to_le_bytes 8 (getr regs rs2)).
assert (Hok : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) addr 8 = true).
{ rewrite Ha. apply store_ok_of_all; [rewrite unsigned_lit_small by lia; cbn; lia|].
  intros x Hx. rewrite unsigned_lit_small in Hx by lia. cbn in Hx.
  destruct (Hpr (bv_unsigned x - a) ltac:(lia)) as [Hh [b Hb]].
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hh, Hb by lia. rewrite Z_to_bv_bv_unsigned in Hh, Hb.
  unfold wview, mrestrict. rewrite Hh, Hb. discriminate. }
eapply (SRr_step_inv SEGS pa_wx P PLAW W); [reflexivity | | exact HPm |].
- rewrite restrict_mkst_fx.
  rewrite (step_sd_val SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hok).
  reflexivity.
- intros model' Hsame HP'. rewrite (e5_pc4 k Hk0 Hk4).
  set (mem' := munrestrict (w_H W) mem (wbytes (mrestrict (w_H W) mem) addr bs)).
  assert (Hlen : length bs = 8%nat) by reflexivity.
  assert (E1 : forall x : word, w_H W x = false -> mrestrict (w_H W) mem' x = wbytes (mrestrict (w_H W) mem) addr bs x).
  { intros x Hx. unfold mem', munrestrict, mrestrict. rewrite Hx. reflexivity. }
  refine (HK model' mem' Hsame _ _ _ _ HP').
  + intros x Hx. destruct (w_H W x) eqn:Ex.
    * unfold mem', munrestrict, mrestrict. rewrite Ex. reflexivity.
    * rewrite (E1 x Ex). rewrite Ha.
      pose proof (YN2e.wbytes_other bs (mrestrict (w_H W) mem) a (bv_unsigned x) Ha0 ltac:(rewrite Hlen; cbn; lia)
        ltac:(apply bv_unsigned_in_range) ltac:(rewrite Hlen; cbn; lia)) as Hw.
      rewrite Z_to_bv_bv_unsigned in Hw. rewrite Hw.
      unfold mrestrict. rewrite Ex. reflexivity.
  + intros x Hx. destruct (w_H W x) eqn:Ex.
    * unfold mrestrict in Hx. rewrite Ex in Hx. exfalso. exact (Hx eq_refl).
    * rewrite (E1 x Ex). exact (wbytes_grows bs (mrestrict (w_H W) mem) addr x Hx).
  + intros x Hx. unfold mem', munrestrict. rewrite Hx. reflexivity.
  + intros q Hq. pose proof (Hpr (Z.of_nat q) ltac:(lia)) as [Hh _].
    pose proof (YN2e.wbytes_mbyte_in SEGS bs (mrestrict (w_H W) mem) a (a + Z.of_nat q) Ha0
      ltac:(rewrite Hlen; cbn; lia) ltac:(rewrite Hlen; cbn; lia)) as Hm.
    replace (Z.to_nat (a + Z.of_nat q - a)) with q in Hm by lia.
    pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned (getr regs rs2)) q ltac:(lia)
      ltac:(apply bv_unsigned_in_range)) as Hn.
    rewrite Z_to_bv_bv_unsigned in Hn. fold bs in Hn. rewrite Hn in Hm. rewrite <- Hm.
    unfold mbyte. rewrite (E1 _ Hh). rewrite Ha. reflexivity.
Qed.

Lemma s_sd : forall (W : world SEGS) regs mem md Q k k' (rs1 rs2 : bv 5) n a,
  e5_slot k (f_sd rs1 rs2 n) = true -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs1) n = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> apresent (w_H W) mem (a + i)) -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, ~ (a <= bv_unsigned x < a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     val_mem SEGS (mrestrict (w_H W) mem') a 8 (bv_unsigned (getr regs rs2)) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + k') mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rs1 rs2 n a Hs Hk0 Hk4 Hk' Ha Ha0 Ha8 Hpr HPm HK.
destruct (e5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with f_sd _ _ _ (Store ?sz _ _ _) = true => destruct sz; try discriminate Hf end.
unfold f_sd in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (h_sd W regs mem md Q w k _ _ _ _ a Hpl Hdec Hk0 Hk4 eq_refl Ha Ha0 Ha8 Hpr HPm HK).
Qed.

(* a run of `sb rs, j(s2)` (each (j, rs) of the list in turn, registers unchanged): the bytes s2v + j written, the
   rest kept *)
Fixpoint e_sb_slots (k : Z) (l : list (Z * bv 5)) : bool :=
  match l with [] => true | (j, r) :: t => e5_slot k (e5f_sb 18%bv r j) && e_sb_slots (k + 4) t end.
Definition e_sbset (s2v : Z) (l : list (Z * bv 5)) (x : Z) : Prop := exists j r, In (j, r) l /\ x = s2v + j.

Lemma h_sbl : forall l (W : world SEGS) regs mem md Q k s2v,
  getr regs 18%bv = Z_to_bv 64 s2v -> 0 <= s2v ->
  0 <= k -> k + 4 * Z.of_nat (length l) < 2 ^ 40 ->
  e_sb_slots k l = true ->
  (forall j r, In (j, r) l -> 0 <= j /\ s2v + j < 2 ^ 64 /\ apresent (w_H W) mem (s2v + j)) -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, ~ e_sbset s2v l (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + (k + 4 * Z.of_nat (length l))) mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
induction l as [|[j r] t IH]; intros W regs mem md Q k s2v Hs2 Hs20 Hk0 Hk4 Hsl Hpr HPm HK.
- cbn [length] in HK. change (Z.of_nat 0) with 0 in HK. rewrite Z.mul_0_r, Z.add_0_r in HK.
  apply (HK md mem (same_but_materialized_refl md)); [intros x _; reflexivity | intros x Hx; exact Hx |
    intros x _; reflexivity | exact HPm].
- cbn [e_sb_slots] in Hsl. apply andb_prop in Hsl as [Hs Hsl]. cbn [length] in Hk4, HK. rewrite Nat2Z.inj_succ in Hk4, HK.
  destruct (Hpr j r (or_introl eq_refl)) as (Hj0 & Hj1 & Hjp).
  apply (e5s_sb P PLAW W regs mem md Q k (k + 4) 18%bv r j (s2v + j) Hs Hk0 ltac:(lia) eq_refl); [| lia | exact (proj1 Hjp) |
    exact (e5_apr_wr _ _ _ _ Hjp) | exact HPm |].
  { rewrite Hs2. unfold v_addi. rewrite unsigned_lit_small by lia. reflexivity. }
  intros md1 mem1 Hs1 Hf1 Hg1 Hh1 _ HP1.
  apply (IH W regs mem1 md1 Q (k + 4) s2v Hs2 Hs20 ltac:(lia) ltac:(lia) Hsl).
  { intros j' r' Hin. destruct (Hpr j' r' (or_intror Hin)) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. exact (e5_apr_grows _ mem mem1 _ Hg1 A3). }
  { exact HP1. }
  intros md' mem' Hs' Hf' Hg' Hh' HP'.
  replace (k + 4 + 4 * Z.of_nat (length t)) with (k + 4 * Z.succ (Z.of_nat (length t))) by lia.
  apply (HK md' mem' (same_but_materialized_trans _ _ _ Hs1 Hs')).
  + intros x Hx. rewrite Hf'; [apply Hf1 | ]; intros E; apply Hx.
    * exists j, r. split; [left; reflexivity | exact E].
    * destruct E as (j' & r' & Hin & E). exists j', r'. split; [right; exact Hin | exact E].
  + exact (e5_grows_trans _ _ _ Hg1 Hg').
  + intros x Hx. rewrite (Hh' x Hx). exact (Hh1 x Hx).
  + exact HP'.
Qed.
End stp2.

(* ======== CA1 Poison (160 -> 388): the frame header, the 40 shadow bytes of the frame, the slots 32 / 80 ======== *)
Section e1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instance PL_cno_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cn_img B.
Hypothesis HW : prh_head_wide.
#[local] Notation CNJ := (@cn_J rc SK PA B ARx).
(* a cut's journal at the empty wild budget (cn_base's wk = 0 at every cut of CA0-CA4: wbudget [] 0 holds only of the
   empty budget list) is the plain journal ajournal_x *)
Lemma e_J0 : forall D ly S Hp W mem md k, CNJ D ly S Hp W mem md k 0 ->
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D)
    (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k.
Proof.
intros D ly S Hp W mem md k (WS & HJ & HBd). unfold YCbqGwild.wbudget in HBd. rewrite YCbqGwild.wfresh_nil_set in HBd.
destruct WS as [|w WS]; [exact HJ | cbn [length] in HBd; lia].
Qed.

Lemma e5_stk : STK_check_no_overread = 27424.
Proof. vm_compute. reflexivity. Qed.

(* where the frame, the stack and sp0 lie (from the cut's journal and frame facts) *)
Definition e5_geo (D : cn_in) (ly : alayout) : Prop :=
  frame_addr ly CN_CID (ci_fpos D) = cn_F D /\
  4096 <= cn_F D /\ cn_F D + 512 <= YM05.alloc_ceiling /\ cn_F D mod 32 = 0 /\
  (cn_F D + 512 <= kLowShadowBeg \/ kHighMemBeg <= cn_F D) /\
  cn_sp0 D mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo ly /\ kHighMemBeg <= ly_stk_lo ly /\
  ly_stk_lo ly + 27424 <= cn_sp0 D /\ cn_sp0 D <= 2 ^ 47.

Lemma e5_geo_of_base : forall D fxk ly S Hp W regs mem md k,
  @cn_base fx rc SK PA B ARx D fxk ly S Hp W regs mem md k 0 -> e5_geo D ly /\ ARx ly S Hp W mem md.
Proof.
intros D fxk ly S Hp W regs mem md k (_ & _ & HJ & HF & _).
apply e_J0 in HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & _).
destruct HF as (Hfrs & _ & _ & _ & _).
assert (Hin : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin) as (F0 & F1 & Fapp).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin) as (F32 & _ & _ & _).
destruct (stk_bounds_x SEGS B ARx LAWS ly S Hp W mem md HAR) as [Hkb _].
rewrite EFa in F0, F1, Fapp, F32.
change (fs_frame_bytes CN_CID) with 512 in F1, Fapp.
rewrite e5_stk in Hslo.
split; [|exact HAR].
unfold e5_geo. split; [exact EFa|]. split; [lia|]. split; [lia|]. split; [exact F32|].
split; [unfold in_app in Fapp; destruct Fapp as (_ & [Hl | [Hh _]]); [left; exact Hl | right; exact Hh]|].
rewrite Elo in Hkb |- *. repeat split; lia.
Qed.

Lemma e5_S1 : forall D, cn_sp0 D mod 16 = 0 ->
  (cn_S1 D - cn_sp0 D) mod 16 = 0 /\ cn_sp0 D - 223 <= cn_S1 D <= cn_sp0 D - 192.
Proof.
intros D H16. unfold cn_S1. rewrite e5_land32.
pose proof (Z.mod_pos_bound (cn_sp0 D - 192) 32 ltac:(lia)).
split; [|lia].
replace (cn_sp0 D - 192 - (cn_sp0 D - 192) mod 32 - cn_sp0 D) with ((2 * ((cn_sp0 D - 192) / 32) - cn_sp0 D / 16) * 16).
- apply Z.mod_mul. lia.
- pose proof (Z.div_mod (cn_sp0 D - 192) 32 ltac:(lia)). pose proof (Z.div_mod (cn_sp0 D) 16 ltac:(lia)). lia.
Qed.

(* the own byte is a program static: an image byte, below the shadow and the stack *)
Lemma e5_own_pst : Exists (in_zr (VAL (A_OBJ 13))) prh_pst.
Proof.
rewrite (cni_own B IMG). unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. change (Z.of_nat pi_gz_own_ran_out) with 1. lia.
Qed.
Lemma e5_own_img : in_img SEGS (VAL (A_OBJ 13)) /\ 0 <= VAL (A_OBJ 13) < kLowMemEnd.
Proof.
destruct (cni_pst_ok B IMG _ e5_own_pst) as [Hi _]. split; [exact Hi | exact (@pa_segs_low _ _ PA _ Hi)].
Qed.

Lemma e5_cell_img : forall a w q, (forall kk, (kk < w)%nat -> Exists (in_zr (a + Z.of_nat kk)) prh_pst) ->
  0 <= q < Z.of_nat w -> in_img SEGS (a + q).
Proof. intros a w q H Hq. replace q with (Z.of_nat (Z.to_nat q)) by lia. exact (proj1 (cni_pst_ok B IMG _ (H (Z.to_nat q) ltac:(lia)))). Qed.


(* the shadow byte of an address off F is not one of F's shadow bytes (F is 8-aligned) *)
Lemma e5_sh_off : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 512) ->
  ~ (shadow_addr F <= shadow_addr x < shadow_addr F + 64).
Proof. intros F x HF Hx Hs. unfold shadow_addr in Hs. lia. Qed.

(* every byte the stretch's own code or its calls write before CA5, but the program static and the new blocks: the
   frame's first 504 bytes, the frame's 64 shadow bytes, and the real stack from the call windows below the realigned
   sp up to the slot at sp + 80 *)
Definition e_wall (D : cn_in) (a : Z) : Prop :=
  cn_F D <= a < cn_F D + 504 \/ shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 \/
  cn_S1 D - ASTACK <= a < cn_S1 D + 88.

Lemma e_cls_stack : forall D ly a, e5_geo D ly -> cn_S1 D + 88 <= a < 2 ^ 47 -> ~ e_wall D a /\ a <> VAL (A_OBJ 13).
Proof.
intros D ly a G Ha. pose proof G as (_ & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _]. pose proof (e5_own_img) as [_ Ho].
split; [|unfold kLowMemEnd in Ho; lia].
unfold e_wall, shadow_addr in *. e5_consts. unfold ASTACK. lia.
Qed.

Lemma e_cls_img : forall D ly S Hp W mem md a, e5_geo D ly -> ARx ly S Hp W mem md ->
  In (CN_CID, ci_fpos D) (frames S) -> in_img SEGS a -> ~ e_wall D a.
Proof.
intros D ly S Hp W mem md a G HAR Hin Hi. pose proof G as (EFa & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow.
pose proof (frm_img_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) a HAR Hin) as Hf.
rewrite EFa in Hf. change (fs_frame_bytes CN_CID) with 512 in Hf.
intros [Hw | [Hw | Hw]].
- exact (Hf ltac:(lia) Hi).
- unfold shadow_addr in Hw. e5_consts. lia.
- e5_consts. unfold ASTACK in Hw. lia.
Qed.

Lemma e_cls_blk : forall D ly S Hp W mem md p n a, e5_geo D ly -> ARx ly S Hp W mem md ->
  In (CN_CID, ci_fpos D) (frames S) -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ e_wall D a /\ a <> VAL (A_OBJ 13) /\ ~ (cn_F D <= a < cn_F D + 512) /\ 0 <= a < YM05.alloc_ceiling.
Proof.
intros D ly S Hp W mem md p n a G HAR Hin Hb Ha. pose proof G as (EFa & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md p n CN_CID (ci_fpos D) HAR Hb Hin) as Hd.
rewrite EFa in Hd. change (fs_frame_bytes CN_CID) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hb) as (_ & H4096 & Hce & Happ & _).
pose proof (in_app_addr p (req_size n) a Happ Ha) as Hap.
pose proof (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n a HAR Hb Ha) as Hni.
pose proof (e5_own_img) as [Hoi _].
split; [|split; [|split]].
- intros [Hw | [Hw | Hw]]; [lia | | e5_consts; unfold ASTACK in Hw; lia].
  unfold app_addr, ASAN_CEIL, shadow_addr in *. e5_consts. lia.
- intros ->. exact (Hni Hoi).
- lia.
- lia.
Qed.

Lemma e_cls_sh : forall D ly x, e5_geo D ly -> 0 <= x < YM05.alloc_ceiling -> ~ (cn_F D <= x < cn_F D + 512) ->
  ~ e_wall D (shadow_addr x) /\ shadow_addr x <> VAL (A_OBJ 13) /\ 0 <= shadow_addr x < 2 ^ 64.
Proof.
intros D ly x G Hx Hxf. pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _]. pose proof (e5_own_img) as [_ Ho].
pose proof (e5_sh_off (cn_F D) x ltac:(lia) Hxf) as Hso.
split; [|split].
- intros [Hw | [Hw | Hw]]; [| exact (Hso Hw) |].
  + unfold shadow_addr in *. e5_consts. lia.
  + unfold shadow_addr in *. e5_consts. unfold ASTACK in Hw. lia.
- unfold shadow_addr in *. e5_consts. lia.
- unfold shadow_addr in *. e5_consts. lia.
Qed.

(* the invariant carried from a cut (memory mem0) through call-free code: the journal, P, every byte off the wall Wl
   kept, the visible memory grows *)
Definition e_inv (P : (word -> option byte) -> Prop) (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (Wl : Z -> Prop) (mem0 : word -> option byte) (k : Z) (memi : word -> option byte) (mdi : Model)
  : Prop :=
  CNJ D ly S Hp W memi mdi k 0 /\ P memi /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wl a -> aview SEGS (w_H W) memi a = aview SEGS (w_H W) mem0 a) /\
  mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) memi).

Lemma e_inv_init : forall P D ly S Hp W Wl mem md k, CNJ D ly S Hp W mem md k 0 -> P mem ->
  e_inv P D ly S Hp W Wl mem k mem md.
Proof.
intros P D ly S Hp W Wl mem md k HJ HP. split; [exact HJ|]. split; [exact HP|]. split; [intros; reflexivity|].
intros x Hx; exact Hx.
Qed.

Lemma e_inv_md : forall P D ly S Hp W Wl mem0 k memi mdi mdi',
  e_inv P D ly S Hp W Wl mem0 k memi mdi -> same_but_materialized mdi mdi' -> e_inv P D ly S Hp W Wl mem0 k memi mdi'.
Proof.
intros P D ly S Hp W Wl mem0 k memi mdi mdi' (HJ & HR) Hs. split; [|exact HR].
rewrite (same_but_materialized_wvb _ _ Hs). apply e_J0 in HJ. apply cn_J_of_x.
exact (ajournal_x_materialize SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* a write inside the wall, each byte one the journal allows *)
Lemma e_inv_write : forall P D ly S Hp W Wl mem0 k memi mdi memo mdo (Wr : Z -> Prop),
  e_inv P D ly S Hp W Wl mem0 k memi mdi ->
  (forall a, Wr a -> Wl a /\
     awr_byte STK_check_no_overread (cn_sp0 D) [] (ablocks B (ci_ly D) (ci_S D)) (ablocks B ly S) ly
       [(CN_CID, ci_fpos D)] a) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) memo x = mrestrict (w_H W) memi x) ->
  mem_grows (mrestrict (w_H W) memi) (mrestrict (w_H W) memo) ->
  (forall x : word, w_H W x = true -> memo x = memi x) -> same_but_materialized mdi mdo -> P memo ->
  e_inv P D ly S Hp W Wl mem0 k memo mdo.
Proof.
intros P D ly S Hp W Wl mem0 k memi mdi memo mdo Wr (HJ & _ & HK & HG) HWr Hfr Hgr Hhid Hs HPo.
split; [|split; [exact HPo|split]].
- apply e_J0 in HJ. apply cn_J_of_x.
  apply (ajournal_x_exec SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Wr HJ Hfr Hgr Hhid Hs). intros a Ha. exact (proj2 (HWr a Ha)).
- intros a Ha Hw. rewrite <- (HK a Ha Hw). apply aview_eq_of. apply Hfr.
  rewrite unsigned_lit_small by exact Ha. intros HWa. exact (Hw (proj1 (HWr a HWa))).
- exact (e5_grows_trans _ _ _ HG Hgr).
Qed.

(* the journal allows the frame's bytes and its shadow, and the real stack below sp0 *)
Lemma e_awr_frame : forall D ly S a, e5_geo D ly -> cn_F D <= a < cn_F D + 512 ->
  awr_byte STK_check_no_overread (cn_sp0 D) [] (ablocks B (ci_ly D) (ci_S D)) (ablocks B ly S) ly
    [(CN_CID, ci_fpos D)] a.
Proof.
intros D ly S a G Ha. pose proof G as (EFa & _). right; right; right. exists CN_CID, (ci_fpos D).
split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes CN_CID) with 512. lia.
Qed.
Lemma e_awr_fsh : forall D ly S a, e5_geo D ly -> shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 ->
  awr_byte STK_check_no_overread (cn_sp0 D) [] (ablocks B (ci_ly D) (ci_S D)) (ablocks B ly S) ly
    [(CN_CID, ci_fpos D)] a.
Proof.
intros D ly S a G Ha. pose proof G as (EFa & _). right; right; right. exists CN_CID, (ci_fpos D).
split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes CN_CID / 8) with 64. lia.
Qed.
Lemma e_awr_stack : forall D ly S a, e5_geo D ly -> cn_S1 D - ASTACK <= a < cn_S1 D + 88 ->
  awr_byte STK_check_no_overread (cn_sp0 D) [] (ablocks B (ci_ly D) (ci_S D)) (ablocks B ly S) ly
    [(CN_CID, ci_fpos D)] a.
Proof.
intros D ly S a G Ha. pose proof G as (_ & _ & _ & _ & _ & S16 & _). destruct (e5_S1 D S16) as [_ HS1].
left. rewrite e5_stk. unfold ASTACK in Ha. lia.
Qed.

(* a word read through rdword, from its value bytes (YCem.v:101's argument, which this file cannot Require: YCem.v
   Requires image B's files) *)
Lemma e_rdword_of_val_mem : forall H (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bq : forall q, (q < 8)%nat -> aview SEGS H mem (a + Z.of_nat q) = Some (le_byte v 8 q)).
{ intros q Hq. unfold aview. rewrite (Hv q Hq). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bq 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bq 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bq 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bq 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bq 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bq 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bq 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bq 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ---- cn_base at a later memory of the same state: every byte off the wall and off the own byte kept ---- *)
Lemma e_base_keep : forall D fxk ly S Hp W regs mem md k memE mdE regsE,
  @cn_base fx rc SK PA B ARx D fxk ly S Hp W regs mem md k 0 ->
  CNJ D ly S Hp W memE mdE k 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ e_wall D a -> a <> VAL (A_OBJ 13) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memE) ->
  getr regsE 3%bv = getr regs 3%bv -> getr regsE 4%bv = getr regs 4%bv ->
  @cn_base fx rc SK PA B ARx D fxk ly S Hp W regsE memE mdE k 0.
Proof.
intros D fxk ly S Hp W regs mem md k memE mdE regsE HB HJE KK GR G3 G4.
destruct (e5_geo_of_base D fxk ly S Hp W regs mem md k HB) as [G HAR].
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3c & G4c & HRO).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
assert (Hin : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [HS16 HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (e5_own_img) as [Hoi Hol].
split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJE|]. split; [|split; [|split; [|split]]].
- split; [exact Hfrs|]. split; [exact Hnin|]. split; [|split].
  + rewrite <- Hflag. apply rdword_ext. intros q Hq. change (fs_frame_bytes CN_CID) with 512 in *.
    pose proof (frm_img_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) (VAL (A_OBJ 13)) HAR Hin) as Hfo.
    rewrite EFa in Hfo. change (fs_frame_bytes CN_CID) with 512 in Hfo.
    apply KK.
    * lia.
    * unfold e_wall, shadow_addr. e5_consts. unfold ASTACK. lia.
    * intros E. apply Hfo; [lia | exact Hoi].
  + intros a Ha. apply (e5_apr_grows _ mem memE _ GR). apply Hfpr. exact Ha.
  + intros a Ha. apply (e5_apr_grows _ mem memE _ GR). apply Hshp. exact Ha.
- assert (KS : forall a, cn_S1 D + 88 <= a < 2 ^ 47 -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
  { intros a Ha. destruct (e_cls_stack D ly a G Ha) as [N1 N2]. apply KK; [lia | exact N1 | exact N2]. }
  unfold cn_saved in *.
  repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSV as [H HSV]; apply Forall_cons;
    [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq; apply KS; lia |]).
  apply Forall_nil.
- rewrite G3. exact G3c.
- rewrite G4. exact G4c.
- intros a Hro Hno Herr.
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]. }
  pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow.
  rewrite KK; [exact (HRO a Hro Hno Herr) | e5_consts; lia | exact (e_cls_img D ly S Hp W mem md a G HAR Hin Hi) |].
  intros ->. exact (cni_pst_rw B IMG _ e5_own_pst Hro).
Qed.


(* ---- cn_early at a later memory of the same state: every byte off the wall kept, the own byte too ---- *)
Lemma e_early_keep : forall D ly S Hp W mem md memE rs own,
  e5_geo D ly -> ARx ly S Hp W mem md -> In (CN_CID, ci_fpos D) (frames S) ->
  cn_early B D ly S Hp W mem rs own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ e_wall D a -> a <> VAL (A_OBJ 13) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a) ->
  aview SEGS (w_H W) memE (VAL (A_OBJ 13)) = aview SEGS (w_H W) mem (VAL (A_OBJ 13)) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memE) ->
  cn_early B D ly S Hp W memE rs own.
Proof.
intros D ly S Hp W mem md memE rs own G HAR Hin HE KK KO GR.
destruct HE as (HHp & HLG & HCP & HPERM & HROOM & HRP & HLIVE & Ho1 & Ho2 & Ho3).
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [HS16 HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (e5_own_img) as [Hoi Hol].
assert (KI : forall a, in_img SEGS a -> a <> VAL (A_OBJ 13) -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
{ intros a Hi Hne. pose proof (@pa_segs_low _ _ PA _ Hi). apply KK; [e5_consts; lia | exact (e_cls_img D ly S Hp W mem md a G HAR Hin Hi) | exact Hne]. }
assert (KP : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (Z.eq_dec a (VAL (A_OBJ 13))) as [->|Hne]; [exact KO|].
  destruct (cni_pst_ok B IMG a Ha) as [Hi _]. exact (KI a Hi Hne). }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
{ intros p n a Hb Ha. destruct (e_cls_blk D ly S Hp W mem md p n a G HAR Hin Hb Ha) as (H1 & H3 & _ & H5).
  apply KK; [lia | exact H1 | exact H3]. }
assert (KH : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + req_size n ->
  aview SEGS (w_H W) memE (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
{ intros p n x Hb Hx. destruct (e_cls_blk D ly S Hp W mem md p n x G HAR Hin Hb Hx) as (_ & _ & H4 & H5).
  destruct (e_cls_sh D ly x G H5 H4) as (S1' & S3' & S4').
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply KK; [exact S4' | exact S1' | exact S3']. }
split; [exact HHp|]. split; [|split; [|split; [exact HPERM|split; [exact HROOM|split; [exact HRP|split; [exact HLIVE|]]]]]].
- apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W memE _ _ _ _ _ _ _ HLG).
  + exact KP.
  + intros a kk i Hin' Hi.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLG Hin') as (Hk0 & Hblk & _).
    pose proof cf_head_nonneg. unfold prh_head_wide in HW.
    apply (KB (a - cf_head) (kk + cf_head)); [exact Hblk|]. unfold req_size.
    destruct (kk + cf_head =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
  + intros a kk _ Hb. exact Hb.
  + apply Permutation_refl.
- revert HCP. apply Forall_impl. intros r [-> | (Hb & Hnh & (Hby & H4096 & Hce & Hamr & Hra & Hhull))]; [left; reflexivity|].
  right. split; [exact Hb|]. split; [exact Hnh|].
  pose proof (proj1 (req_size_pos (cn_size D + 16) ltac:(unfold cn_size; lia))) as Hrq.
  pose proof (proj2 (req_size_pos (cn_size D + 16) ltac:(unfold cn_size; lia))) as Hrq2.
  split; [|split; [exact H4096|]; split; [exact Hce|]; split; [exact Hamr|]; split].
  + intros j Hj. destruct (Hby j Hj) as [Hv Hbd]. split; [|exact Hbd].
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact Hv].
    intros q Hq. apply (KB r (cn_size D + 16)); [exact Hb |]. unfold cn_size in *. lia.
  + apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hra].
    intros x Hx. apply (KH r (cn_size D + 16)); [exact Hb |]. unfold cn_size in *. lia.
  + intros Hl s Hs. apply (e5_aview_vis SEGS _ mem memE s GR). exact (Hhull Hl s Hs).
- split; [exact Ho1|]. split; [|exact Ho3].
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact Ho2].
  intros q Hq. assert (Eq : q = 0) by (cbn in Hq; lia). subst q. rewrite Z.add_0_r. exact KO.
Qed.

Lemma e_in_rng : forall (l : list (Z * bv 5)) j r lo hi, Forall (fun p => lo <= fst p < hi) l -> In (j, r) l -> lo <= j < hi.
Proof. intros l j r lo hi H Hin. exact (proj1 (Forall_forall _ _) H (j, r) Hin). Qed.
Lemma e_srli3 : forall x, 0 <= x < 2 ^ 64 -> v_srli (w64 x) 3 = w64 (x / 8).
Proof. intros x Hx. unfold v_srli, w64. rewrite unsigned_lit_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma e_add64 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_add (w64 x) (w64 y) = w64 (x + y).
Proof. intros x y Hx Hy. unfold v_add, w64. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Ltac e_slot_ok := vm_compute; reflexivity.
Ltac e_bvne := let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E.
Ltac e_rs := repeat first [rewrite getr_same by e_bvne | rewrite getr_other by e_bvne].
Ltac e_in := solve [repeat (first [left; reflexivity | right])].

(* ---- CA1: 160 -> 388 ---- *)
Theorem cn_CA1 : @cn_seg_CA1 fx rc ci cp RL SK PA B ARx CTX0.
Proof.
intros P PLAW D fxk ly S Hp W regs mem md k HPRE HAT HPM.
destruct HAT as (HB & HR & HE).
destruct (e5_geo_of_base D fxk ly S Hp W regs mem md k HB) as [G HAR].
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3 & G4 & HRO).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
change (fs_frame_bytes CN_CID / 8) with 64 in Hshp. change (fs_frame_bytes CN_CID) with 512 in Hfpr, Hflag.
assert (Hin : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (e5_S1 D S16) as [HS16 HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof HJ as HJ'. apply e_J0 in HJ'.
destruct HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
rewrite e5_stk in Hpres.
assert (RG : forall r v, In (r, v) [(2%bv, cn_S1 D); (8%bv, cn_sp0 D); (9%bv, cn_S1 D); (10%bv, cn_F D);
  (18%bv, SHADOW_OFF); (20%bv, cn_size D); (23%bv, ci_data D); (27%bv, cn_F D)] -> getr regs r = w64 v)
  by (intros r v Hin'; exact (proj1 (Forall_forall _ _) HR (r, v) Hin')).
set (W1 := fun a => cn_S1 D + 32 <= a < cn_S1 D + 40 \/ cn_S1 D + 80 <= a < cn_S1 D + 88).
set (W2 := fun a => cn_F D <= a < cn_F D + 504 \/ shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64).
pose proof (e_inv_init P D ly S Hp W W1 mem md k HJ HPM) as HI0.
unfold cn_cfg, cn_pc. change (w64 (BASE + CN_OFF + CN_POISON)) with (Z_to_bv 64 (BASE + 804 + 160)).
replace (BASE + 804 + 160) with (BASE + 964) by lia.
(* 160: sd a0, 32(s1) (the fake-frame pointer) *)
apply (s_sd P PLAW W regs mem md _ 964 968 9%bv 10%bv 32 (cn_S1 D + 32)); [e_slot_ok | lia | lia | reflexivity | | lia | lia | | exact HPM |].
{ rewrite (RG 9%bv (cn_S1 D) ltac:(e_in)). unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ intros i Hi. apply Hpres. lia. }
intros md1 mem1 Hs1 Hf1 Hg1 Hh1 Hv1 HP1.
pose proof (e_inv_write P D ly S Hp W W1 mem k mem md mem1 md1 (fun a => cn_S1 D + 32 <= a < cn_S1 D + 32 + 8) HI0
  ltac:(intros a Ha; cbv beta in Ha; split; [unfold W1; left; lia | apply (e_awr_stack D ly S a G); unfold ASTACK; lia]) Hf1 Hg1 Hh1 Hs1 HP1) as HI1.
(* 164: sd s11, 80(s1) *)
apply (s_sd P PLAW W regs mem1 md1 _ 968 972 9%bv 27%bv 80 (cn_S1 D + 80)); [e_slot_ok | lia | lia | reflexivity | | lia | lia | | exact HP1 |].
{ rewrite (RG 9%bv (cn_S1 D) ltac:(e_in)). unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ intros i Hi. apply (e5_apr_grows _ mem mem1 _ Hg1). apply Hpres. lia. }
intros md2 mem2 Hs2 Hf2 Hg2 Hh2 Hv2 HP2.
pose proof (e_inv_write P D ly S Hp W W1 mem k mem1 md1 mem2 md2 (fun a => cn_S1 D + 80 <= a < cn_S1 D + 80 + 8) HI1
  ltac:(intros a Ha; cbv beta in Ha; split; [unfold W1; right; lia | apply (e_awr_stack D ly S a G); unfold ASTACK; lia]) Hf2 Hg2 Hh2 Hs2 HP2) as HI2.
(* the two slots, read back at mem2 *)
assert (R32 : rdword (aview SEGS (w_H W) mem2) (cn_S1 D + 32) = Some (cn_F D)).
{ apply e_rdword_of_val_mem; [|lia].
  apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem2); [|rewrite (RG 10%bv (cn_F D) ltac:(e_in)) in Hv1;
    unfold w64 in Hv1; rewrite unsigned_lit_small in Hv1 by lia; exact Hv1].
  intros q Hq. apply aview_eq_of. apply Hf2. rewrite unsigned_lit_small by lia. lia. }
assert (R80 : rdword (aview SEGS (w_H W) mem2) (cn_S1 D + 80) = Some (cn_F D)).
{ apply e_rdword_of_val_mem; [|lia].
  rewrite (RG 27%bv (cn_F D) ltac:(e_in)) in Hv2. unfold w64 in Hv2. rewrite unsigned_lit_small in Hv2 by lia. exact Hv2. }
destruct HI2 as (HJ2 & HP2' & HK2 & HG2).
pose proof (e_inv_init P D ly S Hp W W2 mem2 md2 k HJ2 HP2') as HI3.
(* 168: lui a1; 172: auipc a2 (PHi); 176: auipc a3 (PHi) *)
apply (s_lui W regs mem2 md2 _ 972 976 11%bv); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros va1 md3 Hs3.
apply (h_phi W _ mem2 md3 _ 976 980 12%bv 7); [reflexivity | reflexivity | lia | lia | reflexivity |].
intros va2 md4 Hs4.
apply (h_phi W _ mem2 md4 _ 980 984 13%bv 8); [reflexivity | reflexivity | lia | lia | reflexivity |].
intros va3 md5 Hs5.
(* 180: srli a0, s11, 3; 184: add s2, a0, s2 (F's shadow); 188: li a0, -8 *)
apply (s_srli W _ mem2 md5 _ 984 988 10%bv 27%bv 3); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md6 Hs6.
apply (s_add W _ mem2 md6 _ 988 992 18%bv 10%bv 18%bv); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md7 Hs7.
apply (e5s_addi W _ mem2 md7 _ 992 996 10%bv 0%bv (-8)); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md8 Hs8.
(* 192: addiw a1; 196: addi a2 (PAddHi); 200: addi a3 (PAddHi) *)
apply (s_addiw W _ mem2 md8 _ 996 1000 11%bv 11%bv); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros va1' md9 Hs9.
apply (h_paddhi W _ mem2 md9 _ 1000 1004 12%bv 12%bv 7 (A_OBJ 2) 0x883b); [reflexivity | reflexivity | lia | lia | reflexivity |].
intros va2' md10 Hs10.
apply (h_paddhi W _ mem2 md10 _ 1004 1008 13%bv 13%bv 8 A_TEXT 0x324); [reflexivity | reflexivity | lia | lia | reflexivity |].
intros va3' md11 Hs11.
pose proof (e_inv_md P D ly S Hp W W2 mem2 k mem2 md2 md11 HI3
  (same_but_materialized_trans _ _ _ Hs3 (same_but_materialized_trans _ _ _ Hs4 (same_but_materialized_trans _ _ _ Hs5
  (same_but_materialized_trans _ _ _ Hs6 (same_but_materialized_trans _ _ _ Hs7 (same_but_materialized_trans _ _ _ Hs8
  (same_but_materialized_trans _ _ _ Hs9 (same_but_materialized_trans _ _ _ Hs10 Hs11))))))))) as HI4.
lazymatch goal with |- SRr _ _ {| cfg_ms := @YK11.mkst _ ?rg _ _ _; cfg_model := _ |} _ => set (regsH := rg) end.
assert (RS2 : getr regsH 18%bv = w64 (shadow_addr (cn_F D))).
{ unfold regsH. e_rs. rewrite (RG 18%bv SHADOW_OFF ltac:(e_in)), (RG 27%bv (cn_F D) ltac:(e_in)).
  rewrite e_srli3 by lia. rewrite e_add64 by (unfold SHADOW_OFF; first [lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]).
  unfold shadow_addr. f_equal. lia. }
assert (RS11 : getr regsH 27%bv = w64 (cn_F D)) by (unfold regsH; e_rs; exact (RG 27%bv (cn_F D) ltac:(e_in))).
(* 204 / 208 / 212: sd a1, 0(s11); sd a2, 8(s11); sd a3, 16(s11): the frame header *)
apply (s_sd P PLAW W regsH mem2 md11 _ 1008 1012 27%bv 11%bv 0 (cn_F D)); [e_slot_ok | lia | lia | reflexivity | | lia | lia | | exact HP2' |].
{ rewrite RS11. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
{ intros i Hi. apply (e5_apr_grows _ mem mem2 _ HG2). apply Hfpr. lia. }
intros md12 mem3 Hs12 Hf3 Hg3 Hh3 _ HP3.
pose proof (e_inv_write P D ly S Hp W W2 mem2 k mem2 md11 mem3 md12 (fun a => cn_F D <= a < cn_F D + 8) HI4
  ltac:(intros a Ha; cbv beta in Ha; split; [unfold W2; left; lia | apply (e_awr_frame D ly S a G); lia]) Hf3 Hg3 Hh3 Hs12 HP3) as HI5.
apply (s_sd P PLAW W regsH mem3 md12 _ 1012 1016 27%bv 12%bv 8 (cn_F D + 8)); [e_slot_ok | lia | lia | reflexivity | | lia | lia | | exact HP3 |].
{ rewrite RS11. unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ intros i Hi. apply (e5_apr_grows _ mem mem3 _ (e5_grows_trans _ _ _ HG2 Hg3)). apply Hfpr. lia. }
intros md13 mem4 Hs13 Hf4 Hg4 Hh4 _ HP4.
pose proof (e_inv_write P D ly S Hp W W2 mem2 k mem3 md12 mem4 md13 (fun a => cn_F D + 8 <= a < cn_F D + 8 + 8) HI5
  ltac:(intros a Ha; cbv beta in Ha; split; [unfold W2; left; lia | apply (e_awr_frame D ly S a G); lia]) Hf4 Hg4 Hh4 Hs13 HP4) as HI6.
apply (s_sd P PLAW W regsH mem4 md13 _ 1016 1020 27%bv 13%bv 16 (cn_F D + 16)); [e_slot_ok | lia | lia | reflexivity | | lia | lia | | exact HP4 |].
{ rewrite RS11. unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. }
{ intros i Hi. apply (e5_apr_grows _ mem mem4 _ (e5_grows_trans _ _ _ HG2 (e5_grows_trans _ _ _ Hg3 Hg4))). apply Hfpr. lia. }
intros md14 mem5 Hs14 Hf5 Hg5 Hh5 _ HP5.
pose proof (e_inv_write P D ly S Hp W W2 mem2 k mem4 md13 mem5 md14 (fun a => cn_F D + 16 <= a < cn_F D + 16 + 8) HI6
  ltac:(intros a Ha; cbv beta in Ha; split; [unfold W2; left; lia | apply (e_awr_frame D ly S a G); lia]) Hf5 Hg5 Hh5 Hs14 HP5) as HI7.
(* 216: li a1, -15; 220-232: four sb *)
apply (e5s_addi W regsH mem5 md14 _ 1020 1024 11%bv 0%bv (-15)); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md15 Hs15.
pose proof (e_inv_md _ _ _ _ _ _ _ _ _ _ _ _ HI7 Hs15) as HI7'.
(* the shadow runs: each byte F's shadow, present *)
assert (Hshw : forall memi mdi, e_inv P D ly S Hp W W2 mem2 k memi mdi -> forall j (r : bv 5), 0 <= j < 40 ->
  0 <= j /\ shadow_addr (cn_F D) + j < 2 ^ 64 /\ apresent (w_H W) memi (shadow_addr (cn_F D) + j)).
{ intros memi mdi (_ & _ & _ & HGi) j r Hj. split; [lia|]. split; [unfold shadow_addr; e5_consts; lia|].
  apply (e5_apr_grows _ mem memi _ (e5_grows_trans _ _ _ HG2 HGi)). apply Hshp. lia. }
assert (Hshs : 0 <= shadow_addr (cn_F D)) by (unfold shadow_addr; e5_consts; lia).
apply (h_sbl P PLAW [(0, 11%bv); (1, 11%bv); (2, 11%bv); (3, 11%bv)] W _ mem5 md15 _ 1024 (shadow_addr (cn_F D)));
  [e_rs; rewrite RS2; reflexivity | exact Hshs | lia | cbn; lia | e_slot_ok |
   intros j r Hj; apply (Hshw _ _ HI7' j r); eapply (e_in_rng _ j r 0 40); [| exact Hj]; repeat constructor; cbn; lia | exact HP5 |].
intros md16 mem6 Hs16 Hf6 Hg6 Hh6 HP6.
assert (HI8 : e_inv P D ly S Hp W W2 mem2 k mem6 md16).
{ eapply (e_inv_write P D ly S Hp W W2 mem2 k mem5 md15 mem6 md16 _ HI7'); [| exact Hf6 | exact Hg6 | exact Hh6 | exact Hs16 | exact HP6].
  intros a (j & r & Hjr & ->). assert (0 <= j < 40) by (eapply (e_in_rng _ j r 0 40); [| exact Hjr]; repeat constructor; cbn; lia).
  split; [unfold W2; right; lia | apply (e_awr_fsh D ly S _ G); lia]. }
cbn [length Z.of_nat Pos.of_succ_nat] in *. change (1024 + 4 * 4) with 1040.
(* 236: li a1, -14; 240-300: sixteen sb *)
apply (e5s_addi W _ mem6 md16 _ 1040 1044 11%bv 0%bv (-14)); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md17 Hs17.
pose proof (e_inv_md _ _ _ _ _ _ _ _ _ _ _ _ HI8 Hs17) as HI8'.
apply (h_sbl P PLAW [(12, 11%bv); (13, 11%bv); (14, 11%bv); (15, 11%bv); (8, 10%bv); (9, 10%bv); (10, 10%bv);
  (11, 11%bv); (20, 10%bv); (21, 10%bv); (22, 10%bv); (23, 11%bv); (24, 11%bv); (25, 11%bv); (26, 11%bv); (27, 11%bv)]
  W _ mem6 md17 _ 1044 (shadow_addr (cn_F D)));
  [e_rs; rewrite RS2; reflexivity | exact Hshs | lia | cbn; lia | e_slot_ok |
   intros j r Hj; apply (Hshw _ _ HI8' j r); eapply (e_in_rng _ j r 0 40); [| exact Hj]; repeat constructor; cbn; lia | exact HP6 |].
intros md18 mem7 Hs18 Hf7 Hg7 Hh7 HP7.
assert (HI9 : e_inv P D ly S Hp W W2 mem2 k mem7 md18).
{ eapply (e_inv_write P D ly S Hp W W2 mem2 k mem6 md17 mem7 md18 _ HI8'); [| exact Hf7 | exact Hg7 | exact Hh7 | exact Hs18 | exact HP7].
  intros a (j & r & Hjr & ->). assert (0 <= j < 40) by (eapply (e_in_rng _ j r 0 40); [| exact Hjr]; repeat constructor; cbn; lia).
  split; [unfold W2; right; lia | apply (e_awr_fsh D ly S _ G); lia]. }
cbn [length Z.of_nat Pos.of_succ_nat] in *. change (1044 + 4 * 16) with 1108.
(* 304: li a1, -13; 308-384: twenty sb *)
apply (e5s_addi W _ mem7 md18 _ 1108 1112 11%bv 0%bv (-13)); [e_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md19 Hs19.
pose proof (e_inv_md _ _ _ _ _ _ _ _ _ _ _ _ HI9 Hs19) as HI9'.
apply (h_sbl P PLAW [(4, 10%bv); (5, 10%bv); (6, 10%bv); (7, 10%bv); (16, 10%bv); (17, 10%bv); (18, 10%bv);
  (19, 10%bv); (28, 10%bv); (29, 10%bv); (30, 10%bv); (31, 10%bv); (36, 11%bv); (37, 11%bv); (38, 11%bv); (39, 11%bv);
  (32, 10%bv); (33, 10%bv); (34, 10%bv); (35, 11%bv)]
  W _ mem7 md19 _ 1112 (shadow_addr (cn_F D)));
  [e_rs; rewrite RS2; reflexivity | exact Hshs | lia | cbn; lia | e_slot_ok |
   intros j r Hj; apply (Hshw _ _ HI9' j r); eapply (e_in_rng _ j r 0 40); [| exact Hj]; repeat constructor; cbn; lia | exact HP7 |].
intros md20 mem8 Hs20 Hf8 Hg8 Hh8 HP8.
assert (HI10 : e_inv P D ly S Hp W W2 mem2 k mem8 md20).
{ eapply (e_inv_write P D ly S Hp W W2 mem2 k mem7 md19 mem8 md20 _ HI9'); [| exact Hf8 | exact Hg8 | exact Hh8 | exact Hs20 | exact HP8].
  intros a (j & r & Hjr & ->). assert (0 <= j < 40) by (eapply (e_in_rng _ j r 0 40); [| exact Hjr]; repeat constructor; cbn; lia).
  split; [unfold W2; right; lia | apply (e_awr_fsh D ly S _ G); lia]. }
cbn [length Z.of_nat Pos.of_succ_nat] in *. change (1112 + 4 * 20) with 1192.
(* ---- the exit CN_COPY1 (388) ---- *)
destruct HI10 as (HJE & HPE & HKE & HGE).
lazymatch goal with |- SRr _ _ {| cfg_ms := @YK11.mkst _ ?rg _ _ _; cfg_model := _ |} _ => set (regsE := rg) end.
assert (NS : forall a, cn_S1 D - ASTACK <= a < 2 ^ 47 -> ~ W2 a).
{ intros a Ha. unfold W2, shadow_addr. e5_consts. unfold ASTACK in Ha. lia. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ e_wall D a -> aview SEGS (w_H W) mem8 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hw. rewrite (HKE a Ha ltac:(intros H2; apply Hw; destruct H2 as [H2|H2]; [left|right; left]; exact H2)).
  apply HK2; [exact Ha|]. intros H1. apply Hw. right; right. unfold W1 in H1. unfold ASTACK. lia. }
assert (GRE : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem8)) by exact (e5_grows_trans _ _ _ HG2 HGE).
pose proof (e5_own_img) as [Hoi Hol].
apply SRr_ret. split; [|exact HPE].
exists fxk, ly, S, Hp, regsE, mem8, md20, k. split.
{ unfold cn_cfg, cn_pc. change (w64 (BASE + CN_OFF + CN_COPY1)) with (Z_to_bv 64 (BASE + 804 + 388)).
  replace (BASE + 804 + 388) with (BASE + 1192) by lia. reflexivity. }
split.
{ apply (e_base_keep D fxk ly S Hp W regs mem md k mem8 md20 regsE HB HJE
    (fun a Ha Hw _ => KEEP a Ha Hw) GRE); unfold regsE, regsH; e_rs; reflexivity. }
split.
{ unfold cn_regsat, cn_core. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd]; unfold regsE; e_rs;
    first [exact RS2 | unfold regsH; e_rs; apply RG; e_in] |]). apply Forall_nil. }
split.
{ unfold cn_slotsL. apply Forall_cons; [cbn [fst snd] | apply Forall_cons; [cbn [fst snd] | apply Forall_nil]].
  - rewrite <- R32. apply rdword_ext. intros q Hq. apply HKE; [lia | apply NS; unfold ASTACK; lia].
  - rewrite <- R80. apply rdword_ext. intros q Hq. apply HKE; [lia | apply NS; unfold ASTACK; lia]. }
(* the cut's LAST conjunct (the hull stages): this segment's steps are stores, the allocator state S is the entry's,
   so the entry's budget carries over unchanged *)
split; [|exact (proj2 HE)].
exact (e_early_keep D ly S Hp W mem md mem8 [] 0 G HAR Hin (proj1 HE) (fun a Ha Hw _ => KEEP a Ha Hw)
  (KEEP (VAL (A_OBJ 13)) ltac:(unfold kLowMemEnd in Hol; lia) (e_cls_img D ly S Hp W mem md _ G HAR Hin Hoi)) GRE).
Qed.

End e1.
