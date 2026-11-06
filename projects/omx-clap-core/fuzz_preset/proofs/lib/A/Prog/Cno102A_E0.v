(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/Prog/Ent102L0B.v, with its module paths and module names changed; 543 of its 737 lines of code are new or changed and 936 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): segment CA0 of
   the re-walk of check_no_overread (cno) against the text tcheck_no_overread_specX: the entry (A' 0x81904) to the
   cut CN_POISON (+160), with the class-3 fake frame of __asan_stack_malloc_3 (+112). FREE-PIECES-102 Part 7
   row R7-3.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   THE CODE (A' 0x81904; DERIVED byte offsets from the entry, the listing's slots 201 + off / 4):
     +0 .. +88   addi sp, sp, -192; sd zero, 0(sp); the thirteen saves (ra, s0, s1, s2 .. s11 at sp0 - 8 .. sp0 - 104);
                 s0 = sp0; sp = s1 = (sp0 - 192) land -32 (cn_S1); s4 = size; a2 = [A_OBJ 1] (the GOT word of
                 __asan_option_detect_stack_use_after_return), a1 = [A_OBJ 0] (the GOT word of the shadow base).
                 ONE engine run (YC1fPx.paj_run_to_x_inv at P).
     +92         lw a2, 0(a2): the option cell, 1 by the ARx const law (YCbqG.v alx_const). One engine run.
     +96 .. +112 ld s2, 0(a1) (SHADOW_OFF, the const law); s7 = data; beqz a2 (not taken: a2 = 1, a fact of the
                 symbolic state); a0 = 320; jal __asan_stack_malloc_3. One engine run to the callee entry.
     the call    e0_sm_at below: YGcallMxmn.v aj_stack_malloc_at_xm (statement and proof) with its SMX premise
                 replaced by the position the caller names: cn_fp's path, through stack_malloc_inv (the state program is
                 a function of the state, so the frame is at ci_fpos D and the new state is the one cn_fp names).
     +116 .. +128 j +8; mv s11, a0; bnez a0 (taken: a0 = F >= 4096): Cno102A_Ro.v's hand steps, to CN_POISON.
   WHAT THE CUT GETS: the journal and the frame from the call; the saved words from the run's chunks (above the call's
   window: acall_kept's first clause); the ledger, the statics and arodata_okP by acall_kept's image clause (the
   statics are image bytes off the runtime's owned statics and errno: cn_img's cni_pst_ok / cni_pst_errno); the room
   and its position by set_fs (RL_set_fs, PresetRoomPosKeep.room_pos_set_fs).
   SECTION HYPOTHESES (owners): PAL : PALib (the whole-program listing's GOT words and the allocator entries; the
   image binding), SYMS : asyms_ok B (the runtime symbol record's area bounds; the image binding),
   SM3 (the listing's __asan_stack_malloc_3 is the runtime's class-3 entry; the image binding), OWNLOW (ARx's
   owned-low law: AR_laws_x does not carry it; at the cf instance ARx_owned_low_law_xs), ASM3 :
   astack_malloc_realizes_xm .. 3 (the frame-area row), LAWS, IMG (cn_img).
   Numerals: offsets (DERIVED); 192 / 104 / 32 / 16 / 8 (LENGTH: the frame, its slots, the alignment); 320 (LENGTH:
   the class-3 request); 3 (the class); register numbers (WORD); 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (LENGTH). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx YGcallMx YGcallMxmn FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Cno102A_Base Cno102A_Ro Cno102A_E.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image-free facts ---- *)
(* the state program of __asan_stack_malloc_<cid> (YG00.v stack_malloc), inverted (A/FCm3r.v:306's lemma and proof,
   copied: that file is an old-pin image file) *)
Lemma e0_sm_inv : forall cid S pos S',
  apath (stack_malloc cid S) [] (PFake cid pos, S') ->
  exists hint', fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') /\
  S' = set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S.
Proof.
intros cid S pos S' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[p h']|] eqn:Hp.
- cbn [ibind apath] in H. injection H as <- <-. exists h'. split; reflexivity.
- cbn [apath] in H. discriminate H.
Qed.

(* the facts of the state cn_fp names: the new frame on top, fresh, the state a set_fs of the old *)
Lemma e0_sm_facts : forall cid S pos S', 0 <= cid <= 10 ->
  apath (stack_malloc cid S) [] (PFake cid pos, S') ->
  (exists f, S' = set_fs f S) /\ frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof.
intros cid S pos S' Hc H. destruct (e0_sm_inv cid S pos S' H) as (h' & Hpr & ->).
destruct (fs_probe_some _ _ _ _ _ _ (fs_frames_pos cid Hc) Hpr) as (h & _ & _ & _ & Hm).
split; [eexists; reflexivity|]. split; [reflexivity|]. exact (mem_pos_false _ _ _ Hm).
Qed.

Lemma e0_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.

(* `andi sp, sp, -32` (Ent102L0A.v l0_land_m32 / l0_and_m32 by path, written against H6_Base.v:66-98 (sha256 f6829081650b; internal record)) *)
Lemma e0_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x / 32 * 32.
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.shiftl (Z.ones 59) 5) by (vm_compute; reflexivity).
assert (E2 : x / 32 * 32 = Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
rewrite E1, E2. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 5) as [H5|H5].
- rewrite !(Z.testbit_neg_r _ (i - 5)) by lia. apply Bool.andb_false_r.
- rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia.
  destruct (Z.lt_ge_cases (i - 5) 59) as [H59|H59].
  + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
  + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma e0_and_m32 : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 (-32)) = Z_to_bv 64 (x / 32 * 32).
Proof.
intros x Hx. unfold alu64, alu. cbn. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small x) by lia.
replace ((-32) mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity. rewrite e0_land_m32 by exact Hx.
pose proof (Z.div_pos x 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le x 32 ltac:(lia)).
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma e0_add0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
intro x. change (alu64 ALU_ADD x (Z_to_bv 64 0)) with ((x + Z_to_bv 64 0)%bv). apply bv_eq.
rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0%Z. rewrite Z.add_0_r.
apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* a byte the view reads, off the image's segments, is present *)
Lemma e0_present_of_view : forall segs H (mem : word -> option byte) a, seg_rom segs (Z_to_bv 64 a) = None ->
  aview segs H mem a <> None -> apresent H mem a.
Proof.
intros segs H mem a Hr Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
destruct (H (Z_to_bv 64 a)) eqn:EH; [rewrite Hr in Hv; exfalso; apply Hv; reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:EM; [split; [reflexivity | exists b; reflexivity]|].
rewrite Hr in Hv. exfalso. apply Hv. reflexivity.
Qed.
Lemma e0_seg_rom_none : forall segs a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> seg_rom segs (Z_to_bv 64 a) = None.
Proof.
intros segs a Ha Hn. unfold seg_rom, memory_read.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). cbn [Z.of_N].
destruct (find_segment segs a 1) as [sg|] eqn:E; [|reflexivity].
exfalso. apply Hn. apply find_segment_some_spec in E as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

(* ---- THE FRAME CALL at a NAMED position: YGcallMxmn.v aj_stack_malloc_at_xm (Section srule), statement and proof,
   with its Section hypothesis SMX replaced by the four facts of the position the caller names ---- *)
Section esm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Local Abbreviation code := (as_code B).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.

Lemma e0_sm_at : forall cid, astack_malloc_realizes_xm segs B ARx cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw pos S2,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
apath (stack_malloc cid Sc) [] (PFake cid pos, S2) -> (exists f, S2 = set_fs f Sc) ->
frames S2 = (cid, pos) :: frames Sc -> ~ In (cid, pos) (frames Sc) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own) lyc S2 Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept_x segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw pos S2
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt Hpath (f & ES2) Hfrs2 Hfresh.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs. pose proof (ajx_wle HJ) as Hwle.
pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk.
pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4.
pose proof (ajx_gone HJ) as Hgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstatic.
pose proof (ajx_extra HJ) as F5. pose proof (ajx_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
eapply SRr_mono; [exact (ASM lyc Sc Hpc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2 & Hmn).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal_x segs B [] ARx ESTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [(cid, pos)] lyc S2 Hpc W mem2 md2 0).
{ eapply (call_effect_journal_x segs B ARx LAWS segs_low errno_low OWNLOW ESTACK lyc Sc Hpc W regsT memT mdc lyc S2 Hpc W
    mem2 md2 (fun _ => False) [] [(cid, pos)] 0 []);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR
  | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | | ].
  - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p n i Hp0 Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp0.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
  - rewrite ES2. apply wild_part_same. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
  eapply (ajournal_x_sub segs B PST ARx LAWS segs_low);
  [exact HJ | exact (ajournal_x_nil_pst segs B ARx PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1. split; [| exact Hmn].
eapply (acall_kept_of_journal_x segs B ARx segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.
End esm.

(* ======== CA0 ======== *)
Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
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
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis SYMS : asyms_ok B.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SM3 : pc_stack_malloc (as_code B) CN_CID = SIGMA AS___asan_stack_malloc_3.
Hypothesis ASM3 : astack_malloc_realizes_xm SEGS B ARx CN_CID.
Hypothesis HW : prh_head_wide.

Lemma e0_cells :
  (4096 <= as_shadow_cell B /\ as_shadow_cell B + 8 <= kImgEnd) /\
  (4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kImgEnd) /\
  (4096 <= as_got_shadow B /\ as_got_shadow B + 8 <= kImgEnd) /\
  (4096 <= as_got_uar B /\ as_got_uar B + 8 <= kImgEnd).
Proof.
pose proof (asyms_area_bound B (as_shadow_cell B, 8) SYMS ltac:(cbn; tauto)) as C1.
pose proof (asyms_area_bound B (as_uar_cell B, 4) SYMS ltac:(cbn; tauto)) as C2.
pose proof (asyms_area_bound B (as_got_shadow B, 8) SYMS ltac:(cbn; tauto)) as C3.
pose proof (asyms_area_bound B (as_got_uar B, 8) SYMS ltac:(cbn; tauto)) as C4.
cbn [fst snd] in C1, C2, C3, C4. tauto.
Qed.

(* an 8-byte / 4-byte read-only chunk of the symbolic memory, from a value read of the current view (Ent102L0A.v
   l0_chunk8 / l0_chunk4) *)
Lemma e0_chunk8 : forall (E : env) (m : word -> option byte) (e : sv) (base v : Z),
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem SEGS m base 8 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 8 e)).
Proof.
intros E m e base v He Hv Hm.
apply (YI04.chunk_ok_val SEGS E m base 0 8 e v He).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- change (Z.of_N 8) with 8. lia.
- change (N.to_nat 8) with 8%nat. replace (base + 0) with base by lia. exact Hm.
Qed.
Lemma e0_chunk4 : forall (E : env) (m : word -> option byte) (e : sv) (base v : Z),
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> val_mem SEGS m base 4 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 4 e)).
Proof.
intros E m e base v He Hv Hm.
apply (YI04.chunk_ok_val SEGS E m base 0 4 e v He).
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
- change (Z.of_N 4) with 4. lia.
- change (N.to_nat 4) with 4%nat. replace (base + 0) with base by lia. exact Hm.
Qed.
Lemma e0_val_mem_of_rd32 : forall H mem a v,
  rd32 (aview SEGS H mem) a v -> val_mem SEGS (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hr; [|discriminate Hr].
injection Hr as Hb. f_equal. cbv [YO0f.le_byte YG0f.le_byte] in *. rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- the three stretches' symbolic states (Ent102L0A.v's L0a stretches, at cno's frame of 192) ---- *)
Definition e0_Bx : sv := SLit SHADOW_OFF.
Definition e0_Bspan : Z * Z := (0, 0).
Definition e0_r_gots : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 12) 0))].
Definition e0_r_gotu : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition e0_regions0 : smem := [stack_region 192; e0_r_gots; e0_r_gotu].
Definition e0_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition e0_ss0 : sstate := mkSS CN_OFF sr_atoms e0_regions0 None e0_facts0.
Definition e0_E0 (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 (as_uar_cell B)]).
Definition e0_E1 (regs1 : bvmap 5 word) : env := Eimg (Ereg regs1 []).
Definition e0_r_uar : YP09.region := YP09.mkRegion (Some 12%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition e0_ss1 : sstate := mkSS (CN_OFF + 92) sr_atoms [e0_r_uar] None (mkFacts [] [] []).
Definition e0_r_sb : YP09.region := YP09.mkRegion (Some 11%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit SHADOW_OFF))].
Definition e0_ss2 : sstate := mkSS (CN_OFF + 96) sr_atoms [e0_r_sb] None (mkFacts [(12%nat, mkAF 1 1 0)] [] []).

Lemma e0_entry0 : forall ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARx STK_check_no_overread ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (e0_E0 regs) e0_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CN_OFF)) mem (seg_rom SEGS))) /\
  sh_ok SEGS e0_Bx [] (e0_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_check_no_overread = 27424) by (vm_compute; reflexivity).
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
destruct e0_cells as ((D1 & D2) & (D3 & D4) & (D5 & D6) & (D7 & D8)).
rewrite (pal_got_shadow B PAL) in Kgot, D5, D6.
rewrite (pal_cell B PAL) in Kgot, Kcell, D1, D2.
rewrite (pal_got_uar B PAL) in Kguar, D7, D8.
pose proof (pal_got_uar_disj B PAL) as (Hdisj01 & Hdisj112).
pose proof (pal_got_cell B PAL) as Hdisj012.
rewrite restrict_mkst_fx.
set (E := e0_E0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold e0_E0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 (as_uar_cell B)]) n)
  by (intros n0 Hn0; subst E; unfold e0_E0; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (HkI : kImgEnd = 0x677000) by reflexivity.
assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 64) by lia.
assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 64) by lia.
assert (R12 : 0 <= VAL (A_OBJ 12) < 2 ^ 64) by lia.
assert (RU : 0 <= as_uar_cell B < 2 ^ 64) by lia.
split.
- unfold e0_ss0. apply pa_entry_st_ok_full.
  + subst E. unfold e0_E0. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold e0_regions0, stack_region, e0_r_gots, e0_r_gotu.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (e0_chunk8 E _ (SOff (A_OBJ 12) 0) (VAL (A_OBJ 0)) (VAL (A_OBJ 12)));
      [ cbn [sv_denot]; rewrite Z.add_0_r; apply bv_eq; rewrite U12, Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.mod_small by lia; reflexivity
      | exact R12
      | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot) ].
    * rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (e0_chunk8 E _ (SOff 32 0) (VAL (A_OBJ 1)) (as_uar_cell B));
      [ cbn [sv_denot]; rewrite Z.add_0_r, E32; apply Z_to_bv_bv_unsigned
      | exact RU
      | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar) ].
  + apply pairwise_disjoint_of_extents.
    unfold e0_regions0, stack_region, e0_r_gots, e0_r_gotu, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U0, U1.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok e0_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

Theorem cn_CA0 : @cn_seg_CA0 fx rc ci cp RL SK PA B ARx CTX0.
Proof.
intros P PLAW PCALL D HPRE HFP HPM.
pose proof (cn_pre_fpre B ARx CTX0 D HPRE) as HFPRE. pose proof (cn_pre_mn B ARx CTX0 D HPRE) as HMN.
pose proof (cn_pre_univ B ARx CTX0 D HPRE) as HUNIV. pose proof (cn_pre_ctx B ARx CTX0 D HPRE) as HCTX.
pose proof (cn_pre_r10 B ARx CTX0 D HPRE) as Ha0. pose proof (cn_pre_r11 B ARx CTX0 D HPRE) as Ha1.
pose proof (cn_pre_size B ARx CTX0 D HPRE) as Hsz. pose proof (cn_pre_src B ARx CTX0 D HPRE) as HSRC.
pose proof (cn_pre_home B ARx CTX0 D HPRE) as HHOME. pose proof (cn_pre_ledger B ARx CTX0 D HPRE) as HLED.
pose proof (cn_pre_cnt B ARx CTX0 D HPRE) as HCNT. pose proof (cn_pre_ran B ARx CTX0 D HPRE) as HRAN.
pose proof (cn_pre_most B ARx CTX0 D HPRE) as HRQ. pose proof (cn_pre_live B ARx CTX0 D HPRE) as HLIVE.
pose proof (cn_pre_max16 B ARx CTX0 D HPRE) as HMAX1. pose proof (cn_pre_maxpj B ARx CTX0 D HPRE) as HMAX2.
pose proof (cn_pre_frames B ARx CTX0 D HPRE) as HFRS. pose proof (cn_pre_room B ARx CTX0 D HPRE) as HROOM.
pose proof (cn_pre_frm0 B ARx CTX0 D HPRE) as HFRM. pose proof (cn_pre_wild B ARx CTX0 D HPRE) as HWILD.
pose proof (cn_pre_pksec B ARx CTX0 D HPRE) as HPKS. pose proof (cn_pre_pk24 B ARx CTX0 D HPRE) as HPK24.
destruct HFPRE as (HPREx & HROD & HSPHI & HRAC).
pose proof HPREx as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (e0_entry0 (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_regs D) (ci_mem D) (ci_md D) (ci_ch D) HPREx) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B prh_pst ARx STK_check_no_overread [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D)
  (ci_regs D) (ci_mem D) (ci_md D) (ci_ch D) HPREx) as HJ.
set (EV := e0_E0 (ci_regs D)) in *.
assert (HEI : img_env VAL A_LIM EV) by (unfold EV, e0_E0; apply Eimg_env).
assert (EWr : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EV n = getr (ci_regs D) r).
{ intros n r Hn Hr. unfold EV, e0_E0. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat (ci_regs D) _ n r Hr). }
assert (E2 : ew EV 2 = getr (ci_regs D) 2) by (apply EWr; [lia | reflexivity]).
assert (Usp : bv_unsigned (ew EV 2) = spZ (ci_regs D)) by (rewrite E2; reflexivity).
assert (E32 : ew EV 32 = Z_to_bv 64 (as_uar_cell B))
  by (unfold EV, e0_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ci_regs D) _ 0)).
assert (HkI : kImgEnd = 0x677000) by reflexivity.
assert (HSTK : STK_check_no_overread = 27424) by (vm_compute; reflexivity).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_cno_A PA B prh_pst ARx cf_head LAWS P PLAW).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_cno_A PA B prh_pst ARx cf_head LAWS P PLAW).
unfold cn_entry_cfg, cn_cfg. rewrite (cni_entry B IMG). change (w64 (BASE + CN_OFF)) with (Z_to_bv 64 (BASE + CN_OFF)).
(* ---- STRETCH 1: +0 .. +88 ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM e0_Bspan (CN_OFF + 92).
{ intros a (r & Hr & Ha). unfold e0_ss0, e0_regions0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [stack_region e0_r_gots e0_r_gotu YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?Usp in Ha; unfold awr_byte.
  - left. lia.
  - exfalso. lia.
  - exfalso. lia. }
rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (12%bv : bv 5) R12. prreg HS (20%bv : bv 5) R20.
(* the bytes the run wrote: the frame [sp0 - 192, sp0) *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ci_regs D) - 192 <= a < spZ (ci_regs D)) ->
  aview SEGS (w_H (ci_W D)) (ms_mem ms) a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha Hna. unfold aview, mbyte. rewrite (HFr1 (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hb). unfold e0_ss0, e0_regions0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [stack_region e0_r_gots e0_r_gotu YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?Usp in Hb; lia. }
(* the saved block, read back from the prologue's own chunks *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMO & _).
cbn [ss_mem] in HMO. apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HCH).
cbn [YP09.r_chunks YP09.r_base base_val] in HCH. rewrite Usp in HCH.
pose proof (proj1 (Forall_forall _ _) HCH) as HCA.
assert (SAV : forall (off : Z) (n : nat) (r : bv 5),
  YP09.chunk_ok SEGS EV (mrestrict (w_H (ci_W D)) (ms_mem ms)) (spZ (ci_regs D))
    (YP09.mkChunk (- off) (CVal 8 (SOff n 0))) ->
  (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  val_mem SEGS (mrestrict (w_H (ci_W D)) (ms_mem ms)) (spZ (ci_regs D) - off) 8
    (bv_unsigned (getr (ci_regs D) r))).
{ intros off n r HC Hn Hr. rewrite <- (EWr n r Hn Hr).
  assert (Hd : sv_denot EV (SOff n 0) = Z_to_bv 64 (bv_unsigned (ew EV n)))
    by (cbn; rewrite Z.add_0_r; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ew EV n)) as Hrg. change (bv_modulus 64) with (2 ^ 64) in Hrg.
  pose proof (val_of_chunk_ok SEGS EV (mrestrict (w_H (ci_W D)) (ms_mem ms)) (spZ (ci_regs D)) (- off) 8
    (SOff n 0) (bv_unsigned (ew EV n)) HC Hd
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as HV.
  change (N.to_nat 8) with 8%nat in HV. replace (spZ (ci_regs D) - off) with (spZ (ci_regs D) + - off) by lia.
  exact HV. }
(* ---- STRETCH 2: +92, the option cell ---- *)
destruct (alx_const SEGS B ARx LAWS _ _ _ _ _ _ HAR) as (K1 & K2 & K3 & K4).
destruct e0_cells as ((Dc1 & Dc2) & (Du1 & Du2) & (Dg1 & Dg2) & (Dq1 & Dq2)).
assert (HU : val_mem SEGS (mrestrict (w_H (ci_W D)) (ms_mem ms)) (as_uar_cell B) 4 1).
{ apply e0_val_mem_of_rd32. intros q Hq. cbn in Hq.
  rewrite (KEEP0 (as_uar_cell B + Z.of_nat q) ltac:(unfold kImgEnd in Du2; lia)
    ltac:(unfold kImgEnd in Du2; lia)).
  exact (K2 q Hq). }
assert (U12' : bv_unsigned (ew (e0_E1 (ms_regs ms)) 12) = as_uar_cell B).
{ unfold e0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms) [] 12 12%bv eq_refl), R12, E32.
  apply unsigned_lit_small. unfold kImgEnd in Du2. lia. }
assert (HEI1 : img_env VAL A_LIM (e0_E1 (ms_regs ms))) by (unfold e0_E1; apply Eimg_env).
assert (SHOK1 : sh_ok SEGS e0_Bx [] (e0_E1 (ms_regs ms)) (mrestrict (w_H (ci_W D)) (ms_mem ms)))
  by apply Forall_nil.
assert (HS1 : st_ok_pi SEGS VAL (e0_E1 (ms_regs ms)) e0_ss1
  (restrict (w_H (ci_W D)) (mkst (ms_regs ms) (Z_to_bv 64 (BASE + (CN_OFF + 92))) (ms_mem ms) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold e0_ss1. apply pa_entry_st_ok_full.
  - unfold e0_E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, e0_r_uar.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U12'. unfold kImgEnd in Du2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (e0_chunk4 _ _ (SLit 1) (as_uar_cell B) 1); [vm_compute; reflexivity | lia | exact HU].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; exact I. }
clear HS SHOK.
paj_run_to_tok_x_inv RUNTO HS1 HJ SHOK1 HPM e0_Bspan (CN_OFF + 96).
{ intros a (r & Hr & Ha). unfold e0_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[]]. cbn [e0_r_uar YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
pmkst HS1.
prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (12%bv : bv 5) Q12. prreg HS1 (1%bv : bv 5) Q1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
prreg HS1 (8%bv : bv 5) Q8. prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (10%bv : bv 5) Q10.
prreg HS1 (20%bv : bv 5) Q20.
(* stretch 2 wrote nothing (its one region is read-only) *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H (ci_W D)) (ms_mem ms0) a = aview SEGS (w_H (ci_W D)) (ms_mem ms) a).
{ intros a Ha. unfold aview, mbyte. rewrite (HFr2 (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr & Hb). unfold e0_ss1 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [e0_r_uar YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia. }
(* ---- STRETCH 3: +96 .. +112, to the frame call ---- *)
assert (U11b : bv_unsigned (ew (e0_E1 (ms_regs ms0)) 11) = as_shadow_cell B).
{ unfold e0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms0) [] 11 11%bv eq_refl), Q11.
  unfold e0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms) [] 11 11%bv eq_refl), R11.
  rewrite (pal_cell B PAL). exact (HEI (A_OBJ 12) ltac:(unfold A_TEXT, A_OBJ, A_LIM; lia)). }
assert (HSBr : rdword (aview SEGS (w_H (ci_W D)) (ms_mem ms0)) (as_shadow_cell B) = Some SHADOW_OFF).
{ rewrite <- K1. apply rdword_ext. intros q Hq. unfold kImgEnd in Dc2.
  rewrite (KEEP1 (as_shadow_cell B + q) ltac:(lia)).
  exact (KEEP0 (as_shadow_cell B + q) ltac:(lia) ltac:(lia)). }
assert (HSB : val_mem SEGS (mrestrict (w_H (ci_W D)) (ms_mem ms0)) (as_shadow_cell B) 8 SHADOW_OFF)
  by exact (val_mem_of_rdword SEGS (w_H (ci_W D)) (ms_mem ms0) _ _ HSBr).
assert (HEIb : img_env VAL A_LIM (e0_E1 (ms_regs ms0))) by (unfold e0_E1; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS e0_Bx [] (e0_E1 (ms_regs ms0)) (mrestrict (w_H (ci_W D)) (ms_mem ms0)))
  by apply Forall_nil.
assert (HS2 : st_ok_pi SEGS VAL (e0_E1 (ms_regs ms0)) e0_ss2
  (restrict (w_H (ci_W D)) (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + (CN_OFF + 96))) (ms_mem ms0) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold e0_ss2. apply pa_entry_st_ok_full.
  - unfold e0_E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, e0_r_sb.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11b. unfold kImgEnd in Dc2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (e0_chunk8 _ _ (SLit SHADOW_OFF) (as_shadow_cell B) SHADOW_OFF);
      [vm_compute; reflexivity | unfold SHADOW_OFF; lia | exact HSB].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I | exact I]]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (H12 : bv_unsigned (ew (e0_E1 (ms_regs ms0)) 12) = 1).
    { unfold e0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_nat (ms_regs ms0) [] 12 12%bv eq_refl), Q12. apply unsigned_lit_small. lia. }
    rewrite H12. split; [lia|]. split; [reflexivity | lia]. }
clear HS1 SHOK1.
paj_run_tok_x_inv RUN HS2 HJ SHOK2 HPM e0_Bspan.
{ intros a (r & Hr & Ha). unfold e0_ss2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[]]. cbn [e0_r_sb YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
rename HF into HF3. rename HFr into HFr3. rename HG into HG3.
pmkst HS2.
prreg HS2 (1%bv : bv 5) T1. prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3.
prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8. prreg HS2 (9%bv : bv 5) T9.
prreg HS2 (10%bv : bv 5) T10. prreg HS2 (18%bv : bv 5) T18. prreg HS2 (20%bv : bv 5) T20.
prreg HS2 (23%bv : bv 5) T23.
(* stretch 3 wrote nothing either *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H (ci_W D)) (ms_mem ms1) a = aview SEGS (w_H (ci_W D)) (ms_mem ms0) a).
{ intros a Ha. unfold aview, mbyte. rewrite (HFr3 (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr & Hb). unfold e0_ss2 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [e0_r_sb YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia. }
assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ci_regs D) - 192 <= a < spZ (ci_regs D)) ->
  aview SEGS (w_H (ci_W D)) (ms_mem ms1) a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha Hn. rewrite (KEEP2 a Ha), (KEEP1 a Ha). exact (KEEP0 a Ha Hn). }
(* the registers at the call, chained back to the entry registers *)
assert (EW1 : forall (regs1 : bvmap 5 word) (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (e0_E1 regs1) n = getr regs1 r).
{ intros regs1 n r Hn Hr. unfold e0_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs1 _ n r Hr). }
rewrite (EW1 (ms_regs ms0) 2%nat 2%bv ltac:(lia) eq_refl), Q2, (EW1 (ms_regs ms) 2%nat 2%bv ltac:(lia) eq_refl),
  R2, Usp in T2.
rewrite (EW1 (ms_regs ms0) 3%nat 3%bv ltac:(lia) eq_refl), Q3, (EW1 (ms_regs ms) 3%nat 3%bv ltac:(lia) eq_refl),
  R3, (EWr 3%nat 3%bv ltac:(lia) eq_refl) in T3.
rewrite (EW1 (ms_regs ms0) 4%nat 4%bv ltac:(lia) eq_refl), Q4, (EW1 (ms_regs ms) 4%nat 4%bv ltac:(lia) eq_refl),
  R4, (EWr 4%nat 4%bv ltac:(lia) eq_refl) in T4.
rewrite (EW1 (ms_regs ms0) 8%nat 8%bv ltac:(lia) eq_refl), Q8, (EW1 (ms_regs ms) 8%nat 8%bv ltac:(lia) eq_refl),
  R8, E2 in T8.
rewrite (EW1 (ms_regs ms0) 9%nat 9%bv ltac:(lia) eq_refl), Q9, (EW1 (ms_regs ms) 9%nat 9%bv ltac:(lia) eq_refl),
  R9, Usp in T9.
rewrite (EW1 (ms_regs ms0) 20%nat 20%bv ltac:(lia) eq_refl), Q20, (EW1 (ms_regs ms) 20%nat 20%bv ltac:(lia) eq_refl),
  R20, (EWr 11%nat 11%bv ltac:(lia) eq_refl), Ha1 in T20.
rewrite (EW1 (ms_regs ms0) 10%nat 10%bv ltac:(lia) eq_refl), Q10, (EW1 (ms_regs ms) 10%nat 10%bv ltac:(lia) eq_refl),
  R10, (EWr 10%nat 10%bv ltac:(lia) eq_refl), Ha0 in T23.
(* the realigned sp: cn_S1 D *)
pose proof (e5_S1 D Hal16) as [HS1mod HS1b].
assert (HSP1 : spZ (ms_regs ms1) = cn_S1 D).
{ unfold spZ. rewrite T2, (e0_and_m32 (spZ (ci_regs D) + -192) ltac:(lia)).
  unfold cn_S1, cn_sp0. rewrite e5_land32.
  pose proof (Z.div_mod (spZ (ci_regs D) - 192) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (spZ (ci_regs D) - 192) 32 ltac:(lia)).
  rewrite unsigned_lit_small by lia. lia. }
(* the capacity rule: the entry has room for one more class-3 frame *)
assert (HCNTF : count_cid CN_CID (frames (ci_S D)) < fs_frames CN_CID).
{ pose proof (e0_count_le CN_CID (frames (ci_S D))) as Hc.
  assert (HFF : fs_frames CN_CID = 2048) by (vm_compute; reflexivity).
  assert (HCAP : ck_FRAMES_CAP - FR_check_no_overread <= 64) by (vm_compute; discriminate). lia. }
destruct HFP as (S2 & Hpath).
destruct (e0_sm_facts CN_CID (ci_S D) (ci_fpos D) S2 ltac:(unfold CN_CID; lia) Hpath) as (Hsetfs & Hfrs2 & Hfresh).
rewrite <- SM3.
eapply SRr_bind.
{ eapply (e0_sm_at (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW
    CN_CID ASM3 ltac:(unfold CN_CID; lia))
  with (o := cn_S1 D - spZ (ci_regs D)) (raw := Z_to_bv 64 (BASE + 920)) (pos := ci_fpos D) (S2 := S2).
  - exact HJ.
  - rewrite HSP1. unfold cn_sp0 in *. lia.
  - unfold cn_sp0 in HS1mod. replace (cn_S1 D - spZ (ci_regs D)) with (cn_S1 D - cn_sp0 D) by reflexivity.
    exact HS1mod.
  - unfold cn_sp0 in HS1b. lia.
  - unfold cn_sp0 in HS1b. unfold ESTACK. rewrite HSTK. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - exact T1.
  - apply (ret_ok_codeptr_v 920); [lia | reflexivity].
  - exact HCNTF.
  - exact Hpath.
  - exact Hsetfs.
  - exact Hfrs2.
  - exact Hfresh. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HPRES & Hres & Eab2 & Hnev2 & Hbb2 & Hz & Hflag
  & Hfpres & HKEPT & HMNK).
assert (HPM2 : P mem2) by exact (PCALL _ _ HMNK HPM).
destruct HKEPT as (KA & KB & KC & KD & KE & KF).
(* every byte the walk needs, back at the entry memory: off the frame window and off the call's window *)
assert (KEEPc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (cn_S1 D - ESTACK <= a < cn_S1 D) ->
  ~ (spZ (ci_regs D) - 192 <= a < spZ (ci_regs D)) ->
  aview SEGS (w_H (ci_W D)) mem2 a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha Hw Hf. rewrite (KA a Ha ltac:(lia)). exact (KEEPa a ltac:(lia) Hf). }
assert (KEEPi : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H (ci_W D)) mem2 a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Hi Ho He. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow.
  rewrite (KC a Hi Ho He). exact (KEEPa a ltac:(unfold kLowMemEnd in Hlow; lia) ltac:(unfold kLowMemEnd in Hlow; lia)). }
assert (KEEPp : forall a, Exists (in_zr a) prh_pst ->
  aview SEGS (w_H (ci_W D)) mem2 a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha. destruct (cni_pst_ok B IMG a Ha) as [Hi Ho]. exact (KEEPi a Hi Ho (cni_pst_errno B IMG a Ha)). }
(* the frame's bounds *)
assert (Hin2 : In (CN_CID, ci_fpos D) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS (ci_ly D) S2 (ci_Hp D) (ci_W D) mem2 md2 CN_CID (ci_fpos D)
  (ajx_ar HJ2) Hin2) as (HF0 & HF1b & _).
assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
(* ---- +116 j +8; +124 mv s11, a0; +128 bnez a0 (taken) ---- *)
replace (BASE + 920) with (BASE + CN_OFF + 116) by (pose proof cn_off_val; lia).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + CN_OFF + 116)) mem2 (seg_rom SEGS)) md2)
  with (@cn_cfg SEGS fx (cn_pc 116) regs2 mem2 md2).
apply (cn_hs_j (ci_W D) fx regs2 mem2 md2 _ 116 124 8); [vm_compute; reflexivity | lia | reflexivity | lia |].
intros X1.
apply (cn_hs_addi (ci_W D) fx regs2 mem2 _ _ 124 128 27%bv 10%bv 0);
  [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X2.
apply (cn_hs_bnez (ci_W D) fx _ mem2 _ _ 128 10%bv 32 160 132 false);
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0, ro_getr_other by reflexivity. rewrite Hres. unfold cn_F in *.
  rewrite ro_c_eq0 by lia. apply Z.eqb_neq. lia. }
intros X3. cbn [negb].
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg ?mm ?mo) _ => set (md3 := mo) end.
(* ---- THE CUT CN_POISON ---- *)
apply SRr_ret. split; [|exact HPM2].
exists fx, (ci_ly D), S2, (ci_Hp D), (regupd regs2 27%bv (v_addi (getr regs2 10%bv) 0)), mem2, md3, 0.
split; [reflexivity|].
(* the registers at the cut *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r)
  by (intros r Hr; exact (e5_pres _ _ r HPRES Hr)).
assert (G2 : getr regs2 2%bv = w64 (cn_S1 D)).
{ rewrite (PR 2%bv ltac:(apply e5_cs; vm_compute; reflexivity)). unfold w64. rewrite <- HSP1.
  unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G8 : getr regs2 8%bv = w64 (cn_sp0 D)).
{ rewrite (PR 8%bv ltac:(apply e5_cs; vm_compute; reflexivity)), T8. unfold w64, cn_sp0, spZ.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (G9 : getr regs2 9%bv = w64 (cn_S1 D)).
{ rewrite (PR 9%bv ltac:(apply e5_cs; vm_compute; reflexivity)), T9, <- T2, e0_add0.
  unfold w64. rewrite <- HSP1. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G18 : getr regs2 18%bv = w64 SHADOW_OFF).
{ rewrite (PR 18%bv ltac:(apply e5_cs; vm_compute; reflexivity)), T18. reflexivity. }
assert (G20 : getr regs2 20%bv = w64 (cn_size D))
  by (rewrite (PR 20%bv ltac:(apply e5_cs; vm_compute; reflexivity)); exact T20).
assert (G23 : getr regs2 23%bv = w64 (ci_data D))
  by (rewrite (PR 23%bv ltac:(apply e5_cs; vm_compute; reflexivity)); exact T23).
assert (G3 : getr regs2 3%bv = getr (ci_regs D) 3%bv)
  by (rewrite (PR 3%bv ltac:(apply e5_cs; vm_compute; reflexivity)); exact T3).
assert (G4 : getr regs2 4%bv = getr (ci_regs D) 4%bv)
  by (rewrite (PR 4%bv ltac:(apply e5_cs; vm_compute; reflexivity)); exact T4).
(* the saved words at the cut *)
assert (SV : forall (off : Z) (n : nat) (r : bv 5), 8 <= off <= 192 ->
  YP09.chunk_ok SEGS EV (mrestrict (w_H (ci_W D)) (ms_mem ms)) (spZ (ci_regs D))
    (YP09.mkChunk (- off) (CVal 8 (SOff n 0))) -> (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  rdword (aview SEGS (w_H (ci_W D)) mem2) (cn_sp0 D - off) = Some (bv_unsigned (getr (ci_regs D) r))).
{ intros off n r Hoff HC Hn Hr.
  assert (Hv2 : val_mem SEGS (mrestrict (w_H (ci_W D)) mem2) (spZ (ci_regs D) - off) 8
    (bv_unsigned (getr (ci_regs D) r))).
  { apply (val_mem_kept SEGS (w_H (ci_W D)) (w_H (ci_W D)) (ms_mem ms) mem2); [|exact (SAV off n r HC Hn Hr)].
    intros q Hq. cbn in Hq. unfold cn_sp0 in HS1b. rewrite HSTK in *.
    rewrite (KA (spZ (ci_regs D) - off + q) ltac:(lia) ltac:(unfold ESTACK; lia)).
    rewrite (KEEP2 (spZ (ci_regs D) - off + q) ltac:(lia)).
    exact (KEEP1 (spZ (ci_regs D) - off + q) ltac:(lia)). }
  apply e_rdword_of_val_mem; [exact Hv2|].
  pose proof (bv_unsigned_in_range 64 (getr (ci_regs D) r)) as Hrg.
  change (bv_modulus 64) with (2 ^ 64) in Hrg. exact Hrg. }
assert (HCAall : forall c, In c [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
  YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
  YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
  YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  YP09.chunk_ok SEGS EV (mrestrict (w_H (ci_W D)) (ms_mem ms)) (spZ (ci_regs D)) c).
{ intros c Hc. apply HCA. cbn [In] in Hc |- *. tauto. }
assert (HSAVED : cn_saved (rc := rc) (PA := PA) D (ci_W D) mem2).
{ unfold cn_saved. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  [ replace (cn_sp0 D - 192 + 184) with (cn_sp0 D - 8) by lia;
    apply (SV 8 1%nat 1%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 176) with (cn_sp0 D - 16) by lia;
    apply (SV 16 8%nat 8%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 168) with (cn_sp0 D - 24) by lia;
    apply (SV 24 9%nat 9%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 160) with (cn_sp0 D - 32) by lia;
    apply (SV 32 18%nat 18%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 152) with (cn_sp0 D - 40) by lia;
    apply (SV 40 19%nat 19%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 144) with (cn_sp0 D - 48) by lia;
    apply (SV 48 20%nat 20%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 136) with (cn_sp0 D - 56) by lia;
    apply (SV 56 21%nat 21%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 128) with (cn_sp0 D - 64) by lia;
    apply (SV 64 22%nat 22%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 120) with (cn_sp0 D - 72) by lia;
    apply (SV 72 23%nat 23%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 112) with (cn_sp0 D - 80) by lia;
    apply (SV 80 24%nat 24%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 104) with (cn_sp0 D - 88) by lia;
    apply (SV 88 25%nat 25%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 96) with (cn_sp0 D - 96) by lia;
    apply (SV 96 26%nat 26%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl)
  | replace (cn_sp0 D - 192 + 88) with (cn_sp0 D - 104) by lia;
    apply (SV 104 27%nat 27%bv ltac:(lia) ltac:(apply HCAall; cbn [In]; tauto) ltac:(lia) eq_refl) ]. }
(* the frame's shadow bytes are present (the call zeroed them) *)
assert (SHP : forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + fs_frame_bytes CN_CID / 8 ->
  apresent (w_H (ci_W D)) mem2 a).
{ intros a Ha. rewrite HFB in Ha.
  assert (HFa : 4096 <= cn_F D /\ cn_F D + 512 <= alloc_ceiling)
    by (unfold cn_F; rewrite HFB in HF1b; lia).
  assert (Hsh : 2147450880 <= shadow_addr (cn_F D) /\ shadow_addr (cn_F D) + 64 < 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (cn_F D) 8 ltac:(lia) ltac:(lia)).
    assert (cn_F D / 8 <= cn_F D) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (Ea : a = shadow_of_addr SHADOW_OFF (frame_addr (ci_ly D) CN_CID (ci_fpos D)) + (a - shadow_addr (cn_F D)))
    by (unfold shadow_of_addr, shadow_addr, cn_F; lia).
  apply (e0_present_of_view SEGS).
  - apply e0_seg_rom_none; [lia|].
    intros Hi. pose proof (@pa_segs_low _ _ PA _ Hi). unfold kLowMemEnd in *. lia.
  - rewrite Ea, (Hz (a - shadow_addr (cn_F D)) ltac:(rewrite HFB; lia)). discriminate. }
(* cn_base at the cut *)
assert (HB0 : cn_base (fx := fx) B ARx D fx (ci_ly D) S2 (ci_Hp D) (ci_W D) regs2 mem2 md2 0 0).
{ split; [exact HFRM|]. split; [intros r Hr; reflexivity|].
  split; [apply cn_J_of_x; exact HJ2|].
  split.
  { unfold cn_frame. split; [exact Hfrs2|]. split; [exact Hfresh|].
    split; [unfold cn_F; exact Hflag|]. split; [unfold cn_F; exact Hfpres | exact SHP]. }
  split; [exact HSAVED|].
  split; [exact G3|]. split; [exact G4|].
  intros a Hro Hno Herr.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(sg & Hs & _ & Hr)|Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]).
  rewrite (KEEPi a Hi Hno Herr). exact (HROD a Hro Hno Herr). }
pose proof (cn_base_mat B ARx LAWS D fx (ci_ly D) S2 (ci_Hp D) (ci_W D) regs2 regs2 mem2 md2 0 0 X1 HB0
  eq_refl eq_refl) as HB1.
pose proof (cn_base_mat B ARx LAWS D fx (ci_ly D) S2 (ci_Hp D) (ci_W D) regs2
  (regupd regs2 27%bv (v_addi (getr regs2 10%bv) 0)) mem2 _ 0 0 X2 HB1
  ltac:(rewrite ro_getr_other by reflexivity; reflexivity)
  ltac:(rewrite ro_getr_other by reflexivity; reflexivity)) as HB2.
pose proof (cn_base_mat B ARx LAWS D fx (ci_ly D) S2 (ci_Hp D) (ci_W D)
  (regupd regs2 27%bv (v_addi (getr regs2 10%bv) 0)) (regupd regs2 27%bv (v_addi (getr regs2 10%bv) 0))
  mem2 _ 0 0 X3 HB2 eq_refl eq_refl) as HBASE.
split; [exact HBASE|].
(* the register snapshot *)
split.
{ unfold cn_regsat. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite ro_getr_other by reflexivity. exact G2.
  - rewrite ro_getr_other by reflexivity. exact G8.
  - rewrite ro_getr_other by reflexivity. exact G9.
  - rewrite ro_getr_other by reflexivity. unfold cn_F. exact Hres.
  - rewrite ro_getr_other by reflexivity. exact G18.
  - rewrite ro_getr_other by reflexivity. exact G20.
  - rewrite ro_getr_other by reflexivity. exact G23.
  - rewrite ro_getr_same by reflexivity. unfold v_addi. rewrite Hres. unfold w64, cn_F.
    rewrite unsigned_lit_small by lia. f_equal. lia. }
(* cn_early at the cut *)
pose proof (cni_own B IMG) as HOWNA.
destruct Hsetfs as (ff & ES2).
(* the cut's LAST conjunct (the hull stages, poison at cn_hev_all): the fake frame changes only the frames
   (S2 = set_fs ff (ci_S D)), so the meters are the entry's and its budget carries over *)
split.
2:{ eapply PresetHullBudget.hull_budget_same; [|exact (cn_pre_hull B ARx CTX0 D HPRE)].
    rewrite ES2. split; reflexivity. }
unfold cn_early. split; [reflexivity|].
assert (HLED2 : prh_ledger B (ci_ly D) S2 (ci_Hp D) (ci_W D) mem2 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ
  (ci_ran D) (ci_most D) 0).
{ apply (prh_ledger_kept_aview B (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_ly D) S2 (ci_Hp D)
    (ci_W D) mem2 _ _ _ _ _ _ _ HLED).
  - intros a Ha. exact (KEEPp a Ha).
  - intros a k i Hin Hi.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hin) as (Hk0 & Hab & _).
    pose proof cf_head_nonneg as Hcf. unfold prh_head_wide in HW.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hce & _).
    assert (Hreq : 8 <= req_size (k + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    rewrite (KB (a - cf_head) (k + cf_head) i Hab ltac:(lia) ltac:(intros [])).
    apply KEEPa; [pose proof alloc_ceiling_val as [AC _]; lia | rewrite HSTK in *; lia].
  - intros a k _ Hab. rewrite Eab2. exact Hab.
  - apply Permutation_refl. }
split; [exact HLED2|].
split; [apply Forall_nil|].
split; [cbn [flat_map app]; rewrite Eab2; apply Permutation_refl|].
split; [rewrite ES2; apply RL_set_fs; exact HROOM|].
split.
{ (* cn_prog over no copy: the room is the entry's (set_fs keeps it) and a position of the entry state is one of S2 *)
  unfold cn_prog, cn_cevsl. cbn [flat_map map length]. rewrite ES2. split.
  - cbn [PresetReqAt.hlive_from]. apply Permutation_refl.
  - intros sm x0 os i H0 hist Hpos _. rewrite Nat.add_0_r. exists hist.
    apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
split; [rewrite Hbb2; unfold LIVE_check_no_overread, cn_size in *; cbn [length]; lia|].
split; [left; reflexivity|].
split; [|split; [intros _; apply Forall_nil | intros Hne; exfalso; exact (Hne eq_refl)]].
pose proof HLED2 as HLo. apply PRH_Base.prh_ledger_own in HLo. destruct HLo as [Hov _].
rewrite HOWNA. change pi_gz_own_ran_out with 1%nat in Hov. exact Hov.
Qed.

End e0.
