(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 448 of its 496 lines of code are new or changed and 730 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Rtt102CmpS12A.v; 32 of its 497 lines of code are new or changed and 31 lines of the source are left out. *)
(* B' TWIN (asan-ubsan d663f82d7f488d30, unstripped twin c90d4fa54d43160b) of lib/A/Prog/Rtt102CmpS12A.v, by a name map:
   round_trip_text's body on image B is image A's instruction sequence with only pc-relative immediates changed
   (capstone over both twins' symtab bodies; every call site at the same offset), so the twin is the A' file with
   image A's listing / image / PrhImg / CfImg names replaced by image B's (A_prog_* -> B_prog_*, PI_prog_A /
   PL_prog_A -> _B, prh_img_A -> prh_img_B, CfImg_A -> CfImg_B, S1ImgA -> S1ImgB, IMG_LO / IMG_TOP -> IMG_LO_B /
   IMG_TOP_B, the A' stretch modules Rtt102*A -> Rtt102*B, the file's own *_A names -> *_B) and image B's own value
   for each image numeral the file states (a load offset, the function's listing offset, a witness address); every
   closed image check is re-run at B' by the build. The comments below are the A' file's: their addresses and slot
   numbers are image A's. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the FIRST inner segment
   S12 of STRETCH CMP of round_trip_text's walk ON THE #102 PINS (lane CmpS12 of RttCmp, WalkRtt102, the text owner):
   RT_CMP (+740) -> strcmp -> +756 -> strlen -> +772 (Rtt102CmpDefs.v cmp_at_len).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma); the function-level lookup
   (proof-index EXIT=0, no released ASan proof) is the brief's.
   THE CODE (A' +0x2e4 .. +0x2f0, A' capstone listing :187-194):
     +740 beqz s6, abort          REFUTED: s6 = q, the writer's text, q <> 0 (the cut; > 0 from the ledger block)
     +744 mv a0, s6 ; +748 mv a1, s5 ; +752 jal __wrap_strcmp      strcmp (q, want): YGcallMxmn.aj_strcmp_at_xromR
     +756 bnez a0, abort          REFUTED: both strings are ri_tb D ++ [0] (the cut's two bytes_at), so a0 = 0
     +760 addi s7, s10, 0x20 ; +764 mv a0, s6 ; +768 jal __wrap_strlen   strlen (q): YGcallMxmn.aj_strlen_at_xromR
     +772 = cmp_at_len (a0 = |ri_tb D|, s7 = back = F + 32)
   A register-only stretch: the concrete steps of lane RttFR1's Rtt102FR1KitB.v (fr_addi / fr_jal, and fr_beqz_ft /
   fr_bnez_ft through s12_beqz_ft / s12_bnez_ft below, which name the tested register), the journal re-established
   after each step by ajournal_x_materializeR. THE R FORM (Step-2 tip): every statement is at the step relation
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf and the cut's journal rtt_J at RZW := YA0nH.wle' SEGS RZ_cf; the two string
   rules are the _xromR forms at RZW (the call keeps the world, so no law of RZW beyond refl / trans is read), their
   plain SRr conclusion lifted by YA0nH.SRr_SRr'. The two string calls write only their stack window
   [sp1 - 2 * ESTACK, sp1) (sp1 = RT_R sp0, the realigned sp), which lies above YM05.alloc_ceiling (sp0 >= ceiling +
   STK), while every byte the cut reads below sp0 - 104 lies below it (blocks, frames, their shadow, the image):
   rtt_at_cmp is carried across each call by s12_keep (Rtt102FR1Kit.v rtt_carry_keep at E := False, P := []).
   The string rules' premises on q and want come from Rtt102CmpLib.v rcl_hblk_str / rcl_rawblk_str / rcl_first_byte /
   rcl_src_ok; the length bound from rtt_pre's PjWriteHyp.wlen t p + 1 <= 2 ^ 28.
   No premise is withheld: cmp_s12 is unconditional under the Section hypotheses.
   Numerals: 740 / 756 / 772 (DERIVED: Rtt102Cut RT_CMP, Rtt102CmpDefs RT_C1 / RT_C2, byte offsets inside
   round_trip_text, equal on A' and B'), 4 (LENGTH: instruction); 10 / 11 / 21 / 22 / 23 / 26 / 27 / 1 / 2 / 3 / 4 /
   0 (WORD: register numbers); 32 (LENGTH: back at F + 32, the immediate of `addi s7, s10, 0x20`); 104 / 160 / 192 /
   16 / 8384 (LENGTH: the 13 saves, the frame, the realignment bound, the stack alignment, 2 * ESTACK + 192);
   8 (LENGTH: shadow granule); 2 ^ 32 / 2 ^ 40 / 2 ^ 63 / 2 ^ 64 (LENGTH). No ADDRESS literal: every pc is
   pa_sigma / pa_val of the listing. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf YGcallMx YGcallMxmn YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102FR1Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Rtt102FR1KitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102CmpLib Rtt102CmpDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the realigned sp RT_R sp0 (`addi sp, sp, -0xa0; andi sp, sp, -0x20`) of a 16-aligned entry sp: within 192 bytes
   below sp0, at least 160 below, and a 16-multiple away *)
Lemma s12_sp1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 192 <= RT_R sp0 <= sp0 - 160 /\ (RT_R sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H. unfold RT_R, RT_FRAME.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd2. rewrite H in Hd2.
set (r := (sp0 - 160) mod 32) in *. set (d := (sp0 - 160) / 32) in *. set (e := sp0 / 16) in *.
split; [lia|].
apply Z.mod_divide; [lia|]. exists (2 * d - e). lia.
Qed.

(* round_trip_text's stack budget covers the realignment and a string callee's 2 * ESTACK window (A': 27392) *)
Lemma s12_stk : 8384 <= @STK_round_trip_text prh_img_B.
Proof. vm_compute. discriminate. Qed.

(* ---- the branch steps with the tested register named (fr_beqz_ft / fr_bnez_ft, the decoded register equal to
   it by value): a not-taken branch whose register a cut's fact reads ---- *)
Section stp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).

Lemma s12_beqz_ft : forall (W : world SEGS) regs mem md Q w k (rs r0 rs0 : bv 5) (imm : bv 13),
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs r0 imm, 4%Z) -> r0 = 0%bv -> rs = rs0 ->
  0 <= k -> k + 4 < 2 ^ 40 ->
  c_eq (getr regs rs0) (getr regs 0%bv) = false ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rs r0 rs0 imm Hpl Hdec Hr0 Hrs Hk0 Hk4 Hc HK. subst rs0.
exact (fr_beqz_ft (fx := fx) W regs mem md Q w k rs r0 imm Hpl Hdec Hr0 Hk0 Hk4 Hc HK).
Qed.

Lemma s12_bnez_ft : forall (W : world SEGS) regs mem md Q w k (rs r0 rs0 : bv 5) (imm : bv 13),
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs r0 imm, 4%Z) -> r0 = 0%bv -> rs = rs0 ->
  0 <= k -> k + 4 < 2 ^ 40 ->
  c_eq (getr regs rs0) (getr regs 0%bv) = true ->
  (forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
            (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rs r0 rs0 imm Hpl Hdec Hr0 Hrs Hk0 Hk4 Hc HK. subst rs0.
exact (fr_bnez_ft (fx := fx) W regs mem md Q w k rs r0 imm Hpl Hdec Hr0 Hk0 Hk4 Hc HK).
Qed.
End stp.

(* ======================================================================================================== *)
Section s12. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKR := (@STK_round_trip_text prh_img_B).
(* the listing offset of round_trip_text's entry (DERIVED: 4 * its slot), as Rtt102CmpB.v spells it *)
#[local] Notation RTT_K := (4 * Z.of_nat (B_prog_slot AS_round_trip_text)).
#[local] Existing Instance prh_img_B.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* the cut's predicates at the contract's float state fx, BY NAME (the text owner's statement-trap rule: fxc is a
   second FPState in scope) *)
#[local] Notation PRE := (rtt_pre (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx CTX0).
#[local] Notation RJ := (rtt_J (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RCARRY := (rtt_carry (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_CMP := (rtt_at_cmp (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_LEN := (cmp_at_len (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
#[local] Notation POST := (rtt_post (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
(* the walk's world relation (Rtt102Cut.v rtt_J's RZW): the re-hiding move's wle' at the cf shadow zone *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* ---- Section hypotheses (the brief's category (a); each with its owner) ---- *)
(* (a) the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x; S10TxString.v:163) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* (a) PRH_Base.v prh_head_wide (ONE spelling a walk takes; owner: the cf instance owner's preset_head_wide, cf_head = 16):
   Rtt102CmpLib.v rcl_hblk_str / rcl_rawblk_str take it *)
Hypothesis HW : prh_head_wide.
(* (a) the strcmp / strlen wrappers' texts in the read-only-premise form with the memnorm keep (YGcallMxmn.v
   section 8, the rule table's _xrom rows; owned by the stdio-unit owner), at every float state: the calls are made at the
   cut's fxc *)
Hypothesis STRCMP : forall fx' : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fx' SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
Hypothesis STRLEN : forall fx' : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fx' SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).

(* ---- what a string rule asks of a NUL-terminated text p of length n at a state ---- *)
Definition s12_strok (W : world SEGS) (mem : word -> option byte) (p n : Z) : Prop :=
  0 < p /\ p + n + 1 <= 2 ^ 63 /\ p + n < YM05.alloc_ceiling /\ YGcfStr.amem_range8 p (n + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p (n + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) p (n + 1) /\
  (forall a, p + n < a < p + n - (p + n) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None) /\
  first_byte SEGS W mem p (n + 1) 0 n.

(* the cut gives it of both texts, q (a live harness block of the ledger) and want (a live raw block) *)
Lemma s12_str : forall D fxc ly S Hp W regs mem md k pos, PRE D -> AT_CMP D fxc ly S Hp W regs mem md k pos ->
  exists q want, getr regs 22 = w64 q /\ getr regs 21 = w64 want /\
    Z.of_nat (length (ri_tb D)) + 1 < 2 ^ 32 /\
    s12_strok W mem q (Z.of_nat (length (ri_tb D))) /\ s12_strok W mem want (Z.of_nat (length (ri_tb D))) /\
    bytes_at W mem q (ri_tb D ++ [0]) /\ bytes_at W mem want (ri_tb D ++ [0]).
Proof.
intros D fxc ly S Hp W regs mem md k pos HP HC.
destruct HC as (HCA & _ & _ & _ & q & capw & peakw & want & cap & R22 & R21 & _ & _ & HLED &
  _ & HLEN & _ & HBQ & HBW & HWB & HLT & HAMR & _).
pose proof HCA as (_ & HJ & _ & _ & _ & _ & _ & _ & HNODE & _).
pose proof HJ as (HAR & _).
pose proof HWB as (_ & Hwin & _ & Hwhp & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWL & _).
assert (Hn0 : 0 <= Z.of_nat (length (ri_tb D))) by lia.
assert (H28 : Z.of_nat (length (ri_tb D)) + 1 <= 2 ^ 28) by (unfold ri_tb; unfold PjWriteHyp.wlen in HWL; exact HWL).
pose proof (rcl_wdoc_nz _ _ _ _ _ _ (ri_p D) HNODE) as Hnz.
destruct (rcl_hblk_str B ARx LAWS HW ly S Hp W mem md _ _ _ _ _ _ _ q capw _ HAR (proj1 HLED) (in_eq _ _) Hn0 HLEN)
  as (Hq0 & Hq63 & Hqc & Hqm & Hqr & Hqh & Hqt).
destruct (rcl_rawblk_str B ARx LAWS HW ly S Hp W mem md _ _ _ _ _ _ _ want cap _ HAR (proj1 HLED) Hwin Hwhp Hn0 HLT)
  as (Hw0 & Hw63 & Hwc & Hwr & Hwh & Hwt).
exists q, want. split; [exact R22|]. split; [exact R21|]. split; [lia|].
split; [exact (conj Hq0 (conj Hq63 (conj Hqc (conj Hqm (conj Hqr (conj Hqh (conj Hqt
  (rcl_first_byte W mem q (ri_tb D) HBQ Hnz)))))))) |].
split; [exact (conj Hw0 (conj Hw63 (conj Hwc (conj HAMR (conj Hwr (conj Hwh (conj Hwt
  (rcl_first_byte W mem want (ri_tb D) HBW Hnz)))))))) |].
split; [exact HBQ | exact HBW].
Qed.

(* a byte list survives a memory change that keeps its bytes *)
Lemma s12_bytes_keep : forall (W : world SEGS) mem mem2 p l, bytes_at W mem p l ->
  (forall x, p <= x < p + Z.of_nat (length l) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x) ->
  bytes_at W mem2 p l.
Proof.
intros W mem mem2 p l H E. unfold bytes_at in *. apply (garr8R_frame SEGS _ _ p l H).
intros x Hx. apply (mbyte_of_aview SEGS). exact (E x Hx).
Qed.

(* a write confined to [lo, hi) above the ceiling keeps everything rtt_kept asks (E := False, P := []): blocks,
   image and frames (with their shadow) lie below the ceiling *)
Lemma s12_kept_win : forall ly S Hp W mem md mem2 lo hi,
  ARx ly S Hp W mem md -> YM05.alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) ->
  rtt_kept B ly S W mem ly S W mem2 lo hi (fun _ => False) [].
Proof.
intros ly S Hp W mem md mem2 lo hi HAR Hlo Hfr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KB : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply Hfr; lia).
split; [intros a Ha Hn; apply Hfr; [lia | exact Hn]|].
split.
{ intros b m i Hb _ Hi _.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hb) as (_ & H4096 & Hc & _).
  apply KB. lia. }
split.
{ intros a Ha _ _ _. pose proof (@pa_segs_low _ B_prog_listing PA a Ha) as Hl. apply KB. lia. }
intros cid pos' a Hf Ha _.
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hf) as (Hf4 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
apply KB.
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- lia.
- unfold shadow_addr, SHADOW_OFF in Ha.
  pose proof (Z.mul_div_le (frame_addr ly cid pos') 8 ltac:(lia)) as M1.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as M2.
  pose proof (Z.div_pos (frame_addr ly cid pos') 8 ltac:(lia) ltac:(lia)) as M3.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as M4.
  set (u := frame_addr ly cid pos' / 8) in *. set (v := fs_frame_bytes cid / 8) in *. lia.
Qed.

(* ---- THE CUT ACROSS A STRING CALL: the call's journal at the new memory, its stack window above the ceiling and
   below sp0 - 104, its memnorm keep, and the registers the cut reads kept ---- *)
Lemma s12_keep : forall D fxc ly S Hp W regs mem md k pos regs2 mem2 md2 lo hi,
  PRE D -> AT_CMP D fxc ly S Hp W regs mem md k pos ->
  RJ D ly S Hp W mem2 md2 k pos ->
  YM05.alloc_ceiling <= lo -> hi <= ri_sp D - 104 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  rtt_cregs B D ly regs2 pos ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 27 = getr regs 27 ->
  AT_CMP D fxc ly S Hp W regs2 mem2 md2 k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos regs2 mem2 md2 lo hi HP HC HJ2 Hlo Hhi Hfr HMN2 HCR2 E21 E22 E27.
destruct HC as (HCA & HBK & HS11 & HCK & q & capw & peakw & want & cap & R22 & R21 & Hq0 & Hw0 & HLED &
  HNEW & HLEN & HLIVE & HBQ & HBW & HWB & HLT & HAMR & ECAP & ECAPW & HPERM & HBB & HPOS).
pose proof HCA as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HNODE & HTV & _).
pose proof HJ as (HAR & _).
pose proof HWB as (_ & Hwin & _ & Hwhp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KB : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply Hfr; lia).
pose proof (s12_kept_win ly S Hp W mem md mem2 lo hi HAR Hlo Hfr) as HKW.
assert (Hpst : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KB. pose proof (@pa_segs_low _ B_prog_listing PA a (pst_in_img_B a Ha)) as Hl. lia. }
assert (Hinc : incl (ri_Lam D) ((q, capw) :: ri_Lam D)) by (intros bk Hbk; right; exact Hbk).
pose proof (proj1 HLED) as HL1.
assert (HL2 : prh_ledger B ly S Hp W mem2 ((q, capw) :: ri_Lam D) peakw
  (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D)) SIZE_MAXZ (ri_ran D) (ri_most D) 0).
{ apply (prh_ledger_kept_aview (PI := prh_img_B) B ly S Hp W mem); [exact HL1 | exact Hpst | | | apply Permutation_refl].
  - intros a0 k0 i Hin Hi. apply KB.
    destruct (prh_ledger_hblock (PI := prh_img_B) B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HL1 Hin) as (Hk0 & Hbk & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbk) as (_ & H4096 & Hc & _).
    pose proof HW as Hw. unfold prh_head_wide in Hw.
    assert (Hrq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
    lia.
  - intros a0 k0 _ Hb. exact Hb. }
assert (Hn0 : 0 <= Z.of_nat (length (ri_tb D))) by lia.
destruct (rcl_hblk_str B ARx LAWS HW ly S Hp W mem md _ _ _ _ _ _ _ q capw _ HAR HL1 (in_eq _ _) Hn0 HLEN)
  as (Hq1 & _ & Hqc & _).
destruct (rcl_rawblk_str B ARx LAWS HW ly S Hp W mem md _ _ _ _ _ _ _ want cap _ HAR HL1 Hwin Hwhp Hn0 HLT)
  as (Hw1 & _ & Hwc & _).
assert (HBQ2 : bytes_at W mem2 q (ri_tb D ++ [0])).
{ apply (s12_bytes_keep W mem mem2 q _ HBQ). intros x Hx. apply KB. rewrite length_app in Hx. cbn [length] in Hx. lia. }
assert (HBW2 : bytes_at W mem2 want (ri_tb D ++ [0])).
{ apply (s12_bytes_keep W mem mem2 want _ HBW). intros x Hx. apply KB. rewrite length_app in Hx. cbn [length] in Hx.
  lia. }
(* back's shadow lies below the ceiling *)
assert (HBK2 : rtt_back ly W mem2 pos).
{ pose proof HFR as (Efr & _).
  assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
  destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md RT_CID pos HAR Hin) as (Hf4 & Hfc & _).
  assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
  unfold rtt_back in *.
  apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2)); [|exact HBK].
  intros x Hx. unfold RT_BACK in Hx. apply KB. unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.mul_div_le x 8 ltac:(lia)) as M1. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as M2.
  set (u := x / 8) in *. lia. }
assert (HC2 : RCARRY D fxc ly S Hp W regs2 mem2 md2 k pos).
{ refine (rtt_carry_keep B ARx SK CTX0 LAWS pst_not_ro_B rtt_stkr_B D fxc ly S Hp W regs mem md k pos
    ly S Hp W regs2 mem2 md2 k lo hi (fun _ => False) [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HCA HJ2 eq_refl HKW Hhi _
    (fun x Hx => False_ind _ Hx) HL1 Hinc HL2 Hinc HCR2 HMN2 HROOM).
  intros a Ha. inversion Ha. }
split; [exact HC2|]. split; [exact HBK2|].
split; [unfold rtt_s11 in *; rewrite E27; exact HS11|].
split; [exact (rtt_copy_keep B ARx SK CTX0 D fxc ly S Hp W regs mem md k pos ly S W mem2 lo hi (fun _ => False) []
  HP HCA HKW (fun x Hx => False_ind _ Hx) HCK)|].
exists q, capw, peakw, want, cap. cbv zeta.
split; [rewrite E22; exact R22|]. split; [rewrite E21; exact R21|]. split; [exact Hq0|]. split; [exact Hw0|].
split; [split; [exact HL2 | exact (proj2 HLED)]|].
split; [exact HNEW|]. split; [exact HLEN|]. split; [exact HLIVE|].
split; [exact HBQ2|]. split; [exact HBW2|]. split; [exact HWB|]. split; [exact HLT|]. split; [exact HAMR|].
split; [exact ECAP|]. split; [exact ECAPW|]. split; [exact HPERM|]. split; [exact HBB|]. exact HPOS.
Qed.

(* ======================================================================================================== *)
(* ---- S12, FIRST HALF: RT_CMP (+740) -> strcmp (q, want) -> +756 with a0 = 0 ---- *)
Lemma s12_cmp : forall D, PRE D ->
  forall fxc ly S Hp W regs mem md k pos,
  AT_CMP D fxc ly S Hp W regs mem md k pos ->
  (forall regs2 mem2 md2, getr regs2 22 = getr regs 22 ->
     AT_CMP D fxc ly S Hp W regs2 mem2 md2 k pos -> getr regs2 10 = w64 0 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
       (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_K + RT_C1))) mem2 (YK11.seg_rom SEGS)) md2) (POST D)) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_K + RT_CMP))) mem (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D HP fxc ly S Hp W regs mem md k pos HC HCONT.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & _).
pose proof HC as (HCA & _).
pose proof HCA as (_ & HJ & HFR & _ & HCR & _ & HROD & _).
pose proof HJ as (HAR & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof s12_stk as HSTK.
destruct (s12_sp1 (ri_sp D) Hsp16) as (Hsp1 & Ho16).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hn0 : 0 <= Z.of_nat (length (ri_tb D))) by lia.
destruct (s12_str D fxc ly S Hp W regs mem md k pos HP HC) as (q & want & R22 & R21 & H32 &
  (Hq0 & Hq63 & Hqc & Hqm & Hqr & Hqh & Hqt & Hqf) & (Hw0 & Hw63 & Hwc & Hwm & Hwr & Hwh & Hwt & Hwf) & HBQ & HBW).
(* the window facts the string rules ask: the callee's stack window [sp1 - 2 * ESTACK, sp1) misses both texts *)
assert (Hbud : 2 * ESTACK - (RT_R (ri_sp D) - ri_sp D) <= STKR) by lia.
assert (Ho0 : RT_R (ri_sp D) - ri_sp D <= 0) by lia.
assert (Hwq : forall a, q <= a <= q + Z.of_nat (length (ri_tb D)) ->
  ~ (ri_sp D + (RT_R (ri_sp D) - ri_sp D) - 2 * ESTACK <= a < ri_sp D + (RT_R (ri_sp D) - ri_sp D))).
{ intros a Ha. lia. }
assert (Hww : forall a, want <= a <= want + Z.of_nat (length (ri_tb D)) ->
  ~ (ri_sp D + (RT_R (ri_sp D) - ri_sp D) - 2 * ESTACK <= a < ri_sp D + (RT_R (ri_sp D) - ri_sp D))).
{ intros a Ha. lia. }
(* +740 beqz s6, abort: not taken (q <> 0) *)
eapply (s12_beqz_ft (fx := fxc) W regs mem md _ _ (RTT_K + RT_CMP) _ _ 22%bv);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; discriminate | vm_compute; reflexivity | |].
{ unfold c_eq. rewrite R22, getr_zero. unfold w64. apply bv_eqb_neq. intros E.
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_small in E by lia. lia. }
intros mat1.
(* +744 mv a0, s6 *)
eapply (fr_addi (fx := fxc) W regs mem _ _ _ (RTT_K + RT_CMP + 4) _ _ _ 10%bv 22%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; discriminate | vm_compute; reflexivity |].
intros mat2.
(* +748 mv a1, s5 *)
eapply (fr_addi (fx := fxc) W _ mem _ _ _ (RTT_K + RT_CMP + 4 + 4) _ _ _ 11%bv 21%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; discriminate | vm_compute; reflexivity |].
intros mat3.
(* +752 jal __wrap_strcmp *)
eapply (fr_jal (fx := fxc) W _ mem _ _ _ (RTT_K + RT_CMP + 4 + 4 + 4) (SIGMA AS___wrap_strcmp));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | vm_compute; discriminate | vm_compute; reflexivity | vm_compute; reflexivity |].
intros mat4.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (YK11.mkst ?rT _ _ _) ?dT) _ =>
  set (regsT := rT); set (mdT := dT) end.
assert (HJm : RJ D ly S Hp W mem mdT k pos).
{ unfold mdT. do 4 apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ. }
(* the call's registers *)
assert (FK : forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 11%bv -> getr regsT r = getr regs r).
{ intros r H1 H10 H11. unfold regsT. rewrite getr_other by exact H1. rewrite getr_other by exact H11.
  rewrite getr_other by exact H10. reflexivity. }
assert (T10 : getr regsT 10 = w64 q).
{ unfold regsT. rewrite getr_other by reg_neq_tac. rewrite getr_other by reg_neq_tac.
  rewrite getr_same by reg_neq_tac. rewrite R22. unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
assert (T11 : getr regsT 11 = w64 want).
{ unfold regsT. rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
  rewrite getr_other by reg_neq_tac. rewrite R21. unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
assert (T2 : spZ regsT = ri_sp D + (RT_R (ri_sp D) - ri_sp D)).
{ unfold spZ. rewrite FK by reg_neq_tac. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (T3 : getr regsT 3 = w64 (as_gp B)) by (rewrite FK by reg_neq_tac; exact R3).
assert (T4 : getr regsT 4 = w64 (as_tp B)) by (rewrite FK by reg_neq_tac; exact R4).
assert (T1 : getr regsT 1 = Z_to_bv 64 (BASE + (RTT_K + RT_C1))).
{ unfold regsT. rewrite getr_same by reg_neq_tac.
  replace (RTT_K + RT_CMP + 4 + 4 + 4 + 4) with (RTT_K + RT_C1) by (unfold RT_CMP, RT_C1; lia). reflexivity. }
assert (HRA : YK0s.ret_ok (Z_to_bv 64 (BASE + (RTT_K + RT_C1)))).
{ apply (ret_ok_codeptr_v (PI := PA)); vm_compute; [split; [discriminate | reflexivity] | reflexivity]. }
assert (Hsq : src_ok SEGS W regsT mem q (Z.of_nat (length (ri_tb D)) + 1)).
{ replace (Z.of_nat (length (ri_tb D)) + 1) with (Z.of_nat (length (ri_tb D ++ [0])))
    by (rewrite length_app; cbn [length]; lia).
  apply (rcl_src_ok W regsT mem q _ HBQ). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite T2. lia. }
assert (Hsw : src_ok SEGS W regsT mem want (Z.of_nat (length (ri_tb D)) + 1)).
{ replace (Z.of_nat (length (ri_tb D)) + 1) with (Z.of_nat (length (ri_tb D ++ [0])))
    by (rewrite length_app; cbn [length]; lia).
  apply (rcl_src_ok W regsT mem want _ HBW). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite T2.
  lia. }
(* strcmp (q, want) *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  Time exact (YGcallMxmn.aj_strcmp_at_xromR (fx := fxc) (SK := SK) SEGS B PST ARx RLO RHI LAWS Hsegs
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___wrap_strcmp) (STRCMP fxc) W regsT mem STKR (ri_sp D) (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D))
    (ri_Hp D) (ri_W D)
    (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp mdT k q want (Z.of_nat (length (ri_tb D)))
    (Z.of_nat (length (ri_tb D))) (RT_R (ri_sp D) - ri_sp D) (Z_to_bv 64 (BASE + (RTT_K + RT_C1)))
    HJm T10 T11 Hq0 Hw0 Hn0 H32 Hq63 Hn0 H32 Hw63 T2 Ho16 Ho0 Hbud T3 T4 T1 HRA Hqf Hwf Hsq Hsw
    Hwq Hww Hqm Hwm Hqr Hqh Hwr Hwh Hqt Hwt HROD). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & _ & HMN2).
(* the two strings are equal: a0 = 0 *)
assert (Hv0 : v = w64 0).
{ apply Hcmp. split; [reflexivity|]. intros i Hi.
  replace (q + i) with (q + Z.of_nat (Z.to_nat i)) by lia.
  replace (want + i) with (want + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (rcl_garr8_aview W mem q _ (Z.to_nat i) HBQ) by (rewrite length_app; cbn [length]; lia).
  rewrite (rcl_garr8_aview W mem want _ (Z.to_nat i) HBW) by (rewrite length_app; cbn [length]; lia).
  reflexivity. }
assert (HCR2 : rtt_cregs B D ly regs2 pos).
{ assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> r <> 1%bv -> r <> 10%bv -> r <> 11%bv ->
    getr regs2 r = getr regs r).
  { intros r Hr H1 H10 H11. rewrite (ts_ap _ _ r HP2 Hr). exact (FK r H1 H10 H11). }
  unfold rtt_cregs. rewrite !KP by (first [ts_cs | reg_neq_tac]). repeat split; assumption. }
apply HCONT.
- rewrite (ts_ap _ _ 22%bv HP2) by ts_cs. apply FK; reg_neq_tac.
- Time apply (s12_keep D fxc ly S Hp W regs mem md k pos regs2 mem2 md2
    (ri_sp D + (RT_R (ri_sp D) - ri_sp D) - 2 * ESTACK) (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) HP HC HJ2);
    [lia | lia | exact Hfr | exact HMN2 | exact HCR2 | | | ].
  + rewrite (ts_ap _ _ 21%bv HP2) by ts_cs. apply FK; reg_neq_tac.
  + rewrite (ts_ap _ _ 22%bv HP2) by ts_cs. apply FK; reg_neq_tac.
  + rewrite (ts_ap _ _ 27%bv HP2) by ts_cs. apply FK; reg_neq_tac.
- rewrite Hv. exact Hv0.
Time Qed.

(* ---- S12, SECOND HALF: +756 (a0 = 0) -> strlen (q) -> +772 cmp_at_len ---- *)
Lemma s12_len : forall D, PRE D ->
  forall fxc ly S Hp W regs mem md k pos,
  AT_CMP D fxc ly S Hp W regs mem md k pos -> getr regs 10 = w64 0 ->
  (forall regs2 mem2 md2, getr regs2 22 = getr regs 22 -> AT_LEN D fxc ly S Hp W regs2 mem2 md2 k pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
       (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_K + RT_C2))) mem2 (YK11.seg_rom SEGS)) md2) (POST D)) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_K + RT_C1))) mem (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D HP fxc ly S Hp W regs mem md k pos HC R10 HCONT.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & _).
pose proof HC as (HCA & _).
pose proof HCA as (_ & HJ & HFR & _ & HCR & _ & HROD & _).
pose proof HJ as (HAR & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof s12_stk as HSTK.
destruct (s12_sp1 (ri_sp D) Hsp16) as (Hsp1 & Ho16).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hn0 : 0 <= Z.of_nat (length (ri_tb D))) by lia.
destruct (s12_str D fxc ly S Hp W regs mem md k pos HP HC) as (q & want & R22 & _ & H32 &
  (Hq0 & Hq63 & Hqc & Hqm & Hqr & Hqh & Hqt & Hqf) & _ & HBQ & _).
(* the fake frame F = s10 = s2: back = F + 32 *)
assert (HinF : In (RT_CID, pos) (frames S)) by (pose proof HFR as (Efr & _); rewrite Efr; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md RT_CID pos HAR HinF) as (HF4 & HFc & _).
pose proof (fs_frame_bytes_nonneg RT_CID) as HFb.
assert (Hbud : 2 * ESTACK - (RT_R (ri_sp D) - ri_sp D) <= STKR) by lia.
assert (Ho0 : RT_R (ri_sp D) - ri_sp D <= 0) by lia.
assert (Hwq : forall a, q <= a <= q + Z.of_nat (length (ri_tb D)) ->
  ~ (ri_sp D + (RT_R (ri_sp D) - ri_sp D) - 2 * ESTACK <= a < ri_sp D + (RT_R (ri_sp D) - ri_sp D))).
{ intros a Ha. lia. }
(* +756 bnez a0, abort: not taken (a0 = 0) *)
eapply (s12_bnez_ft (fx := fxc) W regs mem md _ _ (RTT_K + RT_C1) _ _ 10%bv);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; discriminate | vm_compute; reflexivity
  | rewrite R10, getr_zero; vm_compute; reflexivity |].
intros mat5.
(* +760 addi s7, s10, 0x20 *)
eapply (fr_addi (fx := fxc) W regs mem _ _ _ (RTT_K + RT_C1 + 4) _ _ _ 23%bv 26%bv 32);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; discriminate | vm_compute; reflexivity |].
intros mat6.
(* +764 mv a0, s6 *)
eapply (fr_addi (fx := fxc) W _ mem _ _ _ (RTT_K + RT_C1 + 4 + 4) _ _ _ 10%bv 22%bv 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; discriminate | vm_compute; reflexivity |].
intros mat7.
(* +768 jal __wrap_strlen *)
eapply (fr_jal (fx := fxc) W _ mem _ _ _ (RTT_K + RT_C1 + 4 + 4 + 4) (SIGMA AS___wrap_strlen));
  [vm_compute; reflexivity | vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity
  | vm_compute; discriminate | vm_compute; reflexivity | vm_compute; reflexivity |].
intros mat8.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (YK11.mkst ?rT _ _ _) ?dT) _ =>
  set (regsU := rT); set (mdU := dT) end.
assert (HJm2 : RJ D ly S Hp W mem mdU k pos).
{ unfold mdU. do 4 apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ. }
assert (FK2 : forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 23%bv -> getr regsU r = getr regs r).
{ intros r H1 H10 H23. unfold regsU. rewrite getr_other by exact H1. rewrite getr_other by exact H10.
  rewrite getr_other by exact H23. reflexivity. }
assert (U10 : getr regsU 10 = w64 q).
{ unfold regsU. rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
  rewrite getr_other by reg_neq_tac. rewrite R22. unfold v_addi, w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
assert (U23 : getr regsU 23 = w64 (frame_addr ly RT_CID pos + RT_BACK)).
{ unfold regsU. rewrite getr_other by reg_neq_tac. rewrite getr_other by reg_neq_tac.
  rewrite getr_same by reg_neq_tac. rewrite R26. unfold v_addi, w64, RT_BACK.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (U2 : spZ regsU = ri_sp D + (RT_R (ri_sp D) - ri_sp D)).
{ unfold spZ. rewrite FK2 by reg_neq_tac. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (U3 : getr regsU 3 = w64 (as_gp B)) by (rewrite FK2 by reg_neq_tac; exact R3).
assert (U4 : getr regsU 4 = w64 (as_tp B)) by (rewrite FK2 by reg_neq_tac; exact R4).
assert (U1 : getr regsU 1 = Z_to_bv 64 (BASE + (RTT_K + RT_C2))).
{ unfold regsU. rewrite getr_same by reg_neq_tac.
  replace (RTT_K + RT_C1 + 4 + 4 + 4 + 4) with (RTT_K + RT_C2) by (unfold RT_C1, RT_C2; lia). reflexivity. }
assert (HRA2 : YK0s.ret_ok (Z_to_bv 64 (BASE + (RTT_K + RT_C2)))).
{ apply (ret_ok_codeptr_v (PI := PA)); vm_compute; [split; [discriminate | reflexivity] | reflexivity]. }
assert (Hsq2 : src_ok SEGS W regsU mem q (Z.of_nat (length (ri_tb D)) + 1)).
{ replace (Z.of_nat (length (ri_tb D)) + 1) with (Z.of_nat (length (ri_tb D ++ [0])))
    by (rewrite length_app; cbn [length]; lia).
  apply (rcl_src_ok W regsU mem q _ HBQ). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite U2.
  lia. }
(* strlen (q) *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  Time exact (YGcallMxmn.aj_strlen_at_xromR (fx := fxc) (SK := SK) SEGS B PST ARx RLO RHI LAWS Hsegs
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___wrap_strlen) (STRLEN fxc) W regsU mem STKR (ri_sp D) (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D))
    (ri_Hp D) (ri_W D)
    (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp mdU k q (Z.of_nat (length (ri_tb D))) (RT_R (ri_sp D) - ri_sp D)
    (Z_to_bv 64 (BASE + (RTT_K + RT_C2)))
    HJm2 U10 Hq0 Hn0 H32 Hq63 U2 Ho16 Ho0 Hbud U3 U4 U1 HRA2 Hqf Hsq2 Hwq Hqm Hqr Hqh Hqt HROD). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hlen3 & Hfr3 & _ & HMN3).
assert (HCR3 : rtt_cregs B D ly regs3 pos).
{ assert (KP3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> r <> 1%bv -> r <> 10%bv -> r <> 23%bv ->
    getr regs3 r = getr regs r).
  { intros r Hr H1 H10 H23. rewrite (ts_ap _ _ r HP3 Hr). exact (FK2 r H1 H10 H23). }
  unfold rtt_cregs. rewrite !KP3 by (first [ts_cs | reg_neq_tac]). repeat split; assumption. }
(* +772: the continuation *)
apply HCONT; [rewrite (ts_ap _ _ 22%bv HP3) by ts_cs; apply FK2; reg_neq_tac|].
split; [|split].
- Time apply (s12_keep D fxc ly S Hp W regs mem md k pos regs3 mem3 md3
    (ri_sp D + (RT_R (ri_sp D) - ri_sp D) - 2 * ESTACK) (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) HP HC HJ3);
    [lia | lia | exact Hfr3 | exact HMN3 | exact HCR3 | | | ].
  + rewrite (ts_ap _ _ 21%bv HP3) by ts_cs. apply FK2; reg_neq_tac.
  + rewrite (ts_ap _ _ 22%bv HP3) by ts_cs. apply FK2; reg_neq_tac.
  + rewrite (ts_ap _ _ 27%bv HP3) by ts_cs. apply FK2; reg_neq_tac.
- exact Hlen3.
- rewrite (ts_ap _ _ 23%bv HP3) by ts_cs. exact U23.
Time Qed.

(* ---- THE SEGMENT: RT_CMP (+740) -> strcmp -> strlen -> +772 ---- *)
Lemma cmp_s12 : forall D, PRE D ->
  forall fxc ly S Hp W regs mem md k pos,
  AT_CMP D fxc ly S Hp W regs mem md k pos ->
  (* s6 (x22, the text q) is the +740 state's: no S12 instruction writes it and the string calls preserve it
     (RttCmp's composition carries a fact about q across the segment through it) *)
  (forall regs2 mem2 md2, getr regs2 22 = getr regs 22 -> AT_LEN D fxc ly S Hp W regs2 mem2 md2 k pos ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
       (mkCfg (@YK11.mkst fxc regs2 (Z_to_bv 64 (BASE + (RTT_K + RT_C2))) mem2 (YK11.seg_rom SEGS)) md2) (POST D)) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTT_K + RT_CMP))) mem (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D HP fxc ly S Hp W regs mem md k pos HC HCONT.
apply (s12_cmp D HP fxc ly S Hp W regs mem md k pos HC).
intros regs2 mem2 md2 E2 HC2 R10.
apply (s12_len D HP fxc ly S Hp W regs2 mem2 md2 k pos HC2 R10).
intros regs3 mem3 md3 E3 HL. apply HCONT; [rewrite E3; exact E2 | exact HL].
Qed.

End s12.

(* the ELABORATED statement (the text owner's statement-trap check, implicits on, notations off): the theorem's type is
   its statement, so `Check @` shows every class slot of the cut's predicates (the contract's fx) and every explicit
   fxc; the one Prop definition of this file, s12_strok, binds no FPState, and `Print` shows its body *)
Set Printing Implicit.
Unset Printing Notations.
Check @cmp_s12.
Print s12_strok.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions cmp_s12.
