(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 408 of its 449 lines of code are new or changed and 473 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): the L0 stretch at the re-hiding
   contract: the walk in YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (Crt102B_T5_bd.v's restated
   CT5_* statements, the goal patterns), the journal at R := YA0nH.wle' SEGS RZ_cf. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T5 (CRT-B-L012): the L0 STRETCH, B' entry + 0x478 ->
   L1 (+0x4f8, doc->n > 0, i = 0) or L2 (+0x56c, doc->n = 0). `sd s8, 0(s1)` (saved), the new:740 abort `bnez s5` (not
   taken: ct5_granted), &doc->n's shadow, doc->n against U's copy (equal), the spills 0x30 / 8, `beqz doc->n` -> L2,
   &doc->keys's shadow, the at-search's set-up (s10 = s8 = doc->keys, s5 = 1, the spills 0x10 = MOD_AT, 0x18 / 0x28,
   0x20). ct5_L0 : CT5_L0_STMT (Crt102B_T5_bd.v).

   proves no function (kind: segment lemma support).

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): crt_at_L0_B and the cuts after it carry crt_live at kb =
   prh_wk F_check_round_trip (the notation liveB); the run keeps the journal's budget WS (Crt102Kit.crt_run_to_xw_inv)
   and ct5_pre_run takes it with its bound. ct5_L0's statement is unchanged.

   NUMERALS. DERIVED: 243 / 69824 as in Crt102B_T5_L1.v. LENGTH: the s1 slots, 0 / 56 (the write window), 32 / 40
   (keys / n inside struct pj), 56 (struct pj), 96, 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (bounds). WORD: register and atom numbers.
   No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp WriterSpec PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6_st Crt102B_T7_kit Crt102B_T7_tree Crt102B_T6 Crt102B_T5_bd Crt102B_T5_L2 Crt102B_T5_L1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* The re-hiding move's world relation and step relation (YA0nH), the zone (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.


(* the L0 state: current registers (x21 = the flag, x24 = saved, x22 = doc), the s1 slots L0 reads (0x38 = &back,
   0x48 = U's doc->n, 0x50 / 0x58 = shadow (&doc->n) / &doc->n) with its writes in [0, 0x38), doc's keys (when
   doc->n > 0) and n; extras 64 = doc->keys, 65 = doc->n *)
Definition ct5_s1R0 : YP09.region := YP09.mkRegion (Some 41%nat) 0 96 0 56
  [YP09.mkChunk 56 (CVal 8 (SOff 51 32)); YP09.mkChunk 72 (CVal 8 (SOff 65 0));
   YP09.mkChunk 80 (CVal 8 (ct6_shx 54 40)); YP09.mkChunk 88 (CVal 8 (SOff 54 40))].
Definition ct5_docR0 (nz : bool) : YP09.region := YP09.mkRegion (Some 54%nat) 32 48 0 0
  ((if nz then [YP09.mkChunk 32 (CVal 8 (SOff 64 0))] else []) ++ [YP09.mkChunk 40 (CVal 8 (SOff 65 0))]).
Definition ct5_atoms0 (nz : bool) : list (nat * afact) :=
  [(59%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (41%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (51%nat, mkAF 4096 CT6_HI 5);
   (54%nat, mkAF 4096 CT6_HI 3)] ++
  (if nz then [(64%nat, mkAF 4096 CT6_HI 4); (65%nat, mkAF 1 (2 ^ 44) 0)] else [(65%nat, mkAF 0 0 0)]).
Definition ct5_conds0 (nz : bool) : list acond :=
  mkAC BC_EQ (SOff 53 0) (SLit 0) :: (if nz then [mkAC BC_NE (SOff 65 0) (SLit 0)] else [mkAC BC_EQ (SOff 65 0) (SLit 0)]).
Definition ct5_SH0 : list shent := [mkSHE 54 0 56].
Definition ct5_ss0 (nz : bool) : sstate :=
  mkSS (CRT_PC_B + CRT_L0_OFF_B) cur_atoms [ct5_s1R0; ct5_docR0 nz] None (mkFacts (ct5_atoms0 nz) (ct5_conds0 nz) []).

Section t5w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* The re-hiding move: the journal at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* tcheck_round_trip_specX's premises at the entry this row reads (PRH_FnCheck.v, the text's own; Crt102Top
   discharges them) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HLED0 : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
(* the text's own request bound (PRH_FnCheck.v tcheck_round_trip_specX): every ledger request is within g_most *)
Hypothesis HRQA : RQA_crt t <= most.
(* the read-only string "modifiedAt" the at-search compares with: the text's own `kept_img B a_mod_at 11` at the
   instance's a_mod_at := CRT_MOD_AT_B (Crt102Img.v:1024) *)
Hypothesis HKMA : @kept_img _ B_prog_listing PA B (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
(* NAMED HYPOTHESES BOK (asyms_ok B; owner image B's start-up record) and IMGVIS (the image's shadow is
   visible in every ARx state; owner the instance owner, img_shadow_vis_cf), as row T7's Crt102B_T7_tree.v takes them for its
   read-only strcmp operands (cb7t_rom_prem_mod_at) *)
Hypothesis BOK : asyms_ok B.
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* THE CALLEE TEXTS, each at ANY float state.
   NAMED HYPOTHESIS ASTRCMP (owner: the libc strcmp row): the __wrap_strcmp row in its read-only-premise form WITH the memnorm
   keep (YGcallMxmn.v:898 astrcmp_realizes_xrom). The _xro form (:849) is not enough here: crt_live's last field
   (Crt102Glue.v crt_live_memnorm, `memnorm mem -> memnorm memc`) must hold again after the call, and astrcmp_realizes_xro's post
   (YGcallMxmn.v:866-873) keeps no memnorm.
   *)
Hypothesis ASTRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc)
  (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
#[local] Notation L3B := (crt_at_L3_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation CB := (crt_at_C_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).

#[local] Notation ENT := (ct6_entry B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam
  peak cnt most HPRE HTREE).
#[local] Notation L0B := (crt_at_L0_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).


Lemma ct5_obj_n : forall segs m lblk p ms Dp, pj_nodeR segs m lblk p (PjTree.JObj ms) Dp ->
  rd_u64 segs m (p + 40) (Z.of_nat (length ms)).
Proof.
intros segs m lblk p ms Dp H. cbn [pj_nodeR] in H.
destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & En & _).
destruct Hh as (_ & _ & _ & _ & _ & _ & Hn & _). rewrite <- En. exact Hn.
Qed.

Lemma ct5_st0 : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg sp1v F doc' kd nn (nz : bool),
  getr rg 9 = w64 sp1v -> getr rg 19 = w64 F -> getr rg 22 = w64 doc' -> getr rg 27 = w64 SHADOW_OFF ->
  getr rg 21 = w64 0 ->
  2 ^ 46 <= sp1v <= 2 ^ 47 -> sp1v mod 32 = 0 ->
  4096 <= F -> F + 512 <= CT6_HI -> F mod 32 = 0 ->
  4096 <= doc' -> doc' + 56 <= CT6_HI -> doc' + 56 <= sp1v -> doc' mod 8 = 0 ->
  (nz = true -> 4096 <= kd <= CT6_HI /\ kd mod 16 = 0 /\ 1 <= nn <= 2 ^ 44) -> (nz = false -> nn = 0) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 56) 8 (F + 32) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 72) 8 nn ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 80) 8 (shadow_addr (doc' + 40)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 88) 8 (doc' + 40) ->
  (nz = true -> val_mem SEGS (mrestrict (w_H Wc) memc) (doc' + 32) 8 kd) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (doc' + 40) 8 nn ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc' 56 -> in_app doc' 56 ->
  (forall a, sp1v <= a < sp1v + 56 -> apresent (w_H Wc) memc a) ->
  st_ok_pi SEGS VAL (TEB regs rg [w64 kd; w64 nn]) (ct5_ss0 nz)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_L0_OFF_B))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SOff 59 0) ct5_SH0 (TEB regs rg [w64 kd; w64 nn]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg sp1v F doc' kd nn nz R9 R19 R22 R27 R21 Hs1 Hs1a HF1 HF2 HF3 Hd1 Hd2 Hd2' Hd3 Hnz Hz
  C56 C72 C80 C88 CD32 CD40 RAd APd HPR.
set (mo := [w64 kd; w64 nn]). set (E := TEB regs rg mo).
assert (HIc : CT6_HI = 2 ^ 47 - 2 ^ 23) by reflexivity.
assert (Hnn : 0 <= nn <= 2 ^ 44) by (destruct nz; [destruct (Hnz eq_refl) as (_ & _ & H); lia | rewrite (Hz eq_refl); lia]).
assert (A41 : ew E 41 = w64 sp1v) by exact (eq_trans (te_cur regs rg mo 9%bv 9 eq_refl) R9).
assert (A51 : ew E 51 = w64 F) by exact (eq_trans (te_cur regs rg mo 19%bv 19 eq_refl) R19).
assert (A54 : ew E 54 = w64 doc') by exact (eq_trans (te_cur regs rg mo 22%bv 22 eq_refl) R22).
assert (A59 : ew E 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (A53 : ew E 53 = w64 0) by exact (eq_trans (te_cur regs rg mo 21%bv 21 eq_refl) R21).
assert (A64 : ew E 64 = w64 kd) by exact (te_more_lt regs rg mo 0 ltac:(cbn; lia)).
assert (A65 : ew E 65 = w64 nn) by exact (te_more_lt regs rg mo 1 ltac:(cbn; lia)).
assert (U41 : bv_unsigned (ew E 41) = sp1v) by (rewrite A41; apply unsigned_lit_small; lia).
assert (U51 : bv_unsigned (ew E 51) = F) by (rewrite A51; apply unsigned_lit_small; lia).
assert (U54 : bv_unsigned (ew E 54) = doc') by (rewrite A54; apply unsigned_lit_small; lia).
assert (U59 : bv_unsigned (ew E 59) = SHADOW_OFF) by (rewrite A59; apply unsigned_lit_small; cbv [SHADOW_OFF]; lia).
assert (U53 : bv_unsigned (ew E 53) = 0) by (rewrite A53; apply unsigned_lit_small; lia).
assert (U65 : bv_unsigned (ew E 65) = nn) by (rewrite A65; apply unsigned_lit_small; lia).
assert (UA : forall n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v).
{ intros n v H. rewrite ts_U0. exact H. }
split.
2:{ unfold sh_ok, ct5_SH0. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite <- (aview_rd_of SEGS);
    rewrite (UA 59%nat SHADOW_OFF U59); rewrite ?Z.add_0_r, ?Z.sub_0_r.
    rewrite (UA 54%nat _ U54). split; [exact RAd|].
    intros a Ha. destruct APd as (A1 & [A2 | (A3 & A4)]); cbv [kLowShadowBeg kHighMemBeg SHADOW_OFF] in *; lia. }
unfold ct5_ss0. apply ts_st_ok.
all: fold E.
- apply te_regs_ok.
- destruct nz; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
  + apply (ts_rok E _ 41 sp1v); [exact U41 | lia | lia | |].
    { intros o Ho. apply (apresent_writable SEGS). apply HPR. lia. }
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    * apply (ts_chunk E _ sp1v 56 8 _ (F + 32)); [| lia | lia | exact C56].
      apply (ct6_denot_off E 51%nat 32 F A51); lia.
    * apply (ts_chunk E _ sp1v 72 8 _ nn); [| lia | lia | exact C72].
      apply (ct6_denot_at E 65%nat nn A65); lia.
    * apply (ts_chunk E _ sp1v 80 8 _ (shadow_addr (doc' + 40))); [| cbv [shadow_addr SHADOW_OFF]; lia | lia | exact C80].
      apply (ct6_shx_denot E 54 40 doc' A54 A59); lia.
    * apply (ts_chunk E _ sp1v 88 8 _ (doc' + 40)); [| lia | lia | exact C88].
      apply (ct6_denot_off E 54%nat 40 doc' A54); lia.
  + apply (ts_rok E _ 54 doc'); [exact U54 | lia | lia | intros o Ho; lia |].
    apply Forall_app. split.
    * destruct nz; [|apply Forall_nil]. destruct (Hnz eq_refl) as (Hk1 & Hk2 & _).
      apply Forall_cons; [|apply Forall_nil].
      apply (ts_chunk E _ doc' 32 8 _ kd); [| lia | lia | exact (CD32 eq_refl)].
      apply (ct6_denot_at E 64%nat kd A64); lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (ts_chunk E _ doc' 40 8 _ nn); [| lia | lia | exact CD40].
      apply (ct6_denot_at E 65%nat nn A65); lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi ct5_s1R0 ct5_docR0]. rewrite !ts_bv_some.
  rewrite U41, U54. repeat split; lia.
- split; [|split].
  + clearbody E mo. cbn [f_atoms]. unfold ct5_atoms0. apply ct6_atoms_app.
    * cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U59, U41, U51, U54.
      change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 5) with 32.
      rewrite !Z.mod_1_r. cbv [SHADOW_OFF]. repeat split; lia.
    * destruct nz.
      -- destruct (Hnz eq_refl) as (Hk1 & Hk2 & Hk3).
         assert (U64 : bv_unsigned (ew E 64) = kd) by (rewrite A64; apply unsigned_lit_small; lia).
         cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U64, U65.
         change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. repeat split; lia.
      -- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U65, (Hz eq_refl).
         change (2 ^ 0) with 1. repeat split; lia.
  + clearbody E mo. cbn [f_conds]. unfold ct5_conds0. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    split.
    * rewrite branch_eq_U, (UA 53%nat 0 U53), U_SLit. change (zcanon 0) with 0. reflexivity.
    * destruct nz; cbn [conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]; split; try exact I.
      -- destruct (Hnz eq_refl) as (_ & _ & Hk3). rewrite branch_ne_U, (UA 65%nat nn U65), U_SLit.
         change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. lia.
      -- rewrite branch_eq_U, (UA 65%nat nn U65), U_SLit, (Hz eq_refl). change (zcanon 0) with 0. reflexivity.
  + exact I.
Qed.

#[local] Notation CORE := (@crt5_core fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam
  peak cnt most).
#[local] Notation spillB := (crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation L0STMT Pd := (@CT5_L0_STMT fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D
  Lam peak cnt ran most Pd).

(* ---- L0 (+0x478) -> L1 at i = 0 (doc->n > 0) or L2 (doc->n = 0) ---- *)
Lemma ct5_L0 : forall Pd, L0STMT Pd.
Proof.
intros Pd. unfold CT5_L0_STMT.
intros HPd0 HL1all HL2s fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg mms cset saved rcd HL0.
destruct (ct5_granted B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D x Lam peak cnt ran most
  HREAD HLENX HWL0 HWL1 HCNT HLED0 HRQA fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg mms cset saved rcd HL0)
  as (Hsv & Hrc & HPOS0 & Hcnt & Dback & kw & EDx & HBK & HbP & HFo & Hkw).
pose proof (HPd0 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg mms cset saved rcd Dback kw HL0 EDx) as HPd.
pose proof (crt_at_L0_B_obj HL0) as Ht. pose proof (crt_at_L0_B_frm_zero HL0) as HFZ.
pose proof (crt_at_L0_B_fregs HL0) as HFK. pose proof (crt_at_L0_B_live HL0) as HL.
pose proof (crt_at_L0_B_dregs HL0) as HDR. pose proof (crt_at_L0_B_saved HL0) as R24.
pose proof (crt_at_L0_B_flag HL0) as R21. pose proof (crt_at_L0_B_sp_back HL0) as S56.
pose proof (crt_at_L0_B_sp_shn HL0) as S80. pose proof (crt_at_L0_B_sp_pn HL0) as S88.
pose proof (crt_at_L0_B_sp_n HL0) as S72. pose proof (crt_at_L0_B_doc_align HL0) as Hd8.
pose proof (crt_at_L0_B_doc_open HL0) as RAd. pose proof (crt_at_L0_B_back_open HL0) as RAb.
pose proof (crt_at_L0_B_v_open HL0) as RAv. pose proof (crt_at_L0_B_cset_range HL0) as Hcs1.
pose proof (crt_at_L0_B_cset_mod HL0) as Hcs2. pose proof (crt_at_L0_B_copy HL0) as HTC.
pose proof (crt_at_L0_B_copy_fd HL0) as HFD. pose proof (crt_at_L0_B_copy_tblk HL0) as HcP.
pose proof (crt_at_L0_B_copy_fo HL0) as HcFo. pose proof (crt_at_L0_B_copy_depth HL0) as Hdep.
subst Dx.
assert (HPOS := conj HPOS0 (conj Hkw (conj HbP (conj HFo (conj HcP (conj HcFo Hdep)))))).
assert (R21' : getr rg 21 = w64 0).
{ rewrite R21. rewrite (proj2 (Z.eqb_neq saved 0) Hsv). rewrite Hrc. reflexivity. }
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED. pose proof (crt_side_doc (crt_live_side HL)) as HDOC.
pose proof (crt_side_doc_blocks (crt_live_side HL)) as HDL. pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & Hdc3 & Hdc4).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
assert (HPRE5 : @crt5_pre fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt most
  fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc mms cset saved kw).
{ unfold crt5_pre. split; [exact Ht|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HL|]. split; [exact Hd8|]. split; [exact RAd|]. split; [exact RAb|]. split; [exact RAv|]. split; [exact Hcs1|]. split; [exact Hcs2|]. split; [exact Hcnt|]. split; [exact Hsv|]. split; [exact HTC|]. split; [exact HFD|]. split; [exact HBK|]. exact HPOS. }
set (F := frame_addr lyc CRT_CID pos) in *.
(* saved's block *)
assert (Hsb : In (saved, kw) Lamc).
{ apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 saved kw (proj1 HJ) HLED Hsb)
  as (sv0 & sv16 & sv4 & svc & _).
(* doc's n *)
rewrite Ht in HDOC.
pose proof (ct5_obj_n SEGS _ (prh_lin Lamc) doc mms D HDOC) as Cd40.
set (nn := Z.of_nat (length mms)) in *.
assert (HIc : CT6_HI = 2 ^ 47 - 2 ^ 23) by reflexivity.
assert (U41g : forall kd, bv_unsigned (ew (TEB regs rg [w64 kd; w64 nn]) 41) = sp1).
{ intros kd. rewrite (te_cur regs rg _ 9%bv 9 eq_refl), R9. apply unsigned_lit_small. lia. }
assert (Hwr : forall kd nz a, in_wrange (TEB regs rg [w64 kd; w64 nn]) (ss_mem (ct5_ss0 nz)) a -> sp1 <= a < sp1 + 56).
{ intros kd nz a (rr & Hr & Ha). cbv [ct5_ss0 ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi ct5_s1R0 ct5_docR0] in Ha;
  rewrite ts_bv_some in Ha; [rewrite (U41g kd) in Ha|]; lia. }
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_spill in S56, S80, S88, S72.
unfold crt_cfg.
destruct (Nat.eq_dec (length mms) 0) as [Hz | Hnz].
- (* doc->n = 0: L2 with at = 0 *)
  assert (Em : mms = []) by (destruct mms; [reflexivity | cbn [length] in Hz; lia]).
  set (mo := [w64 0; w64 nn]).
  destruct (ct5_st0 fxk Wc memc rg sp1 F doc 0 nn false R9 R19 R22 R27 R21') as (HS & SHOK).
  all: try (unfold CT6_HI; lia).
  all: try (intros E0; discriminate E0).
  all: try (intros _; unfold nn; reflexivity).
  all: try assumption.
  { destruct Cd40 as (_ & Cd40). exact Cd40. }
  { intros a Ha. apply HPRc. rewrite HSTKC. lia. }
  fold mo in HS, SHOK.
  assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
  assert (U41 : bv_unsigned (ew (TEB regs rg mo) 41) = sp1) by exact (U41g 0).
  assert (A54 : ew (TEB regs rg mo) 54 = w64 doc) by exact (eq_trans (te_cur regs rg mo 22%bv 22 eq_refl) R22).
  assert (A56 : ew (TEB regs rg mo) 56 = w64 saved) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
  assert (A65 : ew (TEB regs rg mo) 65 = w64 nn) by exact (te_more_lt regs rg mo 1 ltac:(cbn; lia)).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_B + CRT_L2_OFF_B).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 41%nat (sp1 - sp0)); [reflexivity | | | |].
    - rewrite U41. lia.
    - cbn [YP09.r_wlo]. rewrite HSTKC. lia.
    - cbn [YP09.r_whi]. lia.
    - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  pmkst HS.
  set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + CRT_L2_OFF_B) end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. exact (ts_keep Wc _ _ memc (ms_mem ms) _ HFr (Hwr _ _) a Ha Hn). }
  assert (KSP : forall off v, 56 <= off < 2 ^ 32 -> spillB Wc memc off v -> spillB Wc (ms_mem ms) off v).
  { intros off v Hoff Hv. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hv].
    intros k Hk. apply K; lia. }
  assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
    by (intros a Ha; apply K; lia).
  pose proof (ts_region_nth_c (TEB regs rg mo) (abs_ss VAL _) _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  assert (V0 : spillB Wc (ms_mem ms) CRT_SP_SAVED_B saved).
  { unfold crt_spill, CRT_SP_SAVED_B.
    apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 0 (SOff 56 0) saved HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at _ 56%nat saved A56); lia. }
  assert (V8 : spillB Wc (ms_mem ms) 8 nn).
  { unfold crt_spill. apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 8 (SOff 65 0) nn HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at _ 65%nat nn A65); lia. }
  assert (V48 : spillB Wc (ms_mem ms) CRT_SP_KEYS_B (doc + PJ_OFF_KEYS)).
  { unfold crt_spill, CRT_SP_KEYS_B, PJ_OFF_KEYS.
    apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 48 (SOff 54 32) (doc + 32) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off _ 54%nat 32 doc A54); lia. }
  assert (HDR1 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
  { refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
    apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  assert (HCORE1 : CORE fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved
    kw).
  { refine (ct5_pre_run B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt most
      HPRE HTREE fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc mms cset saved kw (ms_mem ms) mdc'
      (ms_regs ms) (fun a => sp1 <= a < sp1 + 56) HPRE5 HJ HB_HJ ltac:(intros a Ha; cbv beta in Ha; lia)
      ltac:(intros a Ha Hn; apply K; [exact Ha | cbv beta in Hn; exact Hn]) HPM HDR1 V0 V8 V48
      (KSP CRT_SP_BACK _ ltac:(unfold CRT_SP_BACK; lia) S56) (KSP CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) S80)
      (KSP CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) S88)). }
  refine (HL2s fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw 0%nat
    _ HPd).
  refine (conj HCORE1 (conj _ (conj _ _))).
  + ct6_reg HS (11%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_at _ 65%nat nn A65) by lia. unfold nn. rewrite Em.
    reflexivity.
  + ct6_reg HS (12%bv : bv 5) Hr. rewrite Hr. rewrite Em. reflexivity.
  + rewrite Em. reflexivity.
- (* doc->n > 0: L1 with i = 0 *)
  destruct (ct6_obj_hdr SEGS _ (prh_lin Lamc) doc mms D HDOC ltac:(lia))
    as (kid & kd & capd & Ddi & _ & Cd32 & _ & _ & Hncd & _ & Lkd & _ & _ & _).
  unfold prh_lin in Lkd.
  destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kd (8 * capd) (proj1 HJ) HLED Lkd)
    as (kd0 & kd16 & kd4 & kdc & _).
  set (mo := [w64 kd; w64 nn]).
  destruct (ct5_st0 fxk Wc memc rg sp1 F doc kd nn true R9 R19 R22 R27 R21') as (HS & SHOK).
  all: try (unfold CT6_HI; lia).
  all: try (intros E0; discriminate E0).
  all: try (intros _; unfold CT6_HI; unfold nn; lia).
  all: try assumption.
  { intros _. destruct Cd32 as (_ & Cd32). exact Cd32. }
  { destruct Cd40 as (_ & Cd40). exact Cd40. }
  { intros a Ha. apply HPRc. rewrite HSTKC. lia. }
  fold mo in HS, SHOK.
  assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
  assert (U41 : bv_unsigned (ew (TEB regs rg mo) 41) = sp1) by exact (U41g kd).
  assert (A54 : ew (TEB regs rg mo) 54 = w64 doc) by exact (eq_trans (te_cur regs rg mo 22%bv 22 eq_refl) R22).
  assert (A56 : ew (TEB regs rg mo) 56 = w64 saved) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
  assert (A64 : ew (TEB regs rg mo) 64 = w64 kd) by exact (te_more_lt regs rg mo 0 ltac:(cbn; lia)).
  assert (A65 : ew (TEB regs rg mo) 65 = w64 nn) by exact (te_more_lt regs rg mo 1 ltac:(cbn; lia)).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_B + CRT_L1_OFF_B).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 41%nat (sp1 - sp0)); [reflexivity | | | |].
    - rewrite U41. lia.
    - cbn [YP09.r_wlo]. rewrite HSTKC. lia.
    - cbn [YP09.r_whi]. lia.
    - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  pmkst HS.
  set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + CRT_L1_OFF_B) end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. exact (ts_keep Wc _ _ memc (ms_mem ms) _ HFr (Hwr _ _) a Ha Hn). }
  assert (KSP : forall off v, 56 <= off < 2 ^ 32 -> spillB Wc memc off v -> spillB Wc (ms_mem ms) off v).
  { intros off v Hoff Hv. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hv].
    intros k Hk. apply K; lia. }
  assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
    by (intros a Ha; apply K; lia).
  pose proof (ts_region_nth_c (TEB regs rg mo) (abs_ss VAL _) _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  assert (V0 : spillB Wc (ms_mem ms) CRT_SP_SAVED_B saved).
  { unfold crt_spill, CRT_SP_SAVED_B.
    apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 0 (SOff 56 0) saved HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at _ 56%nat saved A56); lia. }
  assert (V8 : spillB Wc (ms_mem ms) 8 nn).
  { unfold crt_spill. apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 8 (SOff 65 0) nn HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at _ 65%nat nn A65); lia. }
  assert (V48 : spillB Wc (ms_mem ms) CRT_SP_KEYS_B (doc + PJ_OFF_KEYS)).
  { unfold crt_spill, CRT_SP_KEYS_B, PJ_OFF_KEYS.
    apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 48 (SOff 54 32) (doc + 32) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off _ 54%nat 32 doc A54); lia. }
  assert (HDR1 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
  { refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
    apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  assert (HCORE1 : CORE fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved
    kw).
  { refine (ct5_pre_run B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt most
      HPRE HTREE fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc mms cset saved kw (ms_mem ms) mdc'
      (ms_regs ms) (fun a => sp1 <= a < sp1 + 56) HPRE5 HJ HB_HJ ltac:(intros a Ha; cbv beta in Ha; lia)
      ltac:(intros a Ha Hn; apply K; [exact Ha | cbv beta in Hn; exact Hn]) HPM HDR1 V0 V8 V48
      (KSP CRT_SP_BACK _ ltac:(unfold CRT_SP_BACK; lia) S56) (KSP CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) S80)
      (KSP CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) S88)). }
  assert (HEIx : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
  assert (V16 : spillB Wc (ms_mem ms) 16 (@CRT_MOD_AT_B _ PA)).
  { unfold crt_spill. apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 16 (SOff 243 69824) _ HR0 U41); [ct5_in | |].
    - apply ct5_img_den; [exact HEIx | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity].
    - split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. }
  assert (V24 : spillB Wc (ms_mem ms) 24 1).
  { unfold crt_spill. apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 24 (SLit 1) 1 HR0 U41); [ct5_in | reflexivity | lia]. }
  assert (V32 : spillB Wc (ms_mem ms) 32 kd).
  { unfold crt_spill. apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 32 (SOff 64 0) kd HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at _ 64%nat kd A64); lia. }
  assert (V40 : spillB Wc (ms_mem ms) 40 1).
  { unfold crt_spill. apply (ct5_fld _ _ 41 sp1 _ 0 96 0 56 40 (SLit 1) 1 HR0 U41); [ct5_in | reflexivity | lia]. }
  assert (Hkd1 : rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms)) (doc + PJ_OFF_KEYS) kd).
  { destruct Cd32 as (Hk1 & Hk2). split; [exact Hk1|].
    apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hk2].
    intros k Hk. apply KL. unfold PJ_OFF_KEYS. lia. }
  refine (HL1all mms fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) cset saved kw kd
    _ HPd).
  refine (conj HCORE1 (conj _ (conj _ (conj _ (conj V16 (conj V24 (conj V32 (conj V40 (conj (KSP 72 nn ltac:(lia) S72)
    (conj Hkd1 (conj _ _))))))))))).
  + ct6_reg HS (21%bv : bv 5) Hr. rewrite Hr. reflexivity.
  + ct6_reg HS (24%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_at _ 64%nat kd A64) by lia. f_equal. lia.
  + ct6_reg HS (26%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_at _ 64%nat kd A64) by lia. f_equal. lia.
  + lia.
  + intros j nm u Hj. lia.
Qed.

End g.
End f.
End t5w.
