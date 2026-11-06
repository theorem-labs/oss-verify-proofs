(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 389 of its 429 lines of code are new or changed and 474 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): the L2 stretch at the re-hiding
   contract: the walk in YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (Crt102B_T5_bd.v's restated
   CT5_* statements, the goal patterns), the journal at R := YA0nH.wle' SEGS RZ_cf. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T5 (CRT-B-L012): the L2 STRETCH, B' entry + 0x56c ->
   + 0x5b0 (at found; 18 instructions): `sd a1, 0x40(s1)` (at), back.n against doc->n + (at == doc->n) (the new:748
   abort, not taken: Crt102Model.cm_members_crt), `beqz doc->n` -> C (+0x6f8), else the member loop's registers
   (s5 = s8 = s10 = 0, s6 = shadow (&doc->keys)) and spills (0x48 = &doc->kids, 0x28 = its shadow) -> L3 (+0x5b4).
   ct5_L2 : CT5_L2_STMT (Crt102B_T5_bd.v).

   proves no function (kind: segment lemma support).

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): the cuts carry crt_live at kb = prh_wk F_check_round_trip (the
   notation liveB); the run keeps the journal's budget WS (Crt102Kit.crt_run_to_xw_inv) and ct5_core_run takes it
   with its bound. ct5_L2's statement is unchanged.

   NUMERALS. LENGTH: the s1 slots 8 / 40 / 48 / 56 / 64 / 72 (Crt102Glue's CRT_SP_ names where they exist; 8 is
   doc->n's copy, 0x48 is &doc->kids at L3), 72 (back + 0x28, back.n), 40 / 80 (the run's write window), 96 (the s1
   region), 2 ^ 44 / 2 ^ 45 / 2 ^ 46 / 2 ^ 47 (bounds). WORD: register numbers, atom numbers. No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6_st Crt102B_T7_kit Crt102B_T7_tree Crt102B_T6 Crt102B_T5_bd.
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


(* the L2 state: current registers (x11 = at, x12 = (at == doc->n)), the s1 slots L2 reads (8 = doc->n, 0x30 =
   &doc->keys, 0x38 = &back) with its writes in [0x28, 0x50), back.n at F + 72; extras 64 = doc->n, 65 = back.n *)
Definition ct5_s1R2 : YP09.region := YP09.mkRegion (Some 41%nat) 0 96 40 80
  [YP09.mkChunk 8 (CVal 8 (SOff 64 0)); YP09.mkChunk 48 (CVal 8 (SOff 54 32)); YP09.mkChunk 56 (CVal 8 (SOff 51 32))].
Definition ct5_backR2 : YP09.region := YP09.mkRegion (Some 51%nat) 72 80 0 0 [YP09.mkChunk 72 (CVal 8 (SOff 65 0))].
Definition ct5_atoms2 : list (nat * afact) :=
  [(59%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (41%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (51%nat, mkAF 4096 CT6_HI 5);
   (54%nat, mkAF 4096 CT6_HI 3); (43%nat, mkAF 0 (2 ^ 44) 0); (44%nat, mkAF 0 1 0); (64%nat, mkAF 0 (2 ^ 44) 0);
   (65%nat, mkAF 1 (2 ^ 45) 0)].
Definition ct5_alias2 : list (sv * sv) := [(SAlu ALU_ADD (SOff 64 0) (SOff 44 0), SOff 65 0)].
Definition ct5_ss2 (pc : Z) (xc : list acond) : sstate :=
  mkSS pc cur_atoms [ct5_s1R2; ct5_backR2] None (mkFacts ct5_atoms2 xc ct5_alias2).
Definition ct5_N0 : acond := mkAC BC_EQ (SOff 64 0) (SLit 0).
Definition ct5_N1 : acond := mkAC BC_NE (SOff 64 0) (SLit 0).

(* a chunk's membership in a region's chunk list *)
Ltac ct5_in := cbn [In]; repeat (first [left; reflexivity | right]).

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

(* a chunk of a region of a run's final state, at its value *)
Lemma ct5_fld : forall E m n b cs lo hi wlo whi od e v,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (b + od) 8 v.
Proof.
intros E m n b cs lo hi wlo whi od e v HR Hb Hin He Hv.
pose proof (ts_field E m n b cs lo hi wlo whi od 8 e HR Hb Hin ltac:(lia)) as V.
change (N.to_nat 8) with 8%nat in V. change (U E e) with (bv_unsigned (sv_denot E e)) in V.
rewrite He, unsigned_lit_small in V by lia. rewrite Z.mod_small in V by lia. exact V.
Qed.



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





Lemma ct5_st2 : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg sp1v F doc' atv flg nn bn xc,
  getr rg 9 = w64 sp1v -> getr rg 19 = w64 F -> getr rg 22 = w64 doc' -> getr rg 27 = w64 SHADOW_OFF ->
  getr rg 11 = w64 atv -> getr rg 12 = w64 flg ->
  2 ^ 46 <= sp1v <= 2 ^ 47 -> sp1v mod 32 = 0 ->
  4096 <= F -> F + 512 <= CT6_HI -> F mod 32 = 0 -> F + 80 <= sp1v ->
  4096 <= doc' -> doc' + 56 <= CT6_HI -> doc' mod 8 = 0 ->
  0 <= atv <= 2 ^ 44 -> 0 <= flg <= 1 -> 0 <= nn <= 2 ^ 44 -> bn = nn + flg -> 1 <= bn ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 8) 8 nn ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 48) 8 (doc' + 32) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 56) 8 (F + 32) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 72) 8 bn ->
  (forall a, sp1v + 40 <= a < sp1v + 80 -> apresent (w_H Wc) memc a) ->
  conds_ok (TEB regs rg [w64 nn; w64 bn]) xc ->
  st_ok_pi SEGS VAL (TEB regs rg [w64 nn; w64 bn]) (ct5_ss2 pc xc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))).
Proof.
intros fxk pc Wc memc rg sp1v F doc' atv flg nn bn xc R9 R19 R22 R27 R11 R12 Hs1 Hs1a HF1 HF2 HF3 HF4 Hd1 Hd2 Hd3
  Hat Hfl Hnn Ebn Hbn1 C8 C48 C56 CB72 HPR XC.
set (mo := [w64 nn; w64 bn]). set (E := TEB regs rg mo).
assert (HIc : CT6_HI = 2 ^ 47 - 2 ^ 23) by reflexivity.
assert (A41 : ew E 41 = w64 sp1v) by exact (eq_trans (te_cur regs rg mo 9%bv 9 eq_refl) R9).
assert (A51 : ew E 51 = w64 F) by exact (eq_trans (te_cur regs rg mo 19%bv 19 eq_refl) R19).
assert (A54 : ew E 54 = w64 doc') by exact (eq_trans (te_cur regs rg mo 22%bv 22 eq_refl) R22).
assert (A59 : ew E 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (A43 : ew E 43 = w64 atv) by exact (eq_trans (te_cur regs rg mo 11%bv 11 eq_refl) R11).
assert (A44 : ew E 44 = w64 flg) by exact (eq_trans (te_cur regs rg mo 12%bv 12 eq_refl) R12).
assert (A64 : ew E 64 = w64 nn) by exact (te_more_lt regs rg mo 0 ltac:(cbn; lia)).
assert (A65 : ew E 65 = w64 bn) by exact (te_more_lt regs rg mo 1 ltac:(cbn; lia)).
assert (U41 : bv_unsigned (ew E 41) = sp1v) by (rewrite A41; apply unsigned_lit_small; lia).
assert (U51 : bv_unsigned (ew E 51) = F) by (rewrite A51; apply unsigned_lit_small; lia).
assert (U54 : bv_unsigned (ew E 54) = doc') by (rewrite A54; apply unsigned_lit_small; lia).
assert (U59 : bv_unsigned (ew E 59) = SHADOW_OFF) by (rewrite A59; apply unsigned_lit_small; cbv [SHADOW_OFF]; lia).
assert (U43 : bv_unsigned (ew E 43) = atv) by (rewrite A43; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E 44) = flg) by (rewrite A44; apply unsigned_lit_small; lia).
assert (U64 : bv_unsigned (ew E 64) = nn) by (rewrite A64; apply unsigned_lit_small; lia).
assert (U65 : bv_unsigned (ew E 65) = bn) by (rewrite A65; apply unsigned_lit_small; lia).
assert (UA : forall n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v).
{ intros n v H. rewrite ts_U0. exact H. }
unfold ct5_ss2. apply ts_st_ok.
all: fold E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + apply (ts_rok E _ 41 sp1v); [exact U41 | lia | lia | |].
    { intros o Ho. apply (apresent_writable SEGS). apply HPR. lia. }
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (ts_chunk E _ sp1v 8 8 _ nn); [| lia | lia | exact C8].
      apply (ct6_denot_at E 64%nat nn A64); lia.
    * apply (ts_chunk E _ sp1v 48 8 _ (doc' + 32)); [| lia | lia | exact C48].
      apply (ct6_denot_off E 54%nat 32 doc' A54); lia.
    * apply (ts_chunk E _ sp1v 56 8 _ (F + 32)); [| lia | lia | exact C56].
      apply (ct6_denot_off E 51%nat 32 F A51); lia.
  + apply (ts_rok E _ 51 F); [exact U51 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ F 72 8 _ bn); [| lia | lia | exact CB72].
    apply (ct6_denot_at E 65%nat bn A65); lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi ct5_s1R2 ct5_backR2]. rewrite !ts_bv_some.
  rewrite U41, U51. repeat split; lia.
- split; [|split].
  + clearbody E mo. cbn [f_atoms]. unfold ct5_atoms2. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U59, U41, U51, U54, U43, U44, U64, U65.
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 5) with 32.
    rewrite !Z.mod_1_r. cbv [SHADOW_OFF]. lia.
  + exact XC.
  + clearbody E mo. cbn [f_alias]. unfold ct5_alias2. cbn [alias_ok].
    split; [|exact I]. apply U_inj. rewrite U_SAlu, (UA 64%nat _ U64), (UA 44%nat _ U44), (UA 65%nat _ U65).
    unfold zcanon, M64, zalu_raw. rewrite Z.mod_small by lia. lia.
Qed.


#[local] Notation CORE := (@crt5_core fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam
  peak cnt most).
#[local] Notation L2STMT Pd := (@CT5_L2_STMT fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D
  Lam peak cnt ran most Pd).

(* ---- L2 (+0x56c) -> L3 (doc->n > 0, i = 0) or C (doc->n = 0) ---- *)
Lemma ct5_L2 : forall Pd, L2STMT Pd.
Proof.
intros Pd. unfold CT5_L2_STMT, CT5_ATL3, CT5_ATC, CT5_AT_L2.
intros HL3 HC fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw atn HL2 HPd.
destruct HL2 as (HCORE & R11 & R12 & Eat).
pose proof HCORE as (Ht & HFZ & HFK & HL & HDR & S0 & S8 & S48 & S56 & S80 & S88 & Hd8 & RAd & RAb & RAv & Hcs1 & Hcs2 &
  Hcnt & Hsv & HTC & HFD & HBK & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
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
set (F := frame_addr lyc CRT_CID pos) in *.
(* back's header: back.n *)
unfold crt_tc in HBK. rewrite Ht, cm_crt_tree_obj in HBK.
pose proof (cm_set_len mms (PjTree.JStr ck_STAMP)) as Elen.
set (ms' := PjTree.pj_set_model mms ck_MOD_AT (PjTree.JStr ck_STAMP)) in *.
pose proof (cm_at_le mms) as Hatl.
assert (Hl' : (0 < length ms')%nat).
{ rewrite Elen. destruct (Nat.eqb_spec (cm_at mms) (length mms)) as [E0|E0]; lia. }
destruct (ct6_obj_hdr SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (F + CRT_OFF_BACK) ms' Dback HBK Hl')
  as (kib & kb & capb & Dbi & _ & _ & Cb40 & _ & Hncb & _ & Lkb & _ & _ & _).
unfold prh_lin in Lkb.
destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kb (8 * capb) (proj1 HJ) HLED Lkb)
  as (kb0 & kb16 & kb4 & kbc & _).
destruct Cb40 as (_ & Cb40).
assert (Hn44 : Z.of_nat (length mms) <= 2 ^ 44).
{ assert (Hle : (length mms <= length ms')%nat).
  { rewrite Elen. destruct (Nat.eqb (cm_at mms) (length mms)); lia. }
  apply Nat2Z.inj_le in Hle. lia. }
set (nn := Z.of_nat (length mms)) in *.
set (flg := if Nat.eqb atn (length mms) then 1 else 0) in *.
set (bn := Z.of_nat (length ms')) in *.
assert (Ebn : bn = nn + flg).
{ unfold bn, nn, flg. rewrite Elen, Eat. destruct (Nat.eqb (cm_at mms) (length mms)); lia. }
assert (Hfl : 0 <= flg <= 1) by (unfold flg; destruct (Nat.eqb _ _); lia).
assert (Hnn0 : 0 <= nn) by (unfold nn; lia).
assert (Hat0 : 0 <= Z.of_nat atn <= 2 ^ 44) by (rewrite Eat; unfold nn in Hn44; lia).
set (mo := [w64 nn; w64 bn]).
set (E := TEB regs rg mo).
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (U41 : bv_unsigned (ew E 41) = sp1).
{ rewrite (te_cur regs rg mo 9%bv 9 eq_refl), R9. apply unsigned_lit_small. lia. }
assert (A54 : ew E 54 = w64 doc) by exact (eq_trans (te_cur regs rg mo 22%bv 22 eq_refl) R22).
assert (A51 : ew E 51 = w64 F) by exact (eq_trans (te_cur regs rg mo 19%bv 19 eq_refl) R19).
assert (A59 : ew E 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (A43 : ew E 43 = w64 (Z.of_nat atn)) by exact (eq_trans (te_cur regs rg mo 11%bv 11 eq_refl) R11).
assert (A64 : ew E 64 = w64 nn) by exact (te_more_lt regs rg mo 0 ltac:(cbn; lia)).
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HST : forall xc, conds_ok E xc ->
  st_ok_pi SEGS VAL E (ct5_ss2 (CRT_PC_B + CRT_L2_OFF_B) xc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_L2_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ intros xc XC. unfold crt_spill in S8, S48, S56.
  apply (ct5_st2 fxk _ Wc memc rg sp1 F doc (Z.of_nat atn) flg nn bn xc R9 R19 R22 R27 R11 R12).
  all: try (unfold CT6_HI; lia).
  - exact S8.
  - exact S48.
  - exact S56.
  - replace (F + 72) with (F + CRT_OFF_BACK + 40) by (unfold CRT_OFF_BACK; lia). exact Cb40.
  - intros a Ha. apply HPRc. rewrite HSTKC. lia.
  - exact XC. }
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
(* the write window of the run, and the frame it leaves *)
assert (Hwr : forall xc a, in_wrange E (ss_mem (ct5_ss2 (CRT_PC_B + CRT_L2_OFF_B) xc)) a -> sp1 + 40 <= a < sp1 + 80).
{ intros xc a (rr & Hr & Ha). cbv [ct5_ss2 ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi ct5_s1R2 ct5_backR2] in Ha;
  rewrite ts_bv_some in Ha; [rewrite U41 in Ha|]; lia. }
unfold crt_cfg.
destruct (Z.eq_dec nn 0) as [En0 | En0].
- (* doc->n = 0: `beqz a3` -> C *)
  assert (XC : conds_ok E [ct5_N0]).
  { split; [|exact I]. unfold acond_ok, ct5_N0. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
    rewrite ts_U0, A64, U_SLit. unfold w64. rewrite unsigned_lit_small by lia. change (zcanon 0) with 0. apply Z.eqb_eq. lia. }
  pose proof (HST _ XC) as HS.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (0, 0) (CRT_PC_B + CRT_C_OFF_B).
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
    change n with (CRT_PC_B + CRT_C_OFF_B) end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 40 <= a < sp1 + 80) ->
    aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. exact (ts_keep Wc E _ memc (ms_mem ms) _ HFr (Hwr _) a Ha Hn). }
  assert (KSP : forall off v, (0 <= off /\ off + 8 <= 40 \/ 80 <= off < 2 ^ 32) ->
    crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc memc off v ->
    crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) off v).
  { intros off v Hoff Hv. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hv].
    intros k Hk. apply K; lia. }
  pose proof (ts_region_nth_c E (abs_ss VAL _) _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  assert (V48 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_KEYS_B
    (doc + PJ_OFF_KEYS)).
  { unfold crt_spill, CRT_SP_KEYS_B, PJ_OFF_KEYS.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 48 (SOff 54 32) (doc + 32) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off E 54%nat 32 doc A54); lia. }
  assert (V56 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_BACK
    (F + CRT_OFF_BACK)).
  { unfold crt_spill, CRT_SP_BACK, CRT_OFF_BACK.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 56 (SOff 51 32) (F + 32) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off E 51%nat 32 F A51); lia. }
  assert (V64 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_AT_B
    (Z.of_nat (cm_at mms))).
  { unfold crt_spill, CRT_SP_AT_B. rewrite <- Eat.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 64 (SOff 43 0) (Z.of_nat atn) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at E 43%nat _ A43); lia. }
  pose proof (ct5_core_run B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt most
    HPRE HTREE fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw (ms_mem ms) mdc' rg
    (fun a => sp1 + 40 <= a < sp1 + 80) HCORE HJ HB_HJ ltac:(intros a Ha; cbv beta in Ha; lia)
    ltac:(intros a Ha Hn; apply K; [exact Ha | cbv beta in Hn; exact Hn]) HPM HDR
    (KSP CRT_SP_SAVED_B saved ltac:(unfold CRT_SP_SAVED_B; lia) S0) (KSP 8 nn ltac:(lia) S8) V48 V56
    (KSP CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) S80) (KSP CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) S88))
    as HCORE2.
  destruct HCORE2 as (_ & _ & _ & HL2 & _ & S0' & _ & _ & _ & S80' & S88' & _ & RAd2 & RAb2 & RAv2 & _ & _ & _ & _ &
    HTC2 & HFD2 & HBK2 & HPOS2 & Hkw2 & Hbtb2 & Hbfo2 & Hctb2 & Hcfo2 & Hdep2).
  unfold E in HS.
  assert (BREGS : crt_bregs_B (regs := regs) (ms_regs ms) F).
  { apply (ct6_bregs_eq regs rg (ms_regs ms) F HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  refine (HC fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw _ HPd).
  exact {| crt_at_C_B_obj := Ht; crt_at_C_B_frm_zero := HFZ; crt_at_C_B_fregs := HFK; crt_at_C_B_live := HL2;
           crt_at_C_B_bregs := BREGS; crt_at_C_B_sp_saved := S0'; crt_at_C_B_sp_back := V56; crt_at_C_B_sp_at := V64;
           crt_at_C_B_back_open := RAb2; crt_at_C_B_v_open := RAv2; crt_at_C_B_cset_range := Hcs1;
           crt_at_C_B_cset_mod := Hcs2; crt_at_C_B_cnt := Hcnt; crt_at_C_B_saved_nz := Hsv; crt_at_C_B_copy := HTC2;
           crt_at_C_B_copy_fd := HFD2; crt_at_C_B_back := HBK2; crt_at_C_B_pos := HPOS2; crt_at_C_B_kw := Hkw2;
           crt_at_C_B_back_tblk := Hbtb2; crt_at_C_B_back_fo := Hbfo2; crt_at_C_B_copy_tblk := Hctb2;
           crt_at_C_B_copy_fo := Hcfo2; crt_at_C_B_copy_depth := Hdep2 |}.
- (* doc->n > 0: L3 with i = 0 *)
  assert (XC : conds_ok E [ct5_N1]).
  { split; [|exact I]. unfold acond_ok, ct5_N1. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U.
    rewrite ts_U0, A64, U_SLit. unfold w64. rewrite unsigned_lit_small by lia. change (zcanon 0) with 0.
    apply negb_true_iff, Z.eqb_neq. lia. }
  pose proof (HST _ XC) as HS.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (0, 0) (CRT_PC_B + CRT_L3_OFF_B).
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
    change n with (CRT_PC_B + CRT_L3_OFF_B) end.
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 40 <= a < sp1 + 80) ->
    aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha Hn. exact (ts_keep Wc E _ memc (ms_mem ms) _ HFr (Hwr _) a Ha Hn). }
  assert (KSP : forall off v, (0 <= off /\ off + 8 <= 40 \/ 80 <= off < 2 ^ 32) ->
    crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc memc off v ->
    crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) off v).
  { intros off v Hoff Hv. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hv].
    intros k Hk. apply K; lia. }
  pose proof (ts_region_nth_c E (abs_ss VAL _) _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  assert (V48 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_KEYS_B
    (doc + PJ_OFF_KEYS)).
  { unfold crt_spill, CRT_SP_KEYS_B, PJ_OFF_KEYS.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 48 (SOff 54 32) (doc + 32) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off E 54%nat 32 doc A54); lia. }
  assert (V56 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_BACK
    (F + CRT_OFF_BACK)).
  { unfold crt_spill, CRT_SP_BACK, CRT_OFF_BACK.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 56 (SOff 51 32) (F + 32) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off E 51%nat 32 F A51); lia. }
  assert (V64 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_AT_B
    (Z.of_nat (cm_at mms))).
  { unfold crt_spill, CRT_SP_AT_B. rewrite <- Eat.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 64 (SOff 43 0) (Z.of_nat atn) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_at E 43%nat _ A43); lia. }
  pose proof (ct5_core_run B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt most
    HPRE HTREE fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw (ms_mem ms) mdc' rg
    (fun a => sp1 + 40 <= a < sp1 + 80) HCORE HJ HB_HJ ltac:(intros a Ha; cbv beta in Ha; lia)
    ltac:(intros a Ha Hn; apply K; [exact Ha | cbv beta in Hn; exact Hn]) HPM HDR
    (KSP CRT_SP_SAVED_B saved ltac:(unfold CRT_SP_SAVED_B; lia) S0) (KSP 8 nn ltac:(lia) S8) V48 V56
    (KSP CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) S80) (KSP CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) S88))
    as HCORE2.
  destruct HCORE2 as (_ & _ & _ & HL2 & _ & S0' & _ & _ & _ & S80' & S88' & _ & RAd2 & RAb2 & RAv2 & _ & _ & _ & _ &
    HTC2 & HFD2 & HBK2 & HPOS2 & Hkw2 & Hbtb2 & Hbfo2 & Hctb2 & Hcfo2 & Hdep2).
  unfold E in HS.
  assert (BREGS : crt_bregs_B (regs := regs) (ms_regs ms) F).
  { apply (ct6_bregs_eq regs rg (ms_regs ms) F HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  assert (V40 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_SHKIDS_B
    (shadow_addr (doc + PJ_OFF_KIDS))).
  { unfold crt_spill, CRT_SP_SHKIDS_B, PJ_OFF_KIDS.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 40 (ct6_shx 54 24) (shadow_addr (doc + 24)) HR0 U41);
      [ct5_in | | cbv [shadow_addr SHADOW_OFF]; lia].
    apply (ct6_shx_denot E 54 24 doc A54 A59); lia. }
  assert (V72 : crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms) CRT_SP_KIDS_B
    (doc + PJ_OFF_KIDS)).
  { unfold crt_spill, CRT_SP_KIDS_B, PJ_OFF_KIDS.
    apply (ct5_fld E _ 41 sp1 _ 0 96 40 80 72 (SOff 54 24) (doc + 24) HR0 U41); [ct5_in | | lia].
    apply (ct6_denot_off E 54%nat 24 doc A54); lia. }
  refine (HL3 fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw 0%nat _ HPd).
  refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ; crt_at_L3_B_fregs := HFK; crt_at_L3_B_live := HL2;
            crt_at_L3_B_bregs := BREGS; crt_at_L3_B_s5_i := _; crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _;
            crt_at_L3_B_s6_keys := _; crt_at_L3_B_sp_saved := S0'; crt_at_L3_B_sp_shkids := V40;
            crt_at_L3_B_sp_keys := V48; crt_at_L3_B_sp_back := V56; crt_at_L3_B_sp_at := V64; crt_at_L3_B_sp_kids := V72;
            crt_at_L3_B_sp_shn := S80'; crt_at_L3_B_sp_pn := S88'; crt_at_L3_B_doc_align := Hd8;
            crt_at_L3_B_doc_open := RAd2; crt_at_L3_B_back_open := RAb2; crt_at_L3_B_v_open := RAv2;
            crt_at_L3_B_i_lt := _; crt_at_L3_B_cset_range := Hcs1; crt_at_L3_B_cset_mod := Hcs2;
            crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv; crt_at_L3_B_copy := HTC2;
            crt_at_L3_B_copy_fd := HFD2; crt_at_L3_B_back := HBK2; crt_at_L3_B_pos := HPOS2;
            crt_at_L3_B_kw := Hkw2; crt_at_L3_B_back_tblk := Hbtb2; crt_at_L3_B_back_fo := Hbfo2;
            crt_at_L3_B_copy_tblk := Hctb2; crt_at_L3_B_copy_fo := Hcfo2; crt_at_L3_B_copy_depth := Hdep2 |}.
  + ct6_reg HS (21%bv : bv 5) Hr. rewrite Hr. reflexivity.
  + ct6_reg HS (24%bv : bv 5) Hr. rewrite Hr. reflexivity.
  + ct6_reg HS (26%bv : bv 5) Hr. rewrite Hr. reflexivity.
  + ct6_reg HS (22%bv : bv 5) Hr. rewrite Hr. unfold PJ_OFF_KEYS, w64. apply (ct6_shx_denot E 54 32 doc A54 A59); lia.
  + unfold nn in En0. lia.
Qed.

End g.
End f.
End t5w.
