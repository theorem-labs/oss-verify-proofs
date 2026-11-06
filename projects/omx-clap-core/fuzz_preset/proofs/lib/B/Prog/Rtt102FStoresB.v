(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 135 of its 173 lines of code are new or changed and 740 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Rtt102FStoresA.v; 22 of its 174 lines of code are new or changed and 21 lines of the source are left out. *)
(* B' TWIN (asan-ubsan d663f82d7f488d30, unstripped twin c90d4fa54d43160b) of lib/A/Prog/Rtt102FStoresA.v, by a name map:
   round_trip_text's body on image B is image A's instruction sequence with only pc-relative immediates changed
   (capstone over both twins' symtab bodies; every call site at the same offset), so the twin is the A' file with
   image A's listing / image / PrhImg / CfImg names replaced by image B's (A_prog_* -> B_prog_*, PI_prog_A /
   PL_prog_A -> _B, prh_img_A -> prh_img_B, CfImg_A -> CfImg_B, S1ImgA -> S1ImgB, IMG_LO / IMG_TOP -> IMG_LO_B /
   IMG_TOP_B, the A' stretch modules Rtt102*A -> Rtt102*B, the file's own *_A names -> *_B) and image B's own value
   for each image numeral the file states (a load offset, the function's listing offset, a witness address); every
   closed image check is re-run at B' by the build. The comments below are the A' file's: their addresses and slot
   numbers are image A's. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): THE SEVEN SHADOW STORES of STRETCH F of
   round_trip_text's walk (lane RttFR1 of WalkRtt102, the text owner), RTT_SEG_F of Rtt102Cut.v at the batch kit's cut (shared layer
   80a1d52c32c7): rtt_seg RT_CMP rtt_at_cmp -> rtt_seg RT_TXE rtt_at_txe; Rtt102FB.v proves it, this file is its store
   segment.
   rule 24: proves no function (kind: segment lemma); the function-level lookup is the brief's.
   THE CODE (A' +0x184 .. +0x1c8, A' capstone listing :99-116):
     +388 lw a0, 0x30(s1)     the record's failed (s1 = RT_R sp0, the record at s1 + RT_REC)
     +392 ld s5, 0x18(s1)     the record's buffer, want
     +396 beqz a0, +412
     +412 .. +436 sb zero, 4(s9) .. sb zero, 10(s9)               back's shadow bytes 4 .. 10 := 0 (rtt_back)
     +440 auipc s11, 0x559 ; +444 lbu a0, -0x5e4(s11)             s11 (rtt_s11); a0 := g_own_ran_out
     +448 bnez a0, +460
     +452 jal fuzz_alloc_ran_out ; +456 beqz a0, +740             -> RT_CMP
   (+400 .. +408, the failed = 1 path, and +460 are not reached from RT_TXE: Rtt102FB.v.)
   The seven stores are one run of YC1fPx.v's paj_run_to_x_invR at RZW := YA0nH.wle' SEGS RZ_cf (the frame's shadow
   window, the memnorm keep as its invariant) over the cut's journal RJ, which is the journal from the entry with its
   depot moved to the cut state's (Rtt102Cut.v rtt_J, at RZW): the run keeps the state S, so the journal it returns is
   RJ at the same S. The step relation is YA0nH.SRr' SEGS RZ_cf (the re-hiding move, Rtt102Cut.v rtt_seg).
   Numerals: 412 / 440 (DERIVED: byte offsets inside round_trip_text); 4 .. 11 (LENGTH: back's shadow bytes,
   RT_BACK / 8 .. (RT_BACK + 56) / 8); 2 / 3 / 4 / 8 / 9 / 18 / 19 / 20 / 21 / 22 / 25 / 26 (WORD: register numbers);
   128 / 16 (LENGTH: fs_frame_bytes RT_CID and its shadow); 2 ^ 44 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (LENGTH). No ADDRESS
   literal: every pc is pa_sigma / pa_val of the listing. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102FR1Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Rtt102FR1KitB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offset of round_trip_text's entry (DERIVED: 4 * its slot) *)
Definition RTTF_K : Z := 4 * Z.of_nat (B_prog_slot AS_round_trip_text).

(* a register the run did not write keeps its start value (S10TxString.v tskeep) *)
Ltac fkeep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.
(* a branch step's `rs` comes from decode_any, in the form vm_compute left it: name it before rewriting *)
Ltac fbr r := lazymatch goal with |- c_eq (getr _ ?rr) _ = _ =>
  replace rr with r by (apply bv_eq; vm_compute; reflexivity) end.
(* every bv_signed of a literal, by computation *)
Ltac bvs_norm := repeat match goal with |- context [bv_signed ?i] =>
  let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end.

(* ---- the seven shadow stores' segment: one region, s9's window [4, 11), written and not read ---- *)
Definition ss_SH7 (pc : Z) : sstate := mkSS pc cur_atoms
  [YP09.mkRegion (Some (xr 25)) 4 11 4 11 []] None (mkFacts [(xr 25, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 2)] [] []).

(* the store window, as an address set *)
Definition f_E (ly : alayout) (pos a : Z) : Prop :=
  shadow_addr (frame_addr ly RT_CID pos) + 4 <= a < shadow_addr (frame_addr ly RT_CID pos) + 11.

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
(* a frame's shadow byte is no application byte *)
Lemma f_sh_not_app : forall F j y len, 4096 <= F -> F + 128 <= YM05.alloc_ceiling -> in_app F 128 -> 0 <= j < 16 ->
  in_app y len -> 0 <= len -> ~ (y <= shadow_addr F + j < y + len).
Proof.
intros F j y len HF4 HFc HFa Hj Hya Hlen Hin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hd1 : F / 8 * 8 <= F) by (pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (Hd3 : 0 <= F / 8) by (apply Z.div_pos; lia).
unfold shadow_addr, SHADOW_OFF in Hin.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFa, Hya.
unfold kHighMemBeg in C3. lia.
Qed.

(* S10TxString.v ts_SH_entry, at s9 and the seven bytes *)
Lemma f_SH_entry : forall pc (Wc : world SEGS) memc rg F,
  getr rg 25 = w64 (shadow_addr F) -> F mod 32 = 0 -> 0 <= F < 2 ^ 47 ->
  (forall j, 4 <= j < 11 -> apresent (w_H Wc) memc (shadow_addr F + j)) ->
  st_ok_pi SEGS VAL (TE rg rg []) (ss_SH7 pc)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE rg rg []) (mrestrict (w_H Wc) memc).
Proof.
intros pc Wc memc rg F R25 HF32 HF HP.
set (E := TE rg rg []).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (X25 : bv_unsigned (ew E (xr 25)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur rg rg _ 25%bv 25) by reflexivity. rewrite R25. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE rg rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 25) (shadow_addr F)); [exact X25 | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | |
    constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X25. change (2 ^ 2) with 4.
  split; [|exact I]. unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_mod F 32 ltac:(lia)). lia.
Qed.
End sh.

(* ======================================================================================================== *)
Section fs. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Existing Instance prh_img_B.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Notation RJ := (rtt_J (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RCARRY := (rtt_carry (fx := fx) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK).
(* the world relation of the walk's journals (Rtt102Cut.v rtt_J) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* (a) the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x; S10TxString.v:163) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* ======================================================================================================== *)
(* ---- THE SEVEN STORES (+412 .. +436): one runner segment, the continuation at +440 ---- *)
Lemma f_stores : forall D fxc ly S Hp W regs mem md k pos Q,
  RCARRY D fxc ly S Hp W regs mem md k pos ->
  (forall regs' mem' md',
     (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26]%bv -> getr regs' r = getr regs r) ->
     RJ D ly S Hp W mem' md' k pos ->
     (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ f_E ly pos a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     (forall j, 4 <= j < 11 -> aview SEGS (w_H W) mem' (shadow_addr (frame_addr ly RT_CID pos) + j) = Some 0) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
       (mkCfg (@YK11.mkst fxc regs' (Z_to_bv 64 (BASE + (RTTF_K + 440))) mem' (YK11.seg_rom SEGS)) md') Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTTF_K + 412))) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros D fxc ly S Hp W regs mem md k pos Q HC HK.
pose proof HC as (_ & HJ & (Efr & _) & _ & HCR & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HJ as (HAR & _).
assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md RT_CID pos HAR Hin) as (F32 & _ & _ & Fsh).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md RT_CID pos HAR Hin) as (Fb1 & Fb2 & _).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr ly RT_CID pos) in *.
destruct (f_SH_entry (fx := fxc) (RTTF_K + 412) W mem regs F R25 F32 ltac:(lia)
  ltac:(intros j Hj; exact (proj1 (Fsh j ltac:(rewrite Efs1; lia))))) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
assert (X25 : bv_unsigned (ew (TE regs regs []) (xr 25)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs regs _ 25%bv 25) by reflexivity. rewrite R25. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
set (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as PLAW.
change (srr_inv_laws SEGS P) in PLAW.
assert (HPM : P mem) by (intros H; exact H).
unfold rtt_J in HJ.
pose (RUNTO := @paj_run_to_x_invR fxc rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS P PLAW RZW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM (2 ^ 63, 2 ^ 63) (RTTF_K + 440).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 25) (shadow_addr F)); [reflexivity | exact X25 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists RT_CID, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite Efs1. change (128 / 8) with 16.
    fold F. lia. }
  apply awr_ok_nil. }
pmkst HS.
assert (Hwr : forall a, in_wrange (TE regs regs []) (ss_mem (ss_SH7 (RTTF_K + 412))) a -> f_E ly pos a).
{ intros a (r & Hr & Ha). cbv [ss_SH7 ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X25 in Ha. unfold f_E. fold F. lia. }
assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ f_E ly pos a ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. exact (ts_keep W _ _ mem (ms_mem ms) (f_E ly pos) HFr Hwr a Ha Hn). }
assert (HZ : forall j, 4 <= j < 11 -> aview SEGS (w_H W) (ms_mem ms) (shadow_addr F + j) = Some 0).
{ pose proof (ts_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  intros j Hj. assert (Ej : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10) by lia.
  destruct Ej as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
  (lazymatch goal with |- aview _ _ _ (_ + ?jj) = _ =>
     pose proof (ts_field _ _ (xr 25) (shadow_addr F) _ _ _ _ _ jj 1%N (SLit 0) HR0 X25
       ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V end;
   rewrite U_SLit in V; replace (zcanon 0 mod 2 ^ (8 * Z.of_N 1)) with 0 in V by (vm_compute; reflexivity);
   change (N.to_nat 1) with 1%nat in V;
   exact (ts_aview_of_vm1 _ _ _ _ V ltac:(lia))). }
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [fkeep HS |]). destruct Hr. }
lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 (_ + ?n)) _ _) _) _ =>
  replace n with (RTTF_K + 440) by (vm_compute; reflexivity) end.
apply HK; [exact KR | exact HJ | exact HPM | exact Kf | exact HZ].
Qed.

End fs.
