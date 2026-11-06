(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 389 of its 426 lines of code are new or changed and 741 lines of the source are left out. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): STRETCH F of
   round_trip_text's walk (lane RttFR1 of WalkRtt102, the text owner), RTT_SEG_F of Rtt102Cut.v at the batch kit's cut (the cut
   7cdbb61b5fa0 merged into the lane, c46ea8f2977; the shared layer re-fitted at 80a1d52c32c7):
   rtt_seg RT_CMP rtt_at_cmp -> rtt_seg RT_TXE rtt_at_txe.
   rule 24: proves no function (kind: segment lemma); the function-level lookup is the brief's
   (proof-index round_trip_text EXIT=0, no released ASan proof).
   AT THE BATCH KIT'S CUT: DW is gone; the journal RJ is the depot-moved one (Rtt102Cut.v rtt_J), so the call of
   fuzz_alloc_ran_out is made from the entry `set_depot (st_depot S) (ri_S D)` and its caller journal is RJc at the call
   state S, which rtt_carry_keep takes; the wild budget rtt_wild D S RTT_WK_T that RT_TXE and RT_CMP both end in is the
   SAME fact at the same state: no step of F changes S (the stores and loads keep it, fuzz_alloc_ran_out's text states
   S' = S).
   THE CODE (A' +0x184 .. +0x1c8, A' capstone listing :99-116):
     +388 lw a0, 0x30(s1)     the record's failed; RT_TXE states it 0, so the branch below is TAKEN
     +392 ld s5, 0x18(s1)     the record's buffer, want
     +396 beqz a0, +412       taken
     (+400 .. +408 is the refused path's free (want) and `mv s5, zero`: NOT REACHED from RT_TXE, whose record field
      failed is 0. The cut deleted its arms, so this stretch never frees.)
     +412 .. +436 sb zero, 4(s9) .. sb zero, 10(s9)   back's shadow bytes 4 .. 10 := 0 (rtt_back)
     +440 auipc s11, 0x559 ; +444 lbu a0, -0x5e4(s11) s11 (rtt_s11); a0 := g_own_ran_out, which RT_TXE's ledger
                                                      states 0, so the branch below FALLS THROUGH
     +448 bnez a0, +460       falls through
     +452 jal fuzz_alloc_ran_out ; +456 beqz a0, +740  a0 = the ledger's ran = ri_ran D = 0 (rtt_pre), so TAKEN
                                                       -> RT_CMP
   So F is ONE path. Loads, branches and the call are the closed-slot steps of Rtt102StepKit.v (image-generic) and
   Rtt102FR1KitA.v's two relocated slots; the seven stores are Rtt102FStoresA.v's f_stores, one run of YC1fPx.v's
   paj_run_to_x_invR. AT R: every step is YA0nH.SRr' SEGS RZ_cf (the re-hiding move) and every journal is at
   RZW := YA0nH.wle' SEGS RZ_cf (Rtt102Cut.v rtt_J); fuzz_alloc_ran_out's text stays at the plain SRr, so its post is
   lifted into fr_call_at's callee premise (YA0nH.SRr_SRr' and YCbqG.v apost_base_x_R_lift at YA0nH.wle_wle').
   NO TAGGED PREMISE: the refusal arms are gone from the cut, so the direct free, its room obligation (the earlier
   K0-POS-REFUSED premise) and the whole free-keep are gone with them. The top lemma is rtt_seg_f_A outright, over
   the Section's engine law fold and the kit's fuzz_alloc_ran_out text.
   Numerals: 388 / 392 / 396 / 412 / 440 / 444 / 448 / 452 / 456 / 460 / 740 (DERIVED: byte offsets inside
   round_trip_text, Rtt102Cut RT_TXE / RT_O1 / RT_CMP and the slots between); 24 / 48 (LENGTH: the record's want and
   failed, RT_REC + 0 / + 24); 16 / 12 / 284 (LENGTH: the three branch displacements); 4 .. 11 (LENGTH: back's
   shadow bytes); 10 / 21 / 22 / 25 / 27 / 1 / 0 (WORD: register numbers); 128 / 16 (LENGTH: fs_frame_bytes RT_CID
   and its shadow); 2 ^ 32 / 2 ^ 40 / 2 ^ 47 / 2 ^ 64 (LENGTH). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102FR1Kit Rtt102StepKit Rtt102FR1KitA Rtt102FStoresA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKR := (@STK_round_trip_text prh_img_A).
#[local] Existing Instance prh_img_A.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* the cut's predicates at the Section's float state fx (a bound fxc must not be picked for it) *)
#[local] Notation PRE := (rtt_pre (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx CTX0).
#[local] Notation RJ := (rtt_J (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RCARRY := (rtt_carry (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation RSEG := (rtt_seg (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0).
#[local] Notation AT_TXE := (rtt_at_txe (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_CMP := (rtt_at_cmp (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation POST := (rtt_post (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK).
(* the world relation of the walk's journals (Rtt102Cut.v rtt_J) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* ---- Section hypotheses ---- *)
(* (a) the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x; S10TxString.v:163) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* (a) PRH_Base.v:202 prh_head_wide (`8 <= cf_head`; ONE spelling a walk takes; the preset instance has cf_head = 16):
   the ledger's head word (8 bytes below each harness pointer) lies inside its block, so the seven stores keep it *)
Hypothesis HW : prh_head_wide.
(* (b) the callee's kit text, fuzz_alloc_ran_out (PRH_FnAlloc.v at walkkit-next de5e947c224b), at any float state:
   the call happens at the cut's fxc *)
Hypothesis TFR : forall fx' : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fx' rc cp prh_img_A RL A_prog_listing PA B ARx SK.

Lemma f_sigma : SIGMA AS_round_trip_text = BASE + RTTF_K.
Proof. vm_compute. reflexivity. Qed.
Lemma f_stk : STKR = 27392.
Proof. vm_compute. reflexivity. Qed.
Lemma f_sp1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 192 <= RT_R sp0 <= sp0 - 160 /\ RT_R sp0 mod 32 = 0 /\ (RT_R sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H. unfold RT_R, RT_FRAME.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as Hd.
split; [lia|]. split.
- replace (sp0 - 160 - (sp0 - 160) mod 32) with ((sp0 - 160) / 32 * 32) by lia. apply Z_mod_mult.
- pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd2. rewrite H in Hd2. lia.
Qed.

(* a byte window kept byte for byte keeps its bytes *)
Lemma f_bytes_keep : forall (W W2 : world SEGS) mem mem2 p l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W2) mem2 (p + Z.of_nat j) = aview SEGS (w_H W) mem (p + Z.of_nat j)) ->
  bytes_at W mem p l -> bytes_at W2 mem2 p l.
Proof. intros W W2 mem mem2 p l H Hb. unfold bytes_at in *. exact (ts_garr_av (w_H W) (w_H W2) mem mem2 p l H Hb). Qed.

(* ======================================================================================================== *)
(* ---- FROM +412: the stores, s11, g_own_ran_out's load (0), fuzz_alloc_ran_out (0), and the CMP edge ---- *)
Lemma f_tail : forall D fxc ly S Hp W regs mem md k pos q Lamw peakw cntw ranw wab want cap,
  RSEG RT_CMP AT_CMP -> PRE D ->
  RCARRY D fxc ly S Hp W regs mem md k pos -> rtt_copy_kept D W mem ->
  getr regs 22 = w64 q -> getr regs 21 = w64 want ->
  rtt_led B D ly S Hp W mem Lamw peakw cntw ranw 0 -> rtt_wout B D q Lamw cntw ranw wab ->
  want <> 0 -> bytes_at W mem q (ri_tb D ++ [0]) -> bytes_at W mem want (ri_tb D ++ [0]) ->
  rtt_wblk B D ly S Hp want cap -> Z.of_nat (length (ri_tb D)) < cap ->
  YGcfStr.amem_range8 want (Z.of_nat (length (ri_tb D)) + 1) ->
  cap = last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0 ->
  Permutation (ablocks B ly S) ((want, cap) :: wab) ->
  blocks_bytes S <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) + PRH_FnTx.LIVE_tx ->
  rtt_pos D S (RT_K_R D) -> rtt_wild B D S RTT_WK_T ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (RTTF_K + 412))) mem (YK11.seg_rom SEGS)) md) (POST D).
Proof.
intros D fxc ly S Hp W regs mem md k pos q Lamw peakw cntw ranw wab want cap
  SCMP HP HC HCK R22 R21 (HLED & Hpk) HWOUT Hw0 Hqb Hwb HWB Hcap Hrng Ecap HABw Hbb Hpos Hwild.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & _ & _ & _).
assert (Hran0 : ri_ran D = 0) by (clear -HP; red in HP; tauto).
pose proof HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HNODE & HVIS & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HFR as (Efr & _).
assert (Hin : In (RT_CID, pos) (frames S)) by (rewrite Efr; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md RT_CID pos HAR Hin) as (Fb1 & Fb2 & Fapp).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md RT_CID pos HAR Hin) as (F32 & _).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
rewrite Efs1 in Fb2, Fapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof f_stk as HSTK.
assert (HSTKR : 0 <= @STK_fuzz_alloc_ran_out prh_img_A <= 16384) by (vm_compute; split; discriminate).
destruct (f_sp1 (ri_sp D) Hsp16) as (Hsp1 & Hsp32 & Ho16).
set (sp0 := ri_sp D) in *. set (sp1 := RT_R sp0) in *.
set (F := frame_addr ly RT_CID pos) in *.
pose proof cf_head_nonneg as Hch. pose proof HW as Hw. unfold prh_head_wide in Hw.
(* the store window misses every application byte *)
assert (EA : forall x y len, f_E ly pos x -> in_app y len -> 0 <= len -> ~ (y <= x < y + len)).
{ intros x y len HE Hy Hl Hx. unfold f_E in HE. fold F in HE.
  apply (f_sh_not_app F (x - shadow_addr F) y len Fb1 Fb2 Fapp ltac:(lia) Hy Hl). lia. }
assert (Hincw : incl (ri_Lam D) Lamw).
{ destruct HWOUT as (_ & _ & _ & capw & ELam & _). intros bk Hbk. rewrite ELam. right. exact Hbk. }
apply (f_stores B ARx SK LAWS D fxc ly S Hp W regs mem md k pos _ HC).
intros regs1 mem1 md1 KR HJ1 HMN1 Kf HZ.
(* ---- the keeps of the seven stores ---- *)
assert (KB : forall b m x, In (b, m) (ablocks B ly S) -> b <= x < b + req_size m ->
  aview SEGS (w_H W) mem1 x = aview SEGS (w_H W) mem x).
{ intros b m x Hb Hx.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hb) as (_ & H4096 & Hbc & Happ & _).
  apply Kf; [lia|]. intros HE. exact (EA x b (req_size m) HE Happ ltac:(lia) Hx). }
assert (KI : forall a, in_img SEGS a -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (Hsegs a Ha) as Hl. apply Kf; [lia|].
  unfold f_E. fold F. unfold shadow_addr, SHADOW_OFF. intros HE. lia. }
assert (KP : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; exact (KI a (pst_in_img_K a Ha))).
assert (HK : rtt_kept B ly S W mem ly S W mem1 0 0 (f_E ly pos) []).
{ split; [|split; [|split]].
  - intros a Ha _. apply Kf; [lia|]. unfold f_E. fold F. unfold shadow_addr, SHADOW_OFF. intros HE. lia.
  - intros b m i Hb _ Hi _. apply (KB b m). exact Hb. lia.
  - intros a Ha _ _ _. exact (KI a Ha).
  - intros cid pos' a Hf Ha HE. apply Kf; [|exact HE].
    destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hf) as (G1 & G2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as G3.
    assert (G4 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid)
      by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. unfold shadow_addr, SHADOW_OFF in Ha. destruct Ha; lia. }
assert (HEoff : forall x, f_E ly pos x -> rtt_off D ly S x).
{ intros x HE. split.
  - intros a k0 Hin0 Hx.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HLED (Hincw _ Hin0)) as (Hk0 & Hb & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hb) as (_ & _ & _ & Happ & _).
    assert (Hrq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
    exact (EA x _ _ HE Happ ltac:(lia) Hx).
  - intros cid pos' Hf Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
    destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hf) as (_ & _ & Happ).
    exact (EA x _ _ HE Happ (fs_frame_bytes_nonneg cid) Hz). }
assert (HL1 : prh_ledger B ly S Hp W mem1 Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) 0).
{ apply (prh_ledger_kept_aview B ly S Hp W mem); [exact HLED | exact KP | | intros a k0 _ Hb; exact Hb
    | apply Permutation_refl].
  intros a k0 i Hin0 Hi.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HLED Hin0) as (Hk0 & Hb & _).
  assert (Hrq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
  apply (KB _ _ _ Hb). clear -Hi Hrq Hw Hk0. lia. }
assert (HOWN1 : prh_own W mem1 0) by exact (PRH_Base.prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ HL1).
assert (HCR1 : rtt_cregs B D ly regs1 pos).
{ unfold rtt_cregs in *.
  rewrite (KR 2%bv), (KR 8%bv), (KR 9%bv), (KR 18%bv), (KR 19%bv), (KR 20%bv), (KR 25%bv), (KR 26%bv), (KR 3%bv),
    (KR 4%bv) by (cbv; tauto). exact HCR. }
(* the stores keep S: RJ at S is RJc at the call state S *)
assert (HC1 : RCARRY D fxc ly S Hp W regs1 mem1 md1 k pos)
  by exact (rtt_carry_keep B ARx SK CTX0 LAWS pst_not_ro_K rtt_stkr_A D fxc ly S Hp W regs mem md k pos
    ly S Hp W regs1 mem1 md1 k 0 0 (f_E ly pos) [] Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) 0 Lamw peakw cntw
    SIZE_MAXZ ranw (ri_most D) 0 HP HC (rtt_Jc_of_J B ARx SK D ly S Hp W mem1 md1 k pos HJ1) eq_refl HK ltac:(lia)
    ltac:(intros a Ha; inversion Ha) HEoff HLED Hincw HL1 Hincw HCR1 HMN1 HROOM).
assert (HCK1 : rtt_copy_kept D W mem1)
  by exact (rtt_copy_keep B ARx SK CTX0 D fxc ly S Hp W regs mem md k pos ly S W mem1 0 0 (f_E ly pos) [] HP HC HK
    HEoff HCK).
assert (HBK1 : rtt_back ly W mem1 pos).
{ unfold rtt_back, range_addressable. fold F. intros x Hx. unfold RT_BACK in Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  assert (Hs : SHADOW_OFF + x / 8 = shadow_addr F + (x - F) / 8).
  { unfold shadow_addr. assert (EF : F = F / 8 * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
    replace x with ((x - F) + F / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  rewrite Hs. apply HZ. lia. }
assert (KBc : forall b m x, In (b, m) (ablocks B ly S) -> b <= x < b + req_size m ->
  aview SEGS (w_H W) mem1 x = aview SEGS (w_H W) mem x) by exact KB.
pose proof HC1 as (_ & _ & _ & _ & _ & _ & HROD1 & _).
(* +440 auipc s11, 0x559 *)
eapply (fr_auipc (fx := fxc) W regs1 mem1 md1 _ (rtt_w_A (RTTF_K + 440)) (RTTF_K + 440) 27%bv
          (rtt_auipc_imm_A (RTTF_K + 440)) 27%bv);
  [apply rtt_w_A_ok; unfold RTTF_K; vm_compute; discriminate
  | apply rtt_auipc_dec_A; unfold RTTF_K; vm_compute; reflexivity | reflexivity
  | vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate | unfold RTTF_K; vm_compute; reflexivity |].
intros mat1.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regs2 := r); set (md2 := m) end.
assert (S11 : rtt_s11 regs2).
{ unfold rtt_s11, regs2. rewrite getr_same by reg_neq_tac. apply bv_eq. vm_compute. reflexivity. }
(* +444 lbu a0, -0x5e4(s11): g_own_ran_out, which the cut states 0 *)
eapply (fr_lbu (fx := fxc) W regs2 mem1 md2 _ (rtt_w_A (RTTF_K + 444)) (RTTF_K + 444) 10%bv 27%bv
          (rtt_load_imm_A (RTTF_K + 444)) 10%bv 27%bv (@pi_g_own_ran_out prh_img_A) 0);
  [apply rtt_w_A_ok; unfold RTTF_K; vm_compute; discriminate
  | apply (rtt_load_dec_A _ SZ1 false); unfold RTTF_K; vm_compute; reflexivity | reflexivity | reflexivity
  | unfold regs2; rewrite getr_same by reg_neq_tac; apply bv_eq; vm_compute; reflexivity
  | exact (proj1 HOWN1)
  | vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate | unfold RTTF_K; vm_compute; reflexivity |].
intros mat2.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regs3 := r); set (md3 := m) end.
assert (HJ3 : RJ D ly S Hp W mem1 md3 k pos).
{ unfold md3, md2. apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW).
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ1. }
assert (HCR3 : rtt_cregs B D ly regs3 pos).
{ unfold regs3, regs2. apply rtt_cregs_upd; try reg_neq_tac. apply rtt_cregs_upd; try reg_neq_tac. exact HCR1. }
assert (K3 : forall r : bv 5, r <> 10%bv -> r <> 27%bv -> getr regs3 r = getr regs1 r).
{ intros r N10 N27. unfold regs3, regs2. rewrite getr_other by exact N10. rewrite getr_other by exact N27. reflexivity. }
assert (T22 : getr regs3 22 = w64 q) by (rewrite K3 by reg_neq_tac; rewrite KR by (cbv; tauto); exact R22).
assert (T21 : getr regs3 21 = w64 want) by (rewrite K3 by reg_neq_tac; rewrite KR by (cbv; tauto); exact R21).
assert (T10 : getr regs3 10 = Z_to_bv 64 (0 mod 2 ^ 8)) by (unfold regs3; rewrite getr_same by reg_neq_tac; reflexivity).
(* +448 bnez a0: own = 0, so it falls through *)
eapply (rtt_bnez_ft (fx := fxc) W regs3 mem1 md3 _ (RTTF_K + 448) 10%bv 12);
  [vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate | unfold RTTF_K; vm_compute; reflexivity
  | rewrite T10; vm_compute; reflexivity |].
intros mat3.
(* +452 jal fuzz_alloc_ran_out *)
eapply (rtt_jal_pcall (fx := fxc) W _ mem1 _ _ (RTTF_K + 448 + 4) AS_fuzz_alloc_ran_out);
  [vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate | unfold RTTF_K; vm_compute; reflexivity |].
intros mat4.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsF := r); set (md4 := m) end.
assert (HJm : RJ D ly S Hp W mem1 md4 k pos).
{ unfold md4. apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW).
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ3. }
pose proof HJm as (HARm & _).
assert (FK : forall r : bv 5, r <> 1%bv -> getr regsF r = getr regs3 r).
{ intros r H1. unfold regsF. rewrite getr_other by exact H1. reflexivity. }
assert (F2 : spZ regsF = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite FK, K3, KR by (first [reg_neq_tac | cbv; tauto]). rewrite R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (F8 : s0Z regsF = sp0).
{ unfold s0Z. rewrite FK, K3, KR by (first [reg_neq_tac | cbv; tauto]). rewrite R8. unfold w64.
  apply unsigned_lit_small. lia. }
assert (F1 : getr regsF 1 = Z_to_bv 64 (BASE + (RTTF_K + 456))).
{ unfold regsF. rewrite getr_same by reg_neq_tac. f_equal; lia. }
assert (HRA : YK0s.ret_ok (Z_to_bv 64 (BASE + (RTTF_K + 456)))).
{ apply (ret_ok_codeptr_v (PI := PA)); unfold RTTF_K; vm_compute; [split; [discriminate | reflexivity] | reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (RTTF_K + 456)))) by (vm_compute; discriminate).
assert (HRAc : bv_unsigned (Z_to_bv 64 (BASE + (RTTF_K + 456))) < YM05.alloc_ceiling).
{ assert (E : bv_unsigned (Z_to_bv 64 (BASE + (RTTF_K + 456))) < 2 ^ 32) by (vm_compute; reflexivity). lia. }
destruct (rtt_chain_at B ARx SK CTX0 rtt_stkr_A D ly S Hp W mem1 md4 k pos sp1 HP HJm
  (proj1 (proj2 (proj2 (proj2 HC1)))) ltac:(lia)) as (ch1 & Hach & Hch1).
(* the call is made on RJ: the journal from the entry with its depot moved to the call state S's *)
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (fr_call_at B ARx SK LAWS W regsF mem1 STKR sp0 (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D))
    (ri_Hp D) (ri_W D) (ri_mem D)
    (ri_md D) [(RT_CID, pos)] ly S Hp md4 k (@STK_fuzz_alloc_ran_out prh_img_A) [] (sp1 - sp0)
    (Z_to_bv 64 (BASE + (RTTF_K + 456))) ch1 (SIGMA AS_fuzz_alloc_ran_out)).
  - exact HJm.
  - exact F2.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - rewrite FK, K3, KR by (first [reg_neq_tac | cbv; tauto]). exact R3.
  - rewrite FK, K3, KR by (first [reg_neq_tac | cbv; tauto]). exact R4.
  - exact F1.
  - exact HRA.
  - exact HRA4.
  - replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite F8. exact Hach.
  - (* The kit's text is at the plain SRr: lift it, and its post's journal (at wle) into RZW *)
    intros HAF.
    pose proof (TFR fxc ly S Hp W regsF mem1 md4 ch1 Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) 0) as HT.
    unfold fpostm, fpost in HT.
    eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    + apply YA0nH.SRr_SRr'. apply HT.
      * split; [exact HAF|]. split; [exact HROD1|]. split.
        -- rewrite F2. replace (sp0 + (sp1 - sp0)) with sp1 by lia. rewrite Eshi. lia.
        -- split; [unfold raZ; rewrite F1; exact HRAc | exact (proj1 HFX)].
      * exact HL1.
    + intros W' c' _ HQ'.
      exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARx RZW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
        _ _ _ _ _ _ _ _ _ _ _ _ HQ').
  - intros a Ha. exfalso. destruct Ha as (rg & [] & _). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs4 & mem3 & md5 & k1 & -> & HJ5 & HJc & HP3 & (HQ & HMN3)).
destruct HQ as (HRL3 & R10 & EHp3 & ES3 & Eab3 & HL3). subst Hp3 S3.
pose proof (rtt_kept_of_journal B ARx SK _ _ [] ly S Hp W mem1 md4 ly3 S Hp W3 mem3 md5 k1 HJc sink_closed_nil) as HK2.
assert (HEoff2 : forall x, inFP [] x -> rtt_off D ly S x) by (intros x (rg & [] & _)).
destruct (rtt_fa_eq B ARx SK D ly3 S Hp W3 mem3 md5 (k + k1) pos HJ5) as (Fa3 & _).
destruct (rtt_fa_eq B ARx SK D ly S Hp W mem1 md4 k pos HJm) as (Fac & _).
assert (KP3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr regsF r)
  by (intros r Hr; exact (ts_ap _ _ r HP3 Hr)).
assert (HCR4 : rtt_cregs B D ly3 regs4 pos).
{ unfold rtt_cregs. rewrite Fa3. unfold rtt_cregs in HCR3. rewrite <- Fac.
  rewrite !KP3 by ts_cs. rewrite !FK by reg_neq_tac. exact HCR3. }
assert (HC2 : RCARRY D fxc ly S Hp W regs3 mem1 md4 k pos).
{ apply (rtt_carry_md B ARx SK D fxc ly S Hp W regs3 mem1 md1); [|exact HJm].
  exact (rtt_carry_regs B ARx SK D fxc ly S Hp W regs1 mem1 md1 k pos regs3 HC1 HCR3). }
(* the callee keeps S (S' = S): the caller journal HJ5 is RJc at the call state S *)
assert (HC4 : RCARRY D fxc ly3 S Hp W3 regs4 mem3 md5 (k + k1) pos)
  by exact (rtt_carry_keep B ARx SK CTX0 LAWS pst_not_ro_K rtt_stkr_A D fxc ly S Hp W regs3 mem1 md4 k pos
    ly3 S Hp W3 regs4 mem3 md5 (k + k1) _ _ _ PST Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) 0 Lamw peakw cntw
    SIZE_MAXZ ranw (ri_most D) 0 HP HC2 HJ5 eq_refl HK2 ltac:(lia) (fun a Ha => Ha) HEoff2 HL1 Hincw HL3 Hincw HCR4
    HMN3 HROOM).
assert (HBK4 : rtt_back ly3 W3 mem3 pos).
{ apply (rtt_back_keep B ARx SK LAWS D fxc ly S Hp W regs3 mem1 md4 k pos ly3 S W3 mem3 _ _ _ PST HC2 HK2).
  - intros x (rg & [] & _).
  - intros cid pos'. rewrite Fa3. exact (eq_sym (Fac cid pos')).
  - exact HBK1. }
assert (HCK4 : rtt_copy_kept D W3 mem3)
  by exact (rtt_copy_keep B ARx SK CTX0 D fxc ly S Hp W regs3 mem1 md4 k pos ly3 S W3 mem3 _ _ _ PST HP HC2 HK2
    HEoff2 HCK1).
pose proof HK2 as (_ & K2c & _ & _).
assert (KBc3 : forall b m x, In (b, m) (ablocks B ly S) -> b <= x < b + req_size m ->
  aview SEGS (w_H W3) mem3 x = aview SEGS (w_H W) mem1 x).
{ intros b m x Hb Hx. replace x with (b + (x - b)) by lia.
  apply (K2c b m (x - b) Hb); [rewrite Eab3; exact Hb | lia | intros (rg & [] & _)]. }
assert (T22' : getr regs4 22 = w64 q) by (rewrite KP3 by ts_cs; rewrite FK by reg_neq_tac; exact T22).
assert (T21' : getr regs4 21 = w64 want) by (rewrite KP3 by ts_cs; rewrite FK by reg_neq_tac; exact T21).
assert (S11' : rtt_s11 regs4).
{ unfold rtt_s11. rewrite KP3 by ts_cs. rewrite FK by reg_neq_tac. unfold regs3. rewrite getr_other by reg_neq_tac.
  exact S11. }
(* +456 beqz a0: the ledger's ran is ri_ran D = 0, so it is TAKEN -> RT_CMP *)
destruct HWOUT as (Hq0 & Ecnt & Eran & capw & ELam & Hnew & Ewab & Hlenw & Hcapw & Ecw).
assert (Er0 : ranw = 0) by lia.
eapply (rtt_beqz_tk (fx := fxc) W3 regs4 mem3 md5 _ (RTTF_K + 456) 10%bv 284 (SIGMA AS_round_trip_text + RT_CMP));
  [vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate | unfold RTTF_K; vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite R10, Er0; vm_compute; reflexivity |].
intros mat5.
apply (SCMP D HP fxc ly3 S Hp W3 regs4 mem3 _ (k + k1) pos).
assert (Hqb' : In (q - cf_head, capw + cf_head) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HABw)). rewrite Ewab. right. left. reflexivity. }
assert (Hwb' : In (want, cap) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HABw)). left. reflexivity. }
pose proof HWB as (Hcap0 & Hwin & Hwnew & Hwhp & Htx).
assert (Hrq : 1 <= req_size cap /\ cap <= req_size cap) by (apply req_size_pos; lia).
assert (Hrqw : 1 <= req_size (capw + cf_head) /\ capw + cf_head <= req_size (capw + cf_head))
  by (apply req_size_pos; lia).
split.
{ apply (rtt_carry_md B ARx SK D fxc ly3 S Hp W3 regs4 mem3 md5); [exact HC4|].
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ5. }
split; [exact HBK4|]. split; [exact S11'|]. split; [exact HCK4|].
exists q, capw, peakw, want, cap. cbv zeta.
split; [exact T22'|]. split; [exact T21'|]. split; [exact Hq0|]. split; [exact Hw0|].
split; [rewrite <- ELam, <- Ecnt, <- Eran; split; [exact HL3 | exact Hpk]|].
split; [exact Hnew|]. split; [exact Hlenw|]. split; [exact Hcapw|].
split.
{ apply (f_bytes_keep W W3 mem mem3); [|exact Hqb].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite (KBc3 _ _ _ Hqb') by (clear -Hj Hlenw Hrqw Hch; lia).
  apply (KB _ _ _ Hqb'). clear -Hj Hlenw Hrqw Hch; lia. }
split.
{ apply (f_bytes_keep W W3 mem mem3); [|exact Hwb].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite (KBc3 _ _ _ Hwb') by (clear -Hj Hcap Hrq; lia).
  apply (KB _ _ _ Hwb'). clear -Hj Hcap Hrq; lia. }
split.
{ split; [exact Hcap0|]. split; [rewrite Eab3; exact Hwb'|]. split; [exact Hwnew|]. split; [exact Hwhp | exact Htx]. }
split; [exact Hcap|]. split; [exact Hrng|]. split; [exact Ecap|]. split; [exact Ecw|].
split; [rewrite Eab3, <- Ewab; exact HABw|].
(* the wild budget: F never changes S, so RT_TXE's rtt_wild D S RTT_WK_T is RT_CMP's *)
split; [exact Hbb|]. split; [exact Hpos | exact Hwild].
Qed.

(* ======================================================================================================== *)
(* ---- THE HEAD, from RT_TXE: the record's failed (0) and want, and the taken branch to +412 ---- *)
Lemma f_main : RSEG RT_CMP AT_CMP -> RSEG RT_TXE AT_TXE.
Proof.
intros SCMP D HP fxc ly S Hp W regs mem md k pos HT.
pose proof HT as (HC & R21p & HCK & (q & Lamw & peakw & cntw & ranw & wab & want & n & cap & R22 & HLED &
  HWOUT & Hqb & HREC & Hw0 & En & Hwb & HWB & Hcap & Hrng & Ecap & HABw & Hbb & Hpos & Hwild)).
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof (rtt_pre_facts B ARx CTX0 D HP) as (HAR0 & Hsp0 & Hsp16 & H64 & HDL & _ & _ & _).
pose proof HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HNODE & HVIS & _).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HJ as (HAR & Hly & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof f_stk as HSTK.
destruct (f_sp1 (ri_sp D) Hsp16) as (Hsp1 & Hsp32 & Ho16).
set (sp0 := ri_sp D) in *. set (sp1 := RT_R sp0) in *.
pose proof HREC as (Vb & _ & _ & Vf).
unfold RT_REC in Vb, Vf.
rewrite f_sigma. unfold RT_TXE. replace (BASE + RTTF_K + 388) with (BASE + (RTTF_K + 388)) by lia.
(* +388 lw a0, 0x30(s1) *)
eapply (rtt_lw (fx := fxc) W regs mem md _ (RTTF_K + 388) 10%bv 9%bv 48 (sp1 + 24 + 24) 0);
  [vm_compute; reflexivity | vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate
  | unfold RTTF_K; vm_compute; reflexivity
  | rewrite R9; unfold v_addi, w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | exact Vf |].
intros mat1.
(* +392 ld s5, 0x18(s1) *)
eapply (rtt_ld (fx := fxc) W _ mem _ _ (RTTF_K + 388 + 4) 21%bv 9%bv 24 (sp1 + 24) want);
  [vm_compute; reflexivity | vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate
  | unfold RTTF_K; vm_compute; reflexivity
  | rewrite getr_other by reg_neq_tac; rewrite R9; unfold v_addi, w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | exact Vb |].
intros mat2.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regs1 := r); set (md1 := m) end.
assert (HJ1 : RJ D ly S Hp W mem md1 k pos).
{ unfold md1. apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW).
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ. }
assert (K1 : forall r : bv 5, r <> 10%bv -> r <> 21%bv -> getr regs1 r = getr regs r).
{ intros r N10 N21. unfold regs1. rewrite getr_other by exact N21. rewrite getr_other by exact N10. reflexivity. }
assert (HCR1 : rtt_cregs B D ly regs1 pos).
{ unfold regs1. apply rtt_cregs_upd; try reg_neq_tac. apply rtt_cregs_upd; try reg_neq_tac. exact HCR. }
assert (HC1 : RCARRY D fxc ly S Hp W regs1 mem md1 k pos).
{ apply (rtt_carry_md B ARx SK D fxc ly S Hp W regs1 mem md); [|exact HJ1].
  exact (rtt_carry_regs B ARx SK D fxc ly S Hp W regs mem md k pos regs1 HC HCR1). }
assert (T21 : getr regs1 21 = w64 want) by (unfold regs1; rewrite getr_same by reg_neq_tac; reflexivity).
assert (T22 : getr regs1 22 = w64 q) by (rewrite K1 by reg_neq_tac; exact R22).
assert (T10 : getr regs1 10 = v_lw (Z_to_bv 64 (0 mod 2 ^ 32))).
{ unfold regs1. rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity. }
(* +396 beqz a0: the record's failed is 0, so it is TAKEN, to +412 *)
eapply (rtt_beqz_tk (fx := fxc) W regs1 mem md1 _ (RTTF_K + 396) 10%bv 16 (BASE + (RTTF_K + 412)));
  [vm_compute; reflexivity | unfold RTTF_K; vm_compute; discriminate | unfold RTTF_K; vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite T10; vm_compute; reflexivity |].
intros mat3.
apply (f_tail D fxc ly S Hp W regs1 mem _ k pos q Lamw peakw cntw ranw wab want cap SCMP HP).
- apply (rtt_carry_md B ARx SK D fxc ly S Hp W regs1 mem md1); [exact HC1|].
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW). exact HJ1.
- exact HCK.
- exact T22.
- exact T21.
- exact HLED.
- exact HWOUT.
- exact Hw0.
- exact Hqb.
- exact Hwb.
- exact HWB.
- exact Hcap.
- exact Hrng.
- exact Ecap.
- exact HABw.
- exact Hbb.
- exact Hpos.
- exact Hwild.
Qed.

(* ---- THE STRETCH ---- *)
Theorem rtt_seg_f_A : @RTT_SEG_F fx rc ci cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK CTX0.
Proof. exact f_main. Qed.

End f.

Print Assumptions rtt_seg_f_A.
Set Printing Implicit.
Check @rtt_seg_f_A.
Unset Printing Implicit.
