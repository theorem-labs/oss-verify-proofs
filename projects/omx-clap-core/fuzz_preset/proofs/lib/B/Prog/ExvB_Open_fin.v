(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit 4f18c75d4900 (base cold/h-rw-pre-7-b-ex_value-rebind): EXB carries exv_rm; the two
   ends take the memnorm keep from the entry memory at the end memory (the runs' _inv P) and hand it to exv_kt.
   Does not rest on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CI (container open, B entry + 0x374 .. + 0x530):
   the segment's INTERNAL cut and the concrete ends of its symbolic stretches.
   - CUT_CM: the merge point after the type check, entry + 0x440 (B `addi a1, a1, 1` before the store of in->p): the
     depth stored (dep + 1 <= 32), in->differs dlc and the node still compared vv (exv_dif at acc = []), the spills of
     B 0x838a0 .. 0x83968 (closer at 64(s1), q + 16 at 96(s1), its shadow at 104(s1), the frame at 120(s1)) and 144(s1) /
     152(s1). The front lemma (CI -> CX | CM) and the call lemma (CM -> CC | CL) meet here.
   - exo_cx_fin: a stretch from CI that stored dep + 1 = 33 into in->depth ends in CX with s5 = -1: the refused arm
     (exv_V E = None by the grammar's depth check, exv_V_deep), the cursor at x0 + i1, depth 33, differs dl.
   - exo_cm_fin: a stretch from CI that reached entry + 0x440 ends in CUT_CM.
   Both carry EXB by exv_kt (ExvB_Open_kt.v). Rule 24: proves no function (kind: segment lemma). Numerals: 0x374,
   0x440, 0xa7c (DERIVED: cut offsets, B entry + offset from the internal file neutral_dis.py on the record f8f98a95bc52), 33 / 32 (WORD:
   depth bound), 91 / 93 / 123 / 125 (WORD: ASCII), 64, 96, 104, 120, 144, 152, 176 (LENGTH: slot offsets of B's
   code), 8, 16, 20, 24, 32, 36, 40 (LENGTH: struct ex fields), 2 ^ 47, 2 ^ 64 (LENGTH), 2, 3, 4, 8, 9, 11, 18-27
   (WORD: register numbers). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YK1b YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Open_pure ExvB_Open_kt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* the internal cut at entry + 0x440 *)
Definition CUT_CM (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c vv dlc : Z),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 ->
  prhex_cur Wc memc q (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  (dlc = 0 \/ dlc = 1) -> exv_dif E o vv dlc [] ->
  getr regs 11 = w64 (e_x0 E + exv_i1 E) -> getr regs 27 = w64 c ->
  getr regs 20 = w64 (shadow_addr q) -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spill E Wc memc 64 (if o then 125 else 93) -> exv_spill E Wc memc 96 (q + 16) ->
  exv_spill E Wc memc 104 (shadow_addr (q + 16)) -> exv_spill E Wc memc 120 (frame_addr lyc 1 pos) ->
  exv_spill E Wc memc 144 (shadow_addr q) -> exv_spill E Wc memc 152 vv ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x440) regs memc mdc) (EXV_POST B ARx SK E).

(* the internal cut at entry + 0x460 (B 0x8398c), ex_ws's return site: in->p at the cursor ip after the whitespace that
   follows the opening byte, the rest as at CUT_CM *)
Definition CUT_CR (n : nat) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c vv dlc : Z),
  let o := (c =? 123) in
  let q := e_q E in
  let ip := exv_len E - Z.of_nat (length (PjGrammar.skip (skipn (S (Z.to_nat (exv_i1 E))) (e_x E)))) in
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 ->
  prhex_cur Wc memc q (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  (dlc = 0 \/ dlc = 1) -> exv_dif E o vv dlc [] ->
  getr regs 27 = w64 c ->
  getr regs 20 = w64 (shadow_addr q) -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spill E Wc memc 64 (if o then 125 else 93) -> exv_spill E Wc memc 96 (q + 16) ->
  exv_spill E Wc memc 104 (shadow_addr (q + 16)) -> exv_spill E Wc memc 120 (frame_addr lyc 1 pos) ->
  exv_spill E Wc memc 144 (shadow_addr q) -> exv_spill E Wc memc 152 vv ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x460) regs memc mdc) (EXV_POST B ARx SK E).

Hypothesis HYP : EXV_HYP B ARx SK.

(* a byte of the cursor outside its three FP cells is not in exv_FP (the scratch is apart from the cursor) *)
Lemma exo_cur_notFP : forall E x,
  (e_scr E + exv_len E + 1 <= e_q E \/ e_q E + 40 <= e_scr E) ->
  e_q E <= x < e_q E + 40 -> ~ (e_q E <= x < e_q E + 8) -> ~ (e_q E + 16 <= x < e_q E + 20) ->
  ~ (e_q E + 32 <= x < e_q E + 36) -> ~ inFP (exv_FP E) x.
Proof.
intros E x Hsq Hx H1 H2 H3 (r & Hr & Hrx). unfold exv_FP in Hr. cbn [In] in Hr.
repeat destruct Hr as [<-|Hr]; cbn [fst snd] in Hrx; try lia.
Qed.

(* the cursor cells the segment does not write keep their values *)
Lemma exo_cur_kept : forall E (Wc : world rsegs) memc memc' o (n : nat) v,
  (e_scr E + exv_len E + 1 <= e_q E \/ e_q E + 40 <= e_scr E) ->
  exv_sp E <= e_q E -> e_q E + 40 <= 2 ^ 47 -> exv_s1 E + 176 <= exv_sp E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (o = 8 /\ n = 8%nat \/ o = 24 /\ n = 8%nat) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E + o) n v ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E + o) n v.
Proof.
intros E Wc memc memc' o n v Hsq Hspq Hq47 Hs1 HK Ho HV.
assert (Hsp0 : 0 <= exv_sp E) by (unfold exv_sp, spZ; pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)); lia).
destruct Ho as [(-> & ->)|(-> & ->)];
  (eapply exk_val_kept; [|exact HV]); intros x Hx; change (Z.of_nat 8) with 8 in Hx;
  (apply HK; [lia | lia |]); intros (Hf & _); revert Hf; apply (exo_cur_notFP E x Hsq); lia.
Qed.

(* a stretch whose write windows are a frame window [s1 + lo, s1 + hi) and the three FP cursor cells meets exv_kt's
   keep premise *)
Lemma exo_kept_T1 : forall E (Wc : world rsegs) memc memc' lo hi,
  exv_sp E - exv_STK E <= exv_s1 E + lo -> hi <= 176 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((exv_s1 E + lo <= a < exv_s1 E + hi) \/ (e_q E <= a < e_q E + 8) \/ (e_q E + 16 <= a < e_q E + 20) \/
        (e_q E + 32 <= a < e_q E + 36)) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
    ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
    aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a.
Proof.
intros E Wc memc memc' lo hi Hlo Hhi HK a Ha H1 H2. apply HK; [exact Ha|].
intros [Hw|[Hw|[Hw|Hw]]]; [apply H1; lia | | |]; apply H2; (split; [|lia]); unfold exv_FP.
- exists (e_q E, e_q E + 8). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exists (e_q E + 16, e_q E + 20). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
- exists (e_q E + 32, e_q E + 36). split; [right; right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* the CX end of a stretch from CI at depth 32: the refused arm *)
Lemma exo_cx_fin : forall n, CUT_CX (fx := fx) B ARx SK n ->
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos c (regs' : bvmap 5 word) memc' mdc',
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  getr regs 21 = w64 (-1) -> e_dep E = 32 ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 21]%bv -> getr regs' r = getr regs r) ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E) 8 (e_x0 E + exv_i1 E) ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E + 16) 4 33 ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E + 32) 4 (e_dl E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0xa7c) regs' memc' mdc') (EXV_POST B ARx SK E).
Proof.
intros n HX E lyc Sc Hpc Wc regs memc mdc k pos c regs' memc' mdc' Hn HPRE HB Hcur Hi1 Hnth Hc R21 Hd HJ' HK HG HMN HR
  V0 V16 V32.
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _ & _ & _ & Hi0 & _ & _ & Hdl & _ & _ & _ & Hsq & _ & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop).
destruct Hwin as (_ & _ & Hdtop & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
destruct Hcur as (_ & C8 & _ & C24 & _).
apply (HX E lyc Sc Hpc Wc regs' memc' mdc' k pos (-1) Hn HPRE).
- apply (exv_kt B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k HPRE HB HJ' HK HG HMN).
  intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
- rewrite (HR 21%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R21.
- exists (exv_i1 E), 33, (e_dl E).
  assert (Hq47 : e_q E + 40 <= 2 ^ 47) by (unfold exv_sp in *; lia).
  assert (Hs1' : exv_s1 E + 176 <= exv_sp E) by lia.
  unfold exv_sp in Hspq.
  split; [split; [exact V0|]; split; [|split; [exact V16|split; [|exact V32]]]|].
  + exact (exo_cur_kept E Wc memc memc' 8 8 _ Hsq Hspq Hq47 Hs1' HK ltac:(left; split; reflexivity) C8).
  + exact (exo_cur_kept E Wc memc memc' 24 8 _ Hsq Hspq Hq47 Hs1' HK ltac:(right; split; reflexivity) C24).
  + split; [exact Hdl|].
    rewrite (exv_V_deep E c _ (exv_skipX E c Hi0 Hi1 Hnth) Hc Hd).
    pose proof (PjGrammar.skip_len (exv_X E)) as Hs.
    pose proof (length_skipn (Z.to_nat (e_i0 E)) (e_x E)) as Hls.
    split; [reflexivity|]. unfold exv_i1, exv_len, exv_X in *. split; [lia | lia].
Qed.

(* the CM end of a stretch from CI below depth 32 *)
Lemma exo_cm_fin : forall n, CUT_CM n ->
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos c vv dlc (regs' : bvmap 5 word) memc' mdc',
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> (dlc = 0 \/ dlc = 1) -> exv_dif E (c =? 123) vv dlc [] ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 11; 27; 20; 22; 23]%bv -> getr regs' r = getr regs r) ->
  getr regs 11 = w64 (e_x0 E + exv_i1 E) -> getr regs 27 = w64 c ->
  getr regs 20 = w64 (shadow_addr q) -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  val_mem rsegs (mrestrict (w_H Wc) memc') q 8 (e_x0 E + exv_i1 E) ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (q + 16) 4 (e_dep E + 1) ->
  val_mem rsegs (mrestrict (w_H Wc) memc') (q + 32) 4 dlc ->
  exv_spill E Wc memc' 64 (if c =? 123 then 125 else 93) -> exv_spill E Wc memc' 96 (q + 16) ->
  exv_spill E Wc memc' 104 (shadow_addr (q + 16)) -> exv_spill E Wc memc' 120 (frame_addr lyc 1 pos) ->
  exv_spill E Wc memc' 144 (shadow_addr q) -> exv_spill E Wc memc' 152 vv ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x440) regs' memc' mdc') (EXV_POST B ARx SK E).
Proof.
intros n HM E lyc Sc Hpc Wc regs memc mdc k pos c vv dlc regs' memc' mdc' q Hn HPRE HB Hcur Hi1 Hnth Hc Hd Hdlc Hdif
  HJ' HK HG HMN HR R11 R27 R20 R22 R23 V0 V16 V32 S64 S96 S104 S120 S144 S152.
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _ & _ & _ & Hi0 & _ & _ & Hdl & _ & _ & _ & Hsq & _ & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop).
destruct Hwin as (_ & _ & Hdtop & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
destruct Hcur as (_ & C8 & _ & C24 & _).
assert (Hq47 : e_q E + 40 <= 2 ^ 47) by (unfold exv_sp in *; lia).
assert (Hs1' : exv_s1 E + 176 <= exv_sp E) by lia.
unfold exv_sp in Hspq.
assert (INR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 11; 27; 20; 22; 23]%bv -> getr regs' r = getr regs r)
  by exact HR.
apply (HM E lyc Sc Hpc Wc regs' memc' mdc' k pos c vv dlc Hn HPRE).
- apply (exv_kt B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k HPRE HB HJ' HK HG HMN).
  intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
- exact Hi1.
- exact Hnth.
- exact Hc.
- exact Hd.
- split; [exact V0|]. split; [exact (exo_cur_kept E Wc memc memc' 8 8 _ Hsq Hspq Hq47 Hs1' HK ltac:(left; split; reflexivity) C8)|].
  split; [exact V16|]. split; [exact (exo_cur_kept E Wc memc memc' 24 8 _ Hsq Hspq Hq47 Hs1' HK ltac:(right; split; reflexivity) C24)|].
  exact V32.
- exact Hdlc.
- exact Hdif.
- rewrite (INR 11%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R11.
- rewrite (INR 27%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R27.
- rewrite (INR 20%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R20.
- rewrite (INR 22%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R22.
- rewrite (INR 23%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R23.
- exact S64.
- exact S96.
- exact S104.
- exact S120.
- exact S144.
- exact S152.
Qed.
End c.
