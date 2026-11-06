(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 613 of its 653 lines of code are new or changed and 156 lines of the source are left out. *)
(* fuzz_preset, the IMAGE-GENERIC KIT of lane RttFR1 (WalkRtt102 for the text owner) for round_trip_text's stretches over the
   cut layer Rtt102Cut.v, generic over the listing, its image and the PrhImg instance ({L} {PL} {PA} {PI}): image A'
   instantiates it in Rtt102R1A.v / Rtt102FA.v (with Rtt102FR1KitA.v's concrete steps), image B' in its own files.
   rule 24: proves no function (kind: segment lemma helpers); the function-level lookup is the brief's
   (proof-index round_trip_text EXIT=0, no released ASan proof).
   CONTENTS.
   pure helpers: fr_rdword_of_val_mem (YCem.v:101), fr_fpchain_keep / fr_unwind_eq (H5RttS4.v, the H2H5 walk head
     1934271f1f40), fr_aview_of_apresent, fr_pairwise_app / fr_pairwise_in_map.
   Section k (generic):
   2. fr_call_at: a call of a program text from a concrete state (YCbqGcall.v:107 aj_call_x_sp without its symbolic-state
      premise, proof transcribed).
   3. (fr_free_null_at, free (NULL) at the free wrapper, is DELETED at the batch kit's cut: its one consumer, the r = 1 stretch R1,
      went with RT_R1, and no file uses it.)
   4. rtt_chain_at / rtt_trace_at: round_trip_text's frame-pointer chain and allocator trace at a call in its body
      (H5RttS4.v s4_chain / s4_trace_in, re-cut to Rtt102Cut's rtt_pre / rtt_saved and PRH_Base.v's prh_univ_closure).
   5. keeps: rtt_kept (what a callee's journal or a runtime call's acall_kept_x keeps), rtt_off (the bytes a call's write
      set must miss), rtt_carry_keep (the cut's carried state across the call), rtt_copy_keep, rtt_back_keep, the alloc.c
      flag cells (rtt_own_kept / rtt_most_kept), rtt_free_keep (everything across a direct free).
   The image facts a caller supplies (Section hypotheses pst_in_img, pst_not_ro, RTT_FP, STKR_frame) are computations on
   the concrete image: A' discharges them in Rtt102FR1KitA.v.
   Numerals: 8 / 16 (LENGTH: word, stack alignment), 104 (LENGTH: the 13 saves below sp0), 192 / 16 (LENGTH: the bounds of
   sp1 = RT_R sp0 below sp0: 160 + 31, 16), 128 (LENGTH: fs_frame_bytes RT_CID, by computation), 2 ^ 40 / 2 ^ 47 / 2 ^ 64
   (LENGTH). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure helpers ---- *)
(* YCem.v:101 rdword_of_val_mem, restated (YCem Requires cgif's image files) *)
Lemma fr_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* H5RttS4.v s4_fpchain_keep *)
Lemma fr_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r.
  rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12].
  apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

(* H5RttS4.v s4_flat_chain / s4_unwind_eq, at PRH_Base.v's prh_trace *)
Lemma fr_flat_chain : forall pc0 ch,
  flat_map (fun x : Z * Z * Z => match x with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch
  = flat_map (fun ra => if ra =? pc0 then [] else [ra]) (spine ch).
Proof.
intros pc0 ch. induction ch as [|[[f a] g] ch IH]; [reflexivity|].
unfold spine in *. cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.
Lemma fr_unwind_eq : forall pc0 sp2 r sp0 ch,
  unwind_of_chain pc0 ((sp2, r, sp0) :: ch) = prh_trace pc0 r (spine ch).
Proof.
intros pc0 sp2 r sp0 ch. unfold unwind_of_chain, prh_trace.
cbn [flat_map]. rewrite fr_flat_chain. reflexivity.
Qed.

(* a present byte is visible *)
Lemma fr_aview_of_apresent : forall segs (H : word -> bool) mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.


(* ---- 5. keeps ---- *)
(* pairwise facts (YG0f.v pairwise) *)
Lemma fr_pairwise_app : forall {X} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z t IH]; intros l2 x y Hp Hx Hy; [destruct Hx|].
cbn [app pairwise] in Hp. destruct Hp as [Hz Hp]. destruct Hx as [<- | Hx].
- rewrite Forall_forall in Hz. apply Hz. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.
Lemma fr_pairwise_in_map : forall {X Y} (R : Y -> Y -> Prop) (f : X -> Y) (l : list X) u v,
  pairwise R (map f l) -> In u l -> In v l -> u <> v -> R (f u) (f v) \/ R (f v) (f u).
Proof.
intros X Y R f l. induction l as [|z t IH]; intros u v Hp Hu Hv Hne; [destruct Hu|].
cbn [map pairwise] in Hp. destruct Hp as [Hz Hp]. rewrite Forall_forall in Hz.
destruct Hu as [<- | Hu], Hv as [<- | Hv].
- exfalso. exact (Hne eq_refl).
- left. apply Hz. apply in_map. exact Hv.
- right. apply Hz. apply in_map. exact Hu.
- exact (IH u v Hp Hu Hv Hne).
Qed.

(* ======================================================================================================== *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {L : ptable asym} {PL : PAListing L} {PA : PAImg L} {PI : PrhImg}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation VAL := (@pa_val _ L PA).
#[local] Notation SIGMA := (@pa_sigma _ L PA).
#[local] Notation BASE := (@pa_val _ L PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ L PA).
#[local] Notation RHI := (@pa_relro_hi _ L PA).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation STKR := (@STK_round_trip_text PI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* every journal of the walk is at RZW := YA0nH.wle' SEGS RZ_cf (Rtt102Cut.v's rtt_J) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the cut's predicates at the Section's float state fx (a bound fxc must not be picked for it) *)
#[local] Notation PRE := (rtt_pre (fx := fx) (PI := PI) (L := L) (PA := PA) B ARx CTX0).
#[local] Notation RJ := (rtt_J (PI := PI) (L := L) (PA := PA) B ARx SK).
(* the journal a call rule returns from RJ at the call state Sc *)
#[local] Notation RJc := (rtt_Jc (PI := PI) (L := L) (PA := PA) B ARx SK).
#[local] Notation RCARRY := (rtt_carry (fx := fx) (PI := PI) (L := L) (PA := PA) B ARx SK).

(* ---- engine / instance interface (the brief's category (a)) ---- *)
(* the allocator laws at the cf instance's head (engine fold, YCbqG.v AR_laws_x; S10TxString.v:163) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED STAND-IN (owned by the kit / the core's PALib; S10TxString.v:166): the unit's image binding of B *)
Hypothesis PAL : PALib (L := L) (PI := PA) B.
(* MARKED STAND-IN (owned by the kit, the image binding of B; S10TxString.v:220): alloc.c's statics are not the runtime's own
   statics and not errno, so a runtime call's image clause (acall_kept) keeps them *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* the head is at least one shadow granule wide (PRH_Base.v prh_head_wide: ONE spelling a walk takes as a Section
   hypothesis; the preset instantiation discharges it from the cf instance owner's cf_head = 16) *)
Hypothesis HW : prh_head_wide.
(* ---- the image facts (computations on the concrete image; A': Rtt102FR1KitA.v) ---- *)
(* alloc.c's statics lie in the image and not in its read-only view (A': S1ImgA.v pst_in_img_A / pst_not_ro_A) *)
Hypothesis pst_in_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Hypothesis pst_not_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
(* round_trip_text keeps a frame pointer (PRH_Base.v prh_univ_closure_site's premise; A': by computation) *)
Hypothesis RTT_FP : @pi_fp PI F_round_trip_text = true.
(* round_trip_text's stack budget covers its own frame and realignment (A': 27392, by computation) *)
Hypothesis STKR_frame : 192 <= STKR.

(* ---- 2. a call of a program text from a concrete state (YCbqGcall.v:107 aj_call_x_sp, transcribed), at RZW: the
   callee concludes SRr' with its journal at RZW (apost_base_xR) ---- *)
Lemma fr_call_at : forall W regs memc STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1 pc
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regs = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK0 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regs) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regs memc mdc ch1 ->
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regs (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
     (apost_base_xR (SK := SK) SEGS B PST ARx RZW STK1 FP1 regs lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK0 sp0 FP FP1 ly S own lyc Sc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (mkst regs (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    AJ STK0 sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
    AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
    aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regs memc STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 pc Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof (@pa_segs_low _ L PA) as Hsegs.
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ apply Hcallee.
  exact (afn_pre_x_atR (SK := SK) SEGS B PST ARx RZW STK0 sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k regs
    STK1 o ch1
    HJ Hsp' Hal Hneg Hstk1 Hbud ltac:(rewrite Hra; exact Hraw) ltac:(unfold raZ; rewrite Hra; exact Hra4) Hgp Htp
    ltac:(rewrite Hsp'; exact Hch)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
eapply (ajournal_x_subR (SK := SK) SEGS B PST ARx LAWS Hsegs RZW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf));
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* ---- 4. the chain and the traces at a call in round_trip_text's body (H5RttS4.v s4_chain / s4_trace_in) ---- *)
(* every byte at or above the entry sp is the entry's (the journal's stack clause) *)
Lemma rtt_keep_above : forall D ly S Hp W mem md k pos, RJ D ly S Hp W mem md k pos ->
  forall a, ri_sp D <= a < 2 ^ 64 -> aview SEGS (w_H W) mem a = aview SEGS (w_H (ri_W D)) (ri_mem D) a.
Proof.
intros D ly S Hp W mem md k pos HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (_ & Hstk0 & Hceil & Hslo & _).
apply F1; lia.
Qed.

Lemma rtt_chain_at : forall D ly S Hp W mem md k pos sp1,
  PRE D -> RJ D ly S Hp W mem md k pos -> rtt_saved D W mem ->
  ri_sp D - 192 <= sp1 <= ri_sp D - 16 ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) sp1 (ri_sp D) ch1 /\
    (ch1 = [] \/ ch1 = (ri_sp D, raZ (ri_regs D), s0Z (ri_regs D)) :: ri_ch D).
Proof.
intros D ly S Hp W mem md k pos sp1 HP HJ HSV Hsp1.
destruct HP as ((HAFN & _) & _).
pose proof HAFN as (HAR0 & Hra & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
unfold ri_sp in *.
assert (H8 : spZ (ri_regs D) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
assert (Hce : YM05.alloc_ceiling <= spZ (ri_regs D)) by lia.
pose proof (HSV 0%nat ltac:(lia)) as Hw1. pose proof (HSV 1%nat ltac:(lia)) as Hw8.
unfold RTT_SAVED, ri_sp in Hw1, Hw8. cbn [nth Z.of_nat] in Hw1, Hw8.
replace (spZ (ri_regs D) - 8 * (0 + 1)) with (spZ (ri_regs D) - 8) in Hw1 by lia.
replace (spZ (ri_regs D) - 8 * (1 + 1)) with (spZ (ri_regs D) - 16) in Hw8 by lia.
apply fr_rdword_of_val_mem in Hw1; [|exact (bv_unsigned_in_range 64 _)].
apply fr_rdword_of_val_mem in Hw8; [|exact (bv_unsigned_in_range 64 _)].
destruct (Z_le_gt_dec (ly_top ly - 16) (spZ (ri_regs D))) as [Hbad|Hgood].
- exists []. split; [|left; reflexivity].
  left. split; [right; left; exact Hbad | reflexivity].
- exists ((spZ (ri_regs D), raZ (ri_regs D), s0Z (ri_regs D)) :: ri_ch D).
  split; [|right; reflexivity]. right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, spZ (ri_regs D) <= a -> a < ly_top (ri_ly D) ->
            rdword (aview SEGS (w_H W) mem) a = rdword (aview SEGS (w_H (ri_W D)) (ri_mem D)) a).
  { intros a Ha Hat. apply ts_rdword_keep. intros j Hj.
    apply (rtt_keep_above D ly S Hp W mem md k pos HJ). unfold ri_sp. lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next (spZ (ri_regs D)) (ly_top ly) (s0Z (ri_regs D))) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12].
        - apply Z.leb_le in Eb11. lia.
        - apply Z.leb_le in Eb12. lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (fr_fpchain_keep (aview SEGS (w_H (ri_W D)) (ri_mem D))
               (aview SEGS (w_H W) mem) (spZ (ri_regs D))); [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbn beta. intros x Hx. lia.
Qed.

(* the allocator trace of a call from round_trip_text's body, from the text's universe closure at its context *)
Lemma rtt_trace_at : forall D ly regsT ch1 r rt,
  PRE D ->
  (ch1 = [] \/ ch1 = (ri_sp D, raZ (ri_regs D), s0Z (ri_regs D)) :: ri_ch D) ->
  raZ regsT = r -> In r (@pi_ret_sites PI F_round_trip_text rt) ->
  In (call_trace ly (prh_pc0 B rt) regsT ch1) (as_universe B).
Proof.
intros D ly regsT ch1 r rt HP Hch1 Hra Hr.
destruct HP as (_ & _ & HCL & HCTX & _).
unfold call_trace. destruct (frame0_ok ly regsT) eqn:Ef0; [|exact (proj1 HCL rt)].
rewrite fr_unwind_eq, Hra.
destruct Hch1 as [-> | ->].
- exact (prh_univ_closure_lit B CTX0 F_round_trip_text rt r HCL Hr).
- exact (prh_univ_closure_site B CTX0 F_round_trip_text _ rt r HCL HCTX RTT_FP Hr).
Qed.

(* the journal from the entry keeps the layout's frame base: frame and flag addresses are the entry's *)
Lemma rtt_lyF : forall D ly S Hp W mem md k pos, RJ D ly S Hp W mem md k pos -> ly_F ly = ly_F (ri_ly D).
Proof.
intros D ly S Hp W mem md k pos HJ. pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & E & _). exact E.
Qed.
Lemma rtt_fa_eq : forall D ly S Hp W mem md k pos, RJ D ly S Hp W mem md k pos ->
  (forall cid pos', frame_addr ly cid pos' = frame_addr (ri_ly D) cid pos') /\
  (forall cid pos', flag_addr ly cid pos' = flag_addr (ri_ly D) cid pos').
Proof.
intros D ly S Hp W mem md k pos HJ. pose proof (rtt_lyF D ly S Hp W mem md k pos HJ) as E.
split; intros cid pos'; unfold frame_addr, flag_addr; rewrite E; reflexivity.
Qed.

(* what a callee's journal (PST its static exemption) or a runtime call's acall_kept_x (no static exemption) keeps,
   with E the call's write set; one form for both *)
Definition rtt_kept (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte)
  (slo shi : Z) (E : Z -> Prop) (P : list (Z * Z)) : Prop :=
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H Wc) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) P -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).

Lemma rtt_kept_of_acall : forall lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E,
  acall_kept_x SEGS B lyc Sc Wc memc W2 mem2 slo shi E -> rtt_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E [].
Proof.
intros lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E HK. destruct HK as (K1 & K2 & K3 & K4 & _).
split; [exact K1|]. split; [intros b m i Hb _ Hi HE; exact (K2 b m i Hb Hi HE)|].
split; [intros a Hi Ho He _; exact (K3 a Hi Ho He) | exact K4].
Qed.

Lemma rtt_kept_of_journal : forall STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1,
  AJ STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ~ YI16.sink_open_fp FP1 ->
  rtt_kept lyc Sc Wc memc ly2 S2 W2 mem2 (sp1 - STK1) sp1 (inFP FP1) PST.
Proof.
intros STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 HJ Hcl.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
split; [exact F1|]. split; [exact F2|].
split; [intros a Hi Ho He Hp; exact (F3 a Hi Ho He Hp (fp_spares_closed FP1 a Hcl))|].
exact F4.
Qed.

(* the bytes a call's write set must miss for the cut's carried state to survive it: the entry's harness blocks
   (their heads and the tree's strings) and every live fake frame's bytes (doc's node, *copy, the flag pointer) *)
Definition rtt_off (D : rtt_in) (lyc : alayout) (Sc : astate) (x : Z) : Prop :=
  (forall a k, In (a, k) (ri_Lam D) -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) /\
  (forall cid pos', In (cid, pos') (frames Sc) -> ~ in_zr x (frame_rng lyc (cid, pos'))).

(* a live block that is not one of the entry's misses all of that *)
Lemma rtt_newblk_off : forall D lyc Sc Hpc Wc memc mdc kc pos Lamc peakc cntc failc ranc mostc ownc b m x,
  PRE D -> RJ D lyc Sc Hpc Wc memc mdc kc pos ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> incl (ri_Lam D) Lamc ->
  In (b, m) (ablocks B lyc Sc) -> ~ In (b, m) (ablocks B (ri_ly D) (ri_S D)) ->
  b <= x < b + req_size m -> rtt_off D lyc Sc x.
Proof.
intros D lyc Sc Hpc Wc memc mdc kc pos Lamc peakc cntc failc ranc mostc ownc b m x HP HJ HLc Hinc Hb Hnb Hx.
pose proof HJ as (HARc & _).
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HARc) as [Hpw _].
pose proof (pairwise_app_l zdisjoint _ _ Hpw) as [Hpb _].
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc b m HARc Hb) as (_ & _ & _ & Happ & _).
split.
- intros a k Hin Hx2.
  destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED0 Hin) as (_ & Hb0 & _).
  destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HLc (Hinc _ Hin)) as (_ & Hbc & _).
  assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; rewrite E in Hnb; exact (Hnb Hb0)).
  destruct (fr_pairwise_in_map zdisjoint (fun b0 => (fst b0, req_size (snd b0))) _ _ _ Hpb Hb Hbc Hne) as [Hd | Hd];
    unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
- intros cid pos' Hf.
  intros Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
  pose proof (fr_pairwise_app zdisjoint _ _ _ _ Hpw (in_map (fun b0 => (fst b0, req_size (snd b0))) _ _ Hb)
    (in_map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* a live block misses every live frame's shadow (blocks are application memory) *)
Lemma rtt_blk_off_sh : forall lyc Sc Hpc Wc memc mdc b m x,
  ARx lyc Sc Hpc Wc memc mdc -> In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m ->
  forall cid pos', In (cid, pos') (frames Sc) ->
  ~ in_zr x (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8).
Proof.
intros lyc Sc Hpc Wc memc mdc b m x HARc Hb Hx cid pos' Hf Hz. unfold in_zr in Hz. cbn [fst snd] in Hz.
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc b m HARc Hb) as (_ & _ & _ & Happ & _).
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HARc Hf) as (Hf4 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc cid pos') in *. set (fb := fs_frame_bytes cid) in *.
assert (Hd1 : F / 8 * 8 <= F) by (pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (Hd2 : fb / 8 * 8 <= fb) by (pose proof (Z.mul_div_le fb 8 ltac:(lia)); lia).
assert (Hd3 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Hd4 : 0 <= fb / 8) by (apply Z.div_pos; lia).
unfold shadow_addr, SHADOW_OFF in Hz.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold kHighMemBeg in C3. lia.
Qed.

(* rodata lies in the image (S10TxStrGlue.v ts_ro_img) *)
Lemma rtt_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the entry's facts the keeps read *)
Lemma rtt_pre_facts : forall D, PRE D ->
  ARx (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) /\
  YM05.alloc_ceiling + STKR <= ri_sp D <= 2 ^ 47 /\ ri_sp D mod 16 = 0 /\ ri_sp D + 64 <= ly_stk_hi (ri_ly D) /\
  (forall bk, In bk (ri_D D) -> In bk (ri_Lam D)) /\
  pj_nodeR SEGS (mrestrict (w_H (ri_W D)) (ri_mem D)) (prh_lin (ri_Lam D)) (ri_doc D) (ri_t D) (ri_D D) /\
  ck_in_frame (ri_ly D) (ri_S D) (ri_doc D) 56 /\
  (ri_copy D = 0 \/ ck_in_frame (ri_ly D) (ri_S D) (ri_copy D) 56).
Proof.
intros D HP.
destruct HP as ((HAFN & _ & H64 & _) & _ & _ & _ & _ & _ & _ & _ & _ & HTREE & _ & _ & _ & HCOPY & _).
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HTREE as (Hnode & HDL & _ & (_ & Hhome & _)).
unfold ri_sp. split; [exact HAR0|]. split; [lia|]. split; [exact Hal16|]. split; [exact H64|].
split; [exact HDL|]. split; [exact Hnode|]. split; [exact Hhome|].
destruct HCOPY as [H0 | (_ & _ & (Hin & _) & _)]; [left; exact H0 | right; exact Hin].
Qed.

(* a fake frame of the entry is live at every cut, at the same address *)
Lemma rtt_entry_frame : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos cid pos',
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos -> In (cid, pos') (frames (ri_S D)) ->
  In (cid, pos') (frames Sc) /\ frame_addr lyc cid pos' = frame_addr (ri_ly D) cid pos'.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos cid pos' HC Hf.
destruct HC as (_ & HJc & (Efr & _) & _).
split; [rewrite Efr; right; exact Hf|].
exact (proj1 (rtt_fa_eq D lyc Sc Hpc Wc memc mdc kc pos HJc) cid pos').
Qed.

(* ---- the carried state under a register write a cut does not read, and under materialization ---- *)
Lemma rtt_cregs_upd : forall D ly regs pos (r : bv 5) v,
  rtt_cregs B D ly regs pos ->
  r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> r <> 18%bv -> r <> 19%bv -> r <> 20%bv -> r <> 25%bv -> r <> 26%bv ->
  r <> 3%bv -> r <> 4%bv ->
  rtt_cregs B D ly (regupd regs r v) pos.
Proof.
intros D ly regs pos r v (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4) N2 N8 N9 N18 N19 N20 N25 N26 N3 N4.
unfold rtt_cregs. rewrite !getr_other by (intros E; subst r; auto).
repeat split; assumption.
Qed.
Lemma rtt_carry_regs : forall D fxc ly S Hp W regs mem md k pos regs',
  RCARRY D fxc ly S Hp W regs mem md k pos -> rtt_cregs B D ly regs' pos -> RCARRY D fxc ly S Hp W regs' mem md k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos regs' HC HCR.
destruct HC as (X1 & X2 & X3 & X4 & _ & X6 & X7 & X8 & X9 & X10 & X11).
exact (conj X1 (conj X2 (conj X3 (conj X4 (conj HCR (conj X6 (conj X7 (conj X8 (conj X9 (conj X10 X11)))))))))).
Qed.
Lemma rtt_carry_md : forall D fxc ly S Hp W regs mem md k pos md',
  RCARRY D fxc ly S Hp W regs mem md k pos -> RJ D ly S Hp W mem md' k pos -> RCARRY D fxc ly S Hp W regs mem md' k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos md' HC HJ.
destruct HC as (X1 & _ & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
exact (conj X1 (conj HJ (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj X10 X11)))))))))).
Qed.

(* ---- THE CARRIED STATE ACROSS A CALL (or a run) whose keeps are rtt_kept, whose write set misses rtt_off; the journal
   is the one a call rule returns from RJ at the call state (RJc), at the empty budget, so the wild traces stay
   rtt_wild's (Rtt102Cut.v rtt_wild_Jc) ---- *)
Lemma rtt_carry_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 Hp2 W2 regs2 mem2 md2 k2 slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2,
  PRE D ->
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RJc D Sc ly2 S2 Hp2 W2 mem2 md2 k2 pos ->
  frames S2 = frames Sc ->
  rtt_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  shi <= ri_sp D - 104 ->
  (forall a, Exists (in_zr a) P -> Exists (in_zr a) PST) ->
  (forall x, E x -> rtt_off D lyc Sc x) ->
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> incl (ri_Lam D) Lamc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 -> incl (ri_Lam D) Lam2 ->
  rtt_cregs B D ly2 regs2 pos ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  rtt_room D S2 ->
  RCARRY D fxc ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 Hp2 W2 regs2 mem2 md2 k2 slo shi E P
  Lamc peakc cntc failc ranc mostc ownc Lam2 peak2 cnt2 fail2 ran2 most2 own2
  HP HC HJ2 HFR HK Hshi HPP HEoff HLc Hincc HL2 Hinc2 HCR2 HMN2 HROOM2.
pose proof (rtt_pre_facts D HP) as (HAR0 & Hsp0 & Hsp16 & _ & HDL & _ & Hhome & _).
pose proof HC as (HFX & HJc & HFRc & HSVc & _ & HMNc & HRODc & _ & HNODEc & HVISc & HWc).
pose proof HK as (K1 & K2 & K3 & K4).
pose proof HJ2 as (HAR2 & _).
assert (HJ2' : RJ D ly2 S2 Hp2 W2 mem2 md2 k2 pos) by (eapply rtt_J_of_Jc; exact HJ2).
destruct (rtt_fa_eq D lyc Sc Hpc Wc memc mdc kc pos HJc) as (Fac & Flc).
destruct (rtt_fa_eq D ly2 S2 Hp2 W2 mem2 md2 k2 pos HJ2') as (Fa2 & Fl2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
(* the entry's frames are live at both states *)
assert (HF0c : forall cid pos', In (cid, pos') (frames (ri_S D)) -> In (cid, pos') (frames Sc)).
{ intros cid pos' Hf. destruct HFRc as (Efr & _). rewrite Efr. right. exact Hf. }
assert (HF02 : forall cid pos', In (cid, pos') (frames (ri_S D)) -> In (cid, pos') (frames S2)).
{ intros cid pos' Hf. rewrite HFR. exact (HF0c cid pos' Hf). }
(* a byte of an entry frame is kept *)
assert (KF : forall cid pos' x, In (cid, pos') (frames (ri_S D)) ->
  frame_addr (ri_ly D) cid pos' <= x < frame_addr (ri_ly D) cid pos' + fs_frame_bytes cid ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ intros cid pos' x Hf Hx. apply (K4 cid pos' x (HF0c cid pos' Hf)).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia.
  - intros HE. destruct (HEoff x HE) as (_ & Hfr). apply (Hfr cid pos' (HF0c cid pos' Hf)).
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia. }
(* a byte of an entry harness block is kept *)
assert (KB : forall a k x, In (a, k) (ri_Lam D) -> a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ intros a k x Hin Hx.
  destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HLc (Hincc _ Hin)) as (_ & Hbc & _).
  destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HL2 (Hinc2 _ Hin)) as (_ & Hb2 & _).
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (K2 (a - cf_head) (k + cf_head) (x - (a - cf_head)) Hbc Hb2); [lia|].
  intros HE. destruct (HEoff _ HE) as (Hbl & _). apply (Hbl a k Hin). lia. }
split; [exact HFX|].
split; [exact HJ2'|].
split.
{ (* rtt_frame *)
  destruct HFRc as (Efr & Hni & Hflag & _).
  split; [rewrite HFR; exact Efr|]. split; [exact Hni|]. split.
  - rewrite Fa2, Fl2. rewrite Fac, Flc in Hflag. rewrite <- Hflag. apply ts_rdword_keep. intros j Hj.
    apply (K4 RT_CID pos); [rewrite Efr; left; reflexivity | left | ].
    + unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac, Efs1. unfold RT_FLAGP. lia.
    + intros HE. destruct (HEoff _ HE) as (_ & Hfr). apply (Hfr RT_CID pos ltac:(rewrite Efr; left; reflexivity)).
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac, Efs1. unfold RT_FLAGP. lia.
  - intros a Ha. destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 RT_CID pos HAR2
      ltac:(rewrite HFR, Efr; left; reflexivity)) as (_ & _ & Hpr & _).
    exact (proj1 (Hpr a Ha)). }
split.
{ (* rtt_saved *)
  intros j Hj. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact (HSVc j Hj)].
  intros i Hi. apply K1; unfold ri_sp in *; lia. }
split; [exact HCR2|].
split; [intros H; exact (HMN2 (HMNc H))|].
split.
{ (* the read-only view *)
  intros a Hro Hown Herr. rewrite (K3 a (rtt_ro_img a Hro) Hown Herr).
  - exact (HRODc a Hro Hown Herr).
  - intros HPa. exact (pst_not_ro a (HPP a HPa) Hro). }
split; [exact HROOM2|].
split.
{ (* doc's tree *)
  apply (pj_nodeR_frame SEGS _ _ _ _ _ _ HNODEc). intros x Hx.
  destruct Hhome as (cid & pos' & Hf & Hlo & Hhi).
  destruct Hx as [Hx | ((a, k) & HinD & Hx)].
  - assert (Hx' : frame_addr (ri_ly D) cid pos' <= x < frame_addr (ri_ly D) cid pos' + fs_frame_bytes cid) by lia.
    split; [apply mbyte_of_aview; exact (KF cid pos' x Hf Hx')|].
    intros _. apply apresent_writable.
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 (HF02 cid pos' Hf)) as (_ & _ & Hpr & _).
    apply (Hpr x). rewrite Fa2. exact Hx'.
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (HDL _ HinD) as HinL.
    destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HL2 (Hinc2 _ HinL)) as (Hk0 & Hb2 & _).
    pose proof cf_head_nonneg as Hch0.
    assert (Hrq : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
    assert (Hx' : a - cf_head <= x < a - cf_head + req_size (k + cf_head)) by lia.
    split; [apply mbyte_of_aview; exact (KB a k x HinL Hx')|].
    intros _. apply apresent_writable.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2) as (_ & _ & _ & _ & Hpr & _).
    exact (proj1 (Hpr x Hx')). }
split.
{ (* the tree's visibility, re-derived at the new state from the harness-block laws *)
  unfold PRH_FnWriter.prhWriter_tree_vis, YGcfTreeVis.tree_vis_cf in *. intros a k HinD.
  destruct (HVISc a k HinD) as (V1 & V2 & V3 & V4 & _ & _ & _).
  pose proof (HDL _ HinD) as HinL.
  destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HL2 (Hinc2 _ HinL)) as (Hk0 & Hb2 & Hh2 & _).
  pose proof cf_head_nonneg as Hch.
  assert (Hrq : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
  destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2 Hh2) as (Hbs & Hhull).
  replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hb2) as (_ & _ & _ & _ & Hpr & _).
  split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|].
  split.
  { intros x Hx. exact (block_shadow_range _ _ _ _ a k Hbs ltac:(lia) ltac:(lia) x Hx). }
  split.
  { intros Hk. assert (Er : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    rewrite Er in Hhull. replace (k + cf_head - cf_head) with k in Hhull by lia. apply Hhull. lia. }
  intros x Hx.
  destruct (Z_lt_le_dec x (a - cf_head + req_size (k + cf_head))) as [Hin | Hge].
  - apply fr_aview_of_apresent. exact (proj1 (Hpr x ltac:(lia))).
  - assert (Hmono : (a + k + 7) / 8 <= (a - cf_head + req_size (k + cf_head) + 7) / 8) by (apply Z.div_le_mono; lia).
    apply (alx_blocks_tail SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) x HAR2 Hb2).
    split; [exact Hge | lia]. }
(* the wild traces: the call stored none beyond the caller journal's (rtt_wild_Jc) *)
eapply rtt_wild_Jc; [exact HWc | exact HJ2].
Qed.

(* *copy's 56 bytes (an entry frame) survive the call *)
Lemma rtt_copy_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P,
  PRE D -> RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  rtt_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P -> (forall x, E x -> rtt_off D lyc Sc x) ->
  rtt_copy_kept D Wc memc -> rtt_copy_kept D W2 mem2.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P HP HC HK HEoff HCK Hc0 a Ha.
pose proof (rtt_pre_facts D HP) as (_ & _ & _ & _ & _ & _ & _ & Hcopy).
destruct Hcopy as [H0 | (cid & pos' & Hf & Hlo & Hhi)]; [exfalso; exact (Hc0 H0)|].
destruct (rtt_entry_frame D fxc lyc Sc Hpc Wc regsc memc mdc kc pos cid pos' HC Hf) as (Hfc & Fac).
pose proof HK as (_ & _ & _ & K4).
rewrite <- (HCK Hc0 a Ha). apply (K4 cid pos' a Hfc).
- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia.
- intros HE. destruct (HEoff a HE) as (_ & Hfr). apply (Hfr cid pos' Hfc).
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fac. lia.
Qed.

(* back's shadow (the frame's shadow bytes 4 .. 10) survives the call *)
Lemma rtt_back_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P,
  RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  rtt_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E P ->
  (forall x, E x -> ~ in_zr x (shadow_addr (frame_addr lyc RT_CID pos), fs_frame_bytes RT_CID / 8)) ->
  (forall cid pos', frame_addr ly2 cid pos' = frame_addr lyc cid pos') ->
  rtt_back lyc Wc memc pos -> rtt_back ly2 W2 mem2 pos.
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E P HC HK HEsh Fa2 HB.
pose proof HC as (_ & HJc & (Efr & _ & _ & _) & _).
pose proof HJc as (HARc & _).
pose proof HK as (_ & _ & _ & K4).
assert (Hin : In (RT_CID, pos) (frames Sc)) by (rewrite Efr; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc RT_CID pos HARc Hin) as (F32 & _).
assert (Efs1 : fs_frame_bytes RT_CID = 128) by (vm_compute; reflexivity).
unfold rtt_back in *. rewrite Fa2.
apply (range_addressable_agree (aview SEGS (w_H Wc) memc) (aview SEGS (w_H W2) mem2)); [|exact HB].
intros x Hx. unfold shadow_of_addr.
set (F := frame_addr lyc RT_CID pos) in *.
assert (HF8 : F mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in F32; [|lia]; destruct F32 as [q Hq]; exists (4 * q); lia).
assert (Hs : SHADOW_OFF + x / 8 = shadow_addr F + (x - F) / 8).
{ unfold shadow_addr. assert (EF : F = F / 8 * 8) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
  replace x with ((x - F) + F / 8 * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
rewrite Hs. apply (K4 RT_CID pos); [exact Hin | right | ].
- unfold in_zr. cbn [fst snd]. rewrite Efs1. unfold RT_BACK in Hx.
  assert (0 <= (x - F) / 8 < 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). fold F. lia.
- intros HE. apply (HEsh _ HE).
  unfold in_zr. cbn [fst snd]. rewrite Efs1. unfold RT_BACK in Hx.
  assert (0 <= (x - F) / 8 < 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). fold F. lia.
Qed.

(* alloc.c's two flag cells lie in its statics *)
Lemma rtt_most_pst : forall j, (j < @pi_gz_most PI)%nat -> Exists (in_zr (@pi_g_most PI + Z.of_nat j)) PST.
Proof.
intros j Hj. unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma rtt_own_pst : forall j, (j < @pi_gz_own_ran_out PI)%nat ->
  Exists (in_zr (@pi_g_own_ran_out PI + Z.of_nat j)) PST.
Proof.
intros j Hj. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* a runtime call's image clause keeps alloc.c's statics (pal_pst_static) *)
Lemma rtt_pst_kept_acall : forall lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E,
  rtt_kept lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E [] ->
  forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a.
Proof.
intros lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E (_ & _ & K3 & _) a Ha.
destruct (pal_pst_static a Ha) as [Ho He].
apply (K3 a (pst_in_img a Ha) Ho He). intros Hn. inversion Hn.
Qed.
Lemma rtt_own_kept : forall Wc memc W2 mem2 own,
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  prh_own (PI := PI) Wc memc own -> prh_own (PI := PI) W2 mem2 own.
Proof.
intros Wc memc W2 mem2 own HK (Hv & Ho). split; [|exact Ho].
apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact Hv]. intros j Hj. apply HK. exact (rtt_own_pst j Hj).
Qed.
Lemma rtt_most_kept : forall Wc memc W2 mem2 most,
  (forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  prh_most (PI := PI) Wc memc most -> prh_most (PI := PI) W2 mem2 most.
Proof.
intros Wc memc W2 mem2 most HK (Hv & Ho). split; [|exact Ho].
apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact Hv]. intros j Hj. apply HK. exact (rtt_most_pst j Hj).
Qed.

(* a live block whose base is not hidden is none of the ledger's (their bases are hidden) and misses them all *)
Lemma rtt_blk_off_ledger : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc b m x,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  In (b, m) (ablocks B lyc Sc) -> ~ In b Hpc -> b <= x < b + req_size m ->
  forall a k, In (a, k) Lamc -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head)).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc b m x HAR HL Hb Hnh Hx a k Hin Hx2.
destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HL Hin) as (_ & Hbk & Hhk & _).
assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as -> _; exact (Hnh Hhk)).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as [Hpw _].
pose proof (pairwise_app_l zdisjoint _ _ Hpw) as [Hpb _].
destruct (fr_pairwise_in_map zdisjoint (fun b0 => (fst b0, req_size (snd b0))) _ _ _ Hpb Hb Hbk Hne) as [Hd | Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* no hidden head sits at address 0 (every ledger block lies at or above 4096) *)
Lemma rtt_hp_nonzero : forall lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> ~ In 0 Hpc.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc HAR HL Hin.
pose proof (PRH_Base.prh_ledger_heads (PI := PI) B _ _ _ _ _ _ _ _ _ _ _ _ HL) as HP.
apply (Permutation_in _ HP) in Hin. apply in_map_iff in Hin as ([a k] & Ea & HinL). cbn [fst] in Ea.
destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HL HinL) as (_ & Hbk & _).
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hbk) as (_ & H4096 & _). lia.
Qed.

(* ---- AFTER A DIRECT FREE (want): the carried state, the ledger, the flags, *copy and back; the journal is a call
   rule's from RJ at the call state (RJc) at the empty budget ---- *)
Lemma rtt_free_keep : forall D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 regs2 mem2 md2 k2 slo shi E
  Lamw peakw cntw ranw own,
  PRE D -> RCARRY D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ->
  RJc D Sc ly2 S2 Hpc W2 mem2 md2 k2 pos -> frames S2 = frames Sc ->
  acall_kept_x SEGS B lyc Sc Wc memc W2 mem2 slo shi E -> shi <= ri_sp D - 104 ->
  (forall x, E x -> rtt_off D lyc Sc x) ->
  (forall x, E x -> ~ in_zr x (shadow_addr (frame_addr lyc RT_CID pos), fs_frame_bytes RT_CID / 8)) ->
  (forall x, E x -> forall a k, In (a, k) Lamw -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head))) ->
  (forall a k, In (a, k) Lamw -> In (a - cf_head, k + cf_head) (ablocks B lyc Sc) ->
     In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) ->
  rtt_led (PI := PI) B D lyc Sc Hpc Wc memc Lamw peakw cntw ranw own -> incl (ri_Lam D) Lamw ->
  rtt_cregs B D ly2 regs2 pos -> (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) -> rtt_room D S2 ->
  RCARRY D fxc ly2 S2 Hpc W2 regs2 mem2 md2 k2 pos /\
  rtt_led (PI := PI) B D ly2 S2 Hpc W2 mem2 Lamw peakw cntw ranw own /\
  (rtt_copy_kept D Wc memc -> rtt_copy_kept D W2 mem2) /\ (rtt_back lyc Wc memc pos -> rtt_back ly2 W2 mem2 pos).
Proof.
intros D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 regs2 mem2 md2 k2 slo shi E Lamw peakw cntw ranw own
  HP HC HJ2 HFR HKA Hshi HEoff HEsh HEled Hblk (HLc & Hpk) Hinc HCR2 HMN2 HROOM2.
pose proof (rtt_kept_of_acall lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E HKA) as HK.
pose proof (rtt_pst_kept_acall lyc Sc Wc memc ly2 S2 W2 mem2 slo shi E HK) as HKP.
pose proof HK as (_ & K2 & _ & _).
assert (HL2 : prh_ledger B ly2 S2 Hpc W2 mem2 Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own).
{ apply (prh_ledger_kept_aview (PI := PI) B lyc Sc Hpc Wc memc); [exact HLc | exact HKP | | exact Hblk | apply Permutation_refl].
  intros a k i Hin Hi.
  destruct (prh_ledger_hblock (PI := PI) B _ _ _ _ _ _ _ _ _ _ a k _ _ HLc Hin) as (Hk0 & Hbk & _).
  pose proof HW as Hw. unfold prh_head_wide in Hw.
  assert (Hrq : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
  apply (K2 (a - cf_head) (k + cf_head) i Hbk (Hblk a k Hin Hbk)); [lia|].
  intros HE. apply (HEled _ HE a k Hin). lia. }
split.
{ apply (rtt_carry_keep D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 Hpc W2 regs2 mem2 md2 k2 slo shi E []
    Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own Lamw peakw cntw SIZE_MAXZ ranw (ri_most D) own HP HC HJ2 HFR HK Hshi);
    try assumption.
  intros a Ha. inversion Ha. }
split; [split; [exact HL2 | exact Hpk]|].
split; [exact (rtt_copy_keep D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E [] HP HC HK HEoff)|].
pose proof HC as (_ & HJc & _).
destruct (rtt_fa_eq D lyc Sc Hpc Wc memc mdc kc pos HJc) as (Fac & _).
destruct (rtt_fa_eq D ly2 S2 Hpc W2 mem2 md2 k2 pos ltac:(eapply rtt_J_of_Jc; exact HJ2)) as (Fa2 & _).
apply (rtt_back_keep D fxc lyc Sc Hpc Wc regsc memc mdc kc pos ly2 S2 W2 mem2 slo shi E [] HC HK HEsh).
intros cid pos'. rewrite Fa2, Fac. reflexivity.
Qed.

End k.

(* the elaborated statements, every implicit shown: each cut predicate must take the Section's fx, never fxc *)
Set Printing Implicit.
Check @rtt_carry_keep.
Check @rtt_free_keep.
Check @rtt_copy_keep.
Check @rtt_back_keep.
Check @rtt_entry_frame.
Check @rtt_carry_regs.
Check @rtt_carry_md.
Unset Printing Implicit.
