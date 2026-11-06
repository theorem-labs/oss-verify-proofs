(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutB_Base.v, with its module names changed; 267 of its 318 lines of code are new or changed and 1354 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): the journals of this kit are the
   engine's R forms at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (ajournal_xwR / ajournal_xR, the notations AJW / AJ),
   the relation of the glue's crt_live_journal. Statements otherwise and proofs unchanged (they read the journal by
   position and through aview equalities, never through its world conjunct). Contract note: the internal file WLE-CONTRACT.md. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b): THE IMAGE-B KIT, the helper lemmas the B' rows T4, T6 and T7
   all cite. The unit's owner ordered and approved this move.

   proves no function (kind: helper lemmas). rule 24: no function proved. These are image-B helper lemmas of the
   check_round_trip walk; the walk's rule-24 record is RULE24.md (sha256 96ef6f3404f0; internal record)
   (COMPLETE: no #102 walk of check_round_trip outside this walk).

   WHY THIS FILE: the three rows T4, T6 and T7 cite these helpers, and they lived in row T4's segment file
   (lib/B/Prog/Crt102B_T4.v). There a change of T4's STATEMENT could break the other two rows. Here they depend on no
   row's statement.

   MOVED, NOT RESTATED. Every statement below is copied character for character, and every proof too except the two
   changes named after this list, from
     commit 5e6329de569, proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Crt102B_T4.v,
     blob bfc220939b38.
   The nine helpers, each with its line in that blob:
     cb4_fb :410, cb4_sp :628, cb4_ar0 :642, cb4_ff :646, cb4_doc_home :667, cb4_ro_img :702,
     cb4_fregs_trans :841, cb4_chain :881, cb4_live_call :935.
   The T4 lemmas they use, moved with them unchanged: cb4_stkc :626 (used by cb4_sp), cb4_rdword_of_val_mem :844 and
   cb4_fpchain_keep :860 (used by cb4_chain). Also copied unchanged: the import block and settings (:45-78), the
   Section / Context / Variable declarations the lemmas live under (:388-391, :413-415, :418-425), the local notations
   they use (:392, :394, :398-401, :416, :426-432, :450-451), and the comments attached to the moved lemmas.
   SECTION HYPOTHESES: only the three the moved lemmas use, LAWS (:593), HPRE (:594) and HTREE (:595), with their
   comment (:589-592). T4's other hypotheses (:596-623) are used by none of them and are left out; among them HLED0
   (:605) states the ledger at its arity before the E sweep.
   TWO CHANGES SINCE THE MOVE (2026-10-30): (1) cb4_live_call's proof reads and builds crt_live /
   crt_frame by their Record fields (the glue's Records re-cut; its statement is unchanged); (2) cb_J_B_ccnt24 is NEW
   here (not moved): the class-24 bound at the B' join, for row T8, derived from crt_at_J_B (see its comment).
   KB ROUND (the kb Glue c580eb0fe37c: crt_live carries a budget kb and its journal is `exists WS, AJW .. WS /\ wbudget
   [] kb WS`), the B' twin of the A' kit at a54cc6d36c2c: cb4_ff and cb4_chain take the journal at any budget WS;
   cb4_live_call takes the live state at kbg and the caller's journal after the call at a WS2 within kbg', and gives the
   live state at kbg' (as Crt102Kit.crt102rw_live_call); cb4_live_mono is NEW, the budget step up kb <= kb' (as
   Crt102Arms.arms_live_mono).

   BASE: commit 86b9958cfd5c - the contract texts and Spec
   (PRH_Base fdb45545469b, PRH_FnCheck 9ecd8eb167c6, PresetReqAt 43c958024221, PresetRun 5ac818ab1fe6), S1Ledger
   8cf15eeb6311, the glue lib/A/Prog/Crt102Glue.v. No moved lemma reads a conjunct that the base changed:
   cb4_live_call passes crt_side whole (its arguments are unchanged at the kit tip, Crt102Glue.v:223-225), and the
   intro pattern of cb4_chain names HPRE's conjuncts after afn_pre_x by position; its last name, Hrac, which no step
   uses, now binds the conjunction that ends in the frm_zero conjunct the kit tip appended (PRH_Base.v:602-610).
   No moved lemma names crt_at_J_B, crt_at_C_B, crt_at_L3_B, crt_at_L0_B or prh_ledger (the new cb_J_B_ccnt24 reads
   crt_at_J_B's fields crt_at_J_B_r0 and crt_at_J_B_count).

   build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1,
   PAU pau-preset-102. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
(* the re-hiding move's world relation (YA0nH.wle') at preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section t4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

Lemma cb4_fb : fs_frame_bytes CRT_CID = 512.
Proof. vm_compute. reflexivity. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the re-hiding move: every journal at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (kb round: crt_live's journal is at a budget WS with wbudget [] kb WS) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)) (a_mod_at a_stamp : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
(* crt_live / crt_side carry no room position since 11c39f7e88b7 (so they take no rp_* argument); the position
   travels as crt_pos on the r = 0-path boundaries only *)
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most)).
#[local] Notation sideB := (crt_side (rc := rc) (PI := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PA) (B := B)
  (doc := doc) (t := t) (D := D) (peak := peak) (most := most)).

(* ======================================================================================================== *)
(* THE NAMED SECTION HYPOTHESES of the proofs below. LAWS: the allocator relation's laws (discharged at the
   instance ARcfx by lib/Reusable/YGcallcf.v AR_laws_x_xs). HPRE / HTREE: tcheck_round_trip_specX's premises at the
   entry (Crt102Top.v discharges them from the text's). *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.

(* ---- the entry's stack facts (STK_check_round_trip is 27632 on B' too) ---- *)
Lemma cb4_stkc : STKC = 27632.
Proof. vm_compute. reflexivity. Qed.
Lemma cb4_sp : sp0 mod 16 = 0 /\ YM05.alloc_ceiling + 27632 <= sp0 /\ sp0 <= 2 ^ 47 /\
  sp0 - 255 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0 /\ 0 <= sp1.
Proof.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
rewrite cb4_stkc in *.
pose proof (YM05.alloc_ceiling_val) as Hc.
unfold CRT_sp1, CRT_FRAME, CRT_ALIGN.
pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
split; [exact Hal16|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [apply Z.mod_mul; lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.

Lemma cb4_ar0 : ARx ly S Hp W mem md.
Proof. exact (proj1 (proj1 HPRE)). Qed.

(* ---- the frame (CRT_CID, pos) the journal owns: on the frame list, bounded, its bytes and shadow present ---- *)
Lemma cb4_ff : forall lyc Sc Hpc Wc memc mdc kj pos {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  In (CRT_CID, pos) (frames Sc) /\
  4096 <= frame_addr lyc CRT_CID pos /\ frame_addr lyc CRT_CID pos + 512 <= YM05.alloc_ceiling /\
  in_app (frame_addr lyc CRT_CID pos) 512 /\ frame_addr lyc CRT_CID pos mod 32 = 0 /\
  (forall a, frame_addr lyc CRT_CID pos <= a < frame_addr lyc CRT_CID pos + 512 ->
     apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H Wc) memc (shadow_addr (frame_addr lyc CRT_CID pos) + i) /\
     ~ aowned B lyc Sc (shadow_addr (frame_addr lyc CRT_CID pos) + i)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos WS HJ.
pose proof HJ as (HARc & _ & _ & _ & _ & HFRc & _).
assert (Hin : In (CRT_CID, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & _ & Ffr & Fsh).
rewrite cb4_fb in Fb2, Fb3, Ffr, Fsh. change (512 / 8) with 64 in Fsh.
split; [exact Hin|]. split; [exact Fb1|]. split; [exact Fb2|]. split; [exact Fb3|]. split; [exact F32|].
split; [exact Ffr | exact Fsh].
Qed.

(* ---- the document's 56 bytes lie in a fake frame of the entry: application memory below alloc_ceiling ---- *)
Lemma cb4_doc_home : 4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling /\ in_app doc 56 /\ doc mod 8 = 0.
Proof.
pose proof HTREE as (_ & _ & _ & (Hd8 & (cid & pos' & Hin & H1 & H2) & _)).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos' cb4_ar0 Hin) as (Fb1 & Fb2 & Fb3).
split; [lia|]. split; [lia|]. split; [|exact Hd8].
apply (in_app_sub _ _ _ _ Fb3); lia.
Qed.

Lemma cb4_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* ======================================================================================================== *)
(* SHARED CALL INFRASTRUCTURE of the W walk (every call of T4 is made at sp = s1 = CRT_sp1 with s0 = the entry sp).
   B' twins of Crt102Arms.v 97a937b1e61 (arms_fregs_trans, arms_rdword_of_val_mem, arms_fpchain_keep, arms_chain,
   arms_dregs_pres / _eq) and of Crt102Rewrite.v 370f759b180 (crt102rw_live_call), the register set B''s. *)
Lemma cb4_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

Lemma cb4_rdword_of_val_mem : forall sg (Hh : word -> bool) m0 a v,
  val_mem sg (mrestrict Hh m0) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview sg Hh m0) a = Some v.
Proof.
intros sg Hh m0 a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview sg Hh m0 (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Lemma cb4_fpchain_keep : forall (r1 r2 : reader) lo top ch0 bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch0 -> fpchain (rdword r2) bp top ch0.
Proof.
intros r1 r2 lo top ch0. induction ch0 as [|[[fp ra] nfp] ch0 IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r. rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12]. apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

(* the frame-pointer chain at a call made at sp = CRT_sp1 with s0 = the entry sp: check_round_trip's own record (its
   ra at sp0 - 8 and the caller's s0 at sp0 - 16, crt_saved's first two slots) pushed onto the chain it was given,
   unless the entry sp is within 16 of the layout's top *)
Lemma cb4_chain : forall own lyc Sc Hpc Wc memc mdc kj {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kj WS ->
  @crt_saved rc B_prog_listing PA regs Wc memc ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) sp1 sp0 ch1 /\
    (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch).
Proof.
intros own lyc Sc Hpc Wc memc mdc kj WS HJ HSV.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof cb4_sp as (_ & Hceil0 & H470 & Hs1 & Hs32 & Hs0).
assert (H8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr1. change (bv_modulus 64) with (2 ^ 64) in Hr1.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr8. change (bv_modulus 64) with (2 ^ 64) in Hr8.
assert (Hw1 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 8) = Some (raZ regs)).
{ apply cb4_rdword_of_val_mem; [|unfold raZ; lia]. exact (HSV 0%nat ltac:(lia)). }
assert (Hw8 : rdword (aview SEGS (w_H Wc) memc) (sp0 - 16) = Some (s0Z regs)).
{ apply cb4_rdword_of_val_mem; [|unfold s0Z; lia]. exact (HSV 1%nat ltac:(lia)). }
destruct (Z_le_gt_dec (ly_top lyc - 16) sp0) as [Hbad|Hgood].
- exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hbad | reflexivity].
- exists ((sp0, raZ regs, s0Z regs) :: ch). split; [|right; reflexivity]. right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, sp0 <= a -> a < ly_top ly ->
            rdword (aview SEGS (w_H Wc) memc) a = rdword (aview SEGS (w_H W) mem) a).
  { intros a Ha Hat. apply ts_rdword_keep. intros j Hj. apply F1; lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next sp0 (ly_top lyc) (s0Z regs)) eqn:Eb.
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
      rewrite Etop. apply (cb4_fpchain_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) memc) sp0);
        [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbv beta. intros r Hr. lia.
Qed.

(* ---- THE LIVE STATE ACROSS A CALL (crt102rw_live_call's B' twin): the callee's journal (from this function's
   state, at sp1) keeps the saved words, the spill of F, the frame's flag word and copy's shadow; the caller supplies
   the new side facts and the block relations. kb round: the live state at a budget kbg in, the caller's journal after
   the call at a budget WS2 with wbudget [] kbg' WS2 (the call rule's landing), the callee's journal at any WS1 ---- *)
Lemma cb4_live_call : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc
  STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lamc' peakc' cntc' ownc' ranc' {kbg kbg' : nat} {WS1 : list (list Z)},
  liveB kbg lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  (exists WS2, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS2 /\
     YCbqGwild.wbudget [] kbg' WS2) ->
  AJW STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  0 <= STK1 ->
  (forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1 /\
     ~ (frame_addr lyc CRT_CID pos + 504 <= a < frame_addr lyc CRT_CID pos + 512)) ->
  sideB ly2 S2 Hp2 W2 mem2 Lamc' peakc' cntc' ownc' ranc' ->
  Permutation Lamc' (Dx' ++ Lam) -> Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dx') ->
  (forall bk, In bk Dx' -> ~ In bk D) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  liveB kbg' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dx' Lamc' peakc' cntc' ownc' ranc'.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Dx' Lamc'
  peakc' cntc' ownc' ranc' kbg kbg' WS1 HL (WS2 & HJ2 & HB2) HJ1 HSTK1 HFP HSD HPL HPB HAP HMN'.
destruct (crt_live_journal HL) as (WSj & HJ & HBj). pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc. clear HL.
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (cb4_ff _ _ _ _ _ _ _ _ HJ2) as (_ & _ & _ & _ & _ & Ffr2 & Fsh2).
pose proof HJ1 as (_ & HLY1 & _ & _ & _ & _ & _ & _ & KS1 & _ & _ & KF1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by (unfold frame_addr; rewrite EFF; reflexivity).
assert (EFl : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos) by (unfold flag_addr; rewrite EFF; reflexivity).
rewrite EF in Ffr2, Fsh2.
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof cb4_sp as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KS : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KS1; lia. }
assert (KF : forall a, (F <= a < F + 512 \/ shadow_addr F <= a < shadow_addr F + 64) -> ~ inFP FP1 a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply (KF1 CRT_CID pos a Hin); [|exact Hn].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite cb4_fb. change (512 / 8) with 64. fold F. lia. }
assert (KSH : forall a, shadow_addr F <= a < shadow_addr F + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KF; [right; exact Ha|]. intros Hf. destruct (HFP a Hf) as (H1 & H2 & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *; lia. }
refine {| crt_live_journal := ex_intro _ WS2 (conj HJ2 HB2); crt_live_side := HSD; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := _ |}.
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact (HSV j Hj)].
  intros i Hi. apply KS. lia. }
{ pose proof (crt_frame_flag_word HFRM) as Hfl.
  refine {| crt_frame_listed := _; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - pose proof HJ2 as (_ & _ & _ & _ & _ & HFR2 & _). rewrite HFR2. left. reflexivity.
  - rewrite EF, EFl, <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite cb4_fb. fold F.
    apply KF; [left; lia|]. intros Hf. destruct (HFP _ Hf) as (_ & _ & H3). apply H3. lia.
  - intros a Ha. rewrite EF, cb4_fb in Ha. fold F in Ha. exact (proj1 (Ffr2 a Ha)). }
{ unfold crt_spill in *. rewrite EF. fold F.
  apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact HSPF].
  intros i Hi. apply KS. unfold CRT_SP_F. lia. }
{ rewrite EF. fold F. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply KSH.
  unfold shadow_addr, SHADOW_OFF in *. lia. }
{ rewrite EF. fold F. intros s Hs. pose proof (YM05.alloc_ceiling_val). rewrite KSH; [exact (HCH s Hs)|].
  unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *. lia. }
intros H0. exact (HMN' (HMNc H0)).
Qed.

(* ---- THE BUDGET STEP UP (kb round, the B' twin of Crt102Arms.arms_live_mono): a live state at a budget kb is a live
   state at every larger budget, since wbudget is an upper bound; only room is given up ---- *)
Lemma cb4_live_mono : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kb kb',
  liveB kb lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> (kb <= kb')%nat ->
  liveB kb' lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc kb kb' HL Hk.
destruct (crt_live_journal HL) as (WS & HJ & HB).
exact {| crt_live_journal := ex_intro _ WS (conj HJ (Nat.le_trans _ _ _ HB Hk)); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
         crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
         crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
         crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
         crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

(* ---- THE CLASS-24 BYTE BOUND AT THE JOIN, image B' (row T8's ask; the walk's owner's ruling of 2026-10-30: the
   row cites a NAME, it does not invent the fact). pj_free (&copy) at J needs `ccnt24 Sc <= L24 + DRV` (its text's
   entry, PRH_FnPj dc0d0aa79c0f: `v <> 0 -> ccnt24 S <= L24 + DRV`). It is NOT a field of crt_at_J_B, because the
   boundary already implies it, so a field would make every producer of J supply a derivable fact:
   - crt_at_J_B_r0 says r = 0, so the count's r = 1 arm (where the walk has left the model) is DEAD - the A' twin
     closes it the same way (Crt102Tail.v, crt102_tail's r = 1 case);
   - on the r = 0 arm, crt_pos gives the walk's room position at Sc, and PresetRoomCounts.counts_of_room_pos_rl turns any
     room position into the bound (the A' twin: Crt102Tail.v, crt102_tail's KONT application).
   The count's arms are a conjunction inside the one named field crt_at_J_B_count (the Records ruling), so the r = 0
   arm is read by position: crt_pos is its fifth conjunct. *)
Lemma cb_J_B_ccnt24 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  @crt_at_J_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
    ly S Hp W regs mem md doc t D Lam peak cnt ran most
    fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HJ.
destruct (crt_at_J_B_count HJ) as (cset & _ & _ & [(Hr1 & _) | (_ & _ & _ & _ & HP & _)]).
- exfalso. rewrite (crt_at_J_B_r0 HJ) in Hr1. discriminate Hr1.
- destruct (crt_pos_ex HP) as (pre & hist & HA).
  exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ (crt_pos_room HA))).
Qed.

End g.
End f.
End t4.

(* the moved names, and the assumptions of the nine *)
Locate cb4_fb.
Locate cb4_stkc.
Locate cb4_sp.
Locate cb4_ar0.
Locate cb4_ff.
Locate cb4_doc_home.
Locate cb4_ro_img.
Locate cb4_fregs_trans.
Locate cb4_rdword_of_val_mem.
Locate cb4_fpchain_keep.
Locate cb4_chain.
Locate cb4_live_call.
Locate cb4_live_mono.
Locate cb_J_B_ccnt24.
Print Assumptions cb4_sp.
Print Assumptions cb4_ff.
Print Assumptions cb4_doc_home.
Print Assumptions cb4_ar0.
Print Assumptions cb4_fb.
Print Assumptions cb4_live_call.
Print Assumptions cb4_live_mono.
Print Assumptions cb4_fregs_trans.
Print Assumptions cb4_ro_img.
Print Assumptions cb4_chain.
Print Assumptions cb_J_B_ccnt24.
