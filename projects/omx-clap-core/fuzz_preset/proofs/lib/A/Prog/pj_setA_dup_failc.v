(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the strdup REFUSAL exit of segment DUP of pj_set's image-A' walk (fuzz_preset asan,
   A 0x8685c; the cuts of lib/A/Prog/pj_setA_defs.v): the cut pjsA_FAILc at +0x7c, reached from the state `pjsdA_Cp`
   of lib/A/Prog/pj_setA_dup_mid.v (+0xb0) with dup = 0, once the walk has stored keys[n] := 0 (+0xfc) and taken
   `beqz a1` (+0x100). Only the eight bytes at keys + 8 n differ between the memory of `pjsdA_Cp` and the one here,
   and they are bytes of the object's keys block, a harness block of the ledger:
   - pj_set's frame, the caller's window and the image lie apart from that block (the block is below the
     allocator ceiling, the stack window above it; alx_blocks / blk_img_x), so pjsA_invR (at the re-hiding relation:
     the cut is past grow) rides;
   - the ledger rides (S1Ledger.v prh_ledger_kept_aview): every head word lies below its block's user bytes
     (PRH_Base.v prh_head_wide, the Section hypothesis HWIDE) and distinct blocks are apart (sep_blocks_x);
   - val's tree and slot ride (val's footprint is apart from the object's, pjsdA_Cp's last separation clause and
     the ledger's distinct block addresses);
   - the object keeps its n members (pj_setA_dup_tree.v pjsdA_obj_keep: the stored slot is past the used ones), and
     what pj_free(val) keeps of it is its whole footprint, by its journal and the call rule's extension clause
     (lib/A/Prog/pj_setA_miss_lem.v pjmA_free_agree / pjmA_obl_node, cited); the obligation is pj_fdR at the object's
     depth (pj_setA_glue.v pjsA_g_node_fd);
   - the memnorm keep rides by the store's own keep (pj_setA_dup_step.v pjsdA_sd, a premise here), and the class-24
     bound pjsA_PB and pj_free's hull budget are pjsdA_Cp's (fuzz_strdup's NULL keeps the model-run position, and its
     budget left after its use is pj_free's);
   - the NULL is the CHOSEN failure (pjsdA_Cp's NULL arm: cnt + c = fail, THE DEAD REFUSAL ARM of pj_setA_defs.v), so
     pjsA_FAILc's failure cell and its granted peak are pjsdA_Cp's.
   proves no function (kind: segment lemma, the FAIL exit of DUP).
   Numerals: 56 / 8 (LENGTH: the struct pj, a key pointer); 48 (LENGTH: pj_set's frame); 6 (the object tag);
   2 ^ 64 (DERIVED: the word range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps pj_setA_vis pj_setA_dup_step pj_setA_dup_sep pj_setA_dup_tree pj_setA_dup_mid.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_trans.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require pj_setA_miss_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjsA_g_vis B ARx.
Hypothesis HWIDE : prh_head_wide.
(* the walk's journal is past grow: at the re-hiding relation *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* what pj_free(val) keeps: pj_setA_miss_lem.v's pjm_* lemmas, cited by qualified name *)

(* ---- THE CUT: pjsA_FAILc after the refusal path's store keys[n] := 0 ---- *)
Lemma pjsdA_fail_cut : forall CTX0 dd en ly S Hp W regs mem md k
    dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr num3 str3 kids2 keys2 cap2v
    (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model),
  pjsA_pre B ARx CTX0 dd en ->
  pjsdA_Cp B ARx dd en ly S Hp W regs mem md k dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr
    num3 str3 kids2 keys2 cap2v ->
  dup = 0 ->
  (* mem1 is mem with the eight bytes at keys2 + 8 n overwritten *)
  (forall x, 0 <= x < 2 ^ 64 -> ~ (keys2 + 8 * jsA_n en <= x < keys2 + 8 * jsA_n en + 8) ->
     aview SEGS (w_H W) mem1 x = aview SEGS (w_H W) mem x) ->
  (forall x : word, ~ (keys2 + 8 * jsA_n en <= bv_unsigned x < keys2 + 8 * jsA_n en + 8) ->
     mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x) ->
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem1 x) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem1) ->
  (* the walk's own journal at mem1, and pj_set's registers *)
  AJ (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] ly S Hp W mem1 md1 k ->
  spZ regs1 = jsA_sp1 en ->
  getr regs1 8 = w64 (jsA_w en) -> getr regs1 18 = w64 (jsA_k en) -> getr regs1 20 = w64 SHADOW_OFF ->
  (forall r, In r PJSA_KEPT -> getr regs1 r = getr (jsA_regs en) r) ->
  pjsA_FAILc B ARx dd en ly S Hp W regs1 mem1 md1 k.
Proof.
intros CTX0 dd en ly S Hp W regs mem md k dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr
  num3 str3 kids2 keys2 cap2v regs1 mem1 md1 HPRE HCP Edup KV _ KP KMN HJ1 Hsp1 H8 H18 H20 HKEPT1.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HWIDE as Hw8. unfold prh_head_wide in Hw8.
unfold pjsA_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFWIN & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAPW & _).
pose proof HFWIN as (Hd0 & _).
destruct HCP as (HINV & HROOM & _ & _ & HLED3 & Hoks & Hfa & Hokc & HNI & HpLam & HpLam2 & HBLK & HpD & HpDo &
  _ & _ & HNEW & HCASE & Hncap & HNODEo & HHDRo & _ & HNODEW & HDATAC & HWO2 & HWCEIL & _ & _ & _ & _ & _ & HARM).
destruct HARM as [(_ & ELam & Ecf & Epeak & Hokn & HPB & HHB) | (Hdup & _)]; [|exfalso; exact (Hdup Edup)].
subst Lam3.
pose proof HINV as (HJ & HWIN & _ & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & _ & _ & _ & _ & HPRES & HROD & HMN).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_stk HJ) as Hast.
pose proof (ajxR_ar HJ1) as HAR1.
pose proof Hast as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HDATAC as (_ & HPLo & HSW & _).
pose proof HPLo as (HO4096 & HatO & _ & HamrO & _).
pose proof HSW as (HW4096 & _).
assert (HSTK48 : 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
assert (HSTKF : 0 <= STK_pj_free dd) by (unfold STK_pj_free, zmaxl; cbn [fold_right];
  pose proof (pi_frame_nonneg F_pj_free); lia).
assert (Hsp0c : YM05.alloc_ceiling <= jsA_sp0 en - STK_pj_set dd) by lia.
assert (Hsp0 : YM05.alloc_ceiling <= jsA_sp0 en) by lia.
assert (HOTOP : jsA_o en + 56 <= kHighMemEnd) by (destruct HamrO as [Hx | (Hx1 & Hx2)]; lia).
(* ---- the object's node: its header is the cut's, its block list starts with the two slot arrays ---- *)
pose proof HNODEo as HN1. cbn [pj_nodeR PjTree.tag] in HN1.
destruct HN1 as (HND & HNA & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hh0' & _ & En0 & _ & Hcap0' & Di & ED & _).
pose proof HHDRo as (_ & _ & _ & _ & Hk1 & Hy1 & Hn1 & Hc1).
pose proof Hh0' as (_ & _ & _ & _ & Hk2 & Hy2 & Hn2 & Hc2).
pose proof (pjsdtA_u64_uniq SEGS _ _ _ _ Hk2 Hk1) as Ek. subst kids0.
pose proof (pjsdtA_u64_uniq SEGS _ _ _ _ Hy2 Hy1) as Ey. subst keys0.
pose proof (pjsdtA_u64_uniq SEGS _ _ _ _ Hn2 Hn1) as En. subst n0.
pose proof (pjsdtA_u64_uniq SEGS _ _ _ _ Hc2 Hc1) as Ec. subst cap0.
assert (Enl : jsA_n en = Z.of_nat (length (jsA_ms en))) by lia.
assert (Hn0 : 0 <= jsA_n en) by lia.
assert (Hcap : 0 < cap2v) by lia.
destruct Hcap0' as [(E0 & _ & _) | (_ & HkidL & HkeyL)]; [lia|].
rewrite (proj2 (Z.eqb_neq cap2v 0)) in ED by lia. cbn [app] in ED.
assert (HkeyDo : In (keys2, 8 * cap2v) Do) by (rewrite ED; right; left; reflexivity).
assert (HkNotDi : ~ In (keys2, 8 * cap2v) Di).
{ assert (HNDl : List.NoDup Do) by (first [exact HND | apply NoDup_ListNoDup; exact HND]).
  rewrite ED in HNDl. apply NoDup_cons_iff in HNDl as [_ HNDl]. apply NoDup_cons_iff in HNDl as [Hx _]. exact Hx. }
pose proof HLED3 as (_ & HNDL & _).
assert (HNDL' : List.NoDup (map fst Lam2)) by (first [exact HNDL | apply NoDup_ListNoDup; exact HNDL]).
assert (Hkk : kids2 <> keys2).
{ intros E. rewrite E in HkidL. pose proof (prh_fst_unique Lam2 keys2 _ _ HNDL HkidL HkeyL) as Esz. lia. }
(* ---- the keys block: a harness block, its allocator block below the ceiling, off the image ---- *)
destruct (pjsdA_hb B ARx LAWS ly S Hp W mem md Lam2 peak3 _ fail3 ran3 _ _ keys2 (8 * cap2v) HAR HLED3 HkeyL)
  as (Hk0 & Hkab & Hkce & Rk).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hkab) as (_ & Hk4096 & _ & Hkapp & _).
assert (HWR : forall x, keys2 + 8 * jsA_n en <= x < keys2 + 8 * jsA_n en + 8 ->
  keys2 <= x < keys2 + 8 * cap2v /\ x < YM05.alloc_ceiling /\ ~ in_img SEGS x /\ app_addr x).
{ intros x Hx.
  assert (Hxb : keys2 - cf_head <= x < keys2 - cf_head + req_size (8 * cap2v + cf_head)) by lia.
  split; [lia|]. split; [lia|].
  split; [exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hkab Hxb)|].
  exact (in_app_addr _ _ x Hkapp Hxb). }
(* ---- what the store keeps ---- *)
assert (KHI : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KV; [lia|]. intros Hx. destruct (HWR a Hx) as (_ & Hc & _). lia. }
assert (KIMG : forall a, in_img SEGS a -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Hi. pose proof (Hsegs a Hi) as Hlo. apply KV; [lia|].
  intros Hx. destruct (HWR a Hx) as (_ & _ & Hn & _). exact (Hn Hi). }
assert (KSHD : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W) mem1 s = aview SEGS (w_H W) mem s).
{ intros s Hs. apply KV; [lia|]. intros Hx. destruct (HWR s Hx) as (_ & _ & _ & Happ).
  unfold app_addr, kLowShadowBeg in Happ. lia. }
assert (KVM : forall a v, YM05.alloc_ceiling <= a -> a + 8 <= 2 ^ 64 ->
  val_mem SEGS (rdW W mem) a 8 v -> val_mem SEGS (rdW W mem1) a 8 v).
{ intros a v Ha1 Ha2 Hv. apply (pj_valR_frame SEGS _ _ a 8%nat v Hv). intros x Hx.
  change (Z.of_nat 8) with 8 in Hx. apply (mbyte_of_aview SEGS). apply KHI. lia. }
assert (MG : mem_grows (rdW W mem) (rdW W mem1)) by exact (pjsnA_grows (w_H W) mem mem1 KP).
assert (AGR : forall X : Z -> Prop,
  (forall x, X x -> 0 <= x < 2 ^ 64 /\ ~ (keys2 + 8 * jsA_n en <= x < keys2 + 8 * jsA_n en + 8)) ->
  pj_agreeR SEGS (rdW W mem) (rdW W mem1) X).
{ intros X HX x Hx. destruct (HX x Hx) as (Hr & Hn). split.
  - exact (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem1 x (KV x Hr Hn)).
  - intros Hw. exact (writable_at_grows SEGS _ _ x MG Hw). }
assert (KSH : forall p nn, 0 <= p -> p + nn <= kHighMemEnd ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p nn ->
  range_addressable (aview SEGS (w_H W) mem1) SHADOW_OFF p nn).
{ intros p nn Hp0 Hpn HR. eapply range_addressable_agree; [|exact HR]. intros x Hx.
  pose proof (YCbq.shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
  apply KSHD. exact Hsx. }
assert (KHU : forall p nn, 0 <= p -> 0 < nn -> p + nn <= kHighMemEnd ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p nn -> shadow_hull_vis (aview SEGS (w_H W) mem1) p nn).
{ intros p nn Hp0 Hn Hpn HH s Hs.
  rewrite (KSHD s (pjsA_hull_bounds p nn s Hp0 Hn Hpn Hs)). exact (HH s Hs). }
(* ---- the ledger's blocks: Do's and Dw's are distinct harness blocks, apart from the stored slot ---- *)
assert (HDoL : forall a ka, In (a, ka) Do -> In (a, ka) Lam2)
  by (intros a ka H; apply (Permutation_in _ (Permutation_sym HpLam2)); apply in_or_app; left; exact H).
assert (HDwL : forall a ka, In (a, ka) (jsA_Dw en) -> In (a, ka) Lam2).
{ intros a ka H. apply (Permutation_in _ (Permutation_sym HpLam2)). apply in_or_app. right.
  apply in_or_app. left. exact H. }
pose proof (Permutation_NoDup (Permutation_map fst HpLam2) HNDL') as HNDf. rewrite !map_app in HNDf.
assert (HDoDw : forall a ka a' ka', In (a, ka) Do -> In (a', ka') (jsA_Dw en) -> a <> a').
{ intros a ka a' ka' H1 H2 Ea. subst a'.
  apply (pjsdA_nodup_apart (map fst Do) _ a HNDf).
  - apply in_map_iff. exists (a, ka). split; [reflexivity | exact H1].
  - apply in_or_app. left. apply in_map_iff. exists (a, ka'). split; [reflexivity | exact H2]. }
assert (HDDw : forall bk, In bk (jsA_Dw en) -> ~ In bk Do).
{ intros [a ka] H1 H2. exact (HDoDw a ka a ka H2 H1 eq_refl). }
assert (HrngL : forall a ka x, In (a, ka) Lam2 -> a <= x < a + ka -> 0 <= x < 2 ^ 64).
{ intros a ka x Hin Hx.
  destruct (pjsdA_hb B ARx LAWS ly S Hp W mem md Lam2 peak3 _ fail3 ran3 _ _ a ka HAR HLED3 Hin) as (Hka & Hab & Hce & Rq).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Ha4096 & _). lia. }
assert (HoffK : forall a ka x, In (a, ka) Lam2 -> a <> keys2 -> a <= x < a + ka ->
  ~ (keys2 + 8 * jsA_n en <= x < keys2 + 8 * jsA_n en + 8)).
{ intros a ka x Hin Hne Hx Hw.
  apply (pjsdA_lam_disj B ARx LAWS ly S Hp W mem md Lam2 peak3 _ fail3 ran3 _ _ a ka keys2 (8 * cap2v)
    HAR HLED3 Hin HkeyL Hne x Hx). lia. }
(* ======== pjsA_invR at the new memory ======== *)
assert (HINV1 : pjsA_invR B ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) dd en ly S Hp W regs1 mem1 md1 k).
{ unfold pjsA_invR.
  split; [exact HJ1|].
  split; [intros a Ha Hfp; rewrite KHI by (unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia); exact (HWIN a Ha Hfp)|].
  split; [exact Hsp1|].
  split; [apply KVM; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hra]|].
  split; [apply KVM; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hs0]|].
  split; [apply KVM; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hs1]|].
  split; [apply KVM; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hs2]|].
  split; [apply KVM; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hs3]|].
  split; [apply KVM; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hs4]|].
  split; [exact H8|]. split; [exact H18|]. split; [exact H20|]. split; [exact HKEPT1|].
  split; [intros a Ha; apply KP; exact (HPRES a Ha)|].
  split.
  { intros a Hro Hos Her.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
      [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
    rewrite (KIMG a Hi). exact (HROD a Hro Hos Her). }
  (* the memnorm keep: the cut's, then the store's *)
  intros HMN0. exact (KMN (HMN HMN0)). }
(* ======== the ledger at the new memory: statics and head words kept ======== *)
assert (HLED1 : prh_ledger (PA := PA) B ly S Hp W mem1 Lam2 peak3 (jsA_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (jsA_most en) (jsA_own en)).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem1 Lam2 peak3 _ fail3 ran3 _ _ HLED3).
  - intros a Ha. apply KIMG. exact (pst_in_img_A a Ha).
  - intros a kk i Hin Hi.
    destruct (pjsdA_hb B ARx LAWS ly S Hp W mem md Lam2 peak3 _ fail3 ran3 _ _ a kk HAR HLED3 Hin)
      as (Hk0' & Hab' & Hce' & Rq').
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab') as (_ & H4096' & _).
    apply KV; [lia|]. intros Hw.
    destruct (Z.eq_dec a keys2) as [Ea | Ea]; [lia|].
    assert (Hne : (a - cf_head, kk + cf_head) <> (keys2 - cf_head, 8 * cap2v + cf_head))
      by (intros E; injection E as E1 _; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab' Hkab Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - intros a kk _ H. exact H.
  - apply Permutation_refl. }
(* ======== val: its tree and its slot ride ======== *)
assert (HNODEW1 : pj_nodeR SEGS (rdW W mem1) (prh_lin Lam2) (jsA_w en) (jsA_tv en) (jsA_Dw en)).
{ apply (pjst_node_frame SEGS (jsA_tv en) _ _ _ _ (jsA_w en) (jsA_Dw en) HNODEW); [|intros a kk H; exact (HDwL a kk H)].
  apply AGR. intros x [Hx | ((a', k') & Hb & Hx)].
  - split; [lia|]. intros Hw. destruct (HWR x Hw) as (Hkx & _).
    apply (HWO2 x Hx). right. exists (keys2, 8 * cap2v). split; [exact HkeyDo | unfold pj_holdsR; cbn [fst snd]; lia].
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx. split; [exact (HrngL a' k' x (HDwL a' k' Hb) Hx)|].
    apply (HoffK a' k' x (HDwL a' k' Hb)); [|exact Hx].
    intros E. exact (HDoDw keys2 (8 * cap2v) a' k' HkeyDo Hb (eq_sym E)). }
assert (HSLOTW1 : prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam2 W (jsA_regs en) mem1 (jsA_w en)).
{ destruct HSW as (H4096 & Hat & Hrw & Hamr & Hown & Hra' & Hhull).
  split; [exact H4096|]. split; [exact Hat|].
  split; [split; [exact (proj1 Hrw)|]; intros x Hx; exact (writable_at_grows SEGS _ _ x MG (proj2 Hrw x Hx))|].
  split; [exact Hamr|]. split; [exact Hown|].
  split; [apply KSH; [lia | lia | exact Hra'] | apply KHU; [lia | lia | lia | exact Hhull]]. }
(* ======== the object keeps its n members (the stored slot is past them) ======== *)
assert (HNODEo1 : pj_nodeR SEGS (rdW W mem1) (prh_lin Lam2) (jsA_o en) (PjTree.JObj (jsA_ms en)) Do).
{ pose proof HNODEo as HN0. rewrite ED in HN0 |- *.
  apply (pjsdA_obj_keep (rdW W mem) (rdW W mem1) (prh_lin Lam2) (prh_lin Lam2)
    (jsA_o en) num3 str3 kids2 keys2 (jsA_n en) cap2v (jsA_ms en) Di HN0 HHDRo Enl Hn0 (Z.lt_le_incl _ _ Hncap)).
  - apply AGR. intros x Hx. cbv beta in Hx. destruct Hx as [Hx | [Hx | [Hx | ((a', k') & Hb & Hx)]]].
    + split; [lia|]. intros Hw. destruct (HWR x Hw) as (Hkx & _).
      apply (HNA (keys2, 8 * cap2v) x HkeyDo); [unfold pj_holdsR; cbn [fst snd]; lia | exact Hx].
    + split; [apply (HrngL kids2 (56 * cap2v) x HkidL); lia|].
      apply (HoffK kids2 (56 * cap2v) x HkidL Hkk). lia.
    + split; [apply (HrngL keys2 (8 * cap2v) x HkeyL); lia|]. lia.
    + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      assert (Hin' : In (a', k') Lam2) by (apply HDoL; rewrite ED; right; right; exact Hb).
      split; [exact (HrngL a' k' x Hin' Hx)|].
      apply (HoffK a' k' x Hin'); [|exact Hx].
      intros E. subst a'.
      pose proof (prh_fst_unique Lam2 keys2 _ _ HNDL Hin' HkeyL) as Esz. subst k'. exact (HkNotDi Hb).
  - intros a kk H. unfold prh_lin. apply HDoL. rewrite ED. exact H. }
(* ======== the cut ======== *)
destruct pjsA_glue_holds as (Hfd & _ & _ & _ & Hlen & _).
unfold pjsA_FAILc.
split; [exact HINV1|]. split; [exact HROOM|].
exists Lam2, peak3, fail3, ran3, (Datatypes.S c), ok3, Do, Lr.
split; [exact HLED1|].
split; [exact Hoks|].
split; [exact Hfa|].
split; [exact HpLam|].
split; [exact HpLam2|].
split; [exact HBLK|].
split; [exact HNI|].
split.
{ rewrite Hlen. destruct HCASE as [(Hnc & -> & _) | (Hnc & -> & _)].
  - rewrite (proj2 (Z.eqb_neq (jsA_n en) (jsA_cap en))) by lia. cbv iota. lia.
  - rewrite (proj2 (Z.eqb_eq (jsA_n en) (jsA_cap en)) Hnc). cbv iota. lia. }
split; [replace (Datatypes.S c - 1)%nat with c by lia; exact Hokn|].
split; [intros i Hi; apply Hokc; lia|].
split; [replace (Datatypes.S c - 1)%nat with c by lia; exact Ecf|].
split; [exact Epeak|].
split; [exact HPB|].
split.
{ exists Dold, Dnew, Dr. split; [exact HpD|]. split; [exact HpDo|]. split; [exact HNEW|].
  destruct HCASE as [(Hnc & -> & _ & _ & _ & EDold & EDnew) | (Hnc & -> & _ & EDold & EDnew)].
  - left. split; [reflexivity|]. split; [exact EDold | exact EDnew].
  - right. right. split; [exact Hnc|]. split; [reflexivity|]. split; [exact EDold|].
    exists kids2, keys2. exact EDnew. }
split.
{ intros md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 HJf HXf HP3.
  assert (HN3 : pj_nodeR SEGS (rdW W3 mem3) (prh_lin Lam3) (jsA_o en) (PjTree.JObj (jsA_ms en)) Do)
    by exact (pj_setA_miss_lem.pjmA_obl_node B ARx LAWS dd en ly S Hp W mem1 md1 Lam2 peak3 _ fail3 ran3 _ _ md0 ly3 S3 Hp3 W3 mem3 md3 k3
      Lam3 Lr _ Do Hsp0 HSTKF HAR1 HLED1 HatO HDoL HDwL HDDw HAPW HWO2 HJf HXf HNODEo1 HP3).
  split.
  - exact (Hfd SEGS _ _ _ _ _ _ HN3 (le_n _)).
  - intros _. exact HN3. }
split; [exact HNODEW1|]. split; [exact HSLOTW1 | exact HHB].
Qed.

End x.
