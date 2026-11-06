(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the cut pjs_TAIL that the GRANTED strdup arm of segment DUP of pj_set's image-B walk
   reaches (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of lib/B/Prog/pj_set_defs.v). From the state `pjsd_Cp` at
   +0xb0 (lib/B/Prog/pj_set_dup_mid.v) with dup <> 0, after the two stores keys[n] := dup and n := n + 1 (the
   object's field at o + 40), the join +0x50 holds of the new memory with dest = kids + 56 n and a2 = 56.
   pjsd_tail_cut takes each store as the memory facts pj_set_dup_step.v pjsd_sd hands on, and the walk's own
   journal at the new memory. The cut's obligation is the post arm tpsP_A2 (the key was absent and every allocation
   was granted); the object gains the member by pj_set_dup_tree.v pjsd_obj_app. tpsP_Q's res = 0 position is pjsd_Cp's
   (fuzz_strdup's granted HMal advanced it past the call's events); the memnorm keep is the cut's, then the two
   stores' (pjsd_sd's keep, a premise here). On this arm res = 0, so DEAD-PJSET and the prh_granted clause hold
   outright. The block conjunct (a Permutation against PresetReqAtNoMiss.tblk of the object with the member
   appended) is pjdt_tblk_app, from pjs_pre's tblk Permutation of the entry object, pjs_DUP's capacities
   (cap = ncap |ms|, cap2v = ncap (S |ms|)) and its ordered block equations (all carried by `pjsd_Cp`).
   FREEORD-COPY (the result's ordered free list): pjs_DUP's ordered list of the object (carried by `pjsd_Cp` to
   the state after fuzz_strdup) is cut by pj_set_trans.v pjsf_obj_dest into its slot list and its arrays; the slot
   list is framed to the final memory (PRH_PjOrder.pf_oitemsR_frame, over the agreement pjsd_obj_app's member frame
   uses); slot n is the key block (dup, |kname| + 1) and val's ordered list Fw (the conjunct's premise, at the entry
   memory), framed to the state after fuzz_strdup by val's entry agreement (pjsd_Cp; PRH_PjOrder.pj_foR_frame) and
   moved into kids + 56 n by pjsf_foR_move (the 56-byte copy); pjsf_oitems_one / pjsf_oitems_app / pjsf_obj_intro
   reassemble the object, PjFoMember.pfm_foR_perm puts its block list in pj_nodeR's order, and pjsf_slots_app /
   pjsf_arrz_of give the requests fo (JObj (ms ++ [(kname, tv)])).
   proves no function (kind: cut lemma).
   Helper lemmas of lib/B/Prog/pj_set_ret_lem.v (pjr_hb, pjr_lam_sep, pjr_place_head, pjr_at_where, pjr_hbl_in,
   pjr_hbl_inFP, pjr_mbyte_aview2, pjr_node_nodup) are cited by qualified name.
   Section premise beyond LAWS / VIS: HWIDE (PRH_Base.v prh_head_wide, 8 <= cf_head): the ledger at the new memories
   reads each harness block's 8-byte head at a - cf_head, which lies below the user bytes the stores write.
   Numerals: 56 (LENGTH: the struct pj); 8 / 40 / 48 (LENGTH: a key pointer, the field n); 6 (the object tag).
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
S1ImgB pj_set_defs pj_set_glue pj_set_steps pj_set_trans pj_set_vis
pj_set_dup_step pj_set_dup_sep pj_set_dup_tree pj_set_dup_mid.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_set_ret_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- pure list facts ---- *)
Lemma pjdt_nodup_app_l : forall {A : Type} (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
intros A l l' H. induction l as [|x l IH]; cbn [app] in H; [constructor|].
apply NoDup_cons_iff in H as [Hx H]. constructor.
- intros Hin. apply Hx. apply in_or_app. left. exact Hin.
- exact (IH H).
Qed.

(* a block listed twice in a list whose ranges are pairwise disjoint has an empty range *)
Lemma pjdt_pw_dup : forall (l1 l2 : list (Z * Z)) y,
  YG0f.pairwise YG0f.zdisjoint (map (fun b => (fst b, req_size (snd b))) (l1 ++ y :: l2)) ->
  In y (l1 ++ l2) -> 1 <= req_size (snd y) -> False.
Proof.
intros l1. induction l1 as [|z t IH]; intros l2 y HP Hin Hr; cbn [app map YG0f.pairwise] in HP.
- destruct HP as [HF _]. rewrite Forall_forall in HF.
  assert (Hy : In (fst y, req_size (snd y)) (map (fun b => (fst b, req_size (snd b))) l2))
    by (apply in_map_iff; exists y; split; [reflexivity | exact Hin]).
  pose proof (HF _ Hy) as Hd. unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- destruct HP as [HF HP']. destruct Hin as [Ez | Hin].
  + subst z. rewrite Forall_forall in HF.
    assert (Hy : In (fst y, req_size (snd y)) (map (fun b => (fst b, req_size (snd b))) (t ++ y :: l2))).
    { apply in_map_iff. exists y. split; [reflexivity|]. apply in_or_app. right. left. reflexivity. }
    pose proof (HF _ Hy) as Hd. unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + exact (IH l2 y HP' Hin Hr).
Qed.

Lemma pjdt_perm_twice : forall (l L1 L2 : list (Z * Z)) x,
  YG0f.pairwise YG0f.zdisjoint (map (fun b => (fst b, req_size (snd b))) l) ->
  Permutation l (L1 ++ L2) -> In x L1 -> In x L2 -> 1 <= req_size (snd x) -> False.
Proof.
intros l L1 L2 x HP HPm H1 H2 Hr.
assert (Hxl : In x l) by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; left; exact H1).
destruct (in_split x l Hxl) as (l1 & l2 & El). subst l.
destruct (in_split x L1 H1) as (u & v & EL1). subst L1.
rewrite <- app_assoc in HPm. cbn [app] in HPm.
pose proof (Permutation_app_inv l1 l2 u (v ++ L2) x HPm) as HP2.
apply (pjdt_pw_dup l1 l2 x HP); [|exact Hr].
apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

(* the model's capacity after a parsed item is never 0 *)
Lemma pjdt_ncap_pos : forall k, (0 < PresetReqAt.ncap (Datatypes.S k))%nat.
Proof.
intros k. cbn [PresetReqAt.ncap]. unfold PjRoundTrip.gcap.
destruct (Nat.ltb_spec k (PresetReqAt.ncap k)); [lia|].
destruct (Nat.eqb_spec (PresetReqAt.ncap k) 0); lia.
Qed.

(* ---- the block conjunct of tpsP_A2, tpsP_Q's second arm (PresetReqAtNoMiss.tblk / arrz / ncap / kblk) ---- *)
(* the absent arm's final block list, in pj_nodeR's order (the arrays at the capacity the arm ends with, D's member
   blocks Dr, the key's block, val's blocks Dw), against tblk of the object with the member appended, up to order:
   the entry's tblk Permutation names the arrays at capf 0 0 |ms| = ncap |ms| = cap (PresetReqAtNoMiss.ncap_eq; an
   empty object has cap = 0 and its D no arrays), the arm ends at ncap (S |ms|) = cap2v *)
Lemma pjdt_tblk_app : forall (ms : list (list Z * PjTree.jv)) (kname : list Z) (tv : PjTree.jv)
    (D Dold Dr Dnew Dw Di : list (Z * Z)) (kids keys kids2 keys2 n cap cap2v a : Z),
  Permutation (map (fun b => snd b + PresetReqAt.HEAD) D) (PresetReqAtNoMiss.tblk (PjTree.JObj ms)) ->
  Permutation (map (fun b => snd b + PresetReqAt.HEAD) Dw) (PresetReqAtNoMiss.tblk tv) ->
  length (flat_map PjRoundTrip.ech kname) = length kname ->
  n = Z.of_nat (length ms) ->
  cap = Z.of_nat (PresetReqAt.ncap (length ms)) ->
  cap2v = Z.of_nat (PresetReqAt.ncap (Datatypes.S (length ms))) ->
  D = Dold ++ Dr ->
  (kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di = Dnew ++ Dr ->
  (n < cap /\ cap2v = cap /\ Dold = [] /\ Dnew = [] \/
   n = cap /\ cap2v = cap2R cap /\ Dold = kids_blkR kids cap ++ keys_blkR 6 keys cap /\
   Dnew = [(kids2, 56 * cap2R cap); (keys2, 8 * cap2R cap)]) ->
  Permutation (map (fun b => snd b + PresetReqAt.HEAD)
    ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (a, Z.of_nat (length kname) + 1) :: Dw))
    (PresetReqAtNoMiss.tblk (PjTree.JObj (ms ++ [(kname, tv)]))).
Proof.
intros ms kname tv D Dold Dr Dnew Dw Di kids keys kids2 keys2 n cap cap2v a HD HDw Hech En Ecap Ecap2 ED EDo HC.
set (f := fun m : list Z * PjTree.jv => PresetReqAtNoMiss.kblk (fst m) :: PresetReqAtNoMiss.tblk (snd m)).
set (C := concat (map f ms)).
assert (Ht0 : PresetReqAtNoMiss.tblk (PjTree.JObj ms) =
  PresetReqAt.arrz true (PresetReqAt.ncap (length ms)) ++ C).
{ rewrite PresetReqAtNoMiss.ncap_eq. reflexivity. }
assert (Ht1 : PresetReqAtNoMiss.tblk (PjTree.JObj (ms ++ [(kname, tv)])) =
  PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length ms))) ++
  C ++ PresetReqAtNoMiss.kblk kname :: PresetReqAtNoMiss.tblk tv).
{ change (PresetReqAtNoMiss.tblk (PjTree.JObj (ms ++ [(kname, tv)]))) with
    (PresetReqAt.arrz true (PresetReqAtNoMiss.capf 0 0 (length (ms ++ [(kname, tv)]))) ++
     concat (map f (ms ++ [(kname, tv)]))).
  rewrite length_app, map_app, concat_app. cbn [length map concat]. rewrite app_nil_r.
  rewrite Nat.add_1_r, <- PresetReqAtNoMiss.ncap_eq. reflexivity. }
assert (Hkb : PresetReqAtNoMiss.kblk kname = Z.of_nat (length kname) + 1 + PresetReqAt.HEAD).
{ unfold PresetReqAtNoMiss.kblk. rewrite Hech. lia. }
assert (HA1 : map (fun b => snd b + PresetReqAt.HEAD) [(kids2, 56 * cap2v); (keys2, 8 * cap2v)] =
  PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length ms)))).
{ rewrite Ecap2. exact (pjsf_arrz_of kids2 keys2 _ (pjdt_ncap_pos (length ms))). }
(* the members' blocks of the entry object are C up to order *)
assert (HDi : Permutation (map (fun b => snd b + PresetReqAt.HEAD) Di) C).
{ rewrite Ht0, ED, map_app in HD.
  destruct HC as [(Hlt & Ec & EDold & EDnew) | (Heq & Ec & EDold & EDnew)].
  - subst Dold Dnew. cbn [app] in EDo. cbn [app map] in HD. rewrite <- EDo in HD.
    assert (Hnc : PresetReqAt.ncap (Datatypes.S (length ms)) = PresetReqAt.ncap (length ms)) by lia.
    change (map (fun b => snd b + PresetReqAt.HEAD) ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di)) with
      (map (fun b => snd b + PresetReqAt.HEAD) [(kids2, 56 * cap2v); (keys2, 8 * cap2v)] ++
       map (fun b => snd b + PresetReqAt.HEAD) Di) in HD.
    rewrite HA1, Hnc in HD. exact (Permutation_app_inv_l _ _ _ HD).
  - subst Dnew. cbn [app] in EDo.
    apply (f_equal (@tl _)) in EDo. apply (f_equal (@tl _)) in EDo. cbn [tl] in EDo. subst Dr.
    assert (HA0 : map (fun b => snd b + PresetReqAt.HEAD) Dold = PresetReqAt.arrz true (PresetReqAt.ncap (length ms))).
    { rewrite EDold. unfold kids_blkR, keys_blkR.
      destruct (Z.eq_dec cap 0) as [E0 | N0].
      - rewrite E0, Z.eqb_refl. cbn [orb app map].
        replace (PresetReqAt.ncap (length ms)) with 0%nat by lia. reflexivity.
      - rewrite (proj2 (Z.eqb_neq cap 0) N0). change (6 =? 6) with true. cbn [orb negb app].
        rewrite Ecap. apply pjsf_arrz_of. lia. }
    rewrite HA0 in HD. exact (Permutation_app_inv_l _ _ _ HD). }
rewrite Ht1.
change (map (fun b => snd b + PresetReqAt.HEAD)
    ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (a, Z.of_nat (length kname) + 1) :: Dw)) with
  (map (fun b => snd b + PresetReqAt.HEAD) [(kids2, 56 * cap2v); (keys2, 8 * cap2v)] ++
   map (fun b => snd b + PresetReqAt.HEAD) (Di ++ (a, Z.of_nat (length kname) + 1) :: Dw)).
rewrite HA1, map_app. cbn [map fst snd].
apply Permutation_app_head. apply Permutation_app; [exact HDi|].
rewrite Hkb. apply perm_skip. exact HDw.
Qed.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjs_g_vis B ARx.
Hypothesis HWIDE : prh_head_wide.
(* the walk's journal after grow: at the re-hiding relation wle' (YA0nH over preset's zone) *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).

(* ---- memory views ---- *)
Lemma pjdt_val_kept : forall (W W' : world SEGS) mem mem' a n v,
  val_mem SEGS (mrestrict (w_H W) mem) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  val_mem SEGS (mrestrict (w_H W') mem') a n v.
Proof.
intros W W' mem mem' a n v Hv E.
apply (pj_valR_frame SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') a n v Hv).
intros x Hx. exact (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' x (E x Hx)).
Qed.

(* ---- the ledger's blocks (pj_set_ret_lem.v's lemmas at HW8 := HWIDE) ---- *)
(* a byte of a ledger block's head is no user byte of any ledger block *)
Lemma pjdt_head_user : forall ly S Hp W mem md Lam peak cnt fail ran most own a k0 a' k' y,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k0) Lam -> In (a', k') Lam -> a - cf_head <= y < a -> ~ (a' <= y < a' + k').
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k0 a' k' y HAR HL Hin Hin' Hy Hy'.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam peak cnt fail ran most own a k0 HAR HL Hin) as (Hk0 & _).
destruct (Z.eq_dec a a') as [Ea | Na].
- subst a'. lia.
- apply (pj_set_ret_lem.pjr_lam_sep B ARx LAWS HWIDE ly S Hp W mem md Lam peak cnt fail ran most own a k0 a' k' y HAR HL Hin Hin'
    ltac:(intros E; injection E as E1 _; exact (Na E1)) ltac:(lia)). lia.
Qed.

(* ---- THE CUT: pjs_TAIL after keys[n] := dup and n := n + 1 ---- *)
Lemma pjsd_tail_cut : forall CTX0 dd en ly S Hp W regs mem md k
    dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr num3 str3 kids2 keys2 cap2v
    (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  pjs_pre B ARx CTX0 dd en ->
  pjsd_Cp B ARx dd en ly S Hp W regs mem md k dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr
    num3 str3 kids2 keys2 cap2v ->
  dup <> 0 ->
  (* mem2 is mem with keys[n] := dup and the header's n := n + 1 *)
  (forall x, 0 <= x < 2 ^ 64 -> ~ (keys2 + 8 * js_n en <= x < keys2 + 8 * js_n en + 8) ->
     ~ (js_o en + 40 <= x < js_o en + 48) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x) ->
  (forall x : word, ~ (keys2 + 8 * js_n en <= bv_unsigned x < keys2 + 8 * js_n en + 8) ->
     ~ (js_o en + 40 <= bv_unsigned x < js_o en + 48) ->
     mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (keys2 + 8 * js_n en) 8 dup ->
  val_mem SEGS (mrestrict (w_H W) mem2) (js_o en + 40) 8 (js_n en + 1) ->
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem2 x) ->
  (* the two stores' memnorm keep (pj_set_dup_step.v pjsd_sd) *)
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  (* the walk's own journal at mem2, and pj_set's registers *)
  AJ (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp W mem2 md2 k ->
  spZ regs2 = js_sp1 en ->
  getr regs2 8 = w64 (js_w en) -> getr regs2 18 = w64 (js_k en) -> getr regs2 20 = w64 SHADOW_OFF ->
  (forall r, In r PJS_KEPT -> getr regs2 r = getr (js_regs en) r) ->
  getr regs2 10 = w64 (kids2 + 56 * js_n en) -> getr regs2 12 = w64 56 ->
  pjs_TAIL B ARx dd en ly S Hp W regs2 mem2 md2 k.
Proof.
intros CTX0 dd en ly S Hp W regs mem md k dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr num3 str3
  kids2 keys2 cap2v regs2 mem2 md2 HPRE HCP Hdupnz HVA HMR HVK HVN HPR KMN HJ2 Hsp2 E8 E18 E20 EKEPT E10 E12.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
pose proof (@cf_head_nonneg cp) as Hh0. pose proof HWIDE as Hh8. unfold prh_head_wide in Hh8.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & HFWIN & HNODE0 & HHDR0 & _ & _ & _ & _ & _ & _ & _ & HAPW &
  _ & _ & _ & _ & _ & _ & _ & HKLEN & _ & _ & HTBLK0 & _ & HHEAD & _).
pose proof HFPRE as ((_ & _ & _ & _ & _ & Hstk0 & _) & _).
pose proof Hstk0 as (_ & HSTK0 & Hceil & Hslo & _ & H47 & _ & _ & Htop20).
pose proof HFWIN as (Hd0 & _ & Hdtop & _).
destruct HCP as (HINV & HROOM & _ & _ & HLED3 & HOKS3 & HFA3 & _ & HNI & HpLam & HpLam2 & HBLK3 &
  HpD & HpDo & HoD & HoDo & HNEW & HCASE & Hncap2 & HNODE3 & HHDR3 & HSLOTS & HNODEW3 & HDATA3 & HWAP & HWCEIL & HWPRES &
  Hcapm & Hcap2m & HFO3 & HAGRW3 & HARMD).
destruct HARMD as [(Hz & _) | (_ & EL3 & Hpeak3 & Hokall3 & HBYT & _ & _ & HdupO & HdupW & HPOSF)];
  [exfalso; exact (Hdupnz Hz)|].
pose proof HINV as (HJ & HWIN & _ & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & _ & _ & _ & _ & HPRES & HROD & HMN).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_frs HJ) as HFRS. pose proof (ajxR_pres HJ) as HPRESJ.
rewrite app_nil_l in HFRS.
pose proof (ajxR_ar HJ2) as HAR2.
pose proof HDATA3 as (_ & HPLo & HSLOTW & HCSTR & _).
pose proof HPLo as (_ & HatO & _ & HamrO & _).
pose proof HSLOTW as (Hw4096 & HwAt & HwRw & HwAmr & HwOwn & HwRa & _).
(* ---- the numbers ---- *)
assert (HSTKE : ESTACK + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity).
  assert (HE : STK_RT_ECALL = ESTACK) by reflexivity. lia. }
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSP0 : js_sp0 en = spZ (js_regs en)) by reflexivity.
assert (HSP1 : js_sp1 en = js_sp0 en - 48) by reflexivity.
assert (Hsp0c : YM05.alloc_ceiling <= spZ (js_regs en)) by lia.
assert (HSPLO : YM05.alloc_ceiling <= js_sp1 en - ESTACK) by lia.
assert (HTOPW : js_sp0 en + js_d en <= 2 ^ 47) by lia.
assert (Hn0 : 0 <= js_n en) by (pose proof HHDR3 as (_ & _ & _ & _ & _ & _ & (Hr & _) & _); lia).
pose proof HSLOTS as (_ & (Hnc & Hcapmax) & _ & Hslotpos).
assert (Hcappos : 0 < cap2v) by lia.
destruct (Hslotpos Hcappos) as (Hkids & Hkeys0). pose proof (Hkeys0 eq_refl) as Hkeys. clear Hkeys0.
(* ---- the object's block list: Do = kids :: keys :: Di ---- *)
pose proof HNODE3 as HN3. cbn [pj_nodeR] in HN3.
destruct HN3 as (_ & HapDo & num' & str' & kids' & keys' & n' & cap' & Hh' & Es' & En' & _ & _ & Di & EDo & _).
pose proof Hh' as (_ & _ & _ & Hsr1 & Hk1 & Hy1 & Hn1 & Hc1).
pose proof HHDR3 as (_ & _ & _ & Hsr3 & Hk3 & Hy3 & Hn3 & Hc3).
pose proof (pjsdt_u64_uniq _ _ _ _ _ Hsr1 Hsr3) as Es''. rewrite Es'' in Es'.
pose proof (pjsdt_u64_uniq _ _ _ _ _ Hk1 Hk3) as Ek'.
pose proof (pjsdt_u64_uniq _ _ _ _ _ Hy1 Hy3) as Ey'.
pose proof (pjsdt_u64_uniq _ _ _ _ _ Hn1 Hn3) as En''.
pose proof (pjsdt_u64_uniq _ _ _ _ _ Hc1 Hc3) as Ec'.
subst kids' keys' cap'. rewrite En'' in En'.
rewrite (proj2 (Z.eqb_neq cap2v 0)) in EDo by lia. cbn [app] in EDo.
revert HoDo. subst Do. intros HoDo.
(* ---- the ledger's block names are distinct ---- *)
pose proof HLED3 as (_ & HND3s & _).
assert (HND3 : List.NoDup (map fst Lam3)) by (apply NoDup_ListNoDup; exact HND3s).
assert (HND2 : List.NoDup (map fst Lam2) /\ ~ In dup (map fst Lam2)).
{ pose proof HND3 as HN. rewrite EL3 in HN. cbn [map fst] in HN. apply NoDup_cons_iff in HN as [Hn Hd].
  split; [exact Hd | exact Hn]. }
destruct HND2 as (HNDL2 & HdupL2).
assert (HinL2 : forall b, In b (((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di) ++ js_Dw en ++ Lr) -> In b Lam2)
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HpLam2) Hb)).
assert (HNDp : List.NoDup (map fst (((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di) ++ js_Dw en ++ Lr)))
  by exact (Permutation_NoDup (Permutation_map fst HpLam2) HNDL2).
pose proof HNDp as HNk. cbn [app map fst] in HNk.
apply NoDup_cons_iff in HNk as [HkN HNk]. apply NoDup_cons_iff in HNk as [HyN _].
assert (HkNe : kids2 <> keys2) by (intros E; apply HkN; left; symmetry; exact E).
assert (HnotK : forall a' k', In (a', k') (Di ++ js_Dw en ++ Lr) -> a' <> kids2 /\ a' <> keys2).
{ intros a' k' Hin. split; intros E; subst a'.
  - apply HkN. right. apply in_map_iff. exists (kids2, k'). split; [reflexivity | exact Hin].
  - apply HyN. apply in_map_iff. exists (keys2, k'). split; [reflexivity | exact Hin]. }
assert (HdupK : dup <> kids2 /\ dup <> keys2).
{ split; intros E; apply HdupL2; apply in_map_iff.
  - exists (kids2, 56 * cap2v). split; [cbn [fst]; symmetry; exact E|].
    apply HinL2. apply in_or_app. left. left. reflexivity.
  - exists (keys2, 8 * cap2v). split; [cbn [fst]; symmetry; exact E|].
    apply HinL2. apply in_or_app. left. right. left. reflexivity. }
assert (HUD : forall a0 k0 a1 k1 x, In (a0, k0) Lam3 -> In (a1, k1) Lam3 -> a0 <> a1 ->
  a0 <= x < a0 + k0 -> ~ (a1 <= x < a1 + k1)).
{ intros a0 k0 a1 k1 x H1 H2 H3 H4.
  exact (pjsd_lam_disj B ARx LAWS ly S Hp W mem md Lam3 _ _ _ _ _ _ a0 k0 a1 k1 HARc HLED3 H1 H2 H3 x H4). }
assert (HinDo : forall a' k', In (a', k') ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di) -> In (a', k') Lam3)
  by (intros a' k' Hb; exact (pjst_node_lblk SEGS _ _ _ _ _ HNODE3 a' k' Hb)).
assert (HinDw : forall a' k', In (a', k') (js_Dw en) -> In (a', k') Lam3)
  by (intros a' k' Hb; exact (pjst_node_lblk SEGS _ _ _ _ _ HNODEW3 a' k' Hb)).
pose proof (pj_set_ret_lem.pjr_node_nodup SEGS _ _ _ _ _ HNODEW3) as (_ & HapDw).
(* ---- the kids, keys and key-string blocks ---- *)
destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ kids2 (56 * cap2v) HARc HLED3 Hkids)
  as (_ & HkAB & Hkal & Hk4096 & Hkceil & HkRq & HkApp & HkPo).
destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ keys2 (8 * cap2v) HARc HLED3 Hkeys)
  as (_ & HyAB & Hyal & Hy4096 & Hyceil & HyRq & HyApp & HyPo).
assert (HdL3 : In (dup, js_klen en + 1) Lam3) by (rewrite EL3; left; reflexivity).
destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ dup (js_klen en + 1) HARc HLED3 HdL3)
  as (Hdk0 & HdAB & _ & Hd4096 & Hdceil & HdRq & _ & HdPo).
(* ---- the object's 56 bytes: below the ceiling, or in the caller's window ---- *)
assert (HoW : (4096 <= js_o en /\ js_o en + 56 <= YM05.alloc_ceiling) \/
  (js_sp0 en <= js_o en /\ js_o en + 56 <= js_sp0 en + js_d en)).
{ destruct (pj_set_ret_lem.pjr_at_where B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ (js_regs en) (js_d en) (js_o en) HARc HLED3 HatO)
    as [(H1 & H2 & _) | (H1 & H2)]; [left | right]; lia. }
assert (HOimg : forall x, js_o en <= x < js_o en + 56 -> apresent (w_H W) mem x /\ ~ in_img SEGS x).
{ intros x Hx.
  destruct (pj_set_ret_lem.pjr_at_where B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ (js_regs en) (js_d en) (js_o en) HARc HLED3 HatO)
    as [(_ & _ & Hwh) | (H1 & H2)].
  - destruct (Hwh x Hx) as (Hp' & Hi & _). split; [exact Hp' | exact Hi].
  - split; [apply HPRESJ; lia | intros Hi; pose proof (Hsegs x Hi); lia]. }
(* ---- what the two stores keep ---- *)
assert (HFRM : forall x, js_sp1 en <= x < js_sp0 en -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx. apply HVA; [lia | intros Hk; lia | intros Hn; destruct HoW as [HoW1 | HoW1]; lia]. }
assert (HSHK : forall x, 0 <= x < 2 ^ 47 ->
  aview SEGS (w_H W) mem2 (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HyApp.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HamrO.
  apply HVA; unfold shadow_of_addr, SHADOW_OFF; lia. }
assert (HwPres2 : forall x, js_w en <= x < js_w en + 56 -> apresent (w_H W) mem2 x)
  by (intros x Hx; apply HPR; exact (proj1 (HWPRES x Hx))).
(* ---- the ledger at mem2: the statics and every head word are off both stores ---- *)
assert (HLED2 : prh_ledger (PA := PA) B ly S Hp W mem2 Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (js_most en) (js_own en)).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem2 Lam3 peak3 _ fail3 ran3 _ _ HLED3).
  - intros a Ha. pose proof (pst_in_img_B a Ha) as Himg. pose proof (Hsegs a Himg) as Hlo.
    apply HVA; [lia | |].
    + intros Hk. exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HARc HyAB ltac:(rewrite HyRq; lia) Himg).
    + intros Hn. exact (proj2 (HOimg a ltac:(lia)) Himg).
  - intros a' k' i Hin Hi.
    destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ a' k' HARc HLED3 Hin) as (Hk0' & _ & _ & H4' & Hc' & _).
    assert (Hyh : a' - cf_head <= a' - cf_head + i < a') by lia.
    apply HVA; [lia | |].
    + intros Hk. apply (pjdt_head_user ly S Hp W mem md Lam3 _ _ _ _ _ _ a' k' keys2 (8 * cap2v) (a' - cf_head + i)
        HARc HLED3 Hin Hkeys Hyh). lia.
    + intros Hn. assert (Hyo : js_o en <= a' - cf_head + i < js_o en + 56) by lia.
      exact (pj_set_ret_lem.pjr_place_head B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ (js_regs en) (js_d en) (js_o en) a' k'
        HARc HLED3 HatO Hsp0c Hin (a' - cf_head + i) Hyo Hyh).
  - intros a' k' _ Hab. exact Hab.
  - apply Permutation_refl. }
(* ---- val's slot, val's tree and the destination's slot at mem2 ---- *)
assert (HwSlot2 : prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam3 W (js_regs en) mem2 (js_w en)).
{ split; [exact Hw4096|]. split; [exact HwAt|].
  split; [split; [exact (proj1 HwRw) | intros y Hy; exact (apresent_writable SEGS _ _ y (HwPres2 y Hy))]|].
  split; [exact HwAmr|]. split; [exact HwOwn|].
  split.
  - eapply range_addressable_agree; [|exact HwRa]. intros x Hx. apply HSHK. lia.
  - apply (pjs_hull_low B ARx LAWS VIS ly S Hp W mem2 md2 Lam3 _ _ _ _ _ _ (js_regs en) (js_d en) (js_w en)
      HAR2 HLED2 HwAt). lia. }
assert (HdAt : prhReader_at B ly S Lam3 (js_regs en) (js_d en) (kids2 + 56 * js_n en) 56)
  by (left; exists kids2, (56 * cap2v); split; [exact Hkids | lia]).
assert (HdSlot2 : prhPj_slot (PA := PA) B (STK_pj_set dd) (js_d en) ly S Lam3 W (js_regs en) mem2
  (kids2 + 56 * js_n en)).
{ split; [lia|]. split; [exact HdAt|].
  split; [split; [lia | intros y Hy; apply (apresent_writable SEGS); apply HPR; exact (proj1 (HkPo y ltac:(lia)))]|].
  split; [apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HkApp; lia | lia]|].
  split; [intros y Hy; split; [exact (proj2 (HkPo y ltac:(lia))) | lia]|].
  assert (Hv1 : kids2 <= kids2 + 56 * js_n en) by lia.
  assert (Hv2 : kids2 + 56 * js_n en + 56 <= kids2 + 56 * cap2v) by lia.
  assert (Hv3 : 0 < 56) by lia.
  destruct (pjs_vis_lam B ARx LAWS ly S Hp W mem2 md2 Lam3 _ _ _ _ _ _ kids2 (56 * cap2v) (kids2 + 56 * js_n en) 56
    HAR2 HLED2 Hkids Hv1 Hv2 Hv3) as [Hra' Hhull].
  split; [exact Hra' | exact Hhull]. }
assert (HNODEW2 : pj_nodeR SEGS (mrestrict (w_H W) mem2) (prh_lin Lam3) (js_w en) (js_tv en) (js_Dw en)).
{ apply (pjst_node_frame SEGS (js_tv en) (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) (prh_lin Lam3)
    (prh_lin Lam3) (js_w en) (js_Dw en) HNODEW3); [|exact (pjst_node_lblk SEGS _ _ _ _ _ HNODEW3)].
  apply pjs_agree.
  - intros x [Hx | ((a', k') & Hb & Hh)].
    + apply HVA; [lia | |].
      * intros Hk. apply (HWAP x Hx). right. exists (keys2, 8 * cap2v).
        split; [right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
      * intros Hn. apply (HWAP x Hx). left. lia.
    + unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
      destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ a' k' HARc HLED3 (HinDw a' k' Hb))
        as (_ & _ & _ & H4' & Hc' & _).
      destruct (HnotK a' k' ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & Hn2).
      apply HVA; [lia | |].
      * intros Hk. apply (HUD a' k' keys2 (8 * cap2v) x (HinDw a' k' Hb) Hkeys Hn2 Hh). lia.
      * intros Hn. apply (HAPW (a', k') x Hb); [unfold pj_holdsR; cbn [fst snd]; exact Hh | lia].
  - intros x [Hx | ((a', k') & Hb & Hh)] _.
    + apply (apresent_writable SEGS). apply HPR. exact (proj1 (HWPRES x Hx)).
    + unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
      destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ a' k' HARc HLED3 (HinDw a' k' Hb))
        as (_ & _ & _ & _ & _ & _ & _ & Hpo').
      apply (apresent_writable SEGS). apply HPR. exact (proj1 (Hpo' x ltac:(lia))). }
(* ---- the trace's length, and the allocator facts tpsP_A2 names ---- *)
destruct pjs_glue_holds as (_ & _ & _ & Hmm & Htl & _).
assert (Hclen : Datatypes.S c = length (prhPj_set_trace (js_n en) (js_cap en) (js_kname en))).
{ rewrite (Htl (js_n en) (js_cap en) (js_kname en)). destruct HCASE as [(Hlt & Ec0 & _) | (Heq & Ec2 & _)].
  - rewrite Ec0. replace (js_n en =? js_cap en) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - rewrite Ec2, Heq, Z.eqb_refl. reflexivity. }
assert (PL3 : Permutation Lam3
  (((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) :: js_Dw en) ++ Lr)).
{ rewrite EL3. apply (Permutation_trans (perm_skip _ HpLam2)).
  cbn [app]. rewrite <- app_assoc. cbn [app].
  apply (Permutation_trans (perm_swap _ _ _)). apply perm_skip.
  apply (Permutation_trans (perm_swap _ _ _)). apply perm_skip.
  apply Permutation_middle. }
assert (HFch : Forall (fun ch => 0 < ch < 256) (js_kname en)).
{ destruct HCSTR as ((Hg & Hnz) & _). apply Forall_forall. intros ch Hch. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hnz ch Hch) as Hne. cbv beta in Hne.
  destruct (In_nth _ _ 0 Hch) as (j & Hj & Ej).
  assert (Hj' : (j < length (js_kname en ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  destruct (Hg j Hj') as (_ & Hr).
  rewrite app_nth1 in Hr by lia. rewrite Ej in Hr. lia. }
assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}).
{ intros [u1 u2] [v1 v2]. destruct (Z.eq_dec u1 v1) as [E1 | N1]; [destruct (Z.eq_dec u2 v2) as [E2 | N2]|].
  - left. subst. reflexivity.
  - right. intros E. injection E as _ E2. exact (N2 E2).
  - right. intros E. injection E as E1 _. exact (N1 E1). }
(* ======== the cut ======== *)
split.
{ (* pjs_invR at mem2 *)
  split; [exact HJ2|].
  split.
  { intros a Ha Hnf. transitivity (aview SEGS (w_H W) mem a); [|exact (HWIN a Ha Hnf)].
    apply HVA; [lia | intros Hk; lia |].
    intros Hn. apply Hnf. unfold pjs_FP. apply inFP_cons. left. lia. }
  split; [exact Hsp2|].
  split; [apply (pjdt_val_kept W W mem mem2 _ 8 _ Hra); intros x Hx; apply HFRM;
          try change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjdt_val_kept W W mem mem2 _ 8 _ Hs0); intros x Hx; apply HFRM;
          try change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjdt_val_kept W W mem mem2 _ 8 _ Hs1); intros x Hx; apply HFRM;
          try change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjdt_val_kept W W mem mem2 _ 8 _ Hs2); intros x Hx; apply HFRM;
          try change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjdt_val_kept W W mem mem2 _ 8 _ Hs3); intros x Hx; apply HFRM;
          try change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjdt_val_kept W W mem mem2 _ 8 _ Hs4); intros x Hx; apply HFRM;
          try change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [exact E8|]. split; [exact E18|]. split; [exact E20|]. split; [exact EKEPT|].
  split; [intros a Ha; apply HPR; exact (HPRES a Ha)|].
  split.
  { intros a Hro Hown Herr. transitivity (aview SEGS (w_H W) mem a); [|exact (HROD a Hro Hown Herr)].
    pose proof (pjs_ro_img a Hro) as Himg. pose proof (Hsegs a Himg) as Hlo.
    apply HVA; [lia | |].
    - intros Hk. exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HARc HyAB ltac:(rewrite HyRq; lia) Himg).
    - intros Hn. exact (proj2 (HOimg a ltac:(lia)) Himg). }
  (* the memnorm keep: the cut's, then the two stores' *)
  intros HMN0. exact (KMN (HMN HMN0)). }
split; [exact HROOM|].
exists (kids2 + 56 * js_n en), Lam3, peak3, (js_cnt en + Z.of_nat (Datatypes.S c)), fail3, ran3, (Datatypes.S c), ok3.
split; [exact E10|]. split; [exact E12|]. split; [exact HLED2|]. split; [reflexivity|].
split; [exact HOKS3|]. split; [exact HFA3|].
split; [exact HNODEW2|]. split; [exact HwSlot2|]. split; [exact HdSlot2|].
split; [intros x Hw' Hd; apply (HWAP x Hw'); right; exists (kids2, 56 * cap2v);
        split; [left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia]|].
split; [lia|]. split; [exact HWCEIL|].
split.
{ (* the two writes are permitted: the slot in the kids block (old or new), val in its block or fake frame *)
  intros a [Ha | Ha].
  - destruct HCASE as [(Hlt & _ & Ek & _ & Ecap & _ & _) | (Heq & _ & Ecap & _ & EDnew)].
    + assert (HkD0 : In (js_kids en, 56 * js_cap en) (js_D en)).
      { pose proof HNODE0 as HN0. cbn [pj_nodeR] in HN0.
        destruct HN0 as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & HH0 & _ & _ & _ & _ & Di0 & ED & _).
        pose proof HH0 as (_ & _ & _ & _ & Hk0' & _ & _ & Hc0').
        pose proof HHDR0 as (_ & _ & _ & _ & Hk0'' & _ & _ & Hc0'').
        pose proof (pjsdt_u64_uniq _ _ _ _ _ Hk0' Hk0'') as E1.
        pose proof (pjsdt_u64_uniq _ _ _ _ _ Hc0' Hc0'') as E2.
        subst kids0 cap0. rewrite ED. rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia.
        apply in_or_app. left. left. reflexivity. }
      left. right. left. split.
      * unfold pjs_FP. apply inFP_cons. right. apply inFP_cons. right.
        apply (pj_set_ret_lem.pjr_hbl_inFP (js_D en ++ js_Dw en) kids2 (56 * cap2v) a); [apply in_or_app; left | rewrite HkRq; lia].
        rewrite Ek, Ecap. exact HkD0.
      * exists (kids2 - cf_head), (56 * cap2v + cf_head). split; [exact HkAB | rewrite HkRq; lia].
    + left. right. right. left. exists (kids2 - cf_head), (56 * cap2v + cf_head).
      split; [exact HkAB|]. split; [|rewrite HkRq; lia].
      exact (HNEW kids2 (56 * cap2v) ltac:(rewrite EDnew, Ecap; left; reflexivity)).
  - destruct (pj_set_ret_lem.pjr_at_where B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ (js_regs en) (js_d en) (js_w en) HARc HLED3 HwAt)
      as [(_ & _ & HwWh) | (Hc1' & _)]; [|lia].
    destruct (HwWh a Ha) as (_ & _ & [(bb & nn & Hbn & Hr) | (cid & pos & Hcp' & Hr)]).
    + left. right. left.
      split; [exists (js_w en, js_w en + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
      exists bb, nn. split; [exact Hbn | exact Hr].
    + right.
      split; [exists (js_w en, js_w en + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
      exists cid, pos. split; [rewrite HFRS in Hcp'; exact Hcp' | exact Hr]. }
split; [intros a Ha; exact (aview_some_of_apresent SEGS _ _ a (HwPres2 a Ha))|].
split; [intros a [Ha | Ha];
        [exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HARc HkAB ltac:(rewrite HkRq; lia))
        | exact (proj2 (HWPRES a Ha))]|].
(* ======== the obligation: tpsP_Q (tpj_set_specX's post), second arm ======== *)
intros mem' regs' md' Hcpy Hzero Hkeep Hpres' Ha0'.
assert (HoK2 : forall x, js_o en <= x < js_o en + 56 -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem2 x).
{ intros x Hx. apply Hkeep.
  - destruct HoW as [HoW1 | HoW1]; lia.
  - intros Hd. apply (HapDo (kids2, 56 * cap2v) x); [left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia | exact Hx].
  - intros Hw'. apply (HWAP x Hw'). left. exact Hx.
  - destruct HoW as [HoW1 | HoW1]; lia. }
assert (HoK : forall x, js_o en <= x < js_o en + 56 -> ~ (js_o en + 40 <= x < js_o en + 48) ->
  aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x).
{ intros x Hx Hn. rewrite (HoK2 x Hx). apply HVA; [destruct HoW as [HoW1 | HoW1]; lia | | exact Hn].
  intros Hk. apply (HapDo (keys2, 8 * cap2v) x); [right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia | exact Hx]. }
assert (HKRm : forall x, keys2 + 8 * js_n en <= x < keys2 + 8 * js_n en + 8 ->
  aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem2 x).
{ intros x Hx. apply Hkeep; [lia | | | lia].
  - intros Hd. assert (Hxk : keys2 <= x < keys2 + 8 * cap2v) by lia.
    apply (HUD keys2 (8 * cap2v) kids2 (56 * cap2v) x Hkeys Hkids
      ltac:(intros E; apply HkNe; symmetry; exact E) Hxk). lia.
  - intros Hw'. apply (HWAP x Hw'). right. exists (keys2, 8 * cap2v).
    split; [right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia]. }
assert (HAGS : forall x, (kids2 <= x < kids2 + 56 * js_n en) \/ (keys2 <= x < keys2 + 8 * js_n en) \/
    (exists b, In b Di /\ pj_holdsR b x) \/ (exists b, In b (js_Dw en) /\ pj_holdsR b x) \/
    (dup <= x < dup + (js_klen en + 1)) ->
  aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x /\ apresent (w_H W) mem' x).
{ intros x Hx.
  assert (Hgen : forall a' k', In (a', k') Lam3 -> a' <= x < a' + k' ->
    (a' <> keys2 \/ x < keys2 + 8 * js_n en) -> (a' <> kids2 \/ x < kids2 + 56 * js_n en) ->
    ~ (js_o en <= x < js_o en + 56) -> ~ (js_w en <= x < js_w en + 56) ->
    aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x /\ apresent (w_H W) mem' x).
  { intros a' k' Hin Hr Hky Hki Hno Hnw.
    destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ a' k' HARc HLED3 Hin)
      as (Hk0' & _ & _ & H4' & Hc' & _ & _ & Hpo').
    assert (Hnd : ~ (kids2 + 56 * js_n en <= x < kids2 + 56 * js_n en + 56)).
    { destruct Hki as [Hne | Hlt]; [|lia]. intros Hd.
      apply (HUD a' k' kids2 (56 * cap2v) x Hin Hkids Hne Hr). lia. }
    assert (Hnk : ~ (keys2 + 8 * js_n en <= x < keys2 + 8 * js_n en + 8)).
    { destruct Hky as [Hne | Hlt]; [|lia]. intros Hd.
      apply (HUD a' k' keys2 (8 * cap2v) x Hin Hkeys Hne Hr). lia. }
    split.
    - assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
      assert (Hxs : ~ (js_sp1 en - ESTACK <= x < js_sp1 en)) by lia.
      rewrite (Hkeep x Hx64 Hnd Hnw Hxs). apply HVA; [lia | exact Hnk |].
      intros Hn. apply Hno. lia.
    - apply Hpres'. apply HPR. exact (proj1 (Hpo' x ltac:(lia))). }
  destruct Hx as [Hx | [Hx | [(b & Hb & Hh) | [(b & Hb & Hh) | Hx]]]].
  - apply (Hgen kids2 (56 * cap2v) Hkids); [lia | left; exact HkNe | right; lia | |].
    + intros Ho. apply (HapDo (kids2, 56 * cap2v) x); [left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia | exact Ho].
    + intros Hw'. apply (HWAP x Hw'). right. exists (kids2, 56 * cap2v).
      split; [left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  - apply (Hgen keys2 (8 * cap2v) Hkeys); [lia | right; lia | left; intros E; apply HkNe; symmetry; exact E | |].
    + intros Ho. apply (HapDo (keys2, 8 * cap2v) x); [right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia | exact Ho].
    + intros Hw'. apply (HWAP x Hw'). right. exists (keys2, 8 * cap2v).
      split; [right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  - destruct b as [a' k']. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
    assert (HbDo : In (a', k') ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di)) by (right; right; exact Hb).
    destruct (HnotK a' k' ltac:(apply in_or_app; left; exact Hb)) as (Hq1 & Hq2).
    apply (Hgen a' k' (HinDo a' k' HbDo) Hh (or_introl Hq2) (or_introl Hq1)).
    + intros Ho. apply (HapDo (a', k') x HbDo); [unfold pj_holdsR; cbn [fst snd]; exact Hh | exact Ho].
    + intros Hw'. apply (HWAP x Hw'). right. exists (a', k'). split; [exact HbDo | unfold pj_holdsR; cbn [fst snd]; exact Hh].
  - destruct b as [a' k']. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
    destruct (HnotK a' k' ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (Hq1 & Hq2).
    apply (Hgen a' k' (HinDw a' k' Hb) Hh (or_introl Hq2) (or_introl Hq1)).
    + intros Ho. apply (HAPW (a', k') x Hb); [unfold pj_holdsR; cbn [fst snd]; exact Hh | exact Ho].
    + intros Hw'. apply (HapDw (a', k') x Hb); [unfold pj_holdsR; cbn [fst snd]; exact Hh | exact Hw'].
  - destruct HdupK as (Hq1 & Hq2).
    apply (Hgen dup (js_klen en + 1) HdL3 Hx (or_introl Hq2) (or_introl Hq1)).
    + intros Ho. exact (HdupO x Ho ltac:(lia)).
    + intros Hw'. exact (HdupW x Hw' ltac:(lia)). }
split; [exact HROOM|].
exists Lam3, peak3, fail3, ran3, 0, (Datatypes.S c), ok3, Lr,
  ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) :: js_Dw en).
split; [exact Ha0'|].
split.
{ (* the ledger at tpsP_Q's post state: the statics and every head word are off both writes *)
  apply (prh_ledger_kept_aview B ly S Hp W mem2 ly S Hp W mem' Lam3 peak3 _ fail3 ran3 _ _ HLED2).
  - intros a Ha. pose proof (pst_in_img_B a Ha) as Himg. pose proof (Hsegs a Himg) as Hlo.
    apply Hkeep; [lia | | | lia].
    + intros Hd. exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HARc HkAB ltac:(rewrite HkRq; lia) Himg).
    + intros Hw'. exact (proj2 (HWPRES a Hw') Himg).
  - intros a' k' i Hin Hi.
    destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ a' k' HARc HLED3 Hin) as (Hk0' & _ & _ & H4' & Hc' & _).
    apply Hkeep; [lia | | | lia].
    + intros Hd. apply (pj_set_ret_lem.pjr_place_head B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ (js_regs en) (js_d en)
        (kids2 + 56 * js_n en) a' k' HARc HLED3 HdAt Hsp0c Hin _ Hd). lia.
    + intros Hw'. apply (pj_set_ret_lem.pjr_place_head B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ (js_regs en) (js_d en)
        (js_w en) a' k' HARc HLED3 HwAt Hsp0c Hin _ Hw'). lia.
  - intros a' k' _ Hab. exact Hab.
  - apply Permutation_refl. }
split; [exact HOKS3|]. split; [exact HFA3|]. split; [exact HpLam|]. split; [exact PL3|].
split; [exact HBLK3|].
split.
{ (* val reads 0 *)
  intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  assert (Hj56 : 0 <= Z.of_nat j < 56) by lia.
  pose proof (Hzero (Z.of_nat j) Hj56) as Hzj. unfold aview in Hzj.
  destruct (mbyte SEGS (mrestrict (w_H W) mem') (js_w en + Z.of_nat j)) as [bb|] eqn:Eb;
    cbn [option_map] in Hzj; [|discriminate Hzj].
  injection Hzj as Hbb. f_equal. apply bv_eq. rewrite Hbb. vm_compute. reflexivity. }
(* tpsP_Q's res = 0 position: the cut's, past the call's events (fuzz_strdup's granted HMal) *)
split; [intros _; exact HPOSF|].
(* res = 0 here: the prh_granted clause and DEAD-PJSET hold outright *)
split; [intros _ _; reflexivity|].
split; [intros _; reflexivity|].
right. left.
split; [exact HNI|].
split.
{ rewrite <- Hclen. intros (Hf1 & Hf2). pose proof HOKS3 as (Hok1 & _ & _).
  assert (Hi : (Z.to_nat (js_fail en - js_cnt en) < Datatypes.S c)%nat) by lia.
  assert (Hci : js_cnt en + Z.of_nat (Z.to_nat (js_fail en - js_cnt en)) = js_fail en) by lia.
  pose proof (Hok1 _ Hi Hci) as Hf. rewrite (Hokall3 _ Hi) in Hf. discriminate Hf. }
split; [exact Hclen|].
split; [exact Hokall3|].
split; [reflexivity|].
split; [exact Hpeak3|].
split.
{ exists Dold, Dnew, Dr, dup.
  split; [exact HpD|].
  split.
  { change (Permutation (((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di) ++ (dup, js_klen en + 1) :: js_Dw en)
      (Dnew ++ (dup, js_klen en + 1) :: Dr ++ js_Dw en)).
    apply (Permutation_trans (Permutation_app HpDo (Permutation_refl _))).
    rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle. }
  split.
  { intros a' k' Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
    - right. exact (HNEW a' k' Hin).
    - injection Hin as Ea Ek. subst a' k'.
      destruct (in_dec Hdec (dup, js_klen en + 1) Dold) as [Hd | Hd]; [left; exact Hd | right].
      intros Hab. pose proof HBLK3 as (other & HB0 & HB1).
      apply (Permutation_in _ HB0) in Hab. apply in_app_or in Hab as [Hh | Ho].
      + pose proof (pj_set_ret_lem.pjr_hbl_in (js_Lam en) _ _ Hh) as HL0.
        replace (dup - cf_head + cf_head, js_klen en + 1 + cf_head - cf_head) with (dup, js_klen en + 1) in HL0
          by (f_equal; lia).
        apply (Permutation_in _ HpLam) in HL0.
        apply HdupL2. apply in_map_iff. exists (dup, js_klen en + 1). split; [reflexivity|]. apply HinL2.
        apply in_app_or in HL0 as [HD | HL0].
        * apply (Permutation_in _ HpD) in HD. apply in_app_or in HD as [HD | HD]; [contradiction|].
          apply in_or_app. left. apply (Permutation_in _ (Permutation_sym HpDo)). apply in_or_app. right. exact HD.
        * apply in_or_app. right. exact HL0.
      + assert (Hin3 : In (dup - cf_head, js_klen en + 1 + cf_head) (prhPj_hbl Lam3)).
        { unfold prhPj_hbl. apply in_map_iff. exists (dup, js_klen en + 1). split; [reflexivity | exact HdL3]. }
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc HdAB) as (_ & _ & _ & _ & _ & Hpw).
        apply (pjdt_perm_twice (ablocks B ly S) (prhPj_hbl Lam3) other _ Hpw HB1 Hin3 Ho).
        cbn [snd]. assert (Hq0 : 0 <= js_klen en + 1 + cf_head) by lia.
        pose proof (pjs_req (js_klen en + 1 + cf_head) Hq0) as (_ & Hr1 & _). exact Hr1. }
  destruct HCASE as [(Hlt & _ & _ & _ & _ & EDold & EDnew) | (Heq & _ & _ & EDold & EDnew)].
  - left. split; [exact Hlt|]. split; [exact EDold | exact EDnew].
  - right. split; [exact Heq|]. split; [exact EDold|]. exists kids2, keys2. exact EDnew. }
(* ---- the object with the member appended, at mem' (pjsd_obj_app's premises; FREEORD-COPY reuses them) ---- *)
assert (HHm : pj_hdrR SEGS (mrestrict (w_H W) mem') (js_o en) 6 num3 str3 kids2 keys2 (js_n en + 1) cap2v).
{ (* n + 1 at o + 40, every other field as at mem *)
  pose proof HHDR3 as ((Ho8' & _) & T3 & N3 & S3 & K3 & Y3 & _ & C3).
  assert (HoM : forall a0 w0, js_o en <= a0 -> a0 + w0 <= js_o en + 40 \/ js_o en + 48 <= a0 ->
    a0 + w0 <= js_o en + 56 ->
    forall x, a0 <= x < a0 + w0 -> mbyte SEGS (mrestrict (w_H W) mem') x = mbyte SEGS (mrestrict (w_H W) mem) x).
  { intros a0 w0 H1 H2 H3 x Hx. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem' x). apply HoK; lia. }
  split; [split; [exact Ho8' | intros x Hx; apply (apresent_writable SEGS); apply Hpres'; apply HPR;
                   exact (proj1 (HOimg x Hx))]|].
  split; [apply (rd_u32_frame SEGS _ _ _ _ T3); intros x Hx; apply (HoM (js_o en) 4); lia|].
  split; [apply (rd_u64_frame SEGS _ _ _ _ N3); intros x Hx; apply (HoM (js_o en + 8) 8); lia|].
  split; [apply (rd_u64_frame SEGS _ _ _ _ S3); intros x Hx; apply (HoM (js_o en + 16) 8); lia|].
  split; [apply (rd_u64_frame SEGS _ _ _ _ K3); intros x Hx; apply (HoM (js_o en + 24) 8); lia|].
  split; [apply (rd_u64_frame SEGS _ _ _ _ Y3); intros x Hx; apply (HoM (js_o en + 32) 8); lia|].
  split.
  + split; [lia|].
    apply (pj_valR_frame SEGS (mrestrict (w_H W) mem2) (mrestrict (w_H W) mem') _ 8 _ HVN).
    intros x Hx. try change (Z.of_nat 8) with 8 in Hx.
    apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem2 mem' x). apply HoK2. lia.
  + apply (rd_u64_frame SEGS _ _ _ _ C3). intros x Hx. apply (HoM (js_o en + 48) 8); lia. }
assert (HKm : rd_u64 SEGS (mrestrict (w_H W) mem') (keys2 + 8 * js_n en) dup).
{ (* keys[n] = dup at mem' *)
  split; [lia|]. apply (pj_valR_frame SEGS (mrestrict (w_H W) mem2) (mrestrict (w_H W) mem') _ 8 _ HVK).
  intros x Hx. try change (Z.of_nat 8) with 8 in Hx.
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem2 mem' x). exact (HKRm x Hx). }
assert (HCPm : forall i, 0 <= i < 56 ->
  mbyte SEGS (mrestrict (w_H W) mem') (kids2 + 56 * js_n en + i) = mbyte SEGS (mrestrict (w_H W) mem) (js_w en + i)).
{ (* the copy of val's header into the slot *)
  intros i Hi. apply (pj_set_ret_lem.pjr_mbyte_aview2 SEGS). rewrite (Hcpy i Hi).
  assert (Hwi : js_w en <= js_w en + i < js_w en + 56) by lia.
  apply HVA; [lia | |].
  + intros Hk. apply (HWAP (js_w en + i) Hwi). right. exists (keys2, 8 * cap2v).
    split; [right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  + intros Hn. apply (HWAP (js_w en + i) Hwi). left. lia. }
assert (HRWm : pj_rwR SEGS (mrestrict (w_H W) mem') (kids2 + 56 * js_n en)).
{ split; [lia | intros y Hy; apply (apresent_writable SEGS); apply Hpres'; apply HPR; exact (proj1 (HkPo y ltac:(lia)))]. }
assert (HAGm : pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')
  (fun x => (kids2 <= x < kids2 + 56 * js_n en) \/ (keys2 <= x < keys2 + 8 * js_n en) \/
            (exists b, In b Di /\ pj_holdsR b x) \/ (exists b, In b (js_Dw en) /\ pj_holdsR b x) \/
            (dup <= x < dup + (js_klen en + 1)))).
{ apply pjs_agree.
  + intros x Hx. exact (proj1 (HAGS x Hx)).
  + intros x Hx _. exact (apresent_writable SEGS _ _ x (proj2 (HAGS x Hx))). }
assert (HAPdw : pj_apartR (js_Dw en) (kids2 + 56 * js_n en)).
{ intros b x Hb Hh Hd. destruct b as [a' k']. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
  destruct (HnotK a' k' ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (Hq1 & _).
  apply (HUD a' k' kids2 (56 * cap2v) x (HinDw a' k' Hb) Hkids Hq1 Hh). lia. }
(* the new block list is duplicate-free: a part of Lam3 *)
assert (HNDl : List.NoDup ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) :: js_Dw en)).
{ assert (HNDL3 : List.NoDup Lam3) by exact (List.NoDup_map_inv _ _ HND3).
  exact (pjdt_nodup_app_l _ _ (Permutation_NoDup PL3 HNDL3)). }
assert (HAPm : pj_apartR ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) :: js_Dw en)
  (js_o en)).
{ (* the new block list holds no byte of the object's header *)
  intros b x Hb Hh Ho.
  assert (Hb' : In b ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di) \/ b = (dup, js_klen en + 1) \/
    In b (js_Dw en)).
  { destruct Hb as [Hb | [Hb | Hb]]; [left; left; exact Hb | left; right; left; exact Hb |].
    apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [left; right; right; exact Hb | right; left; symmetry; exact Hb | right; right; exact Hb]. }
  destruct Hb' as [Hb' | [Hb' | Hb']].
  + exact (HapDo b x Hb' Hh Ho).
  + subst b. unfold pj_holdsR in Hh. cbn [fst snd] in Hh. exact (HdupO x Ho ltac:(lia)).
  + exact (HAPW b x Hb' Hh Ho). }
assert (HLm : forall a' k', In (a', k') ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) ::
  js_Dw en) -> prh_lin Lam3 a' k').
{ (* every block of the new list is a block of Lam3 *)
  intros a' k' Hin. unfold prh_lin.
  destruct Hin as [Hin | [Hin | Hin]].
  + rewrite <- Hin. exact Hkids.
  + rewrite <- Hin. exact Hkeys.
  + apply in_app_or in Hin as [Hin | [Hin | Hin]].
    * exact (HinDo a' k' ltac:(right; right; exact Hin)).
    * rewrite <- Hin. exact HdL3.
    * exact (HinDw a' k' Hin). }
assert (HNODEm : pj_nodeR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3) (js_o en)
  (PjTree.JObj (js_ms en ++ [(js_kname en, js_tv en)]))
  ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) :: js_Dw en)).
{ apply (pjsd_obj_app (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (prh_lin Lam3) (prh_lin Lam3)
    (js_o en) num3 str3 kids2 keys2 (js_n en) cap2v (js_ms en) Di dup (js_klen en + 1) (js_kname en) (js_tv en)
    (js_Dw en) (js_w en) HNODE3 HHDR3 En' Hn0 Hncap2 Hcapmax HNODEW3); [| exact HHm | exact HKm | exact HCPm |
    exact HRWm | exact HAGm | exact HAPdw | | exact HAPm | exact HLm].
  - (* the key string, the block strdup returned *)
    split; [unfold prh_lin; exact HdL3|]. split; [unfold js_klen; lia|].
    (* the reader's strings are shorter than 2 ^ 32 - 1: the key's strdup request is below cf_malloc_max *)
    split; [unfold js_klen in HKLEN; pose proof (YG08cf.cf_malloc_max_bound (cp := cp)); lia|].
    split; [exact HFch | exact HBYT].
  - first [apply NoDup_ListNoDup; exact HNDl | exact HNDl]. }
(* the object gains the member (kname, tv) *)
rewrite (Hmm (js_ms en) (js_kname en) (js_tv en) HNI).
split; [exact HNODEm|].
split.
{ (* the block conjunct: the final list against tblk of the new object, up to order *)
  intros Ehd HDw Hech. rewrite Ehd in HDw, HTBLK0 |- *. unfold js_klen.
  apply (pjdt_tblk_app (js_ms en) (js_kname en) (js_tv en) (js_D en) Dold Dr Dnew (js_Dw en) Di
    (js_kids en) (js_keys en) kids2 keys2 (js_n en) (js_cap en) cap2v dup HTBLK0 HDw Hech En' Hcapm Hcap2m HoD HoDo).
  destruct HCASE as [(Hlt & _ & _ & _ & Ec & EDold & EDnew) | (Heq & _ & Ec & EDold & EDnew)].
  - left. split; [exact Hlt|]. split; [exact Ec|]. split; [exact EDold | exact EDnew].
  - right. split; [exact Heq|]. split; [exact Ec|]. split; [exact EDold | exact EDnew]. }
(* FREEORD-COPY: the result's ordered free list *)
intros Ehd HFw Hech nn Hnn. rewrite Ehd in HFw |- *.
destruct nn as [|nn']; [cbn [PjTree.depth] in Hnn; lia|].
assert (Hdo0 : (PjTree.depth (PjTree.JObj (js_ms en)) <= Datatypes.S nn')%nat)
  by (pose proof (pjsf_depth_app (js_ms en) (js_kname en, js_tv en)); lia).
assert (Hdv : (PjTree.depth (js_tv en) <= nn')%nat).
{ apply (proj1 (pjsf_depth_obj (js_ms en ++ [(js_kname en, js_tv en)]) nn') Hnn (js_kname en)).
  apply in_or_app. right. left. reflexivity. }
(* Lam3's block predicate is functional and names no block at address 0 *)
assert (HFN : forall a k k', prh_lin Lam3 a k -> prh_lin Lam3 a k' -> k = k')
  by (intros a k1 k2 H1 H2; exact (prh_fst_unique Lam3 a k1 k2 HND3s H1 H2)).
assert (HNZ : forall a k, prh_lin Lam3 a k -> a <> 0).
{ intros a k1 Hin.
  destruct (pj_set_ret_lem.pjr_hb B ARx LAWS HWIDE ly S Hp W mem md Lam3 _ _ _ _ _ _ a k1 HARc HLED3 Hin)
    as (_ & _ & _ & H4 & _). lia. }
(* the object's ordered list at mem: its slot list, then its arrays *)
destruct (HFO3 (Datatypes.S nn') Hdo0) as (F0 & HF0 & HmF0).
destruct (pjsf_obj_dest SEGS (mrestrict (w_H W) mem) (prh_lin Lam3) nn' (js_o en) (js_ms en) _ F0 HFN HNZ HNODE3 HF0)
  as (numx & kidsx & keysx & capx & Dm & Di' & Fi & _ & Hmx & HOx & HPmx & Hcx).
destruct Hcx as [(_ & _ & ED0 & _) | (_ & _ & _ & _ & EDx & EFx)]; [discriminate ED0|].
assert (Hx3 : kidsx = kids2 /\ capx = cap2v /\ keysx = keys2 /\ Dm = Di)
  by (injection EDx; intros; repeat split; first [congruence | lia]).
destruct Hx3 as (-> & -> & -> & ->).
rewrite EFx in HmF0.
destruct (pjsf_slots_map SEGS (mrestrict (w_H W) mem) (prh_lin Lam3) nn' PresetReqAtNoMiss.kblk (js_ms en) kids2 keys2
  Di Di' Fi [(kids2, 56 * cap2v); (keys2, 8 * cap2v)]
  (PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (js_ms en))))) HFN HNZ Hmx HOx HmF0
  ltac:(destruct (PresetReqAt.ncap (Datatypes.S (length (js_ms en)))); cbn; lia)) as (HmFi & _).
(* the slot list at mem' *)
assert (HOx' : pf_oitemsR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3)
  (pj_foR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3) nn') true kids2 keys2 (length (js_ms en)) Di' Fi).
{ apply (pf_oitemsR_frame SEGS nn' _ _ (prh_lin Lam3) (prh_lin Lam3) true kids2 keys2 (length (js_ms en)) Di' Fi HOx).
  - exact (pf_oitemsR_lblk SEGS _ _ nn' true kids2 keys2 _ Di' Fi HOx).
  - apply (pf_agree_mono SEGS _ _ _ _ HAGm). unfold pf_ofoot. rewrite <- En'.
    intros x [Hx | [(_ & Hx) | (b & Hb & Hx)]]; [left; exact Hx | right; left; exact Hx |].
    right. right. left. exists b. split; [|exact Hx]. exact (Permutation_in _ (Permutation_sym HPmx) Hb). }
(* val's ordered list (the premise, at the entry memory), at mem by val's entry agreement, then moved into the slot *)
destruct (HFw nn' Hdv) as (Fw & HFw0 & HmFw).
assert (HFwm : pj_foR SEGS (mrestrict (w_H W) mem) (prh_lin Lam3) nn' (js_w en) (js_Dw en) Fw)
  by exact (pj_foR_frame SEGS nn' _ _ (prh_lin (js_Lam en)) (prh_lin Lam3) (js_w en) (js_Dw en) Fw HFw0 HinDw HAGRW3).
assert (HFwm' : pj_foR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3) nn' (kids2 + 56 * js_n en) (js_Dw en) Fw).
{ apply (pjsf_foR_move SEGS nn' _ _ (prh_lin Lam3) (prh_lin Lam3) (js_w en) (kids2 + 56 * js_n en) (js_Dw en) Fw
    HFwm HCPm HRWm HAPdw); [|exact HinDw].
  apply (pf_agree_mono SEGS _ _ _ _ HAGm). intros x Hx. right. right. right. left. exact Hx. }
(* slot n: val's list, then the key block *)
assert (HOn : pf_oitemsR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3)
  (pj_foR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3) nn') true
  (kids2 + 56 * Z.of_nat (length (js_ms en))) (keys2 + 8 * Z.of_nat (length (js_ms en))) 1
  ((dup, js_klen en + 1) :: js_Dw en) (Fw ++ [(dup, js_klen en + 1)])).
{ apply (proj2 (pjsf_oitems_one SEGS _ _ _ true _ _ _ _)).
  exists [(dup, js_klen en + 1)], (js_Dw en), Fw. split; [reflexivity|]. split; [reflexivity|]. split.
  - cbn [pj_keyR]. exists dup. split; [rewrite <- En'; exact HKm|].
    right. exists (js_klen en + 1). split; [exact HdL3 | reflexivity].
  - rewrite <- En'. exact HFwm'. }
assert (HOall : pf_oitemsR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3)
  (pj_foR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3) nn') true kids2 keys2 (length (js_ms en) + 1)
  (Di' ++ (dup, js_klen en + 1) :: js_Dw en) (Fi ++ (Fw ++ [(dup, js_klen en + 1)]))).
{ apply (proj2 (pjsf_oitems_app SEGS _ _ _ true (length (js_ms en)) 1 kids2 keys2 _ _)).
  exists Di', Fi, ((dup, js_klen en + 1) :: js_Dw en), (Fw ++ [(dup, js_klen en + 1)]).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HOx' | exact HOn]. }
(* the object reassembled, its block list put in pj_nodeR's order *)
assert (HPx : Permutation ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di' ++ (dup, js_klen en + 1) :: js_Dw en)
  ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di ++ (dup, js_klen en + 1) :: js_Dw en)).
{ apply perm_skip. apply perm_skip. apply Permutation_app_tail. exact (Permutation_sym HPmx). }
assert (HHm0 := HHm). rewrite Es' in HHm0.
assert (HFx : pj_foR SEGS (mrestrict (w_H W) mem') (prh_lin Lam3) (Datatypes.S nn') (js_o en)
  ((kids2, 56 * cap2v) :: (keys2, 8 * cap2v) :: Di' ++ (dup, js_klen en + 1) :: js_Dw en)
  ((Fi ++ (Fw ++ [(dup, js_klen en + 1)])) ++ [(kids2, 56 * cap2v); (keys2, 8 * cap2v)])).
{ apply (pjsf_obj_intro SEGS _ _ nn' (js_o en) num3 kids2 keys2 (js_n en + 1) cap2v);
    [exact HHm0 | lia | lia | exact Hkids | exact Hkeys | | |].
  - first [apply NoDup_ListNoDup; exact (Permutation_NoDup (Permutation_sym HPx) HNDl)
          | exact (Permutation_NoDup (Permutation_sym HPx) HNDl)].
  - intros b x Hb. apply (HAPm b x). exact (Permutation_in _ HPx Hb).
  - replace (Z.to_nat (js_n en + 1)) with (length (js_ms en) + 1)%nat by lia. exact HOall. }
exists ((Fi ++ (Fw ++ [(dup, js_klen en + 1)])) ++ [(kids2, 56 * cap2v); (keys2, 8 * cap2v)]).
split.
{ apply (PjFoMember.pfm_foR_perm SEGS _ _ _ _ _ _ _ HFx HPx); [|exact HAPm].
  first [apply NoDup_ListNoDup; exact HNDl | exact HNDl]. }
(* its requests: the members' slots, the new slot (val's fo, the key block), the arrays at ncap (S |ms|) *)
assert (Hsl1 : PjFoMember.pfm_slots PresetReqAtNoMiss.kblk [(js_kname en, js_tv en)] =
  PresetReqAt.fo (js_tv en) ++ [PresetReqAtNoMiss.kblk (js_kname en)])
  by (unfold PjFoMember.pfm_slots; cbn [map concat fst snd]; rewrite app_nil_r; reflexivity).
assert (Hkb : PresetReqAtNoMiss.kblk (js_kname en) = js_klen en + 1 + PresetReqAt.HEAD)
  by (unfold PresetReqAtNoMiss.kblk, js_klen; rewrite Hech; lia).
rewrite pjsf_fo_obj, pjsf_slots_app, Hsl1, length_app. cbn [length]. rewrite Nat.add_1_r.
rewrite !map_app, HmFi, HmFw, Hcap2m, (pjsf_arrz_of kids2 keys2 _ (pjdt_ncap_pos (length (js_ms en)))).
cbn [map snd]. rewrite Hkb, <- !app_assoc. reflexivity.
Qed.

End x.
